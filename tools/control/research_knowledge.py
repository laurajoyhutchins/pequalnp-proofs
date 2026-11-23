"""Join posted research packets with the public, versioned swarm research map.
No credentials, claim actions, submissions or candidate execution."""
import argparse
import concurrent.futures
import datetime
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

ROOT="https://data.pequalnp.com/"
ID=re.compile(r"L-[a-z0-9]+-[0-9]{3,}")
KEY=re.compile(r"[a-z0-9]+")
REF=re.compile(r"[0-9a-f]{12}")
PATH=re.compile(r"(?:head\.json|data/(?:map/overview|map/program/[a-z0-9_]+|plan|search/(?:index|[0-9a-z])|lemma/L-[a-z0-9]+-[0-9]{3,})\.[0-9a-f]{12}\.json)")
def require(x,msg):
    if not x: raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def write(path,x):path.write_text(json.dumps(x,indent=2,sort_keys=True,ensure_ascii=False)+"\n",encoding="utf-8")
def read(path):return json.loads(path.read_bytes())
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def public(path):
    require(isinstance(path,str) and PATH.fullmatch(path),"unexpected public path")
    raw=subprocess.run(["curl","-fsS","--proto","=https","--max-redirs","0","--retry","2",
                        "--max-time","30","--max-filesize","20000000",ROOT+path],
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
    return json.loads(raw),sha(raw)
def identifier(key,n):
    require(KEY.fullmatch(key) and type(n) is int and n>0,"invalid lemma identifier")
    return f"L-{key}-{n:03d}"
def graph(programs):
    nodes={}
    for p in programs:
        key=p["key"];require(KEY.fullmatch(key),"invalid program key")
        for n in p["nodes"]:
            require(isinstance(n,list) and len(n) in (7,8),"unknown compact node schema")
            gid=identifier(key,n[0])
            require(gid not in nodes and isinstance(n[1],str) and len(n[1])==1
                    and isinstance(n[2],list) and isinstance(n[3],str) and REF.fullmatch(n[3]),"invalid/duplicate node")
            deps=[identifier(key,d) if type(d) is int else d for d in n[2]]
            require(all(isinstance(d,str) and ID.fullmatch(d) for d in deps) and len(set(deps))==len(deps),"invalid edges")
            nodes[gid]={"id":gid,"program":p["program"],"status_code":n[1],
                        "depends_on":deps,"detail_path":"data/lemma/"+gid+"."+n[3]+".json"}
    reverse=defaultdict(list)
    for gid,n in nodes.items():
        for d in n["depends_on"]:reverse[d].append(gid)
    for gid,n in nodes.items():
        n["direct_users"]=sorted(reverse[gid])
        n["unmapped_dependencies"]=sorted(d for d in n["depends_on"] if d not in nodes)
    return nodes
def reachable(nodes,gid):
    seen={gid};todo=list(nodes[gid]["direct_users"])
    while todo:
        d=todo.pop()
        if d in seen:continue
        seen.add(d);todo.extend(nodes[d]["direct_users"])
    return sorted(seen-{gid})
def normalized_detail(d,n):
    require(d["id"]==n["id"] and d["program"]==n["program"],"detail identity mismatch")
    require(isinstance(d["status"],str) and isinstance(d["depends_on"],list)
            and isinstance(d["used_by"],list),"invalid detail")
    require(all(isinstance(x,str) and ID.fullmatch(x) for x in d["depends_on"]+d["used_by"]),"invalid detail edges")
    statement=d.get("formal_statement");h=d.get("statement_hash")
    verified=isinstance(statement,str) and h=="sha256:"+sha(statement.encode())
    # Persist only research evidence, never arbitrary identity/credential metadata.
    result={k:d[k] for k in ("id","title","plain_statement","status","status_at","kind","barrier",
              "depends_on","used_by","statement_hash","layer") if k in d}
    result["formal_statement"]=statement if verified else None
    result["statement_hash_verified"]=verified
    result["graph_dependencies_agree"]=set(d["depends_on"])==set(n["depends_on"])
    result["graph_users_agree"]=set(d["used_by"])==set(n["direct_users"])
    result["attempts"]=[{k:a[k] for k in ("when","ended_at","outcome","why_died","reason","summary")
                          if k in a} for a in d.get("attempts",[]) if isinstance(a,dict)]
    artifact=d.get("artifact")
    if isinstance(artifact,dict):
        result["artifact"]={k:artifact[k] for k in ("lean_file","checker_version","checker_run_id","content_hash","runner_url") if k in artifact}
    result["source"]=ROOT+n["detail_path"]
    return result
def join_packet(packet,n,detail,details,nodes):
    if not n or not detail:return {"join":"unavailable","status":None,"depends_on":None}
    if not detail["statement_hash_verified"] or detail["formal_statement"]!=packet["statement"]:
        return {"join":"statement_mismatch","source":detail["source"],"status":None,"depends_on":None}
    if not detail["graph_dependencies_agree"] or not detail["graph_users_agree"]:
        return {"join":"graph_detail_disagreement","source":detail["source"],"status":None,"depends_on":None}
    deps=detail["depends_on"]
    def neighbor(d):
        x=details.get(d);v=nodes.get(d)
        return {"id":d,"title":x.get("title") if x else None,"status":x.get("status") if x else None,
                "source":ROOT+v["detail_path"] if v else None,
                "statement_hash":x.get("statement_hash") if x else None,
                "artifact":x.get("artifact") if x else None}
    return {"join":"exact_statement","source":detail["source"],"status":detail["status"],
            "status_at":detail.get("status_at"),"title":detail.get("title"),"plain_statement":detail.get("plain_statement"),
            "kind":detail.get("kind"),"barrier":detail.get("barrier"),"depends_on":deps,
            "direct_users":detail["used_by"],"recorded_downstream":reachable(nodes,n["id"]),
            "prerequisites":[neighbor(d) for d in deps],"direct_user_details":[neighbor(d) for d in detail["used_by"]],
            "attempts":detail["attempts"],"artifact":detail.get("artifact")}
def normalize_search(raw,nodes):
    """Convert public exact-token postings into explicit IDs, retaining unmapped hits."""
    require(isinstance(raw,dict),"invalid search shard")
    result={};missing=set()
    for word,groups in raw.items():
        require(isinstance(word,str) and word and isinstance(groups,dict),"invalid search token")
        ids=[]
        for key,numbers in groups.items():
            require(KEY.fullmatch(key) and isinstance(numbers,list),"invalid search posting")
            ids.extend(identifier(key,n) for n in numbers)
        result[word]=sorted(set(ids))
        missing.update(g for g in ids if g not in nodes)
    return result,sorted(missing)
def search_intersection(shards,terms):
    """Exact token conjunction only; no inferred synonyms or relevance score."""
    require(bool(terms),"empty search")
    hits=None
    for term in terms:
        require(isinstance(term,str) and bool(term),"invalid search token")
        ids=set(shards.get(term[0],{}).get(term,[]))
        hits=ids if hits is None else hits&ids
    return sorted(hits)
def posted_restrictions(context):
    # Only literal cues in the posted text, no inferred lease status.
    fields=[context.get(k,"") for k in ("title","context")]
    markers=[]
    for field in fields:
        if not isinstance(field,str):continue
        for pattern in (r"not for lease",r"reserved for (?:the )?(?:fleet|closing)",r"reserved:"):
            for m in re.finditer(pattern,field,re.I):markers.append(m.group(0))
    return sorted(set(markers))
def enrich(out):
    index=read(out/"index.json")
    head,head_hash=public("head.json")
    require(head["layout"]=="pnp-export/2","unrecognized export schema")
    overview,overview_hash=public(head["files"]["map"])
    plan,plan_hash=public(head["files"]["plan"])
    sources={"head.json":head_hash,head["files"]["map"]:overview_hash,head["files"]["plan"]:plan_hash}
    programs=[]
    for p in overview["programs"]:
        raw,digest=public(p["file"]);sources[p["file"]]=digest
        require(raw["key"]==p["key"] and raw["program"]==p["id"],"program identity mismatch")
        programs.append(raw)
    nodes=graph(programs)
    posted={g["id"] for g in index["gaps"]}
    target_ids=set()
    for p in plan.get("programs",{}).values():
        if not isinstance(p,dict):continue
        for x in [p.get("target"),*p.get("chain",[])]:
            if isinstance(x,dict) and isinstance(x.get("lemma_id"),str) and ID.fullmatch(x["lemma_id"]):target_ids.add(x["lemma_id"])
    selected=(posted|target_ids)&nodes.keys()
    selected|={d for g in list(selected) for d in nodes[g]["depends_on"]+nodes[g]["direct_users"] if d in nodes}
    details={};errors={}
    def fetch(g):
        n=nodes[g];raw,digest=public(n["detail_path"])
        return normalized_detail(raw,n),digest
    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
        futures={pool.submit(fetch,g):g for g in sorted(selected)}
        for f in concurrent.futures.as_completed(futures):
            g=futures[f]
            try:details[g],sources[nodes[g]["detail_path"]]=f.result()
            except (ValueError,KeyError,TypeError,subprocess.CalledProcessError) as e:errors[g]=type(e).__name__
    # Graph nodes are the entire map; titles/status are enriched only for explicitly retrieved records.
    # Codes are opaque rather than an invented status mapping.
    knowledge=out/"knowledge";knowledge.mkdir()
    by_program=defaultdict(list)
    for gid,n in sorted(nodes.items()):
        d=details.get(gid)
        row=dict(n,source=ROOT+n["detail_path"])
        if d:
            row.update({k:d.get(k) for k in ("title","status","statement_hash","statement_hash_verified","graph_dependencies_agree","graph_users_agree","artifact")})
        by_program[gid.split("-")[1]].append(row)
    for key,rows in sorted(by_program.items()):
        write(knowledge/("program-"+key+".json"),{"program_key":key,"nodes":rows})
    # Store only requested, source-identified normalized lemma records. One per file allows precise retrieval.
    for gid,d in sorted(details.items()):write(knowledge/(gid+".json"),d)
    # Copy official lexical search postings, normalized to explicit IDs.
    search,search_hash=public(head["files"]["search"]);sources[head["files"]["search"]]=search_hash
    require(isinstance(search["shards"],dict) and all(re.fullmatch(r"[0-9a-z]",k) for k in search["shards"]),"unknown search shard scheme")
    search_shards={};search_missing=set()
    for key,path in sorted(search["shards"].items()):
        require(path.startswith("data/search/"+key+"."),"search shard identity mismatch")
        data,digest=public(path);sources[path]=digest
        postings,missing=normalize_search(data,nodes)
        search_shards[key]=postings;search_missing.update(missing)
        write(knowledge/("search-"+key+".json"),{"source":ROOT+path,"source_sha256":digest,"tokens":postings,"unmapped_ids":missing})
    # Strategy text/plan are explicitly official inputs, not ranking instructions from this tool.
    strategy={"source":ROOT+head["files"]["plan"],"head_source":ROOT+"head.json","generated_at":head.get("generated_at"),
              "strategy_update":{k:head["status"][k] for k in ("at","text") if k in head.get("status",{})},
              "plan_updated_at":plan.get("updated_at"),"programs":plan.get("programs",{})}
    write(knowledge/"strategy.json",strategy)
    counts=Counter();rows=[]
    for row in index["gaps"]:
        gid=row["id"];file=out/row["packet"];p=read(file)
        joined=join_packet(p,nodes.get(gid),details.get(gid),details,nodes)
        p["public_research"]=joined
        row["public_join"]=joined["join"]
        row["public_status"]=joined["status"]
        row["public_dependencies"]=joined["depends_on"]
        row["public_direct_users"]=joined.get("direct_users")
        row["public_recorded_downstream"]=joined.get("recorded_downstream")
        row["title"]=joined.get("title") or p.get("context",{}).get("title")
        row["prior_attempt_count"]=len(joined["attempts"]) if joined["join"]=="exact_statement" else None
        # Transparent evidence dimensions only; never score missing information as zero.
        row["official_plan_reference"]=gid in target_ids
        row["closure_clear"]=row["closure_blocker"] is None and not row["path_exists"]
        row["posted_restriction_markers"]=posted_restrictions(p.get("context",{}))
        p["posted_restriction_markers"]=row["posted_restriction_markers"]
        row["prerequisite_statuses"]=[{"id":d["id"],"status":d["status"]} for d in joined.get("prerequisites",[])] if joined["join"]=="exact_statement" else None
        counts[joined["join"]]+=1;write(file,p)
        rows.append(row)
    # A short list of evidence slices, not a numeric priority rank or allocation decision.
    exact=[r for r in rows if r["public_join"]=="exact_statement"]
    def ids(pred):return sorted(r["id"] for r in exact if pred(r))
    slices={"official_plan_references":ids(lambda r:r["official_plan_reference"]),
            "recorded_direct_users":ids(lambda r:bool(r["public_direct_users"])),
            "recorded_prerequisites":ids(lambda r:bool(r["public_dependencies"])),
            "nonempty_prior_attempts":ids(lambda r:r["prior_attempt_count"]>0),
            "closure_blockers":sorted(r["id"] for r in rows if not r["closure_clear"]),
            "posted_restriction_markers":sorted(r["id"] for r in rows if r["posted_restriction_markers"]),
            "nonconjecture_or_unavailable":sorted(r["id"] for r in rows if r["public_status"]!="conjecture")}
    summary={"schema":"pnp-export/2","generated_at":head.get("generated_at"),"observed_at":now(),
             "source_version":head.get("version"),"source_sha256":sources,
             "generator_sha256":sha(Path(__file__).read_bytes()),"graph_nodes":len(nodes),
             "recorded_edges":sum(len(n["depends_on"]) for n in nodes.values()),
             "unmapped_edges":sum(len(n["unmapped_dependencies"]) for n in nodes.values()),
             "details_requested":len(selected),"details_retrieved":len(details),"detail_errors":errors,
             "search_shards":len(search_shards),"search_tokens":sum(len(x) for x in search_shards.values()),"search_unmapped_ids":sorted(search_missing),
             "posted_join_counts":dict(counts),"strategy":"knowledge/strategy.json","selection_evidence":slices,
             "interpretation":"Recorded edges are not exhaustive mathematical or Lean import dependencies. No ranking or live ownership is inferred."}
    write(knowledge/"summary.json",summary)
    index["public_research"]={k:summary[k] for k in ("schema","generated_at","source_version","generator_sha256","graph_nodes",
             "recorded_edges","unmapped_edges","details_requested","details_retrieved","posted_join_counts","selection_evidence","strategy","search_shards","search_tokens","search_unmapped_ids")}
    index["public_research"]["summary"]="knowledge/summary.json"
    # Include changes in sources even if gap feed/base are unchanged; not observation-time churn.
    index["public_research_sha256"]=sha(json.dumps({"sources":{k:v for k,v in sources.items() if k!="head.json"},
       "strategy":strategy["strategy_update"],"errors":errors,"generator":summary["generator_sha256"]},sort_keys=True).encode())
    write(out/"index.json",index)
    print("Public research enrichment:",json.dumps({k:summary[k] for k in ("graph_nodes","recorded_edges","unmapped_edges","details_requested","details_retrieved","posted_join_counts","selection_evidence","search_shards","search_tokens","search_unmapped_ids")},sort_keys=True))
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("out",type=Path);a=p.parse_args();enrich(a.out)
