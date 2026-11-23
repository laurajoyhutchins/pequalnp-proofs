"""Reconcile public upstream PR state and exact-head authoritative checker evidence.
No claims, comments, submissions, merges, or desk mutations."""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

UPSTREAM="brilliant-hq/pequalnp-proofs"
OWNER="laurajoyhutchins"
HEAD=re.compile(r"[0-9a-f]{40}")
HEX=re.compile(r"[0-9a-f]{64}")
RUN=re.compile(r"^Run: https://github\.com/brilliant-hq/pequalnp-proofs/actions/runs/([1-9][0-9]*)$",re.M)
COMMENT_HEAD=re.compile(r"^Checked on the base repository at commit " + chr(96) + r"([0-9a-f]{7,40})" + chr(96) + r"\.$",re.M)
ANSI=re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
STAMP=re.compile(r"^\d{4}-\d{2}-\d{2}T\S+Z ")
PATH=re.compile(r"lean/PEqualNP/Outside/L_[a-z0-9_]+\.lean")

def gh(endpoint, *args, raw=False):
    # Never execute or interpolate API response text as a command.
    data=subprocess.run(["gh","api",endpoint,*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
    return data if raw else json.loads(data)

def paged(endpoint):
    page=1
    while True:
        result=gh(endpoint+("&" if "?" in endpoint else "?")+"per_page=100&page="+str(page))
        if not isinstance(result,list): raise ValueError("expected API array")
        yield from result
        if len(result)<100: return
        page+=1

def parse_log(log, pr, run, file):
    """Only exact, unquoted records from the upstream authoritative job count."""
    if not (run.get("path")==".github/workflows/authoritative.yml" and
            run.get("event")=="workflow_dispatch" and run.get("head_branch")=="main" and
            run.get("repository",{}).get("full_name")==UPSTREAM and run.get("status")=="completed"):
        return None
    lines=[STAMP.sub("",ANSI.sub("",s),count=1) for s in log.splitlines()]
    # GitHub echoes the shell script with indentation; quoted proof output starts with '  | '.
    outs=[]; heads=[]; bases=[]; verdicts=[]
    for line in lines:
        if line.startswith("OUTSIDE {"):
            try: outs.append(json.loads(line[8:]))
            except ValueError: return None
        elif line.startswith("head commit: "):
            m=re.fullmatch(r"head commit: ([0-9a-f]{40})   file: (\S+)   content hash: ([0-9a-f]{40})",line)
            if m: heads.append(m.groups())
        elif line.startswith("base commit: "):
            m=re.fullmatch(r"base commit: ([0-9a-f]{40})   statement sha256: ([0-9a-f]{64})",line)
            if m: bases.append(m.groups())
        elif re.fullmatch(r"VERDICT: (ACCEPTED|REJECTED|FAULT) \(checker exit [0-9]+\)",line):
            verdicts.append(line)
    if not(len(outs)==len(heads)==len(bases)==len(verdicts)==1): return None
    o=outs[0]; head,path,blob=heads[0]; base,statement=bases[0]; verdict=verdicts[0]
    if not (o.get("pr")==pr["number"] and head==pr["head"]["sha"] and path==file["filename"] and
            PATH.fullmatch(path) and blob==file["sha"] and o.get("file")==path and
            base==run["head_sha"] and o.get("statement_sha256")==statement and
            HEX.fullmatch(o.get("file_sha256","")) and
            re.fullmatch(r"L-[a-z0-9]+(?:-[a-z0-9]+)*",o.get("lemma",""))):
        return None
    kind=verdict.split()[1]
    if kind=="ACCEPTED" and not (verdict=="VERDICT: ACCEPTED (checker exit 0)" and run.get("conclusion")=="success"):
        return None
    if kind=="REJECTED" and not (verdict=="VERDICT: REJECTED (checker exit 1)" and run.get("conclusion")=="failure"):
        return None
    if kind=="FAULT" and run.get("conclusion")!="failure": return None
    return {"kind":kind,"run_id":run["id"],"run_url":run["html_url"],"head_sha":head,
            "base_sha":base,"file":path,"blob":blob,"file_sha256":o["file_sha256"],
            "statement_sha256":statement,"gap":o["lemma"]}

PUBLIC="https://data.pequalnp.com/"
def public_json(path):
    if not (path=="head.json" or re.fullmatch(r"data/contributors\.[0-9a-f]{12}\.json",path)
            or re.fullmatch(r"data/lemma/L-[a-z0-9]+(?:-[a-z0-9]+)*\.[0-9a-f]{12}\.json",path)):
        raise ValueError("unexpected public data path")
    raw=subprocess.run(["curl","-fsS","--proto","=https","--max-redirs","0",
                        "--max-filesize","20000000","--max-time","60",PUBLIC+path],
                       check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
    return json.loads(raw)

def public_credit(detail, credit, pr, file, proof):
    """Authoritative public credit, separately from independently accessed checker logs."""
    a=detail.get("artifact") or {}; c=detail.get("contributor") or {}
    statement=detail.get("formal_statement")
    run=a.get("runner_url","")
    if not (pr.get("merged") is True and detail.get("id")==credit.get("id") and
            detail.get("status")=="checked" and c.get("github")==pr["user"]["login"] and
            c.get("pr_url")==pr["html_url"] and a.get("lean_file")==file["filename"] and
            a.get("content_hash")=="sha256:"+hashlib.sha256(proof).hexdigest() and
            isinstance(statement,str) and
            detail.get("statement_hash")=="sha256:"+hashlib.sha256(statement.encode()).hexdigest() and
            re.fullmatch(r"https://github\.com/brilliant-hq/pequalnp-proofs/actions/runs/[1-9][0-9]*",run)):
        return None
    return {"kind":"CHECKED_CREDIT","gap":detail["id"],"source":PUBLIC+"data/lemma/"+credit["id"]+"."+credit["ref"]+".json",
            "contributor":c["github"],"pr_url":c["pr_url"],"runner_url":run,"head_sha":pr["head"]["sha"],
            "proof_sha256":a["content_hash"][7:],"statement_sha256":detail["statement_hash"][7:],
            "status_at":detail.get("status_at")}

def inspect_pr(number, contributors):
    pr=gh(f"repos/{UPSTREAM}/pulls/{number}")
    if pr["base"]["repo"]["full_name"]!=UPSTREAM or pr["base"]["ref"]!="main":
        raise ValueError("unexpected base")
    row={"number":number,"url":pr["html_url"],"title":pr["title"],"author":pr["user"]["login"],
         "head_sha":pr["head"]["sha"],"pr_state":"merged" if pr["merged"] else pr["state"],
         "merge_commit_sha":pr.get("merge_commit_sha") if pr["merged"] else None,
         "authoritative_exact_head_verdict":None,"public_checked_credit":None,"evidence_errors":[]}
    files=list(paged(f"repos/{UPSTREAM}/pulls/{number}/files"))
    if len(files)!=1 or pr["changed_files"]!=1 or files[0]["status"]!="added" or not PATH.fullmatch(files[0]["filename"]):
        row["evidence_errors"].append("not an exact one-file proof PR")
        return row
    file=files[0]
    row["file"]=file["filename"];row["blob"]=file["sha"]
    # Match the official public credit record to the actual merged PR and exact proof bytes.
    for person in contributors:
        if person.get("github")!=row["author"]: continue
        for credit in person.get("lemmas",[]):
            gid=credit.get("id",""); ref=credit.get("ref","")
            if not (re.fullmatch(r"L-[a-z0-9]+(?:-[a-z0-9]+)*",gid) and re.fullmatch(r"[0-9a-f]{12}",ref)):
                continue
            if file["filename"]!="lean/PEqualNP/Outside/"+gid.replace("-","_")+".lean":continue
            try:
                detail=public_json("data/lemma/"+gid+"."+ref+".json")
                proof=gh(f"repos/{UPSTREAM}/git/blobs/{file['sha']}", "-H","Accept: application/vnd.github.raw+json",raw=True)
                matched=public_credit(detail,credit,pr,file,proof)
                if matched: row["public_checked_credit"]=matched
                else: row["evidence_errors"].append("public credit record does not match PR proof bytes")
            except (ValueError,KeyError,subprocess.CalledProcessError) as e:
                row["evidence_errors"].append("public credit unavailable: "+type(e).__name__)
    # Comments are discovery hints, never standalone authoritative verdicts.
    seen=set(); evidence=[]
    for comment in paged(f"repos/{UPSTREAM}/issues/{number}/comments"):
        if comment.get("author_association") not in ("OWNER","MEMBER","COLLABORATOR"): continue
        body=comment.get("body") or ""; h=COMMENT_HEAD.search(body); m=RUN.search(body)
        if not h or not m or not row["head_sha"].startswith(h[1]) or m[1] in seen: continue
        seen.add(m[1])
        try:
            run=gh(f"repos/{UPSTREAM}/actions/runs/{m[1]}")
            # Jobs endpoint returns an object, not an array. Read all pages.
            found=[]; page=1
            while True:
                x=gh(f"repos/{UPSTREAM}/actions/runs/{m[1]}/jobs?per_page=100&page={page}")
                found.extend(x["jobs"])
                if len(x["jobs"])<100:break
                page+=1
            checks=[j for j in found if j["name"]=="check" and j["status"]=="completed"]
            if len(checks)!=1: raise ValueError("missing unique checker job")
            log=gh(f"repos/{UPSTREAM}/actions/jobs/{checks[0]['id']}/logs",raw=True).decode("utf-8",errors="replace")
            verdict=parse_log(log,pr,run,file)
            if verdict:
                # Verify proof byte hash independently of log text.
                data=gh(f"repos/{UPSTREAM}/git/blobs/{file['sha']}", "-H","Accept: application/vnd.github.raw+json",raw=True)
                if hashlib.sha256(data).hexdigest()!=verdict["file_sha256"]:
                    raise ValueError("proof SHA-256 mismatch")
                verdict["comment_url"]=comment["html_url"]; evidence.append(verdict)
            else: row["evidence_errors"].append("no exact-head verdict in run "+m[1])
        except (ValueError,KeyError,subprocess.CalledProcessError) as e:
            row["evidence_errors"].append("could not independently reconcile run "+m[1]+": "+type(e).__name__)
    row["authoritative_evidence"]=sorted(evidence,key=lambda e:e["run_id"])
    # Do not silently choose between contradictory acceptance and rejection.
    judgments={e["kind"] for e in evidence if e["kind"]!="FAULT"}
    if len(judgments)>1: row["evidence_errors"].append("conflicting exact-head judgments")
    elif evidence:
        row["authoritative_exact_head_verdict"]=next(iter(judgments)) if judgments else "FAULT"
    return row

def discover():
    q=f"repo:{UPSTREAM} is:pr author:{OWNER}"
    page=1; numbers=set(); total=None
    while True:
        x=gh("search/issues","--method","GET","-f","q="+q,"-f","per_page=100","-f","page="+str(page))
        if x.get("incomplete_results"):raise ValueError("incomplete upstream search")
        if total is None: total=x["total_count"]
        if x["total_count"]!=total or total>1000:raise ValueError("search changed or exceeds GitHub search window")
        numbers.update(i["number"] for i in x["items"])
        if len(x["items"])<100 or len(numbers)==total: break
        page+=1
    if len(numbers)!=total:raise ValueError("incomplete or overlapping PR search")
    return sorted(numbers)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("output",type=Path);p.add_argument("--regression-pr",type=int)
    a=p.parse_args()
    nums=[a.regression_pr] if a.regression_pr else discover()
    head=public_json("head.json")
    contributors_path=head["files"]["contributors"]
    contributors=public_json(contributors_path)["contributors"]
    rows=[inspect_pr(n,contributors) for n in nums]
    if not a.regression_pr and any(x["author"]!=OWNER for x in rows):raise ValueError("search returned unrelated author")
    result={"scope":"historical_regression_only" if a.regression_pr else "account_pr_reconciliation",
            "source":UPSTREAM,"account":OWNER,"public_contributors_source":PUBLIC+contributors_path,"public_generated_at":head.get("generated_at"),"observed_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "prs":rows}
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print("Reconciled PR records:",len(rows),"exact-head verdicts:",sum(x["authoritative_exact_head_verdict"] is not None for x in rows),"public checked credits:",sum(x["public_checked_credit"] is not None for x in rows))
if __name__=="__main__":main()
