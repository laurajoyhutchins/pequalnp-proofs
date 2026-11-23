"""Build a one-file commit without checking out or executing candidate code."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

GAP = re.compile(r"L-[a-z0-9]+(?:-[a-z0-9]+)*")
SHA = re.compile(r"[0-9a-f]{40}")
HASH = re.compile(r"[0-9a-f]{64}")
FILE = re.compile(r"lean/PEqualNP/Outside/L_[a-z0-9_]+\.lean")
def require(value, message):
    if not value:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(base, *args, data=None, env=None):
    return subprocess.run(["git", "-C", str(base), *args], input=data, env=env,
                          check=True, stdout=subprocess.PIPE).stdout

def construct(base, upstream_sha, path, candidate, gap):
    """Pure Git objects. No checkout, hooks, push or desk action."""
    require(SHA.fullmatch(upstream_sha) and GAP.fullmatch(gap) and FILE.fullmatch(path), "invalid identity")
    require(0 < len(candidate) <= 524288, "candidate size")
    require(git(base, "rev-parse", "HEAD").decode().strip() == upstream_sha, "base moved")
    require(not git(base, "ls-tree", upstream_sha, "--", path), "target exists")
    blob = git(base, "hash-object", "-w", "--stdin", data=candidate).decode().strip()
    with tempfile.TemporaryDirectory() as tmp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(tmp)/"index"),
                   GIT_AUTHOR_NAME="Research exporter", GIT_AUTHOR_EMAIL="research-exporter@users.noreply.github.com",
                   GIT_COMMITTER_NAME="Research exporter", GIT_COMMITTER_EMAIL="research-exporter@users.noreply.github.com",
                   GIT_AUTHOR_DATE="2000-01-01T00:00:00Z", GIT_COMMITTER_DATE="2000-01-01T00:00:00Z")
        git(base, "read-tree", upstream_sha, env=env)
        git(base, "update-index", "--add", "--cacheinfo", "100644", blob, path, env=env)
        tree = git(base, "write-tree", env=env).decode().strip()
        commit = git(base, "-c", "commit.gpgsign=false", "commit-tree", tree, "-p", upstream_sha,
                     data=(gap+"\n").encode(), env=env).decode().strip()
    require(git(base, "diff-tree", "--no-commit-id", "-r", "--name-status", "-z", upstream_sha, commit)
            == b"A\0"+path.encode()+b"\0", "not exactly one addition")
    require(git(base, "ls-tree", commit, "--", path).decode().startswith("100644 blob "+blob+"\t"), "wrong mode/blob")
    require(git(base, "show", commit+":"+path)==candidate, "bytes changed")
    return commit, blob

def verify_receipt(receipt, gap, head, base, candidate, statement, path, module):
    """A local receipt is necessary, not independent authority. Caller authenticates workflow/run."""
    i=json.loads((receipt/"candidate.identity.json").read_bytes())
    require(i.get("scope")=="fork_local_only", "not a live local candidate receipt")
    for k,v in {"gap":gap,"candidate_sha":head,"upstream_sha":base,"file":path,
                "statement_sha256":digest(statement)}.items():
        require(i.get(k)==v, "receipt identity differs: "+k)
    before=(receipt/"before.sha256").read_bytes()
    require(before==(receipt/"after.sha256").read_bytes(), "checked files changed")
    checks={}
    for line in before.decode().splitlines():
        m=re.fullmatch(r"([0-9a-f]{64})  (.+)",line)
        require(m and m[2] not in checks,"invalid hash manifest")
        checks[m[2]]=m[1]
    require(checks.get("base/"+path)==digest(candidate),"proof hash differs")
    require(checks.get("in/statement.txt")==digest(statement),"statement hash differs")
    require((receipt/"local-verdict.txt").read_text().strip()=="VERDICT: ACCEPTED (checker exit 0)","not locally accepted")
    log=(receipt/"checker.out").read_text().splitlines()
    require(log and log[-1].startswith("ACCEPTED (check): "+module+";"),"wrong checker final line")
    manifests=[json.loads(x[len("MANIFEST "):]) for x in log if x.startswith("MANIFEST ")]
    require(len(manifests)==1 and all(isinstance(manifests[0].get(k),list) for k in ("defs","rests_on")),"missing checker manifest")
    require(not any(x.startswith("REJECTED") for x in log),"conflicting checker output")
    return i

def prepare(base, receipt, snapshot, head, gap, candidate_path, output, run):
    require(SHA.fullmatch(head) and GAP.fullmatch(gap) and re.fullmatch(r"[1-9][0-9]*",run),"invalid input")
    rev=git(base,"rev-parse","HEAD").decode().strip()
    all_gaps=json.loads(snapshot.read_bytes())
    found=[g for g in all_gaps["gaps"] if g.get("id")==gap]
    require(len(found)==1,"gap no longer posted")
    g=found[0]; path=g["file"]; module=g["module"]
    require(FILE.fullmatch(path) and module==path[5:-5].replace("/", "."),"invalid posted path")
    proof=candidate_path.read_bytes()
    statement=g["statement"].encode()
    i=verify_receipt(receipt,gap,head,rev,proof,statement,path,module)
    require(i.get("candidate_blob")==git(base,"hash-object","--stdin",data=proof).decode().strip(),"candidate blob changed")
    # All format and import checks use the actual current upstream guard.
    with tempfile.TemporaryDirectory() as tmp:
        guard=base/".github/scripts/outside-guard.mjs"
        for args in [("gap",snapshot,gap,path,tmp),("imports",candidate_path,Path(tmp)/"imports.json",path),
                     ("closure",base,Path(tmp)/"imports.json",path,tmp)]:
            subprocess.run(["node",str(guard),*map(str,args)],check=True)
        require((Path(tmp)/"statement.txt").read_bytes()==statement,"guard statement mismatch")
    commit,blob=construct(base,rev,path,proof,gap)
    branch="submission/"+gap+"/"+head+"-"+rev[:12]
    output.mkdir()
    (output/"proof.lean").write_bytes(proof)
    (output/"export.json").write_text(json.dumps({"scope":"prepared_not_authorized","gap":gap,"candidate_sha":head,
        "upstream_sha":rev,"file":path,"blob":blob,"proof_sha256":digest(proof),"statement_sha256":digest(statement),
        "commit":commit,"branch":branch,"verification_run":int(run)},indent=2)+"\n")
    return commit

if __name__=="__main__":
    p=argparse.ArgumentParser()
    for name in ("base","receipt","snapshot","head","gap","candidate","output","run"): p.add_argument(name)
    a=p.parse_args()
    print(prepare(Path(a.base),Path(a.receipt),Path(a.snapshot),a.head,a.gap,Path(a.candidate),Path(a.output),a.run))
