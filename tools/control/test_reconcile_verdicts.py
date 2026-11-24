import unittest
from reconcile_verdicts import parse_log,public_credit,UPSTREAM
import hashlib

class VerdictTests(unittest.TestCase):
    def test_exact_head_and_unquoted_only(self):
        head="a"*40;base="b"*40;blob="c"*40;proof="d"*64;statement="e"*64
        path="lean/PEqualNP/Outside/L_test_1.lean"
        pr={"number":7,"head":{"sha":head}}
        file={"filename":path,"sha":blob}
        run={"path":".github/workflows/authoritative.yml","event":"workflow_dispatch","head_branch":"main",
             "repository":{"full_name":UPSTREAM},"status":"completed","conclusion":"success",
             "head_sha":base,"id":8,"html_url":"https://github.com/"+UPSTREAM+"/actions/runs/8"}
        log="\n".join(['OUTSIDE {"lemma":"L-test-1","pr":7,"file":"'+path+'","file_sha256":"'+proof+'","statement_sha256":"'+statement+'"}',
                       f"head commit: {head}   file: {path}   content hash: {blob}",
                       f"base commit: {base}   statement sha256: {statement}",
                       "VERDICT: ACCEPTED (checker exit 0)"])
        self.assertEqual(parse_log(log,pr,run,file)["kind"],"ACCEPTED")
        self.assertIsNone(parse_log("\n".join("  | "+x for x in log.splitlines()),pr,run,file))
        self.assertIsNone(parse_log(log,{"number":7,"head":{"sha":"f"*40}},run,file))
        self.assertIsNone(parse_log(log,pr,dict(run,path=".github/workflows/advisory.yml"),file))
        self.assertIsNone(parse_log(log,pr,dict(run,conclusion="failure"),file))
        self.assertIsNone(parse_log(log+"\nVERDICT: REJECTED (checker exit 1)",pr,run,file))
    def test_public_credit_binds_pr_and_proof(self):
        h=lambda x: "sha256:"+hashlib.sha256(x).hexdigest()
        pr={"merged":True,"number":7,"html_url":"https://github.com/"+UPSTREAM+"/pull/7",
            "user":{"login":"researcher"},"head":{"sha":"a"*40}}
        f={"filename":"lean/PEqualNP/Outside/L_test_1.lean"}
        c={"id":"L-test-1","ref":"b"*12}
        d={"id":c["id"],"status":"checked","formal_statement":"True","statement_hash":h(b"True"),
            "contributor":{"github":"researcher","pr_url":pr["html_url"]},
            "artifact":{"lean_file":f["filename"],"content_hash":h(b"proof"),
                        "runner_url":"https://github.com/"+UPSTREAM+"/actions/runs/8"}}
        self.assertEqual(public_credit(d,c,pr,f,b"proof")["kind"],"CHECKED_CREDIT")
        legacy=dict(d,contributor=dict(d["contributor"],pr_url=d["contributor"]["pr_url"].replace("open-goat","brilliant-hq")),artifact=dict(d["artifact"],runner_url=d["artifact"]["runner_url"].replace("open-goat","brilliant-hq")))
        self.assertEqual(public_credit(legacy,c,pr,f,b"proof")["kind"],"CHECKED_CREDIT")
        self.assertIsNone(public_credit(dict(legacy,contributor=dict(legacy["contributor"],pr_url="https://github.com/other/pequalnp-proofs/pull/7")),c,pr,f,b"proof"))
        self.assertIsNone(public_credit(dict(legacy,contributor=dict(legacy["contributor"],pr_url="https://github.com/brilliant-hq/pequalnp-proofs/pull/8")),c,pr,f,b"proof"))
        self.assertIsNone(public_credit(d,c,pr,f,b"changed"))
        self.assertIsNone(public_credit(d,c,dict(pr,merged=False),f,b"proof"))
        self.assertIsNone(public_credit(dict(d,status="conjecture"),c,pr,f,b"proof"))
if __name__=="__main__":unittest.main()
