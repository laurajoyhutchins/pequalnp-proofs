import unittest
from reconcile_verdicts import parse_log,UPSTREAM

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
if __name__=="__main__":unittest.main()
