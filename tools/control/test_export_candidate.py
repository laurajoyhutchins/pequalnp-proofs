import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from export_candidate import construct, digest, git, verify_receipt

class ExportTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name)
        subprocess.run(["git","init","-q",str(self.base)],check=True)
        (self.base/"README").write_text("base")
        git(self.base,"add","README")
        git(self.base,"-c","user.name=Test","-c","user.email=test@example.com","commit","-qm","base")
        self.rev=git(self.base,"rev-parse","HEAD").decode().strip()
        self.path="lean/PEqualNP/Outside/L_test_1.lean"
        self.proof=b"theorem PEqualNP.Outside.L_test_1 : True := by trivial\n"
    def test_deterministic_one_file(self):
        a=construct(self.base,self.rev,self.path,self.proof,"L-test-1")
        self.assertEqual(a,construct(self.base,self.rev,self.path,self.proof,"L-test-1"))
        self.assertEqual(git(self.base,"status","--porcelain"),b"")
        self.assertEqual(git(self.base,"show",a[0]+":"+self.path),self.proof)
    def test_existing_wrong_base_and_traversal(self):
        for rev,path in [("0"*40,self.path),(self.rev,"../evil"),(self.rev,"README")]:
            with self.assertRaises(ValueError): construct(self.base,rev,path,self.proof,"L-test-1")
        c,_=construct(self.base,self.rev,self.path,self.proof,"L-test-1")
        git(self.base,"checkout","-q","--detach",c)
        with self.assertRaises(ValueError): construct(self.base,c,self.path,self.proof,"L-test-1")
    def test_receipt_fail_closed(self):
        d=self.base/"receipt";d.mkdir();head="a"*40;s=b"True";module="PEqualNP.Outside.L_test_1"
        identity={"scope":"fork_local_only","gap":"L-test-1","candidate_sha":head,"upstream_sha":self.rev,
                  "file":self.path,"statement_sha256":digest(s)}
        (d/"candidate.identity.json").write_text(json.dumps(identity))
        manifest=(digest(self.proof)+"  base/"+self.path+"\n"+digest(s)+"  in/statement.txt\n")
        for n in ("before.sha256","after.sha256"): (d/n).write_text(manifest)
        (d/"local-verdict.txt").write_text("VERDICT: ACCEPTED (checker exit 0)\n")
        (d/"checker.out").write_text('MANIFEST {"defs":[],"rests_on":[]}\nACCEPTED (check): '+module+'; axioms []\n')
        args=(d,"L-test-1",head,self.rev,self.proof,s,self.path,module)
        verify_receipt(*args)
        (d/"after.sha256").write_text("changed")
        with self.assertRaises(ValueError): verify_receipt(*args)
        (d/"after.sha256").write_text(manifest)
        (d/"local-verdict.txt").write_text("VERDICT: FAULT")
        with self.assertRaises(ValueError): verify_receipt(*args)
        (d/"local-verdict.txt").write_text("VERDICT: ACCEPTED (checker exit 0)\n")
        identity["scope"]="historical_regression_only"
        (d/"candidate.identity.json").write_text(json.dumps(identity))
        with self.assertRaises(ValueError): verify_receipt(*args)
if __name__=="__main__": unittest.main()
