import os
import pathlib
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("diagnose.sh").resolve()

class DiagnosticTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name) / "checkout"
        self.root.mkdir()
        self.receipt = pathlib.Path(self.tmp.name) / "receipts"
        self.candidate = "lean/PEqualNP/Research/Example.lean"
        self.put(self.candidate, "theorem example : True := trivial\n")
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            self.put("lean/" + name, "pinned\n")
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture")
        self.bin = pathlib.Path(self.tmp.name) / "bin"
        self.bin.mkdir()
        for name, body in {
            "lean": '#!/bin/bash\necho Lean fixture\n',
            "lake": '''#!/bin/bash
if [[ "$1" == --version ]]; then echo Lake fixture; exit 0; fi
[[ "$LAKE_ARTIFACT_CACHE" == false && -z "${LEAN_PATH+x}" && -z "${ELAN_TOOLCHAIN+x}" ]] || exit 91
[[ "$*" == "build +PEqualNP.Research.Example" ]] || exit 92
echo "target-only $*"
if [[ "${MUTATE:-0}" == 1 ]]; then echo changed >> PEqualNP/Research/Example.lean; fi
exit "${BUILD_EXIT:-0}"
'''
        }.items():
            p = self.bin / name
            p.write_text(body)
            p.chmod(0o755)

    def put(self, name, content):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)

    def git(self, *args):
        subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def run_diag(self, candidate=None, **extra):
        env = dict(os.environ, PATH=str(self.bin) + ":" + os.environ["PATH"],
                   LEAN_PATH="bad", ELAN_TOOLCHAIN="bad", LAKE_ARTIFACT_CACHE="true", **extra)
        return subprocess.run(["bash", str(SCRIPT), candidate or self.candidate, str(self.receipt)],
                              cwd=self.root, env=env, text=True, capture_output=True)

    def test_target_only_success(self):
        r = self.run_diag()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((self.receipt / "result.txt").read_text().strip(), "DIAGNOSTIC_BUILD_SUCCEEDED")
        self.assertIn("build +PEqualNP.Research.Example", (self.receipt / "build.log").read_text())
        self.assertNotIn("ACCEPTED", r.stdout)
        self.assertTrue((self.receipt / "elapsed-seconds.txt").exists())

    def test_compile_failure(self):
        r = self.run_diag(BUILD_EXIT="7")
        self.assertEqual(r.returncode, 1)
        self.assertEqual((self.receipt / "build-exit.txt").read_text().strip(), "7")
        self.assertEqual((self.receipt / "result.txt").read_text().strip(), "DIAGNOSTIC_BUILD_FAILED")

    def test_source_mutation(self):
        r = self.run_diag(MUTATE="1")
        self.assertEqual(r.returncode, 3)
        self.assertEqual((self.receipt / "result.txt").read_text().strip(), "DIAGNOSTIC_INVALIDATED")

    def test_invalid_target(self):
        self.assertEqual(self.run_diag("lean/PEqualNP/../Bad.lean").returncode, 2)

    def test_changed_configuration(self):
        self.put("lean/lean-toolchain", "different\n")
        self.assertEqual(self.run_diag().returncode, 2)

    def test_receipt_cannot_be_reused(self):
        self.assertEqual(self.run_diag().returncode, 0)
        self.assertEqual(self.run_diag().returncode, 2)

if __name__ == "__main__":
    unittest.main()
