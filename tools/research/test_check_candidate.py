import os
import pathlib
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name('check-candidate.sh').resolve()

class CheckerModeTest(unittest.TestCase):
    """Contract tests with fake guard/checker, not mathematical proof tests."""
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.base = self.root / 'base'
        self.base.mkdir()
        for name in ('lean/lean-toolchain', 'lean/lake-manifest.json',
                     'tools/check-lean.mjs', '.github/scripts/outside-guard.mjs'):
            p = self.base / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('fixture\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture')
        self.snapshot = self.root / 'gaps.json'
        self.snapshot.write_text('{}')
        self.candidate = self.root / 'candidate.lean'
        self.candidate.write_text('theorem demo : True := trivial\n')
        self.receipt = self.root / 'receipt'
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        node = self.bin / 'node'
        node.write_text('''#!/usr/bin/env bash
set -eu
printf '%s\\n' "$*" >> "$CALLS"
[[ "${!#}" == "$EXPECTED_KIND" ]] || exit 91
case "$1:$2" in
  .github/scripts/outside-guard.mjs:gap)
    printf '%s\\n' "${GUARD_KIND:-$EXPECTED_KIND}" > "$6/gap.kind"
    printf 'True' > "$6/statement.txt"
    printf '[]' > "$6/imports.json"
    ;;
  .github/scripts/outside-guard.mjs:imports|.github/scripts/outside-guard.mjs:closure)
    ;;
  tools/check-lean.mjs:*)
    [[ -f "$2" ]] || exit 92
    printf 'ACCEPTED (%s) fixture\\n' "${VERDICT_KIND:-$EXPECTED_KIND}"
    ;;
  *) exit 93 ;;
esac
''')
        node.chmod(0o755)

    def git(self, *args):
        subprocess.run(['git', *args], cwd=self.base, check=True, capture_output=True)

    def run_mode(self, kind, file=None, **extra):
        file = file or ('lean/PEqualNP/Outside/R_meta_123_7.lean' if kind == 'reduce'
                        else 'lean/PEqualNP/Outside/L_meta_123.lean')
        env = dict(os.environ, PATH=str(self.bin) + ':' + os.environ['PATH'],
                   CALLS=str(self.root / 'calls'), EXPECTED_KIND=kind, **extra)
        r = subprocess.run(['bash', str(SCRIPT), '--kind', kind, str(self.base), str(self.snapshot),
                            'L-meta-123', file, str(self.candidate), str(self.receipt)],
                           cwd=self.root, env=env, text=True, capture_output=True)
        self.assertFalse((self.base / file).exists(), 'temporary candidate must be removed')
        return r

    def accepted(self, kind):
        r = self.run_mode(kind)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual((self.receipt / 'result.txt').read_text().strip(), 'LOCAL_CHECK_ACCEPTED')
        calls = (self.root / 'calls').read_text().splitlines()
        self.assertEqual(len(calls), 4)
        self.assertTrue(all(s.endswith(' ' + kind) for s in calls))

    def test_check(self): self.accepted('check')
    def test_refute(self): self.accepted('refute')
    def test_reduce(self): self.accepted('reduce')
    def test_wrong_filename(self):
        r = self.run_mode('reduce', file='lean/PEqualNP/Outside/L_meta_123.lean')
        self.assertEqual(r.returncode, 2)
        self.assertFalse((self.root / 'calls').exists())
    def test_mismatched_guard_kind(self):
        r = self.run_mode('reduce', GUARD_KIND='check')
        self.assertEqual(r.returncode, 2)
        self.assertEqual(len((self.root / 'calls').read_text().splitlines()), 1)
    def test_wrong_verdict_kind(self):
        r = self.run_mode('reduce', VERDICT_KIND='check')
        self.assertEqual(r.returncode, 1)
        self.assertEqual((self.receipt / 'result.txt').read_text().strip(), 'LOCAL_CHECK_NOT_ACCEPTED')

if __name__ == '__main__':
    unittest.main()
