#!/usr/bin/env python3
"""Measure real swarm checks without altering the checker or toolchain.

Linux, Python 3.10+, GNU time, Node, pinned Lean and Mathlib.
Run only trusted candidate code in a disposable research checkout.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import tempfile
import time
import unittest


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def capture(args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def verdict(code, output):
    lines = output.splitlines()
    if code == 0 and lines and lines[-1].startswith("ACCEPTED ("):
        return "accepted"
    if code == 1 and any(x.startswith("REJECTED (") for x in lines):
        return "rejected"
    return "fault"


def percentile(values, q):
    return sorted(values)[max(0, math.ceil(q * len(values)) - 1)]


def measure(command, cwd, env, logs, tag):
    log = logs / (tag + ".log")
    timing = logs / (tag + ".time")
    start = time.monotonic()
    with log.open("w") as stream:
        proc = subprocess.run(
            ["/usr/bin/time", "-f", "%e %U %S %M", "-o", str(timing),
             *command], cwd=cwd, env=env, stdout=stream,
            stderr=subprocess.STDOUT, check=False)
    wall = time.monotonic() - start
    # GNU time may prepend its own signal/exit status diagnostics.
    elapsed, user, system, rss = timing.read_text().splitlines()[-1].split()
    return {"returncode": proc.returncode, "wall_s": wall,
            "command_wall_s": float(elapsed), "user_s": float(user),
            "system_s": float(system), "max_rss_kib": int(rss),
            "log": log.name}


def resolve_case(root, item):
    source = (root / item["file"]).resolve(strict=True)
    rel = source.relative_to(root / "lean")
    if not re.fullmatch(r"(PEqualNP|CheckerSuite)(/[A-Za-z][A-Za-z0-9_]*)+\.lean",
                        rel.as_posix()):
        raise ValueError(f"invalid module path: {rel}")
    statement = item["statement"]
    if not isinstance(statement, str) or not statement.strip():
        raise ValueError("statement must be the exact nonempty posted Lean term")
    kind = item.get("kind", "check")
    expected = item.get("expected", "accepted")
    if kind not in ("check", "refute") or expected not in ("accepted", "rejected"):
        raise ValueError("invalid kind or expected verdict")
    return source, ".".join(rel.with_suffix("").parts), statement, kind, expected


def run(args):
    root = args.root.resolve(strict=True)
    out = args.out.resolve()
    if out.is_relative_to(root):
        raise ValueError("report directory must be outside the checkout")
    out.mkdir(parents=True, exist_ok=False)
    configs = ["lean/lean-toolchain", "lean/lake-manifest.json",
               "lean/lakefile.toml", "tools/check-lean.mjs",
               "lean/CheckLemma.lean", "tools/build.sh", "tools/bin/lake"]
    identities = {x: digest(root / x) for x in configs}
    revision = capture(["git", "rev-parse", "HEAD"], root)
    status = capture(["git", "status", "--porcelain"], root)
    manifest = json.loads(args.cases.read_text())
    if not isinstance(manifest, list) or not manifest:
        raise ValueError("cases must be a nonempty JSON array")
    cases = [resolve_case(root, item) for item in manifest]
    env = {k: v for k, v in os.environ.items()
           if not re.match(r"^(LAKE($|_)|LEAN_|ELAN_TOOLCHAIN$|PEQUALNP_)", k)}
    env["PATH"] = str(root / "tools/bin") + os.pathsep + env.get("PATH", "")
    env["PEQUALNP_HOME"] = str(out / "queue")
    lean_dir = root / "lean"
    # Official artifacts only. A named experimental distribution needs its own
    # separate benchmark mode and compatibility evidence, not this baseline.
    pin = (lean_dir / "lean-toolchain").read_text().strip()
    version = capture(["elan", "run", pin, "lean", "--version"], lean_dir)
    sysroot = Path(capture(["elan", "run", pin, "lean", "--print-prefix"], lean_dir))
    real_lake = sysroot / "bin/lake"
    env["PEQUALNP_REAL_LAKE"] = str(real_lake)
    meta = {"schema": 1, "revision": revision, "initial_git_status": status,
            "config_sha256": identities, "lean_version": version,
            "lean_binary_sha256": digest(sysroot / "bin/lean"),
            "lake_binary_sha256": digest(real_lake), "platform": platform.platform(),
            "cpu_count": os.cpu_count(), "affinity": sorted(os.sched_getaffinity(0)),
            "mode": args.mode, "repetitions": args.repetitions,
            "cache_note": "First run is not necessarily cold; no caches are evicted.",
            "rss_note": "GNU time maximum RSS is not aggregate concurrent RSS."}
    if Path("/proc/cpuinfo").exists():
        meta["cpu_model"] = next((x.split(":", 1)[1].strip() for x in
            Path("/proc/cpuinfo").read_text().splitlines()
            if x.startswith("model name")), None)
    (out / "metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
    results = []
    with (out / "samples.jsonl").open("w") as journal:
        for i, (source, module, statement, kind, expected) in enumerate(cases):
            stmt = out / f"case-{i}.statement"
            stmt.write_text(statement)
            source_hash, stmt_hash = digest(source), digest(stmt)
            for rep in range(args.repetitions):
                tag = f"case-{i}-rep-{rep}"
                if args.mode == "official":
                    command = ["node", str(root / "tools/check-lean.mjs"),
                               str(source), str(stmt), kind]
                else:
                    # Direct research elaboration, no shared artifact restoration,
                    # no acceptance claim. Bypass queue only in this isolated serial run.
                    command = [str(real_lake), "env", str(sysroot / "bin/lean"),
                               str(source)]
                sample = measure(command, root if args.mode == "official" else lean_dir,
                                 env, out, tag)
                output = (out / sample["log"]).read_text(errors="replace")
                observed = (verdict(sample["returncode"], output)
                            if args.mode == "official" else
                            ("elaborated" if sample["returncode"] == 0 else "elaboration-failed"))
                stable = (digest(source) == source_hash and digest(stmt) == stmt_hash
                          and all(digest(root / x) == h for x, h in identities.items())
                          and capture(["git", "rev-parse", "HEAD"], root) == revision)
                sample.update(case=i, module=module, repetition=rep,
                              source_sha256=source_hash, statement_sha256=stmt_hash,
                              kind=kind, expected=expected, observed=observed,
                              inputs_stable=stable)
                results.append(sample)
                journal.write(json.dumps(sample) + "\n")
                journal.flush()
                print(f"{tag}: {observed} {sample['wall_s']:.3f}s", flush=True)
                if not stable:
                    raise RuntimeError("inputs changed during benchmark")
    summary = []
    for i, (_, module, _, _, _) in enumerate(cases):
        rows = [x for x in results if x["case"] == i]
        matching = [x for x in rows if
                    (x["observed"] == x["expected"] if args.mode == "official"
                     else x["observed"] == "elaborated")]
        times = [x["wall_s"] for x in matching]
        summary.append({"module": module, "samples": len(rows),
                        "matching": len(matching),
                        "median_s": statistics.median(times) if times else None,
                        "p95_s": percentile(times, .95) if times else None,
                        "first_s": rows[0]["wall_s"],
                        "subsequent_median_s": statistics.median(
                            [x["wall_s"] for x in matching if x["repetition"] > 0])
                        if any(x["repetition"] > 0 for x in matching) else None})
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return 0 if all(x["matching"] == x["samples"] for x in summary) else 1


class DriverTests(unittest.TestCase):
    def test_verdict(self):
        self.assertEqual(verdict(0, "MANIFEST {}\nACCEPTED (check): x\n"), "accepted")
        self.assertEqual(verdict(1, "REJECTED (axiom): x\n"), "rejected")
        self.assertEqual(verdict(3, "CHECKER FAULT: x"), "fault")
        self.assertEqual(verdict(0, "ACCEPTED (check): x\ntrailer"), "fault")
        self.assertEqual(verdict(1, "ACCEPTED (check): x"), "fault")

    def test_percentile(self):
        self.assertEqual(percentile([4, 1, 3, 2], .95), 4)
        self.assertEqual(percentile([4, 1, 3, 2], .5), 2)

    def test_measure(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            r = measure(["sh", "-c", "printf 'sample\\n'; exit 7"],
                        p, os.environ.copy(), p, "test")
            self.assertEqual(r["returncode"], 7)
            self.assertEqual((p / r["log"]).read_text(), "sample\n")
            self.assertGreaterEqual(r["wall_s"], 0)
            self.assertGreaterEqual(r["max_rss_kib"], 0)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path.cwd())
    p.add_argument("--cases", type=Path)
    p.add_argument("--out", type=Path)
    p.add_argument("--mode", choices=("official", "elaborate"), default="official")
    p.add_argument("--repetitions", type=int, default=5)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    if args.self_test:
        return 0 if unittest.main(argv=["benchmark"], exit=False).result.wasSuccessful() else 1
    if not args.cases or not args.out or args.repetitions < 1:
        p.error("--cases, --out and positive repetitions required")
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
