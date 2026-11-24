"""Read-only research preflight; never grants a lease or checker verdict."""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path

UPSTREAM = "open-goat/pequalnp-proofs"
LEAN_COMMIT = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
TOOLCHAIN = "leanprover/lean4:v4.36.0"


def frontier(path, now):
    try:
        raw = path.read_bytes()
        index = json.loads(raw)
        stamp = datetime.fromisoformat(index["observed_at"].replace("Z", "+00:00"))
        age = (now - stamp).total_seconds()
        if index["upstream_repository"] != UPSTREAM:
            raise ValueError("upstream identity mismatch")
        if not re.fullmatch(r"[0-9a-f]{40}", index["upstream_sha"]):
            raise ValueError("invalid upstream revision")
        if index["toolchain"] != TOOLCHAIN:
            raise ValueError("toolchain mismatch")
        if not 0 <= age <= 1200:
            raise ValueError("snapshot stale or future-dated")
        if not isinstance(index["gaps"], list):
            raise ValueError("invalid gap list")
        return {"state": "fresh_public_snapshot", "age_seconds": age,
                "sha256": hashlib.sha256(raw).hexdigest(),
                "upstream_sha": index["upstream_sha"], "gap_count": len(index["gaps"])}
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
        return {"state": "unavailable", "reason": str(exc)}


def run(argv, **kwargs):
    return subprocess.run(argv, capture_output=True, text=True, timeout=30,
                          check=True, **kwargs).stdout.strip()


def lean_probe(bin_dir):
    try:
        lean = str((bin_dir / "lean").resolve())
        lake = str((bin_dir / "lake").resolve())
        if run([lean, "--githash"]) != LEAN_COMMIT:
            raise ValueError("Lean commit mismatch")
        version = run([lean, "--version"])
        lake_version = run([lake, "--version"])
        with tempfile.TemporaryDirectory() as work:
            p = Path(work) / "Probe.lean"
            p.write_text("import Lean\nexample (n : Nat) : n + 0 = n := Nat.add_zero n\n")
            run([lean, str(p)], cwd=work)
        return {"state": "core_checked", "version": version, "lake": lake_version,
                "commit": LEAN_COMMIT}
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        return {"state": "unavailable", "reason": str(exc)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", required=True, type=Path)
    parser.add_argument("--lean-bin", required=True, type=Path)
    args = parser.parse_args()
    now = datetime.now(timezone.utc)
    report = {"schema": "research-preflight/1", "observed_at": now.isoformat(),
              "frontier": frontier(args.frontier, now), "lean": lean_probe(args.lean_bin),
              "mathlib": "not_verified", "checker": "not_run", "lease": "unconfirmed",
              "task_specific_work_authorized": False,
              "next": "Confirm live desk ownership, current statement and pinned dependencies before task-specific work."}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
