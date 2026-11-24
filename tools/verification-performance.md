# Verification performance baseline (research only)

This branch adds an opt-in measurement driver, not a replacement checker. Do not submit these files upstream with a proof.

Prerequisites: Linux, Python 3.10+, GNU time, Node 20+, elan, the committed Lean pin and prebuilt pinned Mathlib. Use a dedicated disposable checkout and trusted candidates. The official checker executes candidate Lean code; isolate it as required by upstream. Do not run lake update.

## Driver checks

    python3 tools/bench-verification.py --self-test

## Corpus

Provide a JSON array, one object per candidate. Each object contains the exact posted statement (not the theorem declaration or a statement reconstructed from the candidate), the repository-relative file, kind (check or refute) and expected verdict (accepted or rejected). Archive the public task snapshot used to construct it. Use actual accepted circuit, algebra, arithmetic and tactic-heavy proofs, and known rejection controls in a separate disposable tree. Example schema (illustrative, not an actual swarm task):

    [{"file":"lean/CheckerSuite/Example.lean","statement":"True","kind":"check","expected":"accepted"}]

The files must exist before benchmarking. A rejected control may elaborate successfully, so elaboration success is not a prediction of acceptance.

## Run

From the repository root:

    python3 tools/bench-verification.py --cases /tmp/corpus.json --out /tmp/pnp-stock-official --mode official --repetitions 5
    python3 tools/bench-verification.py --cases /tmp/corpus.json --out /tmp/pnp-stock-elaboration --mode elaborate --repetitions 5

Report directories must be new and outside the checkout. The driver uses the existing machine-wide queue; for repeatable latency measurements avoid unrelated builds. Set up the same dependency closure before the elaboration comparison. The first invocation is not necessarily a cold start. For a true clean-build comparison use a separately prepared checkout with the same pinned prebuilt dependencies and empty project build outputs; do not evict global system caches.

Reports include raw stdout/stderr, GNU time CPU and maximum RSS, monotonic wall time, exit codes, result classification, source/statement and configuration hashes, executable hashes, revision, CPU information, and per-case median and nearest-rank p95. A mismatch exits nonzero. Faults are not mathematical rejections. GNU time RSS is not a simultaneous aggregate memory measurement. Dependency artifact identity and host isolation remain external experimental prerequisites; the receipt is not a cryptographic proof of acceptance.

## Next measurements

1. Collect the serial stock baseline on real accepted and rejected obligations, keeping raw reports.
2. Measure phase times (queue wait, environment import, elaboration, kernel replay, axiom traversal) in a separate instrumented research build, not by changing the official checker.
3. Compare a warm LSP worker with repeated edits of the same proof; do not compare it to full acceptance as if equivalent.
4. Build an independently named native toolchain at the exact pinned Lean revision; test CPU-specific optimization, LTO, then PGO on a separate training corpus. Rebuild dependency artifacts when ABI compatibility is uncertain.
5. Compare five-worker throughput, peak aggregate RSS and p95 latency on the same host and held-out corpus. Require the unmodified checker for final acceptance.

No performance gain is claimed before measurements.
