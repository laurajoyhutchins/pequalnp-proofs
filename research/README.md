# Research workstation
Research branch: research/workstation. Fork main tracks upstream without research modifications. This branch incorporates the existing pinned checker and Petersen graph experiments; those experiments are not claimed as accepted upstream gaps.

## Quick start
- Read the live strategy and desk rules. Check the current upstream head and pinned environment. Use a separate checkout/worktree per worker. Never run lake update.
- For a frontier snapshot, create JSON {"gaps":[{"id":"A","status":"open","depends_on":[]},{"id":"B","status":"blocked","depends_on":["A"]}]} from documented dependency information. Preserve the original snapshot separately. Use python3 tools/research/frontier.py frontier snapshot.json. Only explicit known dependency edges count; the result is a heuristic, not official priorities or a claim allocator.
- Use python3 tools/research/frontier.py index lean/PEqualNP to retrieve textual candidate declarations with paths and line numbers. It is not an elaborated Lean index. Verify candidates against the actual allowed import closure.
- For an external proof: check out a fresh upstream SHA in an isolated credential-free directory, install its pinned Lean and use lake exe cache get. Keep the checkout warm for multiple independent candidates. Invoke the script in this research checkout with arguments BASE SNAPSHOT GAP FILE CANDIDATE RECEIPTS; see its usage. The candidate and receipts must be outside BASE. The wrapper does not claim or submit anything. Use the official submission protocol only after the exact checked candidate is still eligible. The authoritative workflow runs on upstream.
- Research CI: the upstream checker verifies independently stored research theorem texts. It is not a submission checker for research-only modules.

## Research handoff
Record gap ID and exact statement or source pointer, allowed imports, upstream SHA, mathematical reduction, smallest missing lemma, failed methods, reproducible counterexamples, candidate SHA, exact checker verdict, next action. Keep live lease identifiers in local private state and only renew while active. Coordinate the shared account with a private SHA-checked record. A public note is appropriate only for non-sensitive reusable mathematics.

## Evidence boundaries
A textual dependency graph is incomplete when data is unavailable. Finite experiments do not establish a universal theorem. A source build does not check posted statement identity or axioms. Local guard/checker acceptance does not guarantee authoritative acceptance. A lease expiring or a gap closing invalidates a planned submission. No unattended desk automation is enabled by this branch.

## Fast diagnostic mode

For local iteration in an isolated pinned checkout, run `bash tools/research/diagnose.sh lean/PEqualNP/Research/Name.lean /absolute/fresh/receipts` from its root (or invoke the script from the research checkout). For a desk candidate, use the existing guarded wrapper with `--diagnostic` before BASE. It stages only the permitted file, retains the gap/import/closure checks, and delegates to the target-only diagnostic. Both paths produce diagnostic labels, not checker acceptance. Use a fresh external receipt directory for each attempt; retain compatible same-checkout Lake outputs. The diagnostic does not compare theorem types, audit axioms, or replay the kernel independently.

For GitHub-hosted diagnostics, create a branch under `research/diagnostic-<task>` from the workstation, add or edit the candidate file and put its repository-relative Lean path on a line in `research/diagnostic-targets.txt`. The existing workflow installs the exact pins, builds only those targets, records logs and skips memory provisioning, controls, and full checker. A resource-heavy candidate may need the full verification environment. For full verification use a regular workstation research branch with independent statement files or the guarded wrapper without `--diagnostic`; the original checker remains unchanged. Documentation-only pushes no longer trigger this workflow. A GitHub runner is ephemeral, so hosted runs still have bootstrap cost; warm sub-30-second latency is a benchmark target, not a guarantee.

## Warm diagnostic state

An isolated persistent checkout can opt into the original upstream `tools/build.sh` artifact cache by setting `PNP_DIAGNOSTIC_CACHE_HOME` to an absolute directory outside the checkout and receipts. With no flag the diagnostic uses same-tree incremental outputs only. Hosted diagnostic branches now restore a branch-scoped, exact-pin Lake artifact cache and save at most 1 GiB. Cache reuse is advisory, not acceptance; full checker runs do not restore or read it. Keep one checkout per active worker; never share a mutable checkout. GitHub cache visibility is branch scoped, not a global warm runner. The Mathlib upstream download still occurs per hosted job. The warm smoke branch measures first build, unchanged rebuild, actual source edit, and cache restoration after dropping project outputs. No persistent host has been provisioned.

## Full checker modes and submission quality

The local wrapper defaults to ordinary proof mode. On a fresh isolated checkout of a current upstream revision with the mode-aware guard, use:

```sh
bash tools/research/check-candidate.sh --kind check BASE SNAPSHOT GAP FILE CANDIDATE RECEIPTS
bash tools/research/check-candidate.sh --kind refute BASE SNAPSHOT GAP FILE CANDIDATE RECEIPTS
bash tools/research/check-candidate.sh --kind reduce BASE SNAPSHOT GAP FILE CANDIDATE RECEIPTS
```

The upstream desk must authorize the selected mode. Reduction files have their prescribed R_ name; ordinary proof and refutation files have their prescribed L_ name. The guard's mode must match the request, and the actual checker verdict must name the same mode. Use `--diagnostic` only for iteration, not export. Older upstream guards that cannot validate the mode fail closed. Contract tests mock the command boundary and do not verify mathematical proofs.

The hosted ordinary-proof verification/export pipeline is separate: it still pins the upstream sandbox workflow identity and accepts ordinary proof candidates only. If the upstream workflow changes, review the sandbox changes before adapting that pipeline; never relax the identity check just to get a run. A successful local reduction check is necessary but not sufficient for export: demonstrate a nontrivial solved child or case and reduced residual difficulty. A cross-fork PR needs authorized upstream access; the connector's HTTP 403 is not a checker verdict and no proxy may be used to evade it. See AGENTS.md for the quality ratchet.
