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
