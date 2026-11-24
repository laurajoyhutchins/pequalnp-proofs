# Witnessed restrictions and projected exact certificates

Research-only, not a swarm submission. Frontier snapshot 2026-11-24T08:04:03Z; upstream 04e3866162116fb0b95ee6e68c8814874a300e85. Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9); upstream Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.

The complete proof in this directory checks under Lean core alone. EvaluatorMirror copies the relevant upstream evaluator definitions and expresses FanInTwo by a disjunction rather than membership in a Mathlib set. It is deliberately isolated and is not a substitute for the upstream checker. The small candidates under lean/PEqualNP/Outside use only approved upstream imports and reuse L153/L100/L112. Their composition was checked locally with those exact dependency statements as hypotheses; actual upstream elaboration and authoritative acceptance remain distinct.

## Reproduction
Run from this directory with the pinned Lean binary on PATH:

```sh
export LEAN_PATH=.
lean -o WitnessedRestriction.olean WitnessedRestriction.lean
lean -o ProjectedCertificate.olean ProjectedCertificate.lean
lean -o RestrictedTriangle.olean RestrictedTriangle.lean
lean -o EvaluatorMirror.olean EvaluatorMirror.lean
lean -o MirroredEvaluatorProof.olean MirroredEvaluatorProof.lean
python3 experiment.py full
python3 experiment.py augmented
python3 experiment.py
```

WitnessedRestriction.saveGate (namespace CircuitCompression) deletes one gate in the free-constant overapproximation while preserving the projected terminal wire pool. ProjectedCertificate.searchSound proves no legal computation is lost. The residual majority certificate uses rows [1,2,4,3,5,6], masks [0,63,25,42,52], target 56, fuel 3, and 14 first-mask branches. The split certificate took 17.49 s and peak 1846872 KiB in the isolated local Lean process; the combined core split check took 17.45 s and 1867692 KiB. The pre-split check took 24.88 s and 3178288 KiB. These are elapsed Lean process metrics, not separately measured kernel replay.

The independent Python state-set search: full 32 rows, 161890 depth-4 states, 8903950 final binary pairs, excluded; 17 augmented rows, 133375 depth-4 states, 7335625 pairs, excluded; ten extremal rows, 111695 depth-4 states, reachable. The explicit five-gate impostor on the ten rows is NOT((a OR b) AND (x OR y OR z)); it fails at zero. The six-row residual search has 220 second-step branch occurrences and 3866 final distinct-within-branch candidate-mask occurrences. Those counts are not unique global states.

Axiom audit on the local theorem: propext, Classical.choice, Quot.sound only. No new axioms, no native_decide. No upstream submission or live task claim. The posted L-meta-764/765 reductions are already suggested by the task packets; the reusable mathematical contribution is the semantic witnessed-restriction and projected-checking implementation, not a claim of priority for rigid AND elimination.
