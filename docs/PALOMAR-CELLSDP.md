# Theorem 1.13: KMSW cell shortest paths

Configuration: [`palomar/principal/cell-sdp.json`](../palomar/principal/cell-sdp.json). This intended entry covers **Theorem 1.13** (`thm-cell-sdp`), not every catalogue item. The complete [90-item correspondence](../CORRESPONDENCE.md) is preserved. No entry has been registered.

The [Challenge](../Palomar/Principal/CellSDP/Challenge.lean) imports Mathlib alone and defines the actual KMSW state/step procedure, edge identities and present/missing status, the directed quiver and distances, and the actual one-sided Markov/IID code law. Time zero is the sampler's dummy code; increments use omega(i+1), which is the actual uniform iid sequence. No arbitrary law, map, recurrence or existence hypothesis replaces the construction. The [Solution](../Palomar/Principal/CellSDP/Solution.lean) applies the accepted source theorem directly.

One A(delta)>1 works for every n>=1 and all three clauses jointly: each lower-boundary vertex reaches some upper-boundary vertex within An^(3/8); each upper vertex is similarly reached from some lower vertex; and a lower-right vertex to the right of the ordered root has distance from x0 at least A^(-1)n^(3/8). Boundaries are actual LL/LR/UL/UR edge endpoint sets, with the original missing tags. The boundary-hit witness is existential inside the event, not an added assumption. Upper bounds retain ENat infinity; the lower witness's LR reachability proves finiteness before toNat is used.

Exact compared declarations:

- `DLQG1.Palomar.Principal.cell_sdp`
- `DirectedDistances.KMSW.kmswCodeStep._proof_1`
- `DirectedDistances.RandomWalk.iidCodeMeasure._proof_4`
- `DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure`
- `DirectedDistances.KMSW.boundaryHitTime._proof_4`
- `DirectedDistances.KMSW.boundaryHitTime._proof_2`

Only the first declaration is the numbered result. The remaining targets are already-proved code-typing/normalization helpers, plus the two signed integer boundary-hit index bounds. Their full types and actual Solution proofs are checked. The Challenge has one deliberate terminal theorem hole; all auxiliary proofs remain present. `definition_names=[]` means every reached definition body is compared. Generated names are snapshot-specific and require re-audit after refactoring.

Normal sandboxed source Comparator, NanoDa and default Lean replay passed in 299.481 seconds; all 6 axiom probes use only propext, Classical.choice and Quot.sound. See the [hash-bound local receipt](../verification/PALOMAR-CELLSDP-RESULTS.json). This is not an official preflight report.

Reproduce with `lake comparator --config palomar/principal/cell-sdp.json` and `lake env lean verification/PalomarCellSDPAxioms.lean`; the complete implemented selection is checked by `bash scripts/verify-palomar.sh`. The pinned manual official workflow must pass for each intended configuration on its exact public commit before submission. Intake and registration need separate human authorization.
