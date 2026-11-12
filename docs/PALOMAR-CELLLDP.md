# Theorem 1.12: KMSW cell longest paths

Configuration: [`palomar/principal/cell-ldp.json`](../palomar/principal/cell-ldp.json). This intended entry covers **Theorem 1.12** (`thm-cell-ldp`), not every catalogue item. The complete [90-item correspondence](../CORRESPONDENCE.md) is preserved. No entry has been registered.

The [Challenge](../Palomar/Principal/CellLDP/Challenge.lean) imports Mathlib alone and defines the actual KMSW state/step procedure, edge identities and present/missing status, the directed quiver and distances, and the actual one-sided Markov/IID code law. Time zero is the sampler's dummy code; increments use omega(i+1), which is the actual uniform iid sequence. No arbitrary law, map, recurrence or existence hypothesis replaces the construction. The [Solution](../Palomar/Principal/CellLDP/Solution.lean) applies the accepted source theorem directly.

One A(delta)>1 works for every n>=1. A single event asserts existence of a path of length at least A^(-1)n^(3/4), and LDP at most An^(3/4) for every allocated vertex pair. StagePresentVertex has an infinite ambient ID carrier; the upper quantifiers explicitly restrict allocated IDs. The positive lower bound excludes empty ghost paths. Actual finite-map/path transport and acyclicity give boundedness and attainment, so the finite WithBot-Nat supremum agrees with the paper's LDP, with bottom when unreachable.

Exact compared declarations:

- `DLQG1.Palomar.Principal.cell_ldp`
- `DirectedDistances.KMSW.kmswCodeStep._proof_1`
- `DirectedDistances.RandomWalk.iidCodeMeasure._proof_4`
- `DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure`

Only the first declaration is the numbered result. The remaining targets are already-proved code-typing/normalization helpers. Their full types and actual Solution proofs are checked. The Challenge has one deliberate terminal theorem hole; all auxiliary proofs remain present. `definition_names=[]` means every reached definition body is compared. Generated names are snapshot-specific and require re-audit after refactoring.

Normal sandboxed source Comparator, NanoDa and default Lean replay passed in 284.454 seconds; all 4 axiom probes use only propext, Classical.choice and Quot.sound. See the [hash-bound local receipt](../verification/PALOMAR-CELLLDP-RESULTS.json). This is not an official preflight report.

Reproduce with `lake comparator --config palomar/principal/cell-ldp.json` and `lake env lean verification/PalomarCellLDPAxioms.lean`; the complete implemented selection is checked by `bash scripts/verify-palomar.sh`. The pinned manual official workflow must pass for each intended configuration on its exact public commit before submission. Intake and registration need separate human authorization.
