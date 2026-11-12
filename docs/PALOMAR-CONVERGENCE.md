# Theorem 1.6: whole-line functional Busemann limits

Configuration: [`palomar/principal/busemann-convergence.json`](../palomar/principal/busemann-convergence.json). The main target is `DLQG1.Palomar.Principal.busemann_convergence`, covering **Theorem 1.6** (`thm-busemann-conv`). The configuration additionally compares the Theorem1.4 characterization as a proved prerequisite, not as another new catalogue item.

The Mathlib-only [Challenge](../Palomar/Principal/BusemannConvergence/Challenge.lean) contains the actual uniform-code/KMSW/M0/Busemann definitions, the conditional choice with its zero fallback, ordinary cadlag half/whole-line carriers, the finite-window J1 infimum over increasing endpoint-fixing time changes, weighted cutoff-window distance, its topology and Borel sigma algebra. The [scalar support](../Palomar/Principal/Support/BusemannIdentified.lean) proves equality of the complete chooser predicates and hence both actual scalar functions for every code; it does not assume global uniqueness. The [path support](../Palomar/Principal/Support/BusemannPaths.lean) proves the precise source metric/Borel, floor-path and limiting-law transports.

For positive integer index n+1 the rescaled paths retain exponents -3/2 for LDP and -3/4 for SDP, with floor((n+1)t). The limit uses X-plus at nonnegative times and the left limit Y((-t)-) at negative times, both starting at zero. Independent half laws are combined by the actual product measure. The full partition characteristic functions specify the strict stable laws, correct signs, indices2/3 and4/3, and shared positive parameters. Both a.e. geometric object identifications and both full weak `Tendsto` statements on the whole-line local J1 path space remain. Finite-dimensional convergence does not replace functional convergence.

## Exact compared scope

There are forty-three selected theorem declarations: thirty explicit terminal Challenge holes (the inherited fourteen Busemann construction/characterization targets, eleven metric/glue facts, four floor/probability/measurability facts and the Theorem1.6 main target), and thirteen already-proved constructor certificates. All actual Solution proofs are complete. Every reached data definition is compared; `definition_names=[]`. The interleaved target order is frozen exactly in the manifest/config/probe and contains precisely this complete set.

- `DirectedDistances.KMSW.act_lt_nextEdge` — compared construction/characterization prerequisite.
- `DirectedDistances.KMSW.stageRotation_UL_bound` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.kmswInfRot_existsUnique` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_equivalence` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneVertexRel_equivalence` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_west` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_east` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.eventualValue_existsUnique` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.value_rel` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneRot_comp_inv` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.wholePlaneRotInv_comp_rot` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.eventualPresence_rel` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.KMSW.m0CutData_nonempty` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Principal.busemann` — compared construction/characterization prerequisite.
- `DirectedDistances.KMSW.kmswCodeStep._proof_1` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.step._proof_5` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.step._proof_6` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.step._proof_7` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.step._proof_9` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.step._proof_10` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.allocation._proof_13` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.allocation._proof_4` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.allocation._proof_6` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.allocation._proof_8` — proved constructor certificate.
- `DirectedDistances.KMSW.StageRotation.allocation._proof_11` — proved constructor certificate.
- `DirectedDistances.KMSW.boundaryHitTime._proof_2` — proved constructor certificate.
- `DirectedDistances.KMSW.boundaryHitTime._proof_4` — proved constructor certificate.
- `DLQG1.Palomar.Model.Probability.cutoffWindow_isCadlag` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.j1LocalDist_self` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.j1LocalDist_symm` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.j1LocalDist_triangle` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.j1LocalDist_eq_zero_iff` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineJ1WindowPath_cadlag` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineLocalJ1Distance_self` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineLocalJ1Distance_symm` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineLocalJ1Distance_triangle` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineLocalJ1Distance_eq_zero_iff` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.wholeLineGlue_isCadlag` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.Probability.floorStep_isCadlag` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure_isProbabilityMeasure` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.PaperProofs.Section1.aemeasurable_identifiedLDPScalingPath` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Model.PaperProofs.Section1.aemeasurable_identifiedSDPScalingPath` — compared construction/characterization prerequisite.
- `DLQG1.Palomar.Principal.busemann_convergence` — numbered Theorem1.6 main.

## Validation

Normal sandboxed source Comparator, NanoDa and default Lean replay passed in308.559seconds, peak5,055,364KiB process-treeRSS. All forty-three axiom probes contain only the three permitted foundational axioms. The [local hash-bound receipt](../verification/PALOMAR-CONVERGENCE-RESULTS.json) records exact inputs. Independent statement/definition/transport review passed before Challenge generation. An initial data mismatch was resolved by restoring the checked Source declaration order; no definition was skipped or assumed.

Reproduce with `lake comparator --config palomar/principal/busemann-convergence.json` and `lake env lean verification/PalomarBusemannConvergenceAxioms.lean`, or `bash scripts/verify-palomar.sh` for all implemented configurations. The actual configuration still requires complete official preflight at its exact public commit. Earlier reports do not certify a later commit. No intake or registration has occurred.
