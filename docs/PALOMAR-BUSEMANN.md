# Theorem 1.4: geometric Busemann functions

Configuration: [`palomar/principal/busemann.json`](../palomar/principal/busemann.json). This entry covers **Theorem 1.4** (`thm-busemann`), with its actual construction obligations; it does not register the complete 90-item catalogue.

The Mathlib-only [Challenge](../Palomar/Principal/Busemann/Challenge.lean) contains the actual two-sided uniform three-step code law, finite sewing recursion and whole-plane quotient, rotations and face successors, missing/present incidence, extremal rays, the M0 cut and its boundary vertex indexing, directed paths and extended SDP/LDP, and the full normalized Busemann characterization. It preserves one common probability-one scope, both modes, every pair of boundary indices and every injective sequence of common reachable vertices. Finite distance witnesses remain explicit before subtraction. No abstract random map or assumed Busemann object replaces these constructions.

The [Solution](../Palomar/Principal/Busemann/Solution.lean) proves transport of the constructed geometry, ordered root, boundaries, paths, distances and chosen vertices to the accepted formalization. The [source support](../Palomar/Principal/Support/BusemannSource.lean) supplies proved construction facts. It is imported only by Solutions, never by Challenges or the production library.

## Exact compared declarations

Only `DLQG1.Palomar.Principal.busemann` is the numbered main result. The first thirteen declarations below prove existence/well-definedness for its literal construction; together with the main result they have fourteen deliberate terminal Challenge proof holes. The last thirteen are already-proved public typing/constructor certificates; their proofs remain present in the Challenge. All twenty-seven types and actual Solution proofs are checked. None is a skipped data definition, and `definition_names=[]`.

- `DirectedDistances.KMSW.act_lt_nextEdge` — construction obligation.
- `DirectedDistances.KMSW.stageRotation_UL_bound` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.kmswInfRot_existsUnique` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_equivalence` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneVertexRel_equivalence` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_west` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneEdgeRel_east` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.eventualValue_existsUnique` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.value_rel` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneRot_comp_inv` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.wholePlaneRotInv_comp_rot` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.eventualPresence_rel` — construction obligation.
- `DLQG1.Palomar.Model.KMSW.m0CutData_nonempty` — construction obligation.
- `DLQG1.Palomar.Principal.busemann` — numbered main result.
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

## Validation and compiler behavior

Normal sandboxed source Comparator, NanoDa and default Lean replay passed in 170.822 seconds, with peak process-tree RSS 4,274,408 KiB. All twenty-seven axiom probes contain only the three permitted foundational axioms. Independent source/main review and a separate thirteen-certificate audit passed. The thirteen-certificate exception is confined to this exact path and exact name set; all other existing auxiliary budgets remain unchanged. The [portable receipt](../verification/PALOMAR-BUSEMANN-RESULTS.json) binds the exact source hashes.

The local `bootstrap.genMatcherCode=false` setting is confined to the new Challenge/Solution construction section. In the pinned [Lean matcher implementation](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/Lean/Meta/Match/Match.lean), it controls auxiliary executable generation and the matcher-cache key. Declaration creation and checking still occur; matcher logical bodies are exported. This prevents imported implementation matchers from changing the literal compared body. The production options, toolchain, axiom policy, ordinary source builds and both kernel replays are preserved.

Reproduce with `lake comparator --config palomar/principal/busemann.json` and `lake env lean verification/PalomarBusemannAxioms.lean`, or run all implemented configurations with `bash scripts/verify-palomar.sh`. This configuration still needs complete official preflight at its exact public commit. Historical PASS reports for other configurations do not certify a new commit. No intake or registration has occurred.
