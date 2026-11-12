# Theorem 1.11: finite Boltzmann distances

Configuration: [`palomar/principal/boltzmann-distances.json`](../palomar/principal/boltzmann-distances.json). This intended entry covers **Theorem 1.11** (`thm-boltzmann-ldp`). Definitions 1.9 (`def-bipolar-bdy`) and 1.10 (`def-boltzmann-right`) supply its actual boundary and marked-law definitions; they are not separately registered by this configuration. No intake or registration has occurred. The complete [90-item correspondence](../CORRESPONDENCE.md) remains unchanged.

The [Challenge](../Palomar/Principal/BoltzmannDistances/Challenge.lean) imports Mathlib alone and defines the finite dart/rotation/face map, bipolar orientation, ordered boundary paths, boundary-preserving isomorphism quotient, marked space and normalized atomic law. The mark is on the **left** boundary, including its endpoints; the fixed parameter is the **right** boundary length. Each marked n-edge class has weight 3^(-n) before normalization. This is not the unmarked law followed by a uniform mark. Parallel edges retain their identities, and shared boundaries and the one-edge map remain allowed.

For each real delta in (0,1), one A(delta)>1 works for every integer r>=1. In a single event of probability at least 1-delta, source-to-sink LDP lies between A^(-1)r^(3/2) and Ar^(3/2), source-to-sink SDP is at most Ar^(3/4), and some right-boundary vertex has SDP from the source at least A^(-1)r^(3/4). All three clauses and the shared constant are retained. LDP uses the attained finite maximum on the finite acyclic domain; SDP uses the infimum of present-dart path lengths with infinity when unreachable.

The [Solution](../Palomar/Principal/BoltzmannDistances/Solution.lean) applies the accepted `DirectedDistances.Paper.Section1.thm_boltzmann_ldp` without any new premise. The exact compared declarations are:

- `DLQG1.Palomar.Principal.boltzmann_distances`
- `DirectedDistances.PaperProofs.Section7.rightBoundaryVertex._proof_2`
- `DirectedDistances.PlanarMap.SimpleDirectedDartPath._proof_8`
- `DirectedDistances.PlanarMap.SimpleDirectedDartPath._proof_6`
- `DirectedDistances.PlanarMap.SimpleDirectedDartPath._proof_4`
- `DirectedDistances.PlanarMap.SimpleDirectedDartPath._proof_2`
- `DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase`

Only `DLQG1.Palomar.Principal.boltzmann_distances` represents a numbered paper result here. The other six are already-proved supporting declarations: one right-boundary index bound, four simple-path vertex-index bounds, and membership in the finite source-sink path-length set. They are explicit comparison targets because their proofs have different presentations in the standalone environment; their complete types and real Solution proofs are checked. Their Challenge proofs remain present. The sole deliberate hole is the main theorem. `definition_names` is empty: **every reached definition body is compared**. Generated names are tied to this pinned snapshot and must be re-audited after relevant edits.

Normal sandboxed source-build Comparator passed, including NanoDa and default Lean replay, in 309.293 seconds with aggregate peak RSS 5,126,044 KiB. All seven Solution axiom probes use only propext, Classical.choice and Quot.sound. Separate mathematical-fidelity review found no added assumption, omitted clause or object substitution. See the [hash-bound local receipt](../verification/PALOMAR-BOLTZMANN-RESULTS.json). This is a local result; an official full preflight on an exact public commit is a separate required gate.

Reproduce with `lake comparator --config palomar/principal/boltzmann-distances.json`, then run `lake env lean verification/PalomarBoltzmannDistancesAxioms.lean`. `bash scripts/verify-palomar.sh` also runs the other implemented configurations and exact integrity controls. Preserve the pinned toolchain and dependency manifest. Official runs use the pinned manual workflow, full mode, standard profile, this configuration path and a twelve-character lowercase-alphanumeric request ID. Intake and registration need separate human authorization.
