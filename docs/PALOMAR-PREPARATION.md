# Palomar preparation

This is preparation for optional Palomar entries, starting from public v0.1.0
(`e1cfdce8ee7882a728df85747040e6969544fcb8`). No Palomar intake,
or registration has been initiated. Reviewed preparation changes have been published; no entry has been registered. The complete
[90-entry correspondence](../CORRESPONDENCE.md) and its 97 primary exports remain
the manuscript catalogue; a Comparator configuration is a separate, smaller
selection. One configuration corresponds to one potential Palomar entry.

## Pinned requirements

- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md):
  `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`.
- [Submission guide](https://palomar-registry.org/how-to-submit) and
  [agent protocol](https://submit.palomar-registry.org/llms.txt).
- [Official verification pipeline](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7):
  `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
- [Metadata format and schema](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e):
  v0.4 at `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

A Challenge may import only the permitted core/Mathlib closure (or qualified
Tau Ceti/CSLib dependencies), never this project's implementation modules.
Project-specific mathematical notions must be defined faithfully on the
reviewed Challenge surface. Unspecified objects with assumed desired properties
do not replace their ordinary definitions or proved identifications. A Challenge
has hard limits of 1,000 physical lines and 100 KiB; 300 lines and 32 KiB are the
preferred surface. Every submitted Lean source also requires a module header
and a 10,000-line limit. The theorem selection must be nonempty, with matching
Challenge/Solution names and types and only the permitted foundational axioms.

## Implemented pilot and selected Appendix preparation

The implemented pilot is
`palomar/comparator-pilot.json`, comparing
`DLQG1.Palomar.tauberian_below_one` between
`Palomar.Pilot.Challenge` and `Palomar.Pilot.Solution`.
It is the full natural-valued current-paper Lemma A.2, supplied by
`DirectedDistances.Paper.AppendixA.tauberian`: measurable X on a probability
space, 0 < nu < 1, nonzero real coefficient, the two-sided characteristic-function
expansion, the negative coefficient conclusion, and the exact positive
Gamma/cosine tail constant. The strict upper-tail event is retained.
No custom definitions or extra assumptions are used.
The standalone real-valued generalization is not advertised as the numbered
paper lemma.

The ten Challenge files deliberately contain 105 theorem proof holes: one
optional pilot, six Appendix, fourteen each for Theorems 1.4, 1.7 and 1.8,
thirty for Theorem 1.6, one main-result hole each for Theorems 1.11, 1.12 and
1.13, and 23 for Proposition 5.9. Its 18 constructor certificates remain
proved and separately compared. Production proofs and Solutions contain zero;
there are no definition holes. The pinned v0.4 metadata convention excludes
deliberate Challenge holes from `status.sorry_count`; separate Challenge and
total-tree counts record all 105. Integrity checks enforce the exact Challenge
allowlist.

The pilot passed sandboxed Comparator, NanoDa and Lean kernel checks, and a
separate source-fidelity review found no blocker. Local evidence is written to
`.lake/palomar-evidence/pilot-comparator.log`; that generated file is not a
published Palomar report.

A separate root `comparator.json` is implemented for all six numbered
Appendix lemmas. Its intended compared names and exact existing sources are:

| Paper | New compared name in DLQG1.Palomar.AppendixA | Existing export in DirectedDistances.Paper.AppendixA |
|---|---|---|
| A.1 | `holomorphic_asymptotic` | `holomorphic_asymptotic` |
| A.2 | `tauberian` | `tauberian` |
| A.3 | `tauberian_above_one` | `tauberian_above_one` |
| A.4 | `positive_sine` | `positive_sine` |
| A.5 | `abel` | `abel` |
| A.6 | `riemann` | `riemann` |

These signatures use Mathlib notions rather than project-specific geometric
definitions. The combined six-lemma configuration separately **passed local sandboxed
Comparator, NanoDa and Lean kernel checks** in 1 minute 40.49 seconds
(maximum RSS 729,244 KiB, exit 0). A separate source-fidelity review found no
blocker for all six statements. Its runtime log is
`.lake/palomar-evidence/appendix-comparator.log`. See the portable
[comparison receipts](../verification/PALOMAR-RESULTS.json). Its Mathlib-only Challenge has 142 physical
lines and 7,254 bytes; `definition_names` is empty. A.3 likewise
uses the natural-valued paper statement, including its sign, constant and
tail exponent. General real-valued companion theorems are outside this selection.

## Principal entries and status

Eight principal entries (Theorems 1.4, 1.6, 1.7, 1.8, 1.11, 1.12, 1.13 and
Proposition 5.9) have locally validated standalone configurations. The seven
Theorem entries retain their independent fidelity reviews; Proposition 5.9
also has a separately documented source scope and normal Comparator/kernel
receipt. These local results do not substitute for final official preflight.
Proposition 5.16 remains pending its standalone Challenge and local checks.
Each principal configuration is a separate entry; no entry has been registered.
The existing source exports are under `DirectedDistances.Paper`. The new names
are under `DLQG1.Palomar.Principal`.

| Paper | Proposed config | Proposed compared name | Exact existing export | Required standalone mathematical surface | Current status |
|---|---|---|---|---|---|
| 1.4 | `palomar/principal/busemann.json` | `busemann` | `Section1.thm_busemann` | Whole-plane IID code law, KMSW map carriers and rotation/boundary witnesses, actual m0 seam cut and ordered root, missing-edge incidence, distance transport, reachable-distance finiteness, and both unique identified Busemann characterizations. | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.6 | `palomar/principal/busemann-convergence.json` | `busemann_convergence` | `Section1.thm_busemann_conv` | The actual identified Busemann objects and their probability-one geometric identification, local-Skorokhod cadlag space, scaling laws, stable half/process laws, product law and whole-line glue with left-limit reversal. Both functional convergence claims must remain. | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.7 | `palomar/principal/busemann-increments.json` | `busemann_increments` | `Section1.thm_busemann_property` | Actual LDP/SDP Busemann functions and identification; both independent increment families, side-specific identical-distribution clauses, signs and symmetry. Arbitrary increments cannot replace these objects. | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.8 | `palomar/principal/busemann-tails.json` | `busemann_tails` | `Section1.thm_busemann_tail` | Actual identified functions and their geometric identification; both paired c/2c tail constants and exponents, plus SDP integrability and zero mean. | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.11 | `palomar/principal/boltzmann-distances.json` | `boltzmann_distances` | `Section1.thm_boltzmann_ldp` | Fixed right-boundary length and LEFT-vertex-marked Boltzmann space and law, plane-map isoclasses with edge identity, directed LDP/SDP and left-boundary vertex marking. Preserve one A(delta) for every size and all three bounds. | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.12 | `palomar/principal/cell-ldp.json` | `cell_ldp` | `Section1.thm_cell_ldp` | IID code law and exact KMSW finite stage, allocated/present vertices, directed paths and longest-path supremum, retaining existence and uniform upper bound with one A(delta). | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 1.13 | `palomar/principal/cell-sdp.json` | `cell_sdp` | `Section1.thm_cell_sdp` | The same finite-stage construction, ordered LL/LR/UL/UR boundary incidence, shortest-path semantics and boundary-hit witnesses; retain all three quantified clauses and the shared A(delta). | Local Comparator, NanoDa, Lean and fidelity review PASS; official final-commit run pending. |
| 5.9 | `palomar/principal/half-plane-reflection.json` | `half_plane_reflection` | `Section5.prop_uihbot_sym` | Geometric rooted-map quotient and Borel structure, the actual half-plane law and geometric mirror, including the same missing geometric root with reversed ordered endpoints. | Local normal source Comparator, NanoDa, Lean default kernel and all 41 axiom probes PASS; official final-commit run pending. |
| 5.16 | `palomar/principal/disk-local-limit.json` | `disk_local_limit` | `Section5.prop_disk_bs_conv` | Geometric rooted-map quotient/local topology and probability-law convergence, actual uniform finite class with independent mark and partial-map observable, and actual half-plane law. Preserve every admissibility, congruence and uniform square-root bound. | Pending standalone Challenge and local checks. |

Theorem 1.11 passed normal source Comparator, Lean/NanoDa, axiom checks and
independent fidelity review; its [exact coverage](PALOMAR-BOLTZMANN-DISTANCES.md)
and [local receipt](../verification/PALOMAR-BOLTZMANN-RESULTS.json) are separate
from official preflight. Theorems 1.4, 1.6, 1.7 and 1.8 also have their own
coverage records and hash-bound local receipts. Proposition 5.9 also has its
separate coverage record and local receipt. Proposition 5.16 is the only
principal statement still pending a standalone Challenge and local checks. No
failure of its existing Lean proof is asserted.
No global equality of the broad implementation map classes and the restricted
source views is claimed. The existing source-domain membership and sampling-law
transport must remain available when those actual objects are presented.

## Reusable mathematical definitions for remaining entries

The repeated definition families are: (1) the actual IID walk and KMSW map,
plane incidence and missing-edge/ordered-root data; (2) directed paths,
extended LDP/SDP and the characterized Busemann functions; (3) geometric rooted
map quotients, local topology and reflected marks; and (4) cadlag local-Skorokhod
spaces, stable process laws and right-continuous whole-line gluing. The table
identifies which entries share each family. Their existing implementation and
identification lemmas can be reused in Solutions.

A common project-specific definitions module cannot be imported by a Challenge
under the current rule. Any source-level reuse on that surface must place the
actual audited definitions within each standalone Challenge (or use an already
permitted upstream definition), respecting the size cap. The finite Challenges have 498/252/324 lines for Theorems 1.11/1.12/1.13;
the two Proposition Challenges remain in preparation. See the coverage records for [1.11](PALOMAR-BOLTZMANN-DISTANCES.md),
[1.12](PALOMAR-CELLLDP.md) and [1.13](PALOMAR-CELLSDP.md).

## Metadata and source scope

`formalization.yaml` describes the substantive development, not a thin wrapper.
It retains human formalization authorship and responsibility separately from
paper authorship and discloses material AI assistance. Novelty is not claimed.
The current-source manuscript archive identifier remains SHA256
`85306d3050f88727cbff01ea54ca3023f7c75a38ab770e49802108bf87ecc84b`;
the manuscript itself is not distributed.
The [deviations record](ERRATA-AND-DEVIATIONS.md) retains the 17 designated
rendering/scope notes and four approved conventions still unprinted in the
manuscript. This preparation does not change those records.

The project classifications are `math.PR`, `math.CO`, `60D05`, `60F05`,
`05C10` and `40E05`. Each was checked against the official
[arXiv](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/taxonomies/arxiv-categories.json)
and [MSC2020](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/taxonomies/msc2020-codes.json)
snapshots at the pinned pipeline revision.

## Local reproduction

With the pinned dependencies available, `bash scripts/verify-palomar.sh` runs
the exact Challenge-hole controls, all nine intended local Comparator configurations,
the optional A.2 pilot, and their exact Solution axiom probes. It retains each run in a distinct
`.lake/palomar-evidence/verify-<UTC>-<pid>/` directory. It requires ordinary
Comparator sandbox support and adds the submitted toolchain's real bin
directory to PATH so the bundled `nanoda_bin` is visible. These generated
local logs are separate from an official Palomar mechanical report.
The full original 90-entry verification remains `bash scripts/verify.sh`.

## Manual verification workflows

- `lean.yml` runs the existing source/integrity, full library, axiom and fresh
  Lean-kernel checks through `scripts/verify.sh`, followed by the exact
  Challenge-hole controls and both Appendix/Pilot Solution axiom probes (one pilot plus six
  Appendix declarations). It runs no Comparator job. It installs pinned elan and
  the repository's unchanged toolchain, retrieves only explicitly imported
  Mathlib modules and their dependency closure using the inspected pinned cache
  CLI, frees disposable hosted-runner SDK space
  and requires at least 20 GiB free. Its hosted runtime and memory requirements
  have not been validated.
- `comparator.yml` calls the pinned official reusable workflow with
  `mode: full`, `execution_profile: palomar-standard-v1` and request ID
  a unique twelve-character lowercase alphanumeric value. Its manual selector
  chooses root `comparator.json` or one of the nine explicitly allowlisted principal
  configurations; only paths present at the checked commit can run. The official workflow
  performs its own disk cleanup, protected Challenge/provenance checks,
  mandatory NanoDa and Lean replay, and any recorded advisory checker attempt.

Both workflows are manual-dispatch checks with no push or pull-request trigger.
The root six-Appendix configuration passed the complete official full preflight
at `e2e3be75d8e7b39eaf0d8ce24b504287421c4a41` on 12 November 2026.
The Appendix pass and seven subsequent principal passes are recorded in
[portable receipts](../verification/PALOMAR-OFFICIAL-RESULTS.json), with exact
workflow URLs, configuration paths and report hashes. These eight historical
configurations cover thirteen numbered results; Theorems 1.7 and 1.8 passed at
`63dd637`. A PASS is bound to its exact
commit and configuration; the final integration still requires all ten
configurations to pass at the same exact commit. Local checks alone do not establish this gate.
No Palomar editorial review, intake or registration has occurred.

The minimal pinned caller is on the default branch so GitHub permits manual
dispatch. Its checked source is selected by the dispatch ref and passed as the
exact `github.sha` to the official reusable workflow. The responsible human
confirmed the authorization relationship "I am a responsible author or
maintainer" when approving this preparation push and mechanical preflight.
That approval does not authorize Palomar intake or registration.

For each intended configuration, select the preparation branch's exact final
commit, run the pinned manual Comparator workflow in full mode, and retain its
complete successful mechanical report and workflow URL. The required request
ID is exactly twelve lowercase letters or digits. The final review report must
list the source commit, configuration path, compared declarations and their
source coverage, independent fidelity review, local kernel/axiom checks, and
the official mechanical receipt. The separate pilot overlaps A.2 and is not an
additional intended result. The nine principal configurations and the combined
Appendix configuration cover fifteen results, not the whole 90-item catalogue.
At this snapshot nine intended configurations (the Appendix plus eight principal
entries, including Proposition 5.9) are locally validated; Proposition 5.16 remains pending.

Final submission requires separate human authorization. Do not initiate intake
or registration as part of preparation.

The finite-cell coverage and all comparison auxiliaries are documented separately:
[Theorem1.12](PALOMAR-CELLLDP.md), [Theorem1.13](PALOMAR-CELLSDP.md). Their local receipts are
[CellLDP](../verification/PALOMAR-CELLLDP-RESULTS.json) and
[CellSDP](../verification/PALOMAR-CELLSDP-RESULTS.json). No official or registration
status is inferred from these local passes.

## Implemented Busemann entry

[Theorem 1.4 coverage](PALOMAR-BUSEMANN.md) documents all twenty-seven compared declarations, fourteen explicit construction/main holes, thirteen proved constructor certificates, actual map/distance transports, normal Comparator and both kernel passes. The complete official preflight remains tied to its exact public commit.

## Implemented Busemann increment and tail entries

[Theorems 1.7 and 1.8 coverage](PALOMAR-BUSEMANN-PROPERTIES.md) records the
actual identified LDP/SDP functions, both independent increment families, the
paired tail constants and exponents, and the all-index integrability and mean
clauses. Both entries passed normal source Comparator, NanoDa and default Lean
checks with all 27 axiom targets per entry. Their final official checks remain
pending with the full all-ten configuration set.

## Implemented functional-convergence entry

[Theorem1.6 coverage](PALOMAR-CONVERGENCE.md) lists all forty-three compared declarations and proves actual scalar, metric/Borel and complete path-law correspondence. Both full functional limits remain; no FDD-only substitute or extra assumption is used.
