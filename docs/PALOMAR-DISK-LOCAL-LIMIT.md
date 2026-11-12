# Proposition 5.16: disk local limit

The configuration [`palomar/principal/disk-local-limit.json`](../palomar/principal/disk-local-limit.json) compares `DLQG1.Palomar.Principal.disk_local_limit` with `DirectedDistances.Paper.Section5.prop_disk_bs_conv`. It selects 55 theorem targets: 36 deliberately quarantined Challenge proofs and 19 already-proved typing/construction certificates. `definition_names=[]`; the source-defined data are compared through the ordinary Comparator.

The selected surface includes the actual rooted geometric-map quotient and local topology, the finite uniform map class and independent mark, the full admissibility and congruence conditions, finite path-attainment and endpoint clauses, and the local-limit conclusion. The source support and Solution have no placeholders. The fresh source review matched all 238 compared data constants and all 55 types and declaration kinds; two additional finite proof pairs were also checked for exact types and values.

## Source and proof status

A strict diagnostic compared all 55 declarations, ran NanoDa and replayed the result with Lean's default kernel. A subsequent fresh-source normal Comparator run also passed with NanoDa and the default Lean kernel. A fresh axiom probe covered all 55 targets; the observed union is `propext`, `Classical.choice` and `Quot.sound`, and the 19 proved certificates use only `propext` and `Quot.sound`. The exact file hashes, target-order hash, run summaries and probe digest are in the [portable receipt](../verification/PALOMAR-DISK-LOCAL-LIMIT-RESULTS.json).

The Challenge is 999 physical lines and 69,229 bytes. It is within the 1,000-line/100-KiB hard limit and exceeds the preferred 300-line/32-KiB advisory.

## One transparent frontend helper

The Challenge imports Mathlib and one Lean core module through `public meta import Lean.Elab.PreDefinition.Basic`. A single-use `run_elab` helper builds a public, safe, noncomputable declaration from an ordinary quoted term. It uses normal term elaboration and metavariable synthesis/instantiation, calls `withoutErrToSorry`, infers the ordinary term's type, and registers the declaration with the standard `Elab.addNonRec` API with proof abstraction disabled. Its only delta expansion is the standard `Meta.deltaExpand` on the public `PProd.fst` projection, with the default opaque-constant behavior. This avoids frontend proof sharing for that term. The helper does not construct or rewrite expressions, replace the environment, bypass kernel checks, or add axioms. The resulting source declarations are still checked by exact comparison, NanoDa and Lean.

The local Proposition 5.16 checks are complete. The final official preflight still requires all ten intended configurations to pass in full mode at one exact final commit. No Palomar intake or registration has occurred.
