# Theorems 1.7 and 1.8: Busemann increments and tails

These are two separate Comparator entries. They use the current manuscript
labels `thm-busemann-property` and `thm-busemann-tail`; the Challenges contain
the actual rooted KMSW geometry, quotient and rotation data, identified LDP/SDP
functions, and their source-defined probability law. No arbitrary process or
assumed Busemann object replaces those definitions.

## Theorem 1.7: increment properties

Configuration: [`palomar/principal/busemann-increments.json`](../palomar/principal/busemann-increments.json).
The compared main result is
`DLQG1.Palomar.Principal.busemann_increments`; its source is
`DirectedDistances.Paper.Section1.thm_busemann_property`.

The statement preserves both actual LDP and SDP functions and all independent
increment clauses. It keeps the side-specific stationary ranges (right indices
`k ≥ 1`, left indices `k ≤ 0`), the simultaneous almost-sure LDP/SDP sign
bounds, and the sign-reflected law for every nonpositive-time increment. The
proved per-index witness equivalences and all-code scalar equalities identify
the chosen functions with the current source objects; no uniqueness beyond the
actual source characterization is assumed.

## Theorem 1.8: tail estimates

Configuration: [`palomar/principal/busemann-tails.json`](../palomar/principal/busemann-tails.json).
The compared main result is `DLQG1.Palomar.Principal.busemann_tails`; its
source is `DirectedDistances.PaperProofs.SourceResults.thm_busemann_tail_provider`
for `DirectedDistances.Paper.Section1.thm_busemann_tail`.

The LDP and SDP tails retain their exact signs, threshold parameter, `2/3` and
`4/3` exponents, and the same positive constant `c` and `2c` within each
mode's paired bounds. The SDP statement also retains integrability and mean
zero for every integer index. Both modes use the same proved geometric
identifications as Theorem 1.7.

## Compared scope and validation

Each Challenge selects 27 theorem declarations: fourteen deliberate theorem
holes (thirteen construction obligations and its numbered main result) plus
thirteen constructor certificates whose proofs remain present. No definition
is skipped (`definition_names=[]`), and each Solution has no holes. The
Challenges have 916/909 physical lines and 46,790/44,950 bytes, below the
1,000-line and 100-KiB hard limits. The full target lists and exact file hashes
are in the two portable result receipts.

Both normal source Comparators passed with NanoDa and the default Lean kernel.
All 27 axiom probes per entry use only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` occurs. The [Theorem 1.7 receipt](../verification/PALOMAR-BUSEMANN-INCREMENTS-RESULTS.json)
and [Theorem 1.8 receipt](../verification/PALOMAR-BUSEMANN-TAILS-RESULTS.json)
record the exact local inputs, target types, axiom outputs, kernel acceptance
messages and log hashes.

These are local results. The final official preflight still requires all ten
intended configurations to pass at one exact final integration commit. The
six historical official passes are bound to earlier commits and do not certify
that later snapshot. Propositions 5.9 and 5.16 remain pending. No Palomar
intake or registration has occurred.
