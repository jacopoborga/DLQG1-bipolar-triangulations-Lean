# Errata and deviations

This record concerns the 90 numbered results and their required definitions. It compares the formal statements with the supplied manuscript revision identified in CORRESPONDENCE.json. It contains mathematical scope information, not private development records. The manuscript files are excluded from this repository.

## Current-source domains and supporting proofs

The revised source domains now have explicit views and proved actual-object bindings. Independent focused source-domain review covers all 90 numbered entries and 97 unchanged primary exports, without added premises. The earlier two domain-gap notices are superseded by these bindings. **The source-domain verification files passed compilation, 37 axiom probes and fresh kernel replay.** These are proved correspondence bindings, not additional author rulings.

1. **Definition 3.17: finite boundary-channeled maps.** `DirectedDistances.PlanarMap.KMSWMapIsoClass.IsSourceBoundaryChanneled` in [SourceBoundaryChanneled](../verification/SourceBoundaryChanneled.lean) is primary channeling AND (simple outer boundary OR the actual singleton m0), on the same raw/isoclass carriers. The generic `IsChanneled` remains broader; no global equality is claimed. `isSourceBoundaryChanneled_iff_right_one` proves membership equivalence in every positive-left/right-boundary-one case, including m0. The positive/zero-step 3.19 and 3.18 reversal transports are proved. `DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5.finiteGeometricLaw_sourceView_filter_eq` proves that filtering the actual 5.16 uniform-map/independent-mark sample leaves the exact existing geometric observable law unchanged. No conditioning, changed normalizer or replacement observable is introduced.
2. **Definition 1.1: external-boundary standing convention.** `DirectedDistances.PlanarMap.DirectedPlaneMap.PolesOnExternalBoundary` and `SourceBoundaryDomain` in [SourceBoundaryDomain](../verification/SourceBoundaryDomain.lean) record the clause for each existing pole on the same drawing. `DirectedDistances.KMSW.uiqbot_ae_source_boundary_domain` uses the original UIQBOT event and chosen map/drawing; the whole-plane binding uses the actual source construction and has no finite poles, so no external face is invented. [SourceScopeCheck](../verification/SourceScopeCheck.lean) proves `DirectedDistances.KMSW.finiteIsoClass_source_boundary_domain` for every actual ordinary finite class through its unchanged KMSW realization. The generic bipolar/triangulation predicates remain unchanged and broader. `SourceBipolarTriangulation` is only the literal intersection with the existing BySides predicate: no new concrete inhabitance, faceDegree/sideDegree equivalence or global predicate identity is claimed. Partially oriented future/cell/UIBHBOT maps retain their own source conventions and distance graphs.

## Explicit mathematical rendering conventions

- **Definition 1.2:** longest-path distance is an extended supremum: negative infinity when unreachable, the attained maximum when bounded, and positive infinity when lengths are unbounded. Finite distances used in Busemann subtraction require the proved finiteness statements. The manuscript still says “longest.”
- **Theorems 1.4 and Lemma 5.3:** probability-one scope is explicit, including the simultaneous countable quantifiers.
- **Theorem 1.6:** negative-time reversal uses left limits, giving a right-continuous whole-line path. The printed `X(-t)` shorthand does not state that convention.
- **Definitions 3.1, 3.2 and 3.8:** missing edges remain unoriented geometric edges; external faces are all unbounded complementary components; finite empty boundary paths retain their supplied junctions. The local topology uses connected locally finite plane maps, the ordered root mark, rotations and face incidence. Infinite boundary data come from the limiting construction.
- **Lemma 3.12:** the formal in-particular law marks a left-boundary vertex. The manuscript statement still says boundary edge, whereas its proof describes a vertex.
- **Definition 3.13:** ordinary directed geodesics retain their general acyclic-map meaning; the three-path leftmost characterization is in the finite bipolar planar setting.
- **Lemma 5.5:** independence is on the ordinary unrooted map-class values, as in the source. This is an explicit interpretation note, not a changed independence theorem.
- **Definition 5.8 and Proposition 5.9:** The half-plane object is treated as an acyclic triangulation with missing boundary edges; no global unique-source bipolar assertion is added. missing boundary edges are unoriented. Reflection preserves the distinguished geometric edge and reverses its ordered endpoint mark. The boundary indexing is shifted and recentered accordingly.
- **Lemma 5.10:** the future map in the law and containment clauses is the boundary-channeled object constructed in the lemma. The manuscript still drops that superscript in those clauses.
- **Lemma 5.12:** the implementation has an exact ordered constructor record and geometric face/frontier description. The existing declarations `stageTriangleDartList_left_existing_sides`, `stageTriangleDartList_left_fresh_sides`, `hasCreationCapDartSides_familyG`, `MonotoneStageInvariant.cap_sides_mem_iff` and `flowTriangle_prime_plane_face` supply the cyclic order, lower/upper cap assignments and transport to the actual retained primed face. They identify the upper one-edge side and the lower two-edge side in its order. The source-comparison argument composes these existing geometric characterizations; it is not an additional standalone specialization theorem. All named declarations are included in the dependency build.
- **Lemma 5.18:** the formal valid-window result is independent of the chosen measurable extension outside the finite walk domain. The dedicated constant-window definition, measurability and pointwise agreement are proved in verification/ConstantWindow.lean; ConstantWindowCheck.lean applies the universal conclusion with no extra hypotheses.
- **Appendix A.2 and A.3:** the revised integer-valued standing scope agrees with the natural-number-valued formal carrier.

## Incorporated manuscript updates

The revised manuscript incorporates the legal walk-step corrections, time-zero boundary indexing, both-mode geodesic scope, the stopped-past first-hit correction, finite-map size admissibility, and the integer Appendix standing domain. Proof-text repairs do not change the corresponding numbered formal statements. See the per-entry notes rather than treating every textual change as a new theorem.

## Scope of the source comparison

All 90 labels and kinds survive. Three entries change number. Compared with the earlier source, 71 statement environments are byte-identical, one differs only in whitespace, and 18 change in content. The audit also inspected relevant standing conventions and the formal definitions; those text counts are not a source-fidelity certificate by themselves. Private annotations and standalone remarks outside the 90-item dependency scope are not included here.

## Counts by mathematical source

Counts refer to the distinct numbered entries explicitly listed below: Introduction 1.1, 1.2, 1.4, 1.6; Section 3: 3.1, 3.2, 3.8, 3.12, 3.13, 3.17; Section 5: 5.3, 5.5, 5.8, 5.9, 5.10, 5.12, 5.18. These 17 entries include matching interpretation/specialization notes and the two resolved source-domain view notes. Supporting consumer references do not add notes to this count. It does not count the incorporated updates or the matching Appendix standing scope. Four approved conventions remain unprinted: Definition 1.2, Theorem 1.6, Lemma 3.12 and Lemma 5.10.

| Source | Numbered entries | Entries with explicit rendering/scope notes | Unresolved mathematical source-domain issues |
|---|---:|---:|---:|
| Introduction | 12 | 4 | 0 |
| Section 3 | 17 | 6 | 0 |
| Section 4 | 14 | 0 | 0 |
| Section 5 | 18 | 7 | 0 |
| Section 6 | 10 | 0 | 0 |
| Section 7 | 13 | 0 | 0 |
| Appendix A | 6 | 0 | 0 |
| Total | 90 | 17 | 0 |

The supporting compilation, axiom and kernel checks are recorded in [VERIFICATION.md](../VERIFICATION.md).
