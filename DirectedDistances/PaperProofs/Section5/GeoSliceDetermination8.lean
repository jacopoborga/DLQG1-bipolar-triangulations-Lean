/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination7
import all DirectedDistances.PaperProofs.Section5.BoundaryGeodesicSideGluing






public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: every ambient point at or west of a root
belongs to the closure of its named left side region. The equality case
includes the root itself and uses trace inclusion in that closure. -/
theorem m0CutGeodesic_mem_closure_leftOpen_of_re_le_root
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) {z : ℂ}
    (hza : z ∈ m0GeodesicAmbientRegion W H h)
    (hwest : z.re ≤ seamX (shiftedStream W 0) h (H.1 0) j) :
    z ∈ closure (m0GeodesicLeftOpen hp Q) := by
  rcases lt_or_eq_of_le hwest with hw | heq
  · exact subset_closure (boundaryGluing_west_of_root_mem_leftOpen
      W h j longest hp Q hza hw)
  · have hroot := m0Geodesic_initial_pos_mem_trace hp Q 0
    rw [m0CutGeodesic_initial_zero_pos] at hroot
    have hseam : seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im := hza
    rcases lt_or_eq_of_le hseam with habove | hon
    · apply subset_closure
      apply boundaryGluing_above_trace_mem_leftOpen W h j longest hp Q hroot
      · exact heq.symm
      · change seamFun (shiftedStream W 0) h (H.1 0)
          (seamX (shiftedStream W 0) h (H.1 0) j) < z.im
        rw [← heq]
        exact habove
    · apply m0GeodesicTrace_subset_closure_leftOpen hp Q
      have hzroot : z = (⟨seamX (shiftedStream W 0) h (H.1 0) j,
          seamFun (shiftedStream W 0) h (H.1 0)
            (seamX (shiftedStream W 0) h (H.1 0) j)⟩ : ℂ) := by
        apply Complex.ext
        · exact heq
        · change z.im = seamFun (shiftedStream W 0) h (H.1 0)
            (seamX (shiftedStream W 0) h (H.1 0) j)
          rw [← heq]
          exact hon.symm
      exact hzroot ▸ hroot

/-- Helper toward Lemma 5.6: a point of the earlier trace at or beyond
the coalescence abscissa lies on the later trace. This uses literal edge
tail equality and includes the junction, without a first-meeting premise. -/
theorem m0CutGeodesicTrace_mem_of_re_ge_coalescence
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j l : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (R : M0CutInfiniteGeodesic W H h hLL l longest) (a b : ℕ)
    (hco : M0CutEdgeTailsCoalesce Q R a b) {z : ℂ}
    (hz : z ∈ m0GeodesicTrace hp Q)
    (hre : ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (Q.codePath.initial a).1.id)).re ≤ z.re) :
    z ∈ m0GeodesicTrace hp R := by
  have hrev : M0CutEdgeTailsCoalesce R Q b a := fun n => (hco n).symm
  rcases m0CutGeodesicTrace_subset_segmentTrace_union_of_coalescence
      hp R Q b a hrev hz with hseg | htail
  · have hbound := hseg
    rw [m0CutGeodesicSegmentTrace_eq_trace_inter_re_le] at hbound
    have heqre := le_antisymm hbound.2 hre
    obtain ⟨X, g, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp Q
    have hzg := hz
    have heg := m0Geodesic_initial_pos_mem_trace hp Q a
    rw [hgraph] at hzg heg
    have heq : z = (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 (Q.codePath.initial a).1.id) :=
      Complex.ext heqre (hzg.2.trans ((congrArg g heqre).trans heg.2.symm))
    rw [heq]
    have hmeet := m0Cut_initial_vertex_eq_of_edge_tails_coalesce Q R hco
    have hpos := congrArg (fun v : PresentVertex (shiftedStream W 0) =>
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 v.id)) hmeet
    rw [hpos]
    exact m0Geodesic_initial_pos_mem_trace hp R b
  · exact htail

/-- Helper toward Lemma 5.6: the opposite overlap is strictly east of
the later root and strictly west of the common-tail junction. This is a
localization theorem, not an exclusion of the positive-offset case. -/
theorem m0CutGeodesic_reverse_sides_re_bounds
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) {z : ℂ}
    (hzL : z ∈ m0GeodesicSideOpenRegion hp (P (k - 1)) .left)
    (hzR : z ∈ m0GeodesicSideOpenRegion hp (P k) .right) :
    seamX (shiftedStream W 0) h (H.1 0) k < z.re ∧
      z.re < ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re := by
  have hwest : seamX (shiftedStream W 0) h (H.1 0) k < z.re := by
    by_contra hn
    exact hzR.2 (m0CutGeodesic_mem_closure_leftOpen_of_re_le_root
      hp (P k) hzR.1 (le_of_not_gt hn))
  refine ⟨hwest, ?_⟩
  by_contra hn
  have hge := le_of_not_gt hn
  have hleft := (m0CutGeodesicLeftOpen_iff_west_or_above_trace
    hp (P (k - 1)) z).mp hzL
  rcases hleft.2 with hw | ⟨p, hpT, hpre, hpim⟩
  · have hroots := seamX_strictMono (shiftedStream W 0) h (H.1 0)
      (show k - 1 < k by omega)
    exact (hwest.trans (hw.trans hroots)).false
  · have hpR := m0CutGeodesicTrace_mem_of_re_ge_coalescence
      hp (P (k - 1)) (P k) a b hab.1 hpT (by rw [hpre]; exact hge)
    exact hzR.2 (subset_closure
      (boundaryGluing_above_trace_mem_leftOpen W h k longest hp (P k) hpR hpre hpim))

/-- Helper toward Lemma 5.6: the opposite overlap is bounded. Thus an
argument that excludes this overlap merely by claiming it is unbounded
cannot apply on the unrestricted arbitrary-geodesic domain. This theorem
does not assert that the overlap is nonempty. -/
theorem m0CutGeodesic_reverse_sides_isBounded
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    Bornology.IsBounded (m0GeodesicSideOpenRegion hp (P (k - 1)) .left ∩
      m0GeodesicSideOpenRegion hp (P k) .right) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let c := (G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
  obtain ⟨f, g, hf, hg, _, _, hG, hL, _⟩ :=
    m0CutGeodesicSliceBoundaryTrace_exists_graphs hp P k a b hab
  apply (isBounded_graphRegion
    (continuous_min.comp_continuousOn (hf.prodMk hg))
    (continuous_max.comp_continuousOn (hf.prodMk hg))
    (fun _ _ => min_le_max)).subset
  intro z hz
  obtain ⟨hwest, hzc⟩ := m0CutGeodesic_reverse_sides_re_bounds
    hp P k a b hab hz.1 hz.2
  have hxz : x < z.re :=
    (seamX_strictMono (shiftedStream W 0) h (H.1 0)
      (show k - 1 < k by omega)).trans hwest
  have hpOld : (⟨z.re, g z.re⟩ : ℂ) ∈ m0GeodesicTrace hp (P (k - 1)) := by
    apply m0CutGeodesicSegmentTrace_subset_trace hp (P (k - 1)) a
    rw [← hG]
    exact ⟨hxz.le, hzc.le, rfl⟩
  have hpNew : (⟨z.re, f z.re⟩ : ℂ) ∈ m0GeodesicTrace hp (P k) := by
    have hpt : (⟨z.re, f z.re⟩ : ℂ) ∈ graphOver x c f :=
      ⟨hxz.le, hzc.le, rfl⟩
    rw [hL] at hpt
    rcases hpt with hseg | hedge
    · exact m0CutGeodesicSegmentTrace_subset_trace hp (P k) b hseg
    · have hboundary := m0CutBoundaryEdgeTrace_eq_graphOver (H := H) (h := h) hp (k - 1)
      have hidx : k - 1 + 1 = k := by omega
      rw [hidx] at hboundary
      rw [hboundary] at hedge
      exact False.elim (hwest.not_ge hedge.2.1)
  have hlow : g z.re < z.im := by
    have hleft := (m0CutGeodesicLeftOpen_iff_west_or_above_trace
      hp (P (k - 1)) z).mp hz.1
    rcases hleft.2 with hw | ⟨p, hpT, hpre, hpim⟩
    · exact False.elim ((hxz.trans hw).false)
    · obtain ⟨X, q, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp (P (k - 1))
      rw [hgraph] at hpT hpOld
      have hpval : p.im = g z.re :=
        hpT.2.trans ((congrArg q hpre).trans hpOld.2.symm)
      rw [hpval] at hpim
      exact hpim
  have hhi : z.im < f z.re := by
    have hnot : ¬ f z.re ≤ z.im := by
      intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hz.2.2 (subset_closure
          (boundaryGluing_above_trace_mem_leftOpen W h k longest hp (P k) hpNew rfl hlt))
      · apply hz.2.2
        apply m0GeodesicTrace_subset_closure_leftOpen hp (P k)
        have heqpoint : z = (⟨z.re, f z.re⟩ : ℂ) := by
          apply Complex.ext
          · rfl
          · exact heq.symm
        rw [heqpoint]
        exact hpNew
    exact lt_of_not_ge hnot
  refine ⟨hxz, hzc, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) hlow
  · exact lt_of_lt_of_le hhi (le_max_left _ _)

/-- Helper toward Lemma 5.6: when the later coalescence offset is zero,
the opposite overlap is empty. Zero and positive offsets form an exhaustive
case split on the original unrestricted domain. -/
theorem m0CutGeodesic_reverse_sides_disjoint_of_zero
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0) :
    Disjoint (m0GeodesicSideOpenRegion hp (P (k - 1)) .left)
      (m0GeodesicSideOpenRegion hp (P k) .right) := by
  apply Set.disjoint_left.mpr
  intro z hzL hzR
  obtain ⟨hlo, hhi⟩ := m0CutGeodesic_reverse_sides_re_bounds hp P k a 0 hab hzL hzR
  have hmeet := congrArg (fun v : PresentVertex (shiftedStream W 0) =>
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 v.id))
    (m0Cut_least_edge_coalescence_initial_vertex_eq P k hab)
  rw [hmeet, m0CutGeodesic_initial_zero_pos] at hhi
  exact (hlo.trans hhi).false

/-- Helper toward Lemma 5.6: finite enclosure implies candidate face
representation in the zero later-offset case. No extra face or enclosure
fact is assumed beyond the original reverse implication's antecedent. -/
theorem m0CutGeodesicSliceRepresentsFace_of_enclosedBySegments_of_zero
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P k a 0 F →
      m0CutGeodesicSliceRepresentsFace hp P k a 0 hab F := by
  intro henc
  rcases m0CutFaceEnclosedBySegments_representsFace_or_reverse_sides
      hp P k a 0 hab F henc with hrep | hrev
  · exact hrep
  · obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    exact False.elim (Set.disjoint_left.mp
      (m0CutGeodesic_reverse_sides_disjoint_of_zero hp P k a hab)
      (hrev.1 hzF) (hrev.2 hzF))

/-- Helper toward Lemma 5.6: the full face-identification equivalence
holds for a zero later coalescence offset. The positive-offset case remains
an independent obligation. -/
theorem m0CutGeodesicSlice_face_identification_of_zero
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P k a 0 F ↔
      m0CutGeodesicSliceRepresentsFace hp P k a 0 hab F :=
  ⟨m0CutGeodesicSliceRepresentsFace_of_enclosedBySegments_of_zero hp P k a hab F,
    m0CutFaceEnclosedBySegments_of_representsFace hp P k a 0 hab F⟩


























































end DirectedDistances.PaperProofs.Section5
