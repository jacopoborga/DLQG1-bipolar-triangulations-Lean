/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination6
import all DirectedDistances.PaperProofs.Section5.BoundaryGeodesicSideGluing

/-! Finite enclosure determines an unoriented overlap. The reverse implication
still requires exclusion of the opposite orientation; no such exclusion is -/

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

/-- Helper toward Lemma 5.6: a future face point strictly below a trace
belongs to the named right side region `m0GeodesicSideOpenRegion`.
No openness of the named side region is asserted. -/
theorem m0CutFace_mem_rightSideOpenRegion_of_below_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    {y z : ℂ} (hz : z ∈ F.val)
    (hza : z ∈ m0GeodesicAmbientRegion W H h)
    (hy : y ∈ m0GeodesicTrace hp Q) (hre : y.re = z.re) (him : z.im < y.im) :
    z ∈ m0GeodesicSideOpenRegion hp Q .right := by
  refine ⟨hza, fun hcl => ?_⟩
  have hzT : z ∉ m0GeodesicTrace hp Q := fun hT =>
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).face_subset_compl F hz
      (m0GeodesicTrace_subset_drawing hp Q hT)
  exact boundaryGluing_below_trace_not_mem_leftOpen W h j longest hp Q hy hre him
    (m0GeodesicLeftOpen_closure_inter_complement_subset hp Q ⟨hcl, hza, hzT⟩)

/-- Helper toward Lemma 5.6: an enclosed face either is represented by
the candidate or lies in the opposite left/right overlap. This is an
unoriented classification, not the enclosure-to-candidate implication. -/
theorem m0CutFaceEnclosedBySegments_representsFace_or_reverse_sides
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (henc : m0CutFaceEnclosedBySegments hp P k a b F) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F ∨
      (F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .left ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .right) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let c := (G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
  obtain ⟨f, g, hf, hg, ha, hc, hG, hL, hB⟩ :=
    m0CutGeodesicSliceBoundaryTrace_exists_graphs hp P k a b hab
  obtain ⟨z, hzcompl, hFcomp⟩ := F.property
  have hzF : z ∈ F.val := hFcomp ▸ mem_connectedComponentIn hzcompl
  have hza := henc.1 hzF
  have hzB : z ∉ graphOver x c f ∪ graphOver x c g := by
    rw [← hB]
    exact fun hzb => G.face_subset_compl F hzF
      (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b hzb)
  have hxc : x ≤ c := by
    have hr : G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial 0).1.id) ∈
        m0CutGeodesicSliceBoundaryTrace hp P k a b := Or.inl (Or.inl (Or.inl rfl))
    rw [hB] at hr
    rcases hr with hr | hr <;> exact hr.1.trans hr.2.1
  have hbounded := henc.2 z hzF
  rw [hB] at hbounded
  have hregion := (isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
    hxc hf hg ha hc hzB).mp hbounded
  have hpG : (⟨z.re, g z.re⟩ : ℂ) ∈ m0GeodesicTrace hp (P (k - 1)) := by
    apply m0CutGeodesicSegmentTrace_subset_trace hp (P (k - 1)) a
    rw [← hG]
    exact ⟨hregion.1.le, hregion.2.1.le, rfl⟩
  have hpL : (⟨z.re, f z.re⟩ : ℂ) ∈ m0CutGeodesicSegmentTrace hp (P k) b ∪
      ((G.arc (wholePlaneDartι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image) := by
    rw [← hL]
    exact ⟨hregion.1.le, hregion.2.1.le, rfl⟩
  have hstrict : seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im := by
    obtain ⟨F0, hF0, heq⟩ := m0CutFace_exists_runZero_face hp F henc.1
    exact boundedFace_subset_upper (shiftedStream W 0) h (H.1 0) F0 hF0 (heq ▸ hzF)
  have hboundary := m0CutBoundaryEdgeTrace_eq_graphOver (H := H) (h := h) hp (k - 1)
  have hidx : k - 1 + 1 = k := by omega
  rw [hidx] at hboundary
  rcases le_total (f z.re) (g z.re) with hfg | hgf
  · have hlo : f z.re < z.im := by
      simpa only [min_eq_left hfg] using hregion.2.2.1
    have hhi : z.im < g z.re := by
      simpa only [max_eq_right hfg] using hregion.2.2.2
    have hzR := m0CutFace_mem_rightSideOpenRegion_of_below_trace hp (P (k - 1)) F
      hzF hza hpG rfl hhi
    have hzL : z ∈ m0GeodesicSideOpenRegion hp (P k) .left := by
      rcases hpL with hpSeg | hpEdge
      · exact boundaryGluing_above_trace_mem_leftOpen W h k longest hp (P k)
          (m0CutGeodesicSegmentTrace_subset_trace hp (P k) b hpSeg) rfl hlo
      · rw [hboundary] at hpEdge
        apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) z).mpr
        refine ⟨hza, ?_⟩
        rcases lt_or_eq_of_le hpEdge.2.1 with hw | heq
        · exact Or.inl hw
        · right
          refine ⟨G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial 0).1.id),
            m0Geodesic_initial_pos_mem_trace hp (P k) 0, ?_, ?_⟩
          · rw [m0CutGeodesic_initial_zero_pos]
            exact heq.symm
          · rw [m0CutGeodesic_initial_zero_pos]
            change z.re = seamX (shiftedStream W 0) h (H.1 0) k at heq
            change seamFun (shiftedStream W 0) h (H.1 0)
              (seamX (shiftedStream W 0) h (H.1 0) k) < z.im
            rw [← heq]
            exact hstrict
    exact Or.inl ((m0CutGeodesicSliceRepresentsFace_iff_mem_side_regions
      hp P k a b hab F hzF).mpr ⟨hzR, hzL⟩)
  · have hlo : g z.re < z.im := by
      simpa only [min_eq_right hgf] using hregion.2.2.1
    have hhi : z.im < f z.re := by
      simpa only [max_eq_left hgf] using hregion.2.2.2
    have hzL : z ∈ m0GeodesicSideOpenRegion hp (P (k - 1)) .left :=
      boundaryGluing_above_trace_mem_leftOpen W h (k - 1) longest hp (P (k - 1)) hpG rfl hlo
    have hpNew : (⟨z.re, f z.re⟩ : ℂ) ∈ m0GeodesicTrace hp (P k) := by
      rcases hpL with hpSeg | hpEdge
      · exact m0CutGeodesicSegmentTrace_subset_trace hp (P k) b hpSeg
      · rw [hboundary] at hpEdge
        have hfs : f z.re = seamFun (shiftedStream W 0) h (H.1 0) z.re := hpEdge.2.2
        rw [hfs] at hhi
        exact False.elim ((hstrict.trans hhi).false)
    have hzR := m0CutFace_mem_rightSideOpenRegion_of_below_trace hp (P k) F
      hzF hza hpNew rfl hhi
    exact Or.inr
      ⟨(m0CutFace_subset_sideOpenRegion_iff_mem hp (P (k - 1)) F .left hzF henc.1).mpr hzL,
        (m0CutFace_subset_sideOpenRegion_iff_mem hp (P k) F .right hzF henc.1).mpr hzR⟩

/-- Helper toward Lemma 5.6: the enclosure-to-candidate implication holds
for any face with a point at or west of the later root. The opposite
orientation is impossible there, since that point is on the later left side. -/
theorem m0CutGeodesicSliceRepresentsFace_of_enclosedBySegments_of_re_le_root
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (henc : m0CutFaceEnclosedBySegments hp P k a b F)
    {z : ℂ} (hz : z ∈ F.val)
    (hwest : z.re ≤ seamX (shiftedStream W 0) h (H.1 0) k) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F := by
  rcases m0CutFaceEnclosedBySegments_representsFace_or_reverse_sides
      hp P k a b hab F henc with hrep | hreverse
  · exact hrep
  · have hzL : z ∈ m0GeodesicSideOpenRegion hp (P k) .left := by
      apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) z).mpr
      refine ⟨henc.1 hz, ?_⟩
      rcases lt_or_eq_of_le hwest with hw | heq
      · exact Or.inl hw
      · obtain ⟨F0, hF0, hFF0⟩ := m0CutFace_exists_runZero_face hp F henc.1
        have hstrict := boundedFace_subset_upper (shiftedStream W 0) h (H.1 0)
          F0 hF0 (hFF0 ▸ hz)
        right
        refine ⟨(WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 ((P k).codePath.initial 0).1.id),
          m0Geodesic_initial_pos_mem_trace hp (P k) 0, ?_, ?_⟩
        · rw [m0CutGeodesic_initial_zero_pos]
          exact heq.symm
        · rw [m0CutGeodesic_initial_zero_pos]
          change seamFun (shiftedStream W 0) h (H.1 0)
            (seamX (shiftedStream W 0) h (H.1 0) k) < z.im
          rw [← heq]
          exact hstrict
    exact False.elim (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P k))
      hzL (hreverse.2 hz))



























end DirectedDistances.PaperProofs.Section5
