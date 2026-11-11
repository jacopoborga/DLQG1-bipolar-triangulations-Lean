/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingCcw
import all DirectedDistances.KMSW.UIBHBOTGlueDrawingCcw

/-! # Complete seam traces in the UIBHBOT assembly -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

private theorem polyline_x_image_surjective (p : Polyline)
    (hmono : p.XMonotone) (hlen : 2 ≤ p.points.length) {x : ℝ}
    (hlo : p.start.re ≤ x) (hhi : x ≤ p.finish.re) :
    ∃ z ∈ p.image, z.re = x := by
  by_cases hx : x = p.start.re
  · exact ⟨p.start, Or.inl rfl, hx.symm⟩
  · have hlo' : p.start.re < x := lt_of_le_of_ne hlo (Ne.symm hx)
    let n := p.points.length - 1
    have hn : n < p.points.length := by dsimp [n]; omega
    have hlast : p.point n = p.finish := by
      dsimp [n]
      exact p.point_last_eq_finish
    have hex : ∃ j, x ≤ (p.point j).re := ⟨n, by rw [hlast]; exact hhi⟩
    let j := Nat.find hex
    have hj : x ≤ (p.point j).re := Nat.find_spec hex
    have hjle : j ≤ n := Nat.find_min' hex (by rw [hlast]; exact hhi)
    have hjlt : j < p.points.length := lt_of_le_of_lt hjle hn
    have hp0 : p.point 0 = p.start := p.point_zero_eq_start
    have hjpos : 0 < j := by
      by_contra hjnot
      have hjzero : j = 0 := Nat.eq_zero_of_not_pos hjnot
      have hj' : x ≤ (p.point 0).re := by simpa [hjzero] using hj
      rw [hp0] at hj'
      exact (not_le_of_gt hlo') hj'
    let i := j - 1
    have hij : i + 1 = j := by dsimp [i]; omega
    have hilt : i + 1 < p.points.length := by rw [hij]; exact hjlt
    have hleft : (p.point i).re < x := by
      apply lt_of_not_ge
      intro hxi
      have hnot := Nat.find_min hex (show i < j by dsimp [i]; omega)
      exact hnot hxi
    have hab : (p.point i).re < (p.point (i + 1)).re :=
      p.point_re_lt hmono (Nat.lt_succ_self i) hilt
    let z : ℂ := ⟨x, segmentHeight (p.point i) (p.point (i + 1)) x⟩
    have hzseg : z ∈ p.segmentAt i := by
      change z ∈ segment ℝ (p.point i) (p.point (i + 1))
      rw [mem_segment_iff_height hab]
      exact ⟨hleft.le, by simpa [hij] using hj, rfl⟩
    exact ⟨z, Or.inr ⟨i, hilt, hzseg⟩, rfl⟩

private theorem pastStraightHalfTurn_apply (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (z : ℂ) :
    uibhbotAssemblyHalfTurn (uibhbotPastStraightTransfer W hL hR z) =
      ⟨z.re - 1, z.im - uibhbotPastSeamHeight W hL hR z.re⟩ := by
  apply Complex.ext
  · simp [uibhbotAssemblyHalfTurn, uibhbotPastStraightTransfer,
      pastTransferHomeomorph, pastTransfer]
  · simp [uibhbotAssemblyHalfTurn, uibhbotPastStraightTransfer,
      pastTransferHomeomorph, pastTransfer]
    ring

private theorem futureStraightTransfer_apply (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w) (z : ℂ) :
    uibhbotGlueFutureTransfer w h hfin z =
      ⟨-z.re, -z.im + seamFun w h hfin z.re⟩ := by
  apply Complex.ext
  · simp [uibhbotGlueFutureTransfer, pastTransferHomeomorph, pastTransfer]
  · simp [uibhbotGlueFutureTransfer, pastTransferHomeomorph, pastTransfer]

private theorem past_seam_trace_interval (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (n e : ℕ) (he : e < (kmswStage (kmswPastCode W) n).nextEdge)
    (hseam : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR)
    (j : ℤ)
    (hjw : kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).west e) = -(j : ℚ))
    (hjt : kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).east e) = 1 - (j : ℚ)) :
    uibhbotAssemblyHalfTurn ''
      (uibhbotPastStraightTransfer W hL hR ''
        (layoutArc (kmswPastCode W) n e).image) =
      {z : ℂ | -((j : ℝ) + 1) ≤ z.re ∧ z.re ≤ -(j : ℝ) ∧ z.im = 0} := by
  let p := layoutArc (kmswPastCode W) n e
  have hmono : p.XMonotone := layoutArc_points_pairwise _ n e he
  have hlen : 2 ≤ p.points.length := layoutArc_length_two_le _ n e
  have hstart : p.start.re = -(j : ℝ) := by
    rw [layoutArc_start _ n e he]
    change (kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).west e) : ℝ) = _
    exact_mod_cast hjw
  have hfinish : p.finish.re = 1 - (j : ℝ) := by
    rw [layoutArc_finish _ n e he]
    change (kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).east e) : ℝ) = _
    exact_mod_cast hjt
  have hformula (x : ℂ) := pastStraightHalfTurn_apply W hL hR x
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    have hySource : y ∈ p.image := hy
    have hxg := (layoutArc_image_graph (kmswPastCode W) n e he).choose_spec
    rw [hxg] at hy
    change (kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).west e) : ℝ) ≤ y.re ∧
      y.re ≤ (kmswStageRank (kmswPastCode W) n
        ((kmswStage (kmswPastCode W) n).east e) : ℝ) ∧ _ at hy
    rw [hjw, hjt] at hy
    push_cast at hy
    have hy' : y ∈ ((uibhbotPastMonotoneDrawing W hfin).arc (e, false)).image := by
      rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e he false]
      simpa only [Bool.false_eq_true, ite_false] using hySource
    have hgraph := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n e hseam hy'
    have hh := uibhbotPastSeamHeight_eq_of_mem W hL hR hgraph
    rw [hformula y]
    exact ⟨by dsimp; linarith only [hy.1], by dsimp; linarith only [hy.2.1], by
      simp
      linarith only [hh]⟩
  · intro hz
    let x : ℝ := z.re + 1
    have hxlo : p.start.re ≤ x := by rw [hstart]; dsimp [x]; linarith only [hz.1]
    have hxhi : x ≤ p.finish.re := by rw [hfinish]; dsimp [x]; linarith only [hz.2.1]
    obtain ⟨y, hy, hyr⟩ := polyline_x_image_surjective p hmono hlen hxlo hxhi
    have hy' : y ∈ ((uibhbotPastMonotoneDrawing W hfin).arc (e, false)).image := by
      rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e he false]
      simpa only [Bool.false_eq_true, ite_false] using hy
    have hgraph := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n e hseam hy'
    have hh := uibhbotPastSeamHeight_eq_of_mem W hL hR hgraph
    refine ⟨uibhbotPastStraightTransfer W hL hR y,
      ⟨y, hy, rfl⟩, ?_⟩
    rw [hformula y]
    apply Complex.ext
    · change y.re - 1 = z.re
      dsimp [x] at hyr
      linarith only [hyr]
    · change y.im - uibhbotPastSeamHeight W hL hR y.re = z.im
      rw [hh, hz.2.2]
      ring

private theorem future_seam_trace_interval (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer w h hfin ''
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image)
    (j : ℤ) (b : Bool) :
    (F.arc (boundaryOuterEdge w h j, b)).image =
      {z : ℂ | -((j : ℝ) + 1) ≤ z.re ∧ z.re ≤ -(j : ℝ) ∧ z.im = 0} := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let d := futureMapBoundaryDart w h j
  obtain ⟨g, hg⟩ := seam_arc_image_graph w h hfin j
  have hvs := seam_arc_vertical_sections w h hfin j
  have hXj : seamX w h hfin j = (j : ℝ) := uibhbotGlue_seamX_eq_int w h hfin j
  have hXj1 : seamX w h hfin (j + 1) = (j : ℝ) + 1 := by
    rw [uibhbotGlue_seamX_eq_int w h hfin (j + 1)]
    norm_num
  ext z
  constructor
  · intro hz
    rw [hFa (boundaryOuterEdge w h j, b)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : y ∈ (P.arc d).image := by
      cases b with
      | true => exact hy
      | false =>
        have hr := P.arc_flip (boundaryOuterEdge w h j, true)
        change P.arc (boundaryOuterEdge w h j, false) = _ at hr
        have hy'' : y ∈ (P.arc (boundaryOuterEdge w h j, false)).image := hy
        rwa [hr, Polyline.image_reverse_transfer] at hy''
    have hseam : y.im = seamFun w h hfin y.re := by
      simpa only [Set.mem_ofPred_eq] using
        uibhbotAssembly_future_seam_graph w h hfin j true hy'
    rw [hg] at hy'
    rw [uibhbotGlue_seamX_eq_int w h hfin j,
      uibhbotGlue_seamX_eq_int w h hfin (j + 1)] at hy'
    rw [futureStraightTransfer_apply w h hfin y]
    push_cast at hy'
    change -((j : ℝ) + 1) ≤ -y.re ∧ -y.re ≤ -(j : ℝ) ∧ _
    exact ⟨neg_le_neg hy'.2.1, neg_le_neg hy'.1, by rw [hseam]; ring⟩
  · intro hz
    have hxlo : (j : ℝ) ≤ -z.re := by
      linarith only [hz.2.1]
    have hxhi : -z.re ≤ (j + 1 : ℝ) := by
      have hj : (j : ℝ) + 1 = (j + 1 : ℝ) := by norm_num
      rw [← hj]
      linarith only [hz.1]
    have hXlo : seamX w h hfin j ≤ -z.re := by
      rw [hXj]
      exact hxlo
    have hXhi : -z.re ≤ seamX w h hfin (j + 1) := by
      rw [hXj1]
      exact hxhi
    obtain ⟨y, ⟨hy, hyr⟩, _⟩ := hvs.2 (-z.re) hXlo hXhi
    have hyg := (hg ▸ hy)
    rw [uibhbotGlue_seamX_eq_int w h hfin j,
      uibhbotGlue_seamX_eq_int w h hfin (j + 1)] at hyg
    have hseam : y.im = seamFun w h hfin y.re := by
      simpa only [Set.mem_ofPred_eq] using
        uibhbotAssembly_future_seam_graph w h hfin j true hy
    have htrans := futureStraightTransfer_apply w h hfin y
    have heq : uibhbotGlueFutureTransfer w h hfin y = z := by
      apply Complex.ext
      · rw [htrans]
        simp [hyr]
      · rw [htrans]
        simp [hseam, hz.2.2]
    rw [hFa (boundaryOuterEdge w h j, b)]
    refine ⟨y, ?_, heq⟩
    cases b with
    | true => exact hy
    | false =>
      have hr := P.arc_flip (boundaryOuterEdge w h j, true)
      change P.arc (boundaryOuterEdge w h j, false) = _ at hr
      rw [hr, Polyline.image_reverse_transfer]
      exact hy

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)

/-- Helper toward Definition 5.8. Both orientations of each past seam dart
have exactly the same complete trace as the attached past arc. -/
theorem uibhbotCcw_assembly_seam_trace (d : ℕ × Bool)
    (hd : kmswPastSeamEdge W d.1) :
    ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).arc
      (kmswPastDart W d)).image =
      uibhbotAssemblyHalfTurn '' (P.arc d).image := by
  obtain ⟨n, hn⟩ := hd
  obtain ⟨j, _, hmatch, hjw, hjt⟩ := uibhbotGlue_past_seam_match W h0 hR n d.1 hn
  have he : d.1 < (kmswStage (kmswPastCode W) n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge _ n).2
    simp only [List.mem_append] at hn ⊢
    tauto
  have hD : kmswPastDart W d = wholePlaneDartι W 0
      (boundaryOuterEdge (shiftedStream W 0) h0 j, !d.2) := by
    apply Prod.ext
    · change kmswPastEdge W d.1 = _
      exact hmatch
    · rfl
  let I := {z : ℂ | -((j : ℝ) + 1) ≤ z.re ∧ z.re ≤ -(j : ℝ) ∧ z.im = 0}
  have hpast := past_seam_trace_interval W hL hR hfin n d.1 he hn j hjw hjt
  have hfuture := future_seam_trace_interval (shiftedStream W 0) h0 (H.1 0) F hFa j (!d.2)
  rw [uibhbotCcw_assemblyDrawing_arc W H h0 hL hR hfin P hp ha F hf hFim hFa,
    hD, uibhbotAssemblyArc_future]
  have hPa : (uibhbotAssemblyHalfTurn '' (P.arc d).image) = I := by
    cases hb : d.2 with
    | false =>
      have hdEq : d = (d.1, false) := by cases d with | mk e b => cases b <;> simp_all
      rw [hdEq, ha (d.1, false)]
      have hArc : ((uibhbotPastMonotoneDrawing W hfin).arc (d.1, false)).image =
          (layoutArc (kmswPastCode W) n d.1).image := by
        rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n d.1 he false]
        simp only [Bool.false_eq_true, ite_false]
      rw [hArc]
      exact hpast
    | true =>
      have hdEq : d = (d.1, true) := by cases d with | mk e b => cases b <;> simp_all
      rw [hdEq, ha (d.1, true)]
      have hflip := (uibhbotPastMonotoneDrawing W hfin).arc_flip (d.1, false)
      change (uibhbotPastMonotoneDrawing W hfin).arc (d.1, true) = _ at hflip
      have hImg : ((uibhbotPastMonotoneDrawing W hfin).arc (d.1, true)).image =
          ((uibhbotPastMonotoneDrawing W hfin).arc (d.1, false)).image := by
        rw [hflip, Polyline.image_reverse_transfer]
      rw [hImg]
      have hArc : ((uibhbotPastMonotoneDrawing W hfin).arc (d.1, false)).image =
          (layoutArc (kmswPastCode W) n d.1).image := by
        rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n d.1 he false]
        simp only [Bool.false_eq_true, ite_false]
      rw [hArc]
      exact hpast
  rw [hPa]
  simpa only [I] using hfuture

end DirectedDistances.KMSW
