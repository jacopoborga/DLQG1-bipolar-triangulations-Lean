module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.MonotoneStepCommon
public import DirectedDistances.PlanarMap.GraphRegionSplice
public import DirectedDistances.PlanarMap.GraphRegionWedge

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

private theorem lfr_finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
  have hpos : 0 < p.points.length := by
    cases h : p.points with
    | nil => exact (p.nonempty h).elim
    | cons a as => simp
  by_cases hlen : p.points.length = 1
  · have hfin : p.finish = p.start := by
      rw [← Polyline.point_last_eq_finish, hlen]
      exact Polyline.point_zero_eq_start p
    exact Or.inl hfin
  · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
    unfold Polyline.segmentAt
    have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
    rw [hidx, Polyline.point_last_eq_finish]
    exact right_mem_segment ℝ _ _



theorem invariant_succ_lfr_counts (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]



theorem invariant_succ_lfr_stage_lists (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge ∧
      (kmswStage w (n + 1)).triangles =
        (kmswStage w n).triangles ++
          [( (kmswStage w n).active, (kmswStage w n).nextEdge,
              (kmswStage w n).nextEdge + 1)] ∧
      (kmswStage w (n + 1)).UL = [(kmswStage w n).nextEdge] ∧
      (kmswStage w (n + 1)).LL =
        ((kmswStage w n).nextEdge + 1) :: (kmswStage w n).LL ∧
      (kmswStage w (n + 1)).UR = (kmswStage w n).UR ∧
      (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]




theorem invariant_succ_lfr_old_UL (w : ℕ → Fin 3) (n : ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w n).UL = [(kmswStage w n).active] := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hdrop : (kmswStage w n).UL.dropLast = [] := by
    simpa using congrArg List.reverse hUL
  have hxsDrop : xs = (kmswStage w n).UL.dropLast := by
    rw [hxs]
    simp
  have hxsNil : xs = [] := hxsDrop.trans hdrop
  rw [hxs, hxsNil]
  rfl




theorem invariant_succ_lfr_active_trace_upper {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    (layoutArc w n (kmswStage w n).active).image ⊆
      graphOver G.xmin G.xmax G.upper := by
  intro z hz
  rw [G.upper_trace]
  apply mem_iUnion.mpr ⟨(kmswStage w n).active, ?_⟩
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hm : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by
    rw [hUL]
    simp
  apply mem_iUnion.mpr ⟨hm, ?_⟩
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).1
  simpa [stageEdgeTrace, hb, G.arc_layout, layoutDart] using hz




theorem invariant_succ_lfr_active_endpoints_upper {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
    let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    a ∈ graphOver G.xmin G.xmax G.upper ∧ b ∈ graphOver G.xmin G.xmax G.upper := by
  have he := (kmswStage_boundary_ids_lt_nextEdge w n).1
  constructor
  · apply invariant_succ_lfr_active_trace_upper G
    rw [← layoutArc_start w n _ he]
    exact Or.inl rfl
  · apply invariant_succ_lfr_active_trace_upper G
    rw [← layoutArc_finish w n _ he]
    exact lfr_finish_mem_image _




theorem invariant_succ_lfr_active_endpoint_values {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
    let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    a.re ∈ Icc G.xmin G.xmax ∧ a.im = G.upper a.re ∧
      b.re ∈ Icc G.xmin G.xmax ∧ b.im = G.upper b.re := by
  obtain ⟨ha, hb⟩ := invariant_succ_lfr_active_endpoints_upper G
  exact ⟨⟨ha.1, ha.2.1⟩, ha.2.2, ⟨hb.1, hb.2.1⟩, hb.2.2⟩




theorem invariant_succ_lfr_active_west_xmin {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re = G.xmin := by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  have hsingle : s.UL = [s.active] := invariant_succ_lfr_old_UL w n hUL
  have ha := invariant_succ_lfr_active_endpoints_upper G
  have hxmin : G.xmin ≤ a.re := ha.1.1
  have hboundList : ∀ e ∈ s.active :: s.UR, e < s.nextEdge := by
    intro e he
    have heUpper : e ∈ s.UL ++ s.UR := by simpa [hsingle] using he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at heUpper ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simpa [s] using heAll)
  have hchainBase : List.IsChain (fun e f => s.east e = s.west f)
      (s.UL ++ s.UR) := by
    exact (kmswStage_boundary_chain_invariant w n).1
  have hchain : List.IsChain (fun e f => s.east e = s.west f)
      (s.active :: s.UR) := by
    simpa [hsingle] using hchainBase
  have hrankChain : List.IsChain
      (fun e f => kmswStageRank w n (s.west e) < kmswStageRank w n (s.west f))
      (s.active :: s.UR) := by
    apply hchain.imp_of_mem_imp
    intro e f he _hf hef
    have hstrict := kmswStageRank_strict w n e (by simpa [s] using hboundList e he)
    change kmswStageRank w n (s.west e) < kmswStageRank w n (s.east e) at hstrict
    rw [hef] at hstrict
    exact hstrict
  let z : ℂ := ⟨G.xmin, G.upper G.xmin⟩
  have hz : z ∈ graphOver G.xmin G.xmax G.upper := by
    exact ⟨le_rfl, G.hx, by simp [z]⟩
  rw [G.upper_trace] at hz
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  obtain ⟨heUpper, hzTrace⟩ := mem_iUnion.mp he
  have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
    simp only [List.mem_append] at heUpper ⊢
    tauto
  have heBound : e < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simpa [s] using heAll)
  have htrace' : e < (kmswStage w n).nextEdge ∧
      z ∈ (layoutArc w n e).image := by
    simpa [stageEdgeTrace, s, G.arc_layout, layoutDart] using hzTrace
  have hzArc : z ∈ (layoutArc w n e).image := htrace'.2
  obtain ⟨f, hgraph⟩ := layoutArc_image_graph w n e (by simpa [s] using heBound)
  rw [hgraph] at hzArc
  have hxArc : (layoutPos w n (s.west e)).re ≤ z.re := hzArc.1
  have hrank : kmswStageRank w n (s.west s.active) ≤
      kmswStageRank w n (s.west e) := by
    have heUpper' : e ∈ s.UL ∨ e ∈ s.UR := by
      simpa only [List.mem_append] using heUpper
    have heCase : e = s.active ∨ e ∈ s.UR := by
      rcases heUpper' with heUL | heUR
      · exact Or.inl (by simpa [hsingle] using heUL)
      · exact Or.inr heUR
    rcases heCase with rfl | heUR
    · exact le_rfl
    · exact (hrankChain.rel_cons heUR).le
  have hrankReal : a.re ≤ (layoutPos w n (s.west e)).re := by
    change (kmswStageRank w n (s.west s.active) : ℝ) ≤
      (kmswStageRank w n (s.west e) : ℝ)
    exact_mod_cast hrank
  have hleft : a.re ≤ G.xmin := by
    have h := hrankReal.trans hxArc
    simpa [a, z] using h
  exact le_antisymm hleft hxmin



theorem invariant_succ_lfr_fresh_edge_membership (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w n).nextEdge ∈ freshEdges w n ∧
      (kmswStage w n).nextEdge + 1 ∈ freshEdges w n := by
  have hcount := invariant_succ_lfr_counts w n hc hUL
  simp [freshEdges, hcount]



theorem invariant_succ_lfr_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let s := kmswStage w n
    let s' := kmswStage w (n + 1)
    s'.west s.nextEdge = s.nextVertex ∧
      s'.east s.nextEdge = s.east s.active ∧
      s'.west (s.nextEdge + 1) = s.nextVertex ∧
      s'.east (s.nextEdge + 1) = s.west s.active ∧
      s'.present s.nextEdge = true ∧ s'.present (s.nextEdge + 1) = false := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]




theorem invariant_succ_lfr_new_vertex_rank (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).re + 1 =
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re := by
  have hgap := freshLeft_missing_edge_rank_gap w n hc hUL
  have hend := invariant_succ_lfr_endpoints w n hc hUL
  dsimp only at hend
  rcases hend with ⟨_, _, hwestMiss, heastMiss, _, _⟩
  dsimp only at hgap
  rw [heastMiss, hwestMiss] at hgap
  have hv := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  rw [layoutPos_old_vertex w n _ hv] at hgap
  linarith




theorem invariant_succ_lfr_new_vertex_xmin (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    x.re + 1 = G.xmin := by
  dsimp only
  calc
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).re + 1 =
        (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re :=
      invariant_succ_lfr_new_vertex_rank w n hc hUL
    _ = G.xmin := invariant_succ_lfr_active_west_xmin G hUL




theorem invariant_succ_lfr_new_vertex_height (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).im = (n + 1 : ℝ) := by
  have hg := (invariant_succ_lfr_counts w n hc hUL).2
  rw [layoutPos, layoutHeight_created_vertex w n hg]
  norm_cast




theorem invariant_succ_lfr_active_arc (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) (kmswStage w n).nextEdge =
      roofArc
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
          (kmswStage w n).nextEdge))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
          (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) := by
  have hm : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n _
    (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1]
  simp [hm]




theorem invariant_succ_lfr_missing_arc (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1) =
      segmentArc
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
          ((kmswStage w n).nextEdge + 1)))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
          ((kmswStage w n).nextEdge + 1))) := by
  have hm : isFreshLeftMissing w n ((kmswStage w n).nextEdge + 1) := by
    simp [isFreshLeftMissing, hc, hUL]
  rw [layoutArc_fresh w n _
    (invariant_succ_lfr_fresh_edge_membership w n hc hUL).2]
  simp [hm]




theorem invariant_succ_lfr_active_arc_image (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let a := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)
    let b := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)
    (layoutArc w (n + 1) (kmswStage w n).nextEdge).image =
      {z | a.re ≤ z.re ∧ z.re ≤ b.re ∧
        z.im = roofHeight a b (n + 1) (rampSlope w n) z.re} := by
  dsimp only
  rw [invariant_succ_lfr_active_arc w n hc hUL]
  have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  exact roofArc_image (rampSlope_pos w n)
    (freshEdges_endpoint_heights w n _ hf).1
    (freshEdges_endpoint_heights w n _ hf).2
    (freshEdges_ramp_widths_lt w n _ hf)




theorem invariant_succ_lfr_missing_arc_image (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let e := (kmswStage w n).nextEdge + 1
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    (layoutArc w (n + 1) e).image =
      {z | a.re ≤ z.re ∧ z.re ≤ b.re ∧ z.im = segmentHeight a b z.re} := by
  dsimp only
  rw [invariant_succ_lfr_missing_arc w n hc hUL]
  have hgap := freshLeft_missing_edge_rank_gap w n hc hUL
  dsimp only at hgap
  exact segmentArc_image (by linarith)




theorem invariant_succ_lfr_active_arc_height_le (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    ∀ z ∈ (layoutArc w (n + 1) (kmswStage w n).nextEdge).image,
      z.im ≤ (n + 1 : ℝ) := by
  intro z hz
  have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  have hm : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_image_fresh w n _ hf] at hz
  simp only [hm, ↓reduceIte] at hz
  rcases hz with ⟨_, _, hheight⟩
  rw [hheight]
  exact min_le_left _ _




theorem invariant_succ_lfr_missing_arc_height_le (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    ∀ z ∈ (layoutArc w (n + 1)
      ((kmswStage w n).nextEdge + 1)).image, z.im ≤ (n + 1 : ℝ) := by
  intro z hz
  have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).2
  have hm : isFreshLeftMissing w n ((kmswStage w n).nextEdge + 1) := by
    simp [isFreshLeftMissing, hc, hUL]
  rw [layoutArc_image_fresh w n _ hf] at hz
  simp only [hm, ↓reduceIte] at hz
  rcases hz with ⟨hx, _, hheight⟩
  let a := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1))
  let b := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1))
  have hgap : b.re - a.re = 1 := by
    have h := freshLeft_missing_edge_rank_gap w n hc hUL
    dsimp only at h
    exact h
  have hend := invariant_succ_lfr_endpoints w n hc hUL
  dsimp only at hend
  rcases hend with ⟨_, _, hwest, heast, _, _⟩
  have hA : a.im = (n + 1 : ℝ) := by
    dsimp [a]
    rw [hwest]
    exact invariant_succ_lfr_new_vertex_height w n hc hUL
  have hv := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hB : b.im ≤ (n : ℝ) := by
    dsimp [b]
    rw [heast, layoutPos_old_vertex w n _ hv]
    simpa [layoutPos] using layoutHeight_le w n _ hv
  rw [hheight]
  rw [segmentHeight]
  have hslope : (b.im - a.im) / (b.re - a.re) ≤ 0 := by
    rw [hgap, hA, div_one]
    linarith
  have hproduct : ((b.im - a.im) / (b.re - a.re)) * (z.re - a.re) ≤ 0 := by
    rw [mul_comm]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) hslope
  linarith

private theorem lfr_reverse_point (p : Polyline) (i : ℕ)
    (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.reverse.getD i p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_reverse i hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]

private theorem lfr_reverse_segment (p : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold Polyline.segmentAt
  rw [lfr_reverse_point p i (by omega), lfr_reverse_point p (i + 1) hi]
  have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [h₁, h₂, segment_symm]

private theorem lfr_reverse_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ lfr_finish_mem_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    rw [lfr_reverse_segment p i hi'] at hz
    exact Or.inr ⟨p.points.length - 2 - i, by omega, hz⟩

private theorem lfr_reverse_image (p : Polyline) :
    p.reverse.image = p.image := by
  apply Subset.antisymm (lfr_reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using lfr_reverse_image_subset p.reverse




theorem invariant_succ_lfr_image_height_le (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    ∀ z ∈ (monotoneLayoutDrawing w (n + 1) h).image,
      z.im ≤ (n + 1 : ℝ) := by
  intro z hz
  change z ∈ Set.range (fun v : Fin (kmswStage w (n + 1)).nextVertex =>
      layoutPos w (n + 1) v.val) ∪
    {z | ∃ d : StageDart (kmswStage w (n + 1)).nextEdge,
      z ∈ (layoutDart w (n + 1) d).image} at hz
  rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
  · by_cases hv : v.val < (kmswStage w n).nextVertex
    · change (layoutPos w (n + 1) v.val).im ≤ (n + 1 : ℝ)
      rw [layoutPos_old_vertex w n v.val hv]
      have hheight := layoutHeight_le w n v.val hv
      have hheight' : (layoutPos w n v.val).im ≤ (n : ℝ) := by
        simpa [layoutPos] using hheight
      have hnext : (n : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.le_succ n
      exact hheight'.trans hnext
    · have hcounts := invariant_succ_lfr_counts w n hc hUL
      have hvEq : v.val = (kmswStage w n).nextVertex := by omega
      change layoutHeight w (n + 1) v.val ≤ (n + 1 : ℝ)
      rw [hvEq, layoutHeight_created_vertex w n hcounts.2]
      norm_num [Nat.cast_add, Nat.cast_one]
  · let e := d.1.val
    by_cases ho : e < (kmswStage w n).nextEdge
    · let dOld : StageDart (kmswStage w n).nextEdge := (⟨e, ho⟩, d.2)
      have ho' : d.1.val < (kmswStage w n).nextEdge := by simpa [e] using ho
      have hArc : layoutDart w (n + 1) d = P.arc dOld := by
        have hOld : layoutDart w (n + 1) d = layoutDart w n dOld := by
          unfold layoutDart
          rw [layoutArc_old w n d.1.val ho']
        rw [hOld]
        exact (G.arc_layout dOld).symm
      rw [hArc] at hz
      have hzP : z ∈ P.image := Or.inr ⟨dOld, hz⟩
      have hzBound := G.image_height_le z hzP
      have hn : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
      exact hzBound.trans hn
    · have hlow : (kmswStage w n).nextEdge ≤ e := Nat.le_of_not_gt ho
      have hcount := invariant_succ_lfr_counts w n hc hUL
      have heLt : e < (kmswStage w n).nextEdge + 2 := by
        simpa [hcount.1] using d.1.isLt
      have _hlow : (kmswStage w n).nextEdge ≤ e := hlow
      have hfresh : e = (kmswStage w n).nextEdge ∨
          e = (kmswStage w n).nextEdge + 1 := by omega
      have hzArc : z ∈ (layoutArc w (n + 1) e).image := by
        cases hd : d.2
        · simpa [layoutDart, e, hd] using hz
        · simpa [layoutDart, e, hd, lfr_reverse_image] using hz
      rcases hfresh with heq | heq
      · rw [heq] at hzArc
        exact invariant_succ_lfr_active_arc_height_le w n hc hUL z hzArc
      · rw [heq] at hzArc
        exact invariant_succ_lfr_missing_arc_height_le w n hc hUL z hzArc




theorem invariant_succ_lfr_pos_layout (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 0) (_hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (_G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      (monotoneLayoutDrawing w (n + 1) h).pos v =
        layoutPos w (n + 1) v.val := by
  intro v
  rfl




theorem invariant_succ_lfr_arc_layout (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 0) (_hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (_G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      (monotoneLayoutDrawing w (n + 1) h).arc d = layoutDart w (n + 1) d := by
  intro d
  rfl

private theorem continuousOn_prefix {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc c b))
    (hjoin : f c = g c) :
    ContinuousOn (fun x => if x ≤ c then f x else g x) (Icc a b) := by
  apply ContinuousOn.if
  · intro x hx
    have hxc : x = c := by
      simpa only [mem_singleton_iff] using frontier_Iic_subset c hx.2
    simpa only [hxc, ite_eq_left le_rfl] using hjoin
  · exact hf.mono inter_subset_left
  · apply hg.mono
    intro x hx
    have hcx : c ≤ x := by
      have hclosure : closure {x : ℝ | ¬ x ≤ c} ⊆ Ici c := by
        apply closure_minimal
        · intro y hy
          exact (lt_of_not_ge hy).le
        · exact isClosed_Ici
      exact hclosure hx.2
    exact ⟨hcx, hx.1.2⟩




theorem invariant_succ_lfr_lower_at_active_west {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let s := kmswStage w n
    G.lower (layoutPos w n (s.west s.active)).re =
      (layoutPos w n (s.west s.active)).im := by
  let s := kmswStage w n
  have hULs : s.UL = [s.active] := by
    simpa [s] using invariant_succ_lfr_old_UL w n hUL
  have hne := kmswStage_boundary_nonempty w n
  let e := (s.LL ++ s.LR).head hne.2
  have heMem : e ∈ s.LL ++ s.LR := List.head_mem _
  have heBound : e < s.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at heMem ⊢
    tauto
  have hhead : ((s.UL ++ s.UR).head hne.1) = s.active := by
    simp only [hULs, List.singleton_append, List.head_cons]
  have hvertex : s.west e = s.west s.active := by
    have hend := (kmswStage_boundary_endpoints w n).1
    rw [hhead] at hend
    exact hend.symm
  let z := layoutPos w n (s.west e)
  have hz : z ∈ (layoutArc w n e).image := by
    change layoutPos w n (s.west e) ∈ (layoutArc w n e).image
    rw [← layoutArc_start w n e heBound]
    exact Or.inl rfl
  have hval := G.lower_eq_arc_height heMem hz
  have hpos : z = layoutPos w n (s.west s.active) := by
    simp only [z, hvertex]
  simpa only [hpos] using hval




@[expose] noncomputable def invariant_succ_lfr_lower (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 0) (_hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : ℝ → ℝ := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  exact fun r => if r ≤ u.re then segmentHeight x u r else G.lower r




@[expose] noncomputable def invariant_succ_lfr_upper (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 0) (_hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : ℝ → ℝ := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let v := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  exact fun r => if r ≤ v.re then roofHeight x v (n + 1) (rampSlope w n) r
    else G.upper r




theorem invariant_succ_lfr_lower_continuous (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    ContinuousOn (invariant_succ_lfr_lower w n hc hUL G)
      (Icc x.re G.xmax) := by
  dsimp only [invariant_succ_lfr_lower]
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hxmin : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hlt : x.re < u.re := by linarith
  have hxmax : x.re ≤ G.xmax := by
    calc
      x.re ≤ u.re := hlt.le
      _ = G.xmin := hxmin
      _ ≤ G.xmax := G.hx
  have hjoin : segmentHeight x u u.re = G.lower u.re := by
    rw [invariant_succ_lfr_lower_at_active_west G hUL]
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    field_simp [hden]
    ring
  have hseg : ContinuousOn (segmentHeight x u) (Icc x.re G.xmax) := by
    have hcont : Continuous (segmentHeight x u) := by
      unfold segmentHeight
      fun_prop
    exact hcont.continuousOn
  have hold : ContinuousOn G.lower (Icc u.re G.xmax) := by
    rw [hxmin]
    exact G.lower_continuous
  exact continuousOn_prefix hseg hold hjoin




theorem invariant_succ_lfr_upper_continuous (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    ContinuousOn (invariant_succ_lfr_upper w n hc hUL G)
      (Icc x.re G.xmax) := by
  dsimp only [invariant_succ_lfr_upper]
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let v := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  have hxu : x.re + 1 =
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re :=
    invariant_succ_lfr_new_vertex_rank w n hc hUL
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  have hxmin : (layoutPos w n
      ((kmswStage w n).west (kmswStage w n).active)).re = G.xmin :=
    invariant_succ_lfr_active_west_xmin G hUL
  have huv : u.re < v.re := by
    have hrank := kmswStageRank_strict w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast hrank
  have hlt : x.re < v.re := by linarith [hxu, huv]
  have hvdom := (invariant_succ_lfr_active_endpoint_values G).2.2.1
  have hmax : v.re ≤ G.xmax := hvdom.2
  have hxmax : x.re ≤ G.xmax := hlt.le.trans hmax
  have hend := invariant_succ_lfr_endpoints w n hc hUL
  dsimp only at hend
  rcases hend with ⟨_, heast, _, _, _, _⟩
  have hOldVertex : (kmswStage w n).east (kmswStage w n).active <
      (kmswStage w n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hvpos : layoutPos w (n + 1) ((kmswStage w (n + 1)).east
      (kmswStage w n).nextEdge) = v := by
    rw [heast, layoutPos_old_vertex w n _ hOldVertex]
  have hnewLeft : layoutPos w (n + 1) ((kmswStage w (n + 1)).west
      (kmswStage w n).nextEdge) = x := by
    have hw := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hw
    rcases hw with ⟨hwest, _, _, _, _, _⟩
    rw [hwest]
  have hjoin : roofHeight x v (n + 1) (rampSlope w n) v.re = G.upper v.re := by
    have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
    have hends := freshEdges_endpoint_heights w n _ hf
    rw [hnewLeft, hvpos] at hends
    have hfit := freshEdges_ramp_widths_lt w n _ hf
    rw [hnewLeft, hvpos] at hfit
    rw [(invariant_succ_lfr_active_endpoint_values G).2.2.2.symm]
    exact roofHeight_finish (rampSlope_pos w n) hends.1 hends.2 hfit
  have hroof : ContinuousOn (roofHeight x v (n + 1) (rampSlope w n))
      (Icc x.re G.xmax) := by
    exact (continuous_roofHeight x v (n + 1) (rampSlope w n)).continuousOn
  have hold : ContinuousOn G.upper (Icc v.re G.xmax) := by
    exact G.upper_continuous.mono (by
      intro r hr
      exact ⟨hvdom.1.trans hr.1, hr.2⟩)
  exact continuousOn_prefix hroof hold hjoin




theorem invariant_succ_lfr_lower_le_upper (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    ∀ r ∈ Icc x.re G.xmax,
      invariant_succ_lfr_lower w n hc hUL G r ≤
        invariant_succ_lfr_upper w n hc hUL G r := by
  dsimp only
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  let v := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hxmin : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have huv : u.re < v.re := by
    have hrank := kmswStageRank_strict w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast hrank
  have hlt : x.re < u.re := by linarith
  have hvals := invariant_succ_lfr_active_endpoint_values G
  rcases hvals with ⟨huDom, huVal, hvDom, hvVal⟩
  have huVal' : u.im = G.upper u.re := by simpa [u] using huVal
  have hvVal' : v.im = G.upper v.re := by simpa [v] using hvVal
  have huDom' : u.re ∈ Icc G.xmin G.xmax := by simpa [u] using huDom
  have hvDom' : v.re ∈ Icc G.xmin G.xmax := by simpa [v] using hvDom
  have huHeight : u.im ≤ (n : ℝ) :=
    huVal'.trans_le (G.upper_le_stage (by simpa only [hxmin] using huDom'))
  have hvHeight : v.im ≤ (n : ℝ) :=
    hvVal'.trans_le (G.upper_le_stage hvDom')
  have hNewHeight : x.im = (n + 1 : ℝ) := by
    exact invariant_succ_lfr_new_vertex_height w n hc hUL
  have hneweq : layoutPos w (n + 1) ((kmswStage w (n + 1)).west
      (kmswStage w n).nextEdge) = x := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨hwest, _, _, _, _, _⟩
    rw [hwest]
  have holdvertex : (kmswStage w n).east (kmswStage w n).active <
      (kmswStage w n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hvEq : layoutPos w (n + 1) ((kmswStage w (n + 1)).east
      (kmswStage w n).nextEdge) = v := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨_, heast, _, _, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ holdvertex]
  have hfresh := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  have hEnds := freshEdges_endpoint_heights w n _ hfresh
  rw [hneweq, hvEq] at hEnds
  have hFit := freshEdges_ramp_widths_lt w n _ hfresh
  rw [hneweq, hvEq] at hFit
  have hRoofEnd : roofHeight x v (n + 1) (rampSlope w n) v.re =
      G.upper v.re := by
    exact (roofHeight_finish (rampSlope_pos w n) hEnds.1 hEnds.2 hFit).trans
      hvVal'
  have huSep : G.upper u.re ≤ u.im := huVal'.symm.le
  have hvSep : G.upper v.re ≤ v.im := hvVal'.symm.le
  have hSep := G.upper_lt_roofHeight huDom' hvDom' huSep hvSep
  have hRoofMono : ∀ r ∈ Icc u.re v.re,
      roofHeight u v (n + 1) (rampSlope w n) r ≤
        roofHeight x v (n + 1) (rampSlope w n) r := by
    intro r hr
    have hleft : u.im + rampSlope w n * (r - u.re) ≤
        x.im + rampSlope w n * (r - x.re) := by
      have hgap : u.re - x.re = 1 := by linarith [hxu]
      have hcoord : r - x.re = (r - u.re) + 1 := by linarith [hxu]
      have hmul : rampSlope w n * (r - x.re) =
          rampSlope w n * (r - u.re) + rampSlope w n := by
        rw [hcoord, mul_add, mul_one]
      rw [hNewHeight, hmul]
      nlinarith [rampSlope_pos w n]
    unfold roofHeight
    exact min_le_min le_rfl (min_le_min hleft le_rfl)
  obtain ⟨L, hL0, hLM, hLip⟩ := G.upper_lipschitz_margin
  have hUpperLipschitz : |u.im - v.im| ≤ L * |u.re - v.re| := by
    have h := hLip u.re huDom' v.re hvDom'
    rw [← huVal', ← hvVal'] at h
    exact h
  have hUpperGap : u.im ≤ v.im + rampSlope w n * (v.re - u.re) := by
    have habs : u.im - v.im ≤ L * (v.re - u.re) := by
      have h := (le_abs_self (u.im - v.im)).trans hUpperLipschitz
      simpa [abs_of_nonpos (sub_nonpos.mpr huv.le)] using h
    have hLM' := mul_le_mul_of_nonneg_right hLM.le (sub_nonneg.mpr huv.le)
    nlinarith
  have hMissingLeft : layoutPos w (n + 1) ((kmswStage w (n + 1)).west
      ((kmswStage w n).nextEdge + 1)) = x := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨_, _, hwest, _, _, _⟩
    rw [hwest]
  have holdWest : (kmswStage w n).west (kmswStage w n).active <
      (kmswStage w n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hMissingRight : layoutPos w (n + 1) ((kmswStage w (n + 1)).east
      ((kmswStage w n).nextEdge + 1)) = u := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨_, _, _, heast, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ holdWest]
  have hMissingSlope :
      |(u.im - x.im) / (u.re - x.re)| < rampSlope w n := by
    have h := freshLeft_missing_edge_slope_lt w n n hc hUL le_rfl
    dsimp only at h
    rw [hMissingLeft, hMissingRight] at h
    simpa only [abs_div, abs_of_pos (sub_pos.mpr hlt)] using h
  have hden : 0 < u.re - x.re := sub_pos.mpr hlt
  have hSegmentAtU : segmentHeight x u u.re = u.im := by
    unfold segmentHeight
    field_simp [ne_of_gt hden]
    ring
  have hSegmentLeRoof : ∀ r ∈ Icc x.re u.re,
      segmentHeight x u r ≤ roofHeight x v (n + 1) (rampSlope w n) r := by
    intro r hr
    let slope := (u.im - x.im) / (u.re - x.re)
    have hslope := abs_lt.mp hMissingSlope
    have hslopeNeg : slope < 0 := by
      dsimp [slope]
      rw [hNewHeight]
      exact div_neg_of_neg_of_pos (by linarith [huHeight]) hden
    have hsegH : segmentHeight x u r ≤ x.im := by
      have hprod := mul_nonpos_of_nonpos_of_nonneg hslopeNeg.le
        (sub_nonneg.mpr hr.1)
      unfold segmentHeight
      dsimp [slope] at hprod
      linarith
    have hsegLeft : segmentHeight x u r ≤
        x.im + rampSlope w n * (r - x.re) := by
      have hprod := mul_le_mul_of_nonneg_right hslope.2.le
        (sub_nonneg.mpr hr.1)
      unfold segmentHeight
      linarith
    have hcoeff : -rampSlope w n - slope ≤ 0 := by linarith [hslope.1]
    have hprod : 0 ≤ (-rampSlope w n - slope) * (r - u.re) :=
      mul_nonneg_of_nonpos_of_nonpos hcoeff (sub_nonpos.mpr hr.2)
    have hidentity : v.im + rampSlope w n * (v.re - r) -
        segmentHeight x u r =
          (v.im + rampSlope w n * (v.re - u.re) - u.im) +
            (-rampSlope w n - slope) * (r - u.re) := by
      unfold segmentHeight
      dsimp [slope]
      field_simp [ne_of_gt hden]
      ring
    have hsegRight : segmentHeight x u r ≤
        v.im + rampSlope w n * (v.re - r) := by
      linarith [hUpperGap, hprod, hidentity]
    unfold roofHeight
    exact le_min (by simpa [hNewHeight] using hsegH)
      (le_min (by simpa [hNewHeight] using hsegLeft) hsegRight)
  intro r hr
  change (if r ≤ u.re then segmentHeight x u r else G.lower r) ≤
    (if r ≤ v.re then roofHeight x v (n + 1) (rampSlope w n) r else G.upper r)
  by_cases hru : r ≤ u.re
  · have hrv : r ≤ v.re := hru.trans huv.le
    simp only [ite_eq_left hru, ite_eq_left hrv]
    exact hSegmentLeRoof r ⟨hr.1, hru⟩
  · have hdom : r ∈ Icc G.xmin G.xmax := by
      exact ⟨by rw [← hxmin]; exact le_of_not_ge hru, hr.2⟩
    have hlow := G.lower_le_upper r hdom
    by_cases hrv : r ≤ v.re
    · simp only [ite_eq_right hru, ite_eq_left hrv]
      rcases eq_or_lt_of_le hrv with heq | hltv
      · subst r
        exact hlow.trans (hRoofEnd.symm.le)
      · have hrOpen : r ∈ Ioo u.re v.re := ⟨lt_of_not_ge hru, hltv⟩
        have hSep' := hSep r hrOpen
        have hroofCmp := hRoofMono r ⟨hrOpen.1.le, hrOpen.2.le⟩
        exact hlow.trans (hSep'.trans_le hroofCmp).le
    · simp only [ite_eq_right hru, ite_eq_right hrv]
      exact hlow




theorem invariant_succ_lfr_trace_old (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e = stageEdgeTrace P e := by
  have he' : e < (kmswStage w (n + 1)).nextEdge := by
    rw [(invariant_succ_lfr_counts w n hc hUL).1]
    omega
  have hArc : (monotoneLayoutDrawing w (n + 1) h).arc
      ((⟨e, he'⟩, false) : StageDart (kmswStage w (n + 1)).nextEdge) =
        P.arc ((⟨e, he⟩, false) : StageDart (kmswStage w n).nextEdge) := by
    rw [invariant_succ_lfr_arc_layout w n hc hUL G h]
    rw [G.arc_layout]
    simp only [layoutDart, Bool.false_eq_true, ↓reduceIte,
      layoutArc_old w n e he]
  unfold stageEdgeTrace
  simp only [he, he', ↓reduceDIte, hArc]




theorem invariant_succ_lfr_trace_active (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (h : LayoutGood w (n + 1)) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge =
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
  have he := (invariant_succ_lfr_counts w n hc hUL).1
  have hlt : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
    rw [he]
    omega
  simp only [stageEdgeTrace, hlt, ↓reduceDIte, monotoneLayoutDrawing, layoutDart,
    Bool.false_eq_true, ↓reduceIte]




theorem invariant_succ_lfr_trace_missing (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (h : LayoutGood w (n + 1)) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
      ((kmswStage w n).nextEdge + 1) =
      (layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1)).image := by
  have he := (invariant_succ_lfr_counts w n hc hUL).1
  have hlt : (kmswStage w n).nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by
    rw [he]
    omega
  simp only [stageEdgeTrace, hlt, ↓reduceDIte, monotoneLayoutDrawing, layoutDart,
    Bool.false_eq_true, ↓reduceIte]

private theorem graphOver_prefix {a b c : ℝ} {f g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hjoin : f c = g c) :
    graphOver a b (fun x => if x ≤ c then f x else g x) =
      graphOver a c f ∪ graphOver c b g := by
  ext z
  constructor
  · rintro ⟨ha, hb, hz⟩
    by_cases hzc : z.re ≤ c
    · left
      refine ⟨ha, hzc, ?_⟩
      simpa only [ite_eq_left hzc] using hz
    · right
      have hcz : c ≤ z.re := le_of_not_ge hzc
      refine ⟨hcz, hb, ?_⟩
      simpa only [ite_eq_right hzc] using hz
  · rintro (⟨ha, hc, hz⟩ | ⟨hc, hb, hz⟩)
    · refine ⟨ha, hc.trans hcb, ?_⟩
      simpa only [ite_eq_left hc] using hz
    · refine ⟨hac.trans hc, hb, ?_⟩
      by_cases hzc : z.re ≤ c
      · have heq : z.re = c := le_antisymm hzc hc
        have hzf : z.im = f z.re := by
          calc
            z.im = g z.re := hz
            _ = f z.re := by rw [heq]; exact hjoin.symm
        simpa only [ite_eq_left hzc] using hzf
      · simpa only [ite_eq_right hzc] using hz

private theorem graphOver_cons_iUnion {α : Type*} {β : Type*}
    (a : α) (l : List α) (f : α → Set β) :
    (⋃ x ∈ a :: l, f x) = f a ∪ ⋃ x ∈ l, f x := by
  ext z
  simp [Set.mem_iUnion, List.mem_cons]




theorem invariant_succ_lfr_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    graphOver x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G) =
      ⋃ e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let s := kmswStage w n
  let s' := kmswStage w (n + 1)
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  have hlists := invariant_succ_lfr_stage_lists w n hc hUL
  rcases hlists with ⟨_, _, _, hLL, _, hLR⟩
  have hxmin : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hlt : x.re < u.re := by
    have hrank := invariant_succ_lfr_new_vertex_rank w n hc hUL
    linarith
  have hjoin : segmentHeight x u u.re = G.lower u.re := by
    rw [invariant_succ_lfr_lower_at_active_west G hUL]
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    field_simp [hden]
    ring
  have hcb : u.re ≤ G.xmax := by
    calc
      u.re = G.xmin := hxmin
      _ ≤ G.xmax := G.hx
  have hprefix := graphOver_prefix (a := x.re) (b := G.xmax) (c := u.re)
    (f := segmentHeight x u) (g := G.lower) hlt.le hcb hjoin
  have hMissLeft : layoutPos w (n + 1) (s'.west (s.nextEdge + 1)) = x := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨_, _, hwest, _, _, _⟩
    rw [hwest]
  have hOldWest : s.west s.active < s.nextVertex := by
    exact (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hMissRight : layoutPos w (n + 1) (s'.east (s.nextEdge + 1)) = u := by
    have hend := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at hend
    rcases hend with ⟨_, _, _, heast, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldWest]
  have hMissImage := invariant_succ_lfr_missing_arc_image w n hc hUL
  dsimp only at hMissImage
  rw [hMissLeft, hMissRight] at hMissImage
  have hMissTrace := invariant_succ_lfr_trace_missing w n hc hUL h
  have hSegTrace : graphOver x.re u.re (segmentHeight x u) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) := by
    calc
      graphOver x.re u.re (segmentHeight x u) =
          (layoutArc w (n + 1) (s.nextEdge + 1)).image := by
            simpa only [graphOver] using hMissImage.symm
      _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) :=
        hMissTrace.symm
  have hOldBound : ∀ e, e ∈ s.LL ++ s.LR → e < s.nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at he ⊢
    tauto
  have hUnion :
      (⋃ e ∈ s'.LL ++ s'.LR, stageEdgeTrace
        (monotoneLayoutDrawing w (n + 1) h) e) =
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) ∪
          ⋃ e ∈ s.LL ++ s.LR, stageEdgeTrace P e := by
    rw [hLL, hLR]
    simp only [List.cons_append]
    rw [graphOver_cons_iUnion]
    rw [invariant_succ_lfr_trace_missing w n hc hUL h]
    have hOldUnion :
        (⋃ e ∈ s.LL ++ s.LR, stageEdgeTrace
          (monotoneLayoutDrawing w (n + 1) h) e) =
          ⋃ e ∈ s.LL ++ s.LR, stageEdgeTrace P e := by
      ext z
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨e, he, hz⟩
        have heBound := hOldBound e he
        have htrace := invariant_succ_lfr_trace_old w n hc hUL G h e heBound
        exact ⟨e, he, htrace.symm ▸ hz⟩
      · rintro ⟨e, he, hz⟩
        have heBound := hOldBound e he
        have htrace := invariant_succ_lfr_trace_old w n hc hUL G h e heBound
        exact ⟨e, he, htrace ▸ hz⟩
    exact congrArg (fun S : Set ℂ => (layoutArc w (n + 1)
      (s.nextEdge + 1)).image ∪ S) hOldUnion
  calc
    graphOver x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G) =
        graphOver x.re u.re (segmentHeight x u) ∪
          graphOver u.re G.xmax G.lower := by
            simpa only [invariant_succ_lfr_lower] using hprefix
    _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) ∪
          ⋃ e ∈ s.LL ++ s.LR, stageEdgeTrace P e := by
            rw [hSegTrace, hxmin, G.lower_trace]
    _ = ⋃ e ∈ s'.LL ++ s'.LR,
          stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := hUnion.symm

private theorem lfr_chain_head_east_le_tail_west (W E : ℕ → ℚ) (a : ℕ)
    (es : List ℕ)
    (hc : List.IsChain (fun e f => E e = W f) (a :: es))
    (hstrict : ∀ e ∈ a :: es, W e < E e) :
    ∀ e ∈ es, E a ≤ W e := by
  induction es generalizing a with
  | nil => simp
  | cons b bs ih =>
    intro e he
    have hab : E a = W b := hc.rel_head? (by simp)
    rcases List.mem_cons.mp he with rfl | he
    · exact hab.le
    · have htail := ih b hc.tail (fun f hf => hstrict f (by simp [hf])) e
        (by simp [he])
      exact (calc
        E a = W b := hab
        _ < E b := hstrict b (by simp)
        _ ≤ W e := htail).le



theorem invariant_succ_lfr_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    graphOver x.re G.xmax (invariant_succ_lfr_upper w n hc hUL G) =
      ⋃ e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let s := kmswStage w n
  let s' := kmswStage w (n + 1)
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  have hLists := invariant_succ_lfr_stage_lists w n hc hUL
  rcases hLists with ⟨_, _, hUL', _, hUR', _⟩
  have hOldUL : s.UL = [s.active] := invariant_succ_lfr_old_UL w n hUL
  have hxmin : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hltUV : u.re < v.re := by
    change (kmswStageRank w n (s.west s.active) : ℝ) <
      (kmswStageRank w n (s.east s.active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hltXV : x.re < v.re := by linarith
  have hvdom := (invariant_succ_lfr_active_endpoint_values G).2.2.1
  have hvmax : v.re ≤ G.xmax := hvdom.2
  have hnewLeft : layoutPos w (n + 1) (s'.west s.nextEdge) = x := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨hwest, _, _, _, _, _⟩
    rw [hwest]
  have hOldEast : s.east s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hnewRight : layoutPos w (n + 1) (s'.east s.nextEdge) = v := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, heast, _, _, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldEast]
  have hfresh := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  have hEnds := freshEdges_endpoint_heights w n s.nextEdge hfresh
  rw [hnewLeft, hnewRight] at hEnds
  have hFit := freshEdges_ramp_widths_lt w n s.nextEdge hfresh
  rw [hnewLeft, hnewRight] at hFit
  have hRoofJoin : roofHeight x v (n + 1) (rampSlope w n) v.re = G.upper v.re := by
    rw [(invariant_succ_lfr_active_endpoint_values G).2.2.2.symm]
    exact roofHeight_finish (rampSlope_pos w n) hEnds.1 hEnds.2 hFit
  have hPrefix := graphOver_prefix (a := x.re) (b := G.xmax) (c := v.re)
    (f := roofHeight x v (n + 1) (rampSlope w n)) (g := G.upper)
    hltXV.le hvmax hRoofJoin
  have hActiveImage := invariant_succ_lfr_active_arc_image w n hc hUL
  dsimp only at hActiveImage
  rw [hnewLeft, hnewRight] at hActiveImage
  have hActiveTrace := invariant_succ_lfr_trace_active w n hc hUL h
  have hRoofTrace : graphOver x.re v.re
      (roofHeight x v (n + 1) (rampSlope w n)) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge := by
    calc
      graphOver x.re v.re (roofHeight x v (n + 1) (rampSlope w n)) =
          (layoutArc w (n + 1) s.nextEdge).image := by
            simpa only [graphOver] using hActiveImage.symm
      _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge :=
        hActiveTrace.symm
  have hChain : List.IsChain (fun e f => s.east e = s.west f)
      (s.active :: s.UR) := by
    simpa only [s, hOldUL, List.singleton_append] using kmswStage_upper_chain w n
  have hStrict : ∀ e ∈ s.active :: s.UR,
      kmswStageRank w n (s.west e) < kmswStageRank w n (s.east e) := by
    intro e he
    have heUpper : e ∈ s.UL ++ s.UR := by
      simpa only [hOldUL, List.singleton_append, List.mem_cons] using he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at heUpper ⊢
      tauto
    exact kmswStageRank_strict w n e
      ((kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simpa [s] using heAll))
  have hRankChain : List.IsChain
      (fun e f => kmswStageRank w n (s.east e) = kmswStageRank w n (s.west f))
      (s.active :: s.UR) := by
    exact hChain.imp (fun e f he => congrArg (kmswStageRank w n) he)
  have hURPost :
      (⋃ e ∈ s.UR, stageEdgeTrace P e) ⊆ graphOver v.re G.xmax G.upper := by
    intro z hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    obtain ⟨heUR, hz⟩ := mem_iUnion.mp he
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
        simp only [List.mem_append] at heUR ⊢
        tauto
      simpa [s] using heAll)
    have hRank := lfr_chain_head_east_le_tail_west
      (fun e => kmswStageRank w n (s.west e))
      (fun e => kmswStageRank w n (s.east e)) s.active s.UR hRankChain hStrict e heUR
    have hWest : v.re ≤ (layoutPos w n (s.west e)).re := by
      change (kmswStageRank w n (s.east s.active) : ℝ) ≤
        (kmswStageRank w n (s.west e) : ℝ)
      exact_mod_cast hRank
    have hzArc : z ∈ (layoutArc w n e).image := by
      unfold stageEdgeTrace at hz
      rw [dite_eq_left heBound] at hz
      simpa [G.arc_layout, layoutDart] using hz
    have heUpper : e ∈ s.UL ++ s.UR := by simp [heUR]
    have hzUpper : G.upper z.re = z.im := G.upper_eq_arc_height heUpper hzArc
    obtain ⟨f, hf⟩ := layoutArc_image_graph w n e heBound
    rw [hf] at hzArc
    have hzOld : z ∈ graphOver G.xmin G.xmax G.upper := by
      rw [G.upper_trace]
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨heUpper, hz⟩⟩
    exact ⟨hWest.trans hzArc.1, hzOld.2.1, hzUpper.symm⟩
  have hOldActiveRight : ∀ z ∈ stageEdgeTrace P s.active, z.re ≤ v.re := by
    intro z hz
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).1
    have hzArc : z ∈ (layoutArc w n s.active).image := by
      unfold stageEdgeTrace at hz
      rw [dite_eq_left heBound] at hz
      simpa [G.arc_layout, layoutDart] using hz
    obtain ⟨f, hf⟩ := layoutArc_image_graph w n s.active heBound
    rw [hf] at hzArc
    simpa [v] using hzArc.2.1
  have hPostCover : graphOver v.re G.xmax G.upper ⊆
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge ∪
        ⋃ e ∈ s.UR, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
    intro z hz
    have hzOld : z ∈ graphOver G.xmin G.xmax G.upper := by
      refine ⟨?_, ?_, hz.2.2⟩
      · exact hvdom.1.trans hz.1
      · exact hz.2.1
    rw [G.upper_trace] at hzOld
    obtain ⟨e, he⟩ := mem_iUnion.mp hzOld
    obtain ⟨heUpper, heTrace⟩ := mem_iUnion.mp he
    have heCase : e = s.active ∨ e ∈ s.UR := by
      rw [hOldUL] at heUpper
      simpa only [List.singleton_append, List.mem_cons] using heUpper
    rcases heCase with rfl | heUR
    · have hzActive : z ∈ stageEdgeTrace P s.active := by
        exact heTrace
      have hRight := hOldActiveRight z hzActive
      have hzEq : z.re = v.re := le_antisymm hRight hz.1
      have hzRoof : z ∈ graphOver x.re v.re
          (roofHeight x v (n + 1) (rampSlope w n)) := by
        refine ⟨?_, hzEq.le, ?_⟩
        · rw [hzEq]
          exact hltXV.le
        calc
          z.im = G.upper z.re := hz.2.2
          _ = G.upper v.re := by rw [hzEq]
          _ = roofHeight x v (n + 1) (rampSlope w n) v.re := hRoofJoin.symm
          _ = roofHeight x v (n + 1) (rampSlope w n) z.re := by rw [hzEq]
      left
      rw [← hRoofTrace]
      exact hzRoof
    · right
      have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
          simp only [List.mem_append] at heUR ⊢
          tauto
        simpa [s] using heAll)
      have htrace := invariant_succ_lfr_trace_old w n hc hUL G h e heBound
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨heUR, htrace.symm ▸ heTrace⟩⟩
  have hUnionEq :
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge ∪
          graphOver v.re G.xmax G.upper =
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge ∪
          ⋃ e ∈ s.UR, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · exact Or.inl hz
      · exact hPostCover hz
    · rintro z (hz | hz)
      · exact Or.inl hz
      · obtain ⟨e, he⟩ := mem_iUnion.mp hz
        obtain ⟨heUR, hz⟩ := mem_iUnion.mp he
        have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
          have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
            simp only [List.mem_append] at heUR ⊢
            tauto
          simpa [s] using heAll)
        have htrace := invariant_succ_lfr_trace_old w n hc hUL G h e heBound
        have hzOld : z ∈ stageEdgeTrace P e := htrace.symm ▸ hz
        exact Or.inr (hURPost (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨heUR, hzOld⟩⟩))
  rw [hUL', hUR']
  rw [List.singleton_append, graphOver_cons_iUnion]
  calc
    graphOver x.re G.xmax (invariant_succ_lfr_upper w n hc hUL G) =
        graphOver x.re v.re (roofHeight x v (n + 1) (rampSlope w n)) ∪
          graphOver v.re G.xmax G.upper := hPrefix
    _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge ∪
          graphOver v.re G.xmax G.upper := by rw [hRoofTrace]
    _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge ∪
          ⋃ e ∈ s.UR, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := hUnionEq



@[expose] noncomputable def invariant_succ_lfr_cap_lower (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 0) (_hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : ℝ → ℝ := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  exact fun r => if r ≤ u.re then segmentHeight x u r else G.upper r



@[expose] noncomputable def invariant_succ_lfr_new_cap (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : GraphCap := by
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hltXu : x.re < u.re := by linarith
  have hltUv : u.re < v.re := by
    change (kmswStageRank w n (s.west s.active) : ℝ) <
      (kmswStageRank w n (s.east s.active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hltXv : x.re < v.re := hltXu.trans hltUv
  have hValues := invariant_succ_lfr_active_endpoint_values G
  have huDom : u.re ∈ Icc G.xmin G.xmax := by simpa [u] using hValues.1
  have huVal : u.im = G.upper u.re := by simpa [u] using hValues.2.1
  have hvDom : v.re ∈ Icc G.xmin G.xmax := by simpa [v] using hValues.2.2.1
  have hvVal : v.im = G.upper v.re := by simpa [v] using hValues.2.2.2
  have huHeight : u.im ≤ (n : ℝ) := by
    rw [huVal]
    exact G.upper_le_stage huDom
  have hvHeight : v.im ≤ (n : ℝ) := by
    rw [hvVal]
    exact G.upper_le_stage hvDom
  have hNewHeight : x.im = (n + 1 : ℝ) :=
    invariant_succ_lfr_new_vertex_height w n hc hUL
  have hnewLeft : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west s.nextEdge) = x := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨hwest, _, _, _, _, _⟩
    rw [hwest]
  have hOldEast : s.east s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hnewRight : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east s.nextEdge) = v := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, heast, _, _, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldEast]
  have hMissingLeft : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (s.nextEdge + 1)) = x := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, _, hwest, _, _, _⟩
    rw [hwest]
  have hOldWest : s.west s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hMissingRight : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (s.nextEdge + 1)) = u := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, _, _, heast, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldWest]
  have hfresh := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  have hEnds := freshEdges_endpoint_heights w n s.nextEdge hfresh
  rw [hnewLeft, hnewRight] at hEnds
  have hFit := freshEdges_ramp_widths_lt w n s.nextEdge hfresh
  rw [hnewLeft, hnewRight] at hFit
  have hJoinLow : segmentHeight x u u.re = G.upper u.re := by
    rw [← huVal]
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hltXu)
    field_simp [hden]
    ring
  have hJoinRoof : roofHeight x v (n + 1) (rampSlope w n) v.re =
      G.upper v.re := by
    rw [hvVal.symm]
    exact roofHeight_finish (rampSlope_pos w n) hEnds.1 hEnds.2 hFit
  have hRoofStart : roofHeight x v (n + 1) (rampSlope w n) x.re = x.im := by
    exact roofHeight_start (rampSlope_pos w n) hEnds.1 hEnds.2 hFit
  have hSegCont : ContinuousOn (segmentHeight x u) (Icc x.re v.re) := by
    have hcont : Continuous (segmentHeight x u) := by
      unfold segmentHeight
      fun_prop
    exact hcont.continuousOn
  have hUpperCont : ContinuousOn G.upper (Icc u.re v.re) := by
    apply G.upper_continuous.mono
    intro r hr
    exact ⟨huDom.1.trans hr.1, hr.2.trans hvDom.2⟩
  have hCapLowCont : ContinuousOn
      (invariant_succ_lfr_cap_lower w n hc hUL G) (Icc x.re v.re) := by
    change ContinuousOn (fun r => if r ≤ u.re then segmentHeight x u r else G.upper r)
      (Icc x.re v.re)
    apply ContinuousOn.if
    · intro r hr
      have hrEq : r = u.re := by
        simpa only [mem_singleton_iff] using frontier_Iic_subset u.re hr.2
      simpa only [hrEq, ite_eq_left le_rfl] using hJoinLow
    · exact hSegCont.mono inter_subset_left
    · apply hUpperCont.mono
      intro r hr
      have hclosure : closure {r : ℝ | ¬ r ≤ u.re} ⊆ Ici u.re := by
        apply closure_minimal
        · intro y hy
          exact (lt_of_not_ge hy).le
        · exact isClosed_Ici
      exact ⟨hclosure hr.2, hr.1.2⟩
  have hRoofCont : ContinuousOn (roofHeight x v (n + 1) (rampSlope w n))
      (Icc x.re v.re) :=
    (continuous_roofHeight x v (n + 1) (rampSlope w n)).continuousOn
  let L : ℝ := Classical.choose G.upper_lipschitz_margin
  have hLspec := Classical.choose_spec G.upper_lipschitz_margin
  rcases hLspec with ⟨hL0, hLM, hLip⟩
  have hLipUV : |u.im - v.im| ≤ L * |u.re - v.re| := by
    have h := hLip u.re huDom v.re hvDom
    rw [← huVal, ← hvVal] at h
    exact h
  have hUpperGap : u.im ≤ v.im + L * (v.re - u.re) := by
    have h := (le_abs_self (u.im - v.im)).trans hLipUV
    rw [abs_of_nonpos (sub_nonpos.mpr hltUv.le)] at h
    linarith
  have hStrictAtU : u.im < v.im + rampSlope w n * (v.re - u.re) := by
    have hmul := mul_lt_mul_of_pos_right hLM (sub_pos.mpr hltUv)
    linarith
  let slope := (u.im - x.im) / (u.re - x.re)
  have hSlopeAbs : |slope| < rampSlope w n := by
    have hs := freshLeft_missing_edge_slope_lt w n n hc hUL le_rfl
    dsimp only at hs
    rw [hMissingLeft, hMissingRight] at hs
    simpa [slope, abs_div, abs_of_pos (sub_pos.mpr hltXu)] using hs
  have hSlopeBounds := abs_lt.mp hSlopeAbs
  have hSlopeNeg : slope < 0 := by
    dsimp [slope]
    rw [hNewHeight]
    exact div_neg_of_neg_of_pos (by linarith [huHeight])
      (sub_pos.mpr hltXu)
  have hSegmentLine (r : ℝ) :
      segmentHeight x u r = x.im + slope * (r - x.re) := rfl
  have hSlopeEnd : x.im + slope * (u.re - x.re) = u.im := by
    dsimp [slope]
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hltXu)
    field_simp [hden]
    ring
  have hSegmentLineEnd (r : ℝ) :
      segmentHeight x u r = u.im + slope * (r - u.re) := by
    rw [hSegmentLine r]
    rw [← hSlopeEnd]
    ring
  have hRoofCompare : ∀ r ∈ Icc u.re v.re,
      roofHeight u v (n + 1) (rampSlope w n) r ≤
        roofHeight x v (n + 1) (rampSlope w n) r := by
    intro r hr
    have hLeft : u.im + rampSlope w n * (r - u.re) ≤
        x.im + rampSlope w n * (r - x.re) := by
      rw [hNewHeight]
      nlinarith [hxu, rampSlope_pos w n]
    unfold roofHeight
    exact min_le_min le_rfl (min_le_min hLeft le_rfl)
  have hGap : ∀ r ∈ Ioo x.re v.re,
      invariant_succ_lfr_cap_lower w n hc hUL G r <
        roofHeight x v (n + 1) (rampSlope w n) r := by
    intro r hr
    by_cases hru : r ≤ u.re
    · have hSegTop : segmentHeight x u r < (n + 1 : ℝ) := by
        rw [hSegmentLine r, hNewHeight]
        have hrx : 0 < r - x.re := sub_pos.mpr hr.1
        nlinarith [hSlopeNeg]
      have hSegLeft : segmentHeight x u r <
          x.im + rampSlope w n * (r - x.re) := by
        rw [hSegmentLine r]
        have hmul := mul_lt_mul_of_pos_right hSlopeBounds.2 (sub_pos.mpr hr.1)
        linarith
      have hRightLine : v.im + rampSlope w n * (v.re - r) -
          segmentHeight x u r =
          (v.im + rampSlope w n * (v.re - u.re) - u.im) +
            (-rampSlope w n - slope) * (r - u.re) := by
        rw [hSegmentLineEnd r]
        ring
      have hRightTerm : segmentHeight x u r <
          v.im + rampSlope w n * (v.re - r) := by
        have hprod : 0 ≤ (-rampSlope w n - slope) * (r - u.re) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith [hSlopeBounds.1])
            (sub_nonpos.mpr hru)
        have hdiff : 0 < v.im + rampSlope w n * (v.re - r) -
            segmentHeight x u r := by
          rw [hRightLine]
          linarith [hStrictAtU, hprod]
        linarith
      have hlow : invariant_succ_lfr_cap_lower w n hc hUL G r =
          segmentHeight x u r := by
        change (if r ≤ u.re then segmentHeight x u r else G.upper r) = _
        rw [ite_eq_left hru]
      rw [hlow]
      unfold roofHeight
      change segmentHeight x u r <
        min (n + 1 : ℝ)
          (min (x.im + rampSlope w n * (r - x.re))
            (v.im + rampSlope w n * (v.re - r)))
      exact lt_min hSegTop (lt_min hSegLeft hRightTerm)
    · have hru' : u.re < r := lt_of_not_ge hru
      have hOldGap := G.upper_lt_roofHeight huDom hvDom huVal.symm.le hvVal.symm.le r
        ⟨hru', hr.2⟩
      have hRoofCmp := hRoofCompare r ⟨hru'.le, hr.2.le⟩
      have hlow : invariant_succ_lfr_cap_lower w n hc hUL G r = G.upper r := by
        change (if r ≤ u.re then segmentHeight x u r else G.upper r) = _
        rw [ite_eq_right (not_le_of_gt hru')]
      rw [hlow]
      exact hOldGap.trans_le hRoofCmp
  refine
    { a := x.re
      b := v.re
      low := invariant_succ_lfr_cap_lower w n hc hUL G
      high := roofHeight x v (n + 1) (rampSlope w n)
      ab := hltXv
      low_continuous := hCapLowCont
      high_continuous := hRoofCont
      separated := hGap
      left_join := ?_
      right_join := ?_ }
  ·
    rw [hRoofStart]
    change (if x.re ≤ u.re then segmentHeight x u x.re else G.upper x.re) = x.im
    rw [ite_eq_left hltXu.le]
    simp [segmentHeight]
  ·
    change (if v.re ≤ u.re then segmentHeight x u v.re else G.upper v.re) =
      roofHeight x v (n + 1) (rampSlope w n) v.re
    have hru : ¬ v.re ≤ u.re := not_le_of_gt hltUv
    rw [ite_eq_right hru, hJoinRoof]


private theorem lfr_heightFn_of_mem_image (p : Polyline) (hp : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) : p.heightFn z.re = z.im := by
  rcases hz with hz | ⟨i, hi, hz⟩
  · rw [hz]
    simpa only [Polyline.point_zero_eq_start] using
      (Polyline.heightFn_point hp (List.length_pos_iff.mpr p.nonempty))
  · have hstrict := Polyline.point_re_lt hp (Nat.lt_succ_self i) hi
    have hz' := (mem_segment_iff_height hstrict).mp hz
    rw [Polyline.heightFn_linear_on_segment hp hi hz'.1 hz'.2.1]
    exact hz'.2.2.symm

private theorem lfr_old_active_graph (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    graphOver (layoutPos w n
        ((kmswStage w n).west (kmswStage w n).active)).re
        (layoutPos w n
          ((kmswStage w n).east (kmswStage w n).active)).re G.upper =
      stageEdgeTrace P (kmswStage w n).active := by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  let b := layoutPos w n (s.east s.active)
  have he := (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hUpper : s.active ∈ s.UL ++ s.UR := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
    rw [hUL]
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr
        (Or.inr (List.mem_singleton.mpr rfl))))
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n s.active he
  have hValue : ∀ r ∈ Icc a.re b.re, G.upper r = f r := by
    intro r hr
    have hz : (⟨r, f r⟩ : ℂ) ∈ (layoutArc w n s.active).image := by
      rw [hf]
      exact ⟨hr.1, hr.2, rfl⟩
    have hh := lfr_heightFn_of_mem_image (layoutArc w n s.active)
      (layoutArc_points_pairwise w n s.active he) hz
    exact (G.upper_eq_heightFn hUpper hr).trans hh
  have hImage : graphOver a.re b.re G.upper =
      (layoutArc w n s.active).image := by
    ext z
    constructor
    · intro hz
      rw [hf]
      refine ⟨hz.1, hz.2.1, ?_⟩
      rw [← hValue z.re ⟨hz.1, hz.2.1⟩]
      exact hz.2.2
    · intro hz
      have hupper := G.upper_eq_arc_height hUpper hz
      rw [hf] at hz
      exact ⟨hz.1, hz.2.1, hupper.symm⟩
  have hTrace : stageEdgeTrace P s.active =
      (layoutArc w n s.active).image := by
    unfold stageEdgeTrace
    rw [dite_eq_left he, G.arc_layout]
    rfl
  rw [hImage, hTrace]



theorem invariant_succ_lfr_cap_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let C := invariant_succ_lfr_new_cap w n hc hUL G
    graphOver C.a C.b C.high =
      ⋃ e ∈ [(kmswStage w n).nextEdge],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let v := layoutPos w n (s.east s.active)
  change graphOver x.re v.re (roofHeight x v (n + 1) (rampSlope w n)) =
    ⋃ e ∈ [s.nextEdge],
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e
  have hnewLeft : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west s.nextEdge) = x := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨hwest, _, _, _, _, _⟩
    rw [hwest]
  have hOldEast : s.east s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hnewRight : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east s.nextEdge) = v := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, heast, _, _, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldEast]
  have hImage := invariant_succ_lfr_active_arc_image w n hc hUL
  dsimp only at hImage
  rw [hnewLeft, hnewRight] at hImage
  have hTrace := invariant_succ_lfr_trace_active w n hc hUL h
  have hRoofTrace : graphOver x.re v.re
      (roofHeight x v (n + 1) (rampSlope w n)) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge := by
    calc
      graphOver x.re v.re (roofHeight x v (n + 1) (rampSlope w n)) =
          (layoutArc w (n + 1) s.nextEdge).image := by
            simpa only [graphOver] using hImage.symm
      _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.nextEdge :=
        hTrace.symm
  rw [hRoofTrace]
  simp



theorem invariant_succ_lfr_cap_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let C := invariant_succ_lfr_new_cap w n hc hUL G
    graphOver C.a C.b C.low =
      ⋃ e ∈ [(kmswStage w n).nextEdge + 1, (kmswStage w n).active],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hltXu : x.re < u.re := by linarith
  have hltUv : u.re < v.re := by
    change (kmswStageRank w n (s.west s.active) : ℝ) <
      (kmswStageRank w n (s.east s.active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hJoin : segmentHeight x u u.re = G.upper u.re := by
    have hValues := invariant_succ_lfr_active_endpoint_values G
    have huVal : u.im = G.upper u.re := by simpa [u] using hValues.2.1
    rw [← huVal]
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hltXu)
    field_simp [hden]
    ring
  have hSplit := graphOver_prefix (a := x.re) (b := v.re) (c := u.re)
    (f := segmentHeight x u) (g := G.upper) hltXu.le hltUv.le hJoin
  have hMissLeft : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (s.nextEdge + 1)) = x := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, _, hwest, _, _, _⟩
    rw [hwest]
  have hOldWest : s.west s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hMissRight : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (s.nextEdge + 1)) = u := by
    have he := invariant_succ_lfr_endpoints w n hc hUL
    dsimp only at he
    rcases he with ⟨_, _, _, heast, _, _⟩
    rw [heast, layoutPos_old_vertex w n _ hOldWest]
  have hMissImage := invariant_succ_lfr_missing_arc_image w n hc hUL
  dsimp only at hMissImage
  rw [hMissLeft, hMissRight] at hMissImage
  have hMissTrace := invariant_succ_lfr_trace_missing w n hc hUL h
  have hMissingGraph : graphOver x.re u.re (segmentHeight x u) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) := by
    calc
      graphOver x.re u.re (segmentHeight x u) =
          (layoutArc w (n + 1) (s.nextEdge + 1)).image := by
            simpa only [graphOver] using hMissImage.symm
      _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) :=
        hMissTrace.symm
  have hActiveGraph := lfr_old_active_graph w n G
  have hActiveGraph' : graphOver u.re v.re G.upper = stageEdgeTrace P s.active := by
    simpa [u, v] using hActiveGraph
  have hOldTrace := invariant_succ_lfr_trace_old w n hc hUL G h s.active
    ((kmswStage_boundary_ids_lt_nextEdge w n).1)
  have hActiveNewGraph : graphOver u.re v.re G.upper =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.active := by
    exact hActiveGraph'.trans hOldTrace.symm
  have hListTrace :
      (⋃ e ∈ [s.nextEdge + 1, s.active],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) ∪
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.active := by
    ext z
    simp [List.mem_cons]
  change graphOver x.re v.re (invariant_succ_lfr_cap_lower w n hc hUL G) =
    ⋃ e ∈ [s.nextEdge + 1, s.active],
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e
  calc
    graphOver x.re v.re (invariant_succ_lfr_cap_lower w n hc hUL G) =
        graphOver x.re u.re (segmentHeight x u) ∪ graphOver u.re v.re G.upper := by
          simpa only [invariant_succ_lfr_cap_lower] using hSplit
    _ = stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (s.nextEdge + 1) ∪
          stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) s.active := by
            rw [hMissingGraph, hActiveNewGraph]
    _ = ⋃ e ∈ [s.nextEdge + 1, s.active],
          stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := hListTrace.symm



theorem invariant_succ_lfr_cap_disjoint_region (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    Disjoint (invariant_succ_lfr_new_cap w n hc hUL G).region
      (closedGraphRegion G.xmin G.xmax G.lower G.upper) := by
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  have hxmin : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hltXu : x.re < u.re := by linarith
  have hJoin : segmentHeight x u u.re = G.upper u.re := by
    have hValues := invariant_succ_lfr_active_endpoint_values G
    have huVal : u.im = G.upper u.re := by simpa [u] using hValues.2.1
    rw [← huVal]
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := ne_of_gt (sub_pos.mpr hltXu)
    field_simp [hden]
    ring
  apply Set.disjoint_left.mpr
  intro z hzCap hzOld
  change x.re < z.re ∧ z.re < v.re ∧
    invariant_succ_lfr_cap_lower w n hc hUL G z.re < z.im ∧
      z.im < roofHeight x v (n + 1) (rampSlope w n) z.re at hzCap
  have huLe : u.re ≤ z.re := by
    calc
      u.re = G.xmin := hxmin
      _ ≤ z.re := hzOld.1
  have hLowEq : invariant_succ_lfr_cap_lower w n hc hUL G z.re = G.upper z.re := by
    rcases eq_or_lt_of_le huLe with heq | hlt
    · rw [← heq]
      change (if u.re ≤ u.re then segmentHeight x u u.re else G.upper u.re) = _
      rw [ite_eq_left le_rfl]
      exact hJoin
    · change (if z.re ≤ u.re then segmentHeight x u z.re else G.upper z.re) = _
      rw [ite_eq_right (not_le_of_gt hlt)]
  have hAbove : G.upper z.re < z.im := by
    calc
      G.upper z.re = invariant_succ_lfr_cap_lower w n hc hUL G z.re := hLowEq.symm
      _ < z.im := hzCap.2.2.1
  exact (not_lt_of_ge hzOld.2.2.2) hAbove



theorem invariant_succ_lfr_cap_disjoint_old_cap (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (invariant_succ_lfr_new_cap w n hc hUL G).region (G.cap i).region := by
  apply Set.disjoint_left.mpr
  intro z hzNew hzOld
  have hzClosure : z ∈ closure (G.cap i).region := subset_closure hzOld
  have hzClosed : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inr (mem_iUnion.mpr ⟨i, hzClosure⟩)
  exact Set.disjoint_left.mp
    (invariant_succ_lfr_cap_disjoint_region w n hc hUL G) hzNew hzClosed



theorem invariant_succ_lfr_cap_edges (w : ℕ → Fin 3) (n : ℕ)
    (e : ℕ) :
    e ∈ [(kmswStage w n).nextEdge + 1, (kmswStage w n).active] ++
        [(kmswStage w n).nextEdge] ↔
      e = (kmswStage w n).active ∨ e = (kmswStage w n).nextEdge ∨
        e = (kmswStage w n).nextEdge + 1 := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto


private theorem lfr_old_arc (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (he' : e < (kmswStage w (n + 1)).nextEdge) (b : Bool) :
    (monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he'⟩, b) =
      P.arc (⟨e, he⟩, b) := by
  rw [G.arc_layout]
  change (if b then (layoutArc w (n + 1) e).reverse else layoutArc w (n + 1) e) = _
  rw [layoutArc_old w n e he]



theorem invariant_succ_lfr_drawing_image (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image = P.image ∪
      (stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge ∪
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
          ((kmswStage w n).nextEdge + 1)) := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  obtain ⟨hcount, hvertices⟩ := invariant_succ_lfr_counts w n hc hUL
  have h0 : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by omega
  have h1 : (kmswStage w n).nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by omega
  rw [invariant_succ_lfr_trace_active w n hc hUL h,
    invariant_succ_lfr_trace_missing w n hc hUL h]
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩)
    · by_cases hv : v.val < (kmswStage w n).nextVertex
      · left
        refine Or.inl ⟨⟨v.val, hv⟩, ?_⟩
        rw [G.pos_layout]
        exact (layoutPos_old_vertex w n v.val hv).symm
      · right
        left
        have hv' : v.val = (kmswStage w n).nextVertex := by have := v.isLt; omega
        have hz : Q.pos v = (layoutArc w (n + 1) (kmswStage w n).nextEdge).start := by
          rw [layoutArc_start w (n + 1) _ h0,
            (invariant_succ_lfr_endpoints w n hc hUL).1]
          change layoutPos w (n + 1) v.val = _
          rw [hv']
        exact Or.inl hz
    · by_cases he : e.val < (kmswStage w n).nextEdge
      · left
        rw [lfr_old_arc w n G h e.val he e.isLt b] at hz
        exact Or.inr ⟨(⟨e.val, he⟩, b), hz⟩
      · have hz' : z ∈ (layoutArc w (n + 1) e.val).image := by
          cases b
          · exact hz
          · exact lfr_reverse_image_subset _ hz
        right
        have hid : e.val = (kmswStage w n).nextEdge ∨
            e.val = (kmswStage w n).nextEdge + 1 := by have := e.isLt; omega
        rcases hid with hid | hid
        · exact Or.inl (hid ▸ hz')
        · exact Or.inr (hid ▸ hz')
  · rintro (hz | hz)
    · rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
      · refine Or.inl ⟨stageVertexIncl w n v, ?_⟩
        rw [G.pos_layout]
        exact layoutPos_old_vertex w n v.val v.isLt
      · refine Or.inr ⟨stageDartIncl w n d, ?_⟩
        change z ∈ (layoutDart w (n + 1) (stageDartIncl w n d)).image
        rw [layoutDart_incl_eq]
        simpa only [G.arc_layout, layoutDart] using hz
    · rcases hz with hz | hz
      · exact Or.inr ⟨(⟨_, h0⟩, false), hz⟩
      · exact Or.inr ⟨(⟨_, h1⟩, false), hz⟩



theorem invariant_succ_lfr_new_cap_avoid (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    Disjoint (invariant_succ_lfr_new_cap w n hc hUL G).region
      (monotoneLayoutDrawing w (n + 1) h).image := by
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  apply Set.disjoint_left.mpr
  intro z hz hzQ
  rw [invariant_succ_lfr_drawing_image w n hc hUL G h] at hzQ
  rcases hzQ with hzP | hzRoof | hzSeg
  · apply Set.disjoint_left.mp (invariant_succ_lfr_cap_disjoint_region w n hc hUL G) hz
    rw [← G.cover]
    exact Or.inl hzP
  · have htrace := invariant_succ_lfr_cap_upper_trace w n hc hUL G h
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at htrace
    rw [← htrace] at hzRoof
    exact (ne_of_lt hz.2.2.2) hzRoof.2.2
  · have hzLow : z ∈ graphOver C.a C.b C.low := by
      rw [invariant_succ_lfr_cap_lower_trace w n hc hUL G h]
      exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨by simp, hzSeg⟩⟩
    exact (ne_of_gt hz.2.2.1) hzLow.2.2

private theorem lfr_cap_low_eq_upper (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    {r : ℝ} (hr : G.xmin ≤ r) :
    (invariant_succ_lfr_new_cap w n hc hUL G).low r = G.upper r := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  have hu : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  change (if r ≤ u.re then segmentHeight x u r else G.upper r) = _
  by_cases hru : r ≤ u.re
  · have heq : r = u.re := le_antisymm hru (hu ▸ hr)
    rw [heq, ite_eq_left le_rfl]
    rw [← (invariant_succ_lfr_active_endpoint_values G).2.1]
    change segmentHeight x u u.re = u.im
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := by linarith only [hxu]
    field_simp [hden]
    ring
  · rw [ite_eq_right hru]

private theorem lfr_old_cap_below {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    {z : ℂ} (hz : z ∈ (G.cap i).region) : z.im < G.upper z.re := by
  have hb : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)
  apply lt_of_le_of_ne hb.2.2.2
  intro heq
  have hzgraph : z ∈ graphOver G.xmin G.xmax G.upper := ⟨hb.1, hb.2.1, heq⟩
  rw [G.upper_trace] at hzgraph
  obtain ⟨f, hfz⟩ := mem_iUnion.mp hzgraph
  obtain ⟨hf, hzf⟩ := mem_iUnion.mp hfz
  have hfb : f < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at hf ⊢
    tauto
  have hzP : z ∈ P.image := Or.inr ⟨(⟨f, hfb⟩, false), by
    simpa only [stageEdgeTrace, hfb, ↓reduceDIte] using hzf⟩
  exact Set.disjoint_left.mp (G.cap_avoid i) hz hzP

private theorem lfr_cap_low_le_high (C : GraphCap) {r : ℝ} (hr : r ∈ Icc C.a C.b) :
    C.low r ≤ C.high r := by
  rcases eq_or_lt_of_le hr.1 with heq | hlt
  · rw [← heq, C.left_join]
  · rcases lt_or_eq_of_le hr.2 with hlt' | heq
    · exact (C.separated r ⟨hlt, hlt'⟩).le
    · rw [heq, C.right_join]



theorem invariant_succ_lfr_old_cap_avoid (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (G.cap i).region (monotoneLayoutDrawing w (n + 1) h).image := by
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  apply Set.disjoint_left.mpr
  intro z hz hzQ
  have hzR : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)
  rw [invariant_succ_lfr_drawing_image w n hc hUL G h] at hzQ
  rcases hzQ with hzP | hzRoof | hzSeg
  · exact Set.disjoint_left.mp (G.cap_avoid i) hz hzP
  · have htrace := invariant_succ_lfr_cap_upper_trace w n hc hUL G h
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at htrace
    rw [← htrace] at hzRoof
    have hh := lfr_cap_low_le_high C ⟨hzRoof.1, hzRoof.2.1⟩
    rw [lfr_cap_low_eq_upper w n hc hUL G hzR.1] at hh
    exact (not_le_of_gt (lfr_old_cap_below G i hz)) (hzRoof.2.2 ▸ hh)
  · have hzLow : z ∈ graphOver C.a C.b C.low := by
      rw [invariant_succ_lfr_cap_lower_trace w n hc hUL G h]
      exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨by simp, hzSeg⟩⟩
    have heq := hzLow.2.2
    rw [lfr_cap_low_eq_upper w n hc hUL G hzR.1] at heq
    exact (ne_of_lt (lfr_old_cap_below G i hz)) heq

private theorem lfr_step_triangle_ids (s : State) (c : Step)
    (ha : s.active < s.nextEdge) (hb : ∀ e ∈ s.UL, e < s.nextEdge)
    (htri : ∀ t ∈ s.triangles,
      t.1 < s.nextEdge ∧ t.2.1 < s.nextEdge ∧ t.2.2 < s.nextEdge) :
    ∀ t ∈ (kmswStepOfStep s c).triangles,
      t.1 < (kmswStepOfStep s c).nextEdge ∧
        t.2.1 < (kmswStepOfStep s c).nextEdge ∧
        t.2.2 < (kmswStepOfStep s c).nextEdge := by
  intro t ht
  cases c with
  | down =>
    cases hs : s.UR with
    | nil =>
      simp only [kmswStepOfStep, hs, State.addEdge] at ht ⊢
      obtain ⟨h0, h1, h2⟩ := htri t ht
      omega
    | cons e es =>
      simpa only [kmswStepOfStep, hs] using htri t (by simpa [kmswStepOfStep, hs] using ht)
  | left =>
    cases hs : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · obtain ⟨h0, h1, h2⟩ := htri t ht
        omega
      · dsimp only
        omega
    | cons e es =>
      have he : e < s.nextEdge := by
        apply hb e
        apply List.mem_of_mem_dropLast
        apply List.mem_reverse.mp
        rw [hs]
        exact List.mem_cons_self
      simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · obtain ⟨h0, h1, h2⟩ := htri t ht
        omega
      · dsimp only
        omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.mem_append, List.mem_singleton] at ht ⊢
    rcases ht with ht | rfl
    · obtain ⟨h0, h1, h2⟩ := htri t ht
      omega
    · dsimp only
      omega

private theorem lfr_triangle_ids_lt (w : ℕ → Fin 3) (n : ℕ) :
    ∀ t ∈ (kmswStage w n).triangles,
      t.1 < (kmswStage w n).nextEdge ∧ t.2.1 < (kmswStage w n).nextEdge ∧
        t.2.2 < (kmswStage w n).nextEdge := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    apply lfr_step_triangle_ids (kmswStage w n) (kmswCodeStep (w n))
      (kmswStage_boundary_ids_lt_nextEdge w n).1 ?_ ih
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl he))

private theorem lfr_cap_edge_lt (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    (e : ℕ) (he : e ∈ G.capLower i ++ G.capUpper i) :
    e < (kmswStage w n).nextEdge := by
  have ht := lfr_triangle_ids_lt w n _ (List.get_mem _ i)
  rcases (G.cap_edges i e).mp he with he | he | he
  · exact he ▸ ht.1
  · exact he ▸ ht.2.1
  · exact he ▸ ht.2.2




@[expose] noncomputable def lfrCaps (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : GraphCap :=
  if hi : i.val < (kmswStage w n).triangles.length then G.cap ⟨i.val, hi⟩
  else invariant_succ_lfr_new_cap w n hc hUL G



@[expose] noncomputable def lfrCapLower (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : List ℕ :=
  if hi : i.val < (kmswStage w n).triangles.length then G.capLower ⟨i.val, hi⟩
  else [(kmswStage w n).nextEdge + 1, (kmswStage w n).active]



@[expose] noncomputable def lfrCapUpper (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : List ℕ :=
  if hi : i.val < (kmswStage w n).triangles.length then G.capUpper ⟨i.val, hi⟩
  else [(kmswStage w n).nextEdge]



theorem invariant_succ_lfr_caps_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    graphOver (lfrCaps w n hc hUL G i).a (lfrCaps w n hc hUL G i).b
        (lfrCaps w n hc hUL G i).low =
      ⋃ e ∈ lfrCapLower w n G i,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [lfrCaps, lfrCapLower, hi, ↓reduceDIte]
    rw [G.cap_lower_trace]
    exact iUnion_congr (fun e => iUnion_congr (fun he =>
      (invariant_succ_lfr_trace_old w n hc hUL G h e
        (lfr_cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append_left _ he))).symm))
  · simpa only [lfrCaps, lfrCapLower, hi, ↓reduceDIte] using
      invariant_succ_lfr_cap_lower_trace w n hc hUL G h



theorem invariant_succ_lfr_caps_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    graphOver (lfrCaps w n hc hUL G i).a (lfrCaps w n hc hUL G i).b
        (lfrCaps w n hc hUL G i).high =
      ⋃ e ∈ lfrCapUpper w n G i,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [lfrCaps, lfrCapUpper, hi, ↓reduceDIte]
    rw [G.cap_upper_trace]
    exact iUnion_congr (fun e => iUnion_congr (fun he =>
      (invariant_succ_lfr_trace_old w n hc hUL G h e
        (lfr_cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append_right _ he))).symm))
  · simpa only [lfrCaps, lfrCapUpper, hi, ↓reduceDIte] using
      invariant_succ_lfr_cap_upper_trace w n hc hUL G h



theorem invariant_succ_lfr_caps_edges (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) (e : ℕ) :
    e ∈ lfrCapLower w n G i ++ lfrCapUpper w n G i ↔
      e = ((kmswStage w (n + 1)).triangles.get i).1 ∨
        e = ((kmswStage w (n + 1)).triangles.get i).2.1 ∨
        e = ((kmswStage w (n + 1)).triangles.get i).2.2 := by
  have htri := (invariant_succ_lfr_stage_lists w n hc hUL).2.1
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · have ht : (kmswStage w (n + 1)).triangles.get i =
        (kmswStage w n).triangles.get ⟨i.val, hi⟩ := by
      simp only [List.get_eq_getElem, htri, List.getElem_append_left hi]
    simpa only [lfrCapLower, lfrCapUpper, hi, ↓reduceDIte, ht] using
      G.cap_edges ⟨i.val, hi⟩ e
  · have hcount : (kmswStage w (n + 1)).triangles.length =
        (kmswStage w n).triangles.length + 1 := by simp only [htri, List.length_append]; simp
    have hiB := i.isLt
    have heq : i.val = (kmswStage w n).triangles.length := by omega
    have ht : (kmswStage w (n + 1)).triangles.get i =
        ((kmswStage w n).active, (kmswStage w n).nextEdge,
          (kmswStage w n).nextEdge + 1) := by
      simp only [List.get_eq_getElem, htri, heq,
        List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
    simpa only [lfrCapLower, lfrCapUpper, hi, ↓reduceDIte, ht] using
      invariant_succ_lfr_cap_edges w n e



theorem invariant_succ_lfr_caps_avoid (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    Disjoint (lfrCaps w n hc hUL G i).region
      (monotoneLayoutDrawing w (n + 1) h).image := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simpa only [lfrCaps, hi, ↓reduceDIte] using
      invariant_succ_lfr_old_cap_avoid w n hc hUL G h ⟨i.val, hi⟩
  · simpa only [lfrCaps, hi, ↓reduceDIte] using
      invariant_succ_lfr_new_cap_avoid w n hc hUL G h



theorem invariant_succ_lfr_caps_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i j : Fin (kmswStage w (n + 1)).triangles.length) (hij : i ≠ j) :
    Disjoint (lfrCaps w n hc hUL G i).region (lfrCaps w n hc hUL G j).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length <;>
    by_cases hj : j.val < (kmswStage w n).triangles.length
  · simp only [lfrCaps, hi, hj, ↓reduceDIte]
    apply G.cap_disjoint
    intro heq
    exact hij (Fin.ext (congrArg
      (fun k : Fin (kmswStage w n).triangles.length => k.val) heq))
  · simp only [lfrCaps, hi, hj, ↓reduceDIte]
    exact (invariant_succ_lfr_cap_disjoint_old_cap w n hc hUL G ⟨i.val, hi⟩).symm
  · simp only [lfrCaps, hi, hj, ↓reduceDIte]
    exact invariant_succ_lfr_cap_disjoint_old_cap w n hc hUL G ⟨j.val, hj⟩
  · have htri := (invariant_succ_lfr_stage_lists w n hc hUL).2.1
    have hcount : (kmswStage w (n + 1)).triangles.length =
        (kmswStage w n).triangles.length + 1 := by simp only [htri, List.length_append]; simp
    have hiB := i.isLt
    have hjB := j.isLt
    exact (hij (Fin.ext (by omega))).elim

private theorem lfr_roof_abs_sub_le {a b : ℂ} {H M : ℝ} (hM : 0 ≤ M) (x y : ℝ) :
    |roofHeight a b H M x - roofHeight a b H M y| ≤ M * |x - y| := by
  have hl : |(a.im + M * (x - a.re)) - (a.im + M * (y - a.re))| =
      M * |x - y| := by
    rw [show (a.im + M * (x - a.re)) - (a.im + M * (y - a.re)) =
      M * (x - y) by ring, abs_mul, abs_of_nonneg hM]
  have hr : |(b.im + M * (b.re - x)) - (b.im + M * (b.re - y))| =
      M * |x - y| := by
    rw [show (b.im + M * (b.re - x)) - (b.im + M * (b.re - y)) =
      M * (y - x) by ring, abs_mul, abs_of_nonneg hM, abs_sub_comm y x]
  unfold roofHeight
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le
  · simpa only [sub_self, abs_zero] using mul_nonneg hM (abs_nonneg (x - y))
  · exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hl.le hr.le)




theorem invariant_succ_lfr_upper_lipschitz_margin (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    ∃ L : ℝ, 0 ≤ L ∧ L < rampSlope w (n + 1) ∧
      ∀ r ∈ Icc x.re G.xmax, ∀ t ∈ Icc x.re G.xmax,
        |invariant_succ_lfr_upper w n hc hUL G r -
          invariant_succ_lfr_upper w n hc hUL G t| ≤ L * |r - t| := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let v := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let g := roofHeight x v (n + 1) (rampSlope w n)
  let M := rampSlope w n
  have hv := (invariant_succ_lfr_active_endpoint_values G).2.2.1
  have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
  have hend := invariant_succ_lfr_endpoints w n hc hUL
  have heOld := (kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  have hleft : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge) = x := by rw [hend.1]
  have hright : layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge) = v := by
    rw [hend.2.1, layoutPos_old_vertex w n _ heOld]
  have hh := freshEdges_endpoint_heights w n _ hf
  have hfit := freshEdges_ramp_widths_lt w n _ hf
  rw [hleft, hright] at hh hfit
  have hjoin : g v.re = G.upper v.re :=
    (roofHeight_finish (rampSlope_pos w n) hh.1 hh.2 hfit).trans
      (invariant_succ_lfr_active_endpoint_values G).2.2.2
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  have hg : ∀ r t, |g r - g t| ≤ M * |r - t| :=
    fun r t => lfr_roof_abs_sub_le (rampSlope_pos w n).le r t
  have hu : ∀ r ∈ Icc v.re G.xmax, ∀ t ∈ Icc v.re G.xmax,
      |G.upper r - G.upper t| ≤ M * |r - t| := by
    intro r hr t ht
    exact (hLip r ⟨hv.1.trans hr.1, hr.2⟩ t ⟨hv.1.trans ht.1, ht.2⟩).trans
      (mul_le_mul_of_nonneg_right hLM.le (abs_nonneg _))
  have ordered : ∀ r ∈ Icc x.re G.xmax, ∀ t ∈ Icc x.re G.xmax, r ≤ t →
      |(if r ≤ v.re then g r else G.upper r) -
        (if t ≤ v.re then g t else G.upper t)| ≤ M * |r - t| := by
    intro r hr t ht hrt
    by_cases htv : t ≤ v.re
    · have hrv := hrt.trans htv
      simp only [hrv, htv, ↓reduceIte]
      exact hg r t
    · by_cases hrv : r ≤ v.re
      · simp only [hrv, htv, ↓reduceIte]
        calc
          |g r - G.upper t| ≤ |g r - g v.re| + |g v.re - G.upper t| := abs_sub_le _ _ _
          _ ≤ M * |r - v.re| + M * |v.re - t| := by
            apply add_le_add (hg r v.re)
            rw [hjoin]
            exact hu v.re ⟨le_rfl, hv.2⟩ t ⟨(lt_of_not_ge htv).le, ht.2⟩
          _ = M * |r - t| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hrv),
              abs_of_nonpos (sub_nonpos.mpr (lt_of_not_ge htv).le),
              abs_of_nonpos (sub_nonpos.mpr hrt)]
            ring
      · simp only [hrv, htv, ↓reduceIte]
        exact hu r ⟨(lt_of_not_ge hrv).le, hr.2⟩ t ⟨(lt_of_not_ge htv).le, ht.2⟩
  refine ⟨M, (rampSlope_pos w n).le, rampSlope_lt w (Nat.lt_succ_self n), ?_⟩
  intro r hr t ht
  change |(if r ≤ v.re then g r else G.upper r) -
    (if t ≤ v.re then g t else G.upper t)| ≤ M * |r - t|
  rcases le_total r t with hrt | htr
  · exact ordered r hr t ht hrt
  · simpa only [abs_sub_comm] using ordered t ht r hr htr


private theorem lfr_lower_eq_old (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    {r : ℝ} (hr : G.xmin ≤ r) :
    invariant_succ_lfr_lower w n hc hUL G r = G.lower r := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  have hu : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  change (if r ≤ u.re then segmentHeight x u r else G.lower r) = _
  by_cases hru : r ≤ u.re
  · have heq : r = u.re := le_antisymm hru (hu ▸ hr)
    rw [heq, ite_eq_left le_rfl, invariant_succ_lfr_lower_at_active_west G hUL]
    change segmentHeight x u u.re = u.im
    unfold segmentHeight
    have hden : u.re - x.re ≠ 0 := by linarith only [hxu]
    field_simp [hden]
    ring
  · rw [ite_eq_right hru]



theorem invariant_succ_lfr_region_eq (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    closedGraphRegion x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G)
        (invariant_succ_lfr_upper w n hc hUL G) =
      closedGraphRegion G.xmin G.xmax G.lower G.upper ∪
        closure (invariant_succ_lfr_new_cap w n hc hUL G).region := by
  let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
  let v := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  have hu : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have huv : u.re < v.re := by
    change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hv : v.re ≤ G.xmax := (invariant_succ_lfr_active_endpoint_values G).2.2.1.2
  have hcl : closure C.region = closedGraphRegion C.a C.b C.low C.high :=
    closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous
      C.high_continuous C.separated C.left_join C.right_join
  change closedGraphRegion x.re G.xmax _ _ = _ ∪ closure C.region
  rw [hcl]
  have high (r : ℝ) (hr : r ≤ v.re) :
      invariant_succ_lfr_upper w n hc hUL G r = C.high r := by
    change (if r ≤ v.re then C.high r else G.upper r) = _
    rw [ite_eq_left hr]
  have highOld (r : ℝ) (hr : ¬ r ≤ v.re) :
      invariant_succ_lfr_upper w n hc hUL G r = G.upper r := by
    change (if r ≤ v.re then C.high r else G.upper r) = _
    rw [ite_eq_right hr]
  have low (r : ℝ) (hr : r ≤ u.re) :
      invariant_succ_lfr_lower w n hc hUL G r = C.low r := by
    change (if r ≤ u.re then segmentHeight x u r else G.lower r) =
      (if r ≤ u.re then segmentHeight x u r else G.upper r)
    rw [ite_eq_left hr, ite_eq_left hr]
  ext z
  constructor
  · intro hz
    by_cases hzu : z.re ≤ u.re
    · right
      exact ⟨hz.1, hzu.trans huv.le, (low z.re hzu) ▸ hz.2.2.1,
        (high z.re (hzu.trans huv.le)) ▸ hz.2.2.2⟩
    · have hzOld : G.xmin ≤ z.re := hu ▸ (lt_of_not_ge hzu).le
      by_cases hzy : z.im ≤ G.upper z.re
      · exact Or.inl ⟨hzOld, hz.2.1,
          (lfr_lower_eq_old w n hc hUL G hzOld) ▸ hz.2.2.1, hzy⟩
      · right
        have hzv : z.re ≤ v.re := by
          by_contra hzv
          exact hzy ((highOld z.re hzv) ▸ hz.2.2.2)
        exact ⟨hz.1, hzv, by
          rw [lfr_cap_low_eq_upper w n hc hUL G hzOld]
          exact (lt_of_not_ge hzy).le,
          (high z.re hzv) ▸ hz.2.2.2⟩
  · rintro (hz | hz)
    · have hxz : x.re ≤ z.re := by linarith only [hxu, hu, hz.1]
      refine ⟨hxz, hz.2.1, ?_, ?_⟩
      · rw [lfr_lower_eq_old w n hc hUL G hz.1]
        exact hz.2.2.1
      · by_cases hzv : z.re ≤ v.re
        · rw [high z.re hzv]
          have hh := lfr_cap_low_le_high C ⟨hxz, hzv⟩
          rw [lfr_cap_low_eq_upper w n hc hUL G hz.1] at hh
          exact hz.2.2.2.trans hh
        · rw [highOld z.re hzv]
          exact hz.2.2.2
    · have hzv : z.re ≤ v.re := hz.2.1
      refine ⟨hz.1, hzv.trans hv, ?_, ?_⟩
      · by_cases hzu : z.re ≤ u.re
        · rw [low z.re hzu]
          exact hz.2.2.1
        · have hzOld : G.xmin ≤ z.re := hu ▸ (lt_of_not_ge hzu).le
          rw [lfr_lower_eq_old w n hc hUL G hzOld]
          have hh := G.lower_le_upper z.re ⟨hzOld, hzv.trans hv⟩
          rw [← lfr_cap_low_eq_upper w n hc hUL G hzOld] at hh
          exact hh.trans hz.2.2.1
      · rw [high z.re hzv]
        exact hz.2.2.2

private theorem lfr_caps_union_closure (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    (⋃ i, closure (lfrCaps w n hc hUL G i).region) =
      (⋃ i, closure (G.cap i).region) ∪
        closure (invariant_succ_lfr_new_cap w n hc hUL G).region := by
  have htri := (invariant_succ_lfr_stage_lists w n hc hUL).2.1
  have hcount : (kmswStage w (n + 1)).triangles.length =
      (kmswStage w n).triangles.length + 1 := by simp only [htri, List.length_append]; simp
  ext z
  constructor
  · intro hz
    obtain ⟨i, hz⟩ := mem_iUnion.mp hz
    by_cases hi : i.val < (kmswStage w n).triangles.length
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i.val, hi⟩, by
        simpa only [lfrCaps, hi, ↓reduceDIte] using hz⟩)
    · exact Or.inr (by simpa only [lfrCaps, hi, ↓reduceDIte] using hz)
  · rintro (hz | hz)
    · obtain ⟨i, hz⟩ := mem_iUnion.mp hz
      have hi : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      exact mem_iUnion.mpr ⟨⟨i.val, hi⟩, by
        simpa only [lfrCaps, i.isLt, ↓reduceDIte] using hz⟩
    · have hi : (kmswStage w n).triangles.length <
          (kmswStage w (n + 1)).triangles.length := by omega
      exact mem_iUnion.mpr ⟨⟨(kmswStage w n).triangles.length, hi⟩, by
        simpa only [lfrCaps, lt_self_iff_false, ↓reduceDIte] using hz⟩



theorem invariant_succ_lfr_cover (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    (monotoneLayoutDrawing w (n + 1) h).image ∪
        ⋃ i, closure (lfrCaps w n hc hUL G i).region =
      closedGraphRegion x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G)
        (invariant_succ_lfr_upper w n hc hUL G) := by
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  have freshSub : stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
        (kmswStage w n).nextEdge ∪
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
        ((kmswStage w n).nextEdge + 1) ⊆ closure C.region := by
    have hcl : closure C.region = closedGraphRegion C.a C.b C.low C.high :=
      closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous
        C.high_continuous C.separated C.left_join C.right_join
    rintro z (hz | hz)
    · have htrace := invariant_succ_lfr_cap_upper_trace w n hc hUL G h
      simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at htrace
      rw [← htrace] at hz
      rw [hcl]
      exact ⟨hz.1, hz.2.1, hz.2.2 ▸ lfr_cap_low_le_high C ⟨hz.1, hz.2.1⟩, hz.2.2.le⟩
    · have hzLow : z ∈ graphOver C.a C.b C.low := by
        rw [invariant_succ_lfr_cap_lower_trace w n hc hUL G h]
        exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨by simp, hz⟩⟩
      rw [hcl]
      exact ⟨hzLow.1, hzLow.2.1, hzLow.2.2.ge,
        hzLow.2.2 ▸ lfr_cap_low_le_high C ⟨hzLow.1, hzLow.2.1⟩⟩
  dsimp only
  rw [invariant_succ_lfr_region_eq w n hc hUL G, ← G.cover,
    invariant_succ_lfr_drawing_image w n hc hUL G h, lfr_caps_union_closure w n hc hUL G]
  ext z
  simp only [mem_union]
  have hh := @freshSub z
  simp only [mem_union] at hh
  dsimp only [C] at hh
  tauto



theorem invariant_succ_lfr_cover_lower (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : Fin (kmswStage w (n + 1)).nextEdge) :
    e.val ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR ∨
      ∃ i, e.val ∈ lfrCapLower w n G i := by
  obtain ⟨_, htri, hU, _, hR, _⟩ := invariant_succ_lfr_stage_lists w n hc hUL
  have hcount : (kmswStage w (n + 1)).triangles.length =
      (kmswStage w n).triangles.length + 1 := by simp only [htri, List.length_append]; simp
  let lasti : Fin (kmswStage w (n + 1)).triangles.length :=
    ⟨(kmswStage w n).triangles.length, by omega⟩
  have hlast : ¬ lasti.val < (kmswStage w n).triangles.length := Nat.lt_irrefl _
  by_cases he : e.val < (kmswStage w n).nextEdge
  · rcases G.cover_lower ⟨e.val, he⟩ with hb | ⟨i, hi⟩
    · rw [invariant_succ_lfr_old_UL w n hUL] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inr ⟨lasti, by
          simp only [lfrCapLower, hlast, ↓reduceDIte]
          exact List.mem_cons_of_mem _ hb⟩
      · exact Or.inl (by rw [hU, hR]; exact List.mem_append_right _ hb)
    · have hiB : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      exact Or.inr ⟨⟨i.val, hiB⟩, by
        simpa only [lfrCapLower, i.isLt, ↓reduceDIte] using hi⟩
  · have hcE := (invariant_succ_lfr_counts w n hc hUL).1
    have hid : e.val = (kmswStage w n).nextEdge ∨
        e.val = (kmswStage w n).nextEdge + 1 := by have := e.isLt; omega
    rcases hid with hid | hid
    · exact Or.inl (by rw [hU]; simp [hid])
    · exact Or.inr ⟨lasti, by simp only [lfrCapLower, hlast, ↓reduceDIte]; simp [hid]⟩



theorem invariant_succ_lfr_cover_upper (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : Fin (kmswStage w (n + 1)).nextEdge) :
    e.val ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR ∨
      ∃ i, e.val ∈ lfrCapUpper w n G i := by
  obtain ⟨_, htri, _, hL, _, hR⟩ := invariant_succ_lfr_stage_lists w n hc hUL
  have hcount : (kmswStage w (n + 1)).triangles.length =
      (kmswStage w n).triangles.length + 1 := by simp only [htri, List.length_append]; simp
  by_cases he : e.val < (kmswStage w n).nextEdge
  · rcases G.cover_upper ⟨e.val, he⟩ with hb | ⟨i, hi⟩
    · left
      rw [hL, hR, List.cons_append]
      exact List.mem_cons_of_mem _ hb
    · have hiB : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      exact Or.inr ⟨⟨i.val, hiB⟩, by
        simpa only [lfrCapUpper, i.isLt, ↓reduceDIte] using hi⟩
  · have hcE := (invariant_succ_lfr_counts w n hc hUL).1
    have hid : e.val = (kmswStage w n).nextEdge ∨
        e.val = (kmswStage w n).nextEdge + 1 := by have := e.isLt; omega
    rcases hid with hid | hid
    · have hi : (kmswStage w n).triangles.length <
          (kmswStage w (n + 1)).triangles.length := by omega
      exact Or.inr ⟨⟨(kmswStage w n).triangles.length, hi⟩, by
        simp only [lfrCapUpper, lt_self_iff_false, ↓reduceDIte, List.mem_singleton]
        exact hid⟩
    · exact Or.inl (by rw [hL]; simp [hid])

private theorem lfr_initial_ray_mem_image (p : Polyline) (hlen : 2 ≤ p.points.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  refine Or.inr ⟨0, by omega, ?_⟩
  change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
  rw [Polyline.point_zero_eq_start]
  have heq : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩

private theorem lfr_initial_line_at (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re ≠ 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) (x : ℝ)
    (ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1) :
    f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  have hx : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, div_mul_cancel₀ _ hd]
    ring
  have hh := hgraph _ (lfr_initial_ray_mem_image p hlen ht)
  rw [hx] at hh
  rw [hh]
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  ring

private theorem lfr_initial_line_east (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : 0 < p.initialDirection.re)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc p.start.re (p.start.re + η),
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨p.initialDirection.re, hd, ?_⟩
  intro x hx
  apply lfr_initial_line_at p f hlen hd.ne' hgraph x
  exact ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
    (div_le_one hd).mpr (by linarith only [hx.2])⟩

private theorem lfr_initial_line_west (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re < 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc (p.start.re - η) p.start.re,
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨-p.initialDirection.re, neg_pos.mpr hd, ?_⟩
  intro x hx
  apply lfr_initial_line_at p f hlen hd.ne hgraph x
  exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) hd.le,
    (div_le_one_of_neg hd).mpr (by linarith only [hx.1])⟩




theorem invariant_succ_lfr_ext_upper_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (closedGraphRegion x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G)
        (invariant_succ_lfr_upper w n hc hUL G))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, false)
  have hd : 0 < p.initialDirection.re :=
    Polyline.initialDirection_re_pos (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, invariant_succ_lfr_upper w n hc hUL G z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re G.xmax
        (invariant_succ_lfr_upper w n hc hUL G) := by
      rw [invariant_succ_lfr_upper_trace w n hc hUL G h]
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, by
        simpa only [stageEdgeTrace, he, ↓reduceDIte] using hz⟩⟩
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := lfr_initial_line_east p (invariant_succ_lfr_upper w n hc hUL G)
    (Q.arc_length (⟨e, he⟩, false)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_east_upper p.start p.initialDirection η hd hη hline



theorem invariant_succ_lfr_ext_lower_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR) :
    let x := layoutPos w (n + 1) (kmswStage w n).nextVertex
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).initialDirection
      (closedGraphRegion x.re G.xmax (invariant_succ_lfr_lower w n hc hUL G)
        (invariant_succ_lfr_upper w n hc hUL G))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, true)
  have hd : p.initialDirection.re < 0 :=
    Polyline.reverse_initialDirection_re_neg (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, invariant_succ_lfr_lower w n hc hUL G z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re G.xmax
        (invariant_succ_lfr_lower w n hc hUL G) := by
      rw [invariant_succ_lfr_lower_trace w n hc hUL G h]
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, by
        simp only [stageEdgeTrace, he, ↓reduceDIte]
        exact lfr_reverse_image_subset _ hz⟩⟩
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := lfr_initial_line_west p (invariant_succ_lfr_lower w n hc hUL G)
    (Q.arc_length (⟨e, he⟩, true)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_west_lower p.start p.initialDirection η hd hη hline

private theorem lfr_forward_line (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hd : 0 < p.initialDirection.re) (f : ℝ → ℝ)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∀ x ∈ Icc p.start.re (p.start.re + p.initialDirection.re),
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) *
        (x - p.start.re) := by
  intro x hx
  have ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
      (div_le_one hd).mpr (by linarith only [hx.2])⟩
  have hg := hgraph _ (lfr_initial_ray_mem_image p hlen ht)
  have hx' : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [div_mul_cancel₀ _ hd.ne']
    ring
  rw [hx'] at hg
  simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hg

private theorem lfr_backward_line (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hd : p.initialDirection.re < 0) (f : ℝ → ℝ)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∀ x ∈ Icc (p.start.re + p.initialDirection.re) p.start.re,
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) *
        (x - p.start.re) := by
  intro x hx
  have ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) hd.le,
      (div_le_one_of_neg hd).mpr (by linarith only [hx.1])⟩
  have hg := hgraph _ (lfr_initial_ray_mem_image p hlen ht)
  have hx' : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [div_mul_cancel₀ _ hd.ne]
    ring
  rw [hx'] at hg
  simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hg

private theorem lfr_first_re_le_finish (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.start.re + p.initialDirection.re ≤ p.finish.re := by
  have hi := Polyline.point_re_le_of_le hp
    (show 1 ≤ p.points.length - 1 by omega) (show p.points.length - 1 < p.points.length by
      omega)
  rw [Polyline.point_last_eq_finish] at hi
  simpa only [Polyline.initialDirection, Complex.sub_re, add_sub_cancel] using hi


private theorem lfr_fresh_arcs (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let s := kmswStage w n
    let x := layoutPos w (n + 1) s.nextVertex
    let u := layoutPos w n (s.west s.active)
    let v := layoutPos w n (s.east s.active)
    layoutArc w (n + 1) s.nextEdge = roofArc x v (n + 1) (rampSlope w n) ∧
      layoutArc w (n + 1) (s.nextEdge + 1) = segmentArc x u := by
  dsimp only
  rw [invariant_succ_lfr_active_arc w n hc hUL,
    invariant_succ_lfr_missing_arc w n hc hUL]
  obtain ⟨h0, h1, h2, h3, _, _⟩ := invariant_succ_lfr_endpoints w n hc hUL
  obtain ⟨hu, hv⟩ := kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  rw [h0, h1, h2, h3, layoutPos_old_vertex w n _ hu, layoutPos_old_vertex w n _ hv]
  exact ⟨rfl, rfl⟩



theorem invariant_succ_lfr_new_cap_lower_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ [(kmswStage w n).nextEdge + 1, (kmswStage w n).active]) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (invariant_succ_lfr_new_cap w n hc hUL G).region := by
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  let p := layoutArc w (n + 1) e
  have hlen := layoutArc_length_two_le w (n + 1) e
  have hmono := layoutArc_points_pairwise w (n + 1) e he
  have hd : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos hmono hlen
  have hgraph : ∀ z ∈ p.image, C.low z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver C.a C.b C.low := by
      rw [invariant_succ_lfr_cap_lower_trace w n hc hUL G h]
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, by
        simp only [stageEdgeTrace, he, ↓reduceDIte]
        change z ∈ (layoutArc w (n + 1) e).image
        exact hz⟩⟩
    exact hzG.2.2.symm
  have hline := lfr_forward_line p hlen hd C.low hgraph
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have huv : u.re < v.re := by
    change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hpfirst := lfr_first_re_le_finish p hmono hlen
  obtain ⟨harc, hseg⟩ := lfr_fresh_arcs w n hc hUL
  change layoutArc w (n + 1) s.nextEdge = roofArc x v (n + 1) (rampSlope w n) at harc
  change layoutArc w (n + 1) (s.nextEdge + 1) = segmentArc x u at hseg
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection
    (graphRegion C.a C.b C.low C.high)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · have hps : p.start = x := by
      change (layoutArc w (n + 1) _).start = x
      rw [hseg]
      exact segmentArc_start _ _
    have hpf : p.finish = u := by
      change (layoutArc w (n + 1) _).finish = u
      rw [hseg]
      exact segmentArc_finish _ _
    let q := layoutArc w (n + 1) s.nextEdge
    have hf := (invariant_succ_lfr_fresh_edge_membership w n hc hUL).1
    have hqB := (Finset.mem_Ico.mp hf).2
    have hqlen := layoutArc_length_two_le w (n + 1) s.nextEdge
    have hqmono := layoutArc_points_pairwise w (n + 1) s.nextEdge hqB
    have hqd : 0 < q.initialDirection.re :=
      Polyline.initialDirection_re_pos hqmono hqlen
    have hqs : q.start = x := by
      change (layoutArc w (n + 1) _).start = x
      rw [harc]
      exact roofArc_start _ _ _ _
    have hqf : q.finish = v := by
      change (layoutArc w (n + 1) _).finish = v
      rw [harc]
      exact roofArc_finish _ _ _ _
    have hqgraph : ∀ z ∈ q.image, C.high z.re = z.im := by
      intro z hz
      have htrace := invariant_succ_lfr_cap_upper_trace w n hc hUL G h
      simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at htrace
      have hzG : z ∈ graphOver C.a C.b C.high := by
        rw [htrace, invariant_succ_lfr_trace_active w n hc hUL h]
        exact hz
      exact hzG.2.2.symm
    have hqline := lfr_forward_line q hqlen hqd C.high hqgraph
    have hH : x.im = (n + 1 : ℝ) := invariant_succ_lfr_new_vertex_height w n hc hUL
    have hqSlope : q.initialDirection.im / q.initialDirection.re = 0 := by
      change (layoutArc w (n + 1) s.nextEdge).initialDirection.im /
        (layoutArc w (n + 1) s.nextEdge).initialDirection.re = _
      rw [harc]
      exact roofArc_initialSlope_top hH
    have huH : u.im < x.im := by
      have huV := (kmswStage_endpoints_lt_nextVertex w n _
        (kmswStage_boundary_ids_lt_nextEdge w n).1).1
      have hh := layoutHeight_le w n _ huV
      change u.im ≤ (n : ℝ) at hh
      linarith only [hh, hH]
    have hpSlope : p.initialDirection.im / p.initialDirection.re < 0 := by
      change (layoutArc w (n + 1) (s.nextEdge + 1)).initialDirection.im /
        (layoutArc w (n + 1) (s.nextEdge + 1)).initialDirection.re < _
      rw [hseg]
      change (u.im - x.im) / (u.re - x.re) < 0
      exact div_neg_of_neg_of_pos (sub_neg.mpr huH) (by linarith only [hxu])
    let η := min p.initialDirection.re q.initialDirection.re
    have hη : 0 < η := lt_min hd hqd
    have hηp : η ≤ p.initialDirection.re := min_le_left _ _
    have hηq : η ≤ q.initialDirection.re := min_le_right _ _
    have hηb : p.start.re + η ≤ C.b := by
      have hh := lfr_first_re_le_finish q hqmono hqlen
      rw [hqs, hqf] at hh
      change p.start.re + η ≤ v.re
      rw [hps]
      linarith only [hh, hηq]
    apply wedgeIn_graphRegion_east_lower_slope p.start p.initialDirection η 0
      hd (by change x.re ≤ p.start.re; rw [hps]) hη hηb
    · intro r hr
      exact hline r ⟨hr.1, by linarith only [hr.2, hηp]⟩
    · exact hpSlope
    · intro r hr
      have hrq : r ∈ Icc q.start.re (q.start.re + q.initialDirection.re) := by
        rw [hps] at hr
        rw [hqs]
        exact ⟨hr.1, by linarith only [hr.2, hηq]⟩
      rw [hqline r hrq, hqSlope, hps, hqs]
  · have ha := (kmswStage_boundary_ids_lt_nextEdge w n).1
    have hps : p.start = u := by
      change (layoutArc w (n + 1) s.active).start = u
      rw [layoutArc_old w n _ ha]
      exact layoutArc_start w n _ ha
    have hpf : p.finish = v := by
      change (layoutArc w (n + 1) s.active).finish = v
      rw [layoutArc_old w n _ ha]
      exact layoutArc_finish w n _ ha
    have hgap : p.start.im < C.high p.start.re := by
      rw [← hgraph p.start (Or.inl rfl)]
      exact C.separated p.start.re (by
        change x.re < p.start.re ∧ p.start.re < v.re
        rw [hps]
        exact ⟨by linarith only [hxu], huv⟩)
    exact wedgeIn_graphRegion_east_lower_continuous p.start p.initialDirection
      p.initialDirection.re hd (by change x.re ≤ p.start.re; rw [hps]; linarith only [hxu])
      hd (by change p.start.re + p.initialDirection.re ≤ v.re; rw [← hpf]; exact hpfirst)
      hline (continuous_roofHeight _ _ _ _).continuousAt hgap



theorem invariant_succ_lfr_new_cap_upper_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1))
    (he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc
        (⟨(kmswStage w n).nextEdge, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc
        (⟨(kmswStage w n).nextEdge, he⟩, true)).initialDirection
      (invariant_succ_lfr_new_cap w n hc hUL G).region := by
  let s := kmswStage w n
  let x := layoutPos w (n + 1) s.nextVertex
  let u := layoutPos w n (s.west s.active)
  let v := layoutPos w n (s.east s.active)
  let C := invariant_succ_lfr_new_cap w n hc hUL G
  let p := (layoutArc w (n + 1) s.nextEdge).reverse
  have hlen : 2 ≤ p.points.length := by
    simpa only [p, Polyline.reverse, List.length_reverse] using
      layoutArc_length_two_le w (n + 1) s.nextEdge
  have hd : p.initialDirection.re < 0 := Polyline.reverse_initialDirection_re_neg
    (layoutArc_points_pairwise w (n + 1) s.nextEdge he)
    (layoutArc_length_two_le w (n + 1) s.nextEdge)
  have harc := (lfr_fresh_arcs w n hc hUL).1
  have hps : p.start = v := by
    rw [Polyline.start_reverse, harc]
    exact roofArc_finish _ _ _ _
  have hgraph : ∀ z ∈ p.image, C.high z.re = z.im := by
    intro z hz
    have htrace := invariant_succ_lfr_cap_upper_trace w n hc hUL G h
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at htrace
    have hzG : z ∈ graphOver C.a C.b C.high := by
      rw [htrace, invariant_succ_lfr_trace_active w n hc hUL h]
      exact lfr_reverse_image_subset _ hz
    exact hzG.2.2.symm
  have hline := lfr_backward_line p hlen hd C.high hgraph
  have huv : u.re < v.re := by
    change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hxu : x.re + 1 = u.re := invariant_succ_lfr_new_vertex_rank w n hc hUL
  have hu : u.re = G.xmin := invariant_succ_lfr_active_west_xmin G hUL
  have hvdom := (invariant_succ_lfr_active_endpoint_values G).2.2.1
  have hvval : v.im = G.upper v.re := (invariant_succ_lfr_active_endpoint_values G).2.2.2
  have hvH : v.im < (n + 1 : ℝ) := by
    have hh := G.upper_le_stage hvdom
    rw [← hvval] at hh
    linarith only [hh]
  have hslope : p.initialDirection.im / p.initialDirection.re = -rampSlope w n := by
    change (layoutArc w (n + 1) s.nextEdge).reverse.initialDirection.im /
      (layoutArc w (n + 1) s.nextEdge).reverse.initialDirection.re = _
    rw [harc]
    exact roofArc_reverse_initialSlope (rampSlope_pos w n) hvH
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  let η := min (-p.initialDirection.re) (v.re - u.re)
  have hη : 0 < η := lt_min (neg_pos.mpr hd) (sub_pos.mpr huv)
  have hηp : η ≤ -p.initialDirection.re := min_le_left _ _
  have hηu : η ≤ v.re - u.re := min_le_right _ _
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection
    (graphRegion C.a C.b C.low C.high)
  apply wedgeIn_graphRegion_west_upper_slope p.start p.initialDirection η (-L) hd
    (by change p.start.re ≤ v.re; rw [hps]) hη
  · change x.re ≤ p.start.re - η
    rw [hps]
    linarith only [hηu, hxu]
  · intro r hr
    exact hline r ⟨by linarith only [hr.1, hηp], hr.2⟩
  · rw [hslope]
    linarith only [hLM]
  · intro r hr
    have hrOld : G.xmin ≤ r := by rw [hps] at hr; linarith only [hr.1, hηu, hu]
    rw [lfr_cap_low_eq_upper w n hc hUL G hrOld, hps]
    have hrv : r ≤ v.re := by simpa only [hps] using hr.2
    have hh := (le_abs_self (G.upper r - G.upper v.re)).trans
      (hLip r ⟨hrOld, hrv.trans hvdom.2⟩ v.re hvdom)
    rw [← hvval, abs_of_nonpos (sub_nonpos.mpr hrv)] at hh
    linarith only [hh]



theorem invariant_succ_lfr_caps_lower_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length)
    (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge) (hmem : e ∈ lfrCapLower w n G i) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (lfrCaps w n hc hUL G i).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [lfrCaps, lfrCapLower, hi, ↓reduceDIte] at hmem ⊢
    have heOld := lfr_cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append_left _ hmem)
    rw [lfr_old_arc w n G h e heOld he false]
    exact G.cap_lower_wedge ⟨i.val, hi⟩ e heOld hmem
  · simp only [lfrCaps, lfrCapLower, hi, ↓reduceDIte] at hmem ⊢
    exact invariant_succ_lfr_new_cap_lower_wedge w n hc hUL G h e he hmem



theorem invariant_succ_lfr_caps_upper_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length)
    (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge) (hmem : e ∈ lfrCapUpper w n G i) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).initialDirection
      (lfrCaps w n hc hUL G i).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [lfrCaps, lfrCapUpper, hi, ↓reduceDIte] at hmem ⊢
    have heOld := lfr_cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append_right _ hmem)
    rw [lfr_old_arc w n G h e heOld he true]
    exact G.cap_upper_wedge ⟨i.val, hi⟩ e heOld hmem
  · simp only [lfrCaps, lfrCapUpper, hi, ↓reduceDIte, List.mem_singleton] at hmem ⊢
    subst e
    exact invariant_succ_lfr_new_cap_upper_wedge w n hc hUL G h he



@[expose] noncomputable def invariant_succ_lfr (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h) where
  toMonotoneStageCertificate :=
    { xmin := (layoutPos w (n + 1) (kmswStage w n).nextVertex).re
      xmax := G.xmax
      hx := by
        have hh := invariant_succ_lfr_new_vertex_xmin w n hc hUL G
        linarith only [hh, G.hx]
      lower := invariant_succ_lfr_lower w n hc hUL G
      upper := invariant_succ_lfr_upper w n hc hUL G
      lower_continuous := invariant_succ_lfr_lower_continuous w n hc hUL G
      upper_continuous := invariant_succ_lfr_upper_continuous w n hc hUL G
      lower_le_upper := invariant_succ_lfr_lower_le_upper w n hc hUL G
      lower_trace := invariant_succ_lfr_lower_trace w n hc hUL G h
      upper_trace := invariant_succ_lfr_upper_trace w n hc hUL G h
      cap := lfrCaps w n hc hUL G
      capLower := lfrCapLower w n G
      capUpper := lfrCapUpper w n G
      cap_lower_trace := invariant_succ_lfr_caps_lower_trace w n hc hUL G h
      cap_upper_trace := invariant_succ_lfr_caps_upper_trace w n hc hUL G h
      cap_edges := invariant_succ_lfr_caps_edges w n hc hUL G
      cap_avoid := invariant_succ_lfr_caps_avoid w n hc hUL G h
      cap_disjoint := invariant_succ_lfr_caps_disjoint w n hc hUL G
      cover := invariant_succ_lfr_cover w n hc hUL G h
      cap_lower_wedge := invariant_succ_lfr_caps_lower_wedge w n hc hUL G h
      cap_upper_wedge := invariant_succ_lfr_caps_upper_wedge w n hc hUL G h
      ext_upper_wedge := invariant_succ_lfr_ext_upper_wedge w n hc hUL G h
      ext_lower_wedge := invariant_succ_lfr_ext_lower_wedge w n hc hUL G h }
  cover_lower := invariant_succ_lfr_cover_lower w n hc hUL G
  cover_upper := invariant_succ_lfr_cover_upper w n hc hUL G
  upper_lipschitz_margin := invariant_succ_lfr_upper_lipschitz_margin w n hc hUL G
  image_height_le := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      invariant_succ_lfr_image_height_le w n hc hUL G h
  pos_layout := invariant_succ_lfr_pos_layout w n hc hUL G h
  arc_layout := invariant_succ_lfr_arc_layout w n hc hUL G h

end DirectedDistances.KMSW
