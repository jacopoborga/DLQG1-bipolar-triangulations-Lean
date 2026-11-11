module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
import DirectedDistances.KMSW.MonotoneStepCommon
import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

private theorem lfr_counts (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. Fresh-left step data from `def-kmsw`, -/
theorem lfr_stage_lists (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge ∧
      (kmswStage w (n + 1)).UL = [(kmswStage w n).nextEdge] ∧
      (kmswStage w (n + 1)).LL =
        ((kmswStage w n).nextEdge + 1) :: (kmswStage w n).LL := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The two fresh geometric edges have the LFR endpoint and presence -/
theorem lfr_endpoints (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    t.west s.nextEdge = s.nextVertex ∧ t.east s.nextEdge = s.east s.active ∧
      t.west (s.nextEdge + 1) = s.nextVertex ∧
      t.east (s.nextEdge + 1) = s.west s.active ∧
      t.present s.nextEdge = true ∧ t.present (s.nextEdge + 1) = false := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The two IDs allocated by an LFR step are fresh. See `def-kmsw`, -/
theorem lfr_fresh_edges (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w n).nextEdge ∈ freshEdges w n ∧
      (kmswStage w n).nextEdge + 1 ∈ freshEdges w n := by
  have hcount := lfr_counts w n hc hUL
  simp [freshEdges, hcount]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The active new edge is drawn as its prescribed roof. See -/
theorem layoutArc_succ_lfr_active (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge) =
      roofArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
        ((kmswStage w n).nextEdge)))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
        ((kmswStage w n).nextEdge))) (n + 1) (rampSlope w n) := by
  have hm : ¬ isFreshLeftMissing w n ((kmswStage w n).nextEdge) := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n _ (lfr_fresh_edges w n hc hUL).1, ite_eq_right hm]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The new missing edge remains a segment. See `def-kmsw`, -/
theorem layoutArc_succ_lfr_missing (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1) =
      segmentArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
        ((kmswStage w n).nextEdge + 1)))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
        ((kmswStage w n).nextEdge + 1))) := by
  have hm : isFreshLeftMissing w n ((kmswStage w n).nextEdge + 1) := by
    simp [isFreshLeftMissing, hc, hUL]
  rw [layoutArc_fresh w n _ (lfr_fresh_edges w n hc hUL).2, ite_eq_left hm]

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The fresh vertex has height `n + 1` and lies one rank west of -/
theorem lfr_new_vertex_position (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).im = (n + 1 : ℝ) ∧
      (layoutPos w (n + 1) (kmswStage w n).nextVertex).re + 1 =
        (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re := by
  have hg := (lfr_counts w n hc hUL).2
  have hheight := layoutHeight_created_vertex w n hg
  have hgap := freshLeft_missing_edge_rank_gap w n hc hUL
  have hend := lfr_endpoints w n hc hUL
  dsimp only at hgap
  rw [hend.2.2.2.1, hend.2.2.1] at hgap
  constructor
  · rw [layoutPos, hheight]
    norm_cast
  · dsimp [layoutPos] at hgap ⊢
    rw [layoutRank_old_vertex w n _
      ((kmswStage_endpoints_lt_nextVertex w n _
        (kmswStage_boundary_ids_lt_nextEdge w n).1).1)] at hgap
    linarith

private theorem chain_start_rank_lower (s : State) (ρ : ℕ → ℚ) :
    ∀ (es : List ℕ) (v : ℕ), WestEastChain s es →
      (∀ e ∈ es, ρ (s.west e) < ρ (s.east e)) →
      boundaryStart s es = some v →
      ∀ e ∈ es, ρ v ≤ ρ (s.west e) := by
  intro es
  induction es with
  | nil => intro v _ _ _ e he; simp at he
  | cons a es ih =>
    intro v hchain hstrict hstart e he
    have hwa : s.west a = v := by simpa [boundaryStart] using hstart
    rcases List.mem_cons.mp he with he | he
    · subst e
      rw [hwa]
    · cases es with
      | nil => simp at he
      | cons b bs =>
        have hab : s.east a = s.west b := by
          simpa using hchain.rel_head? (by simp)
        have htailStart : boundaryStart s (b :: bs) = some (s.east a) := by
          simp [boundaryStart, hab]
        have hstrictTail : ∀ f ∈ b :: bs, ρ (s.west f) < ρ (s.east f) := by
          intro f hf
          exact hstrict f (by simp [hf])
        have htail := ih (s.east a) hchain.tail hstrictTail htailStart e he
        have hlt : ρ v < ρ (s.west e) := calc
          ρ v = ρ (s.west a) := by rw [hwa]
          _ < ρ (s.east a) := hstrict a (by simp)
          _ ≤ ρ (s.west e) := htail
        exact hlt.le

private theorem lfr_lower_chain_rank_bound (w : ℕ → Fin 3) (n : ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    ∀ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) ≤
        kmswStageRank w n ((kmswStage w n).west e) := by
  let s := kmswStage w n
  obtain ⟨xs, hULlast⟩ := kmswStage_UL_last w n
  have hdrop : s.UL.dropLast = [] := by
    have h := congrArg List.reverse hUL
    simpa using h
  have hxs : xs = [] := by rw [hULlast] at hdrop; simpa using hdrop
  have hULsingle : s.UL = [s.active] := by
    rw [hULlast, hxs]
    simp [s]
  have hstartLower : boundaryStart s (s.LL ++ s.LR) =
      some (s.west s.active) := by
    have h := (kmswStage_boundary_chain_invariant w n).2.2.1
    change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at h
    have hu : boundaryStart s (s.UL ++ s.UR) = some (s.west s.active) := by
      simp [hULsingle, boundaryStart]
    exact h.symm.trans hu
  have hstrict : ∀ e ∈ s.LL ++ s.LR,
      kmswStageRank w n (s.west e) < kmswStageRank w n (s.east e) := by
    intro e he
    have heall : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at he ⊢
      rcases he with he | he
      · exact Or.inl (Or.inr he)
      · exact Or.inr he
    exact kmswStageRank_strict w n e
      ((kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simpa [s] using heall))
  exact chain_start_rank_lower s (kmswStageRank w n) (s.LL ++ s.LR)
    (s.west s.active) (kmswStage_boundary_chain_invariant w n).2.1 hstrict
    hstartLower

private theorem old_image_below {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {z : ℂ} (hz : z ∈ P.image) :
    G.xmin ≤ z.re ∧ z.re ≤ G.xmax ∧ z.im ≤ G.upper z.re := by
  have hr : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inl hz
  exact ⟨hr.1, hr.2.1, hr.2.2.2⟩

private theorem lfr_xmin_eq_active_west {w : ℕ → Fin 3} {n : ℕ}
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    G.xmin = (layoutPos w n
      ((kmswStage w n).west (kmswStage w n).active)).re := by
  let s := kmswStage w n
  let u := s.west s.active
  have huLt := (kmswStage_endpoints_lt_nextVertex w n s.active
    (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have huImage : layoutPos w n u ∈ P.image := by
    rw [← G.pos_layout ⟨u, huLt⟩]
    exact Or.inl ⟨⟨u, huLt⟩, rfl⟩
  have hxminLe := (old_image_below G huImage).1
  let z : ℂ := ⟨G.xmin, G.lower G.xmin⟩
  have hz : z ∈ graphOver G.xmin G.xmax G.lower :=
    ⟨le_rfl, G.hx, rfl⟩
  rw [G.lower_trace] at hz
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hel, hzedge⟩ := Set.mem_iUnion.mp he
  have hebound : e < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    rcases List.mem_append.mp hel with heLL | heLR
    · exact List.mem_append_left _ (List.mem_append_right _ heLL)
    · exact List.mem_append_right _ heLR
  have hzarc : z ∈ (layoutArc w n e).image := by
    simpa only [stageEdgeTrace, hebound, ↓reduceDIte, G.arc_layout,
      Bool.false_eq_true, ↓reduceIte] using hzedge
  obtain ⟨f, hgraph⟩ := layoutArc_image_graph w n e hebound
  rw [hgraph] at hzarc
  have hrank := lfr_lower_chain_rank_bound w n hUL e hel
  have hrankR : (layoutPos w n u).re ≤
      (layoutPos w n ((kmswStage w n).west e)).re := by
    change (kmswStageRank w n u : ℝ) ≤
      (kmswStageRank w n ((kmswStage w n).west e) : ℝ)
    exact_mod_cast hrank
  have huLe : (layoutPos w n u).re ≤ G.xmin := by
    change (layoutPos w n u).re ≤ z.re
    exact hrankR.trans hzarc.1
  exact le_antisymm hxminLe huLe

private theorem upper_height {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (x : ℝ)
    (hx : x ∈ Icc G.xmin G.xmax) : G.upper x ≤ n := by
  let z : ℂ := ⟨x, G.upper x⟩
  have hz : z ∈ graphOver G.xmin G.xmax G.upper := ⟨hx.1, hx.2, rfl⟩
  rw [G.upper_trace] at hz
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
  obtain ⟨_, hz⟩ := Set.mem_iUnion.mp he
  have htrace : stageEdgeTrace P e ⊆ P.image := by
    unfold stageEdgeTrace
    split
    · intro z hz
      exact Or.inr ⟨_, hz⟩
    · exact empty_subset _
  exact G.image_height_le z (htrace hz)

private theorem finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
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

private theorem reverse_point (p : Polyline) (i : ℕ) (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.reverse.getD i p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_reverse i hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]

private theorem reverse_segment (p : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold Polyline.segmentAt
  rw [reverse_point p i (by omega), reverse_point p (i + 1) hi]
  have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [h₁, h₂, segment_symm]

private theorem reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ finish_mem_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    rw [reverse_segment p i hi'] at hz
    exact Or.inr ⟨p.points.length - 2 - i, by omega, hz⟩

private theorem reverse_image (p : Polyline) : p.reverse.image = p.image := by
  apply Subset.antisymm (reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using reverse_image_subset p.reverse

private theorem reverse_interior (p : Polyline) : p.reverse.interior = p.interior := by
  rw [Polyline.interior, reverse_image, Polyline.start_reverse, Polyline.finish_reverse]
  rw [Set.pair_comm]
  rfl

private theorem dart_interior (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    (layoutDart w m d).interior = (layoutArc w m d.1.val).interior := by
  unfold layoutDart
  split
  · exact reverse_interior _
  · rfl

private theorem dart_old (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  change (if d.2 then (layoutArc w (n + 1) d.1.val).reverse
    else layoutArc w (n + 1) d.1.val) = _
  rw [layoutArc_old w n d.1.val d.1.isLt]
  rfl

private theorem arc_subset_old_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutArc w n e).image ⊆ P.image := by
  intro z hz
  apply Or.inr
  refine ⟨(⟨e, he⟩, false), ?_⟩
  simpa only [G.arc_layout, Bool.false_eq_true, ↓reduceIte] using hz

private theorem segmentArc_interior_re_bounds {a b z : ℂ} (hab : a.re < b.re)
    (hz : z ∈ (segmentArc a b).interior) : a.re < z.re ∧ z.re < b.re := by
  have hzImage : z ∈ (segmentArc a b).image := hz.1
  rw [segmentArc_image hab] at hzImage
  obtain ⟨ha, hb, him⟩ := hzImage
  have hnot : z ≠ a ∧ z ≠ b := by
    simpa [segmentArc, Polyline.start, Polyline.finish] using hz.2
  constructor
  · by_contra hn
    have heq : z.re = a.re := le_antisymm (not_lt.mp hn) ha
    have him' : z.im = a.im := by rw [him, heq]; simp [segmentHeight]
    exact (hnot.1 (Complex.ext heq him')).elim
  · by_contra hn
    have heq : z.re = b.re := le_antisymm hb (not_lt.mp hn)
    have him' : z.im = b.im := by
      rw [him, heq]
      unfold segmentHeight
      have hden : b.re - a.re ≠ 0 := ne_of_gt (sub_pos.mpr hab)
      field_simp [hden]
      ring
    exact (hnot.2 (Complex.ext heq him')).elim

private theorem lfr_active_arc_shape (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge) =
      roofArc (layoutPos w (n + 1) (kmswStage w n).nextVertex)
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) := by
  rw [layoutArc_succ_lfr_active w n hc hUL]
  have hEnds := lfr_endpoints w n hc hUL
  dsimp only at hEnds
  rw [hEnds.1, hEnds.2.1]
  have hv := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [layoutPos_old_vertex w n _ hv]

private theorem lfr_missing_arc_shape (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1) =
      segmentArc (layoutPos w (n + 1) (kmswStage w n).nextVertex)
        (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)) := by
  rw [layoutArc_succ_lfr_missing w n hc hUL]
  have hEnds := lfr_endpoints w n hc hUL
  dsimp only at hEnds
  rw [hEnds.2.2.1, hEnds.2.2.2.1]
  have hu := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  rw [layoutPos_old_vertex w n _ hu]

private theorem lfr_missing_interior_re_bounds (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {z : ℂ} (hz : z ∈ (layoutArc w (n + 1)
      ((kmswStage w n).nextEdge + 1)).interior) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).re < z.re ∧
      z.re < (layoutPos w n
        ((kmswStage w n).west (kmswStage w n).active)).re := by
  have hpos := lfr_new_vertex_position w n hc hUL
  have hgap : (layoutPos w n ((kmswStage w n).west
      (kmswStage w n).active)).re -
      (layoutPos w (n + 1) (kmswStage w n).nextVertex).re = 1 := by
    linarith [hpos.2]
  rw [lfr_missing_arc_shape w n hc hUL] at hz
  exact segmentArc_interior_re_bounds (by linarith) hz

private theorem active_trace_upper {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    (layoutArc w n (kmswStage w n).active).image ⊆
      graphOver G.xmin G.xmax G.upper := by
  intro z hz
  rw [G.upper_trace]
  apply Set.mem_iUnion.mpr ⟨(kmswStage w n).active, ?_⟩
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hmem : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by
    rw [hUL]
    simp
  apply Set.mem_iUnion.mpr ⟨hmem, ?_⟩
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).1
  simpa only [stageEdgeTrace, hb, ↓reduceDIte, G.arc_layout,
    Bool.false_eq_true, ↓reduceIte] using hz

private theorem active_endpoints_upper {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
    let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    a ∈ graphOver G.xmin G.xmax G.upper ∧
      b ∈ graphOver G.xmin G.xmax G.upper := by
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).1
  constructor
  · apply active_trace_upper G
    rw [← layoutArc_start w n _ hb]
    exact Or.inl rfl
  · apply active_trace_upper G
    rw [← layoutArc_finish w n _ hb]
    exact finish_mem_image _

private theorem lfr_active_roof_endpoint_bounds (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).im ≤ (n + 1 : ℝ) ∧
      (layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).im ≤ (n + 1 : ℝ) := by
  obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n
    (kmswStage w n).nextEdge (lfr_fresh_edges w n hc hUL).1
  have hEnds := lfr_endpoints w n hc hUL
  dsimp only at hEnds
  rw [hEnds.1] at ha
  rw [hEnds.2.1] at hb
  have hv := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [layoutPos_old_vertex w n _ hv] at hb
  exact ⟨ha, hb⟩

private theorem lfr_roof_above_upper {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    ∀ x ∈ Icc (layoutPos w n
      ((kmswStage w n).west (kmswStage w n).active)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re,
      x < (layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).re →
      G.upper x < roofHeight
        (layoutPos w (n + 1) (kmswStage w n).nextVertex)
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) x := by
  intro x hx hxv
  have hEnds := active_endpoints_upper G
  rcases hEnds with ⟨ha, hb⟩
  rcases ha with ⟨_, _, _⟩
  rcases hb with ⟨hbmin, hbmax, hbheight⟩
  have hxmin := lfr_xmin_eq_active_west hUL G
  have hxdom : x ∈ Icc G.xmin G.xmax := by
    constructor
    · rw [hxmin]
      exact hx.1
    · exact hxv.le.trans hbmax
  have hbdom : (layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active)).re ∈ Icc G.xmin G.xmax :=
    ⟨hbmin, hbmax⟩
  have hheight := upper_height G x hxdom
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  have hmid : (n : ℝ) < (n + 1 : ℝ) := by norm_num
  have htop : G.upper x < (n + 1 : ℝ) := hheight.trans_lt hmid
  have hnewPos := lfr_new_vertex_position w n hc hUL
  have hxnew : (layoutPos w (n + 1) (kmswStage w n).nextVertex).re < x := by
    exact (lt_of_lt_of_le (by linarith [hnewPos.2]) hx.1)
  have hrise : G.upper x <
      (n + 1 : ℝ) + rampSlope w n *
        (x - (layoutPos w (n + 1) (kmswStage w n).nextVertex).re) := by
    have hM := rampSlope_pos w n
    have hdx : 0 < x -
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re := sub_pos.mpr hxnew
    linarith [mul_pos hM hdx]
  have hfall : G.upper x <
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).im +
        rampSlope w n *
          ((layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re - x) := by
    have hLip' := hLip x hxdom
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re hbdom
    have hL : G.upper x - G.upper
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re ≤
        L * ((layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re - x) := by
      have hleft := (le_abs_self (G.upper x - G.upper
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re)).trans hLip'
      rw [abs_of_nonpos (sub_nonpos.mpr hxv.le), neg_sub] at hleft
      exact hleft
    rw [← hbheight] at hL
    have hdist : 0 < (layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).re - x := sub_pos.mpr hxv
    have hML : L * ((layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).re - x) <
        rampSlope w n * ((layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).re - x) :=
      mul_lt_mul_of_pos_right hLM hdist
    linarith
  have hrise' : G.upper x <
      (layoutPos w (n + 1) (kmswStage w n).nextVertex).im +
        rampSlope w n *
          (x - (layoutPos w (n + 1) (kmswStage w n).nextVertex).re) := by
    rw [hnewPos.1]
    exact hrise
  unfold roofHeight
  exact lt_min htop (lt_min hrise' hfall)

private theorem lfr_active_interior_avoids_old_image {w : ℕ → Fin 3}
    {n : ℕ} {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {z : ℂ} (hz : z ∈ (layoutArc w (n + 1)
      ((kmswStage w n).nextEdge)).interior) : z ∉ P.image := by
  have ⟨ha, hb⟩ := lfr_active_roof_endpoint_bounds w n hc hUL
  have hfresh := (lfr_fresh_edges w n hc hUL).1
  have hfit := freshEdges_ramp_widths_lt w n _ hfresh
  have hEnds := lfr_endpoints w n hc hUL
  dsimp only at hEnds
  rw [hEnds.1, hEnds.2.1] at hfit
  have hv := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [layoutPos_old_vertex w n _ hv] at hfit
  rw [lfr_active_arc_shape w n hc hUL] at hz
  rw [roofArc_interior (rampSlope_pos w n) ha hb hfit] at hz
  intro hzP
  have hbounds := old_image_below G hzP
  have hxmin := lfr_xmin_eq_active_west hUL G
  by_cases hleft : z.re < G.xmin
  · exact (not_lt_of_ge hbounds.1) hleft
  · have hwest : (layoutPos w n
        ((kmswStage w n).west (kmswStage w n).active)).re ≤ z.re := by
      rw [← hxmin]
      exact le_of_not_gt hleft
    have heast : z.re ≤ (layoutPos w n
        ((kmswStage w n).east (kmswStage w n).active)).re := hz.2.1.le
    have hroof := lfr_roof_above_upper G hc hUL z.re ⟨hwest, heast⟩ hz.2.1
    exact (not_lt_of_ge hbounds.2.2) (hz.2.2 ▸ hroof)

private theorem lfr_missing_interior_avoids_old_image {w : ℕ → Fin 3}
    {n : ℕ} {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {z : ℂ} (hz : z ∈ (layoutArc w (n + 1)
      ((kmswStage w n).nextEdge + 1)).interior) : z ∉ P.image := by
  have hzre := lfr_missing_interior_re_bounds w n hc hUL hz
  have hxmin := lfr_xmin_eq_active_west hUL G
  intro hzP
  have hbounds := old_image_below G hzP
  rw [hxmin] at hbounds
  exact (not_lt_of_ge hbounds.1) hzre.2

private theorem lfr_old_arc_interior_subset_image {w : ℕ → Fin 3}
    {n : ℕ} {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge)
    {z : ℂ} (hz : z ∈ (layoutArc w n e).interior) : z ∈ P.image :=
  arc_subset_old_image G e he hz.1

private theorem lfr_roof_separates_missing_segment {a u v : ℂ} {H M L : ℝ}
    (hau : u.re - a.re = 1) (haH : a.im = H) (huH : u.im < H)
    (hL : 0 ≤ L) (hLM : L < M) (hSM : H - u.im < M)
    (huv : u.re < v.re)
    (hEnd : u.im ≤ v.im + L * (v.re - u.re)) :
    ∀ x ∈ Ioo a.re u.re,
      segmentHeight a u x < roofHeight a v H M x := by
  let S := H - u.im
  let L' := max L S
  have hS : 0 < S := sub_pos.mpr huH
  have hL'M : L' < M := max_lt_iff.mpr ⟨hLM, hSM⟩
  have hL'0 : 0 ≤ L' := le_max_of_le_left hL
  have hSle : S ≤ L' := le_max_right L S
  have hLle : L ≤ L' := le_max_left L S
  have hseg (x : ℝ) : segmentHeight a u x = u.im + S * (u.re - x) := by
    have huRe : u.re = a.re + 1 := by linarith [hau]
    unfold segmentHeight
    rw [haH, huRe]
    rw [show a.re + 1 - a.re = 1 by ring, div_one]
    dsimp [S]
    ring
  intro x hx
  have hax : 0 < x - a.re := sub_pos.mpr hx.1
  have hxu : 0 < u.re - x := sub_pos.mpr hx.2
  have hxu1 : u.re - x < 1 := by linarith [hau, hx.1]
  have hbelow : segmentHeight a u x < H := by
    rw [hseg x]
    have hmul := mul_lt_mul_of_pos_left hxu1 hS
    dsimp [S] at hmul ⊢
    linarith
  have hMpos : 0 < M := lt_of_le_of_lt hL hLM
  have hrise : segmentHeight a u x < H + M * (x - a.re) := by
    exact lt_trans hbelow (lt_add_of_pos_right _ (mul_pos hMpos hax))
  have hEnd' : u.im ≤ v.im + L' * (v.re - u.re) := by
    calc
      u.im ≤ v.im + L * (v.re - u.re) := hEnd
      _ ≤ v.im + L' * (v.re - u.re) := by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_right hLle (sub_nonneg.mpr huv.le)) v.im
  have hfall : segmentHeight a u x < v.im + M * (v.re - x) := by
    have hdist : 0 < v.re - x := sub_pos.mpr (lt_trans hx.2 huv)
    have hbound' := mul_le_mul_of_nonneg_right hSle hxu.le
    calc
      segmentHeight a u x = u.im + S * (u.re - x) := hseg x
      _ ≤ v.im + L' * (v.re - u.re) + L' * (u.re - x) :=
        add_le_add hEnd' hbound'
      _ = v.im + L' * (v.re - x) := by ring
      _ < v.im + M * (v.re - x) := by
        simpa [add_comm] using add_lt_add_right
          (mul_lt_mul_of_pos_right hL'M hdist) v.im
  unfold roofHeight
  exact lt_min hbelow (lt_min (by simpa [haH] using hrise) hfall)

private theorem lfr_fresh_pair_disjoint {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    Disjoint (layoutArc w (n + 1) ((kmswStage w n).nextEdge)).interior
        (layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1)).interior := by
  have ha := lfr_active_arc_shape w n hc hUL
  have hb := lfr_missing_arc_shape w n hc hUL
  have hpos := lfr_new_vertex_position w n hc hUL
  let a := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let u := layoutPos w n ((kmswStage w n).west ((kmswStage w n).active))
  let v := layoutPos w n ((kmswStage w n).east ((kmswStage w n).active))
  have hau : u.re - a.re = 1 := by dsimp [a, u]; linarith [hpos.2]
  have hAU : a.re < u.re := by linarith [hau]
  have huv : u.re < v.re := by
    change (kmswStageRank w n ((kmswStage w n).west
        ((kmswStage w n).active)) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east
        ((kmswStage w n).active)) : ℝ)
    exact_mod_cast kmswStageRank_strict w n (kmswStage w n).active
      (kmswStage_boundary_ids_lt_nextEdge w n).1
  obtain ⟨L, hL, hLM, hLip⟩ := G.upper_lipschitz_margin
  have hEnds := active_endpoints_upper G
  have huGraph := hEnds.1
  have hvGraph := hEnds.2
  have huEq : G.upper u.re = u.im := by
    dsimp [u]
    exact huGraph.2.2.symm
  have hvEq : G.upper v.re = v.im := by
    dsimp [v]
    exact hvGraph.2.2.symm
  have huDom : u.re ∈ Icc G.xmin G.xmax := by
    dsimp [u]
    exact ⟨huGraph.1, huGraph.2.1⟩
  have hvDom : v.re ∈ Icc G.xmin G.xmax := by
    dsimp [v]
    exact ⟨hvGraph.1, hvGraph.2.1⟩
  have hLipEnds := hLip u.re huDom v.re hvDom
  have hdiff : u.im - v.im ≤ |G.upper u.re - G.upper v.re| := by
    rw [huEq, hvEq]
    exact le_abs_self _
  have habs : |u.re - v.re| = v.re - u.re := by
    rw [abs_of_nonpos (sub_nonpos.mpr huv.le)]
    ring
  rw [habs] at hLipEnds
  have hEnd : u.im ≤ v.im + L * (v.re - u.re) := by
    have hh := hdiff.trans hLipEnds
    linarith
  have huH : u.im < (n + 1 : ℝ) := by
    have hle : u.im ≤ n := by
      change layoutHeight w n ((kmswStage w n).west (kmswStage w n).active) ≤ n
      exact layoutHeight_le w n _
        ((kmswStage_endpoints_lt_nextVertex w n _
          (kmswStage_boundary_ids_lt_nextEdge w n).1).1)
    exact lt_of_le_of_lt hle (by norm_num)
  have hSM : (n + 1 : ℝ) - u.im < rampSlope w n := by
    have hu0 : 0 ≤ u.im := by
      change 0 ≤ layoutHeight w n ((kmswStage w n).west (kmswStage w n).active)
      exact layoutHeight_nonneg w n _
    linarith [rampSlope_roof_lt w n]
  have hfit := freshEdges_ramp_widths_lt w n (kmswStage w n).nextEdge
    (lfr_fresh_edges w n hc hUL).1
  have hEdges := lfr_endpoints w n hc hUL
  dsimp only at hEdges
  rw [hEdges.1, hEdges.2.1] at hfit
  have hvOld := (kmswStage_endpoints_lt_nextVertex w n
    (kmswStage w n).active (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [layoutPos_old_vertex w n _ hvOld] at hfit
  have ⟨haBound, hbBound⟩ := lfr_active_roof_endpoint_bounds w n hc hUL
  apply Set.disjoint_left.mpr
  intro z hzRoof hzSeg
  rw [ha] at hzRoof
  rw [roofArc_interior (rampSlope_pos w n) haBound hbBound hfit] at hzRoof
  rw [hb] at hzSeg
  have hseg := segmentArc_interior_re_bounds hAU hzSeg
  have hzImage := hzSeg.1
  rw [segmentArc_image hAU] at hzImage
  obtain ⟨_, _, hzHeight⟩ := hzImage
  have hsepAll := lfr_roof_separates_missing_segment
    (a := a) (u := u) (v := v) (H := n + 1) (M := rampSlope w n) (L := L)
    (by dsimp [a, u]; linarith [hpos.2]) (by dsimp [a]; exact hpos.1)
    (by dsimp [u]; exact huH) hL hLM hSM huv hEnd
  have hsep := hsepAll z.re ⟨hseg.1, hseg.2⟩
  have hroofHeight := hzRoof.2.2
  have heq : segmentHeight a u z.re =
      roofHeight a v (n + 1) (rampSlope w n) z.re := hzHeight.symm.trans hroofHeight
  rw [heq] at hsep
  exact (lt_irrefl _ hsep)

private theorem lfr_edge_cases (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (e : Fin (kmswStage w (n + 1)).nextEdge) :
    e.val < (kmswStage w n).nextEdge ∨
      e.val = (kmswStage w n).nextEdge ∨
      e.val = (kmswStage w n).nextEdge + 1 := by
  have hcount := (lfr_counts w n hc hUL).1
  have he : e.val < (kmswStage w n).nextEdge + 2 := by
    simpa only [hcount] using e.isLt
  omega

private theorem lfr_fresh_interior_avoids_old_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (e : Fin (kmswStage w (n + 1)).nextEdge)
    (he : (kmswStage w n).nextEdge ≤ e.val) {z : ℂ}
    (hz : z ∈ (layoutArc w (n + 1) e.val).interior) : z ∉ P.image := by
  rcases lfr_edge_cases w n hc hUL e with hold | hfresh | hmissing
  · omega
  · have hz' : z ∈ (layoutArc w (n + 1)
        ((kmswStage w n).nextEdge)).interior := by
      rw [← hfresh]
      exact hz
    exact lfr_active_interior_avoids_old_image G hc hUL hz'
  · have hz' : z ∈ (layoutArc w (n + 1)
        ((kmswStage w n).nextEdge + 1)).interior := by
      rw [← hmissing]
      exact hz
    exact lfr_missing_interior_avoids_old_image G hc hUL hz'

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The LFR successor interiors are pairwise disjoint. See `def-kmsw`, -/
theorem layoutGood_succ_lfr_interior_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d e : StageDart (kmswStage w (n + 1)).nextEdge,
      e ≠ d → e ≠ edgeFlip _ d →
        Disjoint (layoutDart w (n + 1) d).interior
          (layoutDart w (n + 1) e).interior := by
  intro d e hne hflip
  have hdOld : d.1.val < (kmswStage w n).nextEdge ∨
      d.1.val = (kmswStage w n).nextEdge ∨
      d.1.val = (kmswStage w n).nextEdge + 1 := lfr_edge_cases w n hc hUL d.1
  have heOld : e.1.val < (kmswStage w n).nextEdge ∨
      e.1.val = (kmswStage w n).nextEdge ∨
      e.1.val = (kmswStage w n).nextEdge + 1 := lfr_edge_cases w n hc hUL e.1
  by_cases hd : d.1.val < (kmswStage w n).nextEdge
  · by_cases he : e.1.val < (kmswStage w n).nextEdge
    · let d0 : StageDart (kmswStage w n).nextEdge := (⟨d.1.val, hd⟩, d.2)
      let e0 : StageDart (kmswStage w n).nextEdge := (⟨e.1.val, he⟩, e.2)
      have hdIncl : stageDartIncl w n d0 = d := by
        cases d with
        | mk edge b => rfl
      have heIncl : stageDartIncl w n e0 = e := by
        cases e with
        | mk edge b => rfl
      rw [← hdIncl, ← heIncl, dart_old, dart_old]
      apply (layoutGood_of_invariant G).interior_disjoint
      · intro h
        exact hne (congrArg (stageDartIncl w n) h)
      · intro h
        exact hflip (congrArg (stageDartIncl w n) h)
    · have heFresh : (kmswStage w n).nextEdge ≤ e.1.val := Nat.le_of_not_gt he
      rw [dart_interior, dart_interior, layoutArc_old w n d.1.val hd]
      apply Set.disjoint_left.mpr
      intro z hzOld hzFresh
      have hzImage := lfr_old_arc_interior_subset_image G d.1.val hd hzOld
      exact lfr_fresh_interior_avoids_old_image G hc hUL e.1 heFresh hzFresh hzImage
  · have hdFresh : (kmswStage w n).nextEdge ≤ d.1.val := Nat.le_of_not_gt hd
    by_cases he : e.1.val < (kmswStage w n).nextEdge
    · rw [dart_interior, dart_interior, layoutArc_old w n e.1.val he]
      apply Set.disjoint_left.mpr
      intro z hzFresh hzOld
      have hzImage := lfr_old_arc_interior_subset_image G e.1.val he hzOld
      exact lfr_fresh_interior_avoids_old_image G hc hUL d.1 hdFresh
        hzFresh hzImage
    · have heFresh : (kmswStage w n).nextEdge ≤ e.1.val := Nat.le_of_not_gt he
      have hidne : d.1.val ≠ e.1.val := by
        intro hid
        have hfin : d.1 = e.1 := Fin.ext hid
        rcases d with ⟨dEdge, dBool⟩
        rcases e with ⟨eEdge, eBool⟩
        dsimp only at hfin
        subst eEdge
        cases dBool <;> cases eBool
        · exact hne rfl
        · exact hflip rfl
        · exact hflip rfl
        · exact hne rfl
      have hcount := (lfr_counts w n hc hUL).1
      have hdlt : d.1.val < (kmswStage w n).nextEdge + 2 := by
        simpa only [hcount] using d.1.isLt
      have helt : e.1.val < (kmswStage w n).nextEdge + 2 := by
        simpa only [hcount] using e.1.isLt
      have hcases :
          (d.1.val = (kmswStage w n).nextEdge ∧
            e.1.val = (kmswStage w n).nextEdge + 1) ∨
          (d.1.val = (kmswStage w n).nextEdge + 1 ∧
            e.1.val = (kmswStage w n).nextEdge) := by
        omega
      rw [dart_interior, dart_interior]
      rcases hcases with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
      · rw [hd0, he1]
        exact lfr_fresh_pair_disjoint G hc hUL
      · rw [hd1, he0]
        exact (lfr_fresh_pair_disjoint G hc hUL).symm

private theorem lfr_new_vertex_not_mem_fresh_arc_interior
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (e : Fin (kmswStage w (n + 1)).nextEdge)
    (he : (kmswStage w n).nextEdge ≤ e.val)
    (hz : layoutPos w (n + 1) (kmswStage w n).nextVertex ∈
      (layoutArc w (n + 1) e.val).interior) : False := by
  have hstart : (layoutArc w (n + 1) e.val).start =
      layoutPos w (n + 1) (kmswStage w n).nextVertex := by
    rcases lfr_edge_cases w n hc hUL e with hold | hfresh | hmissing
    · omega
    · have hs := layoutArc_start w (n + 1) e.val (by
        have hcount := (lfr_counts w n hc hUL).1
        omega)
      have hpos := congrArg (layoutPos w (n + 1))
        (lfr_endpoints w n hc hUL).1
      rw [← hfresh] at hpos
      exact hs.trans hpos
    · have hs := layoutArc_start w (n + 1) e.val (by
        have hcount := (lfr_counts w n hc hUL).1
        omega)
      have hpos := congrArg (layoutPos w (n + 1))
        (lfr_endpoints w n hc hUL).2.2.1
      rw [← hmissing] at hpos
      exact hs.trans hpos
  have hnot : layoutPos w (n + 1) (kmswStage w n).nextVertex ≠
      (layoutArc w (n + 1) e.val).start ∧
      layoutPos w (n + 1) (kmswStage w n).nextVertex ≠
        (layoutArc w (n + 1) e.val).finish := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hz.2
  exact hnot.1 hstart.symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The LFR successor interiors avoid all stage vertices. -/
theorem layoutGood_succ_lfr_interior_avoids_vertices (w : ℕ → Fin 3)
    (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ (d : StageDart (kmswStage w (n + 1)).nextEdge)
      (v : Fin (kmswStage w (n + 1)).nextVertex),
      layoutPos w (n + 1) v.val ∉ (layoutDart w (n + 1) d).interior := by
  intro d v
  by_cases hd : d.1.val < (kmswStage w n).nextEdge
  · let d0 : StageDart (kmswStage w n).nextEdge := (⟨d.1.val, hd⟩, d.2)
    have hd0 : stageDartIncl w n d0 = d := rfl
    rw [← hd0, dart_old]
    by_cases hv : v.val < (kmswStage w n).nextVertex
    · rw [layoutPos_old_vertex w n v.val hv]
      exact (layoutGood_of_invariant G).interior_avoids_vertices d0 ⟨v.val, hv⟩
    · have hb := v.isLt
      simp only [(lfr_counts w n hc hUL).2] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq, dart_interior]
      intro hz
      have him := G.image_height_le _ (arc_subset_old_image G d.1.val hd hz.1)
      rw [(lfr_new_vertex_position w n hc hUL).1] at him
      linarith
  · have hdf : (kmswStage w n).nextEdge ≤ d.1.val := Nat.le_of_not_gt hd
    rw [dart_interior]
    by_cases hv : v.val < (kmswStage w n).nextVertex
    · intro hz
      have hvimage : layoutPos w (n + 1) v.val ∈ P.image := by
        rw [layoutPos_old_vertex w n v.val hv, ← G.pos_layout ⟨v.val, hv⟩]
        exact Or.inl ⟨⟨v.val, hv⟩, rfl⟩
      exact lfr_fresh_interior_avoids_old_image G hc hUL d.1 hdf hz hvimage
    · have hb := v.isLt
      simp only [(lfr_counts w n hc hUL).2] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq]
      exact lfr_new_vertex_not_mem_fresh_arc_interior w n hc hUL d.1 hdf


private theorem lfr_ray_interior (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hbound : (0 < p.initialDirection.re ∧ (p.point 1).re ≤ p.finish.re) ∨
      (p.initialDirection.re < 0 ∧ p.finish.re ≤ (p.point 1).re))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    p.start + t • p.initialDirection ∈ p.interior := by
  have hpoint : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  refine ⟨Or.inr ⟨0, by omega, ?_⟩, ?_⟩
  · change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
    rw [Polyline.point_zero_eq_start, hpoint]
    exact ⟨1 - t, t, by linarith, ht.le, by ring, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    have hre : (p.start + t • p.initialDirection).re =
        p.start.re + t * p.initialDirection.re := by simp
    have hdir : p.initialDirection.re = (p.point 1).re - p.start.re := by
      simp only [Polyline.initialDirection, Complex.sub_re]
    rcases hbound with ⟨hp, hb⟩ | ⟨hn, hb⟩
    · have hlow : p.start.re < (p.start + t • p.initialDirection).re := by
        rw [hre]
        exact lt_add_of_pos_right _ (mul_pos ht hp)
      have hhigh : (p.start + t • p.initialDirection).re < p.finish.re := by
        rw [hre]
        nlinarith only [ht1, hp, hb, hdir]
      exact ⟨fun h => (ne_of_gt hlow) (congrArg Complex.re h),
        fun h => (ne_of_lt hhigh) (congrArg Complex.re h)⟩
    · have hhigh : (p.start + t • p.initialDirection).re < p.start.re := by
        rw [hre]
        exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg ht hn)
      have hlow : p.finish.re < (p.start + t • p.initialDirection).re := by
        rw [hre]
        nlinarith only [ht1, hn, hb, hdir]
      exact ⟨fun h => (ne_of_lt hhigh) (congrArg Complex.re h),
        fun h => (ne_of_gt hlow) (congrArg Complex.re h)⟩

private theorem lfr_dart_ray (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) (t : ℝ) (ht : 0 < t)
    (ht1 : t < 1) :
    (layoutDart w m d).start + t • (layoutDart w m d).initialDirection ∈
      (layoutDart w m d).interior := by
  have hp := layoutArc_points_pairwise w m d.1.val d.1.isLt
  have hl := layoutArc_length_two_le w m d.1.val
  have hlast : (layoutArc w m d.1.val).points.length - 1 <
      (layoutArc w m d.1.val).points.length := by omega
  rcases d with ⟨e, b⟩
  change 2 ≤ (layoutArc w m e.val).points.length at hl
  cases b
  · apply lfr_ray_interior _ hl
      (Or.inl ⟨Polyline.initialDirection_re_pos hp hl, ?_⟩) t ht ht1
    rw [← Polyline.point_last_eq_finish]
    exact Polyline.point_re_le_of_le (p := layoutArc w m e.val) hp
      (by omega) hlast
  · apply lfr_ray_interior _
      (by simpa only [layoutDart, ↓reduceIte, Polyline.reverse,
        List.length_reverse] using hl)
      (Or.inr ⟨Polyline.reverse_initialDirection_re_neg hp hl, ?_⟩) t ht ht1
    change (layoutArc w m e.val).reverse.finish.re ≤
      ((layoutArc w m e.val).reverse.point 1).re
    rw [Polyline.finish_reverse, Polyline.reverse_point_one _ hl,
      ← Polyline.point_zero_eq_start]
    exact Polyline.point_re_le_of_le (p := layoutArc w m e.val) hp
      (Nat.zero_le _) (by omega)

private theorem lfr_dart_start (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    (layoutDart w m d).start = layoutPos w m (stageVertex w m d).val := by
  rcases d with ⟨e, b⟩
  cases b
  · exact layoutArc_start w m e.val e.isLt
  · exact (Polyline.start_reverse _).trans (layoutArc_finish w m e.val e.isLt)

private theorem lfr_dart_nonzero (w : ℕ → Fin 3)
    (m : ℕ) (d : StageDart (kmswStage w m).nextEdge) :
    (layoutDart w m d).initialDirection ≠ 0 := by
  have hp := layoutArc_points_pairwise w m d.1.val d.1.isLt
  have hl := layoutArc_length_two_le w m d.1.val
  rcases d with ⟨e, b⟩
  cases b
  · exact Polyline.initialDirection_ne_zero hp hl
  · intro hz
    have hn := Polyline.reverse_initialDirection_re_neg hp hl
    change (layoutArc w m e.val).reverse.initialDirection = 0 at hz
    rw [hz, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn

/-- Helper toward the plane-realization obligation of adjudication n308; not a
paper result. The LFR initial arguments are injective at each stage vertex. -/
theorem layoutGood_succ_lfr_initial_arg_injective (w : ℕ → Fin 3)
    (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d e : StageDart (kmswStage w (n + 1)).nextEdge,
      stageVertex w (n + 1) d = stageVertex w (n + 1) e →
      Complex.arg (layoutDart w (n + 1) d).initialDirection =
        Complex.arg (layoutDart w (n + 1) e).initialDirection → d = e := by
  intro d e hv ha
  by_contra hne
  have hf : e ≠ edgeFlip _ d := by
    intro h
    have hstart := congrArg (fun v => layoutPos w (n + 1) v.val) hv
    rcases d with ⟨di, db⟩
    subst e
    have hstrict := kmswStageRank_strict w (n + 1) di.val di.isLt
    have hneq : (layoutPos w (n + 1)
        ((kmswStage w (n + 1)).west di.val)).re ≠
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east di.val)).re := by
      apply ne_of_lt
      change (kmswStageRank w (n + 1)
          ((kmswStage w (n + 1)).west di.val) : ℝ) <
        (kmswStageRank w (n + 1)
          ((kmswStage w (n + 1)).east di.val) : ℝ)
      exact_mod_cast hstrict
    cases db
    · exact hneq (congrArg Complex.re hstart)
    · exact hneq (congrArg Complex.re hstart).symm
  let u := (layoutDart w (n + 1) d).initialDirection
  let v := (layoutDart w (n + 1) e).initialDirection
  let c : ℝ := ‖v‖ / ‖u‖
  have hcpos : 0 < c := div_pos (norm_pos_iff.mpr (lfr_dart_nonzero w _ e))
    (norm_pos_iff.mpr (lfr_dart_nonzero w _ d))
  have hcv : c • u = v := by
    simpa only [Complex.real_smul, Complex.ofReal_div, c, u, v] using
      (Complex.arg_eq_arg_iff (lfr_dart_nonzero w _ d)
        (lfr_dart_nonzero w _ e)).mp ha
  let t : ℝ := min 1 c / 2
  have ht : 0 < t := div_pos (lt_min (by norm_num) hcpos) (by norm_num)
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_left (1 : ℝ) c]
  have htc : t < c := by dsimp [t]; linarith [min_le_right (1 : ℝ) c]
  have htcpos : 0 < t / c := div_pos ht hcpos
  have htclt : t / c < 1 := (div_lt_one hcpos).mpr htc
  have heq : (layoutDart w (n + 1) d).start + t • u =
      (layoutDart w (n + 1) e).start + (t / c) • v := by
    rw [lfr_dart_start, lfr_dart_start, hv, ← hcv, smul_smul,
      div_mul_cancel₀ _ hcpos.ne']
  have hz0 := lfr_dart_ray w (n + 1) d t ht ht1
  have hz1 := lfr_dart_ray w (n + 1) e (t / c) htcpos htclt
  rw [← heq] at hz1
  exact Set.disjoint_left.mp
    (layoutGood_succ_lfr_interior_disjoint w n hc hUL G d e
      (Ne.symm hne) hf) hz0 hz1


private def lfrFresh (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) (j : Fin 2) (b : Bool) :
    StageDart (kmswStage w (n + 1)).nextEdge :=
  (⟨(kmswStage w n).nextEdge + j.val, by
    have hh := (lfr_counts w n hc hUL)
    have hj := j.isLt
    omega⟩, b)

private theorem lfr_unresize_eval {k l : ℕ} (h : k = l)
    (τ : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (ht : StageRotation.resize h τ = σ) (d : StageDart l) :
    τ (Fin.cast h.symm d.1, d.2) =
      (Fin.cast h.symm (σ d).1, (σ d).2) := by
  cases h
  exact congrArg (fun ρ => ρ d) ht

private theorem lfr_rotation_old (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (d : StageDart (kmswStage w n).nextEdge) :
    stageRot w (n + 1) (stageDartIncl w n d) =
      if d = (⟨(kmswStage w n).active,
          (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, false) then
        lfrFresh w n hc hUL 1 true
      else if stageRot w n d =
          (⟨(kmswStage w n).active,
            (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true) then
        lfrFresh w n hc hUL 0 true
      else stageDartIncl w n (stageRot w n d) := by
  have ht := StageRotation.step_leftFresh (kmswStage w n)
    (act_lt_nextEdge w (le_rfl)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl) hUL
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have hh := lfr_unresize_eval _ _ _ ht
    (StageRotation.allocation (kmswStage w n).nextEdge 2 (.inl d))
  rw [StageRotation.leftFresh_old] at hh
  split_ifs at hh ⊢ <;>
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lfrFresh] using hh

private theorem lfr_rotation_new (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    let a : StageDart (kmswStage w n).nextEdge :=
      (⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, false)
    let A : StageDart (kmswStage w n).nextEdge := (a.1, true)
    stageRot w (n + 1) (lfrFresh w n hc hUL 1 true) =
        (if stageRot w n a = A then lfrFresh w n hc hUL 0 true
          else stageDartIncl w n (stageRot w n a)) ∧
      stageRot w (n + 1) (lfrFresh w n hc hUL 0 true) = stageDartIncl w n A ∧
      stageRot w (n + 1) (lfrFresh w n hc hUL 0 false) =
        lfrFresh w n hc hUL 1 false ∧
      stageRot w (n + 1) (lfrFresh w n hc hUL 1 false) =
        lfrFresh w n hc hUL 0 false := by
  have ht := StageRotation.step_leftFresh (kmswStage w n)
    (act_lt_nextEdge w (le_rfl)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl) hUL
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have hh := StageRotation.leftFresh_new (kmswStage w n).nextEdge (stageRot w n)
    (⟨(kmswStage w n).active, act_lt_nextEdge w (le_rfl)⟩, false)
    (⟨(kmswStage w n).active, act_lt_nextEdge w (le_rfl)⟩, true)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he := lfr_unresize_eval _ _ _ ht
    have he' := he (StageRotation.allocation _ 2 (.inr (1, true)))
    rw [hh.1] at he'
    split_ifs at he' ⊢ <;>
      simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lfrFresh] using he'
  · have he := lfr_unresize_eval _ _ _ ht
    have he' := he (StageRotation.allocation _ 2 (.inr (0, true)))
    rw [hh.2.1] at he'
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lfrFresh] using he'
  · have he := lfr_unresize_eval _ _ _ ht
    have he' := he (StageRotation.allocation _ 2 (.inr (0, false)))
    rw [hh.2.2.1] at he'
    simpa [StageRotation.allocation, lfrFresh] using he'
  · have he := lfr_unresize_eval _ _ _ ht
    have he' := he (StageRotation.allocation _ 2 (.inr (1, false)))
    rw [hh.2.2.2] at he'
    simpa [StageRotation.allocation, lfrFresh] using he'

private theorem lfr_dart_cases (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    (∃ e, d = stageDartIncl w n e) ∨
      d = lfrFresh w n hc hUL 0 false ∨ d = lfrFresh w n hc hUL 0 true ∨
      d = lfrFresh w n hc hUL 1 false ∨ d = lfrFresh w n hc hUL 1 true := by
  rcases d with ⟨i, b⟩
  by_cases hi : i.val < (kmswStage w n).nextEdge
  · exact Or.inl ⟨(⟨i.val, hi⟩, b), rfl⟩
  · have hcount := (lfr_counts w n hc hUL).1
    have hib := i.isLt
    have hcases : i.val = (kmswStage w n).nextEdge ∨
        i.val = (kmswStage w n).nextEdge + 1 := by omega
    right
    rcases hcases with hi | hi <;> cases b
    · exact Or.inl (Prod.ext (Fin.ext (by simpa [lfrFresh] using hi)) rfl)
    · exact Or.inr (Or.inl
        (Prod.ext (Fin.ext (by simpa [lfrFresh] using hi)) rfl))
    · exact Or.inr (Or.inr (Or.inl
        (Prod.ext (Fin.ext (by simpa [lfrFresh] using hi)) rfl)))
    · exact Or.inr (Or.inr (Or.inr
        (Prod.ext (Fin.ext (by simpa [lfrFresh] using hi)) rfl)))

private theorem lfr_fresh_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (stageVertex w (n + 1) (lfrFresh w n hc hUL 0 false)).val =
        (kmswStage w n).nextVertex ∧
      (stageVertex w (n + 1) (lfrFresh w n hc hUL 0 true)).val =
        (kmswStage w n).east (kmswStage w n).active ∧
      (stageVertex w (n + 1) (lfrFresh w n hc hUL 1 false)).val =
        (kmswStage w n).nextVertex ∧
      (stageVertex w (n + 1) (lfrFresh w n hc hUL 1 true)).val =
        (kmswStage w n).west (kmswStage w n).active := by
  have hE := lfr_endpoints w n hc hUL
  simp only [stageVertex, stageEndpoint, lfrFresh, Fin.val_zero, Fin.val_one,
    Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
  exact ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1⟩

private theorem lfr_pair_successor {D : Type*} (dir : D → ℂ) (a b : D)
    (hne : a ≠ b) : CcwSuccessor {a, b} dir a b := by
  refine ⟨(Set.finite_singleton b).insert a, Or.inl rfl, Or.inr rfl,
    Or.inr ⟨hne.symm, ?_⟩⟩
  rintro f (rfl | rfl) hf
  · exact False.elim (hf rfl)
  · exact le_rfl

private theorem lfr_successor_insert_other {D : Type*} (S : Set D) (dir : D → ℂ)
    (f g p x : D) (hold : CcwSuccessor S dir f g)
    (hnew : CcwSuccessor (insert x S) dir p x) (hp : p ∈ S)
    (hf : f ≠ p) (hx : x ∉ S)
    (hargs : ∀ a ∈ insert x S, ∀ b ∈ insert x S, a ≠ b →
      Complex.arg (dir a) ≠ Complex.arg (dir b)) :
    CcwSuccessor (insert x S) dir f g := by
  apply ccwSuccessor_insert_preserve S dir f g x hold.1 hargs hold hx
  intro hbetween
  have hpx : p ≠ x := fun h => hx (h ▸ hp)
  have hfp := hargs f (mem_insert_of_mem x hold.2.1)
    p (mem_insert_of_mem x hp) hf
  have hxp := hargs x (mem_insert x S) p (mem_insert_of_mem x hp) hpx.symm
  have hmin : ccwTurn (dir f) (dir g) ≤ ccwTurn (dir f) (dir p) := by
    rcases hold.2.2.2 with ⟨_, hs⟩ | ⟨_, hm⟩
    · have hpf : p = f := by simpa only [hs, mem_singleton_iff] using hp
      exact False.elim (hf hpf.symm)
    · exact hm p hp hf.symm
  have hcomp := ccwTurn_comp_add (lt_of_lt_of_le hbetween hmin)
  have hrev := ccwTurn_add_reverse (dir f) (dir p) hfp
  have hrev' := ccwTurn_add_reverse (dir x) (dir p) hxp
  have hpos := ccwTurn_pos (dir f) (dir x)
  have hnewmin : ccwTurn (dir p) (dir x) ≤ ccwTurn (dir p) (dir f) := by
    rcases hnew.2.2.2 with ⟨heq, _⟩ | ⟨_, hm⟩
    · exact False.elim (hpx heq.symm)
    · exact hm f (mem_insert_of_mem x hold.2.1) hf
  linarith only [hcomp, hrev, hrev', hpos, hnewmin]

private theorem lfr_preserve_old {w : ℕ → Fin 3} {n : ℕ} (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (d p : StageDart (kmswStage w n).nextEdge)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n)
    (hv : stageVertex w (n + 1) (stageDartIncl w n d) =
      stageVertex w (n + 1) (stageDartIncl w n p))
    (hne : d ≠ p)
    (hnew : CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n p)}
      (fun f => (layoutDart w (n + 1) f).initialDirection) (stageDartIncl w n p) x) :
    CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n d) (stageDartIncl w n (stageRot w n d)) := by
  have hxd := hnew.2.2.1.trans hv.symm
  have hs := stageStar_eq_insert_old_star w n d x hx hxd
  rw [hs]
  apply lfr_successor_insert_other _ _ _ _ (stageDartIncl w n p) x
    (G.old_star_rotation_agreement d)
  · rw [← hs]
    simpa only [hv] using hnew
  · exact ⟨p.1.isLt, hv.symm⟩
  · intro he
    apply hne
    apply Prod.ext
    · exact Fin.ext (congrArg (fun f => f.1.val) he)
    · exact congrArg
        (fun f : StageDart (kmswStage w (n + 1)).nextEdge => f.2) he
  · intro he
    have hlo := he.1
    have hhi := (Finset.mem_Ico.mp hx).1
    omega
  · intro a ha b hb hab harg
    rw [← hs] at ha hb
    exact hab (layoutGood_succ_lfr_initial_arg_injective w n hc hUL G a b
      (ha.trans hb.symm) harg)

private theorem lfr_new_star (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    {f | stageVertex w (n + 1) f =
      stageVertex w (n + 1) (lfrFresh w n hc hUL 0 false)} =
      {lfrFresh w n hc hUL 0 false, lfrFresh w n hc hUL 1 false} := by
  obtain ⟨hx, hv, hx', hu⟩ := lfr_fresh_endpoints w n hc hUL
  have he := kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  ext f
  constructor
  · intro hf
    have hval := congrArg Fin.val hf
    rw [hx] at hval
    rcases lfr_dart_cases w n hc hUL f with ⟨e, rfl⟩ | rfl | rfl | rfl | rfl
    · rw [stageVertex_incl_eq] at hval
      have hb := (stageVertex w n e).isLt
      change (stageVertex w n e).val = _ at hval
      omega
    · exact Or.inl rfl
    · rw [hv] at hval
      omega
    · exact Or.inr rfl
    · rw [hu] at hval
      omega
  · rintro (rfl | rfl)
    · rfl
    · exact Fin.ext (hx'.trans hx.symm)

private theorem lfr_star_unaffected (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    (d : StageDart (kmswStage w n).nextEdge)
    (hu : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (lfrFresh w n hc hUL 1 true))
    (hv : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (lfrFresh w n hc hUL 0 true)) :
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} =
      {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} := by
  ext f
  constructor
  · intro hf
    refine ⟨?_, hf⟩
    rcases lfr_dart_cases w n hc hUL f with ⟨e, rfl⟩ | rfl | rfl | rfl | rfl
    · exact e.1.isLt
    · have hh := congrArg Fin.val hf
      rw [(lfr_fresh_endpoints w n hc hUL).1, stageVertex_incl_eq] at hh
      have hb := (stageVertex w n d).isLt
      change _ = (stageVertex w n d).val at hh
      omega
    · exact False.elim (hv hf.symm)
    · have hh := congrArg Fin.val hf
      rw [(lfr_fresh_endpoints w n hc hUL).2.2.1, stageVertex_incl_eq] at hh
      have hb := (stageVertex w n d).isLt
      change _ = (stageVertex w n d).val at hh
      omega
    · exact False.elim (hu hf.symm)
  · exact fun hf => hf.2

private theorem lfr_insert_next_of_first {D : Type*} (S : Set D) (dir : D → ℂ)
    (a b x : D) (hold : CcwSuccessor S dir a b)
    (hx : x ∉ S) (hfirst : CcwSuccessor (insert x S) dir a x)
    (hargs : ∀ u ∈ insert x S, ∀ v ∈ insert x S, u ≠ v →
      Complex.arg (dir u) ≠ Complex.arg (dir v)) :
    CcwSuccessor (insert x S) dir x b := by
  have hb := hold.2.2.1
  have hle : ccwTurn (dir a) (dir x) ≤ ccwTurn (dir a) (dir b) := by
    by_cases hba : b = a
    · rw [hba, (ccwTurn_eq_two_pi_iff _ _).2 rfl]
      exact ccwTurn_le_two_pi _ _
    · rcases hfirst.2.2.2 with ⟨heq, _⟩ | ⟨_, hmin⟩
      · exact False.elim (hx (heq ▸ hold.2.1))
      · exact hmin b (mem_insert_of_mem x hb) hba
  have hlt : CcwBetween (dir a) (dir x) (dir b) := by
    apply lt_of_le_of_ne hle
    intro heq
    have hxb : x ≠ b := fun h => hx (h.symm ▸ hb)
    exact hargs x (mem_insert x S) b (mem_insert_of_mem x hb) hxb
      (ccwTurn_left_injective heq)
  exact ccwSuccessor_insert_next S dir a b x hold.1 hargs hold hx hlt

private theorem lfr_west_extreme_successors {w : ℕ → Fin 3} {n : ℕ}
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let e : Fin (kmswStage w n).nextEdge :=
      ⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩
    let a : StageDart (kmswStage w n).nextEdge := (e, false)
    let x := lfrFresh w n hc hUL 1 true
    CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n a)}
      (fun f => (layoutDart w (n + 1) f).initialDirection) (stageDartIncl w n a) x ∧
    CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n a)}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      x (stageDartIncl w n (stageRot w n a)) := by
  dsimp only
  let e : Fin (kmswStage w n).nextEdge :=
    ⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩
  let a : StageDart (kmswStage w n).nextEdge := (e, false)
  let x := lfrFresh w n hc hUL 1 true
  let S : Set (StageDart (kmswStage w (n + 1)).nextEdge) :=
    {f | f.1.val < (kmswStage w n).nextEdge ∧
      stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n a)}
  have hx : x.1.val ∈ freshEdges w n := (lfr_fresh_edges w n hc hUL).2
  have hxv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n a) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact (lfr_fresh_endpoints w n hc hUL).2.2.2
  have hs := stageStar_eq_insert_old_star w n a x hx hxv
  change CcwSuccessor _ _ (stageDartIncl w n a) x ∧ CcwSuccessor _ _ x _
  rw [hs]
  have hxnot : x ∉ S := by
    intro hf
    exact (not_lt_of_ge (Finset.mem_Ico.mp hx).1) hf.1
  have hargs : ∀ u ∈ insert x S, ∀ v ∈ insert x S, u ≠ v →
      Complex.arg (layoutDart w (n + 1) u).initialDirection ≠
        Complex.arg (layoutDart w (n + 1) v).initialDirection := by
    intro u hu v hv huv harg
    rw [← hs] at hu hv
    exact huv (layoutGood_succ_lfr_initial_arg_injective w n hc hUL G u v
      (hu.trans hv.symm) harg)
  have hOldEast : ∀ f ∈ S, 0 < (layoutDart w (n + 1) f).initialDirection.re := by
    intro f hf
    let f0 : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf.1⟩, f.2)
    have hfe : stageDartIncl w n f0 = f := rfl
    have hv := hf.2
    rw [← hfe, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    have hvOld : stageVertex w n f0 = stageVertex w n a :=
      Fin.ext (congrArg
        (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv)
    cases hb : f0.2
    · rw [← hfe, layoutDart_incl_eq]
      simpa [hb] using layoutDart_initialDirection_re_sign w n f0
    · have heq := congrArg Fin.val hvOld
      simp only [stageVertex, stageEndpoint, hb, ↓reduceIte] at heq
      have hstrict : (layoutPos w n ((kmswStage w n).west f0.1.val)).re <
          (layoutPos w n ((kmswStage w n).east f0.1.val)).re := by
        change (kmswStageRank w n ((kmswStage w n).west f0.1.val) : ℝ) <
          (kmswStageRank w n ((kmswStage w n).east f0.1.val) : ℝ)
        exact_mod_cast kmswStageRank_strict w n f0.1.val f0.1.isLt
      rw [heq] at hstrict
      have hend := (kmswStage_endpoints_lt_nextVertex w n f0.1.val f0.1.isLt).1
      have himage : layoutPos w n ((kmswStage w n).west f0.1.val) ∈ P.image := by
        rw [← G.pos_layout ⟨_, hend⟩]
        exact Or.inl ⟨⟨_, hend⟩, rfl⟩
      have hbound := (G.image_bounds himage).1
      rw [G.xmin_eq_active_west_of_UL_dropLast_reverse_nil hUL] at hbound
      exact False.elim ((not_lt_of_ge hbound) hstrict)
  have ha : stageDartIncl w n a ∈ S := ⟨e.isLt, rfl⟩
  have hWest : (layoutDart w (n + 1) x).initialDirection.re < 0 := by
    simpa [x, lfrFresh] using layoutDart_initialDirection_re_sign w (n + 1) x
  have he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    simp [e, hes]
  have hmax : ∀ f ∈ S, 0 < (layoutDart w (n + 1) f).initialDirection.re →
      f = stageDartIncl w n a ∨
        (layoutDart w (n + 1) f).initialDirection.im /
            (layoutDart w (n + 1) f).initialDirection.re <
          (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.im /
            (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.re := by
    intro f hf hpos
    let f0 : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf.1⟩, f.2)
    have hfe : stageDartIncl w n f0 = f := rfl
    have hv := hf.2
    rw [← hfe, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    have hvOld : stageVertex w n f0 = stageVertex w n a :=
      Fin.ext (congrArg
        (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv)
    rw [← hfe, layoutDart_incl_eq] at hpos
    rcases G.upper_east_dart_topmost e he f0 hvOld hpos with h | h
    · exact Or.inl ((congrArg (stageDartIncl w n) h).symm.trans hfe).symm
    · right
      simpa only [← hfe, layoutDart_incl_eq] using h
  have hfirst : CcwSuccessor (insert x S)
      (fun f => (layoutDart w (n + 1) f).initialDirection) (stageDartIncl w n a) x := by
    apply east_max_ccwSuccessor (insert x S) _ (stageDartIncl w n a) x
      (Set.finite_univ.subset (fun _ _ => trivial))
      (mem_insert_of_mem x ha) (mem_insert x S)
    · intro f hf
      rcases hf with rfl | hf
      · exact hWest.ne
      · exact (hOldEast f hf).ne'
    · exact hOldEast _ ha
    · exact hWest
    · intro f hf hpos
      rcases hf with rfl | hf
      · exact False.elim ((not_lt_of_ge hWest.le) hpos)
      · exact hmax f hf hpos
    · intro f hf hneg
      rcases hf with rfl | hf
      · exact Or.inl rfl
      · exact False.elim ((not_lt_of_ge (hOldEast f hf).le) hneg)
  exact ⟨hfirst, lfr_insert_next_of_first S _ _ _ x
    (G.old_star_rotation_agreement a) hxnot hfirst hargs⟩

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. Rotation agreement for the fresh-left step of `def-kmsw`, -/
theorem layoutGood_succ_lfr_rotation_agreement (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      CcwSuccessor
        {e | stageVertex w (n + 1) e = stageVertex w (n + 1) d}
        (fun e => (layoutDart w (n + 1) e).initialDirection)
        d (stageRot w (n + 1) d) := by
  let e : Fin (kmswStage w n).nextEdge :=
    ⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩
  let a : StageDart (kmswStage w n).nextEdge := (e, false)
  let A : StageDart (kmswStage w n).nextEdge := (e, true)
  let p := (stageRot w n).symm A
  let x := lfrFresh w n hc hUL 1 true
  let y := lfrFresh w n hc hUL 0 true
  have he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    simp [e, hes]
  have hx : x.1.val ∈ freshEdges w n := (lfr_fresh_edges w n hc hUL).2
  have hy : y.1.val ∈ freshEdges w n := (lfr_fresh_edges w n hc hUL).1
  have hxv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n a) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact (lfr_fresh_endpoints w n hc hUL).2.2.2
  have hyv : stageVertex w (n + 1) y =
      stageVertex w (n + 1) (stageDartIncl w n A) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact (lfr_fresh_endpoints w n hc hUL).2.1
  have hne : stageVertex w n a ≠ stageVertex w n A := by
    intro hv
    have hh := congrArg Fin.val hv
    change (kmswStage w n).west e.val = (kmswStage w n).east e.val at hh
    have hs := kmswStageRank_strict w n e.val e.isLt
    rw [hh] at hs
    exact (lt_irrefl _ hs)
  have hrot : stageRot w n a ≠ A := by
    intro hh
    have hv := P.vert_rotation a
    rw [hh] at hv
    exact hne hv.symm
  have hp : stageRot w n p = A := (stageRot w n).apply_symm_apply A
  have hpv : stageVertex w n p = stageVertex w n A := by
    have hh := P.vert_rotation p
    rw [hp] at hh
    exact hh.symm
  have hE := lfr_west_extreme_successors hc hUL G
  have hW := G.west_roof_insertion_successors e he y hy rfl (by
    rintro ⟨_, _, hh⟩
    change (kmswStage w n).nextEdge + 0 = (kmswStage w n).nextEdge + 1 at hh
    omega) hyv
  have hr := lfr_rotation_new w n hc hUL
  change stageRot w (n + 1) x =
      (if stageRot w n a = A then y else stageDartIncl w n (stageRot w n a)) ∧
    stageRot w (n + 1) y = stageDartIncl w n A ∧ _ at hr
  rw [ite_eq_right hrot] at hr
  have hrold (d : StageDart (kmswStage w n).nextEdge) :
      stageRot w (n + 1) (stageDartIncl w n d) =
        if d = a then x else if stageRot w n d = A then y
          else stageDartIncl w n (stageRot w n d) := lfr_rotation_old w n hc hUL d
  intro d
  rcases lfr_dart_cases w n hc hUL d with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [hrold]
    by_cases hda : d = a
    · subst d
      rw [ite_eq_left rfl]
      exact hE.1
    · rw [ite_eq_right hda]
      by_cases hdA : stageRot w n d = A
      · rw [ite_eq_left hdA]
        have hdp : d = p := (stageRot w n).injective (hdA.trans hp.symm)
        subst d
        have hv : stageVertex w (n + 1) (stageDartIncl w n p) =
            stageVertex w (n + 1) (stageDartIncl w n A) := by
          rw [stageVertex_incl_eq, stageVertex_incl_eq, hpv]
        simpa only [hv] using hW.1
      · rw [ite_eq_right hdA]
        by_cases hdu : stageVertex w (n + 1) (stageDartIncl w n d) =
            stageVertex w (n + 1) (stageDartIncl w n a)
        · exact lfr_preserve_old hc hUL G d a x hx hdu hda hE.1
        · by_cases hdv : stageVertex w (n + 1) (stageDartIncl w n d) =
              stageVertex w (n + 1) (stageDartIncl w n A)
          · have hv : stageVertex w (n + 1) (stageDartIncl w n d) =
                stageVertex w (n + 1) (stageDartIncl w n p) := by
              rw [stageVertex_incl_eq, stageVertex_incl_eq, hpv]
              simpa only [stageVertex_incl_eq] using hdv
            have hdp : d ≠ p := fun hh => hdA (hh ▸ hp)
            have hW' : CcwSuccessor
                {f | stageVertex w (n + 1) f =
                  stageVertex w (n + 1) (stageDartIncl w n p)}
                (fun f => (layoutDart w (n + 1) f).initialDirection)
                (stageDartIncl w n p) y := by
              simpa only [stageVertex_incl_eq, hpv] using hW.1
            exact lfr_preserve_old hc hUL G d p y hy hv hdp hW'
          · rw [lfr_star_unaffected w n hc hUL d
              (fun hh => hdu (hh.trans hxv)) (fun hh => hdv (hh.trans hyv))]
            exact G.old_star_rotation_agreement d
  · rw [hr.2.2.1, lfr_new_star w n hc hUL]
    exact lfr_pair_successor _ _ _ (by
      intro hh
      have hv := congrArg (fun f => f.1.val) hh
      change (kmswStage w n).nextEdge + 0 = (kmswStage w n).nextEdge + 1 at hv
      omega)
  · rw [hr.2.1]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) y}
      (fun f => (layoutDart w (n + 1) f).initialDirection) y _
    rw [hyv]
    exact hW.2
  · rw [hr.2.2.2]
    have hv : stageVertex w (n + 1) (lfrFresh w n hc hUL 1 false) =
        stageVertex w (n + 1) (lfrFresh w n hc hUL 0 false) :=
      Fin.ext ((lfr_fresh_endpoints w n hc hUL).2.2.1.trans
        (lfr_fresh_endpoints w n hc hUL).1.symm)
    rw [hv, lfr_new_star w n hc hUL, Set.pair_comm]
    exact lfr_pair_successor _ _ _ (by
      intro hh
      have heq := congrArg (fun f => f.1.val) hh
      change (kmswStage w n).nextEdge + 1 = (kmswStage w n).nextEdge + 0 at heq
      omega)
  · rw [hr.1]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) x}
      (fun f => (layoutDart w (n + 1) f).initialDirection) x _
    rw [hxv]
    exact hE.2

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. The good layout for the fresh-left step of `def-kmsw`, -/
theorem layoutGood_succ_lfr (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) : LayoutGood w (n + 1) where
  interior_disjoint := layoutGood_succ_lfr_interior_disjoint w n hc hUL G
  interior_avoids_vertices := layoutGood_succ_lfr_interior_avoids_vertices w n hc hUL G
  initial_arg_injective := layoutGood_succ_lfr_initial_arg_injective w n hc hUL G
  rotation_agreement := layoutGood_succ_lfr_rotation_agreement w n hc hUL G

end DirectedDistances.KMSW
