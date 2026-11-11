module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.MonotoneStepCommon
public import DirectedDistances.PlanarMap.GraphRegionSplice






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_pos_layout (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 1) (h : LayoutGood w (n + 1)) :
    ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      (monotoneLayoutDrawing w (n + 1) h).pos v =
        layoutPos w (n + 1) v.val := by
  intro v
  rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_arc_layout (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 1) (h : LayoutGood w (n + 1)) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      (monotoneLayoutDrawing w (n + 1) h).arc d =
        layoutDart w (n + 1) d := by
  intro d
  rfl

/-- In an UP step, the new active edge has a roof arc at height `n + 1`.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_active_layoutArc (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    layoutArc w (n + 1) (kmswStage w n).nextEdge =
      roofArc
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
          (kmswStage w n).nextEdge))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
          (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) := by
  have he : (kmswStage w n).nextEdge ∈ freshEdges w n := by
    simp [freshEdges, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]
  have hmiss : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n (kmswStage w n).nextEdge he]
  simp [hmiss]

/-- The missing side created by an UP step is also drawn as a roof.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_missing_layoutArc (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1) =
      roofArc
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
          ((kmswStage w n).nextEdge + 1)))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
          ((kmswStage w n).nextEdge + 1)))
        (n + 1) (rampSlope w n) := by
  have he : (kmswStage w n).nextEdge + 1 ∈ freshEdges w n := by
    simp [freshEdges, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]
  have hmiss : ¬ isFreshLeftMissing w n ((kmswStage w n).nextEdge + 1) := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n _ he]
  simp [hmiss]

/-- The UP transition adds one vertex at the old `nextVertex` index.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_nextVertex (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- The UP transition allocates exactly two edge IDs.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_nextEdge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- Fresh edge IDs in an UP transition are the present and missing sides.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_fresh_edge_ids (w : ℕ → Fin 3) (n e : ℕ)
    (hc : w n = 1) :
    e ∈ freshEdges w n ↔
      e = (kmswStage w n).nextEdge ∨
        e = (kmswStage w n).nextEdge + 1 := by
  simp only [freshEdges, Finset.mem_Ico, up_nextEdge w n hc]
  omega

/-- Endpoints of the two edges allocated in an UP transition.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_edge_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
        (kmswStage w n).west (kmswStage w n).active ∧
      (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
        (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).east (kmswStage w n).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- Boundary and triangle lists after an UP transition.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_boundary_update (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).UL =
        (kmswStage w n).UL.dropLast ++ [(kmswStage w n).nextEdge] ∧
      (kmswStage w (n + 1)).UR =
        ((kmswStage w n).nextEdge + 1) :: (kmswStage w n).UR ∧
      (kmswStage w (n + 1)).triangles =
        (kmswStage w n).triangles ++
          [((kmswStage w n).active, (kmswStage w n).nextEdge,
            (kmswStage w n).nextEdge + 1)] := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- An UP transition leaves both lower boundary chains unchanged.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_lower_boundary_update (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).LL = (kmswStage w n).LL ∧
      (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- The new active UP edge is present and the new UR edge is missing.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_edge_status (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true ∧
      (kmswStage w (n + 1)).present ((kmswStage w n).nextEdge + 1) = false := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]

/-- An UP transition appends one triangle to the stage record.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_triangle_count (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).triangles.length =
      (kmswStage w n).triangles.length + 1 := by
  rw [(up_boundary_update w n hc).2.2]
  simp

/-- The new UP triangle is the final triangle in the stage list.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_last_triangle (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (kmswStage w (n + 1)).triangles.getLast? =
      some ((kmswStage w n).active, (kmswStage w n).nextEdge,
        (kmswStage w n).nextEdge + 1) := by
  have htri := (up_boundary_update w n hc).2.2
  rw [htri]
  simp

/-- The new UP vertex is placed at height `n + 1`.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_vertex_height (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).im = (n + 1 : ℝ) := by
  change layoutHeight w (n + 1) (kmswStage w n).nextVertex = _
  simpa [Nat.cast_add] using
    layoutHeight_created_vertex w n (up_nextVertex w n hc)

/-- The new UP vertex is at the midpoint rank of the old active edge.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_vertex_rank (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    kmswStageRank w (n + 1) (kmswStage w n).nextVertex =
      (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) +
        kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active)) / 2 := by
  simp [kmswStageRank, hc]

/-- Every point on the new active UP roof has height at most `n + 1`.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_active_image_height (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    ∀ z ∈ (layoutArc w (n + 1) (kmswStage w n).nextEdge).image,
      z.im ≤ (n + 1 : ℝ) := by
  have he : (kmswStage w n).nextEdge ∈ freshEdges w n := by
    simp [freshEdges, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]
  have hi := layoutArc_image_fresh w n (kmswStage w n).nextEdge he
  dsimp only at hi
  simp only [isFreshLeftMissing, hc] at hi
  intro z hz
  rw [hi] at hz
  rcases hz with ⟨_, _, hh⟩
  rw [hh]
  exact (roofHeight_le_top _ _ _ _ _).trans_eq (by norm_num)

/-- Every point on the new missing UP roof has height at most `n + 1`.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_new_missing_image_height (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    ∀ z ∈ (layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1)).image,
      z.im ≤ (n + 1 : ℝ) := by
  have he : (kmswStage w n).nextEdge + 1 ∈ freshEdges w n := by
    simp [freshEdges, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]
  have hi := layoutArc_image_fresh w n _ he
  dsimp only at hi
  simp only [isFreshLeftMissing, hc] at hi
  intro z hz
  rw [hi] at hz
  rcases hz with ⟨_, _, hh⟩
  rw [hh]
  exact (roofHeight_le_top _ _ _ _ _).trans_eq (by norm_num)

private theorem reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · have hz' : z = p.finish := by
      simpa only [Polyline.start_reverse, Set.mem_singleton_iff] using hz
    rw [hz', ← p.point_last_eq_finish]
    by_cases hlen : 2 ≤ p.points.length
    · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
      have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
      rw [Polyline.segmentAt, hidx]
      exact right_mem_segment ℝ _ _
    · have hlen1 : p.points.length = 1 := by
        have := List.length_pos_iff.mpr p.nonempty
        omega
      simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
      exact Or.inl rfl
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_old_arc (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (he' : e < (kmswStage w (n + 1)).nextEdge) (b : Bool) :
    (monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he'⟩, b) =
      P.arc (⟨e, he⟩, b) := by
  rw [G.arc_layout]
  change (if b then (layoutArc w (n + 1) e).reverse else layoutArc w (n + 1) e) = _
  rw [layoutArc_old w n e he]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_old_trace (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e = stageEdgeTrace P e := by
  have he' := he.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))
  simp only [stageEdgeTrace, he, he', ↓reduceDIte, up_old_arc w n G h e he he']

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_lower_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver G.xmin G.xmax G.lower =
      ⋃ e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  rw [(up_lower_boundary_update w n hc).1, (up_lower_boundary_update w n hc).2]
  rw [G.lower_trace]
  apply iUnion_congr
  intro e
  apply iUnion_congr
  intro he
  have he' : e < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp only [List.mem_append] at he ⊢
    tauto
  exact (up_old_trace w n G h e he').symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_image_height_le (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    ∀ z ∈ (monotoneLayoutDrawing w (n + 1) h).image, z.im ≤ (n + 1 : ℝ) := by
  rintro z (⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩)
  · change layoutHeight w (n + 1) v.val ≤ (n + 1 : ℝ)
    simpa only [Nat.cast_add, Nat.cast_one] using
      layoutHeight_le w (n + 1) v.val v.isLt
  · by_cases he : e.val < (kmswStage w n).nextEdge
    · rw [up_old_arc w n G h e.val he e.isLt b] at hz
      exact (G.image_height_le z (Or.inr ⟨(⟨e.val, he⟩, b), hz⟩)).trans
        (by exact_mod_cast Nat.le_succ n)
    · have hf : e.val ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, e.isLt⟩
      have hz' : z ∈ (layoutArc w (n + 1) e.val).image := by
        cases b
        · exact hz
        · exact reverse_image_subset _ hz
      rcases (up_fresh_edge_ids w n e.val hc).mp hf with heq | heq
      · rw [heq] at hz'
        exact up_new_active_image_height w n hc z hz'
      · rw [heq] at hz'
        exact up_new_missing_image_height w n hc z hz'

private theorem up_endpoint_positions (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    layoutPos w (n + 1) (t.west s.nextEdge) = layoutPos w n (s.west s.active) ∧
      layoutPos w (n + 1) (t.east s.nextEdge) = layoutPos w (n + 1) s.nextVertex ∧
      layoutPos w (n + 1) (t.west (s.nextEdge + 1)) =
        layoutPos w (n + 1) s.nextVertex ∧
      layoutPos w (n + 1) (t.east (s.nextEdge + 1)) = layoutPos w n (s.east s.active) := by
  dsimp only
  obtain ⟨hw, hp, hp', he⟩ := up_new_edge_endpoints w n hc
  obtain ⟨hwB, heB⟩ := kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  rw [hw, hp, hp', he, layoutPos_old_vertex w n _ hwB, layoutPos_old_vertex w n _ heB]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem up_roof_setup (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    let s := kmswStage w n
    let a := layoutPos w n (s.west s.active)
    let b := layoutPos w n (s.east s.active)
    let p := layoutPos w (n + 1) s.nextVertex
    a.im ≤ (n + 1 : ℝ) ∧ b.im ≤ (n + 1 : ℝ) ∧ p.im = (n + 1 : ℝ) ∧
      ((n + 1 : ℝ) - a.im) / rampSlope w n < p.re - a.re ∧
      ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - p.re := by
  dsimp only
  obtain ⟨hwB, heB⟩ := kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hH : (n : ℝ) ≤ n + 1 := by linarith
  have ha := (layoutHeight_le w n _ hwB).trans hH
  have hb := (layoutHeight_le w n _ heB).trans hH
  have hp := up_new_vertex_height w n hc
  have h0 := freshEdges_ramp_widths_lt w n (kmswStage w n).nextEdge
    ((up_fresh_edge_ids w n _ hc).mpr (Or.inl rfl))
  have h1 := freshEdges_ramp_widths_lt w n ((kmswStage w n).nextEdge + 1)
    ((up_fresh_edge_ids w n _ hc).mpr (Or.inr rfl))
  obtain ⟨h0w, h0e, h1w, h1e⟩ := up_endpoint_positions w n hc
  rw [h0w, h0e, hp, sub_self, zero_div, add_zero] at h0
  rw [h1w, h1e, hp, sub_self, zero_div, zero_add] at h1
  exact ⟨ha, hb, hp, h0, h1⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_active_graph_data (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let s := kmswStage w n
    let a := layoutPos w n (s.west s.active)
    let b := layoutPos w n (s.east s.active)
    a.re ∈ Icc G.xmin G.xmax ∧ b.re ∈ Icc G.xmin G.xmax ∧
      G.upper a.re = a.im ∧ G.upper b.re = b.im := by
  dsimp only
  have he := (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hmem : (kmswStage w n).active ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    simp only [hxs, List.mem_append, List.mem_singleton, or_true, true_or]
  have hA : (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)) ∈
      (layoutArc w n (kmswStage w n).active).image := by
    rw [← layoutArc_start w n _ he]
    exact Or.inl rfl
  have hB : (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)) ∈
      (layoutArc w n (kmswStage w n).active).image := by
    rw [← layoutArc_finish w n _ he]
    apply reverse_image_subset
    exact Or.inl (Polyline.start_reverse _).symm
  have hAP : (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)) ∈ P.image :=
    Or.inl ⟨⟨_, (kmswStage_endpoints_lt_nextVertex w n _ he).1⟩, G.pos_layout _⟩
  have hBP : (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)) ∈ P.image :=
    Or.inl ⟨⟨_, (kmswStage_endpoints_lt_nextVertex w n _ he).2⟩, G.pos_layout _⟩
  exact ⟨⟨(G.image_bounds hAP).1, (G.image_bounds hAP).2.1⟩,
    ⟨(G.image_bounds hBP).1, (G.image_bounds hBP).2.1⟩,
    G.upper_eq_arc_height hmem hA, G.upper_eq_arc_height hmem hB⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upRoofHeight (w : ℕ → Fin 3) (n : ℕ) : ℝ → ℝ :=
  roofHeight (layoutPos w n ((kmswStage w n).west (kmswStage w n).active))
    (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
    (n + 1) (rampSlope w n)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upSplicedUpper (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : ℝ → ℝ :=
  spliceFn G.upper (upRoofHeight w n)
    (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re
    (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re

private theorem up_outer_roof_fit (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    let s := kmswStage w n
    let a := layoutPos w n (s.west s.active)
    let b := layoutPos w n (s.east s.active)
    ((n + 1 : ℝ) - a.im) / rampSlope w n +
      ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - a.re := by
  obtain ⟨_, _, _, hl, hr⟩ := up_roof_setup w n hc
  dsimp only at hl hr ⊢
  linarith only [hl, hr]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upRoofHeight_endpoints (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re
    let b := (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
    upRoofHeight w n a = G.upper a ∧ upRoofHeight w n b = G.upper b := by
  obtain ⟨ha, hb, _, _, _⟩ := up_roof_setup w n hc
  obtain ⟨_, _, hA, hB⟩ := up_active_graph_data w n G
  exact ⟨(roofHeight_start (rampSlope_pos w n) ha hb (up_outer_roof_fit w n hc)).trans
    hA.symm,
    (roofHeight_finish (rampSlope_pos w n) ha hb (up_outer_roof_fit w n hc)).trans
      hB.symm⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upRoofHeight_gap (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ x ∈ Ioo
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re,
      G.upper x < upRoofHeight w n x := by
  obtain ⟨ha, hb, hA, hB⟩ := up_active_graph_data w n G
  exact G.upper_lt_roofHeight ha hb hA.le hB.le

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_upper_continuous (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ContinuousOn (upSplicedUpper w n G) (Icc G.xmin G.xmax) := by
  have hab :
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re <
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
  obtain ⟨ha, hb⟩ := upRoofHeight_endpoints w n hc G
  exact continuousOn_spliceFn hab.le G.upper_continuous
    (continuous_roofHeight _ _ _ _).continuousOn ha hb

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_lower_le_upper (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ x ∈ Icc G.xmin G.xmax, G.lower x ≤ upSplicedUpper w n G x := by
  obtain ⟨ha, hb⟩ := upRoofHeight_endpoints w n hc G
  exact lower_le_spliceFn G.lower_le_upper ha hb (upRoofHeight_gap w n G)

private theorem roofHeight_abs_sub_le (a b : ℂ) (H M : ℝ) (hM : 0 ≤ M) (x y : ℝ) :
    |roofHeight a b H M x - roofHeight a b H M y| ≤ M * |x - y| := by
  have hl : |(a.im + M * (x - a.re)) - (a.im + M * (y - a.re))| =
      M * |x - y| := by
    rw [show a.im + M * (x - a.re) - (a.im + M * (y - a.re)) = M * (x - y) by ring,
      abs_mul, abs_of_nonneg hM]
  have hr : |(b.im + M * (b.re - x)) - (b.im + M * (b.re - y))| =
      M * |x - y| := by
    rw [show b.im + M * (b.re - x) - (b.im + M * (b.re - y)) = M * (y - x) by ring,
      abs_mul, abs_of_nonneg hM, abs_sub_comm]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le
    (by simpa only [sub_self, abs_zero] using mul_nonneg hM (abs_nonneg (x - y)))
    ((abs_min_sub_min_le_max _ _ _ _).trans (by rw [hl, hr, max_self])))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_upper_lipschitz_margin (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ L : ℝ, 0 ≤ L ∧ L < rampSlope w (n + 1) ∧
      ∀ x ∈ Icc G.xmin G.xmax, ∀ y ∈ Icc G.xmin G.xmax,
        |upSplicedUpper w n G x - upSplicedUpper w n G y| ≤ L * |x - y| := by
  obtain ⟨ha, hb, _, _⟩ := up_active_graph_data w n G
  obtain ⟨hA, hB⟩ := upRoofHeight_endpoints w n hc G
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  refine ⟨rampSlope w n, (rampSlope_pos w n).le,
    rampSlope_lt w (Nat.lt_succ_self n), ?_⟩
  have hab :
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re ≤
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) ≤
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast (kmswStageRank_strict w n _
      (kmswStage_boundary_ids_lt_nextEdge w n).1).le
  apply abs_spliceFn_sub_le ha.1 hab hb.2 hA hB
  · intro x hx y hy
    exact (hLip x hx y hy).trans (mul_le_mul_of_nonneg_right hLM.le (abs_nonneg _))
  · intro x _ y _
    exact roofHeight_abs_sub_le _ _ _ _ (rampSlope_pos w n).le x y

private theorem roofHeight_split {a b p : ℂ} {H M : ℝ} (hM : 0 < M)
    (hp : p.im = H) (hl : (H - a.im) / M < p.re - a.re)
    (hr : (H - b.im) / M < b.re - p.re) :
    (∀ x, x ≤ p.re → roofHeight a b H M x = roofHeight a p H M x) ∧
      (∀ x, p.re ≤ x → roofHeight a b H M x = roofHeight p b H M x) := by
  have hleft : H < a.im + M * (p.re - a.re) := by
    have hh := (div_lt_iff₀ hM).mp hl
    nlinarith only [hh]
  have hright : H < b.im + M * (b.re - p.re) := by
    have hh := (div_lt_iff₀ hM).mp hr
    nlinarith only [hh]
  constructor
  · intro x hx
    have hR : H ≤ b.im + M * (b.re - x) := by nlinarith only [hright, hx, hM]
    have hP : H ≤ p.im + M * (p.re - x) := by rw [hp]; nlinarith only [hx, hM]
    dsimp only [roofHeight]
    rw [← min_assoc, min_eq_left ((min_le_left _ _).trans hR),
      ← min_assoc, min_eq_left ((min_le_left _ _).trans hP)]
  · intro x hx
    have hL : H ≤ a.im + M * (x - a.re) := by nlinarith only [hleft, hx, hM]
    have hP : H ≤ p.im + M * (x - p.re) := by rw [hp]; nlinarith only [hx, hM]
    dsimp only [roofHeight]
    rw [← min_assoc, min_eq_left hL, ← min_assoc, min_eq_left hP]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upRoofHeight_graph (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (h : LayoutGood w (n + 1)) :
    graphOver
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
      (upRoofHeight w n) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge ∪
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
          ((kmswStage w n).nextEdge + 1) := by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  let b := layoutPos w n (s.east s.active)
  let p := layoutPos w (n + 1) s.nextVertex
  obtain ⟨ha, hb, hp, hl, hr⟩ := up_roof_setup w n hc
  change a.im ≤ _ at ha
  change b.im ≤ _ at hb
  change p.im = _ at hp
  change ((n + 1 : ℝ) - a.im) / rampSlope w n < p.re - a.re at hl
  change ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - p.re at hr
  have hap : a.re < p.re := by
    have hh := div_nonneg (sub_nonneg.mpr ha) (rampSlope_pos w n).le
    linarith only [hl, hh]
  have hpb : p.re < b.re := by
    have hh := div_nonneg (sub_nonneg.mpr hb) (rampSlope_pos w n).le
    linarith only [hr, hh]
  have h0 : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
    rw [up_nextEdge w n hc]
    omega
  have h1 : (kmswStage w n).nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by
    rw [up_nextEdge w n hc]
    omega
  simp only [stageEdgeTrace, h0, h1, ↓reduceDIte]
  change graphOver a.re b.re (roofHeight a b (n + 1) (rampSlope w n)) =
    (layoutArc w (n + 1) s.nextEdge).image ∪
      (layoutArc w (n + 1) (s.nextEdge + 1)).image
  rw [up_new_active_layoutArc w n hc, up_new_missing_layoutArc w n hc]
  obtain ⟨h0w, h0e, h1w, h1e⟩ := up_endpoint_positions w n hc
  rw [h0w, h0e, h1w, h1e]
  change graphOver a.re b.re (roofHeight a b (n + 1) (rampSlope w n)) =
    (roofArc a p (n + 1) (rampSlope w n)).image ∪
      (roofArc p b (n + 1) (rampSlope w n)).image
  have hl' : ((n + 1 : ℝ) - a.im) / rampSlope w n +
      ((n + 1 : ℝ) - p.im) / rampSlope w n < p.re - a.re := by simpa [hp] using hl
  have hr' : ((n + 1 : ℝ) - p.im) / rampSlope w n +
      ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - p.re := by simpa [hp] using hr
  rw [roofArc_image (rampSlope_pos w n) ha hp.le hl',
    roofArc_image (rampSlope_pos w n) hp.le hb hr']
  obtain ⟨hleft, hright⟩ := roofHeight_split (rampSlope_pos w n) hp hl hr
  ext z
  constructor
  · intro hz
    rcases le_total z.re p.re with hx | hx
    · exact Or.inl ⟨hz.1, hx, hz.2.2.trans (hleft z.re hx)⟩
    · exact Or.inr ⟨hx, hz.2.1, hz.2.2.trans (hright z.re hx)⟩
  · rintro (hz | hz)
    · exact ⟨hz.1, hz.2.1.trans hpb.le, hz.2.2.trans (hleft z.re hz.2.1).symm⟩
    · exact ⟨hap.le.trans hz.1, hz.2.1, hz.2.2.trans (hright z.re hz.1).symm⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upNewCap (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : GraphCap := by
  have hab :
      (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re <
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
  obtain ⟨ha, hb, _, _⟩ := up_active_graph_data w n G
  obtain ⟨hA, hB⟩ := upRoofHeight_endpoints w n hc G
  exact spliceCap G.upper (upRoofHeight w n) hab
    (G.upper_continuous.mono (fun _ hx => ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩))
    (continuous_roofHeight _ _ _ _).continuousOn (upRoofHeight_gap w n G) hA hB

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_lower_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver (upNewCap w n hc G).a (upNewCap w n hc G).b (upNewCap w n hc G).low =
      ⋃ e ∈ [(kmswStage w n).active],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  let b := layoutPos w n (s.east s.active)
  have he : s.active < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hmem : s.active ∈ s.UL ++ s.UR := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    simp [s, hxs]
  have htrace : stageEdgeTrace P s.active = (layoutArc w n s.active).image := by
    simp only [stageEdgeTrace, he, ↓reduceDIte, G.arc_layout, Bool.false_eq_true,
      ↓reduceIte]
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n s.active he
  have hEq : ∀ x ∈ Icc a.re b.re, G.upper x = f x := by
    intro x hx
    have hz : (⟨x, f x⟩ : ℂ) ∈ (layoutArc w n s.active).image := by
      rw [hf]
      exact ⟨hx.1, hx.2, rfl⟩
    exact G.upper_eq_arc_height hmem hz
  change graphOver a.re b.re G.upper = _
  simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [up_old_trace w n G h s.active he, htrace, hf]
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans (hEq z.re ⟨hz.1, hz.2.1⟩)⟩
  · intro hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans (hEq z.re ⟨hz.1, hz.2.1⟩).symm⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_upper_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver (upNewCap w n hc G).a (upNewCap w n hc G).b (upNewCap w n hc G).high =
      ⋃ e ∈ [(kmswStage w n).nextEdge, (kmswStage w n).nextEdge + 1],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  change graphOver
    (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re
    (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
    (upRoofHeight w n) = _
  rw [upRoofHeight_graph w n hc h]
  simp

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_region (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    closedGraphRegion G.xmin G.xmax G.lower (upSplicedUpper w n G) =
      closedGraphRegion G.xmin G.xmax G.lower G.upper ∪ closure (upNewCap w n hc G).region :=
    by
  obtain ⟨ha, hb, _, _⟩ := up_active_graph_data w n G
  obtain ⟨hA, hB⟩ := upRoofHeight_endpoints w n hc G
  have hab := (upNewCap w n hc G).ab
  exact closedGraphRegion_spliceFn_eq_union_closure ha.1 hab hb.2 G.upper_continuous
    (continuous_roofHeight _ _ _ _).continuousOn G.lower_le_upper hA hB
    (upRoofHeight_gap w n G)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_disjoint_old_region (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    Disjoint (upNewCap w n hc G).region
      (closedGraphRegion G.xmin G.xmax G.lower G.upper) := by
  exact Set.disjoint_iff_inter_eq_empty.mpr
    (graphRegion_cap_inter_closedGraphRegion G.lower G.upper (upRoofHeight w n))

private theorem finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
  apply reverse_image_subset
  exact Or.inl (Polyline.start_reverse p).symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_drawing_image (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image = P.image ∪
      (stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge ∪
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
          ((kmswStage w n).nextEdge + 1)) := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  have hcount := up_nextEdge w n hc
  have h0 : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by omega
  have h1 : (kmswStage w n).nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by omega
  have hpos : ∀ v : Fin (kmswStage w n).nextVertex,
      Q.pos (stageVertexIncl w n v) = P.pos v := by
    intro v
    rw [G.pos_layout]
    exact layoutPos_old_vertex w n v.val v.isLt
  have hf0 : stageEdgeTrace Q (kmswStage w n).nextEdge =
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
    simp only [stageEdgeTrace, h0, ↓reduceDIte]
    rfl
  have hf1 : stageEdgeTrace Q ((kmswStage w n).nextEdge + 1) =
      (layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1)).image := by
    simp only [stageEdgeTrace, h1, ↓reduceDIte]
    rfl
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
        have hgrow := up_nextVertex w n hc
        have hv' : v.val = (kmswStage w n).nextVertex := by have := v.isLt; omega
        rw [hf0]
        have hz : Q.pos v = (layoutArc w (n + 1) (kmswStage w n).nextEdge).finish := by
          rw [layoutArc_finish w (n + 1) _ h0, (up_new_edge_endpoints w n hc).2.1]
          change layoutPos w (n + 1) v.val = _
          rw [hv']
        exact hz ▸ finish_mem_image _
    · by_cases he : e.val < (kmswStage w n).nextEdge
      · left
        rw [up_old_arc w n G h e.val he e.isLt b] at hz
        exact Or.inr ⟨(⟨e.val, he⟩, b), hz⟩
      · have hf : e.val ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, e.isLt⟩
        have hz' : z ∈ (layoutArc w (n + 1) e.val).image := by
          cases b
          · exact hz
          · exact reverse_image_subset _ hz
        right
        rcases (up_fresh_edge_ids w n e.val hc).mp hf with heq | heq
        · left
          rw [hf0, ← heq]
          exact hz'
        · right
          rw [hf1, ← heq]
          exact hz'
  · rintro (hz | hz)
    · rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
      · exact Or.inl ⟨stageVertexIncl w n v, hpos v⟩
      · refine Or.inr ⟨stageDartIncl w n d, ?_⟩
        change z ∈ (layoutDart w (n + 1) (stageDartIncl w n d)).image
        rw [layoutDart_incl_eq]
        change z ∈ (if d.2 then (layoutArc w n d.1.val).reverse
          else layoutArc w n d.1.val).image
        simpa only [G.arc_layout] using hz
    · rcases hz with hz | hz
      · rw [hf0] at hz
        exact Or.inr ⟨(⟨_, h0⟩, false), hz⟩
      · rw [hf1] at hz
        exact Or.inr ⟨(⟨_, h1⟩, false), hz⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_avoid (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    Disjoint (upNewCap w n hc G).region (monotoneLayoutDrawing w (n + 1) h).image := by
  apply Set.disjoint_left.mpr
  intro z hz hzQ
  rw [up_drawing_image w n hc G h] at hzQ
  rcases hzQ with hzP | hzF
  · exact Set.disjoint_left.mp (upNewCap_disjoint_old_region w n hc G) hz
      (by rw [← G.cover]; exact Or.inl hzP)
  · rw [← upRoofHeight_graph w n hc h] at hzF
    exact (ne_of_lt hz.2.2.2) hzF.2.2

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_disjoint_old_cap (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (upNewCap w n hc G).region (G.cap i).region := by
  apply Set.disjoint_left.mpr
  intro z hz hzC
  apply Set.disjoint_left.mp (upNewCap_disjoint_old_region w n hc G) hz
  rw [← G.cover]
  exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hzC⟩)

private theorem chain_rank_separated (W E : ℕ → ℝ) (xs : List ℕ) :
    xs.IsChain (fun e f => E e = W f) → (∀ e ∈ xs, W e < E e) →
      xs.Pairwise (fun e f => E e ≤ W f) := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    intro hc hinc
    cases tail with
    | nil => simp
    | cons b bs =>
      have ht := ih hc.tail (fun e he => hinc e (List.mem_cons_of_mem a he))
      refine List.pairwise_cons.mpr ⟨?_, ht⟩
      intro e he
      have hab : E a = W b := hc.rel_head? (by simp)
      rcases List.mem_cons.mp he with rfl | he
      · exact hab.le
      · exact hab.le.trans ((hinc b (by simp)).le.trans
          ((List.pairwise_cons.mp ht).1 e he))

private theorem upper_edge_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  simp only [List.mem_append] at he ⊢
  tauto

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_retained_upper_edge_interval (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast ++ (kmswStage w n).UR) :
    (layoutPos w n ((kmswStage w n).east e)).re ≤
        (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re ∨
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re ≤
        (layoutPos w n ((kmswStage w n).west e)).re := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hp := chain_rank_separated
    (fun f => (layoutPos w n ((kmswStage w n).west f)).re)
    (fun f => (layoutPos w n ((kmswStage w n).east f)).re)
    ((kmswStage w n).UL ++ (kmswStage w n).UR)
    ((kmswStage_upper_chain w n).imp (fun _ _ hh =>
      congrArg (fun v => (layoutPos w n v).re) hh))
    (fun f hf => by
      change (kmswStageRank w n ((kmswStage w n).west f) : ℝ) <
        (kmswStageRank w n ((kmswStage w n).east f) : ℝ)
      exact_mod_cast kmswStageRank_strict w n f (upper_edge_lt w n f hf))
  rw [hxs, List.append_assoc, List.singleton_append] at hp
  simp only [hxs, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil,
    List.mem_append] at he
  rcases he with he | he
  · exact Or.inl ((List.pairwise_append.mp hp).2.2 e he _ (by simp))
  · exact Or.inr ((List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).1 e he)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_upper_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver G.xmin G.xmax (upSplicedUpper w n G) =
      ⋃ e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  let s := kmswStage w n
  let Q := monotoneLayoutDrawing w (n + 1) h
  let a := (layoutPos w n (s.west s.active)).re
  let b := (layoutPos w n (s.east s.active)).re
  obtain ⟨hA, hB, _, _⟩ := up_active_graph_data w n G
  obtain ⟨ha, hb⟩ := upRoofHeight_endpoints w n hc G
  have hsplit := graphOver_spliceFn hA.1 hB.2 ha hb
  change graphOver G.xmin G.xmax (spliceFn G.upper (upRoofHeight w n) a b) = _
  rw [hsplit, upRoofHeight_graph w n hc h]
  have hnew := up_boundary_update w n hc
  rw [hnew.1, hnew.2.1]
  have hlist : ∀ e, e ∈ (s.UL.dropLast ++ [s.nextEdge]) ++ (s.nextEdge + 1) :: s.UR ↔
      e ∈ s.UL.dropLast ++ s.UR ∨ e = s.nextEdge ∨ e = s.nextEdge + 1 := by
    intro e
    simp only [List.mem_append, List.mem_cons]
    tauto
  have hret : ∀ e ∈ s.UL.dropLast ++ s.UR, e ∈ s.UL ++ s.UR := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append.mpr (Or.inl (List.mem_of_mem_dropLast he))
    · exact List.mem_append.mpr (Or.inr he)
  ext z
  constructor
  · rintro (⟨hz, hx⟩ | hz)
    · rw [G.upper_trace] at hz
      obtain ⟨e, hz⟩ := mem_iUnion.mp hz
      obtain ⟨he, hz⟩ := mem_iUnion.mp hz
      by_cases heR : e ∈ s.UL.dropLast ++ s.UR
      · refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨(hlist e).mpr (Or.inl heR), ?_⟩⟩
        rw [up_old_trace w n G h e (upper_edge_lt w n e he)]
        exact hz
      · have heA : e = s.active := by
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
          simp only [hxs, List.mem_append, List.mem_singleton] at he
          dsimp only [s] at heR ⊢
          simp only [hxs, List.dropLast_append_cons, List.dropLast_singleton,
            List.append_nil, List.mem_append] at heR
          tauto
        subst e
        rw [← up_old_trace w n G h s.active (kmswStage_boundary_ids_lt_nextEdge w n).1]
          at hz
        have hlow := upNewCap_lower_trace w n hc G h
        simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at hlow
        rw [← hlow] at hz
        change a ≤ z.re ∧ z.re ≤ b ∧ z.im = G.upper z.re at hz
        have heq : z.re = a ∨ z.re = b := by
          change ¬ (a < z.re ∧ z.re < b) at hx
          by_cases hza : z.re = a
          · exact Or.inl hza
          · right
            have haz : a < z.re := lt_of_le_of_ne hz.1 (Ne.symm hza)
            exact le_antisymm hz.2.1 (le_of_not_gt (fun hzb => hx ⟨haz, hzb⟩))
        have hg : z ∈ graphOver a b (upRoofHeight w n) := by
          refine ⟨hz.1, hz.2.1, hz.2.2.trans ?_⟩
          rcases heq with heq | heq
          · simpa only [heq] using ha.symm
          · simpa only [heq] using hb.symm
        rw [upRoofHeight_graph w n hc h] at hg
        rcases hg with hg | hg
        · exact mem_iUnion.mpr ⟨s.nextEdge,
            mem_iUnion.mpr ⟨(hlist _).mpr (Or.inr (Or.inl rfl)), hg⟩⟩
        · exact mem_iUnion.mpr ⟨s.nextEdge + 1,
            mem_iUnion.mpr ⟨(hlist _).mpr (Or.inr (Or.inr rfl)), hg⟩⟩
    · rcases hz with hz | hz
      · exact mem_iUnion.mpr ⟨s.nextEdge,
          mem_iUnion.mpr ⟨(hlist _).mpr (Or.inr (Or.inl rfl)), hz⟩⟩
      · exact mem_iUnion.mpr ⟨s.nextEdge + 1,
          mem_iUnion.mpr ⟨(hlist _).mpr (Or.inr (Or.inr rfl)), hz⟩⟩
  · intro hz
    obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨he, hz⟩ := mem_iUnion.mp hz
    rcases (hlist e).mp he with he | rfl | rfl
    · left
      have heOld := upper_edge_lt w n e (hret e he)
      rw [up_old_trace w n G h e heOld] at hz
      have hzG : z ∈ graphOver G.xmin G.xmax G.upper := by
        rw [G.upper_trace]
        exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hret e he, hz⟩⟩
      refine ⟨hzG, ?_⟩
      have hzA : z ∈ (layoutArc w n e).image := by
        simpa only [stageEdgeTrace, heOld, ↓reduceDIte, G.arc_layout,
          Bool.false_eq_true, ↓reduceIte] using hz
      obtain ⟨f, hf⟩ := layoutArc_image_graph w n e heOld
      rw [hf] at hzA
      rcases up_retained_upper_edge_interval w n e he with heL | heR
      · exact fun hx => (not_lt_of_ge (hzA.2.1.trans heL)) hx.1
      · exact fun hx => (not_lt_of_ge (heR.trans hzA.1)) hx.2
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)

private theorem step_triangle_ids (s : State) (c : Step)
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

private theorem triangle_ids_lt (w : ℕ → Fin 3) (n : ℕ) :
    ∀ t ∈ (kmswStage w n).triangles,
      t.1 < (kmswStage w n).nextEdge ∧ t.2.1 < (kmswStage w n).nextEdge ∧
        t.2.2 < (kmswStage w n).nextEdge := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    apply step_triangle_ids (kmswStage w n) (kmswCodeStep (w n))
      (kmswStage_boundary_ids_lt_nextEdge w n).1 ?_ ih
    intro e he
    exact upper_edge_lt w n e (List.mem_append.mpr (Or.inl he))

private theorem cap_edge_lt (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    (e : ℕ) (he : e ∈ G.capLower i ++ G.capUpper i) :
    e < (kmswStage w n).nextEdge := by
  have ht := triangle_ids_lt w n _ (List.get_mem _ i)
  rcases (G.cap_edges i e).mp he with he | he | he
  · exact he ▸ ht.1
  · exact he ▸ ht.2.1
  · exact he ▸ ht.2.2

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upCaps (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : GraphCap :=
  if hi : i.val < (kmswStage w n).triangles.length then G.cap ⟨i.val, hi⟩
  else upNewCap w n hc G

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upCapLower (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : List ℕ :=
  if hi : i.val < (kmswStage w n).triangles.length then G.capLower ⟨i.val, hi⟩
  else [(kmswStage w n).active]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def upCapUpper (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) : List ℕ :=
  if hi : i.val < (kmswStage w n).triangles.length then G.capUpper ⟨i.val, hi⟩
  else [(kmswStage w n).nextEdge, (kmswStage w n).nextEdge + 1]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_lower_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    graphOver (upCaps w n hc G i).a (upCaps w n hc G i).b (upCaps w n hc G i).low =
      ⋃ e ∈ upCapLower w n G i, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [upCaps, upCapLower, hi, ↓reduceDIte]
    rw [G.cap_lower_trace]
    apply iUnion_congr
    intro e
    apply iUnion_congr
    intro he
    exact (up_old_trace w n G h e (cap_edge_lt w n G ⟨i.val, hi⟩ e
      (List.mem_append.mpr (Or.inl he)))).symm
  · simpa only [upCaps, upCapLower, hi, ↓reduceDIte] using upNewCap_lower_trace w n hc G h

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_upper_trace (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    graphOver (upCaps w n hc G i).a (upCaps w n hc G i).b (upCaps w n hc G i).high =
      ⋃ e ∈ upCapUpper w n G i, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [upCaps, upCapUpper, hi, ↓reduceDIte]
    rw [G.cap_upper_trace]
    apply iUnion_congr
    intro e
    apply iUnion_congr
    intro he
    exact (up_old_trace w n G h e (cap_edge_lt w n G ⟨i.val, hi⟩ e
      (List.mem_append.mpr (Or.inr he)))).symm
  · simpa only [upCaps, upCapUpper, hi, ↓reduceDIte] using upNewCap_upper_trace w n hc G h

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem up_old_cap_avoid (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (G.cap i).region (monotoneLayoutDrawing w (n + 1) h).image := by
  apply Set.disjoint_left.mpr
  intro z hz hzQ
  rw [up_drawing_image w n hc G h] at hzQ
  rcases hzQ with hzP | hzF
  · exact Set.disjoint_left.mp (G.cap_avoid i) hz hzP
  · rw [← upRoofHeight_graph w n hc h] at hzF
    have hzR : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
      rw [← G.cover]
      exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)
    obtain ⟨ha, hb⟩ := upRoofHeight_endpoints w n hc G
    have hh := le_spliceFn ha hb (upRoofHeight_gap w n G) z.re
    rw [spliceFn_of_mem ⟨hzF.1, hzF.2.1⟩] at hh
    have hzL : z ∈ graphOver (upNewCap w n hc G).a (upNewCap w n hc G).b
        (upNewCap w n hc G).low :=
      ⟨hzF.1, hzF.2.1, le_antisymm hzR.2.2.2 (hzF.2.2.symm ▸ hh)⟩
    rw [upNewCap_lower_trace w n hc G h] at hzL
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left] at hzL
    have he := (kmswStage_boundary_ids_lt_nextEdge w n).1
    rw [up_old_trace w n G h _ he] at hzL
    simp only [stageEdgeTrace, he, ↓reduceDIte] at hzL
    exact Set.disjoint_left.mp (G.cap_avoid i) hz (Or.inr ⟨(⟨_, he⟩, false), hzL⟩)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_avoid (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length) :
    Disjoint (upCaps w n hc G i).region (monotoneLayoutDrawing w (n + 1) h).image := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simpa only [upCaps, hi, ↓reduceDIte] using up_old_cap_avoid w n hc G h ⟨i.val, hi⟩
  · simpa only [upCaps, hi, ↓reduceDIte] using upNewCap_avoid w n hc G h

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_disjoint (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i j : Fin (kmswStage w (n + 1)).triangles.length) (hij : i ≠ j) :
    Disjoint (upCaps w n hc G i).region (upCaps w n hc G j).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length <;>
    by_cases hj : j.val < (kmswStage w n).triangles.length
  · simp only [upCaps, hi, hj, ↓reduceDIte]
    apply G.cap_disjoint
    intro heq
    exact hij (Fin.ext (congrArg
      (fun k : Fin (kmswStage w n).triangles.length => k.val) heq))
  · simp only [upCaps, hi, hj, ↓reduceDIte]
    exact (upNewCap_disjoint_old_cap w n hc G ⟨i.val, hi⟩).symm
  · simp only [upCaps, hi, hj, ↓reduceDIte]
    exact upNewCap_disjoint_old_cap w n hc G ⟨j.val, hj⟩
  · have hcount := up_triangle_count w n hc
    have hiB := i.isLt
    have hjB := j.isLt
    exact (hij (Fin.ext (by omega))).elim

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_edges (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w (n + 1)).triangles.length) (e : ℕ) :
    e ∈ upCapLower w n G i ++ upCapUpper w n G i ↔
      e = ((kmswStage w (n + 1)).triangles.get i).1 ∨
        e = ((kmswStage w (n + 1)).triangles.get i).2.1 ∨
        e = ((kmswStage w (n + 1)).triangles.get i).2.2 := by
  have htri := (up_boundary_update w n hc).2.2
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · have ht : (kmswStage w (n + 1)).triangles.get i =
        (kmswStage w n).triangles.get ⟨i.val, hi⟩ := by
      simp only [List.get_eq_getElem, htri, List.getElem_append_left hi]
    simpa only [upCapLower, upCapUpper, hi, ↓reduceDIte, ht] using G.cap_edges ⟨i.val, hi⟩ e
  · have hcount := up_triangle_count w n hc
    have hiB := i.isLt
    have heq : i.val = (kmswStage w n).triangles.length := by omega
    have ht : (kmswStage w (n + 1)).triangles.get i =
        ((kmswStage w n).active, (kmswStage w n).nextEdge,
          (kmswStage w n).nextEdge + 1) := by
      simp only [List.get_eq_getElem, htri, heq,
        List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
    simp only [upCapLower, upCapUpper, hi, ↓reduceDIte, ht, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]

private theorem up_caps_union_closure (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    (⋃ i, closure (upCaps w n hc G i).region) =
      (⋃ i, closure (G.cap i).region) ∪ closure (upNewCap w n hc G).region := by
  have hcount := up_triangle_count w n hc
  ext z
  constructor
  · intro hz
    obtain ⟨i, hz⟩ := mem_iUnion.mp hz
    by_cases hi : i.val < (kmswStage w n).triangles.length
    · left
      exact mem_iUnion.mpr ⟨⟨i.val, hi⟩, by simpa only [upCaps, hi, ↓reduceDIte] using hz⟩
    · exact Or.inr (by simpa only [upCaps, hi, ↓reduceDIte] using hz)
  · rintro (hz | hz)
    · obtain ⟨i, hz⟩ := mem_iUnion.mp hz
      have hi : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      refine mem_iUnion.mpr ⟨⟨i.val, hi⟩, ?_⟩
      simpa only [upCaps, i.isLt, ↓reduceDIte] using hz
    · have hi : (kmswStage w n).triangles.length <
          (kmswStage w (n + 1)).triangles.length := by omega
      refine mem_iUnion.mpr ⟨⟨(kmswStage w n).triangles.length, hi⟩, ?_⟩
      simpa only [upCaps, lt_self_iff_false, ↓reduceDIte] using hz

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cover (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image ∪
        ⋃ i, closure (upCaps w n hc G i).region =
      closedGraphRegion G.xmin G.xmax G.lower (upSplicedUpper w n G) := by
  have hhigh : ∀ z ∈
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge ∪
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
          ((kmswStage w n).nextEdge + 1),
      z ∈ closure (upNewCap w n hc G).region := by
    intro z hz
    rw [← upRoofHeight_graph w n hc h] at hz
    let C := upNewCap w n hc G
    have hcl : closure C.region = closedGraphRegion C.a C.b C.low C.high :=
      closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous C.high_continuous
        C.separated C.left_join C.right_join
    rw [hcl]
    obtain ⟨ha, hb⟩ := upRoofHeight_endpoints w n hc G
    have hh := le_spliceFn ha hb (upRoofHeight_gap w n G) z.re
    rw [spliceFn_of_mem ⟨hz.1, hz.2.1⟩] at hh
    exact ⟨hz.1, hz.2.1, hz.2.2.symm ▸ hh, hz.2.2.le⟩
  rw [invariant_succ_up_region w n hc G, ← G.cover, up_drawing_image w n hc G h,
    up_caps_union_closure w n hc G]
  ext z
  constructor
  · rintro ((hz | hz) | (hz | hz))
    · exact Or.inl (Or.inl hz)
    · exact Or.inr (hhigh z hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  · rintro ((hz | hz) | hz)
    · exact Or.inl (Or.inl hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cover_lower (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : Fin (kmswStage w (n + 1)).nextEdge) :
    e.val ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR ∨
      ∃ i, e.val ∈ upCapLower w n G i := by
  have hnew := up_boundary_update w n hc
  have hcount := up_triangle_count w n hc
  have hFresh : ∀ f ∈ freshEdges w n,
      f ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR := by
    intro f hf
    rw [hnew.1, hnew.2.1]
    rcases (up_fresh_edge_ids w n f hc).mp hf with rfl | rfl <;> simp
  by_cases he : e.val < (kmswStage w n).nextEdge
  · rcases G.cover_lower ⟨e.val, he⟩ with heU | ⟨i, hi⟩
    · by_cases heA : e.val = (kmswStage w n).active
      · right
        have hi : (kmswStage w n).triangles.length <
            (kmswStage w (n + 1)).triangles.length := by omega
        refine ⟨⟨(kmswStage w n).triangles.length, hi⟩, ?_⟩
        simp only [upCapLower, lt_self_iff_false, ↓reduceDIte, List.mem_singleton, heA]
      · left
        rw [hnew.1, hnew.2.1]
        rcases List.mem_append.mp heU with heU | heU
        · have heD : e.val ∈ (kmswStage w n).UL.dropLast := by
            obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
            simpa only [hxs, List.dropLast_append_cons, List.dropLast_singleton,
              List.append_nil] using (List.mem_append.mp (hxs ▸ heU)).resolve_right
                (by simpa only [List.mem_singleton] using heA)
          simp only [List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl heD)
        · simp only [List.mem_append, List.mem_cons]
          exact Or.inr (Or.inr heU)
    · right
      have hiB : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      refine ⟨⟨i.val, hiB⟩, ?_⟩
      simpa only [upCapLower, i.isLt, ↓reduceDIte] using hi
  · exact Or.inl (hFresh e.val (Finset.mem_Ico.mpr ⟨by omega, e.isLt⟩))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cover_upper (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : Fin (kmswStage w (n + 1)).nextEdge) :
    e.val ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR ∨
      ∃ i, e.val ∈ upCapUpper w n G i := by
  have hcount := up_triangle_count w n hc
  by_cases he : e.val < (kmswStage w n).nextEdge
  · rcases G.cover_upper ⟨e.val, he⟩ with heL | ⟨i, hi⟩
    · left
      rw [(up_lower_boundary_update w n hc).1, (up_lower_boundary_update w n hc).2]
      exact heL
    · right
      have hiB : i.val < (kmswStage w (n + 1)).triangles.length := by
        have := i.isLt
        omega
      refine ⟨⟨i.val, hiB⟩, ?_⟩
      simpa only [upCapUpper, i.isLt, ↓reduceDIte] using hi
  · right
    have hiB : (kmswStage w n).triangles.length <
        (kmswStage w (n + 1)).triangles.length := by omega
    refine ⟨⟨(kmswStage w n).triangles.length, hiB⟩, ?_⟩
    simp only [upCapUpper, lt_self_iff_false, ↓reduceDIte, List.mem_cons, List.not_mem_nil,
      or_false]
    exact (up_fresh_edge_ids w n e.val hc).mp (Finset.mem_Ico.mpr ⟨by omega, e.isLt⟩)

private theorem initial_ray_mem_image (p : Polyline) (hlen : 2 ≤ p.points.length)
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

private theorem initial_line_at (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re ≠ 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) (x : ℝ)
    (ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1) :
    f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  have hx : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, div_mul_cancel₀ _ hd]
    ring
  have hh := hgraph _ (initial_ray_mem_image p hlen ht)
  rw [hx] at hh
  rw [hh]
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  ring

private theorem initial_line_east (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : 0 < p.initialDirection.re)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc p.start.re (p.start.re + η),
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨p.initialDirection.re, hd, ?_⟩
  intro x hx
  apply initial_line_at p f hlen hd.ne' hgraph x
  exact ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
    (div_le_one hd).mpr (by linarith only [hx.2])⟩

private theorem initial_line_west (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re < 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc (p.start.re - η) p.start.re,
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨-p.initialDirection.re, neg_pos.mpr hd, ?_⟩
  intro x hx
  apply initial_line_at p f hlen hd.ne hgraph x
  exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) hd.le,
    (div_le_one_of_neg hd).mpr (by linarith only [hx.1])⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_ext_upper_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (closedGraphRegion G.xmin G.xmax G.lower (upSplicedUpper w n G))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, false)
  have hd : 0 < p.initialDirection.re :=
    Polyline.initialDirection_re_pos (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, upSplicedUpper w n G z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver G.xmin G.xmax (upSplicedUpper w n G) := by
      rw [invariant_succ_up_upper_trace w n hc G h]
      refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      simpa only [stageEdgeTrace, he, ↓reduceDIte] using hz
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := initial_line_east p (upSplicedUpper w n G)
    (Q.arc_length (⟨e, he⟩, false)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_east_upper p.start p.initialDirection η hd hη hline

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_ext_lower_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).initialDirection
      (closedGraphRegion G.xmin G.xmax G.lower (upSplicedUpper w n G))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, true)
  have hd : p.initialDirection.re < 0 :=
    Polyline.reverse_initialDirection_re_neg (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, G.lower z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver G.xmin G.xmax G.lower := by
      rw [invariant_succ_up_lower_trace w n hc G h]
      refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      simp only [stageEdgeTrace, he, ↓reduceDIte]
      exact reverse_image_subset _ hz
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := initial_line_west p G.lower
    (Q.arc_length (⟨e, he⟩, true)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_west_lower p.start p.initialDirection η hd hη hline

private theorem roof_left_line {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im < H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    ∃ η > 0, a.re + η < b.re ∧
      ∀ x ∈ Icc a.re (a.re + η), roofHeight a b H M x = a.im + M * (x - a.re) := by
  let η := (H - a.im) / M
  have hη : 0 < η := div_pos (sub_pos.mpr ha) hM
  have hηb : a.re + η < b.re := by
    have hh := div_nonneg (sub_nonneg.mpr hb) hM.le
    dsimp only [η]
    linarith only [hfit, hh]
  refine ⟨η, hη, hηb, ?_⟩
  intro x hx
  have hsum : H - a.im + (H - b.im) < (b.re - a.re) * M := by
    rw [← add_div] at hfit
    exact (div_lt_iff₀ hM).mp hfit
  have hwidth : M * (x - a.re) ≤ H - a.im := by
    have hh := mul_le_mul_of_nonneg_left hx.2 hM.le
    dsimp only [η] at hh
    rw [mul_add, mul_div_cancel₀ _ hM.ne'] at hh
    linarith only [hh]
  have hRise : a.im + M * (x - a.re) ≤ H := by linarith only [hwidth]
  have hFall : H ≤ b.im + M * (b.re - x) := by nlinarith only [hsum, hwidth]
  simp only [roofHeight, min_eq_left (hRise.trans hFall), min_eq_right hRise]

private theorem up_fresh_roof_arcs (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    let s := kmswStage w n
    let a := layoutPos w n (s.west s.active)
    let b := layoutPos w n (s.east s.active)
    let p := layoutPos w (n + 1) s.nextVertex
    layoutArc w (n + 1) s.nextEdge = roofArc a p (n + 1) (rampSlope w n) ∧
      layoutArc w (n + 1) (s.nextEdge + 1) = roofArc p b (n + 1) (rampSlope w n) := by
  dsimp only
  rw [up_new_active_layoutArc w n hc, up_new_missing_layoutArc w n hc]
  obtain ⟨h0w, h0e, h1w, h1e⟩ := up_endpoint_positions w n hc
  rw [h0w, h0e, h1w, h1e]
  exact ⟨rfl, rfl⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_lower_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    WedgeIn (layoutArc w n (kmswStage w n).active).start
      (layoutArc w n (kmswStage w n).active).initialDirection (upNewCap w n hc G).region :=
    by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  let b := layoutPos w n (s.east s.active)
  let p := layoutArc w n s.active
  have he : s.active < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hstart : p.start = a := layoutArc_start w n s.active he
  have hd : 0 < p.initialDirection.re :=
    Polyline.initialDirection_re_pos (layoutArc_points_pairwise w n s.active he)
      (layoutArc_length_two_le w n s.active)
  have hmem : s.active ∈ s.UL ++ s.UR := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    simp [s, hxs]
  obtain ⟨η₀, hη₀, hline⟩ := initial_line_east p G.upper
    (layoutArc_length_two_le w n s.active) hd (fun z hz => G.upper_eq_arc_height hmem hz)
  obtain ⟨haB, hbB, hA, _⟩ := up_active_graph_data w n G
  have haH : a.im < (n + 1 : ℝ) := by
    have hh := G.upper_le_stage haB
    rw [hA] at hh
    linarith only [hh]
  obtain ⟨_, hbH, _, _, _⟩ := up_roof_setup w n hc
  obtain ⟨η₁, hη₁, hηb, hroof⟩ := roof_left_line (rampSlope_pos w n) haH hbH
    (up_outer_roof_fit w n hc)
  let η := min η₀ η₁
  have hη : 0 < η := lt_min hη₀ hη₁
  have hs : p.initialDirection.im / p.initialDirection.re < rampSlope w n :=
    (le_abs_self _).trans_lt (layoutArc_initial_slope_abs_lt w n s.active he)
  change WedgeIn p.start p.initialDirection (graphRegion a.re b.re G.upper (upRoofHeight w n))
  apply wedgeIn_graphRegion_east_lower_slope p.start p.initialDirection η (rampSlope w n)
    hd (by rw [hstart]) hη ?_ ?_ hs ?_
  · rw [hstart]
    have hh : η ≤ η₁ := min_le_right _ _
    linarith only [hh, hηb]
  · intro x hx
    have hh : η ≤ η₀ := min_le_left _ _
    exact hline x ⟨hx.1, by linarith only [hx.2, hh]⟩
  · intro x hx
    have hx' : x ∈ Icc a.re (a.re + η₁) := by
      rw [hstart] at hx
      have hh : η ≤ η₁ := min_le_right _ _
      exact ⟨hx.1, by linarith only [hx.2, hh]⟩
    change p.start.im + rampSlope w n * (x - p.start.re) ≤
      roofHeight a b (n + 1) (rampSlope w n) x
    rw [hroof x hx', hstart]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem upNewCap_upper_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hf : e = (kmswStage w n).nextEdge ∨ e = (kmswStage w n).nextEdge + 1) :
    WedgeIn (layoutArc w (n + 1) e).reverse.start
      (layoutArc w (n + 1) e).reverse.initialDirection (upNewCap w n hc G).region := by
  let s := kmswStage w n
  let a := layoutPos w n (s.west s.active)
  let b := layoutPos w n (s.east s.active)
  let p := layoutPos w (n + 1) s.nextVertex
  let q := (layoutArc w (n + 1) e).reverse
  obtain ⟨haB, hbB, _, hB⟩ := up_active_graph_data w n G
  obtain ⟨haH, hbH, hpH, hl, hr⟩ := up_roof_setup w n hc
  change a.im ≤ _ at haH
  change b.im ≤ _ at hbH
  change p.im = _ at hpH
  change ((n + 1 : ℝ) - a.im) / rampSlope w n < p.re - a.re at hl
  change ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - p.re at hr
  have hap : a.re < p.re := by
    have hh := div_nonneg (sub_nonneg.mpr haH) (rampSlope_pos w n).le
    linarith only [hl, hh]
  have hpb : p.re < b.re := by
    have hh := div_nonneg (sub_nonneg.mpr hbH) (rampSlope_pos w n).le
    linarith only [hr, hh]
  have hd : q.initialDirection.re < 0 :=
    Polyline.reverse_initialDirection_re_neg (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hlen : 2 ≤ q.points.length := by
    simpa only [q, Polyline.reverse, List.length_reverse] using
      layoutArc_length_two_le w (n + 1) e
  have hgraph : ∀ z ∈ q.image, upRoofHeight w n z.re = z.im := by
    intro z hz
    have hz' := reverse_image_subset (layoutArc w (n + 1) e) hz
    have hzG : z ∈ graphOver a.re b.re (upRoofHeight w n) := by
      rw [upRoofHeight_graph w n hc h]
      have hzT : z ∈ stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
        simp only [stageEdgeTrace, he, ↓reduceDIte]
        exact hz'
      rcases hf with rfl | rfl
      · exact Or.inl hzT
      · exact Or.inr hzT
    exact hzG.2.2.symm
  obtain ⟨η₀, hη₀, hline⟩ := initial_line_west q (upRoofHeight w n) hlen hd hgraph
  obtain ⟨harc0, harc1⟩ := up_fresh_roof_arcs w n hc
  change layoutArc w (n + 1) s.nextEdge = roofArc a p (n + 1) (rampSlope w n) at harc0
  change layoutArc w (n + 1) (s.nextEdge + 1) = roofArc p b (n + 1) (rampSlope w n) at harc1
  change WedgeIn q.start q.initialDirection (graphRegion a.re b.re G.upper (upRoofHeight w n))
  rcases hf with rfl | rfl
  · have hstart : q.start = p := by
      change (layoutArc w (n + 1) s.nextEdge).reverse.start = p
      rw [harc0, Polyline.start_reverse, roofArc_finish]
    have hfit : ((n + 1 : ℝ) - a.im) / rampSlope w n +
        ((n + 1 : ℝ) - p.im) / rampSlope w n < p.re - a.re := by simpa [hpH] using hl
    have hzero : q.initialDirection.im = 0 := by
      change (layoutArc w (n + 1) s.nextEdge).reverse.initialDirection.im = 0
      rw [harc0]
      exact (roofArc_reverse_initialDirection_top_geom (rampSlope_pos w n) haH hpH hfit).2
    let η := min η₀ (min (p.re - a.re) (1 / 2))
    have hη : 0 < η := lt_min hη₀ (lt_min (sub_pos.mpr hap) (by norm_num))
    have hηa : η ≤ p.re - a.re := (min_le_right _ _).trans (min_le_left _ _)
    have hηhalf : η ≤ (1 / 2 : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
    apply wedgeIn_graphRegion_west_upper_slope q.start q.initialDirection η 1 hd
      (by rw [hstart]; exact hpb.le) hη ?_ ?_ ?_ ?_
    · rw [hstart]
      linarith only [hηa]
    · intro x hx
      have hh : η ≤ η₀ := min_le_left _ _
      exact hline x ⟨by linarith only [hx.1, hh], hx.2⟩
    · rw [hzero, zero_div]
      norm_num
    · intro x hx
      rw [hstart] at hx ⊢
      have hxB : x ∈ Icc G.xmin G.xmax :=
        ⟨haB.1.trans (by linarith only [hx.1, hηa]), hx.2.trans (hpb.le.trans hbB.2)⟩
      have hh := G.upper_le_stage hxB
      rw [hpH]
      linarith only [hh, hx.1, hηhalf]
  · have hstart : q.start = b := by
      change (layoutArc w (n + 1) (s.nextEdge + 1)).reverse.start = b
      rw [harc1, Polyline.start_reverse, roofArc_finish]
    have hbHt : b.im < (n + 1 : ℝ) := by
      have hh := G.upper_le_stage hbB
      rw [hB] at hh
      linarith only [hh]
    have hslope : q.initialDirection.im / q.initialDirection.re = -rampSlope w n := by
      change (layoutArc w (n + 1) (s.nextEdge + 1)).reverse.initialDirection.im /
        (layoutArc w (n + 1) (s.nextEdge + 1)).reverse.initialDirection.re = _
      rw [harc1]
      exact roofArc_reverse_initialSlope (rampSlope_pos w n) hbHt
    obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
    let η := min η₀ (b.re - a.re)
    have hη : 0 < η := lt_min hη₀ (sub_pos.mpr (hap.trans hpb))
    have hηa : η ≤ b.re - a.re := min_le_right _ _
    apply wedgeIn_graphRegion_west_upper_slope q.start q.initialDirection η (-L) hd
      (by rw [hstart]) hη ?_ ?_ ?_ ?_
    · rw [hstart]
      linarith only [hηa]
    · intro x hx
      have hh : η ≤ η₀ := min_le_left _ _
      exact hline x ⟨by linarith only [hx.1, hh], hx.2⟩
    · rw [hslope]
      linarith only [hLM]
    · intro x hx
      rw [hstart] at hx ⊢
      have hxB : x ∈ Icc G.xmin G.xmax :=
        ⟨haB.1.trans (by linarith only [hx.1, hηa]), hx.2.trans hbB.2⟩
      have hh := (le_abs_self (G.upper x - G.upper b.re)).trans (hLip x hxB b.re hbB)
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2), hB] at hh
      linarith only [hh]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_lower_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length)
    (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge) (hmem : e ∈ upCapLower w n G i) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (upCaps w n hc G i).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [upCaps, upCapLower, hi, ↓reduceDIte] at hmem ⊢
    have heOld := cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append.mpr (Or.inl hmem))
    simpa only [up_old_arc w n G h e heOld he false] using
      G.cap_lower_wedge ⟨i.val, hi⟩ e heOld hmem
  · simp only [upCaps, upCapLower, hi, ↓reduceDIte, List.mem_singleton] at hmem ⊢
    subst e
    have heOld := (kmswStage_boundary_ids_lt_nextEdge w n).1
    simpa only [up_old_arc w n G h _ heOld he false, G.arc_layout, Bool.false_eq_true,
      ↓reduceIte] using upNewCap_lower_wedge w n hc G

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_up_cap_upper_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w (n + 1)).triangles.length)
    (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge) (hmem : e ∈ upCapUpper w n G i) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).initialDirection
      (upCaps w n hc G i).region := by
  by_cases hi : i.val < (kmswStage w n).triangles.length
  · simp only [upCaps, upCapUpper, hi, ↓reduceDIte] at hmem ⊢
    have heOld := cap_edge_lt w n G ⟨i.val, hi⟩ e (List.mem_append.mpr (Or.inr hmem))
    simpa only [up_old_arc w n G h e heOld he true] using
      G.cap_upper_wedge ⟨i.val, hi⟩ e heOld hmem
  · simp only [upCaps, upCapUpper, hi, ↓reduceDIte, List.mem_cons, List.not_mem_nil,
      or_false] at hmem ⊢
    exact upNewCap_upper_wedge w n hc G h e he hmem

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def invariant_succ_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) :
    MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h) where
  toMonotoneStageCertificate :=
    { xmin := G.xmin
      xmax := G.xmax
      hx := G.hx
      lower := G.lower
      upper := upSplicedUpper w n G
      lower_continuous := G.lower_continuous
      upper_continuous := invariant_succ_up_upper_continuous w n hc G
      lower_le_upper := invariant_succ_up_lower_le_upper w n hc G
      lower_trace := invariant_succ_up_lower_trace w n hc G h
      upper_trace := invariant_succ_up_upper_trace w n hc G h
      cap := upCaps w n hc G
      capLower := upCapLower w n G
      capUpper := upCapUpper w n G
      cap_lower_trace := invariant_succ_up_cap_lower_trace w n hc G h
      cap_upper_trace := invariant_succ_up_cap_upper_trace w n hc G h
      cap_edges := invariant_succ_up_cap_edges w n hc G
      cap_avoid := invariant_succ_up_cap_avoid w n hc G h
      cap_disjoint := invariant_succ_up_cap_disjoint w n hc G
      cover := invariant_succ_up_cover w n hc G h
      cap_lower_wedge := invariant_succ_up_cap_lower_wedge w n hc G h
      cap_upper_wedge := invariant_succ_up_cap_upper_wedge w n hc G h
      ext_upper_wedge := invariant_succ_up_ext_upper_wedge w n hc G h
      ext_lower_wedge := invariant_succ_up_ext_lower_wedge w n hc G h }
  cover_lower := invariant_succ_up_cover_lower w n hc G
  cover_upper := invariant_succ_up_cover_upper w n hc G
  upper_lipschitz_margin := invariant_succ_up_upper_lipschitz_margin w n hc G
  image_height_le := by
    simpa only [Nat.cast_add, Nat.cast_one] using invariant_succ_up_image_height_le w n hc G h
  pos_layout := invariant_succ_up_pos_layout w n hc h
  arc_layout := invariant_succ_up_arc_layout w n hc h

end DirectedDistances.KMSW
