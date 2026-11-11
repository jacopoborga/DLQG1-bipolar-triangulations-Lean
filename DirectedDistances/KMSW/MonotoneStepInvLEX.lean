module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.MonotoneStepCommon
public import DirectedDistances.PlanarMap.GraphRegionSplice
import DirectedDistances.KMSW.HatTriangleSim






public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open Set





theorem kmswStage_succ_lex_triangles (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).triangles =
      (kmswStage w n).triangles ++ [((kmswStage w n).active,
        (kmswStage w n).nextEdge, e)] := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]





theorem kmswStage_succ_lex_UL (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).UL = es.reverse ++ [(kmswStage w n).nextEdge] := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]





theorem kmswStage_succ_lex_allocation (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]




theorem invariant_succ_lex_stage_lists (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge ∧
      (kmswStage w (n + 1)).triangles =
        (kmswStage w n).triangles ++
          [((kmswStage w n).active, (kmswStage w n).nextEdge, e)] ∧
      (kmswStage w (n + 1)).UL = es.reverse ++ [(kmswStage w n).nextEdge] ∧
      (kmswStage w (n + 1)).UR = (kmswStage w n).UR ∧
      (kmswStage w (n + 1)).LL = (kmswStage w n).LL ∧
      (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- The LEX edge joins the west endpoint of its predecessor to the active
edge's east endpoint.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswStage_succ_lex_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
        (kmswStage w n).west e ∧
      (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
        (kmswStage w n).east (kmswStage w n).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]




theorem kmswStage_succ_lex_fresh (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).nextEdge ∈ freshEdges w n := by
  rw [freshEdges]
  have halloc := (kmswStage_succ_lex_allocation w n hc e es hUL).1
  rw [halloc]
  exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self _⟩




theorem layoutArc_succ_lex_chord (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    layoutArc w (n + 1) (kmswStage w n).nextEdge =
      roofArc
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge))
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) := by
  have hf := kmswStage_succ_lex_fresh w n hc e es hUL
  have hnot : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    intro hm
    have hne : (kmswStage w n).UL.dropLast.reverse ≠ [] := by
      rw [hUL]
      simp
    exact hne hm.2.1
  rw [layoutArc_fresh w n (kmswStage w n).nextEdge hf]
  simp only [hnot, ↓reduceIte]




theorem layoutArc_succ_lex_chord_image (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (layoutArc w (n + 1) (kmswStage w n).nextEdge).image =
      {z | (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)).re ≤ z.re ∧
        z.re ≤ (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)).re ∧
        z.im = roofHeight
          (layoutPos w (n + 1)
            ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge))
          (layoutPos w (n + 1)
            ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge))
          (n + 1) (rampSlope w n) z.re} := by
  rw [layoutArc_succ_lex_chord w n hc e es hUL]
  have hf := kmswStage_succ_lex_fresh w n hc e es hUL
  exact roofArc_image (rampSlope_pos w n)
    (freshEdges_endpoint_heights w n _ hf).1
    (freshEdges_endpoint_heights w n _ hf).2
    (freshEdges_ramp_widths_lt w n _ hf)

/-- Existing vertices retain their layout positions across a LEX step.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutPos_succ_lex_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    layoutPos w (n + 1) v = layoutPos w n v :=
  layoutPos_old_vertex w n v hv




theorem layoutArc_succ_lex_old_edge (w : ℕ → Fin 3) (n f : ℕ)
    (hf : f < (kmswStage w n).nextEdge) :
    layoutArc w (n + 1) f = layoutArc w n f :=
  layoutArc_old w n f hf




theorem invariant_succ_lex_old_dart (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  rcases d with ⟨f, b⟩
  cases b
  · simpa [layoutDart, stageDartIncl] using
      layoutArc_old w n f.val f.isLt
  · simpa [layoutDart, stageDartIncl] using
      congrArg Polyline.reverse (layoutArc_old w n f.val f.isLt)

/-- The endpoints of the new chord keep the old endpoint positions.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutPos_succ_lex_chord_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    layoutPos w (n + 1)
        ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge) =
      layoutPos w n ((kmswStage w n).west e) ∧
    layoutPos w (n + 1)
        ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge) =
      layoutPos w n ((kmswStage w n).east (kmswStage w n).active) := by
  have hend := kmswStage_succ_lex_endpoints w n hc e es hUL
  have hids := kmswStage_boundary_ids_lt_nextEdge w n
  have heULrev : e ∈ (kmswStage w n).UL.dropLast.reverse := by
    rw [hUL]
    simp
  have heUL : e ∈ (kmswStage w n).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp heULrev)
  have hebound : e < (kmswStage w n).nextEdge :=
    hids.2 e (by simp [List.mem_append, heUL])
  have hwest :=
    (kmswStage_endpoints_lt_nextVertex w n e hebound).1
  have hactive :=
    (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active hids.1).2
  rw [hend.1, hend.2]
  exact ⟨layoutPos_old_vertex w n _ hwest,
    layoutPos_old_vertex w n _ hactive⟩

/-- Every point on the new chord has height at most the allocated height.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutArc_succ_lex_chord_height_le (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {z : ℂ} (hz : z ∈ (layoutArc w (n + 1)
      (kmswStage w n).nextEdge).image) : z.im ≤ (n + 1 : ℝ) := by
  rw [layoutArc_succ_lex_chord_image w n hc e es hUL] at hz
  calc
    z.im = roofHeight
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge))
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) z.re := hz.2.2
    _ ≤ n + 1 := roofHeight_le_top _ _ _ _ _

/-- The canonical successor drawing has the required position field by
definition.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_pos_layout (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w (n + 1)) :
    ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      (monotoneLayoutDrawing w (n + 1) h).pos v =
        layoutPos w (n + 1) v.val := by
  intro v
  rfl

/-- The canonical successor drawing has the required arc field by definition.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_arc_layout (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w (n + 1)) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      (monotoneLayoutDrawing w (n + 1) h).arc d =
        if d.2 then (layoutArc w (n + 1) d.1.val).reverse
        else layoutArc w (n + 1) d.1.val := by
  intro d
  rfl




theorem stageEdgeTrace_succ_lex_old (w : ℕ → Fin 3) (n f : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (hf : f < (kmswStage w n).nextEdge) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f =
      stageEdgeTrace P f := by
  have hnew : f < (kmswStage w (n + 1)).nextEdge :=
    hf.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))
  let d₀ : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, false)
  let d₁ : StageDart (kmswStage w (n + 1)).nextEdge := (⟨f, hnew⟩, false)
  have hD : stageDartIncl w n d₀ = d₁ := by
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  have hArc : (monotoneLayoutDrawing w (n + 1) h).arc d₁ = P.arc d₀ := by
    calc
      (monotoneLayoutDrawing w (n + 1) h).arc d₁ = layoutDart w (n + 1) d₁ := by
        simpa [layoutDart] using invariant_succ_lex_arc_layout w n h d₁
      _ = layoutDart w (n + 1) (stageDartIncl w n d₀) := by rw [← hD]
      _ = layoutDart w n d₀ := invariant_succ_lex_old_dart w n d₀
      _ = P.arc d₀ := by simpa [layoutDart] using (G.arc_layout d₀).symm
  unfold stageEdgeTrace
  simp only [dite_eq_left hnew, dite_eq_left hf]
  simpa [d₀, d₁] using congrArg Polyline.image hArc




theorem invariant_succ_lex_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver G.xmin G.xmax G.lower =
      ⋃ f ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
  rcases invariant_succ_lex_stage_lists w n hc e es hUL with
    ⟨_, _, _, _, hLL, hLR⟩
  rw [hLL, hLR, G.lower_trace]
  ext z
  simp only [Set.mem_iUnion, List.mem_append]
  constructor
  · rintro ⟨f, hf, hz⟩
    have hf' : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
        (kmswStage w n).LL ++ (kmswStage w n).LR := by
      have hmem := hf
      simp only [List.mem_append] at hmem ⊢
      rcases hmem with hmem | hmem
      · exact Or.inl (Or.inr hmem)
      · exact Or.inr hmem
    have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 f hf'
    have htrace := stageEdgeTrace_succ_lex_old w n f G h hbound
    exact ⟨f, hf, by simpa only [htrace] using hz⟩
  · rintro ⟨f, hf, hz⟩
    have hf' : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
        (kmswStage w n).LL ++ (kmswStage w n).LR := by
      have hmem := hf
      simp only [List.mem_append] at hmem ⊢
      rcases hmem with hmem | hmem
      · exact Or.inl (Or.inr hmem)
      · exact Or.inr hmem
    have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 f hf'
    have htrace := stageEdgeTrace_succ_lex_old w n f G h hbound
    exact ⟨f, hf, by simpa only [htrace] using hz⟩

private theorem lex_reverse_point (p : Polyline) (i : ℕ)
    (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.reverse.getD i p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_reverse i hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]

private theorem lex_reverse_segment (p : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold Polyline.segmentAt
  rw [lex_reverse_point p i (by omega), lex_reverse_point p (i + 1) hi]
  have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [h₁, h₂, segment_symm]

private theorem lex_finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
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

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_chord_roof_gap (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ x ∈ Ioo
        (layoutPos w n ((kmswStage w n).west e)).re
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re,
      G.upper x < roofHeight
        (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) x := by
  have _hcase : w n = 0 := hc
  let s := kmswStage w n
  have heUL : e ∈ s.UL ++ s.UR := by
    have he : e ∈ s.UL.dropLast.reverse := by rw [hUL]; simp
    exact List.mem_append_left _
      (List.mem_of_mem_dropLast (List.mem_reverse.mp he))
  have he : e < s.nextEdge := by
    exact (stageRotation_UL_bound w n) e
      (List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hUL]; simp)))
  have hactive : s.active ∈ s.UL ++ s.UR := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    have hxs' : s.UL = xs ++ [s.active] := by simpa [s] using hxs
    rw [hxs']
    exact List.mem_append_left _ (List.mem_append_right _ (by simp))
  have haEdge : s.west e < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n e he).1
  have hbEdge : s.east s.active < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (act_lt_nextEdge w (le_refl n))).2
  let va : Fin s.nextVertex := ⟨s.west e, haEdge⟩
  let vb : Fin s.nextVertex := ⟨s.east s.active, hbEdge⟩
  have hia : layoutPos w n va.val ∈ P.image := by
    rw [← G.pos_layout va]
    exact Or.inl ⟨va, rfl⟩
  have hib : layoutPos w n vb.val ∈ P.image := by
    rw [← G.pos_layout vb]
    exact Or.inl ⟨vb, rfl⟩
  have hba := G.image_bounds hia
  have hbb := G.image_bounds hib
  have hza : layoutPos w n va.val ∈ (layoutArc w n e).image := by
    rw [← layoutArc_start w n e he]
    exact Or.inl rfl
  have hzb : layoutPos w n vb.val ∈ (layoutArc w n s.active).image := by
    rw [← layoutArc_finish w n s.active (act_lt_nextEdge w (le_refl n))]
    exact lex_finish_mem_image _
  have hya := G.upper_eq_arc_height heUL hza
  have hyb := G.upper_eq_arc_height hactive hzb
  have hArange : (layoutPos w n (s.west e)).re ∈ Icc G.xmin G.xmax := by
    simpa only [va, Fin.val_mk] using ⟨hba.1, hba.2.1⟩
  have hBrange : (layoutPos w n (s.east s.active)).re ∈ Icc G.xmin G.xmax := by
    simpa only [vb, Fin.val_mk] using ⟨hbb.1, hbb.2.1⟩
  have hya' : G.upper (layoutPos w n (s.west e)).re =
      (layoutPos w n (s.west e)).im := by
    simpa only [va, Fin.val_mk] using hya
  have hyb' : G.upper (layoutPos w n (s.east s.active)).re =
      (layoutPos w n (s.east s.active)).im := by
    simpa only [vb, Fin.val_mk] using hyb
  intro x hx
  exact G.upper_lt_roofHeight hArange hBrange (le_of_eq hya')
    (le_of_eq hyb') x hx

private theorem lex_reverse_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ lex_finish_mem_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    rw [lex_reverse_segment p i hi'] at hz
    exact Or.inr ⟨p.points.length - 2 - i, by omega, hz⟩

/-- Height bound for the full successor drawing, including its fresh chord.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_image_height_le (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    ∀ z ∈ (monotoneLayoutDrawing w (n + 1) h).image,
      z.im ≤ (n + 1 : ℝ) := by
  intro z hz
  change z ∈ Set.range (monotoneLayoutDrawing w (n + 1) h).pos ∪
    {z | ∃ d, z ∈ (layoutDart w (n + 1) d).image} at hz
  rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
  · rw [invariant_succ_lex_pos_layout w n h]
    change layoutHeight w (n + 1) v.val ≤ (n + 1 : ℝ)
    simpa only [Nat.cast_add, Nat.cast_one] using
      layoutHeight_le w (n + 1) v.val v.isLt
  · have halloc := (kmswStage_succ_lex_allocation w n hc e es hUL).1
    have hval : d.1.val ≤ (kmswStage w n).nextEdge := by omega
    by_cases hold : d.1.val < (kmswStage w n).nextEdge
    · let d₀ : StageDart (kmswStage w n).nextEdge :=
        (⟨d.1.val, hold⟩, d.2)
      have hArc : layoutDart w (n + 1) d = P.arc d₀ := by
        cases hb : d.2
        · simp only [layoutDart, hb]
          rw [layoutArc_succ_lex_old_edge w n d.1.val hold]
          have hP := G.arc_layout d₀
          simpa [d₀, hb] using hP.symm
        · simp only [layoutDart, hb, ↓reduceIte]
          rw [layoutArc_succ_lex_old_edge w n d.1.val hold]
          have hP := G.arc_layout d₀
          simpa [d₀, hb] using hP.symm
      rw [hArc] at hz
      have hPimage : z ∈ P.image := by
        change z ∈ Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}
        exact Or.inr ⟨d₀, hz⟩
      exact (G.image_height_le z hPimage).trans (by exact_mod_cast Nat.le_succ n)
    · have hEq : d.1.val = (kmswStage w n).nextEdge := by omega
      cases hb : d.2
      · have hz' : z ∈ (layoutArc w (n + 1)
            (kmswStage w n).nextEdge).image := by
          simpa [layoutDart, hb, hEq] using hz
        exact layoutArc_succ_lex_chord_height_le w n hc e es hUL hz'
      · have hzrev : z ∈ (layoutArc w (n + 1)
            (kmswStage w n).nextEdge).reverse.image := by
          simpa [layoutDart, hb, hEq] using hz
        have hz' : z ∈ (layoutArc w (n + 1)
            (kmswStage w n).nextEdge).image :=
          lex_reverse_image_subset _ hzrev
        exact layoutArc_succ_lex_chord_height_le w n hc e es hUL
          hz'





theorem lipschitz_graph_strictly_below_roof {a b : ℂ} {H L M : ℝ}
    {g : ℝ → ℝ} (hab : a.re < b.re) (hLM : L < M)
    (hbound : ∀ x ∈ Set.Icc a.re b.re, ∀ y ∈ Set.Icc a.re b.re,
      |g x - g y| ≤ L * |x - y|)
    (hleft : g a.re = a.im) (hright : g b.re = b.im)
    (hbelow : ∀ x ∈ Set.Ioo a.re b.re, g x < H) :
    ∀ x ∈ Set.Ioo a.re b.re, g x < roofHeight a b H M x := by
  apply segmentHeight_separation hLM g
  · intro x hx
    have hxa := hbound x hx a.re ⟨le_rfl, hab.le⟩
    have hxb := hbound x hx b.re ⟨hab.le, le_rfl⟩
    have hxa' : |g x - a.im| ≤ L * |x - a.re| := by simpa [hleft] using hxa
    have hxb' : |g x - b.im| ≤ L * |x - b.re| := by simpa [hright] using hxb
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at hxa'
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at hxb'
    have hxa'' := (abs_le.mp hxa').2
    have hxb'' := (abs_le.mp hxb').2
    constructor <;> linarith
  · exact hbelow




theorem layoutArc_succ_lex_chord_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (layoutArc w (n + 1) (kmswStage w n).nextEdge).start =
        layoutPos w (n + 1)
          ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge) ∧
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).finish =
        layoutPos w (n + 1)
          ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge) := by
  constructor
  · rw [layoutArc_succ_lex_chord w n hc e es hUL]
    exact roofArc_start _ _ _ _
  · rw [layoutArc_succ_lex_chord w n hc e es hUL]
    exact roofArc_finish _ _ _ _

private theorem lex_old_UL (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).UL = es.reverse ++ [e, (kmswStage w n).active] := by
  have hd : (kmswStage w n).UL.dropLast = es.reverse ++ [e] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse hUL
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hx : xs = es.reverse ++ [e] := by
    simpa only [hxs, List.dropLast_append_cons, List.dropLast_singleton,
    List.append_nil] using hd
  rw [hxs, hx, List.append_assoc]
  rfl

private theorem lex_upper_bound (w : ℕ → Fin 3) (n f : ℕ)
    (hf : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    f < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 f
  simp only [List.mem_append] at hf ⊢
  tauto

private theorem lex_trace_layout {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {f : ℕ} (hf : f < (kmswStage w n).nextEdge) :
    stageEdgeTrace P f = (layoutArc w n f).image := by
  simp only [stageEdgeTrace, hf, ↓reduceDIte, G.arc_layout, Bool.false_eq_true,
    ↓reduceIte]

private theorem lex_upper_graph {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {f : ℕ}
    (hf : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    (layoutArc w n f).image ⊆ graphOver G.xmin G.xmax G.upper := by
  rw [G.upper_trace]
  intro z hz
  exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf,
    (lex_trace_layout G (lex_upper_bound w n f hf)).symm ▸ hz⟩⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem lex_chord_geometry (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west e)
    let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    let g := roofHeight a b (n + 1) (rampSlope w n)
    a.re < b.re ∧ a.re ∈ Icc G.xmin G.xmax ∧ b.re ∈ Icc G.xmin G.xmax ∧
      g a.re = G.upper a.re ∧ g b.re = G.upper b.re := by
  dsimp only
  have hULold := lex_old_UL w n e es hUL
  have heU : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have haU : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have he := lex_upper_bound w n e heU
  have hal := lex_upper_bound w n _ haU
  have hza := lex_upper_graph G heU (show
      layoutPos w n ((kmswStage w n).west e) ∈ (layoutArc w n e).image by
    rw [← layoutArc_start w n e he]
    exact Or.inl rfl)
  have hzb := lex_upper_graph G haU (show
      layoutPos w n ((kmswStage w n).east (kmswStage w n).active) ∈
        (layoutArc w n (kmswStage w n).active).image by
    rw [← layoutArc_finish w n _ hal]
    exact lex_finish_mem_image _)
  have hf := kmswStage_succ_lex_fresh w n hc e es hUL
  obtain ⟨hp, hq⟩ := layoutPos_succ_lex_chord_endpoints w n hc e es hUL
  have hab : (layoutPos w n ((kmswStage w n).west e)).re <
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    rw [← hp, ← hq]
    change (kmswStageRank w (n + 1) _ : ℝ) < (kmswStageRank w (n + 1) _ : ℝ)
    exact_mod_cast kmswStageRank_strict w (n + 1) _ (Finset.mem_Ico.mp hf).2
  have hh := freshEdges_endpoint_heights w n _ hf
  have hfit := freshEdges_ramp_widths_lt w n _ hf
  rw [hp, hq] at hh hfit
  exact ⟨hab, ⟨hza.1, hza.2.1⟩, ⟨hzb.1, hzb.2.1⟩,
    (roofHeight_start (rampSlope_pos w n) hh.1 hh.2 hfit).trans hza.2.2,
    (roofHeight_finish (rampSlope_pos w n) hh.1 hh.2 hfit).trans hzb.2.2⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def lexSplicedUpper (w : ℕ → Fin 3) (n e : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : ℝ → ℝ :=
  let a := layoutPos w n ((kmswStage w n).west e)
  let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  spliceFn G.upper (roofHeight a b (n + 1) (rampSlope w n)) a.re b.re

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_upper_continuous (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ContinuousOn (lexSplicedUpper w n e G) (Icc G.xmin G.xmax) := by
  obtain ⟨hab, _, _, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  exact continuousOn_spliceFn hab.le G.upper_continuous
    (continuous_roofHeight _ _ _ _).continuousOn ha hb

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_lower_le_upper (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ x ∈ Icc G.xmin G.xmax, G.lower x ≤ lexSplicedUpper w n e G x := by
  obtain ⟨_, _, _, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  exact lower_le_spliceFn G.lower_le_upper ha hb
    (invariant_succ_lex_chord_roof_gap w n hc e es hUL G)

private theorem lex_edge_graph {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {f : ℕ}
    (hf : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    graphOver (layoutPos w n ((kmswStage w n).west f)).re
      (layoutPos w n ((kmswStage w n).east f)).re G.upper = stageEdgeTrace P f := by
  have hfb := lex_upper_bound w n f hf
  rw [lex_trace_layout G hfb]
  obtain ⟨g, hg⟩ := layoutArc_image_graph w n f hfb
  rw [hg]
  ext z
  constructor
  · intro hz
    have hz' : (⟨z.re, g z.re⟩ : ℂ) ∈ (layoutArc w n f).image :=
      hg.symm ▸ ⟨hz.1, hz.2.1, rfl⟩
    exact ⟨hz.1, hz.2.1, hz.2.2.trans (G.upper_eq_arc_height hf hz')⟩
  · intro hz
    exact ⟨hz.1, hz.2.1, (lex_upper_graph G hf (hg.symm ▸ hz)).2.2⟩

private theorem lex_adjacent (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).east e = (kmswStage w n).west (kmswStage w n).active := by
  have hc := kmswStage_upper_chain w n
  rw [lex_old_UL w n e es hUL, List.append_assoc] at hc
  exact (List.isChain_append_cons_cons.mp hc).2.1

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_cap_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    graphOver (layoutPos w n ((kmswStage w n).west e)).re
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re G.upper =
      stageEdgeTrace P e ∪ stageEdgeTrace P (kmswStage w n).active := by
  have hULold := lex_old_UL w n e es hUL
  have heU : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have haU : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have he := lex_upper_bound w n e heU
  have hal := lex_upper_bound w n _ haU
  have hx1 : (layoutPos w n ((kmswStage w n).west e)).re <
      (layoutPos w n ((kmswStage w n).east e)).re := by
    change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
    exact_mod_cast kmswStageRank_strict w n e he
  have hx2 : (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re <
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ hal
  rw [← lex_edge_graph G heU, ← lex_edge_graph G haU]
  have hadj := congrArg (fun v => (layoutPos w n v).re) (lex_adjacent w n e es hUL)
  ext z
  change (_ ≤ z.re ∧ z.re ≤ _ ∧ z.im = G.upper z.re) ↔
    (_ ≤ z.re ∧ z.re ≤ _ ∧ z.im = G.upper z.re) ∨
    (_ ≤ z.re ∧ z.re ≤ _ ∧ z.im = G.upper z.re)
  constructor
  · intro hz
    rcases le_total z.re (layoutPos w n ((kmswStage w n).east e)).re with hle | hle
    · exact Or.inl ⟨hz.1, hle, hz.2.2⟩
    · exact Or.inr ⟨by linarith only [hle, hadj], hz.2.1, hz.2.2⟩
  · rintro (hz | hz)
    · exact ⟨hz.1, by linarith only [hz.2.1, hx2, hadj], hz.2.2⟩
    · exact ⟨by linarith only [hz.1, hx1, hadj], hz.2.1, hz.2.2⟩

private theorem lex_roof_abs_sub_le {a b : ℂ} {H M : ℝ} (hM : 0 ≤ M) (x y : ℝ) :
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

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_upper_lipschitz_margin (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ L : ℝ, 0 ≤ L ∧ L < rampSlope w (n + 1) ∧
      ∀ x ∈ Icc G.xmin G.xmax, ∀ y ∈ Icc G.xmin G.xmax,
        |lexSplicedUpper w n e G x - lexSplicedUpper w n e G y| ≤ L * |x - y| := by
  obtain ⟨hab, haI, hbI, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  refine ⟨rampSlope w n, (rampSlope_pos w n).le,
    rampSlope_lt w (Nat.lt_succ_self n), ?_⟩
  apply abs_spliceFn_sub_le haI.1 hab.le hbI.2 ha hb
  · intro x hx y hy
    exact (hLip x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLM.le (abs_nonneg (x - y)))
  · intro x _ y _
    exact lex_roof_abs_sub_le (rampSlope_pos w n).le x y

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def lexSpliceCap (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : GraphCap := by
  let a := layoutPos w n ((kmswStage w n).west e)
  let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let g := roofHeight a b (n + 1) (rampSlope w n)
  obtain ⟨hab, haI, hbI, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  exact spliceCap G.upper g hab (G.upper_continuous.mono
    (fun _ hx => ⟨haI.1.trans hx.1, hx.2.trans hbI.2⟩))
    (continuous_roofHeight _ _ _ _).continuousOn
    (invariant_succ_lex_chord_roof_gap w n hc e es hUL G) ha hb

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_region_eq (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    closedGraphRegion G.xmin G.xmax G.lower (lexSplicedUpper w n e G) =
      closedGraphRegion G.xmin G.xmax G.lower G.upper ∪
        closure (lexSpliceCap w n hc e es hUL G).region := by
  obtain ⟨hab, haI, hbI, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  exact closedGraphRegion_spliceFn_eq_union_closure haI.1 hab hbI.2
    G.upper_continuous (continuous_roofHeight _ _ _ _).continuousOn
    G.lower_le_upper ha hb (invariant_succ_lex_chord_roof_gap w n hc e es hUL G)

private theorem lex_chain_order (W E : ℕ → ℝ) (l : List ℕ)
    (hc : l.IsChain (fun e f => E e = W f)) (hinc : ∀ e ∈ l, W e < E e) :
    l.Pairwise (fun e f => E e ≤ W f) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a tail ih =>
    cases tail with
    | nil => simp
    | cons b bs =>
      have ht := ih hc.tail (fun e he => hinc e (by simp [he]))
      have hab : E a = W b := hc.rel_head? (by simp)
      apply List.pairwise_cons.mpr
      refine ⟨?_, ht⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hab.le
      · exact hab.le.trans ((hinc b (by simp)).le.trans
          ((List.pairwise_cons.mp ht).1 f hf))

private theorem lex_outside_bounds (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (∀ f ∈ es.reverse, (layoutPos w n ((kmswStage w n).east f)).re ≤
      (layoutPos w n ((kmswStage w n).west e)).re) ∧
    (∀ f ∈ (kmswStage w n).UR,
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re ≤
        (layoutPos w n ((kmswStage w n).west f)).re) := by
  have hp := lex_chain_order
    (fun f => (layoutPos w n ((kmswStage w n).west f)).re)
    (fun f => (layoutPos w n ((kmswStage w n).east f)).re)
    ((kmswStage w n).UL ++ (kmswStage w n).UR)
    ((kmswStage_upper_chain w n).imp (fun _ _ hh =>
      congrArg (fun v => (layoutPos w n v).re) hh)) (by
        intro f hf
        change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
        exact_mod_cast kmswStageRank_strict w n f (lex_upper_bound w n f hf))
  rw [lex_old_UL w n e es hUL] at hp
  constructor
  · intro f hf
    rw [List.append_assoc] at hp
    exact (List.pairwise_append.mp hp).2.2 f hf e (by simp)
  · intro f hf
    exact (List.pairwise_append.mp hp).2.2 (kmswStage w n).active (by simp) f hf

private theorem lex_trace_bounds {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {f : ℕ} (hf : f < (kmswStage w n).nextEdge)
    {z : ℂ} (hz : z ∈ stageEdgeTrace P f) :
    (layoutPos w n ((kmswStage w n).west f)).re ≤ z.re ∧
      z.re ≤ (layoutPos w n ((kmswStage w n).east f)).re := by
  rw [lex_trace_layout G hf] at hz
  obtain ⟨g, hg⟩ := layoutArc_image_graph w n f hf
  rw [hg] at hz
  exact ⟨hz.1, hz.2.1⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_cap_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (h : LayoutGood w (n + 1)) :
    graphOver (layoutPos w n ((kmswStage w n).west e)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
      (roofHeight (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n)) =
      stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge := by
  have hf := (Finset.mem_Ico.mp (kmswStage_succ_lex_fresh w n hc e es hUL)).2
  simp only [stageEdgeTrace, hf, ↓reduceDIte]
  change _ = (layoutArc w (n + 1) (kmswStage w n).nextEdge).image
  rw [layoutArc_succ_lex_chord_image w n hc e es hUL]
  obtain ⟨hp, hq⟩ := layoutPos_succ_lex_chord_endpoints w n hc e es hUL
  rw [hp, hq]
  rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    graphOver G.xmin G.xmax (lexSplicedUpper w n e G) =
      ⋃ f ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR,
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
  let a := layoutPos w n ((kmswStage w n).west e)
  let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  obtain ⟨hab, haI, hbI, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  change graphOver G.xmin G.xmax (spliceFn G.upper
    (roofHeight a b (n + 1) (rampSlope w n)) a.re b.re) = _
  rw [graphOver_spliceFn haI.1 hbI.2 ha hb,
    invariant_succ_lex_cap_upper_trace w n hc e es hUL h]
  obtain ⟨_, _, hULnew, hURnew, _, _⟩ :=
    invariant_succ_lex_stage_lists w n hc e es hUL
  rw [hULnew, hURnew]
  have hULold := lex_old_UL w n e es hUL
  have hout := lex_outside_bounds w n e es hUL
  have hbnd : ∀ f ∈ es.reverse ++ (kmswStage w n).UR,
      f < (kmswStage w n).nextEdge := by
    intro f hf
    apply lex_upper_bound w n f
    simp only [hULold, List.mem_append, List.mem_cons] at hf ⊢
    tauto
  have hkeep : ∀ f ∈ es.reverse ++ (kmswStage w n).UR,
      stageEdgeTrace P f ⊆ graphOver G.xmin G.xmax G.upper ∩
        {z | z.re ∉ Ioo a.re b.re} := by
    intro f hf z hz
    have hfold : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
      simp only [hULold, List.mem_append, List.mem_cons] at hf ⊢
      tauto
    have hx := lex_trace_bounds G (hbnd f hf) hz
    refine ⟨lex_upper_graph G hfold ((lex_trace_layout G (hbnd f hf)) ▸ hz), ?_⟩
    rintro ⟨hax, hxb⟩
    rcases List.mem_append.mp hf with hpre | hpost
    · exact (not_lt_of_ge (hx.2.trans (hout.1 f hpre))) hax
    · exact (not_lt_of_ge ((hout.2 f hpost).trans hx.1)) hxb
  ext z
  simp only [mem_union, mem_iUnion, List.mem_append, List.mem_singleton]
  constructor
  · rintro (hz | hz)
    · have hzold := hz.1
      rw [G.upper_trace] at hzold
      obtain ⟨f, hfz⟩ := mem_iUnion.mp hzold
      obtain ⟨hf, hzf⟩ := mem_iUnion.mp hfz
      have hf' := hf
      simp only [hULold, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf'
      rcases hf' with (hpre | heq | heq) | hpost
      · exact ⟨f, Or.inl (Or.inl hpre),
          (stageEdgeTrace_succ_lex_old w n f G h (hbnd f (by simp [hpre]))).symm ▸ hzf⟩
      · subst f
        have hx := lex_trace_bounds G (lex_upper_bound w n e hf) hzf
        have hxe : z.re = a.re := by
          by_contra hne
          have hax : a.re < z.re := lt_of_le_of_ne hx.1 (Ne.symm hne)
          have heab : (layoutPos w n ((kmswStage w n).east e)).re < b.re := by
            rw [lex_adjacent w n e es hUL]
            change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
            exact_mod_cast kmswStageRank_strict w n _ (act_lt_nextEdge w (le_refl n))
          exact hz.2 ⟨hax, hx.2.trans_lt heab⟩
        refine ⟨(kmswStage w n).nextEdge, Or.inl (Or.inr rfl), ?_⟩
        rw [← invariant_succ_lex_cap_upper_trace w n hc e es hUL h]
        exact ⟨hxe.ge, hxe.le.trans hab.le, hz.1.2.2.trans (by rw [hxe]; exact ha.symm)⟩
      · subst f
        have hx := lex_trace_bounds G (act_lt_nextEdge w (le_refl n)) hzf
        have hxe : z.re = b.re := by
          by_contra hne
          have hxb : z.re < b.re := lt_of_le_of_ne hx.2 hne
          have haab : a.re <
              (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re := by
            rw [← lex_adjacent w n e es hUL]
            change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
            exact_mod_cast kmswStageRank_strict w n e (lex_upper_bound w n e (by
              simp [hULold]))
          exact hz.2 ⟨haab.trans_le hx.1, hxb⟩
        refine ⟨(kmswStage w n).nextEdge, Or.inl (Or.inr rfl), ?_⟩
        rw [← invariant_succ_lex_cap_upper_trace w n hc e es hUL h]
        exact ⟨hab.le.trans hxe.ge, hxe.le,
          hz.1.2.2.trans (by rw [hxe]; exact hb.symm)⟩
      · exact ⟨f, Or.inr hpost,
          (stageEdgeTrace_succ_lex_old w n f G h (hbnd f (by simp [hpost]))).symm ▸ hzf⟩
    · exact ⟨(kmswStage w n).nextEdge, Or.inl (Or.inr rfl), hz⟩
  · rintro ⟨f, ((hpre | rfl) | hpost), hz⟩
    · left
      exact hkeep f (by simp [hpre])
        ((stageEdgeTrace_succ_lex_old w n f G h (hbnd f (by simp [hpre]))) ▸ hz)
    · exact Or.inr hz
    · left
      exact hkeep f (by simp [hpost])
        ((stageEdgeTrace_succ_lex_old w n f G h (hbnd f (by simp [hpost]))) ▸ hz)

private theorem lex_old_arc (w : ℕ → Fin 3) (n f : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (hf : f < (kmswStage w n).nextEdge)
    (hf' : f < (kmswStage w (n + 1)).nextEdge) (b : Bool) :
    (monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf'⟩, b) =
      P.arc (⟨f, hf⟩, b) := by
  rw [G.arc_layout]
  change (if b then (layoutArc w (n + 1) f).reverse else layoutArc w (n + 1) f) = _
  rw [layoutArc_old w n f hf]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_image_eq (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image =
      P.image ∪ stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
        (kmswStage w n).nextEdge := by
  obtain ⟨hE, hV⟩ := kmswStage_succ_lex_allocation w n hc e es hUL
  have hnew : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by omega
  have hchord : stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
      (kmswStage w n).nextEdge = (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
    simp only [stageEdgeTrace, hnew, ↓reduceDIte]
    rfl
  rw [hchord]
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hz⟩)
    · left
      let v' : Fin (kmswStage w n).nextVertex := ⟨v.val, by have hh := v.isLt; omega⟩
      refine Or.inl ⟨v', ?_⟩
      rw [G.pos_layout]
      exact (layoutPos_old_vertex w n v.val v'.isLt).symm
    · by_cases ho : d.1.val < (kmswStage w n).nextEdge
      · left
        exact Or.inr ⟨(⟨d.1.val, ho⟩, d.2),
          (lex_old_arc w n d.1.val G h ho d.1.isLt d.2) ▸ hz⟩
      · right
        have hid : d.1.val = (kmswStage w n).nextEdge := by have hh := d.1.isLt; omega
        change z ∈ (if d.2 then (layoutArc w (n + 1) d.1.val).reverse
          else layoutArc w (n + 1) d.1.val).image at hz
        rw [hid] at hz
        cases hb : d.2
        · simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hz
        · exact lex_reverse_image_subset _ (by simpa only [hb, ↓reduceIte] using hz)
  · rintro (hz | hz)
    · rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
      · refine Or.inl ⟨stageVertexIncl w n v, ?_⟩
        rw [G.pos_layout]
        exact layoutPos_old_vertex w n v.val v.isLt
      · have hd : d.1.val < (kmswStage w (n + 1)).nextEdge := by
          have hh := d.1.isLt
          omega
        exact Or.inr ⟨(⟨d.1.val, hd⟩, d.2),
          (lex_old_arc w n d.1.val G h d.1.isLt hd d.2).symm ▸ hz⟩
    · exact Or.inr ⟨(⟨(kmswStage w n).nextEdge, hnew⟩, false), hz⟩

private theorem lex_old_cap_subset {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length) :
    (G.cap i).region ⊆ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
  intro z hz
  rw [← G.cover]
  exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)

private theorem lex_old_cap_below {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    {z : ℂ} (hz : z ∈ (G.cap i).region) : z.im < G.upper z.re := by
  have hb := lex_old_cap_subset G i hz
  apply lt_of_le_of_ne hb.2.2.2
  intro heq
  have hzgraph : z ∈ graphOver G.xmin G.xmax G.upper := ⟨hb.1, hb.2.1, heq⟩
  rw [G.upper_trace] at hzgraph
  obtain ⟨f, hfz⟩ := mem_iUnion.mp hzgraph
  obtain ⟨hf, hzf⟩ := mem_iUnion.mp hfz
  have hfb := lex_upper_bound w n f hf
  have hzP : z ∈ P.image := Or.inr ⟨(⟨f, hfb⟩, false), by
    simpa only [stageEdgeTrace, hfb, ↓reduceDIte] using hzf⟩
  exact Set.disjoint_left.mp (G.cap_avoid i) hz hzP

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_new_cap_avoid (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    Disjoint (lexSpliceCap w n hc e es hUL G).region
      (monotoneLayoutDrawing w (n + 1) h).image := by
  rw [invariant_succ_lex_image_eq w n hc e es hUL G h]
  apply Set.disjoint_left.mpr
  intro z hz hzP
  change _ < z.re ∧ z.re < _ ∧ G.upper z.re < z.im ∧ z.im < _ at hz
  rcases hzP with hzP | hzP
  · exact (not_lt_of_ge (G.image_bounds hzP).2.2.2) hz.2.2.1
  · rw [← invariant_succ_lex_cap_upper_trace w n hc e es hUL h] at hzP
    exact (ne_of_lt hz.2.2.2) hzP.2.2

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_old_cap_avoid (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (G.cap i).region (monotoneLayoutDrawing w (n + 1) h).image := by
  obtain ⟨_, _, _, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
  rw [invariant_succ_lex_image_eq w n hc e es hUL G h]
  apply Set.disjoint_left.mpr
  intro z hz hzP
  rcases hzP with hzP | hzP
  · exact Set.disjoint_left.mp (G.cap_avoid i) hz hzP
  · rw [← invariant_succ_lex_cap_upper_trace w n hc e es hUL h] at hzP
    have hgap := le_spliceFn ha hb (invariant_succ_lex_chord_roof_gap w n hc e es hUL G)
      z.re
    rw [spliceFn_of_mem ⟨hzP.1, hzP.2.1⟩] at hgap
    exact (not_le_of_gt (lex_old_cap_below G i hz)) (hzP.2.2 ▸ hgap)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_new_cap_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (lexSpliceCap w n hc e es hUL G).region (G.cap i).region := by
  apply Set.disjoint_left.mpr
  intro z hz hzi
  exact (not_lt_of_ge (lex_old_cap_subset G i hzi).2.2.2) hz.2.2.1

private theorem lex_initial_ray (p : Polyline) (hlen : 2 ≤ p.points.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  refine Or.inr ⟨0, by omega, ?_⟩
  change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
  rw [Polyline.point_zero_eq_start]
  have hz : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  rw [hz]
  exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩

private theorem lex_forward_line (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hd : 0 < p.initialDirection.re) (f : ℝ → ℝ)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∀ x ∈ Icc p.start.re (p.start.re + p.initialDirection.re),
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) *
        (x - p.start.re) := by
  intro x hx
  have ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
      (div_le_one hd).mpr (by linarith only [hx.2])⟩
  have hg := hgraph _ (lex_initial_ray p hlen ht)
  have hx' : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [div_mul_cancel₀ _ hd.ne']
    ring
  rw [hx'] at hg
  simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hg

private theorem lex_backward_line (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hd : p.initialDirection.re < 0) (f : ℝ → ℝ)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∀ x ∈ Icc (p.start.re + p.initialDirection.re) p.start.re,
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) *
        (x - p.start.re) := by
  intro x hx
  have ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) hd.le,
      (div_le_one_of_neg hd).mpr (by linarith only [hx.1])⟩
  have hg := hgraph _ (lex_initial_ray p hlen ht)
  have hx' : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [div_mul_cancel₀ _ hd.ne]
    ring
  rw [hx'] at hg
  simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hg

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_ext_upper_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (f : ℕ)
    (hf : f < (kmswStage w (n + 1)).nextEdge)
    (hmem : f ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, false)).initialDirection
      (closedGraphRegion G.xmin G.xmax G.lower (lexSplicedUpper w n e G))ᶜ := by
  let p := layoutArc w (n + 1) f
  have hd : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos
    (layoutArc_points_pairwise w (n + 1) f hf) (layoutArc_length_two_le w (n + 1) f)
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection _
  apply wedgeIn_compl_closedGraphRegion_east_upper p.start p.initialDirection
    p.initialDirection.re hd hd
  apply lex_forward_line p (layoutArc_length_two_le w (n + 1) f) hd
  intro z hz
  have hzgraph : z ∈ graphOver G.xmin G.xmax (lexSplicedUpper w n e G) := by
    rw [invariant_succ_lex_upper_trace w n hc e es hUL G h]
    exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hmem, by
      simp only [stageEdgeTrace, hf, ↓reduceDIte]
      exact hz⟩⟩
  exact hzgraph.2.2.symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_ext_lower_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (f : ℕ)
    (hf : f < (kmswStage w (n + 1)).nextEdge)
    (hmem : f ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, true)).initialDirection
      (closedGraphRegion G.xmin G.xmax G.lower (lexSplicedUpper w n e G))ᶜ := by
  let p := (layoutArc w (n + 1) f).reverse
  have hd : p.initialDirection.re < 0 := Polyline.reverse_initialDirection_re_neg
    (layoutArc_points_pairwise w (n + 1) f hf) (layoutArc_length_two_le w (n + 1) f)
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection _
  apply wedgeIn_compl_closedGraphRegion_west_lower p.start p.initialDirection
    (-p.initialDirection.re) hd (neg_pos.mpr hd)
  have hline := lex_backward_line p (by
    simpa only [p, Polyline.reverse, List.length_reverse] using
      layoutArc_length_two_le w (n + 1) f) hd G.lower (by
        intro z hz
        have hzgraph : z ∈ graphOver G.xmin G.xmax G.lower := by
          rw [invariant_succ_lex_lower_trace w n hc e es hUL G h]
          exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hmem, by
            simp only [stageEdgeTrace, hf, ↓reduceDIte]
            exact lex_reverse_image_subset (layoutArc w (n + 1) f) hz⟩⟩
        exact hzgraph.2.2.symm)
  simpa only [sub_neg_eq_add] using hline

private theorem lex_first_re_le_finish (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.start.re + p.initialDirection.re ≤ p.finish.re := by
  have hi := Polyline.point_re_le_of_le hp
    (show 1 ≤ p.points.length - 1 by omega) (show p.points.length - 1 < p.points.length by
      omega)
  rw [Polyline.point_last_eq_finish] at hi
  simpa only [Polyline.initialDirection, Complex.sub_re, add_sub_cancel] using hi

private theorem lex_chord_graph (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    ∀ z ∈ (layoutArc w (n + 1) (kmswStage w n).nextEdge).image,
      roofHeight (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) z.re = z.im := by
  intro z hz
  rw [layoutArc_succ_lex_chord_image w n hc e es hUL] at hz
  obtain ⟨hp, hq⟩ := layoutPos_succ_lex_chord_endpoints w n hc e es hUL
  rw [hp, hq] at hz
  exact hz.2.2.symm

private theorem lex_chord_old_roof (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    layoutArc w (n + 1) (kmswStage w n).nextEdge =
      roofArc (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) := by
  rw [layoutArc_succ_lex_chord w n hc e es hUL]
  obtain ⟨hp, hq⟩ := layoutPos_succ_lex_chord_endpoints w n hc e es hUL
  rw [hp, hq]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_new_cap_lower_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (f : ℕ)
    (hf : f < (kmswStage w (n + 1)).nextEdge)
    (hmem : f ∈ [e, (kmswStage w n).active]) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨f, hf⟩, false)).initialDirection
      (lexSpliceCap w n hc e es hUL G).region := by
  let a := layoutPos w n ((kmswStage w n).west e)
  let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let g := roofHeight a b (n + 1) (rampSlope w n)
  have hULold := lex_old_UL w n e es hUL
  have heU : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have halU : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have he := lex_upper_bound w n e heU
  have hal := act_lt_nextEdge w (le_refl n)
  have hfU : f ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact heU
    · exact halU
  have hfo := lex_upper_bound w n f hfU
  rw [lex_old_arc w n f G h hfo hf false, G.arc_layout]
  let p := layoutArc w n f
  have hpLen := layoutArc_length_two_le w n f
  have hpMono := layoutArc_points_pairwise w n f hfo
  have hd : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos hpMono hpLen
  have hline := lex_forward_line p hpLen hd G.upper (fun z hz =>
    G.upper_eq_arc_height hfU hz)
  have hpf : p.start.re + p.initialDirection.re ≤
      (layoutPos w n ((kmswStage w n).east f)).re := by
    rw [← layoutArc_finish w n f hfo]
    exact lex_first_re_le_finish p hpMono hpLen
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection
    (graphRegion a.re b.re G.upper g)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hfe | hfa
  · subst f
    have hps : p.start = a := layoutArc_start w n e he
    let q := layoutArc w (n + 1) (kmswStage w n).nextEdge
    have hqB := (Finset.mem_Ico.mp (kmswStage_succ_lex_fresh w n hc e es hUL)).2
    have hqLen := layoutArc_length_two_le w (n + 1) (kmswStage w n).nextEdge
    have hqMono := layoutArc_points_pairwise w (n + 1) (kmswStage w n).nextEdge hqB
    have hqd : 0 < q.initialDirection.re := Polyline.initialDirection_re_pos hqMono hqLen
    have hqs : q.start = a := by
      dsimp only [q]
      rw [lex_chord_old_roof w n hc e es hUL]
      exact roofArc_start _ _ _ _
    have hqf : q.finish = b := by
      dsimp only [q]
      rw [lex_chord_old_roof w n hc e es hUL]
      exact roofArc_finish _ _ _ _
    have hqline := lex_forward_line q hqLen hqd g (lex_chord_graph w n hc e es hUL)
    have haH : a.im < (n + 1 : ℝ) := by
      have haV := (kmswStage_endpoints_lt_nextVertex w n e he).1
      have hh := layoutHeight_le w n _ haV
      change (layoutHeight w n _ : ℝ) < _
      exact lt_of_le_of_lt (by exact_mod_cast hh) (by norm_num)
    have hqslope : q.initialDirection.im / q.initialDirection.re = rampSlope w n := by
      dsimp only [q]
      rw [lex_chord_old_roof w n hc e es hUL]
      exact roofArc_initialSlope (rampSlope_pos w n) haH
    let η := min p.initialDirection.re q.initialDirection.re
    have hη : 0 < η := lt_min hd hqd
    have hηp : η ≤ p.initialDirection.re := min_le_left _ _
    have hηq : η ≤ q.initialDirection.re := min_le_right _ _
    have hηb : p.start.re + η ≤ b.re := by
      have hh := lex_first_re_le_finish q hqMono hqLen
      rw [hqs, hqf] at hh
      rw [hps]
      linarith only [hηq, hh]
    apply wedgeIn_graphRegion_east_lower_slope p.start p.initialDirection η
      (rampSlope w n) hd (by rw [hps]) hη hηb
    · intro x hx
      exact hline x ⟨hx.1, by linarith only [hx.2, hηp]⟩
    · exact (le_abs_self _).trans_lt (layoutArc_initial_slope_abs_lt w n e he)
    · intro x hx
      have hxq : x ∈ Icc q.start.re (q.start.re + q.initialDirection.re) := by
        rw [hps] at hx
        rw [hqs]
        exact ⟨hx.1, by linarith only [hx.2, hηq]⟩
      rw [hqline x hxq, hqs, hqslope, hps]
  · subst f
    have hps : p.start = layoutPos w n ((kmswStage w n).west (kmswStage w n).active) :=
      layoutArc_start w n _ hal
    have hpI : p.start.re ∈ Ioo a.re b.re := by
      rw [hps]
      constructor
      · change a.re < _
        rw [← lex_adjacent w n e es hUL]
        change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
        exact_mod_cast kmswStageRank_strict w n e he
      · change (kmswStageRank w n _ : ℝ) < (kmswStageRank w n _ : ℝ)
        exact_mod_cast kmswStageRank_strict w n _ hal
    have hpgraph : G.upper p.start.re = p.start.im :=
      G.upper_eq_arc_height halU (Or.inl rfl)
    have hgap : p.start.im < g p.start.re := by
      rw [← hpgraph]
      exact invariant_succ_lex_chord_roof_gap w n hc e es hUL G _ hpI
    exact wedgeIn_graphRegion_east_lower_continuous p.start p.initialDirection
      p.initialDirection.re hd hpI.1.le hd hpf hline
      (continuous_roofHeight _ _ _ _).continuousAt hgap

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_lex_new_cap_upper_wedge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1))
    (hf : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge) :
    WedgeIn
      ((monotoneLayoutDrawing w (n + 1) h).arc
        (⟨(kmswStage w n).nextEdge, hf⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc
        (⟨(kmswStage w n).nextEdge, hf⟩, true)).initialDirection
      (lexSpliceCap w n hc e es hUL G).region := by
  let a := layoutPos w n ((kmswStage w n).west e)
  let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let g := roofHeight a b (n + 1) (rampSlope w n)
  let p := (layoutArc w (n + 1) (kmswStage w n).nextEdge).reverse
  have hpLen : 2 ≤ p.points.length := by
    simpa only [p, Polyline.reverse, List.length_reverse] using
      layoutArc_length_two_le w (n + 1) (kmswStage w n).nextEdge
  have hd : p.initialDirection.re < 0 := Polyline.reverse_initialDirection_re_neg
    (layoutArc_points_pairwise w (n + 1) _ hf) (layoutArc_length_two_le w (n + 1) _)
  have hps : p.start = b := by
    rw [Polyline.start_reverse, lex_chord_old_roof w n hc e es hUL]
    exact roofArc_finish _ _ _ _
  have hline := lex_backward_line p hpLen hd g (fun z hz =>
    lex_chord_graph w n hc e es hUL z (lex_reverse_image_subset _ hz))
  obtain ⟨hab, haI, hbI, _, _⟩ := lex_chord_geometry w n hc e es hUL G
  have hpI : a.re ≤ p.start.re + p.initialDirection.re := by
    have hz := lex_initial_ray p hpLen (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    have hz' := lex_reverse_image_subset _ hz
    rw [layoutArc_succ_lex_chord_image w n hc e es hUL] at hz'
    obtain ⟨hp, hq⟩ := layoutPos_succ_lex_chord_endpoints w n hc e es hUL
    rw [hp, hq] at hz'
    simpa only [one_smul, Complex.add_re] using hz'.1
  have hbgraph : G.upper b.re = b.im := by
    have hu := lex_old_UL w n e es hUL
    have hbU : (kmswStage w n).active ∈
        (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hu]
    exact G.upper_eq_arc_height hbU (by
      dsimp only [b]
      rw [← layoutArc_finish w n (kmswStage w n).active
        (act_lt_nextEdge w (le_refl n))]
      exact lex_finish_mem_image _)
  have hbH : b.im < (n + 1 : ℝ) := by
    have hh := G.upper_le_stage hbI
    rw [hbgraph] at hh
    linarith only [hh]
  have hslope : p.initialDirection.im / p.initialDirection.re = -rampSlope w n := by
    dsimp only [p]
    rw [lex_chord_old_roof w n hc e es hUL]
    exact roofArc_reverse_initialSlope (rampSlope_pos w n) hbH
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  change DirectedDistances.PlanarMap.WedgeIn p.start p.initialDirection
    (graphRegion a.re b.re G.upper g)
  apply wedgeIn_graphRegion_west_upper_slope p.start p.initialDirection
    (-p.initialDirection.re) (-L) hd (by rw [hps]) (neg_pos.mpr hd)
    (by simpa only [sub_neg_eq_add] using hpI)
  · simpa only [sub_neg_eq_add] using hline
  · rw [hslope]
    linarith only [hLM]
  · intro x hx
    have hxI : x ∈ Icc G.xmin G.xmax := by
      rw [sub_neg_eq_add] at hx
      exact ⟨haI.1.trans (hpI.trans hx.1), hx.2.trans (by simpa only [hps] using hbI.2)⟩
    have hh := (le_abs_self (G.upper x - G.upper b.re)).trans (hLip x hxI b.re hbI)
    rw [hbgraph, abs_of_nonpos (by simpa only [hps] using sub_nonpos.mpr hx.2)] at hh
    rw [hps]
    linarith only [hh]

private theorem lex_cap_edge_bound {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    (f : ℕ) (hf : f ∈ G.capLower i ++ G.capUpper i) :
    f < (kmswStage w n).nextEdge := by
  have ht := triBound_stage w n ((kmswStage w n).triangles.get i) (List.get_mem _ i)
  rcases (G.cap_edges i f).mp hf with rfl | rfl | rfl
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2

private theorem lex_trace_union (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (l : List ℕ)
    (hl : ∀ f ∈ l, f < (kmswStage w n).nextEdge) :
    (⋃ f ∈ l, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f) =
      ⋃ f ∈ l, stageEdgeTrace P f := by
  exact iUnion_congr (fun f => iUnion_congr (fun hf =>
    stageEdgeTrace_succ_lex_old w n f G h (hl f hf)))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
noncomputable def invariant_succ_lex (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h) := by
  let len := (kmswStage w n).triangles.length
  have hTri := kmswStage_succ_lex_triangles w n hc e es hUL
  have hLen : (kmswStage w (n + 1)).triangles.length = len + 1 := by
    simp only [hTri, List.length_append, List.length_singleton]
    rfl
  let C := lexSpliceCap w n hc e es hUL G
  let cap' : Fin (kmswStage w (n + 1)).triangles.length → GraphCap := fun i =>
    if hi : i.val < len then G.cap ⟨i.val, hi⟩ else C
  let capL' : Fin (kmswStage w (n + 1)).triangles.length → List ℕ := fun i =>
    if hi : i.val < len then G.capLower ⟨i.val, hi⟩ else [e, (kmswStage w n).active]
  let capU' : Fin (kmswStage w (n + 1)).triangles.length → List ℕ := fun i =>
    if hi : i.val < len then G.capUpper ⟨i.val, hi⟩ else [(kmswStage w n).nextEdge]
  let oldi : Fin len → Fin (kmswStage w (n + 1)).triangles.length :=
    fun i => ⟨i.val, by rw [hLen]; omega⟩
  let lasti : Fin (kmswStage w (n + 1)).triangles.length := ⟨len, by rw [hLen]; omega⟩
  have hLast : ¬ lasti.val < len := Nat.lt_irrefl len
  have hOld (i : Fin len) : (oldi i).val < len := i.isLt
  have hTriOld (i : Fin (kmswStage w (n + 1)).triangles.length) (hi : i.val < len) :
      (kmswStage w (n + 1)).triangles.get i =
        (kmswStage w n).triangles.get ⟨i.val, hi⟩ := by
    simp only [List.get_eq_getElem, hTri, List.getElem_append_left hi]
  have hTriNew (i : Fin (kmswStage w (n + 1)).triangles.length) (hi : ¬ i.val < len) :
      (kmswStage w (n + 1)).triangles.get i =
        ((kmswStage w n).active, (kmswStage w n).nextEdge, e) := by
    have hiv : i.val = len := by have hh := i.isLt; omega
    simp only [List.get_eq_getElem, hTri]
    rw [List.getElem_append_right (by omega : (kmswStage w n).triangles.length ≤ i.val)]
    simp only [hiv, len, Nat.sub_self, List.getElem_cons_zero]
  have hOldLower (i : Fin len) :
      graphOver (G.cap i).a (G.cap i).b (G.cap i).low =
        ⋃ f ∈ G.capLower i, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
    rw [lex_trace_union w n G h _ (fun f hf =>
      lex_cap_edge_bound G i f (List.mem_append_left _ hf))]
    exact G.cap_lower_trace i
  have hOldUpper (i : Fin len) :
      graphOver (G.cap i).a (G.cap i).b (G.cap i).high =
        ⋃ f ∈ G.capUpper i, stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
    rw [lex_trace_union w n G h _ (fun f hf =>
      lex_cap_edge_bound G i f (List.mem_append_right _ hf))]
    exact G.cap_upper_trace i
  have hULold := lex_old_UL w n e es hUL
  have heU : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by simp [hULold]
  have he := lex_upper_bound w n e heU
  have hal := act_lt_nextEdge w (le_refl n)
  have hNewLower : graphOver C.a C.b C.low =
      ⋃ f ∈ [e, (kmswStage w n).active],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
    rw [lex_trace_union w n G h _ (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact he
      · exact hal)]
    change graphOver (layoutPos w n ((kmswStage w n).west e)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re G.upper = _
    rw [invariant_succ_lex_cap_lower_trace w n e es hUL G]
    ext z
    simp
  have hNewUpper : graphOver C.a C.b C.high =
      ⋃ f ∈ [(kmswStage w n).nextEdge],
        stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) f := by
    change graphOver (layoutPos w n ((kmswStage w n).west e)).re
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
      (roofHeight (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n)) = _
    simpa using invariant_succ_lex_cap_upper_trace w n hc e es hUL h
  have hCaps : (⋃ i, closure (cap' i).region) =
      (⋃ i : Fin len, closure (G.cap i).region) ∪ closure C.region := by
    ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hz⟩
      by_cases hi : i.val < len
      · exact Or.inl ⟨⟨i.val, hi⟩, by simpa only [cap', dite_eq_left hi] using hz⟩
      · exact Or.inr (by simpa only [cap', dite_eq_right hi] using hz)
    · rintro (⟨i, hz⟩ | hz)
      · exact ⟨oldi i, by simpa only [cap', dite_eq_left (hOld i)] using hz⟩
      · exact ⟨lasti, by simpa only [cap', dite_eq_right hLast] using hz⟩
  have hChordSub : stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h)
      (kmswStage w n).nextEdge ⊆ closure C.region := by
    rw [← invariant_succ_lex_cap_upper_trace w n hc e es hUL h]
    change graphOver C.a C.b C.high ⊆ closure (graphRegion C.a C.b C.low C.high)
    rw [closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous
      C.high_continuous C.separated C.left_join C.right_join]
    intro z hz
    obtain ⟨_, _, _, ha, hb⟩ := lex_chord_geometry w n hc e es hUL G
    have hup := le_spliceFn ha hb (invariant_succ_lex_chord_roof_gap w n hc e es hUL G)
      z.re
    have hx : z.re ∈ Icc (layoutPos w n ((kmswStage w n).west e)).re
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := ⟨hz.1, hz.2.1⟩
    rw [spliceFn_of_mem hx] at hup
    exact ⟨hz.1, hz.2.1, by rw [hz.2.2]; exact hup, hz.2.2.le⟩
  obtain ⟨_, _, hULnew, hURnew, hLLnew, hLRnew⟩ :=
    invariant_succ_lex_stage_lists w n hc e es hUL
  have hKeep (f : ℕ) (hf : f ∈ es.reverse ++ (kmswStage w n).UR) :
      f ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR := by
    rw [hULnew, hURnew]
    simp only [List.mem_append, List.mem_singleton] at hf ⊢
    tauto
  have hNew : (kmswStage w n).nextEdge ∈
      (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR := by
    rw [hULnew]
    simp
  refine
    { toMonotoneStageCertificate :=
        { xmin := G.xmin
          xmax := G.xmax
          hx := G.hx
          lower := G.lower
          upper := lexSplicedUpper w n e G
          lower_continuous := G.lower_continuous
          upper_continuous := invariant_succ_lex_upper_continuous w n hc e es hUL G
          lower_le_upper := invariant_succ_lex_lower_le_upper w n hc e es hUL G
          lower_trace := invariant_succ_lex_lower_trace w n hc e es hUL G h
          upper_trace := invariant_succ_lex_upper_trace w n hc e es hUL G h
          cap := cap'
          capLower := capL'
          capUpper := capU'
          cap_lower_trace := ?_
          cap_upper_trace := ?_
          cap_edges := ?_
          cap_avoid := ?_
          cap_disjoint := ?_
          cover := ?_
          cap_lower_wedge := ?_
          cap_upper_wedge := ?_
          ext_upper_wedge := invariant_succ_lex_ext_upper_wedge w n hc e es hUL G h
          ext_lower_wedge := invariant_succ_lex_ext_lower_wedge w n hc e es hUL G h }
      cover_lower := ?_
      cover_upper := ?_
      upper_lipschitz_margin := invariant_succ_lex_upper_lipschitz_margin w n hc e es hUL G
      image_height_le := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          invariant_succ_lex_image_height_le w n hc e es hUL G h
      pos_layout := invariant_succ_lex_pos_layout w n h
      arc_layout := invariant_succ_lex_arc_layout w n h }
  · intro i
    by_cases hi : i.val < len
    · simpa only [cap', capL', dite_eq_left hi] using hOldLower ⟨i.val, hi⟩
    · simpa only [cap', capL', dite_eq_right hi] using hNewLower
  · intro i
    by_cases hi : i.val < len
    · simpa only [cap', capU', dite_eq_left hi] using hOldUpper ⟨i.val, hi⟩
    · simpa only [cap', capU', dite_eq_right hi] using hNewUpper
  · intro i f
    by_cases hi : i.val < len
    · simp only [capL', capU', dite_eq_left hi, hTriOld i hi]
      exact G.cap_edges ⟨i.val, hi⟩ f
    · simp only [capL', capU', dite_eq_right hi, hTriNew i hi, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      tauto
  · intro i
    by_cases hi : i.val < len
    · simpa only [cap', dite_eq_left hi] using
        invariant_succ_lex_old_cap_avoid w n hc e es hUL G h ⟨i.val, hi⟩
    · simpa only [cap', dite_eq_right hi] using
        invariant_succ_lex_new_cap_avoid w n hc e es hUL G h
  · intro i j hij
    by_cases hi : i.val < len
    · by_cases hj : j.val < len
      · simp only [cap', dite_eq_left hi, dite_eq_left hj]
        apply G.cap_disjoint ⟨i.val, hi⟩ ⟨j.val, hj⟩
        intro heq
        exact hij (Fin.ext (congrArg (fun k : Fin len => k.val) heq))
      · simpa only [cap', dite_eq_left hi, dite_eq_right hj] using
          (invariant_succ_lex_new_cap_disjoint w n hc e es hUL G ⟨i.val, hi⟩).symm
    · by_cases hj : j.val < len
      · simpa only [cap', dite_eq_right hi, dite_eq_left hj] using
          invariant_succ_lex_new_cap_disjoint w n hc e es hUL G ⟨j.val, hj⟩
      · exfalso
        apply hij
        apply Fin.ext
        have hiB := i.isLt
        have hjB := j.isLt
        omega
  · rw [invariant_succ_lex_image_eq w n hc e es hUL G h, hCaps,
      invariant_succ_lex_region_eq w n hc e es hUL G, ← G.cover]
    ext z
    simp only [mem_union]
    have hh := @hChordSub z
    tauto
  · intro i f hf hmem
    by_cases hi : i.val < len
    · simp only [capL', dite_eq_left hi] at hmem
      have hfo := lex_cap_edge_bound G ⟨i.val, hi⟩ f (List.mem_append_left _ hmem)
      simpa only [cap', dite_eq_left hi, lex_old_arc w n f G h hfo hf false] using
        G.cap_lower_wedge ⟨i.val, hi⟩ f hfo hmem
    · simp only [capL', dite_eq_right hi] at hmem
      simpa only [cap', dite_eq_right hi] using
        invariant_succ_lex_new_cap_lower_wedge w n hc e es hUL G h f hf hmem
  · intro i f hf hmem
    by_cases hi : i.val < len
    · simp only [capU', dite_eq_left hi] at hmem
      have hfo := lex_cap_edge_bound G ⟨i.val, hi⟩ f (List.mem_append_right _ hmem)
      simpa only [cap', dite_eq_left hi, lex_old_arc w n f G h hfo hf true] using
        G.cap_upper_wedge ⟨i.val, hi⟩ f hfo hmem
    · simp only [capU', dite_eq_right hi, List.mem_singleton] at hmem
      subst f
      simpa only [cap', dite_eq_right hi] using
        invariant_succ_lex_new_cap_upper_wedge w n hc e es hUL G h hf
  · intro f
    by_cases ho : f.val < (kmswStage w n).nextEdge
    · rcases G.cover_lower ⟨f.val, ho⟩ with hboundary | ⟨i, hcap⟩
      · simp only [hULold, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hboundary
        rcases hboundary with (hpre | hfe | hfa) | hpost
        · exact Or.inl (hKeep f.val (List.mem_append_left _ hpre))
        · exact Or.inr ⟨lasti, by simp only [capL', dite_eq_right hLast]; simp [hfe]⟩
        · exact Or.inr ⟨lasti, by simp only [capL', dite_eq_right hLast]; simp [hfa]⟩
        · exact Or.inl (hKeep f.val (List.mem_append_right _ hpost))
      · exact Or.inr ⟨oldi i, by simpa only [capL', dite_eq_left (hOld i)] using hcap⟩
    · have halloc := (kmswStage_succ_lex_allocation w n hc e es hUL).1
      have hid : f.val = (kmswStage w n).nextEdge := by have hh := f.isLt; omega
      exact Or.inl (hid.symm ▸ hNew)
  · intro f
    by_cases ho : f.val < (kmswStage w n).nextEdge
    · rcases G.cover_upper ⟨f.val, ho⟩ with hboundary | ⟨i, hcap⟩
      · left
        simpa only [hLLnew, hLRnew] using hboundary
      · exact Or.inr ⟨oldi i, by simpa only [capU', dite_eq_left (hOld i)] using hcap⟩
    · have halloc := (kmswStage_succ_lex_allocation w n hc e es hUL).1
      have hid : f.val = (kmswStage w n).nextEdge := by have hh := f.isLt; omega
      exact Or.inr ⟨lasti, by simp only [capU', dite_eq_right hLast, List.mem_singleton]; exact hid⟩

end DirectedDistances.KMSW
