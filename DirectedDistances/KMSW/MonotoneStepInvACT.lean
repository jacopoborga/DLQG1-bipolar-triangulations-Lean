module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing






public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Set



theorem kmswStage_succ_act_nextEdge (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge := by
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem kmswStage_succ_act_nextVertex (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex := by
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem kmswStage_succ_act_triangles (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).triangles = (kmswStage w n).triangles := by
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem kmswStage_succ_act_lowerLists (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).LL = (kmswStage w n).LL ∧
      (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem kmswStage_succ_act_upperUnion (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR =
      (kmswStage w n).UL ++ (kmswStage w n).UR := by
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem stageRot_succ_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    StageRotation.resize (kmswStage_succ_act_nextEdge w n e es hc hr)
      (stageRot w (n + 1)) = stageRot w n := by
  rw [stageRot_succ]
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  exact StageRotation.step_activation (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) hcode e es hr



theorem layoutDart_succ_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    layoutDart w (n + 1) d =
      layoutDart w n (d.1.cast (kmswStage_succ_act_nextEdge w n e es hc hr), d.2) := by
  have hcount := kmswStage_succ_act_nextEdge w n e es hc hr
  have hval : (d.1.cast hcount).val = d.1.val := Fin.val_cast hcount d.1
  have hlt : d.1.val < (kmswStage w n).nextEdge := by
    simpa only [hval] using (d.1.cast hcount).isLt
  unfold layoutDart
  simp only [Fin.val_cast]
  split_ifs with hd
  · rw [layoutArc_old w n d.1.val hlt]
  · rw [layoutArc_old w n d.1.val hlt]



theorem stageVertex_succ_act_val (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    (stageVertex w (n + 1) d).val =
      (stageVertex w n
        (d.1.cast (kmswStage_succ_act_nextEdge w n e es hc hr), d.2)).val := by
  have hcount := kmswStage_succ_act_nextEdge w n e es hc hr
  have hval : (d.1.cast hcount).val = d.1.val := Fin.val_cast hcount d.1
  have hcode : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, hc]
  change stageEndpoint (kmswStage w (n + 1)) d =
    stageEndpoint (kmswStage w n) (d.1.cast hcount, d.2)
  unfold stageEndpoint
  rw [hval]
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hr]



theorem layoutDrawing_pos_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (v : Fin (kmswStage w (n + 1)).nextVertex) :
    (monotoneLayoutDrawing w (n + 1) h).pos v =
      P.pos (v.cast (kmswStage_succ_act_nextVertex w n e es hc hr)) := by
  have hcount := kmswStage_succ_act_nextVertex w n e es hc hr
  have hval : (v.cast hcount).val = v.val := Fin.val_cast hcount v
  calc
    (monotoneLayoutDrawing w (n + 1) h).pos v = layoutPos w (n + 1) v.val := rfl
    _ = layoutPos w n (v.cast hcount).val := by
      rw [hval, layoutPos_old_vertex w n v.val (by simpa only [hval] using (v.cast hcount).isLt)]
    _ = P.pos (v.cast hcount) := (G.pos_layout (v.cast hcount)).symm



theorem layoutDrawing_arc_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    (monotoneLayoutDrawing w (n + 1) h).arc d =
      P.arc (d.1.cast (kmswStage_succ_act_nextEdge w n e es hc hr), d.2) := by
  calc
    (monotoneLayoutDrawing w (n + 1) h).arc d = layoutDart w (n + 1) d := rfl
    _ = layoutDart w n
        (d.1.cast (kmswStage_succ_act_nextEdge w n e es hc hr), d.2) :=
      layoutDart_succ_act w n e es hc hr d
    _ = P.arc (d.1.cast (kmswStage_succ_act_nextEdge w n e es hc hr), d.2) := by
      rw [G.arc_layout]
      rfl



theorem layoutDrawing_image_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image = P.image := by
  have hv := kmswStage_succ_act_nextVertex w n e es hc hr
  have he := kmswStage_succ_act_nextEdge w n e es hc hr
  change Set.range (monotoneLayoutDrawing w (n + 1) h).pos ∪
      {z | ∃ d, z ∈ ((monotoneLayoutDrawing w (n + 1) h).arc d).image} =
    Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}
  ext z
  simp only [Set.mem_union, Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hz⟩)
    · exact Or.inl ⟨v.cast hv, (layoutDrawing_pos_act w n e es hc hr G h v).symm⟩
    · exact Or.inr ⟨(d.1.cast he, d.2),
        (layoutDrawing_arc_act w n e es hc hr G h d).symm ▸ hz⟩
  · rintro (⟨v, hvz⟩ | ⟨d, hz⟩)
    · refine Or.inl ⟨v.cast hv.symm, ?_⟩
      have hp := layoutDrawing_pos_act w n e es hc hr G h (v.cast hv.symm)
      have hcast : (v.cast hv.symm).cast hv = v := by ext; simp
      rw [hp, hcast]
      exact hvz
    · refine Or.inr ⟨(d.1.cast he.symm, d.2), ?_⟩
      have ha := layoutDrawing_arc_act w n e es hc hr G h (d.1.cast he.symm, d.2)
      have hcast : (d.1.cast he.symm).cast he = d.1 := by ext; simp
      rw [ha, hcast]
      exact hz



theorem layoutDrawing_arc_edge_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : ℕ)
    (hi : i < (kmswStage w (n + 1)).nextEdge)
    (hi' : i < (kmswStage w n).nextEdge) (b : Bool) :
    (monotoneLayoutDrawing w (n + 1) h).arc (⟨i, hi⟩, b) =
      P.arc (⟨i, hi'⟩, b) := by
  have he := kmswStage_succ_act_nextEdge w n e es hc hr
  have hcast : (⟨i, hi⟩ : Fin (kmswStage w (n + 1)).nextEdge).cast he =
      (⟨i, hi'⟩ : Fin (kmswStage w n).nextEdge) := by
    apply Fin.ext
    rfl
  rw [layoutDrawing_arc_act w n e es hc hr G h (⟨i, hi⟩, b), hcast]



theorem stageEdgeTrace_succ_act (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (i : ℕ) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) i = stageEdgeTrace P i := by
  have he := kmswStage_succ_act_nextEdge w n e es hc hr
  by_cases hi' : i < (kmswStage w n).nextEdge
  · have hi : i < (kmswStage w (n + 1)).nextEdge := by omega
    unfold stageEdgeTrace
    rw [dite_eq_left hi, dite_eq_left hi']
    rw [layoutDrawing_arc_edge_act w n e es hc hr G h i hi hi' false]
  · have hi : ¬ i < (kmswStage w (n + 1)).nextEdge := by omega
    simp [stageEdgeTrace, hi, hi']



@[expose] noncomputable def invariant_succ_act (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (e : ℕ) (es : List ℕ)
    (hr : (kmswStage w n).UR = e :: es) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) :
    MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h) := by
  let hTri := kmswStage_succ_act_triangles w n e es hc hr
  let hLen := congrArg List.length hTri
  let ci : Fin (kmswStage w (n + 1)).triangles.length →
      Fin (kmswStage w n).triangles.length := fun i => i.cast hLen
  let cap' := fun i => G.cap (ci i)
  let capL' := fun i => G.capLower (ci i)
  let capU' := fun i => G.capUpper (ci i)
  have hImage := layoutDrawing_image_act w n e es hc hr G h
  have hLower := kmswStage_succ_act_lowerLists w n e es hc hr
  have hUpper := kmswStage_succ_act_upperUnion w n e es hc hr
  have hCaps : (⋃ i, closure (cap' i).region) =
      ⋃ i : Fin (kmswStage w n).triangles.length, closure (G.cap i).region := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hz⟩
      exact ⟨ci i, hz⟩
    · rintro ⟨i, hz⟩
      refine ⟨i.cast hLen.symm, ?_⟩
      simpa [cap', ci] using hz
  refine
    { toMonotoneStageCertificate :=
        { xmin := G.xmin
          xmax := G.xmax
          hx := G.hx
          lower := G.lower
          upper := G.upper
          lower_continuous := G.lower_continuous
          upper_continuous := G.upper_continuous
          lower_le_upper := G.lower_le_upper
          lower_trace := ?_
          upper_trace := ?_
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
          ext_upper_wedge := ?_
          ext_lower_wedge := ?_ }
      cover_lower := ?_
      cover_upper := ?_
      upper_lipschitz_margin := ?_
      image_height_le := ?_
      pos_layout := ?_
      arc_layout := ?_ }
  · rw [hLower.1, hLower.2]
    simp_rw [stageEdgeTrace_succ_act w n e es hc hr G h]
    exact G.lower_trace
  · rw [hUpper]
    simp_rw [stageEdgeTrace_succ_act w n e es hc hr G h]
    exact G.upper_trace
  · intro i
    simp_rw [stageEdgeTrace_succ_act w n e es hc hr G h]
    simpa [cap', capL', ci] using G.cap_lower_trace (ci i)
  · intro i
    simp_rw [stageEdgeTrace_succ_act w n e es hc hr G h]
    simpa [cap', capU', ci] using G.cap_upper_trace (ci i)
  · intro i edge
    simpa [capL', capU', ci, hTri] using G.cap_edges (ci i) edge
  · intro i
    simpa [cap', ci, hImage] using G.cap_avoid (ci i)
  · intro i j hij
    apply G.cap_disjoint (ci i) (ci j)
    intro heq
    apply hij
    apply Fin.ext
    simpa [ci] using congrArg Fin.val heq
  · calc
      (monotoneLayoutDrawing w (n + 1) h).image ∪ ⋃ i, closure (cap' i).region =
          P.image ∪ ⋃ i : Fin (kmswStage w n).triangles.length,
            closure (G.cap i).region := by rw [hImage, hCaps]
      _ = closedGraphRegion G.xmin G.xmax G.lower G.upper := G.cover
  · intro i edge he hmem
    have heOld : edge < (kmswStage w n).nextEdge := by
      rw [← kmswStage_succ_act_nextEdge w n e es hc hr]
      exact he
    have hmemOld : edge ∈ G.capLower (ci i) := by simpa [capL', ci] using hmem
    have hw := G.cap_lower_wedge (ci i) edge heOld hmemOld
    simpa only [layoutDrawing_arc_edge_act w n e es hc hr G h edge he heOld false] using hw
  · intro i edge he hmem
    have heOld : edge < (kmswStage w n).nextEdge := by
      rw [← kmswStage_succ_act_nextEdge w n e es hc hr]
      exact he
    have hmemOld : edge ∈ G.capUpper (ci i) := by simpa [capU', ci] using hmem
    have hw := G.cap_upper_wedge (ci i) edge heOld hmemOld
    simpa only [layoutDrawing_arc_edge_act w n e es hc hr G h edge he heOld true] using hw
  · intro edge he hmem
    have heOld : edge < (kmswStage w n).nextEdge := by
      rw [← kmswStage_succ_act_nextEdge w n e es hc hr]
      exact he
    have hmemOld : edge ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
      rw [← hUpper]
      exact hmem
    have hw := G.ext_upper_wedge edge heOld hmemOld
    simpa only [layoutDrawing_arc_edge_act w n e es hc hr G h edge he heOld false] using hw
  · intro edge he hmem
    have heOld : edge < (kmswStage w n).nextEdge := by
      rw [← kmswStage_succ_act_nextEdge w n e es hc hr]
      exact he
    have hmemOld : edge ∈ (kmswStage w n).LL ++ (kmswStage w n).LR := by
      rw [← hLower.1, ← hLower.2]
      exact hmem
    have hw := G.ext_lower_wedge edge heOld hmemOld
    simpa only [layoutDrawing_arc_edge_act w n e es hc hr G h edge he heOld true] using hw
  · intro edge
    let old : Fin (kmswStage w n).nextEdge := edge.cast
      (kmswStage_succ_act_nextEdge w n e es hc hr)
    have hval : old.val = edge.val := Fin.val_cast _ _
    rcases G.cover_lower old with hupper | ⟨i, hcap⟩
    · left
      rw [hUpper]
      simpa only [hval] using hupper
    · right
      refine ⟨i.cast hLen.symm, ?_⟩
      simpa [capL', ci, hval] using hcap
  · intro edge
    let old : Fin (kmswStage w n).nextEdge := edge.cast
      (kmswStage_succ_act_nextEdge w n e es hc hr)
    have hval : old.val = edge.val := Fin.val_cast _ _
    rcases G.cover_upper old with hlower | ⟨i, hcap⟩
    · left
      rw [hLower.1, hLower.2]
      simpa only [hval] using hlower
    · right
      refine ⟨i.cast hLen.symm, ?_⟩
      simpa [capU', ci, hval] using hcap
  · obtain ⟨L, hL0, hLM, hLip⟩ := G.upper_lipschitz_margin
    refine ⟨L, hL0, hLM.trans (rampSlope_lt w (Nat.lt_succ_self n)), hLip⟩
  · intro z hz
    exact (G.image_height_le z (hImage.symm ▸ hz)).trans (by exact_mod_cast Nat.le_succ n)
  · intro v
    rfl
  · rintro ⟨edge, b⟩
    cases b <;> rfl

end DirectedDistances.KMSW
