module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.PlanarMap.RoofPolyline
public import DirectedDistances.PlanarMap.MonotonePolyline
public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.PlanarMap.SlopeAngularOrder






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set



theorem kmswStage_upper_chain (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).UL ++ (kmswStage w n).UR).IsChain
      (fun e f => (kmswStage w n).east e = (kmswStage w n).west f) :=
  (kmswStage_boundary_chain_invariant w n).1



theorem kmswStage_lower_chain (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).LL ++ (kmswStage w n).LR).IsChain
      (fun e f => (kmswStage w n).east e = (kmswStage w n).west f) :=
  (kmswStage_boundary_chain_invariant w n).2.1



theorem kmswStage_boundary_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL ++ (kmswStage w n).UR ≠ [] ∧
      (kmswStage w n).LL ++ (kmswStage w n).LR ≠ [] := by
  exact ⟨List.append_ne_nil_of_left_ne_nil
    (kmswStage_UL_nonempty_active_last w n).1 _,
    List.append_ne_nil_of_right_ne_nil _
      (kmswStage_boundary_chain_invariant w n).2.2.2.2.1⟩



theorem kmswStage_boundary_endpoints (w : ℕ → Fin 3) (n : ℕ) :
    let s := kmswStage w n
    s.west ((s.UL ++ s.UR).head (kmswStage_boundary_nonempty w n).1) =
        s.west ((s.LL ++ s.LR).head (kmswStage_boundary_nonempty w n).2) ∧
      s.east ((s.UL ++ s.UR).getLast (kmswStage_boundary_nonempty w n).1) =
        s.east ((s.LL ++ s.LR).getLast (kmswStage_boundary_nonempty w n).2) := by
  have hs := (kmswStage_boundary_chain_invariant w n).2.2.1
  have he := (kmswStage_boundary_chain_invariant w n).2.2.2.1
  unfold boundaryStart at hs
  unfold boundaryEnd at he
  rw [List.head?_eq_some_head (kmswStage_boundary_nonempty w n).1,
    List.head?_eq_some_head (kmswStage_boundary_nonempty w n).2] at hs
  rw [List.getLast?_eq_getLast_of_ne_nil (kmswStage_boundary_nonempty w n).1,
    List.getLast?_eq_getLast_of_ne_nil (kmswStage_boundary_nonempty w n).2] at he
  exact ⟨Option.some.inj hs, Option.some.inj he⟩

private theorem boundary_edge_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∨
      e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  simp only [List.mem_append] at he ⊢
  tauto

private theorem trace_layout {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    stageEdgeTrace P e = (layoutArc w n e).image := by
  simp only [stageEdgeTrace, he, ↓reduceDIte, G.arc_layout, Bool.false_eq_true,
    ↓reduceIte]

private theorem upper_arc_graph {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {e : ℕ}
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    (layoutArc w n e).image ⊆ graphOver G.xmin G.xmax G.upper := by
  rw [G.upper_trace]
  intro z hz
  exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he,
    (trace_layout G e (boundary_edge_bound w n e (Or.inl he))).symm ▸ hz⟩⟩

private theorem chain_bounds (W E : ℕ → ℝ) (es : List ℕ) (hne : es ≠ [])
    (hc : es.IsChain (fun e f => E e = W f))
    (hinc : ∀ e ∈ es, W e < E e) :
    ∀ e ∈ es, W (es.head hne) ≤ W e ∧ E e ≤ E (es.getLast hne) := by
  induction es with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil => simp
    | cons b bs =>
      have ht := ih (by simp) hc.tail (fun e he => hinc e (by simp [he]))
      have hab : E a = W b := hc.rel_head? (by simp)
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨le_rfl, ?_⟩
        have hb := ht b (by simp)
        simpa only [List.getLast_cons_cons] using
          (hab.le.trans ((hinc b (by simp)).le.trans hb.2))
      · have he' := ht e he
        constructor
        · exact (hinc a (by simp)).le.trans (hab.le.trans he'.1)
        · simpa only [List.getLast_cons_cons] using he'.2

private theorem upper_rank_bounds (w : ℕ → Fin 3) (n : ℕ) :
    let s := kmswStage w n
    ∀ e ∈ s.UL ++ s.UR,
      (layoutPos w n (s.west ((s.UL ++ s.UR).head
        (kmswStage_boundary_nonempty w n).1))).re ≤
          (layoutPos w n (s.west e)).re ∧
      (layoutPos w n (s.east e)).re ≤
        (layoutPos w n (s.east ((s.UL ++ s.UR).getLast
          (kmswStage_boundary_nonempty w n).1))).re := by
  dsimp only
  apply chain_bounds (fun e => (layoutPos w n ((kmswStage w n).west e)).re)
    (fun e => (layoutPos w n ((kmswStage w n).east e)).re) _ _
    ((kmswStage_upper_chain w n).imp (fun _ _ h =>
      congrArg (fun v => (layoutPos w n v).re) h))
  intro e he
  change (kmswStageRank w n ((kmswStage w n).west e) : ℝ) <
    (kmswStageRank w n ((kmswStage w n).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict w n e (boundary_edge_bound w n e (Or.inl he))



theorem MonotoneStageInvariant.xmin_eq_upper_start {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    G.xmin = (layoutPos w n ((kmswStage w n).west
      (((kmswStage w n).UL ++ (kmswStage w n).UR).head
        (kmswStage_boundary_nonempty w n).1))).re := by
  let es := (kmswStage w n).UL ++ (kmswStage w n).UR
  let e := es.head (kmswStage_boundary_nonempty w n).1
  have he : e ∈ es := List.head_mem _
  have heB := boundary_edge_bound w n e (Or.inl he)
  have hstart := upper_arc_graph G he (Or.inl rfl)
  rw [layoutArc_start w n e heB] at hstart
  apply le_antisymm hstart.1
  have hz : (⟨G.xmin, G.upper G.xmin⟩ : ℂ) ∈
      graphOver G.xmin G.xmax G.upper := ⟨le_rfl, G.hx, rfl⟩
  rw [G.upper_trace] at hz
  obtain ⟨f, hf⟩ := mem_iUnion.mp hz
  obtain ⟨hf, hz⟩ := mem_iUnion.mp hf
  rw [trace_layout G f (boundary_edge_bound w n f (Or.inl hf))] at hz
  obtain ⟨g, hg⟩ := layoutArc_image_graph w n f (boundary_edge_bound w n f (Or.inl hf))
  rw [hg] at hz
  exact (upper_rank_bounds w n f hf).1.trans hz.1



theorem MonotoneStageInvariant.xmax_eq_upper_end {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    G.xmax = (layoutPos w n ((kmswStage w n).east
      (((kmswStage w n).UL ++ (kmswStage w n).UR).getLast
        (kmswStage_boundary_nonempty w n).1))).re := by
  let es := (kmswStage w n).UL ++ (kmswStage w n).UR
  let e := es.getLast (kmswStage_boundary_nonempty w n).1
  have he : e ∈ es := List.getLast_mem _
  have heB := boundary_edge_bound w n e (Or.inl he)
  obtain ⟨g, hg⟩ := layoutArc_image_graph w n e heB
  have hre : (layoutPos w n ((kmswStage w n).west e)).re ≤
      (layoutPos w n ((kmswStage w n).east e)).re := by
    change (kmswStageRank w n ((kmswStage w n).west e) : ℝ) ≤
      (kmswStageRank w n ((kmswStage w n).east e) : ℝ)
    exact_mod_cast (kmswStageRank_strict w n e heB).le
  have hend := upper_arc_graph G he (show
      (⟨(layoutPos w n ((kmswStage w n).east e)).re,
        g (layoutPos w n ((kmswStage w n).east e)).re⟩ : ℂ) ∈
        (layoutArc w n e).image from hg.symm ▸ ⟨hre, le_rfl, rfl⟩)
  apply le_antisymm ?_ hend.2.1
  have hz : (⟨G.xmax, G.upper G.xmax⟩ : ℂ) ∈
      graphOver G.xmin G.xmax G.upper := ⟨G.hx, le_rfl, rfl⟩
  rw [G.upper_trace] at hz
  obtain ⟨f, hf⟩ := mem_iUnion.mp hz
  obtain ⟨hf, hz⟩ := mem_iUnion.mp hf
  rw [trace_layout G f (boundary_edge_bound w n f (Or.inl hf))] at hz
  obtain ⟨g, hg⟩ := layoutArc_image_graph w n f (boundary_edge_bound w n f (Or.inl hf))
  rw [hg] at hz
  exact hz.2.1.trans (upper_rank_bounds w n f hf).2



theorem MonotoneStageInvariant.xmax_eq_active_east_of_UR_nil
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (hUR : (kmswStage w n).UR = []) :
    G.xmax = (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
  rw [G.xmax_eq_upper_end]
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  simp only [hUR, List.append_nil, hxs, List.getLast_append_singleton]



theorem MonotoneStageInvariant.xmin_eq_active_west_of_UL_dropLast_reverse_nil
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    G.xmin = (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re := by
  rw [G.xmin_eq_upper_start]
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hd : (kmswStage w n).UL.dropLast = [] := by
    simpa using congrArg List.reverse hUL
  have hxs0 : xs = [] := by simpa [hxs] using hd
  simp only [hxs, hxs0, List.nil_append, List.singleton_append, List.head_cons]



theorem MonotoneStageInvariant.upper_eq_arc_height
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {e : ℕ}
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    {z : ℂ} (hz : z ∈ (layoutArc w n e).image) : G.upper z.re = z.im :=
  (upper_arc_graph G he hz).2.2.symm



theorem MonotoneStageInvariant.lower_eq_arc_height
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {e : ℕ}
    (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)
    {z : ℂ} (hz : z ∈ (layoutArc w n e).image) : G.lower z.re = z.im := by
  have hg : z ∈ graphOver G.xmin G.xmax G.lower := by
    rw [G.lower_trace]
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he,
      (trace_layout G e (boundary_edge_bound w n e (Or.inr he))).symm ▸ hz⟩⟩
  exact hg.2.2.symm

private theorem heightFn_of_mem_image {p : Polyline} (hp : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) : p.heightFn z.re = z.im := by
  rcases hz with hz | ⟨i, hi, hz⟩
  · rw [hz]
    simpa only [Polyline.point_zero_eq_start] using
      (Polyline.heightFn_point hp (List.length_pos_iff.mpr p.nonempty))
  · have hstrict := Polyline.point_re_lt hp (Nat.lt_succ_self i) hi
    have hz' := (mem_segment_iff_height hstrict).mp hz
    rw [Polyline.heightFn_linear_on_segment hp hi hz'.1 hz'.2.1]
    exact hz'.2.2.symm



theorem MonotoneStageInvariant.upper_eq_heightFn
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {e : ℕ}
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) {x : ℝ}
    (hx : x ∈ Icc (layoutPos w n ((kmswStage w n).west e)).re
      (layoutPos w n ((kmswStage w n).east e)).re) :
    G.upper x = (layoutArc w n e).heightFn x := by
  have heB := boundary_edge_bound w n e (Or.inl he)
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n e heB
  have hz : (⟨x, f x⟩ : ℂ) ∈ (layoutArc w n e).image := hf.symm ▸ ⟨hx.1, hx.2, rfl⟩
  exact (G.upper_eq_arc_height he hz).trans
    (heightFn_of_mem_image (layoutArc_points_pairwise w n e heB) hz).symm



theorem MonotoneStageInvariant.lower_eq_heightFn
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {e : ℕ}
    (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) {x : ℝ}
    (hx : x ∈ Icc (layoutPos w n ((kmswStage w n).west e)).re
      (layoutPos w n ((kmswStage w n).east e)).re) :
    G.lower x = (layoutArc w n e).heightFn x := by
  have heB := boundary_edge_bound w n e (Or.inr he)
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n e heB
  have hz : (⟨x, f x⟩ : ℂ) ∈ (layoutArc w n e).image := hf.symm ▸ ⟨hx.1, hx.2, rfl⟩
  exact (G.lower_eq_arc_height he hz).trans
    (heightFn_of_mem_image (layoutArc_points_pairwise w n e heB) hz).symm



theorem MonotoneStageInvariant.image_bounds
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {z : ℂ} (hz : z ∈ P.image) :
    G.xmin ≤ z.re ∧ z.re ≤ G.xmax ∧ G.lower z.re ≤ z.im ∧ z.im ≤ G.upper z.re := by
  have hr : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inl hz
  exact hr



theorem MonotoneStageInvariant.upper_le_stage
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {x : ℝ} (hx : x ∈ Icc G.xmin G.xmax) :
    G.upper x ≤ n := by
  have hz : (⟨x, G.upper x⟩ : ℂ) ∈ graphOver G.xmin G.xmax G.upper :=
    ⟨hx.1, hx.2, rfl⟩
  rw [G.upper_trace] at hz
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  obtain ⟨he, hz⟩ := mem_iUnion.mp he
  rw [trace_layout G e (boundary_edge_bound w n e (Or.inl he))] at hz
  apply G.image_height_le ⟨x, G.upper x⟩
  exact Or.inr ⟨(⟨e, boundary_edge_bound w n e (Or.inl he)⟩, false),
    by simpa only [G.arc_layout, Bool.false_eq_true, ↓reduceIte] using hz⟩



theorem MonotoneStageInvariant.upper_lt_roofHeight
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {a b : ℂ}
    (ha : a.re ∈ Icc G.xmin G.xmax) (hb : b.re ∈ Icc G.xmin G.xmax)
    (hya : G.upper a.re ≤ a.im) (hyb : G.upper b.re ≤ b.im) :
    ∀ x ∈ Ioo a.re b.re, G.upper x < roofHeight a b (n + 1) (rampSlope w n) x := by
  obtain ⟨L, _, hLM, hLip⟩ := G.upper_lipschitz_margin
  apply segmentHeight_separation hLM G.upper
  · intro x hx
    have hdom : x ∈ Icc G.xmin G.xmax := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    have hL := (le_abs_self (G.upper x - G.upper a.re)).trans (hLip x hdom a.re ha)
    have hR := (le_abs_self (G.upper x - G.upper b.re)).trans (hLip x hdom b.re hb)
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at hL
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] at hR
    constructor <;> linarith only [hL, hR, hya, hyb]
  · intro x hx
    have hdom : x ∈ Icc G.xmin G.xmax := ⟨ha.1.trans hx.1.le, hx.2.le.trans hb.2⟩
    have hh := G.upper_le_stage hdom
    linarith only [hh]



theorem MonotoneStageInvariant.roof_interior_disjoint_image
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {a b : ℂ}
    (ha : a.re ∈ Icc G.xmin G.xmax) (hb : b.re ∈ Icc G.xmin G.xmax)
    (hya : a.im = G.upper a.re) (hyb : b.im = G.upper b.re)
    (hfit : ((n + 1 : ℝ) - a.im) / rampSlope w n +
      ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - a.re) :
    Disjoint (roofArc a b (n + 1) (rampSlope w n)).interior P.image := by
  apply Set.disjoint_left.mpr
  intro z hz hzP
  have haH : a.im ≤ (n + 1 : ℝ) := by
    have hh := G.upper_le_stage ha
    rw [hya]
    linarith only [hh]
  have hbH : b.im ≤ (n + 1 : ℝ) := by
    have hh := G.upper_le_stage hb
    rw [hyb]
    linarith only [hh]
  rw [roofArc_interior (rampSlope_pos w n) haH hbH hfit] at hz
  have hsep := G.upper_lt_roofHeight ha hb hya.ge hyb.ge z.re ⟨hz.1, hz.2.1⟩
  exact (not_lt_of_ge (G.image_bounds hzP).2.2.2) (hz.2.2 ▸ hsep)



theorem MonotoneStageInvariant.old_vertex_not_mem_roof_interior
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {a b : ℂ}
    (ha : a.re ∈ Icc G.xmin G.xmax) (hb : b.re ∈ Icc G.xmin G.xmax)
    (hya : a.im = G.upper a.re) (hyb : b.im = G.upper b.re)
    (hfit : ((n + 1 : ℝ) - a.im) / rampSlope w n +
      ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - a.re)
    (v : Fin (kmswStage w n).nextVertex) :
    layoutPos w n v.val ∉ (roofArc a b (n + 1) (rampSlope w n)).interior := by
  intro hz
  have hv : layoutPos w n v.val ∈ P.image := by
    rw [← G.pos_layout v]
    exact Or.inl ⟨v, rfl⟩
  exact Set.disjoint_left.mp (G.roof_interior_disjoint_image ha hb hya hyb hfit) hz hv

private theorem roof_adjacent_height_bound {a b : ℂ} {H M : ℝ}
    (hM : 0 < M) (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    (roofArc a b H M).points.IsChain
      (fun z z' => |z'.im - z.im| ≤ M * (z'.re - z.re)) := by
  have hl : |H - a.im| = M * ((a.re + (H - a.im) / M) - a.re) := by
    rw [abs_of_nonneg (sub_nonneg.mpr ha)]
    field_simp
    ring
  have hr : |b.im - H| = M * (b.re - (b.re - (H - b.im) / M)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hb)]
    field_simp
    ring
  have hmid : 0 ≤ M * ((b.re - (H - b.im) / M) -
      (a.re + (H - a.im) / M)) :=
    mul_nonneg hM.le (by linarith only [hfit])
  have hab : 0 ≤ M * (b.re - a.re) := by
    apply mul_nonneg hM.le
    have ha0 := div_nonneg (sub_nonneg.mpr ha) hM.le
    have hb0 := div_nonneg (sub_nonneg.mpr hb) hM.le
    linarith only [hfit, ha0, hb0]
  by_cases haH : a.im = H <;> by_cases hbH : b.im = H
  · simpa [roofArc, haH, hbH] using hab
  · have hm : 0 ≤ M * ((b.re - (H - b.im) / M) - a.re) := by
      simpa only [haH, sub_self, zero_div, add_zero] using hmid
    simpa [roofArc, haH, hbH] using And.intro hm hr.le
  · have hm : 0 ≤ M * (b.re - (a.re + (H - a.im) / M)) := by
      simpa only [hbH, sub_self, zero_div, sub_zero] using hmid
    simpa [roofArc, haH, hbH] using And.intro hl.le hm
  · simpa [roofArc, haH, hbH] using And.intro hl.le (And.intro hmid hr.le)

private theorem roof_segment_slope_le {a b : ℂ} {H M : ℝ}
    (hM : 0 < M) (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re)
    (i : ℕ) (hi : i + 1 < (roofArc a b H M).points.length) :
    |((roofArc a b H M).point (i + 1)).im - ((roofArc a b H M).point i).im| /
      (((roofArc a b H M).point (i + 1)).re - ((roofArc a b H M).point i).re) ≤ M := by
  have hc := List.isChain_iff_getElem.mp (roof_adjacent_height_bound hM ha hb hfit) i hi
  have hpos := sub_pos.mpr (Polyline.point_re_lt
    (roofArc_points_pairwise hM ha hb hfit) (Nat.lt_succ_self i) hi)
  apply (div_le_iff₀ hpos).mpr
  simpa only [Polyline.point, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega : i < (roofArc a b H M).points.length),
    Option.getD_some] using hc



theorem layoutArc_segment_slope_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) (i : ℕ)
    (hi : i + 1 < (layoutArc w n e).points.length) :
    |((layoutArc w n e).point (i + 1)).im - ((layoutArc w n e).point i).im| /
      (((layoutArc w n e).point (i + 1)).re - ((layoutArc w n e).point i).re) <
        rampSlope w n := by
  induction n with
  | zero =>
    have hi0 : i = 0 := by
      simp only [layoutArc, segmentArc, List.length_cons, List.length_nil] at hi
      omega
    subst i
    simpa [layoutArc, segmentArc, Polyline.point, Polyline.start, layoutPos,
      layoutHeight, kmswStageRank] using rampSlope_pos w 0
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · rw [layoutArc_old w n e ho] at hi ⊢
      exact (ih ho hi).trans (rampSlope_lt w (Nat.lt_succ_self n))
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [layoutArc_fresh w n e hf] at hi ⊢
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at hi
        have hi0 : i = 0 := by
          simp only [segmentArc, List.length_cons, List.length_nil] at hi
          omega
        subst i
        obtain ⟨hl, hnil, rfl⟩ := hm
        simpa [segmentArc, Polyline.point] using
          freshLeft_missing_edge_slope_lt w n (n + 1) hl hnil (Nat.le_succ n)
      · obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e hf
        rename_i hm
        simp only [hm, ↓reduceIte] at hi
        exact (roof_segment_slope_le (rampSlope_pos w n) ha hb
          (freshEdges_ramp_widths_lt w n e hf) i hi).trans_lt
            (rampSlope_lt w (Nat.lt_succ_self n))



theorem layoutArc_length_two_le (w : ℕ → Fin 3) (n e : ℕ) :
    2 ≤ (layoutArc w n e).points.length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [layoutArc]
    split
    · exact ih
    · split
      · split
        · exact le_rfl
        · exact roofArc_length _ _ _ _
      · exact ih



theorem layoutArc_initial_slope_abs_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    |(layoutArc w n e).initialDirection.im / (layoutArc w n e).initialDirection.re| <
      rampSlope w n := by
  have hlen := layoutArc_length_two_le w n e
  have hs := layoutArc_segment_slope_lt w n e he 0 (by omega)
  have hp := Polyline.initialDirection_re_pos (layoutArc_points_pairwise w n e he) hlen
  change 0 < ((layoutArc w n e).point 1).re - (layoutArc w n e).start.re at hp
  simpa only [Nat.zero_add, Polyline.point_zero_eq_start, Polyline.initialDirection,
    Complex.sub_im, Complex.sub_re, abs_div, abs_of_pos hp] using hs



theorem layoutArc_reverse_initial_slope_abs_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    |(layoutArc w n e).reverse.initialDirection.im /
      (layoutArc w n e).reverse.initialDirection.re| < rampSlope w n := by
  let p := layoutArc w n e
  have hp : p.XMonotone := layoutArc_points_pairwise w n e he
  have hlen : 2 ≤ p.points.length := layoutArc_length_two_le w n e
  have hi : p.points.length - 2 + 1 < p.points.length := by omega
  have hs := layoutArc_segment_slope_lt w n e he (p.points.length - 2) hi
  have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
  have hpos : 0 < (p.point (p.points.length - 1)).re -
      (p.point (p.points.length - 2)).re := sub_pos.mpr
        (Polyline.point_re_lt hp (by omega) (by omega))
  have hd : p.reverse.initialDirection =
      -(p.point (p.points.length - 1) - p.point (p.points.length - 2)) := by
    rw [Polyline.initialDirection, Polyline.start_reverse, p.reverse_point_one hlen,
      ← p.point_last_eq_finish]
    abel
  change |p.reverse.initialDirection.im / p.reverse.initialDirection.re| < _
  rw [hd]
  simpa only [hidx, Complex.neg_im, Complex.neg_re, neg_div_neg_eq, Complex.sub_im,
    Complex.sub_re, abs_div, abs_of_pos hpos] using hs



theorem layoutDart_initial_slope_abs_lt (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    |(layoutDart w n d).initialDirection.im / (layoutDart w n d).initialDirection.re| <
      rampSlope w n := by
  cases hb : d.2
  · simpa only [layoutDart, hb, Bool.false_eq_true, ↓reduceIte] using
      layoutArc_initial_slope_abs_lt w n d.1.val d.1.isLt
  · simpa only [layoutDart, hb, ↓reduceIte] using
      layoutArc_reverse_initial_slope_abs_lt w n d.1.val d.1.isLt



theorem layoutDart_initialDirection_re_sign (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    if d.2 then (layoutDart w n d).initialDirection.re < 0
    else 0 < (layoutDart w n d).initialDirection.re := by
  have hp := layoutArc_points_pairwise w n d.1.val d.1.isLt
  have hlen := layoutArc_length_two_le w n d.1.val
  cases hb : d.2
  · simpa only [layoutDart, hb, Bool.false_eq_true, ↓reduceIte] using
      Polyline.initialDirection_re_pos hp hlen
  · simpa only [layoutDart, hb, ↓reduceIte] using
      Polyline.reverse_initialDirection_re_neg hp hlen



theorem layoutDart_incl_eq (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  change (if d.2 then (layoutArc w (n + 1) d.1.val).reverse
    else layoutArc w (n + 1) d.1.val) = _
  rw [layoutArc_old w n d.1.val d.1.isLt]
  rfl



theorem layoutDart_old_initial_slope_bounds (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    -rampSlope w n <
        (layoutDart w (n + 1) (stageDartIncl w n d)).initialDirection.im /
          (layoutDart w (n + 1) (stageDartIncl w n d)).initialDirection.re ∧
      (layoutDart w (n + 1) (stageDartIncl w n d)).initialDirection.im /
          (layoutDart w (n + 1) (stageDartIncl w n d)).initialDirection.re <
        rampSlope w n := by
  rw [layoutDart_incl_eq]
  exact abs_lt.mp (layoutDart_initial_slope_abs_lt w n d)

private theorem initial_ray_mem_image (p : Polyline) (hlen : 2 ≤ p.points.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  refine Or.inr ⟨0, by omega, ?_⟩
  change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
  rw [Polyline.point_zero_eq_start]
  have hpoint : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  rw [hpoint]
  exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩

private theorem east_initial_slope_le (p q : Polyline) (upper : ℝ → ℝ)
    (hpLen : 2 ≤ p.points.length) (hqLen : 2 ≤ q.points.length)
    (hp : 0 < p.initialDirection.re) (hq : 0 < q.initialDirection.re)
    (hs : q.start = p.start)
    (hgraph : ∀ z ∈ p.image, z.im = upper z.re)
    (hbelow : ∀ z ∈ q.image, z.im ≤ upper z.re) :
    q.initialDirection.im / q.initialDirection.re ≤
      p.initialDirection.im / p.initialDirection.re := by
  let δ := min p.initialDirection.re q.initialDirection.re / 2
  have hδ : 0 < δ := div_pos (lt_min hp hq) (by norm_num)
  have hδp : δ ≤ p.initialDirection.re := by
    have hh := min_le_left p.initialDirection.re q.initialDirection.re
    dsimp only [δ]
    linarith only [hh, hp]
  have hδq : δ ≤ q.initialDirection.re := by
    have hh := min_le_right p.initialDirection.re q.initialDirection.re
    dsimp only [δ]
    linarith only [hh, hq]
  have hP := hgraph _ (initial_ray_mem_image p hpLen
    ⟨div_nonneg hδ.le hp.le, (div_le_one hp).mpr hδp⟩)
  have hQ := hbelow _ (initial_ray_mem_image q hqLen
    ⟨div_nonneg hδ.le hq.le, (div_le_one hq).mpr hδq⟩)
  have hxp : (p.start + (δ / p.initialDirection.re) • p.initialDirection).re =
      p.start.re + δ := by simp [div_mul_cancel₀ _ hp.ne']
  have hxq : (q.start + (δ / q.initialDirection.re) • q.initialDirection).re =
      p.start.re + δ := by simp [hs, div_mul_cancel₀ _ hq.ne']
  rw [hxp] at hP
  rw [hxq] at hQ
  have him : δ * (q.initialDirection.im / q.initialDirection.re) ≤
      δ * (p.initialDirection.im / p.initialDirection.re) := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hP hQ
    rw [hs] at hQ
    simp only [div_eq_mul_inv] at hP hQ ⊢
    nlinarith only [hP, hQ]
  exact (mul_le_mul_iff_right₀ hδ).mp him



theorem MonotoneStageInvariant.upper_east_dart_topmost
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (e : Fin (kmswStage w n).nextEdge)
    (he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    (d : StageDart (kmswStage w n).nextEdge)
    (hv : stageVertex w n d = stageVertex w n (e, false))
    (hd : 0 < (layoutDart w n d).initialDirection.re) :
    d = (e, false) ∨
      (layoutDart w n d).initialDirection.im / (layoutDart w n d).initialDirection.re <
        (layoutDart w n (e, false)).initialDirection.im /
          (layoutDart w n (e, false)).initialDirection.re := by
  have harc : ∀ f, P.arc f = layoutDart w n f := G.arc_layout
  have hp : 0 < (layoutArc w n e.val).initialDirection.re :=
    Polyline.initialDirection_re_pos (layoutArc_points_pairwise w n e.val e.isLt)
      (layoutArc_length_two_le w n e.val)
  have hs : (layoutDart w n d).start = (layoutArc w n e.val).start := by
    change (layoutDart w n d).start = (layoutDart w n (e, false)).start
    rw [← harc d, ← harc (e, false), P.arc_start, P.arc_start, hv]
  have hlen : 2 ≤ (layoutDart w n d).points.length := by
    rw [← harc]
    exact P.arc_length d
  have hle := east_initial_slope_le (layoutArc w n e.val) (layoutDart w n d) G.upper
    (layoutArc_length_two_le w n e.val) hlen hp hd hs
    (fun z hz => (G.upper_eq_arc_height he hz).symm)
    (fun z hz => (G.image_bounds (Or.inr ⟨d, by rwa [harc d]⟩)).2.2.2)
  by_cases hde : d = (e, false)
  · exact Or.inl hde
  · right
    apply lt_of_le_of_ne hle
    intro heq
    apply hde
    apply (layoutGood_of_invariant G).initial_arg_injective d (e, false) hv
    change Complex.arg (layoutDart w n d).initialDirection =
      Complex.arg (layoutArc w n e.val).initialDirection
    rw [east_arg_eq_arctan hd, east_arg_eq_arctan hp, heq]

private theorem reverse_initial_ray_mem_image (p : Polyline)
    (hlen : 2 ≤ p.points.length) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.reverse.start + t • p.reverse.initialDirection ∈ p.image := by
  refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
  have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
  change p.reverse.start + t • p.reverse.initialDirection ∈
    segment ℝ (p.point (p.points.length - 2)) (p.point (p.points.length - 2 + 1))
  rw [hidx, Polyline.point_last_eq_finish, Polyline.initialDirection,
    Polyline.start_reverse, p.reverse_point_one hlen]
  have hpoint : p.finish + t • (p.point (p.points.length - 2) - p.finish) =
      t • p.point (p.points.length - 2) + (1 - t) • p.finish := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hpoint]
  exact ⟨t, 1 - t, ht.1, sub_nonneg.mpr ht.2, by ring, rfl⟩

private theorem west_initial_slope_le (p q : Polyline) (upper : ℝ → ℝ)
    (hqLen : 2 ≤ q.points.length)
    (hp : p.initialDirection.re < 0) (hq : q.initialDirection.re < 0)
    (hs : q.start = p.start)
    (hgraph : ∀ t ∈ Icc (0 : ℝ) 1,
      (p.start + t • p.initialDirection).im = upper (p.start + t • p.initialDirection).re)
    (hbelow : ∀ z ∈ q.image, z.im ≤ upper z.re) :
    p.initialDirection.im / p.initialDirection.re ≤
      q.initialDirection.im / q.initialDirection.re := by
  let δ := min (-p.initialDirection.re) (-q.initialDirection.re) / 2
  have hδ : 0 < δ := div_pos (lt_min (neg_pos.mpr hp) (neg_pos.mpr hq)) (by norm_num)
  have hδp : δ ≤ -p.initialDirection.re := by
    have hh := min_le_left (-p.initialDirection.re) (-q.initialDirection.re)
    dsimp only [δ]
    linarith only [hh, hp]
  have hδq : δ ≤ -q.initialDirection.re := by
    have hh := min_le_right (-p.initialDirection.re) (-q.initialDirection.re)
    dsimp only [δ]
    linarith only [hh, hq]
  have hP := hgraph _ ⟨div_nonneg hδ.le (neg_nonneg.mpr hp.le),
    (div_le_one (neg_pos.mpr hp)).mpr hδp⟩
  have hQ := hbelow _ (initial_ray_mem_image q hqLen
    ⟨div_nonneg hδ.le (neg_nonneg.mpr hq.le),
      (div_le_one (neg_pos.mpr hq)).mpr hδq⟩)
  have hxp : (p.start + (δ / -p.initialDirection.re) • p.initialDirection).re =
      p.start.re - δ := by simp [div_neg, div_mul_cancel₀ _ hp.ne, sub_eq_add_neg]
  have hxq : (q.start + (δ / -q.initialDirection.re) • q.initialDirection).re =
      p.start.re - δ := by simp [hs, div_neg, div_mul_cancel₀ _ hq.ne, sub_eq_add_neg]
  rw [hxp] at hP
  rw [hxq] at hQ
  have him : δ * (p.initialDirection.im / p.initialDirection.re) ≤
      δ * (q.initialDirection.im / q.initialDirection.re) := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hP hQ
    rw [hs] at hQ
    simp only [div_eq_mul_inv, inv_neg] at hP hQ ⊢
    nlinarith only [hP, hQ]
  exact (mul_le_mul_iff_right₀ hδ).mp him

private theorem west_arg_eq_of_slope_eq {a b : ℂ} (ha : a.re < 0) (hb : b.re < 0)
    (heq : a.im / a.re = b.im / b.re) : Complex.arg a = Complex.arg b := by
  have hc := (div_eq_div_iff ha.ne hb.ne).mp heq
  have hab : a = ((a.re / b.re : ℝ) : ℂ) * b := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      field_simp [hb.ne]
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      field_simp [hb.ne]
      nlinarith only [hc]
  rw [hab]
  exact Complex.arg_real_mul b (div_pos_of_neg_of_neg ha hb)



theorem MonotoneStageInvariant.upper_west_dart_topmost
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (e : Fin (kmswStage w n).nextEdge)
    (he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    (d : StageDart (kmswStage w n).nextEdge)
    (hv : stageVertex w n d = stageVertex w n (e, true))
    (hd : (layoutDart w n d).initialDirection.re < 0) :
    d = (e, true) ∨
      (layoutDart w n (e, true)).initialDirection.im /
          (layoutDart w n (e, true)).initialDirection.re <
        (layoutDart w n d).initialDirection.im / (layoutDart w n d).initialDirection.re := by
  have harc : ∀ f, P.arc f = layoutDart w n f := G.arc_layout
  have hp : (layoutArc w n e.val).reverse.initialDirection.re < 0 :=
    Polyline.reverse_initialDirection_re_neg (layoutArc_points_pairwise w n e.val e.isLt)
      (layoutArc_length_two_le w n e.val)
  have hs : (layoutDart w n d).start = (layoutArc w n e.val).reverse.start := by
    change (layoutDart w n d).start = (layoutDart w n (e, true)).start
    rw [← harc d, ← harc (e, true), P.arc_start, P.arc_start, hv]
  have hlen : 2 ≤ (layoutDart w n d).points.length := by
    rw [← harc]
    exact P.arc_length d
  have hle := west_initial_slope_le (layoutArc w n e.val).reverse (layoutDart w n d)
    G.upper hlen hp hd hs
    (fun t ht => (G.upper_eq_arc_height he (reverse_initial_ray_mem_image
      (layoutArc w n e.val) (layoutArc_length_two_le w n e.val) ht)).symm)
    (fun z hz => (G.image_bounds (Or.inr ⟨d, by rwa [harc d]⟩)).2.2.2)
  by_cases hde : d = (e, true)
  · exact Or.inl hde
  · right
    apply lt_of_le_of_ne hle
    intro heq
    apply hde
    apply (layoutGood_of_invariant G).initial_arg_injective d (e, true) hv
    exact west_arg_eq_of_slope_eq hd hp heq.symm



theorem stageVertex_incl_eq (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageVertex w (n + 1) (stageDartIncl w n d) = stageVertexIncl w n (stageVertex w n d) := by
  apply Fin.ext
  have he := kmswStage_endpoints_stable w (Nat.le_succ n) d.1.isLt
  cases hb : d.2
  · simpa only [stageVertex, stageVertexIncl, stageDartIncl, stageEndpoint, hb,
      Bool.false_eq_true, ↓reduceIte, Fin.val_castLE] using he.1
  · simpa only [stageVertex, stageVertexIncl, stageDartIncl, stageEndpoint, hb,
      ↓reduceIte, Fin.val_castLE] using he.2

private theorem dartIncl_injective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Injective (stageDartIncl w n) := by
  intro d e h
  apply Prod.ext
  · exact Fin.ext (congrArg (fun f => f.1.val) h)
  · exact congrArg (fun f : StageDart (kmswStage w (n + 1)).nextEdge => f.2) h

private theorem ccwSuccessor_image {D E : Type*} (ι : D → E)
    (hinj : Function.Injective ι) (star : Set D) (dir : D → ℂ) (dir' : E → ℂ)
    (hdir : ∀ d, dir' (ι d) = dir d) {d e : D}
    (h : CcwSuccessor star dir d e) : CcwSuccessor (ι '' star) dir' (ι d) (ι e) := by
  obtain ⟨hfin, hd, he, hcase⟩ := h
  refine ⟨hfin.image ι, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
  rcases hcase with ⟨rfl, hs⟩ | ⟨hne, hmin⟩
  · exact Or.inl ⟨rfl, by simp only [hs, Set.image_singleton]⟩
  · refine Or.inr ⟨fun h => hne (hinj h), ?_⟩
    rintro f ⟨g, hg, rfl⟩ hgd
    simpa only [hdir] using hmin g hg (fun h => hgd (congrArg ι h))

private theorem old_star_eq_image (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    {f : StageDart (kmswStage w (n + 1)).nextEdge |
      f.1.val < (kmswStage w n).nextEdge ∧
        stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} =
      stageDartIncl w n '' {e | stageVertex w n e = stageVertex w n d} := by
  ext f
  constructor
  · rintro ⟨hf, hv⟩
    let e : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf⟩, f.2)
    have he : stageDartIncl w n e = f := by apply Prod.ext <;> rfl
    refine ⟨e, ?_, he⟩
    rw [← he, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    exact Fin.ext (congrArg
      (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv)
  · rintro ⟨e, hv, rfl⟩
    exact ⟨e.1.isLt, by rw [stageVertex_incl_eq, stageVertex_incl_eq, hv]⟩



theorem MonotoneStageInvariant.old_star_rotation_agreement
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (d : StageDart (kmswStage w n).nextEdge) :
    CcwSuccessor
      {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n d) (stageDartIncl w n (stageRot w n d)) := by
  rw [old_star_eq_image]
  exact ccwSuccessor_image (stageDartIncl w n) (dartIncl_injective w n) _ _ _
    (fun e => congrArg Polyline.initialDirection (layoutDart_incl_eq w n e))
    ((layoutGood_of_invariant G).rotation_agreement d)

private theorem same_edge_same_vertex (w : ℕ → Fin 3) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hid : d.1.val = e.1.val) (hv : stageVertex w n d = stageVertex w n e) : d = e := by
  apply Prod.ext (Fin.ext hid)
  have hends : (kmswStage w n).west d.1.val ≠ (kmswStage w n).east d.1.val := by
    intro h
    have hh := kmswStageRank_strict w n d.1.val d.1.isLt
    rw [h] at hh
    exact (lt_irrefl _ hh)
  have hval := congrArg (fun v : Fin (kmswStage w n).nextVertex => v.val) hv
  change stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) e at hval
  simp only [stageEndpoint] at hval
  rw [← hid] at hval
  cases hd : d.2 <;> cases he : e.2 <;>
    simp only [hd, he, Bool.false_eq_true, ↓reduceIte] at hval <;>
    first | rfl | exact False.elim (hends hval) | exact False.elim (hends hval.symm)

private theorem two_fresh_vertex_unique (w : ℕ → Fin 3) (n : ℕ)
    {d e : StageDart (kmswStage w (n + 1)).nextEdge}
    (hd : d.1.val = (kmswStage w n).nextEdge ∨
      d.1.val = (kmswStage w n).nextEdge + 1)
    (he : e.1.val = (kmswStage w n).nextEdge ∨
      e.1.val = (kmswStage w n).nextEdge + 1)
    (hv : stageVertex w (n + 1) d = stageVertex w (n + 1) e)
    (hOld : (stageVertex w (n + 1) d).val < (kmswStage w n).nextVertex)
    (huv : (kmswStage w n).west (kmswStage w n).active ≠
      (kmswStage w n).east (kmswStage w n).active)
    (hends :
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
          (kmswStage w n).nextVertex ∧
        (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
          (kmswStage w n).east (kmswStage w n).active ∧
        (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) =
          (kmswStage w n).nextVertex ∧
        (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
          (kmswStage w n).west (kmswStage w n).active) ∨
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
          (kmswStage w n).west (kmswStage w n).active ∧
        (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
          (kmswStage w n).nextVertex ∧
        (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) =
          (kmswStage w n).nextVertex ∧
        (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
          (kmswStage w n).east (kmswStage w n).active)) : d = e := by
  have hval := congrArg (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv
  change stageEndpoint (kmswStage w (n + 1)) d < _ at hOld
  rcases hd with hd | hd <;> rcases he with he | he
  · exact same_edge_same_vertex w (n + 1) d e (hd.trans he.symm) hv
  · rcases hends with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
      cases hb : d.2 <;> cases hc : e.2 <;>
      simp only [stageVertex, stageEndpoint, hb, hc, Bool.false_eq_true, ↓reduceIte,
        hd, he, h0, h1, h2, h3] at hval hOld <;> omega
  · rcases hends with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
      cases hb : d.2 <;> cases hc : e.2 <;>
      simp only [stageVertex, stageEndpoint, hb, hc, Bool.false_eq_true, ↓reduceIte,
        hd, he, h0, h1, h2, h3] at hval hOld <;> omega
  · exact same_edge_same_vertex w (n + 1) d e (hd.trans he.symm) hv

private theorem fresh_darts_same_old_vertex (w : ℕ → Fin 3) (n : ℕ)
    {d e : StageDart (kmswStage w (n + 1)).nextEdge}
    (hd : d.1.val ∈ freshEdges w n) (he : e.1.val ∈ freshEdges w n)
    (hv : stageVertex w (n + 1) d = stageVertex w (n + 1) e)
    (hOld : (stageVertex w (n + 1) d).val < (kmswStage w n).nextVertex) : d = e := by
  obtain ⟨hd0, hd1⟩ := Finset.mem_Ico.mp hd
  obtain ⟨he0, he1⟩ := Finset.mem_Ico.mp he
  have huv : (kmswStage w n).west (kmswStage w n).active ≠
      (kmswStage w n).east (kmswStage w n).active := by
    intro h
    have hh := kmswStageRank_strict w n _ (kmswStage_boundary_ids_lt_nextEdge w n).1
    rw [h] at hh
    exact (lt_irrefl _ hh)
  by_cases hl : w n = 0
  · cases hs : (kmswStage w n).UL.dropLast.reverse with
    | nil =>
      have hcount : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
        simp [kmswStage, kmswStep, kmswCodeStep, hl, kmswStepOfStep, hs, State.addEdge]
      apply two_fresh_vertex_unique w n (by omega) (by omega) hv hOld huv
      left
      simp [kmswStage, kmswStep, kmswCodeStep, hl, kmswStepOfStep, hs, State.addEdge]
    | cons a as =>
      have hcount : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
        simp [kmswStage, kmswStep, kmswCodeStep, hl, kmswStepOfStep, hs, State.addEdge]
      exact same_edge_same_vertex w (n + 1) d e (by omega) hv
  · by_cases hu : w n = 1
    · have hcount : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
        simp [kmswStage, kmswStep, kmswCodeStep, hu, kmswStepOfStep, State.addEdge]
      apply two_fresh_vertex_unique w n (by omega) (by omega) hv hOld huv
      right
      simp [kmswStage, kmswStep, kmswCodeStep, hu, kmswStepOfStep, State.addEdge]
    · cases hs : (kmswStage w n).UR with
      | nil =>
        have hcount : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
          simp [kmswStage, kmswStep, kmswCodeStep, hl, hu, kmswStepOfStep, hs, State.addEdge]
        exact same_edge_same_vertex w (n + 1) d e (by omega) hv
      | cons a as =>
        have hcount : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge := by
          simp [kmswStage, kmswStep, kmswCodeStep, hl, hu, kmswStepOfStep, hs]
        omega



theorem stageStar_eq_insert_old_star (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n)
    (hv : stageVertex w (n + 1) x = stageVertex w (n + 1) (stageDartIncl w n d)) :
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} =
      insert x {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} := by
  ext f
  constructor
  · intro hf
    by_cases ho : f.1.val < (kmswStage w n).nextEdge
    · exact Set.mem_insert_of_mem x ⟨ho, hf⟩
    · have hfr : f.1.val ∈ freshEdges w n :=
        Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt ho, f.1.isLt⟩
      have hOld : (stageVertex w (n + 1) f).val < (kmswStage w n).nextVertex := by
        rw [hf, stageVertex_incl_eq]
        exact (stageVertex w n d).isLt
      exact Or.inl (fresh_darts_same_old_vertex w n hfr hx (hf.trans hv.symm) hOld)
  · rintro (rfl | ⟨_, hf⟩)
    · exact hv
    · exact hf

private theorem fresh_east_roof_geom (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n) (hb : x.2 = false)
    (hOld : (stageVertex w (n + 1) x).val < (kmswStage w n).nextVertex) :
    0 < (layoutDart w (n + 1) x).initialDirection.re ∧
      (layoutDart w (n + 1) x).initialDirection.im /
        (layoutDart w (n + 1) x).initialDirection.re = rampSlope w n := by
  have hwOld : (kmswStage w (n + 1)).west x.1.val < (kmswStage w n).nextVertex := by
    simpa only [stageVertex, stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hOld
  have hm : ¬ isFreshLeftMissing w n x.1.val := by
    rintro ⟨hl, he, hid⟩
    have hw : (kmswStage w (n + 1)).west x.1.val = (kmswStage w n).nextVertex := by
      rw [hid]
      simp [kmswStage, kmswStep, kmswCodeStep, hl, kmswStepOfStep, he, State.addEdge]
    rw [hw] at hwOld
    exact (Nat.lt_irrefl _ hwOld)
  have hheight : (layoutPos w (n + 1) ((kmswStage w (n + 1)).west x.1.val)).im <
      (n + 1 : ℝ) := by
    rw [layoutPos_old_vertex w n _ hwOld]
    have hh := layoutHeight_le w n _ hwOld
    change (layoutHeight w n _ : ℝ) < _
    exact lt_of_le_of_lt (by exact_mod_cast hh) (by exact_mod_cast Nat.lt_succ_self n)
  simp only [layoutDart, hb, Bool.false_eq_true, ↓reduceIte, layoutArc_fresh w n _ hx,
    hm] at *
  exact ⟨roofArc_initialDirection_re_pos (rampSlope_pos w n) hheight,
    roofArc_initialSlope (rampSlope_pos w n) hheight⟩

private theorem fresh_west_roof_geom (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n) (hb : x.2 = true)
    (hm : ¬ isFreshLeftMissing w n x.1.val)
    (hOld : (stageVertex w (n + 1) x).val < (kmswStage w n).nextVertex) :
    (layoutDart w (n + 1) x).initialDirection.re < 0 ∧
      (layoutDart w (n + 1) x).initialDirection.im /
        (layoutDart w (n + 1) x).initialDirection.re = -rampSlope w n := by
  have heOld : (kmswStage w (n + 1)).east x.1.val < (kmswStage w n).nextVertex := by
    simpa only [stageVertex, stageEndpoint, hb, ↓reduceIte] using hOld
  have hheight : (layoutPos w (n + 1) ((kmswStage w (n + 1)).east x.1.val)).im <
      (n + 1 : ℝ) := by
    rw [layoutPos_old_vertex w n _ heOld]
    have hh := layoutHeight_le w n _ heOld
    change (layoutHeight w n _ : ℝ) < _
    exact lt_of_le_of_lt (by exact_mod_cast hh) (by exact_mod_cast Nat.lt_succ_self n)
  constructor
  · simpa only [hb, ↓reduceIte] using layoutDart_initialDirection_re_sign w (n + 1) x
  · simp only [layoutDart, hb, ↓reduceIte, layoutArc_fresh w n _ hx, hm]
    exact roofArc_reverse_initialSlope (rampSlope_pos w n) hheight

private theorem old_star_args_injective {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (d : StageDart (kmswStage w n).nextEdge)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hslope : (layoutDart w (n + 1) x).initialDirection.im /
      (layoutDart w (n + 1) x).initialDirection.re = rampSlope w n ∨
      (layoutDart w (n + 1) x).initialDirection.im /
      (layoutDart w (n + 1) x).initialDirection.re = -rampSlope w n) :
    ∀ a ∈ insert x (stageDartIncl w n '' {f | stageVertex w n f = stageVertex w n d}),
      ∀ b ∈ insert x (stageDartIncl w n '' {f | stageVertex w n f = stageVertex w n d}),
        a ≠ b → Complex.arg (layoutDart w (n + 1) a).initialDirection ≠
          Complex.arg (layoutDart w (n + 1) b).initialDirection := by
  have hnew : ∀ f, Complex.arg (layoutDart w (n + 1) x).initialDirection ≠
      Complex.arg (layoutDart w (n + 1) (stageDartIncl w n f)).initialDirection := by
    intro f harg
    have hs := congrArg Real.tan harg
    simp only [Complex.tan_arg, layoutDart_incl_eq] at hs
    have hh := abs_lt.mp (layoutDart_initial_slope_abs_lt w n f)
    rcases hslope with hx | hx <;> rw [hx] at hs <;> linarith only [hs, hh.1, hh.2]
  rintro a (rfl | ⟨a, ha, rfl⟩) b (rfl | ⟨b, hb, rfl⟩) hne
  · exact (hne rfl).elim
  · exact hnew b
  · exact (hnew a).symm
  · intro harg
    apply hne
    apply congrArg (stageDartIncl w n)
    apply (layoutGood_of_invariant G).initial_arg_injective a b (ha.trans hb.symm)
    simpa only [layoutDart_incl_eq] using harg

private theorem layoutDart_nonvertical (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (layoutDart w n d).initialDirection.re ≠ 0 := by
  have h := layoutDart_initialDirection_re_sign w n d
  cases hb : d.2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    exact h.ne'
  · simp only [hb, ↓reduceIte] at h
    exact h.ne

private theorem fresh_not_mem_old_star (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (x : StageDart (kmswStage w (n + 1)).nextEdge) (hx : x.1.val ∈ freshEdges w n) :
    x ∉ stageDartIncl w n '' {f | stageVertex w n f = stageVertex w n d} := by
  rintro ⟨f, _, hf⟩
  have hval := congrArg (fun a : StageDart (kmswStage w (n + 1)).nextEdge => a.1.val) hf
  have hlt := f.1.isLt
  have hge := (Finset.mem_Ico.mp hx).1
  change f.1.val = x.1.val at hval
  omega



theorem MonotoneStageInvariant.east_roof_insertion_successors
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (e : Fin (kmswStage w n).nextEdge)
    (he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n) (hb : x.2 = false)
    (hv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n (e, false))) :
    CcwSuccessor
      {f | stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n (e, false))}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n (e, false)) x ∧
    CcwSuccessor
      {f | stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n (e, false))}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      x (stageDartIncl w n (stageRot w n (e, false))) := by
  let a : StageDart (kmswStage w n).nextEdge := (e, false)
  let S := stageDartIncl w n '' {f | stageVertex w n f = stageVertex w n a}
  have hOld : (stageVertex w (n + 1) x).val < (kmswStage w n).nextVertex := by
    rw [hv, stageVertex_incl_eq]
    exact (stageVertex w n a).isLt
  obtain ⟨hxEast, hxSlope⟩ := fresh_east_roof_geom w n x hx hb hOld
  have hStar : {f | stageVertex w (n + 1) f =
      stageVertex w (n + 1) (stageDartIncl w n a)} = insert x S := by
    rw [stageStar_eq_insert_old_star w n a x hx hv, old_star_eq_image]
  change CcwSuccessor _ _ (stageDartIncl w n a) x ∧ CcwSuccessor _ _ x _
  rw [hStar]
  have hold : CcwSuccessor S (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n a) (stageDartIncl w n (stageRot w n a)) := by
    simpa only [old_star_eq_image] using G.old_star_rotation_agreement a
  have hdEast : 0 < (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.re := by
    rw [layoutDart_incl_eq]
    exact Polyline.initialDirection_re_pos (layoutArc_points_pairwise w n e.val e.isLt)
      (layoutArc_length_two_le w n e.val)
  apply east_insert_topmost_successors S _ _ _ x hold.1
    (old_star_args_injective G a x (Or.inl hxSlope))
    (fun f _ => layoutDart_nonvertical w (n + 1) f)
    ⟨a, rfl, rfl⟩ (fresh_not_mem_old_star w n a x hx) hdEast hxEast
    ?_ ?_ hold
  · rintro f ⟨g, hg, rfl⟩ hpos
    simp only [layoutDart_incl_eq] at hpos ⊢
    rcases G.upper_east_dart_topmost e he g hg hpos with h | h
    · exact Or.inl (congrArg (stageDartIncl w n) h)
    · exact Or.inr h
  · rw [hxSlope]
    exact (layoutDart_old_initial_slope_bounds w n a).2



theorem MonotoneStageInvariant.west_roof_insertion_successors
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (e : Fin (kmswStage w n).nextEdge)
    (he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n) (hb : x.2 = true)
    (hm : ¬ isFreshLeftMissing w n x.1.val)
    (hv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n (e, true))) :
    CcwSuccessor
      {f | stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n (e, true))}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n ((stageRot w n).symm (e, true))) x ∧
    CcwSuccessor
      {f | stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n (e, true))}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      x (stageDartIncl w n (e, true)) := by
  let a : StageDart (kmswStage w n).nextEdge := (e, true)
  let p := (stageRot w n).symm a
  let S := stageDartIncl w n '' {f | stageVertex w n f = stageVertex w n a}
  have hOld : (stageVertex w (n + 1) x).val < (kmswStage w n).nextVertex := by
    rw [hv, stageVertex_incl_eq]
    exact (stageVertex w n a).isLt
  obtain ⟨hxWest, hxSlope⟩ := fresh_west_roof_geom w n x hx hb hm hOld
  have hStar : {f | stageVertex w (n + 1) f =
      stageVertex w (n + 1) (stageDartIncl w n a)} = insert x S := by
    rw [stageStar_eq_insert_old_star w n a x hx hv, old_star_eq_image]
  change CcwSuccessor _ _ (stageDartIncl w n p) x ∧
    CcwSuccessor _ _ x (stageDartIncl w n a)
  rw [hStar]
  have hrot : stageRot w n p = a := (stageRot w n).apply_symm_apply a
  have hpv : stageVertex w n p = stageVertex w n a := by
    have hh := P.vert_rotation p
    rw [hrot] at hh
    exact hh.symm
  have hold : CcwSuccessor S (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n p) (stageDartIncl w n a) := by
    apply ccwSuccessor_image (stageDartIncl w n) (dartIncl_injective w n) _ _ _
      (fun f => congrArg Polyline.initialDirection (layoutDart_incl_eq w n f))
    have hh := (layoutGood_of_invariant G).rotation_agreement p
    rw [hpv, hrot] at hh
    exact hh
  have hdWest : (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.re < 0 := by
    rw [layoutDart_incl_eq]
    exact Polyline.reverse_initialDirection_re_neg
      (layoutArc_points_pairwise w n e.val e.isLt) (layoutArc_length_two_le w n e.val)
  have hmin : ∀ f ∈ S, (layoutDart w (n + 1) f).initialDirection.re < 0 →
      f = stageDartIncl w n a ∨
        (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.im /
            (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.re <
          (layoutDart w (n + 1) f).initialDirection.im /
            (layoutDart w (n + 1) f).initialDirection.re := by
    rintro f ⟨g, hg, rfl⟩ hneg
    simp only [layoutDart_incl_eq] at hneg ⊢
    rcases G.upper_west_dart_topmost e he g hg hneg with h | h
    · exact Or.inl (congrArg (stageDartIncl w n) h)
    · exact Or.inr h
  have hnew : (layoutDart w (n + 1) x).initialDirection.im /
      (layoutDart w (n + 1) x).initialDirection.re <
        (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.im /
          (layoutDart w (n + 1) (stageDartIncl w n a)).initialDirection.re := by
    rw [hxSlope]
    exact (layoutDart_old_initial_slope_bounds w n a).1
  exact (west_insert_topmost_splice S _ (stageDartIncl w n p) (stageDartIncl w n a) x
    hold.1 (fun f _ => layoutDart_nonvertical w (n + 1) f)
    (old_star_args_injective G a x (Or.inr hxSlope)) (fresh_not_mem_old_star w n a x hx)
    hdWest hxWest hmin hnew hold).2

end DirectedDistances.KMSW
