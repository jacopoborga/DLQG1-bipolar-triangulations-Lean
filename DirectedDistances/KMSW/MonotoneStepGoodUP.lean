module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
import DirectedDistances.KMSW.MonotoneStepCommon

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

private theorem up_counts (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]

private theorem dart_old (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  change (if d.2 then (layoutArc w (n + 1) d.1.val).reverse
    else layoutArc w (n + 1) d.1.val) = _
  rw [layoutArc_old w n d.1.val d.1.isLt]
  rfl

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

private theorem reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ finish_mem_image p
  · have hi' : i + 1 < p.points.length := by simpa only [Polyline.reverse,
        List.length_reverse] using hi
    rw [reverse_segment p i hi'] at hz
    exact Or.inr ⟨p.points.length - 2 - i, by omega, hz⟩

private theorem reverse_image (p : Polyline) : p.reverse.image = p.image := by
  apply Subset.antisymm (reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using reverse_image_subset p.reverse

private theorem reverse_interior (p : Polyline) : p.reverse.interior = p.interior := by
  rw [Polyline.interior, reverse_image, Polyline.start_reverse, Polyline.finish_reverse]
  rw [Set.pair_comm]
  rfl

private theorem dart_interior (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (layoutDart w n d).interior = (layoutArc w n d.1.val).interior := by
  unfold layoutDart
  split
  · exact reverse_interior _
  · rfl

private theorem old_image_below {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {z : ℂ} (hz : z ∈ P.image) :
    G.xmin ≤ z.re ∧ z.re ≤ G.xmax ∧ z.im ≤ G.upper z.re := by
  have hr : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inl hz
  exact ⟨hr.1, hr.2.1, hr.2.2.2⟩

private theorem trace_subset_image {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (e : ℕ) : stageEdgeTrace P e ⊆ P.image := by
  unfold stageEdgeTrace
  split
  · intro z hz
    exact Or.inr ⟨_, hz⟩
  · exact empty_subset _

private theorem upper_height {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (x : ℝ) (hx : x ∈ Icc G.xmin G.xmax) :
    G.upper x ≤ n := by
  let z : ℂ := ⟨x, G.upper x⟩
  have hz : z ∈ graphOver G.xmin G.xmax G.upper := ⟨hx.1, hx.2, rfl⟩
  rw [G.upper_trace] at hz
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  obtain ⟨_, hz⟩ := mem_iUnion.mp he
  exact G.image_height_le z (trace_subset_image P e hz)

private theorem active_trace_upper {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    (layoutArc w n (kmswStage w n).active).image ⊆
      graphOver G.xmin G.xmax G.upper := by
  intro z hz
  rw [G.upper_trace]
  apply mem_iUnion.mpr ⟨(kmswStage w n).active, ?_⟩
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hm : (kmswStage w n).active ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    rw [hxs]
    simp
  apply mem_iUnion.mpr ⟨hm, ?_⟩
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).1
  simp only [stageEdgeTrace, hb, ↓reduceDIte, G.arc_layout, Bool.false_eq_true,
    ↓reduceIte]
  exact hz

private theorem active_endpoints_upper {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west (kmswStage w n).active)
    let b := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    a ∈ graphOver G.xmin G.xmax G.upper ∧ b ∈ graphOver G.xmin G.xmax G.upper := by
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).1
  constructor
  · apply active_trace_upper G
    rw [← layoutArc_start w n _ hb]
    exact Or.inl rfl
  · apply active_trace_upper G
    rw [← layoutArc_finish w n _ hb]
    exact finish_mem_image _

private theorem roof_above_upper {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
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
    have hh := upper_height G x hdom
    linarith only [hh]

private theorem up_endpoints (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
        (kmswStage w n).west (kmswStage w n).active ∧
      (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
        (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).east (kmswStage w n).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]

private theorem up_new_pos (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (layoutPos w (n + 1) (kmswStage w n).nextVertex).re =
        ((layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re +
          (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re) / 2 ∧
      (layoutPos w (n + 1) (kmswStage w n).nextVertex).im = (n + 1 : ℝ) := by
  constructor
  · simp [layoutPos, kmswStageRank, hc]
  · exact (layoutHeight_created_vertex w n (up_counts w n hc).2).trans (by push_cast; rfl)

private theorem up_fresh_endpoint_bounds {w : ℕ → Fin 3} {n : ℕ}
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : ℕ) (he : e ∈ freshEdges w n) :
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    a.re ∈ Icc G.xmin G.xmax ∧ b.re ∈ Icc G.xmin G.xmax ∧
      G.upper a.re ≤ a.im ∧ G.upper b.re ≤ b.im := by
  obtain ⟨ha, hb⟩ := active_endpoints_upper G
  have hact := (kmswStage_boundary_ids_lt_nextEdge w n).1
  obtain ⟨hu, hv⟩ := kmswStage_endpoints_lt_nextVertex w n _ hact
  have hab : (layoutPos w n ((kmswStage w n).west (kmswStage w n).active)).re <
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re := by
    change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
    exact_mod_cast kmswStageRank_strict w n _ hact
  obtain ⟨hp, hpy⟩ := up_new_pos w n hc
  have hpdom : (layoutPos w (n + 1) (kmswStage w n).nextVertex).re ∈
      Icc G.xmin G.xmax := by
    constructor <;> linarith only [ha.1, hb.2.1, hab, hp]
  have hpbound : G.upper (layoutPos w (n + 1) (kmswStage w n).nextVertex).re ≤
      (layoutPos w (n + 1) (kmswStage w n).nextVertex).im := by
    rw [hpy]
    exact (upper_height G _ hpdom).trans (by linarith)
  obtain ⟨h0, h1, h2, h3⟩ := up_endpoints w n hc
  have hh := Finset.mem_Ico.mp he
  rw [(up_counts w n hc).1] at hh
  have cases_e : e = (kmswStage w n).nextEdge ∨
      e = (kmswStage w n).nextEdge + 1 := by omega
  dsimp only
  rcases cases_e with rfl | rfl
  · rw [h0, h1, layoutPos_old_vertex w n _ hu]
    exact ⟨⟨ha.1, ha.2.1⟩, hpdom, ha.2.2.ge, hpbound⟩
  · rw [h2, h3, layoutPos_old_vertex w n _ hv]
    exact ⟨hpdom, ⟨hb.1, hb.2.1⟩, hpbound, hb.2.2.ge⟩

private theorem up_fresh_interior_above {w : ℕ → Fin 3} {n : ℕ}
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (e : ℕ) (he : e ∈ freshEdges w n) {z : ℂ}
    (hz : z ∈ (layoutArc w (n + 1) e).interior) : G.upper z.re < z.im := by
  have hm : ¬ isFreshLeftMissing w n e := by
    rintro ⟨h0, _, _⟩
    rw [hc] at h0
    cases h0
  rw [layoutArc_fresh w n e he, ite_eq_right hm] at hz
  obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e he
  rw [roofArc_interior (rampSlope_pos w n) ha hb
    (freshEdges_ramp_widths_lt w n e he)] at hz
  obtain ⟨hda, hdb, hya, hyb⟩ := up_fresh_endpoint_bounds hc G e he
  rw [hz.2.2]
  exact roof_above_upper G hda hdb hya hyb z.re ⟨hz.1, hz.2.1⟩

private theorem arc_subset_old_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) : (layoutArc w n e).image ⊆ P.image := by
  intro z hz
  apply Or.inr
  refine ⟨(⟨e, he⟩, false), ?_⟩
  simpa only [G.arc_layout, Bool.false_eq_true, ↓reduceIte] using hz

private theorem up_fresh_pair_disjoint (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    Disjoint (layoutArc w (n + 1) (kmswStage w n).nextEdge).interior
      (layoutArc w (n + 1) ((kmswStage w n).nextEdge + 1)).interior := by
  have hcount := (up_counts w n hc).1
  have hf0 : (kmswStage w n).nextEdge ∈ freshEdges w n :=
    Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hf1 : (kmswStage w n).nextEdge + 1 ∈ freshEdges w n :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hroof (e : ℕ) (he : e ∈ freshEdges w n) :
      (layoutArc w (n + 1) e).interior =
        {z | (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).re < z.re ∧
          z.re < (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).re ∧
          z.im = roofHeight
            (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e))
            (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e))
            (n + 1) (rampSlope w n) z.re} := by
    have hm : ¬ isFreshLeftMissing w n e := by
      rintro ⟨h0, _, _⟩
      rw [hc] at h0
      cases h0
    rw [layoutArc_fresh w n e he, ite_eq_right hm]
    obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e he
    exact roofArc_interior (rampSlope_pos w n) ha hb
      (freshEdges_ramp_widths_lt w n e he)
  rw [hroof _ hf0, hroof _ hf1]
  obtain ⟨_, h0, h1, _⟩ := up_endpoints w n hc
  rw [h0, h1]
  exact Set.disjoint_left.mpr (fun z hz0 hz1 => (not_lt_of_gt hz0.2.1) hz1.1)




theorem layoutGood_succ_up_interior_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d e : StageDart (kmswStage w (n + 1)).nextEdge,
      e ≠ d → e ≠ edgeFlip _ d →
        Disjoint (layoutDart w (n + 1) d).interior
          (layoutDart w (n + 1) e).interior := by
  intro d e hne hf
  by_cases hd : d.1.val < (kmswStage w n).nextEdge
  · by_cases he : e.1.val < (kmswStage w n).nextEdge
    · let d0 : StageDart (kmswStage w n).nextEdge := (⟨d.1.val, hd⟩, d.2)
      let e0 : StageDart (kmswStage w n).nextEdge := (⟨e.1.val, he⟩, e.2)
      have hd0 : stageDartIncl w n d0 = d := rfl
      have he0 : stageDartIncl w n e0 = e := rfl
      rw [← hd0, ← he0, dart_old, dart_old]
      apply (layoutGood_of_invariant G).interior_disjoint
      · intro h
        exact hne (congrArg (stageDartIncl w n) h)
      · intro h
        apply hf
        exact congrArg (stageDartIncl w n) h
    · rw [dart_interior, dart_interior, layoutArc_old w n d.1.val hd]
      have hef : e.1.val ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, e.1.isLt⟩
      apply Set.disjoint_left.mpr
      intro z hzd hze
      have hbelow := old_image_below G (arc_subset_old_image G d.1.val hd hzd.1)
      exact (not_lt_of_ge hbelow.2.2) (up_fresh_interior_above hc G _ hef hze)
  · by_cases he : e.1.val < (kmswStage w n).nextEdge
    · rw [dart_interior, dart_interior, layoutArc_old w n e.1.val he]
      have hdf : d.1.val ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, d.1.isLt⟩
      apply Set.disjoint_left.mpr
      intro z hzd hze
      have hbelow := old_image_below G (arc_subset_old_image G e.1.val he hze.1)
      exact (not_lt_of_ge hbelow.2.2) (up_fresh_interior_above hc G _ hdf hzd)
    · have hdiff : e.1.val ≠ d.1.val := by
        intro hv
        have heq : e.1 = d.1 := Fin.ext hv
        rcases d with ⟨di, db⟩
        rcases e with ⟨ei, eb⟩
        dsimp only at heq
        subst ei
        cases db <;> cases eb <;> first | exact hne rfl | exact hf rfl
      have hde := d.1.isLt
      have hee := e.1.isLt
      simp only [(up_counts w n hc).1] at hde hee
      have hcases :
          (d.1.val = (kmswStage w n).nextEdge ∧
            e.1.val = (kmswStage w n).nextEdge + 1) ∨
          (d.1.val = (kmswStage w n).nextEdge + 1 ∧
            e.1.val = (kmswStage w n).nextEdge) := by omega
      rw [dart_interior, dart_interior]
      rcases hcases with ⟨hd0, he1⟩ | ⟨hd1, he0⟩
      · rw [hd0, he1]
        exact up_fresh_pair_disjoint w n hc
      · rw [hd1, he0]
        exact (up_fresh_pair_disjoint w n hc).symm




theorem layoutGood_succ_up_interior_avoids_vertices (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
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
      simp only [(up_counts w n hc).2] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq, dart_interior]
      intro hz
      have him := G.image_height_le _ (arc_subset_old_image G d.1.val hd hz.1)
      rw [(up_new_pos w n hc).2] at him
      linarith only [him]
  · have hdf : d.1.val ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, d.1.isLt⟩
    rw [dart_interior]
    by_cases hv : v.val < (kmswStage w n).nextVertex
    · intro hz
      have hvimage : layoutPos w (n + 1) v.val ∈ P.image := by
        rw [layoutPos_old_vertex w n v.val hv, ← G.pos_layout ⟨v.val, hv⟩]
        exact Or.inl ⟨⟨v.val, hv⟩, rfl⟩
      exact (not_lt_of_ge (old_image_below G hvimage).2.2)
        (up_fresh_interior_above hc G _ hdf hz)
    · have hb := v.isLt
      simp only [(up_counts w n hc).2] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq]
      intro hz
      have he := d.1.isLt
      simp only [(up_counts w n hc).1] at he
      have hcases : d.1.val = (kmswStage w n).nextEdge ∨
          d.1.val = (kmswStage w n).nextEdge + 1 := by omega
      rcases hcases with he0 | he1
      · have heast := (up_endpoints w n hc).2.1
        have hfinish := layoutArc_finish w (n + 1) d.1.val d.1.isLt
        rw [he0, heast] at hfinish
        apply hz.2
        rw [he0]
        exact Or.inr hfinish.symm
      · have hwest := (up_endpoints w n hc).2.2.1
        have hstart := layoutArc_start w (n + 1) d.1.val d.1.isLt
        rw [he1, hwest] at hstart
        apply hz.2
        rw [he1]
        exact Or.inl hstart.symm

private theorem arc_length (w : ℕ → Fin 3) (m e : ℕ) :
    2 ≤ (layoutArc w m e).points.length := by
  induction m with
  | zero => exact le_refl 2
  | succ m ih =>
    rw [layoutArc]
    split
    · exact ih
    · split
      · split
        · exact le_refl 2
        · exact roofArc_length _ _ _ _
      · exact ih

private theorem ray_interior (p : Polyline) (hlen : 2 ≤ p.points.length)
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

private theorem dart_ray (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (layoutDart w m d).start + t • (layoutDart w m d).initialDirection ∈
      (layoutDart w m d).interior := by
  have hp := layoutArc_points_pairwise w m d.1.val d.1.isLt
  have hl := arc_length w m d.1.val
  have hlast : (layoutArc w m d.1.val).points.length - 1 <
      (layoutArc w m d.1.val).points.length := by omega
  rcases d with ⟨e, b⟩
  change 2 ≤ (layoutArc w m e.val).points.length at hl
  cases b
  · apply ray_interior _ hl (Or.inl ⟨Polyline.initialDirection_re_pos hp hl, ?_⟩) t ht ht1
    rw [← Polyline.point_last_eq_finish]
    exact Polyline.point_re_le_of_le (p := layoutArc w m e.val) hp (by omega) hlast
  · apply ray_interior _ (by simpa only [layoutDart, ↓reduceIte,
        Polyline.reverse, List.length_reverse] using hl)
      (Or.inr ⟨Polyline.reverse_initialDirection_re_neg hp hl, ?_⟩) t ht ht1
    change (layoutArc w m e.val).reverse.finish.re ≤
      ((layoutArc w m e.val).reverse.point 1).re
    rw [Polyline.finish_reverse, Polyline.reverse_point_one _ hl,
      ← Polyline.point_zero_eq_start]
    exact Polyline.point_re_le_of_le (p := layoutArc w m e.val) hp
      (Nat.zero_le _) (by omega)

private theorem dart_start (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    (layoutDart w m d).start = layoutPos w m (stageVertex w m d).val := by
  rcases d with ⟨e, b⟩
  cases b
  · exact layoutArc_start w m e.val e.isLt
  · exact (Polyline.start_reverse _).trans (layoutArc_finish w m e.val e.isLt)

private theorem dart_nonzero (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    (layoutDart w m d).initialDirection ≠ 0 := by
  have hp := layoutArc_points_pairwise w m d.1.val d.1.isLt
  have hl := arc_length w m d.1.val
  rcases d with ⟨e, b⟩
  cases b
  · exact Polyline.initialDirection_ne_zero hp hl
  · intro hz
    have hn := Polyline.reverse_initialDirection_re_neg hp hl
    change (layoutArc w m e.val).reverse.initialDirection = 0 at hz
    rw [hz, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn




theorem layoutGood_succ_up_initial_arg_injective (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
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
      change (kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west di.val) : ℝ) <
        (kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east di.val) : ℝ)
      exact_mod_cast hstrict
    cases db
    · exact hneq (congrArg Complex.re hstart)
    · exact hneq (congrArg Complex.re hstart).symm
  let u := (layoutDart w (n + 1) d).initialDirection
  let v := (layoutDart w (n + 1) e).initialDirection
  let c : ℝ := ‖v‖ / ‖u‖
  have hcpos : 0 < c := div_pos (norm_pos_iff.mpr (dart_nonzero w _ e))
    (norm_pos_iff.mpr (dart_nonzero w _ d))
  have hcv : c • u = v := by
    simpa only [Complex.real_smul, Complex.ofReal_div, c, u, v] using
      (Complex.arg_eq_arg_iff (dart_nonzero w _ d) (dart_nonzero w _ e)).mp ha
  let t : ℝ := min 1 c / 2
  have ht : 0 < t := div_pos (lt_min (by norm_num) hcpos) (by norm_num)
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_left (1 : ℝ) c]
  have htc : t < c := by dsimp [t]; linarith [min_le_right (1 : ℝ) c]
  have htcpos : 0 < t / c := div_pos ht hcpos
  have htclt : t / c < 1 := (div_lt_one hcpos).mpr htc
  have heq : (layoutDart w (n + 1) d).start + t • u =
      (layoutDart w (n + 1) e).start + (t / c) • v := by
    rw [dart_start, dart_start, hv, ← hcv, smul_smul, div_mul_cancel₀ _ hcpos.ne']
  have hz0 := dart_ray w (n + 1) d t ht ht1
  have hz1 := dart_ray w (n + 1) e (t / c) htcpos htclt
  rw [← heq] at hz1
  exact Set.disjoint_left.mp (layoutGood_succ_up_interior_disjoint w n hc G d e
    (Ne.symm hne) hf) hz0 hz1

private theorem successor_insert_other {D : Type*} (S : Set D) (dir : D → ℂ)
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

private def upFresh (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (j : Fin 2) (b : Bool) : StageDart (kmswStage w (n + 1)).nextEdge :=
  (⟨(kmswStage w n).nextEdge + j.val, by
    have hh := (up_counts w n hc).1
    have hj := j.isLt
    omega⟩, b)

private theorem unresize_eval {k l : ℕ} (h : k = l)
    (τ : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (ht : StageRotation.resize h τ = σ) (d : StageDart l) :
    τ (Fin.cast h.symm d.1, d.2) =
      (Fin.cast h.symm (σ d).1, (σ d).2) := by
  cases h
  exact congrArg (fun ρ => ρ d) ht

private theorem up_rotation_old (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageRot w (n + 1) (stageDartIncl w n d) =
      if d = (⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩,
          false) then upFresh w n hc 0 false
      else if stageRot w n d =
          (⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩,
            true) then upFresh w n hc 1 true
      else stageDartIncl w n (stageRot w n d) := by
  have ht := StageRotation.step_up (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl)
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have hh := unresize_eval _ _ _ ht
    (StageRotation.allocation (kmswStage w n).nextEdge 2 (.inl d))
  rw [StageRotation.up_old] at hh
  split_ifs at hh ⊢ <;>
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, upFresh] using hh

private theorem up_rotation_new (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    let a : StageDart (kmswStage w n).nextEdge :=
      (⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, false)
    let A : StageDart (kmswStage w n).nextEdge := (a.1, true)
    stageRot w (n + 1) (upFresh w n hc 0 false) =
        (if stageRot w n a = A then upFresh w n hc 1 true
          else stageDartIncl w n (stageRot w n a)) ∧
      stageRot w (n + 1) (upFresh w n hc 1 true) = stageDartIncl w n A ∧
      stageRot w (n + 1) (upFresh w n hc 0 true) = upFresh w n hc 1 false ∧
      stageRot w (n + 1) (upFresh w n hc 1 false) = upFresh w n hc 0 true := by
  have ht := StageRotation.step_up (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl)
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have hh := StageRotation.up_new (kmswStage w n).nextEdge (stageRot w n)
    (⟨(kmswStage w n).active, (act_lt_nextEdge w (le_refl n))⟩, false)
    (⟨(kmswStage w n).active, (act_lt_nextEdge w (le_refl n))⟩, true)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    have he := unresize_eval _ _ _ ht
    first
    | have he' := he (StageRotation.allocation _ 2 (.inr (0, false)))
      rw [hh.1] at he'
      split_ifs at he' ⊢ <;>
        simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, upFresh] using he'
    | have he' := he (StageRotation.allocation _ 2 (.inr (1, true)))
      rw [hh.2.1] at he'
      simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, upFresh] using he'
    | have he' := he (StageRotation.allocation _ 2 (.inr (0, true)))
      rw [hh.2.2.1] at he'
      simpa [StageRotation.allocation, upFresh] using he'
    | have he' := he (StageRotation.allocation _ 2 (.inr (1, false)))
      rw [hh.2.2.2] at he'
      simpa [StageRotation.allocation, upFresh] using he'

private theorem up_dart_cases (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    (∃ e, d = stageDartIncl w n e) ∨
      d = upFresh w n hc 0 false ∨ d = upFresh w n hc 0 true ∨
      d = upFresh w n hc 1 false ∨ d = upFresh w n hc 1 true := by
  rcases d with ⟨i, b⟩
  by_cases hi : i.val < (kmswStage w n).nextEdge
  · exact Or.inl ⟨(⟨i.val, hi⟩, b), rfl⟩
  · have hh := (up_counts w n hc).1
    have hib := i.isLt
    have hcases : i.val = (kmswStage w n).nextEdge ∨
        i.val = (kmswStage w n).nextEdge + 1 := by omega
    right
    rcases hcases with hi | hi <;> cases b
    · exact Or.inl (Prod.ext (Fin.ext (by simpa [upFresh] using hi)) rfl)
    · exact Or.inr (Or.inl (Prod.ext (Fin.ext (by simpa [upFresh] using hi)) rfl))
    · exact Or.inr (Or.inr (Or.inl
        (Prod.ext (Fin.ext (by simpa [upFresh] using hi)) rfl)))
    · exact Or.inr (Or.inr (Or.inr
        (Prod.ext (Fin.ext (by simpa [upFresh] using hi)) rfl)))

private theorem up_fresh_endpoints (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (stageVertex w (n + 1) (upFresh w n hc 0 false)).val =
        (kmswStage w n).west (kmswStage w n).active ∧
      (stageVertex w (n + 1) (upFresh w n hc 0 true)).val =
        (kmswStage w n).nextVertex ∧
      (stageVertex w (n + 1) (upFresh w n hc 1 false)).val =
        (kmswStage w n).nextVertex ∧
      (stageVertex w (n + 1) (upFresh w n hc 1 true)).val =
        (kmswStage w n).east (kmswStage w n).active := by
  simpa only [stageVertex, stageEndpoint, upFresh, Fin.val_zero, Fin.val_one,
    Nat.add_zero, Bool.false_eq_true, ↓reduceIte] using up_endpoints w n hc

private theorem up_mid_star (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (upFresh w n hc 0 true)} =
      {upFresh w n hc 0 true, upFresh w n hc 1 false} := by
  obtain ⟨hu, hp, hq, hv⟩ := up_fresh_endpoints w n hc
  have he := kmswStage_endpoints_lt_nextVertex w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  ext f
  constructor
  · intro hf
    have hval := congrArg Fin.val hf
    rw [hp] at hval
    rcases up_dart_cases w n hc f with ⟨e, rfl⟩ | rfl | rfl | rfl | rfl
    · rw [stageVertex_incl_eq] at hval
      have hb := (stageVertex w n e).isLt
      change (stageVertex w n e).val = _ at hval
      omega
    · rw [hu] at hval
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [hv] at hval
      omega
  · rintro (rfl | rfl)
    · rfl
    · exact Fin.ext (hq.trans hp.symm)

private theorem up_star_unaffected (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (d : StageDart (kmswStage w n).nextEdge)
    (hu : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (upFresh w n hc 0 false))
    (hv : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (upFresh w n hc 1 true)) :
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} =
      {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} := by
  ext f
  constructor
  · intro hf
    refine ⟨?_, hf⟩
    rcases up_dart_cases w n hc f with ⟨e, rfl⟩ | rfl | rfl | rfl | rfl
    · exact e.1.isLt
    · exact False.elim (hu hf.symm)
    · have hh := congrArg Fin.val hf
      rw [(up_fresh_endpoints w n hc).2.1, stageVertex_incl_eq] at hh
      have hb := (stageVertex w n d).isLt
      change _ = (stageVertex w n d).val at hh
      omega
    · have hh := congrArg Fin.val hf
      rw [(up_fresh_endpoints w n hc).2.2.1, stageVertex_incl_eq] at hh
      have hb := (stageVertex w n d).isLt
      change _ = (stageVertex w n d).val at hh
      omega
    · exact False.elim (hv hf.symm)
  · exact fun hf => hf.2

private theorem pair_successor {D : Type*} (dir : D → ℂ) (a b : D) (hne : a ≠ b) :
    CcwSuccessor {a, b} dir a b := by
  refine ⟨(Set.finite_singleton b).insert a, Or.inl rfl, Or.inr rfl,
    Or.inr ⟨hne.symm, ?_⟩⟩
  rintro f (rfl | rfl) hf
  · exact False.elim (hf rfl)
  · exact le_rfl

private theorem up_preserve_old {w : ℕ → Fin 3} {n : ℕ} (hc : w n = 1)
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
  apply successor_insert_other _ _ _ _ (stageDartIncl w n p) x
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
    exact hab (layoutGood_succ_up_initial_arg_injective w n hc G a b
      (ha.trans hb.symm) harg)

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. Rotation agreement for the up step of `def-kmsw`, -/
theorem layoutGood_succ_up_rotation_agreement (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
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
  let x := upFresh w n hc 0 false
  let y := upFresh w n hc 1 true
  have he : e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    simp [e, hes]
  have hx : x.1.val ∈ freshEdges w n := by
    apply Finset.mem_Ico.mpr
    have hh := (up_counts w n hc).1
    dsimp [x, upFresh]
    omega
  have hy : y.1.val ∈ freshEdges w n := by
    apply Finset.mem_Ico.mpr
    have hh := (up_counts w n hc).1
    dsimp [y, upFresh]
    omega
  have hxv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n a) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact (up_fresh_endpoints w n hc).1
  have hyv : stageVertex w (n + 1) y =
      stageVertex w (n + 1) (stageDartIncl w n A) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact (up_fresh_endpoints w n hc).2.2.2
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
  have hE := G.east_roof_insertion_successors e he x hx rfl hxv
  have hW := G.west_roof_insertion_successors e he y hy rfl (by
    rintro ⟨hh, _, _⟩
    rw [hc] at hh
    cases hh) hyv
  have hr := up_rotation_new w n hc
  change stageRot w (n + 1) x =
      (if stageRot w n a = A then y else stageDartIncl w n (stageRot w n a)) ∧
    stageRot w (n + 1) y = stageDartIncl w n A ∧ _ at hr
  rw [ite_eq_right hrot] at hr
  have hrold (d : StageDart (kmswStage w n).nextEdge) :
      stageRot w (n + 1) (stageDartIncl w n d) =
        if d = a then x else if stageRot w n d = A then y
          else stageDartIncl w n (stageRot w n d) := up_rotation_old w n hc d
  intro d
  rcases up_dart_cases w n hc d with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
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
        · exact up_preserve_old hc G d a x hx hdu hda hE.1
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
            exact up_preserve_old hc G d p y hy hv hdp hW'
          · rw [up_star_unaffected w n hc d
              (fun hh => hdu (hh.trans hxv)) (fun hh => hdv (hh.trans hyv))]
            exact G.old_star_rotation_agreement d
  · rw [hr.1]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) x}
      (fun f => (layoutDart w (n + 1) f).initialDirection) x _
    rw [hxv]
    exact hE.2
  · rw [hr.2.2.1, up_mid_star]
    exact pair_successor _ _ _ (by
      intro hh
      have hv := congrArg (fun f => f.1.val) hh
      change (kmswStage w n).nextEdge + 0 = (kmswStage w n).nextEdge + 1 at hv
      omega)
  · rw [hr.2.2.2]
    have hv : stageVertex w (n + 1) (upFresh w n hc 1 false) =
        stageVertex w (n + 1) (upFresh w n hc 0 true) :=
      Fin.ext ((up_fresh_endpoints w n hc).2.2.1.trans
        (up_fresh_endpoints w n hc).2.1.symm)
    rw [hv, up_mid_star, Set.pair_comm]
    exact pair_successor _ _ _ (by
      intro hh
      have heq := congrArg (fun f => f.1.val) hh
      change (kmswStage w n).nextEdge + 1 = (kmswStage w n).nextEdge + 0 at heq
      omega)
  · rw [hr.2.1]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) y}
      (fun f => (layoutDart w (n + 1) f).initialDirection) y _
    rw [hyv]
    exact hW.2

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. The good layout for the up step of `def-kmsw`, -/
theorem layoutGood_succ_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) : LayoutGood w (n + 1) where
  interior_disjoint := layoutGood_succ_up_interior_disjoint w n hc G
  interior_avoids_vertices := layoutGood_succ_up_interior_avoids_vertices w n hc G
  initial_arg_injective := layoutGood_succ_up_initial_arg_injective w n hc G
  rotation_agreement := layoutGood_succ_up_rotation_agreement w n hc G

end DirectedDistances.KMSW
