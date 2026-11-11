module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.StageRotation
public import DirectedDistances.PlanarMap.SlopeAngularOrder
import DirectedDistances.KMSW.MonotoneStepCommon

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
In the pendant branch, the new edge joins the active east
endpoint to the new vertex, and that vertex is placed one rank unit to its right. -/
theorem pen_step_geometry (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 ∧
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 ∧
    (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge) =
      (kmswStage w n).east (kmswStage w n).active ∧
    (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge) =
      (kmswStage w n).nextVertex ∧
    kmswStageRank w (n + 1) ((kmswStage w n).nextVertex) =
      kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR,
    State.addEdge, kmswStageRank]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The pendant vertex has the new top height. -/
theorem pen_new_vertex_height (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    (layoutPos w (n + 1) ((kmswStage w n).nextVertex)).im =
      (n + 1 : ℝ) := by
  have hgrow : (kmswStage w (n + 1)).nextVertex =
      (kmswStage w n).nextVertex + 1 := (pen_step_geometry w n hc hUR).2.1
  change layoutHeight w (n + 1) ((kmswStage w n).nextVertex) =
    (n + 1 : ℝ)
  simpa only [Nat.cast_add, Nat.cast_one] using
    layoutHeight_created_vertex w n hgrow

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The old upper trace ends no farther right than the active
east endpoint when UR is empty. See `def-kmsw`, -/
theorem pen_upper_bound (w : ℕ → Fin 3) (n : ℕ)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    G.xmax ≤ (layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active)).re := by
  let s := kmswStage w n
  have hULne : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  have hlast : s.UL.getLast hULne = s.active := by
    have h := (kmswStage_UL_nonempty_active_last w n).2
    rw [List.getLast?_eq_getLast_of_ne_nil hULne] at h
    exact Option.some.inj h
  have hchain : List.IsChain (fun e f => s.east e = s.west f) s.UL := by
    simpa [WestEastChain, hUR] using
      (kmswStage_boundary_chain_invariant w n).1
  have hbound : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp [s, hUR, he]
  have hchain' : List.IsChain
      (fun e f => e ∈ s.UL ∧ f ∈ s.UL ∧ s.east e = s.west f) s.UL :=
    (List.IsChain.iff_mem (R := fun e f => s.east e = s.west f)).mp hchain
  have hrank : ∀ e ∈ s.UL,
      kmswStageRank w n (s.east e) ≤ kmswStageRank w n (s.east s.active) := by
    apply hchain'.backwards_induction
      (fun e => kmswStageRank w n (s.east e) ≤
        kmswStageRank w n (s.east s.active))
    · intro e f hef hf
      have hs := kmswStageRank_strict w n f (hbound f hef.2.1)
      have hadj : kmswStageRank w n (s.east e) <
          kmswStageRank w n (s.east f) := by
        rw [hef.2.2]
        exact hs
      exact hadj.le.trans hf
    · intro hne
      rw [hlast]
  have hpoint :
      (⟨G.xmax, G.upper G.xmax⟩ : ℂ) ∈ graphOver G.xmin G.xmax G.upper := by
    simp [graphOver, G.hx]
  rw [G.upper_trace] at hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨e, hpoint⟩
  rcases Set.mem_iUnion.mp hpoint with ⟨he, hz⟩
  have he' : e ∈ s.UL := by simpa [s, hUR] using he
  have hb := hbound e he'
  have hz' : (⟨G.xmax, G.upper G.xmax⟩ : ℂ) ∈ (layoutArc w n e).image := by
    have harc := G.arc_layout ((⟨e, hb⟩, false))
    simp only [Bool.false_eq_true, ↓reduceIte] at harc
    have hz0 := hz
    simp only [stageEdgeTrace, s, dite_eq_left hb] at hz0
    rw [harc] at hz0
    exact hz0
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n e hb
  rw [hf] at hz'
  have hx := hz'.2.1
  have hxe : (layoutPos w n (s.east e)).re ≤
      (layoutPos w n (s.east s.active)).re := by
    change (kmswStageRank w n (s.east e) : ℝ) ≤
      (kmswStageRank w n (s.east s.active) : ℝ)
    exact_mod_cast hrank e he'
  change G.xmax ≤ (layoutPos w n (s.east s.active)).re
  exact hx.trans (hxe)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The old image lies at or left of the active east endpoint. -/
theorem pen_old_image_bound (w : ℕ → Fin 3) (n : ℕ)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) {z : ℂ} (hz : z ∈ P.image) :
    z.re ≤ (layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active)).re := by
  have hzRegion : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact Or.inl hz
  exact hzRegion.2.1.trans (pen_upper_bound w n hUR G)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
Every old vertex lies at or left of the active east endpoint. -/
theorem pen_old_vertex_bound (w : ℕ → Fin 3) (n : ℕ)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (v : Fin (kmswStage w n).nextVertex) :
    (layoutPos w n v.val).re ≤ (layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active)).re := by
  have hvImage : P.pos v ∈ P.image := by
    change P.pos v ∈ Set.range P.pos ∪ _
    exact Or.inl ⟨v, rfl⟩
  have hvLayout : P.pos v = layoutPos w n v.val := G.pos_layout v
  rw [hvLayout] at hvImage
  exact pen_old_image_bound w n hUR G hvImage

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

private theorem dart_interior (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (layoutDart w n d).interior = (layoutArc w n d.1.val).interior := by
  unfold layoutDart
  split
  · exact reverse_interior _
  · rfl

private theorem arc_subset_old_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutArc w n e).image ⊆ P.image := by
  intro z hz
  apply Or.inr
  refine ⟨(⟨e, he⟩, false), ?_⟩
  simpa only [G.arc_layout, Bool.false_eq_true, ↓reduceIte] using hz

private theorem pen_fresh_edge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    (kmswStage w n).nextEdge ∈ freshEdges w n := by
  have hcount := (pen_step_geometry w n hc hUR).1
  rw [freshEdges, hcount]
  exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩

private theorem pen_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge) =
        (kmswStage w n).east (kmswStage w n).active ∧
      (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge) =
        (kmswStage w n).nextVertex := by
  exact ⟨(pen_step_geometry w n hc hUR).2.2.1,
    (pen_step_geometry w n hc hUR).2.2.2.1⟩

private theorem pen_new_endpoint_positions (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    layoutPos w (n + 1) ((kmswStage w (n + 1)).west
        ((kmswStage w n).nextEdge)) =
      layoutPos w n ((kmswStage w n).east (kmswStage w n).active) ∧
    layoutPos w (n + 1) ((kmswStage w (n + 1)).east
        ((kmswStage w n).nextEdge)) =
      layoutPos w (n + 1) ((kmswStage w n).nextVertex) := by
  obtain ⟨hwest, heast⟩ := pen_endpoints w n hc hUR
  have hv := (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
    (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [hwest, layoutPos_old_vertex w n _ hv, heast]
  exact ⟨rfl, rfl⟩

private theorem layoutArc_succ_pen (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge) =
      roofArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west
        ((kmswStage w n).nextEdge)))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east
        ((kmswStage w n).nextEdge))) (n + 1) (rampSlope w n) := by
  have hm : ¬ isFreshLeftMissing w n ((kmswStage w n).nextEdge) := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n _ (pen_fresh_edge w n hc hUR), ite_eq_right hm]

private theorem pen_new_interior_right_bound (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) {z : ℂ}
    (hz : z ∈ (layoutArc w (n + 1) ((kmswStage w n).nextEdge)).interior) :
    (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re < z.re := by
  rw [layoutArc_succ_pen w n hc hUR] at hz
  obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n
    _ (pen_fresh_edge w n hc hUR)
  rw [roofArc_interior (rampSlope_pos w n) ha hb
    (freshEdges_ramp_widths_lt w n _ (pen_fresh_edge w n hc hUR))] at hz
  rw [(pen_new_endpoint_positions w n hc hUR).1] at hz
  exact hz.1

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The interior-disjointness field for the pendant branch. -/
theorem layoutGood_succ_pen_interior_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d e : StageDart (kmswStage w (n + 1)).nextEdge,
      e ≠ d → e ≠ edgeFlip _ d →
        Disjoint (layoutDart w (n + 1) d).interior
          (layoutDart w (n + 1) e).interior := by
  intro d e hne hflip
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
        apply hflip
        exact congrArg (stageDartIncl w n) h
    · rw [dart_interior, dart_interior, layoutArc_old w n d.1.val hd]
      apply Set.disjoint_left.mpr
      intro z hzd hze
      have hcount := (pen_step_geometry w n hc hUR).1
      have hval : e.1.val = (kmswStage w n).nextEdge := by
        have he := e.1.isLt
        simp only [hcount] at he
        omega
      rw [hval] at hze
      have hleft := pen_old_image_bound w n hUR G
        (arc_subset_old_image G d.1.val hd hzd.1)
      exact (not_lt_of_ge hleft) (pen_new_interior_right_bound w n hc hUR hze)
  · by_cases he : e.1.val < (kmswStage w n).nextEdge
    · rw [dart_interior, dart_interior, layoutArc_old w n e.1.val he]
      apply Set.disjoint_left.mpr
      intro z hzd hze
      have hcount := (pen_step_geometry w n hc hUR).1
      have hval : d.1.val = (kmswStage w n).nextEdge := by
        have hd' := d.1.isLt
        simp only [hcount] at hd'
        omega
      rw [hval] at hzd
      have hleft := pen_old_image_bound w n hUR G
        (arc_subset_old_image G e.1.val he hze.1)
      exact (not_lt_of_ge hleft) (pen_new_interior_right_bound w n hc hUR hzd)
    · have hcount := (pen_step_geometry w n hc hUR).1
      have hnew : d.1.val = (kmswStage w n).nextEdge ∧
          e.1.val = (kmswStage w n).nextEdge := by
        have hdlt := d.1.isLt
        have helt := e.1.isLt
        simp only [hcount] at hdlt helt
        omega
      have hdiff : e.1.val ≠ d.1.val := by
        intro hv
        have hfin : e.1 = d.1 := Fin.ext hv
        rcases d with ⟨di, db⟩
        rcases e with ⟨ei, eb⟩
        dsimp only at hfin
        subst ei
        cases db <;> cases eb <;>
          first | exact hne rfl | exact hflip rfl
      exact False.elim (hdiff (hnew.2.trans hnew.1.symm))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The vertex-avoidance field for the pendant branch. -/
theorem layoutGood_succ_pen_interior_avoids_vertices (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
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
      exact (layoutGood_of_invariant G).interior_avoids_vertices d0
        ⟨v.val, hv⟩
    · have hb := v.isLt
      simp only [(pen_step_geometry w n hc hUR).2.1] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq, dart_interior]
      intro hz
      have him := G.image_height_le _
        (arc_subset_old_image G d.1.val hd hz.1)
      rw [pen_new_vertex_height w n hc hUR] at him
      linarith
  · have hdfresh : d.1.val ∈ freshEdges w n :=
      Finset.mem_Ico.mpr ⟨by omega, d.1.isLt⟩
    clear hdfresh
    rw [dart_interior]
    have hcount := (pen_step_geometry w n hc hUR).1
    have hlt := d.1.isLt
    simp only [hcount] at hlt
    have hval : d.1.val = (kmswStage w n).nextEdge := by omega
    by_cases hv : v.val < (kmswStage w n).nextVertex
    · intro hz
      rw [hval] at hz
      have hbound := pen_old_vertex_bound w n hUR G ⟨v.val, hv⟩
      have hnew := pen_new_interior_right_bound w n hc hUR hz
      rw [layoutPos_old_vertex w n v.val hv] at hnew
      exact (not_lt_of_ge hbound)
        hnew
    · have hb := v.isLt
      simp only [(pen_step_geometry w n hc hUR).2.1] at hb
      have heq : v.val = (kmswStage w n).nextVertex := by omega
      rw [heq]
      intro hz
      have he := d.1.isLt
      simp only [(pen_step_geometry w n hc hUR).1] at he
      have hval : d.1.val = (kmswStage w n).nextEdge := by omega
      rw [hval] at hz
      have hfinish := layoutArc_finish w (n + 1) d.1.val d.1.isLt
      rw [hval, (pen_endpoints w n hc hUR).2] at hfinish
      apply hz.2
      exact Or.inr hfinish.symm

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
    (d : StageDart (kmswStage w m).nextEdge) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (layoutDart w m d).start + t • (layoutDart w m d).initialDirection ∈
      (layoutDart w m d).interior := by
  have hp := layoutArc_points_pairwise w m d.1.val d.1.isLt
  have hl := arc_length w m d.1.val
  have hlast : (layoutArc w m d.1.val).points.length - 1 <
      (layoutArc w m d.1.val).points.length := by omega
  rcases d with ⟨e, b⟩
  change 2 ≤ (layoutArc w m e.val).points.length at hl
  cases b
  · apply ray_interior _ hl
      (Or.inl ⟨Polyline.initialDirection_re_pos hp hl, ?_⟩) t ht ht1
    rw [← Polyline.point_last_eq_finish]
    exact Polyline.point_re_le_of_le (p := layoutArc w m e.val) hp
      (by omega) hlast
  · apply ray_interior _
      (by simpa only [layoutDart, ↓reduceIte, Polyline.reverse,
        List.length_reverse] using hl)
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

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The distinct-initial-arguments field for the pendant -/
theorem layoutGood_succ_pen_initial_arg_injective (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d e : StageDart (kmswStage w (n + 1)).nextEdge,
      stageVertex w (n + 1) d = stageVertex w (n + 1) e →
      Complex.arg (layoutDart w (n + 1) d).initialDirection =
        Complex.arg (layoutDart w (n + 1) e).initialDirection → d = e := by
  intro d e hv ha
  by_contra hne
  have hflip : e ≠ edgeFlip _ d := by
    intro h
    have hstart := congrArg (fun v => layoutPos w (n + 1) v.val) hv
    rcases d with ⟨di, db⟩
    subst e
    have hstrict := kmswStageRank_strict w (n + 1) di.val di.isLt
    have hneq :
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west di.val)).re ≠
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
  exact Set.disjoint_left.mp
    (layoutGood_succ_pen_interior_disjoint w n hc hUR G d e
      (Ne.symm hne) hflip) hz0 hz1

private theorem pen_unresize_eval {k l : ℕ} (h : k = l)
    (τ : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (ht : StageRotation.resize h τ = σ) (d : StageDart l) :
    τ (Fin.cast h.symm d.1, d.2) =
      (Fin.cast h.symm (σ d).1, (σ d).2) := by
  cases h
  exact congrArg (fun ρ => ρ d) ht

private theorem pen_rotation_old (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    (d : StageDart (kmswStage w n).nextEdge) :
    stageRot w (n + 1) (stageDartIncl w n d) =
      if stageRot w n d =
          ((⟨(kmswStage w n).active,
            (kmswStage_boundary_ids_lt_nextEdge w n).1⟩ :
              Fin (kmswStage w n).nextEdge), true) then
        (⟨(kmswStage w n).nextEdge,
          by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false)
      else stageDartIncl w n (stageRot w n d) := by
  let A : StageDart (kmswStage w n).nextEdge :=
    (⟨(kmswStage w n).active,
      (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true)
  let x : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨(kmswStage w n).nextEdge,
      by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false)
  have ht := StageRotation.step_pendant (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl) hUR
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have he := pen_unresize_eval _ _ _ ht
    (StageRotation.allocation (kmswStage w n).nextEdge 1 (.inl d))
  rw [StageRotation.pendant_old] at he
  split_ifs at he ⊢ <;>
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, A, x] using he

private theorem pen_rotation_new (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    let x : StageDart (kmswStage w (n + 1)).nextEdge :=
      (⟨(kmswStage w n).nextEdge,
        by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false)
    let y : StageDart (kmswStage w (n + 1)).nextEdge :=
      (⟨(kmswStage w n).nextEdge,
        by have h := (pen_step_geometry w n hc hUR).1; omega⟩, true)
    stageRot w (n + 1) x = stageDartIncl w n
        ((⟨(kmswStage w n).active,
          (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true) :
          StageDart (kmswStage w n).nextEdge) ∧
      stageRot w (n + 1) y = y := by
  let x : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨(kmswStage w n).nextEdge,
      by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false)
  let y : StageDart (kmswStage w (n + 1)).nextEdge := (x.1, true)
  let A : StageDart (kmswStage w n).nextEdge :=
    (⟨(kmswStage w n).active,
      (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true)
  have ht := StageRotation.step_pendant (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by simp only [hc, kmswCodeStep]; rfl) hUR
  change StageRotation.resize _ (stageRot w (n + 1)) = _ at ht
  have hn := StageRotation.pendant_new (kmswStage w n).nextEdge
    (stageRot w n) A
  have hx := pen_unresize_eval _ _ _ ht
    (StageRotation.allocation (kmswStage w n).nextEdge 1 (.inr (0, false)))
  have hy := pen_unresize_eval _ _ _ ht
    (StageRotation.allocation (kmswStage w n).nextEdge 1 (.inr (0, true)))
  rw [hn.1] at hx
  rw [hn.2] at hy
  constructor
  · simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, x, A] using hx
  · simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, y, x] using hy

private theorem pen_fresh_vertex_eq (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    stageVertex w (n + 1)
        (⟨⟨(kmswStage w n).nextEdge,
          by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false⟩) =
        stageVertex w (n + 1)
          (stageDartIncl w n
            ((⟨(kmswStage w n).active,
              (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true))) ∧
      (stageVertex w (n + 1)
        (⟨⟨(kmswStage w n).nextEdge,
          by have h := (pen_step_geometry w n hc hUR).1; omega⟩, true⟩)).val =
        (kmswStage w n).nextVertex := by
  have hp := pen_endpoints w n hc hUR
  constructor
  · apply Fin.ext
    rw [stageVertex_incl_eq]
    simpa [stageVertexIncl, stageVertex, stageEndpoint] using hp.1
  · simpa only [stageVertex, stageEndpoint, ↓reduceIte] using hp.2

private theorem pen_old_vertex_star (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    (d : StageDart (kmswStage w n).nextEdge)
    (haway : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1)
        (⟨⟨(kmswStage w n).nextEdge,
          by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false⟩)) :
    {f : StageDart (kmswStage w (n + 1)).nextEdge |
      stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n d)} =
      {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f =
            stageVertex w (n + 1) (stageDartIncl w n d)} := by
  ext f
  constructor
  · intro hf
    by_cases hold : f.1.val < (kmswStage w n).nextEdge
    · exact ⟨hold, hf⟩
    · have hcount := (pen_step_geometry w n hc hUR).1
      have heq : f.1.val = (kmswStage w n).nextEdge := by
        have hlt := f.1.isLt
        simp only [hcount] at hlt
        omega
      have hval := congrArg Fin.val hf
      have hdold : (stageVertex w (n + 1)
          (stageDartIncl w n d)).val < (kmswStage w n).nextVertex := by
        rw [stageVertex_incl_eq]
        exact (stageVertex w n d).isLt
      cases hb : f.2
      · exact False.elim (haway (by
          apply Fin.ext
          simpa [stageVertex, stageEndpoint, heq, hb] using hval.symm))
      · have hq := (pen_fresh_vertex_eq w n hc hUR).2
        have hnew : (stageVertex w (n + 1) f).val =
            (kmswStage w n).nextVertex := by
          simpa [stageVertex, stageEndpoint, heq, hb] using hq
        omega
  · rintro ⟨_, hf⟩
    exact hf

private theorem pen_west_slope_arg_eq {u v : ℂ}
    (hu : u.re < 0) (hv : v.re < 0)
    (heq : u.im / u.re = v.im / v.re) : Complex.arg u = Complex.arg v := by
  have hc := (div_eq_div_iff hu.ne hv.ne).mp heq
  have huv : u = ((u.re / v.re : ℝ) : ℂ) * v := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      field_simp [hv.ne]
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      field_simp [hv.ne]
      nlinarith only [hc]
  rw [huv]
  exact Complex.arg_real_mul v (div_pos_of_neg_of_neg hu hv)

private theorem pen_predecessor_max_slope {D : Type*} (star : Set D)
    (dir : D → ℂ) (p a : D) (hold : CcwSuccessor star dir p a)
    (hargs : ∀ x ∈ star, ∀ y ∈ star, x ≠ y →
      Complex.arg (dir x) ≠ Complex.arg (dir y))
    (hp : p ∈ star) (ha : a ∈ star)
    (hpWest : (dir p).re < 0) (haWest : (dir a).re < 0)
    (hmin : ∀ f ∈ star, (dir f).re < 0 →
      f = a ∨ (dir a).im / (dir a).re < (dir f).im / (dir f).re) :
    ∀ f ∈ star, (dir f).re < 0 →
      f = p ∨ (dir f).im / (dir f).re < (dir p).im / (dir p).re := by
  intro f hf hfw
  by_cases hfp : f = p
  · exact Or.inl hfp
  · right
    by_contra hnot
    have hpf : (dir p).im / (dir p).re ≤ (dir f).im / (dir f).re :=
      le_of_not_gt hnot
    have hneq : (dir p).im / (dir p).re ≠ (dir f).im / (dir f).re := by
      intro heq
      have harg := pen_west_slope_arg_eq hpWest hfw heq
      exact hargs p hp f hf (Ne.symm hfp) harg
    have hpf' : (dir p).im / (dir p).re < (dir f).im / (dir f).re :=
      lt_of_le_of_ne hpf hneq
    have hpa : a ≠ p := by
      intro h
      subst a
      rcases hold.2.2.2 with hsingle | hcase
      · have : f = p := by simpa [hsingle.2] using hf
        exact hfp this
      · exact hcase.1 rfl
    have haSlope := hmin p hp hpWest
    have haP : (dir a).im / (dir a).re < (dir p).im / (dir p).re := by
      rcases haSlope with h | h
      · exact False.elim (hpa h.symm)
      · exact h
    have hpaTurn := west_west_turn_formula haWest hpWest haP
    have hpfTurn := west_west_turn_formula hpWest hfw hpf'
    have hrev := ccwTurn_add_reverse (dir p) (dir a)
      (hargs p hp a ha hpa.symm)
    have hAF : a ≠ f := by
      intro h
      subst f
      have hAp := hmin p hp hpWest
      rcases hAp with h | h
      · exact hpa h.symm
      · exact (not_lt_of_ge (le_of_lt hpf')) h
    have hargsAF : Complex.arg (dir a) ≠ Complex.arg (dir f) :=
      hargs a ha f hf hAF
    have hboundsP := Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (show 0 < (-dir p).re by simpa using neg_pos.mpr hpWest))
    have hboundsA := Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (show 0 < (-dir a).re by simpa using neg_pos.mpr haWest))
    have hboundsF := Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (show 0 < (-dir f).re by simpa using neg_pos.mpr hfw))
    have hbetween : CcwBetween (dir p) (dir f) (dir a) := by
      unfold CcwBetween
      have hpaFromReverse : ccwTurn (dir p) (dir a) =
          2 * Real.pi - ccwTurn (dir a) (dir p) := by linarith [hrev]
      rw [hpfTurn, hpaFromReverse, hpaTurn]
      have hA := (abs_lt.mp hboundsA).1
      have hF := (abs_lt.mp hboundsF).2
      linarith [Real.pi_pos]
    have hno := (ccwSuccessor_iff_no_between star dir p a
      hold.1 hp).mp hold
    rcases hno with hsingle | ⟨_, _, hno⟩
    · have hfp' : f = p := by simpa [hsingle.2] using hf
      exact hfp hfp'
    · exact hno f hf hfp hAF.symm hbetween

private theorem pen_no_between_old_link {D : Type*} (star : Set D)
    (dir : D → ℂ) (d g p a x : D)
    (hold : CcwSuccessor star dir d g)
    (hargs : ∀ u ∈ star, ∀ v ∈ star, u ≠ v →
      Complex.arg (dir u) ≠ Complex.arg (dir v))
    (hd : d ∈ star) (hg : g ∈ star) (hp : p ∈ star) (ha : a ∈ star)
    (hdp : d ≠ p)
    (hdWest : (dir d).re < 0) (hgWest : (dir g).re < 0)
    (hpWest : (dir p).re < 0) (haWest : (dir a).re < 0)
    (hxEast : 0 < (dir x).re)
    (hmin : ∀ f ∈ star, (dir f).re < 0 →
      f = a ∨ (dir a).im / (dir a).re < (dir f).im / (dir f).re)
    (hmax : ∀ f ∈ star, (dir f).re < 0 →
      f = p ∨ (dir f).im / (dir f).re < (dir p).im / (dir p).re) :
    ¬ CcwBetween (dir d) (dir x) (dir g) := by
  intro hbetween
  have hdg : d ≠ g := by
    intro heq
    subst g
    rcases hold.2.2.2 with hsingle | hcase
    · have hdp' : p = d := by simpa [hsingle.2] using hp
      exact hdp hdp'.symm
    · exact hcase.1 rfl
  have hslopeNe : (dir d).im / (dir d).re ≠
      (dir g).im / (dir g).re := by
    intro heq
    exact hargs d hd g hg hdg (pen_west_slope_arg_eq hdWest hgWest heq)
  have hthetaX := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxEast)
  have hthetaG := Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < (-dir g).re by simpa using neg_pos.mpr hgWest))
  by_cases hdgSlope : (dir d).im / (dir d).re < (dir g).im / (dir g).re
  · have hdx := west_east_turn_formula hdWest hxEast
    have hdgTurn := west_west_turn_formula hdWest hgWest hdgSlope
    have hxlow := (abs_lt.mp hthetaX).1
    have hghigh := (abs_lt.mp hthetaG).2
    unfold CcwBetween at hbetween
    rw [hdx, hdgTurn] at hbetween
    linarith [Real.pi_pos]
  · have hgdSlope : (dir g).im / (dir g).re <
        (dir d).im / (dir d).re :=
      lt_of_le_of_ne (le_of_not_gt hdgSlope) (Ne.symm hslopeNe)
    by_cases hga : g = a
    · subst g
      have hda : d ≠ a := by
        intro h
        subst d
        exact (lt_irrefl _) hgdSlope
      have haD : (dir a).im / (dir a).re < (dir d).im / (dir d).re := by
        rcases hmin d hd hdWest with h | h
        · exact False.elim (hda h)
        · exact h
      have hdpSlope : (dir d).im / (dir d).re <
          (dir p).im / (dir p).re := by
        rcases hmax d hd hdWest with h | h
        · exact False.elim (hdp h)
        · exact h
      have hADTurn := west_west_turn_formula haWest hdWest haD
      have hDPTurn := west_west_turn_formula hdWest hpWest hdpSlope
      have hrevDA := ccwTurn_add_reverse (dir d) (dir a)
        (hargs d hd a ha hda)
      have hturnDA : ccwTurn (dir d) (dir a) =
          2 * Real.pi - ccwTurn (dir a) (dir d) := by linarith [hrevDA]
      have hturnDP : ccwTurn (dir d) (dir p) =
          Complex.arg (-dir p) - Complex.arg (-dir d) := hDPTurn
      have hturnDA' : ccwTurn (dir d) (dir a) =
          2 * Real.pi - (Complex.arg (-dir d) - Complex.arg (-dir a)) := by
        rw [hturnDA, hADTurn]
      have hthetaP := Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (show 0 < (-dir p).re by simpa using neg_pos.mpr hpWest))
      have hthetaA := Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (show 0 < (-dir a).re by simpa using neg_pos.mpr haWest))
      have hPin : CcwBetween (dir d) (dir p) (dir a) := by
        unfold CcwBetween
        rw [hturnDP, hturnDA']
        linarith [(abs_lt.mp hthetaP).2, (abs_lt.mp hthetaA).1, Real.pi_pos]
      have hno := (ccwSuccessor_iff_no_between star dir d a hold.1 hd).mp hold
      rcases hno with hsingle | ⟨_, _, hno⟩
      · have hdp' : p = d := by simpa [hsingle.2] using hp
        exact hdp hdp'.symm
      · have hpa : p ≠ a := by
          intro h
          subst a
          exact (not_lt_of_ge (le_of_lt hdpSlope)) haD
        exact hno p hp hdp.symm hpa hPin
    · have hgaSlope := hmin g hg hgWest
      have haG : (dir a).im / (dir a).re < (dir g).im / (dir g).re := by
        rcases hgaSlope with heq | hlt
        · exact False.elim (hga heq)
        · exact hlt
      have haD : (dir a).im / (dir a).re < (dir d).im / (dir d).re :=
        haG.trans hgdSlope
      have hpaTurn := west_west_turn_formula haWest hdWest haD
      have hgdTurn := west_west_turn_formula hgWest hdWest hgdSlope
      have hrevDG := ccwTurn_add_reverse (dir d) (dir g) (by
        intro h
        exact hargs d hd g hg hdg h)
      by_cases hda : d = a
      · subst d
        have hturnDX := west_east_turn_formula haWest hxEast
        have hturnDG := west_west_turn_formula haWest hgWest haG
        have hxlow := (abs_lt.mp hthetaX).1
        have hghigh := (abs_lt.mp hthetaG).2
        unfold CcwBetween at hbetween
        rw [hturnDX, hturnDG] at hbetween
        linarith [Real.pi_pos]
      · have hrevDA := ccwTurn_add_reverse (dir d) (dir a)
          (hargs d hd a ha hda)
        have hturnDA : ccwTurn (dir d) (dir a) =
            2 * Real.pi - ccwTurn (dir a) (dir d) := by linarith [hrevDA]
        have hturnDG : ccwTurn (dir d) (dir g) =
            2 * Real.pi - ccwTurn (dir g) (dir d) := by linarith [hrevDG]
        have hAin : CcwBetween (dir d) (dir a) (dir g) := by
          have hthetaOrder := (west_slope_order haWest hgWest).2 haG
          unfold CcwBetween
          rw [hturnDA, hturnDG]
          rw [hpaTurn, hgdTurn]
          linarith only [hthetaOrder]
        have hno := (ccwSuccessor_iff_no_between star dir d g hold.1 hd).mp hold
        rcases hno with hsingle | ⟨_, _, hno⟩
        · have hdp' : p = d := by simpa [hsingle.2] using hp
          exact hdp hdp'.symm
        · exact hno a ha (fun h => hda h.symm) (fun h => hga h.symm) hAin

private theorem pen_new_vertex_star (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    let y : StageDart (kmswStage w (n + 1)).nextEdge :=
      (⟨(kmswStage w n).nextEdge,
        by have h := (pen_step_geometry w n hc hUR).1; omega⟩, true)
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) y} = {y} := by
  dsimp only
  let y : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨(kmswStage w n).nextEdge,
      by have h := (pen_step_geometry w n hc hUR).1; omega⟩, true)
  ext f
  constructor
  · intro hf
    by_cases hold : f.1.val < (kmswStage w n).nextEdge
    · have hcount := (pen_step_geometry w n hc hUR).1
      have hnew := congrArg Fin.val hf
      have hyval := (pen_fresh_vertex_eq w n hc hUR).2
      let f0 : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hold⟩, f.2)
      have hfEq : stageDartIncl w n f0 = f := by
        apply Prod.ext
        · exact Fin.ext rfl
        · rfl
      rw [← hfEq, stageVertex_incl_eq] at hnew
      simp only [stageVertexIncl, Fin.val_castLE] at hnew
      have hfv := (stageVertex w n f0).isLt
      omega
    · have hcount := (pen_step_geometry w n hc hUR).1
      have heq : f.1.val = (kmswStage w n).nextEdge := by
        have hlt := f.1.isLt
        simp only [hcount] at hlt
        omega
      cases hb : f.2
      · have hnew := congrArg Fin.val hf
        have hwest := (pen_endpoints w n hc hUR).1
        have heast := (pen_endpoints w n hc hUR).2
        have hactive := kmswStage_endpoints_lt_nextVertex w n _
          (kmswStage_boundary_ids_lt_nextEdge w n).1
        simp [stageVertex, stageEndpoint, heq, hb] at hnew
        rw [hwest, heast] at hnew
        exact False.elim ((Nat.ne_of_lt hactive.2) hnew)
      · have hval := congrArg Fin.val hf
        have heq' : f = y := by
          apply Prod.ext
          · exact Fin.ext heq
          · exact hb
        rw [heq']
        rfl
  · rintro rfl
    rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
Rotation agreement for the pendant step of `def-kmsw`, -/
theorem layoutGood_succ_pen_rotation_agreement (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      CcwSuccessor
        {e | stageVertex w (n + 1) e = stageVertex w (n + 1) d}
        (fun e => (layoutDart w (n + 1) e).initialDirection)
        d (stageRot w (n + 1) d) := by
  let k := (kmswStage w n).nextEdge
  let A0 : StageDart (kmswStage w n).nextEdge :=
    (⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩, true)
  let A : StageDart (kmswStage w (n + 1)).nextEdge := stageDartIncl w n A0
  let x : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨k, by have h := (pen_step_geometry w n hc hUR).1; omega⟩, false)
  let y : StageDart (kmswStage w (n + 1)).nextEdge := (x.1, true)
  let S : Set (StageDart (kmswStage w (n + 1)).nextEdge) :=
    {f | f.1.val < k ∧ stageVertex w (n + 1) f =
      stageVertex w (n + 1) A}
  have hxFresh : x.1.val ∈ freshEdges w n := by
    change k ∈ Finset.Ico k (kmswStage w (n + 1)).nextEdge
    rw [(pen_step_geometry w n hc hUR).1]
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hxVertex : stageVertex w (n + 1) x = stageVertex w (n + 1) A := by
    simpa [x, A, A0] using (pen_fresh_vertex_eq w n hc hUR).1
  have hyVertex : (stageVertex w (n + 1) y).val =
      (kmswStage w n).nextVertex := by
    simpa [y, x] using (pen_fresh_vertex_eq w n hc hUR).2
  have hactive : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    rw [hes]
    simp
  have hAin : A ∈ S := by
    refine ⟨A0.1.isLt, ?_⟩
    rfl
  have hStarA :
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) A} =
        insert x S := by
    simpa [S, A] using stageStar_eq_insert_old_star w n A0 x hxFresh hxVertex
  have hxNotS : x ∉ S := by
    intro hx
    exact (not_lt_of_ge (Finset.mem_Ico.mp hxFresh).1) hx.1
  have hOldWest : ∀ f ∈ S,
      (layoutDart w (n + 1) f).initialDirection.re < 0 := by
    intro f hf
    let f0 : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf.1⟩, f.2)
    have hfEq : stageDartIncl w n f0 = f := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    have hv := hf.2
    rw [← hfEq, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    have hvOld : stageVertex w n f0 = stageVertex w n A0 := by
      apply Fin.ext
      simpa only [stageVertexIncl, Fin.val_castLE] using congrArg Fin.val hv
    cases hb : f0.2
    · have heq := congrArg Fin.val hvOld
      simp only [stageVertex, stageEndpoint, hb, Bool.false_eq_true,
        ↓reduceIte] at heq
      have hstrict : (layoutPos w n ((kmswStage w n).west f0.1.val)).re <
          (layoutPos w n ((kmswStage w n).east f0.1.val)).re := by
        change (kmswStageRank w n ((kmswStage w n).west f0.1.val) : ℝ) <
          (kmswStageRank w n ((kmswStage w n).east f0.1.val) : ℝ)
        exact_mod_cast kmswStageRank_strict w n f0.1.val f0.1.isLt
      rw [heq] at hstrict
      have hend := kmswStage_endpoints_lt_nextVertex w n f0.1.val f0.1.isLt
      have hbound := pen_old_vertex_bound w n hUR G
        ⟨(kmswStage w n).east f0.1.val, hend.2⟩
      exact False.elim ((not_lt_of_ge hbound) hstrict)
    · have hsign := layoutDart_initialDirection_re_sign w n f0
      rw [← hfEq, layoutDart_incl_eq]
      simpa [hb] using hsign
  have hAwest : (layoutDart w (n + 1) A).initialDirection.re < 0 :=
    hOldWest A hAin
  have hfin : S.Finite := Set.finite_univ.subset (fun _ _ => trivial)
  have hargs : ∀ u ∈ insert x S, ∀ v ∈ insert x S, u ≠ v →
      Complex.arg (layoutDart w (n + 1) u).initialDirection ≠
        Complex.arg (layoutDart w (n + 1) v).initialDirection := by
    intro u hu v hv huv
    have huV : stageVertex w (n + 1) u = stageVertex w (n + 1) A := by
      rcases Set.mem_insert_iff.mp hu with h | h
      · rw [h]
        exact hxVertex
      · exact h.2
    have hvV : stageVertex w (n + 1) v = stageVertex w (n + 1) A := by
      rcases Set.mem_insert_iff.mp hv with h | h
      · rw [h]
        exact hxVertex
      · exact h.2
    exact fun h => huv (layoutGood_succ_pen_initial_arg_injective
      w n hc hUR G u v (huV.trans hvV.symm) h)
  have hAmin : ∀ f ∈ S,
      (layoutDart w (n + 1) f).initialDirection.re < 0 →
        f = A ∨
          (layoutDart w (n + 1) A).initialDirection.im /
              (layoutDart w (n + 1) A).initialDirection.re <
            (layoutDart w (n + 1) f).initialDirection.im /
              (layoutDart w (n + 1) f).initialDirection.re := by
    intro f hf hneg
    let f0 : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf.1⟩, f.2)
    have hfEq : stageDartIncl w n f0 = f := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    have hv := hf.2
    rw [← hfEq, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    have hvOld : stageVertex w n f0 = stageVertex w n A0 := by
      apply Fin.ext
      simpa only [stageVertexIncl, Fin.val_castLE] using congrArg Fin.val hv
    have hneg0 : (layoutDart w n f0).initialDirection.re < 0 := by
      rw [← hfEq, layoutDart_incl_eq] at hneg
      exact hneg
    have htop := G.upper_west_dart_topmost
      ⟨(kmswStage w n).active, (kmswStage_boundary_ids_lt_nextEdge w n).1⟩
      hactive f0 hvOld hneg0
    rcases htop with h | h
    · left
      rw [← hfEq]
      exact congrArg (stageDartIncl w n) h
    · right
      have hdirF : layoutDart w (n + 1) f = layoutDart w n f0 := by
        rw [← hfEq, layoutDart_incl_eq]
      have hdirA : layoutDart w (n + 1) A = layoutDart w n A0 := by
        simpa [A] using layoutDart_incl_eq w n A0
      simpa [hdirF, hdirA] using h
  let p0 : StageDart (kmswStage w n).nextEdge := (stageRot w n).symm A0
  let p : StageDart (kmswStage w (n + 1)).nextEdge := stageDartIncl w n p0
  have hrotP : stageRot w n p0 = A0 := by
    simp [p0]
  have hpVertex : stageVertex w n p0 = stageVertex w n A0 := by
    have hv := P.vert_rotation p0
    rw [hrotP] at hv
    exact hv.symm
  have hpVertexNew : stageVertex w (n + 1) (stageDartIncl w n p0) =
      stageVertex w (n + 1) (stageDartIncl w n A0) := by
    rw [stageVertex_incl_eq, stageVertex_incl_eq]
    exact congrArg (stageVertexIncl w n) hpVertex
  have hOldPA : CcwSuccessor S
      (fun f => (layoutDart w (n + 1) f).initialDirection) p A := by
    have h := G.old_star_rotation_agreement p0
    have hS : {f | f.1.val < k ∧ stageVertex w (n + 1) f =
        stageVertex w (n + 1) (stageDartIncl w n p0)} = S := by
      ext f
      simp only [S, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hf, hv⟩
        exact ⟨hf, hv.trans hpVertexNew⟩
      · rintro ⟨hf, hv⟩
        exact ⟨hf, hv.trans hpVertexNew.symm⟩
    rw [hS, hrotP] at h
    simpa [p, A] using h
  have hArgsOld : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      Complex.arg (layoutDart w (n + 1) u).initialDirection ≠
        Complex.arg (layoutDart w (n + 1) v).initialDirection := by
    intro u hu v hv huv
    exact hargs u (Set.mem_insert_of_mem x hu) v
      (Set.mem_insert_of_mem x hv) huv
  have hpWest : (layoutDart w (n + 1) p).initialDirection.re < 0 :=
    hOldWest p hOldPA.2.1
  have hmax : ∀ f ∈ S,
      (layoutDart w (n + 1) f).initialDirection.re < 0 →
        f = p ∨
          (layoutDart w (n + 1) f).initialDirection.im /
              (layoutDart w (n + 1) f).initialDirection.re <
            (layoutDart w (n + 1) p).initialDirection.im /
              (layoutDart w (n + 1) p).initialDirection.re :=
    pen_predecessor_max_slope S
      (fun f => (layoutDart w (n + 1) f).initialDirection) p A hOldPA
      hArgsOld hOldPA.2.1 hAin hpWest hAwest hAmin
  have hxEast : (layoutDart w (n + 1) x).initialDirection.re > 0 := by
    have hs := layoutDart_initialDirection_re_sign w (n + 1) x
    simpa [x] using hs
  have hnewXA : CcwSuccessor (insert x S)
      (fun f => (layoutDart w (n + 1) f).initialDirection) x A := by
    apply east_max_ccwSuccessor (insert x S)
      (fun f => (layoutDart w (n + 1) f).initialDirection) x A (hfin.insert x)
      (Set.mem_insert x S) (Set.mem_insert_of_mem x hAin)
      (fun f hf => by
        rcases Set.mem_insert_iff.mp hf with rfl | hf
        · exact ne_of_gt hxEast
        · exact ne_of_lt (hOldWest f hf))
      hxEast hAwest
      (fun f hf hpos => by
        rcases Set.mem_insert_iff.mp hf with rfl | hf
        · exact Or.inl rfl
        · exact False.elim (not_lt_of_ge (hOldWest f hf).le hpos))
      (fun f hf hneg => by
        rcases Set.mem_insert_iff.mp hf with rfl | hf
        · exact False.elim (not_lt_of_ge hxEast.le hneg)
        · exact hAmin f hf hneg)
  have hslot : CcwBetween
      (layoutDart w (n + 1) p).initialDirection
      (layoutDart w (n + 1) x).initialDirection
      (layoutDart w (n + 1) A).initialDirection := by
    by_cases hpa : p = A
    · have hnotfull : ccwTurn (layoutDart w (n + 1) p).initialDirection
          (layoutDart w (n + 1) x).initialDirection ≠ 2 * Real.pi := by
        intro hfull
        have hparg := hargs p (Set.mem_insert_of_mem x hOldPA.2.1)
          x (Set.mem_insert x S) (by
            intro h
            exact hxNotS (h ▸ hOldPA.2.1))
        exact hparg ((ccwTurn_eq_two_pi_iff _ _).mp hfull)
      have hlt := lt_of_le_of_ne
        (ccwTurn_le_two_pi (layoutDart w (n + 1) p).initialDirection
          (layoutDart w (n + 1) x).initialDirection) hnotfull
      unfold CcwBetween
      simpa [hpa, (ccwTurn_eq_two_pi_iff _ _).2 rfl] using hlt
    · have hminP := hAmin p hOldPA.2.1 hpWest
      have hAP :
          (layoutDart w (n + 1) A).initialDirection.im /
            (layoutDart w (n + 1) A).initialDirection.re <
          (layoutDart w (n + 1) p).initialDirection.im /
            (layoutDart w (n + 1) p).initialDirection.re := by
        rcases hminP with h | h
        · exact False.elim (hpa h)
        · exact h
      have hAPturn := west_west_turn_formula hAwest hpWest hAP
      have hrev := ccwTurn_add_reverse
        (layoutDart w (n + 1) p).initialDirection
        (layoutDart w (n + 1) A).initialDirection
        (hargs p (Set.mem_insert_of_mem x hOldPA.2.1) A
          (Set.mem_insert_of_mem x hAin) hpa)
      have hPAturn : ccwTurn (layoutDart w (n + 1) p).initialDirection
          (layoutDart w (n + 1) A).initialDirection =
            2 * Real.pi - ccwTurn (layoutDart w (n + 1) A).initialDirection
              (layoutDart w (n + 1) p).initialDirection := by linarith [hrev]
      have hPXturn := west_east_turn_formula hpWest hxEast
      have hargA := Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (show 0 < (-(layoutDart w (n + 1) A).initialDirection).re by
          simpa using neg_pos.mpr hAwest))
      have hargX := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxEast)
      unfold CcwBetween
      rw [hPXturn, hPAturn, hAPturn]
      linarith [(abs_lt.mp hargX).2, (abs_lt.mp hargA).1, Real.pi_pos]
  have hPrevX : CcwSuccessor (insert x S)
      (fun f => (layoutDart w (n + 1) f).initialDirection) p x := by
    apply (ccwSuccessor_iff_no_between (insert x S)
      (fun f => (layoutDart w (n + 1) f).initialDirection) p x
      (hfin.insert x) (Set.mem_insert_of_mem x hOldPA.2.1)).2
    have hxp : x ≠ p := by
      intro h
      exact hxNotS (h ▸ hOldPA.2.1)
    refine Or.inr ⟨hxp, Set.mem_insert x S, ?_⟩
    intro f hf hfp hfx hbetween
    rcases Set.mem_insert_iff.mp hf with heq | hf
    · exact (hfx heq).elim
    · have hno :=
        (ccwSuccessor_iff_no_between S
          (fun f => (layoutDart w (n + 1) f).initialDirection)
          p A hfin hOldPA.2.1).mp hOldPA
      have hfa : f ≠ A := by
        intro heq
        subst f
        exact (not_lt_of_ge hslot.le) hbetween
      rcases hno with hsingle | ⟨_, _, hno⟩
      · have hfp' : f = p := by simpa [hsingle.2] using hf
        exact hfp hfp'
      · exact hno f hf hfp hfa
          (by unfold CcwBetween at *; exact lt_trans hbetween hslot)
  have hNewRot := pen_rotation_new w n hc hUR
  have hOldRot (d : StageDart (kmswStage w n).nextEdge) :=
    pen_rotation_old w n hc hUR d
  intro d
  rcases d with ⟨e, b⟩
  by_cases he : e.val < k
  · let d0 : StageDart (kmswStage w n).nextEdge := (⟨e.val, he⟩, b)
    have hdEq : stageDartIncl w n d0 = (e, b) := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    by_cases hAtA : stageVertex w (n + 1) (stageDartIncl w n d0) =
        stageVertex w (n + 1) A
    · have hStarD :
          {f | stageVertex w (n + 1) f =
            stageVertex w (n + 1) (stageDartIncl w n d0)} = insert x S := by
        rw [hAtA]
        exact hStarA
      have hOldD : CcwSuccessor S
          (fun f => (layoutDart w (n + 1) f).initialDirection)
          (stageDartIncl w n d0)
          (stageDartIncl w n (stageRot w n d0)) := by
        have h := G.old_star_rotation_agreement d0
        have hS : {f | f.1.val < k ∧ stageVertex w (n + 1) f =
            stageVertex w (n + 1) (stageDartIncl w n d0)} = S := by
          ext f
          simp only [S, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨hf, hv⟩
            exact ⟨hf, hv.trans hAtA⟩
          · rintro ⟨hf, hv⟩
            exact ⟨hf, hv.trans hAtA.symm⟩
        rw [hS] at h
        exact h
      by_cases hdp : d0 = p0
      · have hStarP : {f | stageVertex w (n + 1) f =
            stageVertex w (n + 1) (stageDartIncl w n p0)} = insert x S := by
          rw [hpVertexNew]
          exact hStarA
        rw [← hdEq, hOldRot, hdp]
        rw [ite_eq_left hrotP, hStarP]
        simpa [p] using hPrevX
      · have hrotNe : stageRot w n d0 ≠ A0 := by
          intro h
          apply hdp
          exact (stageRot w n).injective (h.trans hrotP.symm)
        rw [← hdEq, hOldRot]
        have hOldD' : CcwSuccessor S
            (fun f => (layoutDart w (n + 1) f).initialDirection)
            (stageDartIncl w n d0)
            (stageDartIncl w n (stageRot w n d0)) := hOldD
        have hdpNew : stageDartIncl w n d0 ≠ p := by
          intro h
          apply hdp
          have h' : stageDartIncl w n d0 = stageDartIncl w n p0 := by
            simpa [p] using h
          apply Prod.ext
          · apply Fin.ext
            simpa only [stageDartIncl, Fin.val_castLE] using
              congrArg (fun q : StageDart (kmswStage w (n + 1)).nextEdge => q.1.val) h'
          · exact congrArg
              (fun q : StageDart (kmswStage w (n + 1)).nextEdge => q.2) h'
        have hAway := pen_no_between_old_link S
          (fun f => (layoutDart w (n + 1) f).initialDirection)
          (stageDartIncl w n d0)
          (stageDartIncl w n (stageRot w n d0)) p A x hOldD' hArgsOld
          hOldD'.2.1 hOldD'.2.2.1 hOldPA.2.1 hAin hdpNew
          (hOldWest _ hOldD'.2.1) (hOldWest _ hOldD'.2.2.1)
          hpWest hAwest hxEast hAmin hmax
        rw [hStarD, ite_eq_right hrotNe]
        exact ccwSuccessor_insert_preserve S
          (fun f => (layoutDart w (n + 1) f).initialDirection)
          (stageDartIncl w n d0)
          (stageDartIncl w n (stageRot w n d0)) x hfin hargs hOldD' hxNotS hAway
    · have hAway : stageVertex w (n + 1) (stageDartIncl w n d0) ≠
          stageVertex w (n + 1) x := by
        intro h
        exact hAtA (h.trans hxVertex)
      have hStarD := pen_old_vertex_star w n hc hUR d0 hAway
      have hOldD := G.old_star_rotation_agreement d0
      have hrotNe : stageRot w n d0 ≠ A0 := by
        intro h
        have hpEq : d0 = p0 := (stageRot w n).injective
          (h.trans hrotP.symm)
        have hvertexEq : stageVertex w (n + 1) (stageDartIncl w n d0) =
            stageVertex w (n + 1) A := by
          rw [hpEq]
          exact hpVertexNew
        exact hAtA hvertexEq
      rw [← hdEq, hStarD, hOldRot, ite_eq_right hrotNe]
      exact hOldD
  · have hcount := (pen_step_geometry w n hc hUR).1
    have heq : e.val = k := by
      have hlt := e.isLt
      simp only [hcount] at hlt
      omega
    cases b
    · have hrotX := hNewRot.1
      have hdEq : (e, false) = x := by
        apply Prod.ext
        · exact Fin.ext heq
        · rfl
      rw [hdEq, hxVertex, hStarA, hrotX]
      exact hnewXA
    · have hrotY := hNewRot.2
      have hdEq : (e, true) = y := by
        apply Prod.ext
        · exact Fin.ext heq
        · rfl
      rw [hdEq]
      rw [pen_new_vertex_star w n hc hUR]
      have hYmem : y ∈ ({y} : Set (StageDart (kmswStage w (n + 1)).nextEdge)) :=
        Set.mem_singleton y
      rw [hrotY]
      exact ⟨Set.finite_singleton y, hYmem, hYmem,
        Or.inl ⟨rfl, rfl⟩⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result.
The good layout for the pendant step of `def-kmsw`, -/
theorem layoutGood_succ_pen (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    LayoutGood w (n + 1) where
  interior_disjoint := layoutGood_succ_pen_interior_disjoint w n hc hUR G
  interior_avoids_vertices := layoutGood_succ_pen_interior_avoids_vertices
    w n hc hUR G
  initial_arg_injective := layoutGood_succ_pen_initial_arg_injective
    w n hc hUR G
  rotation_agreement := layoutGood_succ_pen_rotation_agreement
    w n hc hUR G

end DirectedDistances.KMSW
