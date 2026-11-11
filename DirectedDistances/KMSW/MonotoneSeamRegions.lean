module

public import DirectedDistances.KMSW.MonotoneSeamTiling
public import DirectedDistances.KMSW.MonotoneSeamStabilization
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
import DirectedDistances.KMSW.RunInfDartPartition

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology Classical





private theorem regions_hit_left_below (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, L w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨n, hn.le.trans (min_le_left _ _)⟩





private theorem regions_hit_right_below (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
  refine ⟨n, ?_⟩
  have hm := le_max_left (-a) 1
  omega




private theorem regions_upper_trace_escapes (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    ∃ N, ∀ n, N ≤ n →
      Disjoint (graphOver (G n).xmin (G n).xmax (G n).upper) K := by
  let hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P) := fun n => ⟨Q n, ⟨G n⟩⟩
  let P := monotoneLimitDrawing w hfin hfam
  have hagree := monotoneLimitDrawing_agrees w hfin hfam Q
    (fun n v => (G n).pos_layout v) (fun n d => (G n).arc_layout d)
  let E : Set ℕ := Prod.fst '' {d | (K ∩ (P.arc d).image).Nonempty}
  have hE : E.Finite := (P.locally_finite K hK).image Prod.fst
  have htime (e : ℕ) : ∃ N, ∀ n, N ≤ n →
      e ∉ (kmswStage w n).UL ∧ e ∉ (kmswStage w n).UR := by
    obtain ⟨A, hA⟩ := kmswRun_UL_eventually_absent w (regions_hit_left_below w h) e
    obtain ⟨B, hB⟩ := kmswRun_UR_eventually_absent w (regions_hit_right_below w h) e
    exact ⟨max A B, fun n hn =>
      ⟨hA n ((le_max_left _ _).trans hn), hB n ((le_max_right _ _).trans hn)⟩⟩
  let T : ℕ → ℕ := fun e => (htime e).choose
  have hT (e : ℕ) := (htime e).choose_spec
  obtain ⟨N, hN⟩ := (hE.image T).bddAbove
  refine ⟨N, fun n hn => disjoint_left.mpr ?_⟩
  intro z hzUpper hzK
  rw [(G n).upper_trace] at hzUpper
  obtain ⟨e, hzUpper⟩ := mem_iUnion.mp hzUpper
  obtain ⟨heUpper, hzTrace⟩ := mem_iUnion.mp hzUpper
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heUpper ⊢
      tauto)
  have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
    simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
  have hzArc : z ∈ (layoutArc w n e).image := by
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hzP : z ∈ (P.arc (e, false)).image := by
    rw [hagree.2 n (⟨⟨e, he⟩, false⟩), hd]
    exact hzArc
  have heE : e ∈ E :=
    Set.mem_image_of_mem Prod.fst
      (show (e, false) ∈ {d | (K ∩ (P.arc d).image).Nonempty} from
        ⟨z, hzK, hzP⟩)
  have ht := hT e n ((hN (Set.mem_image_of_mem T heE)).trans hn)
  exact (List.mem_append.mp heUpper).elim ht.1 ht.2





private theorem regions_vertical_range (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (A : ℝ) :
    ∃ N, ∀ n, N ≤ n → (G n).xmin ≤ -|A| ∧ |A| ≤ (G n).xmax ∧
      ∀ x ∈ Icc (-|A|) |A|, |A| < (G n).upper x := by
  obtain ⟨N1, hN1⟩ := monotoneStage_xmax_unbounded
    (w := w) (regions_hit_right_below w h) Q G |A|
  obtain ⟨N2, hN2⟩ := monotoneStage_xmin_unbounded_below w
    (infinitelyManyFreshLeft_of_L_unbounded_below w (regions_hit_left_below w h)) Q G (-|A|)
  obtain ⟨N3, hN3⟩ := regions_upper_trace_escapes w hfin h Q G
    (Metric.closedBall (0 : ℂ) (2 * |A|)) Metric.isBounded_closedBall
  refine ⟨max N1 (max N2 N3), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_left N2 N3).trans ((le_max_right _ _).trans hn)
  have hn3 : N3 ≤ n := (le_max_right N2 N3).trans ((le_max_right _ _).trans hn)
  refine ⟨hN2 n hn2, hN1 n hn1, fun x hx => ?_⟩
  by_contra hnot
  have hle : (G n).upper x ≤ |A| := not_lt.mp hnot
  let q : ℂ := ⟨x, (G n).upper x⟩
  have hq : q ∈ graphOver (G n).xmin (G n).xmax (G n).upper :=
    ⟨(hN2 n hn2).trans hx.1, hx.2.trans (hN1 n hn1), rfl⟩
  have hq0 : 0 ≤ q.im := monotoneUpperTrace_nonneg Q G hq
  have hqK : q ∈ Metric.closedBall (0 : ℂ) (2 * |A|) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm := Complex.norm_le_abs_re_add_abs_im q
    have hre : |q.re| ≤ |A| := abs_le.mpr hx
    have him : |q.im| ≤ |A| := by rw [abs_of_nonneg hq0]; exact hle
    linarith only [hnorm, hre, him]
  exact (disjoint_left.mp (hN3 n hn3)) hq hqK




private theorem regions_reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
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




private theorem regions_reverse_image (p : Polyline) : p.reverse.image = p.image := by
  apply Set.Subset.antisymm (regions_reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using regions_reverse_image_subset p.reverse

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include h hfin in



theorem monotoneSeam_stage_at (x : ℝ) :
    ∃ n, (familyG w (monotone_family_all w) n).xmin < x ∧
      x < (familyG w (monotone_family_all w) n).xmax := by
  obtain ⟨N, hN⟩ := regions_vertical_range w hfin h
    (familyQ w (monotone_family_all w)) (familyG w (monotone_family_all w)) (|x| + 1)
  obtain ⟨hl, hr, _⟩ := hN N le_rfl
  rw [abs_of_pos (by positivity : 0 < |x| + 1)] at hl hr
  exact ⟨N, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩




private theorem regions_lower_agree (n m : ℕ) (x : ℝ)
    (hn : x ∈ Icc (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax)
    (hm : x ∈ Icc (familyG w (monotone_family_all w) m).xmin
      (familyG w (monotone_family_all w) m).xmax) :
    (familyG w (monotone_family_all w) n).lower x =
      (familyG w (monotone_family_all w) m).lower x := by
  exact ((monotoneSeam_lower_stable w n x hn (max n m) (le_max_left _ _)).2).symm.trans
    (monotoneSeam_lower_stable w m x hm (max n m) (le_max_right _ _)).2




@[expose] noncomputable def seamFun (x : ℝ) : ℝ :=
  (familyG w (monotone_family_all w) (monotoneSeam_stage_at w h hfin x).choose).lower x




theorem seamFun_eq_lower (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax) :
    seamFun w h hfin x = (familyG w (monotone_family_all w) n).lower x := by
  have hc := (monotoneSeam_stage_at w h hfin x).choose_spec
  exact regions_lower_agree w _ n x ⟨hc.1.le, hc.2.le⟩ hx




theorem seamFun_continuous : Continuous (seamFun w h hfin) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n, hn⟩ := monotoneSeam_stage_at w h hfin x
  have hnhds : Icc (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax ∈ nhds x :=
    Icc_mem_nhds hn.1 hn.2
  apply ((familyG w (monotone_family_all w) n).lower_continuous.continuousAt
    hnhds).congr_of_eventuallyEq
  exact Filter.eventually_of_mem hnhds (fun y hy => seamFun_eq_lower w h hfin n y hy)




private theorem regions_seam_point (k : ℤ) (z : ℂ)
    (hz : z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k)).image) :
    ∃ n, z ∈ graphOver (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax
      (familyG w (monotone_family_all w) n).lower := by
  obtain ⟨n, hn⟩ := boundaryOuterEdge_mem_finite_LL_LR w h k
  have hlower : boundaryOuterEdge w h k ∈
      (kmswStage w n).LL ++ (kmswStage w n).LR := List.mem_append.mpr hn
  have he : boundaryOuterEdge w h k < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
      simp only [List.mem_append] at hlower ⊢
      tauto)
  have harc : (monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k) =
      (layoutArc w n (boundaryOuterEdge w h k)).reverse :=
    monotoneLimitDrawing_arc_layout w hfin _ n (boundaryOuterEdge w h k) he true
  rw [harc, regions_reverse_image] at hz
  refine ⟨n, ?_⟩
  rw [(familyG w (monotone_family_all w) n).lower_trace]
  refine mem_iUnion.mpr ⟨boundaryOuterEdge w h k, mem_iUnion.mpr ⟨hlower, ?_⟩⟩
  have hd := (familyG w (monotone_family_all w) n).arc_layout
    (⟨⟨boundaryOuterEdge w h k, he⟩, false⟩)
  simpa only [stageEdgeTrace, dite_eq_left he, hd, Bool.false_eq_true, ↓reduceIte]
    using hz




theorem seamFun_graph : {z : ℂ | z.im = seamFun w h hfin z.re} =
    ⋃ k : ℤ, ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k)).image := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := seamX_tiling w h hfin z.re
    obtain ⟨q, hq, _⟩ := (seam_arc_vertical_sections w h hfin k).2 z.re hk.1 hk.2
    obtain ⟨n, hn⟩ := regions_seam_point w h hfin k q hq.1
    have hheight : q.im = seamFun w h hfin q.re :=
      hn.2.2.trans (seamFun_eq_lower w h hfin n q.re ⟨hn.1, hn.2.1⟩).symm
    have heq : q = z := Complex.ext hq.2 (by rw [hheight, hq.2]; exact hz.symm)
    exact mem_iUnion.mpr ⟨k, heq ▸ hq.1⟩
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    obtain ⟨n, hn⟩ := regions_seam_point w h hfin k z hk
    exact hn.2.2.trans (seamFun_eq_lower w h hfin n z.re ⟨hn.1, hn.2.1⟩).symm




theorem monotoneFamilyDrawing_above_seam :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).image ⊆
      {z : ℂ | seamFun w h hfin z.re ≤ z.im} := by
  intro z hz
  rw [monotoneFamilyDrawing_image] at hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  have hr : z ∈ closedGraphRegion
      (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax
      (familyG w (monotone_family_all w) n).lower
      (familyG w (monotone_family_all w) n).upper := by
    rw [← (familyG w (monotone_family_all w) n).cover]
    exact Or.inl hn
  change seamFun w h hfin z.re ≤ z.im
  rw [seamFun_eq_lower w h hfin n z.re ⟨hr.1, hr.2.1⟩]
  exact hr.2.2.1

include h hfin in



theorem monotoneSeam_upper_eventually_above (x y : ℝ) :
    ∃ N, ∀ n, N ≤ n →
      x ∈ Icc (familyG w (monotone_family_all w) n).xmin
        (familyG w (monotone_family_all w) n).xmax ∧
      y < (familyG w (monotone_family_all w) n).upper x := by
  obtain ⟨N, hN⟩ := regions_vertical_range w hfin h
    (familyQ w (monotone_family_all w)) (familyG w (monotone_family_all w))
    (|x| + |y| + 1)
  have hA : 0 ≤ |x| + |y| + 1 := by positivity
  have hx : x ∈ Icc (-|(|x| + |y| + 1)|) |(|x| + |y| + 1)| := by
    rw [abs_of_nonneg hA]
    constructor <;> linarith [neg_abs_le x, le_abs_self x, abs_nonneg y]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hl, hr, hu⟩ := hN n hn
  refine ⟨⟨hl.trans hx.1, hx.2.trans hr⟩, ?_⟩
  have hy : y < |(|x| + |y| + 1)| := by
    rw [abs_of_nonneg hA]
    linarith [le_abs_self y, abs_nonneg x]
  exact hy.trans (hu x hx)




theorem monotoneLimitExteriorRegion_eq_below_seam :
    monotoneLimitExteriorRegion w (familyQ w (monotone_family_all w))
      (familyG w (monotone_family_all w)) =
      {z : ℂ | z.im < seamFun w h hfin z.re} := by
  ext z
  change (z ∉ ⋃ n, monotoneLimitStageRegion w
    (familyQ w (monotone_family_all w)) (familyG w (monotone_family_all w)) n) ↔ _
  constructor
  · intro hz
    obtain ⟨N, hN⟩ := monotoneSeam_upper_eventually_above w h hfin z.re z.im
    obtain ⟨hx, hu⟩ := hN N le_rfl
    by_contra hnot
    apply hz
    refine mem_iUnion.mpr ⟨N, hx.1, hx.2, ?_, hu.le⟩
    rw [← seamFun_eq_lower w h hfin N z.re hx]
    exact not_lt.mp hnot
  · intro hz hmem
    obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
    have hlow := hn.2.2.1
    rw [← seamFun_eq_lower w h hfin n z.re ⟨hn.1, hn.2.1⟩] at hlow
    exact (not_le_of_gt hz) hlow

end DirectedDistances.KMSW
