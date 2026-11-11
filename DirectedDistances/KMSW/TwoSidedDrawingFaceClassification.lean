module

public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneExteriorPaths
public import DirectedDistances.KMSW.MonotoneXminGrowth
public import DirectedDistances.KMSW.FreshLeftRecurrence
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary
public import DirectedDistances.KMSW.LocalFinitenessIID
import DirectedDistances.KMSW.RunInfDartPartition

/-! Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Two-sided lower-boundary classification for the raw one-sided iid KMSW code.

Both coordinates are unbounded below. Thus every fixed upper edge disappears,
whereas both lower chains persist. No nonnegativity or transience of L is used. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set MeasureTheory
open scoped Topology Classical

private theorem hit_left_below (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, L w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨n, hn.le.trans (min_le_left _ _)⟩

private theorem hit_right_below (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
  refine ⟨n, ?_⟩
  have hm := le_max_left (-a) 1
  omega

private theorem upper_trace_escapes (w : ℕ → Fin 3)
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
    obtain ⟨A, hA⟩ := kmswRun_UL_eventually_absent w (hit_left_below w h) e
    obtain ⟨B, hB⟩ := kmswRun_UR_eventually_absent w (hit_right_below w h) e
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

private theorem vertical_range (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (A : ℝ) :
    ∃ N, ∀ n, N ≤ n → (G n).xmin ≤ -|A| ∧ |A| ≤ (G n).xmax ∧
      ∀ x ∈ Icc (-|A|) |A|, |A| < (G n).upper x := by
  obtain ⟨N1, hN1⟩ := monotoneStage_xmax_unbounded
    (w := w) (hit_right_below w h) Q G |A|
  obtain ⟨N2, hN2⟩ := monotoneStage_xmin_unbounded_below w
    (infinitelyManyFreshLeft_of_L_unbounded_below w (hit_left_below w h)) Q G (-|A|)
  obtain ⟨N3, hN3⟩ := upper_trace_escapes w hfin h Q G
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

private theorem lower_edge_mem_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) :
    e ∈ (kmswStage w m).LL ++ (kmswStage w m).LR := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m _ ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL ++
      (kmswStep (kmswStage w m) (w m)).LR
    unfold kmswStep
    cases kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR with
      | nil =>
        simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
          List.mem_singleton] at *
        tauto
      | cons a as => simpa only [kmswStepOfStep, hs] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
          List.mem_cons] at *
        tauto

private theorem arc_stable (w : ℕ → Fin 3) {n m e : ℕ} (hnm : n ≤ m)
    (he : e < (kmswStage w n).nextEdge) : layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

private theorem excludes_below_lower {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    {n : ℕ} {q z : ℂ}
    (hq : q ∈ graphOver (G n).xmin (G n).xmax (G n).lower)
    (hre : q.re = z.re) (him : z.im < q.im) :
    ∀ m, n ≤ m → z ∉ monotoneStageRegion Q G m := by
  rw [(G n).lower_trace] at hq
  obtain ⟨e, hq⟩ := mem_iUnion.mp hq
  obtain ⟨heLower, hzTrace⟩ := mem_iUnion.mp hq
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heLower ⊢
      tauto)
  have hqArc : q ∈ (layoutArc w n e).image := by
    have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
      simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
    simpa [stageEdgeTrace, he, hd] using hzTrace
  intro m hnm hzm
  have hqm : q ∈ (layoutArc w m e).image := by
    rwa [arc_stable w hnm he]
  have hlower := (G m).lower_eq_arc_height (lower_edge_mem_mono w hnm heLower) hqm
  have hbound : (G m).lower z.re ≤ z.im := hzm.2.2.1
  rw [← hre, hlower] at hbound
  exact (not_le_of_gt him) hbound

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Bounded exhaustion for raw codes whose two coordinates hit all negative levels. -/
theorem monotoneRegionBoundedExhaustion_twoSided (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    monotoneRegionBoundedExhaustion Q G := by
  intro K hK
  obtain ⟨A, hA⟩ := hK.subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ := vertical_range w hfin h Q G A
  refine ⟨N, fun n hn z hzK => ?_⟩
  by_cases hz : z ∈ monotoneStageRegion Q G n
  · exact Or.inl hz
  right
  have hzA : ‖z‖ ≤ |A| := by
    have hb := hA hzK
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    exact hb.trans (le_abs_self A)
  have hx : z.re ∈ Icc (-|A|) |A| :=
    abs_le.mp ((Complex.abs_re_le_norm z).trans hzA)
  obtain ⟨hmin, hmax, hupper⟩ := hN n hn
  have hrange : z.re ∈ Icc (G n).xmin (G n).xmax :=
    ⟨hmin.trans hx.1, hx.2.trans hmax⟩
  have hup : z.im ≤ (G n).upper z.re :=
    ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzA)).trans
      (hupper z.re hx).le
  have hlow : z.im < (G n).lower z.re := by
    by_contra hnot
    exact hz ⟨hrange.1, hrange.2, not_lt.mp hnot, hup⟩
  have hq : (⟨z.re, (G n).lower z.re⟩ : ℂ) ∈
      graphOver (G n).xmin (G n).xmax (G n).lower := ⟨hrange.1, hrange.2, rfl⟩
  intro m hm
  exact excludes_below_lower Q G (z := z) hq rfl hlow (max m n) (le_max_right _ _)
    (monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G (le_max_left _ _) hm)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The exterior is unbounded because it contains the open lower half-plane. -/
theorem monotoneLimitExterior_unbounded_twoSided {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (r : ℝ) : ∃ z ∈ monotoneLimitExterior Q G, r < ‖z‖ := by
  let z : ℂ := ⟨0, -(|r| + 1)⟩
  have hz : z.im < 0 := by dsimp [z]; linarith [abs_nonneg r]
  refine ⟨z, lowerHalf_subset_monotoneLimitExterior hz, ?_⟩
  have him : |z.im| = |r| + 1 := by
    change |-(|r| + 1)| = |r| + 1
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ |r| + 1)]
  calc
    r ≤ |r| := le_abs_self r
    _ < |r| + 1 := by linarith
    _ = |z.im| := him.symm
    _ ≤ ‖z‖ := Complex.abs_im_le_norm z

private theorem segment_re_im {a b p : ℂ} (hp : p ∈ segment ℝ a b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ p.re = a.re + θ * (b.re - a.re) ∧
      p.im = a.im + θ * (b.im - a.im) := by
  rw [segment_eq_image'] at hp
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hp
  refine ⟨θ, h0, h1, ?_, ?_⟩ <;> simp

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Every exterior point joins the lower half-plane by a vertical segment. -/
theorem monotoneLimitExterior_isPathConnected_twoSided (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    IsPathConnected (monotoneLimitExterior Q G) := by
  let c : ℂ := ⟨0, -1⟩
  have hcim : c.im < 0 := by norm_num [c]
  have hc : c ∈ monotoneLimitExterior Q G := lowerHalf_subset_monotoneLimitExterior hcim
  suffices key : ∀ z ∈ monotoneLimitExterior Q G,
      JoinedIn (monotoneLimitExterior Q G) z c by
    exact isPathConnected_iff.mpr
      ⟨⟨c, hc⟩, fun x hx y hy => (key x hx).trans (key y hy).symm⟩
  intro z hz
  by_cases him : z.im < 0
  · exact joinedIn_lowerHalf him hcim
  have him0 : 0 ≤ z.im := not_lt.mp him
  obtain ⟨N, hN⟩ := vertical_range w hfin h Q G ‖z‖
  obtain ⟨hmin, hmax, hupper⟩ := hN N le_rfl
  have hx : z.re ∈ Icc (-|‖z‖|) |‖z‖| :=
    abs_le.mp ((Complex.abs_re_le_norm z).trans (le_abs_self ‖z‖))
  have hrange : z.re ∈ Icc (G N).xmin (G N).xmax :=
    ⟨hmin.trans hx.1, hx.2.trans hmax⟩
  have hup : z.im ≤ (G N).upper z.re :=
    ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans
      (le_abs_self ‖z‖))).trans (hupper z.re hx).le
  have hlow : z.im < (G N).lower z.re := by
    by_contra hnot
    exact (mem_monotoneLimitExterior_iff.mp hz) N
      ⟨hrange.1, hrange.2, not_lt.mp hnot, hup⟩
  let y : ℂ := ⟨z.re, (G N).lower z.re⟩
  have hy : y ∈ monotoneStageRegion Q G N :=
    ⟨hrange.1, hrange.2, le_rfl, (G N).lower_le_upper z.re hrange⟩
  have hjoin : JoinedIn (monotoneLimitExterior Q G) z ⟨z.re, -1⟩ := by
    apply JoinedIn.of_segment_subset
    intro p hp
    obtain ⟨θ, hθ0, _, hpre, hpim⟩ := segment_re_im hp
    apply monotoneLimitExterior_down hz hy rfl hlow
    · rw [hpre]
      change z.re + θ * (z.re - z.re) = z.re
      ring
    · rw [hpim]
      change z.im + θ * (-1 - z.im) ≤ z.im
      have hnn := mul_nonneg hθ0 (show 0 ≤ 1 + z.im by linarith)
      linarith only [hnn]
  exact hjoin.trans (joinedIn_lowerHalf (show (-1 : ℝ) < 0 by norm_num) hcim)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The raw-code drawing has a unique unbounded face with exactly its external darts. -/
theorem monotoneFamilyDrawing_faceClassification_twoSided (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ limitExternalDart w d := by
  let hfam := monotone_family_all w
  let Q := familyQ w hfam
  let G := familyG w hfam
  let P := monotoneFamilyDrawing w hfin hfam
  have hbd := monotoneRegionBoundedExhaustion_twoSided w hfin h Q G
  have himage : P.image = ⋃ n, (Q n).image := monotoneFamilyDrawing_image w hfin hfam
  have hfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image := by
    rw [himage]
    exact monotoneLimitExterior_frontier_subset_trace Q G hbd
  have hdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image := by
    rw [himage]
    apply disjoint_left.mpr
    intro z hzE hzImage
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzImage
    exact (disjoint_left.mp (monotoneLimitExterior_disjoint_stageImage Q G n)) hzE hzn
  have hcover : ∀ z ∉ P.image, z ∉ monotoneLimitExteriorRegion w Q G →
      ∃ n i, z ∈ ((G n).cap i).region := by
    intro z hzImage hzE
    apply monotoneStageRegionUnion_mem_cap_of_not_trace Q G (not_not.mp hzE)
    simp only [monotoneLayoutTraceUnion, mem_iUnion, not_exists]
    intro n hzn
    exact hzImage (himage.symm ▸ mem_iUnion.mpr ⟨n, hzn⟩)
  obtain ⟨U, _, hU, huniq, _, hdart⟩ := monotoneLimit_dartBorders_iff w hfin Q G P
    (familyDrawing_pos w hfin hfam) (familyDrawing_arc w hfin hfam)
    (family_cap_persistence w hfam) (family_region_mono w hfam)
    (monotoneLimitExterior_isOpen_of_boundedExhaustion Q G hbd)
    (monotoneLimitExterior_isPathConnected_twoSided w hfin h Q G)
    (monotoneLimitExterior_unbounded_twoSided Q G) hfront hdisj hcover
  exact ⟨U, hU, huniq, hdart⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The realized boundary is the hit-labelled lower boundary in decreasing successor order. -/
theorem monotoneFamilyDrawing_realized_boundary_twoSided (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      (∀ d, P.dartBorders d U ↔
        (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d) ∧
      (∀ d, P.dartBorders d U ↔
        ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
      {v | ∃ d, P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
        Set.range (boundaryVertex w h) ∧
      ∀ k : ℤ,
        kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
          futureMapBoundaryDart w h (k - 1) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hU, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin h
  have horbit (d : ℕ × Bool) :
      P.dartBorders d U ↔
        (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d := by
    rw [hborder d, futureMap_limitExternalDart_iff_sameCycle w hfin h d]
  have hlabel (d : ℕ × Bool) :
      P.dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k := by
    rw [hborder d, futureMap_limitExternalDart_iff_boundaryDart w h d]
  have hvertices :
      {v | ∃ d, P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
        Set.range (boundaryVertex w h) := by
    calc
      {v | ∃ d, P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
          {v | ∃ d, (kmswInfFaceSucc w hfin).SameCycle
            futureMapOuterDart d ∧ kmswLimitDartVertex w d = v} := by
        ext v
        constructor
        · rintro ⟨d, hd, hv⟩
          exact ⟨d, (horbit d).mp hd, hv⟩
        · rintro ⟨d, hd, hv⟩
          exact ⟨d, (horbit d).mpr hd, hv⟩
      _ = Set.range (boundaryVertex w h) :=
        futureMap_outerOrbit_vertex_range w hfin h
  exact ⟨U, hU, huniq, horbit, hlabel, hvertices,
    fun k => futureMapBoundaryDart_faceSucc w hfin h k⟩


/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The hypotheses and full boundary classification hold on one common raw iid event. -/
theorem iidCodes_ae_realized_boundary_twoSided :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (h : BoundaryHitWitnesses w),
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        ∃ U : P.Face, P.IsUnbounded U ∧
          (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
          (∀ d, P.dartBorders d U ↔
            (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d) ∧
          (∀ d, P.dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
          {v | ∃ d, P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
            Set.range (boundaryVertex w h) ∧
          ∀ k : ℤ, kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
            futureMapBoundaryDart w h (k - 1) := by
  filter_upwards [iidCodes_ae_finite_incident_edges,
    iidCodes_ae_boundaryHitWitnesses] with ω hfin h
  exact ⟨hfin, h, monotoneFamilyDrawing_realized_boundary_twoSided _ hfin h⟩

end DirectedDistances.KMSW
