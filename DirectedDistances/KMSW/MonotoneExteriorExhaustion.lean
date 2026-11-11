module

public import DirectedDistances.KMSW.MonotoneLimitExterior
public import DirectedDistances.KMSW.MonotoneLRGrowth










public section
namespace DirectedDistances.KMSW

open Set DirectedDistances.PlanarMap

private theorem layoutArc_stable_of_le {w : ℕ → Fin 3} {n m e : ℕ}
    (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

/-- Under `hL0`, every point of a stage lower boundary lies on a persistent lower-right
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStageLowerTrace_persistentLR {w : ℕ → Fin 3}
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    graphOver (G n).xmin (G n).xmax (G n).lower ⊆ monotonePersistentLRTrace w := by
  classical
  intro z hzLower
  rw [(G n).lower_trace] at hzLower
  obtain ⟨e, hzLower⟩ := mem_iUnion.mp hzLower
  obtain ⟨heLower, hzTrace⟩ := mem_iUnion.mp hzLower
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heLower ⊢
      tauto)
  have hLL := kmswStage_LL_eq_nil w hL0 n
  have heLR : e ∈ (kmswStage w n).LR := by
    rw [hLL, List.nil_append] at heLower
    exact heLower
  have hstay (m : ℕ) (hnm : n ≤ m) : e ∈ (kmswStage w m).LR := by
    induction hnm with
    | refl => exact heLR
    | @step m hnm ih =>
      obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w m
      rw [ht]
      exact List.mem_append.mpr (Or.inl ih)
  have hInfinite : IsRightBoundaryEdge w e := by
    apply Set.Infinite.mono (s := Set.Ici n) ?_ (Set.Ici_infinite n)
    intro m hm
    exact hstay m (Set.mem_Ici.mp hm)
  obtain ⟨i, hi⟩ := (isRightBoundaryEdge_iff w hR e).mp hInfinite
  have hzArc : z ∈ (layoutArc w n e).image := by
    have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
      simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hArcStable : layoutArc w n e = layoutArc w e e := by
    let m := max n e
    calc
      layoutArc w n e = layoutArc w m e :=
        (layoutArc_stable_of_le (le_max_left n e) he).symm
      _ = layoutArc w e e :=
        layoutArc_stable_of_le (le_max_right n e) (kmsw_edge_allocated_by_self w e)
  rw [hi] at hzArc hArcStable
  rw [hArcStable] at hzArc
  exact ⟨i, hzArc⟩

/-- Under `hfin`, `htrans`, `hR` and the one-sided hypothesis `hL0 : ∀ j, 0 ≤ L w j`, the stage
regions of every family of monotone stage invariants exhaust bounded sets (`remark-kmsw-infinite`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneRegionBoundedExhaustion_of_KMSW (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    monotoneRegionBoundedExhaustion Q G := by
  intro K hK
  obtain ⟨A, hA⟩ := hK.subset_closedBall (0 : ℂ)
  obtain ⟨N1, hN1⟩ := monotoneStage_xmax_unbounded w hR Q G A
  obtain ⟨N2, hN2⟩ := monotoneStageUpperTrace_eventually_persistentUL hfin htrans hR Q G
    (Metric.closedBall (0 : ℂ) (2 * A)) Metric.isBounded_closedBall
  refine ⟨max N1 N2, fun n hn z hzK => ?_⟩
  by_cases hz : z ∈ monotoneStageRegion Q G n
  · exact Or.inl hz
  right
  suffices h : ∃ N', ∀ m, N' ≤ m → z ∉ monotoneStageRegion Q G m by
    obtain ⟨N', hN'⟩ := h
    intro m hm
    exact hN' (max m N') (le_max_right _ _)
      (monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G (le_max_left _ _) hm)
  have hzA : ‖z‖ ≤ A := by
    have := hA hzK
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hre_le : |z.re| ≤ A := (Complex.abs_re_le_norm z).trans hzA
  have him_le : |z.im| ≤ A := (Complex.abs_im_le_norm z).trans hzA
  have hxmin : (G n).xmin = 0 := monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 (G n)
  have hxmax : A ≤ (G n).xmax := hN1 n (le_of_max_le_left hn)
  have hz' : ¬ (0 ≤ z.re ∧ z.re ≤ (G n).xmax ∧ (G n).lower z.re ≤ z.im ∧
      z.im ≤ (G n).upper z.re) := by
    intro h
    apply hz
    change z ∈ closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper
    rw [hxmin]
    exact h
  by_cases hneg : z.re < 0
  · refine ⟨0, fun m _ hzm => ?_⟩
    have hx0 := monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 (G m)
    have hle : (G m).xmin ≤ z.re := hzm.1
    linarith
  have hre0 : 0 ≤ z.re := not_lt.mp hneg
  have hrex : z.re ≤ (G n).xmax := by linarith [le_abs_self z.re]
  by_cases hup : (G n).upper z.re < z.im
  · let q : ℂ := ⟨z.re, (G n).upper z.re⟩
    have hq : q ∈ graphOver (G n).xmin (G n).xmax (G n).upper := by
      refine ⟨?_, hrex, rfl⟩
      rw [hxmin]
      exact hre0
    have hq0 : 0 ≤ q.im := monotoneUpperTrace_nonneg Q G hq
    have hqK : q ∈ Metric.closedBall (0 : ℂ) (2 * A) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖q‖ ≤ |q.re| + |q.im| := Complex.norm_le_abs_re_add_abs_im q
      have h2 : |q.im| ≤ A := by
        rw [abs_of_nonneg hq0]
        have hlt : q.im < z.im := hup
        linarith [le_abs_self z.im]
      have h3 : |q.re| ≤ A := hre_le
      linarith
    obtain ⟨i, hi⟩ := hN2 n (le_of_max_le_right hn) ⟨hq, hqK⟩
    exact monotoneStageRegion_excludes_above_persistentUL htrans Q G i hi rfl hup
  · have hlow : z.im < (G n).lower z.re := by
      by_contra hcon
      exact hz' ⟨hre0, hrex, not_lt.mp hcon, not_lt.mp hup⟩
    let q : ℂ := ⟨z.re, (G n).lower z.re⟩
    have hq : q ∈ graphOver (G n).xmin (G n).xmax (G n).lower := by
      refine ⟨?_, hrex, rfl⟩
      rw [hxmin]
      exact hre0
    obtain ⟨i, hi⟩ := monotoneStageLowerTrace_persistentLR hL0 hR Q G n hq
    exact monotoneStageRegion_excludes_below_persistentLR hR Q G i hi rfl hlow

end DirectedDistances.KMSW
