module

public import DirectedDistances.KMSW.MonotoneExteriorExhaustion

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.KMSW

open Set DirectedDistances.PlanarMap

variable {w : ℕ → Fin 3} {Q : ∀ n, StageDrawing w n}
  {G : ∀ n, MonotoneStageInvariant w n (Q n)}

/-- Membership in the limit exterior (`remark-kmsw-infinite`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem mem_monotoneLimitExterior_iff {z : ℂ} :
    z ∈ monotoneLimitExterior Q G ↔ ∀ m, z ∉ monotoneStageRegion Q G m := by
  simp [monotoneLimitExterior, monotoneStageRegionUnion]

/-- Lower boundary traces have nonnegative height (`def-kmsw`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneLowerTrace_nonneg (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {n : ℕ} {z : ℂ}
    (hz : z ∈ graphOver (G n).xmin (G n).xmax (G n).lower) : 0 ≤ z.im := by
  rw [(G n).lower_trace] at hz
  obtain ⟨e, hz⟩ := mem_iUnion.mp hz
  obtain ⟨heLower, hzTrace⟩ := mem_iUnion.mp hz
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heLower ⊢
      tauto)
  have hzArc : z ∈ (layoutArc w n e).image := by
    have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
      simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hheight := layoutArc_height_lower w n e he z hzArc
  have hw : 0 ≤ (layoutPos w n ((kmswStage w n).west e)).im := by
    simpa [layoutPos] using layoutHeight_nonneg w n ((kmswStage w n).west e)
  have heast : 0 ≤ (layoutPos w n ((kmswStage w n).east e)).im := by
    simpa [layoutPos] using layoutHeight_nonneg w n ((kmswStage w n).east e)
  exact (le_min hw heast).trans hheight

/-- Stage regions lie in the closed upper half-plane (`def-kmsw`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStageRegion_im_nonneg {n : ℕ} {z : ℂ}
    (hz : z ∈ monotoneStageRegion Q G n) : 0 ≤ z.im := by
  obtain ⟨h1, h2, h3, _⟩ := hz
  have hq : (⟨z.re, (G n).lower z.re⟩ : ℂ) ∈
      graphOver (G n).xmin (G n).xmax (G n).lower := ⟨h1, h2, rfl⟩
  have h0 : 0 ≤ (G n).lower z.re := monotoneLowerTrace_nonneg Q G hq
  exact h0.trans h3

/-- The open lower half-plane lies in the limit exterior (`remark-kmsw-infinite`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem lowerHalf_subset_monotoneLimitExterior :
    {z : ℂ | z.im < 0} ⊆ monotoneLimitExterior Q G := by
  intro z hz
  rw [mem_monotoneLimitExterior_iff]
  intro m hm
  have h0 := monotoneStageRegion_im_nonneg hm
  change z.im < 0 at hz
  linarith

/-- Under `hL0` the open left half-plane lies in the limit exterior
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem leftHalf_subset_monotoneLimitExterior (hL0 : ∀ j, 0 ≤ L w j) :
    {z : ℂ | z.re < 0} ⊆ monotoneLimitExterior Q G := by
  intro z hz
  rw [mem_monotoneLimitExterior_iff]
  intro m hm
  have h0 := monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 (G m)
  have h1 : (G m).xmin ≤ z.re := hm.1
  change z.re < 0 at hz
  linarith

private theorem region_vertical {n : ℕ} {p y z : ℂ}
    (hp : p ∈ monotoneStageRegion Q G n) (hy : y ∈ monotoneStageRegion Q G n)
    (hpre : p.re = z.re) (hyre : y.re = z.re) (h1 : p.im ≤ z.im) (h2 : z.im ≤ y.im) :
    z ∈ monotoneStageRegion Q G n := by
  obtain ⟨hp1, hp2, hp3, _⟩ := hp
  obtain ⟨_, _, _, hy4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hpre]
    exact hp1
  · rw [← hpre]
    exact hp2
  · rw [← hpre]
    exact hp3.trans h1
  · rw [← hyre]
    exact h2.trans hy4

/-- Below an exterior point that lies under a stage-region point, the whole downward
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneLimitExterior_down {z y : ℂ} {n : ℕ}
    (hz : z ∈ monotoneLimitExterior Q G) (hy : y ∈ monotoneStageRegion Q G n)
    (hyre : y.re = z.re) (hlt : z.im < y.im) {p : ℂ} (hpre : p.re = z.re)
    (hpim : p.im ≤ z.im) : p ∈ monotoneLimitExterior Q G := by
  rw [mem_monotoneLimitExterior_iff] at hz ⊢
  intro m hpm
  have hpk := monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G
    (le_max_left m n) hpm
  have hyk := monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G
    (le_max_right m n) hy
  exact hz (max m n) (region_vertical hpk hyk hpre hyre hpim hlt.le)

/-- Above an exterior point that lies over a stage-region point, the whole upward
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneLimitExterior_up {z y : ℂ} {n : ℕ}
    (hz : z ∈ monotoneLimitExterior Q G) (hy : y ∈ monotoneStageRegion Q G n)
    (hyre : y.re = z.re) (hlt : y.im < z.im) {p : ℂ} (hpre : p.re = z.re)
    (hpim : z.im ≤ p.im) : p ∈ monotoneLimitExterior Q G := by
  rw [mem_monotoneLimitExterior_iff] at hz ⊢
  intro m hpm
  have hpk := monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G
    (le_max_left m n) hpm
  have hyk := monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G
    (le_max_right m n) hy
  exact hz (max m n) (region_vertical hyk hpk hyre hpre hlt.le hpim)

/-- Any two points of the open lower half-plane are joined inside the limit exterior.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem joinedIn_lowerHalf {z c : ℂ} (hz : z.im < 0) (hc : c.im < 0) :
    JoinedIn (monotoneLimitExterior Q G) z c := by
  have hconv : Convex ℝ {p : ℂ | p.im < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage Complex.imLm
  exact ((hconv.isPathConnected ⟨z, hz⟩).joinedIn z hz c hc).mono
    lowerHalf_subset_monotoneLimitExterior

/-- Under `hL0`, any two points of the open left half-plane are joined inside the limit
exterior. Helper toward the plane-realization obligation of adjudication n308; not a paper
result. -/
theorem joinedIn_leftHalf (hL0 : ∀ j, 0 ≤ L w j) {z c : ℂ} (hz : z.re < 0)
    (hc : c.re < 0) : JoinedIn (monotoneLimitExterior Q G) z c := by
  have hconv : Convex ℝ {p : ℂ | p.re < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage Complex.reLm
  exact ((hconv.isPathConnected ⟨z, hz⟩).joinedIn z hz c hc).mono
    (leftHalf_subset_monotoneLimitExterior hL0)

private theorem arc_stable_of_le {n m e : ℕ} (hnm : n ≤ m)
    (he : e < (kmswStage w n).nextEdge) : layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

private theorem arc_eq_of_allocated {a b e : ℕ} (ha : e < (kmswStage w a).nextEdge)
    (hb : e < (kmswStage w b).nextEdge) : layoutArc w a e = layoutArc w b e := by
  rcases le_total a b with h | h
  · exact (arc_stable_of_le h ha).symm
  · exact arc_stable_of_le h hb

private theorem UL_prefix_eventually (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (i : ℕ) : ∃ M, ∀ m, M ≤ m → ∀ j, j ≤ i →
      (kmswStage w m).UL[j]? = some (kmswLeftBoundaryEdge w j) := by
  induction i with
  | zero =>
    obtain ⟨N, hN⟩ := kmswStage_UL_getElem?_eventually w htrans 0
    refine ⟨N, fun m hm j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    exact hN m hm
  | succ i ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨N, hN⟩ := kmswStage_UL_getElem?_eventually w htrans (i + 1)
    refine ⟨max M N, fun m hm j hj => ?_⟩
    rcases Nat.lt_or_ge j (i + 1) with h | h
    · exact hM m (le_of_max_le_left hm) j (by omega)
    · have hji : j = i + 1 := by omega
      subst hji
      exact hN m (le_of_max_le_right hm)

private theorem UL_prefix_cover (hL0 : ∀ j, 0 ≤ L w j) {m i : ℕ} {P : StageDrawing w m}
    (Gm : MonotoneStageInvariant w m P)
    (hpre : ∀ j, j ≤ i → (kmswStage w m).UL[j]? = some (kmswLeftBoundaryEdge w j)) :
    ∀ j, j ≤ i → ∀ x : ℝ, 0 ≤ x →
      x ≤ (layoutPos w m ((kmswStage w m).east (kmswLeftBoundaryEdge w j))).re →
      ∃ k, k ≤ j ∧
        (layoutPos w m ((kmswStage w m).west (kmswLeftBoundaryEdge w k))).re ≤ x ∧
        x ≤ (layoutPos w m ((kmswStage w m).east (kmswLeftBoundaryEdge w k))).re := by
  intro j
  induction j with
  | zero =>
    intro _ x hx0 hx1
    refine ⟨0, le_rfl, ?_, hx1⟩
    have h0 := hpre 0 (Nat.zero_le _)
    have hne : (kmswStage w m).UL ≠ [] := by
      intro h
      simp [h] at h0
    have hhead : ((kmswStage w m).UL ++ (kmswStage w m).UR).head
        (kmswStage_boundary_nonempty w m).1 = kmswLeftBoundaryEdge w 0 := by
      have h1 := List.head?_eq_some_head (kmswStage_boundary_nonempty w m).1
      rw [List.head?_append_of_ne_nil _ hne, List.head?_eq_getElem?, h0] at h1
      exact (Option.some_injective _ h1).symm
    have hx := Gm.xmin_eq_upper_start
    rw [hhead, monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 Gm] at hx
    rw [← hx]
    exact hx0
  | succ j ih =>
    intro hj x hx0 hx1
    have hj1 := hpre (j + 1) hj
    have hj0 := hpre j (by omega)
    obtain ⟨hlt1, heq1⟩ := List.getElem?_eq_some_iff.mp hj1
    obtain ⟨hlt0, heq0⟩ := List.getElem?_eq_some_iff.mp hj0
    have hlen : j + 1 < ((kmswStage w m).UL ++ (kmswStage w m).UR).length := by
      rw [List.length_append]
      omega
    have hR := (kmswStage_upper_chain w m).getElem j hlen
    rw [List.getElem_append_left hlt0, List.getElem_append_left hlt1, heq0, heq1] at hR
    by_cases hle : x ≤ (layoutPos w m ((kmswStage w m).east (kmswLeftBoundaryEdge w j))).re
    · obtain ⟨k, hk, hk1, hk2⟩ := ih (by omega) x hx0 hle
      exact ⟨k, by omega, hk1, hk2⟩
    · refine ⟨j + 1, le_rfl, ?_, hx1⟩
      rw [← hR]
      exact (not_le.mp hle).le

private theorem upper_le_of_persistent {M m j : ℕ} (hMm : M ≤ m)
    (hjM : (kmswStage w M).UL[j]? = some (kmswLeftBoundaryEdge w j))
    (hjm : (kmswStage w m).UL[j]? = some (kmswLeftBoundaryEdge w j)) {x : ℝ}
    (hx1 : (layoutPos w m ((kmswStage w m).west (kmswLeftBoundaryEdge w j))).re ≤ x)
    (hx2 : x ≤ (layoutPos w m ((kmswStage w m).east (kmswLeftBoundaryEdge w j))).re) :
    (G m).upper x ≤ M := by
  have heM : kmswLeftBoundaryEdge w j ∈ (kmswStage w M).UL := List.mem_of_getElem? hjM
  have hem : kmswLeftBoundaryEdge w j ∈ (kmswStage w m).UL := List.mem_of_getElem? hjm
  have heltM : kmswLeftBoundaryEdge w j < (kmswStage w M).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w M).2 _ (by simp [heM])
  have heltm : kmswLeftBoundaryEdge w j < (kmswStage w m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w m).2 _ (by simp [hem])
  obtain ⟨f, hf⟩ := layoutArc_image_graph w m _ heltm
  have hz : (⟨x, f x⟩ : ℂ) ∈ (layoutArc w m (kmswLeftBoundaryEdge w j)).image := by
    rw [hf]
    exact ⟨hx1, hx2, rfl⟩
  have hup := (G m).upper_eq_arc_height (List.mem_append_left _ hem) hz
  have hzM : (⟨x, f x⟩ : ℂ) ∈ (layoutArc w M (kmswLeftBoundaryEdge w j)).image := by
    rwa [arc_stable_of_le hMm heltM] at hz
  have hzimg : (⟨x, f x⟩ : ℂ) ∈ (Q M).image := by
    have hd : (Q M).arc (⟨⟨kmswLeftBoundaryEdge w j, heltM⟩, false⟩) =
        layoutArc w M (kmswLeftBoundaryEdge w j) := by
      simpa using (G M).arc_layout (⟨⟨kmswLeftBoundaryEdge w j, heltM⟩, false⟩)
    exact Or.inr ⟨⟨⟨kmswLeftBoundaryEdge w j, heltM⟩, false⟩, by rw [hd]; exact hzM⟩
  have hh := (G M).image_height_le _ hzimg
  change (G m).upper x = f x at hup
  change f x ≤ (M : ℝ) at hh
  rw [hup]
  exact hh

private theorem segment_re_im {a b p : ℂ} (hp : p ∈ segment ℝ a b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ p.re = a.re + θ * (b.re - a.re) ∧
      p.im = a.im + θ * (b.im - a.im) := by
  rw [segment_eq_image'] at hp
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hp
  refine ⟨θ, h0, h1, ?_, ?_⟩ <;> simp




theorem monotoneLimitExterior_isPathConnected_of_KMSW (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    IsPathConnected (monotoneLimitExterior Q G) := by
  let c : ℂ := ⟨-1, -1⟩
  have hcim : c.im < 0 := by show (-1 : ℝ) < 0; norm_num
  have hcre : c.re < 0 := by show (-1 : ℝ) < 0; norm_num
  have hc : c ∈ monotoneLimitExterior Q G := lowerHalf_subset_monotoneLimitExterior hcim
  suffices key : ∀ z ∈ monotoneLimitExterior Q G,
      JoinedIn (monotoneLimitExterior Q G) z c by
    refine isPathConnected_iff.mpr ⟨⟨c, hc⟩, fun x hx y hy => ?_⟩
    exact (key x hx).trans (key y hy).symm
  intro z hz
  by_cases hneg : z.re < 0
  · exact joinedIn_leftHalf hL0 hneg hcre
  by_cases himneg : z.im < 0
  · exact joinedIn_lowerHalf himneg hcim
  have hre0 : 0 ≤ z.re := not_lt.mp hneg
  have him0 : 0 ≤ z.im := not_lt.mp himneg
  obtain ⟨N1, hN1⟩ := monotoneStage_xmax_unbounded w hR Q G z.re
  obtain ⟨N2, hN2⟩ := monotoneStageUpperTrace_eventually_persistentUL hfin htrans hR Q G
    (Metric.closedBall (0 : ℂ) (2 * ‖z‖)) Metric.isBounded_closedBall
  have hxmax : z.re ≤ (G (max N1 N2)).xmax := hN1 (max N1 N2) (le_max_left _ _)
  have hxmin : (G (max N1 N2)).xmin = 0 :=
    monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 (G (max N1 N2))
  have hzn : z ∉ monotoneStageRegion Q G (max N1 N2) :=
    (mem_monotoneLimitExterior_iff.mp hz) (max N1 N2)
  have hrange : z.re ∈ Icc (G (max N1 N2)).xmin (G (max N1 N2)).xmax :=
    ⟨by rw [hxmin]; exact hre0, hxmax⟩
  by_cases hup : (G (max N1 N2)).upper z.re < z.im
  · let y : ℂ := ⟨z.re, (G (max N1 N2)).upper z.re⟩
    have hyR : y ∈ monotoneStageRegion Q G (max N1 N2) :=
      ⟨hrange.1, hrange.2, (G (max N1 N2)).lower_le_upper z.re hrange, le_rfl⟩
    have hyg : y ∈ graphOver (G (max N1 N2)).xmin (G (max N1 N2)).xmax
        (G (max N1 N2)).upper := ⟨hrange.1, hrange.2, rfl⟩
    have hy0 : 0 ≤ y.im := monotoneUpperTrace_nonneg Q G hyg
    have hyK : y ∈ Metric.closedBall (0 : ℂ) (2 * ‖z‖) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ |y.re| + |y.im| := Complex.norm_le_abs_re_add_abs_im y
      have h2 : |y.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h3 : |y.im| ≤ ‖z‖ := by
        rw [abs_of_nonneg hy0]
        have hlt : y.im < z.im := hup
        have h4 := Complex.abs_im_le_norm z
        linarith [le_abs_self z.im]
      linarith
    obtain ⟨i, hi⟩ := hN2 (max N1 N2) (le_max_right _ _) ⟨hyg, hyK⟩
    obtain ⟨M, hM⟩ := UL_prefix_eventually htrans i
    have hTz : z.im < max (M : ℝ) z.im + 1 := by linarith [le_max_right (M : ℝ) z.im]
    have hTM : (M : ℝ) < max (M : ℝ) z.im + 1 := by linarith [le_max_left (M : ℝ) z.im]
    have hrow : ∀ x : ℝ, 0 ≤ x → x ≤ z.re →
        (⟨x, max (M : ℝ) z.im + 1⟩ : ℂ) ∈ monotoneLimitExterior Q G := by
      intro x hx0 hxz
      rw [mem_monotoneLimitExterior_iff]
      intro m hm
      have hmk := monotoneStageRegion_subset_of_le_fromKMSWHypotheses Q G
        (le_max_left m M) hm
      have hpre := hM (max m M) (le_max_right _ _)
      have hiUL : kmswLeftBoundaryEdge w i ∈ (kmswStage w (max m M)).UL :=
        List.mem_of_getElem? (hpre i le_rfl)
      have hilt : kmswLeftBoundaryEdge w i < (kmswStage w (max m M)).nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge w _).2 _ (by simp [hiUL])
      have hyk : y ∈ (layoutArc w (max m M) (kmswLeftBoundaryEdge w i)).image := by
        rw [arc_eq_of_allocated hilt (kmsw_edge_allocated_by_self w _)]
        exact hi
      obtain ⟨f, hf⟩ := layoutArc_image_graph w (max m M) _ hilt
      rw [hf] at hyk
      have hyre : z.re ≤ (layoutPos w (max m M)
          ((kmswStage w (max m M)).east (kmswLeftBoundaryEdge w i))).re := hyk.2.1
      obtain ⟨k0, hk0, hk1, hk2⟩ := UL_prefix_cover hL0 (G (max m M)) hpre i le_rfl x hx0
        (hxz.trans hyre)
      have hbound := upper_le_of_persistent (G := G) (le_max_right m M)
        (hM M le_rfl k0 hk0) (hpre k0 hk0) hk1 hk2
      have hin : max (M : ℝ) z.im + 1 ≤ (G (max m M)).upper x := hmk.2.2.2
      linarith
    have h1 : JoinedIn (monotoneLimitExterior Q G) z ⟨z.re, max (M : ℝ) z.im + 1⟩ := by
      apply JoinedIn.of_segment_subset
      intro p hp
      obtain ⟨θ, hθ0, _, hpre, hpim⟩ := segment_re_im hp
      apply monotoneLimitExterior_up hz hyR rfl hup
      · rw [hpre]
        show z.re + θ * (z.re - z.re) = z.re
        ring
      · rw [hpim]
        show z.im ≤ z.im + θ * (max (M : ℝ) z.im + 1 - z.im)
        have hnn : 0 ≤ θ * (max (M : ℝ) z.im + 1 - z.im) :=
          mul_nonneg hθ0 (by linarith)
        linarith
    have h2 : JoinedIn (monotoneLimitExterior Q G) ⟨z.re, max (M : ℝ) z.im + 1⟩
        ⟨-1, max (M : ℝ) z.im + 1⟩ := by
      apply JoinedIn.of_segment_subset
      intro p hp
      obtain ⟨θ, hθ0, _, hpre, hpim⟩ := segment_re_im hp
      have hpim' : p.im = max (M : ℝ) z.im + 1 := by
        rw [hpim]
        show max (M : ℝ) z.im + 1 +
          θ * (max (M : ℝ) z.im + 1 - (max (M : ℝ) z.im + 1)) = max (M : ℝ) z.im + 1
        ring
      by_cases hpneg : p.re < 0
      · exact leftHalf_subset_monotoneLimitExterior hL0 hpneg
      · have hp0 : 0 ≤ p.re := not_lt.mp hpneg
        have hpz : p.re ≤ z.re := by
          rw [hpre]
          show z.re + θ * (-1 - z.re) ≤ z.re
          have hnn : 0 ≤ θ * (1 + z.re) := mul_nonneg hθ0 (by linarith)
          linarith
        have hpeq : p = ⟨p.re, max (M : ℝ) z.im + 1⟩ := Complex.ext rfl hpim'
        rw [hpeq]
        exact hrow p.re hp0 hpz
    have h3 : JoinedIn (monotoneLimitExterior Q G) ⟨-1, max (M : ℝ) z.im + 1⟩ c :=
      joinedIn_leftHalf hL0 (show (-1 : ℝ) < 0 by norm_num) hcre
    exact (h1.trans h2).trans h3
  · have hlow : z.im < (G (max N1 N2)).lower z.re := by
      by_contra hcon
      exact hzn ⟨hrange.1, hrange.2, not_lt.mp hcon, not_lt.mp hup⟩
    let y : ℂ := ⟨z.re, (G (max N1 N2)).lower z.re⟩
    have hyR : y ∈ monotoneStageRegion Q G (max N1 N2) :=
      ⟨hrange.1, hrange.2, le_rfl, (G (max N1 N2)).lower_le_upper z.re hrange⟩
    have h1 : JoinedIn (monotoneLimitExterior Q G) z ⟨z.re, -1⟩ := by
      apply JoinedIn.of_segment_subset
      intro p hp
      obtain ⟨θ, hθ0, _, hpre, hpim⟩ := segment_re_im hp
      apply monotoneLimitExterior_down hz hyR rfl hlow
      · rw [hpre]
        show z.re + θ * (z.re - z.re) = z.re
        ring
      · rw [hpim]
        show z.im + θ * (-1 - z.im) ≤ z.im
        have hnn : 0 ≤ θ * (1 + z.im) := mul_nonneg hθ0 (by linarith)
        linarith
    exact h1.trans (joinedIn_lowerHalf (show (-1 : ℝ) < 0 by norm_num) hcim)

end DirectedDistances.KMSW
