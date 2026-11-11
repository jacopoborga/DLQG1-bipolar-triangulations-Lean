module

public import DirectedDistances.KMSW.BoundaryEnumeration
public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.PaperProofs.Section7.LongPathStageVertices

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW

private theorem coordinate_hit_by_time_of_running_min (f : ℕ → ℤ)
    (hstep : ∀ i, f i - 1 ≤ f (i + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem coordinate_hit_time_left_le (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    {m : ℕ} (hm : L w m = k) : boundaryHitTime w h k ≤ m := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  rw [htime]
  exact Nat.find_min' (h.leftHit k hk) hm

private theorem coordinate_hit_time_right_le (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k)
    {m : ℕ} (hm : R w m = -k) : boundaryHitTime w h k ≤ m := by
  have htime : boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_left (by omega : 0 < k)]
  rw [htime]
  exact Nat.find_min' (h.rightHit k hk) hm

private theorem L_hit_by_running_min (w : ℕ → Fin 3) {n : ℕ} {a : ℤ}
    (ha : a < 0) (hmin : minL w n ≤ a) :
    ∃ m ≤ n, L w m = a := by
  obtain ⟨j, hj, hJ⟩ := runningMin_attained (L w) n
  change minL w n = L w j at hJ
  have hjmin : L w j ≤ a := by rw [← hJ]; exact hmin
  obtain ⟨m, hmj, hlevel⟩ := coordinate_hit_by_time_of_running_min (L w)
    (fun i => by
      have hs : L w (i + 1) = L w i +
          (RandomWalk.lazyTwoDimensionalStep (w i)).1 := Finset.sum_range_succ _ _
      rw [hs]
      have hstep : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w i)).1 := by
        generalize hc : w i = c
        fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
      omega)
    (by simp [L]) ha hjmin
  exact ⟨m, hmj.trans hj, hlevel⟩

private theorem R_hit_by_running_min (w : ℕ → Fin 3) {n : ℕ} {a : ℤ}
    (ha : a < 0) (hmin : minR w n ≤ a) :
    ∃ m ≤ n, R w m = a := by
  obtain ⟨j, hj, hJ⟩ := runningMin_attained (R w) n
  change minR w n = R w j at hJ
  have hjmin : R w j ≤ a := by rw [← hJ]; exact hmin
  obtain ⟨m, hmj, hlevel⟩ := coordinate_hit_by_time_of_running_min (R w)
    (fun i => by
      have hs : R w (i + 1) = R w i +
          (RandomWalk.lazyTwoDimensionalStep (w i)).2 := Finset.sum_range_succ _ _
      rw [hs]
      have hstep : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w i)).2 := by
        generalize hc : w i = c
        fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
      omega)
    (by simp [R]) ha hjmin
  exact ⟨m, hmj.trans hj, hlevel⟩




theorem boundaryVertex_lt_stage_of_lowerRange (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w) (ℓ : ℤ)
    (hℓ : -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ)) :
    boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex := by
  by_cases hneg : ℓ ≤ -1
  · have hmin : minL w n ≤ ℓ := by
      have hlen := kmswStage_LL_length w n
      omega
    obtain ⟨m, hmn, hlevel⟩ := L_hit_by_running_min w
      (by omega) hmin
    have htime := (coordinate_hit_time_left_le w h0 hneg hlevel).trans hmn
    exact boundaryVertex_lt_stageNextVertex w h0 ℓ n htime
  · by_cases hzero : ℓ = 0
    · subst ℓ
      have hbound := (kmswStage_endpoints_lt_nextVertex w 0 0
        (by simp [kmswStage, kmswInit])).1
      simpa [kmswStage, kmswInit, boundaryVertex_zero] using
        hbound.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le n))
    · by_cases hone : ℓ = 1
      · subst ℓ
        have hbound := (kmswStage_endpoints_lt_nextVertex w 0 0
          (by simp [kmswStage, kmswInit])).2
        simpa [kmswStage, kmswInit, boundaryVertex_one] using
          hbound.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le n))
      · have hpos : 2 ≤ ℓ := by omega
        let k : ℤ := ℓ - 1
        have hk : 1 ≤ k := by dsimp [k]; omega
        have hmin : minR w n ≤ -k := by
          have hlen := kmswStage_LR_length w n
          dsimp [k]
          omega
        obtain ⟨m, hmn, hlevel⟩ := R_hit_by_running_min w
          (by omega) hmin
        have htime := coordinate_hit_time_right_le w h0 hk hlevel
        have htimeN : boundaryHitTime w h0 k ≤ n := htime.trans hmn
        obtain ⟨N, htN, hEdge⟩ := boundaryVertex_right_edge w h0 hk
        let e := act w (boundaryHitTime w h0 k)
        have heBound := act_lt_nextEdge w (Nat.le_refl (boundaryHitTime w h0 k))
        have hStableN := kmswStage_endpoints_stable w htN heBound
        have hEastAtHit : (kmswStage w (boundaryHitTime w h0 k)).east e =
            boundaryVertex w h0 (k + 1) := by
          dsimp [e]
          calc
            (kmswStage w (boundaryHitTime w h0 k)).east
                (act w (boundaryHitTime w h0 k)) =
              (kmswStage w N).east (act w (boundaryHitTime w h0 k)) :=
                hStableN.2.symm
            _ = boundaryVertex w h0 (k + 1) := (hEdge N le_rfl).2.2.2
        have hStableTarget := kmswStage_endpoints_stable w htimeN heBound
        have hEastTarget : (kmswStage w n).east e = boundaryVertex w h0 ℓ := by
          have hkadd : k + 1 = ℓ := by dsimp [k]; omega
          calc
            (kmswStage w n).east e =
                (kmswStage w (boundaryHitTime w h0 k)).east e :=
              hStableTarget.2
            _ = boundaryVertex w h0 (k + 1) := hEastAtHit
            _ = boundaryVertex w h0 ℓ := by rw [hkadd]
        have hEndpoints := kmswStage_endpoints_lt_nextVertex w n e
          (act_lt_nextEdge w htimeN)
        simpa [e, hEastTarget] using hEndpoints.2

end DirectedDistances.PaperProofs.Section7
