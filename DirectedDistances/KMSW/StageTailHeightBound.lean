module

public import DirectedDistances.KMSW.StageTailULHeight

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW




theorem kmswStage_UL_length_height (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.length = (L w n - minL w n).toNat + 1 := by
  have hlen := kmswStage_UL_length w n
  have hmin := runningMin_le (L w) n n le_rfl
  change minL w n ≤ L w n at hmin
  omega




theorem kmswStage_active_UL_height_index (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL[(L w n - minL w n).toNat]? =
      some (kmswStage w n).active := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hlen := kmswStage_UL_length_height w n
  have hi : (L w n - minL w n).toNat = xs.length := by
    rw [hxs, List.length_append, List.length_singleton] at hlen
    omega
  rw [hxs, hi]
  simp




theorem kmswStage_active_tail_UL_height_index (w : ℕ → Fin 3) (n : ℕ) :
    (((kmswStage w n).UL.map (kmswStage w n).west) ++
      [(kmswStage w n).east (kmswStage w n).active])[
        (L w n - minL w n).toNat]? =
      some ((kmswStage w n).west (kmswStage w n).active) := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hlen := kmswStage_UL_length_height w n
  have hi : (L w n - minL w n).toNat = xs.length := by
    rw [hxs, List.length_append, List.length_singleton] at hlen
    omega
  rw [hxs, hi, List.map_append, List.map_singleton, List.append_assoc]
  simp




theorem kmswStage_minL_eq_of_interval_lower_bound (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m) (hLL : ∀ k, N ≤ k → k ≤ m → minL w N ≤ L w k) :
    minL w m = minL w N := by
  obtain ⟨i, hi, hei⟩ := runningMin_attained (L w) N
  obtain ⟨j, hj, hej⟩ := runningMin_attained (L w) m
  change minL w N = L w i at hei
  change minL w m = L w j at hej
  have hle := runningMin_le (L w) m i (by omega)
  change minL w m ≤ L w i at hle
  by_cases hjN : j ≤ N
  · have hle' := runningMin_le (L w) N j hjN
    change minL w N ≤ L w j at hle'
    omega
  · have hle' := hLL j (by omega) hj
    omega




theorem kmswStage_active_tail_UL_quadrant_index (w : ℕ → Fin 3) (m : ℕ)
    (hL : ∀ k, k ≤ m → 0 ≤ L w k) :
    (((kmswStage w m).UL.map (kmswStage w m).west) ++
      [(kmswStage w m).east (kmswStage w m).active])[(L w m).toNat]? =
      some ((kmswStage w m).west (kmswStage w m).active) := by
  have hmin : minL w m = 0 := by
    obtain ⟨j, hj, hej⟩ := runningMin_attained (L w) m
    have hle := runningMin_le (L w) m 0 (Nat.zero_le _)
    have hzero : L w 0 = 0 := by simp only [L, Finset.range_zero, Finset.sum_empty]
    change minL w m ≤ L w 0 at hle
    change minL w m = L w j at hej
    have hnonneg := hL j hj
    omega
  simpa only [hmin, sub_zero] using kmswStage_active_tail_UL_height_index w m






theorem kmswStage_old_tail_height_index_obstruction :
    let w : ℕ → Fin 3 := fun k => if k = 2 then 0 else 2
    let xs := ((kmswStage w 2).UL.map (kmswStage w 2).west) ++
      [(kmswStage w 2).east (kmswStage w 2).active]
    let y := (kmswStage w 4).west (kmswStage w 4).active
    (kmswStage w 2).UR = [] ∧ y < (kmswStage w 2).nextVertex ∧
      minL w 4 = minL w 2 ∧ minL w 4 = 0 ∧
      xs = [0, 1, 2, 3] ∧ y = 3 ∧ L w 4 = 2 ∧
      xs[3]? = some y ∧ xs[(L w 4 - minL w 4).toNat]? ≠ some y := by
  decide

end DirectedDistances.KMSW
