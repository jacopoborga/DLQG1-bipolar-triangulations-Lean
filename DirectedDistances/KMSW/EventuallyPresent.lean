module

public import DirectedDistances.KMSW.BoundaryDynamics
import DirectedDistances.KMSW.BoundaryRecordsMissing
import DirectedDistances.KMSW.BoundaryRecordsUL
import DirectedDistances.KMSW.CutEquivalenceConverse
import DirectedDistances.KMSW.StageIncidence

/-! # Eventually present KMSW edges -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

private theorem present_forever (w : ℕ → Fin 3) {e n : ℕ} (hen : e < n)
    (hp : (kmswStage w n).present e = true) :
    ∀ k, n ≤ k → (kmswStage w k).present e = true := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hp
  | succ k hnk ih =>
    have hlt : e < (kmswStage w k).nextEdge := by
      have := CutConverse.nextEdge_ge_time_add_UR w k
      omega
    have h := kmswStep_present_existing (kmswStage w k) (w k) hlt
    change (kmswStep (kmswStage w k) (w k)).present e = true
    rw [h]
    split <;> simp [ih]

/-- Every edge ID is eventually allocated and permanently present, when `L` stays -/
theorem eventually_present_of_nonneg_of_unbounded (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) :
    ∃ N, ∀ n, N ≤ n → e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true := by
  obtain ⟨n, hn⟩ := hR (-(∑ t ∈ Finset.range (e + 1), |R w t|) - 1)
  have hbelow : ∀ t, t ≤ e → R w n < R w t := by
    intro t ht
    have h1 : |R w t| ≤ ∑ t ∈ Finset.range (e + 1), |R w t| :=
      Finset.single_le_sum (f := fun t => |R w t|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have h2 := neg_abs_le (R w t)
    omega
  have hne : e < n := by
    by_contra h
    have := hbelow n (by omega)
    omega
  have hlt : ∀ k, e < k → e < (kmswStage w k).nextEdge := by
    intro k hk
    have := CutConverse.nextEdge_ge_time_add_UR w k
    omega
  have hpres : (kmswStage w n).present e = true := by
    by_contra hnp
    have hfalse : (kmswStage w n).present e = false := by simpa using hnp
    have hstat := ((kmswStage_status w n).1 e (hlt n hne)).mp hfalse
    have hLL : (kmswStage w n).LL.length = 0 := by
      have hlen := kmswStage_LL_length w n
      obtain ⟨i, _, hi⟩ := runningMin_attained (L w) n
      have h0 := runningMin_le (L w) n 0 (Nat.zero_le _)
      have hz : L w 0 = 0 := by simp [L]
      have := hL0 i
      change minL w n = L w i at hi
      change minL w n ≤ L w 0 at h0
      omega
    rcases hstat with hUR | hLLm
    · rw [kmswStage_UR_eq] at hUR
      obtain ⟨m, hm, hme⟩ := List.mem_map.mp hUR
      have hm' := (List.mem_filter.mp (List.mem_reverse.mp hm)).2
      obtain ⟨hm0, hmn, hfut⟩ := of_decide_eq_true hm'
      have hge := CutConverse.nextEdge_ge_time_add_UR w m
      have hme' : (kmswStage w m).nextEdge - 1 = e := hme
      have hmle : m ≤ e := by omega
      have := hfut n hmn le_rfl
      have := hbelow (m - 1) (by omega)
      omega
    · have := List.length_pos_iff.mpr (List.ne_nil_of_mem hLLm)
      omega
  exact ⟨n, fun k hk => ⟨hlt k (by omega), present_forever w hne hpres k hk⟩⟩

end DirectedDistances.KMSW
