module

public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.LLBoundaryPersistent

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open scoped Classical

private theorem kmswStage_LR_mem_mono_local (w : ℕ → Fin 3)
    {m n e : ℕ} (hmn : m ≤ n) (he : e ∈ (kmswStage w m).LR) :
    e ∈ (kmswStage w n).LR := by
  induction n, hmn using Nat.le_induction with
  | base => exact he
  | succ n _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left _ ih

private theorem boundaryHit_right_unbounded (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  by_cases ha : a ≤ -1
  · obtain ⟨n, hn⟩ := h.rightHit (-a) (by omega)
    exact ⟨n, by omega⟩
  · obtain ⟨n, hn⟩ := h.rightHit 1 (by omega)
    exact ⟨n, by omega⟩

/-- The edges eventually in the lower-right stack are exactly the right-record
edges, including the root edge at index zero. Helper toward F4c / Lemma 3.10
k287); this is not the paper result. -/
theorem kmswRunEventuallyLR_eq_range (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage w n).LR} =
      Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
  have hR := boundaryHit_right_unbounded w h
  ext e
  constructor
  · rintro ⟨n₀, he⟩
    have hInfinite : IsRightBoundaryEdge w e := by
      unfold IsRightBoundaryEdge
      apply Set.Infinite.mono (s := Set.Ici n₀) ?_ (Set.Ici_infinite _)
      intro n hn
      exact he n (Set.mem_Ici.mp hn)
    obtain ⟨j, hj⟩ := (isRightBoundaryEdge_iff w hR e).mp hInfinite
    exact ⟨j, hj.symm⟩
  · intro he
    obtain ⟨j, hj⟩ := Set.mem_range.mp he
    have hInfinite : IsRightBoundaryEdge w e :=
      (isRightBoundaryEdge_iff w hR e).mpr ⟨j, hj.symm⟩
    obtain ⟨n₀, hn₀⟩ := hInfinite.nonempty
    refine ⟨n₀, fun n hn => ?_⟩
    exact kmswStage_LR_mem_mono_local w hn hn₀

private theorem boundaryHitTime_eq_strict_left_record_local
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : q ≤ -1) (hvalue : L w m = q)
    (hrecord : ∀ j < m, L w m < L w j) :
    boundaryHitTime w h q = m := by
  have hhit : ∃ n, L w n = q := ⟨m, hvalue⟩
  have hq0 : q ≠ 0 := by omega
  have hqpos : ¬ 0 < q := by omega
  have hle : boundaryHitTime w h q ≤ m := by
    unfold boundaryHitTime
    simp only [dite_eq_right hq0, dite_eq_right hqpos]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_left_spec w h hq
    have hstrict := hrecord _ hlt
    rw [hfirst] at hstrict
    simp [hvalue] at hstrict
  omega

/-- The edges eventually in the lower-left stack are exactly the missing
edges created at first hits of the negative horizontal levels. Helper toward
F4c / Lemma 3.10 (`lem-uibot-bdy`,
the paper result. -/
theorem kmswRunEventuallyLL_eq_range (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage w n).LL} =
      Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w
          (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
  ext e
  constructor
  · rintro ⟨n₀, hevent⟩
    have he := hevent n₀ le_rfl
    rw [kmswStage_LL_eq] at he
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp he
    have hm' := List.mem_reverse.mp hm
    have hfilter := List.mem_filter.mp hm'
    have hrecord : 0 < m ∧ ∀ j < m, L w m < L w j :=
      of_decide_eq_true hfilter.2
    have hmle : m ≤ n₀ := by
      have := List.mem_range.mp hfilter.1
      omega
    have hzero : L w 0 = 0 := by simp [L]
    have hnegative : L w m ≤ -1 := by
      have h := hrecord.2 0 (by omega)
      rw [hzero] at h
      omega
    let q : ℤ := L w m
    have hq : q ≤ -1 := by simpa [q] using hnegative
    have hrecord' : ∀ j < m, L w m < L w j := hrecord.2
    have htime := boundaryHitTime_eq_strict_left_record_local w h hq rfl hrecord'
    let j : ℕ := Int.toNat (-q - 1)
    have hjcast : (j : ℤ) = -q - 1 := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    have hqrepr : q = -((j : ℤ) + 1) := by omega
    refine ⟨j, ?_⟩
    change kmswLLCreatedEdge w
      (boundaryHitTime w h (-((j : ℤ) + 1)))
      = e
    rw [← hqrepr, htime]
    exact hme
  · intro he
    obtain ⟨j, rfl⟩ := Set.mem_range.mp he
    let k : ℤ := -((j : ℤ) + 1)
    have hk : k ≤ -1 := by dsimp [k]; omega
    have hpersist := boundary_left_edge_persistent w h hk
    refine ⟨boundaryHitTime w h k, fun n hn => ?_⟩
    exact (hpersist.2 n hn).1

/-- The eventual lower-right and lower-left stack edge sets are disjoint.
Helper toward F4c / Lemma 3.10 (`lem-uibot-bdy`,
the paper result. -/
theorem kmswRunEventuallyLR_disjoint_LL (w : ℕ → Fin 3) :
    Disjoint
      {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage w n).LR}
      {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage w n).LL} := by
  simp only [Set.disjoint_left]
  intro e heLR heLL
  obtain ⟨nLR, hLR⟩ := heLR
  obtain ⟨nLL, hLL⟩ := heLL
  let n := max nLR nLL
  have heLRn := hLR n (by dsimp [n]; omega)
  have heLLn := hLL n (by dsimp [n]; omega)
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append]
    tauto)
  have hpresent := (kmswStage_status w n).2.2.1 e heLRn
  have hmissing := ((kmswStage_status w n).1 e hbound).mpr (Or.inr heLLn)
  rw [hpresent] at hmissing
  cases hmissing

end DirectedDistances.KMSW
