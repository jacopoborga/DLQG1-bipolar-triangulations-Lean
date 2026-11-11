module

public import DirectedDistances.KMSW.UpperVertexFutureTail
import DirectedDistances.KMSW.StageActiveEdges

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW




theorem kmswStage_active_of_becomes_present (w : ℕ → Fin 3) {m e : ℕ}
    (hnew : ¬ e < (kmswStage w m).nextEdge ∨
      (kmswStage w m).present e = false)
    (he : e < (kmswStage w (m + 1)).nextEdge)
    (hp : (kmswStage w (m + 1)).present e = true) :
    (kmswStage w (m + 1)).active = e := by
  obtain ⟨t, ht, hte⟩ := kmswStage_present_eq_active w (m + 1) e he hp
  by_cases htm : t ≤ m
  · have hpast : (kmswStage w m).present e = true := by
      rw [← hte]
      exact kmswStage_active_present_mono w htm
    have heast : e < (kmswStage w m).nextEdge := by
      rw [← hte]
      exact (act_lt_nextEdge w le_rfl).trans_le
        (kmswStage_nextEdge_mono w htm)
    rcases hnew with hnalloc | hmissing
    · exact False.elim (hnalloc heast)
    · rw [hpast] at hmissing
      cases hmissing
  · have htm' : t = m + 1 := by omega
    subst t
    exact hte




private theorem upperTail_right_unbounded (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (a : ℤ) : ∃ n, R w n ≤ a := by
  obtain ⟨n, hn⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
  exact ⟨n, by omega⟩



private theorem upperTail_pending (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {n y : ℕ} (hy : y ∈ CutConverse.pendingVertices (kmswStage w n)) :
    ∃ m ≥ n, (kmswStage w m).west (kmswStage w m).active = y := by
  have hybound : y < (kmswStage w n).nextVertex := by
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy]
      exact (CutConverse.endpoint_bound w n _ (kmswStage_active_lt w n)).2
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      have he' := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        tauto)
      exact (CutConverse.endpoint_bound w n e he').2
  obtain ⟨m, hm⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded w
    (upperTail_right_unbounded w h) y ⟨n, hybound⟩
  have hnm : n ≤ m := by
    by_contra hnot
    have hnever := (CutConverse.frontier_history w n).2.2 m (by omega)
    exact hnever (hm.symm ▸ hy)
  exact ⟨m, hnm, (CutConverse.activeInitial_eq w m).symm.trans hm⟩



private theorem upperTail_UR (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {n y : ℕ} (hy : ∃ e ∈ (kmswStage w n).UR,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) :
    ∃ m ≥ n, (kmswStage w m).west (kmswStage w m).active = y := by
  obtain ⟨e, he, hwest | heast⟩ := hy
  · apply upperTail_pending w h
    have hmem : y ∈ (kmswStage w n).UR.map (kmswStage w n).west :=
      List.mem_map.mpr ⟨e, he, hwest⟩
    rw [(CutConverse.frontier_history w n).1] at hmem
    exact List.dropLast_subset _ hmem
  · apply upperTail_pending w h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, heast⟩)




private theorem upperTail_left_return (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {a n : ℕ} (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j) :
    ∃ m ≥ n, L w m = L w a ∧
      ∀ j, a ≤ j → j ≤ m → L w a ≤ L w j := by
  classical
  obtain ⟨q, hq⟩ := h.leftHit
    (min (-1) (min (minL w n - 1) (L w a))) (min_le_left _ _)
  have hnq : n < q := by
    by_contra hnot
    have hmin := runningMin_le (L w) n q (by omega)
    change minL w n ≤ L w q at hmin
    omega
  let P : ℕ → Prop := fun m => n ≤ m ∧ L w m ≤ L w a
  have hP : ∃ m, P m := ⟨q, by dsimp [P]; omega⟩
  let m := Nat.find hP
  have hm : n ≤ m ∧ L w m ≤ L w a := Nat.find_spec hP
  have hbefore (j : ℕ) (hnj : n ≤ j) (hjm : j < m) : L w a < L w j := by
    have hnot := Nat.find_min hP hjm
    change ¬ (n ≤ j ∧ L w j ≤ L w a) at hnot
    omega
  have hlevel : L w m = L w a := by
    by_cases hmn : m = n
    · have := habove n han le_rfl
      rw [hmn] at hm ⊢
      omega
    · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      change m = t + 1 at ht
      have hnt : n ≤ t := by omega
      have hprior := hbefore t hnt (by omega)
      have hstep := kmswL_succ w t
      change L w (t + 1) = L w t + ((w t : ℤ) - 1) at hstep
      have hnonneg : 0 ≤ (w t : ℤ) := Int.natCast_nonneg _
      rw [ht] at hm ⊢
      omega
  refine ⟨m, hm.1, hlevel, ?_⟩
  intro j haj hjm
  by_cases hjn : j ≤ n
  · exact habove j haj hjn
  · by_cases hj : j < m
    · exact (hbefore j (by omega) hj).le
    · have : j = m := by omega
      simpa only [this, hlevel] using (le_refl (L w a))




private theorem upperTail_westStack (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {n y : ℕ} (hy : y ∈ CutConverse.westStack w n) :
    ∃ m ≥ n, (kmswStage w m).west (kmswStage w m).active = y := by
  classical
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hy
  have heUL := List.mem_reverse.mp he
  rw [kmswStage_UL_eq] at heUL
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp heUL
  obtain ⟨harange, harecord⟩ := List.mem_filter.mp ha
  have han : a ≤ n := by
    have := List.mem_range.mp harange
    omega
  have hrecord : ∀ j, a < j → j ≤ n → L w a + 1 ≤ L w j :=
    of_decide_eq_true harecord
  have habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j := by
    intro j haj hjn
    by_cases haj' : a < j
    · have := hrecord j haj' hjn
      omega
    · have : j = a := by omega
      simp only [this, le_refl]
  obtain ⟨m, hnm, hmlevel, hmabove⟩ := upperTail_left_return w h han habove
  have ham : a ≤ m := han.trans hnm
  have hvisit := kmsw_west_act_eq_of_level w ham hmlevel.symm hmabove
  have hstable := (kmswStage_endpoints_stable w hnm
    (act_lt_nextEdge w han)).1
  exact ⟨m, hnm, hvisit.symm.trans (hstable.trans heq)⟩



private theorem upperTail_UL (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {n y : ℕ} (hy : ∃ e ∈ (kmswStage w n).UL,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) :
    ∃ m ≥ n, (kmswStage w m).west (kmswStage w m).active = y := by
  obtain ⟨e, he, hwest | heast⟩ := hy
  · exact upperTail_westStack w h
      (List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, hwest⟩)
  · have hmem : y ∈ (kmswStage w n).UL.reverse.map (kmswStage w n).east :=
      List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, heast⟩
    rw [CutConverse.ul_coherent w n] at hmem
    rcases List.mem_cons.mp hmem with hpending | hwest
    · apply upperTail_pending w h
      exact List.mem_cons.mpr (Or.inl hpending)
    · exact upperTail_westStack w h (List.dropLast_subset _ hwest)




theorem kmswStage_upper_vertex_future_tail (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (n y : ℕ)
    (hy : ∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) :
    ∃ m ≥ n, (kmswStage w m).west (kmswStage w m).active = y := by
  obtain ⟨e, he, heq⟩ := hy
  rcases List.mem_append.mp he with heUL | heUR
  · exact upperTail_UL w h ⟨e, heUL, heq⟩
  · exact upperTail_UR w h ⟨e, heUR, heq⟩

end DirectedDistances.KMSW
