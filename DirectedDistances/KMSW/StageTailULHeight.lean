module

public import DirectedDistances.KMSW.StageTailULIndex

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW





theorem kmswStage_UL_index_lastHeight (w : ℕ → Fin 3) (n i : ℕ)
    (hi : i < (kmswStage w n).UL.length) :
    (kmswStage w n).UL[i] =
      (kmswStage w (kmswUlTime w n (i + 1))).active := by
  have hUL := kmswStage_UL_eq_lastHeight w n
  have hopt := congrArg (fun xs : List ℕ => xs[i]?) hUL
  have hlen : (List.range (L w n - minL w n + 1).toNat).length =
      (kmswStage w n).UL.length := by
    rw [hUL]
    simp only [List.length_map, List.length_range]
  have hiRange : i < (List.range (L w n - minL w n + 1).toNat).length := by
    rw [hlen]
    exact hi
  have hiMapRange : i <
      (List.map (fun j => (kmswStage w (kmswUlTime w n (j + 1))).active)
        (List.range (L w n - minL w n + 1).toNat)).length := by
    simpa only [List.length_map] using hiRange
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiMapRange] at hopt
  simp only [List.getElem_map, List.getElem_range] at hopt
  exact Option.some.inj hopt





theorem kmswStage_UL_vertex_index_lastHeight (w : ℕ → Fin 3) (n i : ℕ)
    (hi : i < (kmswStage w n).UL.length) :
    (((kmswStage w n).UL.map (kmswStage w n).west) ++
      [(kmswStage w n).east (kmswStage w n).active])[i]'(by
        simp only [List.length_append, List.length_map, List.length_singleton]
        omega) =
        (kmswStage w (kmswUlTime w n (i + 1))).west
          (kmswStage w (kmswUlTime w n (i + 1))).active := by
  have hiMap : i < ((kmswStage w n).UL.map (kmswStage w n).west).length := by
    simpa only [List.length_map] using hi
  have htime : kmswUlTime w n (i + 1) ≤ n := by
    unfold kmswUlTime
    exact Nat.findGreatest_le n
  have hstable := kmswStage_endpoints_stable w
    (m := kmswUlTime w n (i + 1)) (n := n)
    (e := (kmswStage w (kmswUlTime w n (i + 1))).active) htime
    (act_lt_nextEdge w (m := kmswUlTime w n (i + 1))
      (n := kmswUlTime w n (i + 1)) le_rfl)
  rw [List.getElem_append_left hiMap, List.getElem_map]
  rw [kmswStage_UL_index_lastHeight w n i hi]
  simpa only [act] using hstable.1










theorem kmswStage_tail_UL_vertex_slot (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = []) :
    ∃ i, i ≤ (kmswStage w N).UL.length ∧
      ((i < (kmswStage w N).UL.length ∧
          (kmswStage w m).west (kmswStage w m).active =
            (kmswStage w (kmswUlTime w N (i + 1))).west
              (kmswStage w (kmswUlTime w N (i + 1))).active) ∨
        (i = (kmswStage w N).UL.length ∧
          (kmswStage w m).west (kmswStage w m).active =
            (kmswStage w N).east (kmswStage w N).active)) := by
  let xs := ((kmswStage w N).UL.map (kmswStage w N).west) ++
    [(kmswStage w N).east (kmswStage w N).active]
  have hmem : (kmswStage w m).west (kmswStage w m).active ∈ xs := by
    simpa only [xs] using
      kmswStage_tail_mem_UL_vertex_list w hNm hOld hUR
  obtain ⟨i, hi, hvertex⟩ := List.mem_iff_getElem.mp hmem
  have hbound : i ≤ (kmswStage w N).UL.length := by
    simp only [xs, List.length_append, List.length_map, List.length_singleton] at hi
    omega
  by_cases hindex : i < (kmswStage w N).UL.length
  · refine ⟨i, hbound, Or.inl ⟨hindex, ?_⟩⟩
    have hslot := kmswStage_UL_vertex_index_lastHeight w N i hindex
    change xs[i] = (kmswStage w m).west (kmswStage w m).active at hvertex
    exact hvertex.symm.trans (by simpa only [xs] using hslot)
  · have hlast : i = (kmswStage w N).UL.length := by omega
    subst i
    refine ⟨(kmswStage w N).UL.length, le_rfl, Or.inr ⟨rfl, ?_⟩⟩
    have hterminal : xs[(kmswStage w N).UL.length] =
        (kmswStage w N).east (kmswStage w N).active := by
      simp [xs]
    change xs[(kmswStage w N).UL.length] =
      (kmswStage w m).west (kmswStage w m).active at hvertex
    exact hvertex.symm.trans hterminal

end DirectedDistances.KMSW
