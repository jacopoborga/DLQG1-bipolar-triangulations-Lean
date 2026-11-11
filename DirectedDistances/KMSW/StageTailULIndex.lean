module

public import DirectedDistances.KMSW.StageTailUpper
public import DirectedDistances.KMSW.StageStackInvariantUL
public import DirectedDistances.KMSW.StageStackInvariantUR
public import DirectedDistances.KMSW.StageActiveEdges

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW




private theorem mem_iff_exists_getElem? {α : Type} (xs : List α)
    (x : α) : x ∈ xs ↔ ∃ i : ℕ, xs[i]? = some x := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    constructor
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst a
        exact ⟨0, by simp⟩
      · obtain ⟨i, hi⟩ := ih.mp h
        exact ⟨i + 1, by simpa only [List.getElem?_cons_succ] using hi⟩
    · rintro ⟨i, hi⟩
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
                simp [hi]
      | succ i =>
        have hi' : as[i]? = some x := by
          simpa only [List.getElem?_cons_succ] using hi
        exact List.mem_cons_of_mem _ (ih.mpr ⟨i, hi'⟩)







theorem kmswStage_tail_UL_endpoint_index (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = []) :
    ∃ (i e : ℕ), (kmswStage w N).UL[i]? = some e ∧
      ((kmswStage w N).west e = (kmswStage w m).west (kmswStage w m).active ∨
        (kmswStage w N).east e = (kmswStage w m).west (kmswStage w m).active) := by
  obtain ⟨e, he, hend⟩ := kmswStage_tail_mem_up w hNm hOld
  have heUL : e ∈ (kmswStage w N).UL := by
    simpa [hUR] using he
  obtain ⟨i, hi⟩ := (mem_iff_exists_getElem? (kmswStage w N).UL e).mp heUL
  exact ⟨i, e, hi, hend⟩





theorem kmswStage_tail_mem_UL_vertex_list (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = []) :
    (kmswStage w m).west (kmswStage w m).active ∈
      ((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active] := by
  obtain ⟨e, he, htail⟩ := kmswStage_tail_mem_up w hNm hOld
  have heUL : e ∈ (kmswStage w N).UL := by
    simpa [hUR] using he
  rcases htail with hwest | heast
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨e, heUL, hwest⟩)
  · have heastMap : (kmswStage w m).west (kmswStage w m).active ∈
        (kmswStage w N).UL.reverse.map (kmswStage w N).east :=
      List.mem_map.mpr ⟨e, List.mem_reverse.mpr heUL, heast⟩
    have hcoh := CutConverse.ul_coherent w N
    change (kmswStage w N).UL.reverse.map (kmswStage w N).east =
      (kmswStage w N).east (kmswStage w N).active ::
        ((kmswStage w N).UL.reverse.map (kmswStage w N).west).dropLast at hcoh
    rw [hcoh] at heastMap
    rcases List.mem_cons.mp heastMap with htip | hprev
    · exact List.mem_append_right _ (List.mem_singleton.mpr htip)
    · have hwestStack : (kmswStage w m).west (kmswStage w m).active ∈
          (kmswStage w N).UL.reverse.map (kmswStage w N).west :=
        List.dropLast_subset _ hprev
      have hrev : (kmswStage w m).west (kmswStage w m).active ∈
          ((kmswStage w N).UL.map (kmswStage w N).west).reverse := by
        simpa only [List.map_reverse] using hwestStack
      exact List.mem_append_left _ (List.mem_reverse.mp hrev)

end DirectedDistances.KMSW
