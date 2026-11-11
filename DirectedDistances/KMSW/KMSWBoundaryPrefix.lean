module

public import DirectedDistances.KMSW.StageBoundaryMap

/-! # Initial lower-right boundary prefix

the procedure reading of the increments (`def-kmsw`,
forced steps. These declarations are not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- If the first `n` codes are `2`, the stage after exactly those `n` steps
has all allocated edges in its lower-right run. That run is the creation-order
list `0, …, n`, with geometric endpoints `e` and `e+1` for edge ID `e`; no
other edge has yet been allocated. Helper toward `lem-kmsw-left`
count: `r−1` forced steps; not the paper result. -/
theorem kmswStage_allDown_prefix_exactLR (w : ℕ → Fin 3) :
    ∀ n, (∀ i < n, w i = 2) →
      (kmswStage w n).nextEdge = n + 1 ∧
      (kmswStage w n).nextVertex = n + 2 ∧
      (kmswStage w n).active = n ∧
      (kmswStage w n).UL = List.range (n + 1) ∧
      (kmswStage w n).LR = List.range (n + 1) ∧
      (kmswStage w n).UR = [] ∧
      (kmswStage w n).LL = [] ∧
      (∀ e, e < (kmswStage w n).nextEdge →
        e ∈ (kmswStage w n).LR ∧
        (kmswStage w n).west e = e ∧
        (kmswStage w n).east e = e + 1 ∧
        (kmswStage w n).present e = true) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [kmswStage, kmswInit]
  | succ n ih =>
      intro hp
      have hprev := ih (fun i hi => hp i (by omega))
      rcases hprev with ⟨hnext, hvertex, hactive, hUL, hLR, hUR, hLL, hedge⟩
      have hcode : w n = 2 := hp n (by omega)
      have hstage : kmswStage w (n + 1) =
          kmswStepOfStep (kmswStage w n) .down := by
        simp [kmswStage, kmswStep, hcode, kmswCodeStep]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hnext]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hvertex]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hnext, hactive]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hnext, hUL, List.range_succ]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hnext, hLR, List.range_succ]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge]
      · rw [hstage]
        simp [kmswStepOfStep, hUR, State.addEdge, hLL]
      · intro e he
        rw [hstage] at he ⊢
        simp only [kmswStepOfStep, hUR, State.addEdge] at he ⊢
        have hbound : e < (kmswStage w n).nextEdge + 1 := by omega
        by_cases heq : e = (kmswStage w n).nextEdge
        · subst e
          have hn_lt : n < (kmswStage w n).nextEdge := by
            rw [hnext]
            omega
          have hactive_east := (hedge n hn_lt).2.2.1
          have hnew_east : (kmswStage w n).east (kmswStage w n).active =
              (kmswStage w n).nextEdge := by
            rw [hactive, hnext]
            exact hactive_east
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [hLR]
          · simpa [State.addEdge] using hnew_east
          · simp [hvertex, hnext]
          · simp
        · have hold : e < (kmswStage w n).nextEdge := by omega
          have h := hedge e hold
          rcases h with ⟨hmem, hwest, heast, hpresent⟩
          have heq' : e ≠ n + 1 := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact List.mem_append.mpr (Or.inl hmem)
          · simpa [hnext, heq'] using hwest
          · simpa [hnext, heq'] using heast
          · simpa [hnext, heq'] using hpresent

end DirectedDistances.KMSW
