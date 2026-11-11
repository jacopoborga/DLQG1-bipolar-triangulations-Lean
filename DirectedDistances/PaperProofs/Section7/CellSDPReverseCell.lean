module

public import DirectedDistances.PaperProofs.Section7.CellSDPReversalLaw

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7




theorem codeReversal_stageLetter (n : ℕ) (ω : ℕ → Fin 3) (i : ℕ)
    (hi : i < n) :
    codeReversal n ω (i + 1) =
      Equiv.swap (0 : Fin 3) 1 (ω (n - i)) := by
  have hIn : 1 ≤ i + 1 ∧ i + 1 ≤ n := by omega
  have hidx : n + 1 - (i + 1) = n - i := by omega
  simp [codeReversal, hIn, hidx]

end DirectedDistances.PaperProofs.Section7
