module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified

/-! Supporting lemmas for paper labels `lem-ldp-fluctuation` (see CORRESPONDENCE.md). -/

public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.RandomWalk




theorem lem_ldp_fluctuation_paper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨C, hC, hbound⟩ := lem_ldp_fluctuation_identified
  exact ⟨C, hC, fun k _hk A hA => hbound k A hA⟩

end DirectedDistances.PaperProofs.Section7
