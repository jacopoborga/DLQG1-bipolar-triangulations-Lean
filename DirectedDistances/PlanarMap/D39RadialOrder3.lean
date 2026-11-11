/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder2

/-! # Unrestricted radial order preservation

Helpers toward Proposition 5.16. The unrestricted triple and radial-order
statements are recorded below with their full binders; neither is proved here. -/

public section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. If each of two triples of positive turns
has total turn `2 * Real.pi`, then some matching cyclic position is strictly
convex in both triples. -/
theorem d39_exists_joint_convex_turn_of_turn_sums
    {a b c a' b' c' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (hsum : a + b + c = 2 * Real.pi)
    (hsum' : a' + b' + c' = 2 * Real.pi) :
    (a < Real.pi ∧ a' < Real.pi) ∨
      (b < Real.pi ∧ b' < Real.pi) ∨
      (c < Real.pi ∧ c' < Real.pi) := by
  have hab : ¬ (Real.pi ≤ a ∧ Real.pi ≤ b) := by
    rintro ⟨haπ, hbπ⟩
    linarith
  have hac : ¬ (Real.pi ≤ a ∧ Real.pi ≤ c) := by
    rintro ⟨haπ, hcπ⟩
    linarith
  have hbc : ¬ (Real.pi ≤ b ∧ Real.pi ≤ c) := by
    rintro ⟨hbπ, hcπ⟩
    linarith
  have ha'b' : ¬ (Real.pi ≤ a' ∧ Real.pi ≤ b') := by
    rintro ⟨haπ, hbπ⟩
    linarith
  have ha'c' : ¬ (Real.pi ≤ a' ∧ Real.pi ≤ c') := by
    rintro ⟨haπ, hcπ⟩
    linarith
  have hb'c' : ¬ (Real.pi ≤ b' ∧ Real.pi ≤ c') := by
    rintro ⟨hbπ, hcπ⟩
    linarith
  by_contra h
  have hA : Real.pi ≤ a ∨ Real.pi ≤ a' := by
    by_contra hn
    have haLt : a < Real.pi := lt_of_not_ge (fun hle => hn (Or.inl hle))
    have ha'Lt : a' < Real.pi := lt_of_not_ge (fun hle => hn (Or.inr hle))
    exact h (Or.inl ⟨haLt, ha'Lt⟩)
  have hB : Real.pi ≤ b ∨ Real.pi ≤ b' := by
    by_contra hn
    have hbLt : b < Real.pi := lt_of_not_ge (fun hle => hn (Or.inl hle))
    have hb'Lt : b' < Real.pi := lt_of_not_ge (fun hle => hn (Or.inr hle))
    exact h (Or.inr (Or.inl ⟨hbLt, hb'Lt⟩))
  have hC : Real.pi ≤ c ∨ Real.pi ≤ c' := by
    by_contra hn
    have hcLt : c < Real.pi := lt_of_not_ge (fun hle => hn (Or.inl hle))
    have hc'Lt : c' < Real.pi := lt_of_not_ge (fun hle => hn (Or.inr hle))
    exact h (Or.inr (Or.inr ⟨hcLt, hc'Lt⟩))
  rcases hA with haπ | ha'π
  · rcases hB with hbπ | hb'π
    · exact hab ⟨haπ, hbπ⟩
    · rcases hC with hcπ | hc'π
      · exact hac ⟨haπ, hcπ⟩
      · exact hb'c' ⟨hb'π, hc'π⟩
  · rcases hB with hbπ | hb'π
    · rcases hC with hcπ | hc'π
      · exact hbc ⟨hbπ, hcπ⟩
      · exact ha'c' ⟨ha'π, hc'π⟩
    · rcases hC with hcπ | hc'π
      · exact ha'b' ⟨ha'π, hb'π⟩
      · exact ha'c' ⟨ha'π, hc'π⟩






























































end DirectedDistances.PlanarMap

end
