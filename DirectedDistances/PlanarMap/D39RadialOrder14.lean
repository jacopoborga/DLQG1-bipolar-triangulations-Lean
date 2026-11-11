/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder13

/-! # Cyclic order helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the cyclic order of three real
parameters in one turn. -/
def d39CyclicOrder (a b c : ℝ) : Prop :=
  (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)

/-- Helper toward Proposition 5.16: on `[0,1)`, subtracting two distinct
parameters and taking fractional part gives the forward displacement in one
turn. -/
theorem d39_fract_sub_unit_interval (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hab : a ≠ b) :
    Int.fract (b - a) = if a < b then b - a else b - a + 1 := by
  rcases lt_or_gt_of_ne hab with hablt | hblt
  · rw [if_pos hablt, Int.fract_eq_self]
    constructor <;> linarith
  · have habnot : ¬ a < b := not_lt_of_ge hblt.le
    rw [if_neg habnot]
    have hfract : Int.fract (b - a) = Int.fract (b - a + 1) := by
      exact Int.fract_eq_fract.mpr ⟨-1, by ring⟩
    rw [hfract, Int.fract_eq_self]
    constructor <;> linarith

/-- Helper toward Proposition 5.16: for distinct parameters in `[0,1)`, the
order of the two fractional displacements from `a` is exactly their cyclic
order. -/
theorem d39_fract_sub_lt_iff_cyclicOrder
    (a b c : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Int.fract (b - a) < Int.fract (c - a) ↔ d39CyclicOrder a b c := by
  have hfab := d39_fract_sub_unit_interval a b ha0 ha1 hb0 hb1 hab
  have hfac := d39_fract_sub_unit_interval a c ha0 ha1 hc0 hc1 hac
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · have hleft : Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_pos hab', if_pos hac']
          linarith
        have hright : d39CyclicOrder a b c := Or.inl ⟨hab', hbc'⟩
        exact ⟨fun _ => hright, fun _ => hleft⟩
      · have hleft : ¬ Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_pos hab', if_pos hac']
          intro h
          linarith
        have hright : ¬ d39CyclicOrder a b c := by
          intro h
          change (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) at h
          rcases h with ⟨_, hbcx⟩ | ⟨hbcx, _⟩ | ⟨hca, _⟩ <;> linarith
        exact ⟨fun h => (hleft h).elim, fun h => (hright h).elim⟩
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact False.elim (not_lt_of_ge hca'.le (lt_trans hab' hbc'))
      · have hleft : Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_pos hab', if_neg (not_lt_of_ge hca'.le)]
          linarith
        have hright : d39CyclicOrder a b c := Or.inr (Or.inr ⟨hca', hab'⟩)
        exact ⟨fun _ => hright, fun _ => hleft⟩
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · have hleft : ¬ Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_neg (not_lt_of_ge hba'.le), if_pos hac']
          intro h
          linarith
        have hright : ¬ d39CyclicOrder a b c := by
          intro h
          change (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) at h
          rcases h with ⟨habx, _⟩ | ⟨_, hca⟩ | ⟨hca, _⟩ <;> linarith
        exact ⟨fun h => (hleft h).elim, fun h => (hright h).elim⟩
      · exact False.elim (not_lt_of_ge hba'.le (lt_trans hac' hcb'))
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · have hleft : Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_neg (not_lt_of_ge hba'.le),
            if_neg (not_lt_of_ge hca'.le)]
          linarith
        have hright : d39CyclicOrder a b c := Or.inr (Or.inl ⟨hbc', hca'⟩)
        exact ⟨fun _ => hright, fun _ => hleft⟩
      · have hleft : ¬ Int.fract (b - a) < Int.fract (c - a) := by
          rw [hfab, hfac]
          simp only [if_neg (not_lt_of_ge hba'.le),
            if_neg (not_lt_of_ge hca'.le)]
          intro h
          linarith
        have hright : ¬ d39CyclicOrder a b c := by
          intro h
          change (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) at h
          rcases h with ⟨habx, _⟩ | ⟨hbcx, _⟩ | ⟨_, habx⟩ <;> linarith
        exact ⟨fun h => (hleft h).elim, fun h => (hright h).elim⟩

/-- Helper toward Proposition 5.16: cyclic order is preserved by any
relabelling that preserves all pairwise strict comparisons. -/
theorem d39CyclicOrder_iff_of_pairwise_lt_iff
    (a b c a' b' c' : ℝ)
    (hab : a < b ↔ a' < b') (_hac : a < c ↔ a' < c')
    (_hba : b < a ↔ b' < a') (hbc : b < c ↔ b' < c')
    (hca : c < a ↔ c' < a') (_hcb : c < b ↔ c' < b') :
    d39CyclicOrder a b c ↔ d39CyclicOrder a' b' c' := by
  simp [d39CyclicOrder, hab, hbc, hca]

































































































end DirectedDistances.PlanarMap

end
