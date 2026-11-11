/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.SelectedCutPastMapLaw
public import DirectedDistances.PaperProofs.Section4.RenewalTimeCharacterization

/-! Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The selected renewal time is zero or the first hit at the last successful
barrier, and these branches form a measurable partition almost surely. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Helper toward Lemma 4.13; not a paper result. -/
private theorem renewalTime_is_literalSelector :
    ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m
      (Paper.Section4.renewalTime m p) := by
  intro p m
  exact (renewalTime_characterization m p).1

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
For every `k ≥ 1`, almost surely the selected renewal time is zero with no
successful barrier, or is the first hit of the greatest successful barrier -/
theorem selectedCutTime_zero_or_firstHit (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (selectedCutTime Paper.Section4.renewalTime k p = 0 ∧
        ∀ s, 1 ≤ s → s ≤ k → ¬ firstHitBarrier s p) ∨
      ∃ r, 1 ≤ r ∧ r ≤ k ∧
        selectedCutTime Paper.Section4.renewalTime k p =
          conditionedSecondCoordinateFirstHit r p ∧
        firstHitBarrier r p ∧
        ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    firstHitPastMap_finite_hit_ae k hk] with p hlegal hfinite
  have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
  have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
    intro j
    obtain ⟨c, hc⟩ := hlegal.2 j
    have hs := congrArg Prod.snd hc
    fin_cases c <;>
      norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  obtain ⟨_, _, _, hbranch, hzero⟩ := selectedCutTime_lastSuccessTime
    Paper.Section4.renewalTime p k hk hstep h0
    (fun m => (renewalTime_is_literalSelector p m)) hfinite
  by_cases hnone : ∀ s, 1 ≤ s → s ≤ k → ¬ firstHitBarrier s p
  · exact Or.inl ⟨hzero.mpr hnone, hnone⟩
  · right
    have hex : ∃ s, 1 ≤ s ∧ s ≤ k ∧ firstHitBarrier s p := by
      by_contra h
      apply hnone
      intro s hs hsk hb
      exact h ⟨s, hs, hsk, hb⟩
    obtain ⟨s, hs, hsk, hb⟩ := hex
    let r := Nat.findGreatest (fun j => firstHitBarrier j p) k
    have hsr : s ≤ r := Nat.le_findGreatest hsk hb
    have hr : 1 ≤ r := hs.trans hsr
    have hrk : r ≤ k := Nat.findGreatest_le k
    have hbar : firstHitBarrier r p :=
      Nat.findGreatest_spec (P := fun j => firstHitBarrier j p) hsk hb
    have hlast : ∀ j, r < j → j ≤ k → ¬ firstHitBarrier j p := by
      intro j hj hjk
      exact Nat.findGreatest_is_greatest hj hjk
    exact ⟨r, hr, hrk, (hbranch r hr hrk).mpr ⟨hbar, hlast⟩, hbar, hlast⟩

/-- Helper toward Lemma 4.13; not a paper result. -/
private theorem measurableSet_of_conditionedVectorPast (n : ℕ)
    (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast n] A) : MeasurableSet A := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix n)

/-- Helper toward Lemma 4.13; not a paper result. -/
private theorem measurable_firstHitTime (r : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit r) := by
  apply ENat.measurable_iff.mpr
  intro n
  exact measurableSet_of_conditionedVectorPast n _
    (measurableSet_conditionedVectorPast_firstHit_eq r n)

/-- Helper toward Lemma 4.13; not a paper result. -/
private theorem secondCoordinate_at_finite_firstHit
    (r t : ℕ) (p : ℕ → ℤ × ℤ)
    (hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞)) :
    (p t).2 = -(r : ℤ) := by
  classical
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hnone
    have htop : conditionedSecondCoordinateFirstHit r p = ⊤ := by
      simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hnone]
    rw [htop] at hτ
    exact (ENat.top_ne_natCast t hτ).elim
  have hfind : ((Nat.find hh : ℕ) : ℕ∞) = (t : ℕ∞) := by
    simpa only [conditionedSecondCoordinateFirstHit, dite_eq_left hh] using hτ
  have hfindNat : Nat.find hh = t := by
    exact_mod_cast hfind
  rw [← hfindNat]
  exact Nat.find_spec hh

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The events that the selected renewal time is zero or equals one of the first
hit times through `k` are measurable, pairwise disjoint almost surely, and -/
theorem selectedCutTime_partition (k : ℕ) (hk : 1 ≤ k) :
    MeasurableSet
        {p | selectedCutTime Paper.Section4.renewalTime k p = (0 : ℕ∞)} ∧
      (∀ r, 1 ≤ r → r ≤ k →
        MeasurableSet {p | selectedCutTime Paper.Section4.renewalTime k p =
          conditionedSecondCoordinateFirstHit r p}) ∧
      (∀ r, 1 ≤ r → r ≤ k → ∀ s, 1 ≤ s → s ≤ k → r ≠ s →
        ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
          ¬ (selectedCutTime Paper.Section4.renewalTime k p =
              conditionedSecondCoordinateFirstHit r p ∧
            selectedCutTime Paper.Section4.renewalTime k p =
              conditionedSecondCoordinateFirstHit s p)) ∧
      (∀ r, 1 ≤ r → r ≤ k →
        ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
          ¬ (selectedCutTime Paper.Section4.renewalTime k p = (0 : ℕ∞) ∧
            selectedCutTime Paper.Section4.renewalTime k p =
              conditionedSecondCoordinateFirstHit r p)) ∧
      (∀ᵐ p ∂conditionedVectorPathLaw 0 0,
        selectedCutTime Paper.Section4.renewalTime k p = (0 : ℕ∞) ∨
          ∃ r, 1 ≤ r ∧ r ≤ k ∧
            selectedCutTime Paper.Section4.renewalTime k p =
              conditionedSecondCoordinateFirstHit r p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_selectedCutTime Paper.Section4.renewalTime k
      renewalTime_is_literalSelector (measurableSet_singleton 0)
  · intro r hr hrk
    exact measurableSet_eq_fun
      (measurable_selectedCutTime Paper.Section4.renewalTime k
        renewalTime_is_literalSelector)
      (measurable_firstHitTime r)
  · intro r hr hrk s hs hsk hrs
    filter_upwards [firstHitPastMap_finite_hit_ae r hr,
      firstHitPastMap_finite_hit_ae s hs] with p hfr hfs hboth
    have heq : conditionedSecondCoordinateFirstHit r p =
        conditionedSecondCoordinateFirstHit s p := hboth.1.symm.trans hboth.2
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfr.ne
    have hτr : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := ht.symm
    have hτs : conditionedSecondCoordinateFirstHit s p = (t : ℕ∞) :=
      heq.symm.trans hτr
    have hrlevel := secondCoordinate_at_finite_firstHit r t p hτr
    have hslevel := secondCoordinate_at_finite_firstHit s t p hτs
    apply hrs
    have : (r : ℤ) = (s : ℤ) := by omega
    exact_mod_cast this
  · intro r hr hrk
    filter_upwards [conditionedVectorPathLaw_ae_legal,
      firstHitPastMap_finite_hit_ae r hr] with p hlegal hfinite hboth
    have hτ : conditionedSecondCoordinateFirstHit r p = (0 : ℕ∞) :=
      hboth.2.symm.trans hboth.1
    have hlevel := secondCoordinate_at_finite_firstHit r 0 p hτ
    have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
    omega
  · filter_upwards [selectedCutTime_zero_or_firstHit k hk] with p hparts
    rcases hparts with ⟨hzero, _⟩ | ⟨r, hr, hrk, htime, _, _⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨r, hr, hrk, htime⟩

end DirectedDistances.PaperProofs.Section4
