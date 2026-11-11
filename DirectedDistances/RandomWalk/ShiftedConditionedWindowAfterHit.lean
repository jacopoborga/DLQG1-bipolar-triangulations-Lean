/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ShiftedConditionedWindowRN
public import DirectedDistances.RandomWalk.ConditionedStrongMarkov

/-! Supporting lemmas for paper labels `lem-boltzmann-ldp-lower` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped ENNReal

private theorem measurableConditionedPastSet (k : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast k] A) : MeasurableSet A := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

private theorem measurableConditionedFirstHitNat (r : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ => (conditionedSecondCoordinateFirstHit r p).toNat) := by
  apply (measurable_of_countable ENat.toNat).comp
  apply ENat.measurable_iff.mpr
  intro k
  exact measurableConditionedPastSet k _
    (measurableSet_conditionedVectorPast_firstHit_eq r k)

private theorem conditionedSecondCoordinateFirstHit_level (r : ℕ)
    (p : ℕ → ℤ × ℤ)
    (hτ : conditionedSecondCoordinateFirstHit r p < ⊤) :
    (p (conditionedSecondCoordinateFirstHit r p).toNat).2 = -(r : ℤ) := by
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · simpa [conditionedSecondCoordinateFirstHit, h] using Nat.find_spec h
  · simp [conditionedSecondCoordinateFirstHit, h] at hτ

theorem conditionedVectorPathLaw_postFirstHit_window_law
    (x : ℕ) (y : ℤ) (r ℓ N : ℕ) :
    ((conditionedVectorPathLaw x y).restrict
      {p | conditionedSecondCoordinateFirstHit r p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ℓ : ℤ)}).map
      (fun p => fun j : Fin (N + 1) =>
        (p ((conditionedSecondCoordinateFirstHit r p).toNat + j.val)) -
          p (conditionedSecondCoordinateFirstHit r p).toNat) =
    (conditionedVectorPathLaw x y
      {p | conditionedSecondCoordinateFirstHit r p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ℓ : ℤ)}) •
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
      (fun q => if ∀ j, -(ℓ : ℤ) ≤ (q j).1 then
        ENNReal.ofReal ((((ℓ : ℝ) + (q (Fin.last N)).1 + 1) / ((ℓ : ℝ) + 1)))
        else 0) := by
  classical
  let τ := conditionedSecondCoordinateFirstHit r
  let A : Set (ℕ → ℤ × ℤ) := {p | (p (τ p).toNat).1 = (ℓ : ℤ)}
  let H : Set (ℕ → ℤ × ℤ) :=
    {p | τ p < ⊤ ∧ (p (τ p).toNat).1 = (ℓ : ℤ)}
  let C : (ℕ → ℤ × ℤ) → (Fin (N + 1) → ℤ × ℤ) :=
    fun q j => q j.val - q 0
  let F : (ℕ → ℤ × ℤ) → (Fin (N + 1) → ℤ × ℤ) :=
    fun p j => p ((τ p).toNat + j.val) - p (τ p).toNat
  have hC : Measurable C := by
    exact .of_eval fun j =>
      (measurable_pi_apply j.val).sub (measurable_pi_apply 0)
  have htime := measurableConditionedFirstHitNat r
  have hEval (n : ℕ) : Measurable (fun p : ℕ → ℤ × ℤ =>
      p ((τ p).toNat + n)) := by
    have he : Measurable (fun z : (ℕ → ℤ × ℤ) × ℕ => z.1 (z.2 + n)) :=
      measurable_from_prod_countable_left fun k => measurable_pi_apply (k + n)
    exact he.comp (measurable_id.prodMk htime)
  have hF : Measurable F := by
    exact .of_eval fun j => (hEval j.val).sub (hEval 0)
  have hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | τ p = (k : ℕ∞)}) := by
    intro k
    have hlevel := measurableSet_conditionedVectorPast_firstHit_eq r k
    have hcoord : MeasurableSet[conditionedVectorPast k] {p | (p k).1 = (ℓ : ℤ)} := by
      let S : Set (Fin (k + 1) → ℤ × ℤ) :=
        {q | (q (Fin.last k)).1 = (ℓ : ℤ)}
      refine ⟨S, (Set.to_countable S).measurableSet, ?_⟩
      ext p
      simp [S, conditionedVectorPrefix]
    have hrepr : A ∩ {p | τ p = (k : ℕ∞)} =
        {p | (p k).1 = (ℓ : ℤ)} ∩ {p | τ p = (k : ℕ∞)} := by
      ext p
      change ((p (τ p).toNat).1 = (ℓ : ℤ) ∧ τ p = (k : ℕ∞)) ↔
        ((p k).1 = (ℓ : ℤ) ∧ τ p = (k : ℕ∞))
      constructor
      · rintro ⟨hp, hτ⟩
        have hto : (τ p).toNat = k := by simp [hτ]
        rw [hto] at hp
        exact ⟨hp, hτ⟩
      · rintro ⟨hp, hτ⟩
        have hto : (τ p).toNat = k := by simp [hτ]
        rw [hto]
        exact ⟨hp, hτ⟩
    rw [hrepr]
    exact hcoord.inter hlevel
  have hAk : ∀ k : ℕ, MeasurableSet (A ∩ {p | τ p = (k : ℕ∞)}) := by
    intro k
    obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp (hA k)
    rw [← hpre]
    exact hS.preimage (measurable_conditionedVectorPrefix k)
  have hHrepr : H = ⋃ k : ℕ, A ∩ {p | τ p = (k : ℕ∞)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hp.1.ne
      have hτ : τ p = (k : ℕ∞) := hk.symm
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      exact ⟨by simpa [A, hτ] using hp.2, hτ⟩
    · intro hp
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq] at hp
      obtain ⟨k, hheight, hτ⟩ := hp
      have hfinite : τ p < ⊤ := by rw [hτ]; exact ENat.natCast_lt_top k
      exact ⟨hfinite, by simpa [A, hτ] using hheight⟩
  have hH : MeasurableSet H := by
    rw [hHrepr]
    exact MeasurableSet.iUnion hAk
  have hRH : A ∩ {p | τ p < ⊤} = H := by
    ext p
    simp [A, H, and_comm]
  ext E' hE'
  have hwindowSet : F ⁻¹' E' ∩ H = {p | p ∈ H ∧ F p ∈ E'} := by
    ext p
    simp [and_comm]
  have hSMwindow := conditionedVectorPathLaw_strongMarkov x y τ
    (fun k => measurableSet_conditionedVectorPast_firstHit_eq r k) A hA
    {q | C q ∈ E'} (hE'.preimage hC)
  have hleftWindow : A ∩ {p | τ p < ⊤} ∩
      {p | conditionedVectorShift (τ p).toNat p ∈ {q | C q ∈ E'}} =
      {p | p ∈ H ∧ F p ∈ E'} := by
    ext p
    simp [A, H, C, F, τ, conditionedVectorShift, and_comm]
  have hSMwindow' := hSMwindow
  rw [hleftWindow, hRH] at hSMwindow'
  have hmarkovWindow :
      conditionedVectorPathLaw x y {p | p ∈ H ∧ F p ∈ E'} =
        conditionedVectorPathLaw x y H *
          conditionedVectorPathLaw ℓ (-(r : ℤ)) {q | C q ∈ E'} := by
    calc
      conditionedVectorPathLaw x y {p | p ∈ H ∧ F p ∈ E'} =
          ∫⁻ p in H,
            conditionedVectorPathLaw ((p (τ p).toNat).1.toNat)
              (p (τ p).toNat).2 {q | C q ∈ E'} ∂conditionedVectorPathLaw x y :=
        hSMwindow'
      _ = conditionedVectorPathLaw x y H *
            conditionedVectorPathLaw ℓ (-(r : ℤ)) {q | C q ∈ E'} := by
        rw [setLIntegral_congr_fun hH (fun p hp => by
          have hheight : (p (τ p).toNat).1 = (ℓ : ℤ) := hp.2
          have hfirst : (p (τ p).toNat).1.toNat = ℓ := by rw [hheight]; rfl
          have hlevel := conditionedSecondCoordinateFirstHit_level r p hp.1
          rw [hfirst, hlevel]), setLIntegral_const, mul_comm]
  have hcenter := conditionedVectorPathLaw_centeredPrefix_law ℓ (-(r : ℤ)) N
  have hcenterWindow :
      conditionedVectorPathLaw ℓ (-(r : ℤ)) {q | C q ∈ E'} =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, -(ℓ : ℤ) ≤ (q j).1 then
            ENNReal.ofReal ((((ℓ : ℝ) + (q (Fin.last N)).1 + 1) /
              ((ℓ : ℝ) + 1))) else 0) E' := by
    have hh := congrArg (fun μ : Measure (Fin (N + 1) → ℤ × ℤ) => μ E') hcenter
    change (conditionedVectorPathLaw ℓ (-(r : ℤ))).map C E' = _ at hh
    rw [Measure.map_apply hC hE'] at hh
    change conditionedVectorPathLaw ℓ (-(r : ℤ)) (C ⁻¹' E') =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, -(ℓ : ℤ) ≤ (q j).1 then
          ENNReal.ofReal ((((ℓ : ℝ) + (q (Fin.last N)).1 + 1) /
            ((ℓ : ℝ) + 1))) else 0) E'
    exact hh
  rw [Measure.map_apply hF hE', Measure.restrict_apply (hE'.preimage hF),
    Measure.smul_apply, smul_eq_mul]
  rw [hwindowSet, hmarkovWindow, hcenterWindow]
