/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorRegeneration
public import DirectedDistances.Probability.FinitePartition

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem map_restrict_eq_smul_of_cond_map_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (J : Set Ω) (hJ : MeasurableSet J)
    (f : Ω → α) (hf : Measurable f) (ρ : Measure α)
    (h : (ProbabilityTheory.cond μ J).map f = ρ) :
    (μ.restrict J).map f = μ J • ρ := by
  ext E hE
  rw [Measure.map_apply hf hE, Measure.restrict_apply (hE.preimage hf),
    Measure.smul_apply, smul_eq_mul, Set.inter_comm]
  have hh := congrArg (fun ν : Measure α => ν E) h
  rw [Measure.map_apply hf hE] at hh
  rw [← cond_mul_eq_inter hJ (f ⁻¹' E) μ, hh, mul_comm]

/-- Every actual source-word cylinder, including killed words, has its
unnormalized joint future-above-endpoint law proportional to the full source
law after subtracting the actual path endpoint in both coordinates. -/
theorem conditionedSource_cylinder_restrict_regeneration
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n : ℕ) (w : Fin n → Fin 3) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    (ν.restrict (C ∩ B)).map (fun p => fun k => p (n + k) - p n) =
      ν (C ∩ B) • ν := by
  classical
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
  have hC : MeasurableSet C := (measurableSet_singleton _).preimage (by fun_prop)
  have hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN
  by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1
  · let X : ℕ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1.toNat
    let Y : ℤ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2
    let F : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (X : ℤ) ≤ (p (n + k)).1}
    have hX : (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 = (X : ℤ) :=
      (Int.toNat_of_nonneg (hw (Fin.last n))).symm
    have hp (p : ℕ → ℤ × ℤ) (hc : p ∈ C) : p n = ((X : ℤ), Y) := by
      have hh := congrFun hc (Fin.last n)
      change p n = lazyTwoDimensionalPrefix 0 0 w (Fin.last n) at hh
      apply hh.trans
      exact Prod.ext hX rfl
    have hF : MeasurableSet F := by
      change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ k, (X : ℤ) ≤ (p (n + k)).1}
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun k =>
        measurableSet_le measurable_const (measurable_pi_apply (n + k)).fst
    have hset : C ∩ B = C ∩ F := by
      ext p
      constructor
      · rintro ⟨hc, hb⟩
        change ∀ k, (p n).1 ≤ (p (n + k)).1 at hb
        refine ⟨hc, ?_⟩
        change ∀ k, (X : ℤ) ≤ (p (n + k)).1
        simpa only [hp p hc] using hb
      · rintro ⟨hc, hf⟩
        change ∀ k, (X : ℤ) ≤ (p (n + k)).1 at hf
        refine ⟨hc, ?_⟩
        change ∀ k, (p n).1 ≤ (p (n + k)).1
        simpa only [hp p hc] using hf
    have hregen := conditionedSource_cylinder_regeneration ν hRN n X w hw hX
    change (ProbabilityTheory.cond ν (C ∩ F)).map
      (fun p => fun k => p (n + k) - ((X : ℤ), Y)) = ν at hregen
    have hraw := map_restrict_eq_smul_of_cond_map_eq ν (C ∩ F) (hC.inter hF)
      (fun p => fun k => p (n + k) - ((X : ℤ), Y)) (by fun_prop) ν hregen
    change (ν.restrict (C ∩ B)).map (fun p => fun k => p (n + k) - p n) = _
    rw [hset]
    have hmap : (ν.restrict (C ∩ F)).map (fun p => fun k => p (n + k) - p n) =
        (ν.restrict (C ∩ F)).map (fun p => fun k => p (n + k) - ((X : ℤ), Y)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hC.inter hF)] with p hc
      funext k
      rw [hp p hc.1]
    rw [hmap]
    exact hraw
  · have hzeroC : ν C = 0 := by
      change ν {p | (fun j : Fin (n + 1) => p j.val) =
        lazyTwoDimensionalPrefix 0 0 w} = 0
      have hh := conditionedSource_prefix_atom 0 0 ν hRN0 n w
      simp only [Nat.cast_zero] at hh
      rw [hh, ite_eq_right hw, zero_mul]
    have hzeroJ : ν (C ∩ B) = 0 := measure_mono_null Set.inter_subset_left hzeroC
    change (ν.restrict (C ∩ B)).map (fun p => fun k => p (n + k) - p n) = _
    rw [Measure.restrict_eq_zero.mpr hzeroJ, Measure.map_zero, hzeroJ, zero_smul]

/-- The actual future-above-endpoint law regenerates against every event
measurable in the whole finite past. The complete finite-word partition and
all its piece laws are produced from the original source RN data. -/
theorem conditionedSource_past_restrict_regeneration
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) inferInstance] A) :
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    (ν.restrict (A ∩ B)).map (fun p => fun k => p (n + k) - p n) =
      ν (A ∩ B) • ν := by
  classical
  let P : (ℕ → ℤ × ℤ) → (Fin (n + 1) → ℤ × ℤ) := fun p j => p j.val
  let C : (Fin n → Fin 3) → Set (ℕ → ℤ × ℤ) :=
    fun w => {p | P p = lazyTwoDimensionalPrefix 0 0 w}
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
  let f : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) := fun p k => p (n + k) - p n
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  change P ⁻¹' S = A at hpre
  let I : Finset (Fin n → Fin 3) := Finset.univ.filter
    (fun w => lazyTwoDimensionalPrefix 0 0 w ∈ S)
  let U : Set (ℕ → ℤ × ℤ) := ⋃ w ∈ I, C w
  have hC : ∀ w : Fin n → Fin 3, MeasurableSet (C w) :=
    fun w => (measurableSet_singleton _).preimage (by fun_prop)
  have hd : (I : Set (Fin n → Fin 3)).Pairwise (fun w v => Disjoint (C w) (C v)) := by
    intro w hw v hv hne
    apply Set.disjoint_left.mpr
    intro p hpw hpv
    apply hne
    apply lazyTwoDimensionalPrefix_injective 0 0
    exact hpw.symm.trans hpv
  have hB : MeasurableSet B := by
    change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ k, (p n).1 ≤ (p (n + k)).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le (measurable_pi_apply n).fst (measurable_pi_apply (n + k)).fst
  have hf : Measurable f := by fun_prop
  have hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN
  have hcover : A ∩ B =ᵐ[ν] U ∩ B := by
    filter_upwards [conditionedSource_ae_prefix_mem_range 0 0 ν hRN0 n] with p hp
    obtain ⟨w, hw⟩ := hp
    change lazyTwoDimensionalPrefix 0 0 w = P p at hw
    have hmem : p ∈ U ↔ p ∈ A := by
      constructor
      · intro hu
        simp only [U, Set.mem_iUnion] at hu
        obtain ⟨v, hvi, hpv⟩ := hu
        have hvs : lazyTwoDimensionalPrefix 0 0 v ∈ S :=
          (Finset.mem_filter.mp hvi).2
        rw [← hpre]
        change P p ∈ S
        exact hpv.symm ▸ hvs
      · intro hpA
        have hps : P p ∈ S := by
          change p ∈ P ⁻¹' S
          rw [hpre]
          exact hpA
        have hwi : w ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.symm ▸ hps⟩
        exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwi, hw.symm⟩⟩
    exact propext (and_congr hmem.symm Iff.rfl)
  have hpieces : ∀ w ∈ I,
      (ν.restrict (C w ∩ B)).map f = ν (C w ∩ B) • ν := by
    intro w hw
    exact conditionedSource_cylinder_restrict_regeneration ν hRN n w
  have hsum := DirectedDistances.Probability.map_restrict_biUnion_inter_eq_smul
    ν ν I C (fun w _ => hC w) hd B hB f hf hpieces
  change (ν.restrict (A ∩ B)).map f = ν (A ∩ B) • ν
  rw [Measure.restrict_congr_set hcover, measure_congr hcover]
  exact hsum

end DirectedDistances.RandomWalk
