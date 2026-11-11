/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorMarkov
public import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport
public import DirectedDistances.RandomWalk.ConditionedVectorAtomSupport
import Mathlib.Probability.ConditionalProbability

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A prescribed past word and its actual future word are exactly the
concatenated full-vector cylinder, on every path. -/
theorem lazyTwoDimensionalPrefix_joint_cylinder
    (n m x X : ℕ) (y : ℤ) (w : Fin n → Fin 3) (v : Fin m → Fin 3)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    {p : ℕ → ℤ × ℤ |
      (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w ∧
      (fun j : Fin (m + 1) => p (n + j.val)) =
        lazyTwoDimensionalPrefix (X : ℤ)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 v} =
    {p | (fun j : Fin (n + m + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y (Fin.append w v)} := by
  ext p
  constructor
  · rintro ⟨hp, hq⟩
    funext j
    by_cases hj : j.val ≤ n
    · have h := congrFun hp (⟨j.val, by omega⟩ : Fin (n + 1))
      have he := lazyTwoDimensionalPrefix_append_left (x : ℤ) y w v
        (⟨j.val, by omega⟩ : Fin (n + 1))
      exact h.trans he.symm
    · have h := congrFun hq (⟨j.val - n, by omega⟩ : Fin (m + 1))
      have he := lazyTwoDimensionalPrefix_append_right (x : ℤ) y w v
        (⟨j.val - n, by omega⟩ : Fin (m + 1))
      have hi : n + (j.val - n) = j.val := by omega
      simp only [hi, hX] at h he
      exact h.trans he.symm
  · intro hp
    constructor
    · funext j
      have h := congrFun hp (⟨j.val, by omega⟩ : Fin (n + m + 1))
      exact h.trans (lazyTwoDimensionalPrefix_append_left (x : ℤ) y w v j)
    · funext j
      have h := congrFun hp (⟨n + j.val, by omega⟩ : Fin (n + m + 1))
      have he := lazyTwoDimensionalPrefix_append_right (x : ℤ) y w v j
      rw [hX] at he
      exact h.trans he

/-- On a past word cylinder, every represented full prefix has an actual
future word starting at the past endpoint. This discharges off-source atoms. -/
theorem lazyTwoDimensionalPrefix_tail_mem_range
    (n m x X : ℕ) (y : ℤ) (w : Fin n → Fin 3)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ))
    (p : ℕ → ℤ × ℤ)
    (hp : (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w)
    (hs : (fun j : Fin (n + m + 1) => p j.val) ∈
      Set.range (@lazyTwoDimensionalPrefix (n + m) (x : ℤ) y)) :
    (fun j : Fin (m + 1) => p (n + j.val)) ∈
      Set.range (@lazyTwoDimensionalPrefix m (X : ℤ)
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2) := by
  obtain ⟨u, hu⟩ := hs
  let a : Fin n → Fin 3 := fun i => u (Fin.castAdd m i)
  let b : Fin m → Fin 3 := fun i => u (Fin.natAdd n i)
  have hab : Fin.append a b = u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left a b j
    · exact Fin.append_right a b j
  have ha : lazyTwoDimensionalPrefix (x : ℤ) y a =
      lazyTwoDimensionalPrefix (x : ℤ) y w := by
    funext j
    have h := congrFun hu (⟨j.val, by omega⟩ : Fin (n + m + 1))
    rw [← hab] at h
    rw [lazyTwoDimensionalPrefix_append_left] at h
    exact h.trans (congrFun hp j)
  have haw : a = w := lazyTwoDimensionalPrefix_injective (x : ℤ) y ha
  refine ⟨b, ?_⟩
  funext j
  have h := congrFun hu (⟨n + j.val, by omega⟩ : Fin (n + m + 1))
  rw [← hab] at h
  rw [lazyTwoDimensionalPrefix_append_right, haw, hX] at h
  exact h

/-- The actual restricted future-prefix measure is its source RN law times
the actual past-cylinder probability. Equality holds on every measurable
event, including atoms outside the actual word image. -/
theorem conditionedSource_restrict_map_future_prefix
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n m X : ℕ) (w : Fin n → Fin 3)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    (ν.restrict {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w}).map
        (fun p => fun j : Fin (m + 1) => p (n + j.val)) =
      ν {p | (fun j : Fin (n + 1) => p j.val) =
        lazyTwoDimensionalPrefix (x : ℤ) y w} •
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3))).map
        (lazyTwoDimensionalPrefix (X : ℤ)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0)) := by
  classical
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q),
    Measure.restrict_apply ((measurableSet_singleton q).preimage (by fun_prop)),
    Measure.smul_apply, smul_eq_mul]
  by_cases hq : q ∈ Set.range (@lazyTwoDimensionalPrefix m (X : ℤ)
      (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)
  · obtain ⟨v, rfl⟩ := hq
    have he :
        (fun p : ℕ → ℤ × ℤ => fun j : Fin (m + 1) => p (n + j.val)) ⁻¹'
            {lazyTwoDimensionalPrefix (X : ℤ)
              (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 v} ∩
          {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w} =
        {p | (fun j : Fin (n + m + 1) => p j.val) =
          lazyTwoDimensionalPrefix (x : ℤ) y (Fin.append w v)} := by
      rw [← lazyTwoDimensionalPrefix_joint_cylinder n m x X y w v hX]
      ext p
      exact and_comm
    rw [he]
    have hfull := congrArg
      (fun μ : Measure (Fin (n + m + 1) → ℤ × ℤ) =>
        μ {lazyTwoDimensionalPrefix (x : ℤ) y (Fin.append w v)}) (hRN (n + m))
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hfull
    change ν {p | (fun j : Fin (n + m + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y (Fin.append w v)} = _ at hfull
    rw [hfull, conditionedTwoDimensionalPrefix_atom_append n m x X y w v hX]
    have hpast := congrArg
      (fun μ : Measure (Fin (n + 1) → ℤ × ℤ) =>
        μ {lazyTwoDimensionalPrefix (x : ℤ) y w}) (hRN n)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hpast
    change ν {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w} = _ at hpast
    rw [hpast]
  · have hzero :
        ν ((fun p : ℕ → ℤ × ℤ => fun j : Fin (m + 1) => p (n + j.val)) ⁻¹' {q} ∩
          {p | (fun j : Fin (n + 1) => p j.val) =
            lazyTwoDimensionalPrefix (x : ℤ) y w}) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [conditionedSource_ae_prefix_mem_range x y ν hRN (n + m)] with p hp
      rintro ⟨htail, hpast⟩
      apply hq
      have h := lazyTwoDimensionalPrefix_tail_mem_range n m x X y w hX p hpast hp
      exact (Set.mem_singleton_iff.mp htail) ▸ h
    rw [hzero]
    have hz :
        (((Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3))).map
          (lazyTwoDimensionalPrefix (X : ℤ)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
            (fun q => if ∀ j, 0 ≤ (q j).1 then
              ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0))
          {q} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [lazyTwoDimensionalPrefix_withDensity_ae_mem_range m (X : ℤ)
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0)] with z hz
      intro he
      exact hq ((Set.mem_singleton_iff.mp he) ▸ hz)
    rw [hz, mul_zero]

/-- Normalizing the actual past-cylinder restriction produces the exact
all-horizon source RN law at the actual endpoint. Positivity of the
conditioning event is derived from the complete surviving-word condition. -/
theorem conditionedSource_normalized_tail_RN
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n X : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
    let η : Measure (ℕ → ℤ × ℤ) :=
      (ν C)⁻¹ • (ν.restrict C).map (fun p => fun k => p (n + k))
    ∀ m : ℕ, η.map (fun p => fun j : Fin (m + 1) => p j.val) =
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3))).map
        (lazyTwoDimensionalPrefix (X : ℤ)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0)) := by
  dsimp only
  intro m
  have hpos := (conditionedSource_prefix_atom_pos_iff x y ν hRN n w).mpr hw
  have hne := ne_of_gt hpos
  have hm : Measurable (fun p : ℕ → ℤ × ℤ => fun j : Fin (m + 1) => p j.val) :=
    by fun_prop
  rw [Measure.map_smul _ hm.aemeasurable,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change _ • (ν.restrict _).map
    (fun p => fun j : Fin (m + 1) => p (n + j.val)) = _
  rw [conditionedSource_restrict_map_future_prefix x y ν hRN n m X w hX,
    smul_smul, ENNReal.inv_mul_cancel hne (measure_ne_top _ _), one_smul]

end DirectedDistances.RandomWalk
