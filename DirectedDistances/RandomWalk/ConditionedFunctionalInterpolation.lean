/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedFunctionalLimitReduction
public import DirectedDistances.RandomWalk.IIDVectorWalk
import Mathlib.Topology.LocallyFinite
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Step paths and polygonal interpolation toward Lemma 4.11

The step path is the literal `z (floor (n*t)) / sqrt n`. Only the polygonal
interpolation is bundled as a continuous map. The discrete transform is the
actual `vectorPitman` coupled by `map_vectorPitman_codeWalk` in `IIDVectorWalk`.
No functional limit theorem or Bessel process law is assumed here. Joint iid
functional convergence and tightness, the whole-path Pitman/BES3 identification,
independence of the residual Brownian motion, and the limiting covariance and
normalization remain separate obligations. -/

public section
namespace DirectedDistances.RandomWalk

open scoped NNReal

/-- Literal adjacent-grid interpolation, before diffusive scaling. -/
@[expose] noncomputable def walkLinearScalar (p : ℕ → ℝ) (x : ℝ≥0) : ℝ :=
  p ⌊(x : ℝ)⌋₊ + ((x : ℝ) - (⌊(x : ℝ)⌋₊ : ℝ)) *
    (p (⌊(x : ℝ)⌋₊ + 1) - p ⌊(x : ℝ)⌋₊)

/-- On a closed grid cell the interpolation is the affine formula, including its right end. -/
theorem walkLinearScalar_on_cell (p : ℕ → ℝ) (k : ℕ) (x : ℝ≥0)
    (hx : x ∈ Set.Icc (k : ℝ≥0) (k + 1)) :
    walkLinearScalar p x = p k + ((x : ℝ) - k) * (p (k + 1) - p k) := by
  have hl : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  have hu : (x : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hx.2
  by_cases h : (x : ℝ) < (k : ℝ) + 1
  · have he := (Nat.floor_eq_iff x.coe_nonneg).mpr ⟨hl, h⟩
    simp only [walkLinearScalar, he]
  · have he : (x : ℝ) = (k : ℝ) + 1 := le_antisymm hu (le_of_not_gt h)
    have hf : ⌊(x : ℝ)⌋₊ = k + 1 := by
      rw [he, ← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
    unfold walkLinearScalar
    rw [hf, he]
    push_cast
    ring

/-- Polygonal interpolation is continuous on the entire nonnegative half-line. -/
theorem continuous_walkLinearScalar (p : ℕ → ℝ) : Continuous (walkLinearScalar p) := by
  have hlf : LocallyFinite (fun k : ℕ => Set.Icc (k : ℝ≥0) (k + 1)) := by
    intro x
    refine ⟨Set.Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩
    apply (Finset.range (⌊((x : ℝ) + 1)⌋₊ + 1)).finite_toSet.subset
    intro k hk
    obtain ⟨y, hy, hyx⟩ := hk
    have hky : (k : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy.1
    have hyx' : (y : ℝ) < (x : ℝ) + 1 := by exact_mod_cast hyx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hky.trans hyx'.le)))
  apply hlf.continuous
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨⌊(x : ℝ)⌋₊, ?_⟩
    constructor
    · exact_mod_cast Nat.floor_le x.coe_nonneg
    · exact_mod_cast (Nat.lt_floor_add_one (x : ℝ)).le
  · intro k
    exact isClosed_Icc
  · intro k
    have hc : Continuous (fun x : ℝ≥0 =>
        p k + ((x : ℝ) - k) * (p (k + 1) - p k)) := by fun_prop
    exact hc.continuousOn.congr (fun x hx => walkLinearScalar_on_cell p k x hx)

/-- The source step rescaling on all times, without imposing continuity on a step path. -/
@[expose] noncomputable def diffusiveStep (n : ℕ) (z : ℕ → ℤ × ℤ)
    (t : ℝ≥0) : ℝ × ℝ :=
  (((z ⌊(n : ℝ) * t⌋₊).1 : ℝ) / Real.sqrt n,
    ((z ⌊(n : ℝ) * t⌋₊).2 : ℝ) / Real.sqrt n)

/-- Actual polygonal interpolation between adjacent rescaled walk values. -/
@[expose] noncomputable def diffusiveInterpolation (n : ℕ) (z : ℕ → ℤ × ℤ) :
    C(ℝ≥0, ℝ × ℝ) where
  toFun t := (walkLinearScalar (fun k => ((z k).1 : ℝ)) ((n : ℝ≥0) * t) / Real.sqrt n,
    walkLinearScalar (fun k => ((z k).2 : ℝ)) ((n : ℝ≥0) * t) / Real.sqrt n)
  continuous_toFun := by
    exact (((continuous_walkLinearScalar _).comp (continuous_const.mul continuous_id)).div_const _).prodMk
      (((continuous_walkLinearScalar _).comp (continuous_const.mul continuous_id)).div_const _)

/-- The interpolation agrees with every grid value, including time zero. -/
theorem diffusiveInterpolation_grid (n : ℕ) (hn : 0 < n) (z : ℕ → ℤ × ℤ) (k : ℕ) :
    diffusiveInterpolation n z ((k : ℝ≥0) / n) =
      (((z k).1 : ℝ) / Real.sqrt n, ((z k).2 : ℝ) / Real.sqrt n) := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (n : ℝ≥0) * ((k : ℝ≥0) / n) = k := mul_div_cancel₀ _ hn0
  simp only [diffusiveInterpolation, ContinuousMap.coe_mk, he, walkLinearScalar,
    NNReal.coe_natCast, Nat.floor_natCast, sub_self, zero_mul, add_zero]

/-- At every grid time the step rescaling takes exactly the integer-time value. -/
theorem diffusiveStep_grid (n : ℕ) (hn : 0 < n) (z : ℕ → ℤ × ℤ) (k : ℕ) :
    diffusiveStep n z ((k : ℝ≥0) / n) =
      (((z k).1 : ℝ) / Real.sqrt n, ((z k).2 : ℝ) / Real.sqrt n) := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (n : ℝ≥0) * ((k : ℝ≥0) / n) = k := mul_div_cancel₀ _ hn0
  have heR : (n : ℝ) * (((k : ℝ≥0) / n : ℝ≥0) : ℝ) = k := by exact_mod_cast he
  simp only [diffusiveStep, heR, Nat.floor_natCast]

/-- Step and interpolation agree at every grid time, including the initial grid point. -/
theorem diffusiveStep_eq_interpolation_grid (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (k : ℕ) :
    diffusiveStep n z ((k : ℝ≥0) / n) =
      diffusiveInterpolation n z ((k : ℝ≥0) / n) := by
  rw [diffusiveStep_grid n hn z k, diffusiveInterpolation_grid n hn z k]

/-- The initial values are literal, with no start-at-zero hypothesis on the walk. -/
theorem diffusiveStep_interpolation_zero (n : ℕ) (z : ℕ → ℤ × ℤ) :
    diffusiveStep n z 0 = (((z 0).1 : ℝ) / Real.sqrt n, ((z 0).2 : ℝ) / Real.sqrt n) ∧
    diffusiveInterpolation n z 0 =
      (((z 0).1 : ℝ) / Real.sqrt n, ((z 0).2 : ℝ) / Real.sqrt n) := by
  simp only [diffusiveStep, diffusiveInterpolation, ContinuousMap.coe_mk,
    walkLinearScalar, NNReal.coe_zero, mul_zero, Nat.floor_zero, Nat.cast_zero,
    sub_self, zero_mul, add_zero, and_self]

/-- On each closed rescaled grid cell the two coordinates are exactly the affine
interpolants between its endpoints. This includes the last fractional cell of any horizon. -/
theorem diffusiveInterpolation_on_cell (n : ℕ) (z : ℕ → ℤ × ℤ) (k : ℕ)
    (t : ℝ≥0) (ht : (n : ℝ≥0) * t ∈ Set.Icc (k : ℝ≥0) (k + 1)) :
    diffusiveInterpolation n z t =
      ((((z k).1 : ℝ) + ((n : ℝ) * t - k) * (((z (k + 1)).1 : ℝ) - (z k).1)) /
        Real.sqrt n,
       (((z k).2 : ℝ) + ((n : ℝ) * t - k) * (((z (k + 1)).2 : ℝ) - (z k).2)) /
        Real.sqrt n) := by
  change (walkLinearScalar _ _ / _, walkLinearScalar _ _ / _) = _
  rw [walkLinearScalar_on_cell _ k _ ht, walkLinearScalar_on_cell _ k _ ht]
  rfl

/-- A unit increment bounds the error on each complete or fractional cell. -/
theorem walkLinearScalar_sub_abs_le (p : ℕ → ℝ)
    (hp : ∀ k, |p (k + 1) - p k| ≤ 1) (x : ℝ≥0) :
    |p ⌊(x : ℝ)⌋₊ - walkLinearScalar p x| ≤ 1 := by
  have ha : 0 ≤ (x : ℝ) - (⌊(x : ℝ)⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le x.coe_nonneg)
  have hb : (x : ℝ) - (⌊(x : ℝ)⌋₊ : ℝ) ≤ 1 := by
    linarith only [Nat.lt_floor_add_one (x : ℝ)]
  calc
    |p ⌊(x : ℝ)⌋₊ - walkLinearScalar p x| =
        ((x : ℝ) - (⌊(x : ℝ)⌋₊ : ℝ)) * |p (⌊(x : ℝ)⌋₊ + 1) - p ⌊(x : ℝ)⌋₊| := by
      simp only [walkLinearScalar, sub_add_cancel_left, abs_neg, abs_mul, abs_of_nonneg ha]
    _ ≤ ((x : ℝ) - (⌊(x : ℝ)⌋₊ : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (hp _) ha
    _ ≤ 1 := by simpa only [mul_one] using hb

/-- Both source coordinates have interpolation error at most `1 / sqrt n`, at every time. -/
theorem diffusiveStep_sub_interpolation_abs_le (n : ℕ) (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (t : ℝ≥0) :
    |(diffusiveStep n z t).1 - (diffusiveInterpolation n z t).1| ≤ 1 / Real.sqrt n ∧
    |(diffusiveStep n z t).2 - (diffusiveInterpolation n z t).2| ≤ 1 / Real.sqrt n := by
  have h₁ := walkLinearScalar_sub_abs_le (fun k => ((z k).1 : ℝ)) (fun k => (hz k).1)
    ((n : ℝ≥0) * t)
  have h₂ := walkLinearScalar_sub_abs_le (fun k => ((z k).2 : ℝ)) (fun k => (hz k).2)
    ((n : ℝ≥0) * t)
  have hs := Real.sqrt_nonneg (n : ℝ)
  constructor
  · simpa only [diffusiveStep, diffusiveInterpolation, ContinuousMap.coe_mk,
      NNReal.coe_mul, NNReal.coe_natCast, ← sub_div, abs_div, abs_of_nonneg hs] using
      div_le_div_of_nonneg_right h₁ hs
  · simpa only [diffusiveStep, diffusiveInterpolation, ContinuousMap.coe_mk,
      NNReal.coe_mul, NNReal.coe_natCast, ← sub_div, abs_div, abs_of_nonneg hs] using
      div_le_div_of_nonneg_right h₂ hs

/-- The step path visits precisely the integer prefix, including its final grid value.
This image identity uses no continuity assumption. -/
theorem scaledStep_image_prefix {β : Type*} (p : ℕ → β) (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) :
    (fun s : ℝ≥0 => p ⌊(n : ℝ) * s⌋₊) '' Set.Icc 0 t =
      p '' Set.Iic ⌊(n : ℝ) * t⌋₊ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnN : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  ext b
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⌊(n : ℝ) * s⌋₊, ?_, rfl⟩
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hs.2) hnR.le)
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ℝ≥0) / n, ⟨zero_le, ?_⟩, ?_⟩
    · have hkr : (k : ℝ) ≤ (n : ℝ) * t :=
        (by exact_mod_cast hk : (k : ℝ) ≤ (⌊(n : ℝ) * t⌋₊ : ℝ)).trans
          (Nat.floor_le (mul_nonneg hnR.le t.coe_nonneg))
      apply (div_le_iff₀ (show 0 < (n : ℝ≥0) by exact_mod_cast hn)).mpr
      have hkrt : (k : ℝ) ≤ (t : ℝ) * n := by simpa only [mul_comm] using hkr
      exact_mod_cast hkrt
    · have he : (n : ℝ≥0) * ((k : ℝ≥0) / n) = k := mul_div_cancel₀ _ hnN
      have heR : (n : ℝ) * (((k : ℝ≥0) / n : ℝ≥0) : ℝ) = k := by
        exact_mod_cast he
      dsimp only
      rw [heR, Nat.floor_natCast]

/-- The running minimum of a step coordinate is the scaled discrete prefix minimum.
In particular the discontinuous step image is nonempty and bounded below. -/
theorem diffusiveStep_runningMinimum (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (t : ℝ≥0) :
    sInf ((fun s => (diffusiveStep n z s).1) '' Set.Icc 0 t) =
      (globalLazyRunningMinimum (fun k => (z k).1) ⌊(n : ℝ) * t⌋₊ : ℝ) / Real.sqrt n := by
  change sInf ((fun s : ℝ≥0 =>
    ((z ⌊(n : ℝ) * s⌋₊).1 : ℝ) / Real.sqrt n) '' Set.Icc 0 t) = _
  rw [scaledStep_image_prefix (fun k => ((z k).1 : ℝ) / Real.sqrt n) n hn t]
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.range (⌊(n : ℝ) * t⌋₊ + 1)) ⟨0, by simp⟩ (fun k => (z k).1)
  have hj' : j ≤ ⌊(n : ℝ) * t⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hmin : globalLazyRunningMinimum (fun k => (z k).1) ⌊(n : ℝ) * t⌋₊ = (z j).1 := he
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨j, hj', by rw [hmin]⟩
  · rintro b ⟨k, hk, rfl⟩
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast globalLazyRunningMinimum_le (fun k => (z k).1) hk)
      (Real.sqrt_nonneg _)

/-- Infimum stability on a nonempty domain with bounded-below images.
Unlike the continuous-path helper this applies directly to step paths. -/
theorem sInf_image_sub_abs_le {α : Type*} (A : Set α) (hA : A.Nonempty)
    (f g : α → ℝ) (hf : BddBelow (f '' A)) (hg : BddBelow (g '' A))
    {ε : ℝ} (hfg : ∀ s ∈ A, |f s - g s| ≤ ε) :
    |sInf (f '' A) - sInf (g '' A)| ≤ ε := by
  apply abs_le.mpr
  constructor
  · have h : sInf (g '' A) - ε ≤ sInf (f '' A) := by
      apply le_csInf (hA.image f)
      rintro b ⟨s, hs, rfl⟩
      have hg' := csInf_le hg (Set.mem_image_of_mem g hs)
      have hfg' := (abs_le.mp (hfg s hs)).1
      linarith only [hg', hfg']
    linarith only [h]
  · have h : sInf (f '' A) - ε ≤ sInf (g '' A) := by
      apply le_csInf (hA.image g)
      rintro b ⟨s, hs, rfl⟩
      have hf' := csInf_le hf (Set.mem_image_of_mem f hs)
      have hfg' := (abs_le.mp (hfg s hs)).2
      linarith only [hf', hfg']
    linarith only [h]

/-- A step coordinate has a bounded-below image on every finite initial interval. -/
theorem diffusiveStep_fst_bddBelow (n : ℕ) (z : ℕ → ℤ × ℤ) (t : ℝ≥0) :
    BddBelow ((fun s => (diffusiveStep n z s).1) '' Set.Icc 0 t) := by
  refine ⟨(globalLazyRunningMinimum (fun k => (z k).1) ⌊(n : ℝ) * t⌋₊ : ℝ) /
    Real.sqrt n, ?_⟩
  rintro b ⟨s, hs, rfl⟩
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hst : ⌊(n : ℝ) * s⌋₊ ≤ ⌊(n : ℝ) * t⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hs.2) (Nat.cast_nonneg n))
  exact_mod_cast globalLazyRunningMinimum_le (fun k => (z k).1) hst

/-- Running minima of the step path and its actual interpolation differ by at most
`1 / sqrt n`. The step path is handled as an unbundled function. -/
theorem diffusiveStep_interpolation_runningMinimum_abs_le (n : ℕ)
    (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (t : ℝ≥0) :
    |sInf ((fun s => (diffusiveStep n z s).1) '' Set.Icc 0 t) -
      sInf ((fun s => (diffusiveInterpolation n z s).1) '' Set.Icc 0 t)| ≤
        1 / Real.sqrt n := by
  apply sInf_image_sub_abs_le (Set.Icc 0 t) ⟨0, le_rfl, zero_le⟩
    (fun s => (diffusiveStep n z s).1) (fun s => (diffusiveInterpolation n z s).1)
    (diffusiveStep_fst_bddBelow n z t)
    (isCompact_Icc.bddBelow_image (diffusiveInterpolation n z).continuous.fst.continuousOn)
  intro s _
  exact (diffusiveStep_sub_interpolation_abs_le n z hz s).1

/-- Scaling the actual discrete vector Pitman transform gives the literal continuous
formula applied to the step values and their (discontinuous-path) running minimum. -/
theorem diffusiveStep_vectorPitman (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (t : ℝ≥0) :
    diffusiveStep n (vectorPitman z) t =
      ((diffusiveStep n z t).1 - 2 *
        sInf ((fun s => (diffusiveStep n z s).1) '' Set.Icc 0 t),
       (diffusiveStep n z t).2 +
        sInf ((fun s => (diffusiveStep n z s).1) '' Set.Icc 0 t)) := by
  rw [diffusiveStep_runningMinimum n hn z t]
  apply Prod.ext <;> simp only [diffusiveStep, vectorPitman, globalLazyPhi,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_add] <;> ring

/-- Exact coordinate transport estimates toward Lemma 4.11 at every time.
The constants are shared across all finite horizons. -/
theorem diffusiveStep_vectorPitman_sub_abs_le (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (t : ℝ≥0) :
    |(diffusiveStep n (vectorPitman z) t).1 -
      (continuousVectorPitman (diffusiveInterpolation n z) t).1| ≤ 3 / Real.sqrt n ∧
    |(diffusiveStep n (vectorPitman z) t).2 -
      (continuousVectorPitman (diffusiveInterpolation n z) t).2| ≤ 2 / Real.sqrt n := by
  have hm := abs_le.mp (diffusiveStep_interpolation_runningMinimum_abs_le n z hz t)
  have h₁ := abs_le.mp (diffusiveStep_sub_interpolation_abs_le n z hz t).1
  have h₂ := abs_le.mp (diffusiveStep_sub_interpolation_abs_le n z hz t).2
  rw [diffusiveStep_vectorPitman n hn z t, continuousVectorPitman_apply]
  dsimp only [Prod.fst, Prod.snd]
  simp only [div_eq_mul_inv, one_mul] at hm h₁ h₂ ⊢
  constructor <;> apply abs_le.mpr <;> constructor <;>
    linarith only [hm.1, hm.2, h₁.1, h₁.2, h₂.1, h₂.2]

/-- Every compact horizon has the same step/interpolation coordinate supremum bound. -/
theorem diffusiveStep_interpolation_sup_le (n : ℕ) (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (T : ℝ≥0) :
    sSup ((fun t => |(diffusiveStep n z t).1 - (diffusiveInterpolation n z t).1|) ''
      Set.Icc 0 T) ≤ 1 / Real.sqrt n ∧
    sSup ((fun t => |(diffusiveStep n z t).2 - (diffusiveInterpolation n z t).2|) ''
      Set.Icc 0 T) ≤ 1 / Real.sqrt n := by
  constructor
  · apply csSup_le ((Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ T)).image _)
    rintro b ⟨t, _, rfl⟩
    exact (diffusiveStep_sub_interpolation_abs_le n z hz t).1
  · apply csSup_le ((Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ T)).image _)
    rintro b ⟨t, _, rfl⟩
    exact (diffusiveStep_sub_interpolation_abs_le n z hz t).2

/-- The conditioned-step versus continuous-Pitman comparison holds in coordinate
suprema on every compact horizon, with the exact constants `3` and `2`. -/
theorem diffusiveStep_vectorPitman_sup_le (n : ℕ) (hn : 0 < n) (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (T : ℝ≥0) :
    sSup ((fun t => |(diffusiveStep n (vectorPitman z) t).1 -
      (continuousVectorPitman (diffusiveInterpolation n z) t).1|) '' Set.Icc 0 T) ≤
        3 / Real.sqrt n ∧
    sSup ((fun t => |(diffusiveStep n (vectorPitman z) t).2 -
      (continuousVectorPitman (diffusiveInterpolation n z) t).2|) '' Set.Icc 0 T) ≤
        2 / Real.sqrt n := by
  constructor
  · apply csSup_le ((Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ T)).image _)
    rintro b ⟨t, _, rfl⟩
    exact (diffusiveStep_vectorPitman_sub_abs_le n hn z hz t).1
  · apply csSup_le ((Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ T)).image _)
    rintro b ⟨t, _, rfl⟩
    exact (diffusiveStep_vectorPitman_sub_abs_le n hn z hz t).2

/-- The bounded-increment premise is proved for every actual source code sequence,
with the `codeWalk` indexing and all three literal `Fin 3` steps. -/
theorem codeWalk_real_coord_increment_abs_le (ω : ℕ → Fin 3) (k : ℕ) :
    |((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1| ≤ 1 ∧
    |((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2| ≤ 1 := by
  have h := codeWalk_succ_sub ω k
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂
  rw [← Int.cast_sub, ← Int.cast_sub, h₁, h₂]
  generalize ω (k + 1) = c
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

/-- The actual code walk satisfies the coordinate supremum estimate on every horizon. -/
theorem codeWalk_interpolation_sup_le (n : ℕ) (ω : ℕ → Fin 3) (T : ℝ≥0) :
    sSup ((fun t => |(diffusiveStep n (codeWalk ω) t).1 -
      (diffusiveInterpolation n (codeWalk ω) t).1|) '' Set.Icc 0 T) ≤ 1 / Real.sqrt n ∧
    sSup ((fun t => |(diffusiveStep n (codeWalk ω) t).2 -
      (diffusiveInterpolation n (codeWalk ω) t).2|) '' Set.Icc 0 T) ≤ 1 / Real.sqrt n :=
  diffusiveStep_interpolation_sup_le n _ (codeWalk_real_coord_increment_abs_le ω) T

/-- Deterministic transport for the actual coupling whose pushforward law is
`map_vectorPitman_codeWalk` in `IIDVectorWalk`; no law or functional convergence is assumed. -/
theorem codeWalk_vectorPitman_interpolation_sup_le (n : ℕ) (hn : 0 < n)
    (ω : ℕ → Fin 3) (T : ℝ≥0) :
    sSup ((fun t => |(diffusiveStep n (vectorPitman (codeWalk ω)) t).1 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t).1|) ''
      Set.Icc 0 T) ≤ 3 / Real.sqrt n ∧
    sSup ((fun t => |(diffusiveStep n (vectorPitman (codeWalk ω)) t).2 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t).2|) ''
      Set.Icc 0 T) ≤ 2 / Real.sqrt n :=
  diffusiveStep_vectorPitman_sup_le n hn _ (codeWalk_real_coord_increment_abs_le ω) T

end DirectedDistances.RandomWalk
