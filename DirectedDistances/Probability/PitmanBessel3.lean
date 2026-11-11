/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedFunctionalLimitReduction
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped NNReal

-- Local canonical Borel instances avoid importing an unavailable dependency artifact.
local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℝ × ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ × ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, Fin 3 → ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, Fin 3 → ℝ) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: the one-dimensional Pitman transform with running minimum. -/
@[expose] noncomputable def scalarPitman (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => f t - 2 * continuousRunningMinimum f t,
    f.continuous.sub (continuous_const.mul (continuousRunningMinimum f).continuous)⟩

/-- Helper toward Lemma 4.11: the scalar transform is continuous on whole paths. -/
theorem continuous_scalarPitman : Continuous scalarPitman := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.sub (continuous_const.mul continuous_runningMinimum_eval)

/-- Helper toward Lemma 4.11: the source normalization and correlation, on continuous paths. -/
@[expose] noncomputable def brownianMix (f g : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ × ℝ) :=
  ⟨fun t => (Real.sqrt (2 / 3) * f t,
    Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * g t - f t / 2)),
    (continuous_const.mul f.continuous).prodMk
      (continuous_const.mul ((continuous_const.mul g.continuous).sub
        (f.continuous.div_const 2)))⟩

/-- Helper toward Lemma 4.11: the linear coordinate change is continuous on path pairs. -/
theorem continuous_brownianMix :
    Continuous (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => brownianMix p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hf : Continuous (fun p : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × ℝ≥0 => p.1.1 p.2) :=
    continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
  have hg : Continuous (fun p : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × ℝ≥0 => p.1.2 p.2) :=
    continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
  exact (continuous_const.mul hf).prodMk
    (continuous_const.mul ((continuous_const.mul hg).sub (hf.div_const 2)))

/-- Helper toward Lemma 4.11: exact covariance quadratic form of the coordinate change.
Independent standard coordinates therefore give covariance matrix
`[[2/3, -1/3], [-1/3, 2/3]]`. -/
theorem brownianMix_covariance_form (a b : ℝ) :
    (Real.sqrt (2 / 3) * (a - b / 2)) ^ 2 +
      (Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * b)) ^ 2 =
        (2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2) := by
  have h₂ : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have h₃ : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc
    _ = Real.sqrt (2 / 3 : ℝ) ^ 2 * (a - b / 2) ^ 2 +
        Real.sqrt (2 / 3 : ℝ) ^ 2 * (Real.sqrt (3 : ℝ) ^ 2 / 4 * b ^ 2) := by ring
    _ = _ := by rw [h₂, h₃]; ring

/-- Helper toward Lemma 4.11: every linear projection of the normalized independent
Gaussian coordinates has the exact source covariance, including the zero-time case. -/
theorem hasLaw_brownianMix_projection {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {t : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 t) P) (hY : HasLaw Y (gaussianReal 0 t) P)
    (hI : IndepFun X Y P) (a b : ℝ) :
    HasLaw (fun ω => a * (Real.sqrt (2 / 3) * X ω) +
      b * (Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * Y ω - X ω / 2)))
      (gaussianReal 0 (((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal * t)) P := by
  let c : ℝ := Real.sqrt (2 / 3) * (a - b / 2)
  let d : ℝ := Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * b)
  have hi : IndepFun (fun ω => c * X ω) (fun ω => d * Y ω) P :=
    hI.comp (by fun_prop) (by fun_prop)
  have h := gaussianReal_add_gaussianReal_of_indepFun hi
    (gaussianReal_const_mul hX c) (gaussianReal_const_mul hY d)
  have hvar : (NNReal.mk (c ^ 2) (sq_nonneg _) * t +
      NNReal.mk (d ^ 2) (sq_nonneg _) * t) =
        ((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal * t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by
      nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b])]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
    rw [← add_mul, brownianMix_covariance_form]
  have he : (fun ω => a * (Real.sqrt (2 / 3) * X ω) +
      b * (Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * Y ω - X ω / 2))) =
        (fun ω => c * X ω) + (fun ω => d * Y ω) := by
    funext ω
    dsimp [c, d]
    ring
  rw [he]
  refine ⟨(hX.aemeasurable.const_mul c).add (hY.aemeasurable.const_mul d), ?_⟩
  simpa only [hvar, mul_zero, add_zero] using h

/-- Helper toward Lemma 4.11: positive scalar multiplication commutes with running minima. -/
theorem runningMinimum_const_mul (f : C(ℝ≥0, ℝ)) (c : ℝ) (hc : 0 ≤ c) (t : ℝ≥0) :
    sInf ((fun s => c * f s) '' Set.Icc 0 t) =
      c * continuousRunningMinimum f t := by
  let g : C(ℝ≥0, ℝ) := ⟨fun s => c * f s, continuous_const.mul f.continuous⟩
  obtain ⟨u, hu, heu, hminu⟩ := continuousRunningMinimum_exists_eq_and_le f t
  obtain ⟨v, hv, hev, hminv⟩ := continuousRunningMinimum_exists_eq_and_le g t
  change continuousRunningMinimum g t = c * continuousRunningMinimum f t
  rw [heu, hev]
  apply le_antisymm
  · exact hminv u hu
  · exact mul_le_mul_of_nonneg_left (hminu v hv) hc

/-- Helper toward Lemma 4.11: the vector transform acts only on the first independent
Brownian coordinate; the residual coordinate is retained on the entire path. -/
theorem continuousVectorPitman_brownianMix (f g : C(ℝ≥0, ℝ)) :
    continuousVectorPitman (brownianMix f g) = brownianMix (scalarPitman f) g := by
  ext t
  · change Real.sqrt (2 / 3) * f t -
        2 * sInf ((fun s => Real.sqrt (2 / 3) * f s) '' Set.Icc 0 t) =
      Real.sqrt (2 / 3) * (f t - 2 * continuousRunningMinimum f t)
    rw [runningMinimum_const_mul f _ (Real.sqrt_nonneg _) t]
    ring
  · change Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * g t - f t / 2) +
        sInf ((fun s => Real.sqrt (2 / 3) * f s) '' Set.Icc 0 t) =
      Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * g t -
        (f t - 2 * continuousRunningMinimum f t) / 2)
    rw [runningMinimum_const_mul f _ (Real.sqrt_nonneg _) t]
    ring

/-- Helper toward Lemma 4.11: the residual linear coordinate is unchanged by the transform. -/
theorem continuousVectorPitman_residual (f : C(ℝ≥0, ℝ × ℝ)) (t : ℝ≥0) :
    2 * (continuousVectorPitman f t).2 + (continuousVectorPitman f t).1 =
      2 * (f t).2 + (f t).1 := by
  simp only [continuousVectorPitman_apply]
  ring

/-- Helper toward Lemma 4.11: recovery of the independent residual Brownian coordinate. -/
theorem brownianMix_residual (f g : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    (2 * (brownianMix f g t).2 + (brownianMix f g t).1) /
      (Real.sqrt (2 / 3) * Real.sqrt 3) = g t := by
  have hd : Real.sqrt (2 / 3 : ℝ) * Real.sqrt 3 ≠ 0 := by positivity
  change (2 * (Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * g t - f t / 2)) +
    Real.sqrt (2 / 3) * f t) / _ = _
  apply (div_eq_iff hd).mpr
  ring

/-- Helper toward Lemma 4.11: measurable transforms of the first whole path preserve its
independence from the second whole path, including after the scalar Pitman transform. -/
theorem IndepFun.scalarPitman_left {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A B : Ω → C(ℝ≥0, ℝ)} (h : IndepFun A B P) :
    IndepFun (fun ω => scalarPitman (A ω)) B P := by
  simpa only [Function.comp_def, id_eq] using
    h.comp continuous_scalarPitman.measurable measurable_id

/-- Helper toward Lemma 4.11: the Euclidean radial path of three real coordinates. -/
@[expose] noncomputable def radial3Path
    (p : C(ℝ≥0, Fin 3 → ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => Real.sqrt ((p t 0) ^ 2 + (p t 1) ^ 2 + (p t 2) ^ 2), by fun_prop⟩

/-- Helper toward Lemma 4.11: the three-dimensional radial operator is continuous. -/
theorem continuous_radial3Path : Continuous radial3Path := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h (i : Fin 3) : Continuous
      (fun p : C(ℝ≥0, Fin 3 → ℝ) × ℝ≥0 => p.1 p.2 i) :=
    (continuous_apply i).comp continuous_eval
  exact Real.continuous_sqrt.comp (((h 0).pow 2 |>.add ((h 1).pow 2)).add ((h 2).pow 2))

/-- Helper toward Lemma 4.11: the radial law of a three-dimensional continuous path law.
When `W₃` is standard three-dimensional Brownian law, this is BES(3) started at zero.
The input law is not selected by choice or identified with the Pitman image. -/
@[expose] noncomputable def bessel3PathLaw (W₃ : Measure C(ℝ≥0, Fin 3 → ℝ)) :
    Measure C(ℝ≥0, ℝ) := W₃.map radial3Path

/-- Helper toward Lemma 4.11: the radial construction preserves total probability. -/
instance bessel3PathLaw_isProbabilityMeasure (W₃ : Measure C(ℝ≥0, Fin 3 → ℝ))
    [IsProbabilityMeasure W₃] : IsProbabilityMeasure (bessel3PathLaw W₃) :=
  (Measure.isProbabilityMeasure_map_iff
    continuous_radial3Path.measurable.aemeasurable).mpr inferInstance

/-- Helper toward Lemma 4.11: the radial path is nonnegative at every time. -/
theorem radial3Path_nonneg (p : C(ℝ≥0, Fin 3 → ℝ)) (t : ℝ≥0) :
    0 ≤ radial3Path p t := Real.sqrt_nonneg _

/-- Helper toward Lemma 4.11: the radial construction preserves a zero initial point. -/
theorem radial3Path_zero (p : C(ℝ≥0, Fin 3 → ℝ)) (hp : p 0 = 0) :
    radial3Path p 0 = 0 := by
  simp only [radial3Path, ContinuousMap.coe_mk, hp, Pi.zero_apply, zero_pow,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, add_zero, Real.sqrt_zero]

/- OPEN, with full binders: the one-dimensional whole-path Pitman theorem.
The coordinate maps in the independence premise have the product sigma algebra.

∀ (W : Measure C(ℝ≥0, ℝ)) (W₃ : Measure C(ℝ≥0, Fin 3 → ℝ))
  [IsProbabilityMeasure W] [IsProbabilityMeasure W₃]
  (hW : IsBrownianReal (fun t (f : C(ℝ≥0, ℝ)) => f t) W)
  (hW₃ : ∀ i : Fin 3,
    IsBrownianReal (fun t (f : C(ℝ≥0, Fin 3 → ℝ)) => f t i) W₃)
  (hI : iIndepFun (fun i (f : C(ℝ≥0, Fin 3 → ℝ)) => fun t => f t i) W₃),
  W.map scalarPitman = bessel3PathLaw W₃

This is not supplied by scalar Gaussian marginals or finite-dimensional CLTs.
Existence of Brownian measures on these continuous path spaces is a separate
obligation; no choice-defined Brownian law is introduced here. -/

end DirectedDistances.Probability
