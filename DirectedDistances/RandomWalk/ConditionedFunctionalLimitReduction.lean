/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith

/-! # Deterministic reductions toward Lemma 4.11

Running minima and the literal vector Pitman transform used toward
stability results, not a functional limit theorem. Step paths are not represented
as continuous maps here.

The existing source-law identification is
`IIDVectorWalk.map_vectorPitman_codeWalk`, with the all-prefix RN formula
`conditionedVectorPathLaw_map_prefix`. The deterministic operator below is to be
applied to polygonal interpolations of that iid walk; convergence of the
conditioned law is not assumed.

The remaining Lemma 4.11 obligations are joint iid functional convergence and
tightness, the step/interpolation transport bound `3 / sqrt n` on every compact
time interval, the whole-path Pitman-to-BES3 law, independence of the residual
Brownian motion, and the covariance/normalization calculation. These obligations
have no placeholder declarations in this module. -/

public section

namespace DirectedDistances.RandomWalk

open scoped NNReal

/-- Running minima on every initial interval preserve a uniform error bound.
This deterministic helper for Lemma 4.11 includes both zero horizons and zero times. -/
theorem runningMinimum_sub_abs_le (f g : C(ℝ≥0, ℝ)) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ s ∈ Set.Icc 0 T, |f s - g s| ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      |sInf (f '' Set.Icc 0 t) - sInf (g '' Set.Icc 0 t)| ≤ ε := by
  intro t ht
  have hne : (Set.Icc (0 : ℝ≥0) t).Nonempty := ⟨0, le_rfl, zero_le⟩
  obtain ⟨u, hu, hfu, hminf⟩ := isCompact_Icc.exists_sInf_image_eq_and_le
    hne f.continuous.continuousOn
  obtain ⟨v, hv, hgv, hming⟩ := isCompact_Icc.exists_sInf_image_eq_and_le
    hne g.continuous.continuousOn
  have huT : u ∈ Set.Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
  have hvT : v ∈ Set.Icc 0 T := ⟨hv.1, hv.2.trans ht.2⟩
  have hufg := (abs_le.mp (hfg u huT)).1
  have hvfg := (abs_le.mp (hfg v hvT)).2
  have huv := hminf v hv
  have hvu := hming u hu
  rw [hfu, hgv, abs_le]
  constructor <;> linarith only [hufg, hvfg, huv, hvu, hε]

/-- The fixed unit interval parameterizes every initial interval, including at time zero. -/
theorem image_unitInterval_mul (t : ℝ≥0) :
    (fun u : ℝ≥0 => u * t) '' Set.Icc 0 1 = Set.Icc 0 t := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨zero_le, ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hu.2 (zero_le : 0 ≤ t)
  · intro hs
    by_cases ht : t = 0
    · subst t
      have hs0 : s = 0 := le_antisymm hs.2 zero_le
      subst s
      exact ⟨0, ⟨le_rfl, zero_le⟩, zero_mul 0⟩
    · exact ⟨s / t, ⟨zero_le, (div_le_one₀ (pos_iff_ne_zero.mpr ht)).mpr hs.2⟩,
        div_mul_cancel₀ s ht⟩

/-- Fixed compact parameter formula for the running minimum in Lemma 4.11's reduction. -/
theorem runningMinimum_image_unitInterval (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (fun u : ℝ≥0 => f (u * t)) '' Set.Icc 0 1 = f '' Set.Icc 0 t := by
  rw [← image_unitInterval_mul t, Set.image_image]

/-- The running minimum is jointly continuous in the path and time for the compact-open topology. -/
theorem continuous_runningMinimum_eval :
    Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => sInf (p.1 '' Set.Icc 0 p.2)) := by
  have heval : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.1 (p.2 * p.1.2)) :=
    continuous_eval.comp
      (continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd))
  have hmin := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1)).continuous_sInf
    (f := fun p : C(ℝ≥0, ℝ) × ℝ≥0 => fun u : ℝ≥0 => p.1 (u * p.2)) heval
  simpa only [runningMinimum_image_unitInterval] using hmin

/-- A continuous path has a continuous running minimum, including at time zero. -/
theorem continuous_runningMinimum (f : C(ℝ≥0, ℝ)) :
    Continuous (fun t : ℝ≥0 => sInf (f '' Set.Icc 0 t)) :=
  continuous_runningMinimum_eval.comp (continuous_const.prodMk continuous_id)

/-- The running minimum as a continuous path; the displayed infimum is attained on every interval. -/
@[expose] noncomputable def continuousRunningMinimum (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => sInf (f '' Set.Icc 0 t), continuous_runningMinimum f⟩

/-- The bundled running minimum is the literal infimum on the initial interval. -/
@[simp] theorem continuousRunningMinimum_apply (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    continuousRunningMinimum f t = sInf (f '' Set.Icc 0 t) := rfl

/-- The running minimum is attained and is a lower bound for every value in the interval. -/
theorem continuousRunningMinimum_exists_eq_and_le (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc 0 t, continuousRunningMinimum f t = f u ∧
      ∀ s ∈ Set.Icc 0 t, f u ≤ f s :=
  isCompact_Icc.exists_sInf_image_eq_and_le ⟨0, le_rfl, zero_le⟩
    f.continuous.continuousOn

/-- At time zero the running minimum is the initial value, without a start-at-zero assumption. -/
@[simp] theorem continuousRunningMinimum_zero (f : C(ℝ≥0, ℝ)) :
    continuousRunningMinimum f 0 = f 0 := by
  simp only [continuousRunningMinimum_apply, Set.Icc_self, Set.image_singleton, csInf_singleton]

/-- Running minimum is a continuous operator on the existing compact-open path space. -/
theorem continuous_continuousRunningMinimum : Continuous continuousRunningMinimum :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_runningMinimum_eval

/-- The literal continuous vector Pitman transform used toward Lemma 4.11:
`(f₁ - 2 m(f₁), f₂ + m(f₁))`. No probability law is part of this definition. -/
@[expose] noncomputable def continuousVectorPitman
    (f : C(ℝ≥0, ℝ × ℝ)) : C(ℝ≥0, ℝ × ℝ) where
  toFun t := ((f t).1 - 2 * sInf ((fun s => (f s).1) '' Set.Icc 0 t),
    (f t).2 + sInf ((fun s => (f s).1) '' Set.Icc 0 t))
  continuous_toFun := by
    have hm := continuous_runningMinimum (⟨fun s => (f s).1, f.continuous.fst⟩ : C(ℝ≥0, ℝ))
    exact (f.continuous.fst.sub (continuous_const.mul hm)).prodMk (f.continuous.snd.add hm)

/-- The continuous vector Pitman transform is the literal two-coordinate formula. -/
@[simp] theorem continuousVectorPitman_apply (f : C(ℝ≥0, ℝ × ℝ)) (t : ℝ≥0) :
    continuousVectorPitman f t =
      ((f t).1 - 2 * sInf ((fun s => (f s).1) '' Set.Icc 0 t),
        (f t).2 + sInf ((fun s => (f s).1) '' Set.Icc 0 t)) := rfl

/-- The literal vector Pitman operator is continuous in the existing compact-open topology. -/
theorem continuous_continuousVectorPitman : Continuous continuousVectorPitman := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have he : Continuous (fun p : C(ℝ≥0, ℝ × ℝ) × ℝ≥0 => p.1 p.2) := continuous_eval
  have hemin : Continuous
      (fun p : (C(ℝ≥0, ℝ × ℝ) × ℝ≥0) × ℝ≥0 => (p.1.1 (p.2 * p.1.2)).1) :=
    (continuous_eval.comp
      (continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd))).fst
  have hm := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1)).continuous_sInf
    (f := fun p : C(ℝ≥0, ℝ × ℝ) × ℝ≥0 => fun u : ℝ≥0 => (p.1 (u * p.2)).1) hemin
  have hm' : Continuous (fun p : C(ℝ≥0, ℝ × ℝ) × ℝ≥0 =>
      sInf ((fun s => (p.1 s).1) '' Set.Icc 0 p.2)) := by
    convert hm using 1
    funext p
    rw [runningMinimum_image_unitInterval (fun s => (p.1 s).1) p.2]
  exact (he.fst.sub (continuous_const.mul hm')).prodMk (he.snd.add hm')

/-- Exact coordinate errors for the vector Pitman transform on a fixed horizon:
the first coordinate costs `3 ε`, the second `2 ε`. -/
theorem continuousVectorPitman_sub_abs_le
    (f g : C(ℝ≥0, ℝ × ℝ)) (T : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg₁ : ∀ s ∈ Set.Icc 0 T, |(f s).1 - (g s).1| ≤ ε)
    (hfg₂ : ∀ s ∈ Set.Icc 0 T, |(f s).2 - (g s).2| ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      |(continuousVectorPitman f t).1 - (continuousVectorPitman g t).1| ≤ 3 * ε ∧
      |(continuousVectorPitman f t).2 - (continuousVectorPitman g t).2| ≤ 2 * ε := by
  intro t ht
  have hm := runningMinimum_sub_abs_le
    (⟨fun s => (f s).1, f.continuous.fst⟩ : C(ℝ≥0, ℝ))
    (⟨fun s => (g s).1, g.continuous.fst⟩ : C(ℝ≥0, ℝ)) T hε hfg₁ t ht
  change |sInf ((fun s => (f s).1) '' Set.Icc 0 t) -
    sInf ((fun s => (g s).1) '' Set.Icc 0 t)| ≤ ε at hm
  have hm' := abs_le.mp hm
  have h₁ := abs_le.mp (hfg₁ t ht)
  have h₂ := abs_le.mp (hfg₂ t ht)
  change |((f t).1 - 2 * sInf ((fun s => (f s).1) '' Set.Icc 0 t)) -
      ((g t).1 - 2 * sInf ((fun s => (g s).1) '' Set.Icc 0 t))| ≤ 3 * ε ∧
    |((f t).2 + sInf ((fun s => (f s).1) '' Set.Icc 0 t)) -
      ((g t).2 + sInf ((fun s => (g s).1) '' Set.Icc 0 t))| ≤ 2 * ε
  constructor <;> apply abs_le.mpr <;> constructor <;>
    linarith only [hm'.1, hm'.2, h₁.1, h₁.2, h₂.1, h₂.2]

end DirectedDistances.RandomWalk
