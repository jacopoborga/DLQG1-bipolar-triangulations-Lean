/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # The finite-interval lazy harmonic equation

Deterministic support for the gambler's-ruin calculation in Lemma 4.10
increment probabilities give the interior equation `3 f(i) =
f(i-1) + f(i) + f(i+1)`. Its finite-interval solution is uniquely affine.

These are numerical recurrence lemmas. They do not assert that an infinite
walk exits an interval, nor identify an unconstructed hitting-event probability
with a harmonic function, nor prove the numbered conditioned-walk result. -/

public section
namespace DirectedDistances.RandomWalk

open Filter
open scoped Topology

/-- The lazy harmonic recurrence forces a constant slope on its whole finite
interval. No probabilistic assumption is hidden in the recurrence. -/
theorem lazy_harmonic_eq_initial_slope {f : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i, 0 < i → i < N →
      3 * f i = f (i - 1) + f i + f (i + 1)) :
    ∀ i, i ≤ N → f i = f 0 + (i : ℝ) * (f 1 - f 0) := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, add_zero]
  | one =>
      intro _
      simp only [Nat.cast_one, one_mul, add_sub_cancel]
  | more i hi hi1 =>
      intro hi2
      have h₀ := hi (by omega : i ≤ N)
      have h₁ := hi1 (by omega : i + 1 ≤ N)
      have h₂ := hrec (i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h₁ h₂ ⊢
      nlinarith

/-- The unique lazy harmonic function on a finite interval is the affine
interpolation of its endpoint values. The positive interval length is explicit. -/
theorem lazy_harmonic_eq_affine {f : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hrec : ∀ i, 0 < i → i < N →
      3 * f i = f (i - 1) + f i + f (i + 1))
    (i : ℕ) (hi : i ≤ N) :
    f i = f 0 + (i : ℝ) / (N : ℝ) * (f N - f 0) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he := lazy_harmonic_eq_initial_slope hrec N le_rfl
  rw [lazy_harmonic_eq_initial_slope hrec i hi]
  have hs : f N - f 0 = (N : ℝ) * (f 1 - f 0) := by linarith
  rw [hs, ← mul_assoc, div_mul_cancel₀ _ hn]

/-- Boundary values zero and one determine the usual finite-interval
gambler's-ruin ratio, once a genuine hitting probability satisfies the recurrence.
This theorem itself is only uniqueness for a real-valued recurrence. -/
theorem lazy_harmonic_eq_ratio {f : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (h0 : f 0 = 0) (h1 : f N = 1)
    (hrec : ∀ i, 0 < i → i < N →
      3 * f i = f (i - 1) + f i + f (i + 1))
    (i : ℕ) (hi : i ≤ N) : f i = (i : ℝ) / (N : ℝ) := by
  rw [lazy_harmonic_eq_affine hN hrec i hi, h0, h1]
  simp only [sub_zero, mul_one, zero_add]

/-- The literal finite-horizon survival recursion of the uniform lazy walk
killed on its first negative state. The time argument precedes the starting
state. This numerical definition is not a new conditioned process. -/
@[expose] noncomputable def lazyKilledSurvival : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, 0 => (lazyKilledSurvival n 0 + lazyKilledSurvival n 1) / 3
  | n + 1, z + 1 =>
      (lazyKilledSurvival n z + lazyKilledSurvival n (z + 1) +
        lazyKilledSurvival n (z + 2)) / 3

/-- The time-zero survival value. -/
theorem lazyKilledSurvival_zero (z : ℕ) : lazyKilledSurvival 0 z = 1 := rfl

/-- At the killing boundary only the holding and upward moves survive. -/
theorem lazyKilledSurvival_succ_zero (n : ℕ) :
    lazyKilledSurvival (n + 1) 0 =
      (lazyKilledSurvival n 0 + lazyKilledSurvival n 1) / 3 := rfl

/-- At a positive state all three one-step moves remain nonnegative. -/
theorem lazyKilledSurvival_succ_succ (n z : ℕ) :
    lazyKilledSurvival (n + 1) (z + 1) =
      (lazyKilledSurvival n z + lazyKilledSurvival n (z + 1) +
        lazyKilledSurvival n (z + 2)) / 3 := rfl

/-- Actual survival probabilities can be identified with the numerical
recursion by proving their initial value and genuine one-step decomposition. -/
theorem lazyKilledSurvival_unique {u : ℕ → ℕ → ℝ}
    (h0 : ∀ z, u 0 z = 1)
    (hz : ∀ n, u (n + 1) 0 = (u n 0 + u n 1) / 3)
    (hs : ∀ n z, u (n + 1) (z + 1) =
      (u n z + u n (z + 1) + u n (z + 2)) / 3) :
    ∀ n z, u n z = lazyKilledSurvival n z := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      intro z
      cases z with
      | zero => rw [hz, lazyKilledSurvival_succ_zero, ih, ih]
      | succ z => rw [hs, lazyKilledSurvival_succ_succ, ih, ih, ih]

/-- The killed first moment of the shifted height is conserved by the literal
lazy recurrence. To apply this to an expectation, its actual one-step
decomposition must first be proved; no martingale or stopping claim is assumed. -/
theorem lazy_killed_first_moment_eq {u : ℕ → ℕ → ℝ}
    (h0 : ∀ z, u 0 z = (z : ℝ) + 1)
    (hz : ∀ n, u (n + 1) 0 = (u n 0 + u n 1) / 3)
    (hs : ∀ n z, u (n + 1) (z + 1) =
      (u n z + u n (z + 1) + u n (z + 2)) / 3) :
    ∀ n z, u n z = (z : ℝ) + 1 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      intro z
      cases z with
      | zero => rw [hz, ih, ih]; norm_num
      | succ z =>
          rw [hs, ih, ih, ih]
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring

/-- Every recursion value lies in the probability interval. -/
theorem lazyKilledSurvival_mem_unitInterval (n z : ℕ) :
    0 ≤ lazyKilledSurvival n z ∧ lazyKilledSurvival n z ≤ 1 := by
  induction n generalizing z with
  | zero => simp only [lazyKilledSurvival_zero]; norm_num
  | succ n ih =>
      cases z with
      | zero =>
          rw [lazyKilledSurvival_succ_zero]
          have h0 := ih 0
          have h1 := ih 1
          constructor <;> linarith
      | succ z =>
          rw [lazyKilledSurvival_succ_succ]
          have h0 := ih z
          have h1 := ih (z + 1)
          have h2 := ih (z + 2)
          constructor <;> linarith

/-- Surviving one additional step can only decrease the recursion value. -/
theorem lazyKilledSurvival_succ_le (n z : ℕ) :
    lazyKilledSurvival (n + 1) z ≤ lazyKilledSurvival n z := by
  induction n generalizing z with
  | zero =>
      rw [lazyKilledSurvival_zero]
      exact (lazyKilledSurvival_mem_unitInterval 1 z).2
  | succ n ih =>
      cases z with
      | zero =>
          change (lazyKilledSurvival (n + 1) 0 + lazyKilledSurvival (n + 1) 1) / 3 ≤
            (lazyKilledSurvival n 0 + lazyKilledSurvival n 1) / 3
          have h0 := ih 0
          have h1 := ih 1
          linarith
      | succ z =>
          change (lazyKilledSurvival (n + 1) z + lazyKilledSurvival (n + 1) (z + 1) +
            lazyKilledSurvival (n + 1) (z + 2)) / 3 ≤
              (lazyKilledSurvival n z + lazyKilledSurvival n (z + 1) +
                lazyKilledSurvival n (z + 2)) / 3
          have h0 := ih z
          have h1 := ih (z + 1)
          have h2 := ih (z + 2)
          linarith

/-- For every fixed starting state the numerical survival values decrease
with the horizon. -/
theorem antitone_lazyKilledSurvival (z : ℕ) :
    Antitone (fun n => lazyKilledSurvival n z) :=
  antitone_nat_of_succ_le (fun n => lazyKilledSurvival_succ_le n z)

/-- A nonnegative bounded killed-lazy harmonic function on the half-line
vanishes. This is the recurrence argument that replaces a stochastic recurrence
or gambler's-ruin black box in the survival-limit calculation. -/
theorem lazy_killed_harmonic_eq_zero {f : ℕ → ℝ}
    (hnonneg : ∀ z, 0 ≤ f z) (hbound : ∀ z, f z ≤ 1)
    (hz : 3 * f 0 = f 0 + f 1)
    (hs : ∀ z, 3 * f (z + 1) = f z + f (z + 1) + f (z + 2)) :
    ∀ z, f z = 0 := by
  have hform : ∀ z, f z = ((z : ℝ) + 1) * f 0 := by
    intro z
    induction z using Nat.twoStepInduction with
    | zero => simp only [Nat.cast_zero, zero_add, one_mul]
    | one => norm_num only [Nat.cast_one] at ⊢; linarith
    | more z h0 h1 =>
        have h2 := hs z
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1 ⊢
        nlinarith
  have hf0 : f 0 = 0 := by
    apply le_antisymm _ (hnonneg 0)
    by_contra h
    have hp : 0 < f 0 := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / f 0)
    have hm : 1 < (n : ℝ) * f 0 := (div_lt_iff₀ hp).mp hn
    have hb := hbound n
    rw [hform n] at hb
    nlinarith
  intro z
  rw [hform z, hf0, mul_zero]

/-- The finite-horizon killed-lazy survival recursion tends to zero at every
fixed starting state. This is a numerical theorem; identifying genuine random
walk survival events with this recursion remains a separate measure-theoretic
obligation. -/
theorem tendsto_lazyKilledSurvival (z : ℕ) :
    Tendsto (fun n => lazyKilledSurvival n z) atTop (𝓝 0) := by
  let g : ℕ → ℝ := fun x => ⨅ n, lazyKilledSurvival n x
  have hbb (x : ℕ) : BddBelow (Set.range (fun n => lazyKilledSurvival n x)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (lazyKilledSurvival_mem_unitInterval n x).1
  have hlim (x : ℕ) : Tendsto (fun n => lazyKilledSurvival n x) atTop (𝓝 (g x)) :=
    tendsto_atTop_ciInf (antitone_lazyKilledSurvival x) (hbb x)
  have hnonneg (x : ℕ) : 0 ≤ g x := by
    exact le_ciInf (fun n => (lazyKilledSurvival_mem_unitInterval n x).1)
  have hbound (x : ℕ) : g x ≤ 1 := by
    exact (ciInf_le (hbb x) 0).trans_eq (lazyKilledSurvival_zero x)
  have hz : 3 * g 0 = g 0 + g 1 := by
    have hl := (hlim 0).comp (tendsto_add_atTop_nat 1)
    have hr := ((hlim 0).add (hlim 1)).div_const 3
    have he : g 0 = (g 0 + g 1) / 3 :=
      tendsto_nhds_unique hl (by
        change Tendsto (fun n => (lazyKilledSurvival n 0 + lazyKilledSurvival n 1) / 3)
          atTop (𝓝 ((g 0 + g 1) / 3))
        exact hr)
    linarith
  have hs (x : ℕ) : 3 * g (x + 1) = g x + g (x + 1) + g (x + 2) := by
    have hl := (hlim (x + 1)).comp (tendsto_add_atTop_nat 1)
    have hr := (((hlim x).add (hlim (x + 1))).add (hlim (x + 2))).div_const 3
    have he : g (x + 1) = (g x + g (x + 1) + g (x + 2)) / 3 :=
      tendsto_nhds_unique hl (by
        change Tendsto (fun n => (lazyKilledSurvival n x + lazyKilledSurvival n (x + 1) +
          lazyKilledSurvival n (x + 2)) / 3) atTop (𝓝 ((g x + g (x + 1) + g (x + 2)) / 3))
        exact hr)
    linarith
  have hg := lazy_killed_harmonic_eq_zero hnonneg hbound hz hs z
  simpa only [hg] using hlim z

end DirectedDistances.RandomWalk
