/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WholeLineGlue
public import DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
public import DirectedDistances.Probability.SkorokhodJ1LocalPositive

import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Continuity of left-limit gluing in the local J1 distance

Deterministic part of the joint-convergence-and-gluing step: the window of the glued
whole-line path depends J1-continuously on the cutoff windows of the two half-line paths. -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter TopologicalSpace
open scoped Topology

/-- Extension of a window time change to the real line (identity outside the window). -/
private noncomputable def timeChangeExt {T : ℝ} (φ : J1TimeChange T) (r : ℝ) : ℝ :=
  if h : r ∈ Set.Icc (0 : ℝ) T then ((φ ⟨r, h⟩ : J1Window T) : ℝ) else r

private theorem timeChangeExt_of_mem {T : ℝ} (φ : J1TimeChange T) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    timeChangeExt φ r = ((φ ⟨r, hr⟩ : J1Window T) : ℝ) := by
  unfold timeChangeExt
  rw [dite_eq_left hr]

private theorem timeChangeExt_eq {T : ℝ} (φ : J1TimeChange T) (r : J1Window T) :
    timeChangeExt φ r.1 = (φ r).1 :=
  timeChangeExt_of_mem φ r.2

private theorem timeChangeExt_mem {T : ℝ} (φ : J1TimeChange T) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) : timeChangeExt φ r ∈ Set.Icc (0 : ℝ) T := by
  rw [timeChangeExt_of_mem φ hr]
  exact (φ ⟨r, hr⟩).2

private theorem timeChangeExt_lt {T : ℝ} (φ : J1TimeChange T) {r r' : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hr' : r' ∈ Set.Icc (0 : ℝ) T) (h : r < r') :
    timeChangeExt φ r < timeChangeExt φ r' := by
  rw [timeChangeExt_of_mem φ hr, timeChangeExt_of_mem φ hr']
  have h1 : (⟨r, hr⟩ : J1Window T) < ⟨r', hr'⟩ := h
  exact φ.strictMono h1

private theorem timeChange_zero {T : ℝ} (hT : 0 < T) (φ : J1TimeChange T) :
    φ ⟨0, ⟨le_rfl, hT.le⟩⟩ = ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
  apply Subtype.ext
  apply le_antisymm
  · obtain ⟨x, hx⟩ := φ.surjective ⟨0, ⟨le_rfl, hT.le⟩⟩
    have hxe : (⟨0, ⟨le_rfl, hT.le⟩⟩ : J1Window T) ≤ x := x.property.1
    have hmono := φ.monotone hxe
    rw [hx] at hmono
    exact hmono
  · exact (φ _).property.1

private theorem timeChange_pos {T : ℝ} (hT : 0 < T) (ψ : J1TimeChange T)
    (s : J1Window T) (hs : 0 < s.1) : 0 < (ψ s).1 := by
  have h1 := ψ.strictMono (show (⟨0, ⟨le_rfl, hT.le⟩⟩ : J1Window T) < s from hs)
  rw [timeChange_zero hT ψ] at h1
  exact h1

private theorem timeChangeExt_zero {T : ℝ} (hT : 0 < T) (φ : J1TimeChange T) :
    timeChangeExt φ 0 = 0 := by
  rw [timeChangeExt_of_mem φ (⟨le_rfl, hT.le⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T)]
  exact congrArg Subtype.val (timeChange_zero hT φ)

private theorem timeChangeExt_pos {T : ℝ} (hT : 0 < T) (φ : J1TimeChange T) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hr0 : 0 < r) : 0 < timeChangeExt φ r := by
  have h := timeChangeExt_lt φ (⟨le_rfl, hT.le⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T) hr hr0
  rwa [timeChangeExt_zero hT φ] at h

private theorem timeChangeExt_surj {T : ℝ} (φ : J1TimeChange T) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) T) : ∃ r ∈ Set.Icc (0 : ℝ) T, timeChangeExt φ r = v := by
  obtain ⟨a, ha⟩ := φ.surjective ⟨v, hv⟩
  refine ⟨a.1, a.2, ?_⟩
  rw [timeChangeExt_of_mem φ a.2]
  exact congrArg Subtype.val ha

/-- The concatenation at the midpoint of a pair of window time changes: the second one is
reflected through the midpoint. -/
private noncomputable def glueTimeFun {T : ℝ} (φ ψ : J1TimeChange T) (u : ℝ) : ℝ :=
  if T ≤ u then T + timeChangeExt φ (u - T) else T - timeChangeExt ψ (T - u)

private theorem glueTimeFun_mem {T : ℝ} (hT : 0 < T) (φ ψ : J1TimeChange T) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (2 * T)) :
    glueTimeFun φ ψ u ∈ Set.Icc (0 : ℝ) (2 * T) := by
  obtain ⟨hu0, hu1⟩ := hu
  unfold glueTimeFun
  split_ifs with h
  · obtain ⟨h1, h2⟩ := timeChangeExt_mem φ
      (⟨by linarith, by linarith⟩ : u - T ∈ Set.Icc (0 : ℝ) T)
    exact ⟨by linarith, by linarith⟩
  · have h' := not_le.mp h
    obtain ⟨h1, h2⟩ := timeChangeExt_mem ψ
      (⟨by linarith, by linarith⟩ : T - u ∈ Set.Icc (0 : ℝ) T)
    exact ⟨by linarith, by linarith⟩

private theorem glueTimeFun_lt {T : ℝ} (hT : 0 < T) (φ ψ : J1TimeChange T) {u u' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (2 * T)) (hu' : u' ∈ Set.Icc (0 : ℝ) (2 * T))
    (h : u < u') : glueTimeFun φ ψ u < glueTimeFun φ ψ u' := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hu'
  unfold glueTimeFun
  by_cases h1 : T ≤ u
  · have h2 : T ≤ u' := h1.trans h.le
    rw [ite_eq_left h1, ite_eq_left h2]
    have := timeChangeExt_lt φ (⟨by linarith, by linarith⟩ : u - T ∈ Set.Icc (0 : ℝ) T)
      (⟨by linarith, by linarith⟩ : u' - T ∈ Set.Icc (0 : ℝ) T) (by linarith)
    linarith
  · have h1' := not_le.mp h1
    rw [ite_eq_right h1]
    have hs := timeChangeExt_pos hT ψ
      (⟨by linarith, by linarith⟩ : T - u ∈ Set.Icc (0 : ℝ) T) (by linarith)
    by_cases h2 : T ≤ u'
    · rw [ite_eq_left h2]
      have := timeChangeExt_mem φ (⟨by linarith, by linarith⟩ : u' - T ∈ Set.Icc (0 : ℝ) T)
      linarith [this.1]
    · rw [ite_eq_right h2]
      have h2' := not_le.mp h2
      have := timeChangeExt_lt ψ (⟨by linarith, by linarith⟩ : T - u' ∈ Set.Icc (0 : ℝ) T)
        (⟨by linarith, by linarith⟩ : T - u ∈ Set.Icc (0 : ℝ) T) (by linarith)
      linarith

private theorem glueTimeFun_surj {T : ℝ} (hT : 0 < T) (φ ψ : J1TimeChange T) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (2 * T)) :
    ∃ u ∈ Set.Icc (0 : ℝ) (2 * T), glueTimeFun φ ψ u = v := by
  obtain ⟨hv0, hv1⟩ := hv
  by_cases h : T ≤ v
  · obtain ⟨r, ⟨hr0, hr1⟩, hr⟩ := timeChangeExt_surj φ
      (⟨by linarith, by linarith⟩ : v - T ∈ Set.Icc (0 : ℝ) T)
    refine ⟨T + r, ⟨by linarith, by linarith⟩, ?_⟩
    unfold glueTimeFun
    have hc : T ≤ T + r := by linarith
    rw [ite_eq_left hc, add_sub_cancel_left, hr]
    ring
  · have h' := not_le.mp h
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := timeChangeExt_surj ψ
      (⟨by linarith, by linarith⟩ : T - v ∈ Set.Icc (0 : ℝ) T)
    have hspos : 0 < s := by
      rcases lt_or_eq_of_le hs0 with h0 | h0
      · exact h0
      · exfalso
        rw [← h0, timeChangeExt_zero hT ψ] at hs
        linarith
    refine ⟨T - s, ⟨by linarith, by linarith⟩, ?_⟩
    unfold glueTimeFun
    have hc : ¬ T ≤ T - s := not_le.mpr (by linarith)
    rw [ite_eq_right hc, sub_sub_cancel, hs]
    ring

private theorem exists_glueTimeChange {T : ℝ} (hT : 0 < T) (φ ψ : J1TimeChange T) :
    ∃ Φ : J1TimeChange (2 * T),
      (∀ (u : J1Window (2 * T)) (r : J1Window T), T ≤ u.1 → r.1 = u.1 - T →
        (Φ u).1 = T + (φ r).1) ∧
      (∀ (u : J1Window (2 * T)) (s : J1Window T), u.1 < T → s.1 = T - u.1 →
        (Φ u).1 = T - (ψ s).1) := by
  let f : J1Window (2 * T) → J1Window (2 * T) :=
    fun u => ⟨glueTimeFun φ ψ u.1, glueTimeFun_mem hT φ ψ u.2⟩
  have hmono : StrictMono f := fun u u' h => glueTimeFun_lt hT φ ψ u.2 u'.2 h
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨u, hu, hv⟩ := glueTimeFun_surj hT φ ψ v.2
    exact ⟨⟨u, hu⟩, Subtype.ext hv⟩
  let Φ : J1TimeChange (2 * T) := StrictMono.orderIsoOfSurjective f hmono hsurj
  have hΦ : ∀ u : J1Window (2 * T), (Φ u).1 = glueTimeFun φ ψ u.1 := fun u => rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro u r hu hr
    rw [hΦ]
    unfold glueTimeFun
    rw [ite_eq_left hu, ← hr, timeChangeExt_eq φ r]
  · intro u s hu hs
    rw [hΦ]
    unfold glueTimeFun
    rw [ite_eq_right (not_le.mpr hu), ← hs, timeChangeExt_eq ψ s]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
A time change of a window with uniformly small displacement and value error bounds the
J1 window distance. -/
theorem j1WindowDist_le_of_timeChange_bound {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (Φ : J1TimeChange T) (c : ℝ)
    (hd : ∀ t : J1Window T, |((Φ t : ℝ) - (t : ℝ))| ≤ c)
    (hv : ∀ t : J1Window T, |f.1 (Φ t) - g.1 t| ≤ c) :
    j1WindowDist hT f g ≤ c := by
  have : Nonempty (J1Window T) := ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩
  have hbdd : BddBelow (Set.range fun φ : J1TimeChange T =>
      max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact le_max_of_le_left (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ)
      ⟨0, ⟨le_rfl, hT.le⟩⟩ (abs_nonneg _))
  unfold j1WindowDist
  refine le_trans (ciInf_le hbdd Φ) ?_
  apply max_le
  · exact ciSup_le hd
  · exact ciSup_le hv

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
A J1 window distance below `c` is witnessed by a time change with displacement and value
error below `c`. -/
theorem exists_timeChange_of_j1WindowDist_lt {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (c : ℝ) (h : j1WindowDist hT f g < c) :
    ∃ φ : J1TimeChange T, (∀ t : J1Window T, |((φ t : ℝ) - (t : ℝ))| < c) ∧
      (∀ t : J1Window T, |f.1 (φ t) - g.1 t| < c) := by
  have : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  change (⨅ φ : J1TimeChange T,
    max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) < c at h
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt h
  refine ⟨φ, fun t => ?_, fun t => ?_⟩
  · have hle : |((φ t : ℝ) - (t : ℝ))| ≤
        max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) :=
      (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) t le_rfl).trans
        (le_max_left _ _)
    exact hle.trans_lt hφ
  · have hle : |f.1 (φ t) - g.1 t| ≤
        max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) :=
      (le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) t le_rfl).trans
        (le_max_right _ _)
    exact hle.trans_lt hφ

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The glued whole-line path of two nonnegative paths vanishing at zero, as an element of the
whole-line càdlàg space. -/
noncomputable def wholeLineGlueCadlag (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) : WholeLineCadlag :=
  ⟨wholeLineGlue x y hx0 hy0, wholeLineGlue_isCadlag x y hx0 hy0⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The value of the left-limit reversal of the cutoff window at a positive window time `s`:
the left limit of `y` at `s` times the cutoff. -/
noncomputable def reversedWindowValue (m : ℕ) (y : CadlagNonnegative)
    (s : J1Window ((m : ℝ) + 1)) : ℝ :=
  y.1.leftLim (localWindowTime s) * localCutoff m (localWindowTime s)

private theorem glueWindowPath_right (m : ℕ) (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    (u : J1Window (2 * ((m : ℝ) + 1))) (r : J1Window ((m : ℝ) + 1))
    (hr : r.1 = u.1 - ((m : ℝ) + 1)) :
    (wholeLineJ1WindowPath m (wholeLineGlueCadlag x y hx0 hy0)).1 u =
      (cutoffWindow m x).1 r := by
  have ht : (u : ℝ) - ((m : ℝ) + 1) = r.1 := hr.symm
  have hg := wholeLineGlue_nonnegative x y hx0 hy0 (localWindowTime r)
  show wholeLineJ1Cutoff m ((u : ℝ) - ((m : ℝ) + 1)) *
      wholeLineGlue x y hx0 hy0 ((u : ℝ) - ((m : ℝ) + 1)) =
    x.1 (localWindowTime r) * localCutoff m (localWindowTime r)
  rw [ht]
  have hc : wholeLineJ1Cutoff m r.1 = localCutoff m (localWindowTime r) := by
    show max 0 (min 1 ((m : ℝ) + 1 - |r.1|)) = max 0 (min 1 ((m : ℝ) + 1 - r.1))
    rw [abs_of_nonneg r.2.1]
  rw [hc, mul_comm]
  congr 1

private theorem glueWindowPath_left (m : ℕ) (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    (u : J1Window (2 * ((m : ℝ) + 1))) (s : J1Window ((m : ℝ) + 1))
    (hu : u.1 < (m : ℝ) + 1) (hs : s.1 = ((m : ℝ) + 1) - u.1) :
    (wholeLineJ1WindowPath m (wholeLineGlueCadlag x y hx0 hy0)).1 u =
      reversedWindowValue m y s := by
  have ht : (u : ℝ) - ((m : ℝ) + 1) < 0 := by linarith
  have hsv : (localWindowTime s : Set.Ici (0 : ℝ)) =
      ⟨-((u : ℝ) - ((m : ℝ) + 1)), neg_nonneg.mpr ht.le⟩ :=
    Subtype.ext (by
      show (s : ℝ) = -((u : ℝ) - ((m : ℝ) + 1))
      linarith [hs])
  show wholeLineJ1Cutoff m ((u : ℝ) - ((m : ℝ) + 1)) *
      wholeLineGlue x y hx0 hy0 ((u : ℝ) - ((m : ℝ) + 1)) =
    y.1.leftLim (localWindowTime s) * localCutoff m (localWindowTime s)
  rw [wholeLineGlue_negative x y hx0 hy0 ht, hsv, mul_comm]
  congr 1
  show max 0 (min 1 ((m : ℝ) + 1 - |(u : ℝ) - ((m : ℝ) + 1)|)) =
    max 0 (min 1 ((m : ℝ) + 1 - (-((u : ℝ) - ((m : ℝ) + 1)))))
  rw [abs_of_neg ht]

private theorem cutoffWindow_tendsto_reversed (m : ℕ) (y : CadlagNonnegative)
    (s : J1Window ((m : ℝ) + 1)) (hs : 0 < s.1) :
    Tendsto (fun r : J1Window ((m : ℝ) + 1) => (cutoffWindow m y).1 r) (𝓝[<] s)
      (𝓝 (reversedWindowValue m y s)) := by
  let p : Set.Ici (0 : ℝ) := localWindowTime s
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl⟩, hs⟩
  have hl := y.2.tendsto_nhdsLT_leftLim p
  have hcut : Tendsto (localCutoff m) (𝓝[<] p) (𝓝 (localCutoff m p)) :=
    (localCutoff_continuous m).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hl.mul hcut
  have hmap : Tendsto (localWindowTime (T := (m : ℝ) + 1)) (𝓝[<] s) (𝓝[<] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(localWindowTime_continuous.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro t ht
    change (t : ℝ) < (s : ℝ) at ht
    exact Set.mem_Iio.mpr ht
  exact hprod.comp hmap

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Time-change transport for the left-limit reversal on a window: a time change `ψ` of
`[0,m+1]` that aligns the cutoff windows of `y` and `y'` within `c` also aligns the
left-limit reversal values at every positive window time. -/
theorem reversedWindowValue_transport (m : ℕ) (y y' : CadlagNonnegative)
    (ψ : J1TimeChange ((m : ℝ) + 1)) (c : ℝ)
    (h : ∀ t : J1Window ((m : ℝ) + 1),
      |(cutoffWindow m y).1 (ψ t) - (cutoffWindow m y').1 t| ≤ c)
    (s : J1Window ((m : ℝ) + 1)) (hs : 0 < s.1) :
    |reversedWindowValue m y (ψ s) - reversedWindowValue m y' s| ≤ c := by
  have hT : 0 < (m : ℝ) + 1 := by positivity
  have h0M : 0 ≤ (m : ℝ) + 1 := hT.le
  have hψs : 0 < (ψ s).1 := timeChange_pos hT ψ s hs
  have : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨⟨0, ⟨le_rfl, h0M⟩⟩, hs⟩
  have hψmap : Tendsto ψ (𝓝[<] s) (𝓝[<] (ψ s)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(j1TimeChange_continuous ψ).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro t ht
    exact ψ.strictMono (Set.mem_Iio.mp ht)
  have h1 := (cutoffWindow_tendsto_reversed m y (ψ s) hψs).comp hψmap
  have h2 := cutoffWindow_tendsto_reversed m y' s hs
  have h3 := (continuous_abs.tendsto _).comp (h1.sub h2)
  exact le_of_tendsto h3 (Eventually.of_forall fun r => h r)

private theorem wholeLineJ1WindowDistance_glue_le_of_lt (m : ℕ)
    (xa ya xb yb : CadlagNonnegative)
    (hxa : xa.1 ⟨0, le_rfl⟩ = 0) (hya : ya.1 ⟨0, le_rfl⟩ = 0)
    (hxb : xb.1 ⟨0, le_rfl⟩ = 0) (hyb : yb.1 ⟨0, le_rfl⟩ = 0) (c : ℝ)
    (hx : j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
      (cutoffWindow m xa) (cutoffWindow m xb) < c)
    (hy : j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
      (cutoffWindow m ya) (cutoffWindow m yb) < c) :
    wholeLineJ1WindowDistance m (wholeLineGlueCadlag xa ya hxa hya)
      (wholeLineGlueCadlag xb yb hxb hyb) ≤ c := by
  have hT : 0 < (m : ℝ) + 1 := by positivity
  obtain ⟨φ, hφd, hφv⟩ := exists_timeChange_of_j1WindowDist_lt hT _ _ c hx
  obtain ⟨ψ, hψd, hψv⟩ := exists_timeChange_of_j1WindowDist_lt hT _ _ c hy
  obtain ⟨Φ, hΦr, hΦl⟩ := exists_glueTimeChange hT φ ψ
  unfold wholeLineJ1WindowDistance
  refine j1WindowDist_le_of_timeChange_bound _ _ _ Φ c ?_ ?_
  · intro u
    by_cases hu : (m : ℝ) + 1 ≤ u.1
    · obtain ⟨r, hr⟩ : ∃ r : J1Window ((m : ℝ) + 1), r.1 = u.1 - ((m : ℝ) + 1) :=
        ⟨⟨u.1 - ((m : ℝ) + 1), ⟨by linarith, by linarith [u.2.2]⟩⟩, rfl⟩
      have h1 := hΦr u r hu hr
      obtain ⟨a1, a2⟩ := abs_lt.mp (hφd r)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hu' := not_le.mp hu
      obtain ⟨s, hs⟩ : ∃ s : J1Window ((m : ℝ) + 1), s.1 = ((m : ℝ) + 1) - u.1 :=
        ⟨⟨((m : ℝ) + 1) - u.1, ⟨by linarith, by linarith [u.2.1]⟩⟩, rfl⟩
      have h1 := hΦl u s hu' hs
      obtain ⟨a1, a2⟩ := abs_lt.mp (hψd s)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro u
    by_cases hu : (m : ℝ) + 1 ≤ u.1
    · obtain ⟨r, hr⟩ : ∃ r : J1Window ((m : ℝ) + 1), r.1 = u.1 - ((m : ℝ) + 1) :=
        ⟨⟨u.1 - ((m : ℝ) + 1), ⟨by linarith, by linarith [u.2.2]⟩⟩, rfl⟩
      have h1 := hΦr u r hu hr
      have hr' : (φ r).1 = (Φ u).1 - ((m : ℝ) + 1) := by linarith
      rw [glueWindowPath_right m xa ya hxa hya (Φ u) (φ r) hr',
        glueWindowPath_right m xb yb hxb hyb u r hr]
      exact (hφv r).le
    · have hu' := not_le.mp hu
      obtain ⟨s, hs⟩ : ∃ s : J1Window ((m : ℝ) + 1), s.1 = ((m : ℝ) + 1) - u.1 :=
        ⟨⟨((m : ℝ) + 1) - u.1, ⟨by linarith, by linarith [u.2.1]⟩⟩, rfl⟩
      have h1 := hΦl u s hu' hs
      have hpos : 0 < (ψ s).1 := timeChange_pos hT ψ s (by linarith)
      have hlt : (Φ u).1 < (m : ℝ) + 1 := by linarith
      have hs' : (ψ s).1 = ((m : ℝ) + 1) - (Φ u).1 := by linarith
      rw [glueWindowPath_left m xa ya hxa hya (Φ u) (ψ s) hlt hs',
        glueWindowPath_left m xb yb hxb hyb u s hu' hs]
      exact reversedWindowValue_transport m ya yb ψ c (fun t => (hψv t).le) s
        (by linarith)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The window of the glued whole-line path on `[-m-1,m+1]` is within the larger of the J1
distances of the cutoff windows of the two half-line paths. -/
theorem wholeLineJ1WindowDistance_glue_le (m : ℕ)
    (xa ya xb yb : CadlagNonnegative)
    (hxa : xa.1 ⟨0, le_rfl⟩ = 0) (hya : ya.1 ⟨0, le_rfl⟩ = 0)
    (hxb : xb.1 ⟨0, le_rfl⟩ = 0) (hyb : yb.1 ⟨0, le_rfl⟩ = 0) :
    wholeLineJ1WindowDistance m (wholeLineGlueCadlag xa ya hxa hya)
        (wholeLineGlueCadlag xb yb hxb hyb) ≤
      max (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m xa) (cutoffWindow m xb))
        (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m ya) (cutoffWindow m yb)) := by
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have hmid := wholeLineJ1WindowDistance_glue_le_of_lt m xa ya xb yb hxa hya hxb hyb
    ((wholeLineJ1WindowDistance m (wholeLineGlueCadlag xa ya hxa hya)
        (wholeLineGlueCadlag xb yb hxb hyb) +
      max (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m xa) (cutoffWindow m xb))
        (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m ya) (cutoffWindow m yb))) / 2)
    (by
      have := le_max_left (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m xa) (cutoffWindow m xb))
        (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m ya) (cutoffWindow m yb))
      linarith)
    (by
      have := le_max_right (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m xa) (cutoffWindow m xb))
        (j1WindowDist (by positivity : 0 < (m : ℝ) + 1)
          (cutoffWindow m ya) (cutoffWindow m yb))
      linarith)
  linarith

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
If `xn → x` and `yn → y` in the positive local J1 distance, with all paths vanishing at the
origin, then the left-limit gluings converge in the whole-line local J1 distance.  No
continuity at positive integers is needed for this deterministic statement. -/
theorem wholeLineGlue_tendsto_of_local_tendsto
    (xn yn : ℕ → CadlagNonnegative) (x y : CadlagNonnegative)
    (hxn : ∀ k, (xn k).1 ⟨0, le_rfl⟩ = 0) (hyn : ∀ k, (yn k).1 ⟨0, le_rfl⟩ = 0)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    (hx : Tendsto (fun k => j1LocalDist (xn k) x) atTop (𝓝 0))
    (hy : Tendsto (fun k => j1LocalDist (yn k) y) atTop (𝓝 0)) :
    Tendsto (fun k => wholeLineLocalJ1Distance
      (wholeLineGlueCadlag (xn k) (yn k) (hxn k) (hyn k))
      (wholeLineGlueCadlag x y hx0 hy0)) atTop (𝓝 0) := by
  refine (wholeLineLocalJ1Distance_tendsto_iff_window_tendsto
    (fun k => wholeLineGlueCadlag (xn k) (yn k) (hxn k) (hyn k))
    (wholeLineGlueCadlag x y hx0 hy0)).2 ?_
  intro m
  have hx' : Tendsto (fun k => weightedJ1ProductDist (localWindowCoordinates (xn k))
      (localWindowCoordinates x)) atTop (𝓝 0) := hx
  have hy' : Tendsto (fun k => weightedJ1ProductDist (localWindowCoordinates (yn k))
      (localWindowCoordinates y)) atTop (𝓝 0) := hy
  have hxm := weightedJ1ProductDist_tendsto_coordinate
    (fun k => localWindowCoordinates (xn k)) (localWindowCoordinates x) hx' m
  have hym := weightedJ1ProductDist_tendsto_coordinate
    (fun k => localWindowCoordinates (yn k)) (localWindowCoordinates y) hy' m
  have hmax := hxm.max hym
  rw [max_self] at hmax
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hmax
  · exact j1WindowDist_nonneg (by positivity : 0 < 2 * ((m : ℝ) + 1)) _ _
  · exact wholeLineJ1WindowDistance_glue_le m (xn k) (yn k) x y (hxn k) (hyn k) hx0 hy0

end DirectedDistances.Probability
