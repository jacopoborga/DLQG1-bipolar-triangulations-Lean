/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowMetric

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Billingsley local Skorokhod J1 distance on the whole line -/

public section
namespace DirectedDistances.Probability

open Filter TopologicalSpace
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. Real-valued càdlàg paths on the whole real line. -/
abbrev WholeLineCadlag := {f : ℝ → ℝ // IsCadlag f}

/-- The continuous Billingsley cutoff: one on `[-m,m]`, zero outside
`[-m-1,m+1]`, and linear on each intervening interval.
Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. -/
def wholeLineJ1Cutoff (m : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 ((m : ℝ) + 1 - |t|))

private theorem wholeLineJ1Cutoff_continuous (m : ℕ) :
    Continuous (wholeLineJ1Cutoff m) := by
  unfold wholeLineJ1Cutoff
  fun_prop

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The cutoff is one on the centered core. -/
theorem wholeLineJ1Cutoff_eq_one {m : ℕ} {t : ℝ} (ht : |t| ≤ m) :
    wholeLineJ1Cutoff m t = 1 := by
  unfold wholeLineJ1Cutoff
  have h : 1 ≤ (m : ℝ) + 1 - |t| := by linarith
  simp [min_eq_left h]

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The cutoff vanishes outside its support window. -/
theorem wholeLineJ1Cutoff_eq_zero {m : ℕ} {t : ℝ}
    (ht : (m : ℝ) + 1 ≤ |t|) : wholeLineJ1Cutoff m t = 0 := by
  unfold wholeLineJ1Cutoff
  have h : (m : ℝ) + 1 - |t| ≤ 0 := by linarith
  rw [min_eq_right (le_trans h (by norm_num : (0 : ℝ) ≤ 1))]
  rw [max_eq_left h]

private def wholeLineJ1WindowTime (m : ℕ) :
    Set.Icc (0 : ℝ) (2 * ((m : ℝ) + 1)) → ℝ :=
  fun u => (u : ℝ) - ((m : ℝ) + 1)

private theorem wholeLineJ1WindowTime_right {m : ℕ}
    (a : Set.Icc (0 : ℝ) (2 * ((m : ℝ) + 1))) :
    Tendsto (wholeLineJ1WindowTime m)
      (𝓝[>] a) (𝓝[>] wholeLineJ1WindowTime m a) := by
  apply tendsto_nhdsWithin_iff.mpr
  have hcont : Continuous (wholeLineJ1WindowTime m) := by
    unfold wholeLineJ1WindowTime
    fun_prop
  refine ⟨hcont.continuousAt.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall ?_⟩
  · intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    dsimp [wholeLineJ1WindowTime]
    have hxReal : (a : ℝ) < (x : ℝ) := hx
    simpa [wholeLineJ1WindowTime] using
      (sub_lt_sub_right hxReal ((m : ℝ) + 1))

private theorem wholeLineJ1WindowTime_left {m : ℕ}
    (a : Set.Icc (0 : ℝ) (2 * ((m : ℝ) + 1))) :
    Tendsto (wholeLineJ1WindowTime m)
      (𝓝[<] a) (𝓝[<] wholeLineJ1WindowTime m a) := by
  apply tendsto_nhdsWithin_iff.mpr
  have hcont : Continuous (wholeLineJ1WindowTime m) := by
    unfold wholeLineJ1WindowTime
    fun_prop
  refine ⟨hcont.continuousAt.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall ?_⟩
  · intro x hx
    simp only [Set.mem_Iio] at hx ⊢
    dsimp [wholeLineJ1WindowTime]
    have hxReal : (x : ℝ) < (a : ℝ) := hx
    simpa [wholeLineJ1WindowTime] using
      (sub_lt_sub_right hxReal ((m : ℝ) + 1))

private theorem wholeLineJ1WindowPath_cadlag (m : ℕ) (f : WholeLineCadlag) :
    IsCadlag (fun u : Set.Icc (0 : ℝ) (2 * ((m : ℝ) + 1)) =>
      wholeLineJ1Cutoff m (wholeLineJ1WindowTime m u) *
        f.1 (wholeLineJ1WindowTime m u)) := by
  let h : ℝ → ℝ := fun t => wholeLineJ1Cutoff m t * f.1 t
  have hh : IsCadlag h :=
    (wholeLineJ1Cutoff_continuous m).isCadlag.mul f.2
  refine ⟨?_, ?_⟩
  · intro a
    exact (hh.isRightContinuous (wholeLineJ1WindowTime m a)).tendsto.comp
      (wholeLineJ1WindowTime_right a)
  · intro a
    obtain ⟨l, hl⟩ := hh.tendsto_nhdsLT (wholeLineJ1WindowTime m a)
    exact ⟨l, hl.comp (wholeLineJ1WindowTime_left a)⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The cutoff path on `[-m-1,m+1]`, represented on
`[0,2m+2]` by an affine time change. -/
noncomputable def wholeLineJ1WindowPath (m : ℕ) (f : WholeLineCadlag) :
    CadlagWindow (2 * ((m : ℝ) + 1)) :=
  ⟨fun u => wholeLineJ1Cutoff m (wholeLineJ1WindowTime m u) *
      f.1 (wholeLineJ1WindowTime m u),
    wholeLineJ1WindowPath_cadlag m f⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The J1 distance between the two cutoff paths on
`[-m-1,m+1]`. -/
noncomputable def wholeLineJ1WindowDistance (m : ℕ)
    (f g : WholeLineCadlag) : ℝ :=
  j1WindowDist (by positivity : 0 < 2 * ((m : ℝ) + 1))
    (wholeLineJ1WindowPath m f) (wholeLineJ1WindowPath m g)

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The `m`th weighted, truncated window distance. -/
noncomputable def wholeLineLocalJ1Term (m : ℕ) (f g : WholeLineCadlag) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 1) * min 1 (wholeLineJ1WindowDistance m f g)

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. Billingsley's weighted local J1 distance, with the
index shifted so the summands use windows `[-m-1,m+1]`. -/
noncomputable def wholeLineLocalJ1Distance
    (f g : WholeLineCadlag) : ℝ :=
  ∑' m : ℕ, wholeLineLocalJ1Term m f g

private theorem wholeLineJ1WindowDistance_nonneg (m : ℕ)
    (f g : WholeLineCadlag) : 0 ≤ wholeLineJ1WindowDistance m f g :=
  j1WindowDist_nonneg (by positivity) _ _

private theorem wholeLineJ1WindowDistance_self (m : ℕ)
    (f : WholeLineCadlag) : wholeLineJ1WindowDistance m f f = 0 := by
  exact j1WindowDist_self (by positivity) _

private theorem wholeLineJ1WindowDistance_symm (m : ℕ)
    (f g : WholeLineCadlag) :
    wholeLineJ1WindowDistance m f g = wholeLineJ1WindowDistance m g f := by
  exact j1WindowDist_symm (by positivity) _ _

private theorem wholeLineLocalJ1Term_summable (f g : WholeLineCadlag) :
    Summable (fun m => wholeLineLocalJ1Term m f g) := by
  have hweight : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 / 2 : ℝ) ^ n) 1).mpr
        summable_geometric_two
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hweight
  · change 0 ≤ (1 / 2 : ℝ) ^ (m + 1) *
      min 1 (wholeLineJ1WindowDistance m f g)
    exact mul_nonneg (by positivity)
      (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg m f g))
  · change (1 / 2 : ℝ) ^ (m + 1) *
      min 1 (wholeLineJ1WindowDistance m f g) ≤ (1 / 2 : ℝ) ^ (m + 1)
    calc
      (1 / 2 : ℝ) ^ (m + 1) *
          min 1 (wholeLineJ1WindowDistance m f g) ≤
        (1 / 2 : ℝ) ^ (m + 1) * 1 :=
          mul_le_mul_of_nonneg_left
            (min_le_left (1 : ℝ) (wholeLineJ1WindowDistance m f g))
            (by positivity)
      _ = (1 / 2 : ℝ) ^ (m + 1) := by ring

private theorem wholeLineLocalJ1Term_le_distance (m : ℕ)
    (f g : WholeLineCadlag) :
    wholeLineLocalJ1Term m f g ≤ wholeLineLocalJ1Distance f g := by
  unfold wholeLineLocalJ1Distance
  exact (wholeLineLocalJ1Term_summable f g).le_tsum m
    (fun i _ => by
      change 0 ≤ (1 / 2 : ℝ) ^ (i + 1) *
        min 1 (wholeLineJ1WindowDistance i f g)
      exact mul_nonneg (by positivity)
        (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg i f g)))

private theorem wholeLineLocalJ1Term_tendsto_zero
    (x : ℕ → WholeLineCadlag) (f : WholeLineCadlag)
    (hwin : ∀ m, Tendsto (fun k => wholeLineJ1WindowDistance m (x k) f)
      atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun k => wholeLineLocalJ1Term m (x k) f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let w : ℝ := (1 / 2 : ℝ) ^ (m + 1)
  let η : ℝ := min 1 (ε / w)
  have hw : 0 < w := by positivity
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hw)
  filter_upwards [(Metric.tendsto_nhds.mp (hwin m) η hη)] with k hk
  have hd : wholeLineJ1WindowDistance m (x k) f < η := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg
      (wholeLineJ1WindowDistance_nonneg m (x k) f)] using hk
  have hmin : min 1 (wholeLineJ1WindowDistance m (x k) f) < η :=
    (min_le_right 1 _).trans_lt hd
  have hterm : wholeLineLocalJ1Term m (x k) f < ε := by
    change w * min 1 (wholeLineJ1WindowDistance m (x k) f) < ε
    calc
      w * min 1 (wholeLineJ1WindowDistance m (x k) f) < w * η :=
        mul_lt_mul_of_pos_left hmin hw
      _ ≤ w * (ε / w) :=
        mul_le_mul_of_nonneg_left (min_le_right 1 (ε / w)) hw.le
      _ = ε := by field_simp
  rw [Real.dist_eq, sub_zero]
  change |(1 / 2 : ℝ) ^ (m + 1) *
    min 1 (wholeLineJ1WindowDistance m (x k) f)| < ε
  rw [abs_of_nonneg (mul_nonneg hw.le
    (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg m (x k) f)))]
  exact hterm


private theorem min_one_add_le {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b + c) : min 1 a ≤ min 1 b + min 1 c := by
  by_cases hb1 : 1 ≤ b
  · apply (min_le_iff).2
    left
    rw [min_eq_left hb1]
    have hcn : 0 ≤ min 1 c := le_min (by norm_num) hc
    linarith
  · by_cases hc1 : 1 ≤ c
    · apply (min_le_iff).2
      left
      rw [min_eq_left hc1]
      have hbn : 0 ≤ min 1 b := le_min (by norm_num) hb
      linarith
    · apply (min_le_iff).2
      right
      have hble : b ≤ 1 := le_of_lt (lt_of_not_ge hb1)
      have hcle : c ≤ 1 := le_of_lt (lt_of_not_ge hc1)
      rw [min_eq_right hble, min_eq_right hcle]
      exact hab

private theorem wholeLineLocalJ1Term_triangle (m : ℕ)
    (f g h : WholeLineCadlag) :
    wholeLineLocalJ1Term m f h ≤
      wholeLineLocalJ1Term m f g + wholeLineLocalJ1Term m g h := by
  have hclip := min_one_add_le
    (wholeLineJ1WindowDistance_nonneg m f g)
    (wholeLineJ1WindowDistance_nonneg m g h)
    (j1WindowDist_triangle (by positivity)
      (wholeLineJ1WindowPath m f) (wholeLineJ1WindowPath m g)
      (wholeLineJ1WindowPath m h))
  unfold wholeLineLocalJ1Term
  calc
    (1 / 2 : ℝ) ^ (m + 1) * min 1 (wholeLineJ1WindowDistance m f h) ≤
        (1 / 2 : ℝ) ^ (m + 1) *
          (min 1 (wholeLineJ1WindowDistance m f g) +
            min 1 (wholeLineJ1WindowDistance m g h)) :=
      mul_le_mul_of_nonneg_left hclip (by positivity)
    _ = _ := by ring


/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The weighted local J1 distance is reflexive. -/
theorem wholeLineLocalJ1Distance_self (f : WholeLineCadlag) :
    wholeLineLocalJ1Distance f f = 0 := by
  simp [wholeLineLocalJ1Distance, wholeLineLocalJ1Term,
    wholeLineJ1WindowDistance_self]

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The weighted local J1 distance is symmetric. -/
theorem wholeLineLocalJ1Distance_symm (f g : WholeLineCadlag) :
    wholeLineLocalJ1Distance f g = wholeLineLocalJ1Distance g f := by
  simp [wholeLineLocalJ1Distance, wholeLineLocalJ1Term,
    wholeLineJ1WindowDistance_symm]



/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The weighted local J1 distance is nonnegative. -/
theorem wholeLineLocalJ1Distance_nonneg (f g : WholeLineCadlag) :
    0 ≤ wholeLineLocalJ1Distance f g := by
  unfold wholeLineLocalJ1Distance
  apply tsum_nonneg
  intro m
  exact mul_nonneg (by positivity)
    (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg m f g))

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The weighted local J1 distance satisfies the triangle
inequality. -/
theorem wholeLineLocalJ1Distance_triangle (f g h : WholeLineCadlag) :
    wholeLineLocalJ1Distance f h ≤
      wholeLineLocalJ1Distance f g + wholeLineLocalJ1Distance g h := by
  unfold wholeLineLocalJ1Distance
  calc
    ∑' m, wholeLineLocalJ1Term m f h ≤
        ∑' m, (wholeLineLocalJ1Term m f g + wholeLineLocalJ1Term m g h) :=
      (wholeLineLocalJ1Term_summable f h).tsum_le_tsum
        (fun m => wholeLineLocalJ1Term_triangle m f g h)
        ((wholeLineLocalJ1Term_summable f g).add
          (wholeLineLocalJ1Term_summable g h))
    _ = _ := Summable.tsum_add
      (wholeLineLocalJ1Term_summable f g)
      (wholeLineLocalJ1Term_summable g h)

private theorem wholeLineLocalJ1WindowDistance_tendsto_of_distance_tendsto
    (x : ℕ → WholeLineCadlag) (f : WholeLineCadlag)
    (h : Tendsto (fun k => wholeLineLocalJ1Distance (x k) f) atTop (𝓝 0))
    (m : ℕ) :
    Tendsto (fun k => wholeLineJ1WindowDistance m (x k) f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let w : ℝ := (1 / 2 : ℝ) ^ (m + 1)
  let δ : ℝ := w * min ε 1
  have hw : 0 < w := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos hw (lt_min hε (by norm_num))
  filter_upwards [(tendsto_order.1 h).2 δ hδ] with k hk
  have hterm := wholeLineLocalJ1Term_le_distance m (x k) f
  have hterm' : w * min 1 (wholeLineJ1WindowDistance m (x k) f) ≤
      wholeLineLocalJ1Distance (x k) f := by
    simpa [w, wholeLineLocalJ1Term] using hterm
  have hstrict : w * min 1 (wholeLineJ1WindowDistance m (x k) f) <
      w * min ε 1 := by
    simpa [δ] using hterm'.trans_lt hk
  have hmin : min 1 (wholeLineJ1WindowDistance m (x k) f) < min ε 1 := by
    by_contra hnot
    have hle : min ε 1 ≤ min 1 (wholeLineJ1WindowDistance m (x k) f) :=
      le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_left hle hw.le
    exact (not_lt_of_ge hmul) hstrict
  have hdist : wholeLineJ1WindowDistance m (x k) f < ε := by
    have hltone : wholeLineJ1WindowDistance m (x k) f < 1 := by
      by_contra hnot
      have heq : min 1 (wholeLineJ1WindowDistance m (x k) f) = 1 :=
        min_eq_left (le_of_not_gt hnot)
      rw [heq] at hmin
      exact (not_lt_of_ge (min_le_right ε 1)) hmin
    rw [min_eq_right hltone.le] at hmin
    exact hmin.trans_le (min_le_left ε 1)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (wholeLineJ1WindowDistance_nonneg m (x k) f)]
  exact hdist

private theorem wholeLineLocalJ1TailWeight_eq (M : ℕ) :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + M) + 1)) = (1 / 2 : ℝ) ^ M := by
  have hgeom : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
    calc
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) =
          (1 / 2 : ℝ) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
        simp only [pow_succ']
        rw [tsum_mul_left]
      _ = 1 := by rw [tsum_geometric_two]; norm_num
  calc
    (∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + M) + 1)) =
        ∑' n : ℕ, (1 / 2 : ℝ) ^ M * (1 / 2 : ℝ) ^ (n + 1) := by
      congr 1
      funext n
      have hexp : (n + M) + 1 = M + (n + 1) := by
        omega
      rw [hexp, pow_add]
    _ = (1 / 2 : ℝ) ^ M * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) := tsum_mul_left
    _ = (1 / 2 : ℝ) ^ M := by rw [hgeom]; ring

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. Convergence in the weighted whole-line local J1 distance
is equivalent to convergence on every finite window. -/
theorem wholeLineLocalJ1Distance_tendsto_iff_window_tendsto
    (x : ℕ → WholeLineCadlag) (f : WholeLineCadlag) :
    Tendsto (fun k => wholeLineLocalJ1Distance (x k) f) atTop (𝓝 0) ↔
      ∀ m, Tendsto (fun k => wholeLineJ1WindowDistance m (x k) f)
        atTop (𝓝 0) := by
  constructor
  · intro h m
    exact wholeLineLocalJ1WindowDistance_tendsto_of_distance_tendsto x f h m
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hpow : Tendsto (fun M : ℕ => (1 / 2 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1
      ((Metric.tendsto_nhds.mp hpow) (ε / 2) (by linarith : 0 < ε / 2)))
    let M : ℕ := max M₀ 1
    have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right M₀ 1)
    have hpowNonneg : 0 ≤ (1 / 2 : ℝ) ^ M := by positivity
    have htailSmall : (1 / 2 : ℝ) ^ M < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hpowNonneg] using
        hM₀ M (le_max_left M₀ 1)
    let δ : ℝ := ε / (2 * (M : ℝ))
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hheadEvent : ∀ᶠ k in atTop, ∀ m ∈ Finset.range M,
        wholeLineLocalJ1Term m (x k) f < δ := by
      exact (Finset.range M).eventually_all.2 fun m hm =>
        (Metric.tendsto_nhds.mp
          (wholeLineLocalJ1Term_tendsto_zero x f h m) δ hδ).mono fun k hk => by
            have hnonneg : 0 ≤ wholeLineLocalJ1Term m (x k) f := by
              change 0 ≤ (1 / 2 : ℝ) ^ (m + 1) *
                min 1 (wholeLineJ1WindowDistance m (x k) f)
              exact mul_nonneg (by positivity)
                (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg m (x k) f))
            simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hk
    filter_upwards [hheadEvent] with k hk
    have hhead : (∑ m ∈ Finset.range M, wholeLineLocalJ1Term m (x k) f) ≤
        ε / 2 := by
      calc
        (∑ m ∈ Finset.range M, wholeLineLocalJ1Term m (x k) f) ≤
            ∑ m ∈ Finset.range M, δ :=
          Finset.sum_le_sum fun m hm => (hk m hm).le
        _ = ε / 2 := by
          simp [δ]
          field_simp
    have htermTail : Summable (fun n : ℕ => wholeLineLocalJ1Term (n + M) (x k) f) :=
      (wholeLineLocalJ1Term_summable (x k) f).comp_injective
      (fun a b hab => Nat.add_right_cancel hab)
    have hweight : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) := by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff (f := fun n : ℕ => (1 / 2 : ℝ) ^ n) 1).mpr
          summable_geometric_two
    have hweightTail : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ ((n + M) + 1)) :=
      hweight.comp_injective (fun a b hab => Nat.add_right_cancel hab)
    have htail :
        (∑' n : ℕ, wholeLineLocalJ1Term (n + M) (x k) f) ≤
          (1 / 2 : ℝ) ^ M := by
      calc
        (∑' n : ℕ, wholeLineLocalJ1Term (n + M) (x k) f) ≤
            ∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + M) + 1) :=
          htermTail.tsum_le_tsum (fun n => by
            change (1 / 2 : ℝ) ^ ((n + M) + 1) *
                min 1 (wholeLineJ1WindowDistance (n + M) (x k) f) ≤
              (1 / 2 : ℝ) ^ ((n + M) + 1)
            calc
              _ ≤ (1 / 2 : ℝ) ^ ((n + M) + 1) * 1 :=
                mul_le_mul_of_nonneg_left (min_le_left 1 _)
                  (by positivity)
              _ = _ := by ring) hweightTail
        _ = (1 / 2 : ℝ) ^ M := wholeLineLocalJ1TailWeight_eq M
    have hsplit :=
      (wholeLineLocalJ1Term_summable (x k) f).sum_add_tsum_nat_add M
    have hsum : wholeLineLocalJ1Distance (x k) f =
        (∑ m ∈ Finset.range M, wholeLineLocalJ1Term m (x k) f) +
          ∑' n : ℕ, wholeLineLocalJ1Term (n + M) (x k) f := by
      unfold wholeLineLocalJ1Distance
      exact hsplit.symm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (wholeLineLocalJ1Distance_nonneg (x k) f)]
    rw [hsum]
    calc
      (∑ m ∈ Finset.range M, wholeLineLocalJ1Term m (x k) f) +
          ∑' n : ℕ, wholeLineLocalJ1Term (n + M) (x k) f ≤
        ε / 2 + (1 / 2 : ℝ) ^ M := add_le_add hhead htail
      _ < ε / 2 + ε / 2 := add_lt_add_right htailSmall _
      _ = ε := by ring

private theorem wholeLineJ1WindowPath_eval (m : ℕ) (f : WholeLineCadlag)
    (t : ℝ) (htlo : -(m : ℝ) ≤ t) (hthi : t ≤ (m : ℝ)) :
    (wholeLineJ1WindowPath m f).1
      ⟨t + ((m : ℝ) + 1), ⟨by linarith, by linarith⟩⟩ = f.1 t := by
  have htabs : |t| ≤ (m : ℝ) := abs_le.mpr ⟨htlo, hthi⟩
  have htime : wholeLineJ1WindowTime m
      ⟨t + ((m : ℝ) + 1), ⟨by linarith, by linarith⟩⟩ = t := by
    dsimp [wholeLineJ1WindowTime]
    ring
  change wholeLineJ1Cutoff m (wholeLineJ1WindowTime m
      ⟨t + ((m : ℝ) + 1), ⟨by linarith, by linarith⟩⟩) *
        f.1 (wholeLineJ1WindowTime m
          ⟨t + ((m : ℝ) + 1), ⟨by linarith, by linarith⟩⟩) = f.1 t
  rw [htime, wholeLineJ1Cutoff_eq_one htabs]
  ring

/-- Helper toward Theorem 1.6 (thm-busemann-conv, whole-line local J1);
not a paper result. The weighted whole-line local J1 distance separates paths. -/
theorem wholeLineLocalJ1Distance_eq_zero_iff (f g : WholeLineCadlag) :
    wholeLineLocalJ1Distance f g = 0 ↔ f = g := by
  constructor
  · intro hzero
    apply Subtype.ext
    funext t
    obtain ⟨m, hm⟩ := exists_nat_gt |t|
    have hbound : |t| ≤ (m : ℝ) := le_of_lt hm
    have hterm : wholeLineLocalJ1Term m f g ≤ wholeLineLocalJ1Distance f g :=
      wholeLineLocalJ1Term_le_distance m f g
    rw [hzero] at hterm
    have hterm0 : wholeLineLocalJ1Term m f g = 0 := by
      apply le_antisymm hterm
      change 0 ≤ (1 / 2 : ℝ) ^ (m + 1) *
        min 1 (wholeLineJ1WindowDistance m f g)
      exact mul_nonneg (by positivity)
        (le_min (by norm_num) (wholeLineJ1WindowDistance_nonneg m f g))
    have hmin : min 1 (wholeLineJ1WindowDistance m f g) = 0 := by
      unfold wholeLineLocalJ1Term at hterm0
      have hw : (1 / 2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hterm0).resolve_left hw
    have hwindow : wholeLineJ1WindowDistance m f g = 0 := by
      by_contra hne
      have hpos : 0 < wholeLineJ1WindowDistance m f g :=
        lt_of_le_of_ne (wholeLineJ1WindowDistance_nonneg m f g) (Ne.symm hne)
      have hminpos : 0 < min 1 (wholeLineJ1WindowDistance m f g) :=
        lt_min (by norm_num) hpos
      rw [hmin] at hminpos
      exact (lt_irrefl 0 hminpos)
    have hpaths :=
      (j1WindowDist_eq_zero_iff (by positivity)
        (wholeLineJ1WindowPath m f) (wholeLineJ1WindowPath m g)).mp hwindow
    have hpoint := congrArg (fun p : CadlagWindow (2 * ((m : ℝ) + 1)) =>
      p.1 ⟨t + ((m : ℝ) + 1), ⟨by linarith [abs_le.mp hbound], by linarith [abs_le.mp hbound]⟩⟩)
        hpaths
    rw [wholeLineJ1WindowPath_eval m f t (le_of_lt (abs_lt.mp hm).1)
        (le_of_lt (abs_lt.mp hm).2),
      wholeLineJ1WindowPath_eval m g t (le_of_lt (abs_lt.mp hm).1)
        (le_of_lt (abs_lt.mp hm).2)] at hpoint
    exact hpoint
  · rintro rfl
    exact wholeLineLocalJ1Distance_self f


end DirectedDistances.Probability
