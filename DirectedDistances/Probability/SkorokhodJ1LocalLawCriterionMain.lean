/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1LocalLawCriterion

import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite-coordinate approximation for local J1 laws

Helpers toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter MeasureTheory
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result.
Paper label: `thm-busemann-conv`.
The local J1 distance splits into a finite prefix and its remaining series; -/
theorem j1LocalDist_eq_finite_prefix_add_tail (N : ℕ) (x y : CadlagLocal) :
    j1LocalDist x y =
      (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) +
        ∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n x y := by
  unfold j1LocalDist
  exact (localJ1Term_summable x y).sum_add_tsum_compl
    (s := Finset.range (N + 1)) |>.symm

/-- Helper toward Theorem 1.6; not a paper result.
Paper label: `thm-busemann-conv`.
McShane inf-convolution gives a bounded Lipschitz approximation through a
finite-coordinate map when its induced distance approximates the source metric; -/
theorem exists_bounded_lipschitz_finite_map_approximation
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [Nonempty X]
    (f : X → ℝ) (Φ : X → Y) (D : Y → Y → ℝ)
    (L ε B : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hfBound : ∀ x, |f x| ≤ B)
    (hfLip : ∀ x y, f x ≤ f y + L * dist x y)
    (hDnonneg : ∀ y z, 0 ≤ D y z)
    (hDself : ∀ y, D y y = 0)
    (hDtri : ∀ y z w, D y w ≤ D y z + D z w)
    (hDle : ∀ y z, D y z ≤ dist y z)
    (hDbounded : ∀ y z, D y z ≤ 1)
    (hApprox : ∀ x y, dist x y ≤ D (Φ x) (Φ y) + ε) :
    ∃ g : Y → ℝ, LipschitzWith (Real.toNNReal L) g ∧
      (∀ y, |g y| ≤ B + L) ∧ ∀ x, |f x - g (Φ x)| ≤ L * ε := by
  classical
  let g : Y → ℝ := fun y => ⨅ x, f x + L * D y (Φ x)
  have hbdd : ∀ y, BddBelow (Set.range fun x => f x + L * D y (Φ x)) := by
    intro y
    refine ⟨-B, ?_⟩
    rintro r ⟨x, rfl⟩
    have hfx : -B ≤ f x := (abs_le.mp (hfBound x)).1
    have hterm : 0 ≤ L * D y (Φ x) := mul_nonneg hL (hDnonneg y (Φ x))
    linarith
  have hglo (y : Y) : -B ≤ g y := by
    apply le_ciInf
    intro x
    have hfx : -B ≤ f x := (abs_le.mp (hfBound x)).1
    have hterm : 0 ≤ L * D y (Φ x) := mul_nonneg hL (hDnonneg y (Φ x))
    linarith
  have hghi (y : Y) : g y ≤ B + L := by
    rcases ‹Nonempty X› with ⟨x₀⟩
    calc
      g y ≤ f x₀ + L * D y (Φ x₀) := ciInf_le (hbdd y) x₀
      _ ≤ B + L := by
        have hfu : f x₀ ≤ B := (abs_le.mp (hfBound x₀)).2
        have hterm : L * D y (Φ x₀) ≤ L := by
          calc
            L * D y (Φ x₀) ≤ L * 1 := mul_le_mul_of_nonneg_left
              (hDbounded y (Φ x₀)) hL
            _ = L := by ring
        linarith
  have hLipG : LipschitzWith (Real.toNNReal L) g := by
    refine LipschitzWith.of_le_add_mul (Real.toNNReal L) ?_
    intro y z
    rw [Real.toNNReal_of_nonneg hL]
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun x => ?_
    rw [sub_le_iff_le_add]
    have htri : D y (Φ x) ≤ D z (Φ x) + dist y z := by
      calc
        D y (Φ x) ≤ D y z + D z (Φ x) := hDtri y z (Φ x)
        _ ≤ dist y z + D z (Φ x) := by nlinarith [hDle y z]
        _ = D z (Φ x) + dist y z := by ring
    calc
      g y ≤ f x + L * D y (Φ x) := ciInf_le (hbdd y) x
      _ ≤ f x + L * D z (Φ x) + L * dist y z := by
        calc
          f x + L * D y (Φ x) ≤ f x + L * (D z (Φ x) + dist y z) := by
            gcongr
          _ = f x + L * D z (Φ x) + L * dist y z := by ring
  have happroxAbove (x : X) : g (Φ x) ≤ f x := by
    calc
      g (Φ x) ≤ f x + L * D (Φ x) (Φ x) := ciInf_le (hbdd (Φ x)) x
      _ = f x := by rw [hDself]; ring
  have happroxBelow (x : X) : f x - L * ε ≤ g (Φ x) := by
    apply le_ciInf
    intro y
    have hxy := hApprox x y
    have hscaled : L * dist x y ≤ L * (D (Φ x) (Φ y) + ε) :=
      mul_le_mul_of_nonneg_left hxy hL
    have hLipxy := hfLip x y
    nlinarith
  refine ⟨g, hLipG, ?_, ?_⟩
  · intro y
    have hlo := hglo y
    have hhi := hghi y
    rw [abs_le]
    constructor <;> linarith
  · intro x
    rw [abs_le]
    have herror : 0 ≤ L * ε := mul_nonneg hL hε
    constructor <;> linarith [happroxAbove x, happroxBelow x, herror]

/-- Helper toward Theorem 1.6; not a paper result.
The bounded distance on a finite cutoff-window tuple, truncated at one. -/
noncomputable def finiteCutoffWindowTruncDist {N : ℕ}
    (u v : LocalCutoffTuple N) : ℝ :=
  min 1 (dist u v)

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff-window truncated distance is nonnegative. -/
theorem finiteCutoffWindowTruncDist_nonneg {N : ℕ}
    (u v : LocalCutoffTuple N) :
    0 ≤ finiteCutoffWindowTruncDist u v := by
  exact le_min (by norm_num) dist_nonneg

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff-window truncated distance vanishes on the diagonal. -/
theorem finiteCutoffWindowTruncDist_self {N : ℕ} (u : LocalCutoffTuple N) :
    finiteCutoffWindowTruncDist u u = 0 := by
  simp [finiteCutoffWindowTruncDist]

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff-window truncated distance satisfies the triangle inequality. -/
theorem finiteCutoffWindowTruncDist_triangle {N : ℕ}
    (u v w : LocalCutoffTuple N) :
    finiteCutoffWindowTruncDist u w ≤
      finiteCutoffWindowTruncDist u v + finiteCutoffWindowTruncDist v w := by
  unfold finiteCutoffWindowTruncDist
  by_cases huv : dist u v < 1
  · by_cases hvw : dist v w < 1
    · rw [min_eq_right huv.le, min_eq_right hvw.le]
      exact (min_le_right 1 (dist u w)).trans (dist_triangle u v w)
    · rw [min_eq_left (le_of_not_gt hvw)]
      have hleft : min 1 (dist u w) ≤ 1 := min_le_left _ _
      have hnonneg : 0 ≤ min 1 (dist u v) :=
        le_min (by norm_num) dist_nonneg
      linarith
  · rw [min_eq_left (le_of_not_gt huv)]
    have hleft : min 1 (dist u w) ≤ 1 := min_le_left _ _
    have hnonneg : 0 ≤ min 1 (dist v w) :=
      le_min (by norm_num) dist_nonneg
    linarith

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff-window truncated distance is bounded by the Pi distance. -/
theorem finiteCutoffWindowTruncDist_le_dist {N : ℕ}
    (u v : LocalCutoffTuple N) :
    finiteCutoffWindowTruncDist u v ≤ dist u v :=
  min_le_right _ _

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff-window truncated distance is at most one. -/
theorem finiteCutoffWindowTruncDist_le_one {N : ℕ}
    (u v : LocalCutoffTuple N) :
    finiteCutoffWindowTruncDist u v ≤ 1 :=
  min_le_left _ _

/-- Helper toward Theorem 1.6; not a paper result.
The finite local J1 prefix is bounded by the truncated distance of its window tuple. -/
theorem finiteCutoffPrefix_le_truncated_window_dist (N : ℕ)
    (x y : CadlagLocal) :
    (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) ≤
      finiteCutoffWindowTruncDist (finiteCutoffWindows N x)
        (finiteCutoffWindows N y) := by
  let d := finiteCutoffWindowTruncDist (finiteCutoffWindows N x)
    (finiteCutoffWindows N y)
  have hd : 0 ≤ d := finiteCutoffWindowTruncDist_nonneg _ _
  have hWeights :
      (∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
    have hsum : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
      convert HasSum.mul_left (1 / 2 : ℝ) hasSum_geometric_two using 1
      · funext n
        rw [pow_succ']
      · norm_num [tsum_geometric_two]
    calc
      (∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (n + 1)) ≤
          ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) :=
        hsum.summable.sum_le_tsum _ (by intro n hn; positivity)
      _ = 1 := hsum.tsum_eq
  have hterm (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      localJ1Term n x y ≤ (1 / 2 : ℝ) ^ (n + 1) * d := by
    have hn' : n < N + 1 := Finset.mem_range.mp hn
    let i : Fin (N + 1) := ⟨n, hn'⟩
    have hcoord := dist_le_pi_dist
      (finiteCutoffWindows N x) (finiteCutoffWindows N y) i
    have hwindow :
        dist (finiteCutoffWindows N x i) (finiteCutoffWindows N y i) ≤
        dist (finiteCutoffWindows N x) (finiteCutoffWindows N y) := by
      exact hcoord
    have hdistcoord :
        dist (finiteCutoffWindows N x i) (finiteCutoffWindows N y i) =
          j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y) := by
      rfl
    have hwindow' := hwindow
    rw [hdistcoord] at hwindow'
    have htrunc :
        min 1 (j1WindowDist (by positivity)
          (cutoffWindow n x) (cutoffWindow n y)) ≤ d := by
      change min 1 (j1WindowDist (by positivity)
        (cutoffWindow n x) (cutoffWindow n y)) ≤
          min 1 (dist (finiteCutoffWindows N x) (finiteCutoffWindows N y))
      exact min_le_min_left 1 hwindow'
    rw [localJ1Term]
    exact mul_le_mul_of_nonneg_left htrunc (by positivity)
  have hprefix :
      (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) ≤ d := by
    calc
      (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) ≤
          ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (n + 1) * d :=
        Finset.sum_le_sum fun n hn => hterm n hn
      _ = (∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (n + 1)) * d := by
        rw [Finset.sum_mul]
      _ ≤ d := by nlinarith [mul_le_mul_of_nonneg_right hWeights hd]
  change (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) ≤ d
  exact hprefix

/-- Helper toward Theorem 1.6; not a paper result.
The local J1 distance is controlled by its finite window tuple and exact tail. -/
theorem j1LocalDist_le_finiteCutoffWindowTruncDist_add_tail (N : ℕ)
    (x y : CadlagLocal) :
    j1LocalDist x y ≤
      finiteCutoffWindowTruncDist (finiteCutoffWindows N x)
        (finiteCutoffWindows N y) +
        ∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y := by
  rw [j1LocalDist_eq_finite_prefix_add_tail]
  calc
    (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) +
        ∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y =
      (∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y) +
        (∑ n ∈ Finset.range (N + 1), localJ1Term n x y) := by ring
    _ ≤ (∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y) +
        finiteCutoffWindowTruncDist (finiteCutoffWindows N x)
          (finiteCutoffWindows N y) :=
      add_le_add_right (finiteCutoffPrefix_le_truncated_window_dist N x y) _
    _ = _ := by ring

end DirectedDistances.Probability
