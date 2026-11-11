/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.ScaledPartialSumWindow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section
namespace DirectedDistances.Probability

open MeasureTheory

/-- Helper toward E-STABLE / Theorem 1.6
which is Polish by `SkorokhodJ1WindowSeparableSpace`; not the paper result. -/
noncomputable instance j1WindowDMeasurableSpace {T : ℝ} (hT : 0 < T) :
    MeasurableSpace (J1WindowD T hT) := borel _

/-- Helper toward E-STABLE / Theorem 1.6
σ-algebra as measurable sets; not the paper result. -/
noncomputable instance j1WindowDBorelSpace {T : ℝ} (hT : 0 < T) :
    BorelSpace (J1WindowD T hT) := ⟨rfl⟩

/-- Helper toward E-STABLE / Theorem 1.6
the time window; not the paper result. -/
noncomputable def j1WindowIndexBound (n : ℕ) (T : ℝ) : ℕ :=
  ⌊((n + 1 : ℕ) : ℝ) * T⌋₊

/-- Helper toward E-STABLE / Theorem 1.6
zero outside the possible floor indices; not the paper result. -/
noncomputable def j1WindowVectorIncrement {T : ℝ} (n : ℕ)
    (v : Fin (j1WindowIndexBound n T + 1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j ≤ j1WindowIndexBound n T then
    v ⟨j, Nat.lt_succ_of_le hj⟩
  else 0

/-- Helper toward E-STABLE / Theorem 1.6
many increment values; indices beyond `floor ((n + 1) * T)` are zero, and
not the paper result. -/
noncomputable def scaledPartialSumWindowVector {T : ℝ} (hT : 0 < T)
    (ν : ℝ) (n : ℕ)
    (v : Fin (j1WindowIndexBound n T + 1) → ℝ) : J1WindowD T hT :=
  scaledPartialSumWindow (fun j (_ : Unit) => j1WindowVectorIncrement n v j)
    ν n hT PUnit.unit

private theorem j1WindowScaledFloor_le {T : ℝ} (_hT : 0 < T) (n : ℕ)
    (t : J1Window T) :
    ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ ≤ j1WindowIndexBound n T := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left t.property.2 (by positivity)

private theorem j1WindowScaledFloor_intCast {T : ℝ} (_hT : 0 < T)
    (n : ℕ) (t : J1Window T) :
    (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℤ) =
      ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ := by
  apply Int.natCast_floor_eq_floor
  exact mul_nonneg (by positivity) t.property.1

private theorem partialSumZ_nat_local (X : ℕ → Ω → ℝ) (ω : Ω)
    (k : ℕ) : partialSumZ X ω (k : ℤ) =
      ∑ j ∈ Finset.range k, X j ω := by
  cases k with
  | zero => simp [partialSumZ]
  | succ k => simp [partialSumZ]

private theorem scaledPartialSumWindowVector_apply {T : ℝ} (hT : 0 < T)
    (ν : ℝ) (n : ℕ) (v : Fin (j1WindowIndexBound n T + 1) → ℝ)
    (t : J1Window T) :
    (scaledPartialSumWindowVector hT ν n v).path.1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        ∑ j ∈ Finset.range
          (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊),
            j1WindowVectorIncrement n v j := by
  change (scaledPartialSumWindow
    (fun j (_ : Unit) => j1WindowVectorIncrement n v j) ν n hT PUnit.unit
      ).path.1 t = _
  rw [scaledPartialSumWindow_apply,
    ← j1WindowScaledFloor_intCast hT n t, partialSumZ_nat_local]

private theorem j1WindowVectorCoordinate_dist {T : ℝ} (n : ℕ)
    (v w : Fin (j1WindowIndexBound n T + 1) → ℝ) {j : ℕ}
    (hj : j ≤ j1WindowIndexBound n T) :
    |j1WindowVectorIncrement n v j - j1WindowVectorIncrement n w j| ≤
      dist v w := by
  let i : Fin (j1WindowIndexBound n T + 1) :=
    ⟨j, Nat.lt_succ_of_le hj⟩
  have h := dist_le_pi_dist v w i
  simpa [j1WindowVectorIncrement, hj, i, Real.dist_eq] using h

private theorem j1WindowD_ext {T : ℝ} {hT : 0 < T}
    {x y : J1WindowD T hT} (h : x.path = y.path) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Helper toward E-STABLE / Theorem 1.6
Lipschitz from the sup metric to the J1 metric, using the identity time
change; not the paper result. -/
theorem scaledPartialSumWindowVector_lipschitzWith {T : ℝ}
    (hT : 0 < T) (ν : ℝ) (n : ℕ) :
    LipschitzWith
      ⟨((j1WindowIndexBound n T + 1 : ℕ) : ℝ) *
        |((n + 1 : ℕ) : ℝ) ^ (-(1 / ν))|, by positivity⟩
      (scaledPartialSumWindowVector hT ν n) := by
  let K := j1WindowIndexBound n T
  let a : ℝ := ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν))
  let C : ℝ := ((K + 1 : ℕ) : ℝ) * |a|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let L : NNReal := ⟨C, hC⟩
  change LipschitzWith L (scaledPartialSumWindowVector hT ν n)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change j1WindowDist hT (scaledPartialSumWindowVector hT ν n v).path
      (scaledPartialSumWindowVector hT ν n w).path ≤
        (L : ℝ) * dist v w
  rw [show (L : ℝ) = C by rfl]
  have hpoint (t : J1Window T) :
      |(scaledPartialSumWindowVector hT ν n v).path.1 t -
        (scaledPartialSumWindowVector hT ν n w).path.1 t| ≤ C * dist v w := by
    rw [scaledPartialSumWindowVector_apply, scaledPartialSumWindowVector_apply]
    let k := ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊
    have hk : k ≤ K := by
      dsimp [k, K]
      exact j1WindowScaledFloor_le hT n t
    have hsum :
        |(∑ j ∈ Finset.range k, j1WindowVectorIncrement n v j) -
          ∑ j ∈ Finset.range k, j1WindowVectorIncrement n w j| ≤
            ((K + 1 : ℕ) : ℝ) * dist v w := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ j ∈ Finset.range k,
            (j1WindowVectorIncrement n v j -
              j1WindowVectorIncrement n w j)| ≤
              ∑ j ∈ Finset.range k,
                |j1WindowVectorIncrement n v j -
                  j1WindowVectorIncrement n w j| :=
          Finset.abs_sum_le_sum_abs ..
        _ ≤ ∑ j ∈ Finset.range k, dist v w := by
          apply Finset.sum_le_sum
          intro j hj
          apply j1WindowVectorCoordinate_dist
          exact (Nat.le_of_lt (Finset.mem_range.mp hj)).trans hk
        _ = (k : ℝ) * dist v w := by simp
        _ ≤ ((K + 1 : ℕ) : ℝ) * dist v w := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          exact_mod_cast Nat.le_succ_of_le hk
    have habs :
        |a * (∑ j ∈ Finset.range k, j1WindowVectorIncrement n v j) -
          a * (∑ j ∈ Finset.range k, j1WindowVectorIncrement n w j)| ≤
            |a| * (((K + 1 : ℕ) : ℝ) * dist v w) := by
      calc
        _ = |a| * |(∑ j ∈ Finset.range k,
            j1WindowVectorIncrement n v j) -
              ∑ j ∈ Finset.range k, j1WindowVectorIncrement n w j| := by
          rw [← mul_sub, abs_mul]
        _ ≤ |a| * (((K + 1 : ℕ) : ℝ) * dist v w) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg a)
    calc
      _ = |a * (∑ j ∈ Finset.range k, j1WindowVectorIncrement n v j) -
          a * (∑ j ∈ Finset.range k, j1WindowVectorIncrement n w j)| := by
            simp [a, k]
      _ ≤ |a| * (((K + 1 : ℕ) : ℝ) * dist v w) := habs
      _ = C * dist v w := by dsimp [C]; ring
  let : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  have hsup :
      (⨆ t : J1Window T,
        |(scaledPartialSumWindowVector hT ν n v).path.1 t -
          (scaledPartialSumWindowVector hT ν n w).path.1 t|) ≤ C * dist v w :=
    ciSup_le hpoint
  exact (j1WindowDist_le_sup_dist hT
    (scaledPartialSumWindowVector hT ν n v).path
    (scaledPartialSumWindowVector hT ν n w).path).trans hsup

/-- Helper toward E-STABLE / Theorem 1.6
path map follows from its Lipschitz bound; not the paper result. -/
theorem scaledPartialSumWindowVector_continuous {T : ℝ} (hT : 0 < T)
    (ν : ℝ) (n : ℕ) :
    Continuous (scaledPartialSumWindowVector hT ν n) :=
  (scaledPartialSumWindowVector_lipschitzWith hT ν n).continuous

private theorem scaledPartialSumWindow_eq_vector {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) :
    scaledPartialSumWindow X ν n hT ω =
      scaledPartialSumWindowVector hT ν n (fun i => X i.val ω) := by
  apply j1WindowD_ext
  apply Subtype.ext
  funext t
  rw [scaledPartialSumWindow_apply, scaledPartialSumWindowVector_apply]
  let k := ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊
  have hk : k ≤ j1WindowIndexBound n T := by
    dsimp [k]
    exact j1WindowScaledFloor_le hT n t
  have hsum :
      (∑ j ∈ Finset.range k, X j ω) =
        ∑ j ∈ Finset.range k,
          j1WindowVectorIncrement n
            (fun i : Fin (j1WindowIndexBound n T + 1) => X i.val ω) j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjK : j ≤ j1WindowIndexBound n T :=
      (Nat.le_of_lt (Finset.mem_range.mp hj)).trans hk
    simp [j1WindowVectorIncrement, hjK]
  rw [← j1WindowScaledFloor_intCast hT n t, partialSumZ_nat_local]
  exact congrArg (fun x : ℝ => ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) * x) hsum

/-- Helper toward E-STABLE / Theorem 1.6
path from measurable increments; not the paper result. -/
theorem measurable_scaledPartialSumWindow {Ω : Type*}
    [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (ν : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) :
    Measurable (fun ω => scaledPartialSumWindow X ν n hT ω) := by
  let v : Ω → Fin (j1WindowIndexBound n T + 1) → ℝ :=
    fun ω i => X i.val ω
  have hv : Measurable v := by
    apply measurable_pi_iff.mpr
    intro i
    exact hX i.val
  have heq : (fun ω => scaledPartialSumWindow X ν n hT ω) =
      fun ω => scaledPartialSumWindowVector hT ν n (v ω) := by
    funext ω
    exact scaledPartialSumWindow_eq_vector X ν n hT ω
  rw [heq]
  exact (scaledPartialSumWindowVector_continuous hT ν n).measurable.comp hv

/-- Helper toward E-STABLE / Theorem 1.6
random window path; not the paper result. -/
theorem aemeasurable_scaledPartialSumWindow {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (ν : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) :
    AEMeasurable (fun ω => scaledPartialSumWindow X ν n hT ω) μ :=
  (measurable_scaledPartialSumWindow X hX ν n hT).aemeasurable

end DirectedDistances.Probability
