/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace DirectedDistances.PlanarMap

variable {a b : ℤ → ℝ}

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Unique half-open strip containing a point. -/
theorem existsUnique_breakpointInterval (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (x : ℝ) : ∃! k : ℤ, a k ≤ x ∧ x < a (k + 1) := by
  obtain ⟨u, hu⟩ := haTop x
  obtain ⟨l, hl⟩ := haBot x
  have hbounded : ∃ u : ℤ, ∀ k : ℤ, a k ≤ x → k ≤ u := by
    refine ⟨u, fun k hk => ?_⟩
    by_contra h
    have hlt := ha (lt_of_not_ge h)
    linarith
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd hbounded ⟨l, hl.le⟩
  have hkNext : x < a (k + 1) := by
    by_contra h
    have hle := hmax (k + 1) (le_of_not_gt h)
    omega
  refine ⟨k, ⟨hk, hkNext⟩, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    have hkj : k + 1 ≤ j := by omega
    have hle := ha.monotone hkj
    linarith
  · by_contra h
    have hjk : j + 1 ≤ k := by omega
    have hle := ha.monotone hjk
    linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The selected half-open strip index. -/
@[expose] noncomputable def pwIndex (a : ℤ → ℝ) (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (x : ℝ) : ℤ :=
  Classical.choose (existsUnique_breakpointInterval ha haTop haBot x)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The selected index satisfies the strip inequalities. -/
theorem pwIndex_spec (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (x : ℝ) :
    a (pwIndex a ha haTop haBot x) ≤ x ∧
      x < a (pwIndex a ha haTop haBot x + 1) :=
  (Classical.choose_spec (existsUnique_breakpointInterval ha haTop haBot x)).1

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Affine formula on one strip. -/
@[expose] noncomputable def pwAffine (a b : ℤ → ℝ) (k : ℤ) (x : ℝ) : ℝ :=
  b k + (b (k + 1) - b k) / (a (k + 1) - a k) * (x - a k)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The slope on each strip is positive. -/
theorem pwAffine_slope_pos (ha : StrictMono a) (hb : StrictMono b) (k : ℤ) :
    0 < (b (k + 1) - b k) / (a (k + 1) - a k) :=
  div_pos (sub_pos.mpr (hb (by omega))) (sub_pos.mpr (ha (by omega)))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The left endpoint value. -/
theorem pwAffine_left (a b : ℤ → ℝ) (k : ℤ) : pwAffine a b k (a k) = b k := by
  simp only [pwAffine, sub_self, mul_zero, add_zero]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The right endpoint value. -/
theorem pwAffine_right (ha : StrictMono a) (b : ℤ → ℝ) (k : ℤ) :
    pwAffine a b k (a (k + 1)) = b (k + 1) := by
  have hne : a (k + 1) - a k ≠ 0 := ne_of_gt (sub_pos.mpr (ha (by omega)))
  unfold pwAffine
  rw [div_mul_cancel₀ _ hne]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Strict monotonicity of the affine formula. -/
theorem pwAffine_strictMono (ha : StrictMono a) (hb : StrictMono b) (k : ℤ) :
    StrictMono (pwAffine a b k) := by
  intro x y hxy
  unfold pwAffine
  have h := mul_lt_mul_of_pos_left (sub_lt_sub_right hxy (a k))
    (pwAffine_slope_pos ha hb k)
  linarith only [h]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Interpolation using the unique half-open strip. -/
@[expose] noncomputable def pwInterp (a b : ℤ → ℝ) (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (x : ℝ) : ℝ :=
  pwAffine a b (pwIndex a ha haTop haBot x) x

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result.
Interpolation agrees with the affine formula on a half-open strip. -/
theorem pwInterp_eq_of_mem_Ico (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    {k : ℤ} {x : ℝ} (hx : a k ≤ x ∧ x < a (k + 1)) :
    pwInterp a b ha haTop haBot x = pwAffine a b k x := by
  have heq := (existsUnique_breakpointInterval ha haTop haBot x).unique
    (pwIndex_spec ha haTop haBot x) hx
  unfold pwInterp
  rw [heq]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Interpolation matches every breakpoint. -/
theorem pwInterp_breakpoint (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (k : ℤ) : pwInterp a b ha haTop haBot (a k) = b k := by
  rw [pwInterp_eq_of_mem_Ico ha haTop haBot ⟨le_rfl, ha (by omega)⟩]
  exact pwAffine_left a b k

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result.
Affine formula on the closed strip, including its right endpoint. -/
theorem pwInterp_eq_of_mem_Icc (ha : StrictMono a)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    {k : ℤ} {x : ℝ} (hx : a k ≤ x ∧ x ≤ a (k + 1)) :
    pwInterp a b ha haTop haBot x =
      b k + (b (k + 1) - b k) / (a (k + 1) - a k) * (x - a k) := by
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · exact pwInterp_eq_of_mem_Ico ha haTop haBot ⟨hx.1, hlt⟩
  · rw [pwInterp_breakpoint ha haTop haBot]
    exact (pwAffine_right ha b k).symm

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result.
Interpolation maps a half-open strip into the corresponding strip. -/
theorem pwInterp_mem_Ico (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    {k : ℤ} {x : ℝ} (hx : a k ≤ x ∧ x < a (k + 1)) :
    b k ≤ pwInterp a b ha haTop haBot x ∧
      pwInterp a b ha haTop haBot x < b (k + 1) := by
  rw [pwInterp_eq_of_mem_Ico ha haTop haBot hx]
  constructor
  · simpa only [pwAffine_left] using (pwAffine_strictMono ha hb k).monotone hx.1
  · simpa only [pwAffine_right ha b k] using (pwAffine_strictMono ha hb k) hx.2

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Strict monotonicity across all strips. -/
theorem pwInterp_strictMono (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M) :
    StrictMono (pwInterp a b ha haTop haBot) := by
  intro x y hxy
  let j := pwIndex a ha haTop haBot x
  let k := pwIndex a ha haTop haBot y
  have hx : a j ≤ x ∧ x < a (j + 1) := pwIndex_spec ha haTop haBot x
  have hy : a k ≤ y ∧ y < a (k + 1) := pwIndex_spec ha haTop haBot y
  have hjk : j ≤ k := by
    by_contra h
    have hle : k + 1 ≤ j := by omega
    have hmono := ha.monotone hle
    linarith
  rcases eq_or_lt_of_le hjk with heq | hlt
  · rw [pwInterp_eq_of_mem_Ico ha haTop haBot hx,
      pwInterp_eq_of_mem_Ico ha haTop haBot hy, heq]
    exact pwAffine_strictMono ha hb k hxy
  · have hle : j + 1 ≤ k := by omega
    exact lt_of_lt_of_le (pwInterp_mem_Ico ha hb haTop haBot hx).2
      ((hb.monotone hle).trans (pwInterp_mem_Ico ha hb haTop haBot hy).1)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. Swapping the breakpoint sequences gives the inverse. -/
theorem pwInterp_inverse (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M)
    (x : ℝ) :
    pwInterp b a hb hbTop hbBot (pwInterp a b ha haTop haBot x) = x := by
  let k := pwIndex a ha haTop haBot x
  have hx : a k ≤ x ∧ x < a (k + 1) := pwIndex_spec ha haTop haBot x
  have hy := pwInterp_mem_Ico ha hb haTop haBot hx
  rw [pwInterp_eq_of_mem_Ico hb hbTop hbBot hy,
    pwInterp_eq_of_mem_Ico ha haTop haBot hx]
  have hneA : a (k + 1) - a k ≠ 0 := ne_of_gt (sub_pos.mpr (ha (by omega)))
  have hneB : b (k + 1) - b k ≠ 0 := ne_of_gt (sub_pos.mpr (hb (by omega)))
  unfold pwAffine
  field_simp [hneA, hneB]; ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The interpolation is bijective. -/
theorem pwInterp_bijective (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M) :
    Function.Bijective (pwInterp a b ha haTop haBot) := by
  refine ⟨(pwInterp_strictMono ha hb haTop haBot).injective, ?_⟩
  intro y
  exact ⟨pwInterp b a hb hbTop hbBot y,
    pwInterp_inverse hb ha hbTop hbBot haTop haBot y⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The interpolation is continuous. -/
theorem pwInterp_continuous (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M) :
    Continuous (pwInterp a b ha haTop haBot) :=
  (pwInterp_strictMono ha hb haTop haBot).monotone.continuous_of_surjective
    (pwInterp_bijective ha hb haTop haBot hbTop hbBot).surjective

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result. The interpolation as an order isomorphism. -/
@[expose] noncomputable def pwInterpOrderIso (a b : ℤ → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M) :
    ℝ ≃o ℝ where
  toFun := pwInterp a b ha haTop haBot
  invFun := pwInterp b a hb hbTop hbBot
  left_inv := pwInterp_inverse ha hb haTop haBot hbTop hbBot
  right_inv := pwInterp_inverse hb ha hbTop hbBot haTop haBot
  map_rel_iff' := (pwInterp_strictMono ha hb haTop haBot).le_iff_le

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result.
The order isomorphism has the specified affine formula on closed strips. -/
theorem pwInterpOrderIso_eq_of_mem_Icc (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M)
    {k : ℤ} {x : ℝ} (hx : a k ≤ x ∧ x ≤ a (k + 1)) :
    pwInterpOrderIso a b ha hb haTop haBot hbTop hbBot x =
      b k + (b (k + 1) - b k) / (a (k + 1) - a k) * (x - a k) :=
  pwInterp_eq_of_mem_Icc ha haTop haBot hx

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: piecewise-linear matching of seam
breakpoints); not a paper result.
The inverse order isomorphism is interpolation with swapped sequences. -/
theorem pwInterpOrderIso_symm_apply (ha : StrictMono a) (hb : StrictMono b)
    (haTop : ∀ M : ℝ, ∃ k, M < a k) (haBot : ∀ M : ℝ, ∃ k, a k < M)
    (hbTop : ∀ M : ℝ, ∃ k, M < b k) (hbBot : ∀ M : ℝ, ∃ k, b k < M)
    (x : ℝ) :
    (pwInterpOrderIso a b ha hb haTop haBot hbTop hbBot).symm x =
      pwInterp b a hb hbTop hbBot x := rfl

end DirectedDistances.PlanarMap
