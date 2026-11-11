/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section5.DiskWalkConv

/-!
# Constant extension for the finite bridge window in Lemma 5.18

This is a correspondence specialization of the universal measurable-extension
clause. The finite walk is extended constantly before time zero and after time `n`.
The probability law and convergence theorem are inherited from the main development.
-/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

/-- The whole centered radius-`N` vector of the finite bridge extended constantly
outside `[0,n]`. Natural subtraction clamps at zero; `min n` clamps at the terminal time.
The initial translation by `(ell,0)` cancels in the centered difference. -/
@[expose] noncomputable def bridgeConstantWindow (n N : ℕ)
    (p : (ℕ → Fin 3) × ℕ) : Fin (2 * N + 1) → ℤ × ℤ :=
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  fun j => codeWalk p.1 (min n (T + j.val - N)) - codeWalk p.1 (min n T)

/-- The exact constant-extension window of Lemma 5.18 is measurable. -/
theorem measurable_bridgeConstantWindow (n N : ℕ) :
    Measurable (bridgeConstantWindow n N) := by
  have hh (K : ℕ) : Measurable (codeFstFirstHit (-(K : ℤ))) := by
    rw [ENat.measurable_iff]
    intro k
    exact codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq _ k)
  apply measurable_from_prod_countable_left
  intro K
  have ht : Measurable (fun ω => (codeFstFirstHit (-(K : ℤ)) ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp (hh K)
  have hmin : Measurable (fun t : ℕ => min n t) := measurable_of_countable _
  apply measurable_pi_iff.mpr
  intro j
  have hw : Measurable (fun z : ℕ × (ℕ → Fin 3) => codeWalk z.2 z.1) :=
    measurable_from_prod_countable_right fun t =>
      (measurable_pi_apply t).comp measurable_codeWalk
  exact (hw.comp ((hmin.comp ((ht.add_const j.val).sub_const N)).prodMk
      measurable_id)).sub
    (hw.comp ((hmin.comp ht).prodMk measurable_id))

/-- Constant extension agrees pointwise with every valid finite bridge window, including all
coordinates at the two endpoints. No conditioning or almost-sure restriction is needed. -/
theorem bridgeConstantWindow_eq_of_some (n N : ℕ)
    (p : (ℕ → Fin 3) × ℕ) (x : Fin (2 * N + 1) → ℤ × ℤ)
    (h : bridgeOptionWindow n N p = some x) : bridgeConstantWindow n N p = x := by
  have hx := bridgeOptionWindow_some_eq h
  have hvalid : codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
      N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
    unfold bridgeOptionWindow at h
    split at h
    · assumption
    · contradiction
  rw [hx]
  funext j
  have ht : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ≤ n := by
    omega
  have hj : j.val ≤ 2 * N := by have := j.isLt; omega
  have hidx : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + j.val - N ≤ n := by
    omega
  simp only [bridgeConstantWindow, bridgeRawWindow, Nat.min_eq_right hidx,
    Nat.min_eq_right ht]

end DirectedDistances.RandomWalk
