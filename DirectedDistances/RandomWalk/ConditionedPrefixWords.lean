/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyPathLaw

/-! # Actual legal prefix words

Deterministic support for Lemma 4.10's finite conditioned barrier calculation,
Every nonnegative lazy prefix started at x has exactly one word of the actual
three increments. This is a bijection statement, not a probability assumption. -/

public section
namespace DirectedDistances.RandomWalk

/-- Integrating the actual lazy increment word is injective. -/
theorem lazyWordValues_injective {n : ℕ} :
    Function.Injective (@lazyWordValues n) := by
  intro w v h
  have hp : lazyPathOfWord w = lazyPathOfWord v := Subtype.ext h
  have hh := congrArg (@lazyPathWord n) hp
  simpa only [lazyPathWord_ofWord] using hh

/-- Adding the actual initial height preserves injectivity of word integration. -/
theorem shifted_lazyWordValues_injective {n : ℕ} (x : ℤ) :
    Function.Injective (fun w : Fin n → Fin 3 =>
      fun j : Fin (n + 1) => x + lazyWordValues w j) := by
  intro w v h
  apply lazyWordValues_injective
  funext j
  exact add_left_cancel (congrFun h j)

/-- Every legal nonnegative finite prefix started at x is represented by exactly
one actual lazy word. All path obligations are proved before invoking the
existing inverse increment-word map. -/
theorem existsUnique_lazyWord_of_natPrefix {n : ℕ} (x : ℕ)
    (q : Fin (n + 1) → ℕ) (h0 : q 0 = x)
    (hstep : ∀ i : Fin n, |(q i.succ : ℤ) - (q i.castSucc : ℤ)| ≤ 1) :
    ∃! w : Fin n → Fin 3,
      ∀ j : Fin (n + 1), (q j : ℤ) = (x : ℤ) + lazyWordValues w j := by
  let p : LazyPath n := ⟨fun j => (q j : ℤ) - (x : ℤ), by simp only [h0, sub_self], by
    intro i
    apply lazy_increment_iff.mpr
    have hi := (abs_le.mp (hstep i))
    constructor <;> dsimp only <;> omega⟩
  refine ⟨lazyPathWord p, ?_, ?_⟩
  · intro j
    have hp := congrArg (fun r : LazyPath n => r.val j) (lazyPathOfWord_word p)
    change lazyWordValues (lazyPathWord p) j = (q j : ℤ) - (x : ℤ) at hp
    omega
  · intro w hw
    apply shifted_lazyWordValues_injective (x : ℤ)
    funext j
    have hp := congrArg (fun r : LazyPath n => r.val j) (lazyPathOfWord_word p)
    change lazyWordValues (lazyPathWord p) j = (q j : ℤ) - (x : ℤ) at hp
    have hh := hw j
    change (x : ℤ) + lazyWordValues w j = (x : ℤ) + lazyWordValues (lazyPathWord p) j
    omega

end DirectedDistances.RandomWalk
