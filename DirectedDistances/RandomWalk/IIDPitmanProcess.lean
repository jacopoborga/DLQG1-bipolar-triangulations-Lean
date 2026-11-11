/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyWalkConditioning
public import DirectedDistances.RandomWalk.PitmanPrefixCompatibility

/-! Supporting lemmas for paper labels `lem-lazy-walk-flip` (see CORRESPONDENCE.md). -/











public section
namespace DirectedDistances.RandomWalk
open MeasureTheory

/-- The proof Wn zero-start global walk integrating the supplied step codes;
no probability law is encoded, and the statement's unspecified start is not modeled. -/
@[expose] def globalIIDLazyWalk {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω)
    (j : ℕ) : ℤ := ∑ i ∈ Finset.range j, (((ξ i ω).val : ℤ) - 1)

@[simp] theorem globalIIDLazyWalk_zero {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω) :
    globalIIDLazyWalk ξ ω 0 = 0 := by
  simp only [globalIIDLazyWalk, Finset.range_zero, Finset.sum_empty]

/-- The global walk has exactly the supplied actual step at every time. -/
theorem globalIIDLazyWalk_step {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω) (j : ℕ) :
    globalIIDLazyWalk ξ ω (j + 1) - globalIIDLazyWalk ξ ω j = ((ξ j ω).val : ℤ) - 1 := by
  unfold globalIIDLazyWalk
  rw [Finset.sum_range_succ]
  omega

/-- Code zero is the integer step minus one, without arithmetic in Fin 3. -/
theorem globalIIDLazyWalk_step_zero {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω)
    (j : ℕ) (hzero : ξ j ω = 0) :
    globalIIDLazyWalk ξ ω (j + 1) - globalIIDLazyWalk ξ ω j = -1 := by
  rw [globalIIDLazyWalk_step, hzero]
  rfl

/-- The literal global walk is characterized by its actual start and increments. -/
theorem globalIIDLazyWalk_unique {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω)
    (p : ℕ → ℤ) (hp₀ : p 0 = 0)
    (hstep : ∀ j : ℕ, p (j + 1) - p j = ((ξ j ω).val : ℤ) - 1) :
    p = globalIIDLazyWalk ξ ω := by
  funext j
  induction j with
  | zero => exact hp₀
  | succ j ih =>
      have h₁ := hstep j
      have h₂ := globalIIDLazyWalk_step ξ ω j
      omega

/-- The actual finite integrated word is a restriction of that same global walk. -/
theorem lazyIIDPrefix_apply {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (n : ℕ)
    (ω : Ω) (j : Fin (n + 1)) :
    (lazyIIDPrefix ξ n ω).val j = globalIIDLazyWalk ξ ω j.val := by
  induction j using Fin.induction with
  | zero => exact lazyWordValues_zero (fun i : Fin n => ξ (i : ℕ) ω)
  | succ i ih =>
      have h := lazyWordValues_step (fun i : Fin n => ξ (i : ℕ) ω) i
      change (lazyIIDPrefix ξ n ω).val i.succ - (lazyIIDPrefix ξ n ω).val i.castSucc =
        ((ξ (i : ℕ) ω).val : ℤ) - 1 at h
      change (lazyIIDPrefix ξ n ω).val i.castSucc =
        ∑ k ∈ Finset.range i.val, (((ξ k ω).val : ℤ) - 1) at ih
      change (lazyIIDPrefix ξ n ω).val i.succ =
        ∑ k ∈ Finset.range (i.val + 1), (((ξ k ω).val : ℤ) - 1)
      rw [Finset.sum_range_succ]
      omega

/-- Every actual transformed prefix is the restriction of the literal global
Pitman transform of the same actual zero-start walk. -/
theorem pitmanIIDPrefix_apply_global {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (n : ℕ)
    (ω : Ω) (j : Fin (n + 1)) :
    (pitmanIIDPrefix ξ n ω).val j = globalLazyPhi (globalIIDLazyWalk ξ ω) j.val := by
  have he : (lazyIIDPrefix ξ n ω).val =
      fun k : Fin (n + 1) => globalIIDLazyWalk ξ ω k.val :=
    funext (lazyIIDPrefix_apply ξ n ω)
  change lazyPhiValues (lazyIIDPrefix ξ n ω).val j = _
  rw [he]
  exact lazyPhiValues_prefix_eq_global _ n j

/-- Actual transformed prefixes agree on every common time coordinate;
no consistency hypothesis is imposed on the family of finite laws. -/
theorem pitmanIIDPrefix_consistent {Ω : Type*} (ξ : ℕ → Ω → Fin 3)
    (n m : ℕ) (ω : Ω) (i : Fin (n + 1)) (j : Fin (m + 1)) (hij : i.val = j.val) :
    (pitmanIIDPrefix ξ n ω).val i = (pitmanIIDPrefix ξ m ω).val j := by
  rw [pitmanIIDPrefix_apply_global, pitmanIIDPrefix_apply_global, hij]

/-- The actual integrated global walk is measurable for the product path sigma algebra. -/
theorem measurable_globalIIDLazyWalk {Ω : Type*} [MeasurableSpace Ω]
    {ξ : ℕ → Ω → Fin 3} (hξ : ∀ i, Measurable (ξ i)) :
    Measurable (globalIIDLazyWalk ξ) := by
  apply Measurable.of_eval
  intro j
  have he : Measurable (fun p : LazyPath j => p.val (Fin.last j)) := measurable_of_countable _
  have h := he.comp (measurable_lazyIIDPrefix hξ j)
  simpa only [Function.comp_def, lazyIIDPrefix_apply, Fin.val_last] using h

/-- The actual globally transformed zero-start walk is also product-measurable. -/
theorem measurable_globalIIDLazyPhi {Ω : Type*} [MeasurableSpace Ω]
    {ξ : ℕ → Ω → Fin 3} (hξ : ∀ i, Measurable (ξ i)) :
    Measurable (fun ω => globalLazyPhi (globalIIDLazyWalk ξ ω)) :=
  measurable_globalLazyPhi.comp (measurable_globalIIDLazyWalk hξ)

end DirectedDistances.RandomWalk
