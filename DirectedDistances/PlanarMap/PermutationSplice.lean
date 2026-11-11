/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Local permutation splices

The insertion operations used for the rotation updates of `sec-kmsw` -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

universe u

variable {D : Type u} [DecidableEq D]

/-- Insert `x` immediately after `a` in the successor table of `σ` by
exchanging the successors of `a` and `x` (`sec-kmsw`, -/
@[expose] def insertAfter (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D :=
  σ * Equiv.swap a x

/-- Insert `x` immediately before `a` in the successor table of `σ` by
exchanging the predecessors of `a` and `x` (`sec-kmsw`, -/
@[expose] def insertBefore (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D :=
  Equiv.swap a x * σ

/-- The successor of `a` after a right swap is `x`'s former successor -/
theorem insertAfter_apply_left (σ : Equiv.Perm D) (a x : D) :
    insertAfter σ a x a = σ x := by
  simp [insertAfter]

/-- The inserted point follows `a` after a right swap -/
theorem insertAfter_apply_right (σ : Equiv.Perm D) (a x : D) :
    insertAfter σ a x x = σ a := by
  simp [insertAfter]

/-- Successors away from the two splice locations are unchanged -/
theorem insertAfter_apply_of_ne (σ : Equiv.Perm D) {a x y : D}
    (hya : y ≠ a) (hyx : y ≠ x) :
    insertAfter σ a x y = σ y := by
  rw [insertAfter, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hya hyx]

/-- If `x` is fixed by `σ`, the new point inserted before `a` points to `a` -/
theorem insertBefore_apply_new (σ : Equiv.Perm D) {a x : D}
    (hx : σ x = x) :
    insertBefore σ a x x = a := by
  simp [insertBefore, hx]

/-- The predecessor of `a` points to the inserted point after a left swap -/
theorem insertBefore_apply_pred (σ : Equiv.Perm D) {a x : D} :
    insertBefore σ a x (σ.symm a) = x := by
  simp [insertBefore, Equiv.Perm.mul_apply]

/-- All other successors remain unchanged when `x` is fixed by `σ` -/
theorem insertBefore_apply_of_ne (σ : Equiv.Perm D) {a x y : D}
    (hx : σ x = x)
    (hyx : y ≠ x) (hypred : y ≠ σ.symm a) :
    insertBefore σ a x y = σ y := by
  have hσya : σ y ≠ a := by
    intro h
    apply hypred
    exact σ.injective (by simpa using h)
  have hσyx : σ y ≠ x := by
    intro h
    apply hyx
    apply σ.injective
    calc
      σ y = x := h
      _ = σ x := hx.symm
  rw [insertBefore, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hσya hσyx]

/-- Extend a permutation by fixing the fresh `none` point. -/
@[expose] def optionExtend (σ : Equiv.Perm D) : Equiv.Perm (Option D) :=
  σ.extendDomain (Equiv.optionIsSomeEquiv D).symm

omit [DecidableEq D] in
/-- The fixed extension leaves the fresh point as a singleton orbit -/
@[simp]
theorem optionExtend_apply_none (σ : Equiv.Perm D) : optionExtend σ none = none := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

omit [DecidableEq D] in
/-- Old successors are unchanged by the fixed extension -/
@[simp]
theorem optionExtend_apply_some (σ : Equiv.Perm D) (x : D) :
    optionExtend σ (some x) = some (σ x) := by
  rw [optionExtend, Equiv.Perm.extendDomain_apply_subtype]
  · simp [Equiv.optionIsSomeEquiv]
  · simp

omit [DecidableEq D] in
/-- Old points have the same orbit relation after adding a fixed `none` -/
theorem optionExtend_sameCycle_some (σ : Equiv.Perm D) (x y : D) :
    (optionExtend σ).SameCycle (some x) (some y) ↔ σ.SameCycle x y := by
  simpa [optionExtend, Equiv.optionIsSomeEquiv] using
    (Equiv.Perm.sameCycle_extendDomain (g := σ)
      (f := (Equiv.optionIsSomeEquiv D).symm) (x := x) (y := y))

private def optionExtendQuotientMap (σ : Equiv.Perm D) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) →
      Quotient (Equiv.Perm.SameCycle.setoid (optionExtend σ)) :=
  Quotient.map some (fun _ _ h => (optionExtend_sameCycle_some σ _ _).2 h)

omit [DecidableEq D] in
private theorem optionExtendQuotientMap_injective (σ : Equiv.Perm D) :
    Function.Injective (optionExtendQuotientMap σ) := by
  intro q r h
  revert h
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  apply Quotient.sound
  apply (optionExtend_sameCycle_some σ x y).1
  exact Quotient.exact (by simpa [optionExtendQuotientMap] using h)

omit [DecidableEq D] in
private theorem optionExtend_none_not_sameCycle (σ : Equiv.Perm D) (x : D) :
    ¬ (optionExtend σ).SameCycle none (some x) := by
  intro h
  have heq := h.eq_of_left (optionExtend_apply_none σ)
  cases heq

omit [DecidableEq D] in
private theorem optionExtendQuotientMap_ne_none (σ : Equiv.Perm D)
    (q : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    optionExtendQuotientMap σ q ≠ Quotient.mk _ none := by
  refine Quotient.inductionOn q ?_
  intro x h
  have hquot : Quotient.mk (Equiv.Perm.SameCycle.setoid (optionExtend σ)) (some x) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid (optionExtend σ)) none := by
    simpa [optionExtendQuotientMap] using h
  have horbit : (optionExtend σ).SameCycle (some x) none := Quotient.exact hquot
  exact optionExtend_none_not_sameCycle σ x horbit.symm

private noncomputable def optionExtendQuotientEquiv (σ : Equiv.Perm D) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕ PUnit.{u + 1} ≃
      Quotient (Equiv.Perm.SameCycle.setoid (optionExtend σ)) := by
  classical
  apply Equiv.ofBijective
    (fun q => match q with
      | Sum.inl c => optionExtendQuotientMap σ c
      | Sum.inr _ => Quotient.mk
          (Equiv.Perm.SameCycle.setoid (optionExtend σ)) none)
  constructor
  · intro q r h
    cases q with
    | inl q =>
      cases r with
      | inl r => exact congrArg Sum.inl (optionExtendQuotientMap_injective σ h)
      | inr u =>
        have h' : optionExtendQuotientMap σ q = Quotient.mk
            (Equiv.Perm.SameCycle.setoid (optionExtend σ)) none := h
        exact False.elim (optionExtendQuotientMap_ne_none σ q h')
    | inr q =>
      cases r with
      | inl r =>
        have h' : optionExtendQuotientMap σ r = Quotient.mk
            (Equiv.Perm.SameCycle.setoid (optionExtend σ)) none := h.symm
        exact False.elim (optionExtendQuotientMap_ne_none σ r h')
      | inr r => rfl
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    cases x with
    | none => exact ⟨Sum.inr PUnit.unit, rfl⟩
    | some x => exact ⟨Sum.inl (Quotient.mk _ x), rfl⟩

noncomputable local instance (f : Equiv.Perm D) [Finite D] :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid f)) := Fintype.ofFinite _

omit [DecidableEq D] in
/-- Extending a permutation by a fixed fresh point adds one orbit -/
theorem optionExtend_orbit_count (σ : Equiv.Perm D) [Fintype D] :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (optionExtend σ))) =
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) + 1 := by
  classical
  calc
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (optionExtend σ))) =
        Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕ PUnit) :=
      Fintype.card_congr (optionExtendQuotientEquiv σ).symm
    _ = Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) + 1 := by simp

/-- Insert the fresh `none` point immediately after `some a` -/
@[expose] def insertAfterFresh (σ : Equiv.Perm D) (a : D) : Equiv.Perm (Option D) :=
  optionExtend σ * Equiv.swap (some a) none

/-- Insert the fresh `none` point immediately before `some a` -/
@[expose] def insertBeforeFresh (σ : Equiv.Perm D) (a : D) : Equiv.Perm (Option D) :=
  Equiv.swap (some a) none * optionExtend σ

/-- The fresh point is the successor of `some a` -/
theorem insertAfterFresh_apply_left (σ : Equiv.Perm D) (a : D) :
    insertAfterFresh σ a (some a) = none := by
  simp [insertAfterFresh]

/-- The fresh point's successor is the former successor of `some a` -/
theorem insertAfterFresh_apply_right (σ : Equiv.Perm D) (a : D) :
    insertAfterFresh σ a none = some (σ a) := by
  simp [insertAfterFresh]

/-- Successors at other old points are unchanged by fresh insertion -/
theorem insertAfterFresh_apply_of_ne (σ : Equiv.Perm D) (a y : D) (hya : y ≠ a) :
    insertAfterFresh σ a (some y) = some (σ y) := by
  rw [insertAfterFresh, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hya) (by simp),
    optionExtend_apply_some]

/-- The fresh point joins the orbit of the point after which it is inserted -/
theorem insertAfterFresh_sameCycle_new (σ : Equiv.Perm D) (a : D) :
    (insertAfterFresh σ a).SameCycle (some a) none := by
  refine ⟨1, ?_⟩
  simp [insertAfterFresh]

private theorem insertAfterFresh_iterate_classify (σ : Equiv.Perm D) (a x : D) :
    ∀ n z, (insertAfterFresh σ a ^ n) (some x) = z →
      (z = none → σ.SameCycle x a) ∧
        ∀ y, z = some y → σ.SameCycle x y := by
  intro n
  induction n with
  | zero =>
    intro z hz
    cases z with
    | none => simp at hz
    | some y =>
      have hxy : x = y := Option.some.inj hz
      subst y
      constructor
      · intro h
        cases h
      · intro y hy
        have : x = y := Option.some.inj hy
        subst y
        exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    intro z hz
    have hz' : insertAfterFresh σ a ((insertAfterFresh σ a ^ n) (some x)) = z := by
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hz
    cases hp : (insertAfterFresh σ a ^ n) (some x) with
    | none =>
      have hval : some (σ a) = z := by
        simpa [hp, insertAfterFresh_apply_right] using hz'
      constructor
      · intro hnone
        exact (ih none hp).1 rfl
      · intro y hy
        have hay : σ a = y := Option.some.inj (hval.trans hy)
        have hxa : σ.SameCycle x a := (ih none hp).1 rfl
        have hstep : σ.SameCycle a (σ a) := ⟨1, rfl⟩
        rw [← hay]
        exact hxa.trans hstep
    | some z₀ =>
      have hclass := ih (some z₀) hp
      by_cases hza : z₀ = a
      · subst z₀
        have hval : none = z := by
          rw [hp, insertAfterFresh_apply_left] at hz'
          exact hz'
        subst z
        constructor
        · intro _
          exact hclass.2 a rfl
        · intro y hy
          have hnone : (none : Option D) = some y := hval.trans hy
          exact False.elim (Option.some_ne_none y hnone.symm)
      · have hval : some (σ z₀) = z := by
          rw [hp, insertAfterFresh_apply_of_ne σ a z₀ hza] at hz'
          exact hz'
        constructor
        · intro hnone
          exact False.elim (Option.some_ne_none _ (hval.trans hnone))
        · intro y hy
          have hzy : σ z₀ = y := Option.some.inj (hval.trans hy)
          have hxz : σ.SameCycle x z₀ := hclass.2 z₀ rfl
          have hstep : σ.SameCycle z₀ (σ z₀) := ⟨1, rfl⟩
          rw [← hzy]
          exact hxz.trans hstep

private theorem insertAfterFresh_sameCycle_pow (σ : Equiv.Perm D) (a x : D) (n : ℕ) :
    (insertAfterFresh σ a).SameCycle (some x) (some ((σ ^ n) x) : Option D) := by
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    have hnext : (insertAfterFresh σ a).SameCycle
        (some ((σ ^ n) x) : Option D) (some (σ ((σ ^ n) x))) := by
      by_cases hxa : (σ ^ n) x = a
      · subst a
        refine ⟨2, ?_⟩
        simp [pow_two, insertAfterFresh]
      · refine ⟨1, ?_⟩
        simpa using insertAfterFresh_apply_of_ne σ a ((σ ^ n) x) hxa
    exact ih.trans (by simpa [pow_succ'] using hnext)

/-- Inserting a fresh point after `a` leaves the orbit relation on old points -/
theorem insertAfterFresh_sameCycle_some_iff (σ : Equiv.Perm D) (a : D) [Fintype D]
    (x y : D) :
    (insertAfterFresh σ a).SameCycle (some x) (some y) ↔ σ.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq'
    exact (insertAfterFresh_iterate_classify σ a x n (some y) hpow).2 y rfl
  · intro h
    obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq'
    have hnew := insertAfterFresh_sameCycle_pow σ a x n
    rw [hpow] at hnew
    exact hnew

private noncomputable def freshOrbitQuotientEquiv (σ : Equiv.Perm D)
    (g : Equiv.Perm (Option D)) (a : D)
    (hold : ∀ x y : D, g.SameCycle (some x) (some y) ↔ σ.SameCycle x y)
    (hfresh : g.SameCycle none (some a)) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid g) := by
  classical
  apply Equiv.ofBijective
    (Quotient.map some (fun x y h => hold x y |>.2 h))
  constructor
  · intro q r h
    revert h
    refine Quotient.inductionOn₂ q r ?_
    intro x y h
    apply Quotient.sound
    exact (hold x y).1 (Quotient.exact (by simpa using h))
  · intro q
    refine Quotient.inductionOn q ?_
    intro d
    cases d with
    | none => exact ⟨Quotient.mk _ a, Quotient.sound hfresh.symm⟩
    | some x => exact ⟨Quotient.mk _ x, rfl⟩

/-- Inserting a fresh point after an old point preserves the number of orbits -/
theorem insertAfterFresh_orbit_count (σ : Equiv.Perm D) (a : D) [Fintype D] :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (insertAfterFresh σ a))) =
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) := by
  classical
  exact Fintype.card_congr
    (freshOrbitQuotientEquiv σ (insertAfterFresh σ a) a
      (fun x y => insertAfterFresh_sameCycle_some_iff σ a x y)
      (insertAfterFresh_sameCycle_new σ a).symm).symm

/-- The fresh point is the successor of `some a` when inserted before it -/
theorem insertBeforeFresh_apply_new (σ : Equiv.Perm D) (a : D) :
    insertBeforeFresh σ a none = some a := by
  simp [insertBeforeFresh]

/-- The fresh point joins the orbit of `some a` when inserted before it -/
theorem insertBeforeFresh_sameCycle_new (σ : Equiv.Perm D) (a : D) :
    (insertBeforeFresh σ a).SameCycle none (some a) := by
  refine ⟨1, ?_⟩
  simp [insertBeforeFresh]

/-- The old predecessor of `some a` points to the fresh point -/
theorem insertBeforeFresh_apply_pred (σ : Equiv.Perm D) (a : D) :
    insertBeforeFresh σ a (some (σ.symm a)) = none := by
  simp [insertBeforeFresh]

/-- Other old successors are unchanged when inserting a fresh point before `a` -/
theorem insertBeforeFresh_apply_of_ne (σ : Equiv.Perm D) {a y : D}
    (hya : y ≠ σ.symm a) :
    insertBeforeFresh σ a (some y) = some (σ y) := by
  have hσya : σ y ≠ a := by
    intro h
    apply hya
    exact σ.injective (by simpa using h)
  rw [insertBeforeFresh, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hσya) (by simp),
    optionExtend_apply_some]

/-- Inserting before a fresh point is inverse to inserting after it under the -/
theorem insertBeforeFresh_eq_inv_insertAfterFresh_inv (σ : Equiv.Perm D) (a : D) :
    insertBeforeFresh σ a = (insertAfterFresh σ⁻¹ a)⁻¹ := by
  simp [insertBeforeFresh, insertAfterFresh, optionExtend,
    Equiv.Perm.extendDomain_inv, mul_inv_rev]

/-- Inserting a fresh point before `a` leaves the orbit relation on old points -/
theorem insertBeforeFresh_sameCycle_some_iff (σ : Equiv.Perm D) (a : D) [Fintype D]
    (x y : D) :
    (insertBeforeFresh σ a).SameCycle (some x) (some y) ↔ σ.SameCycle x y := by
  rw [insertBeforeFresh_eq_inv_insertAfterFresh_inv]
  rw [Equiv.Perm.sameCycle_inv, insertAfterFresh_sameCycle_some_iff]
  exact Equiv.Perm.sameCycle_inv

/-- Inserting a fresh point before an old point preserves the number of orbits -/
theorem insertBeforeFresh_orbit_count (σ : Equiv.Perm D) (a : D) [Fintype D] :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (insertBeforeFresh σ a))) =
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) := by
  classical
  exact Fintype.card_congr
    (freshOrbitQuotientEquiv σ (insertBeforeFresh σ a) a
      (fun x y => insertBeforeFresh_sameCycle_some_iff σ a x y)
      (insertBeforeFresh_sameCycle_new σ a)).symm

end DirectedDistances.PlanarMap
