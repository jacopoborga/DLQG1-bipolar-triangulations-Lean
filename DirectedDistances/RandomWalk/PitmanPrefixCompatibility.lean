/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyPath
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory

/-- The actual minimum of an integer path on the nonempty closed prefix
`{0,...,j}`. This has no empty-set default branch. -/
@[expose] noncomputable def globalLazyRunningMinimum (p : ℕ → ℤ) (j : ℕ) : ℤ :=
  (Finset.range (j + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ p

/-- The source's literal global Pitman formula on every integer path.
At time zero the same formula is used, without imposing a starting value. -/
@[expose] noncomputable def globalLazyPhi (p : ℕ → ℤ) (j : ℕ) : ℤ :=
  p j - 2 * globalLazyRunningMinimum p j

/-- The actual global minimum lies below every coordinate of its prefix. -/
theorem globalLazyRunningMinimum_le (p : ℕ → ℤ) {i j : ℕ} (hij : i ≤ j) :
    globalLazyRunningMinimum p j ≤ p i :=
  Finset.inf'_le p (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))

/-- Any lower bound on the closed prefix bounds its actual minimum. -/
theorem le_globalLazyRunningMinimum (p : ℕ → ℤ) (j : ℕ) {a : ℤ}
    (ha : ∀ i ≤ j, a ≤ p i) : a ≤ globalLazyRunningMinimum p j := by
  apply Finset.le_inf'
  intro i hi
  exact ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- The finite raw minimum is the restriction of the same global minimum,
independently of the longer finite horizon. The case `n=0` is included. -/
theorem runningMinimum_prefix_eq_global (p : ℕ → ℤ) (n : ℕ) (j : Fin (n + 1)) :
    runningMinimum (fun i : Fin (n + 1) => p i.val) j =
      globalLazyRunningMinimum p j.val := by
  apply le_antisymm
  · apply le_globalLazyRunningMinimum
    intro i hi
    have hiN : i < n + 1 := lt_of_le_of_lt hi j.isLt
    exact runningMinimum_le (fun i : Fin (n + 1) => p i.val)
      (i := ⟨i, hiN⟩) (show (⟨i, hiN⟩ : Fin (n + 1)) ≤ j from hi)
  · apply le_runningMinimum
    intro i hi
    exact globalLazyRunningMinimum_le p (show i.val ≤ j.val from hi)

/-- Every finite raw Pitman formula is pathwise the restriction of the actual
global formula, with no prefix-consistency assumption. -/
theorem lazyPhiValues_prefix_eq_global (p : ℕ → ℤ) (n : ℕ) (j : Fin (n + 1)) :
    lazyPhiValues (fun i : Fin (n + 1) => p i.val) j = globalLazyPhi p j.val := by
  rw [lazyPhiValues, globalLazyPhi, runningMinimum_prefix_eq_global]

/-- Each actual finite-prefix minimum is measurable in the product sigma
algebra. It is a countable finite-vector function composed with restriction. -/
theorem measurable_globalLazyRunningMinimum (j : ℕ) :
    Measurable (fun p : ℕ → ℤ => globalLazyRunningMinimum p j) := by
  have hprefix : Measurable (fun p : ℕ → ℤ => fun i : Fin (j + 1) => p i.val) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hmin : Measurable (fun q : Fin (j + 1) → ℤ => runningMinimum q (Fin.last j)) :=
    measurable_of_countable _
  have h := hmin.comp hprefix
  convert h using 1
  funext p
  exact (runningMinimum_prefix_eq_global p j (Fin.last j)).symm

/-- The literal global path transform is measurable for the inherited
natural-index product sigma algebra on integer paths. -/
theorem measurable_globalLazyPhi : Measurable (globalLazyPhi : (ℕ → ℤ) → (ℕ → ℤ)) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply j).sub ((measurable_globalLazyRunningMinimum j).const_mul 2)

/-- The closed time-zero prefix has its actual sole value as minimum. -/
@[simp] theorem globalLazyRunningMinimum_zero (p : ℕ → ℤ) :
    globalLazyRunningMinimum p 0 = p 0 := by
  apply le_antisymm (globalLazyRunningMinimum_le p le_rfl)
  apply le_globalLazyRunningMinimum
  intro i hi
  have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
  rw [hi0]

/-- The formula at zero exposes the missing source start-state condition:
the transform starts at `-p(0)` and has no hidden normalization. -/
@[simp] theorem globalLazyPhi_zero (p : ℕ → ℤ) : globalLazyPhi p 0 = -p 0 := by
  rw [globalLazyPhi, globalLazyRunningMinimum_zero]
  omega

/-- Zero start for the transform is equivalent to zero start for its input. -/
theorem globalLazyPhi_zero_iff (p : ℕ → ℤ) : globalLazyPhi p 0 = 0 ↔ p 0 = 0 := by
  rw [globalLazyPhi_zero, neg_eq_zero]

/-- A pathwise conditional fact: a zero-start path has nonnegative transform.
This is not a law statement and needs no assumption about its steps. -/
theorem globalLazyPhi_nonneg_of_start_zero (p : ℕ → ℤ) (hp : p 0 = 0) (j : ℕ) :
    0 ≤ globalLazyPhi p j := by
  have hm := globalLazyRunningMinimum_le p (i := j) le_rfl
  have hzero := globalLazyRunningMinimum_le p (Nat.zero_le j)
  rw [hp] at hzero
  rw [globalLazyPhi]
  omega

/-- A separate pathwise conditional fact: zero start and legal lazy input
steps give legal lazy transformed steps, using the proved finite-path result.
No law or prefix-consistency premise is used. -/
theorem globalLazyPhi_step_of_legal_steps (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i : ℕ, p (i + 1) - p i ∈ ({-1, 0, 1} : Set ℤ)) (j : ℕ) :
    globalLazyPhi p (j + 1) - globalLazyPhi p j ∈ ({-1, 0, 1} : Set ℤ) := by
  let q : LazyPath (j + 1) := ⟨(fun i => p i.val), hp0,
    fun i => by
      simpa only [Fin.val_succ, Fin.val_castSucc] using hstep i.val⟩
  have h := (lazyPhiValues_isLazyPath q).2 (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
  change lazyPhiValues (fun i : Fin (j + 1 + 1) => p i.val)
      (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)).succ -
    lazyPhiValues (fun i : Fin (j + 1 + 1) => p i.val)
      (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)).castSucc ∈ _ at h
  rw [lazyPhiValues_prefix_eq_global, lazyPhiValues_prefix_eq_global] at h
  exact h

end DirectedDistances.RandomWalk
