/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.List.Count
public import Mathlib.Algebra.Order.Group.Int
meta import Lean.Elab.Tactic.Omega

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/











@[expose] public section
namespace DirectedDistances.KMSW

/-- The three legal increments, retaining their exact signs. -/
inductive Step
  | down
  | left
  | up
  deriving DecidableEq

namespace Step

/-- Horizontal increment. -/
def dx : Step → ℤ
  | down => 1
  | left => -1
  | up => 0

/-- Vertical increment. -/
def dy : Step → ℤ
  | down => -1
  | left => 0
  | up => 1

end Step

/-- Total horizontal displacement of a finite step word. -/
def horizontal : List Step → ℤ
  | [] => 0
  | s :: w => s.dx + horizontal w

/-- Total vertical displacement of a finite step word. -/
def vertical : List Step → ℤ
  | [] => 0
  | s :: w => s.dy + vertical w

/-- Every visited point, including the initial and final points, lies in the
closed nonnegative quadrant. Positions are integers, so subtraction never truncates. -/
def InQuadrantFrom (x y : ℤ) : List Step → Prop
  | [] => 0 ≤ x ∧ 0 ≤ y
  | s :: w => 0 ≤ x ∧ 0 ≤ y ∧ InQuadrantFrom (x + s.dx) (y + s.dy) w

/-- The recursive quadrant predicate is exactly nonnegativity after every prefix,
including the empty prefix and the complete word. -/
theorem inQuadrantFrom_iff_prefix (x y : ℤ) (w : List Step) :
    InQuadrantFrom x y w ↔ ∀ n ≤ w.length,
      0 ≤ x + horizontal (w.take n) ∧ 0 ≤ y + vertical (w.take n) := by
  induction w generalizing x y with
  | nil =>
    constructor
    · intro h n _
      simpa only [List.take_nil, InQuadrantFrom, horizontal, vertical, add_zero] using h
    · intro h
      simpa only [List.take_zero, InQuadrantFrom, horizontal, vertical, add_zero]
        using h 0 (Nat.le_refl 0)
  | cons s w ih =>
    constructor
    · rintro ⟨hx, hy, hw⟩ n hn
      cases n with
      | zero =>
        simpa only [List.take_zero, horizontal, vertical, add_zero] using And.intro hx hy
      | succ n =>
        have hp := (ih (x + s.dx) (y + s.dy)).1 hw n (Nat.le_of_succ_le_succ hn)
        simpa only [List.take_succ_cons, horizontal, vertical, add_assoc] using hp
    · intro h
      have h₀ := h 0 (Nat.zero_le _)
      have hx : 0 ≤ x := by
        simpa only [List.take_zero, horizontal, add_zero] using h₀.1
      have hy : 0 ≤ y := by
        simpa only [List.take_zero, vertical, add_zero] using h₀.2
      refine ⟨hx, hy, (ih (x + s.dx) (y + s.dy)).2 ?_⟩
      intro n hn
      have hp := h (n + 1) (Nat.succ_le_succ hn)
      simpa only [List.take_succ_cons, horizontal, vertical, add_assoc] using hp

/-- In particular, the final point is included in the quadrant constraint. -/
theorem InQuadrantFrom.endpoint_nonnegative {x y : ℤ} {w : List Step}
    (h : InQuadrantFrom x y w) : 0 ≤ x + horizontal w ∧ 0 ≤ y + vertical w := by
  simpa only [List.take_length] using (inQuadrantFrom_iff_prefix x y w).1 h w.length (Nat.le_refl _)

/-- The three step counts partition the word, without any endpoint assumption. -/
theorem length_eq_counts (w : List Step) :
    w.length = w.count .down + w.count .left + w.count .up := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp at * <;> omega

/-- Horizontal displacement is the number of D steps minus the number of L steps. -/
theorem horizontal_eq_counts (w : List Step) :
    horizontal w = (w.count .down : ℤ) - (w.count .left : ℤ) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp [horizontal, Step.dx, ih] <;> omega

/-- Vertical displacement is the number of U steps minus the number of D steps. -/
theorem vertical_eq_counts (w : List Step) :
    vertical w = (w.count .up : ℤ) - (w.count .down : ℤ) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp [vertical, Step.dy, ih] <;> omega

/-- Endpoint equations alone force the exact admissible length. No quadrant or
probability hypothesis is used in this counting direction. -/
theorem length_eq_of_endpoint (ell : ℕ) (w : List Step)
    (hx : horizontal w = -(ell : ℤ)) (hy : vertical w = 0) :
    w.length = ell + 3 * w.count .down := by
  have hh := horizontal_eq_counts w
  have hv := vertical_eq_counts w
  have hl := length_eq_counts w
  omega

/-- Repeated three-step U,D,L excursions from the origin. -/
def excursion : ℕ → List Step
  | 0 => []
  | n + 1 => .up :: .down :: .left :: excursion n

theorem excursion_length (n : ℕ) : (excursion n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [excursion, List.length_cons, ih]; omega

theorem excursion_horizontal (n : ℕ) : horizontal (excursion n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [excursion, horizontal, Step.dx, ih]; omega

theorem excursion_vertical (n : ℕ) : vertical (excursion n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [excursion, vertical, Step.dy, ih]; omega

theorem excursion_inQuadrant (n : ℕ) : InQuadrantFrom 0 0 (excursion n) := by
  induction n with
  | zero => exact ⟨le_refl _, le_refl _⟩
  | succ n ih => simpa [excursion, InQuadrantFrom, Step.dx, Step.dy] using ih

/-- First take `ell` L steps to the origin, then `a` U,D,L excursions. -/
def bridgeWord : ℕ → ℕ → List Step
  | 0, a => excursion a
  | ell + 1, a => .left :: bridgeWord ell a

theorem bridgeWord_length (ell a : ℕ) : (bridgeWord ell a).length = ell + 3 * a := by
  induction ell with
  | zero => simpa only [bridgeWord, Nat.zero_add] using excursion_length a
  | succ ell ih => simp only [bridgeWord, List.length_cons, ih]; omega

theorem bridgeWord_horizontal (ell a : ℕ) : horizontal (bridgeWord ell a) = -(ell : ℤ) := by
  induction ell with
  | zero => exact excursion_horizontal a
  | succ ell ih => simp only [bridgeWord, horizontal, Step.dx, ih]; omega

theorem bridgeWord_vertical (ell a : ℕ) : vertical (bridgeWord ell a) = 0 := by
  induction ell with
  | zero => exact excursion_vertical a
  | succ ell ih => simpa only [bridgeWord, vertical, Step.dy, zero_add] using ih

theorem bridgeWord_inQuadrant (ell a : ℕ) :
    InQuadrantFrom ell 0 (bridgeWord ell a) := by
  induction ell with
  | zero => exact excursion_inQuadrant a
  | succ ell ih =>
    change 0 ≤ ((ell + 1 : ℕ) : ℤ) ∧ 0 ≤ (0 : ℤ) ∧
      InQuadrantFrom (((ell + 1 : ℕ) : ℤ) + -1) (0 + 0) (bridgeWord ell a)
    have hx : ((ell + 1 : ℕ) : ℤ) + -1 = (ell : ℤ) := by omega
    rw [hx, add_zero]
    exact ⟨Int.natCast_nonneg _, le_refl _, ih⟩

/-- Exact feasibility of a closed-quadrant bridge from `(ell,0)` to `(0,0)`.
This includes zero lengths and enforces both nonnegativity and the period three
restriction. It is a deterministic walk theorem, not a conditioned probability bound. -/
theorem exists_quadrant_bridge_iff (ell n : ℕ) :
    (∃ w : List Step, w.length = n ∧ horizontal w = -(ell : ℤ) ∧
      vertical w = 0 ∧ InQuadrantFrom ell 0 w) ↔
      ∃ a : ℕ, n = ell + 3 * a := by
  constructor
  · rintro ⟨w, hn, hx, hy, _⟩
    exact ⟨w.count .down, hn.symm.trans (length_eq_of_endpoint ell w hx hy)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨bridgeWord ell a, bridgeWord_length ell a, bridgeWord_horizontal ell a,
      bridgeWord_vertical ell a, bridgeWord_inQuadrant ell a⟩

/-- In particular, there is no legal one-step excursion from the origin. -/
theorem no_one_step_quadrant_bridge :
    ¬ ∃ w : List Step, w.length = 1 ∧ horizontal w = 0 ∧
      vertical w = 0 ∧ InQuadrantFrom 0 0 w := by
  intro h
  obtain ⟨a, ha⟩ := (exists_quadrant_bridge_iff 0 1).1 h
  omega

end DirectedDistances.KMSW
