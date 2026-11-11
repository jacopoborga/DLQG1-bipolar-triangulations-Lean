/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Closed-quadrant return counts

The exact closed-quadrant return count used as combinatorial input toward the -/

public section
namespace DirectedDistances.RandomWalk

/-- Number of length-`n` walks from `(x,y)` to `(0,0)` that stay in the closed
quadrant, with steps `(1,-1)`, `(-1,0)`, and `(0,1)`. This is combinatorial
input toward the corrected `lem-cone-prob-lower` claim -/
@[expose] def quadrantReturnCount : ℕ → ℕ → ℕ → ℕ
  | 0, x, y => if x = 0 ∧ y = 0 then 1 else 0
  | n + 1, x, y =>
      (if 0 < x then quadrantReturnCount n (x - 1) y else 0) +
        quadrantReturnCount n x (y + 1) +
          (if 0 < y then quadrantReturnCount n (x + 1) (y - 1) else 0)

private theorem quadrantReturnCount_support (n x y : ℕ)
    (hpos : 0 < quadrantReturnCount n x y) : ∃ r, n = 3 * r + x + 2 * y := by
  induction n generalizing x y with
  | zero =>
      simp only [quadrantReturnCount] at hpos
      split_ifs at hpos with hxy
      · rcases hxy with ⟨rfl, rfl⟩
        exact ⟨0, rfl⟩
      · omega
  | succ n ih =>
      have hterms :
          (0 < (if 0 < x then quadrantReturnCount n (x - 1) y else 0) ∨
            0 < quadrantReturnCount n x (y + 1)) ∨
              0 < (if 0 < y then quadrantReturnCount n (x + 1) (y - 1) else 0) := by
        simpa [quadrantReturnCount] using hpos
      rcases hterms with (hleft | hmid) | hright
      · have hx : 0 < x := by
          by_contra hn
          simp [hn] at hleft
        have hc : 0 < quadrantReturnCount n (x - 1) y := by simpa [hx] using hleft
        obtain ⟨r, hr⟩ := ih (x - 1) y hc
        exact ⟨r, by omega⟩
      · obtain ⟨r, hr⟩ := ih x (y + 1) hmid
        exact ⟨r + 1, by omega⟩
      · have hy : 0 < y := by
          by_contra hn
          simp [hn] at hright
        have hc : 0 < quadrantReturnCount n (x + 1) (y - 1) := by simpa [hy] using hright
        obtain ⟨r, hr⟩ := ih (x + 1) (y - 1) hc
        exact ⟨r, by omega⟩

/-- A return is possible only at an admissible length: `n = 3*r + x + 2*y`.
This support restriction is a combinatorial input toward the corrected -/
theorem quadrantReturnCount_eq_zero (n x y : ℕ)
    (h : ¬ ∃ r, n = 3 * r + x + 2 * y) : quadrantReturnCount n x y = 0 := by
  by_contra hnz
  have hpos : 0 < quadrantReturnCount n x y := Nat.pos_of_ne_zero hnz
  exact h (quadrantReturnCount_support n x y hpos)

private theorem quadrantReturnCount_closedForm_aux :
    ∀ n r x y, n = 3 * r + x + 2 * y →
      quadrantReturnCount n x y *
          ((r + x + y + 2).factorial * (r + y + 1).factorial * r.factorial) =
        n.factorial * ((x + 1) * (y + 1) * (x + y + 2)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro r x y hn
      subst n
      by_cases hN : 0 < 3 * r + x + 2 * y
      · let m : ℕ := 3 * r + x + 2 * y - 1
        have hs : m + 1 = 3 * r + x + 2 * y := by
          dsimp [m]
          omega
        have hm_lt : m < 3 * r + x + 2 * y := by
          dsimp [m]
          omega
        let D : ℕ := (r + x + y + 2).factorial * (r + y + 1).factorial * r.factorial
        have hfacA : (r + x + y + 2).factorial =
            (r + x + y + 2) * (r + x + y + 1).factorial := by
          simpa [Nat.add_assoc] using Nat.factorial_succ (r + x + y + 1)
        have hA :
            (if 0 < x then quadrantReturnCount m (x - 1) y else 0) * D =
              m.factorial * ((r + x + y + 2) * (x * (y + 1) * (x + y + 1))) := by
          by_cases hx : 0 < x
          · have hmA : m = 3 * r + (x - 1) + 2 * y := by
              dsimp [m]
              omega
            have hi := ih m hm_lt r (x - 1) y hmA
            have hi' : quadrantReturnCount m (x - 1) y *
                  ((r + x + y + 1).factorial * (r + y + 1).factorial * r.factorial) =
                m.factorial * (x * (y + 1) * (x + y + 1)) := by
              have harg : r + (x - 1) + y + 2 = r + x + y + 1 := by omega
              have hlast : x - 1 + y + 2 = x + y + 1 := by omega
              rw [harg, Nat.sub_add_cancel hx, hlast] at hi
              exact hi
            calc
              (if 0 < x then quadrantReturnCount m (x - 1) y else 0) * D =
                  quadrantReturnCount m (x - 1) y * D := by simp [hx]
              _ = quadrantReturnCount m (x - 1) y *
                    ((r + x + y + 2) * ((r + x + y + 1).factorial *
                      (r + y + 1).factorial * r.factorial)) := by
                    dsimp [D]
                    rw [hfacA]
                    ring
              _ = (r + x + y + 2) *
                    (quadrantReturnCount m (x - 1) y *
                      ((r + x + y + 1).factorial * (r + y + 1).factorial * r.factorial)) := by ring
              _ = (r + x + y + 2) * (m.factorial * (x * (y + 1) * (x + y + 1))) := by rw [hi']
              _ = m.factorial * ((r + x + y + 2) * (x * (y + 1) * (x + y + 1))) := by ring
          · have hx0 : x = 0 := by omega
            simp [hx0, D]
        have hB :
            quadrantReturnCount m x (y + 1) * D =
              m.factorial * (r * ((x + 1) * (y + 2) * (x + y + 3))) := by
          by_cases hr : 0 < r
          · have hmB : m = 3 * (r - 1) + x + 2 * (y + 1) := by
              dsimp [m]
              omega
            have hi := ih m hm_lt (r - 1) x (y + 1) hmB
            have hi' : quadrantReturnCount m x (y + 1) *
                  ((r + x + y + 2).factorial * (r + y + 1).factorial * (r - 1).factorial) =
                m.factorial * ((x + 1) * (y + 2) * (x + y + 3)) := by
              have harg₁ : (r - 1) + x + (y + 1) + 2 = r + x + y + 2 := by omega
              have harg₂ : (r - 1) + (y + 1) + 1 = r + y + 1 := by omega
              rw [harg₁, harg₂] at hi
              exact hi
            have hfacR : r.factorial = r * (r - 1).factorial := by
              simpa [Nat.sub_add_cancel hr] using Nat.factorial_succ (r - 1)
            calc
              quadrantReturnCount m x (y + 1) * D =
                  quadrantReturnCount m x (y + 1) *
                    (r * ((r + x + y + 2).factorial * (r + y + 1).factorial *
                      (r - 1).factorial)) := by
                        dsimp [D]
                        rw [hfacR]
                        ring
              _ = r * (quadrantReturnCount m x (y + 1) *
                    ((r + x + y + 2).factorial * (r + y + 1).factorial *
                      (r - 1).factorial)) := by ring
              _ = r * (m.factorial * ((x + 1) * (y + 2) * (x + y + 3))) := by rw [hi']
              _ = m.factorial * (r * ((x + 1) * (y + 2) * (x + y + 3))) := by ring
          · have hr0 : r = 0 := by omega
            have hzero : quadrantReturnCount m x (y + 1) = 0 := by
              apply quadrantReturnCount_eq_zero
              rintro ⟨s, hs⟩
              dsimp [m] at hs
              omega
            simp [hr0, hzero, D]
        have hfacC : (r + y + 1).factorial =
            (r + y + 1) * (r + y).factorial := by
          simpa [Nat.add_assoc] using Nat.factorial_succ (r + y)
        have hC :
            (if 0 < y then quadrantReturnCount m (x + 1) (y - 1) else 0) * D =
              m.factorial * ((r + y + 1) * ((x + 2) * y * (x + y + 2))) := by
          by_cases hy : 0 < y
          · have hmC : m = 3 * r + (x + 1) + 2 * (y - 1) := by
              dsimp [m]
              omega
            have hi := ih m hm_lt r (x + 1) (y - 1) hmC
            have hi' : quadrantReturnCount m (x + 1) (y - 1) *
                  ((r + x + y + 2).factorial * (r + y).factorial * r.factorial) =
                m.factorial * ((x + 2) * y * (x + y + 2)) := by
              have harg₁ : r + (x + 1) + (y - 1) + 2 = r + x + y + 2 := by omega
              have harg₂ : r + (y - 1) + 1 = r + y := by omega
              have hpoly : x + 1 + (y - 1) + 2 = x + y + 2 := by omega
              rw [harg₁, harg₂, hpoly, Nat.sub_add_cancel hy] at hi
              exact hi
            calc
              (if 0 < y then quadrantReturnCount m (x + 1) (y - 1) else 0) * D =
                  quadrantReturnCount m (x + 1) (y - 1) * D := by simp [hy]
              _ = quadrantReturnCount m (x + 1) (y - 1) *
                    ((r + x + y + 2).factorial *
                      ((r + y + 1) * (r + y).factorial) * r.factorial) := by
                    dsimp [D]
                    rw [hfacC]
              _ = (r + y + 1) *
                    (quadrantReturnCount m (x + 1) (y - 1) *
                      ((r + x + y + 2).factorial * (r + y).factorial * r.factorial)) := by ring
              _ = (r + y + 1) * (m.factorial * ((x + 2) * y * (x + y + 2))) := by rw [hi']
              _ = m.factorial * ((r + y + 1) * ((x + 2) * y * (x + y + 2))) := by ring
          · have hy0 : y = 0 := by omega
            simp [hy0, D]
        rw [← hs, quadrantReturnCount]
        calc
          ((if 0 < x then quadrantReturnCount m (x - 1) y else 0) +
              quadrantReturnCount m x (y + 1) +
                (if 0 < y then quadrantReturnCount m (x + 1) (y - 1) else 0)) * D =
              (if 0 < x then quadrantReturnCount m (x - 1) y else 0) * D +
                quadrantReturnCount m x (y + 1) * D +
                  (if 0 < y then quadrantReturnCount m (x + 1) (y - 1) else 0) * D := by ring
          _ = m.factorial * ((r + x + y + 2) * (x * (y + 1) * (x + y + 1))) +
                m.factorial * (r * ((x + 1) * (y + 2) * (x + y + 3))) +
                  m.factorial * ((r + y + 1) * ((x + 2) * y * (x + y + 2))) := by
                rw [hA, hB, hC]
          _ = (m + 1).factorial * ((x + 1) * (y + 1) * (x + y + 2)) := by
                rw [Nat.factorial_succ m, hs]
                ring
      · have hr0 : r = 0 := by omega
        have hx0 : x = 0 := by omega
        have hy0 : y = 0 := by omega
        subst r
        subst x
        subst y
        norm_num [quadrantReturnCount]

/-- For every admissible length `3*r + x + 2*y`, the exact closed-quadrant
return count is given by the factorial formula. This is combinatorial input -/
theorem quadrantReturnCount_closedForm (r x y : ℕ) :
    quadrantReturnCount (3 * r + x + 2 * y) x y *
        ((r + x + y + 2).factorial * (r + y + 1).factorial * r.factorial) =
      (3 * r + x + 2 * y).factorial * ((x + 1) * (y + 1) * (x + y + 2)) := by
  exact quadrantReturnCount_closedForm_aux (3 * r + x + 2 * y) r x y rfl

/-- Every admissible closed-quadrant return count is positive. This is a
corollary of the exact count used as combinatorial input toward the corrected -/
theorem quadrantReturnCount_pos (r x y : ℕ) :
    0 < quadrantReturnCount (3 * r + x + 2 * y) x y := by
  have hformula := quadrantReturnCount_closedForm r x y
  have hpositive :
      0 < (3 * r + x + 2 * y).factorial * ((x + 1) * (y + 1) * (x + y + 2)) := by
    positivity
  by_contra hcount
  have hzero : quadrantReturnCount (3 * r + x + 2 * y) x y = 0 :=
    Nat.eq_zero_of_not_pos hcount
  rw [hzero] at hformula
  omega

end DirectedDistances.RandomWalk
