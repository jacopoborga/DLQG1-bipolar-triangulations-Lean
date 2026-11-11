/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantBridgePadding
import Lean.Elab.Tactic.Omega

/-! # Bounded bridge padding toward Proposition 3.9 -/

public section
namespace DirectedDistances.RandomWalk

/-- Helper toward Proposition 3.9: the prescribed length of the fixed
prefix from (a₀,b₀) to (k,k). -/
def padding2PrefixLength (a₀ b₀ k : ℕ) : ℕ :=
  3 * k - 2 * a₀ - b₀

/-- Helper toward Proposition 3.9: the fixed total budget for the loops and
canonical closing word. -/
def padding2LoopBudget (a₁ b₁ k : ℕ) : ℕ :=
  6 * k + 2 * a₁ + b₁

/-- Helper toward Proposition 3.9: the middle-word length after reserving the
fixed prefix and loop/suffix budget from N. -/
def padding2MiddleLength (a₀ b₀ a₁ b₁ k N : ℕ) : ℕ :=
  N - padding2PrefixLength a₀ b₀ k - padding2LoopBudget a₁ b₁ k

/-- Helper toward Proposition 3.9: the natural endpoint obtained by
translating a bounded middle word from (k,k). -/
def padding2MiddleStart (k : ℕ) (w : List (Fin 3)) : ℕ × ℕ :=
  (((k : ℤ) + (paddingWordDisplacement w).1).toNat,
   ((k : ℤ) + (paddingWordDisplacement w).2).toNat)

/-- Helper toward Proposition 3.9: the length of the canonical closing word
from the middle endpoint to (a₁,b₁). -/
def padding2SuffixLength (a₁ b₁ : ℕ) (x : ℕ × ℕ) : ℕ :=
  x.1 + 2 * x.2 + 2 * a₁ + b₁

/-- Helper toward Proposition 3.9: the deterministic padded word associated
to a bounded middle word. -/
def padding2PaddedWord (a₀ b₀ a₁ b₁ k N : ℕ)
    (w : BoundedPaddingMiddleWords (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    List (Fin 3) :=
  let x := padding2MiddleStart k w.1
  let L := padding2SuffixLength a₁ b₁ x
  quadrantPaddingPrefix a₀ b₀ k ++ w.1 ++
    quadrantPaddingLoops ((padding2LoopBudget a₁ b₁ k - L) / 3) ++
    quadrantPaddingClosing x.1 x.2 a₁ b₁

private theorem padding2_middleStart_cast (k m : ℕ)
    (w : BoundedPaddingMiddleWords m k) :
    ((padding2MiddleStart k w.1).1 : ℤ) =
        (k : ℤ) + (paddingWordDisplacement w.1).1 ∧
      ((padding2MiddleStart k w.1).2 : ℤ) =
        (k : ℤ) + (paddingWordDisplacement w.1).2 := by
  have htake : w.1.take m = w.1 := List.take_of_length_le (by rw [w.property.1])
  have hb := w.property.2 m (le_rfl)
  rw [htake] at hb
  rcases hb with ⟨hx0, hx1, hy0, hy1⟩
  constructor
  · exact Int.toNat_of_nonneg (by omega)
  · exact Int.toNat_of_nonneg (by omega)

private theorem padding2_middleStart_bounds (k m : ℕ)
    (w : BoundedPaddingMiddleWords m k) :
    (padding2MiddleStart k w.1).1 ≤ 2 * k ∧
      (padding2MiddleStart k w.1).2 ≤ 2 * k := by
  have htake : w.1.take m = w.1 := List.take_of_length_le (by rw [w.property.1])
  have hdisp := w.property.2 m (le_rfl)
  rw [htake] at hdisp
  rcases hdisp with ⟨hx0, hx1, hy0, hy1⟩
  rcases padding2_middleStart_cast k m w with ⟨hxc, hyc⟩
  constructor <;> omega

/-- Helper toward Proposition 3.9: the chosen middle-word endpoint is the
integer point (k,k) translated by its total displacement. -/
theorem padding2_middleStart_characterization (k m : ℕ)
    (w : BoundedPaddingMiddleWords m k) :
    ((padding2MiddleStart k w.1).1 : ℤ) =
        (k : ℤ) + (paddingWordDisplacement w.1).1 ∧
      ((padding2MiddleStart k w.1).2 : ℤ) =
        (k : ℤ) + (paddingWordDisplacement w.1).2 :=
  padding2_middleStart_cast k m w

/-- Helper toward Proposition 3.9: for the fixed suffix length L and
padding budget Q, the congruence and size assumptions make (Q-L)/3 a
natural loop count, with exactly Q-L letters supplied by its loops. -/
theorem quadrantPadding2_loopCount
    (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)])
    (w : BoundedPaddingMiddleWords
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    let x := padding2MiddleStart k w.1
    let L := padding2SuffixLength a₁ b₁ x
    L ≤ padding2LoopBudget a₁ b₁ k ∧
      padding2LoopBudget a₁ b₁ k = L +
        3 * ((padding2LoopBudget a₁ b₁ k - L) / 3) := by
  dsimp only
  let P := padding2PrefixLength a₀ b₀ k
  let Q := padding2LoopBudget a₁ b₁ k
  let m := padding2MiddleLength a₀ b₀ a₁ b₁ k N
  let x := padding2MiddleStart k w.1
  let L := padding2SuffixLength a₁ b₁ x
  have hm : m = N - P - Q := rfl
  have hPQ : P + Q ≤ N := by simpa [P, Q] using hN
  have hmcast : (m : ℤ) = (N : ℤ) - P - Q := by
    rw [hm]
    omega
  have hstart := padding2_middleStart_cast k m w
  have hbound := padding2_middleStart_bounds k m w
  have hboundx : x.1 ≤ 2 * k ∧ x.2 ≤ 2 * k := by simpa [x] using hbound
  have hword := paddingWordDisplacement_difference_modEq w.1
  have hword' : (paddingWordDisplacement w.1).1 -
      (paddingWordDisplacement w.1).2 ≡ -(m : ℤ) [ZMOD (3 : ℤ)] := by
    rw [w.property.1] at hword
    exact hword
  have hcong' : (a₀ : ℤ) - b₀ - (N : ℤ) ≡
      (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)] := hcong
  constructor
  · change x.1 + 2 * x.2 + 2 * a₁ + b₁ ≤ 6 * k + 2 * a₁ + b₁
    rcases hboundx with ⟨hx, hy⟩
    omega
  · have hLQ : L ≤ Q := by
      change x.1 + 2 * x.2 + 2 * a₁ + b₁ ≤ 6 * k + 2 * a₁ + b₁
      rcases hboundx with ⟨hx, hy⟩
      omega
    have hmodZ : ((Q : ℤ) - (L : ℤ)) % 3 = 0 := by
      have hPcast : (P : ℤ) = 3 * (k : ℤ) - 2 * a₀ - b₀ := by
        have h2a : 2 * a₀ ≤ 3 * k := by omega
        have hb0 : b₀ ≤ 3 * k - 2 * a₀ := by omega
        dsimp [P, padding2PrefixLength]
        rw [Nat.cast_sub hb0, Nat.cast_sub h2a]
        simp
      have hQcast : (Q : ℤ) = 6 * (k : ℤ) + 2 * a₁ + b₁ := by
        simp [Q, padding2LoopBudget]
      have hmcast' : (m : ℤ) = (N : ℤ) - P - Q := hmcast
      have hLcast : (L : ℤ) = (x.1 : ℤ) + 2 * x.2 + 2 * a₁ + b₁ := by
        change ((x.1 + 2 * x.2 + 2 * a₁ + b₁ : ℕ) : ℤ) = _
        push_cast
        ring
      rcases hstart with ⟨hxc, hyc⟩
      have hbudget : (Q : ℤ) - (L : ℤ) =
          3 * (k : ℤ) - (paddingWordDisplacement w.1).1 -
            2 * (paddingWordDisplacement w.1).2 := by
        rw [hQcast, hLcast, hxc, hyc]
        ring
      unfold Int.ModEq at hcong' hword'
      omega
    have hmod : (Q - L) % 3 = 0 := by
      have hcast := hmodZ
      rw [← Nat.cast_sub hLQ] at hcast
      exact_mod_cast hcast
    have hcount : Q = L + 3 * ((Q - L) / 3) := by omega
    exact hcount

/-- Helper toward Proposition 3.9: any number of consecutive `UDW` padding
loops has zero total displacement. -/
theorem padding2Loops_displacement (r : ℕ) :
    paddingWordDisplacement (quadrantPaddingLoops r) = (0, 0) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hrec : quadrantPaddingLoops (r + 1) =
          quadrantPaddingLoop ++ quadrantPaddingLoops r := by
        simp [quadrantPaddingLoops, List.replicate_succ, quadrantPaddingLoop]
      rw [hrec, paddingWordDisplacement_append, ih,
        quadrantPaddingLoop_displacement]
      simp

end DirectedDistances.RandomWalk

