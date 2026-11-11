/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
import Mathlib.Data.List.Basic
import Mathlib.Data.Int.ModEq
import Lean.Elab.Tactic.Omega

/-! # Bounded bridge padding toward Proposition 3.9

The finite word predicates and deterministic prefix/suffix data for the
quadrant bridge padding construction in Proposition 3.9. -/

public section
namespace DirectedDistances.RandomWalk

/-! The source alphabet is identified with `lazyTwoDimensionalStep`: codes
`1`, `2`, and `0` are respectively the proposal's `U`, `D`, and `W`. -/

/-- Helper toward Proposition 3.9: the displacement of a finite source step
word, using the literal step map of `lazyTwoDimensionalPrefix`. -/
@[expose] def paddingWordDisplacement (w : List (Fin 3)) : ℤ × ℤ :=
  w.foldl (fun p c => p + lazyTwoDimensionalStep c) (0, 0)

/-- Helper toward Proposition 3.9: the position after `j` letters of a word
started at `p`. -/
@[expose] def paddingWordPosition (p : ℤ × ℤ) (w : List (Fin 3)) (j : ℕ) : ℤ × ℤ :=
  p + paddingWordDisplacement (w.take j)

/-- Helper toward Proposition 3.9: the length-`N` quadrant bridges from
`u` to `v`, stated as source step words with every integer-time vertex in the
quadrant. -/
@[expose] def QuadrantBridgeWords (N : ℕ) (u v : ℕ × ℕ) :=
  {w : List (Fin 3) // w.length = N ∧
    paddingWordPosition (u.1, u.2) w N = ((v.1 : ℤ), (v.2 : ℤ)) ∧
    ∀ j ≤ N, 0 ≤ (paddingWordPosition (u.1, u.2) w j).1 ∧
      0 ≤ (paddingWordPosition (u.1, u.2) w j).2}

/-- Helper toward Proposition 3.9: middle words whose every partial
displacement lies in the specified integer square. -/
@[expose] def BoundedPaddingMiddleWords (m k : ℕ) :=
  {w : List (Fin 3) // w.length = m ∧
    ∀ j ≤ m,
      -(k : ℤ) ≤ (paddingWordDisplacement (w.take j)).1 ∧
        (paddingWordDisplacement (w.take j)).1 ≤ k ∧
        -(k : ℤ) ≤ (paddingWordDisplacement (w.take j)).2 ∧
        (paddingWordDisplacement (w.take j)).2 ≤ k}

/-- Helper toward Proposition 3.9: the fixed prefix from `(a₀,b₀)` to
`(k,k)`, written in the source code alphabet. -/
@[expose] def quadrantPaddingPrefix (a₀ b₀ k : ℕ) : List (Fin 3) :=
  List.replicate (2 * k - a₀ - b₀) 1 ++ List.replicate (k - a₀) 2

/-- Helper toward Proposition 3.9: the canonical suffix from `(a,b)` to
`(a₁,b₁)` given in the padding proposal. -/
@[expose] def quadrantPaddingClosing (a b a₁ b₁ : ℕ) : List (Fin 3) :=
  List.replicate a 0 ++ List.replicate b 2 ++ List.replicate b 0 ++
    List.replicate (a₁ + b₁) 1 ++ List.replicate a₁ 2

/-- Helper toward Proposition 3.9: one zero-displacement `UDW` loop in the
source alphabet. -/
@[expose] def quadrantPaddingLoop : List (Fin 3) := [1, 2, 0]

/-- Helper toward Proposition 3.9: `r` consecutive copies of the zero
displacement padding loop. -/
@[expose] def quadrantPaddingLoops (r : ℕ) : List (Fin 3) :=
  (List.replicate r quadrantPaddingLoop).flatten

private theorem paddingWordDisplacement_foldl (w : List (Fin 3))
    (p : ℤ × ℤ) :
    w.foldl (fun q c => q + lazyTwoDimensionalStep c) p =
      p + paddingWordDisplacement w := by
  induction w generalizing p with
  | nil => simp [paddingWordDisplacement]
  | cons c w ih =>
      simp only [List.foldl_cons, paddingWordDisplacement, List.foldl_cons]
      rw [show ((0, 0) : ℤ × ℤ) + lazyTwoDimensionalStep c =
        lazyTwoDimensionalStep c by simp]
      rw [ih (p + lazyTwoDimensionalStep c), ih (lazyTwoDimensionalStep c)]
      exact add_assoc p (lazyTwoDimensionalStep c)
        (paddingWordDisplacement w)

/-- Helper toward Proposition 3.9: appending a word adds its displacement. -/
theorem paddingWordDisplacement_append (p q : List (Fin 3)) :
    paddingWordDisplacement (p ++ q) =
      paddingWordDisplacement p + paddingWordDisplacement q := by
  simp only [paddingWordDisplacement, List.foldl_append]
  exact paddingWordDisplacement_foldl q (paddingWordDisplacement p)

/-- Helper toward Proposition 3.9: positions through an appended middle word
are obtained by continuing from the endpoint of the first word. -/
theorem paddingWordPosition_append_at (pfx w : List (Fin 3))
    (start : ℤ × ℤ) (j : ℕ) :
    paddingWordPosition start (pfx ++ w) (pfx.length + j) =
      paddingWordPosition (paddingWordPosition start pfx pfx.length) w j := by
  simp only [paddingWordPosition, List.take_length_add_append,
    paddingWordDisplacement_append]
  rw [List.take_of_length_le (Nat.le_refl pfx.length)]
  exact (add_assoc start (paddingWordDisplacement pfx)
    (paddingWordDisplacement (w.take j))).symm

/-- Helper toward Proposition 3.9: before the end of a prefix, appending a
suffix does not change the path position. -/
theorem paddingWordPosition_append_before (pfx w : List (Fin 3))
    (start : ℤ × ℤ) (j : ℕ) (hj : j ≤ pfx.length) :
    paddingWordPosition start (pfx ++ w) j = paddingWordPosition start pfx j := by
  simp [paddingWordPosition, List.take_append_of_le_length hj]

private theorem paddingStep_difference (c : Fin 3) :
    (lazyTwoDimensionalStep c).1 - (lazyTwoDimensionalStep c).2 ≡
      -1 [ZMOD (3 : ℤ)] := by
  by_cases h0 : c = 0
  · subst c
    norm_num [lazyTwoDimensionalStep, Int.ModEq]
  by_cases h1 : c = 1
  · subst c
    norm_num [lazyTwoDimensionalStep, Int.ModEq]
  have hc : c = 2 := by
    apply Fin.ext
    have hval0 : c.val ≠ 0 := fun h => h0 (Fin.ext h)
    have hval1 : c.val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  subst c
  norm_num [lazyTwoDimensionalStep, Int.ModEq]

/-- Helper toward Proposition 3.9: each source step decreases the difference
of coordinates by one modulo three, so every finite word has the corresponding
endpoint congruence. -/
theorem paddingWordDisplacement_difference_modEq (w : List (Fin 3)) :
    (paddingWordDisplacement w).1 - (paddingWordDisplacement w).2 ≡
      -(w.length : ℤ) [ZMOD (3 : ℤ)] := by
  induction w with
  | nil => simp [paddingWordDisplacement, Int.ModEq]
  | cons c w ih =>
      have hrec : paddingWordDisplacement (c :: w) =
          lazyTwoDimensionalStep c + paddingWordDisplacement w := by
        calc
          paddingWordDisplacement (c :: w) =
              w.foldl (fun p d => p + lazyTwoDimensionalStep d)
                ((0, 0) + lazyTwoDimensionalStep c) := by rfl
          _ = (0, 0) + lazyTwoDimensionalStep c +
                paddingWordDisplacement w :=
            paddingWordDisplacement_foldl w ((0, 0) + lazyTwoDimensionalStep c)
          _ = lazyTwoDimensionalStep c + paddingWordDisplacement w := by simp
      rw [hrec]
      simp only [Prod.fst_add, Prod.snd_add, List.length_cons,
        Nat.cast_succ, neg_add_rev]
      have hc := paddingStep_difference c
      have hsum := hc.add ih
      convert hsum using 1; ring

/-- Helper toward Proposition 3.9: the padding loop returns to its starting
point and has length three. -/
theorem quadrantPaddingLoop_displacement :
    paddingWordDisplacement quadrantPaddingLoop = (0, 0) := by
  norm_num [quadrantPaddingLoop, paddingWordDisplacement,
    lazyTwoDimensionalStep, List.foldl_cons]

/-- Helper toward Proposition 3.9: repeating the source loop has the exact
length needed for the modular padding. -/
theorem quadrantPaddingLoop_replicate_length (r : ℕ) :
    (quadrantPaddingLoops r).length = 3 * r := by
  simp [quadrantPaddingLoops, quadrantPaddingLoop, Nat.mul_comm]

private theorem paddingWordDisplacement_replicate (c : Fin 3) (n : ℕ) :
    paddingWordDisplacement (List.replicate n c) =
      ((n : ℤ) * (lazyTwoDimensionalStep c).1,
        (n : ℤ) * (lazyTwoDimensionalStep c).2) := by
  induction n with
  | zero => simp [paddingWordDisplacement]
  | succ n ih =>
      rw [List.replicate_succ']
      rw [paddingWordDisplacement_append, ih]
      have hsingle : paddingWordDisplacement [c] = lazyTwoDimensionalStep c := by
        simp [paddingWordDisplacement]
      rw [hsingle]
      simp only [Nat.cast_succ]
      change ((↑n * (lazyTwoDimensionalStep c).1 +
          (lazyTwoDimensionalStep c).1,
        ↑n * (lazyTwoDimensionalStep c).2 +
          (lazyTwoDimensionalStep c).2) =
        ((↑n + 1) * (lazyTwoDimensionalStep c).1,
          (↑n + 1) * (lazyTwoDimensionalStep c).2))
      apply Prod.ext <;> ring

private theorem paddingWordPosition_replicate (p : ℤ × ℤ) (c : Fin 3)
    (n j : ℕ) (hj : j ≤ n) :
    paddingWordPosition p (List.replicate n c) j =
      (p.1 + (j : ℤ) * (lazyTwoDimensionalStep c).1,
        p.2 + (j : ℤ) * (lazyTwoDimensionalStep c).2) := by
  simp [paddingWordPosition, List.take_replicate, Nat.min_eq_left hj,
    paddingWordDisplacement_replicate]
  exact Prod.ext rfl rfl

/-- Helper toward Proposition 3.9: the fixed prefix has displacement from
`(a₀,b₀)` to `(k,k)`. -/
theorem quadrantPaddingPrefix_displacement (a₀ b₀ k : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k) :
    paddingWordDisplacement (quadrantPaddingPrefix a₀ b₀ k) =
      ((k : ℤ) - a₀, (k : ℤ) - b₀) := by
  have ha : a₀ ≤ k := le_trans (le_max_left _ _) hk
  have hb' : max b₀ 1 ≤ k := le_trans (le_max_right _ _) hk
  have hb : b₀ ≤ k := le_trans (le_max_left _ _) hb'
  simp [quadrantPaddingPrefix, paddingWordDisplacement_append,
    paddingWordDisplacement_replicate, lazyTwoDimensionalStep_one,
    lazyTwoDimensionalStep_two]
  omega

/-- Helper toward Proposition 3.9: every vertex on the fixed prefix lies in
the quadrant. -/
theorem quadrantPaddingPrefix_stays (a₀ b₀ k : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k) :
    ∀ j ≤ (quadrantPaddingPrefix a₀ b₀ k).length,
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (quadrantPaddingPrefix a₀ b₀ k) j).1 ∧
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (quadrantPaddingPrefix a₀ b₀ k) j).2 := by
  have ha : a₀ ≤ k := le_trans (le_max_left _ _) hk
  have hb' : max b₀ 1 ≤ k := le_trans (le_max_right _ _) hk
  have hb : b₀ ≤ k := le_trans (le_max_left _ _) hb'
  let A := 2 * k - a₀ - b₀
  let B := k - a₀
  have hform : quadrantPaddingPrefix a₀ b₀ k =
      List.replicate A 1 ++ List.replicate B 2 := rfl
  have hlenA : A = 2 * k - a₀ - b₀ := rfl
  have hlenB : B = k - a₀ := rfl
  intro j hj
  have hlen : (quadrantPaddingPrefix a₀ b₀ k).length = A + B := by
    simp [quadrantPaddingPrefix, A, B]
  by_cases hja : j ≤ A
  · rw [hform]
    have hja' : j ≤ (List.replicate A (1 : Fin 3)).length := by simpa using hja
    rw [paddingWordPosition_append_before _ _ _ _ hja']
    rw [paddingWordPosition_replicate _ _ _ _ hja]
    simp [lazyTwoDimensionalStep_one]
    omega
  · have hAj : A ≤ j := by omega
    let t := j - A
    have hjEq : j = A + t := by simp [t, Nat.add_sub_of_le hAj]
    have htB : t ≤ B := by omega
    rw [hform, hjEq]
    have hidx : A + t = (List.replicate A (1 : Fin 3)).length + t := by simp
    have happ := paddingWordPosition_append_at
      (List.replicate A (1 : Fin 3)) (List.replicate B (2 : Fin 3))
      ((a₀ : ℤ), (b₀ : ℤ)) t
    rw [hidx, happ]
    simp only [List.length_replicate]
    rw [paddingWordPosition_replicate _ _ _ _ (by omega : A ≤ A)]
    rw [paddingWordPosition_replicate _ _ _ _ htB]
    simp [A, t, lazyTwoDimensionalStep_one, lazyTwoDimensionalStep_two]
    omega

/-- Helper toward Proposition 3.9: the canonical closing path has displacement
`(a₁-a,b₁-b)`. -/
theorem quadrantPaddingClosing_displacement (a b a₁ b₁ : ℕ) :
    paddingWordDisplacement (quadrantPaddingClosing a b a₁ b₁) =
      ((a₁ : ℤ) - a, (b₁ : ℤ) - b) := by
  simp [quadrantPaddingClosing, paddingWordDisplacement_append,
    paddingWordDisplacement_replicate, lazyTwoDimensionalStep_zero,
    lazyTwoDimensionalStep_one, lazyTwoDimensionalStep_two]
  constructor <;> omega

/-- Helper toward Proposition 3.9: the bounded middle word stays in the
quadrant when translated from the anchor `(k,k)`, and ends in `[0,2k]^2`. -/
theorem boundedPaddingMiddle_quadrant (m k : ℕ)
    (w : BoundedPaddingMiddleWords m k) (j : ℕ) (hj : j ≤ m) :
    0 ≤ (paddingWordPosition ((k : ℤ), (k : ℤ)) w.1 j).1 ∧
      (paddingWordPosition ((k : ℤ), (k : ℤ)) w.1 j).1 ≤ 2 * (k : ℤ) ∧
      0 ≤ (paddingWordPosition ((k : ℤ), (k : ℤ)) w.1 j).2 ∧
      (paddingWordPosition ((k : ℤ), (k : ℤ)) w.1 j).2 ≤ 2 * (k : ℤ) := by
  have hb := w.property.2 j hj
  change 0 ≤ (k : ℤ) + (paddingWordDisplacement (w.1.take j)).1 ∧
    ((k : ℤ) + (paddingWordDisplacement (w.1.take j)).1) ≤ 2 * (k : ℤ) ∧
    0 ≤ (k : ℤ) + (paddingWordDisplacement (w.1.take j)).2 ∧
    ((k : ℤ) + (paddingWordDisplacement (w.1.take j)).2) ≤ 2 * (k : ℤ)
  rcases hb with ⟨hx0, hx1, hy0, hy1⟩
  omega

/-- Helper toward Proposition 3.9: the fixed prefix reaches the anchor
`(k,k)`. -/
theorem quadrantPaddingPrefix_endpoint (a₀ b₀ k : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k) :
    paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
      (quadrantPaddingPrefix a₀ b₀ k)
      (quadrantPaddingPrefix a₀ b₀ k).length = ((k : ℤ), (k : ℤ)) := by
  rw [paddingWordPosition, List.take_length, quadrantPaddingPrefix_displacement a₀ b₀ k hk]
  change ((a₀ : ℤ) + ((k : ℤ) - a₀), (b₀ : ℤ) + ((k : ℤ) - b₀)) =
    ((k : ℤ), (k : ℤ))
  apply Prod.ext <;> omega

/-- Helper toward Proposition 3.9: the canonical closing word ends at the
prescribed endpoint. -/
theorem quadrantPaddingClosing_endpoint (a b a₁ b₁ : ℕ) :
    paddingWordPosition ((a : ℤ), (b : ℤ))
      (quadrantPaddingClosing a b a₁ b₁)
      (quadrantPaddingClosing a b a₁ b₁).length = ((a₁ : ℤ), (b₁ : ℤ)) := by
  rw [paddingWordPosition, List.take_length,
    quadrantPaddingClosing_displacement a b a₁ b₁]
  change ((a : ℤ) + ((a₁ : ℤ) - a), (b : ℤ) + ((b₁ : ℤ) - b)) =
    ((a₁ : ℤ), (b₁ : ℤ))
  apply Prod.ext <;> omega

/-- Helper toward Proposition 3.9: the canonical prefix has the proposed
length `3k - 2a₀ - b₀`. -/
theorem quadrantPaddingPrefix_length (a₀ b₀ k : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k) :
    (quadrantPaddingPrefix a₀ b₀ k).length = 3 * k - 2 * a₀ - b₀ := by
  simp [quadrantPaddingPrefix]
  omega

/-- Helper toward Proposition 3.9: the closing word has length
`a + 2b + 2a₁ + b₁`. -/
theorem quadrantPaddingClosing_length (a b a₁ b₁ : ℕ) :
    (quadrantPaddingClosing a b a₁ b₁).length = a + 2 * b + 2 * a₁ + b₁ := by
  simp [quadrantPaddingClosing]
  omega

end DirectedDistances.RandomWalk
