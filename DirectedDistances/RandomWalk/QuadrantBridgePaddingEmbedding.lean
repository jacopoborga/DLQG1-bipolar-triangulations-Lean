/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantBridgePadding2
import all DirectedDistances.RandomWalk.QuadrantBridgePadding2

/-! # The deterministic padding embedding toward Proposition 3.9 -/

public section
namespace DirectedDistances.RandomWalk

private theorem displacement_replicate (c : Fin 3) (n : ℕ) :
    paddingWordDisplacement (List.replicate n c) =
      ((n : ℤ) * (lazyTwoDimensionalStep c).1,
        (n : ℤ) * (lazyTwoDimensionalStep c).2) := by
  induction n with
  | zero => simp [paddingWordDisplacement]
  | succ n ih =>
      rw [List.replicate_succ', paddingWordDisplacement_append, ih]
      simp only [paddingWordDisplacement, List.foldl_cons, List.foldl_nil,
        Nat.cast_succ, add_mul, one_mul]
      apply Prod.ext <;> simp

private theorem position_replicate (p : ℤ × ℤ) (c : Fin 3) (n j : ℕ)
    (hj : j ≤ n) :
    paddingWordPosition p (List.replicate n c) j =
      (p.1 + (j : ℤ) * (lazyTwoDimensionalStep c).1,
        p.2 + (j : ℤ) * (lazyTwoDimensionalStep c).2) := by
  simp [paddingWordPosition, List.take_replicate, Nat.min_eq_left hj,
    displacement_replicate]
  rfl

private theorem append_stays (p : ℤ × ℤ) (u v : List (Fin 3))
    (hu : ∀ j ≤ u.length, 0 ≤ (paddingWordPosition p u j).1 ∧
      0 ≤ (paddingWordPosition p u j).2)
    (hv : ∀ j ≤ v.length,
      0 ≤ (paddingWordPosition (paddingWordPosition p u u.length) v j).1 ∧
      0 ≤ (paddingWordPosition (paddingWordPosition p u u.length) v j).2) :
    ∀ j ≤ (u ++ v).length, 0 ≤ (paddingWordPosition p (u ++ v) j).1 ∧
      0 ≤ (paddingWordPosition p (u ++ v) j).2 := by
  intro j hj
  by_cases h : j ≤ u.length
  · rw [paddingWordPosition_append_before _ _ _ _ h]
    exact hu j h
  · have heq : j = u.length + (j - u.length) := by omega
    rw [heq, paddingWordPosition_append_at]
    exact hv _ (by simp only [List.length_append] at hj; omega)

private theorem replicate_stays (p : ℤ × ℤ) (c : Fin 3) (n : ℕ)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hend : 0 ≤ p.1 + (n : ℤ) * (lazyTwoDimensionalStep c).1 ∧
      0 ≤ p.2 + (n : ℤ) * (lazyTwoDimensionalStep c).2) :
    ∀ j ≤ (List.replicate n c).length,
      0 ≤ (paddingWordPosition p (List.replicate n c) j).1 ∧
      0 ≤ (paddingWordPosition p (List.replicate n c) j).2 := by
  intro j hj
  simp only [List.length_replicate] at hj
  rw [position_replicate _ _ _ _ hj]
  fin_cases c <;> simp_all [lazyTwoDimensionalStep] <;> omega

/-- Helper toward Proposition 3.9: one padding loop stays in the closed
quadrant from every point of that quadrant. -/
theorem quadrantPaddingLoop_stays (p : ℤ × ℤ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    ∀ j ≤ quadrantPaddingLoop.length,
      0 ≤ (paddingWordPosition p quadrantPaddingLoop j).1 ∧
      0 ≤ (paddingWordPosition p quadrantPaddingLoop j).2 := by
  intro j hj
  have hj3 : j ≤ 3 := by simpa [quadrantPaddingLoop] using hj
  interval_cases j <;>
    simp [paddingWordPosition, quadrantPaddingLoop, paddingWordDisplacement,
      lazyTwoDimensionalStep] <;> omega

/-- Helper toward Proposition 3.9: every repeated padding loop stays in the
closed quadrant from every point of that quadrant. -/
theorem quadrantPaddingLoops_stays (r : ℕ) (p : ℤ × ℤ)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    ∀ j ≤ (quadrantPaddingLoops r).length,
      0 ≤ (paddingWordPosition p (quadrantPaddingLoops r) j).1 ∧
      0 ≤ (paddingWordPosition p (quadrantPaddingLoops r) j).2 := by
  induction r with
  | zero => simpa [quadrantPaddingLoops, paddingWordPosition,
      paddingWordDisplacement] using hp
  | succ r ih =>
      have hrec : quadrantPaddingLoops (r + 1) =
          quadrantPaddingLoop ++ quadrantPaddingLoops r := by
        simp [quadrantPaddingLoops, List.replicate_succ]
      rw [hrec]
      apply append_stays _ _ _ (quadrantPaddingLoop_stays p hp)
      simpa [paddingWordPosition, quadrantPaddingLoop_displacement] using ih

/-- Helper toward Proposition 3.9: the canonical closing path stays in the
closed quadrant, including when either endpoint is on its boundary. -/
theorem quadrantPaddingClosing_stays (a b a₁ b₁ : ℕ) :
    ∀ j ≤ (quadrantPaddingClosing a b a₁ b₁).length,
      0 ≤ (paddingWordPosition ((a : ℤ), (b : ℤ))
        (quadrantPaddingClosing a b a₁ b₁) j).1 ∧
      0 ≤ (paddingWordPosition ((a : ℤ), (b : ℤ))
        (quadrantPaddingClosing a b a₁ b₁) j).2 := by
  unfold quadrantPaddingClosing
  apply append_stays
  · apply append_stays
    · apply append_stays
      · apply append_stays
        · apply replicate_stays <;> simp
        · have he : paddingWordPosition ((a : ℤ), (b : ℤ))
              (List.replicate a (0 : Fin 3))
              (List.replicate a (0 : Fin 3)).length = (0, (b : ℤ)) := by
            rw [paddingWordPosition, List.take_length]
            simp [displacement_replicate]
          rw [he]
          apply replicate_stays <;> simp
      · have he : paddingWordPosition ((a : ℤ), (b : ℤ))
            (List.replicate a (0 : Fin 3) ++ List.replicate b 2)
            (List.replicate a (0 : Fin 3) ++ List.replicate b 2).length = ((b : ℤ), 0) := by
          rw [paddingWordPosition, List.take_length]
          apply Prod.ext <;>
            simp [paddingWordDisplacement_append,
              displacement_replicate]
        rw [he]
        apply replicate_stays <;> simp
    · have he : paddingWordPosition ((a : ℤ), (b : ℤ))
          (List.replicate a (0 : Fin 3) ++ List.replicate b 2 ++ List.replicate b 0)
          (List.replicate a (0 : Fin 3) ++ List.replicate b 2 ++ List.replicate b 0).length =
          (0, 0) := by
        rw [paddingWordPosition, List.take_length]
        apply Prod.ext <;>
          simp [paddingWordDisplacement_append,
            displacement_replicate]
      rw [he]
      apply replicate_stays <;> simp
      omega
  · have he : paddingWordPosition ((a : ℤ), (b : ℤ))
        (List.replicate a (0 : Fin 3) ++ List.replicate b 2 ++ List.replicate b 0 ++
          List.replicate (a₁ + b₁) 1)
        (List.replicate a (0 : Fin 3) ++ List.replicate b 2 ++ List.replicate b 0 ++
          List.replicate (a₁ + b₁) 1).length = (0, (a₁ : ℤ) + b₁) := by
      rw [paddingWordPosition, List.take_length]
      apply Prod.ext <;>
        simp [paddingWordDisplacement_append,
          displacement_replicate]
    rw [he]
    apply replicate_stays <;> simp
    omega



theorem padding2PaddedWord_length (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)])
    (w : BoundedPaddingMiddleWords
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    (padding2PaddedWord a₀ b₀ a₁ b₁ k N w).length = N := by
  have hc := (quadrantPadding2_loopCount a₀ b₀ a₁ b₁ k N hk hN hcong w).2
  have hp := quadrantPaddingPrefix_length a₀ b₀ k hk
  have hm := w.property.1
  unfold padding2PaddedWord
  simp only [List.length_append, hp, hm,
    quadrantPaddingLoop_replicate_length, quadrantPaddingClosing_length]
  change padding2PrefixLength a₀ b₀ k +
    padding2MiddleLength a₀ b₀ a₁ b₁ k N +
    3 * ((padding2LoopBudget a₁ b₁ k -
      padding2SuffixLength a₁ b₁ (padding2MiddleStart k w.1)) / 3) +
    padding2SuffixLength a₁ b₁ (padding2MiddleStart k w.1) = N
  unfold padding2MiddleLength
  omega

private theorem position_append_end (p : ℤ × ℤ) (u v : List (Fin 3)) :
    paddingWordPosition p (u ++ v) (u ++ v).length =
      paddingWordPosition (paddingWordPosition p u u.length) v v.length := by
  rw [List.length_append, paddingWordPosition_append_at]

private theorem middle_endpoint (a₀ b₀ k m : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k) (w : BoundedPaddingMiddleWords m k) :
    paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
      (quadrantPaddingPrefix a₀ b₀ k ++ w.1)
      (quadrantPaddingPrefix a₀ b₀ k ++ w.1).length =
      (((padding2MiddleStart k w.1).1 : ℤ),
        ((padding2MiddleStart k w.1).2 : ℤ)) := by
  rw [position_append_end, quadrantPaddingPrefix_endpoint _ _ _ hk,
    paddingWordPosition, List.take_length]
  rcases padding2_middleStart_characterization k m w with ⟨hx, hy⟩
  apply Prod.ext
  · exact hx.symm
  · exact hy.symm

private theorem loops_endpoint (p : ℤ × ℤ) (r : ℕ) :
    paddingWordPosition p (quadrantPaddingLoops r)
      (quadrantPaddingLoops r).length = p := by
  simp [paddingWordPosition, padding2Loops_displacement]

/-- Helper toward Proposition 3.9: the padded word ends at the prescribed
endpoint, with the same size and congruence binders as the loop-count theorem. -/
theorem padding2PaddedWord_endpoint (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)])
    (w : BoundedPaddingMiddleWords
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
      (padding2PaddedWord a₀ b₀ a₁ b₁ k N w) N = ((a₁ : ℤ), (b₁ : ℤ)) := by
  conv_lhs =>
    arg 3
    rw [← padding2PaddedWord_length a₀ b₀ a₁ b₁ k N hk hN hcong w]
  unfold padding2PaddedWord
  dsimp only
  rw [position_append_end, position_append_end, middle_endpoint _ _ _ _ hk w,
    loops_endpoint, quadrantPaddingClosing_endpoint]

/-- Helper toward Proposition 3.9: every integer-time position of the padded
word lies in the closed quadrant. -/
theorem padding2PaddedWord_stays (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)])
    (w : BoundedPaddingMiddleWords
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    ∀ j ≤ N,
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (padding2PaddedWord a₀ b₀ a₁ b₁ k N w) j).1 ∧
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (padding2PaddedWord a₀ b₀ a₁ b₁ k N w) j).2 := by
  intro j hj
  have hj' : j ≤ (padding2PaddedWord a₀ b₀ a₁ b₁ k N w).length := by
    rwa [padding2PaddedWord_length a₀ b₀ a₁ b₁ k N hk hN hcong w]
  suffices hs : ∀ j ≤ (padding2PaddedWord a₀ b₀ a₁ b₁ k N w).length,
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (padding2PaddedWord a₀ b₀ a₁ b₁ k N w) j).1 ∧
      0 ≤ (paddingWordPosition ((a₀ : ℤ), (b₀ : ℤ))
        (padding2PaddedWord a₀ b₀ a₁ b₁ k N w) j).2 from hs j hj'
  unfold padding2PaddedWord
  dsimp only
  apply append_stays
  · apply append_stays
    · apply append_stays
      · exact quadrantPaddingPrefix_stays a₀ b₀ k hk
      · rw [quadrantPaddingPrefix_endpoint _ _ _ hk]
        intro j hj
        have hb := boundedPaddingMiddle_quadrant _ k w j
          (by simpa only [w.property.1] using hj)
        exact ⟨hb.1, hb.2.2.1⟩
    · rw [middle_endpoint _ _ _ _ hk w]
      apply quadrantPaddingLoops_stays
      exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  · rw [position_append_end, middle_endpoint _ _ _ _ hk w, loops_endpoint]
    exact quadrantPaddingClosing_stays _ _ _ _

/-- Helper toward Proposition 3.9: dropping the fixed prefix and taking the
middle length recovers the input word exactly. -/
theorem padding2PaddedWord_recovery (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (w : BoundedPaddingMiddleWords
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) :
    ((padding2PaddedWord a₀ b₀ a₁ b₁ k N w).drop
      (padding2PrefixLength a₀ b₀ k)).take
      (padding2MiddleLength a₀ b₀ a₁ b₁ k N) = w.1 := by
  have hp : (quadrantPaddingPrefix a₀ b₀ k).length =
      padding2PrefixLength a₀ b₀ k := quadrantPaddingPrefix_length a₀ b₀ k hk
  unfold padding2PaddedWord
  dsimp only
  rw [List.append_assoc, List.append_assoc, ← hp, List.drop_left]
  exact List.take_left' w.property.1

/-- Helper toward Proposition 3.9: deterministic padding embeds bounded
middle words into length-N quadrant bridges without changing the input word. -/
@[expose] def padding2BridgeEmbedding (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)]) :
    BoundedPaddingMiddleWords (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k ↪
      QuadrantBridgeWords N (a₀, b₀) (a₁, b₁) where
  toFun w := ⟨padding2PaddedWord a₀ b₀ a₁ b₁ k N w,
    padding2PaddedWord_length a₀ b₀ a₁ b₁ k N hk hN hcong w,
    padding2PaddedWord_endpoint a₀ b₀ a₁ b₁ k N hk hN hcong w,
    padding2PaddedWord_stays a₀ b₀ a₁ b₁ k N hk hN hcong w⟩
  inj' := by
    intro w v h
    apply Subtype.ext
    have he := congrArg (fun z : QuadrantBridgeWords N (a₀, b₀) (a₁, b₁) =>
      (z.1.drop (padding2PrefixLength a₀ b₀ k)).take
        (padding2MiddleLength a₀ b₀ a₁ b₁ k N)) h
    change ((padding2PaddedWord a₀ b₀ a₁ b₁ k N w).drop _).take _ =
      ((padding2PaddedWord a₀ b₀ a₁ b₁ k N v).drop _).take _ at he
    simpa only [padding2PaddedWord_recovery _ _ _ _ _ _ hk] using he

/-- Helper toward Proposition 3.9: length-N quadrant bridges form a finite
type, by encoding their letters as a function on `Fin N`. -/
instance quadrantBridgeWords_finite (N : ℕ) (u v : ℕ × ℕ) :
    Finite (QuadrantBridgeWords N u v) := by
  let f : QuadrantBridgeWords N u v → (Fin N → Fin 3) := fun w i =>
    w.1[i.val]'(by rw [w.property.1]; exact i.isLt)
  apply Finite.of_injective f
  intro w z h
  apply Subtype.ext
  apply List.ext_getElem (w.property.1.trans z.property.1.symm)
  intro i hi hiz
  have hiN : i < N := by rwa [w.property.1] at hi
  exact congrFun h ⟨i, hiN⟩

/-- Helper toward Proposition 3.9: the padding embedding gives the finite
cardinal comparison between bounded middle words and quadrant bridges. -/
theorem padding2_card_le_quadrantBridgeWords (a₀ b₀ a₁ b₁ k N : ℕ)
    (hk : max a₀ (max b₀ 1) ≤ k)
    (hN : padding2PrefixLength a₀ b₀ k + padding2LoopBudget a₁ b₁ k ≤ N)
    (hcong : (a₀ : ℤ) - b₀ - N ≡ (a₁ : ℤ) - b₁ [ZMOD (3 : ℤ)]) :
    Nat.card (BoundedPaddingMiddleWords (padding2MiddleLength a₀ b₀ a₁ b₁ k N) k) ≤
      Nat.card (QuadrantBridgeWords N (a₀, b₀) (a₁, b₁)) := by
  exact Nat.card_le_card_of_injective
    (padding2BridgeEmbedding a₀ b₀ a₁ b₁ k N hk hN hcong)
    (padding2BridgeEmbedding a₀ b₀ a₁ b₁ k N hk hN hcong).injective

end DirectedDistances.RandomWalk
