/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWInverseLeft
public import DirectedDistances.RandomWalk.PitmanCodes













public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped BigOperators

/-- Extend a finite code word by the fixed code `0`. Values in the first
`n - 1` positions are exactly the finite word. -/
@[expose] def finiteCodeExtend {n : ℕ} (c : Fin (n - 1) → Fin 3) : ℕ → Fin 3 :=
  fun i => if h : i < n - 1 then c ⟨i, h⟩ else 0

/-- The finite walk predicate for the implemented lazy step map. Its endpoint
is `(ℓ - 1, -r + 1)` in integer coordinates; every time in `range (n - 1 + 1)`
lies in `[0, ∞) × [-r + 1, ∞)` (`thm-kmsw`,
implemented `(0, 1)` step rather than the theorem's printed `(1, 0)`. -/
@[expose] def KMSWWalkAdmissible (ℓ r n : ℕ) (c : Fin (n - 1) → Fin 3) : Prop :=
  integrateCodes (finiteCodeExtend c) (n - 1) =
      ((ℓ : ℤ) - 1, -(r : ℤ) + 1) ∧
    ∀ k ∈ Finset.range (n - 1 + 1),
      0 ≤ (integrateCodes (finiteCodeExtend c) k).1 ∧
        -(r : ℤ) + 1 ≤ (integrateCodes (finiteCodeExtend c) k).2

/-- Decidable finite endpoint and cone conditions for a finite code word. -/
instance instDecidableKMSWWalkAdmissible (ℓ r n : ℕ) :
    DecidablePred (KMSWWalkAdmissible ℓ r n) := by
  intro c
  unfold KMSWWalkAdmissible
  infer_instance

/-- The subtype of words with `n - 1` implemented lazy steps, starting at
`(0, 0)`, ending at `(ℓ - 1, -r + 1)`, and staying in the prescribed quadrant
at every integer time from `0` through `n - 1` (`thm-kmsw`, -/
@[expose] def KMSWWalkClass (ℓ r n : ℕ) :=
  {c : Fin (n - 1) → Fin 3 // KMSWWalkAdmissible ℓ r n c}

/-- The finite walk class has a computable finite enumeration. -/
noncomputable instance instFintypeKMSWWalkClass (ℓ r n : ℕ) :
    Fintype (KMSWWalkClass ℓ r n) := by
  classical
  change Fintype {c : Fin (n - 1) → Fin 3 // KMSWWalkAdmissible ℓ r n c}
  exact Fintype.subtype
    (Finset.univ.filter (fun c : Fin (n - 1) → Fin 3 => KMSWWalkAdmissible ℓ r n c))
    (by intro c; simp)

/-- Extend the class word to an infinite code sequence by padding with code `0`
after its `n - 1` source steps. -/
@[expose] def codeExtend {ℓ r n : ℕ} (c : KMSWWalkClass ℓ r n) : ℕ → Fin 3 :=
  finiteCodeExtend c.val

/-- On each position of the finite word, `codeExtend` returns that word's
code. -/
theorem codeExtend_of_lt {ℓ r n : ℕ} (c : KMSWWalkClass ℓ r n)
    (i : ℕ) (hi : i < n - 1) :
    codeExtend c i = c.val ⟨i, hi⟩ := by
  simp [codeExtend, finiteCodeExtend, hi]

/-- The rooted KMSW stage after the `n - 1` codes of a finite walk. -/
@[expose] def kmswWalkClassMap {ℓ r n : ℕ} (c : KMSWWalkClass ℓ r n) :=
  kmswRootedStage (codeExtend c) (n - 1)

/-- Rooted-stage isomorphism forces equality of the finite source words. This
is the injectivity half of Theorem 3.5 (`thm-kmsw`,
no surjectivity claim; the contour-tree inverse and an isomorphism-class -/
theorem kmswWalkClassMap_injective {ℓ r n : ℕ}
    (c c' : KMSWWalkClass ℓ r n)
    (h : RootedDirectedMapIso (kmswWalkClassMap c) (kmswWalkClassMap c')) :
    c = c' := by
  apply Subtype.ext
  funext i
  have hp := prefixCodes_of_iso (codeExtend c) (codeExtend c') (n - 1) h i.val i.isLt
  have hi : (⟨i.val, i.isLt⟩ : Fin (n - 1)) = i := Fin.ext rfl
  rw [codeExtend_of_lt c i.val i.isLt, codeExtend_of_lt c' i.val i.isLt] at hp
  rw [hi] at hp
  exact hp

/-- The cardinality of the finite walk class is the number of words in the
decidable Finset filter satisfying its endpoint and quadrant conditions. -/
theorem card_KMSWWalkClass (ℓ r n : ℕ) :
    Fintype.card (KMSWWalkClass ℓ r n) =
      (Finset.univ.filter (fun c : Fin (n - 1) → Fin 3 =>
        KMSWWalkAdmissible ℓ r n c)).card := by
  classical
  change Fintype.card
      {c : Fin (n - 1) → Fin 3 // KMSWWalkAdmissible ℓ r n c} = _
  rw [Fintype.card_subtype]

end DirectedDistances.KMSW
