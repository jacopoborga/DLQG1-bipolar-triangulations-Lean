/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWPeanoPrefixFinal
public import DirectedDistances.KMSW.KMSWForwardClass
public import DirectedDistances.KMSW.KMSWInverseClass

/-! Supporting lemmas for paper labels `def-kmsw`, `thm-kmsw` (see CORRESPONDENCE.md). -/

/-! # Conditional class bijection for the KMSW procedure

`KMSWPeanoPrefixExistsFinal`; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The open induction step of the Peano-prefix reconstruction (stated, NOT
assumed anywhere as an axiom). Helper toward `thm-kmsw`
conditional on the named open step `KMSWPeanoPrefixExistsFinal`; not the paper
result. -/
@[expose] def KMSWPeanoPrefixExistsFinal (ℓ r n : ℕ) : Prop :=
  ∀ R : KMSWMapRep ℓ r n,
    Nonempty (KMSWPeanoPrefixEmbedding R.B (kmswRepInverseWalkClass R)
      (n - 1) (kmswPeanoPrefixFinal_lt R))

private instance instFiniteKMSWMapIsoClass (ℓ r n : ℕ) :
    Finite (KMSWMapIsoClass ℓ r n) := KMSWMapIsoClass.finite ℓ r n

/-- Given the open final-prefix induction step, mapping the inverse walk class
back to its map class is the identity. Helper toward `thm-kmsw`
conditional on the named open step `KMSWPeanoPrefixExistsFinal`; not the paper
result. -/
theorem kmswToMapIsoClass_comp_inverse_of_prefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    ∀ q : KMSWMapIsoClass ℓ r n,
      kmswToMapIsoClass hn (kmswClassInverseWalkClass q) = q := by
  intro q
  refine KMSWMapIsoClass.ind
    (motive := fun q =>
      kmswToMapIsoClass hn (kmswClassInverseWalkClass q) = q) ?_ q
  intro R
  obtain ⟨P⟩ := h R
  exact kmswToMapIsoClass_inverse_of_finalPrefix R P

/-- The inverse walk class supplies a preimage for every map class, assuming
the open final-prefix step. Helper toward `thm-kmsw`
conditional on the named open step `KMSWPeanoPrefixExistsFinal`; not the paper
result. -/
theorem kmswToMapIsoClass_surjective_of_prefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    Function.Surjective (@kmswToMapIsoClass ℓ r n hn) := by
  intro q
  exact ⟨kmswClassInverseWalkClass q,
    kmswToMapIsoClass_comp_inverse_of_prefix h hn q⟩

/-- The walk-to-map class function is bijective assuming the open
final-prefix step, combining its proved injectivity with the conditional
surjectivity. Helper toward `thm-kmsw`
conditional on the named open step `KMSWPeanoPrefixExistsFinal`; not the paper
result. -/
theorem kmswToMapIsoClass_bijective_of_prefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    Function.Bijective (@kmswToMapIsoClass ℓ r n hn) := by
  exact ⟨kmswToMapIsoClass_injective hn,
    kmswToMapIsoClass_surjective_of_prefix h hn⟩

/-- Applying the forward map-class function after the inverse walk-class
function recovers every walk class, by injectivity of the forward function.
`KMSWPeanoPrefixExistsFinal`; not the paper result. -/
theorem kmswClassInverseWalkClass_comp_forward_of_prefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    ∀ c : KMSWWalkClass ℓ r n,
      kmswClassInverseWalkClass (kmswToMapIsoClass hn c) = c := by
  intro c
  apply kmswToMapIsoClass_injective hn
  exact kmswToMapIsoClass_comp_inverse_of_prefix h hn
    (kmswToMapIsoClass hn c)

/-- The walk-class and unrooted map-class carriers have equal finite
cardinality, conditional on the open final-prefix step. Helper toward
the paper result. -/
theorem kmswToMapIsoClass_natCard_eq_of_prefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    Nat.card (KMSWWalkClass ℓ r n) = Nat.card (KMSWMapIsoClass ℓ r n) := by
  exact Nat.card_eq_of_bijective _
    (kmswToMapIsoClass_bijective_of_prefix h hn)

/-- The conditional walk-class/map-class equivalence. The target is the
unrooted `KMSWMapIsoClass` carrier used by `kmswToMapIsoClass`. Helper toward
the paper result. -/
noncomputable def kmswProcedureEquivOfPrefix {ℓ r n : ℕ}
    (h : KMSWPeanoPrefixExistsFinal ℓ r n) (hn : 1 ≤ n) :
    KMSWWalkClass ℓ r n ≃ KMSWMapIsoClass ℓ r n :=
  Equiv.ofBijective (@kmswToMapIsoClass ℓ r n hn)
    (kmswToMapIsoClass_bijective_of_prefix h hn)








end DirectedDistances.KMSW
