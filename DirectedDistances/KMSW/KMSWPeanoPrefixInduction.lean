/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariant
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantSteps
public import DirectedDistances.KMSW.KMSWProcedureBijection

/-! # Conditional induction for Peano prefixes

conditional on the named step Props; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- The rotate preservation obligation for one Peano-prefix extension.
conditional on the named step Props; not the paper result. -/
@[expose] def KMSWPeanoRotatePreserves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) : Prop :=
  ∀ j (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj),
    KMSWPeanoPrefixInv B c j hj P →
    ∀ (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges),
      peanoStepKind B j hj1 = .rotate →
      codeExtend c j = 1 →
      ∃ Q : KMSWPeanoPrefixEmbedding B c (j + 1) hj1,
        KMSWPeanoPrefixInv B c (j + 1) hj1 Q

/-- The climb preservation obligation for one Peano-prefix extension.
conditional on the named step Props; not the paper result. -/
@[expose] def KMSWPeanoClimbPreserves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) : Prop :=
  ∀ j (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj),
    KMSWPeanoPrefixInv B c j hj P →
    ∀ (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges),
      peanoStepKind B j hj1 = .climb →
      codeExtend c j = 0 →
      ∃ Q : KMSWPeanoPrefixEmbedding B c (j + 1) hj1,
        KMSWPeanoPrefixInv B c (j + 1) hj1 Q

/-- Inductively construct every Peano-prefix embedding together with its
geometric invariant from the initial prefix, the descend construction, and the
named rotate and climb preservation steps. Helper toward thm-kmsw
step Props; not the paper result. -/
theorem kmswPeanoPrefix_exists_of_steps
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n)
    (hkind : ∀ j (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges),
      (codeExtend c j = 2 ↔ peanoStepKind B j hj1 = .descend) ∧
      (codeExtend c j = 0 ↔ peanoStepKind B j hj1 = .climb) ∧
      (codeExtend c j = 1 ↔ peanoStepKind B j hj1 = .rotate))
    (hrot : KMSWPeanoRotatePreserves B c)
    (hclimb : KMSWPeanoClimbPreserves B c) :
    ∀ j (hj : j < B.map.toCombinatorialMap.numEdges),
      ∃ P : KMSWPeanoPrefixEmbedding B c j hj,
        KMSWPeanoPrefixInv B c j hj P := by
  intro j
  induction j with
  | zero =>
      intro hj
      have hj0 : hj = contour_numEdges_pos B := Subsingleton.elim _ _
      subst hj
      exact ⟨kmswPeanoPrefixEmbedding_zero B c, kmswPeanoPrefixInv_zero B c⟩
  | succ j ih =>
      intro hj
      have hj0 : j < B.map.toCombinatorialMap.numEdges := by omega
      obtain ⟨P, I⟩ := ih hj0
      have hj1 : j + 1 < B.map.toCombinatorialMap.numEdges := by omega
      rcases hk : peanoStepKind B j hj1 with _ | _ | _
      · have hcode : codeExtend c j = 2 := ((hkind j hj1).1).2 hk
        obtain ⟨Q, IQ, _⟩ := kmswPeanoPrefixInv_descend
          B c j hj0 P I hj1 hk hcode
        exact ⟨Q, IQ⟩
      · have hcode : codeExtend c j = 1 := ((hkind j hj1).2.2).2 hk
        exact hrot j hj0 P I hj1 hk hcode
      · have hcode : codeExtend c j = 0 := ((hkind j hj1).2.1).2 hk
        exact hclimb j hj0 P I hj1 hk hcode

/-- The inverse walk class of every representative admits the final Peano
prefix, assuming the named rotate and climb preservation steps. Helper toward
the named step Props; not the paper result. -/
theorem kmswPeanoPrefixExistsFinal_of_steps {ℓ r n : ℕ}
    (hrot : ∀ R : KMSWMapRep ℓ r n,
      KMSWPeanoRotatePreserves R.B (kmswRepInverseWalkClass R))
    (hclimb : ∀ R : KMSWMapRep ℓ r n,
      KMSWPeanoClimbPreserves R.B (kmswRepInverseWalkClass R)) :
    KMSWPeanoPrefixExistsFinal ℓ r n := by
  intro R
  have hkind :
      ∀ j (hj1 : j + 1 < R.B.map.toCombinatorialMap.numEdges),
        (codeExtend (kmswRepInverseWalkClass R) j = 2 ↔
          peanoStepKind R.B j hj1 = .descend) ∧
        (codeExtend (kmswRepInverseWalkClass R) j = 0 ↔
          peanoStepKind R.B j hj1 = .climb) ∧
        (codeExtend (kmswRepInverseWalkClass R) j = 1 ↔
          peanoStepKind R.B j hj1 = .rotate) := by
    intro j hj1
    have hjn : j + 1 < n := by simpa only [R.edges] using hj1
    exact ⟨
      codeExtend_kmswRepInverseWalkClass_eq_two_iff_peanoStepKind_descend R j hjn,
      codeExtend_kmswRepInverseWalkClass_eq_zero_iff_peanoStepKind_climb R j hjn,
      codeExtend_kmswRepInverseWalkClass_eq_one_iff_peanoStepKind_rotate R j hjn⟩
  obtain ⟨P, _⟩ := kmswPeanoPrefix_exists_of_steps R.B
    (kmswRepInverseWalkClass R) hkind (hrot R) (hclimb R)
    (n - 1) (kmswPeanoPrefixFinal_lt R)
  exact ⟨P⟩

/-- The walk-class-to-map-class function is bijective assuming the named
rotate and climb preservation steps. Helper toward thm-kmsw
step Props; not the paper result. -/
theorem kmswToMapIsoClass_bijective_of_steps {ℓ r n : ℕ}
    (hrot : ∀ R : KMSWMapRep ℓ r n,
      KMSWPeanoRotatePreserves R.B (kmswRepInverseWalkClass R))
    (hclimb : ∀ R : KMSWMapRep ℓ r n,
      KMSWPeanoClimbPreserves R.B (kmswRepInverseWalkClass R))
    (hn : 1 ≤ n) :
    Function.Bijective (@kmswToMapIsoClass ℓ r n hn) := by
  exact kmswToMapIsoClass_bijective_of_prefix
    (kmswPeanoPrefixExistsFinal_of_steps hrot hclimb) hn

end DirectedDistances.KMSW
