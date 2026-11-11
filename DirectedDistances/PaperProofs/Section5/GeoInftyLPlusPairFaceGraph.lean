/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairRotation

/-! The complete face-successor graph in certified three-block pair coordinates. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Reversal on the geometric dart quotient
reverses exactly the endpoint bit in the measurable pair coordinates. -/
theorem lPlusPairGluedDartId_opposite
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusGluedDart s.longest s.hqMode s.hτ) :
    lPlusPairGluedDartId x k r s hk (lPlusSide4GluedOpposite a) =
      ((lPlusPairGluedDartId x k r s hk a).1,
        !(lPlusPairGluedDartId x k r s hk a).2) := by
  induction a using Quotient.inductionOn with
  | h a =>
    change lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawLabel (lPlusSide4BlockOpposite a)) =
      ((lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawLabel a)).1,
        !(lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
          (lPlusBlockDartRawLabel a)).2)
    rcases a with a | (a | a)
    · rfl
    · change (_, (!a.2) ^^ lMinusCodePrimedSideFlip _ a.1) =
        (_, !(a.2 ^^ lMinusCodePrimedSideFlip _ a.1))
      cases a.2 <;> cases lMinusCodePrimedSideFlip _ a.1 <;> rfl
    · rfl

/-- Helper toward Lemma 5.5. A face successor is a retained creation dart
whose opposite is the corrected rotation of the successor. The retained
predicate includes the prefix, primed and hatted blocks. -/
@[expose] noncomputable def lPlusPairFaceNext (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  lPlusPairRetainedCreationDart x k z d ∧
    lPlusPairCorrectedRotationGraph x k z e (d.1, !d.2)

/-- Helper toward Lemma 5.5. Every coordinate of the complete face graph
is measurable on the certified pair domain. -/
theorem measurableSet_lPlusPairFaceNext (x : XDP) (k : ℤ) (d e : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairFaceNext x k z d e} :=
  (measurableSet_lPlusPairRetainedCreationDart x k d).inter
    (measurableSet_lPlusPairCorrectedRotationGraph x k e (d.1, !d.2))

/-- Helper toward Lemma 5.5. On every aligned nonnegative source pair,
the complete measurable face graph is exactly the code-block face relation. -/
theorem lPlusPairFaceNext_iff_codeBlockSide4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairFaceNext x k z (lPlusPairGluedDartId x k r s hk a)
      (lPlusPairGluedDartId x k r s hk b) ↔
    geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) .faceNext
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr a))
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr b)) := by
  dsimp only
  have hret := lPlusPairRetainedCreationDart_iff_of_aligned x k r s hk a
  have hface :=
    s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_faceNext_iff_triangle
      x k r hk a b
  dsimp only at hret hface
  rw [lPlusPairFaceNext, ← lPlusPairGluedDartId_opposite x k r s hk a,
    hret, hface,
    lPlusPairCorrectedRotationGraph_iff_source x k r s hk]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨c, hc, hd⟩
    have hcb := (lPlusPairGluedDartId_injective x k r s hk) hc
    subst c
    exact (lPlusPairGluedDartId_injective x k r s hk) hd
  · intro h
    exact ⟨b, rfl, congrArg (lPlusPairGluedDartId x k r s hk) h⟩

/-- Helper toward Lemma 5.5. The same complete face graph identifies the
canonical side's face successor in transported pair coordinates. -/
theorem lPlusPairFaceNext_iff_canonicalSide4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    lPlusPairFaceNext x k z (lPlusPairGluedDartId x k r s hk a)
      (lPlusPairGluedDartId x k r s hk b) ↔
    (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).faceNext
      (D a).val (D b).val := by
  exact lPlusPairFaceNext_iff_codeBlockSide4 x k r s hk a b

/-- Helper toward Lemma 5.5. A complete measurable face graph exists and
recovers the exact code-block relation on all aligned witnesses. -/
theorem exists_lPlusPairFaceNext
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ F : lPlusCertifiedCodingPairDomain x → (ℕ × Bool) → (ℕ × Bool) → Prop,
      (∀ d e, MeasurableSet {z | F z d e}) ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
        (a b : LPlusGluedDart s.longest s.hqMode s.hτ),
        let z : lPlusCertifiedCodingPairDomain x :=
          ⟨(r, boundaryFutureHattedPath k s.W),
            LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
        F z (lPlusPairGluedDartId x k r s hk a)
          (lPlusPairGluedDartId x k r s hk b) ↔
        geometricSideRelation
          (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) .faceNext
          (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr a))
          (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr b)) :=
  ⟨lPlusPairFaceNext x k, measurableSet_lPlusPairFaceNext x k,
    fun r s a b => lPlusPairFaceNext_iff_codeBlockSide4 x k r s hk a b⟩

/-- Helper toward Lemma 5.5. The complete measurable graph recovers the
canonical side face relation after the exact geometric dart transport. -/
theorem exists_lPlusPairFaceNext_canonicalSide4
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ F : lPlusCertifiedCodingPairDomain x → (ℕ × Bool) → (ℕ × Bool) → Prop,
      (∀ d e, MeasurableSet {z | F z d e}) ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
        (a b : LPlusGluedDart s.longest s.hqMode s.hτ),
        let z : lPlusCertifiedCodingPairDomain x :=
          ⟨(r, boundaryFutureHattedPath k s.W),
            LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
        let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
        F z (lPlusPairGluedDartId x k r s hk a)
          (lPlusPairGluedDartId x k r s hk b) ↔
        (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).faceNext
          (D a).val (D b).val :=
  ⟨lPlusPairFaceNext x k, measurableSet_lPlusPairFaceNext x k,
    fun r s a b => lPlusPairFaceNext_iff_canonicalSide4 x k r s hk a b⟩

end DirectedDistances.PaperProofs.Section5










