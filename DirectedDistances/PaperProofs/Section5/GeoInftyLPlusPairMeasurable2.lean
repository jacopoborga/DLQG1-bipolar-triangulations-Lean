/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusReader5

/-! Conditional witness independence for the corrected left class, with the exact -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. At zero the certified future subassembly
is the complete corrected canonical class, including its boundary markings. -/
theorem lPlusCertifiedCodingPairFuture_class_eq_canonical_zero
    (x : XDP) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x 0 r) :
    geometricSideClass
      (lMinusCanonicalSideOnCoherent x (lPlusCertifiedCodingPairFuture x
        ⟨(r, boundaryFutureHattedPath 0 s.W),
          LPlusSourceWitnessAligned.codingPair_mem_domain x 0 r s⟩)) =
    geometricSideClass
      (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft (le_refl 0)) := by
  rcases s with ⟨⟨W, h, H, hLL, longest, hτ, hp, P, hqMode, Tpath, hfin,
    hleft, hprefix, hcoherent, hprimed⟩, hmode⟩
  change (if longest then XDP.ldp else XDP.sdp) = x at hmode
  subst x
  have hobs : leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) 0 W =
      (hatLawPrimedCodes (boundaryFutureCode 0 W),
        thinSideCode (if longest then XDP.ldp else XDP.sdp) renewalTime
          renewalTime_positiveSuccessTime .left (boundaryFutureHattedPath 0 W)) := by
    rfl
  have hm := lMinusCanonicalSide_class_eq_decodedSide4 hτ hqMode hfin
  have ha := lMinusDecodedSide4_class_eq_actual hτ hp P hqMode
      Tpath hfin hleft (le_refl 0)
  have hplus := (geometricSideClass_eq_iff _ _).mpr
      (boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4
        hτ hp P hqMode Tpath hfin hleft (le_refl 0))
  have he := (hm.trans ha).trans (hplus.trans
      (lPlusCanonicalSide4_class_eq_codeBlockSide4
        hτ hp P hqMode Tpath hfin hleft (le_refl 0)).symm)
  simp only [hobs] at he
  simpa only [lMinusCanonicalSideOnCoherent, lPlusCertifiedCodingPairFuture,
      lPlusCertifiedCodingPairPath, ← hprimed, ← hcoherent] using he

/-- Helper toward Lemma 5.5. The certified corrected-pair target at zero
has a measurable solution without a cross-witness premise. -/
theorem exists_measurable_lPlusCertifiedPairClass_zero (x : XDP) :
    ∃ f : lPlusCertifiedCodingPairDomain x → GeometricSideClass,
      Measurable f ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x 0 r),
        f ⟨(r, boundaryFutureHattedPath 0 s.W),
          LPlusSourceWitnessAligned.codingPair_mem_domain x 0 r s⟩ =
        geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
            (le_refl 0)) := by
  exact ⟨fun z => geometricSideClass
    (lMinusCanonicalSideOnCoherent x (lPlusCertifiedCodingPairFuture x z)),
    measurable_lPlusCertifiedCodingPairFuture_class x,
    lPlusCertifiedCodingPairFuture_class_eq_canonical_zero x⟩

/-- Helper toward Lemma 5.5. The raw corrected-pair target at zero has a
measurable solution, present exactly on the full certification domain. -/
theorem exists_measurable_lPlusRawPairClassOption_zero (x : XDP) :
    ∃ f : LPlusCodingPair x → Option GeometricSideClass,
      Measurable f ∧
      (∀ z, (f z).isSome ↔ z ∈ lPlusCertifiedCodingPairDomain x) ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x 0 r),
        f (r, boundaryFutureHattedPath 0 s.W) =
          some (geometricSideClass
            (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
              (le_refl 0))) := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_lPlusCertifiedPairClass_zero x
  let f (z : LPlusCodingPair x) : Option GeometricSideClass :=
    if hz : z ∈ lPlusCertifiedCodingPairDomain x then some (g ⟨z, hz⟩) else none
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (measurable_some_geometricSideClass.comp hgm).dite measurable_const
      (measurableSet_lPlusCertifiedCodingPairDomain x)
  · intro z
    dsimp only [f]
    split <;> simp_all only [Option.isSome_some, Option.isSome_none,
      Bool.false_eq_true, iff_self]
  · intro r s
    have hz := LPlusSourceWitnessAligned.codingPair_mem_domain x 0 r s
    dsimp only [f]
    rw [dite_eq_left hz, hg r s]

section CrossWitness

variable (hcross : ∀ (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r') (hk : 0 ≤ k)
    (hr : r.code = r'.code),
    geometricSideClass
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
    geometricSideClass
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk))

include hcross

/-- Helper toward Lemma 5.5. Reader 5 returns the corrected canonical class
of every aligned witness; its internal witness choice is irrelevant under
`hcross`. This statement asserts no measurability. -/
theorem LPlusSidePresentation.classOptionAt5_eq_canonical_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    LPlusSidePresentation.classOptionAt5 x k r =
      some (geometricSideClass
        (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)) := by
  let hw : Nonempty (LPlusSourceWitnessAligned x k r) := ⟨s⟩
  rw [LPlusSidePresentation.classOptionAt5_eq_some x k r hk hw]
  apply congrArg some
  exact (hcross x k r r (Classical.choice hw) s hk rfl).trans
    (lPlusCanonicalSide4_class_eq_codeBlockSide4
      s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).symm





theorem exists_lPlusCertifiedPairClass_of_crossWitness
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ f : lPlusCertifiedCodingPairDomain x → GeometricSideClass,
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        f ⟨(r, boundaryFutureHattedPath k s.W),
          LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ =
        geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) := by
  let f (z : lPlusCertifiedCodingPairDomain x) : GeometricSideClass :=
    (LPlusSidePresentation.classOptionAt5 x k z.val.1).getD
      (geometricSideClass
        (lMinusCanonicalSideOnCoherent x (lPlusCertifiedCodingPairFuture x z)))
  refine ⟨f, ?_⟩
  intro r s
  dsimp only [f]
  rw [LPlusSidePresentation.classOptionAt5_eq_canonical_of_aligned hcross x k r s hk]
  rfl

/-- Helper toward Lemma 5.5. There is a raw pair extension present exactly
on the certified domain, agreeing with every aligned corrected class.
This is set-theoretic factorization, without a measurability assertion. -/
theorem exists_lPlusRawPairClassOption_of_crossWitness
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ f : LPlusCodingPair x → Option GeometricSideClass,
      (∀ z, (f z).isSome ↔ z ∈ lPlusCertifiedCodingPairDomain x) ∧
      (∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        f (r, boundaryFutureHattedPath k s.W) =
          some (geometricSideClass
            (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk))) ∧
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        f ∘ lPlusCodingPairObservation x k := by
  obtain ⟨g, hg⟩ := exists_lPlusCertifiedPairClass_of_crossWitness hcross x k hk
  let f (z : LPlusCodingPair x) : Option GeometricSideClass :=
    if hz : z ∈ lPlusCertifiedCodingPairDomain x then some (g ⟨z, hz⟩) else none
  have hf (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) :
      f (r, boundaryFutureHattedPath k s.W) =
        some (geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)) := by
    have hz := LPlusSourceWitnessAligned.codingPair_mem_domain x k r s
    dsimp only [f]
    rw [dite_eq_left hz, hg r s]
  refine ⟨f, ?_, hf, ?_⟩
  · intro z
    dsimp only [f]
    split <;> simp_all only [Option.isSome_some, Option.isSome_none,
      Bool.false_eq_true, iff_self]
  · filter_upwards
      [lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
        hcross x k hk, ae_LPlusSidePresentation_exists_alignedWitness x k]
      with W hactual hsource
    obtain ⟨s, hsW⟩ := hsource
    have hpair :
        (decodeLPlus x k (leftSideObsNonneg x k W), boundaryFutureHattedPath k s.W) =
          lPlusCodingPairObservation x k W := by
      rw [hsW]
      rfl
    change lemma55LeftSideClassOption x k W = f (lPlusCodingPairObservation x k W)
    calc
      lemma55LeftSideClassOption x k W =
          LPlusSidePresentation.classOptionAt5 x k
            (decodeLPlus x k (leftSideObsNonneg x k W)) := hactual
      _ = some (geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)) :=
        LPlusSidePresentation.classOptionAt5_eq_canonical_of_aligned
          hcross x k _ s hk
      _ = f (lPlusCodingPairObservation x k W) := by
        rw [← hpair]
        exact (hf _ s).symm

/-- Helper toward Lemma 5.5. The reader-5 composition is a.e. measurable
at the zero endpoint under precisely the cross-witness comparison. -/
theorem aemeasurable_decodeLPlus_leftSideObsNonneg_classOptionAt5_zero
    (x : XDP) :
    AEMeasurable
      ((LPlusSidePresentation.classOptionAt5 x 0) ∘
        (fun W => decodeLPlus x 0 (leftSideObsNonneg x 0 W)))
      wholePlaneIIDCodeMeasure :=
  (aemeasurable_lemma55LeftSideClassOption_zero x).congr
    (lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
      hcross x 0 (le_refl 0))

/-- Helper toward Lemma 5.5. Reader 5 is a.e. measurable for the exact
observed presentation law at zero, using its proved descent theorem. -/
theorem aemeasurable_LPlusSidePresentation_classOptionAt5_zero
    (x : XDP) :
    AEMeasurable (LPlusSidePresentation.classOptionAt5 x 0)
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLPlus x 0 (leftSideObsNonneg x 0 W))) :=
  aemeasurable_LPlusSidePresentation_classOptionAt5_of_comp x 0 (le_refl 0)
    (aemeasurable_decodeLPlus_leftSideObsNonneg_classOptionAt5_zero hcross x)

end CrossWitness
end DirectedDistances.PaperProofs.Section5



























































































































































/- 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0.
The temporary axiom/signature probe compile exited 0. Each of the eight
new theorems reported exactly [propext, Classical.choice, Quot.sound].
separate kernel checker was run. The unused hr warning preserves the exact
required hcross binder; its name and type have not been changed. -/
