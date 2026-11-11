/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCanonicalCoding3

/-! Certified presentation/path pairs for the nonnegative left side. Certification
here means coherence, primed finite incidence, and exact hatted-code agreement;
it does not assert that a pair has a source preimage or a corrected side reader. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Keep the complete presentation together with
the actual hatted path, rather than choosing a preimage of its thin code. -/
abbrev LPlusCodingPair (x : XDP) := LPlusSidePresentation x × (ℕ → ℤ × ℤ)

/-- Helper toward Lemma 5.5. The pair observation retains all three code
blocks and the coherent hatted path from the same source stream. -/
@[expose] noncomputable def lPlusCodingPairObservation (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : LPlusCodingPair x :=
  (decodeLPlus x k (leftSideObsNonneg x k W), boundaryFutureHattedPath k W)

/-- Helper toward Lemma 5.5. The joint pair observation is a.e. measurable. -/
theorem aemeasurable_lPlusCodingPairObservation (x : XDP) (k : ℤ) :
    AEMeasurable (lPlusCodingPairObservation x k) wholePlaneIIDCodeMeasure :=
  (aemeasurable_decodeLPlus_leftSideObsNonneg x k).prodMk
    (aemeasurable_boundaryFutureHattedPath k)

/-- Helper toward Lemma 5.5. The exact coherent-pair certification domain
also requires local finiteness of the primed KMSW code. -/
@[expose] def lPlusCertifiedCodingPairDomain (x : XDP) : Set (LPlusCodingPair x) :=
  {z | z.2 ∈ (Coherent x) ∧ KMSWFiniteIncidence z.1.code.2.2 ∧
    ∀ i : ℕ, ∃ a : LeftThinValue i,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left z.2 i = a.val ∧
      z.1.code.2.1 i = a.val}

/-- Helper toward Lemma 5.5. Pair certification is a measurable event;
the hatted-code agreement is a countable intersection of coordinate tests. -/
theorem measurableSet_lPlusCertifiedCodingPairDomain (x : XDP) :
    MeasurableSet (lPlusCertifiedCodingPairDomain x) := by
  have hq : MeasurableSet {z : LPlusCodingPair x | z.2 ∈ Coherent x} :=
    (selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1.preimage measurable_snd
  have hf : MeasurableSet {z : LPlusCodingPair x |
      KMSWFiniteIncidence z.1.code.2.2} :=
    measurableSet_finiteIncidence.preimage
      ((measurable_lPlusSidePresentation_code x).snd.snd.comp measurable_fst)
  have hc (i : ℕ) : MeasurableSet {z : LPlusCodingPair x |
      ∃ a : LeftThinValue i,
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .left z.2 i = a.val ∧
        z.1.code.2.1 i = a.val} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun a =>
      ((((measurable_pi_apply i).comp
        ((measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime
          .left).comp measurable_snd)).eq_const a.val).setOf).inter
      ((((measurable_pi_apply i).comp
        ((measurable_lPlusSidePresentation_code x).snd.fst.comp
          measurable_fst)).eq_const a.val).setOf))
  simpa only [lPlusCertifiedCodingPairDomain, Set.ofPred_and, Set.ofPred_forall] using
    hq.inter (hf.inter (MeasurableSet.iInter hc))

/-- Helper toward Lemma 5.5. Certification says exactly that the path is
coherent, the primed code has finite incidence, and the certified presentation's
hatted code is the code of that very path. -/
theorem mem_lPlusCertifiedCodingPairDomain_iff (x : XDP) (z : LPlusCodingPair x) :
    z ∈ lPlusCertifiedCodingPairDomain x ↔
      z.2 ∈ (Coherent x) ∧ KMSWFiniteIncidence z.1.code.2.2 ∧
      z.1 ∈ lPlusCertifiedPresentationDomain x ∧
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left z.2 =
        z.1.code.2.1 := by
  constructor
  · rintro ⟨hq, hf, hc⟩
    refine ⟨hq, hf, ?_, ?_⟩
    · intro i
      obtain ⟨a, _, ha⟩ := hc i
      exact ha.symm ▸ a.property
    · funext i
      obtain ⟨a, hq, hr⟩ := hc i
      exact hq.trans hr.symm
  · rintro ⟨hq, hf, hr, hc⟩
    refine ⟨hq, hf, fun i => ?_⟩
    exact ⟨⟨z.1.code.2.1 i, hr i⟩, congrFun hc i, rfl⟩

/-- Helper toward Lemma 5.5. All certification requirements hold on one
source-law probability-one event, for every fixed index and mode. -/
theorem ae_lPlusCodingPairObservation_mem_domain (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      lPlusCodingPairObservation x k W ∈ lPlusCertifiedCodingPairDomain x := by
  filter_upwards [ae_m0LeftSideReaderWitness, wholePlane_ae_boundaryGluing_inputs,
    (boundaryFutureThinSides_package x k).2.2.2.2.2,
    ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range x k] with W hr hg hq hc
  rw [lPlusCodingPairObservation, mem_lPlusCertifiedCodingPairDomain_iff]
  refine ⟨hq, ?_, hc, ?_⟩
  · let w := Classical.choice (hr true)
    obtain ⟨hτ, hfin, _, _⟩ := hg w.h k
    simpa only [decodeLPlus_code, leftSideObsNonneg, leftSideObsNonpos,
      boundaryFourObservations, Fin.cases, Fin.induction, Fin.induction.go] using
      (lMinus_primed_observation_finiteIncidence (longest := true) hτ hfin)
  · simp only [decodeLPlus_code, leftSideObsNonneg, boundaryFourObservations,
      Fin.cases, Fin.induction, Fin.induction.go]
    rfl

/-- Helper toward Lemma 5.5. The joint pair law is concentrated on the
measurable certified domain; source validity is proved a.e., not assumed. -/
theorem ae_lPlusCodingPair_mem_domain (x : XDP) (k : ℤ) :
    ∀ᵐ z ∂wholePlaneIIDCodeMeasure.map (lPlusCodingPairObservation x k),
      z ∈ lPlusCertifiedCodingPairDomain x :=
  (ae_map_iff (aemeasurable_lPlusCodingPairObservation x k)
    (measurableSet_lPlusCertifiedCodingPairDomain x)).mpr
      (ae_lPlusCodingPairObservation_mem_domain x k)

/-- Helper toward Lemma 5.5. The certified hatted path projection makes
no additional choice of a path with the same thin code. -/
@[expose] def lPlusCertifiedCodingPairPath (x : XDP)
    (z : lPlusCertifiedCodingPairDomain x) : Coherent x :=
  ⟨z.val.2, z.property.1⟩

/-- Helper toward Lemma 5.5. The coherent path projection is measurable
for the inherited measurable structures. -/
theorem measurable_lPlusCertifiedCodingPairPath (x : XDP) :
    Measurable (lPlusCertifiedCodingPairPath x) :=
  (measurable_snd.comp measurable_subtype_coe).subtype_mk

/-- Helper toward Lemma 5.5. On certified pairs, the path projection
recovers the entire hatted coordinate of the presentation. -/
theorem lPlusCertifiedCodingPairPath_code (x : XDP)
    (z : lPlusCertifiedCodingPairDomain x) :
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
      (lPlusCertifiedCodingPairPath x z).val = z.val.1.code.2.1 :=
  ((mem_lPlusCertifiedCodingPairDomain_iff x z.val).mp z.property).2.2.2

/-- Helper toward Lemma 5.5. Project the primed and hatted blocks to the
existing two-block canonical constructor. The stopped prefix is retained in
the original pair and is not included in this future subassembly. -/
@[expose] def lPlusCertifiedCodingPairFuture (x : XDP)
    (z : lPlusCertifiedCodingPairDomain x) : LMinusCanonicalCodingDomain x :=
  ⟨(decodeLMinus x 0 (z.val.1.code.2.2, z.val.1.code.2.1),
    lPlusCertifiedCodingPairPath x z), z.property.2.1⟩

/-- Helper toward Lemma 5.5. The two-block future projection is measurable
on certified pairs, including its original finite-incidence certificate. -/
theorem measurable_lPlusCertifiedCodingPairFuture (x : XDP) :
    Measurable (lPlusCertifiedCodingPairFuture x) := by
  have hc := (measurable_lPlusSidePresentation_code x).comp
    (measurable_fst.comp
      (measurable_subtype_coe (p := fun z : LPlusCodingPair x =>
        z ∈ lPlusCertifiedCodingPairDomain x)))
  exact (((measurable_decodeLMinus x 0).comp (hc.snd.snd.prodMk hc.snd.fst)).prodMk
    (measurable_lPlusCertifiedCodingPairPath x)).subtype_mk

/-- Helper toward Lemma 5.5. All geometric coordinates of the primed/hatted
future subassembly are measurable on the certified pair domain. This is not
the three-block corrected side when the stopped prefix is nonempty. -/
theorem measurable_lPlusCertifiedCodingPairFuture_geometricSideCode (x : XDP) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      geometricSideCode (lMinusCanonicalSideOnCoherent x
        (lPlusCertifiedCodingPairFuture x z))) :=
  (measurable_lMinusCanonicalSideOnCoherent_code x).comp
    (measurable_lPlusCertifiedCodingPairFuture x)

/-- Helper toward Lemma 5.5. The primed/hatted future class is measurable
on certified pairs. The finite stopped-prefix attachment remains separate. -/
theorem measurable_lPlusCertifiedCodingPairFuture_class (x : XDP) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      geometricSideClass (lMinusCanonicalSideOnCoherent x
        (lPlusCertifiedCodingPairFuture x z))) :=
  (measurable_lMinusCanonicalSideOnCoherent_class x).comp
    (measurable_lPlusCertifiedCodingPairFuture x)

/-- Helper toward Lemma 5.5. Every mode-aligned source witness supplies
a certified pair. No coherence, incidence, or range premise is added. -/
theorem LPlusSourceWitnessAligned.codingPair_mem_domain
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) :
    (r, boundaryFutureHattedPath k s.W) ∈ lPlusCertifiedCodingPairDomain x := by
  have hq := s.hattedPath_mem
  have hf := lMinus_primed_observation_finiteIncidence
    (longest := s.longest) s.hτ s.hfin
  change KMSWFiniteIncidence (hatLawPrimedCodes (boundaryFutureCode k s.W)) at hf
  rw [s.primedCode_eq] at hf
  apply (mem_lPlusCertifiedCodingPairDomain_iff x _).mpr
  refine ⟨hq, hf, ?_, s.coherentCode_eq⟩
  intro i
  rw [← s.coherentCode_eq]
  rw [thinSideCode_coe x renewalTime renewalTime_positiveSuccessTime .left
    ⟨boundaryFutureHattedPath k s.W, hq⟩]
  exact ⟨selectedCutSide x renewalTime .left
    (leastGoodCut x renewalTime renewalTime_positiveSuccessTime i
      ⟨boundaryFutureHattedPath k s.W, hq⟩) (boundaryFutureHattedPath k s.W), rfl⟩

/-- Helper toward Lemma 5.5. The actual optional class equals the canonical
class built from its own chosen witness on the certified pair event. This
does not replace that witness by a selected preimage of the pair. -/
theorem ae_lemma55LeftSideClassOption_eq_lPlusCanonicalSide4_on_pairs
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      lPlusCodingPairObservation x k W ∈ lPlusCertifiedCodingPairDomain x ∧
      ∃ hw : Nonempty (M0LeftSideReaderWitness W
          (if x = XDP.ldp then true else false)),
      let w := Classical.choice hw
      ∃ (hτ : HasFlowLineHits (boundaryGluingFutureStream W w.h k))
        (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W w.h k))
        (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
          (if (if x = XDP.ldp then true else false) then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime),
        lemma55LeftSideClassOption x k W =
          some (geometricSideClass
            (lPlusCanonicalSide4 hτ w.hp (w.P k) hqMode (w.T k) hfin (w.hleft k) hk)) := by
  filter_upwards [ae_lPlusCodingPairObservation_mem_domain x k,
    ae_lemma55LeftSideClassOption_eq_lPlusCodeBlockSide4 x k hk] with W hD hW
  obtain ⟨hw, hτ, hfin, hq, he⟩ := hW
  let w := Classical.choice hw
  refine ⟨hD, hw, hτ, hfin, hq, ?_⟩
  exact he.trans (congrArg some
    (lPlusCanonicalSide4_class_eq_codeBlockSide4
      hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk).symm)


































































































end DirectedDistances.PaperProofs.Section5

/- compiled together without duplicate declarations. Development compile exits
were 1, 1, 0, 0, 0, 0. The first two failures concerned a notation parse,
an unavailable measurable-diagonal instance on unrestricted truncation
values, and unfolding the certification set; all were resolved above.
The temporary axiom/signature probe compile exited 0. All seventeen named
definitions and theorems reported exactly
[propext, Classical.choice, Quot.sound]. Both full existential corrected-pair
were removed before the final production compile. No separate kernel checker -/
