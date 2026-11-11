/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7
public import DirectedDistances.PaperProofs.Section3.IntrinsicBusemannIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTLawStatementsSections135
import DirectedDistances.Probability.SkorokhodFloorStep

/-! # Intrinsic Busemann consumers on sampled classes

coordinator; no qualification removal or numbered-result closure is claimed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open DirectedDistances.Probability MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology Classical

local instance intrinsicConsumers14To18MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumers14To18BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: retain precisely the intrinsic cut's
vertices, geometric edges and missing tags for its distance characterization. -/
@[expose] def intrinsicConsumerCut {A : D39DomainRootedMap.{0}}
    (C : IntrinsicFutureCut2 A) : IntrinsicBusemannCut A :=
  ⟨C.vertices, C.edges, C.missing⟩

/-- Helper toward Proposition 3.9: both normalized characterizations on
the unique intrinsic cut, simultaneously for every sampled representative. -/
theorem intrinsicConsumers_characterization_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ A : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W →
        (∃! _C : IntrinsicFutureCut2 A, True) ∧
        ∀ C : IntrinsicFutureCut2 A,
          (IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
              (identifiedSDPBusemann W) ∧
            ∀ X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X →
              X = identifiedSDPBusemann W) ∧
          (IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (identifiedLDPBusemann W) ∧
            ∀ X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X →
              X = identifiedLDPBusemann W) := by
  filter_upwards [uibotCut2_sample_unique_realization,
    intrinsicBusemann_sample_identification_ae, uibotRecoveredCode_ae] with W hcut hbus hcode
  dsimp only at hcut hbus ⊢
  rw [hcode] at hbus
  obtain ⟨H, h, hpast, hp, hrep⟩ := hcut
  obtain ⟨_, _, H', h', hpast', hp', _, hbrep⟩ := hbus
  cases Subsingleton.elim H' H
  cases Subsingleton.elim h' h
  cases Subsingleton.elim hpast' hpast
  cases Subsingleton.elim hp' hp
  intro A hA
  obtain ⟨⟨I⟩, C₀, hC₀, _⟩ := hrep A hA
  refine ⟨⟨C₀, trivial, fun C _ => hC₀.1 C⟩, ?_⟩
  intro C
  have heq := hC₀.1 C
  subst C
  have hdata := hC₀.2 I
  obtain ⟨hv, he, _, _, hm, _, _, hx, _⟩ := hdata
  have hS : intrinsicConsumerCut C₀ =
      intrinsicBusemannImageCut W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
        (m0CutData W H h (fun _ _ => hp _)) A I := by
    cases C₀
    simp only [intrinsicConsumerCut, intrinsicBusemannImageCut,
      IntrinsicBusemannCut.mk.injEq]
    refine ⟨hv, he, funext fun e => propext ?_⟩
    simpa only [Equiv.apply_symm_apply] using hm (I.edgeEquiv.symm e)
  have hlabel : C₀.x = fun k => I.vertexEquiv
      ((m0CutData W H h (fun _ _ => hp _)).x k) := funext hx
  rw [hS, hlabel]
  exact (hbrep A hA).2 I

/-- Helper toward Proposition 3.9: a sequence is intrinsic to the class
when it satisfies the characterization on every representative and cut. -/
@[expose] def IsIntrinsicConsumerSequence (longest : Bool)
    (z : D39GeomRootedMapClass.{0}) (X : ℤ → ℤ) : Prop :=
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    ∀ C : IntrinsicFutureCut2 A,
      if longest then IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X
      else IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X

/-- Helper toward Proposition 3.9: existence and uniqueness precede the
class selector; the same entire sequence works for all representatives. -/
theorem intrinsicConsumers_existsUnique_ae (longest : Bool) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃! X : ℤ → ℤ, IsIntrinsicConsumerSequence longest
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) X := by
  filter_upwards [intrinsicConsumers_characterization_ae] with W hW
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
  obtain ⟨A, hA⟩ := Quotient.exists_rep z
  obtain ⟨C, _, _⟩ := (hW A hA).1
  cases longest
  · refine ⟨identifiedSDPBusemann W, ?_, ?_⟩
    · intro B hB D
      exact ((hW B hB).2 D).1.1
    · intro X hX
      exact ((hW A hA).2 C).1.2 X (hX A hA C)
  · refine ⟨identifiedLDPBusemann W, ?_, ?_⟩
    · intro B hB D
      exact ((hW B hB).2 D).2.1
    · intro X hX
      exact ((hW A hA).2 C).2.2 X (hX A hA C)

/-- Helper toward Proposition 3.9: the intrinsic class sequence selected
by its full characterization, with zero extension outside its existence set. -/
@[expose] def intrinsicConsumerSequence (longest : Bool)
    (z : D39GeomRootedMapClass.{0}) : ℤ → ℤ :=
  if h : ∃! X, IsIntrinsicConsumerSequence longest z X then
    Classical.choose h.exists else 0

/-- Helper toward Proposition 3.9: the random intrinsic sequence of the
sampled map, defined without choosing a representative or a source isomorphism. -/
@[expose] def sampledIntrinsicSequence (longest : Bool) (W : ℤ → Fin 3) : ℤ → ℤ :=
  intrinsicConsumerSequence longest
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)

/-- Helper toward Proposition 3.9: on one event both intrinsic sequences
are well-defined and equal the entire identified code sequences. -/
theorem sampledIntrinsicSequence_identification_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (∀ longest, IsIntrinsicConsumerSequence longest
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)
        (sampledIntrinsicSequence longest W)) ∧
      sampledIntrinsicSequence false W = identifiedSDPBusemann W ∧
      sampledIntrinsicSequence true W = identifiedLDPBusemann W := by
  filter_upwards [intrinsicConsumers_characterization_ae,
    intrinsicConsumers_existsUnique_ae false, intrinsicConsumers_existsUnique_ae true]
      with W hW hS hL
  have hs (longest : Bool) : IsIntrinsicConsumerSequence longest
      (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)
      (sampledIntrinsicSequence longest W) := by
    have hex : ∃! X, IsIntrinsicConsumerSequence longest
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) X := by
      cases longest <;> assumption
    exact (by
      simpa only [sampledIntrinsicSequence, intrinsicConsumerSequence, dite_eq_left hex] using
        Classical.choose_spec hex.exists)
  obtain ⟨A, hA⟩ := Quotient.exists_rep
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)
  obtain ⟨C, _, _⟩ := (hW A hA).1
  exact ⟨hs, ((hW A hA).2 C).1.2 _ (hs false A hA C),
    ((hW A hA).2 C).2.2 _ (hs true A hA C)⟩

private def identifiedConsumerSequence (longest : Bool) (W : ℤ → Fin 3) : ℤ → ℤ :=
  if longest then identifiedLDPBusemann W else identifiedSDPBusemann W

/-- Helper toward Proposition 3.9: on one iid event, every representative
has a unique cut, both modes have unique normalized intrinsic sequences on
that cut, and the representative-independent selectors realize them. -/
theorem intrinsicConsumers_cut_sequences_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ A : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W →
        (∃! _C : IntrinsicFutureCut2 A, True) ∧
        ∀ C : IntrinsicFutureCut2 A,
          (∃! X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
          (∃! X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
          (sampledIntrinsicSequence false W = identifiedSDPBusemann W ∧
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence false W)) ∧
          (sampledIntrinsicSequence true W = identifiedLDPBusemann W ∧
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence true W)) := by
  filter_upwards [intrinsicConsumers_characterization_ae,
    sampledIntrinsicSequence_identification_ae] with W hW hseq
  intro A hA
  refine ⟨(hW A hA).1, ?_⟩
  intro C
  obtain ⟨hS, hL⟩ := (hW A hA).2 C
  exact ⟨⟨_, hS.1, hS.2⟩, ⟨_, hL.1, hL.2⟩,
    ⟨hseq.2.1, hseq.1 false A hA C⟩, ⟨hseq.2.2, hseq.1 true A hA C⟩⟩

private theorem sampled_sequence_ae (longest : Bool) :
    sampledIntrinsicSequence longest =ᵐ[wholePlaneIIDCodeMeasure]
      identifiedConsumerSequence longest := by
  filter_upwards [sampledIntrinsicSequence_identification_ae] with W hW
  cases longest
  · exact hW.2.1
  · exact hW.2.2

/-- Helper toward Proposition 3.9: each mode's four increment-law clauses
of Theorem 1.7, including simultaneous positive-index bounds. -/
@[expose] def IntrinsicConsumerIncrementLaw (longest : Bool)
    (X : (ℤ → Fin 3) → ℤ → ℤ) : Prop :=
  iIndepFun (fun k W => X W k - X W (k - 1)) wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => X W k - X W (k - 1))
      (fun W => X W 1 - X W (1 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => X W k - X W (k - 1))
      (fun W => X W 0 - X W (0 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      if longest then X W k - X W (k - 1) ≤ -1
      else -1 ≤ X W k - X W (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => X W k - X W (k - 1))
      (fun W => X W (k - 1) - X W k)
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure)

private theorem consumer_identDistrib_congr {f g f' g' : (ℤ → Fin 3) → ℤ}
    (h : IdentDistrib f g wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure)
    (hf : f =ᵐ[wholePlaneIIDCodeMeasure] f')
    (hg : g =ᵐ[wholePlaneIIDCodeMeasure] g') :
    IdentDistrib f' g' wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure :=
  ⟨h.aemeasurable_fst.congr hf, h.aemeasurable_snd.congr hg,
    (Measure.map_congr hf).symm.trans (h.map_eq.trans (Measure.map_congr hg))⟩

/-- Helper toward Proposition 3.9: independence, both stationary halves,
the bounds and symmetry hold for the sampled intrinsic sequences. -/
theorem intrinsicConsumers_increment_law (longest : Bool) :
    IntrinsicConsumerIncrementLaw longest (sampledIntrinsicSequence longest) := by
  have hcode : IntrinsicConsumerIncrementLaw longest (identifiedConsumerSequence longest) := by
    cases longest
    · exact DirectedDistances.Paper.Section1.thm_busemann_property.2.2
    · exact DirectedDistances.Paper.Section1.thm_busemann_property.1.2
  obtain ⟨hind, hpos, hneg, hbound, hsym⟩ := hcode
  have heq (k : ℤ) :
      (fun W => identifiedConsumerSequence longest W k -
        identifiedConsumerSequence longest W (k - 1)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => sampledIntrinsicSequence longest W k -
        sampledIntrinsicSequence longest W (k - 1)) :=
    (sampled_sequence_ae longest).symm.mono fun W h =>
      congrArg (fun X => X k - X (k - 1)) h
  refine ⟨hind.congr heq, fun k hk => consumer_identDistrib_congr (hpos k hk)
    (heq k) (heq 1), fun k hk => consumer_identDistrib_congr (hneg k hk)
    (heq k) (heq 0), ?_, ?_⟩
  · filter_upwards [hbound, sampled_sequence_ae longest] with W hb he
    simpa only [he] using hb
  · intro k hk
    exact consumer_identDistrib_congr (hsym k hk) (heq k)
      ((sampled_sequence_ae longest).symm.mono fun W h =>
        congrArg (fun X => X (k - 1) - X k) h)

/-- Helper toward Proposition 3.9: literal floor rescaling of the intrinsic
sequence in the whole-line local Skorokhod carrier, at scale `n + 1`. -/
@[expose] def sampledIntrinsicScalingPath (longest : Bool) (n : ℕ)
    (W : ℤ → Fin 3) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (if longest then (-3 / 2 : ℝ) else (-3 / 4 : ℝ)) *
      (sampledIntrinsicSequence longest W ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (sampledIntrinsicSequence longest W j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (if longest then (-3 / 2 : ℝ) else (-3 / 4 : ℝ)))
      ((n + 1 : ℕ) : ℝ) (by positivity)⟩

/-- Helper toward Proposition 3.9: one event identifies both entire
intrinsic sequences and all whole-path rescalings jointly. -/
theorem sampledIntrinsicObservables_ae :
    (fun W => ((sampledIntrinsicSequence true W, sampledIntrinsicSequence false W),
      fun n => (sampledIntrinsicScalingPath true n W,
        sampledIntrinsicScalingPath false n W))) =ᵐ[wholePlaneIIDCodeMeasure]
      uibotCodeBusemannObservables := by
  filter_upwards [sampledIntrinsicSequence_identification_ae] with W hW
  apply Prod.ext
  · exact Prod.ext hW.2.2 hW.2.1
  · funext n
    apply Prod.ext <;> apply Subtype.ext <;> funext t
    · simp only [uibotCodeBusemannObservables, sampledIntrinsicScalingPath,
        identifiedLDPScalingPath, ite_true, hW.2.2]
    · simp only [uibotCodeBusemannObservables, sampledIntrinsicScalingPath,
        identifiedSDPScalingPath, Bool.false_eq_true,
        ite_false, hW.2.1]

/-- Helper toward Proposition 3.9: the full joint intrinsic sequence/path
law equals the transported UIBOT observable law, preserving every scale. -/
theorem intrinsicConsumers_joint_law :
    wholePlaneIIDCodeMeasure.map
      (fun W => ((sampledIntrinsicSequence true W, sampledIntrinsicSequence false W),
        fun n => (sampledIntrinsicScalingPath true n W,
          sampledIntrinsicScalingPath false n W))) =
      (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
        Measure D39GeomRootedMapClass).map uibotGeomBusemannObservables := by
  exact (Measure.map_congr sampledIntrinsicObservables_ae).trans
    uibotLaw135_busemann_observables_law.symm

private theorem scaling_path_ae (longest : Bool) (n : ℕ) :
    sampledIntrinsicScalingPath longest n =ᵐ[wholePlaneIIDCodeMeasure]
      (if longest then identifiedLDPScalingPath n else identifiedSDPScalingPath n) := by
  filter_upwards [sampledIntrinsicObservables_ae] with W hW
  cases longest
  · exact congrArg (fun y => (y.2 n).2) hW
  · exact congrArg (fun y => (y.2 n).1) hW

/-- Helper toward Proposition 3.9: the whole-path law of the random
intrinsic sequence, with almost-everywhere measurability proved by identification. -/
@[expose] def sampledIntrinsicScalingLaw (longest : Bool) (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨wholePlaneIIDCodeMeasure.map (sampledIntrinsicScalingPath longest n),
    (Measure.isProbabilityMeasure_map_iff (by
      have hm : AEMeasurable
          (if longest then identifiedLDPScalingPath n else identifiedSDPScalingPath n)
          wholePlaneIIDCodeMeasure := by
        cases longest
        · exact aemeasurable_identifiedSDPScalingPath n
        · exact aemeasurable_identifiedLDPScalingPath n
      exact hm.congr (scaling_path_ae longest n).symm)).2 inferInstance⟩

/-- Helper toward Proposition 3.9: the intrinsic scaling law is exactly
the installed transported UIBOT whole-path law at every positive scale. -/
theorem intrinsicConsumers_scaling_law_eq (longest : Bool) (n : ℕ) :
    sampledIntrinsicScalingLaw longest n = uibotLaw135ScalingLaw longest n := by
  apply ProbabilityMeasure.toMeasure_injective
  change wholePlaneIIDCodeMeasure.map (sampledIntrinsicScalingPath longest n) =
    (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass).map
      (fun z => if longest then ((uibotGeomBusemannObservables z).2 n).1
        else ((uibotGeomBusemannObservables z).2 n).2)
  have hm : Measurable
      (fun z => if longest then ((uibotGeomBusemannObservables z).2 n).1
        else ((uibotGeomBusemannObservables z).2 n).2) := by
    cases longest
    · exact (((measurable_pi_apply n).comp measurable_uibotGeomBusemannObservables.snd).snd)
    · exact (((measurable_pi_apply n).comp measurable_uibotGeomBusemannObservables.snd).fst)
  rw [uibotLaw135_observable_pushforward _ hm]
  apply Measure.map_congr
  filter_upwards [sampledIntrinsicObservables_ae, uibotGeomBusemannObservables_ae]
    with W hi hg
  cases longest
  · exact congrArg (fun y => (y.2 n).2) (hi.trans hg)
  · exact congrArg (fun y => (y.2 n).1) (hi.trans hg)

/-- Helper toward Proposition 3.9: the two full local-Skorokhod convergence
conclusions, with the same constant for both halves in each mode. -/
theorem intrinsicConsumers_convergence :
    ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto (sampledIntrinsicScalingLaw true) atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto (sampledIntrinsicScalingLaw false) atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  have heq (longest : Bool) : sampledIntrinsicScalingLaw longest =
      uibotLaw135ScalingLaw longest := funext (intrinsicConsumers_scaling_law_eq longest)
  rw [heq true, heq false]
  exact uibotLaw135_busemann_convergence

private theorem consumer_probability (longest : Bool) (P : (ℤ → ℤ) → Prop) :
    wholePlaneIIDCodeMeasure.real {W | P (sampledIntrinsicSequence longest W)} =
      wholePlaneIIDCodeMeasure.real {W | P (identifiedConsumerSequence longest W)} := by
  apply measureReal_congr
  filter_upwards [sampled_sequence_ae longest] with W hW
  simp only [hW]

/-- Helper toward Proposition 3.9: the two tail asymptotics in each mode
share one positive constant, including the factor two for the negative half. -/
theorem intrinsicConsumers_tail :
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | ((sampledIntrinsicSequence true W 1 -
          sampledIntrinsicSequence true W 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((sampledIntrinsicSequence true W 0 -
          sampledIntrinsicSequence true W (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ ((sampledIntrinsicSequence false W 1 -
          sampledIntrinsicSequence false W 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((sampledIntrinsicSequence false W 0 -
          sampledIntrinsicSequence false W (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) := by
  have hL1 (x : ℝ) := consumer_probability true
    (fun X => ((X 1 - X 0 : ℤ) : ℝ) ≤ -x)
  have hL0 (x : ℝ) := consumer_probability true
    (fun X => x ≤ |((X 0 - X (-1) : ℤ) : ℝ)|)
  have hS1 (x : ℝ) := consumer_probability false
    (fun X => x ≤ ((X 1 - X 0 : ℤ) : ℝ))
  have hS0 (x : ℝ) := consumer_probability false
    (fun X => x ≤ |((X 0 - X (-1) : ℤ) : ℝ)|)
  simp only [identifiedConsumerSequence, ite_true, Bool.false_eq_true, ite_false]
    at hL1 hL0 hS1 hS0
  constructor
  · obtain ⟨c, hc, h1, h0⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.1.2
    exact ⟨c, hc, by simpa only [hL1] using h1, by simpa only [hL0] using h0⟩
  · obtain ⟨c, hc, h1, h0⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.2.2.1
    exact ⟨c, hc, by simpa only [hS1] using h1, by simpa only [hS0] using h0⟩

/-- Helper toward Proposition 3.9: every integer SDP increment of the
intrinsic sequence is integrable with mean zero. -/
theorem intrinsicConsumers_sdp_mean (k : ℤ) :
    Integrable (fun W => ((sampledIntrinsicSequence false W k -
      sampledIntrinsicSequence false W (k - 1) : ℤ) : ℝ)) wholePlaneIIDCodeMeasure ∧
    (∫ W, ((sampledIntrinsicSequence false W k -
      sampledIntrinsicSequence false W (k - 1) : ℤ) : ℝ) ∂wholePlaneIIDCodeMeasure) = 0 := by
  have heq : (fun W => ((identifiedSDPBusemann W k -
      identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => ((sampledIntrinsicSequence false W k -
        sampledIntrinsicSequence false W (k - 1) : ℤ) : ℝ)) := by
    filter_upwards [sampledIntrinsicSequence_identification_ae] with W hW
    rw [hW.2.1]
  obtain ⟨hi, hm⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.2.2.2 k
  exact ⟨hi.congr heq, (integral_congr_ae heq).symm.trans hm⟩

end DirectedDistances.PaperProofs.Section3
end
