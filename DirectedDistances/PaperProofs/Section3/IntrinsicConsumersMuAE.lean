/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation6
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers14To18
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers38And51And53
import DirectedDistances.Probability.SkorokhodFloorStep










public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open DirectedDistances.Probability MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology Classical

local instance intrinsicConsumersMuAEMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumersMuAEBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "μᵢ" =>
  (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
    Measure D39GeomRootedMapClass)
local notation "Fᵢ" =>
  uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved

private theorem intrinsicConsumersMuAE_transfer
    (P : D39GeomRootedMapClass.{0} → (ℤ → Fin 3) → Prop)
    (hP : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, P (Fᵢ W) W) :
    ∀ᵐ z ∂μᵢ, P z (uibotRecoveredCode z) := by
  rw [← uibotLaw135_recoveredCode_law] at hP
  have hp := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hP
  filter_upwards [hp, uibotClassSeparation6_ae_reconstruction] with z hz hrec
  rwa [hrec] at hz

/-- Helper toward Proposition 3.9: almost every UIBOT class has exactly
one intrinsic future cut in each representative, with uniqueness among all cuts. -/
theorem intrinsicConsumersMuAE_unique_cut :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z → ∃! _C : IntrinsicFutureCut2 A, True := by
  filter_upwards [uibotClassSeparation6_ae_unique_intrinsic_cut] with z hz
  obtain ⟨H, h, hpast, hp, hrep⟩ := hz
  intro A hA
  obtain ⟨_, C, hC, _⟩ := hrep A hA
  exact ⟨C, trivial, fun C' _ => hC.1 C'⟩

/-- Helper toward Proposition 3.9: both modes have a unique entire
normalized intrinsic sequence simultaneously on every representative and cut. -/
theorem intrinsicConsumersMuAE_existsUnique :
    ∀ᵐ z ∂μᵢ, ∀ longest : Bool,
      ∃! X : ℤ → ℤ, IsIntrinsicConsumerSequence longest z X := by
  apply intrinsicConsumersMuAE_transfer (fun z _ => ∀ longest : Bool,
    ∃! X : ℤ → ℤ, IsIntrinsicConsumerSequence longest z X)
  filter_upwards [intrinsicConsumers_existsUnique_ae false,
    intrinsicConsumers_existsUnique_ae true] with W hS hL
  intro longest
  cases longest <;> assumption

/-- Helper toward Proposition 3.9: the class-defined intrinsic Busemann
sequence realizes Theorem 1.4 on each representative's unique cut. The
normalization and eventual finite-distance characterization are included
in the two intrinsic predicates. No sampled word occurs in this statement. -/
theorem intrinsicConsumersMuAE_cut_sequences :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ C : IntrinsicFutureCut2 A,
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
        IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence false z) ∧
        IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence true z) := by
  apply intrinsicConsumersMuAE_transfer (fun z _ => ∀ A : D39DomainRootedMap.{0},
    Quotient.mk d39DomainSetoid A = z →
    (∃! _C : IntrinsicFutureCut2 A, True) ∧
    ∀ C : IntrinsicFutureCut2 A,
      (∃! X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
      (∃! X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
      IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
        (intrinsicConsumerSequence false z) ∧
      IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
        (intrinsicConsumerSequence true z))
  filter_upwards [intrinsicConsumers_cut_sequences_ae] with W hW
  intro A hA
  refine ⟨(hW A hA).1, ?_⟩
  intro C
  obtain ⟨hS, hL, hs, hl⟩ := (hW A hA).2 C
  exact ⟨hS, hL, hs.2, hl.2⟩

/-- Helper toward Proposition 3.9: the class selector is the unique
representative-independent sequence satisfying the full intrinsic characterization. -/
theorem intrinsicConsumersMuAE_sequence_spec :
    ∀ᵐ z ∂μᵢ, ∀ longest : Bool,
      IsIntrinsicConsumerSequence longest z (intrinsicConsumerSequence longest z) ∧
      ∀ X : ℤ → ℤ, IsIntrinsicConsumerSequence longest z X →
        X = intrinsicConsumerSequence longest z := by
  filter_upwards [intrinsicConsumersMuAE_existsUnique] with z hz
  intro longest
  have hex := hz longest
  have hs : IsIntrinsicConsumerSequence longest z (intrinsicConsumerSequence longest z) := by
    simpa only [intrinsicConsumerSequence, dite_eq_left hex] using
      Classical.choose_spec hex.exists
  exact ⟨hs, fun X hX => hex.unique hX hs⟩

/-- Helper toward Proposition 3.9: both intrinsic class sequences agree
with the identified sequences of the class's recovered code on one event. -/
theorem intrinsicConsumersMuAE_recovered_sequences :
    ∀ᵐ z ∂μᵢ,
      intrinsicConsumerSequence false z = identifiedSDPBusemann (uibotRecoveredCode z) ∧
      intrinsicConsumerSequence true z = identifiedLDPBusemann (uibotRecoveredCode z) := by
  apply intrinsicConsumersMuAE_transfer (fun z W =>
    intrinsicConsumerSequence false z = identifiedSDPBusemann W ∧
    intrinsicConsumerSequence true z = identifiedLDPBusemann W)
  filter_upwards [sampledIntrinsicSequence_identification_ae] with W hW
  exact hW.2

/-- Helper toward Proposition 3.9: literal floor rescaling of the intrinsic
class sequence as a whole-line local Skorokhod path, at positive scale `n + 1`. -/
@[expose] def intrinsicConsumerScalingPath (longest : Bool) (n : ℕ)
    (z : D39GeomRootedMapClass.{0}) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (if longest then (-3 / 2 : ℝ) else (-3 / 4 : ℝ)) *
      (intrinsicConsumerSequence longest z ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (intrinsicConsumerSequence longest z j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (if longest then (-3 / 2 : ℝ) else (-3 / 4 : ℝ)))
      ((n + 1 : ℕ) : ℝ) (by positivity)⟩

/-- Helper toward Proposition 3.9: both intrinsic sequences and every
whole-path rescaling form one class observable, preserving their joint law. -/
@[expose] def intrinsicConsumerObservables (z : D39GeomRootedMapClass.{0}) :
    ((ℤ → ℤ) × (ℤ → ℤ)) × (ℕ → WholeLineCadlag × WholeLineCadlag) :=
  ((intrinsicConsumerSequence true z, intrinsicConsumerSequence false z),
    fun n => (intrinsicConsumerScalingPath true n z, intrinsicConsumerScalingPath false n z))

/-- Helper toward Proposition 3.9: the full intrinsic observable equals
the installed Borel sequence/path observable almost everywhere under the UIBOT law. -/
theorem intrinsicConsumersMuAE_observables :
    intrinsicConsumerObservables =ᵐ[μᵢ] uibotGeomBusemannObservables := by
  apply intrinsicConsumersMuAE_transfer (fun z _ =>
    intrinsicConsumerObservables z = uibotGeomBusemannObservables z)
  filter_upwards [sampledIntrinsicObservables_ae, uibotGeomBusemannObservables_ae]
    with W hi hg
  exact hi.trans hg

/-- Helper toward Proposition 3.9: the intrinsic joint observable is
almost-everywhere measurable, by its proved identification with a Borel observable. -/
theorem aemeasurable_intrinsicConsumerObservables :
    AEMeasurable intrinsicConsumerObservables μᵢ :=
  measurable_uibotGeomBusemannObservables.aemeasurable.congr
    intrinsicConsumersMuAE_observables.symm

/-- Helper toward Proposition 3.9: the intrinsic class sequences and all
their rescaled paths have exactly the joint law proved in IntrinsicConsumers14To18. -/
theorem intrinsicConsumersMuAE_joint_law :
    (μᵢ).map intrinsicConsumerObservables = wholePlaneIIDCodeMeasure.map
      (fun W => ((sampledIntrinsicSequence true W, sampledIntrinsicSequence false W),
        fun n => (sampledIntrinsicScalingPath true n W,
          sampledIntrinsicScalingPath false n W))) := by
  exact (Measure.map_congr intrinsicConsumersMuAE_observables).trans
    intrinsicConsumers_joint_law.symm

/-- Helper toward Proposition 3.9: either intrinsic sequence is almost
everywhere measurable under the UIBOT class law. -/
theorem aemeasurable_intrinsicConsumerSequence (longest : Bool) :
    AEMeasurable (intrinsicConsumerSequence longest) μᵢ := by
  cases longest
  · exact aemeasurable_intrinsicConsumerObservables.fst.snd
  · exact aemeasurable_intrinsicConsumerObservables.fst.fst

/-- Helper toward Proposition 3.9: the entire intrinsic sequence has
the sampled intrinsic sequence law, by pushforward along the measurable class map. -/
theorem intrinsicConsumersMuAE_sequence_law (longest : Bool) :
    (μᵢ).map (intrinsicConsumerSequence longest) =
      wholePlaneIIDCodeMeasure.map (sampledIntrinsicSequence longest) := by
  exact AEMeasurable.map_map_of_aemeasurable
    (aemeasurable_intrinsicConsumerSequence longest)
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable

private theorem intrinsicConsumersMuAE_sequence_eq (longest : Bool) :
    intrinsicConsumerSequence longest =ᵐ[μᵢ] uibotQualifier135Busemann longest := by
  filter_upwards [intrinsicConsumersMuAE_observables] with z hz
  cases longest
  · exact congrArg (fun y => y.1.2) hz
  · exact congrArg (fun y => y.1.1) hz

/-- Helper toward Proposition 3.9: each literal rescaled intrinsic path
is almost everywhere measurable under the UIBOT class law. -/
theorem aemeasurable_intrinsicConsumerScalingPath (longest : Bool) (n : ℕ) :
    AEMeasurable (intrinsicConsumerScalingPath longest n) μᵢ := by
  have hm := (measurable_pi_apply n).comp_aemeasurable
    aemeasurable_intrinsicConsumerObservables.snd
  cases longest
  · exact hm.snd
  · exact hm.fst

/-- Helper toward Proposition 3.9: the probability law of the literal
rescaled intrinsic class sequence in the whole-line local Skorokhod space. -/
@[expose] def intrinsicConsumerScalingLaw (longest : Bool) (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨(μᵢ).map (intrinsicConsumerScalingPath longest n),
    (Measure.isProbabilityMeasure_map_iff
      (aemeasurable_intrinsicConsumerScalingPath longest n)).2 inferInstance⟩

/-- Helper toward Proposition 3.9: every intrinsic class scaling law
equals the sampled scaling law established in IntrinsicConsumers14To18. -/
theorem intrinsicConsumersMuAE_scaling_law_eq (longest : Bool) (n : ℕ) :
    intrinsicConsumerScalingLaw longest n = sampledIntrinsicScalingLaw longest n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact AEMeasurable.map_map_of_aemeasurable
    (aemeasurable_intrinsicConsumerScalingPath longest n)
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable

/-- Helper toward Proposition 3.9: both intrinsic class sequences have
Theorem 1.6's full local-Skorokhod limits, with one constant for each pair
of independent limiting halves. -/
theorem intrinsicConsumersMuAE_convergence :
    ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto (intrinsicConsumerScalingLaw true) atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto (intrinsicConsumerScalingLaw false) atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  have heq (longest : Bool) : intrinsicConsumerScalingLaw longest =
      sampledIntrinsicScalingLaw longest := funext (intrinsicConsumersMuAE_scaling_law_eq longest)
  rw [heq true, heq false]
  exact intrinsicConsumers_convergence

private theorem intrinsicConsumersMuAE_identDistrib_congr
    {f g f' g' : D39GeomRootedMapClass.{0} → ℤ}
    (h : IdentDistrib f g μᵢ μᵢ) (hf : f =ᵐ[μᵢ] f') (hg : g =ᵐ[μᵢ] g') :
    IdentDistrib f' g' μᵢ μᵢ :=
  ⟨h.aemeasurable_fst.congr hf, h.aemeasurable_snd.congr hg,
    (Measure.map_congr hf).symm.trans (h.map_eq.trans (Measure.map_congr hg))⟩

/-- Helper toward Proposition 3.9: the intrinsic class sequence has
independent increments, stationary positive and negative halves, simultaneous
positive-index bounds, and negative-index symmetry as in Theorem 1.7. -/
theorem intrinsicConsumersMuAE_increment_law (longest : Bool) :
    iIndepFun (fun k z => intrinsicConsumerSequence longest z k -
      intrinsicConsumerSequence longest z (k - 1)) μᵢ ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun z => intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1))
      (fun z => intrinsicConsumerSequence longest z 1 -
        intrinsicConsumerSequence longest z (1 - 1)) μᵢ μᵢ) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1))
      (fun z => intrinsicConsumerSequence longest z 0 -
        intrinsicConsumerSequence longest z (0 - 1)) μᵢ μᵢ) ∧
    (∀ᵐ z ∂μᵢ, ∀ k : ℤ, 1 ≤ k →
      if longest then intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1) ≤ -1
      else -1 ≤ intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1))
      (fun z => intrinsicConsumerSequence longest z (k - 1) -
        intrinsicConsumerSequence longest z k) μᵢ μᵢ) := by
  obtain ⟨hind, hpos, hneg, hbound, hsym⟩ := uibotLaw135_busemann_property longest
  have heq (k : ℤ) :
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1)) =ᵐ[μᵢ]
      (fun z => intrinsicConsumerSequence longest z k -
        intrinsicConsumerSequence longest z (k - 1)) :=
    (intrinsicConsumersMuAE_sequence_eq longest).symm.mono fun z h =>
      congrArg (fun X => X k - X (k - 1)) h
  refine ⟨hind.congr heq, fun k hk => intrinsicConsumersMuAE_identDistrib_congr (hpos k hk)
    (heq k) (heq 1), fun k hk => intrinsicConsumersMuAE_identDistrib_congr (hneg k hk)
    (heq k) (heq 0), ?_, ?_⟩
  · filter_upwards [hbound, intrinsicConsumersMuAE_sequence_eq longest] with z hb he
    simpa only [he] using hb
  · intro k hk
    exact intrinsicConsumersMuAE_identDistrib_congr (hsym k hk) (heq k)
      ((intrinsicConsumersMuAE_sequence_eq longest).symm.mono fun z h =>
        congrArg (fun X => X (k - 1) - X k) h)

private theorem intrinsicConsumersMuAE_probability (longest : Bool)
    (P : (ℤ → ℤ) → Prop) :
    (μᵢ).real {z | P (intrinsicConsumerSequence longest z)} =
      (μᵢ).real {z | P (uibotQualifier135Busemann longest z)} := by
  apply measureReal_congr
  filter_upwards [intrinsicConsumersMuAE_sequence_eq longest] with z hz
  simp only [hz]

/-- Helper toward Proposition 3.9: the intrinsic class sequences have
Theorem 1.8's four tail asymptotics with one positive constant in each mode
and the same constant, multiplied by two, on the negative half. -/
theorem intrinsicConsumersMuAE_tail :
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => (μᵢ).real
        {z | ((intrinsicConsumerSequence true z 1 -
          intrinsicConsumerSequence true z 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => (μᵢ).real
        {z | x ≤ |((intrinsicConsumerSequence true z 0 -
          intrinsicConsumerSequence true z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => (μᵢ).real
        {z | x ≤ ((intrinsicConsumerSequence false z 1 -
          intrinsicConsumerSequence false z 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => (μᵢ).real
        {z | x ≤ |((intrinsicConsumerSequence false z 0 -
          intrinsicConsumerSequence false z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) := by
  have hL1 (x : ℝ) := intrinsicConsumersMuAE_probability true
    (fun X => ((X 1 - X 0 : ℤ) : ℝ) ≤ -x)
  have hL0 (x : ℝ) := intrinsicConsumersMuAE_probability true
    (fun X => x ≤ |((X 0 - X (-1) : ℤ) : ℝ)|)
  have hS1 (x : ℝ) := intrinsicConsumersMuAE_probability false
    (fun X => x ≤ ((X 1 - X 0 : ℤ) : ℝ))
  have hS0 (x : ℝ) := intrinsicConsumersMuAE_probability false
    (fun X => x ≤ |((X 0 - X (-1) : ℤ) : ℝ)|)
  constructor
  · obtain ⟨c, hc, h1, h0⟩ := uibotLaw135_busemann_tail.1
    exact ⟨c, hc, by simpa only [hL1] using h1, by simpa only [hL0] using h0⟩
  · obtain ⟨c, hc, h1, h0⟩ := uibotLaw135_busemann_tail.2
    exact ⟨c, hc, by simpa only [hS1] using h1, by simpa only [hS0] using h0⟩

/-- Helper toward Proposition 3.9: every integer SDP increment of the
intrinsic class sequence is integrable and has expectation zero under the UIBOT law. -/
theorem intrinsicConsumersMuAE_sdp_mean (k : ℤ) :
    Integrable (fun z => ((intrinsicConsumerSequence false z k -
      intrinsicConsumerSequence false z (k - 1) : ℤ) : ℝ)) μᵢ ∧
    (∫ z, ((intrinsicConsumerSequence false z k -
      intrinsicConsumerSequence false z (k - 1) : ℤ) : ℝ) ∂μᵢ) = 0 := by
  have heq : (fun z => ((uibotQualifier135Busemann false z k -
      uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ)) =ᵐ[μᵢ]
      (fun z => ((intrinsicConsumerSequence false z k -
        intrinsicConsumerSequence false z (k - 1) : ℤ) : ℝ)) := by
    filter_upwards [intrinsicConsumersMuAE_sequence_eq false] with z hz
    rw [hz]
  obtain ⟨hi, hm⟩ := uibotLaw135_sdp_mean k
  exact ⟨hi.congr heq, (integral_congr_ae heq).symm.trans hm⟩

/-- Helper toward Proposition 3.9: almost every UIBOT class satisfies
Lemma 3.10 for every representative and every source isomorphism of the
recovered code, and Lemma 5.3 on its unique intrinsic cut. -/
theorem intrinsicConsumersMuAE_boundary_cut_vertices :
    ∀ᵐ z ∂μᵢ,
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∃! C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          IntrinsicConsumerCutVertices A C ∧
          ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
            (uibotWholePlaneSourceRoot W H G) A.map A.root,
            IntrinsicConsumerBoundary W A I.vertexEquiv I.edgeEquiv := by
  apply intrinsicConsumersMuAE_transfer (fun z W =>
    ∃ (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
      Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
      ∃! C : IntrinsicFutureCut2 A,
        (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
        IntrinsicConsumerCutVertices A C ∧
        ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root,
          IntrinsicConsumerBoundary W A I.vertexEquiv I.edgeEquiv)
  filter_upwards [intrinsicConsumers38And51And53_sample] with W hW
  obtain ⟨H, h, hpast, hp, hrep⟩ := hW
  refine ⟨H, h, hpast, hp, ?_⟩
  dsimp only
  intro A hA
  obtain ⟨hI, C, hC, _⟩ := hrep A hA
  exact ⟨hI, C, ⟨hC.1, hC.2.1, fun I => (hC.2.2 I).1⟩,
    fun C' _ => hC.1 C'⟩

/-- Helper toward Proposition 3.9: Lemma 5.3 holds for every intrinsic
cut of every representative of almost every UIBOT class. -/
theorem intrinsicConsumersMuAE_cut_vertices :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
      ∀ C : IntrinsicFutureCut2 A, IntrinsicConsumerCutVertices A C := by
  filter_upwards [intrinsicConsumersMuAE_boundary_cut_vertices] with z hz
  obtain ⟨H, h, hpast, hp, hrep⟩ := hz
  intro A hA C
  obtain ⟨_, C₀, hC₀, _⟩ := hrep A hA
  rw [hC₀.1 C]
  exact hC₀.2.1

end DirectedDistances.PaperProofs.Section3
end
