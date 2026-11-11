/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart8
public import DirectedDistances.Paper.Section1.BusemannProperty
public import DirectedDistances.Paper.Section1.BusemannTail
public import DirectedDistances.Paper.Section1.BusemannConvergence
public import DirectedDistances.Paper.Section1.FutureMap
public import DirectedDistances.Paper.Section1.BusemannM0
public import DirectedDistances.Paper.Section3.UIBOTBoundary
public import DirectedDistances.Paper.Section5.InftyCut
public import DirectedDistances.Paper.Section5.GeoInfty
public import DirectedDistances.Paper.Section5.BusemannCls
public import DirectedDistances.Paper.Section5.FutureMapLaw
public import DirectedDistances.Paper.Section5.GeoInftyInd
public import DirectedDistances.Paper.Section5.GeoSlice
public import DirectedDistances.Paper.Section5.DirectedContain
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued
import Mathlib.Probability.Independence.InfinitePi





public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.Probability DirectedDistances.PaperProofs.Section1
open DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.Section7
open DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section5.Xdp
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology Classical

local instance uibotQualifierSections135MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotQualifierSections135BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: the pushforward law used throughout these helpers. -/
@[expose] def uibotQualifier135Measure : Measure D39GeomRootedMapClass.{0} :=
  wholePlaneIIDCodeMeasure.map
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)

local instance uibotQualifierSections135Probability :
    IsProbabilityMeasure uibotQualifier135Measure := by
  unfold uibotQualifier135Measure
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_uibotMeasurableWholePlaneClassMap _).aemeasurable).mpr inferInstance

private theorem factor_law {α : Type*} [MeasurableSpace α]
    (Y : D39GeomRootedMapClass.{0} → α) (hY : Measurable Y)
    (X : (ℤ → Fin 3) → α)
    (h : X =ᵐ[wholePlaneIIDCodeMeasure] Y ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) :
    uibotQualifier135Measure.map Y = wholePlaneIIDCodeMeasure.map X := by
  rw [uibotQualifier135Measure, Measure.map_map hY
    (measurable_uibotMeasurableWholePlaneClassMap _)]
  exact Measure.map_congr h.symm

/-- Helper toward Proposition 3.9: recovery has exactly the iid code law. -/
theorem uibotQualifier135_recoveredCode_law :
    uibotQualifier135Measure.map uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
  have h : id =ᵐ[wholePlaneIIDCodeMeasure] uibotRecoveredCode ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
    filter_upwards [uibotRecoveredCode_ae] with W hW
    exact hW.symm
  exact (factor_law _ measurable_uibotRecoveredCode _ h).trans Measure.map_id

private theorem recovered_ae (Q : (ℤ → Fin 3) → Prop)
    (h : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W) :
    ∀ᵐ z ∂uibotQualifier135Measure, Q (uibotRecoveredCode z) := by
  rw [← uibotQualifier135_recoveredCode_law] at h
  exact ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h

private theorem recovered_observable_ae {α : Type*} [MeasurableSpace α]
    (X : (ℤ → Fin 3) → α) (hX : AEMeasurable X wholePlaneIIDCodeMeasure) :
    ∀ᵐ z ∂uibotQualifier135Measure,
      X (uibotRecoveredCode z) = uibotRecoveredObservable X hX z :=
  recovered_ae _ hX.ae_eq_mk

private theorem borel_recovered_ae (Q : (ℤ → Fin 3) → Prop)
    (h : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W) :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S → Q (uibotRecoveredCode z)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  let N := toMeasurable wholePlaneIIDCodeMeasure {W | ¬ Q W}
  have hN : wholePlaneIIDCodeMeasure N = 0 :=
    (measure_toMeasurable _).trans h
  have hn : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∉ N := by
    change wholePlaneIIDCodeMeasure (Nᶜ)ᶜ = 0
    rw [compl_compl]
    exact hN
  refine ⟨{z | uibotRecoveredCode z ∉ N},
    ((measurableSet_toMeasurable _ _).preimage measurable_uibotRecoveredCode).compl,
    recovered_ae _ hn, ?_, ?_⟩
  · intro z hz
    by_contra hbad
    exact hz (subset_toMeasurable _ _ hbad)
  · filter_upwards [h, hn, uibotRecoveredCode_ae] with W hW hnW hc
    rw [hc]
    exact iff_of_true hW hnW

private theorem factor_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : D39GeomRootedMapClass.{0} → α) (Z : D39GeomRootedMapClass.{0} → β)
    (hY : Measurable Y) (hZ : Measurable Z)
    (X : (ℤ → Fin 3) → α) (T : (ℤ → Fin 3) → β)
    (hX : AEMeasurable X wholePlaneIIDCodeMeasure)
    (hT : AEMeasurable T wholePlaneIIDCodeMeasure)
    (heq : (fun W => (X W, T W)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z => (Y z, Z z)) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
    (hind : IndepFun X T wholePlaneIIDCodeMeasure) :
    IndepFun Y Z uibotQualifier135Measure := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mpr
  rw [factor_law _ (hY.prodMk hZ) _ heq,
    factor_law _ hY _ (heq.mono fun _ h => congrArg Prod.fst h),
    factor_law _ hZ _ (heq.mono fun _ h => congrArg Prod.snd h)]
  exact hind.map_prod_eq_prod_map_map hX hT

/-- Helper toward Proposition 3.9: Proposition 5.1's complete generating-code
law transports to the geometric law at every integer shift. -/
theorem uibotQualifier135_future_map_law :
    (∀ n : ℤ, IndepFun
      (fun z => (uibotGeomFutureObservables z n).1.1)
      (fun z => (uibotGeomFutureObservables z n).1.2) uibotQualifier135Measure) ∧
    (∀ n : ℤ, uibotQualifier135Measure.map
      (fun z => (uibotGeomFutureObservables z n).1.1) =
        iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) := by
  have heq (n : ℤ) := uibotGeomFutureObservables_ae.mono
    (fun W h => congrArg (fun y => (y n).1) h)
  constructor
  · intro n
    exact factor_indep _ _
      (((measurable_pi_apply n).comp measurable_uibotGeomFutureObservables).fst.fst)
      (((measurable_pi_apply n).comp measurable_uibotGeomFutureObservables).fst.snd)
      _ _ (aemeasurable_futureMapShiftedHatCodes n).1
      (aemeasurable_futureMapShiftedHatCodes n).2 (heq n)
      (DirectedDistances.Paper.Section5.future_map_law.1 n)
  · intro n
    exact (factor_law _
      (((measurable_pi_apply n).comp measurable_uibotGeomFutureObservables).fst.fst)
      _ ((heq n).mono fun _ h => congrArg Prod.fst h)).trans
        (DirectedDistances.Paper.Section5.future_map_law.2.1 n)

/-- Helper toward Proposition 3.9: Proposition 5.1's rooted-map clauses hold
under the pushforward law using the single Borel recovered code, simultaneously
at all shifts and with the primed missing-root convention unchanged. -/
theorem uibotQualifier135_future_rooted_maps :
    ∀ᵐ z ∂uibotQualifier135Measure, ∀ n : ℤ,
      let W := uibotRecoveredCode z
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
          (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          (uibotGeomFutureObservables z n).1.1 = hatCodes u h ∧
          (uibotGeomFutureObservables z n).1.2 = primedCode (primedSimInput u) h ∧
          hatRootedMapClause u h hfin_hat ∧ primedRootedMapClause u h hfin_primed hb := by
  have h := recovered_ae _ DirectedDistances.Paper.Section5.future_map_law.2.2
  have heq : ∀ᵐ z ∂uibotQualifier135Measure,
      uibotCodeFutureObservables (uibotRecoveredCode z) = uibotGeomFutureObservables z := by
    exact recovered_observable_ae _ aemeasurable_uibotCodeFutureObservables
  filter_upwards [h, heq] with z hz heq
  intro n
  obtain ⟨hu, h, hh, hp, hb, hhat, hprime, hmaps⟩ := hz n
  refine ⟨hu, h, hh, hp, hb, ?_, ?_, hmaps⟩
  · exact (congrArg (fun y => (y n).1.1) heq).symm.trans hhat
  · exact (congrArg (fun y => (y n).1.2) heq).symm.trans hprime

/-- Helper toward Proposition 3.9: Lemma 5.5's side classes, independence,
and both half-line stationary laws under the geometric pushforward measure. -/
theorem uibotQualifier135_geo_infty_ind (default : GeometricSideClass)
    (x : XDP) (k : ℤ) :
    ((fun z => (uibotGeomSideSliceObservables z x k).1.1) =ᵐ[uibotQualifier135Measure]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.1)) ∧
    ((fun z => (uibotGeomSideSliceObservables z x k).1.2) =ᵐ[uibotQualifier135Measure]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.2)) ∧
    IndepFun
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1)
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2)
      uibotQualifier135Measure ∧
    (0 ≤ k → uibotQualifier135Measure.map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2) =
      uibotQualifier135Measure.map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.2)) ∧
    (k ≤ 0 → uibotQualifier135Measure.map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1) =
      uibotQualifier135Measure.map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.1)) := by
  obtain ⟨hL, hR, hind, hpos, hneg⟩ :=
    DirectedDistances.Paper.Section5.lem_geo_infty_ind default x k
  have hmL (j : ℤ) : Measurable
      (fun z => (uibotGeomSideSliceObservables z x j).1.1) :=
    (((measurable_pi_apply j).comp
      ((measurable_pi_apply x).comp measurable_uibotGeomSideSliceObservables)).fst.fst)
  have hmR (j : ℤ) : Measurable
      (fun z => (uibotGeomSideSliceObservables z x j).1.2) :=
    (((measurable_pi_apply j).comp
      ((measurable_pi_apply x).comp measurable_uibotGeomSideSliceObservables)).fst.snd)
  have heqL (j : ℤ) : lemma55LeftSideClassOption x j =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z => (uibotGeomSideSliceObservables z x j).1.1) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
    uibotGeomSideSliceObservables_ae.mono
      (fun W h => congrArg (fun y => (y x j).1.1) h)
  have heqR (j : ℤ) : lemma55RightSideClassOption2 x j =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z => (uibotGeomSideSliceObservables z x j).1.2) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
    uibotGeomSideSliceObservables_ae.mono
      (fun W h => congrArg (fun y => (y x j).1.2) h)
  have hm := measurable_forgetMarksOptionClassValue default
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hp : ∀ᵐ z ∂uibotQualifier135Measure,
        (uibotGeomSideSliceObservables z x k).1.1 ≠ none := by
      apply (ae_map_iff (measurable_uibotMeasurableWholePlaneClassMap _).aemeasurable
        ((measurableSet_optionGeometricSideClass_none.preimage (hmL k)).compl)).mpr
      filter_upwards [hL, heqL k] with W hp he
      dsimp only [Function.comp_apply] at he
      change (uibotGeomSideSliceObservables _ x k).1.1 ≠ none
      rw [← he, hp]
      exact Option.some_ne_none _
    filter_upwards [hp] with z hz
    cases he : (uibotGeomSideSliceObservables z x k).1.1 with
    | none => exact False.elim (hz he)
    | some c => simp only [lemma55OptionClassValue, Option.getD_some]
  · have hp : ∀ᵐ z ∂uibotQualifier135Measure,
        (uibotGeomSideSliceObservables z x k).1.2 ≠ none := by
      apply (ae_map_iff (measurable_uibotMeasurableWholePlaneClassMap _).aemeasurable
        ((measurableSet_optionGeometricSideClass_none.preimage (hmR k)).compl)).mpr
      filter_upwards [hR, heqR k] with W hp he
      dsimp only [Function.comp_apply] at he
      change (uibotGeomSideSliceObservables _ x k).1.2 ≠ none
      rw [← he, hp]
      exact Option.some_ne_none _
    filter_upwards [hp] with z hz
    cases he : (uibotGeomSideSliceObservables z x k).1.2 with
    | none => exact False.elim (hz he)
    | some c => simp only [lemma55OptionClassValue, Option.getD_some]
  · apply factor_indep _ _ (hm.comp (hmL k)) (hm.comp (hmR k)) _ _
      (hm.comp_aemeasurable (aemeasurable_lemma55LeftSideClassOption_all x k))
      _ _ hind
    · exact (hm.comp (hmR k)).aemeasurable.comp_aemeasurable
        (measurable_uibotMeasurableWholePlaneClassMap _).aemeasurable |>.congr
          ((heqR k).symm.mono fun _ h => congrArg (forgetMarksOptionClassValue default) h)
    · filter_upwards [heqL k, heqR k] with W hL hR
      exact Prod.ext (congrArg (forgetMarksOptionClassValue default) hL)
        (congrArg (forgetMarksOptionClassValue default) hR)
  · intro hk
    exact (factor_law _ (hm.comp (hmR k)) _
      ((heqR k).mono fun _ h => congrArg (forgetMarksOptionClassValue default) h)).trans
      ((hpos hk).trans (factor_law _ (hm.comp (hmR 0)) _
      ((heqR 0).mono fun _ h => congrArg (forgetMarksOptionClassValue default) h)).symm)
  · intro hk
    exact (factor_law _ (hm.comp (hmL k)) _
      ((heqL k).mono fun _ h => congrArg (forgetMarksOptionClassValue default) h)).trans
      ((hneg hk).trans (factor_law _ (hm.comp (hmL 0)) _
      ((heqL 0).mono fun _ h => congrArg (forgetMarksOptionClassValue default) h)).symm)

/-- Helper toward Proposition 3.9: select a full Borel Busemann sequence;
`true` is LDP and `false` is SDP. -/
@[expose] def uibotQualifier135Busemann (longest : Bool)
    (z : D39GeomRootedMapClass.{0}) : ℤ → ℤ :=
  if longest then (uibotGeomBusemannObservables z).1.1
  else (uibotGeomBusemannObservables z).1.2

private def codeBusemann (longest : Bool) (W : ℤ → Fin 3) : ℤ → ℤ :=
  if longest then identifiedLDPBusemann W else identifiedSDPBusemann W

private theorem measurable_busemann (longest : Bool) :
    Measurable (uibotQualifier135Busemann longest) := by
  cases longest
  · exact measurable_uibotGeomBusemannObservables.fst.snd
  · exact measurable_uibotGeomBusemannObservables.fst.fst

private theorem busemann_ae (longest : Bool) :
    codeBusemann longest =ᵐ[wholePlaneIIDCodeMeasure]
      uibotQualifier135Busemann longest ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  filter_upwards [uibotGeomBusemannObservables_ae] with W hW
  cases longest
  · exact congrArg (fun y => y.1.2) hW
  · exact congrArg (fun y => y.1.1) hW

private theorem measurable_increment (longest : Bool) (k : ℤ) :
    Measurable (fun z => uibotQualifier135Busemann longest z k -
      uibotQualifier135Busemann longest z (k - 1)) :=
  ((measurable_pi_apply k).comp (measurable_busemann longest)).sub
    ((measurable_pi_apply (k - 1)).comp (measurable_busemann longest))

private theorem increment_ae (longest : Bool) (k : ℤ) :
    (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
      =ᵐ[wholePlaneIIDCodeMeasure]
    (fun z => uibotQualifier135Busemann longest z k -
      uibotQualifier135Busemann longest z (k - 1)) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  (busemann_ae longest).mono fun _ h => congrArg (fun f => f k - f (k - 1)) h

private theorem factor_iindep {ι α : Type*} [Countable ι] [MeasurableSpace α]
    (Y : ι → D39GeomRootedMapClass.{0} → α) (hY : ∀ i, Measurable (Y i))
    (X : ι → (ℤ → Fin 3) → α)
    (heq : ∀ i, X i =ᵐ[wholePlaneIIDCodeMeasure] Y i ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
    (hX : ∀ i, AEMeasurable (X i) wholePlaneIIDCodeMeasure)
    (hind : iIndepFun X wholePlaneIIDCodeMeasure) :
    iIndepFun Y uibotQualifier135Measure := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (hY i).aemeasurable)).mpr
  have hj : (fun W i => X i W) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z i => Y i z) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
    filter_upwards [ae_all_iff.mpr heq] with W hW
    exact funext hW
  rw [factor_law _ (Measurable.of_eval hY) _ hj,
    (iIndepFun_iff_map_fun_eq_infinitePi_map₀' hX).mp hind]
  congr 1
  funext i
  exact (factor_law _ (hY i) _ (heq i)).symm

private theorem factor_identDistrib {α : Type*} [MeasurableSpace α]
    (Y Z : D39GeomRootedMapClass.{0} → α) (hY : Measurable Y) (hZ : Measurable Z)
    (X T : (ℤ → Fin 3) → α)
    (heqX : X =ᵐ[wholePlaneIIDCodeMeasure] Y ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
    (heqT : T =ᵐ[wholePlaneIIDCodeMeasure] Z ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
    (h : IdentDistrib X T wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) :
    IdentDistrib Y Z uibotQualifier135Measure uibotQualifier135Measure :=
  ⟨hY.aemeasurable, hZ.aemeasurable,
    (factor_law _ hY _ heqX).trans (h.map_eq.trans (factor_law _ hZ _ heqT).symm)⟩

/-- Helper toward Proposition 3.9: all four increment-law clauses of
Theorem 1.7, for each mode under the geometric law. The positive-index bound
is simultaneous in the entire half-line. -/
theorem uibotQualifier135_busemann_property (longest : Bool) :
    iIndepFun (fun k z => uibotQualifier135Busemann longest z k -
      uibotQualifier135Busemann longest z (k - 1)) uibotQualifier135Measure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z 1 -
        uibotQualifier135Busemann longest z (1 - 1))
      uibotQualifier135Measure uibotQualifier135Measure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z 0 -
        uibotQualifier135Busemann longest z (0 - 1))
      uibotQualifier135Measure uibotQualifier135Measure) ∧
    (∀ᵐ z ∂uibotQualifier135Measure, ∀ k : ℤ, 1 ≤ k →
      if longest then uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1) ≤ -1
      else -1 ≤ uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z (k - 1) -
        uibotQualifier135Busemann longest z k)
      uibotQualifier135Measure uibotQualifier135Measure) := by
  have hcode :
      iIndepFun (fun k W => codeBusemann longest W k - codeBusemann longest W (k - 1))
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → IdentDistrib
        (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
        (fun W => codeBusemann longest W 1 - codeBusemann longest W (1 - 1))
        wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
      (∀ k : ℤ, k ≤ 0 → IdentDistrib
        (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
        (fun W => codeBusemann longest W 0 - codeBusemann longest W (0 - 1))
        wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
        if longest then codeBusemann longest W k - codeBusemann longest W (k - 1) ≤ -1
        else -1 ≤ codeBusemann longest W k - codeBusemann longest W (k - 1)) ∧
      (∀ k : ℤ, k ≤ 0 → IdentDistrib
        (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
        (fun W => codeBusemann longest W (k - 1) - codeBusemann longest W k)
        wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) := by
    cases longest
    · exact DirectedDistances.Paper.Section1.thm_busemann_property.2.2
    · exact DirectedDistances.Paper.Section1.thm_busemann_property.1.2
  obtain ⟨hind, hpos, hneg, hbound, hsym⟩ := hcode
  have hm (k : ℤ) : AEMeasurable
      (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
      wholePlaneIIDCodeMeasure := by
    cases longest
    · exact ((aemeasurable_identifiedSDPBusemann.eval k).sub
        (aemeasurable_identifiedSDPBusemann.eval (k - 1)))
    · exact ((aemeasurable_identifiedLDPBusemann.eval k).sub
        (aemeasurable_identifiedLDPBusemann.eval (k - 1)))
  refine ⟨factor_iindep _ (measurable_increment longest) _ (increment_ae longest) hm hind,
    ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact factor_identDistrib _ _ (measurable_increment longest k)
      (measurable_increment longest 1) _ _ (increment_ae longest k)
      (increment_ae longest 1) (hpos k hk)
  · intro k hk
    exact factor_identDistrib _ _ (measurable_increment longest k)
      (measurable_increment longest 0) _ _ (increment_ae longest k)
      (increment_ae longest 0) (hneg k hk)
  · apply (ae_map_iff (measurable_uibotMeasurableWholePlaneClassMap _).aemeasurable
      (by
        simp only [Set.ofPred_forall]
        apply MeasurableSet.iInter
        intro k
        apply MeasurableSet.iInter
        intro _
        cases longest
        · exact measurableSet_le measurable_const (measurable_increment false k)
        · exact measurableSet_le (measurable_increment true k) measurable_const)).mpr
    filter_upwards [hbound, busemann_ae longest] with W hb he
    dsimp only [Function.comp_apply] at he
    rw [← he]
    exact hb
  · intro k hk
    exact factor_identDistrib _ _ (measurable_increment longest k)
      (((measurable_pi_apply (k - 1)).comp (measurable_busemann longest)).sub
        ((measurable_pi_apply k).comp (measurable_busemann longest))) _ _
      (increment_ae longest k)
      ((busemann_ae longest).mono fun W h => congrArg (fun f => f (k - 1) - f k) h)
      (hsym k hk)

/-- Helper toward Proposition 3.9: both Borel sequences have the full
eventual-distance characterization on the same recovered cut, before any
endpoint sequence is chosen. This is the identification clause for 1.6–1.8
and a characterization helper for 1.4, not its complete cut identification. -/
theorem uibotQualifier135_busemann_characterization :
    ∀ᵐ z ∂uibotQualifier135Measure,
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (uibotQualifier135Busemann true z) ∧
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (uibotQualifier135Busemann false z) ∧
        ∀ n : ℕ, (uibotGeomBusemannObservables z).2 n =
          (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W) := by
  have hex := recovered_ae _ m0Cut_busemann_identified_ae
  have hL := recovered_ae _ identifiedLDPBusemann_characterization_ae
  have hS := recovered_ae _ identifiedSDPBusemann_characterization_ae
  have heq := recovered_observable_ae _ aemeasurable_uibotCodeBusemannObservables
  filter_upwards [hex, hL, hS, heq] with z hz hl hs he
  obtain ⟨H, h, hLL, _⟩ := hz
  refine ⟨H, h, hLL, ?_, ?_, ?_⟩
  · have hB := congrArg (fun y => y.1.1) he
    change identifiedLDPBusemann (uibotRecoveredCode z) =
      uibotQualifier135Busemann true z at hB
    rw [← hB]
    exact hl H h hLL
  · have hB := congrArg (fun y => y.1.2) he
    change identifiedSDPBusemann (uibotRecoveredCode z) =
      uibotQualifier135Busemann false z at hB
    rw [← hB]
    exact hs H h hLL
  · intro n
    exact (congrArg (fun y => y.2 n) he).symm

private theorem increment_probability (longest : Bool) (k : ℤ) (S : Set ℤ) :
    uibotQualifier135Measure.real
      {z | uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1) ∈ S} =
    wholePlaneIIDCodeMeasure.real
      {W | codeBusemann longest W k - codeBusemann longest W (k - 1) ∈ S} := by
  have hlaw := factor_law _ (measurable_increment longest k) _ (increment_ae longest k)
  have hcode : AEMeasurable
      (fun W => codeBusemann longest W k - codeBusemann longest W (k - 1))
      wholePlaneIIDCodeMeasure :=
    ((measurable_increment longest k).comp
      (measurable_uibotMeasurableWholePlaneClassMap _)).aemeasurable.congr
        (increment_ae longest k).symm
  have hs : MeasurableSet S := (Set.to_countable S).measurableSet
  exact (map_measureReal_apply (measurable_increment longest k) hs).symm.trans
    ((congrArg (fun μ : Measure ℤ => μ.real S) hlaw).trans
      (map_measureReal_apply_of_aemeasurable hcode hs))

/-- Helper toward Proposition 3.9: Theorem 1.8's two asymptotic tails per
mode, with one positive constant shared by both tails of that mode. -/
theorem uibotQualifier135_busemann_tail :
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => uibotQualifier135Measure.real
        {z | ((uibotQualifier135Busemann true z 1 -
          uibotQualifier135Busemann true z 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => uibotQualifier135Measure.real
        {z | x ≤ |((uibotQualifier135Busemann true z 0 -
          uibotQualifier135Busemann true z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => uibotQualifier135Measure.real
        {z | x ≤ ((uibotQualifier135Busemann false z 1 -
          uibotQualifier135Busemann false z 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => uibotQualifier135Measure.real
        {z | x ≤ |((uibotQualifier135Busemann false z 0 -
          uibotQualifier135Busemann false z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) := by
  have hL (x : ℝ) := increment_probability true 1 {j : ℤ | (j : ℝ) ≤ -x}
  have hL' (x : ℝ) := increment_probability true 0 {j : ℤ | x ≤ |(j : ℝ)|}
  have hS (x : ℝ) := increment_probability false 1 {j : ℤ | x ≤ (j : ℝ)}
  have hS' (x : ℝ) := increment_probability false 0 {j : ℤ | x ≤ |(j : ℝ)|}
  simp only [Int.reduceSub, codeBusemann, ite_true, Bool.false_eq_true, ite_false,
    Set.mem_ofPred_eq] at hL hL' hS hS'
  constructor
  · obtain ⟨c, hc, ht, ht'⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.1.2
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [hL] using ht
    · simpa only [hL'] using ht'
  · obtain ⟨c, hc, ht, ht'⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.2.2.1
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [hS] using ht
    · simpa only [hS'] using ht'

/-- Helper toward Proposition 3.9: every SDP increment is integrable
and has mean zero under the geometric law, as in Theorem 1.8. -/
theorem uibotQualifier135_sdp_mean (k : ℤ) :
    Integrable (fun z => ((uibotQualifier135Busemann false z k -
      uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ)) uibotQualifier135Measure ∧
    (∫ z, ((uibotQualifier135Busemann false z k -
      uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ) ∂uibotQualifier135Measure) = 0 := by
  have hm := (measurable_of_countable (fun j : ℤ => (j : ℝ))).comp
    (measurable_increment false k)
  have heq := (increment_ae false k).mono
    (fun _ h => congrArg (fun j : ℤ => (j : ℝ)) h)
  have hcode := (aemeasurable_identifiedSDPBusemann.eval k).sub
    (aemeasurable_identifiedSDPBusemann.eval (k - 1))
  have hd : IdentDistrib
      (fun z => ((uibotQualifier135Busemann false z k -
        uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ))
      (fun W => ((identifiedSDPBusemann W k -
        identifiedSDPBusemann W (k - 1) : ℤ) : ℝ))
      uibotQualifier135Measure wholePlaneIIDCodeMeasure :=
    ⟨hm.aemeasurable, (measurable_of_countable (fun j : ℤ => (j : ℝ))).comp_aemeasurable hcode,
      factor_law _ hm _ heq⟩
  obtain ⟨hi, he⟩ := DirectedDistances.Paper.Section1.thm_busemann_tail.2.2.2 k
  exact ⟨hd.integrable_iff.mpr hi, hd.integral_eq.trans he⟩

/-- Helper toward Proposition 3.9: the complete rescaled whole-path law
on the geometric probability space, with both modes still available jointly. -/
@[expose] def uibotQualifier135ScalingLaw (longest : Bool) (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨uibotQualifier135Measure.map
    (fun z => if longest then ((uibotGeomBusemannObservables z).2 n).1
      else ((uibotGeomBusemannObservables z).2 n).2), inferInstance⟩

private theorem scaling_law_eq (longest : Bool) (n : ℕ) :
    uibotQualifier135ScalingLaw longest n =
      if longest then identifiedLDPScalingLaw n else identifiedSDPScalingLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  cases longest
  · exact factor_law _
      (((measurable_pi_apply n).comp measurable_uibotGeomBusemannObservables.snd).snd)
      _ (uibotGeomBusemannObservables_ae.mono fun _ h => congrArg (fun y => (y.2 n).2) h)
  · exact factor_law _
      (((measurable_pi_apply n).comp measurable_uibotGeomBusemannObservables.snd).fst)
      _ (uibotGeomBusemannObservables_ae.mono fun _ h => congrArg (fun y => (y.2 n).1) h)

/-- Helper toward Proposition 3.9: both local-Skorokhod convergence
conclusions of Theorem 1.6 for the Borel geometric paths, preserving the
shared constants within each pair of limiting half-processes. -/
theorem uibotQualifier135_busemann_convergence :
    ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto (uibotQualifier135ScalingLaw true) atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto (uibotQualifier135ScalingLaw false) atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  have hL : uibotQualifier135ScalingLaw true = identifiedLDPScalingLaw :=
    funext fun n => scaling_law_eq true n
  have hS : uibotQualifier135ScalingLaw false = identifiedSDPScalingLaw :=
    funext fun n => scaling_law_eq false n
  rw [hL, hS]
  exact DirectedDistances.Paper.Section1.thm_busemann_conv.2.2

/-- Helper toward Proposition 3.9: Lemma 5.6 with one Borel slice family
under the geometric law. The common cut, both leftmost clauses and least
edge-coalescence witnesses are retained before the full integer family. -/
theorem uibotQualifier135_geo_slice (default : GeometricSideClass) (x : XDP) :
    ∃ Phi : ℤ → D39GeomRootedMapClass.{0} → Option GeometricSideClass,
      (∀ k, Measurable (Phi k)) ∧
      (∀ k, ∀ᵐ z ∂uibotQualifier135Measure, (Phi k z).isSome) ∧
      (∀ᵐ z ∂uibotQualifier135Measure,
        let W := uibotRecoveredCode z
        ∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
        ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
          (boundaryPresentVertex (shiftedStream W 0) h k),
        ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
          (if x = XDP.ldp then true else false),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL
          (if x = XDP.ldp then true else false) k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
          (if x = XDP.ldp then true else false) k Q (T k) → Q = P k) ∧
        ∀ k : ℤ, ∃ a b : ℕ,
          ∃ hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
          Phi k z = some (geometricSideClass
            (m0CutGeodesicSlice (hp := hp) P k a b hab))) ∧
      iIndepFun (fun k => forgetMarksOptionClassValue default ∘ Phi k)
        uibotQualifier135Measure ∧
      (∀ k : ℤ, 1 ≤ k → uibotQualifier135Measure.map
        (forgetMarksOptionClassValue default ∘ Phi k) =
        uibotQualifier135Measure.map (forgetMarksOptionClassValue default ∘ Phi 1)) ∧
      (∀ k : ℤ, k ≤ 0 → uibotQualifier135Measure.map
        (forgetMarksOptionClassValue default ∘ Phi k) =
        uibotQualifier135Measure.map (forgetMarksOptionClassValue default ∘ Phi 0)) := by
  obtain ⟨G, hm, hp, hchar, hind, hpos, hneg⟩ :=
    DirectedDistances.Paper.Section5.lem_geo_slice default x
  let X := fun W k => G k W
  have hX : AEMeasurable X wholePlaneIIDCodeMeasure := aemeasurable_pi_iff.mpr hm
  let Y := uibotRecoveredObservable X hX
  have hY : Measurable Y := measurable_uibotRecoveredObservable _ _
  have heq (k : ℤ) : G k =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z => Y z k) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
    (uibotRecoveredObservable_ae X hX).mono fun _ h => congrFun h k
  have hrec : ∀ᵐ z ∂uibotQualifier135Measure, ∀ k, G k (uibotRecoveredCode z) = Y z k := by
    filter_upwards [recovered_observable_ae X hX] with z hz
    exact congrFun hz
  have hread := measurable_forgetMarksOptionClassValue default
  have hreadY (k : ℤ) := hread.comp ((measurable_pi_apply k).comp hY)
  have hreadEq (k : ℤ) : (forgetMarksOptionClassValue default ∘ G k)
      =ᵐ[wholePlaneIIDCodeMeasure]
      (forgetMarksOptionClassValue default ∘ (fun z => Y z k)) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
    (heq k).mono fun _ h => congrArg (forgetMarksOptionClassValue default) h
  refine ⟨fun k z => Y z k, fun k => (measurable_pi_apply k).comp hY,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [recovered_ae _ (hp k), hrec] with z hz he
    rw [← he k]
    exact hz
  · filter_upwards [recovered_ae _ hchar, hrec] with z hz he
    obtain ⟨H, h, hLL, hp, T, P, hleft, huniq, hs⟩ := hz
    refine ⟨H, h, hLL, hp, T, P, hleft, huniq, ?_⟩
    intro k
    rw [← he k]
    exact hs k
  · exact factor_iindep _ hreadY _ hreadEq
      (fun k => hread.comp_aemeasurable (hm k)) hind
  · intro k hk
    exact (factor_law _ (hreadY k) _ (hreadEq k)).trans
      ((hpos k hk).trans (factor_law _ (hreadY 1) _ (hreadEq 1)).symm)
  · intro k hk
    exact (factor_law _ (hreadY k) _ (hreadEq k)).trans
      ((hneg k hk).trans (factor_law _ (hreadY 0) _ (hreadEq 0)).symm)

/-- Helper toward Proposition 3.9: Definition 1.3's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_future_map_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let D := m0CutData W H h hLL
      let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
      let f := seamFun (shiftedStream W 0) h (H.1 0)
      (D.betaR.vertex 0 = D.x 1) ∧
      (∀ n, wholePlaneRightmostOutgoingAt W H (D.betaR.vertex n) (D.betaR.edge n) ∧
        wholePlaneEdgeEast W (D.betaR.edge n) = D.betaR.vertex (n + 1)) ∧
      (D.betaL.vertex 0 = D.x 0) ∧
      (∀ n, wholePlaneLeftmostIncomingAt W H (D.betaL.vertex n) (D.betaL.edge n) ∧
        wholePlaneEdgeWest W (D.betaL.edge n) = D.betaL.vertex (n + 1)) ∧
      (D.rootDart.1 = m0CutLambdaZero W) ∧
      Function.Injective (futureMapInternalGluedFace W H h hp) ∧
      ((∀ e, D.seam e ↔ e = m0CutLambdaZero W ∨
        e ∈ Set.range D.betaR.edge ∨ e ∈ Set.range D.betaL.edge) ∧
      (m0CutLeftVertices W H D.seam = Set.range (wholePlaneVertexι W 0)) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      D.darts = Set.range (wholePlaneDartι W 0) ∧
      (∀ e, D.seam e → e ∈ D.edges) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      (∀ e, e ∈ D.edges → wholePlaneEdgePresent W e) ∧
      (∀ e, (e ∈ D.edges ∧ ¬ D.missing e) ↔
        (e ∈ D.edges ∧ ¬ D.seam e) ∨ e = m0CutLambdaZero W ∨
          e ∈ Set.range D.betaR.edge) ∧
      (∀ d, d ∈ D.darts →
        (D.tail d ↔ wholePlaneDartTail W d ∧ d.1 ∉ Set.range D.betaL.edge)) ∧
      (∀ e, D.missing e → ¬ D.tail (e, false) ∧ ¬ D.tail (e, true)) ∧
      (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
        wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
        wholePlaneEdgePresent W D.rootDart.1 ∧
        ¬ D.missing D.rootDart.1 ∧ D.tail D.rootDart) ∧
      Function.Injective D.x ∧
      (Set.range D.x = {v | ∃ e, D.seam e ∧
        (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)}) ∧
      (∀ k, D.x k ∈ m0CutLeftVertices W H D.seam) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∧
      (∀ k, wholePlaneEdgeWest W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
        wholePlaneEdgeEast W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x (k + 1)) ∧
      (∀ d, wholePlaneDartFlip W (wholePlaneDartι W 0 d) =
        wholePlaneDartι W 0 (futureMapEdgeInv d)) ∧
      (∀ d, wholePlaneDartVertex W (wholePlaneDartι W 0 d) =
        wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) d)) ∧
      (∀ d a, D.IsRot (wholePlaneDartι W 0 d) a ↔
        a = wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d))) ∧
      ((∀ d a, D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d)) a ↔
        a = wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) ∧
      (∀ F : G.Face, (∃ q, futureMapInternalGluedFace W H h hp q = F) ↔
        F.val ⊆ {z : ℂ | f z.re < z.im}) ∧
      (∀ d q, G.dartBorders (wholePlaneDartι W 0 d)
        (futureMapInternalGluedFace W H h hp q) ↔ Quotient.mk _ d = q.val) ∧
      (∀ d, P.dartBorders d
        (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
        d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1)) ∧
      (∀ q : FutureMapInternalFaceOrbit W H,
        ∃ j : TriangleCreationTime (shiftedStream W 0),
          {a | G.dartBorders a (futureMapInternalGluedFace W H h hp q)} =
            wholePlaneDartι W 0 '' {d | d ∈ stageTriangleDartList (shiftedStream W 0) j} ∧
          ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image
            (wholePlaneDartι W 0)).card = 3) ∧
      (∀ v : RootedLocallyFiniteVertex (ℕ × Bool)
          (kmswInfRot (shiftedStream W 0) (H.1 0)),
        ¬ Relation.TransGen
          (rootedLocallyFiniteDirectedStep (kmswInfRot (shiftedStream W 0) (H.1 0))
            futureMapEdgeInv (fun d => D.missing (wholePlaneDartι W 0 d).1)
            (fun d => D.tail (wholePlaneDartι W 0 d))) v v) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      ({z | ∃ a : WholePlaneDart W, D.seam a.1 ∧ z ∈ (G.arc a).image} =
        {z : ℂ | z.im = f z.re}) ∧
      (∀ v, v ∈ m0CutLeftVertices W H D.seam ↔ f (G.pos v).re ≤ (G.pos v).im) ∧
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im}))) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let D := m0CutData W H h hLL
      let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
      let f := seamFun (shiftedStream W 0) h (H.1 0)
      (D.betaR.vertex 0 = D.x 1) ∧
      (∀ n, wholePlaneRightmostOutgoingAt W H (D.betaR.vertex n) (D.betaR.edge n) ∧
        wholePlaneEdgeEast W (D.betaR.edge n) = D.betaR.vertex (n + 1)) ∧
      (D.betaL.vertex 0 = D.x 0) ∧
      (∀ n, wholePlaneLeftmostIncomingAt W H (D.betaL.vertex n) (D.betaL.edge n) ∧
        wholePlaneEdgeWest W (D.betaL.edge n) = D.betaL.vertex (n + 1)) ∧
      (D.rootDart.1 = m0CutLambdaZero W) ∧
      Function.Injective (futureMapInternalGluedFace W H h hp) ∧
      ((∀ e, D.seam e ↔ e = m0CutLambdaZero W ∨
        e ∈ Set.range D.betaR.edge ∨ e ∈ Set.range D.betaL.edge) ∧
      (m0CutLeftVertices W H D.seam = Set.range (wholePlaneVertexι W 0)) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      D.darts = Set.range (wholePlaneDartι W 0) ∧
      (∀ e, D.seam e → e ∈ D.edges) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      (∀ e, e ∈ D.edges → wholePlaneEdgePresent W e) ∧
      (∀ e, (e ∈ D.edges ∧ ¬ D.missing e) ↔
        (e ∈ D.edges ∧ ¬ D.seam e) ∨ e = m0CutLambdaZero W ∨
          e ∈ Set.range D.betaR.edge) ∧
      (∀ d, d ∈ D.darts →
        (D.tail d ↔ wholePlaneDartTail W d ∧ d.1 ∉ Set.range D.betaL.edge)) ∧
      (∀ e, D.missing e → ¬ D.tail (e, false) ∧ ¬ D.tail (e, true)) ∧
      (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
        wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
        wholePlaneEdgePresent W D.rootDart.1 ∧
        ¬ D.missing D.rootDart.1 ∧ D.tail D.rootDart) ∧
      Function.Injective D.x ∧
      (Set.range D.x = {v | ∃ e, D.seam e ∧
        (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)}) ∧
      (∀ k, D.x k ∈ m0CutLeftVertices W H D.seam) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∧
      (∀ k, wholePlaneEdgeWest W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
        wholePlaneEdgeEast W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x (k + 1)) ∧
      (∀ d, wholePlaneDartFlip W (wholePlaneDartι W 0 d) =
        wholePlaneDartι W 0 (futureMapEdgeInv d)) ∧
      (∀ d, wholePlaneDartVertex W (wholePlaneDartι W 0 d) =
        wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) d)) ∧
      (∀ d a, D.IsRot (wholePlaneDartι W 0 d) a ↔
        a = wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d))) ∧
      ((∀ d a, D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d)) a ↔
        a = wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) ∧
      (∀ F : G.Face, (∃ q, futureMapInternalGluedFace W H h hp q = F) ↔
        F.val ⊆ {z : ℂ | f z.re < z.im}) ∧
      (∀ d q, G.dartBorders (wholePlaneDartι W 0 d)
        (futureMapInternalGluedFace W H h hp q) ↔ Quotient.mk _ d = q.val) ∧
      (∀ d, P.dartBorders d
        (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
        d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1)) ∧
      (∀ q : FutureMapInternalFaceOrbit W H,
        ∃ j : TriangleCreationTime (shiftedStream W 0),
          {a | G.dartBorders a (futureMapInternalGluedFace W H h hp q)} =
            wholePlaneDartι W 0 '' {d | d ∈ stageTriangleDartList (shiftedStream W 0) j} ∧
          ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image
            (wholePlaneDartι W 0)).card = 3) ∧
      (∀ v : RootedLocallyFiniteVertex (ℕ × Bool)
          (kmswInfRot (shiftedStream W 0) (H.1 0)),
        ¬ Relation.TransGen
          (rootedLocallyFiniteDirectedStep (kmswInfRot (shiftedStream W 0) (H.1 0))
            futureMapEdgeInv (fun d => D.missing (wholePlaneDartι W 0 d).1)
            (fun d => D.tail (wholePlaneDartι W 0 d))) v v) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      ({z | ∃ a : WholePlaneDart W, D.seam a.1 ∧ z ∈ (G.arc a).image} =
        {z : ℂ | z.im = f z.re}) ∧
      (∀ v, v ∈ m0CutLeftVertices W H D.seam ↔ f (G.pos v).re ≤ (G.pos v).im) ∧
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im}))) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section1.defn_future_map

/-- Helper toward Proposition 3.9: Theorem 1.4's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_busemann_cut_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section1.thm_busemann

/-- Helper toward Proposition 3.9: Lemma 3.10's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_boundary_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section3.lem_uibot_bdy

/-- Helper toward Proposition 3.9: Lemma 5.3's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_infty_cut_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section5.lem_infty_cut

/-- Helper toward Proposition 3.9: Lemma 5.4's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_geo_infty_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section5.geo_infty

/-- Helper toward Proposition 3.9: Lemma 5.7's complete installed predicate
has a Borel geometric representative. Its equivalence holds on one common
code event, retaining every shared witness and simultaneous quantifier.
On the Borel conull set the full statement holds for the recovered code;
no individual Borel witness selection or new geometric attribution is claimed. -/
theorem uibotQualifier135_busemann_coalescence_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂uibotQualifier135Measure, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  exact borel_recovered_ae _ DirectedDistances.Paper.Section5.busemann_cls

/-- Helper toward Proposition 3.9: the stopped hatted code observation is
a.e. measurable under the original iid code law. -/
theorem aemeasurable_stopped_hat_codes_qualifier135 (k : ℤ) :
    AEMeasurable (hatLawCodes ∘ boundaryFutureCode k) wholePlaneIIDCodeMeasure := by
  have hm : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_hatLawCodes.1
  exact hm.comp_aemeasurable (measurable_boundaryFutureCode k).aemeasurable

/-- Helper toward Proposition 3.9: the Borel stopped hatted generating word
at each boundary label, using the fixed recovered-code representative. -/
@[expose] def uibotQualifier135StoppedHat (k : ℤ) :
    D39GeomRootedMapClass.{0} → (ℕ → Fin 3) :=
  uibotRecoveredObservable (hatLawCodes ∘ boundaryFutureCode k)
    (aemeasurable_stopped_hat_codes_qualifier135 k)

/-- Helper toward Proposition 3.9: each stopped hatted word is Borel. -/
theorem measurable_uibotQualifier135StoppedHat (k : ℤ) :
    Measurable (uibotQualifier135StoppedHat k) :=
  measurable_uibotRecoveredObservable _ _

/-- Helper toward Proposition 3.9: both stopped-word laws of Lemma 5.2
under the geometric pushforward law, at every boundary label. -/
theorem uibotQualifier135_stopped_laws (k : ℤ) :
    uibotQualifier135Measure.map (fun z => (uibotGeomFutureObservables z k).2) =
      uibotQualifier135Measure.map (fun z => (uibotGeomFutureObservables z 0).2) ∧
    uibotQualifier135Measure.map (uibotQualifier135StoppedHat k) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
  have hm (j : ℤ) := ((measurable_pi_apply j).comp
    measurable_uibotGeomFutureObservables).snd
  have heq (j : ℤ) : boundaryFutureCode j =ᵐ[wholePlaneIIDCodeMeasure]
      (fun z => (uibotGeomFutureObservables z j).2) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
    uibotGeomFutureObservables_ae.mono fun _ h => congrArg (fun y => (y j).2) h
  constructor
  · exact (factor_law _ (hm k) _ (heq k)).trans
      ((boundaryFutureCode_law_eq_zero k).trans (factor_law _ (hm 0) _ (heq 0)).symm)
  · exact (factor_law _ (measurable_uibotQualifier135StoppedHat k) _
      (uibotRecoveredObservable_ae _ (aemeasurable_stopped_hat_codes_qualifier135 k))).trans
        (boundaryFuture_hatLawCodes_law k)

/-- Helper toward Proposition 3.9: Lemma 5.2's simultaneous stopped-word,
containment and rooted-map clauses, on one common recovered cut. Both the
stopping times and generating words are the Borel geometric factors. -/
theorem uibotQualifier135_directed_contain :
    ∀ᵐ z ∂uibotQualifier135Measure,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∀ k : ℤ,
        uibotGeomBoundaryTimes z k = boundaryHitTime (shiftedStream W 0) h k ∧
        (fun i => (uibotGeomFutureObservables z k).2 (i + 1)) =
          (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)) ∧
        (∃ hτ : HasFlowLineHits
            (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)),
          uibotQualifier135StoppedHat k z =
            hatCodes (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)) hτ) ∧
        M0CutShiftContainment W H h hLL k ∧ boundaryFutureRootedMapClause W h k := by
  have hf := recovered_observable_ae _ aemeasurable_uibotCodeFutureObservables
  have hh : ∀ᵐ z ∂uibotQualifier135Measure, ∀ k : ℤ,
      hatLawCodes (boundaryFutureCode k (uibotRecoveredCode z)) =
        uibotQualifier135StoppedHat k z :=
    ae_all_iff.mpr fun k => recovered_observable_ae _ (aemeasurable_stopped_hat_codes_qualifier135 k)
  filter_upwards [recovered_ae _ DirectedDistances.Paper.Section5.directed_contain,
    hf, hh] with z hz hf hh
  obtain ⟨H, h, hLL, hall⟩ := hz
  refine ⟨H, h, hLL, ?_⟩
  intro k
  have ht : uibotGeomBoundaryTimes z k =
      boundaryHitTime (shiftedStream (uibotRecoveredCode z) 0) h k := by
    have hω : BoundaryHitWitnesses
        (fun i => shiftedCodePath (uibotRecoveredCode z) 0 (i + 1)) := by
      rw [shiftedCodePath_tail_eq]
      exact h
    exact (boundaryCodeTime_eq_boundaryHitTime
      (shiftedCodePath (uibotRecoveredCode z) 0) hω k)
  obtain ⟨_, _, hword, hhat, hcontain, hroot⟩ := hall k
  refine ⟨ht, ?_, ?_, hcontain, hroot⟩
  · have he := congrArg (fun y => (y k).2) hf
    change boundaryFutureCode k (uibotRecoveredCode z) =
      (uibotGeomFutureObservables z k).2 at he
    rw [ht, ← he]
    exact hword
  · rw [ht, ← hh k]
    exact hhat

/- Transport coverage and remaining scope:
* 1.3: complete Borel predicate and recovered-code cut/face characterization.
* 1.4: complete Borel predicate, uniqueness/finiteness, and joint Busemann characterization.
* 1.6: both whole-path convergence laws and their common cut characterization.
* 1.7: independence, both stationarity clauses, simultaneous bounds, symmetry, characterization.
* 1.8: both pairs of tails with shared constants, integrability/mean zero, characterization.
* 3.8: complete Borel predicate with all integer shifts and start isomorphisms.
* 5.1: generating-code independence/law and simultaneous rooted-map clauses.
* 5.2: both stopped laws, Borel times/words, common-cut containment/rooted-map clauses.
* 5.3: complete Borel predicate; vertices precede all endpoint/path quantifiers.
* 5.4: complete Borel predicate with both modes, uniqueness and edge coalescence.
* 5.5: optional presence, unmarked independence and both half-line laws.
* 5.6: one Borel family per mode, complete common-cut characterization and joint laws.
* 5.7: complete Borel predicate with both modes and least-offset difference identity.

The exact predicates, including all binders, are displayed in the declarations.
geometric qualifications remain. Predicate transport does not select individually
Borel geodesics or offsets and does not identify arbitrary geometric representatives.
No numbered-result or whole-paper completion status is changed. -/

end DirectedDistances.PaperProofs.Section3
end
