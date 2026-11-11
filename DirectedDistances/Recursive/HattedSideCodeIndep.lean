module

public import DirectedDistances.KMSW.FutureMapHatLaw
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
import DirectedDistances.KMSW.PathSpaceTransfer

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk
open DirectedDistances.Paper.Section4
open DirectedDistances.PlanarMap

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integrated path built from the hatted code sequence. -/
@[expose] noncomputable def hattedIntegratedPath (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  integrateCodes (hatLawCodes ω)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Exact measurability goal for the integrated hatted path. -/
def hattedIntegratedPathMeasurableGoal : Prop :=
  Measurable hattedIntegratedPath

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integrated hatted path is almost-everywhere measurable. -/
theorem aemeasurable_hattedIntegratedPath :
    AEMeasurable hattedIntegratedPath iidCodeMeasure := by
  exact measurable_integrateCodes.comp_aemeasurable aemeasurable_hatLawCodes.1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integrated hatted path has the conditioned path law. -/
theorem hattedIntegratedPath_map_law :
    iidCodeMeasure.map hattedIntegratedPath = conditionedVectorPathLaw 0 0 := by
  exact hatLawCodes_integrate_law

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
theorem hattedThinSideCodes_indep (x : XDP) :
    IndepFun
      (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (hattedIntegratedPath ω))
      (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
        (hattedIntegratedPath ω))
      iidCodeMeasure := by
  let f : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  let g : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hf : Measurable f :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  have hg : Measurable g :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hfg : Measurable (fun p => (f p, g p)) := hf.prodMk hg
  have hmap := hattedIntegratedPath_map_law
  have hpair : iidCodeMeasure.map
      ((fun p => (f p, g p)) ∘ hattedIntegratedPath) =
      (conditionedVectorPathLaw 0 0).map (fun p => (f p, g p)) := by
    rw [← AEMeasurable.map_map_of_aemeasurable hfg.aemeasurable
      aemeasurable_hattedIntegratedPath, hmap]
  have hleft : iidCodeMeasure.map (f ∘ hattedIntegratedPath) =
      (conditionedVectorPathLaw 0 0).map f := by
    rw [← AEMeasurable.map_map_of_aemeasurable hf.aemeasurable
      aemeasurable_hattedIntegratedPath, hmap]
  have hright : iidCodeMeasure.map (g ∘ hattedIntegratedPath) =
      (conditionedVectorPathLaw 0 0).map g := by
    rw [← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
      aemeasurable_hattedIntegratedPath, hmap]
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp_aemeasurable aemeasurable_hattedIntegratedPath)
    (hg.comp_aemeasurable aemeasurable_hattedIntegratedPath)).2
  change iidCodeMeasure.map
      ((fun p => (f p, g p)) ∘ hattedIntegratedPath) = _
  rw [hpair, hleft, hright]
  simpa only [f, g] using
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp
      (thin_side_codes_indep_renewal x)

/-- Exact unresolved goal for independence from the primed code.
Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
def hattedLeftPrimed_indep_right_goal (x : XDP) : Prop :=
  IndepFun
    (fun ω =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (hattedIntegratedPath ω),
        hatLawPrimedCodes ω))
    (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
      (hattedIntegratedPath ω))
    iidCodeMeasure

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Exact optional companion goal with the left code independent of the right side -/
def hattedLeft_indep_rightPrimed_goal (x : XDP) : Prop :=
  IndepFun
    (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
      (hattedIntegratedPath ω))
    (fun ω =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (hattedIntegratedPath ω),
        hatLawPrimedCodes ω))
    iidCodeMeasure

end DirectedDistances.Recursive
