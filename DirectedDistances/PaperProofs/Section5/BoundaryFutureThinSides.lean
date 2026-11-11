module

public import DirectedDistances.PaperProofs.Section5.DirectedContainIdentified
public import DirectedDistances.PaperProofs.SourceResults.ThinIndependence

/-! # Hatted future paths and thin side codes

code is passed through the hatted code map and its path integral; the resulting
side-code package is transferred from Proposition 4.7 by the exact path law. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open DirectedDistances.Paper.Section4 DirectedDistances.PaperProofs.Section4

/-- integrated from the hatted boundary-future code. -/
@[expose] noncomputable def boundaryFutureHattedPath (k : ℤ)
    (W : ℤ → Fin 3) : ℕ → ℤ × ℤ :=
  integrateCodes (hatLawCodes (boundaryFutureCode k W))

/-- measurability of the integrated hatted boundary-future path. -/
theorem aemeasurable_boundaryFutureHattedPath (k : ℤ) :
    AEMeasurable (boundaryFutureHattedPath k) wholePlaneIIDCodeMeasure := by
  have hhat : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_hatLawCodes.1
  exact measurable_integrateCodes.comp_aemeasurable
    (hhat.comp_aemeasurable (measurable_boundaryFutureCode k).aemeasurable)

/-- hatted boundary-future path has exactly the conditioned-walk path law, via the
Pitman code law. -/
theorem boundaryFutureHattedPath_map_law (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (boundaryFutureHattedPath k) =
      conditionedVectorPathLaw 0 0 := by
  have hhat : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_hatLawCodes.1
  have hcomp : AEMeasurable (hatLawCodes ∘ boundaryFutureCode k)
      wholePlaneIIDCodeMeasure :=
    hhat.comp_aemeasurable (measurable_boundaryFutureCode k).aemeasurable
  change wholePlaneIIDCodeMeasure.map
      (integrateCodes ∘ (hatLawCodes ∘ boundaryFutureCode k)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable
      measurable_integrateCodes.aemeasurable hcomp,
    boundaryFuture_hatLawCodes_law]
  rw [Measure.map_map measurable_integrateCodes measurable_pitmanCode_shift]
  have hpoint (ω : ℕ → Fin 3) :
      integrateCodes (pitmanCode (fun i => ω (i + 1))) =
        fun n => vectorPitman (codeWalk ω) n := by
    funext n
    rw [integrateCodes_pitmanCode]
    rfl
  change iidCodeMeasure.map
      (fun ω => integrateCodes (pitmanCode (fun i => ω (i + 1)))) = _
  rw [Measure.map_congr (Filter.Eventually.of_forall hpoint)]
  exact map_vectorPitman_codeWalk

private theorem boundaryFutureThinSides_pair_map_law (x : XDP) (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath k W),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W))) =
      (conditionedVectorPathLaw 0 0).map (fun p =>
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left p,
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right p)) := by
  let f : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  let g : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hf : Measurable f :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  have hg : Measurable g :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hfg : Measurable (fun p => (f p, g p)) := hf.prodMk hg
  change wholePlaneIIDCodeMeasure.map
      ((fun p => (f p, g p)) ∘ boundaryFutureHattedPath k) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hfg.aemeasurable
      (aemeasurable_boundaryFutureHattedPath k),
    boundaryFutureHattedPath_map_law]

/-- two-side code package, transported to each boundary-future hatted path. -/
theorem boundaryFutureThinSides_package (x : XDP) (k : ℤ) :
    AEMeasurable
        (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath k W)) wholePlaneIIDCodeMeasure ∧
      AEMeasurable
        (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W)) wholePlaneIIDCodeMeasure ∧
      IndepFun
        (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath k W))
        (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W)) wholePlaneIIDCodeMeasure ∧
      ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime ∧
      MeasurableSet
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        boundaryFutureHattedPath k W ∈
          selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := by
  let f : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  let g : (ℕ → ℤ × ℤ) → ℕ → Option FiniteThinMap :=
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hf : Measurable f :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
  have hg : Measurable g :=
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
  have hpath := aemeasurable_boundaryFutureHattedPath k
  have hfae : AEMeasurable (f ∘ boundaryFutureHattedPath k)
      wholePlaneIIDCodeMeasure := hf.comp_aemeasurable hpath
  have hgae : AEMeasurable (g ∘ boundaryFutureHattedPath k)
      wholePlaneIIDCodeMeasure := hg.comp_aemeasurable hpath
  have hindep : IndepFun (f ∘ boundaryFutureHattedPath k)
      (g ∘ boundaryFutureHattedPath k) wholePlaneIIDCodeMeasure := by
    have hpair : wholePlaneIIDCodeMeasure.map
        ((fun p => (f p, g p)) ∘ boundaryFutureHattedPath k) =
        (conditionedVectorPathLaw 0 0).map (fun p => (f p, g p)) := by
      change wholePlaneIIDCodeMeasure.map (fun W =>
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
            (boundaryFutureHattedPath k W),
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
            (boundaryFutureHattedPath k W))) = _
      exact boundaryFutureThinSides_pair_map_law x k
    have hleft : wholePlaneIIDCodeMeasure.map (f ∘ boundaryFutureHattedPath k) =
        (conditionedVectorPathLaw 0 0).map f := by
      rw [← AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hpath,
        boundaryFutureHattedPath_map_law]
    have hright : wholePlaneIIDCodeMeasure.map (g ∘ boundaryFutureHattedPath k) =
        (conditionedVectorPathLaw 0 0).map g := by
      rw [← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hpath,
        boundaryFutureHattedPath_map_law]
    apply (indepFun_iff_map_prod_eq_prod_map_map hfae hgae).2
    change wholePlaneIIDCodeMeasure.map
        ((fun p => (f p, g p)) ∘ boundaryFutureHattedPath k) = _
    rw [hpair, hleft, hright]
    exact (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp
      (DirectedDistances.PaperProofs.SourceResults.thin_ind x).1
  have hdomain : ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      p ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ae_iff.mpr
      (DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.2.2
  have hdomainMap : ∀ᵐ p ∂wholePlaneIIDCodeMeasure.map
      (boundaryFutureHattedPath k),
        p ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := by
    rw [boundaryFutureHattedPath_map_law]
    exact hdomain
  have hdomainPullback := (Measure.tendsto_ae_map hpath).eventually hdomainMap
  refine ⟨?_, ?_, ?_,
    (DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.1,
    (DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.2.1, ?_⟩
  · change AEMeasurable (f ∘ boundaryFutureHattedPath k) wholePlaneIIDCodeMeasure
    exact hfae
  · change AEMeasurable (g ∘ boundaryFutureHattedPath k) wholePlaneIIDCodeMeasure
    exact hgae
  · change IndepFun (f ∘ boundaryFutureHattedPath k)
      (g ∘ boundaryFutureHattedPath k) wholePlaneIIDCodeMeasure
    exact hindep
  · exact hdomainPullback

/-- the left and right hatted future side codes is independent of the boundary index. -/
theorem boundaryFutureThinSides_joint_law_eq_zero (x : XDP) (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath k W),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W))) =
      wholePlaneIIDCodeMeasure.map (fun W =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath 0 W),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath 0 W))) := by
  exact (boundaryFutureThinSides_pair_map_law x k).trans
    (boundaryFutureThinSides_pair_map_law x 0).symm

end DirectedDistances.PaperProofs.Section5
