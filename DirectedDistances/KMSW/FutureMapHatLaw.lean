module

public import DirectedDistances.Paper.Section5.QuadrantWalk
public import DirectedDistances.Paper.Section4.CondWalkRNLaw
public import DirectedDistances.PaperProofs.Section4.PastMapPathDecoding
public import DirectedDistances.KMSW.QuadrantCodesIncrements
public import DirectedDistances.KMSW.HatLimitRotation
import DirectedDistances.KMSW.LocalFinitenessIID

/-! Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.

The source path is the zero path off the almost-sure flow-hit event. The code
observations below instead use the fixed constant-zero code stream there. All
identifications between these representatives are explicitly almost everywhere.
The conditioned law is the RN-characterized law; no limiting-conditioning claim
or complementary-component identification is asserted here. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The zero-based KMSW codes of a path, discarding `pathCode`'s dummy coordinate. -/
@[expose] def hatLawPathCodes (p : ℕ → ℤ × ℤ) : ℕ → Fin 3 :=
  fun i => pathCode p (i + 1)

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Measurability of the increment decoder. -/
private theorem measurable_hatLawPathCodes : Measurable hatLawPathCodes := by
  exact Measurable.of_eval fun i =>
    (measurable_pi_apply (i + 1)).comp measurable_pathCode

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The actual unprimed compressed code stream, with constant-zero null-set default. -/
@[expose] noncomputable def hatLawCodes (ω : ℕ → Fin 3) : ℕ → Fin 3 := by
  classical
  exact if h : HasFlowLineHits (fun i => ω (i + 1)) then
    hatCodes (fun i => ω (i + 1)) h else fun _ => 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The corrected primed compressed codes, with the same constant-zero default. -/
@[expose] noncomputable def hatLawPrimedCodes (ω : ℕ → Fin 3) : ℕ → Fin 3 := by
  classical
  exact if h : HasFlowLineHits (fun i => ω (i + 1)) then
    primedCode (primedSimInput (fun i => ω (i + 1))) h else fun _ => 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
On the flow-hit event, integrating precisely `hatCodes` gives the counted source path. -/
theorem sourceQuadrantHatPath_eq_integrate_hatCodes (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    sourceQuadrantHatPath ω = integrateCodes (hatCodes (fun i => ω (i + 1)) h) := by
  rw [sourceQuadrantHatPath, dite_eq_left h]
  exact (sourceQuadrantHatWalk_eq_quadrantHatSourceWalk _ h).trans
    (quadrantHatSourceWalk_eq_integrateCodes_hatCodes _ h)

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Decoding the integral of a code stream recovers every zero-based code. -/
private theorem hatLawPathCodes_integrate (c : ℕ → Fin 3) :
    hatLawPathCodes (integrateCodes c) = c := by
  funext i
  apply lazyTwoDimensionalStep_injective
  have hs : integrateCodes c (i + 1) - integrateCodes c i =
      lazyTwoDimensionalStep (c i) := by
    simp only [integrateCodes, Finset.sum_range_succ]
    abel
  exact (step_pathCode (integrateCodes c) i ⟨c i, hs.symm⟩).trans hs

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The explicitly totalized codes agree almost surely with decoding the source path. -/
private theorem hatLawCodes_ae_eq_decoded :
    hatLawCodes =ᵐ[iidCodeMeasure] (hatLawPathCodes ∘ sourceQuadrantHatPath) := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
  simp only [hatLawCodes, dite_eq_left h, Function.comp_apply,
    sourceQuadrantHatPath_eq_integrate_hatCodes ω h, hatLawPathCodes_integrate]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The primed code observation decodes the corrected source path almost surely. -/
private theorem hatLawPrimedCodes_ae_eq_decoded :
    hatLawPrimedCodes =ᵐ[iidCodeMeasure]
      (hatLawPathCodes ∘ sourceQuadrantPrimedPath) := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
  simp only [hatLawPrimedCodes, Function.comp_apply,
    sourceQuadrantPrimedPath, dite_eq_left h]
  funext i
  apply lazyTwoDimensionalStep_injective
  have hs := quadrantPrimedSourceWalk_increment_simInput (fun i => ω (i + 1)) h i
  rw [← sourceQuadrantPrimedWalk_eq_quadrantPrimedSourceWalk] at hs
  exact hs.symm.trans
    (step_pathCode _ i ⟨_, hs.symm⟩).symm

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The entire source compressed path has the RN-characterized conditioned law. -/
theorem sourceQuadrantHatPath_law :
    iidCodeMeasure.map sourceQuadrantHatPath = conditionedVectorPathLaw 0 0 := by
  have hq := DirectedDistances.Paper.Section5.quadrant_walk_corrected
  apply (DirectedDistances.Paper.Section4.cond_walk_rn_law 0 0).2.2
    (iidCodeMeasure.map sourceQuadrantHatPath) inferInstance
  intro n
  have hm : Measurable (fun q : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => q j.val) := by
    fun_prop
  rw [AEMeasurable.map_map_of_aemeasurable
    hm.aemeasurable hq.2.2.2.2.1]
  simpa only [Nat.cast_zero, Function.comp_def] using hq.2.1 n

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The hatted codes have the Definition 4.1 UIQBOT encoding law as a measure equality. -/
theorem hatLawCodes_law :
    iidCodeMeasure.map hatLawCodes =
      (conditionedVectorPathLaw 0 0).map hatLawPathCodes := by
  rw [Measure.map_congr hatLawCodes_ae_eq_decoded,
    ← AEMeasurable.map_map_of_aemeasurable measurable_hatLawPathCodes.aemeasurable
      DirectedDistances.Paper.Section5.quadrant_walk_corrected.2.2.2.2.1,
    sourceQuadrantHatPath_law]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Integrating the codes with their explicit null-set default has the full conditioned law. -/
theorem hatLawCodes_integrate_law :
    iidCodeMeasure.map (fun ω => integrateCodes (hatLawCodes ω)) =
      conditionedVectorPathLaw 0 0 := by
  calc
    _ = iidCodeMeasure.map sourceQuadrantHatPath := by
      apply Measure.map_congr
      filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
      simp only [hatLawCodes, dite_eq_left h,
        sourceQuadrantHatPath_eq_integrate_hatCodes ω h]
    _ = conditionedVectorPathLaw 0 0 := sourceQuadrantHatPath_law

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The conditioned-path decoder retains both coordinates of the entire path almost surely. -/
theorem conditionedPath_integrate_hatLawPathCodes :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0, integrateCodes (hatLawPathCodes p) = p := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  funext n
  change codeWalk (pathCode p) n = p n
  have hzero : p 0 = 0 := hp.1
  simpa only [hzero, sub_zero] using codeWalk_pathCode p hp.2 n

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Independence holds for the actual unprimed and corrected primed compressed codes. -/
theorem hatLawCodes_indep :
    hatLawCodes ⟂ᵢ[iidCodeMeasure] hatLawPrimedCodes := by
  exact (DirectedDistances.Paper.Section5.quadrant_walk_corrected.1.comp
    measurable_hatLawPathCodes measurable_hatLawPathCodes).congr
      hatLawCodes_ae_eq_decoded.symm hatLawPrimedCodes_ae_eq_decoded.symm

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Both explicitly totalized code observations are almost-everywhere measurable. -/
theorem aemeasurable_hatLawCodes :
    AEMeasurable hatLawCodes iidCodeMeasure ∧
      AEMeasurable hatLawPrimedCodes iidCodeMeasure := by
  have hq := DirectedDistances.Paper.Section5.quadrant_walk_corrected.2.2.2.2
  exact ⟨(measurable_hatLawPathCodes.comp_aemeasurable hq.1).congr
      hatLawCodes_ae_eq_decoded.symm,
    (measurable_hatLawPathCodes.comp_aemeasurable hq.2).congr
      hatLawPrimedCodes_ae_eq_decoded.symm⟩

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Almost surely the code observation constructs the geometric hatted dart carrier,
preserving root, rotation, reversal, missing and tail tags. Ambient and compressed
finite incidence are proved, not additional premises. This is an identification
of rotation systems; complementary components and ordered boundaries are separate. -/
theorem hatLawCodes_dartIdentification_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h : HasFlowLineHits w, ∃ hfin : hatLimitFiniteIncidence w,
        hatLawCodes ω = hatCodes w h ∧
        ∃ H : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1},
          (H futureMapRootDart).val = futureMapRootDart ∧
          (∀ d, H (kmswInfRot (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
            drawingFirstReturnPerm
              (monotoneFamilyDrawing w hfin (monotone_family_all w))
              {d : ℕ × Bool | MhatGeometricEdge w d.1} (H d)) ∧
          (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
          (∀ d, futureMapMissing (hatCodes w h) d ↔ futureMapMissing w (H d).val) ∧
          (∀ d, futureMapTail (hatCodes w h) d ↔ futureMapTail w (H d).val) := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits,
    iidCodes_ae_finite_incident_edges] with ω h hfin
  refine ⟨h, hfin, ?_, hatLimitDartEquiv _ h, hatLimitDartMap_root _ h,
    hatLimitDartEquiv_rotation _ h hfin, hatLimitDartMap_edgeInv _ h,
    hatLimitDartMap_missing _ h, hatLimitDartMap_tail _ h⟩
  simp only [hatLawCodes, dite_eq_left h]

end DirectedDistances.KMSW
