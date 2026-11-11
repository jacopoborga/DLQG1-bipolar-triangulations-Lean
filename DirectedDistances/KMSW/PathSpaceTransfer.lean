module

public import DirectedDistances.KMSW.MeasurableCutEvents
public import DirectedDistances.KMSW.MapCutVertices
public import DirectedDistances.KMSW.UIQBOTOrientation
public import DirectedDistances.KMSW.InfiniteTriangulation
import Mathlib.MeasureTheory.Constructions.Polish.Basic






public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

/-- Integration determines every step code, since its first-coordinate increment -/
theorem integrateCodes_injective : Function.Injective integrateCodes := by
  intro c d h
  funext n
  have hn := congrArg (fun p : ℕ → ℤ × ℤ => (p n).1) h
  have hs := congrArg (fun p : ℕ → ℤ × ℤ => (p (n + 1)).1) h
  simp only [integrateCodes, Finset.sum_range_succ, Prod.fst_add] at hn hs
  have hc : (lazyTwoDimensionalStep (c n)).1 = ((c n : ℕ) : ℤ) - 1 := rfl
  have hd : (lazyTwoDimensionalStep (d n)).1 = ((d n : ℕ) : ℤ) - 1 := rfl
  rw [hc, hd] at hs
  apply Fin.ext
  omega

/-- Integration is measurable for the product σ-algebras -/
theorem measurable_integrateCodes : Measurable integrateCodes := by
  apply Measurable.of_eval
  intro n
  exact (Finset.range n).measurable_sum (fun i _ =>
    (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply i))

/-- Lusin–Souslin on code space and vector path space; the standard Borel and -/
theorem measurableEmbedding_integrateCodes : MeasurableEmbedding integrateCodes :=
  measurable_integrateCodes.measurableEmbedding integrateCodes_injective

/-- A measurable code event has measurable image in path space (SA43). -/
theorem measurableSet_image_integrateCodes {S : Set (ℕ → Fin 3)}
    (hS : MeasurableSet S) : MeasurableSet (integrateCodes '' S) :=
  measurableEmbedding_integrateCodes.measurableSet_image' hS

private theorem integrateCodes_shift_pitman (ω : ℕ → Fin 3) :
    integrateCodes (pitmanCode (fun i => ω (i + 1))) = vectorPitman (codeWalk ω) := by
  funext n
  rw [integrateCodes_pitmanCode]
  rfl

/-- An almost-sure measurable code event transfers to existence of a code witness -/
theorem conditionedVectorPathLaw_ae_exists_codes_of_ae
    {S : Set (ℕ → Fin 3)} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂iidCodeMeasure, pitmanCode (fun i => ω (i + 1)) ∈ S) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∃ w ∈ S, integrateCodes w = p := by
  have hm : Measurable (fun ω : ℕ → Fin 3 =>
      integrateCodes (pitmanCode (fun i => ω (i + 1)))) :=
    measurable_integrateCodes.comp measurable_pitmanCode_shift
  have hlaw : iidCodeMeasure.map (fun ω : ℕ → Fin 3 =>
      integrateCodes (pitmanCode (fun i => ω (i + 1)))) =
      conditionedVectorPathLaw 0 0 := by
    simpa only [integrateCodes_shift_pitman] using map_vectorPitman_codeWalk
  have hi : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, p ∈ integrateCodes '' S := by
    rw [← hlaw]
    apply (ae_map_iff hm.aemeasurable (measurableSet_image_integrateCodes hS)).mpr
    exact h.mono (fun ω hω => ⟨_, hω, rfl⟩)
  exact hi

/-- Probability-one version of the measurable-event transfer (SA43, -/
theorem conditionedVectorPathLaw_ae_exists_codes
    {S : Set (ℕ → Fin 3)} (hS : MeasurableSet S)
    (h : iidCodeMeasure {ω | pitmanCode (fun i => ω (i + 1)) ∈ S} = 1) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∃ w ∈ S, integrateCodes w = p := by
  apply conditionedVectorPathLaw_ae_exists_codes_of_ae hS
  exact (mem_ae_iff_prob_eq_one (measurableSet_preimage_pitmanCode_shift hS)).mpr h

/-- Under the conditioned path law there is an integrating locally finite code
realization with infinitely many map-level cut vertices and the simultaneous
first-visit characterization, whose record inequalities concern the path itself -/
theorem conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃ w : ℕ → Fin 3, integrateCodes w = p ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        Tendsto (L w) atTop atTop ∧ (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
        (∀ j, 0 ≤ L w j) ∧ {v : ℕ | mapCutVertex w hfin v}.Infinite ∧
        ∀ n : ℕ, (mapCutVertex w hfin (activeInitial w n) ∧
          ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
          ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
            (∀ j, n ≤ j → (p n).1 ≤ (p j).1)) := by
  let S : Set (ℕ → Fin 3) := {w |
    (∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) ∧
    Tendsto (L w) atTop atTop ∧ (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
      (∀ j, 0 ≤ L w j) ∧ {v : ℕ | IsCutVertex w v}.Infinite}
  have hS : MeasurableSet S := measurableSet_finiteIncidence.inter
    (measurableSet_tendsto_L.inter (measurableSet_R_unbounded_below.inter
      (measurableSet_L_nonneg.inter measurableSet_infinite_cutVertices)))
  have hfull : ∀ᵐ ω ∂iidCodeMeasure, pitmanCode (fun i => ω (i + 1)) ∈ S := by
    filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
    obtain ⟨hfin, hT, hR, hL, hinf⟩ := hω
    refine ⟨hfin, hT, hR, hL, ?_⟩
    exact hinf.mono (fun v hv => (mapCutVertex_iff _ hfin hT hR hL v).mp hv)
  filter_upwards [conditionedVectorPathLaw_ae_exists_codes_of_ae hS hfull] with p hp
  obtain ⟨w, ⟨hfin, hT, hR, hL, hinf⟩, hwp⟩ := hp
  refine ⟨w, hwp, hfin, hT, hR, hL, ?_, ?_⟩
  · exact hinf.mono (fun v hv => (mapCutVertex_iff w hfin hT hR hL v).mpr hv)
  · intro n
    have hLn : ∀ j, L w j = (p j).1 := by
      intro j
      rw [kmsw_L_eq, hwp]
    have hRn : ∀ j, R w j = (p j).2 := by
      intro j
      rw [kmsw_R_eq, hwp]
    simpa only [hLn, hRn] using mapCutVertex_first_visit_iff w hfin hT hR hL n

/-- The same path-space realization has an acyclic present-edge orientation,
a unique allocated source, no allocated sink, and triangular non-outer faces -/
theorem conditionedVectorPathLaw_ae_orientation_triangulation :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃ w : ℕ → Fin 3, integrateCodes w = p ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        {v : ℕ | mapCutVertex w hfin v}.Infinite ∧
        acyclic (PresentVertex w) ∧
        (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
          ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔ v = 0)) ∧
        (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
          ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
        (∀ d : ℕ × Bool,
          (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
          (∃ i, d = (kmswRightBoundaryEdge w i, true)) ∨
          ∃! j : TriangleCreationTime w, d ∈ stageTriangleDartList w j) ∧
        (∀ d : ℕ × Bool,
          (∀ i, d ≠ (kmswLeftBoundaryEdge w i, false)) →
          (∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) →
          ∃! j : TriangleCreationTime w,
            d ∈ stageTriangleDartList w j ∧
            FaceSucc3Cycle (kmswInfFaceSucc w hfin)
              (stageTriangleDartTriple w j).1
              (stageTriangleDartTriple w j).2.1
              (stageTriangleDartTriple w j).2.2) := by
  filter_upwards [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp
  obtain ⟨w, hwp, hfin, hT, hR, hL, hinf, _⟩ := hp
  exact ⟨w, hwp, hfin, hinf, presentVertex_acyclic w,
    fun v hv => allocated_vertex_source_iff_zero w hL v hv,
    fun v hv => allocated_vertex_outgoing_present_edge w hR v hv,
    kmswInfDart_partition w hfin hT hR hL,
    kmswInfDart_nonOuterFace_cycle w hfin hT hR hL⟩

end DirectedDistances.KMSW
