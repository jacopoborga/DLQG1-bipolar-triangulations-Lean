module

public import DirectedDistances.KMSW.WholePlaneRightBoundaryRot
public import DirectedDistances.KMSW.BoundaryRecordsMissing
public import DirectedDistances.KMSW.WholePlaneRotationAE

/-! Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
presence/missingness of the run boundary edges in the whole-plane colimit; not the paper result. -/

public section
namespace DirectedDistances.KMSW
open MeasureTheory RandomWalk

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
the run root edge is present in the whole-plane colimit; not the paper result. -/
theorem wholePlaneRootEdge_present (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N 0) := by
  apply wholePlaneEdgePresent_ι_of_run_present
  exact ⟨0, by change 0 < 1; omega, rfl⟩

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
every indexed right-boundary edge present in a run is present in the whole-plane colimit;
not the paper result. -/
theorem wholePlaneRightBoundaryEdge_present (W : ℤ → Fin 3) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℕ) :
    wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) k)) := by
  by_cases hk : k = 0
  · subst k
    rw [kmswRightBoundaryEdge_zero]
    exact wholePlaneRootEdge_present W N
  · have hkpos : 1 ≤ k := by omega
    have hp := boundaryVertex_right_edge_present_source (shiftedStream W N) h hkpos
    exact wholePlaneEdgePresent_ι_of_run_present W N _ hp.1

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
every lower-left boundary edge is missing in its one-sided run, by its exact
lower-left record description; not the paper result. -/
theorem kmswStage_LL_edge_missing (w : ℕ → Fin 3) (N e : ℕ)
    (he : e ∈ (kmswStage w N).LL) :
    (kmswStage w N).present e = false := by
  have hb : e < (kmswStage w N).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w N).2 e
    simp only [List.mem_append]
    tauto
  exact ((kmswStage_status w N).1 e hb).mpr (Or.inr he)

private theorem wholePlaneIID_ae_runBoundaryHits :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      BoundaryHitWitnesses (shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hf := iidCodes_ae_boundaryHitWitnesses
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [shiftedCodePath, insertDummy] using hp

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
almost surely the rotation hypothesis holds, every run root and right-boundary edge
is present in the colimit, and every run-N LL edge is missing at the ONE-SIDED run-N stage,
not in the colimit; not the paper result. -/
theorem wholePlaneIID_ae_rotation_boundary_status :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Nonempty (WholePlaneRotationHypothesis W) ∧ ∀ N : ℕ,
        wholePlaneEdgePresent W (wholePlaneEdgeι W N 0) ∧
          (∀ k : ℕ, wholePlaneEdgePresent W
            (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) k))) ∧
          (∀ e : ℕ, e ∈ (kmswStage (shiftedStream W N) N).LL →
            (kmswStage (shiftedStream W N) N).present e = false) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_runBoundaryHits] with W H h
  refine ⟨⟨H⟩, fun N => ?_⟩
  refine ⟨wholePlaneRootEdge_present W N, ?_, ?_⟩
  · intro k
    exact wholePlaneRightBoundaryEdge_present W N (h N) k
  · intro e he
    exact kmswStage_LL_edge_missing (shiftedStream W N) N e he

end DirectedDistances.KMSW
