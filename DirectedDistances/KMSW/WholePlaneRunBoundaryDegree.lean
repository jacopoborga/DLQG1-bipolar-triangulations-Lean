module

public import DirectedDistances.KMSW.UIBOTBoundaryM0
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure

/-! # Degree classification for nonpositive whole-plane runs

Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
runs m_{n,∞} with n ≤ 0 (N : ℕ); runs with n > 0 remain uncovered here. Not the paper result. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
runs m_{n,∞} with n ≤ 0 (N : ℕ); runs with n > 0 remain uncovered here. Not the paper
result. In the one-sided run, a boundary-hit witness gives every allocated vertex an
outgoing edge and characterizes exactly those with no incoming edge. -/
theorem kmswRunBoundaryDegree (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ v, (∃ m, v < (kmswStage w m).nextVertex) →
      (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
        ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
          ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k) := by
  intro v hv
  exact ⟨uibot_allocated_vertex_outgoing w h.R_unbounded_below v hv,
    allocated_source_iff_left_boundary w h v hv⟩

private theorem wholePlaneIID_ae_runBoundaryHitWitnesses :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      BoundaryHitWitnesses (shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hf := iidCodes_ae_boundaryHitWitnesses
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [shiftedCodePath, insertDummy] using hp

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
shifted run starting at n = −N has one boundary-hit witness that classifies incoming
and outgoing edges at all allocated vertices. Runs with n > 0 remain uncovered here;
this is not the paper result. -/
theorem wholePlaneIID_ae_runBoundaryDegree :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      ∃ h : BoundaryHitWitnesses (shiftedStream W N), ∀ v,
        (∃ m, v < (kmswStage (shiftedStream W N) m).nextVertex) →
          (∃ e, EdgePresent (shiftedStream W N) e ∧
            edgeWest (shiftedStream W N) e = v) ∧
          ((¬ ∃ e, EdgePresent (shiftedStream W N) e ∧
              edgeEast (shiftedStream W N) e = v) ↔
            ∃ k : ℤ, k ≤ 0 ∧
              v = boundaryVertex (shiftedStream W N) h k) := by
  filter_upwards [wholePlaneIID_ae_runBoundaryHitWitnesses] with W h N
  exact ⟨h N, kmswRunBoundaryDegree (shiftedStream W N) (h N)⟩

end DirectedDistances.KMSW
