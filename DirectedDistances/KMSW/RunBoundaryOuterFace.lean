module

public import DirectedDistances.KMSW.RunInfDartPartition
public import DirectedDistances.KMSW.RunBoundaryStackSets
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private theorem kmswRun_boundaryHit_coordinates_unbounded_below
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    (∀ a : ℤ, ∃ n, L w n ≤ a) ∧ (∀ a : ℤ, ∃ n, R w n ≤ a) := by
  constructor
  · intro a
    let k := min a (-1)
    obtain ⟨n, hn⟩ := h.leftHit k (min_le_right _ _)
    exact ⟨n, by omega⟩
  · intro a
    let k := max 1 (-a)
    obtain ⟨n, hn⟩ := h.rightHit k (le_max_left _ _)
    exact ⟨n, by omega⟩





theorem kmswRun_outerFace_edges_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    {e : ℕ | ¬ ∃ j : TriangleCreationTime w,
      (e, true) ∈ stageTriangleDartList w j} =
      Set.range (kmswRightBoundaryEdge w) ∪
        Set.range (fun j : ℕ =>
          kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
  ext e
  constructor
  · intro hnot
    have hboundary :=
      (kmswRunInfDart_boundary_iff_not_triangle w hL hR (e, true)).2 hnot
    rcases hboundary with hLL | hLR
    · rcases hLL with ⟨e', he', hde⟩
      have heq : e = e' := congrArg Prod.fst hde
      subst e'
      right
      rw [← kmswRunEventuallyLL_eq_range w h]
      exact he'
    · rcases hLR with ⟨e', he', hde⟩
      have heq : e = e' := congrArg Prod.fst hde
      subst e'
      left
      rw [← kmswRunEventuallyLR_eq_range w h]
      exact he'
  · intro hranges
    rcases hranges with hLR | hLL
    · rw [← kmswRunEventuallyLR_eq_range w h] at hLR
      exact (kmswRunInfDart_boundary_iff_not_triangle w hL hR (e, true)).mp
        (Or.inr ⟨e, hLR, rfl⟩)
    · rw [← kmswRunEventuallyLL_eq_range w h] at hLL
      exact (kmswRunInfDart_boundary_iff_not_triangle w hL hR (e, true)).mp
        (Or.inl ⟨e, hLL, rfl⟩)

/-- The right-boundary and first-hit LL edge ranges are disjoint. -/
theorem kmswRun_outerFace_ranges_disjoint (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    Disjoint (Set.range (kmswRightBoundaryEdge w))
      (Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1))))) := by
  rw [← kmswRunEventuallyLR_eq_range w h, ← kmswRunEventuallyLL_eq_range w h]
  exact kmswRunEventuallyLR_disjoint_LL w

/-- The boundary-hit witnesses themselves imply both unbounded-below
coordinates, so the edge characterization needs only those witnesses. -/
theorem kmswRun_outerFace_edges_eq_of_hits (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {e : ℕ | ¬ ∃ j : TriangleCreationTime w,
      (e, true) ∈ stageTriangleDartList w j} =
      Set.range (kmswRightBoundaryEdge w) ∪
        Set.range (fun j : ℕ =>
          kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
  obtain ⟨hL, hR⟩ := kmswRun_boundaryHit_coordinates_unbounded_below w h
  exact kmswRun_outerFace_edges_eq w h hL hR

private theorem kmswRun_ae_runBoundaryHitWitnesses :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      BoundaryHitWitnesses (shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hf := iidCodes_ae_boundaryHitWitnesses
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [shiftedCodePath, insertDummy] using hp

/-- Almost surely, every shifted whole-plane run has a boundary-hit witness
whose root, right-boundary records and first-hit LL edges are exactly its
outer-face edges; helper toward F4c / Lemma 3.10, not the paper result. -/
theorem wholePlaneIID_ae_run_outerFace_edges_eq :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      ∃ h : BoundaryHitWitnesses (shiftedStream W N),
        {e : ℕ | ¬ ∃ j : TriangleCreationTime (shiftedStream W N),
          (e, true) ∈ stageTriangleDartList (shiftedStream W N) j} =
          Set.range (kmswRightBoundaryEdge (shiftedStream W N)) ∪
            Set.range (fun j : ℕ => kmswLLCreatedEdge (shiftedStream W N)
              (boundaryHitTime (shiftedStream W N) h (-((j : ℤ) + 1)))) := by
  filter_upwards [kmswRun_ae_runBoundaryHitWitnesses] with W h N
  exact ⟨h N, kmswRun_outerFace_edges_eq_of_hits (shiftedStream W N) (h N)⟩

end DirectedDistances.KMSW
