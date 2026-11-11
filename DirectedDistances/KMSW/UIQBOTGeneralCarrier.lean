module

public import DirectedDistances.PaperProofs.Section4.UIQBOTCarrier
public import DirectedDistances.KMSW.KMSWConstructedEdgeCarrier
public import DirectedDistances.KMSW.KMSWConstructedGeometricEdgeEquiv

 

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory Quiver
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Definition 4.1: the finite-incidence and walk hypotheses
needed by the constructed drawing hold almost surely for the exact code law
used by `uiqbot_carrier`. -/
theorem uiqbot_code_ae_constructed_hypotheses :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ _hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        Tendsto (L w) atTop atTop ∧
          (∀ a : ℤ, ∃ n, R w n ≤ a) ∧ (∀ j, 0 ≤ L w j) := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  rcases hω with ⟨hfin, htrans, hR, hL0, _⟩
  exact ⟨hfin, htrans, hR, hL0⟩

private theorem kmswDrawingStep_to_presentHom
    {w : ℕ → Fin 3}
    {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    {P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)}
    {M : DirectedPlaneMap ℕ P.GeometricEdge} {iota : ℕ ≃ P.GeometricEdge}
    (hcompat : ∀ e, M.tail (iota e) = edgeWest w e ∧
      M.head (iota e) = edgeEast w e)
    (hpresent : ∀ e, EdgePresent w e) {u v : ℕ} (hstep : M.step u v) :
    Nonempty ((⟨u⟩ : PresentVertex w) ⟶ (⟨v⟩ : PresentVertex w)) := by
  rcases hstep with ⟨q, htail, hhead⟩
  obtain ⟨e, heq⟩ := iota.surjective q
  have hwest : edgeWest w e = u := by
    calc
      edgeWest w e = M.tail (iota e) := (hcompat e).1.symm
      _ = u := by rw [heq]; exact htail
  have heast : edgeEast w e = v := by
    calc
      edgeEast w e = M.head (iota e) := (hcompat e).2.symm
      _ = v := by rw [heq]; exact hhead
  exact ⟨⟨e, ⟨hpresent e, hwest, heast⟩⟩⟩

/-- Helper toward Definition 4.1: every constructed drawing admits the
compatible KMSW directed map; acyclicity, edge presence, and the root-source
fact transport to that map. This does not assume the plane-realization predicate. -/
theorem kmswConstructedDrawing_acyclic_edge_carrier
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) :
    ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
      ∃ iota : ℕ ≃ P.GeometricEdge,
        M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
        (∀ e, M.tail (iota e) = edgeWest w e ∧ M.head (iota e) = edgeEast w e) ∧
        M.IsAcyclic ∧
        (∀ q : P.GeometricEdge, ∃ e, iota e = q ∧ EdgePresent w e) ∧
        M.IsSource 0 := by
  obtain ⟨M, iota, hdraw, hcompat⟩ :=
    kmswConstructedDrawing_directedMap_compat w hfin P
  have hpresent : ∀ e, EdgePresent w e :=
    fun e => kmsw_edgePresent_of_uiqbot w hL0 hR e
  have hac : M.IsAcyclic := by
    intro v hcycle
    have hlift : ∀ {a b : ℕ}, Relation.TransGen M.step a b →
        ∃ p : Path (⟨a⟩ : PresentVertex w) ⟨b⟩, 0 < p.length := by
      intro a b hab
      induction hab using Relation.TransGen.head_induction_on with
      | single hstep =>
          obtain ⟨e⟩ := kmswDrawingStep_to_presentHom hcompat hpresent hstep
          exact ⟨e.toPath, by simp⟩
      | head hstep htail ih =>
          obtain ⟨e⟩ := kmswDrawingStep_to_presentHom hcompat hpresent hstep
          rcases ih with ⟨p, hp⟩
          refine ⟨(Path.nil.cons e).comp p, ?_⟩
          simp only [Path.length_comp, Path.length_cons, Path.length_nil]
          omega
    obtain ⟨p, hp⟩ := hlift hcycle
    have hz := presentVertex_acyclic w ⟨v⟩ p
    omega
  have hsource : M.IsSource 0 := by
    intro q hq
    obtain ⟨e, heq⟩ := iota.surjective q
    have hno := zero_no_incoming_present_edge w hL0 e (hpresent e)
    apply hno
    calc
      edgeEast w e = M.head (iota e) := (hcompat e).2.symm
      _ = 0 := by rw [heq]; exact hq
  refine ⟨M, iota, hdraw, hcompat, hac, ?_, hsource⟩
  intro q
  obtain ⟨e, rfl⟩ := iota.surjective q
  exact ⟨e, rfl, hpresent e⟩

/-- Helper toward Definition 4.1: acyclicity, edge presence, and the root-source
fact hold almost surely for every drawing of the constructed KMSW type. -/
theorem uiqbot_ae_general_acyclic_edge_carrier :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∀ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot w hfin) (kmswLimitDartVertex w),
          ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
            ∃ iota : ℕ ≃ P.GeometricEdge,
              M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
              (∀ e, M.tail (iota e) = edgeWest w e ∧ M.head (iota e) = edgeEast w e) ∧
              M.IsAcyclic ∧
              (∀ q : P.GeometricEdge, ∃ e, iota e = q ∧ EdgePresent w e) ∧
              M.IsSource 0 := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  rcases hω with ⟨hfin, htrans, hR, hL0, _⟩
  exact ⟨hfin, fun P => kmswConstructedDrawing_acyclic_edge_carrier
    (pitmanCode (fun i => ω (i + 1))) hfin hR hL0 P⟩

/-- Helper toward Definition 4.1: the code-level left and right boundary
chains follow the limiting face successor and are exactly the persistent
upper-left and lower-right boundary edges, almost surely. Geometric external
face identification is the separate realization obligation. -/
theorem uiqbot_ae_code_boundary_paths :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        (∀ i, kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
          (kmswLeftBoundaryEdge w (i + 1), false)) ∧
        (∀ i, kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
          (kmswRightBoundaryEdge w i, true)) ∧
        kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
          (kmswLeftBoundaryEdge w 0, false) ∧
        (∀ e, IsLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i) ∧
        (∀ e, IsRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i) := by
  filter_upwards [DirectedDistances.PaperProofs.Section4.uiqbot_carrier.2.2] with ω hω
  rcases hω with ⟨hfin, hleft, hright, hjunction, hL, hR, _, _, _, _, _, _⟩
  exact ⟨hfin, hleft, hright, hjunction, hL, hR⟩




















































end DirectedDistances.KMSW
