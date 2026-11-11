module

public import DirectedDistances.KMSW.UIQBOTGeneralCarrier

 

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Definition 4.1: almost surely, every natural vertex ID is
allocated at a finite KMSW stage. This follows from the almost-sure finite
incidence of edges and the deterministic finite-incidence allocation lemma. -/
theorem uiqbot_ae_vertex_allocated_by_stage :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ v : ℕ, ∃ n, v < (kmswStage w n).nextVertex := by
  exact pitmanCodes_ae_vertex_allocated

/-- Helper toward Definition 4.1: every vertex allocated at a finite stage is
incident to a geometric edge identity in the KMSW limit. Missing status does
not remove geometric edge identities. -/
theorem kmsw_vertex_incident_to_limit_edge_of_stage_allocation
    (w : ℕ → Fin 3) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    ∃ e, edgeWest w e = v ∨ edgeEast w e = v := by
  obtain ⟨n, hvn⟩ := hv
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v hvn
  have hend := edge_endpoints_eq w d.1.isLt
  cases hb : d.2
  · refine ⟨d.1.val, Or.inl ?_⟩
    rw [← hend.1]
    simpa [stageEndpoint, hb] using hd
  · refine ⟨d.1.val, Or.inr ?_⟩
    rw [← hend.2]
    simpa [stageEndpoint, hb] using hd

/-- Helper toward Definition 4.1: almost surely every vertex of the natural
vertex carrier is incident to a geometric edge of the limit. -/
theorem uiqbot_ae_every_vertex_incident_to_limit_edge :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ v : ℕ, ∃ e, edgeWest w e = v ∨ edgeEast w e = v := by
  filter_upwards [uiqbot_ae_vertex_allocated_by_stage] with ω halloc
  change ∀ v : ℕ, ∃ n, v < (kmswStage (pitmanCode (fun i => ω (i + 1))) n).nextVertex at halloc
  change ∀ v : ℕ, ∃ e,
    edgeWest (pitmanCode (fun i => ω (i + 1))) e = v ∨
      edgeEast (pitmanCode (fun i => ω (i + 1))) e = v
  intro v
  exact kmsw_vertex_incident_to_limit_edge_of_stage_allocation _ v (halloc v)

/-- Helper toward Definition 4.1: the unique-source and no-sink properties
transport from the allocated KMSW vertices to every vertex of a constructed
drawing, since every natural vertex ID is allocated almost surely. -/
theorem uiqbot_ae_general_source_sink_carrier :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ htrans : Tendsto (L w) atTop atTop,
          ∃ hR : ∀ a : ℤ, ∃ n, R w n ≤ a,
            ∃ hL0 : ∀ j, 0 ≤ L w j,
              ∀ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
                (kmswInfRot w hfin) (kmswLimitDartVertex w),
                ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
                  ∃ iota : ℕ ≃ P.GeometricEdge,
                    M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
                    (∀ e, M.tail (iota e) = edgeWest w e ∧
                      M.head (iota e) = edgeEast w e) ∧
                    M.IsAcyclic ∧
                    (∀ q : P.GeometricEdge, ∃ e, iota e = q ∧ EdgePresent w e) ∧
                    M.IsSource 0 ∧ (∀ v, M.IsSource v → v = 0) ∧
                    ∀ v, ¬ M.IsSink v := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices,
    pitmanCodes_ae_source_and_no_sink] with ω hwalk horient
  rcases hwalk with ⟨hfin, htrans, hR, hL0, _⟩
  rcases horient with ⟨_, hsource, hnosink⟩
  let w := pitmanCode (fun i => ω (i + 1))
  have hallocated : ∀ v : ℕ, ∃ n, v < (kmswStage w n).nextVertex := by
    intro v
    exact kmsw_vertex_allocated_of_finite_incidence w hfin v
  refine ⟨hfin, htrans, hR, hL0, fun P => ?_⟩
  obtain ⟨M, iota, hdraw, hcompat, hac, hpresent, hroot⟩ :=
    kmswConstructedDrawing_acyclic_edge_carrier w hfin hR hL0 P
  refine ⟨M, iota, hdraw, hcompat, hac, hpresent, hroot, ?_, ?_⟩
  · intro v hv
    have hnoIncoming : ¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v := by
      rintro ⟨e, _, he⟩
      exact (M.isSource_iff v).mp hv (iota e) ((hcompat e).2.trans he)
    exact (hsource v (hallocated v)).mp hnoIncoming
  · intro v hsink
    have houtgoing := (M.isSink_iff v).mp hsink
    obtain ⟨e, _, hw⟩ := hnosink v (hallocated v)
    exact houtgoing (iota e) ((hcompat e).1.trans hw)
















end DirectedDistances.KMSW
