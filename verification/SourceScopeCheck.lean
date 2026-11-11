module

public import verification.SourceBoundaryDomain
public import verification.SourceBoundaryChanneled
public import DirectedDistances.Paper.Section3.KMSW

/-! Current-paper domain bindings and their concrete finite-class consumption. -/

public section

/-- Every ordinary finite isomorphism class has the unchanged cone-walk realization
with its actual poles on the same drawing’s external-face boundary. -/
theorem DirectedDistances.KMSW.finiteIsoClass_source_boundary_domain (ell r n : Nat) (hL : 1 ≤ ell) (hR : 1 ≤ r) (hn : 1 ≤ n)
    (q : DirectedDistances.PlanarMap.KMSWMapIsoClass ell r n) :
    ∃ c : DirectedDistances.KMSW.KMSWWalkClass ell r n,
      DirectedDistances.KMSW.kmswToMapIsoClass hn c = q ∧
      ∃ P : DirectedDistances.KMSW.StageDrawing
        (DirectedDistances.KMSW.codeExtend c) (n - 1),
        (∀ d, ¬ (DirectedDistances.KMSW.kmswStageDirectedMap
          (DirectedDistances.KMSW.codeExtend c) (n - 1)).missing d) ∧
        (DirectedDistances.KMSW.finiteWalkClassDirectedPlaneMap c P).PolesOnExternalBoundary := by
  obtain ⟨c, hc⟩ := (DirectedDistances.Paper.Section3.kmsw ell r n hL hR hn).2 q
  obtain ⟨P, hpres, hpoles⟩ :=
    DirectedDistances.KMSW.finiteWalkClass_exists_source_boundary_domain hn c
  exact ⟨c, hc, P, hpres, hpoles⟩
#print axioms DirectedDistances.PlanarMap.DirectedPlaneMap.PolesOnExternalBoundary
#print axioms DirectedDistances.PlanarMap.SourceBoundaryDomain
#print axioms DirectedDistances.PlanarMap.SourceBipolarTriangulation
#print axioms DirectedDistances.KMSW.finiteWalkClassDirectedPlaneMap
#print axioms DirectedDistances.PlanarMap.DirectedPlaneMap.polesOnExternalBoundary_of_no_poles
#print axioms DirectedDistances.PlanarMap.PLDrawing.dartBorders_start_mem_frontier
#print axioms DirectedDistances.PlanarMap.PLDrawing.externalBoundary_of_dartBorders
#print axioms DirectedDistances.KMSW.uiqbot_ae_source_boundary_domain
#print axioms DirectedDistances.PaperProofs.Section3.uibotWholePlaneSourceDirectedMap_source_boundary_domain
#print axioms DirectedDistances.KMSW.MonotoneStageInvariant.allocated_poles_mem_frontier
#print axioms DirectedDistances.KMSW.finiteWalkClass_source_boundary_realization
#print axioms DirectedDistances.KMSW.finiteWalkClassDirectedPlaneMap_endpoints
#print axioms DirectedDistances.KMSW.finiteWalkClassDirectedPlaneMap_source_boundary_domain
#print axioms DirectedDistances.KMSW.finiteWalkClass_exists_source_boundary_domain
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.IsSingleEdgeClass
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.IsSourceBoundaryChanneled
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.isSimpleOuterBoundary_one_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.isSourceBoundaryChanneled_iff_right_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.isSourceBoundaryChanneled_iff_of_two_le_left
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.isSourceBoundaryChanneled_iff_of_two_le_right
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.filter_isSourceBoundaryChanneled_right_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.restrict_isSourceBoundaryChanneled_right_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.restrict_sourceView_eq_self_right_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.isSourceBoundaryChanneled_singleEdge
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.sourceBoundaryChanneledEquivRightOne
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.sourceBoundaryChanneledEquivRightOne_val
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.sum_filter_sourceView_right_one
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.uniform_sourceBoundaryChanneledEquivRightOne
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.map_restrict_sourceView_prod_eq
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.kmsw_left_source_view
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.kmsw_left_zeroStep_source_view
#print axioms DirectedDistances.PlanarMap.KMSWMapIsoClass.sourceBoundaryRightPrefixReversalEquiv
#print axioms DirectedDistances.PlanarMap.KMSWMapRep.IsSourceBoundaryChanneled
#print axioms DirectedDistances.PlanarMap.KMSWMapRep.isSourceBoundaryChanneled_iff
#print axioms DirectedDistances.PlanarMap.KMSWMapRep.isSourceBoundaryChanneled_iff_right_one
#print axioms DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5.finiteGeometricLaw_sourceView_filter_eq
#print axioms DirectedDistances.KMSW.finiteIsoClass_source_boundary_domain
