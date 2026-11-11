module

public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneExteriorPaths

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.KMSW

open Set DirectedDistances.PlanarMap

/-- The KMSW constructed plane-realization statement holds under the UIQBOT hypotheses
Helper discharging the plane-realization obligation of adjudication n308; not a paper
result. -/
theorem kmswConstructedPlaneRealization (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 := by
  have hfam := monotone_family_all w
  have hbd := monotoneRegionBoundedExhaustion_of_KMSW w hfin htrans hR hL0
    (familyQ w hfam) (familyG w hfam)
  refine kmswConstructedPlaneRealization_of_family_exterior w hfin htrans hR hL0 hfam
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact monotoneLimitExterior_isOpen_of_boundedExhaustion _ _ hbd
  · exact monotoneLimitExterior_isPathConnected_of_KMSW w hfin htrans hR hL0 _ _
  · exact monotoneLimitExterior_unbounded_of_xmin_zero _ _
      (fun n => monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 _)
  · exact monotoneLimitExterior_frontier_subset_trace _ _ hbd
  · exact fun n => monotoneLimitExterior_disjoint_stageImage _ _ n
  · intro z hz hzE
    apply monotoneStageRegionUnion_mem_cap_of_not_trace _ _ (not_not.mp hzE)
    simp only [monotoneLayoutTraceUnion, mem_iUnion, not_exists]
    exact hz

end DirectedDistances.KMSW
