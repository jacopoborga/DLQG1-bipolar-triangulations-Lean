module

public import DirectedDistances.KMSW.KMSWLeftProcedureUniform

/-! Supporting lemmas for paper labels `lem-kmsw-left` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

 
theorem kmswZeroStepStage_initialData (w : ℕ → Fin 3) :
    (kmswStage w 0).nextEdge = 1 ∧
      (kmswStage w 0).UL = [0] ∧ (kmswStage w 0).LR = [0] ∧
      (kmswStage w 0).UR = [] ∧ (kmswStage w 0).LL = [] := by
  simp [kmswStage, kmswInit]

 
theorem kmswZeroStepStage_outerDarts (w : ℕ → Fin 3)
    (d : StageDart (kmswStage w 0).nextEdge) :
    (kmswStageDirectedMap w 0).IsOuter d := by
  rcases d with ⟨e, b⟩
  have he : e.val = 0 := by
    have h := e.isLt
    simp [kmswStage, kmswInit] at h
    omega
  have he' : e = ⟨0, by simp [kmswStage, kmswInit]⟩ := Fin.ext he
  cases he'
  cases b
  · change Equiv.Perm.SameCycle _ _ _
    exact ⟨0, rfl⟩
  · change Equiv.Perm.SameCycle _ _ _
    exact ⟨1, rfl⟩

 
theorem kmswOneOneRep_isChanneled {N : ℕ} (R : KMSWMapRep 1 1 N) :
    R.IsChanneled := by
  change R.B.IsBoundaryChanneledBase
  intro d _ htail hboundary hnotSink
  change dartHeadVertex R.B.map d ∈ R.B.leftPath.vertices ∨
    dartHeadVertex R.B.map d ∈ R.B.rightPath.vertices at hboundary
  have hstep : R.B.map.directedStep
      (dartTailVertex R.B.map d) (dartHeadVertex R.B.map d) := by
    exact ⟨d, R.B.noMissingDarts d, htail, rfl, rfl⟩
  rcases hboundary with hleft | hright
  · rcases leftPath_vertex_mem_endpoint R.B hleft with hsource | hsink
    · rw [hsource] at hstep
      exact (R.B.isSource ⟨dartTailVertex R.B.map d, hstep⟩).elim
    · exact (hnotSink hsink).elim
  · rcases rightPath_vertex_mem_endpoint R.B hright with hsource | hsink
    · rw [hsource] at hstep
      exact (R.B.isSource ⟨dartTailVertex R.B.map d, hstep⟩).elim
    · exact (hnotSink hsink).elim

 
theorem kmswZeroStep_singleEdge_isChanneled :
    KMSWMapRep.singleEdge.IsChanneled :=
  kmswOneOneRep_isChanneled KMSWMapRep.singleEdge



noncomputable def kmswZeroStepMapClass :
    {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled} :=
  ⟨KMSWMapIsoClass.mk KMSWMapRep.singleEdge,
    (KMSWMapIsoClass.isChanneled_mk _).2 kmswZeroStep_singleEdge_isChanneled⟩



theorem kmswOneOneRep_nonBoundaryEdgeCount_zero
    (R : KMSWMapRep 1 1 1) : R.nonBoundaryEdgeCount = 0 := by
  classical
  change Fintype.card
    {e : CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap //
      ∀ d ∈ R.B.leftPath.darts ++ R.B.rightPath.darts,
        Quotient.mk _ d ≠ e} = 0
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨?_⟩
  intro e
  let i : Fin R.B.leftPath.darts.length :=
    ⟨0, by rw [R.B.leftPath.darts_length]; omega⟩
  let d := R.B.leftPath.darts.get i
  have hd : d ∈ R.B.leftPath.darts := List.get_mem _ i
  have hcard : Fintype.card
      (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) = 1 := by
    change R.B.map.toCombinatorialMap.numEdges = 1
    exact R.edges
  obtain ⟨e₀, he₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have heq : e.val = Quotient.mk _ d := by
    calc
      e.val = e₀ := he₀ _
      _ = Quotient.mk _ d := (he₀ _).symm
  exact e.property d (List.mem_append_left _ hd) heq.symm



theorem kmswZeroStepMapClass_nonBoundaryEdgeCount_zero :
    KMSWMapIsoClass.nonBoundaryEdgeCount kmswZeroStepMapClass.val = 0 := by
  change KMSWMapIsoClass.nonBoundaryEdgeCount
    (KMSWMapIsoClass.mk KMSWMapRep.singleEdge) = 0
  rw [KMSWMapIsoClass.nonBoundaryEdgeCount_mk]
  exact kmswOneOneRep_nonBoundaryEdgeCount_zero KMSWMapRep.singleEdge

private theorem kmswZeroStep_finalPrefix :
    KMSWPeanoPrefixExistsFinal 1 1 1 := by
  intro R
  exact ⟨by simpa only [Nat.sub_self] using
    kmswPeanoPrefixEmbedding_zero R.B (kmswRepInverseWalkClass R)⟩



theorem kmswZeroStepMapClass_unique
    (q : {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled}) :
    q = kmswZeroStepMapClass := by
  have hsurj := kmswToMapIsoClass_surjective_of_prefix
    kmswZeroStep_finalPrefix (by omega : 1 ≤ 1)
  obtain ⟨c, hc⟩ := hsurj q.val
  obtain ⟨c', hc'⟩ := hsurj kmswZeroStepMapClass.val
  have hcc : c = c' := by
    apply Subtype.ext
    funext i
    have hi : Fin 0 := by simpa using i
    exact Fin.elim0 hi
  apply Subtype.ext
  change q.val = kmswZeroStepMapClass.val
  exact hc.symm.trans
    ((congrArg (kmswToMapIsoClass (by omega)) hcc).trans hc')



theorem kmswZeroStep_singleEdge_partialMap_iso
    (c0 : Fin (1 - 1) → Fin 3) :
    Nonempty (DirectedMapWithMissingIso KMSWMapRep.singleEdge.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := 1) c0) 0)) := by
  have hc : KMSWLeftWalkAdmissible 1 0 c0 := by
    simp [KMSWLeftWalkAdmissible, RandomWalk.integrateCodes]
  let c : KMSWLeftWalkClass 1 0 := ⟨c0, hc⟩
  let q := kmswLeftEndpointSideEquivOne 0 c
  have hStage : Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := 1) c0) 0)) := by
    simpa [q, c] using kmswLeftEndpointSideEquivOne_partialMapIso 0 c
  have hq := kmswZeroStepMapClass_unique q
  have hclass : KMSWMapIsoClass.mk q.val.out =
      KMSWMapIsoClass.mk KMSWMapRep.singleEdge := by
    calc
      KMSWMapIsoClass.mk q.val.out = q.val := Quotient.out_eq _
      _ = KMSWMapIsoClass.mk KMSWMapRep.singleEdge := by
        change q.val = kmswZeroStepMapClass.val
        exact congrArg Subtype.val hq
  obtain ⟨J⟩ := (KMSWMapRep.mk_eq_mk_iff_partialMapIso_one
    KMSWMapRep.singleEdge q.val.out).mp hclass.symm
  exact ⟨J.trans hStage.some⟩




theorem kmsw_left_zeroStep_procedureReading :
    ∃ F : KMSWLeftWalkClass 1 0 ≃
      {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled},
      (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0))) ∧
      (∀ c (q : {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0)) →
            q = F c) ∧
      (∀ q : {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = 0) := by
  refine ⟨kmswLeftEndpointSideEquivOne 0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact kmswLeftEndpointSideEquivOne_partialMapIso 0 c
  · intro c q _
    exact (kmswZeroStepMapClass_unique q).trans
      (kmswZeroStepMapClass_unique (kmswLeftEndpointSideEquivOne 0 c)).symm
  · intro q
    rw [kmswZeroStepMapClass_unique q]
    exact kmswZeroStepMapClass_nonBoundaryEdgeCount_zero

end DirectedDistances.KMSW
