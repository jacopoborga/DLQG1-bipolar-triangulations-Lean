module

public import DirectedDistances.KMSW.KMSWBoundaryPrefixFinal
import all DirectedDistances.KMSW.KMSWBoundaryPrefixConverse
import DirectedDistances.PlanarMap.KMSWRightEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled

/-! Supporting lemmas for paper labels `lem-kmsw-left` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem base_right_dart_LR_fwd {r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass 1 r N)
    {d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge}
    (hd : d ∈ (kmswWalkClassBase hn c).rightPath.darts) :
    d.1.val ∈ (kmswStage (codeExtend c) (N - 1)).LR := by
  let B := kmswWalkClassBase hn c
  have hm : B.map.toCombinatorialMap.edgeInv d ∈
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
    List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  have hlr := (B.outerSplit.2.2.2.1 _).mp hm
  have hfin := (kmswStageLRDartsFinset_map_mem (codeExtend c) (N - 1) _).mpr hlr
  exact ((kmswStageLRDartsFinset_mem (codeExtend c) (N - 1) _).mp hfin).2

private theorem base_right_vertex_incoming_fwd {D : Type*} [Fintype D]
    [DecidableEq D] {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r)
    {v : MapVertex B.map} (hv : v ∈ B.rightPath.vertices)
    (hns : v ≠ B.source) :
    ∃ d ∈ B.rightPath.darts, dartHeadVertex B.map d = v := by
  have hdlen := B.rightPath.darts_length
  have hvlen := B.rightPath.vertices_length
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have hjpos : 0 < j.val := by
    by_contra h
    have hj0 : j = ⟨0, by rw [B.rightPath.vertices_length]; omega⟩ :=
      Fin.ext (by change j.val = 0; omega)
    apply hns
    rw [← hj, hj0]
    exact B.rightPath.start_vertex
  have hjlt : j.val ≤ r := by
    have hjbound : j.val < r + 1 := by
      simpa only [B.rightPath.vertices_length] using j.isLt
    omega
  let i : Fin B.rightPath.darts.length :=
    ⟨j.val - 1, by rw [B.rightPath.darts_length]; omega⟩
  refine ⟨B.rightPath.darts.get i, List.get_mem _ _, ?_⟩
  have hs := (B.rightPath.edge_step i).2.2.2
  have hij : (⟨i.val + 1, by omega⟩ : Fin B.rightPath.vertices.length) = j := by
    apply Fin.ext
    dsimp only [i]
    omega
  rw [hij] at hs
  exact hs.symm.trans hj

private theorem base_right_head_label_le_fwd {r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2)
    {d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge}
    (hd : d ∈ (kmswWalkClassBase hn c).rightPath.darts) :
    ((stageVertexEquiv (codeExtend c) (N - 1))
      (dartHeadVertex (kmswWalkClassBase hn c).map d)).val ≤ r := by
  let B := kmswWalkClassBase hn c
  have hr := B.right_length_pos
  have hLR := kmswWalkClassBase_LR_eq_range_of_downPrefix hn hr c hpre
  have he := base_right_dart_LR_fwd hn c hd
  rw [hLR, List.mem_range] at he
  have hlabels := kmswWalkClassBase_LR_endpoint_labels_of_downPrefix hn hr c hpre d.1 he
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have ht := (B.rightPath.edge_step i).2.1
  rw [hi] at ht
  have hb : d.2 = false := ht.2
  rcases d with ⟨e, b⟩
  dsimp only at hb
  subst b
  change (kmswStage (codeExtend c) (N - 1)).east e.val ≤ r
  have heast : (kmswStage (codeExtend c) (N - 1)).east e.val = e.val + 1 := hlabels.2
  have he' : e.val < r := he
  omega

private theorem base_sink_label_fwd {r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2)
    (hm : r - 1 ≤ N - 1)
    (hcodes : ∀ i < r - 1, codeExtend c i = 2) :
    ((stageVertexEquiv (codeExtend c) (N - 1)) (kmswWalkClassBase hn c).sink).val = r := by
  let B := kmswWalkClassBase hn c
  have hr := B.right_length_pos
  have hdlen := B.rightPath.darts_length
  have hvlen := B.rightPath.vertices_length
  let i : Fin B.rightPath.darts.length :=
    ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩
  have hs := (B.rightPath.edge_step i).2.2.2
  have hiend : (⟨i.val + 1, by omega⟩ : Fin B.rightPath.vertices.length) =
      ⟨r, by rw [B.rightPath.vertices_length]; omega⟩ := by
    apply Fin.ext
    dsimp only [i]
    omega
  rw [hiend, B.rightPath.end_vertex] at hs
  have hle := base_right_head_label_le_fwd hn c hpre (List.get_mem B.rightPath.darts i)
  rw [← hs] at hle
  have hge := (kmswStage_activeEast_and_presentEast_ge_of_downPrefix
    (codeExtend c) hr hcodes (N - 1) hm).1
  rw [base_sink_label_conv hn c]
  rw [base_sink_label_conv hn c] at hle
  omega

 
theorem kmswToMapIsoClass_isChanneled_of_prefix {r N : ℕ}
    (hn : 1 ≤ N) (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2) :
    (kmswToMapIsoClass hn c).IsChanneled := by
  classical
  let B := kmswWalkClassBase hn c
  have hr := B.right_length_pos
  have hR := R_lower_conv (codeExtend c) (N - 1)
  have hRend : R (codeExtend c) (N - 1) = -(r : ℤ) + 1 := by
    rw [RandomWalk.kmsw_R_eq]
    exact congrArg Prod.snd c.property.1
  have hm : r - 1 ≤ N - 1 := by omega
  have hcodes : ∀ i < r - 1, codeExtend c i = 2 := by
    intro i hi
    rw [codeExtend_of_lt c i (by omega)]
    exact hpre ⟨i, by omega⟩ hi
  have hbc : B.IsBoundaryChanneledBase := by
    intro d hmiss ht hb hnotSink
    have hnotSource : dartHeadVertex B.map d ≠ B.source := by
      intro heq
      exact B.isSource ⟨dartTailVertex B.map d, d, hmiss, ht, rfl, heq⟩
    rcases hb with hleft | hright
    · rcases leftPath_vertex_mem_endpoint B hleft with hs | ht
      · exact (hnotSource hs).elim
      · exact (hnotSink ht).elim
    · obtain ⟨f, hf, hhead⟩ := base_right_vertex_incoming_fwd B hright hnotSource
      have hle := base_right_head_label_le_fwd hn c hpre hf
      rw [hhead] at hle
      have hne : ((stageVertexEquiv (codeExtend c) (N - 1))
          (dartHeadVertex B.map d)).val ≠ r := by
        intro heq
        apply hnotSink
        apply (stageVertexEquiv (codeExtend c) (N - 1)).injective
        apply Fin.ext
        exact heq.trans (base_sink_label_fwd hn c hpre hm hcodes).symm
      have hlt : ((stageVertexEquiv (codeExtend c) (N - 1))
          (dartHeadVertex B.map d)).val < r := by omega
      have hbfalse : d.2 = false := ht.2
      rcases d with ⟨e, b⟩
      dsimp only at hbfalse
      subst b
      change (kmswStage (codeExtend c) (N - 1)).east e.val < r at hlt
      have he : e.val < r := by
        by_contra h
        have hge := (kmswStage_activeEast_and_presentEast_ge_of_downPrefix
          (codeExtend c) hr hcodes (N - 1) hm).2 e.val (by omega) e.isLt
          (Or.inl ht.1)
        omega
      have hLR := kmswWalkClassBase_LR_eq_range_of_downPrefix hn hr c hpre
      have hem : e.val ∈ (kmswStage (codeExtend c) (N - 1)).LR := by
        rw [hLR, List.mem_range]
        exact he
      exact ⟨(e, false), List.mem_append_right _ (base_LR_tail_mem_conv hn c e hem),
        Equiv.Perm.SameCycle.rfl⟩
  apply (KMSWMapIsoClass.isChanneled_mk _).mpr
  let E := Fintype.equivFin (StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge)
  change (B.transport E).IsBoundaryChanneledBase
  exact (isBoundaryChanneledBase_iff_of_iso (B.transportIso E)).mp hbc

end DirectedDistances.KMSW
