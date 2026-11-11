module

public import DirectedDistances.KMSW.KMSWBoundaryPrefix
public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled
public import DirectedDistances.KMSW.KMSWForwardClass

/-! # A first departure from the down prefix

paper result. A first non-down step creates another geometric edge entering
the last vertex of the existing lower-right run. Its ID and endpoints persist,
and it never belongs to the lower-right run. In a final admissible stage it
is present, including when it was initially a missing upper-right edge.

The converse below transports this obstruction to the base carrier and then
to the channeling predicate on isomorphism classes of arbitrary boundary lengths. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem step_LR_existing_conv (s : State) (c : Fin 3) {e : ℕ}
    (he : e < s.nextEdge) :
    e ∈ (kmswStep s c).LR ↔ e ∈ s.LR := by
  unfold kmswStep
  cases kmswCodeStep c with
  | left =>
      dsimp only [kmswStepOfStep]
      split <;> rfl
  | up => rfl
  | down =>
      cases hUR : s.UR with
      | cons f fs => simp only [kmswStepOfStep, hUR]
      | nil =>
          have hne : e ≠ s.nextEdge := by omega
          simp [kmswStepOfStep, hUR, State.addEdge, hne]

private theorem stage_LR_existing_conv (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    e ∈ (kmswStage w m).LR ↔ e ∈ (kmswStage w n).LR := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      exact (step_LR_existing_conv _ _
        (he.trans_le (kmswStage_nextEdge_mono w hnm))).trans ih

/-- A first non-`2` step after `i` down steps allocates a second geometric
edge entering vertex `i+1`, distinct from edge `i`. This new edge never
enters LR, whereas edge `i` stays in LR with the same head. Helper toward -/
theorem kmswStage_firstNonDown_extra_head_conv (w : ℕ → Fin 3) (i : ℕ)
    (hp : ∀ j < i, w j = 2) (hc : w i ≠ 2) :
    ∃ e, i < e ∧ ∀ m, i + 1 ≤ m →
      e < (kmswStage w m).nextEdge ∧
      (kmswStage w m).east e = i + 1 ∧
      e ∉ (kmswStage w m).LR ∧
      i ∈ (kmswStage w m).LR ∧
      (kmswStage w m).east i = i + 1 := by
  rcases kmswStage_allDown_prefix_exactLR w i hp with
    ⟨hnext, hvertex, hactive, hUL, hLR, _hUR, _hLL, hedge⟩
  have hi : i < (kmswStage w i).nextEdge := by omega
  have hhead : (kmswStage w i).east (kmswStage w i).active = i + 1 := by
    rw [hactive]
    exact (hedge i hi).2.2.1
  have hlocal : ∃ e, i < e ∧ e < (kmswStage w (i + 1)).nextEdge ∧
      (kmswStage w (i + 1)).east e = i + 1 ∧
      e ∉ (kmswStage w (i + 1)).LR := by
    by_cases hzero : w i = 0
    · have hstep : kmswStage w (i + 1) =
          kmswStepOfStep (kmswStage w i) .left := by
        simp [kmswStage, kmswStep, kmswCodeStep, hzero]
      refine ⟨i + 1, by omega, ?_⟩
      rw [hstep]
      dsimp only [kmswStepOfStep]
      split <;> simp [State.addEdge, hnext, hhead, hLR]
    · have hone : w i = 1 := by
        apply Fin.ext
        have hb := (w i).isLt
        have hz : (w i).val ≠ 0 := fun h => hzero (Fin.ext h)
        have ht : (w i).val ≠ 2 := fun h => hc (Fin.ext h)
        omega
      refine ⟨i + 2, by omega, ?_⟩
      simp [kmswStage, kmswStep, kmswCodeStep, hone, kmswStepOfStep,
        State.addEdge, hnext, hhead, hLR]
  obtain ⟨e, hie, he, heast, hnotLR⟩ := hlocal
  refine ⟨e, hie, fun m hm => ?_⟩
  have heim := he.trans_le (kmswStage_nextEdge_mono w hm)
  have heastm := (kmswStage_endpoints_stable w hm he).2.trans heast
  have hLRm : e ∉ (kmswStage w m).LR :=
    fun h => hnotLR ((stage_LR_existing_conv w hm he).mp h)
  have him : i ≤ m := by omega
  have hiLR := (stage_LR_existing_conv w him hi).mpr (hedge i hi).1
  have hihead := (kmswStage_endpoints_stable w him hi).2.trans (hedge i hi).2.2.1
  exact ⟨heim, heastm, hLRm, hiLR, hihead⟩

/-- At the final admissible stage the extra geometric edge from the first
non-down step is present, even if the step initially created it missing.
It is distinct from the persistent LR edge with the same head, and is
outside LR. Helper toward `lem-kmsw-left` -/
theorem kmswWalkClass_firstNonDown_extra_incoming_conv {ℓ r N : ℕ}
    (hn : 1 ≤ N) (c : KMSWWalkClass ℓ r N) (i : ℕ) (hi : i < N - 1)
    (hp : ∀ j < i, codeExtend c j = 2) (hc : codeExtend c i ≠ 2) :
    ∃ e, i < e ∧ e < N ∧
      (kmswStage (codeExtend c) (N - 1)).present e = true ∧
      (kmswStage (codeExtend c) (N - 1)).east e = i + 1 ∧
      e ∉ (kmswStage (codeExtend c) (N - 1)).LR ∧
      i ∈ (kmswStage (codeExtend c) (N - 1)).LR ∧
      (kmswStage (codeExtend c) (N - 1)).east i = i + 1 := by
  obtain ⟨e, hie, h⟩ := kmswStage_firstNonDown_extra_head_conv (codeExtend c) i hp hc
  obtain ⟨he, heast, hnotLR, hiLR, hihead⟩ := h (N - 1) (by omega)
  have hfinal := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hfinal
  rcases hfinal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpresent,
    _, hnext, _, _⟩
  exact ⟨e, hie, by omega, hpresent e he, heast, hnotLR, hiLR, hihead⟩

private theorem step_LR_append_conv (s : State) (c : Fin 3) :
    ∃ es, (kmswStep s c).LR = s.LR ++ es := by
  unfold kmswStep
  cases kmswCodeStep c with
  | left =>
      dsimp only [kmswStepOfStep]
      split <;> exact ⟨[], (List.append_nil _).symm⟩
  | up => exact ⟨[], (List.append_nil _).symm⟩
  | down =>
      cases h : s.UR with
      | nil => exact ⟨[s.nextEdge], by simp only [kmswStepOfStep, h]⟩
      | cons e es => exact ⟨[], by simp only [kmswStepOfStep, h, List.append_nil]⟩

private theorem stage_LR_append_conv (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m) :
    ∃ es, (kmswStage w m).LR = (kmswStage w n).LR ++ es := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm⟩
  | succ m _ ih =>
      obtain ⟨es, hes⟩ := ih
      obtain ⟨fs, hfs⟩ := step_LR_append_conv (kmswStage w m) (w m)
      exact ⟨es ++ fs, by rw [kmswStage, hfs, hes, List.append_assoc]⟩

private theorem chain_rank_head_lt_end_conv (s : State) (rank : ℕ → ℚ)
    (es : List ℕ) (hne : es ≠ []) (hchain : WestEastChain s es)
    (hstrict : ∀ e ∈ es, rank (s.west e) < rank (s.east e)) :
    rank (s.west (es.head hne)) < rank (s.east (es.getLast hne)) := by
  induction es with
  | nil => exact (hne rfl).elim
  | cons e es ih =>
      cases es with
      | nil => simpa only [List.head_cons, List.getLast_singleton] using hstrict e (by simp)
      | cons f fs =>
          have hrel : s.east e = s.west f := hchain.rel
          have ht := ih (by simp) hchain.tail
            (fun g hg => hstrict g (List.mem_cons_of_mem e hg))
          have he := hstrict e (by simp)
          simp only [List.head_cons, List.getLast_cons_cons] at ht ⊢
          exact he.trans (by simpa only [hrel] using ht)

private theorem R_lower_conv (w : ℕ → Fin 3) (n : ℕ) : -(n : ℤ) ≤ R w n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
      have hb : ∀ c : Fin 3, -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 := by
        intro c
        fin_cases c <;> decide
      have hs : R w (n + 1) = R w n +
          (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
      have hstep := hb (w n)
      rw [hs]
      push_cast
      omega

/-- A first departure before the required `r−1` down steps yields a
present edge outside both final boundary runs. Its head agrees with that
of the persistent LR edge `i`, and differs from the final active edge's
head (the terminal LR vertex). Helper toward `lem-kmsw-left` -/
theorem kmswWalkClass_firstNonDown_outside_boundary_runs_conv {r N : ℕ}
    (hn : 1 ≤ N) (c : KMSWWalkClass 1 r N) (i : ℕ) (hi : i < r - 1)
    (hp : ∀ j < i, codeExtend c j = 2) (hc : codeExtend c i ≠ 2) :
    ∃ e, i < e ∧ e < N ∧
      (kmswStage (codeExtend c) (N - 1)).present e = true ∧
      (kmswStage (codeExtend c) (N - 1)).east e = i + 1 ∧
      (kmswStage (codeExtend c) (N - 1)).east e ≠
        (kmswStage (codeExtend c) (N - 1)).east
          (kmswStage (codeExtend c) (N - 1)).active ∧
      e ∉ (kmswStage (codeExtend c) (N - 1)).UL ∧
      e ∉ (kmswStage (codeExtend c) (N - 1)).LR ∧
      i ∈ (kmswStage (codeExtend c) (N - 1)).LR ∧
      (kmswStage (codeExtend c) (N - 1)).east i = i + 1 := by
  have hR := R_lower_conv (codeExtend c) (N - 1)
  have hRend : R (codeExtend c) (N - 1) = -(r : ℤ) + 1 := by
    rw [RandomWalk.kmsw_R_eq]
    exact congrArg Prod.snd c.property.1
  have hitime : i < N - 1 := by omega
  obtain ⟨e, hie, heN, hpres, heast, hnotLR, hiLR, hihead⟩ :=
    kmswWalkClass_firstNonDown_extra_incoming_conv hn c i hitime hp hc
  let w := codeExtend c
  let m := N - 1
  let s := kmswStage w m
  have hfinal := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hfinal
  rcases hfinal with ⟨_, _, _, _, _, _, _, _, hULlen, hLRlen, _, _, hUR, hLL,
    _, _, _, _, _⟩
  change s.UL.length = 1 at hULlen
  change s.LR.length = r at hLRlen
  change (kmswStage w m).UR = [] at hUR
  change (kmswStage w m).LL = [] at hLL
  have hpLR := (kmswStage_allDown_prefix_exactLR w i hp).2.2.2.2.1
  obtain ⟨tail, htail⟩ := stage_LR_append_conv w (by omega : i ≤ m)
  rw [hpLR] at htail
  have htailne : tail ≠ [] := by
    intro hnil
    have hlen := congrArg List.length htail
    simp only [hnil, List.append_nil, List.length_range] at hlen
    change s.LR.length = i + 1 at hlen
    omega
  have hchain := kmswStage_boundary_chain_invariant w m
  have hlow : WestEastChain s s.LR := by
    simpa only [hLL, List.nil_append] using hchain.2.1
  have htailchain : WestEastChain s tail := by
    rw [htail] at hlow
    exact hlow.right_of_append
  have hjoin : s.east i = s.west (tail.head htailne) := by
    rw [htail, List.range_succ, List.append_assoc] at hlow
    have hcons := hlow.right_of_append
    have hrel := hcons.rel_getLast_head_of_append (by simp) htailne
    simpa only [List.getLast_singleton] using hrel
  have hrank : kmswStageRank w m (s.west (tail.head htailne)) <
      kmswStageRank w m (s.east (tail.getLast htailne)) := by
    apply chain_rank_head_lt_end_conv s (kmswStageRank w m) tail htailne htailchain
    intro f hf
    apply kmswStageRank_strict w m f
    apply stageRun_edge_bound w m f
    exact Or.inr (by rw [htail]; exact List.mem_append_right _ hf)
  have hLRne : s.LR ≠ [] := hchain.2.2.2.2.1
  have hlast : s.LR.getLast hLRne = tail.getLast htailne := by
    change (kmswStage w m).LR.getLast _ = tail.getLast htailne
    simp only [htail, List.getLast_append_of_right_ne_nil _ _ htailne]
  have hactiveEnd : s.east s.active = s.east (s.LR.getLast hLRne) :=
    hchain.2.2.2.2.2.2 hLRne hUR
  have hneq : s.east e ≠ s.east s.active := by
    intro heq
    have hihead' : s.east i = i + 1 := hihead
    have heast' : s.east e = i + 1 := heast
    rw [← hjoin, hihead', ← heast', heq, hactiveEnd, hlast] at hrank
    exact (lt_irrefl _ hrank)
  have hnotUL : e ∉ s.UL := by
    intro hmem
    obtain ⟨es, hes⟩ := kmswStage_UL_last w m
    have hlen := congrArg List.length hes
    simp only [List.length_append, List.length_singleton] at hlen
    change s.UL.length = es.length + 1 at hlen
    have hesnil : es = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hesnil, List.nil_append] at hes
    rw [hes] at hmem
    have heq : e = s.active := List.mem_singleton.mp hmem
    exact hneq (congrArg s.east heq)
  exact ⟨e, hie, heN, hpres, heast, hneq, hnotUL, hnotLR, hiLR, hihead⟩

private theorem base_LR_tail_mem_conv {ℓ r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N)
    (e : Fin (kmswStage (codeExtend c) (N - 1)).nextEdge)
    (he : e.val ∈ (kmswStage (codeExtend c) (N - 1)).LR) :
    (e, false) ∈ (kmswWalkClassBase hn c).rightPath.darts := by
  let B := kmswWalkClassBase hn c
  have h := (kmswStageDirectedMap_LR_bridge (codeExtend c) (N - 1) e).mp he
  have hr := B.outerSplit.2.2.2.1 (e, true)
  have hm : (e, true) ∈ B.rightPath.darts.reverse.map
      B.map.toCombinatorialMap.edgeInv := hr.mpr h
  obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
  have hdeq : d = (e, false) := by
    have hf := congrArg B.map.toCombinatorialMap.edgeInv heq
    exact (B.map.toCombinatorialMap.edgeInv_invol d).symm.trans hf
  exact hdeq ▸ List.mem_reverse.mp hd

private theorem base_not_boundary_conv {ℓ r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N)
    (e : Fin (kmswStage (codeExtend c) (N - 1)).nextEdge)
    (hu : e.val ∉ (kmswStage (codeExtend c) (N - 1)).UL)
    (hl : e.val ∉ (kmswStage (codeExtend c) (N - 1)).LR) :
    ¬ (kmswWalkClassBase hn c).boundaryEdgeBase (e, false) := by
  let B := kmswWalkClassBase hn c
  rintro ⟨d, hd, hc⟩
  have hid : d.1 = e := by
    rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap
      (e, false) d).mp hc with h | h
    · exact congrArg Prod.fst h
    · exact congrArg Prod.fst h
  rcases List.mem_append.mp hd with hd | hd
  · have hm := (B.outerSplit.2.2.1 d).mp hd
    have hfin := (kmswStageULDartsFinset_map_mem (codeExtend c) (N - 1) d).mpr hm
    have hv := (kmswStageULDartsFinset_mem (codeExtend c) (N - 1) d).mp hfin
    exact hu (hid ▸ hv.2)
  · have hm : B.map.toCombinatorialMap.edgeInv d ∈
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
      List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
    have hlr := (B.outerSplit.2.2.2.1 _).mp hm
    have hfin := (kmswStageLRDartsFinset_map_mem (codeExtend c) (N - 1) _).mpr hlr
    have hv := (kmswStageLRDartsFinset_mem (codeExtend c) (N - 1) _).mp hfin
    exact hl (hid ▸ hv.2)

private theorem base_sink_label_conv {ℓ r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) :
    (stageVertexEquiv (codeExtend c) (N - 1)
      (kmswWalkClassBase hn c).sink).val =
      (kmswStage (codeExtend c) (N - 1)).east
        (kmswStage (codeExtend c) (N - 1)).active := by
  let w := codeExtend c
  let m := N - 1
  have hfinal := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hfinal
  rcases hfinal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, _, _, _, _, _, _⟩
  have hLR := kmswStage_LR_nonempty w m
  have ha := (kmswStage_boundary_chain_invariant w m).2.2.2.2.2.2 hLR hUR
  rw [ha]
  change stageEndpoint (kmswStage w m) ((kmswStageLRDartRun w m).head _) = _
  simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
    stageEndpoint, List.head_reverse, ↓reduceIte]

private theorem prefix_of_base_isChanneled_conv {r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass 1 r N)
    (hbc : (kmswWalkClassBase hn c).IsBoundaryChanneledBase) :
    ∀ i < r - 1, codeExtend c i = 2 := by
  classical
  by_contra h
  have hex : ∃ i, i < r - 1 ∧ codeExtend c i ≠ 2 := by
    push Not at h
    exact h
  let i := Nat.find hex
  have hi := (Nat.find_spec hex).1
  have hc := (Nat.find_spec hex).2
  have hp : ∀ j < i, codeExtend c j = 2 := by
    intro j hj
    by_contra hne
    exact Nat.find_min hex hj ⟨hj.trans hi, hne⟩
  obtain ⟨e, hie, heN, hpres, heast, hneq, hnu, hnl, hiLR, hihead⟩ :=
    kmswWalkClass_firstNonDown_outside_boundary_runs_conv hn c i hi hp hc
  let w := codeExtend c
  let m := N - 1
  let s := kmswStage w m
  let B := kmswWalkClassBase hn c
  have heb : e < s.nextEdge := by
    have hf := kmswWalkClassMap_mem_sourceClass hn c
    dsimp only at hf
    rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq, _, _⟩
    change s.nextEdge = N at heq
    omega
  let ef : Fin s.nextEdge := ⟨e, heb⟩
  have hib : i < s.nextEdge := by omega
  let fi : Fin s.nextEdge := ⟨i, hib⟩
  let d : StageDart s.nextEdge := (ef, false)
  have hhead : dartHeadVertex B.map d = dartHeadVertex B.map (fi, false) := by
    apply (stageVertexEquiv w m).injective
    apply Fin.ext
    change s.east e = s.east i
    exact heast.trans hihead.symm
  have hbound : dartHeadVertex B.map d ∈ B.boundaryVerticesBase := by
    right
    rw [hhead]
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (base_LR_tail_mem_conv hn c fi hiLR)
    have hs := B.rightPath.edge_step j
    rw [← hj, ← hs.2.2.2]
    exact List.get_mem _ _
  have hnotSink : dartHeadVertex B.map d ≠ B.sink := by
    intro heq
    apply hneq
    have hv := congrArg (fun v => ((stageVertexEquiv w m) v).val) heq
    exact hv.trans (base_sink_label_conv hn c)
  have ht : B.map.tail d := ⟨hpres, rfl⟩
  exact base_not_boundary_conv hn c ef hnu hnl
    (hbc d (B.noMissingDarts d) ht hbound hnotSink)



theorem prefix_codeExtend_of_kmswToMapIsoClass_isChanneled {r N : ℕ}
    (hn : 1 ≤ N) (c : KMSWWalkClass 1 r N)
    (h : (kmswToMapIsoClass hn c).IsChanneled) :
    ∀ i < r - 1, codeExtend c i = 2 := by
  have hr : (kmswWalkClassRep hn c).IsChanneled :=
    (KMSWMapIsoClass.isChanneled_mk _).mp h
  let B := kmswWalkClassBase hn c
  let E := Fintype.equivFin (StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge)
  have ht : (B.transport E).IsBoundaryChanneledBase := hr
  exact prefix_of_base_isChanneled_conv hn c
    ((isBoundaryChanneledBase_iff_of_iso (B.transportIso E)).mpr ht)



theorem prefix_of_kmswToMapIsoClass_isChanneled {r N : ℕ}
    (hn : 1 ≤ N) (c : KMSWWalkClass 1 r N)
    (h : (kmswToMapIsoClass hn c).IsChanneled) :
    ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2 := by
  intro i hi
  have hp := prefix_codeExtend_of_kmswToMapIsoClass_isChanneled hn c h i.val hi
  simpa only [codeExtend_of_lt c i.val i.isLt] using hp

end DirectedDistances.KMSW
