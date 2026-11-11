module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.KMSWWalkClassRepStage
import DirectedDistances.PlanarMap.LexLeftmostBaseIso

/-! # Directed paths in finite KMSW stage maps

stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Quiver

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
@[expose] noncomputable def stageMapVertex (w : ℕ → Fin 3) (n : ℕ)
    (v : MapVertex (kmswStageDirectedMap w n)) : StagePresentVertex w n :=
  ⟨(stageVertexEquiv w n v).val⟩

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMapVertex_injective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Injective (stageMapVertex w n) := by
  intro u v h
  apply (stageVertexEquiv w n).injective
  apply Fin.ext
  exact congrArg StagePresentVertex.id h

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMapVertex_tail (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d)).id =
      stageEndpoint (kmswStage w n) d := rfl

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMap_dart_arrow_iff (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (u v : MapVertex (kmswStageDirectedMap w n)) :
    (¬ (kmswStageDirectedMap w n).missing d ∧
      (kmswStageDirectedMap w n).tail d ∧
      dartTailVertex (kmswStageDirectedMap w n) d = u ∧
      dartHeadVertex (kmswStageDirectedMap w n) d = v) ↔
    (d.2 = false ∧ (kmswStage w n).present d.1.val = true ∧
      (kmswStage w n).west d.1.val = (stageMapVertex w n u).id ∧
      (kmswStage w n).east d.1.val = (stageMapVertex w n v).id) := by
  have hi := stageMapVertex_injective w n
  constructor
  · rintro ⟨_, ht, hu, hv⟩
    have ht' : (kmswStage w n).present d.1.val = true ∧ d.2 = false := ht
    refine ⟨ht'.2, ht'.1, ?_, ?_⟩
    · rw [← hu, stageMapVertex_tail]
      simp only [stageEndpoint, ht'.2, Bool.false_eq_true, ↓reduceIte]
    · rw [← hv]
      change (kmswStage w n).east d.1.val = stageEndpoint (kmswStage w n)
        (edgeFlip (kmswStage w n).nextEdge d)
      change (kmswStage w n).east d.1.val =
        if !d.2 then (kmswStage w n).east d.1.val else (kmswStage w n).west d.1.val
      rw [ht'.2]
      rfl
  · rintro ⟨hb, hp, hu, hv⟩
    refine ⟨?_, ⟨hp, hb⟩, ?_, ?_⟩
    · change ¬ (kmswStage w n).present d.1.val = false
      rw [hp]
      decide
    · apply hi
      apply congrArg (StagePresentVertex.mk (w := w) (n := n))
      change stageEndpoint (kmswStage w n) d = _
      simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte, stageMapVertex]
        using hu
    · apply hi
      apply congrArg (StagePresentVertex.mk (w := w) (n := n))
      change stageEndpoint (kmswStage w n)
        (edgeFlip (kmswStage w n).nextEdge d) = _
      change (if !d.2 then (kmswStage w n).east d.1.val
        else (kmswStage w n).west d.1.val) = _
      simpa only [hb, Bool.not_false, ↓reduceIte, stageMapVertex] using hv

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMap_directedStep_iff (w : ℕ → Fin 3) (n : ℕ)
    (u v : MapVertex (kmswStageDirectedMap w n)) :
    (kmswStageDirectedMap w n).directedStep u v ↔
      Nonempty (stageMapVertex w n u ⟶ stageMapVertex w n v) := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨_, hp, hu, hv⟩ := (stageMap_dart_arrow_iff w n d u v).1 hd
    exact ⟨⟨d.1.val, d.1.isLt, hp, hu, hv⟩⟩
  · rintro ⟨e⟩
    let d : StageDart (kmswStage w n).nextEdge := (⟨e.val, e.property.1⟩, false)
    exact ⟨d, (stageMap_dart_arrow_iff w n d u v).2
      ⟨rfl, e.property.2.1, e.property.2.2⟩⟩

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private structure DartWalk {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (s t : MapVertex M) (k : ℕ) where
  darts : List D
  vertices : List (MapVertex M)
  darts_length : darts.length = k
  vertices_length : vertices.length = k + 1
  start_vertex : vertices[0]'(by omega) = s
  end_vertex : vertices[k]'(by omega) = t
  edge_step : ∀ i : Fin darts.length,
    ¬ M.missing (darts.get i) ∧ M.tail (darts.get i) ∧
      vertices[i.val]'(by omega) = dartTailVertex M (darts.get i) ∧
      vertices[i.val + 1]'(by omega) = dartHeadVertex M (darts.get i)

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private def DartWalk.toSimple {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : DartWalk M s t k) (ha : M.IsAcyclic) :
    SimpleDirectedDartPath M s t k := by
  have hc : P.vertices.IsChain M.directedStep := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hd : i < P.darts.length := by
      have := P.vertices_length
      have := P.darts_length
      omega
    obtain ⟨hm, ht, hu, hv⟩ := P.edge_step ⟨i, hd⟩
    exact ⟨P.darts.get ⟨i, hd⟩, hm, ht, hu.symm, hv.symm⟩
  have hp : P.vertices.Pairwise (Relation.TransGen M.directedStep) :=
    List.isChain_iff_pairwise.mp (hc.imp fun _ _ h => Relation.TransGen.single h)
  exact {
    darts := P.darts
    vertices := P.vertices
    darts_length := P.darts_length
    vertices_length := P.vertices_length
    vertices_nodup := hp.imp (by intro a b h heq; subst b; exact ha a h)
    start_vertex := P.start_vertex
    end_vertex := P.end_vertex
    edge_step := P.edge_step }

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private def DartWalk.nil {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (s : MapVertex M) : DartWalk M s s 0 where
  darts := []
  vertices := [s]
  darts_length := rfl
  vertices_length := rfl
  start_vertex := rfl
  end_vertex := rfl
  edge_step := fun i => Fin.elim0 i

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private def DartWalk.cons {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t z : MapVertex M} {k : ℕ}
    (P : DartWalk M s t k) (d : D)
    (hd : ¬ M.missing d ∧ M.tail d ∧
      dartTailVertex M d = t ∧ dartHeadVertex M d = z) :
    DartWalk M s z (k + 1) := by
  refine {
    darts := P.darts ++ [d]
    vertices := P.vertices ++ [z]
    darts_length := by simp only [List.length_append, List.length_singleton, P.darts_length]
    vertices_length := by
      simp only [List.length_append, List.length_singleton, P.vertices_length]
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_ }
  · rw [List.getElem_append_left (by rw [P.vertices_length]; omega)]
    exact P.start_vertex
  · rw [List.getElem_append_right (by rw [P.vertices_length])]
    simp only [P.vertices_length, Nat.sub_self, List.getElem_cons_zero]
  · intro i
    by_cases hi : i.val < P.darts.length
    · have hi' : i.val + 1 < P.vertices.length := by
        have := P.vertices_length
        have := P.darts_length
        omega
      simpa only [List.get_eq_getElem, List.getElem_append_left hi,
        List.getElem_append_left (by omega : i.val < P.vertices.length),
        List.getElem_append_left hi'] using P.edge_step ⟨i.val, hi⟩
    · have hieq : i.val = k := by
        have := i.isLt
        simp only [List.length_append, List.length_singleton, P.darts_length] at this
        have := P.darts_length
        omega
      have hget : (P.darts ++ [d]).get i = d := by
        change (P.darts ++ [d])[i.val] = d
        rw [List.getElem_append_right (Nat.le_of_not_gt hi)]
        simp only [hieq, P.darts_length, Nat.sub_self, List.getElem_cons_zero]
      rw [hget]
      refine ⟨hd.1, hd.2.1, ?_, ?_⟩
      · rw [List.getElem_append_left (by rw [P.vertices_length]; omega)]
        simpa only [hieq, P.end_vertex] using hd.2.2.1.symm
      · rw [List.getElem_append_right (by rw [P.vertices_length]; omega)]
        simpa only [P.vertices_length, hieq, Nat.sub_self, List.getElem_cons_zero]
          using hd.2.2.2.symm

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private theorem stageDartPath_to_code {w : ℕ → Fin 3} {n k : ℕ}
    {u v : MapVertex (kmswStageDirectedMap w n)}
    (P : SimpleDirectedDartPath (kmswStageDirectedMap w n) u v k) :
    ∃ p : Path (stageMapVertex w n u) (stageMapVertex w n v), p.length = k := by
  let V (i : Fin (k + 1)) : StagePresentVertex w n :=
    stageMapVertex w n (P.vertices[i.val]'(by rw [P.vertices_length]; exact i.isLt))
  have hedge (i : Fin k) : V ⟨i.val, by omega⟩ ⟶ V ⟨i.val + 1, by omega⟩ := by
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
    obtain ⟨hm, ht, hu, hv⟩ := P.edge_step j
    let d := P.darts.get j
    have hh := (stageMap_dart_arrow_iff w n d
      (P.vertices[i.val]'(by rw [P.vertices_length]; omega))
      (P.vertices[i.val + 1]'(by rw [P.vertices_length]; omega))).1
        ⟨hm, ht, hu.symm, hv.symm⟩
    exact ⟨d.1.val, d.1.isLt, hh.2⟩
  have hbuild : ∀ j (hj : j ≤ k),
      ∃ p : Path (V ⟨0, by omega⟩) (V ⟨j, by omega⟩), p.length = j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨Path.nil, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨p, hp⟩ := ih (by omega)
      exact ⟨p.cons (hedge ⟨j, by omega⟩), congrArg (· + 1) hp⟩
  have hstart : V ⟨0, by omega⟩ = stageMapVertex w n u :=
    congrArg (stageMapVertex w n) P.start_vertex
  have hend : V ⟨k, by omega⟩ = stageMapVertex w n v :=
    congrArg (stageMapVertex w n) P.end_vertex
  have hh := hbuild k (Nat.le_refl k)
  dsimp only [V] at hh hstart hend
  rw [hstart, hend] at hh
  exact hh

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private theorem stageCodePath_lifts (w : ℕ → Fin 3) (n : ℕ)
    {a b : StagePresentVertex w n} (p : Path a b) :
    ∀ (u : MapVertex (kmswStageDirectedMap w n)), stageMapVertex w n u = a →
      ∃ v, stageMapVertex w n v = b ∧
        Nonempty (DartWalk (kmswStageDirectedMap w n) u v p.length) := by
  induction p with
  | nil => intro u hu; exact ⟨u, hu, ⟨DartWalk.nil _ u⟩⟩
  | @cons b c p e ih =>
    intro u hu
    obtain ⟨v, hv, ⟨P⟩⟩ := ih u hu
    let d : StageDart (kmswStage w n).nextEdge := (⟨e.val, e.property.1⟩, false)
    let z := dartHeadVertex (kmswStageDirectedMap w n) d
    have htail : dartTailVertex (kmswStageDirectedMap w n) d = v := by
      apply stageMapVertex_injective w n
      apply congrArg (StagePresentVertex.mk (w := w) (n := n))
      change (kmswStage w n).west e.val = (stageMapVertex w n v).id
      rw [hv]
      exact e.property.2.2.1
    have hz : stageMapVertex w n z = c := by
      apply congrArg (StagePresentVertex.mk (w := w) (n := n))
      exact e.property.2.2.2
    refine ⟨z, hz, ⟨P.cons d ?_⟩⟩
    refine ⟨?_, ⟨e.property.2.1, rfl⟩, htail, rfl⟩
    change ¬ (kmswStage w n).present e.val = false
    rw [e.property.2.1]
    decide

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMap_path_iff (w : ℕ → Fin 3) (n k : ℕ)
    (u v : MapVertex (kmswStageDirectedMap w n)) :
    Nonempty (SimpleDirectedDartPath (kmswStageDirectedMap w n) u v k) ↔
      ∃ p : Path (stageMapVertex w n u) (stageMapVertex w n v), p.length = k := by
  constructor
  · rintro ⟨P⟩
    exact stageDartPath_to_code P
  · rintro ⟨p, rfl⟩
    obtain ⟨v', hv', ⟨P⟩⟩ := stageCodePath_lifts w n p u rfl
    have heq : v' = v := stageMapVertex_injective w n hv'
    subst v'
    exact ⟨P.toSimple (kmswStageDirectedMap_isAcyclic w n)⟩

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem stageMap_pathLengths_eq (w : ℕ → Fin 3) (n : ℕ)
    (u v : MapVertex (kmswStageDirectedMap w n)) :
    {k | Nonempty (SimpleDirectedDartPath (kmswStageDirectedMap w n) u v k)} =
      pathLengths (stageMapVertex w n u) (stageMapVertex w n v) := by
  ext k
  exact stageMap_path_iff w n k u v

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private theorem stageLR_head_zero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private theorem walkClassBase_labels {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).source = ⟨0⟩ ∧
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).sink =
      ⟨(kmswStage (codeExtend c) (n - 1)).east
        (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  have hf := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hf
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL,
    _, _, _, _, _⟩
  constructor
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    change s.west (s.UL.head _) = 0
    have hs := (kmswStage_boundary_chain_invariant w m).2.2.1
    have hUL := (kmswStage_UL_nonempty_active_last w m).1
    have h0 := (initial_edge_endpoints w m).1
    change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at hs
    have hURs : s.UR = [] := hUR
    have hLLs : s.LL = [] := hLL
    rw [hURs, hLLs, List.append_nil, List.nil_append] at hs
    have huhead : s.UL.head? = some (s.UL.head hUL) := List.head?_eq_some_head hUL
    have hrhead : s.LR.head? = some 0 := stageLR_head_zero w m
    change s.UL.head?.map s.west = s.LR.head?.map s.west at hs
    rw [huhead, hrhead] at hs
    exact (Option.some.inj hs).trans h0
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    have hLR := kmswStage_LR_nonempty w m
    have ha := (kmswStage_boundary_chain_invariant w m).2.2.2.2.2.2 hLR hUR
    rw [ha]
    change stageEndpoint s ((kmswStageLRDartRun w m).head _) = _
    simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, List.head_reverse, ↓reduceIte]
    rfl

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
private noncomputable def repBaseIso {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    BipolarBoundaryBaseIso (kmswWalkClassRep hn c).B (kmswWalkClassBase hn c) :=
  ((kmswWalkClassBase hn c).transportIso (Fintype.equivFin _)).symm

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem kmswWalkClassRep_stage_endpoints {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) (d : Fin (kmswWalkClassRep hn c).dartCount) :
    (dartTailVertex (kmswWalkClassRep hn c).B.map d =
        (kmswWalkClassRep hn c).B.source ↔
      stageEndpoint (kmswStage (codeExtend c) (n - 1))
        ((kmswWalkClassRep_mapIso hn c).toEquiv d) = 0) ∧
    (dartTailVertex (kmswWalkClassRep hn c).B.map d =
        (kmswWalkClassRep hn c).B.sink ↔
      stageEndpoint (kmswStage (codeExtend c) (n - 1))
        ((kmswWalkClassRep_mapIso hn c).toEquiv d) =
          (kmswStage (codeExtend c) (n - 1)).east
            (kmswStage (codeExtend c) (n - 1)).active) := by
  let I := repBaseIso hn c
  let F := stageMapVertex (codeExtend c) (n - 1)
  have hinj : Function.Injective (F ∘ I.vertexEquiv) :=
    (stageMapVertex_injective _ _).comp I.vertexEquiv.injective
  have hlabel : (F (I.vertexEquiv
      (dartTailVertex (kmswWalkClassRep hn c).B.map d))).id =
      stageEndpoint (kmswStage (codeExtend c) (n - 1))
        ((kmswWalkClassRep_mapIso hn c).toEquiv d) := by
    rw [I.vertexEquiv_dartTailVertex]
    rfl
  have hsource : F (I.vertexEquiv (kmswWalkClassRep hn c).B.source) = ⟨0⟩ := by
    rw [I.vertexEquiv_source]
    exact (walkClassBase_labels hn c).1
  have hsink : F (I.vertexEquiv (kmswWalkClassRep hn c).B.sink) =
      ⟨(kmswStage (codeExtend c) (n - 1)).east
        (kmswStage (codeExtend c) (n - 1)).active⟩ := by
    rw [I.vertexEquiv_sink]
    exact (walkClassBase_labels hn c).2
  constructor
  · constructor
    · intro h
      rw [← hlabel, h, hsource]
    · intro h
      apply hinj
      change F (I.vertexEquiv _) = F (I.vertexEquiv _)
      rw [hsource]
      have he := hlabel.trans h
      exact congrArg (StagePresentVertex.mk (w := codeExtend c) (n := n - 1)) he
  · constructor
    · intro h
      rw [← hlabel, h, hsink]
    · intro h
      apply hinj
      change F (I.vertexEquiv _) = F (I.vertexEquiv _)
      rw [hsink]
      have he := hlabel.trans h
      exact congrArg (StagePresentVertex.mk (w := codeExtend c) (n := n - 1)) he

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem kmswWalkClassRep_pathLengths_eq_stage {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (sourceSinkPathLengthsBase (kmswWalkClassRep hn c).B : Set ℕ) =
      pathLengths (⟨0⟩ : StagePresentVertex (codeExtend c) (n - 1))
        ⟨(kmswStage (codeExtend c) (n - 1)).east
          (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let B := kmswWalkClassBase hn c
  let I := repBaseIso hn c
  have hiso : (sourceSinkPathLengthsBase (kmswWalkClassRep hn c).B : Set ℕ) =
      (sourceSinkPathLengthsBase B : Set ℕ) := by
    ext k
    simp only [Finset.mem_coe, mem_sourceSinkPathLengthsBase]
    constructor
    · rintro ⟨P, _⟩
      exact ⟨I.mapPath P, trivial⟩
    · rintro ⟨P, _⟩
      exact ⟨I.symm.mapPath P, trivial⟩
  rw [hiso]
  have hbase : (sourceSinkPathLengthsBase B : Set ℕ) =
      pathLengths (stageMapVertex (codeExtend c) (n - 1) B.source)
        (stageMapVertex (codeExtend c) (n - 1) B.sink) := by
    ext k
    rw [Finset.mem_coe, mem_sourceSinkPathLengthsBase]
    exact (show (∃ _P : SimpleDirectedDartPath B.map B.source B.sink k, True) ↔
      Nonempty (SimpleDirectedDartPath B.map B.source B.sink k) from
        ⟨fun ⟨P, _⟩ => ⟨P⟩, fun ⟨P⟩ => ⟨P, trivial⟩⟩).trans
          (stageMap_path_iff (codeExtend c) (n - 1) k B.source B.sink)
  rw [hbase, (walkClassBase_labels hn c).1, (walkClassBase_labels hn c).2]

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem kmswWalkClassRep_ldpLength_eq_stage {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (ldpLengthBase (kmswWalkClassRep hn c).B : WithBot ℕ) =
      ldpSup (⟨0⟩ : StagePresentVertex (codeExtend c) (n - 1))
        ⟨(kmswStage (codeExtend c) (n - 1)).east
          (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let B := (kmswWalkClassRep hn c).B
  let a : StagePresentVertex (codeExtend c) (n - 1) := ⟨0⟩
  let b : StagePresentVertex (codeExtend c) (n - 1) :=
    ⟨(kmswStage (codeExtend c) (n - 1)).east
      (kmswStage (codeExtend c) (n - 1)).active⟩
  have hset : (sourceSinkPathLengthsBase B : Set ℕ) = pathLengths a b :=
    kmswWalkClassRep_pathLengths_eq_stage hn c
  have hbound : ∀ k ∈ pathLengths a b, k ≤ ldpLengthBase B := by
    intro k hk
    have hk' : k ∈ sourceSinkPathLengthsBase B := by
      change k ∈ (sourceSinkPathLengthsBase B : Set ℕ)
      rw [hset]
      exact hk
    exact (sourceSinkPathLengthsBase B).le_max' k hk'
  have hmem : (ldpLengthBase B : WithBot ℕ) ∈
      (fun k : ℕ => (k : WithBot ℕ)) '' pathLengths a b := by
    refine ⟨ldpLengthBase B, ?_, rfl⟩
    rw [← hset]
    exact ldpLengthBase_mem B
  have hupper : ∀ z ∈ (fun k : ℕ => (k : WithBot ℕ)) '' pathLengths a b,
      z ≤ (ldpLengthBase B : WithBot ℕ) := by
    rintro _ ⟨k, hk, rfl⟩
    exact WithBot.coe_le_coe.mpr (hbound k hk)
  exact le_antisymm (le_csSup ⟨_, hupper⟩ hmem) (csSup_le ⟨_, hmem⟩ hupper)

/-- stage map directed paths versus stage code-graph paths; the renewal-time selection
T_{m_k} and the infinite source-map (F4c) identification are not treated;
not the paper result. -/
theorem kmswWalkClassRep_sdpLength_eq_stage {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (sdpLengthBase (kmswWalkClassRep hn c).B : ℕ∞) =
      sdp (⟨0⟩ : StagePresentVertex (codeExtend c) (n - 1))
        ⟨(kmswStage (codeExtend c) (n - 1)).east
          (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let B := (kmswWalkClassRep hn c).B
  let a : StagePresentVertex (codeExtend c) (n - 1) := ⟨0⟩
  let b : StagePresentVertex (codeExtend c) (n - 1) :=
    ⟨(kmswStage (codeExtend c) (n - 1)).east
      (kmswStage (codeExtend c) (n - 1)).active⟩
  have hset : (sourceSinkPathLengthsBase B : Set ℕ) = pathLengths a b :=
    kmswWalkClassRep_pathLengths_eq_stage hn c
  apply le_antisymm
  · apply le_iInf
    intro p
    apply ENat.natCast_le_natCast.mpr
    apply (sourceSinkPathLengthsBase B).min'_le
    change p.length ∈ (sourceSinkPathLengthsBase B : Set ℕ)
    rw [hset]
    exact ⟨p, rfl⟩
  · have hmem : sdpLengthBase B ∈ pathLengths a b := by
      rw [← hset]
      exact sdpLengthBase_mem B
    obtain ⟨p, hp⟩ := hmem
    calc sdp a b ≤ (p.length : ℕ∞) := sdp_le_length p
      _ = (sdpLengthBase B : ℕ∞) := congrArg (fun j : ℕ => (j : ℕ∞)) hp

end DirectedDistances.KMSW
