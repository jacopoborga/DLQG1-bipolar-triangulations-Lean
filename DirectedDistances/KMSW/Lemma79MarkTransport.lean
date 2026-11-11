module

public import DirectedDistances.KMSW.Lemma79StoppedSubmap
public import DirectedDistances.KMSW.StoppedLeftBoundaryMarkAE
public import DirectedDistances.KMSW.KMSWWalkClassRooting
public import DirectedDistances.KMSW.KMSWForwardClass
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.PlanarMap.DirectedMapIso
public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap









private theorem leftBoundary_getD_map {α β : Type*} (f : α → β)
    (xs : List α) (j : ℕ) (d : α) :
    (xs.map f).getD j (f d) = f (xs.getD j d) := by
  induction xs generalizing j with
  | nil => cases j <;> rfl
  | cons x xs ih => cases j with
    | zero => rfl
    | succ j => exact ih j

private theorem getD_eq_get {α : Type*} (xs : List α)
    (i : Fin xs.length) (d : α) : xs.getD i.val d = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i with
    | mk k hk =>
      cases k with
      | zero => rfl
      | succ k =>
        have hi : k < xs.length := by simpa using hk
        exact ih ⟨k, hi⟩

private theorem getD_append_left_of_lt {α : Type*} (xs ys : List α)
    (j : ℕ) (d : α) (hj : j < xs.length) :
    (xs ++ ys).getD j d = xs.getD j d := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simpa using hj)

private theorem getD_append_singleton_length {α : Type*} (xs : List α)
    (y d : α) : (xs ++ [y]).getD xs.length d = y := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

private theorem walkClassBase_sink_stage_label {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n) :
    (stageMapVertex (codeExtend c) (n - 1)
      (kmswWalkClassBase hn c).sink).id =
        (kmswStage (codeExtend c) (n - 1)).east
          (kmswStage (codeExtend c) (n - 1)).active := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  have hsourceClass := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hsourceClass
  rcases hsourceClass with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, _,
    _, _, _, _, _⟩
  have hLR := kmswStage_LR_nonempty w m
  have htip := CutConverse.east_active_eq_LR_terminal_of_UR_nil w m hUR
  rw [List.getLast?_eq_getLast_of_ne_nil hLR] at htip
  simp only [Option.map_some, Option.some.injEq] at htip
  change (stageMapVertex w m
      (dartTailVertex (kmswStageDirectedMap w m)
        ((kmswStageLRDartRun w m).head _))).id = s.east s.active
  rw [stageMapVertex_tail]
  simp only [kmswStageLRDartRun, stageDarts, List.head_map,
    List.head_attach, stageEndpoint, List.head_reverse, ↓reduceIte]
  exact htip.symm

private theorem walkClassBase_leftBoundaryVertex_getD_stage
    {ℓ r n : ℕ} (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n)
    (j : Fin (ℓ + 1)) :
    (stageMapVertex (codeExtend c) (n - 1)
      ((kmswWalkClassBase hn c).leftPath.vertices.getD j.val
        (kmswWalkClassBase hn c).source)).id =
      (stoppedLeftBoundaryVertices (codeExtend c) n).getD j.val 0 := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  let B := kmswWalkClassBase hn c
  have hlen : s.UL.length = ℓ := by
    simpa [kmswStageULDartRun, stageDarts] using
      (kmswWalkClassBase_leftDartRun_length hn c)
  by_cases hj : j.val < ℓ
  · let i : Fin B.leftPath.darts.length :=
      ⟨j.val, by rw [B.leftPath.darts_length]; exact hj⟩
    let vi : Fin B.leftPath.vertices.length :=
      ⟨j.val, by rw [B.leftPath.vertices_length]; omega⟩
    have hpath : B.leftPath.darts = kmswStageULDartRun w m := by
      change (Classical.choose (kmswWalkClassBase_paths hn c)).darts = _
      exact (Classical.choose_spec (Classical.choose_spec
        (kmswWalkClassBase_paths hn c))).1
    have htail : B.leftPath.vertices.getD j.val B.source =
        dartTailVertex B.map (B.leftPath.darts.get i) := by
      calc
        B.leftPath.vertices.getD j.val B.source =
            B.leftPath.vertices.get vi := getD_eq_get _ vi B.source
        _ = dartTailVertex B.map (B.leftPath.darts.get i) :=
          (B.leftPath.edge_step i).2.2.1
    let k : Fin s.UL.length := ⟨j.val, by omega⟩
    have hrlen : (kmswStageULDartRun w m).length = s.UL.length := by
      simp [kmswStageULDartRun, stageDarts, s]
    have hrbound : j.val < (kmswStageULDartRun w m).length := by
      rw [hrlen, hlen]
      exact hj
    let d0 : StageDart s.nextEdge :=
      (kmswStageULDartRun w m).get ⟨0, by
        have hpos := (kmswStage_UL_nonempty_active_last w m).1
        rw [hrlen]
        exact List.length_pos_iff.mpr hpos⟩
    have hpathD : B.leftPath.darts.getD j.val d0 =
        (kmswStageULDartRun w m).getD j.val d0 :=
      congrArg (fun ds : List (StageDart s.nextEdge) => ds.getD j.val d0) hpath
    have hDartLabel :
        stageEndpoint s (B.leftPath.darts.get i) = s.west (s.UL.get k) := by
      have hleft := getD_eq_get B.leftPath.darts i d0
      have hright := getD_eq_get (kmswStageULDartRun w m)
        ⟨j.val, hrbound⟩ d0
      rw [hleft, hright] at hpathD
      have hrunGet : (kmswStageULDartRun w m).get ⟨j.val, hrbound⟩ =
          ((⟨s.UL.get k,
            stageRun_edge_bound w m (s.UL.get k)
              (Or.inl (Or.inl (Or.inl (List.get_mem s.UL k))))⟩ :
            Fin s.nextEdge), false) := by
        simp [kmswStageULDartRun, stageDarts, k, s]
      rw [hpathD, hrunGet]
      simp [stageEndpoint]
    have hjmap : j.val < (s.UL.map s.west).length := by
      simpa [hlen] using hj
    have htarget :
        (s.UL.map s.west ++ [s.east (act w m)]).getD j.val 0 =
          s.west (s.UL.get k) := by
      rw [getD_append_left_of_lt _ _ _ _ hjmap]
      rw [getD_eq_get _ ⟨j.val, hjmap⟩ 0]
      simp
      congr 2
    have htail' : B.leftPath.vertices.getD j.val B.source =
        dartTailVertex (kmswStageDirectedMap w m)
          (B.leftPath.darts.get i) := by
      simpa [B] using htail
    change (stageMapVertex w m (B.leftPath.vertices.getD j.val B.source)).id = _
    calc
      _ = (stageMapVertex w m
          (dartTailVertex (kmswStageDirectedMap w m)
            (B.leftPath.darts.get i))).id := by
          exact congrArg (fun v => (stageMapVertex w m v).id) htail'
      _ = stageEndpoint s (B.leftPath.darts.get i) := by
          rw [stageMapVertex_tail]
      _ = s.west (s.UL.get k) := hDartLabel
      _ = (stoppedLeftBoundaryVertices w n).getD j.val 0 := by
          simpa [stoppedLeftBoundaryVertices, w, m] using htarget.symm
  · have hjEq : j.val = ℓ := by omega
    have hlast : B.leftPath.vertices.getD ℓ B.source = B.sink := by
      rw [getD_eq_get _ ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩ B.source]
      exact B.leftPath.end_vertex
    change (stageMapVertex w m (B.leftPath.vertices.getD j.val B.source)).id = _
    rw [hjEq, hlast, walkClassBase_sink_stage_label]
    have htarget :
        (stoppedLeftBoundaryVertices w n).getD ℓ 0 = s.east (act w m) := by
      change (s.UL.map s.west ++ [s.east (act w m)]).getD ℓ 0 = _
      rw [← hlen]
      simpa only [List.length_map] using
        getD_append_singleton_length (s.UL.map s.west)
          (s.east (act w m)) 0
    exact htarget.symm

/-- The left boundary order of a map class is invariant under its defining -/
theorem kmswClass_leftBoundaryVertex_getD
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
    {B : DirectedDistances.PlanarMap.BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : DirectedDistances.PlanarMap.BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : DirectedDistances.PlanarMap.BipolarBoundaryBaseIso B B') (j : ℕ) :
    I.vertexEquiv (B.leftPath.vertices.getD j B.source) =
      B'.leftPath.vertices.getD j B'.source := by
  have hpath : I.transportPath B.leftPath = B'.leftPath := by
    apply DirectedDistances.PlanarMap.SimpleDirectedDartPath.eq_of_darts_eq
    rw [DirectedDistances.PlanarMap.BipolarBoundaryBaseIso.transportPath_darts,
      I.leftDarts]
  have hverts := congrArg
    DirectedDistances.PlanarMap.SimpleDirectedDartPath.vertices hpath
  have hverts' : B.leftPath.vertices.map I.vertexEquiv = B'.leftPath.vertices := by
    simpa only [DirectedDistances.PlanarMap.BipolarBoundaryBaseIso.transportPath]
      using hverts
  calc
    I.vertexEquiv (B.leftPath.vertices.getD j B.source) =
        (B.leftPath.vertices.map I.vertexEquiv).getD j
          (I.vertexEquiv B.source) :=
      (leftBoundary_getD_map I.vertexEquiv B.leftPath.vertices j B.source).symm
    _ = B'.leftPath.vertices.getD j (I.vertexEquiv B.source) :=
      congrArg (fun xs => xs.getD j (I.vertexEquiv B.source)) hverts'
    _ = B'.leftPath.vertices.getD j B'.source := by
      rw [I.vertexEquiv_source]

/-- Base isomorphism from the walk-class representative's map to its stage-map
not the paper result. -/
noncomputable def kmswWalkClassRep_baseIso {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n) :
    BipolarBoundaryBaseIso (kmswWalkClassRep hn c).B
      (kmswWalkClassBase hn c) :=
  ((kmswWalkClassBase hn c).transportIso (Fintype.equivFin _)).symm

/-- representative's ordered left-path vertex at any valid index is the same stage
vertex as the corresponding stopped UL-list vertex. The finite-prefix
comparison to a conditioned stream is stated below; not the paper result. -/
theorem kmswWalkClassRep_leftBoundaryVertex_getD_stage
    {ℓ r n : ℕ} (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n)
    (j : Fin (ℓ + 1)) :
    (stageMapVertex (codeExtend c) (n - 1)
      ((kmswWalkClassRep_baseIso hn c).vertexEquiv
        ((kmswWalkClassRep hn c).B.leftPath.vertices.getD j.val
          (kmswWalkClassRep hn c).B.source))).id =
      (stoppedLeftBoundaryVertices (codeExtend c) n).getD j.val 0 := by
  let I := kmswWalkClassRep_baseIso hn c
  have hpath := kmswClass_leftBoundaryVertex_getD I j.val
  rw [hpath]
  exact walkClassBase_leftBoundaryVertex_getD_stage hn c j

/-- the stopped word's finite-prefix equality, the representative's ordered left
vertex agrees with the actual stream stage vertex list. This transports the
concrete UL path through the class and stage construction; not the paper result. -/
theorem kmswWalkClassRep_leftBoundaryVertex_getD_stagePrefix
    {ℓ r n : ℕ} (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n)
    (w : ℕ → Fin 3) (hc : ∀ i : Fin (n - 1), c.val i = w i.val)
    (j : Fin (ℓ + 1)) :
    (stageMapVertex (codeExtend c) (n - 1)
      ((kmswWalkClassRep_baseIso hn c).vertexEquiv
        ((kmswWalkClassRep hn c).B.leftPath.vertices.getD j.val
          (kmswWalkClassRep hn c).B.source))).id =
      (stoppedLeftBoundaryVertices w n).getD j.val 0 := by
  rw [kmswWalkClassRep_leftBoundaryVertex_getD_stage hn c j]
  have hp : ∀ i < n - 1, codeExtend c i = w i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hc ⟨i, hi⟩
  have hs := kmswStage_eq_of_prefix (codeExtend c) w (n - 1) hp
  simp [stoppedLeftBoundaryVertices, act, hs]

private theorem stageMapVertex_head_id (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (stageMapVertex w n
      (dartHeadVertex (kmswStageDirectedMap w n) d)).id =
        stageEndpoint (kmswStage w n) (edgeFlip _ d) := by
  rfl

end DirectedDistances.KMSW
