module

public import DirectedDistances.KMSW.PrimedSimAll
public import DirectedDistances.KMSW.HatLimitIncidenceIso
import DirectedDistances.KMSW.CoherentLimitMaps

/-! # Primed image at the graph level

not counted. -/

public section
namespace DirectedDistances.KMSW

private theorem primedLocal_nextEdge_mono (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m n : ℕ} (hmn : m ≤ n) :
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ≤
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n).nextEdge := by
  let u := primedCode (primedSimInput w) h
  have hm := kmswMissingRootStage_agree u m
  have hn := kmswMissingRootStage_agree u n
  calc
    _ = (kmswStage u m).nextEdge := hm.2.1
    _ ≤ (kmswStage u n).nextEdge := kmswStage_nextEdge_mono u hmn
    _ = _ := hn.2.1.symm

private theorem primedLocal_nextVertex_mono (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m n : ℕ} (hmn : m ≤ n) :
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex ≤
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n).nextVertex := by
  let u := primedCode (primedSimInput w) h
  have hm := kmswMissingRootStage_agree u m
  have hn := kmswMissingRootStage_agree u n
  calc
    _ = (kmswStage u m).nextVertex := hm.1
    _ ≤ (kmswStage u n).nextVertex := CutConverse.nextVertex_mono u hmn
    _ = _ := hn.1.symm

private theorem primedLocal_nextVertex_base_ge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    k + 2 ≤ (kmswMissingRootStage (primedCode (primedSimInput w) h)
      (primedIntervalBase (primedSimInput w) h k)).nextVertex := by
  let u := primedCode (primedSimInput w) h
  induction k with
  | zero =>
      rw [primedIntervalBase_zero]
      simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit]
  | succ k ih =>
      have hc : u (primedIntervalBase (primedSimInput w) h k) = 1 := by
        cases k with
        | zero => simpa [primedIntervalBase_zero, u] using primedCode_zero (primedSimInput w) h
        | succ j =>
            simpa [u] using (primedCrossing_codes w h j).1
      have hup : (kmswMissingRootStage u
          (primedIntervalBase (primedSimInput w) h k + 1)).nextVertex =
          (kmswMissingRootStage u
            (primedIntervalBase (primedSimInput w) h k)).nextVertex + 1 := by
        simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
          State.addEdge]
      have hwidth := primedIntervalWidth_pos (primedSimInput w) h k
      have htime : primedIntervalBase (primedSimInput w) h k + 1 ≤
          primedIntervalBase (primedSimInput w) h (k + 1) := by
        rw [primedIntervalBase_succ]
        omega
      have hmono : (kmswMissingRootStage u
          (primedIntervalBase (primedSimInput w) h k + 1)).nextVertex ≤
          (kmswMissingRootStage u
            (primedIntervalBase (primedSimInput w) h k +
              primedIntervalWidth (primedSimInput w) h k)).nextVertex := by
        simpa only [primedIntervalBase_succ] using
          (primedLocal_nextVertex_mono w h htime)
      have ih' : k + 2 ≤ (kmswMissingRootStage u
          (primedIntervalBase (primedSimInput w) h k)).nextVertex := by
        simpa only [u] using ih
      rw [primedIntervalBase_succ]
      calc
        k + 1 + 2 ≤
            (kmswMissingRootStage u (primedIntervalBase (primedSimInput w) h k)).nextVertex + 1 := by
          omega
        _ = (kmswMissingRootStage u
            (primedIntervalBase (primedSimInput w) h k + 1)).nextVertex := hup.symm
        _ ≤ (kmswMissingRootStage u
            (primedIntervalBase (primedSimInput w) h k +
              primedIntervalWidth (primedSimInput w) h k)).nextVertex := hmono

/-- not counted. Every primed edge ID and vertex ID is allocated at some finite
local stage. -/
theorem primedLocalIds_eventually_allocated (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    (∀ e, ∃ m, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) ∧
    (∀ v, ∃ m, v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex) := by
  constructor
  · intro e
    refine ⟨e, ?_⟩
    have hc := CutConverse.allocation_count (primedCode (primedSimInput w) h) e
    rw [(kmswMissingRootStage_agree (primedCode (primedSimInput w) h) e).2.1]
    omega
  · intro v
    refine ⟨primedIntervalBase (primedSimInput w) h v, ?_⟩
    have hv := primedLocal_nextVertex_base_ge w h v
    omega

/-- not counted. First-allocation limit edge map for the coherent primed maps. -/
@[expose] noncomputable def primedLimitEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  leastAllocatedStageMap
    (fun m => (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (primedAllEdgeMap w h)

/-- not counted. First-allocation limit vertex map for the coherent primed maps. -/
@[expose] noncomputable def primedLimitVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  leastAllocatedStageMap
    (fun m => (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex)
    (primedAllVertexMap w h)

/-- not counted. At every stage where an edge or vertex ID is allocated, its limit
map equals the canonical coherent stage map. -/
theorem primedLimit_maps_eq_of_allocated (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    (∀ e, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge →
      primedLimitEdgeMap w h e = primedAllEdgeMap w h m e) ∧
    (∀ v, v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex →
      primedLimitVertexMap w h v = primedAllVertexMap w h m v) := by
  constructor
  · intro e he
    change leastAllocatedStageMap
        (fun j => (kmswMissingRootStage (primedCode (primedSimInput w) h) j).nextEdge)
        (primedAllEdgeMap w h) e = primedAllEdgeMap w h m e
    exact leastAllocatedStageMap_eq_of_allocated
      (fun j => (kmswMissingRootStage (primedCode (primedSimInput w) h) j).nextEdge)
      (primedAllEdgeMap w h)
      (fun a b hab => primedLocal_nextEdge_mono w h hab)
      (fun j e hj => (primedAll_maps_extend w h j).1 e hj)
      m e he
  · intro v hv
    change leastAllocatedStageMap
        (fun j => (kmswMissingRootStage (primedCode (primedSimInput w) h) j).nextVertex)
        (primedAllVertexMap w h) v = primedAllVertexMap w h m v
    exact leastAllocatedStageMap_eq_of_allocated
      (fun j => (kmswMissingRootStage (primedCode (primedSimInput w) h) j).nextVertex)
      (primedAllVertexMap w h)
      (fun a b hab => primedLocal_nextVertex_mono w h hab)
      (fun j v hj => (primedAll_maps_extend w h j).2 v hj)
      m v hv

private theorem primedStage_edge_injective (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m e f : ℕ)
    (he : e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hf : f < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hEq : primedAllEdgeMap w h m e = primedAllEdgeMap w h m f) : e = f := by
  cases m with
  | zero => exact (primedAll_sim_zero w h).1.edge_injective e f he hf hEq
  | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.edge_injective e f he hf hEq

private theorem primedStage_vertex_injective (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m v z : ℕ)
    (hv : v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex)
    (hz : z < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex)
    (hEq : primedAllVertexMap w h m v = primedAllVertexMap w h m z) : v = z := by
  cases m with
  | zero => exact (primedAll_sim_zero w h).1.vertex_injective v z hv hz hEq
  | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.vertex_injective v z hv hz hEq

/-- not counted. The limit edge and vertex maps are injective on all allocated
primed IDs. -/
theorem primedLimit_maps_injective_on_allocated (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    Set.InjOn (primedLimitEdgeMap w h)
      {e | ∃ m, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge} ∧
    Set.InjOn (primedLimitVertexMap w h)
      {v | ∃ m, v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex} := by
  constructor
  · intro e he f hf hEq
    obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ := hf
    let q := max m n
    have hqe : e < (kmswMissingRootStage (primedCode (primedSimInput w) h) q).nextEdge :=
      hm.trans_le (primedLocal_nextEdge_mono w h (Nat.le_max_left m n))
    have hqf : f < (kmswMissingRootStage (primedCode (primedSimInput w) h) q).nextEdge :=
      hn.trans_le (primedLocal_nextEdge_mono w h (Nat.le_max_right m n))
    have hEq' : primedAllEdgeMap w h q e = primedAllEdgeMap w h q f := by
      rw [← (primedLimit_maps_eq_of_allocated w h q).1 e hqe,
        ← (primedLimit_maps_eq_of_allocated w h q).1 f hqf]
      exact hEq
    exact primedStage_edge_injective w h q e f hqe hqf hEq'
  · intro v hv z hz hEq
    obtain ⟨m, hm⟩ := hv
    obtain ⟨n, hn⟩ := hz
    let q := max m n
    have hqv : v < (kmswMissingRootStage (primedCode (primedSimInput w) h) q).nextVertex :=
      hm.trans_le (primedLocal_nextVertex_mono w h (Nat.le_max_left m n))
    have hqz : z < (kmswMissingRootStage (primedCode (primedSimInput w) h) q).nextVertex :=
      hn.trans_le (primedLocal_nextVertex_mono w h (Nat.le_max_right m n))
    have hEq' : primedAllVertexMap w h q v = primedAllVertexMap w h q z := by
      rw [← (primedLimit_maps_eq_of_allocated w h q).2 v hqv,
        ← (primedLimit_maps_eq_of_allocated w h q).2 z hqz]
      exact hEq
    exact primedStage_vertex_injective w h q v z hqv hqz hEq'

/-- not counted. A primed edge is present if it is directed at some missing-root
local stage. -/
@[expose] def PrimedEdgePresent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) : Prop :=
  ∃ m, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ∧
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e = true

/-- not counted. Once a primed edge is present, it stays present and allocated at
every later local stage. -/
theorem PrimedEdgePresent.eventually_present (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {e : ℕ} (he : PrimedEdgePresent w h e) :
    ∃ M, ∀ m, M ≤ m →
      e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ∧
      (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e = true := by
  obtain ⟨n, hbound, hp⟩ := he
  let u := primedCode (primedSimInput w) h
  have hne : e ≠ 0 := by
    intro he0
    subst e
    rw [kmswMissingRootStage_present_zero u n] at hp
    cases hp
  have hAgree := kmswMissingRootStage_agree u n
  have hboundOrd : e < (kmswStage u n).nextEdge := by
    rw [← hAgree.2.1]
    exact hbound
  have hpOrd : (kmswStage u n).present e = true := by
    rw [← hAgree.2.2.2.2.1 e hne]
    exact hp
  obtain ⟨M, hM⟩ := (EdgePresent.of_stage_present hboundOrd hpOrd).eventually_present
  refine ⟨M, fun m hm => ?_⟩
  have hlocal := hM m hm
  have hAgree' := kmswMissingRootStage_agree u m
  constructor
  · rw [hAgree'.2.1]
    exact hlocal.1
  · rw [hAgree'.2.2.2.2.1 e hne]
    exact hlocal.2

/-- not counted. Root-reachable present edges form an increasing family of sets
as the global KMSW stage increases. -/
theorem stageReachablePresentEdges_mono (w : ℕ → Fin 3) {m n : ℕ}
    (hmn : m ≤ n) :
    stageReachablePresentEdges w m ⊆ stageReachablePresentEdges w n := by
  induction hmn with
  | refl => exact Set.Subset.rfl
  | @step n hmn ih =>
      rw [stageReachablePresentEdges_succ]
      exact ih.trans Set.subset_union_left

private theorem primedAll_stage_cut (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    ∃ k, PrimedComplementSimCut (primedCode (primedSimInput w) h) w h k m
      (primedStageTime w h m) (primedAllEdgeMap w h m) (primedAllVertexMap w h m) := by
  cases m with
  | zero => exact ⟨0, (primedAll_sim_zero w h).1.toCut h 0⟩
  | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact ⟨k, hs.forget.toCut⟩

private theorem walkNR_ge_index (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : k ≤ walkNR w h k := by
  induction k with
  | zero => simp [walkNR_zero]
  | succ k ih =>
      have hL := (walkNL_spec w h k).1
      have hR := (walkNR_succ_spec w h k).1
      omega

private theorem primedStageTime_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (N : ℕ) :
    ∃ m, N ≤ primedStageTime w h m := by
  refine ⟨primedIntervalBase (primedSimInput w) h (N + 1), ?_⟩
  rw [primedStageTime_at_crossing]
  have hNR := walkNR_ge_index w h (N + 1)
  omega

private theorem primedLimitEdge_not_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {e : ℕ} (he : PrimedEdgePresent w h e)
    (n : ℕ) :
    primedLimitEdgeMap w h e ∉ stageReachablePresentEdges w n := by
  obtain ⟨M, hM⟩ := he.eventually_present w h
  let k := max M n
  let m := primedIntervalBase (primedSimInput w) h (k + 1)
  have hmge : M ≤ m := by
    have hb := primedIntervalBase_ge (primedSimInput w) h (k + 1)
    dsimp [m]
    omega
  have hpres := hM m hmge
  have htime : n ≤ primedStageTime w h m := by
    dsimp [m]
    rw [primedStageTime_at_crossing]
    have hNR := walkNR_ge_index w h (k + 1)
    omega
  obtain ⟨j, sim⟩ := primedAll_stage_cut w h m
  have hnot := sim.present_complement e hpres.1 hpres.2
  have hEq := (primedLimit_maps_eq_of_allocated w h m).1 e hpres.1
  intro hreach
  have hreach' : primedAllEdgeMap w h m e ∈ stageReachablePresentEdges w n := by
    rw [← hEq]
    exact hreach
  exact hnot.2 (stageReachablePresentEdges_mono w htime hreach')

/-- not counted. Every eventually present primed edge maps to a globally present
edge that is outside the root-reachable present-edge set at every global
stage, and its ordered endpoints are the limit vertex images. -/
theorem primedLimitEdge_data (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {e : ℕ} (he : PrimedEdgePresent w h e) :
    EdgePresent w (primedLimitEdgeMap w h e) ∧
      (∀ n, primedLimitEdgeMap w h e ∉ stageReachablePresentEdges w n) ∧
      edgeWest w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeWest (primedCode (primedSimInput w) h) e) ∧
      edgeEast w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeEast (primedCode (primedSimInput w) h) e) := by
  obtain ⟨m, hbound, hp⟩ := he
  obtain ⟨k, sim⟩ := primedAll_stage_cut w h m
  let u := primedCode (primedSimInput w) h
  let T := primedStageTime w h m
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w T
  have hEqE := (primedLimit_maps_eq_of_allocated w h m).1 e hbound
  have hGlobalBound := sim.edge_bound e hbound
  have hGlobalPresent := (sim.present_complement e hbound hp).1
  have hInc := sim.present_incidence e hbound hp
  have hGlobalEdgePresent : EdgePresent w (primedLimitEdgeMap w h e) := by
    rw [hEqE]
    exact ⟨T, hGlobalBound, hGlobalPresent⟩
  have hAgree := kmswMissingRootStage_agree u m
  have hOrdBound : e < (kmswStage u m).nextEdge := by
    rw [← hAgree.2.1]
    exact hbound
  have hOrdEnds := kmswStage_endpoints_lt_nextVertex u m e hOrdBound
  have hLocalWestBound : sh.west e < sh.nextVertex := by
    rw [hAgree.2.2.1 e, hAgree.1]
    exact hOrdEnds.1
  have hLocalEastBound : sh.east e < sh.nextVertex := by
    rw [hAgree.2.2.2.1 e, hAgree.1]
    exact hOrdEnds.2
  have hEqVW := (primedLimit_maps_eq_of_allocated w h m).2 (sh.west e) hLocalWestBound
  have hEqVE := (primedLimit_maps_eq_of_allocated w h m).2 (sh.east e) hLocalEastBound
  have hLocalWestStable : sh.west e = edgeWest u e := by
    calc
      sh.west e = (kmswStage u m).west e := hAgree.2.2.1 e
      _ = edgeWest u e := (edge_endpoints_eq u hOrdBound).1
  have hLocalEastStable : sh.east e = edgeEast u e := by
    calc
      sh.east e = (kmswStage u m).east e := hAgree.2.2.2.1 e
      _ = edgeEast u e := (edge_endpoints_eq u hOrdBound).2
  have hGlobalEnds := edge_endpoints_eq w hGlobalBound
  have hWest : edgeWest w (primedLimitEdgeMap w h e) =
      primedLimitVertexMap w h (edgeWest u e) := by
    rw [hEqE]
    calc
      edgeWest w (primedAllEdgeMap w h m e) = gl.west (primedAllEdgeMap w h m e) :=
        (edge_endpoints_eq w hGlobalBound).1.symm
      _ = primedAllVertexMap w h m (sh.west e) := hInc.1
      _ = primedLimitVertexMap w h (sh.west e) := hEqVW.symm
      _ = primedLimitVertexMap w h (edgeWest u e) :=
        congrArg (primedLimitVertexMap w h) hLocalWestStable
  have hEast : edgeEast w (primedLimitEdgeMap w h e) =
      primedLimitVertexMap w h (edgeEast u e) := by
    rw [hEqE]
    calc
      edgeEast w (primedAllEdgeMap w h m e) = gl.east (primedAllEdgeMap w h m e) :=
        (edge_endpoints_eq w hGlobalBound).2.symm
      _ = primedAllVertexMap w h m (sh.east e) := hInc.2
      _ = primedLimitVertexMap w h (sh.east e) := hEqVE.symm
      _ = primedLimitVertexMap w h (edgeEast u e) :=
        congrArg (primedLimitVertexMap w h) hLocalEastStable
  exact ⟨hGlobalEdgePresent, primedLimitEdge_not_reachable w h ⟨m, hbound, hp⟩,
    hWest, hEast⟩

/-- not counted. The subtype of all vertex IDs allocated by a primed local stage. -/
@[expose] def PrimedAllocatedVertex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Type :=
  {v : ℕ // ∃ m,
    v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex}

/-- not counted. The image subtype of the primed limit vertex map on allocated IDs. -/
@[expose] def PrimedLimitVertexImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Type :=
  {v : ℕ // ∃ a : PrimedAllocatedVertex w h,
    primedLimitVertexMap w h a.1 = v}

/-- not counted. The image subtype of primed eventually present edges, carrying
global presence, absence from every root-reachable present-edge set, and an
explicit primed preimage. -/
@[expose] def PrimedLimitEdgeImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Type :=
  {e' : ℕ // EdgePresent w e' ∧
    (∀ n, e' ∉ stageReachablePresentEdges w n) ∧
    ∃ e, PrimedEdgePresent w h e ∧ primedLimitEdgeMap w h e = e'}

/-- not counted. The primed limit vertex and present-edge maps give Equivalences
to their image subtypes, and the edge Equivalence preserves ordered west/east
endpoints through the vertex limit map. This graph-layer helper does not
assert coverage of the global present-edge complement. -/
theorem primedLimitIncidence (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    ∃ (V : PrimedAllocatedVertex w h ≃ PrimedLimitVertexImage w h)
      (E : {e : ℕ // PrimedEdgePresent w h e} ≃ PrimedLimitEdgeImage w h),
      (∀ a, (V a).1 = primedLimitVertexMap w h a.1) ∧
      (∀ e, (E e).1 = primedLimitEdgeMap w h e.1) ∧
      (∀ e : {e : ℕ // PrimedEdgePresent w h e},
        edgeWest w (E e).1 =
          primedLimitVertexMap w h (edgeWest (primedCode (primedSimInput w) h) e.1) ∧
        edgeEast w (E e).1 =
          primedLimitVertexMap w h (edgeEast (primedCode (primedSimInput w) h) e.1)) := by
  let V : PrimedAllocatedVertex w h ≃ PrimedLimitVertexImage w h :=
    Equiv.ofBijective
      (fun a => ⟨primedLimitVertexMap w h a.1, ⟨a, rfl⟩⟩)
      (by
        constructor
        · intro a b hab
          have hval : primedLimitVertexMap w h a.1 = primedLimitVertexMap w h b.1 :=
            congrArg Subtype.val hab
          have hinj := (primedLimit_maps_injective_on_allocated w h).2
          exact Subtype.ext (hinj a.2 b.2 hval)
        · rintro ⟨v, a, hav⟩
          exact ⟨a, Subtype.ext hav⟩)
  let E : {e : ℕ // PrimedEdgePresent w h e} ≃ PrimedLimitEdgeImage w h :=
    Equiv.ofBijective
      (fun e =>
        let hd := primedLimitEdge_data w h e.2
        ⟨primedLimitEdgeMap w h e.1, hd.1, hd.2.1, ⟨e.1, e.2, rfl⟩⟩)
      (by
        constructor
        · intro e f hef
          have hval : primedLimitEdgeMap w h e.1 = primedLimitEdgeMap w h f.1 :=
            congrArg Subtype.val hef
          obtain ⟨me, hme, _⟩ := e.2
          obtain ⟨mf, hmf, _⟩ := f.2
          have hinj := (primedLimit_maps_injective_on_allocated w h).1
          exact Subtype.ext (hinj ⟨me, hme⟩ ⟨mf, hmf⟩ hval)
        · rintro ⟨e', _, _, e, he, heq⟩
          exact ⟨⟨e, he⟩, Subtype.ext heq⟩)
  refine ⟨V, E, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro e
    rfl
  · intro e
    obtain ⟨_, _, hwest,heast⟩ := primedLimitEdge_data w h e.2
    exact ⟨hwest, heast⟩

end DirectedDistances.KMSW
