module

public import DirectedDistances.KMSW.KMSWShiftAllTimes
public import DirectedDistances.KMSW.ActiveTimeMonotone
public import DirectedDistances.KMSW.DirectedContain

/-! Supporting lemmas for paper labels `def-kmsw`, `lem-directed-contain` (see CORRESPONDENCE.md). -/

/-! # Directed containment in the shifted KMSW map

Path lifting from a hit-indexed boundary vertex into the all-times shifted

Here hit-indexed `x_k := boundaryVertex w h k` and `τ_k := boundaryHitTime w h k`;
identifying them with the source's directed-order `x_k` / `τ_k` is a separate
bridge. `M̂_{τ_k,∞}` is modelled by `kmswShiftHatVertices`. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory

/-- The hit-indexed boundary vertex is the west endpoint of the active edge at
its hit time, including the explicit root conventions `x₀ = 0`, `x₁ = 1` -/
theorem boundaryVertex_eq_edgeWest_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryVertex w h k = edgeWest w (act w (boundaryHitTime w h k)) := by
  have hactive : boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
    by_cases hk0 : k = 0
    · subst k
      rw [boundaryVertex_zero, boundaryHitTime_zero]
      rw [CutConverse.activeInitial_eq]
      simp [act, kmswStage, kmswInit]
    · by_cases hk1 : k = 1
      · subst k
        exact boundaryVertex_one_eq_activeInitial_hit w h
      · exact boundaryVertex_eq_activeInitial w h hk0 hk1
  rw [hactive]
  rfl

/-- The all-times simulation sends the shifted active edge at time `m` to the
global active edge at time `t + m` (`def-kmsw`, -/
theorem kmswShift_active_edge_map (w : ℕ → Fin 3) (t m : ℕ) :
    kmswShiftEdgeMapAll w t m (act (fun i => w (t + i)) m) = act w (t + m) := by
  have hs := kmswShift_sim2_all w t m
  have hactive := hs.sim.active
  simpa [act] using hactive

/-- The shifted root vertex maps to the boundary vertex at the chosen hit
time; this includes `k = 0` and `k = 1` (`lem-directed-contain`, -/
theorem kmswShift_root_vertex_map (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    kmswShiftVertexMapAll w (boundaryHitTime w h k) 0 0 = boundaryVertex w h k := by
  let t := boundaryHitTime w h k
  have hs := kmswShift_sim2_all w t 0
  have hinc := hs.sim.incidence 0 (by simp [kmswStage, kmswInit])
  have hactive := hs.sim.active
  have hedge : kmswShiftEdgeMapAll w t 0 0 = act w t := by
    simpa [kmswStage, kmswInit, act] using hactive
  have hroot : kmswShiftVertexMapAll w t 0 0 =
      (kmswStage w t).west (act w t) := by
    have hwest := hinc.1
    simpa [kmswStage, kmswInit, hedge] using hwest.symm
  calc
    kmswShiftVertexMapAll w (boundaryHitTime w h k) 0 0 =
        kmswShiftVertexMapAll w t 0 0 := by rfl
    _ = (kmswStage w t).west (act w t) := hroot
    _ = edgeWest w (act w t) :=
      (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))).1
    _ = boundaryVertex w h k := (boundaryVertex_eq_edgeWest_hit w h k).symm

/-- The shifted active edge at every shifted time is present in its finite -/
theorem kmswShift_active_present (w : ℕ → Fin 3) (t m : ℕ) :
    act (fun i => w (t + i)) m <
        (kmswStage (fun i => w (t + i)) m).nextEdge ∧
      (kmswStage (fun i => w (t + i)) m).present
        (act (fun i => w (t + i)) m) = true := by
  exact ⟨act_lt_nextEdge (fun i => w (t + i)) (Nat.le_refl m),
    (kmswStage_status (fun i => w (t + i)) m).2.1 _ (by
      obtain ⟨xs, hUL⟩ := kmswStage_UL_last (fun i => w (t + i)) m
      have hmem : (kmswStage (fun i => w (t + i)) m).active ∈
          (kmswStage (fun i => w (t + i)) m).UL := by rw [hUL]; simp
      simpa [act] using hmem)⟩

/-- Each shifted active edge is present in the shifted limit quiver -/
theorem kmswShift_active_edge_present_limit (w : ℕ → Fin 3) (t m : ℕ) :
    EdgePresent (fun i => w (t + i)) (act (fun i => w (t + i)) m) := by
  exact EdgePresent.of_stage_present (kmswShift_active_present w t m).1
    (kmswShift_active_present w t m).2

/-- Once the shifted active edge at time `r` has been allocated, its image
under every later all-times map is the global active edge at `t + r` -/
theorem kmswShift_active_edge_map_of_le (w : ℕ → Fin 3) (t r m : ℕ)
    (hrm : r ≤ m) :
    kmswShiftEdgeMapAll w t m (act (fun i => w (t + i)) r) = act w (t + r) := by
  have he := (kmswShift_active_present w t r).1
  calc
    kmswShiftEdgeMapAll w t m (act (fun i => w (t + i)) r) =
        kmswShiftEdgeMapAll w t r (act (fun i => w (t + i)) r) :=
      kmswShiftEdgeMapAll_eq_of_le w t r m _ hrm he
    _ = act w (t + r) := kmswShift_active_edge_map w t r

/-- The shifted root remains mapped to the same global vertex at every later -/
theorem kmswShift_root_vertex_map_at (w : ℕ → Fin 3) (t m : ℕ) :
    kmswShiftVertexMapAll w t m 0 = kmswShiftVertexMapAll w t 0 0 := by
  exact kmswShiftVertexMapAll_eq_of_le w t 0 m 0 (Nat.zero_le m)
    (by simp [kmswStage, kmswInit])

private theorem list_witnesses_bounded {l : List ℕ} (P : ℕ → ℕ → Prop)
    (h : ∀ e ∈ l, ∃ r, P e r) :
    ∃ M, ∀ e ∈ l, ∃ r ≤ M, P e r := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons e es ih =>
      obtain ⟨N, hN⟩ := ih (by
        intro f hf
        exact h f (List.mem_cons_of_mem e hf))
      obtain ⟨r, hr⟩ := h e (by simp)
      refine ⟨max r N, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with hfe | hfe
      · subst f
        exact ⟨r, le_max_left _ _, hr⟩
      · obtain ⟨s, hsM, hs⟩ := hN f hfe
        exact ⟨s, hsM.trans (Nat.le_max_right _ _), hs⟩

/-- The active times of all edges in a path from a hit vertex have a common
finite shifted-stage bound (`lem-directed-contain`, -/
theorem boundaryPath_shiftOffsets_bounded (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b) :
    ∃ M, ∀ e ∈ pathEdgeList p,
      ∃ r ≤ M, e = act w (boundaryHitTime w h k + r) := by
  apply list_witnesses_bounded (fun e r =>
    e = act w (boundaryHitTime w h k + r))
  intro e he
  obtain ⟨n, htn, hen⟩ := boundary_path_future_edges w h k p e he
  refine ⟨n - boundaryHitTime w h k, ?_⟩
  rw [Nat.add_sub_of_le htn]
  exact hen

private def shiftedStagePathEdgeList {u : ℕ → Fin 3} {m : ℕ}
    {a b : StagePresentVertex u m} : Path a b → List ℕ
  | .nil => []
  | .cons p e => shiftedStagePathEdgeList p ++ [e.val]

private theorem shiftedStagePathEdgeList_length {u : ℕ → Fin 3} {m : ℕ}
    {a b : StagePresentVertex u m} (p : Path a b) :
    (shiftedStagePathEdgeList p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [shiftedStagePathEdgeList, Path.length_cons, ih]

private theorem shiftedStagePath_map_edgeList (w : ℕ → Fin 3) (t m : ℕ)
    {a b : StagePresentVertex (fun i => w (t + i)) m} (p : Path a b) :
    pathEdgeList ((kmswShiftStageToLimit w t m).mapPath p) =
      List.map (kmswShiftEdgeMapAll w t m) (shiftedStagePathEdgeList p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, pathEdgeList, ih,
        shiftedStagePathEdgeList, List.map_append, List.map_singleton]
      rfl

private theorem shiftedStage_path_target_bound (u : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex u m} (p : Path a b)
    (ha : a.id < (kmswStage u m).nextVertex) :
    b.id < (kmswStage u m).nextVertex := by
  induction p with
  | nil => exact ha
  | @cons x y q e =>
      have hbound := (kmswStage_endpoints_lt_nextVertex u m e.val e.property.1).2
      rw [e.property.2.2.2] at hbound
      exact hbound

private theorem shiftedStage_path_lift (w : ℕ → Fin 3) (t M : ℕ)
    {a b : PresentVertex w} (p : Path a b)
    (hstart : kmswShiftVertexMapAll w t M 0 = a.id)
    (hfuture : ∀ e ∈ pathEdgeList p, ∃ r ≤ M,
      e = act w (t + r)) :
    ∃ z : StagePresentVertex (fun i => w (t + i)) M,
      ∃ q : Path (⟨0⟩ : StagePresentVertex (fun i => w (t + i)) M) z,
        kmswShiftVertexMapAll w t M z.id = b.id ∧
        List.map (kmswShiftEdgeMapAll w t M) (shiftedStagePathEdgeList q) =
          pathEdgeList p := by
  induction p with
  | nil =>
      exact ⟨⟨0⟩, Path.nil, hstart, rfl⟩
  | @cons mid final p e ih =>
      have hfuturePrefix : ∀ f ∈ pathEdgeList p, ∃ r ≤ M,
          f = act w (t + r) := by
        intro f hf
        exact hfuture f (by
          rw [pathEdgeList]
          exact List.mem_append_left _ hf)
      obtain ⟨z, q, hz, hqedges⟩ := ih hfuturePrefix
      have hfutureLast : e.val ∈ pathEdgeList (Path.cons p e) := by
        rw [pathEdgeList]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      obtain ⟨r, hrM, her⟩ := hfuture e.val hfutureLast
      let u : ℕ → Fin 3 := fun i => w (t + i)
      let f := act u r
      have hfr := kmswShift_active_present w t r
      have hfM := present_mono u hfr.1 hfr.2 M hrM
      have hsim := kmswShift_sim2_all w t M
      have hfb := hsim.sim.edge_bound f hfM.1
      have hfp := hsim.sim.present f hfM.1 hfM.2
      have hfeq : kmswShiftEdgeMapAll w t M f = e.val := by
        rw [kmswShift_active_edge_map_of_le w t r M hrM, her]
      have hinc := hsim.sim.incidence f hfM.1
      have hwestMap : kmswShiftVertexMapAll w t M
          ((kmswStage u M).west f) = mid.id := by
        calc
          kmswShiftVertexMapAll w t M ((kmswStage u M).west f) =
              (kmswStage w (t + M)).west (kmswShiftEdgeMapAll w t M f) :=
            hinc.1.symm
          _ = edgeWest w (kmswShiftEdgeMapAll w t M f) :=
            (edge_endpoints_eq w hfb).1
          _ = edgeWest w e.val := by rw [hfeq]
          _ = mid.id := e.property.2.1
      have heastMap : kmswShiftVertexMapAll w t M
          ((kmswStage u M).east f) = final.id := by
        calc
          kmswShiftVertexMapAll w t M ((kmswStage u M).east f) =
              (kmswStage w (t + M)).east (kmswShiftEdgeMapAll w t M f) :=
            hinc.2.symm
          _ = edgeEast w (kmswShiftEdgeMapAll w t M f) :=
            (edge_endpoints_eq w hfb).2
          _ = edgeEast w e.val := by rw [hfeq]
          _ = final.id := e.property.2.2
      have hrootBound : 0 < (kmswStage u M).nextVertex := by
        have hm := CutConverse.nextVertex_mono u (Nat.zero_le M)
        simp [kmswStage, kmswInit] at hm
        omega
      have hzBound := shiftedStage_path_target_bound u M q hrootBound
      have hwestBound :=
        (kmswStage_endpoints_lt_nextVertex u M f hfM.1).1
      have hvertexEq : z.id = (kmswStage u M).west f :=
        hsim.sim.vertex_injective z.id ((kmswStage u M).west f)
          hzBound hwestBound (hz.trans hwestMap.symm)
      let fM : z ⟶ ⟨(kmswStage u M).east f⟩ :=
        ⟨f, hfM.1, hfM.2, hvertexEq.symm, rfl⟩
      refine ⟨⟨(kmswStage u M).east f⟩, Path.cons q fM, heastMap, ?_⟩
      simp only [shiftedStagePathEdgeList, List.map_append, List.map_singleton]
      rw [hqedges, hfeq]
      rfl

/-- A present path from a hit-indexed boundary vertex lifts to one common
finite stage of the shifted run. The image path has the same edge-ID sequence,
length, and terminal vertex (`lem-directed-contain`, -/
theorem boundary_path_lifts_to_shifted_stage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b) :
    ∃ m, ∃ z : StagePresentVertex (fun i => w (boundaryHitTime w h k + i)) m,
      ∃ q : Path (⟨0⟩ : StagePresentVertex
        (fun i => w (boundaryHitTime w h k + i)) m) z,
        (kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj
            (⟨0⟩ : StagePresentVertex
              (fun i => w (boundaryHitTime w h k + i)) m) =
          (⟨boundaryVertex w h k⟩ : PresentVertex w) ∧
        (kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj z = b ∧
        pathEdgeList ((kmswShiftStageToLimit w
          (boundaryHitTime w h k) m).mapPath q) = pathEdgeList p ∧
        ((kmswShiftStageToLimit w (boundaryHitTime w h k) m).mapPath q).length =
          p.length := by
  let t := boundaryHitTime w h k
  let u : ℕ → Fin 3 := fun i => w (t + i)
  obtain ⟨M, hfuture⟩ := boundaryPath_shiftOffsets_bounded w h k p
  have hstart : kmswShiftVertexMapAll w t M 0 =
      (⟨boundaryVertex w h k⟩ : PresentVertex w).id := by
    calc
      kmswShiftVertexMapAll w t M 0 = kmswShiftVertexMapAll w t 0 0 :=
        kmswShift_root_vertex_map_at w t M
      _ = boundaryVertex w h k := kmswShift_root_vertex_map w h k
  obtain ⟨z, q, hz, hqedges⟩ := shiftedStage_path_lift w t M p hstart hfuture
  have hobj : (kmswShiftStageToLimit w t M).obj z = b := by
    cases b
    simpa [kmswShiftStageToLimit] using hz
  have hstartObj : (kmswShiftStageToLimit w t M).obj
      (⟨0⟩ : StagePresentVertex u M) =
        (⟨boundaryVertex w h k⟩ : PresentVertex w) := by
    change (⟨kmswShiftVertexMapAll w t M 0⟩ : PresentVertex w) =
      ⟨boundaryVertex w h k⟩
    exact congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex w))
      ((kmswShift_root_vertex_map_at w t M).trans
        (kmswShift_root_vertex_map w h k))
  have hmapEdges :
      pathEdgeList ((kmswShiftStageToLimit w t M).mapPath q) = pathEdgeList p := by
    exact (shiftedStagePath_map_edgeList w t M q).trans hqedges
  have hlength : q.length = (pathEdgeList p).length := by
    have h := congrArg List.length hqedges
    simpa [List.length_map, shiftedStagePathEdgeList_length] using h
  have hmapLength :
      ((kmswShiftStageToLimit w t M).mapPath q).length = p.length := by
    calc
      ((kmswShiftStageToLimit w t M).mapPath q).length = q.length :=
        kmswShiftStageToLimit_length w t M q
      _ = (pathEdgeList p).length := hlength
      _ = p.length := pathEdgeList_length p
  exact ⟨M, z, q, hstartObj, hobj, hmapEdges, hmapLength⟩

/-- The vertex set of the hatted map at time `t`: images in the global limit
of vertices reachable from the shifted root in some finite shifted stage; this
is the vertex set of `M̂_{t,∞}`, used with hit-indexed `τ_k := boundaryHitTime w h k`
(identification with the source's directed-order `τ_k` is a separate bridge;
defined through finite stages; its equivalence with limit-reachability in the
shifted map and an induced submap structure (needed for clause 2) are not
provided here. -/
@[expose] def kmswShiftHatVertices (w : ℕ → Fin 3) (t : ℕ) :
    Set (PresentVertex w) :=
  {b | ∃ m, ∃ z : StagePresentVertex (fun i => w (t + i)) m,
    Reachable (⟨0⟩ : StagePresentVertex (fun i => w (t + i)) m) z ∧
      (kmswShiftStageToLimit w t m).obj z = b}

/-- Every endpoint of a present path from a hit-indexed boundary vertex lies
in the hatted map at its hit time (`lem-directed-contain`,
edge IDs and length in `boundary_path_lifts_to_shifted_stage`. -/
theorem boundary_path_endpoint_mem_shiftHat (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b) :
    b ∈ kmswShiftHatVertices w (boundaryHitTime w h k) := by
  obtain ⟨m, z, q, _, hobj, _, _⟩ :=
    boundary_path_lifts_to_shifted_stage w h k p
  exact ⟨m, z, ⟨q⟩, hobj⟩

/-- Every vertex reachable from the hit-indexed `x_k := boundaryVertex w h k`
lies in `M̂_{τ_k,∞}` with `τ_k := boundaryHitTime w h k` (here the vertex set
`kmswShiftHatVertices`). In particular, every prefix endpoint of a directed
path from `x_k` lies in the hatted map. Identifying these `x_k` / `τ_k` with
the source's directed-order ones is a separate bridge -/
theorem boundary_reachable_vertex_mem_shiftHat (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {c : PresentVertex w}
    (hr : Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w) c) :
    c ∈ kmswShiftHatVertices w (boundaryHitTime w h k) := by
  obtain ⟨q⟩ := hr
  exact boundary_path_endpoint_mem_shiftHat w h k q

/-- Almost surely, for the iid code realization every present path from every
hit-indexed boundary vertex `x_k := boundaryVertex w h k` is contained in the
hatted map at `τ_k := boundaryHitTime w h k`
witness is simultaneous over all integer levels. Identifying these with the
source's directed-order `x_k` / `τ_k` is a separate bridge. The reachability
form is `iidCodes_ae_boundary_reachable_in_shiftHat`. -/
theorem iidCodes_ae_boundary_paths_in_shiftHat :
    ∀ᵐ (ω : ℕ → Fin 3) ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i : ℕ => ω (i + 1)),
        ∀ k : ℤ, ∀ b : PresentVertex (fun i : ℕ => ω (i + 1)),
          ∀ p : Path
            (⟨boundaryVertex (fun i : ℕ => ω (i + 1)) h k⟩ :
              PresentVertex (fun i : ℕ => ω (i + 1))) b,
            ∃ m, ∃ z : StagePresentVertex
                (fun i : ℕ => (fun j : ℕ => ω (j + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k + i)) m,
              ∃ q : Path (⟨0⟩ : StagePresentVertex
                (fun i : ℕ => (fun j : ℕ => ω (j + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k + i)) m) z,
                (kmswShiftStageToLimit (fun i : ℕ => ω (i + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k) m).obj
                    (⟨0⟩ : StagePresentVertex
                      (fun i : ℕ => (fun j : ℕ => ω (j + 1))
                        (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k + i)) m) =
                  (⟨boundaryVertex (fun i : ℕ => ω (i + 1)) h k⟩ :
                    PresentVertex (fun i : ℕ => ω (i + 1))) ∧
                (kmswShiftStageToLimit (fun i : ℕ => ω (i + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k) m).obj z = b ∧
                pathEdgeList ((kmswShiftStageToLimit (fun i : ℕ => ω (i + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k) m).mapPath q) =
                    pathEdgeList p ∧
                ((kmswShiftStageToLimit (fun i : ℕ => ω (i + 1))
                  (boundaryHitTime (fun j : ℕ => ω (j + 1)) h k) m).mapPath q).length =
                    p.length := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, fun k b p => boundary_path_lifts_to_shifted_stage
    (fun i : ℕ => ω (i + 1)) h k p⟩





theorem iidCodes_ae_boundary_reachable_in_shiftHat :
    ∀ᵐ (ω : ℕ → Fin 3) ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i : ℕ => ω (i + 1)),
        ∀ (k : ℤ) (c : PresentVertex (fun i : ℕ => ω (i + 1))),
          Reachable (⟨boundaryVertex (fun i : ℕ => ω (i + 1)) h k⟩ :
            PresentVertex (fun i : ℕ => ω (i + 1))) c →
          c ∈ kmswShiftHatVertices (fun i : ℕ => ω (i + 1))
            (boundaryHitTime (fun i : ℕ => ω (i + 1)) h k) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, fun k c hr =>
    boundary_reachable_vertex_mem_shiftHat (fun i : ℕ => ω (i + 1)) h k hr⟩

end DirectedDistances.KMSW
