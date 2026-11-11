module

public import DirectedDistances.Recursive.LDPRelatingDistances
public import DirectedDistances.KMSW.KMSWShiftLateLift
import DirectedDistances.KMSW.UIBOTBoundaryM0

/-! Supporting lemmas for paper labels `lem:LDP-relating-X1-X` (see CORRESPONDENCE.md). -/

/-! # First-step LDP path lifting: initial edge data

Deterministic bookkeeping for the `(0,1)` code step in
global root edge is present but is not the shifted root edge; the other
allocated edge at the upper-right corner is initially missing. This file
retains the stage-one edge inventory, shifted-root mapping, nonroot edge
preimage, global-root presence, a concrete path using the root edge, the
root-avoiding finite path lift, and the activation-time characterization of
root avoidance.

The public declarations retained are `upShift_stageOne_edge_inventory`,
`upShift_initial_shifted_root_edge`,
`upShift_present_edge_has_shifted_preimage`,
`upShift_global_root_edge_present`,
`upShift_root_edge_can_precede_a_path`,
`upShift_path_lifts_avoiding_root`, and
`upShift_path_avoids_root_iff_late`.

Removed declarations: `upShift_root_path_decompose`,
`upShift_boundary_path_root_cases`, `upShift_global_path_dominated`, and
`upShift_boundary_ldpSup_eq`. The root-path decomposition proof and the
global path domination proof did not compile; the latter two public results
depend on those declarations. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- Exact stage-one edge inventory after `w 0 = 1`: the three allocated edge
IDs are `0,1,2`; IDs `0,1` are present, ID `2` is the missing upper-right
edge, and the displayed endpoints fix the edge orientations. This is the
initial exception data in the `(0,1)` case of `lem:LDP-relating-X1-X` -/
theorem upShift_stageOne_edge_inventory (w : ℕ → Fin 3) (hw : w 0 = 1) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 3 ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).west 0 = 0 ∧ (kmswStage w 1).east 0 = 1 ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).west 1 = 0 ∧ (kmswStage w 1).east 1 = 2 ∧
    (kmswStage w 1).present 2 = false ∧
    (kmswStage w 1).west 2 = 2 ∧ (kmswStage w 1).east 2 = 1 := by
  rcases firstStage_up w hw with
    ⟨hv, he, _, _, _, hp0, hp1, hp2, hw1, he1, hw2, he2⟩
  refine ⟨hv, he, hp0, ?_, ?_, hp1, hw1, he1, hp2, hw2, he2⟩
  · simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]
  · simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]

/-- At shifted time zero, the root edge of the shifted run maps to global edge
`1`, the active edge created by the first up step. Thus the global root edge
`0` is present but is not in this initial shifted-stage image -/
theorem upShift_initial_shifted_root_edge (w : ℕ → Fin 3)
    (hw : w 0 = 1) :
    kmswShiftEdgeMapAll w 1 0 0 = 1 ∧
      kmswShiftEdgeMapAll w 1 0 0 ≠ 0 := by
  have h := firstStage_up w hw
  constructor
  · simp [kmswShiftEdgeMapAll, kmswShiftRootEdgeNatMap, act,
      kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]
  · simp [kmswShiftEdgeMapAll, kmswShiftRootEdgeNatMap, act,
      kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]

/-- Every present global edge other than the initial root edge is the image
of a present edge in some finite run shifted by one time. Indeed, each present
edge has an activation time; a nonroot edge activates at a positive time, and
the shifted active edge maps to it. The global root edge `0` is present by
`upShift_global_root_edge_present` and is the sole exception to this
surjectivity statement (`lem:LDP-relating-X1-X`, -/
theorem upShift_present_edge_has_shifted_preimage (w : ℕ → Fin 3)
    {e : ℕ} (he : EdgePresent w e) (hne : e ≠ 0) :
    ∃ m, ∃ f, f < (kmswStage (fun i => w (1 + i)) m).nextEdge ∧
      (kmswStage (fun i => w (1 + i)) m).present f = true ∧
      kmswShiftEdgeMapAll w 1 m f = e := by
  let n := actTime w e he
  have htime : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    apply hne
    dsimp [n] at hn0
    rw [actTime_spec w e he, hn0]
    simp [act, kmswStage, kmswInit]
  let m := n - 1
  let f := act (fun i => w (1 + i)) m
  have hf := kmswShift_active_present w 1 m
  refine ⟨m, f, hf.1, hf.2, ?_⟩
  calc
    kmswShiftEdgeMapAll w 1 m f = act w (1 + m) := by
      dsimp [f]
      exact kmswShift_active_edge_map w 1 m
    _ = act w n := by
      congr 1
      dsimp [m]
      omega
    _ = e := (actTime_spec w e he).symm

/-- The global root edge `λ₀` is present after the first up step, with
orientation `0 → 1`. Its presence follows the manuscript's root convention -/
theorem upShift_global_root_edge_present (w : ℕ → Fin 3)
    (hw : w 0 = 1) : EdgePresent w 0 := by
  rcases upShift_stageOne_edge_inventory w hw with
    ⟨_, hne, hp0, hw0, he0, _, _, _, _, _, _⟩
  exact EdgePresent.of_stage_present (by omega) hp0

/-- The root exception can occur on a directed path from the global root to a
later vertex. For any walk whose first three steps are up, down, down, the
stage-three present graph contains the path `0 → 1 → 3`, whose first edge is
the exceptional global root edge. This records why the root edge cannot be
discarded from arbitrary paths before an LDP-maximizing argument -/
theorem upShift_root_edge_can_precede_a_path (w : ℕ → Fin 3)
    (h0 : w 0 = 1) (h1 : w 1 = 2) (h2 : w 2 = 2) :
    Nonempty (Path (⟨0⟩ : StagePresentVertex w 3) ⟨3⟩) := by
  have e01 : (⟨0⟩ : StagePresentVertex w 3) ⟶ ⟨1⟩ := by
    refine ⟨0, ?_, ?_, ?_, ?_⟩ <;>
      simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, h2,
        kmswStepOfStep, kmswInit, State.addEdge]
  have e13 : (⟨1⟩ : StagePresentVertex w 3) ⟶ ⟨3⟩ := by
    refine ⟨3, ?_, ?_, ?_, ?_⟩ <;>
      simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, h2,
        kmswStepOfStep, kmswInit, State.addEdge]
  exact ⟨Path.nil.cons e01 |>.cons e13⟩

private def upShiftStagePathEdgeList
    {u : ℕ → Fin 3} {m : ℕ} {a b : StagePresentVertex u m} :
    Path a b → List ℕ
  | .nil => []
  | .cons p e => upShiftStagePathEdgeList p ++ [e.val]

private theorem upShiftStagePathEdgeList_length
    {u : ℕ → Fin 3} {m : ℕ} {a b : StagePresentVertex u m}
    (p : Path a b) : (upShiftStagePathEdgeList p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [upShiftStagePathEdgeList, Path.length_cons, ih]

private theorem upShiftStagePath_map_edgeList (w : ℕ → Fin 3) (M : ℕ)
    {a b : StagePresentVertex (fun i => w (1 + i)) M} (p : Path a b) :
    pathEdgeList ((kmswShiftStageToLimit w 1 M).mapPath p) =
      List.map (kmswShiftEdgeMapAll w 1 M) (upShiftStagePathEdgeList p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, pathEdgeList, ih,
        upShiftStagePathEdgeList, List.map_append, List.map_singleton]
      rfl

private theorem upShiftStage_path_target_bound (u : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex u m} (p : Path a b)
    (ha : a.id < (kmswStage u m).nextVertex) :
    b.id < (kmswStage u m).nextVertex := by
  induction p with
  | nil => exact ha
  | @cons x y q e ih =>
      have hb := (kmswStage_endpoints_lt_nextVertex u m e.val e.property.1).2
      rw [e.property.2.2.2] at hb
      exact hb

/-- Lift a finite global path whose edges occur at or after the first shifted
time. This is the constructive path step used below; edge coverage is supplied
by the active-edge times, while `Sim2` supplies vertex injectivity and
incidence. -/
private theorem upShiftStage_path_lift (w : ℕ → Fin 3) (M : ℕ)
    {a b : PresentVertex w} (p : Path a b)
    {a₀ : StagePresentVertex (fun i => w (1 + i)) M}
    (hstart : kmswShiftVertexMapAll w 1 M a₀.id = a.id)
    (hstartBound : a₀.id < (kmswStage (fun i => w (1 + i)) M).nextVertex)
    (hfuture : ∀ e ∈ pathEdgeList p, ∃ r ≤ M,
      e = act w (1 + r)) :
    ∃ z : StagePresentVertex (fun i => w (1 + i)) M,
      ∃ q : Path a₀ z,
        kmswShiftVertexMapAll w 1 M z.id = b.id ∧
          List.map (kmswShiftEdgeMapAll w 1 M) (upShiftStagePathEdgeList q) =
            pathEdgeList p := by
  induction p generalizing a₀ with
  | nil =>
      exact ⟨a₀, Path.nil, hstart, rfl⟩
  | @cons mid final p e ih =>
      have hfuturePrefix : ∀ f ∈ pathEdgeList p, ∃ r ≤ M,
          f = act w (1 + r) := by
        intro f hf
        exact hfuture f (by
          rw [pathEdgeList]
          exact List.mem_append_left _ hf)
      obtain ⟨z, q, hz, hqedges⟩ :=
        ih hstart hstartBound hfuturePrefix
      have hfutureLast : e.val ∈ pathEdgeList (Path.cons p e) := by
        rw [pathEdgeList]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      obtain ⟨r, hrM, her⟩ := hfuture e.val hfutureLast
      let u : ℕ → Fin 3 := fun i => w (1 + i)
      let f := act u r
      have hfr := kmswShift_active_present w 1 r
      have hfM := present_mono u hfr.1 hfr.2 M hrM
      have hsim := kmswShift_sim2_all w 1 M
      have hfb := hsim.sim.edge_bound f hfM.1
      have hfp := hsim.sim.present f hfM.1 hfM.2
      have hfeq : kmswShiftEdgeMapAll w 1 M f = e.val := by
        rw [kmswShift_active_edge_map_of_le w 1 r M hrM, her]
      have hinc := hsim.sim.incidence f hfM.1
      have hwestMap : kmswShiftVertexMapAll w 1 M
          ((kmswStage u M).west f) = mid.id := by
        calc
          kmswShiftVertexMapAll w 1 M ((kmswStage u M).west f) =
              (kmswStage w (1 + M)).west
                (kmswShiftEdgeMapAll w 1 M f) := hinc.1.symm
          _ = edgeWest w (kmswShiftEdgeMapAll w 1 M f) :=
            (edge_endpoints_eq w hfb).1
          _ = edgeWest w e.val := by rw [hfeq]
          _ = mid.id := e.property.2.1
      have heastMap : kmswShiftVertexMapAll w 1 M
          ((kmswStage u M).east f) = final.id := by
        calc
          kmswShiftVertexMapAll w 1 M ((kmswStage u M).east f) =
              (kmswStage w (1 + M)).east
                (kmswShiftEdgeMapAll w 1 M f) := hinc.2.symm
          _ = edgeEast w (kmswShiftEdgeMapAll w 1 M f) :=
            (edge_endpoints_eq w hfb).2
          _ = edgeEast w e.val := by rw [hfeq]
          _ = final.id := e.property.2.2
      have hzBound := upShiftStage_path_target_bound u M q hstartBound
      have hwestBound :=
        (kmswStage_endpoints_lt_nextVertex u M f hfM.1).1
      have hvertexEq : z.id = (kmswStage u M).west f :=
        hsim.sim.vertex_injective z.id ((kmswStage u M).west f)
          hzBound hwestBound (hz.trans hwestMap.symm)
      let fM : z ⟶ ⟨(kmswStage u M).east f⟩ :=
        ⟨f, hfM.1, hfM.2, hvertexEq.symm, rfl⟩
      let q' := Path.cons q fM
      refine ⟨⟨(kmswStage u M).east f⟩, q', ?_, ?_⟩
      · simpa [q', fM] using heastMap
      · simp [q', fM, upShiftStagePathEdgeList, List.map_append,
          hqedges, hfeq, pathEdgeList]

private theorem upShift_boundary_vertex_stage_bound (u : ℕ → Fin 3)
    (h : BoundaryHitWitnesses u) (k : ℤ) :
    boundaryVertex u h k <
      (kmswStage u (boundaryHitTime u h k)).nextVertex := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryVertex_zero, boundaryHitTime_zero, kmswStage, kmswInit]
  · by_cases hk1 : k = 1
    · subst k
      have hmono := CutConverse.nextVertex_mono u (Nat.zero_le
        (boundaryHitTime u h 1))
      simp [kmswStage, kmswInit] at hmono
      simpa [boundaryVertex_one] using (show 1 <
        (kmswStage u (boundaryHitTime u h 1)).nextVertex by omega)
    · have hact := act_lt_nextEdge u (Nat.le_refl (boundaryHitTime u h k))
      have hbound := kmswStage_endpoints_lt_nextVertex u
        (boundaryHitTime u h k) (act u (boundaryHitTime u h k)) hact
      have hwest : edgeWest u (act u (boundaryHitTime u h k)) <
          (kmswStage u (boundaryHitTime u h k)).nextVertex := by
        rw [← (edge_endpoints_eq u hact).1]
        exact hbound.1
      simpa [boundaryVertex, hk0, hk1, activeInitial] using hwest







theorem upShift_path_lifts_avoiding_root (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) (j k : ℤ)
    (hpair : (j = -1 ∧ k = -1) ∨ (j = 0 ∧ k = 0) ∨ (j = 1 ∧ k = 2))
    {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h0 j⟩ : PresentVertex w) b)
    (havoid : 0 ∉ pathEdgeList p) :
    ∃ M, ∃ z : StagePresentVertex (fun i => w (1 + i)) M,
      ∃ q : Path (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        StagePresentVertex (fun i => w (1 + i)) M) z,
        (kmswShiftStageToLimit w 1 M).obj
          (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
            StagePresentVertex (fun i => w (1 + i)) M) =
          (⟨boundaryVertex w h0 j⟩ : PresentVertex w) ∧
        (kmswShiftStageToLimit w 1 M).obj z = b ∧
        pathEdgeList ((kmswShiftStageToLimit w 1 M).mapPath q) =
          pathEdgeList p ∧
        ((kmswShiftStageToLimit w 1 M).mapPath q).length = p.length := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  obtain ⟨M0, hbound⟩ := boundaryPath_shiftOffsets_bounded w h0 j p
  let M := max (boundaryHitTime w h0 j + M0)
    (boundaryHitTime u h1 k)
  have hfuture0 : ∀ e ∈ pathEdgeList p, ∃ r ≤ M,
      e = act w (1 + r) := by
    intro e he
    obtain ⟨r, hr, her⟩ := hbound e he
    have hidx : boundaryHitTime w h0 j + r ≠ 0 := by
      intro hz
      have hzero : boundaryHitTime w h0 j + r = 0 := hz
      have heq : e = 0 := by
        rw [her, hzero]
        simp [act, kmswStage, kmswInit]
      exact havoid (by simpa [heq] using he)
    refine ⟨boundaryHitTime w h0 j + r - 1, ?_, ?_⟩
    · dsimp [M]
      have hrM : boundaryHitTime w h0 j + r ≤
          boundaryHitTime w h0 j + M0 := by omega
      omega
    · have hidx' : 1 + (boundaryHitTime w h0 j + r - 1) =
        boundaryHitTime w h0 j + r := by omega
      rw [hidx']
      exact her
  have hfuture : ∀ e ∈ pathEdgeList p, ∃ r ≤ M,
      e = act w (1 + r) := by
    exact hfuture0
  let v : ℕ := boundaryVertex u h1 k
  have hvBoundAtHit : v <
      (kmswStage (fun i => w (1 + i)) (boundaryHitTime u h1 k)).nextVertex := by
    simpa [v, hseq] using upShift_boundary_vertex_stage_bound u h1 k
  have hstartAtHit : kmswShiftVertexMapAll w 1
      (boundaryHitTime u h1 k) v = boundaryVertex w h0 j := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact upShift_boundaryVertex_left w h0 h1 hw (-1) (by omega)
    · have hh := upShift_rootVertices w h0 hw
      simpa [v, boundaryHitTime_zero, boundaryVertex_zero] using hh.1
    · exact upShift_boundaryVertex_right w h0 h1 hw 2 (by omega)
  have hstart : kmswShiftVertexMapAll w 1 M v = boundaryVertex w h0 j := by
    have hstable := kmswShiftVertexMapAll_eq_of_le w 1
      (boundaryHitTime u h1 k) M v (Nat.le_max_right _ _)
      (by simpa [v, hseq] using upShift_boundary_vertex_stage_bound u h1 k)
    exact hstable.trans hstartAtHit
  have hvBound : v < (kmswStage (fun i => w (1 + i)) M).nextVertex := by
    have hm := CutConverse.nextVertex_mono (fun i => w (1 + i))
      (Nat.le_max_right (boundaryHitTime w h0 j + M0)
        (boundaryHitTime u h1 k))
    exact hvBoundAtHit.trans_le hm
  let a₀ : StagePresentVertex (fun i => w (1 + i)) M := ⟨v⟩
  obtain ⟨z, q, hz, hqedges⟩ :=
    upShiftStage_path_lift w M p hstart hvBound hfuture
  have hstartObj : (kmswShiftStageToLimit w 1 M).obj a₀ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
    change (⟨kmswShiftVertexMapAll w 1 M v⟩ : PresentVertex w) = _
    exact congrArg (fun x : ℕ => (⟨x⟩ : PresentVertex w)) hstart
  have hobj : (kmswShiftStageToLimit w 1 M).obj z = b := by
    cases b
    simpa [kmswShiftStageToLimit] using hz
  have hmapEdges : pathEdgeList ((kmswShiftStageToLimit w 1 M).mapPath q) =
      pathEdgeList p := by
    calc
      pathEdgeList ((kmswShiftStageToLimit w 1 M).mapPath q) =
          List.map (kmswShiftEdgeMapAll w 1 M) (upShiftStagePathEdgeList q) :=
        upShiftStagePath_map_edgeList w M q
      _ = pathEdgeList p := hqedges
  have hlength :
      ((kmswShiftStageToLimit w 1 M).mapPath q).length = p.length := by
    calc
      ((kmswShiftStageToLimit w 1 M).mapPath q).length = q.length :=
        kmswShiftStageToLimit_length w 1 M q
      _ = (pathEdgeList p).length := by
        have h := congrArg List.length hqedges
        simpa [List.length_map, upShiftStagePathEdgeList_length] using h
      _ = p.length := pathEdgeList_length p
  exact ⟨M, z, q, hstartObj, hobj, hmapEdges, hlength⟩

private theorem upShift_pathEdge_present (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) : EdgePresent w e := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons x y p f ih =>
      rw [pathEdgeList] at he
      rcases List.mem_append.mp he with hp | hf
      · exact ih hp
      · have h : e = f.val := List.mem_singleton.mp hf
        subst e
        exact f.property.1





theorem upShift_path_avoids_root_iff_late (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) :
    0 ∉ pathEdgeList p ↔
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        1 ≤ actTime w e he := by
  constructor
  · intro h e he hpresent
    by_contra htime
    have hz : actTime w e hpresent = 0 := by omega
    have heq : e = 0 := by
      rw [actTime_spec w e hpresent, hz]
      simp [act, kmswStage, kmswInit]
    exact h (heq ▸ he)
  · intro h hroot
    have hpresent := upShift_pathEdge_present w p hroot
    have hzero : actTime w 0 hpresent = 0 :=
      (actTime_eq_iff w 0 hpresent 0).2 (by simp [act, kmswStage, kmswInit])
    have := h 0 hroot hpresent
    omega

private theorem upShift_vertex_ext {w : ℕ → Fin 3} {a b : PresentVertex w}
    (h : a.id = b.id) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem upShift_path_source_mem (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) :
    (⟨edgeWest w e⟩ : PresentVertex w) ∈ p.vertices := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons x y p f ih =>
      rw [pathEdgeList] at he
      rcases List.mem_append.mp he with hp | hf
      · exact (Path.mem_vertices_cons p f).2 (Or.inl (ih hp))
      · have h : e = f.val := List.mem_singleton.mp hf
        subst e
        have hmid : (⟨edgeWest w f.val⟩ : PresentVertex w) = x :=
          upShift_vertex_ext f.property.2.1
        rw [hmid]
        exact (Path.mem_vertices_cons p f).2 (Or.inl p.end_mem_vertices)

private theorem upShift_path_source_vertex_eq_start {w : ℕ → Fin 3}
    {a b x : PresentVertex w} (p : Path a b)
    (hsource : ∀ e, EdgePresent w e → edgeEast w e ≠ x.id)
    (hx : x ∈ p.vertices) : x = a := by
  induction p with
  | nil => simpa only [Path.vertices_nil, List.mem_singleton] using hx
  | @cons a' b' p e ih =>
      rcases (Path.mem_vertices_cons p e).mp hx with hprefix | hend
      · exact ih hprefix
      · have hid : x.id = edgeEast w e.val := by
          rw [hend]
          exact e.property.2.2.symm
        exact (hsource e.val e.property.1 hid.symm).elim

private theorem upShift_path_avoids_root_from_ne_zero_index
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) {j : ℤ}
    (hj : j = -1 ∨ j = 1) {z : PresentVertex w}
    (p : Path (⟨boundaryVertex w h j⟩ : PresentVertex w) z) :
    0 ∉ pathEdgeList p := by
  intro hroot
  have hsourceMem := upShift_path_source_mem w p hroot
  have hno : ∀ e, EdgePresent w e →
      edgeEast w e ≠ boundaryVertex w h 0 := by
    intro e he
    exact boundaryVertex_nonpos_no_incoming w h (by omega : (0 : ℤ) ≤ 0) e he
  have hstart := upShift_path_source_vertex_eq_start
    (x := (⟨boundaryVertex w h 0⟩ : PresentVertex w)) p hno hsourceMem
  have hneq : boundaryVertex w h j ≠ boundaryVertex w h 0 := by
    rcases hj with rfl | rfl
    · have hhitpos : 0 < boundaryHitTime w h (-1) := by
        have hs := boundaryHitTime_left_spec w h (by omega : (-1 : ℤ) ≤ -1)
        by_contra hn
        have hn0 : boundaryHitTime w h (-1) = 0 := by omega
        rw [hn0] at hs
        simp [L] at hs
      have hfirst := boundaryVertex_first_visit_left w h
        (by omega : (-1 : ℤ) ≤ -1) 0 hhitpos
      intro heq
      apply hfirst
      calc
        boundaryVertex w h (-1) = boundaryVertex w h 0 := heq
        _ = activeInitial w 0 := by
          rw [boundaryVertex_zero]
          calc
            0 = (kmswStage w 0).west 0 := (initial_edge_endpoints w 0).1.symm
            _ = edgeWest w 0 :=
              (edge_endpoints_eq w (by change 0 < 1; omega)).1
            _ = activeInitial w 0 := by
              simp [activeInitial, act, kmswStage, kmswInit]
    · simp [boundaryVertex_one, boundaryVertex_zero]
  have hrootWest : edgeWest w 0 = 0 := by
    calc
      edgeWest w 0 = (kmswStage w 0).west 0 :=
        (edge_endpoints_eq w (by change 0 < 1; omega)).1.symm
      _ = 0 := (initial_edge_endpoints w 0).1
  exact hneq (by
    have hids := congrArg PresentVertex.id hstart
    calc
      boundaryVertex w h j = edgeWest w 0 := hids.symm
      _ = boundaryVertex w h 0 := by rw [boundaryVertex_zero, hrootWest])

private def upShift_root_arrow (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hw : w 0 = 1) :
    (⟨boundaryVertex w h 0⟩ : PresentVertex w) ⟶
      (⟨boundaryVertex w h 1⟩ : PresentVertex w) := by
  refine ⟨0, upShift_global_root_edge_present w hw, ?_, ?_⟩
  · calc
      edgeWest w 0 = (kmswStage w 0).west 0 :=
        (edge_endpoints_eq w (by change 0 < 1; omega)).1.symm
      _ = 0 := (initial_edge_endpoints w 0).1
      _ = boundaryVertex w h 0 := (boundaryVertex_zero w h).symm
  · calc
      edgeEast w 0 = (kmswStage w 0).east 0 :=
        (edge_endpoints_eq w (by change 0 < 1; omega)).2.symm
      _ = 1 := (initial_edge_endpoints w 0).2
      _ = boundaryVertex w h 1 := (boundaryVertex_one w h).symm

private theorem upShift_path_ending_at_root_source_is_nil
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {a : PresentVertex w} (p : Path a ⟨boundaryVertex w h 0⟩) :
    p.length = 0 := by
  cases p with
  | nil => rfl
  | @cons x y p e =>
      have hend : edgeEast w e.val = boundaryVertex w h 0 := by
        simpa using e.property.2.2
      exact (boundaryVertex_nonpos_no_incoming w h (by omega : (0 : ℤ) ≤ 0)
        e.val e.property.1 hend).elim

private noncomputable def upShiftLimitToGlobal (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let ef : {f : ℕ // EdgePresent (fun i => w (1 + i)) f} :=
      ⟨e.val, e.property.1⟩
    have hinc := shiftLimitEdge_incidence w 1 ef
    have ha : a = ⟨edgeWest (fun i => w (1 + i)) e.val⟩ :=
      upShift_vertex_ext e.property.2.1.symm
    have hb : b = ⟨edgeEast (fun i => w (1 + i)) e.val⟩ :=
      upShift_vertex_ext e.property.2.2.symm
    exact ⟨shiftLimitEdge w 1 ef, shiftLimitEdge_present w 1 ef,
      hinc.1.trans (congrArg (fun v => v.id)
        (congrArg (shiftLimitVertex w 1) ha.symm)),
      hinc.2.trans (congrArg (fun v => v.id)
        (congrArg (shiftLimitVertex w 1) hb.symm))⟩

private theorem upShiftLimitToGlobal_length (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))} (p : Path a b) :
    ((upShiftLimitToGlobal w).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem upShift_shiftStart_allocated (w : ℕ → Fin 3)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    kmswVertexAllocated (fun i => w (1 + i))
      ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  exact ⟨boundaryHitTime u h1 k,
    by simpa [hseq] using upShift_boundary_vertex_stage_bound u h1 k⟩

private theorem upShift_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) {j k : ℤ}
    (hpair : (j = -1 ∧ k = -1) ∨ (j = 0 ∧ k = 0) ∨ (j = 1 ∧ k = 2)) :
    shiftLimitVertex w 1
      ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
        (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  have hbound : boundaryVertex u h1 k <
      (kmswStage (fun i => w (1 + i)) (boundaryHitTime u h1 k)).nextVertex := by
    simpa [hseq] using upShift_boundary_vertex_stage_bound u h1 k
  have hstage : kmswShiftVertexMapAll w 1 (boundaryHitTime u h1 k)
      (boundaryVertex u h1 k) = boundaryVertex w h0 j := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact upShift_boundaryVertex_left w h0 h1 hw (-1) (by omega)
    · have hh := upShift_rootVertices w h0 hw
      simpa [u, boundaryHitTime_zero, boundaryVertex_zero] using hh.1
    · exact upShift_boundaryVertex_right w h0 h1 hw 2 (by omega)
  rw [shiftLimitVertex_eq w 1 (boundaryHitTime u h1 k)
    ⟨boundaryVertex u h1 k⟩ hbound]
  exact congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex w)) hstage

private theorem upShift_boundary_0_to_2_path (u : ℕ → Fin 3)
    (h : BoundaryHitWitnesses u) :
    ∃ p : Path (⟨boundaryVertex u h 0⟩ : PresentVertex u)
        ⟨boundaryVertex u h 2⟩, p.length = 2 := by
  obtain ⟨e₀, hp₀, hw₀, he₀⟩ := boundaryVertex_nonneg_successor_edge u h
    (k := 0) (by omega)
  obtain ⟨e₁, hp₁, hw₁, he₁⟩ := boundaryVertex_nonneg_successor_edge u h
    (k := 1) (by omega)
  let f₀ : (⟨boundaryVertex u h 0⟩ : PresentVertex u) ⟶
      ⟨boundaryVertex u h 1⟩ := ⟨e₀, hp₀, hw₀, he₀⟩
  let f₁ : (⟨boundaryVertex u h 1⟩ : PresentVertex u) ⟶
      ⟨boundaryVertex u h 2⟩ := ⟨e₁, hp₁, hw₁, he₁⟩
  exact ⟨Path.nil.cons f₀ |>.cons f₁, by simp⟩

end DirectedDistances.Recursive
