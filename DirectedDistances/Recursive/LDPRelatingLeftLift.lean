module

public import DirectedDistances.Recursive.LDPRelatingLeft
public import DirectedDistances.KMSW.KMSWShiftLateLift
import DirectedDistances.KMSW.UIBOTBoundaryM0









public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- The first-stage `(-1,0)` triangle, including the retained edge IDs,
is the missing side at stage one; it is never present: its east endpoint is vertex 0, which has no incoming edge (`uibot_zero_no_incoming`). -/
theorem leftStep_firstStage_triangle (w : ℕ → Fin 3) (hw : w 0 = 0) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 3 ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).present 2 = false ∧
    (kmswStage w 1).west 0 = 0 ∧ (kmswStage w 1).east 0 = 1 ∧
    (kmswStage w 1).west 1 = 2 ∧ (kmswStage w 1).east 1 = 1 ∧
    (kmswStage w 1).west 2 = 2 ∧ (kmswStage w 1).east 2 = 0 := by
  rcases firstStage_left w hw with
    ⟨hv, he, _, _, _, hp0, hp1, hp2, hw1, he1⟩
  have hroot := initial_edge_endpoints w 1
  refine ⟨hv, he, hp0, hp1, hp2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hroot.1
  · exact hroot.2
  · exact hw1
  · exact he1
  · simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]
  · simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      kmswInit, State.addEdge]

private theorem leftStep_globalRoot_edge (w : ℕ → Fin 3) :
    EdgePresent w 0 ∧ edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 ∧ act w 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨0, (initial_edge_present w 0).1, (initial_edge_present w 0).2⟩
  · exact (initial_edge_endpoints w 0).1
  · exact (initial_edge_endpoints w 0).2
  · simp [act, kmswStage, kmswInit]

private theorem leftStep_path_endpoint_ne_root {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) : b.id ≠ 0 := by
  induction p with
  | nil => exact ha
  | @cons mid final p e ih =>
      intro hfinal
      have heast0 : edgeEast w e.val = 0 := e.property.2.2.trans hfinal
      exact (uibot_zero_no_incoming w e.val e.property.1) heast0

private theorem leftStep_path_edges_avoid_root (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) :
    ∀ e ∈ pathEdgeList p, e ≠ 0 := by
  revert ha
  induction p with
  | nil => intro ha; simp [pathEdgeList]
  | @cons mid final p edge ih =>
      intro ha
      have hmid : mid.id ≠ 0 := leftStep_path_endpoint_ne_root p ha
      intro e he
      simp only [pathEdgeList, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact ih ha e he
      · subst e
        intro hz
        have hw0 := (leftStep_globalRoot_edge w).2.1
        have hmid0 : mid.id = 0 := by
          calc
            mid.id = edgeWest w edge.val := edge.property.2.1.symm
            _ = edgeWest w 0 := by rw [hz]
            _ = 0 := hw0
        exact hmid hmid0

private theorem leftStep_path_edges_late (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) :
    ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, 1 ≤ actTime w e he := by
  intro e hemem he
  have hne := leftStep_path_edges_avoid_root w p ha e hemem
  have htime : e = act w (actTime w e he) := actTime_spec w e he
  by_contra hn
  have hzero : actTime w e he = 0 := by omega
  rw [hzero] at htime
  have hact0 := (leftStep_globalRoot_edge w).2.2.2
  rw [hact0] at htime
  exact hne htime

/-- Every global path between image vertices whose edges all activate at time ≥ 1 lifts to the shifted limit with exactly the same length. The
no-time-zero-edge condition is automatic for paths whose initial global
vertex is a non-root boundary vertex (`lem:LDP-relating-X1-X`, -/
theorem leftStep_late_path_lift (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    {z : PresentVertex w}
    (q : Path (shiftLimitVertex w 1 a) z)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      1 ≤ actTime w e he)
    (hzb : z = shiftLimitVertex w 1 b) :
    ∃ r : Path a b, r.length = q.length := by
  have hlate' : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      1 ≤ actTime w e he := hlate
  obtain ⟨c, hc, r, hr, hlen, _⟩ :=
    shiftLimitVertex_late_path_lift w 1 a ha q (by
      intro e hemem he
      exact hlate' e hemem he)
  have hcb : c = b := by
    apply shiftLimitVertex_injective w 1 hc hb
    rw [hr, hzb]
  subst c
  exact ⟨r, hlen⟩

private noncomputable def leftStepLimitMap (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let f : {f : ℕ // EdgePresent (fun i => w (1 + i)) f} := ⟨e.val, e.property.1⟩
    refine ⟨shiftLimitEdge w 1 f, shiftLimitEdge_present w 1 f, ?_, ?_⟩
    · have hi := (shiftLimitEdge_incidence w 1 f).1
      have ha : (⟨edgeWest (fun i => w (1 + i)) e.val⟩ :
          PresentVertex (fun i => w (1 + i))) = a := by
        cases a
        exact congrArg PresentVertex.mk e.property.2.1
      exact hi.trans (congrArg PresentVertex.id
        (congrArg (shiftLimitVertex w 1) ha))
    · have hi := (shiftLimitEdge_incidence w 1 f).2
      have hb : (⟨edgeEast (fun i => w (1 + i)) e.val⟩ :
          PresentVertex (fun i => w (1 + i))) = b := by
        cases b
        exact congrArg PresentVertex.mk e.property.2.2
      exact hi.trans (congrArg PresentVertex.id
        (congrArg (shiftLimitVertex w 1) hb))

private theorem leftStepLimitMap_path_length (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))} (p : Path a b) :
    ((leftStepLimitMap w).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem leftStep_pathLengths_eq (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hsource : (shiftLimitVertex w 1 a).id ≠ 0) :
    pathLengths a b =
      pathLengths (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := by
  apply Set.Subset.antisymm
  · rintro n ⟨p, rfl⟩
    exact ⟨(leftStepLimitMap w).mapPath p,
      leftStepLimitMap_path_length w p⟩
  · rintro n ⟨p, rfl⟩
    have hlate := leftStep_path_edges_late w p hsource
    obtain ⟨c, hc, q, hq, hlen, _⟩ :=
      shiftLimitVertex_late_path_lift w 1 a ha p (by
        intro e hemem he
        exact hlate e hemem he)
    have hcb : c = b := by
      apply shiftLimitVertex_injective w 1 hc hb
      exact hq
    subst c
    exact ⟨q, hlen⟩

/-- For a non-root shifted image source, every global path to another image
vertex has exactly the same possible lengths as a shifted path, for reachable pairs. The path lift is the one in
`(-1,0)` case of `lem:LDP-relating-X1-X` -/
theorem leftStep_ldpSup_image_eq (w : ℕ → Fin 3)
    (hbound : PresentPathLengthsBounded (w := w))
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hreach : Reachable a b)
    (hsource : (shiftLimitVertex w 1 a).id ≠ 0) :
    ldpSup (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) = ldpSup a b := by
  have hpaths := leftStep_pathLengths_eq w ha hb hsource
  have hglobal : Reachable (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := by
    obtain ⟨p⟩ := hreach
    exact ⟨(leftStepLimitMap w).mapPath p⟩
  have _ := hbound (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) hglobal
  unfold ldpSup
  rw [hpaths]

/-- The shifted root source maps to global `x^0_{-1}`; its global paths avoid
the time-zero root edge and therefore have the same LDP supremum as paths
from shifted `x^1_0`. This is the first deterministic identity in
`eqn-ldp-relating2` (`lem:LDP-relating-X1-X`, -/
theorem leftStep_ldpSup_leftBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0)
    (hbound : PresentPathLengthsBounded (w := w)) :
    ∀ b : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) b →
      Reachable (⟨0⟩ : PresentVertex (fun i => w (1 + i))) b →
      ldpSup (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
        ldpSup (⟨0⟩ : PresentVertex (fun i => w (1 + i))) b := by
  intro b hb hreach
  have ha : kmswVertexAllocated (fun i => w (1 + i))
      (⟨0⟩ : PresentVertex (fun i => w (1 + i))) := by
    exact ⟨0, by simp [kmswStage, kmswInit]⟩
  have hrootMap : shiftLimitVertex w 1
      (⟨0⟩ : PresentVertex (fun i => w (1 + i))) =
      (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w) := by
    rw [shiftLimitVertex_eq w 1 0 ⟨0⟩ (by simp [kmswStage, kmswInit])]
    exact congrArg PresentVertex.mk
      (leftShift_rootVertices_and_firstStageImage w h0 hw).1
  have hsource : (shiftLimitVertex w 1
      (⟨0⟩ : PresentVertex (fun i => w (1 + i)))).id ≠ 0 := by
    rw [hrootMap]
    intro hz
    change boundaryVertex w h0 (-1) = 0 at hz
    have hzero := boundaryVertex_zero w h0
    have hidx := (boundaryVertex_injective w h0) (hz.trans hzero.symm)
    omega
  rw [← hrootMap]
  exact leftStep_ldpSup_image_eq w hbound ha hb hreach hsource

/-- The shifted right root maps to global `x^0_1`, yielding the third
deterministic identity in `eqn-ldp-relating2` for every reachable pair -/
theorem leftStep_ldpSup_rightBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0)
    (hbound : PresentPathLengthsBounded (w := w)) :
    ∀ b : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) b →
      Reachable (⟨1⟩ : PresentVertex (fun i => w (1 + i))) b →
      ldpSup (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
        ldpSup (⟨1⟩ : PresentVertex (fun i => w (1 + i))) b := by
  intro b hb hreach
  have ha : kmswVertexAllocated (fun i => w (1 + i))
      (⟨1⟩ : PresentVertex (fun i => w (1 + i))) := by
    exact ⟨0, by simp [kmswStage, kmswInit]⟩
  have hrootMap : shiftLimitVertex w 1
      (⟨1⟩ : PresentVertex (fun i => w (1 + i))) =
      (⟨boundaryVertex w h0 1⟩ : PresentVertex w) := by
    rw [shiftLimitVertex_eq w 1 0 ⟨1⟩ (by simp [kmswStage, kmswInit])]
    exact congrArg PresentVertex.mk
      (leftShift_rootVertices_and_firstStageImage w h0 hw).2.1
  have hsource : (shiftLimitVertex w 1
      (⟨1⟩ : PresentVertex (fun i => w (1 + i)))).id ≠ 0 := by
    rw [hrootMap]
    change boundaryVertex w h0 1 ≠ 0
    rw [boundaryVertex_one]
    omega
  rw [← hrootMap]
  exact leftStep_ldpSup_image_eq w hbound ha hb hreach hsource

end DirectedDistances.Recursive
