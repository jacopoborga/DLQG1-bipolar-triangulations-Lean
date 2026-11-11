module

public import DirectedDistances.Recursive.LDPRelatingDistances
public import DirectedDistances.KMSW.KMSWShiftLateLift











public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

private noncomputable def upShiftLimitFunctor (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let f : {e : ℕ // EdgePresent (fun i => w (1 + i)) e} := ⟨e.val, e.property.1⟩
    have hi := shiftLimitEdge_incidence w 1 f
    have ha : a = ⟨edgeWest (fun i => w (1 + i)) e.val⟩ := by
      cases a
      exact congrArg PresentVertex.mk e.property.2.1.symm
    have hb : b = ⟨edgeEast (fun i => w (1 + i)) e.val⟩ := by
      cases b
      exact congrArg PresentVertex.mk e.property.2.2.symm
    refine ⟨shiftLimitEdge w 1 f, shiftLimitEdge_present w 1 f, ?_, ?_⟩
    · rw [ha]
      exact hi.1
    · rw [hb]
      exact hi.2

private theorem upShiftLimitFunctor_length (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))} (p : Path a b) :
    ((upShiftLimitFunctor w).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- The shift embedding sends every shifted path to a global path of the same
length. Consequently the global SDP is at most the shifted SDP, including
unreachable pairs (`lem:SDP-relating-X1-X`, -/
theorem upShift_sdp_le (w : ℕ → Fin 3)
    (a b : PresentVertex (fun i => w (1 + i))) :
    sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) ≤ sdp a b := by
  by_cases hr : Reachable a b
  · obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
    calc
      sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) ≤
          ((upShiftLimitFunctor w).mapPath p).length := sdp_le_length _
      _ = p.length := by exact_mod_cast upShiftLimitFunctor_length w p
      _ = sdp a b := hp
  · rw [sdp_eq_top_iff_not_reachable.mpr hr]
    exact le_top

private theorem upShift_pathEdgeList_cast_start (w : ℕ → Fin 3)
    {a b c : PresentVertex w} (h : a = b) (q : Path a c) :
    pathEdgeList (h ▸ q) = pathEdgeList q := by
  cases h
  rfl

private theorem upShift_pathLength_cast_start (w : ℕ → Fin 3)
    {a b c : PresentVertex w} (h : a = b) (q : Path a c) :
    (h ▸ q).length = q.length := by
  cases h
  rfl

private theorem upShift_pathVertices_cast_start (w : ℕ → Fin 3)
    {a b c : PresentVertex w} (h : a = b) (q : Path a c) :
    (h ▸ q).vertices = q.vertices := by
  cases h
  rfl

private theorem upShift_late_of_avoiding_root (w : ℕ → Fin 3)
    {a b : PresentVertex w} (q : Path a b)
    (havoid : ∀ e ∈ pathEdgeList q, e ≠ act w 0) :
    ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, 1 ≤ actTime w e he := by
  intro e he heP
  have hne : actTime w e heP ≠ 0 := by
    intro hz
    apply havoid e he
    rw [actTime_spec w e heP, hz]
  omega

/-- A global path from a hit-indexed boundary point to a shift-image endpoint
that avoids the time-zero root edge lifts with its length unchanged. Only
the allocation hypothesis `ha` is explicit; reachability is given by the path `q` -/
theorem upShift_path_lift_avoiding_root (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (j : ℤ)
    (a : PresentVertex (fun i => w (1 + i)))
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hsource : shiftLimitVertex w 1 a = ⟨boundaryVertex w h0 j⟩)
    {v : PresentVertex w} (q : Path (⟨boundaryVertex w h0 j⟩) v)
    (havoid : ∀ e ∈ pathEdgeList q, e ≠ act w 0) :
    ∃ b : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) b ∧
      ∃ r : Path a b, shiftLimitVertex w 1 b = v ∧
        r.length = q.length ∧
        ∀ y ∈ r.vertices, shiftLimitVertex w 1 y ∈ q.vertices := by
  let q' : Path (shiftLimitVertex w 1 a) v := hsource.symm ▸ q
  have hedge : pathEdgeList q' = pathEdgeList q :=
    upShift_pathEdgeList_cast_start w hsource.symm q
  have hlate0 := upShift_late_of_avoiding_root w q havoid
  have hlate : ∀ e ∈ pathEdgeList q', ∀ he : EdgePresent w e,
      1 ≤ actTime w e he := by
    rw [hedge]
    exact hlate0
  obtain ⟨b, hb, r, hr, hlen, hvertices⟩ :=
    shiftLimitVertex_late_path_lift w 1 a ha q' hlate
  refine ⟨b, hb, r, hr, ?_, ?_⟩
  · exact hlen.trans (upShift_pathLength_cast_start w hsource.symm q)
  · have hv := upShift_pathVertices_cast_start w hsource.symm q
    intro y hy
    rw [← hv]
    exact hvertices y hy

end DirectedDistances.Recursive
