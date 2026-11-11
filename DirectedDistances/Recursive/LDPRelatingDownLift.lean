module

public import DirectedDistances.Recursive.LDPRelatingDown
public import DirectedDistances.KMSW.KMSWShiftLateLift
import DirectedDistances.KMSW.BoundaryEnumeration
import DirectedDistances.KMSW.UIBOTBoundaryM0










public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- The first global stage after the `(1,-1)` step, with both present edge
IDs and their orientations. The shifted initial image is the pair of
vertices `1,2`, while the older root edge `0 : 0 → 1` is the time-zero -/
theorem downShift_stageOne_edge_inventory (w : ℕ → Fin 3) (hw : w 0 = 2) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 2 ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).west 0 = 0 ∧ (kmswStage w 1).east 0 = 1 ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).west 1 = 1 ∧ (kmswStage w 1).east 1 = 2 := by
  rcases firstStage_down w hw with
    ⟨hv, he, _, _, _, hp0, hp1, hw1, he1⟩
  refine ⟨hv, he, hp0, ?_, ?_, hp1, hw1, he1⟩
  · exact (initial_edge_endpoints w 1).1
  · exact (initial_edge_endpoints w 1).2

private theorem downShift_globalRoot_edge (w : ℕ → Fin 3) :
    EdgePresent w 0 ∧ edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 ∧ act w 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨0, (initial_edge_present w 0).1, (initial_edge_present w 0).2⟩
  · exact (initial_edge_endpoints w 0).1
  · exact (initial_edge_endpoints w 0).2
  · simp [act, kmswStage, kmswInit]

private theorem downShift_vertex_ext {w : ℕ → Fin 3}
    {a b : PresentVertex w} (h : a.id = b.id) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem downShift_pathEdge_present (w : ℕ → Fin 3)
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

private theorem downShift_path_source_mem (w : ℕ → Fin 3)
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
        have hmid : (⟨edgeWest w f.val⟩ : PresentVertex w) = x := by
          cases y
          exact congrArg PresentVertex.mk f.property.2.1
        rw [hmid]
        exact (Path.mem_vertices_cons p f).2 (Or.inl p.end_mem_vertices)

private theorem downShift_path_source_eq_start (w : ℕ → Fin 3)
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

private theorem downShift_path_ending_at_root_source_is_nil
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {a : PresentVertex w} (p : Path a ⟨boundaryVertex w h 0⟩) :
    p.length = 0 := by
  cases p with
  | nil => rfl
  | @cons x y p e =>
      have hend : edgeEast w e.val = boundaryVertex w h 0 := by
        simpa using e.property.2.2
      exact (boundaryVertex_nonpos_no_incoming w h (by omega) e.val
        e.property.1 hend).elim

private theorem downShift_root_path_decompose (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {z : PresentVertex w}
    (p : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) z)
    (hroot : 0 ∈ pathEdgeList p) :
    ∃ q : Path (⟨boundaryVertex w h 1⟩ : PresentVertex w) z,
      pathEdgeList p = 0 :: pathEdgeList q ∧ p.length = q.length + 1 := by
  induction p with
  | nil => simp [pathEdgeList] at hroot
  | @cons mid final p e ih =>
      rw [pathEdgeList] at hroot
      rcases List.mem_append.mp hroot with hp | he
      · obtain ⟨q, hq, hlen⟩ := ih hp
        refine ⟨q.cons e, ?_, ?_⟩
        · rw [pathEdgeList, hq]
          simp [pathEdgeList, hq]
        · simp only [Path.length_cons, hlen]
      · have he0 : e.val = 0 := (List.mem_singleton.mp he).symm
        have hmid : mid = (⟨boundaryVertex w h 0⟩ : PresentVertex w) := by
          apply downShift_vertex_ext
          calc
            mid.id = edgeWest w e.val := e.property.2.1.symm
            _ = edgeWest w 0 := by rw [he0]
            _ = (kmswStage w 0).west 0 :=
              (edge_endpoints_eq w (by change 0 < 1; omega)).1.symm
            _ = boundaryVertex w h 0 := by
              rw [(initial_edge_endpoints w 0).1, boundaryVertex_zero]
        have hpLen : p.length = 0 := by
          cases hmid
          exact downShift_path_ending_at_root_source_is_nil w h p
        cases hmid
        have hpNil : p = Path.nil := Path.eq_nil_of_length_zero p hpLen
        rw [hpNil]
        have hfinal : final = (⟨boundaryVertex w h 1⟩ : PresentVertex w) := by
          apply downShift_vertex_ext
          calc
            final.id = edgeEast w e.val := e.property.2.2.symm
            _ = edgeEast w 0 := by rw [he0]
            _ = (kmswStage w 0).east 0 :=
              (edge_endpoints_eq w (by change 0 < 1; omega)).2.symm
            _ = boundaryVertex w h 1 := by
              rw [(initial_edge_endpoints w 0).2, boundaryVertex_one]
        subst final
        refine ⟨Path.nil, ?_, ?_⟩ <;> simp [pathEdgeList, he0]

/-- A path from a hit-indexed global boundary vertex either avoids the
time-zero root edge or starts at `x⁰₀` and traverses that edge first. In the
second case the remaining path starts at `x⁰₁` and its length is exactly one -/
theorem downShift_boundary_path_root_cases (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (j : ℤ) {z : PresentVertex w}
    (p : Path (⟨boundaryVertex w h0 j⟩ : PresentVertex w) z) :
    0 ∉ pathEdgeList p ∨
      (j = 0 ∧ ∃ q : Path (⟨boundaryVertex w h0 1⟩ : PresentVertex w) z,
        pathEdgeList p = 0 :: pathEdgeList q ∧ p.length = q.length + 1) := by
  by_cases hroot : 0 ∈ pathEdgeList p
  · right
    have hsourceMem := downShift_path_source_mem w p hroot
    have hrootSource : (⟨edgeWest w 0⟩ : PresentVertex w) = ⟨0⟩ := by
      exact downShift_vertex_ext (downShift_globalRoot_edge w).2.1
    rw [hrootSource] at hsourceMem
    have hno : ∀ e, EdgePresent w e → edgeEast w e ≠ 0 := by
      intro e he
      exact uibot_zero_no_incoming w e he
    have hstart := downShift_path_source_eq_start w p hno hsourceMem
    have hj : j = 0 := by
      apply boundaryVertex_injective w h0
      have hid := congrArg PresentVertex.id hstart.symm
      rw [boundaryVertex_zero]
      exact hid
    subst j
    exact ⟨rfl, downShift_root_path_decompose w h0 p hroot⟩
  · exact Or.inl hroot

/-- A global path avoids the initial root edge exactly when every one of its
edges activates at or after shifted time one. The activation-time convention
is that edge `0` is the unique edge activated at global time zero -/
theorem downShift_path_avoids_root_iff_late (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) :
    0 ∉ pathEdgeList p ↔
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        1 ≤ actTime w e he := by
  constructor
  · intro h e hemem he
    by_contra htime
    have hz : actTime w e he = 0 := by omega
    have heq : e = 0 := by
      rw [actTime_spec w e he, hz]
      simp [act, kmswStage, kmswInit]
    exact h (heq ▸ hemem)
  · intro h hroot
    have he := downShift_pathEdge_present w p hroot
    have hz : actTime w 0 he = 0 :=
      (actTime_eq_iff w 0 he 0).2 (by simp [act, kmswStage, kmswInit])
    have hlate := h 0 hroot he
    omega

private noncomputable def downShiftLimitMap (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let ef : {f : ℕ // EdgePresent (fun i => w (1 + i)) f} :=
      ⟨e.val, e.property.1⟩
    have hinc := shiftLimitEdge_incidence w 1 ef
    have ha : a = ⟨edgeWest (fun i => w (1 + i)) e.val⟩ := by
      cases a
      exact congrArg PresentVertex.mk e.property.2.1.symm
    have hb : b = ⟨edgeEast (fun i => w (1 + i)) e.val⟩ := by
      cases b
      exact congrArg PresentVertex.mk e.property.2.2.symm
    exact ⟨shiftLimitEdge w 1 ef, shiftLimitEdge_present w 1 ef,
      hinc.1.trans (congrArg (fun v => v.id)
        (congrArg (shiftLimitVertex w 1) ha.symm)),
      hinc.2.trans (congrArg (fun v => v.id)
        (congrArg (shiftLimitVertex w 1) hb.symm))⟩

private theorem downShiftLimitMap_length (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))} (p : Path a b) :
    ((downShiftLimitMap w).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem downShift_late_path_liftCore (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    {z : PresentVertex w}
    (q : Path (shiftLimitVertex w 1 a) z)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      1 ≤ actTime w e he)
    (hzb : z = shiftLimitVertex w 1 b) :
    ∃ r : Path a b, r.length = q.length := by
  obtain ⟨c, hc, r, hr, hlen, _⟩ :=
    shiftLimitVertex_late_path_lift w 1 a ha q hlate
  have hcb : c = b := by
    apply shiftLimitVertex_injective w 1 hc hb
    rw [hr, hzb]
  subst c
  exact ⟨r, hlen⟩

private theorem downShift_boundaryVertex_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    kmswVertexAllocated w ⟨boundaryVertex w h k⟩ := by
  by_cases hk0 : k = 0
  · subst k
    exact ⟨0, by simp [boundaryVertex_zero, kmswStage, kmswInit]⟩
  · by_cases hk1 : k = 1
    · subst k
      let n := boundaryHitTime w h 1
      have hmono := CutConverse.nextVertex_mono w (Nat.zero_le n)
      have hinit : (kmswStage w 0).nextVertex = 2 := by
        simp [kmswStage, kmswInit]
      have hbound : 1 < (kmswStage w n).nextVertex := by
        omega
      exact ⟨n, by simpa [boundaryVertex_one, n] using hbound⟩
    · let n := boundaryHitTime w h k
      have hact := act_lt_nextEdge w (Nat.le_refl n)
      have hends := kmswStage_endpoints_lt_nextVertex w n (act w n) hact
      have hwest : edgeWest w (act w n) < (kmswStage w n).nextVertex := by
        rw [← (edge_endpoints_eq w hact).1]
        exact hends.1
      refine ⟨n, ?_⟩
      simpa [boundaryVertex, hk0, hk1, activeInitial] using hwest

private theorem downShift_boundaryZero_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) :
    shiftLimitVertex w 1
      ⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ =
        (⟨boundaryVertex w h0 1⟩ : PresentVertex w) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hroot := (downShift_rootVertices_and_firstStageImage w h0 hw).1
  have hbound : boundaryVertex u h1 0 <
      (kmswStage (fun i => w (1 + i)) 0).nextVertex := by
    simpa [u, Nat.one_add] using
      (show boundaryVertex u h1 0 < (kmswStage u 0).nextVertex by
        simp [boundaryVertex_zero, kmswStage, kmswInit])
  rw [shiftLimitVertex_eq w 1 0 ⟨boundaryVertex u h1 0⟩ hbound]
  simpa [u, boundaryVertex_zero] using
    congrArg (fun n : ℕ => (⟨n⟩ : PresentVertex w)) hroot

private theorem downShift_path_avoids_root_of_source_ne_zero
    (w : ℕ → Fin 3) {a b : PresentVertex w}
    (p : Path a b) (ha : a.id ≠ 0) : 0 ∉ pathEdgeList p := by
  intro hroot
  have hsourceMem := downShift_path_source_mem w p hroot
  have hrootSource : (⟨edgeWest w 0⟩ : PresentVertex w) = ⟨0⟩ := by
    exact downShift_vertex_ext (downShift_globalRoot_edge w).2.1
  rw [hrootSource] at hsourceMem
  have hno : ∀ e, EdgePresent w e → edgeEast w e ≠ 0 := by
    intro e he
    exact uibot_zero_no_incoming w e he
  have hstart := downShift_path_source_eq_start w p hno hsourceMem
  exact ha (congrArg PresentVertex.id hstart.symm)

private def downShift_globalRootArrow (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    (⟨boundaryVertex w h 0⟩ : PresentVertex w) ⟶
      ⟨boundaryVertex w h 1⟩ := by
  refine ⟨0, (downShift_globalRoot_edge w).1, ?_, ?_⟩
  · rw [boundaryVertex_zero]
    exact (downShift_globalRoot_edge w).2.1
  · rw [boundaryVertex_one]
    exact (downShift_globalRoot_edge w).2.2.1

/-- A global path from the image of an allocated shifted vertex lifts to the
shifted limit with the same length if all its edges are late. The endpoint is
identified by injectivity on allocated vertices (`def-kmsw`, -/
theorem downShift_late_path_lift (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    {z : PresentVertex w}
    (q : Path (shiftLimitVertex w 1 a) z)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      1 ≤ actTime w e he)
    (hzb : z = shiftLimitVertex w 1 b) :
    ∃ r : Path a b, r.length = q.length := by
  obtain ⟨c, hc, r, hr, hlen, _⟩ :=
    shiftLimitVertex_late_path_lift w 1 a ha q hlate
  have hcb : c = b := by
    apply shiftLimitVertex_injective w 1 hc hb
    rw [hr, hzb]
  subst c
  exact ⟨r, hlen⟩

/-- For allocated shifted vertices whose global source is not the initial
root, global and shifted paths have the same attainable lengths. In
particular the `⊥` convention for unreachable pairs agrees. The boundedness
and reachability hypotheses are kept explicit for the LDP use -/
theorem downShift_ldpSup_image_eq (w : ℕ → Fin 3)
    (hbound : PresentPathLengthsBounded (w := w))
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hreach : Reachable a b)
    (hsource : (shiftLimitVertex w 1 a).id ≠ 0) :
    ldpSup (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) =
      ldpSup a b := by
  have hpaths : pathLengths a b =
      pathLengths (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := by
    apply Set.Subset.antisymm
    · rintro n ⟨p, rfl⟩
      exact ⟨(downShiftLimitMap w).mapPath p, downShiftLimitMap_length w p⟩
    · rintro n ⟨p, rfl⟩
      have hlate := (downShift_path_avoids_root_iff_late w p).1 ?_
      · obtain ⟨q, hlen⟩ := downShift_late_path_lift w ha hb p hlate rfl
        exact ⟨q, hlen⟩
      · intro hroot
        have hsourceMem := downShift_path_source_mem w p hroot
        have hrootSource : (⟨edgeWest w 0⟩ : PresentVertex w) = ⟨0⟩ := by
          exact downShift_vertex_ext (downShift_globalRoot_edge w).2.1
        rw [hrootSource] at hsourceMem
        have hno : ∀ e, EdgePresent w e → edgeEast w e ≠ 0 := by
          intro e he
          exact uibot_zero_no_incoming w e he
        have hstart := downShift_path_source_eq_start w p hno hsourceMem
        exact hsource (congrArg PresentVertex.id hstart.symm)
  have hglobal : Reachable (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := by
    obtain ⟨p⟩ := hreach
    exact ⟨(downShiftLimitMap w).mapPath p⟩
  have _ := hbound (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) hglobal
  unfold ldpSup
  rw [hpaths]

end DirectedDistances.Recursive
