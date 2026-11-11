module

public import DirectedDistances.KMSW.DirectedContainHat
public import DirectedDistances.KMSW.HatLimitIncidenceIso
public import DirectedDistances.KMSW.InftyCutP1Compose
import DirectedDistances.KMSW.LeftmostGeodesicSdpPlanar

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW
open Quiver

private theorem edge_self_bound (u : ℕ → Fin 3) (e : ℕ) :
    e < (kmswStage u e).nextEdge := by
  have := CutConverse.allocation_count u e
  omega

private noncomputable def shiftedPrefunctor (w : ℕ → Fin 3) (t : ℕ) :
    Prefunctor (PresentVertex (fun i => w (t + i))) (PresentVertex w) where
  obj := shiftLimitVertex w t
  map {a b} e := by
    let f : {e : ℕ // EdgePresent (fun i => w (t + i)) e} :=
      ⟨e.val, e.property.1⟩
    have hi := shiftLimitEdge_incidence w t f
    refine ⟨shiftLimitEdge w t f, shiftLimitEdge_present w t f, ?_, ?_⟩
    · exact hi.1.trans (congrArg (fun n => (shiftLimitVertex w t ⟨n⟩).id)
        e.property.2.1)
    · exact hi.2.trans (congrArg (fun n => (shiftLimitVertex w t ⟨n⟩).id)
        e.property.2.2)

private noncomputable def hatPrefunctor {u v : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u v T eφ vφ) :
    Prefunctor (PresentVertex u) (PresentVertex v) where
  obj a := ⟨vφ a.id⟩
  map {a b} e := by
    have hi := hatLimit_edge_incidence D e.property.1
    exact ⟨eφ e.val, hi.1,
      hi.2.1.trans (congrArg vφ e.property.2.1),
      hi.2.2.trans (congrArg vφ e.property.2.2)⟩

private theorem map_length {u v : ℕ → Fin 3}
    (F : Prefunctor (PresentVertex u) (PresentVertex v))
    {a b : PresentVertex u} (p : Path a b) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem map_edges {u v : ℕ → Fin 3}
    (F : Prefunctor (PresentVertex u) (PresentVertex v)) (f : ℕ → ℕ)
    (hf : ∀ {a b} (e : a ⟶ b), (F.map e).val = f e.val)
    {a b : PresentVertex u} (p : Path a b) :
    pathEdgeList (F.mapPath p) = (pathEdgeList p).map f := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, pathEdgeList, List.map_append,
      List.map_singleton, ih, hf]

private noncomputable def mapInfinite {u v : ℕ → Fin 3}
    (F : Prefunctor (PresentVertex u) (PresentVertex v)) (f : ℕ → ℕ)
    (hf : ∀ {a b} (e : a ⟶ b), (F.map e).val = f e.val)
    {a : PresentVertex u} (Q : InfinitePresentPath u a) :
    InfinitePresentPath v (F.obj a) where
  edge n := f (Q.edge n)
  initial n := ⟨F.obj (Q.initial n).1, F.mapPath (Q.initial n).2⟩
  prefix_length n := (map_length F _).trans (Q.prefix_length n)
  prefix_edges n := by
    rw [map_edges F f hf, Q.prefix_edges]
    simp only [List.map_ofFn, Function.comp_def]

private theorem hat_lift_aux {u v : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u v T eφ vφ)
    {a : PresentVertex u} {y : PresentVertex v}
    (p : Path ((hatPrefunctor D).obj a) y) :
    ∃ b : PresentVertex u, ∃ q : Path a b,
      (hatPrefunctor D).obj b = y ∧ q.length = p.length := by
  induction p with
  | nil => exact ⟨a, Path.nil, rfl, rfl⟩
  | @cons x y p e ih =>
    obtain ⟨b, q, hb, hlen⟩ := ih
    have hx : Reachable (⟨0⟩ : PresentVertex v) x := by
      rw [← hb]
      exact alloc_reachable D (kmswVertexAllocated_all u b)
    have hy : Reachable (⟨0⟩ : PresentVertex v) y := hx.trans e.toPath.reachable
    obtain ⟨j, hj, hje⟩ := edge_cover D e.property.1
      (by rw [e.property.2.1]; exact hx)
      (by rw [e.property.2.2]; exact hy)
    have hi := hatLimit_edge_incidence D hj
    have hw : vφ (edgeWest u j) = vφ b.id := by
      rw [← hi.2.1, hje, e.property.2.1]
      exact congrArg PresentVertex.id hb.symm
    have hs : edgeWest u j = b.id :=
      vertex_inj D (kmswVertexAllocated_all u ⟨edgeWest u j⟩)
        (kmswVertexAllocated_all u b) hw
    let c : PresentVertex u := ⟨edgeEast u j⟩
    let f : b ⟶ c := ⟨j, hj, hs, rfl⟩
    refine ⟨c, q.cons f, ?_, ?_⟩
    · apply congrArg PresentVertex.mk
      exact hi.2.2.symm.trans ((congrArg (edgeEast v) hje).trans e.property.2.2)
    · simp only [Path.length_cons, hlen]

private theorem hat_lift {u v : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u v T eφ vφ)
    {a b : PresentVertex u}
    (p : Path ((hatPrefunctor D).obj a) ((hatPrefunctor D).obj b)) :
    ∃ q : Path a b, q.length = p.length := by
  obtain ⟨c, q, hc, hlen⟩ := hat_lift_aux D p
  have hcb : c = b := by
    have hid := vertex_inj D (kmswVertexAllocated_all u c)
      (kmswVertexAllocated_all u b) (congrArg PresentVertex.id hc)
    exact congrArg PresentVertex.mk hid
  subst c
  exact ⟨q, hlen⟩

private theorem raw_root (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ)
    {u : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u (fun i => w (boundaryHitTime w h k + i)) T eφ vφ) :
    ((hatPrefunctor D).comp (shiftedPrefunctor w (boundaryHitTime w h k))).obj
        ⟨0⟩ = (⟨boundaryVertex w h k⟩ : PresentVertex w) := by
  change shiftLimitVertex w (boundaryHitTime w h k) ⟨vφ 0⟩ = _
  rw [D.root, shiftLimitVertex_eq w (boundaryHitTime w h k) 0 ⟨0⟩
    (by change 0 < 2; decide)]
  exact congrArg PresentVertex.mk (kmswShift_root_vertex_map w h k)

private theorem raw_lift (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ)
    {u : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u (fun i => w (boundaryHitTime w h k + i)) T eφ vφ)
    {a b : PresentVertex u}
    (ha : Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
      (shiftLimitVertex w (boundaryHitTime w h k) ⟨vφ a.id⟩))
    (p : Path (shiftLimitVertex w (boundaryHitTime w h k) ⟨vφ a.id⟩)
      (shiftLimitVertex w (boundaryHitTime w h k) ⟨vφ b.id⟩)) :
    ∃ q : Path a b, q.length = p.length := by
  obtain ⟨s⟩ := ha
  have hlate : ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      boundaryHitTime w h k ≤ actTime w e he := by
    intro e he hep
    have hmem : e ∈ pathEdgeList (s.comp p) := by
      rw [pathEdgeList_comp]
      exact List.mem_append_right _ he
    exact (boundary_path_actTime_ge w h k (s.comp p) e hmem).2
  obtain ⟨c, hc, r, hr, hlen, _⟩ := shiftLimitVertex_late_path_lift w
    (boundaryHitTime w h k) ⟨vφ a.id⟩
    (kmswVertexAllocated_all _ _) p hlate
  have hcb : c = (⟨vφ b.id⟩ : PresentVertex
      (fun i => w (boundaryHitTime w h k + i))) :=
    shiftLimitVertex_injective w (boundaryHitTime w h k) hc
      (kmswVertexAllocated_all _ _) hr
  subst c
  obtain ⟨q, hq⟩ := hat_lift D r
  exact ⟨q, hq.trans hlen⟩

private def prefixOptimal {u : ℕ → Fin 3} (longest : Bool)
    {a b : PresentVertex u} (p : Path a b) : Prop :=
  if longest then IsLongest p else IsShortest p

private theorem segments_of_prefix {u : ℕ → Fin 3} {a : PresentVertex u}
    (longest : Bool) (P : InfinitePresentPath u a)
    (hP : ∀ N, prefixOptimal longest (P.initial N).2) :
    ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧
      prefixOptimal longest q := by
  intro a b ha hab
  obtain ⟨z, p, q, hpq, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, q, ?_, ?_, ?_⟩
  · have hlen := P.prefix_length b
    rw [hpq, Path.length_comp, hp] at hlen
    omega
  · rw [← P.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := hP b
    rw [hpq] at hopt
    cases longest
    · exact IsShortest.of_comp_right hopt
    · exact IsLongest.of_comp_right hopt





theorem rawHat_infinitePath_transport (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ)
    (hτ : HasFlowLineHits (fun i => w (boundaryHitTime w h k + i)))
    {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput
      (hatCodes (fun i => w (boundaryHitTime w h k + i)) hτ)
      (fun i => w (boundaryHitTime w h k + i)) T eφ vφ)
    (Q : InfinitePresentPath
      (hatCodes (fun i => w (boundaryHitTime w h k + i)) hτ) ⟨0⟩) :
    ∃ P : InfinitePresentPath w ⟨boundaryVertex w h k⟩,
      P.edge = (fun n => kmswShiftEdgeMapAll w (boundaryHitTime w h k)
        (eφ (Q.edge n)) (eφ (Q.edge n))) ∧
      (∀ N, (P.initial N).1 =
        shiftLimitVertex w (boundaryHitTime w h k) ⟨vφ (Q.initial N).1.id⟩) ∧
      (∀ N, pathEdgeList (P.initial N).2 =
        (pathEdgeList (Q.initial N).2).map
          (fun e => kmswShiftEdgeMapAll w (boundaryHitTime w h k) (eφ e) (eφ e))) ∧
      (Q.HasLongestSegments → P.HasLongestSegments) ∧
      (Q.HasShortestSegments → P.HasShortestSegments) := by
  let t := boundaryHitTime w h k
  let F := (hatPrefunctor D).comp (shiftedPrefunctor w t)
  let f : ℕ → ℕ := fun e => kmswShiftEdgeMapAll w t (eφ e) (eφ e)
  have hf : ∀ {a b} (e : a ⟶ b), (F.map e).val = f e.val := by
    intro a b e
    exact shiftLimitEdge_eq w t (eφ e.val)
      ⟨eφ e.val, (hatLimit_edge_incidence D e.property.1).1⟩
      (edge_self_bound _ _)
  have hroot : F.obj ⟨0⟩ = (⟨boundaryVertex w h k⟩ : PresentVertex w) :=
    raw_root w h k D
  have hr : Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w) (F.obj ⟨0⟩) := by
    rw [hroot]
  have hpull {b : PresentVertex
      (hatCodes (fun i => w (boundaryHitTime w h k + i)) hτ)}
      (p : Path (F.obj ⟨0⟩) (F.obj b)) :
      ∃ q : Path (⟨0⟩ : PresentVertex
        (hatCodes (fun i => w (boundaryHitTime w h k + i)) hτ)) b,
        q.length = p.length := raw_lift w h k D hr p
  rw [← hroot]
  let P := mapInfinite F f hf Q
  refine ⟨P, rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro N
    exact map_edges F f hf (Q.initial N).2
  · intro hQ
    apply segments_of_prefix true P
    intro N
    change IsLongest (F.mapPath (Q.initial N).2)
    intro p
    obtain ⟨q, hq⟩ := hpull p
    calc
      p.length = q.length := hq.symm
      _ ≤ (Q.initial N).2.length := Q.initial_isLongest _ hQ N q
      _ = (F.mapPath (Q.initial N).2).length := (map_length F _).symm
  · intro hQ
    apply segments_of_prefix false P
    intro N
    change IsShortest (F.mapPath (Q.initial N).2)
    intro p
    obtain ⟨q, hq⟩ := hpull p
    calc
      (F.mapPath (Q.initial N).2).length = (Q.initial N).2.length := map_length F _
      _ ≤ q.length := Q.initial_isShortest _ hQ N q
      _ = p.length := hq

end DirectedDistances.KMSW
