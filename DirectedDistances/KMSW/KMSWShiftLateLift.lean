module

public import DirectedDistances.KMSW.KMSWShiftAllTimes
public import DirectedDistances.KMSW.ActiveTimeMonotone









public section
namespace DirectedDistances.KMSW
open Quiver

/-- Eventual allocation of a KMSW vertex ID (`def-kmsw`,
unrestricted `PresentVertex` carrier. -/
@[expose] def kmswVertexAllocated (u : ℕ → Fin 3) (a : PresentVertex u) : Prop :=
  ∃ m, a.id < (kmswStage u m).nextVertex

private theorem shift_vertex_maps_agree (w : ℕ → Fin 3) (t m n v : ℕ)
    (hm : v < (kmswStage (fun i => w (t + i)) m).nextVertex)
    (hn : v < (kmswStage (fun i => w (t + i)) n).nextVertex) :
    kmswShiftVertexMapAll w t m v = kmswShiftVertexMapAll w t n v := by
  exact (kmswShiftVertexMapAll_eq_of_le w t m (max m n) v
    (Nat.le_max_left _ _) hm).symm.trans
      (kmswShiftVertexMapAll_eq_of_le w t n (max m n) v
        (Nat.le_max_right _ _) hn)

/-- The limit vertex embedding of `M_{t,∞}` into `M_{0,∞}`. On an allocated
ID it uses any allocating stage, and on unused IDs it is zero (`def-kmsw`, -/
@[expose] noncomputable def shiftLimitVertex (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex (fun i => w (t + i))) : PresentVertex w := by
  classical
  exact if h : kmswVertexAllocated (fun i => w (t + i)) a then
    ⟨kmswShiftVertexMapAll w t (Classical.choose h) a.id⟩ else ⟨0⟩

/-- The limit vertex map agrees with every allocating stage, independently -/
theorem shiftLimitVertex_eq (w : ℕ → Fin 3) (t m : ℕ)
    (a : PresentVertex (fun i => w (t + i)))
    (ha : a.id < (kmswStage (fun i => w (t + i)) m).nextVertex) :
    shiftLimitVertex w t a = ⟨kmswShiftVertexMapAll w t m a.id⟩ := by
  classical
  have h : kmswVertexAllocated (fun i => w (t + i)) a := ⟨m, ha⟩
  simp only [shiftLimitVertex, dite_eq_left h]
  exact congrArg PresentVertex.mk
    (shift_vertex_maps_agree w t (Classical.choose h) m a.id
      (Classical.choose_spec h) ha)

/-- The junk case of the limit vertex map (`def-kmsw`, -/
theorem shiftLimitVertex_of_not_allocated (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex (fun i => w (t + i)))
    (ha : ¬kmswVertexAllocated (fun i => w (t + i)) a) :
    shiftLimitVertex w t a = ⟨0⟩ := by
  classical
  simp only [shiftLimitVertex, dite_eq_right ha]

/-- Injectivity of the limit embedding on allocated shifted vertices -/
theorem shiftLimitVertex_injective (w : ℕ → Fin 3) (t : ℕ)
    {a b : PresentVertex (fun i => w (t + i))}
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    (hb : kmswVertexAllocated (fun i => w (t + i)) b)
    (hab : shiftLimitVertex w t a = shiftLimitVertex w t b) : a = b := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  have ham : a.id < (kmswStage (fun i => w (t + i)) (max m n)).nextVertex :=
    hm.trans_le (CutConverse.nextVertex_mono _ (Nat.le_max_left m n))
  have hbm : b.id < (kmswStage (fun i => w (t + i)) (max m n)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono _ (Nat.le_max_right m n))
  rw [shiftLimitVertex_eq w t (max m n) a ham,
    shiftLimitVertex_eq w t (max m n) b hbm] at hab
  have hid := (kmswShift_sim2_all w t (max m n)).sim.vertex_injective
    a.id b.id ham hbm (congrArg PresentVertex.id hab)
  cases a
  cases b
  exact congrArg PresentVertex.mk hid

private theorem shift_active_present (u : ℕ → Fin 3) (m : ℕ) :
    EdgePresent u (act u m) := by
  refine ⟨m, act_lt_nextEdge u le_rfl, ?_⟩
  apply (kmswStage_status u m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The limit edge embedding, indexed by the unique activation time. It
retains each edge identity, including parallel edges (`def-kmsw`, -/
@[expose] noncomputable def shiftLimitEdge (w : ℕ → Fin 3) (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e}) : ℕ :=
  act w (t + actTime (fun i => w (t + i)) e.val e.property)

/-- Images of present shifted edges are present (`def-kmsw`, -/
theorem shiftLimitEdge_present (w : ℕ → Fin 3) (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e}) :
    EdgePresent w (shiftLimitEdge w t e) :=
  shift_active_present w _

/-- The limit edge map equals every finite-stage map after allocation,
including stages before activation (`def-kmsw`, -/
theorem shiftLimitEdge_eq (w : ℕ → Fin 3) (t m : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e})
    (he : e.val < (kmswStage (fun i => w (t + i)) m).nextEdge) :
    shiftLimitEdge w t e = kmswShiftEdgeMapAll w t m e.val := by
  let n := actTime (fun i => w (t + i)) e.val e.property
  have hspec : e.val = act (fun i => w (t + i)) n := actTime_spec _ _ _
  have hn : e.val < (kmswStage (fun i => w (t + i)) n).nextEdge := by
    rw [hspec]
    exact act_lt_nextEdge _ le_rfl
  have hactive : kmswShiftEdgeMapAll w t n e.val = act w (t + n) := by
    rw [hspec]
    exact (kmswShift_sim2_all w t n).sim.active
  change act w (t + n) = _
  exact hactive.symm.trans
    ((kmswShiftEdgeMapAll_eq_of_le w t n (max n m) e.val
      (Nat.le_max_left _ _) hn).symm.trans
        (kmswShiftEdgeMapAll_eq_of_le w t m (max n m) e.val
          (Nat.le_max_right _ _) he))

/-- Activation times translate by the cutoff under the embedding -/
theorem shiftLimitEdge_actTime (w : ℕ → Fin 3) (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e})
    (he : EdgePresent w (shiftLimitEdge w t e)) :
    actTime w (shiftLimitEdge w t e) he =
      t + actTime (fun i => w (t + i)) e.val e.property :=
  (actTime_eq_iff w _ he _).2 rfl

/-- The present-edge image is exactly the edges activated at or after the
cutoff. This is the edge-range ingredient for the second lift in
`lem-directed-contain` (87–120) and `def-kmsw` -/
theorem shiftLimitEdge_image_iff (w : ℕ → Fin 3) (t e : ℕ)
    (he : EdgePresent w e) :
    (∃ f : {f : ℕ // EdgePresent (fun i => w (t + i)) f},
      shiftLimitEdge w t f = e) ↔ t ≤ actTime w e he := by
  constructor
  · rintro ⟨f, rfl⟩
    rw [shiftLimitEdge_actTime w t f he]
    exact Nat.le_add_right _ _
  · intro ht
    let n := actTime w e he - t
    let f : {f : ℕ // EdgePresent (fun i => w (t + i)) f} :=
      ⟨act (fun i => w (t + i)) n, shift_active_present _ n⟩
    have hf : actTime (fun i => w (t + i)) f.val f.property = n :=
      (actTime_eq_iff _ _ _ _).2 rfl
    refine ⟨f, ?_⟩
    change act w (t + actTime (fun i => w (t + i)) f.val f.property) = e
    rw [hf, Nat.add_sub_of_le ht]
    exact (actTime_spec w e he).symm

/-- Edge injectivity of the limit embedding (`def-kmsw`, -/
theorem shiftLimitEdge_injective (w : ℕ → Fin 3) (t : ℕ) :
    Function.Injective (shiftLimitEdge w t) := by
  intro e f hef
  have htimes := CutConverse.act_injective w hef
  change t + actTime _ e.val e.property = t + actTime _ f.val f.property at htimes
  have htime : actTime _ e.val e.property = actTime _ f.val f.property := by omega
  apply Subtype.ext
  rw [actTime_spec _ e.val e.property, actTime_spec _ f.val f.property, htime]

private theorem shift_endpoint_allocated (u : ℕ → Fin 3) {e : ℕ}
    (he : EdgePresent u e) :
    kmswVertexAllocated u ⟨edgeWest u e⟩ ∧
      kmswVertexAllocated u ⟨edgeEast u e⟩ := by
  obtain ⟨m, hm, _⟩ := he
  have hb := kmswStage_endpoints_lt_nextVertex u m e hm
  rw [(edge_endpoints_eq u hm).1, (edge_endpoints_eq u hm).2] at hb
  exact ⟨⟨m, hb.1⟩, ⟨m, hb.2⟩⟩

/-- Both incidence identities for the limit embedding, with stable endpoint -/
theorem shiftLimitEdge_incidence (w : ℕ → Fin 3) (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e}) :
    edgeWest w (shiftLimitEdge w t e) =
        (shiftLimitVertex w t ⟨edgeWest (fun i => w (t + i)) e.val⟩).id ∧
      edgeEast w (shiftLimitEdge w t e) =
        (shiftLimitVertex w t ⟨edgeEast (fun i => w (t + i)) e.val⟩).id := by
  obtain ⟨m, hm, hp⟩ := e.property
  have hb := kmswStage_endpoints_lt_nextVertex (fun i => w (t + i)) m e.val hm
  have hends := edge_endpoints_eq (fun i => w (t + i)) hm
  rw [hends.1, hends.2] at hb
  rw [shiftLimitVertex_eq w t m ⟨edgeWest (fun i => w (t + i)) e.val⟩ hb.1,
    shiftLimitVertex_eq w t m ⟨edgeEast (fun i => w (t + i)) e.val⟩ hb.2,
    shiftLimitEdge_eq w t m e hm]
  exact (kmswShift_present_edge_maps w t m e.val hm hp).2

/-- The shifted root vertex maps to the initial endpoint of the global -/
theorem shiftLimitVertex_root (w : ℕ → Fin 3) (t : ℕ) :
    shiftLimitVertex w t ⟨0⟩ = ⟨(kmswStage w t).west (act w t)⟩ := by
  rw [shiftLimitVertex_eq w t 0 ⟨0⟩ (by change 0 < 2; omega)]
  rfl

/-- Any present shifted root edge maps to the cutoff active edge -/
theorem shiftLimitEdge_root (w : ℕ → Fin 3) (t : ℕ)
    (hroot : EdgePresent (fun i => w (t + i)) 0) :
    shiftLimitEdge w t ⟨0, hroot⟩ = act w t := by
  rw [shiftLimitEdge_eq w t 0 ⟨0, hroot⟩ (by change 0 < 1; omega)]
  rfl

private theorem shift_late_path_lift_aux (w : ℕ → Fin 3) (t : ℕ)
    {c v : PresentVertex w} (q : Path c v) :
    ∀ (a : PresentVertex (fun i => w (t + i))),
      kmswVertexAllocated (fun i => w (t + i)) a →
      shiftLimitVertex w t a = c →
      (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, t ≤ actTime w e he) →
      ∃ b : PresentVertex (fun i => w (t + i)),
        kmswVertexAllocated (fun i => w (t + i)) b ∧
        ∃ r : Path a b, shiftLimitVertex w t b = v ∧
          r.length = q.length ∧
          ∀ y ∈ r.vertices, shiftLimitVertex w t y ∈ q.vertices := by
  induction q with
  | nil =>
    intro a ha hca _
    refine ⟨a, ha, Path.nil, hca, rfl, ?_⟩
    intro y hy
    have hya : y = a := List.mem_singleton.mp hy
    rw [hya, hca]
    exact List.mem_singleton.mpr rfl
  | @cons mid final p e ih =>
    intro a ha hca hlate
    have hlatep : ∀ f ∈ pathEdgeList p, ∀ hf : EdgePresent w f,
        t ≤ actTime w f hf := by
      intro f hf hfp
      exact hlate f (List.mem_append_left _ hf) hfp
    obtain ⟨b, hb, r, hr, hlen, hvertices⟩ := ih a ha hca hlatep
    have heLate : t ≤ actTime w e.val e.property.1 :=
      hlate e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl)) e.property.1
    obtain ⟨f, hf⟩ := (shiftLimitEdge_image_iff w t e.val e.property.1).2 heLate
    let aw : PresentVertex (fun i => w (t + i)) :=
      ⟨edgeWest (fun i => w (t + i)) f.val⟩
    let ae : PresentVertex (fun i => w (t + i)) :=
      ⟨edgeEast (fun i => w (t + i)) f.val⟩
    have halloc := shift_endpoint_allocated (fun i => w (t + i)) f.property
    have hinc := shiftLimitEdge_incidence w t f
    rw [hf] at hinc
    have hw : shiftLimitVertex w t aw = mid :=
      congrArg PresentVertex.mk (hinc.1.symm.trans e.property.2.1)
    have ht : shiftLimitVertex w t ae = final :=
      congrArg PresentVertex.mk (hinc.2.symm.trans e.property.2.2)
    have haw : aw = b :=
      shiftLimitVertex_injective w t halloc.1 hb (hw.trans hr.symm)
    let ef : b ⟶ ae :=
      ⟨f.val, f.property, congrArg PresentVertex.id haw, rfl⟩
    refine ⟨ae, halloc.2, r.cons ef, ht, ?_, ?_⟩
    · simp only [Path.length_cons, hlen]
    · intro y hy
      rcases (Path.mem_vertices_cons r ef).1 hy with hy | hy
      · exact (Path.mem_vertices_cons p e).2 (Or.inl (hvertices y hy))
      · rw [hy, ht]
        exact (Path.mem_vertices_cons p e).2 (Or.inr rfl)

/-- Lift a global path whose edges are all activated at or after `t`, from
any allocated image vertex. The lift has the same length and maps every
visited vertex into the original path. This is an embedding fact for
`M_{t,∞} ⊂ M_{0,∞}` from `def-kmsw`
`lem-infty-cut` (127–143); it is not `lem-infty-cut`. -/
theorem shiftLimitVertex_late_path_lift (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex (fun i => w (t + i)))
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    {v : PresentVertex w} (q : Path (shiftLimitVertex w t a) v)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      t ≤ actTime w e he) :
    ∃ b : PresentVertex (fun i => w (t + i)),
      kmswVertexAllocated (fun i => w (t + i)) b ∧
      ∃ r : Path a b, shiftLimitVertex w t b = v ∧
        r.length = q.length ∧
        ∀ y ∈ r.vertices, shiftLimitVertex w t y ∈ q.vertices :=
  shift_late_path_lift_aux w t q a ha rfl hlate

/-- Every vertex of a late path from an allocated image vertex has an
allocated preimage. This is another embedding fact for the second lift, -/
theorem shiftLimitVertex_late_path_allocation (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex (fun i => w (t + i)))
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    {v : PresentVertex w} (q : Path (shiftLimitVertex w t a) v)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
      t ≤ actTime w e he)
    {y : PresentVertex w} (hy : y ∈ q.vertices) :
    ∃ b : PresentVertex (fun i => w (t + i)),
      kmswVertexAllocated (fun i => w (t + i)) b ∧ shiftLimitVertex w t b = y := by
  obtain ⟨p, s, hq⟩ := q.exists_eq_comp_of_mem_vertices hy
  have hp : ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      t ≤ actTime w e he := by
    intro e he hep
    apply hlate e _ hep
    rw [hq, pathEdgeList_comp]
    exact List.mem_append_left _ he
  obtain ⟨b, hb, r, hr, _, _⟩ := shiftLimitVertex_late_path_lift w t a ha p hp
  exact ⟨b, hb, hr⟩

end DirectedDistances.KMSW
