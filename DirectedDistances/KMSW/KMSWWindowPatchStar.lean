module

public import DirectedDistances.KMSW.KMSWWindowPatchVertex
public import DirectedDistances.KMSW.KMSWWindowPatchInjective
public import DirectedDistances.KMSW.StageVertices

/-! not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem window_map_endpoint (w : ℕ → Fin 3) (s m : ℕ)
    (z : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m z) =
      kmswWindowPatchVertexMap w s m
        (stageEndpoint (kmswStage (fun i => w (s + i)) m) z) :=
  kmswWindowDartMap_vertex w s m z

/-- not the paper result. Every dart in the rotation orbit belongs to a window triangle. -/
@[expose] def KMSWWindowInteriorDart (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) : Prop :=
  ∀ k : ℕ,
    ((((kmswMap (fun i => w (s + i)) m).rot ^ k) x).1.val,
      (((kmswMap (fun i => w (s + i)) m).rot ^ k) x).2) ∈
        stageTriangleDartsVal (fun i => w (s + i)) m

/-- not the paper result. The entire global star is the image of the window star. -/
theorem kmswWindowDartMap_star (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : KMSWWindowInteriorDart w s m x)
    (y : StageDart (kmswStage w (s + m)).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) y =
        stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m x) ↔
      ∃ k : ℕ, y = kmswWindowDartMap w s m
        (((kmswMap (fun i => w (s + i)) m).rot ^ k) x) := by
  constructor
  · intro hy
    have hc := (stageRot_sameCycle_iff_endpoint_eq w (s + m)
      (kmswWindowDartMap w s m x) y).mpr hy.symm
    obtain ⟨k, hk⟩ := hc.exists_nat_pow_eq
    exact ⟨k, hk.symm.trans (kmswWindowDartMap_rot_pow w s m x hx k)⟩
  · rintro ⟨k, rfl⟩
    rw [← kmswWindowDartMap_rot_pow w s m x hx k]
    apply (stageRot_sameCycle_iff_endpoint_eq w (s + m) _ _).mp
    exact Equiv.Perm.SameCycle.rfl.pow_left

/-- not the paper result. Far endpoints correspond for every window dart. -/
theorem kmswWindowDartMap_neighbour (w : ℕ → Fin 3) (s m : ℕ)
    (z : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) (edgeFlip _ (kmswWindowDartMap w s m z)) =
      kmswWindowPatchVertexMap w s m
        (stageEndpoint (kmswStage (fun i => w (s + i)) m) (edgeFlip _ z)) := by
  rw [kmswWindowDartMap_edgeFlip]
  exact kmswWindowDartMap_vertex w s m (edgeFlip _ z)

/-- not the paper result. Interior degrees count geometric darts, retaining multiedges. -/
theorem kmswWindowDartMap_degree (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : KMSWWindowInteriorDart w s m x) :
    Fintype.card {y : StageDart (kmswStage w (s + m)).nextEdge //
      stageEndpoint (kmswStage w (s + m)) y =
        stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m x)} =
    Fintype.card {z : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge //
      stageEndpoint (kmswStage (fun i => w (s + i)) m) z =
        stageEndpoint (kmswStage (fun i => w (s + i)) m) x} := by
  classical
  let f : {z : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge //
      stageEndpoint (kmswStage (fun i => w (s + i)) m) z =
        stageEndpoint (kmswStage (fun i => w (s + i)) m) x} →
      {y : StageDart (kmswStage w (s + m)).nextEdge //
      stageEndpoint (kmswStage w (s + m)) y =
        stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m x)} :=
    fun z => ⟨kmswWindowDartMap w s m z.val, by
      rw [window_map_endpoint w s m z.val, window_map_endpoint w s m x, z.property]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact kmswWindowDartMap_injective w s m (congrArg Subtype.val hab)
    · intro y
      obtain ⟨k, hk⟩ := (kmswWindowDartMap_star w s m x hx y.val).mp y.property
      have hz : stageEndpoint (kmswStage (fun i => w (s + i)) m)
          (((kmswMap (fun i => w (s + i)) m).rot ^ k) x) =
          stageEndpoint (kmswStage (fun i => w (s + i)) m) x :=
        (stageRot_sameCycle_iff_endpoint_eq (fun i => w (s + i)) m _ _).mp
          Equiv.Perm.SameCycle.rfl.pow_left
      exact ⟨⟨_, hz⟩, Subtype.ext hk.symm⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- not the paper result. Each incident face is an entire triangle created in the window. -/
theorem kmswWindowDartMap_face (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : KMSWWindowInteriorDart w s m x) (k : ℕ) :
    let u := fun i => w (s + i)
    let z := ((kmswMap u m).rot ^ k) x
    ∃ (j : TriangleCreationTime u) (hj : j.val < m),
      (z.1.val, z.2) ∈ stageTriangleDartList u j ∧
      ((kmswWindowDartMap w s m z).1.val, (kmswWindowDartMap w s m z).2) ∈
        stageTriangleDartList w ⟨s + j.val, j.property⟩ ∧
      FaceSucc3Cycle (kmswMap w (s + m)).faceSucc
        (kmswWindowDartMap w s m (stageTriangleDart₁ u m j hj))
        (kmswWindowDartMap w s m (stageTriangleDart₂ u m j hj))
        (kmswWindowDartMap w s m (stageTriangleDart₃ u m j hj)) ∧
      ∀ d : StageDart (kmswStage u m).nextEdge,
        (d.1.val, d.2) ∈ stageTriangleDartList u j →
        (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m d) =
          kmswWindowDartMap w s m ((kmswMap u m).faceSucc d) := by
  let u := fun i => w (s + i)
  let z := ((kmswMap u m).rot ^ k) x
  obtain ⟨j, hj, hz⟩ := List.mem_flatMap.mp (hx k)
  have hjm := (mem_stageTriangleTimes u m j).mp hj
  refine ⟨j, hjm, hz, ?_, ?_, ?_⟩
  · have hr := kmswWindowPatchData_triangle_rotated w s m j.val hjm j.property
    exact hr.mem_iff.mp (List.mem_map.mpr ⟨(z.1.val, z.2), hz, rfl⟩)
  · have h₁ : ((stageTriangleDart₁ u m j hjm).1.val,
        (stageTriangleDart₁ u m j hjm).2) ∈ stageTriangleDartsVal u m := by
      apply List.mem_flatMap.mpr
      refine ⟨j, hj, ?_⟩
      simp only [stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
        List.mem_cons, List.not_mem_nil, or_false, true_or]
    have h₂ : ((stageTriangleDart₂ u m j hjm).1.val,
        (stageTriangleDart₂ u m j hjm).2) ∈ stageTriangleDartsVal u m := by
      apply List.mem_flatMap.mpr
      refine ⟨j, hj, ?_⟩
      simp only [stageTriangleDart₂, stageTriangleDartAt, stageTriangleDartList,
        List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
    have h₃ : ((stageTriangleDart₃ u m j hjm).1.val,
        (stageTriangleDart₃ u m j hjm).2) ∈ stageTriangleDartsVal u m := by
      apply List.mem_flatMap.mpr
      refine ⟨j, hj, ?_⟩
      simp only [stageTriangleDart₃, stageTriangleDartAt, stageTriangleDartList,
        List.mem_cons, List.not_mem_nil, or_false, or_true]
    obtain ⟨ha, hb, hc, hab, hbc, hca⟩ := stageTriangle_isFace u j m hjm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (kmswWindowDartMap_faceSucc w s m _ h₁).trans (congrArg _ ha)
    · exact (kmswWindowDartMap_faceSucc w s m _ h₂).trans (congrArg _ hb)
    · exact (kmswWindowDartMap_faceSucc w s m _ h₃).trans (congrArg _ hc)
    · exact fun h => hab (kmswWindowDartMap_injective w s m h)
    · exact fun h => hbc (kmswWindowDartMap_injective w s m h)
    · exact fun h => hca (kmswWindowDartMap_injective w s m h)
  · intro d hd
    exact kmswWindowDartMap_faceSucc w s m d (List.mem_flatMap.mpr ⟨j, hj, hd⟩)

/-- not the paper result. The vertex map is injective on finite sets of allocated vertices. -/
theorem kmswWindowPatchVertexMap_injOn_finset (w : ℕ → Fin 3) (s m : ℕ)
    (V : Finset ℕ)
    (hV : ∀ v ∈ V, v < (kmswStage (fun i => w (s + i)) m).nextVertex) :
    Set.InjOn (kmswWindowPatchVertexMap w s m) (↑V : Set ℕ) := by
  intro a ha b hb hab
  exact kmswWindowPatchVertexMap_injOn w s m (hV a ha) (hV b hb) hab

/-- not the paper result. Geometric adjacency within an interior finite vertex set transfers
in both directions, with a dart witnessing each edge. -/
theorem kmswWindowPatchVertexMap_adjacent_iff (w : ℕ → Fin 3) (s m : ℕ)
    (V : Finset ℕ)
    (hV : ∀ v ∈ V, v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hInterior : ∀ v ∈ V,
      ∀ x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        stageEndpoint (kmswStage (fun i => w (s + i)) m) x = v →
          KMSWWindowInteriorDart w s m x)
    (v v' : ℕ) (hv : v ∈ V) (hv' : v' ∈ V) :
    (∃ y : StageDart (kmswStage w (s + m)).nextEdge,
      stageEndpoint (kmswStage w (s + m)) y = kmswWindowPatchVertexMap w s m v ∧
      stageEndpoint (kmswStage w (s + m)) (edgeFlip _ y) =
        kmswWindowPatchVertexMap w s m v') ↔
    (∃ z : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) z = v ∧
      stageEndpoint (kmswStage (fun i => w (s + i)) m) (edgeFlip _ z) = v') := by
  constructor
  · rintro ⟨y, hy, hy'⟩
    obtain ⟨x, hx⟩ := stageEndpoint_exists (fun i => w (s + i)) m v (hV v hv)
    have hxi := hInterior v hv x hx
    have hyx : stageEndpoint (kmswStage w (s + m)) y =
        stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m x) := by
      rw [window_map_endpoint, hx]
      exact hy
    obtain ⟨k, hk⟩ := (kmswWindowDartMap_star w s m x hxi y).mp hyx
    let z := ((kmswMap (fun i => w (s + i)) m).rot ^ k) x
    have hz : stageEndpoint (kmswStage (fun i => w (s + i)) m) z = v := by
      apply Eq.trans _ hx
      exact (stageRot_sameCycle_iff_endpoint_eq (fun i => w (s + i)) m _ _).mp
        Equiv.Perm.SameCycle.rfl.pow_left
    refine ⟨z, hz, ?_⟩
    apply kmswWindowPatchVertexMap_injOn w s m
      (stageEndpoint_lt_nextVertex (fun i => w (s + i)) m (edgeFlip _ z)) (hV v' hv')
    rw [hk] at hy'
    exact (kmswWindowDartMap_neighbour w s m z).symm.trans hy'
  · rintro ⟨z, hz, hz'⟩
    refine ⟨kmswWindowDartMap w s m z, ?_, ?_⟩
    · rw [window_map_endpoint, hz]
    · rw [kmswWindowDartMap_neighbour, hz']

end DirectedDistances.KMSW
