module

public import DirectedDistances.KMSW.KMSWWindowPatchTriangles
public import DirectedDistances.KMSW.StageOuterCycle

 

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

 
@[expose] def kmswWindowDartMap (w : ℕ → Fin 3) (s m : ℕ) :
    StageDart (kmswStage (fun i => w (s + i)) m).nextEdge →
      StageDart (kmswStage w (s + m)).nextEdge :=
  fun x => (⟨(kmswWindowPatchData w s m).φ x.1.val,
    (kmswWindowPatchData_rel w s m).edge_bound x.1.val x.1.isLt⟩, x.2)

 
theorem kmswWindowDartMap_injective (w : ℕ → Fin 3) (s m : ℕ) :
    Function.Injective (kmswWindowDartMap w s m) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have he : (kmswWindowPatchData w s m).φ e.val =
      (kmswWindowPatchData w s m).φ f.val := congrArg (fun x => x.1.val) h
  have hb : b = c := congrArg Prod.snd h
  have hef : e = f := Fin.ext
    ((kmswWindowPatchData_rel w s m).edge_injective e.val e.isLt f.val f.isLt he)
  cases hef
  cases hb
  rfl

 
theorem kmswWindowDartMap_edgeFlip (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    edgeFlip _ (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m (edgeFlip _ x) := rfl

private theorem dartVal_injective (k : ℕ) :
    Function.Injective (fun x : StageDart k => (x.1.val, x.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl

private theorem rotated_of_map {α β : Type*} (f : α → β)
    (hf : Function.Injective f) {l l' : List α}
    (h : List.IsRotated (l.map f) (l'.map f)) : List.IsRotated l l' := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply List.map_injective_iff.mpr hf
  simpa only [List.map_rotate] using hn

private theorem cycle_map {α β : Type*} {f : Equiv.Perm α} {g : Equiv.Perm β}
    (φ : α → β) {a b c : α} {a' b' c' : β}
    (hs : FaceSucc3Cycle f a b c) (ht : FaceSucc3Cycle g a' b' c')
    (hr : List.IsRotated [φ a, φ b, φ c] [a', b', c']) :
    ∀ x ∈ [a, b, c], g (φ x) = φ (f x) := by
  obtain ⟨n, hn, he⟩ := List.isRotated_iff_mod.mp hr
  have hn' : n ≤ 3 := by simpa only [List.length_cons, List.length_nil] using hn
  interval_cases n <;>
    simp only [List.rotate] at he <;>
    simp_all [FaceSucc3Cycle]

private abbrev triangleList (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) : List (StageDart (kmswStage w n).nextEdge) :=
  [stageTriangleDart₁ w n j hj, stageTriangleDart₂ w n j hj,
    stageTriangleDart₃ w n j hj]

private theorem triangleList_val (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    (triangleList w n j hj).map (fun x => (x.1.val, x.2)) =
      stageTriangleDartList w j := by
  simp only [triangleList, List.map_cons, List.map_nil, stageTriangleDart₁,
    stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt, stageTriangleDartList]

private theorem mem_triangleList_iff (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (x : StageDart (kmswStage w n).nextEdge) :
    x ∈ triangleList w n j hj ↔ (x.1.val, x.2) ∈ stageTriangleDartList w j := by
  rw [← triangleList_val w n j hj]
  constructor
  · intro hx
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
    exact (dartVal_injective _ he) ▸ hy

private theorem triangle_faceSucc_map (w : ℕ → Fin 3) (s m : ℕ)
    (j : TriangleCreationTime (fun i => w (s + i))) (hj : j.val < m)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartList (fun i => w (s + i)) j) :
    (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).faceSucc x) := by
  let u := fun i => w (s + i)
  let j' : TriangleCreationTime w := ⟨s + j.val, j.property⟩
  have hj' : j'.val < s + m := Nat.add_lt_add_left hj s
  let l := triangleList u m j hj
  let l' := triangleList w (s + m) j' hj'
  let v := fun x : StageDart (kmswStage u m).nextEdge => (x.1.val, x.2)
  let v' := fun x : StageDart (kmswStage w (s + m)).nextEdge => (x.1.val, x.2)
  let φ := kmswWindowDartMap w s m
  let g := fun p : ℕ × Bool => ((kmswWindowPatchData w s m).φ p.1, p.2)
  have hl : l.map v = stageTriangleDartList u j := triangleList_val u m j hj
  have hl' : l'.map v' = stageTriangleDartList w j' :=
    triangleList_val w (s + m) j' hj'
  have hsource : (l.map φ).map v' = (stageTriangleDartList u j).map g := by
    rw [← hl, List.map_map, List.map_map]
    rfl
  have hrval : List.IsRotated ((l.map φ).map v') (l'.map v') := by
    rw [hsource, hl']
    exact kmswWindowPatchData_triangle_rotated w s m j.val hj j.property
  have hr : List.IsRotated (l.map φ) l' :=
    rotated_of_map v' (dartVal_injective _) hrval
  exact cycle_map φ (stageTriangle_isFace u j m hj)
    (stageTriangle_isFace w j' (s + m) hj') hr x
    ((mem_triangleList_iff u m j hj x).mpr hx)

 
theorem kmswWindowDartMap_faceSucc (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartsVal (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).faceSucc x) := by
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
  exact triangle_faceSucc_map w s m j
    ((mem_stageTriangleTimes (fun i => w (s + i)) m j).mp hj) x hxj

private theorem cycle_symm_mem {α : Type*} {f : Equiv.Perm α} {a b c : α}
    (hs : FaceSucc3Cycle f a b c) (x : α) (hx : x ∈ [a, b, c]) :
    f.symm x ∈ [a, b, c] := by
  obtain ⟨ha, hb, hc, _⟩ := hs
  have hca : f.symm a = c := by rw [← hc, Equiv.symm_apply_apply]
  have hab : f.symm b = a := by rw [← ha, Equiv.symm_apply_apply]
  have hbc : f.symm c = b := by rw [← hb, Equiv.symm_apply_apply]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl | rfl
  · exact Or.inr (Or.inr hca)
  · exact Or.inl hab
  · exact Or.inr (Or.inl hbc)

private theorem triangleDartsVal_symm_mem (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartsVal w n) :
    (((kmswMap w n).faceSucc.symm x).1.val, ((kmswMap w n).faceSucc.symm x).2) ∈
      stageTriangleDartsVal w n := by
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
  have hjn := (mem_stageTriangleTimes w n j).mp hj
  have hmem := cycle_symm_mem (stageTriangle_isFace w j n hjn) x
    ((mem_triangleList_iff w n j hjn x).mpr hxj)
  exact List.mem_flatMap.mpr ⟨j, hj,
    (mem_triangleList_iff w n j hjn _).mp hmem⟩

 
theorem kmswWindowDartMap_faceSucc_symm (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartsVal (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).faceSucc.symm (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).faceSucc.symm x) := by
  apply (kmswMap w (s + m)).faceSucc.injective
  rw [Equiv.apply_symm_apply, kmswWindowDartMap_faceSucc w s m _
    (triangleDartsVal_symm_mem (fun i => w (s + i)) m x hx), Equiv.apply_symm_apply]

private theorem rot_eq_edgeInv_mul_faceSucc_inv {D : Type*} [Fintype D]
    [DecidableEq D] (M : CombinatorialMap D) :
    M.rot = M.edgeInv * M.faceSucc⁻¹ := by
  ext d
  simp [CombinatorialMap.faceSucc]

 
theorem kmswWindowDartMap_rot (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartsVal (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).rot (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).rot x) := by
  rw [rot_eq_edgeInv_mul_faceSucc_inv (kmswMap w (s + m)),
    rot_eq_edgeInv_mul_faceSucc_inv (kmswMap (fun i => w (s + i)) m)]
  change edgeFlip _ ((kmswMap w (s + m)).faceSucc.symm (kmswWindowDartMap w s m x)) =
    kmswWindowDartMap w s m
      (edgeFlip _ ((kmswMap (fun i => w (s + i)) m).faceSucc.symm x))
  rw [kmswWindowDartMap_faceSucc_symm w s m x hx, kmswWindowDartMap_edgeFlip]

 
theorem kmswWindowDartMap_rot_symm (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : ((edgeFlip _ x).1.val, (edgeFlip _ x).2) ∈
      stageTriangleDartsVal (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).rot.symm x) := by
  have hh := kmswWindowDartMap_faceSucc w s m (edgeFlip _ x) hx
  rw [← kmswWindowDartMap_edgeFlip w s m x] at hh
  simpa [CombinatorialMap.faceSucc, kmswMap, edgeFlip] using hh

 
theorem kmswWindowDartMap_rot_pow (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hx : ∀ k : ℕ,
      ((((kmswMap (fun i => w (s + i)) m).rot ^ k) x).1.val,
        (((kmswMap (fun i => w (s + i)) m).rot ^ k) x).2) ∈
          stageTriangleDartsVal (fun i => w (s + i)) m) (k : ℕ) :
    ((kmswMap w (s + m)).rot ^ k) (kmswWindowDartMap w s m x) =
      kmswWindowDartMap w s m (((kmswMap (fun i => w (s + i)) m).rot ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [ih, kmswWindowDartMap_rot w s m _ (hx k)]

end DirectedDistances.KMSW
