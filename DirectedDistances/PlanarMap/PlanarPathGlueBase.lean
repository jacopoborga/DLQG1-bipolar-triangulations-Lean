module

public import DirectedDistances.PlanarMap.PlanarPathGlue
public import DirectedDistances.PlanarMap.CombinatorialMapEulerBound

import DirectedDistances.PlanarMap.BipolarCanonicalTrees
import DirectedDistances.PlanarMap.FiniteBipolarSwitchCount

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.PlanarMap

attribute [local instance] Classical.propDecidable

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

private theorem glue_rot_faceSucc {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d : D) : M.rot (M.faceSucc d) = M.edgeInv d := by
  change M.rot (M.rot.symm (M.edgeInv d)) = M.edgeInv d
  exact M.rot.apply_symm_apply _



theorem glue_rot_left_inner_corner (d : DL) (hd : ¬ BL.map.IsOuter d) :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.faceSucc d))) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d)) := by
  rw [← glue_faceSucc_left_inner BL BR d hd, glue_rot_faceSucc,
    glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl



theorem glue_rot_right_inner_corner (d : DR) (hd : ¬ BR.map.IsOuter d) :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.faceSucc d))) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)) := by
  rw [← glue_faceSucc_right_inner BL BR d hd, glue_rot_faceSucc,
    glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl



theorem glue_rot_left_of_inner (d : DL) (hd : ¬ BL.map.IsOuter d) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inl d)) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)) := by
  have hp : ¬ BL.map.IsOuter (BL.map.toCombinatorialMap.faceSucc.symm d) := by
    intro h
    exact hd (Equiv.Perm.sameCycle_symm_apply_right.mp h)
  have h := glue_rot_left_inner_corner BL BR
    (BL.map.toCombinatorialMap.faceSucc.symm d) hp
  rw [Equiv.apply_symm_apply] at h
  have he : BL.map.toCombinatorialMap.edgeInv
      (BL.map.toCombinatorialMap.faceSucc.symm d) = BL.map.toCombinatorialMap.rot d := by
    have he' := glue_rot_faceSucc BL.map.toCombinatorialMap
      (BL.map.toCombinatorialMap.faceSucc.symm d)
    rw [Equiv.apply_symm_apply] at he'
    exact he'.symm
  rw [he] at h
  exact h



theorem glue_rot_right_of_inner (d : DR) (hd : ¬ BR.map.IsOuter d) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)) := by
  have hp : ¬ BR.map.IsOuter (BR.map.toCombinatorialMap.faceSucc.symm d) := by
    intro h
    exact hd (Equiv.Perm.sameCycle_symm_apply_right.mp h)
  have h := glue_rot_right_inner_corner BL BR
    (BR.map.toCombinatorialMap.faceSucc.symm d) hp
  rw [Equiv.apply_symm_apply] at h
  have he : BR.map.toCombinatorialMap.edgeInv
      (BR.map.toCombinatorialMap.faceSucc.symm d) = BR.map.toCombinatorialMap.rot d := by
    have he' := glue_rot_faceSucc BR.map.toCombinatorialMap
      (BR.map.toCombinatorialMap.faceSucc.symm d)
    rw [Equiv.apply_symm_apply] at he'
    exact he'.symm
  rw [he] at h
  exact h

private theorem glue_stable_orbit_pow {A B : Type*} [Finite A]
    (f : Equiv.Perm A) (g : Equiv.Perm B) (p : A → B) (a : A)
    (h : ∀ x, f.SameCycle a x → g (p x) = p (f x)) (n : ℕ) :
    (g ^ n) (p a) = p ((f ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, h _
      ((Equiv.Perm.SameCycle.refl f a).pow_right), pow_succ', Equiv.Perm.mul_apply]

private theorem glue_stable_orbit_iff {A B : Type*} [Finite A] [Finite B]
    (f : Equiv.Perm A) (g : Equiv.Perm B) (p : A → B) (a : A)
    (h : ∀ x, f.SameCycle a x → g (p x) = p (f x)) (b : B) :
    g.SameCycle (p a) b ↔ ∃ x, f.SameCycle a x ∧ p x = b := by
  constructor
  · intro hb
    obtain ⟨n, hn⟩ := hb.exists_nat_pow_eq
    refine ⟨(f ^ n) a, (Equiv.Perm.SameCycle.refl f a).pow_right, ?_⟩
    exact (glue_stable_orbit_pow f g p a h n).symm.trans hn
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast, hn] using glue_stable_orbit_pow f g p a h n




theorem glue_left_interior_rotation_cycle (d : DL)
    (hd : ∀ e, BL.map.toCombinatorialMap.rot.SameCycle d e → ¬ BL.map.IsOuter e)
    (a : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).rot.SameCycle (glueIdentify BL BR (.inl d)) a ↔
      ∃ e : DL, BL.map.toCombinatorialMap.rot.SameCycle d e ∧
        glueIdentify BL BR (.inl e) = a := by
  exact glue_stable_orbit_iff BL.map.toCombinatorialMap.rot
    (glueCombinatorialMap BL BR).rot (fun e => glueIdentify BL BR (.inl e)) d
    (fun e he => glue_rot_left_of_inner BL BR e (hd e he)) a




theorem glue_right_interior_rotation_cycle (d : DR)
    (hd : ∀ e, BR.map.toCombinatorialMap.rot.SameCycle d e → ¬ BR.map.IsOuter e)
    (a : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).rot.SameCycle (glueIdentify BL BR (.inr d)) a ↔
      ∃ e : DR, BR.map.toCombinatorialMap.rot.SameCycle d e ∧
        glueIdentify BL BR (.inr e) = a := by
  exact glue_stable_orbit_iff BR.map.toCombinatorialMap.rot
    (glueCombinatorialMap BL BR).rot (fun e => glueIdentify BL BR (.inr e)) d
    (fun e he => glue_rot_right_of_inner BL BR e (hd e he)) a



theorem glue_seam_tailVertex (i : Fin s) :
    dartTailVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inl (BL.rightPath.darts.get
          ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩))) =
      dartTailVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inr (BR.leftPath.darts.get
          ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩))) :=
  congrArg (dartTailVertex (glueDirectedMap BL BR)) (glueIdentify_seam BL BR i)



theorem glue_seam_headVertex (i : Fin s) :
    dartHeadVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inl (BL.rightPath.darts.get
          ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩))) =
      dartHeadVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inr (BR.leftPath.darts.get
          ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩))) :=
  congrArg (dartHeadVertex (glueDirectedMap BL BR)) (glueIdentify_seam BL BR i)

private def glue_path_vertex_dart {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (hn : 0 < n) (i : Fin (n + 1)) : D :=
  if hi : i.val < n then P.darts.get ⟨i.val, by rw [P.darts_length]; exact hi⟩
  else M.toCombinatorialMap.edgeInv
    (P.darts.get ⟨n - 1, by rw [P.darts_length]; omega⟩)

private theorem glue_path_vertex_dart_vertex {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (hn : 0 < n) (i : Fin (n + 1)) :
    dartTailVertex M (glue_path_vertex_dart P hn i) =
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ := by
  unfold glue_path_vertex_dart
  split
  · exact (P.edge_step _).2.2.1.symm
  · rename_i hi
    have hin : i.val = n := by omega
    change dartHeadVertex M
      (P.darts.get ⟨n - 1, by rw [P.darts_length]; omega⟩) = _
    have h := (P.edge_step ⟨n - 1, by rw [P.darts_length]; omega⟩).2.2.2.symm
    exact h.trans (congrArg P.vertices.get (Fin.ext (by dsimp; omega)))




@[expose] def glueLeftSeamVertexDart (i : Fin (s + 1)) : DL :=
  if hi : i.val < s then
    BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩
  else BL.map.toCombinatorialMap.edgeInv
    (BL.rightPath.darts.get ⟨s - 1, by
      rw [BL.rightPath.darts_length]; have := BL.right_length_pos; omega⟩)




@[expose] def glueRightSeamVertexDart (i : Fin (s + 1)) : DR :=
  if hi : i.val < s then
    BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact hi⟩
  else BR.map.toCombinatorialMap.edgeInv
    (BR.leftPath.darts.get ⟨s - 1, by
      rw [BR.leftPath.darts_length]; have := BR.left_length_pos; omega⟩)



theorem glueLeftSeamVertexDart_vertex (i : Fin (s + 1)) :
    dartTailVertex BL.map (glueLeftSeamVertexDart BL i) =
      BL.rightPath.vertices.get ⟨i.val, by rw [BL.rightPath.vertices_length]; exact i.isLt⟩ :=
  glue_path_vertex_dart_vertex BL.rightPath (by have := BL.right_length_pos; omega) i



theorem glueRightSeamVertexDart_vertex (i : Fin (s + 1)) :
    dartTailVertex BR.map (glueRightSeamVertexDart BR i) =
      BR.leftPath.vertices.get ⟨i.val, by rw [BR.leftPath.vertices_length]; exact i.isLt⟩ :=
  glue_path_vertex_dart_vertex BR.leftPath (by have := BR.left_length_pos; omega) i



theorem glueLeftSeamVertexDart_sameCycle_iff (i j : Fin (s + 1)) :
    BL.map.toCombinatorialMap.rot.SameCycle
      (glueLeftSeamVertexDart BL i) (glueLeftSeamVertexDart BL j) ↔ i = j := by
  constructor
  · intro h
    have hv : dartTailVertex BL.map (glueLeftSeamVertexDart BL i) =
        dartTailVertex BL.map (glueLeftSeamVertexDart BL j) := Quotient.sound h
    rw [glueLeftSeamVertexDart_vertex, glueLeftSeamVertexDart_vertex] at hv
    have he := BL.rightPath.vertices_nodup.get_inj_iff.mp hv
    exact Fin.ext (congrArg (fun x : Fin BL.rightPath.vertices.length => x.val) he)
  · rintro rfl
    exact Equiv.Perm.SameCycle.rfl



theorem glueRightSeamVertexDart_sameCycle_iff (i j : Fin (s + 1)) :
    BR.map.toCombinatorialMap.rot.SameCycle
      (glueRightSeamVertexDart BR i) (glueRightSeamVertexDart BR j) ↔ i = j := by
  constructor
  · intro h
    have hv : dartTailVertex BR.map (glueRightSeamVertexDart BR i) =
        dartTailVertex BR.map (glueRightSeamVertexDart BR j) := Quotient.sound h
    rw [glueRightSeamVertexDart_vertex, glueRightSeamVertexDart_vertex] at hv
    have he := BR.leftPath.vertices_nodup.get_inj_iff.mp hv
    exact Fin.ext (congrArg (fun x : Fin BR.leftPath.vertices.length => x.val) he)
  · rintro rfl
    exact Equiv.Perm.SameCycle.rfl




theorem glueIdentify_seamVertexDart (i : Fin (s + 1)) :
    glueIdentify BL BR (.inl (glueLeftSeamVertexDart BL i)) =
      glueIdentify BL BR (.inr (glueRightSeamVertexDart BR i)) := by
  unfold glueLeftSeamVertexDart glueRightSeamVertexDart
  split
  · rename_i hi
    exact glueIdentify_seam BL BR ⟨i.val, hi⟩
  · have hs : 0 < s := by have := BL.right_length_pos; omega
    have h := congrArg (glueEdgeInv BL BR) (glueIdentify_seam BL BR ⟨s - 1, by omega⟩)
    simpa only [glueEdgeInv_identify, Sum.map_inl, Sum.map_inr] using h



theorem glue_seamVertex_pair (i : Fin (s + 1)) :
    dartTailVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inl (glueLeftSeamVertexDart BL i))) =
      dartTailVertex (glueDirectedMap BL BR)
        (glueIdentify BL BR (.inr (glueRightSeamVertexDart BR i))) :=
  congrArg (dartTailVertex (glueDirectedMap BL BR)) (glueIdentify_seamVertexDart BL BR i)




theorem glue_dart_partition (a : GlueDart BL BR) :
    (glueDirectedMap BL BR).IsOuter a ∨
      (∃ d : DL, ¬ BL.map.IsOuter d ∧ glueIdentify BL BR (.inl d) = a) ∨
      (∃ d : DR, ¬ BR.map.IsOuter d ∧ glueIdentify BL BR (.inr d) = a) := by
  rcases a with a | a
  · by_cases ha : BL.map.IsOuter a.val
    · left
      apply (glue_isOuterCycle BL BR).1
      rw [glueOuterWord_letters, glueOuterDarts]
      have hm := BL.outerSplit.2.1.mem_iff.mp (BL.outerSplit.1.2.1 a.val ha)
      simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
      rcases hm with hm | ⟨d, hd, hda⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨a.val, hm, glueIdentify_inl_kept BL BR a⟩
      · exfalso
        apply a.property
        rw [← hda, BL.map.toCombinatorialMap.edgeInv_invol]
        exact hd
    · exact Or.inr (Or.inl ⟨a.val, ha, glueIdentify_inl_kept BL BR a⟩)
  · by_cases ha : BR.map.IsOuter a.val
    · left
      apply (glue_isOuterCycle BL BR).1
      rw [glueOuterWord_letters, glueOuterDarts]
      have hm := BR.outerSplit.2.1.mem_iff.mp (BR.outerSplit.1.2.1 a.val ha)
      simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
      rcases hm with hm | ⟨d, hd, hda⟩
      · exact False.elim (a.property hm)
      · apply List.mem_append_right
        apply List.mem_map.mpr
        refine ⟨d, List.mem_reverse.mpr hd, ?_⟩
        rw [hda, glueIdentify_inr_kept]
    · exact Or.inr (Or.inr ⟨a.val, ha, glueIdentify_inr_kept BL BR a⟩)




@[expose] def glueVertexCorner (a b : GlueDart BL BR) : Prop :=
  (∃ d : DL, ¬ BL.map.IsOuter d ∧
    a = glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.faceSucc d)) ∧
    b = glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d))) ∨
  (∃ d : DR, ¬ BR.map.IsOuter d ∧
    a = glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.faceSucc d)) ∧
    b = glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))) ∨
  (∃ d ∈ (glueOuterWord BL BR).letters,
    a = (glueOuterWord BL BR).letters.formPerm d ∧ b = glueEdgeInv BL BR d)

private theorem glue_rot_outer_corner (d : GlueDart BL BR)
    (hd : d ∈ (glueOuterWord BL BR).letters) :
    (glueCombinatorialMap BL BR).rot ((glueOuterWord BL BR).letters.formPerm d) =
      glueEdgeInv BL BR d := by
  have hf := (glue_isOuterCycle BL BR).2.2 d hd
  rw [glueDirectedMap_toCombinatorialMap] at hf
  rw [← hf, glue_rot_faceSucc, glueCombinatorialMap_edgeInv]




theorem glueVertexCorner_iff_rot (a b : GlueDart BL BR) :
    glueVertexCorner BL BR a b ↔ (glueCombinatorialMap BL BR).rot a = b := by
  constructor
  · rintro (⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩)
    · exact glue_rot_left_inner_corner BL BR d hd
    · exact glue_rot_right_inner_corner BL BR d hd
    · exact glue_rot_outer_corner BL BR d hd
  · intro hab
    let d := (glueCombinatorialMap BL BR).faceSucc.symm a
    have hx : (glueCombinatorialMap BL BR).faceSucc d = a :=
      (glueCombinatorialMap BL BR).faceSucc.apply_symm_apply a
    rcases glue_dart_partition BL BR d with hd | ⟨e, he, hed⟩ | ⟨e, he, hed⟩
    · refine Or.inr (Or.inr ⟨d, (glue_isOuterCycle BL BR).2.1 d hd, ?_, ?_⟩)
      · have hf := (glue_isOuterCycle BL BR).2.2 d
          ((glue_isOuterCycle BL BR).2.1 d hd)
        rw [glueDirectedMap_toCombinatorialMap, hx] at hf
        exact hf
      · rw [← hab, ← hx, glue_rot_faceSucc, glueCombinatorialMap_edgeInv]
    · have hx' : a = glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.faceSucc e)) := by
        rw [← hx, ← hed, glue_faceSucc_left_inner BL BR e he]
      refine Or.inl ⟨e, he, hx', ?_⟩
      rw [← hab, hx', glue_rot_left_inner_corner BL BR e he]
    · have hx' : a = glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.faceSucc e)) := by
        rw [← hx, ← hed, glue_faceSucc_right_inner BL BR e he]
      refine Or.inr (Or.inl ⟨e, he, hx', ?_⟩)
      rw [← hab, hx', glue_rot_right_inner_corner BL BR e he]




theorem glue_rotation_cycle_iff (a b : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).rot.SameCycle a b ↔
      Relation.EqvGen (glueVertexCorner BL BR) a b := by
  constructor
  · intro hab
    obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
    rw [← hn]
    clear hn
    induction n with
    | zero => exact Relation.EqvGen.refl a
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _
        ((glueVertexCorner_iff_rot BL BR _ _).mpr rfl))
  · intro hab
    induction hab with
    | rel x y h =>
      rw [← (glueVertexCorner_iff_rot BL BR x y).mp h]
      exact (Equiv.Perm.SameCycle.refl _ x).apply_right
    | refl => exact Equiv.Perm.SameCycle.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem glue_outer_length : (glueOuterWord BL BR).letters.length = ℓ + r := by
  rw [glueOuterWord_letters, glueOuterDarts, List.length_append,
    List.length_map, List.length_map, List.length_reverse,
    BL.leftPath.darts_length, BR.rightPath.darts_length]

private theorem glue_outer_get_left (i : ℕ) (hi : i < ℓ) :
    (glueOuterWord BL BR).letters[i]'(by rw [glue_outer_length]; omega) =
      glueIdentify BL BR (.inl (BL.leftPath.darts.get
        ⟨i, by rw [BL.leftPath.darts_length]; exact hi⟩)) := by
  have hi' : i < (BL.leftPath.darts.map (fun d => glueIdentify BL BR (.inl d))).length := by
    rw [List.length_map, BL.leftPath.darts_length]
    exact hi
  simp only [glueOuterWord_letters, glueOuterDarts]
  simp only [List.getElem_append_left hi', List.getElem_map]
  rfl

private theorem glue_outer_get_right (j : ℕ) (hj : j < r) :
    (glueOuterWord BL BR).letters[ℓ + j]'(by rw [glue_outer_length]; omega) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv
        (BR.rightPath.darts.get ⟨r - 1 - j, by rw [BR.rightPath.darts_length]; omega⟩))) := by
  have hj' : (BL.leftPath.darts.map (fun d => glueIdentify BL BR (.inl d))).length ≤ ℓ + j := by
    rw [List.length_map, BL.leftPath.darts_length]
    omega
  simp only [glueOuterWord_letters, glueOuterDarts]
  simp only [List.getElem_append_right hj', List.getElem_map, List.getElem_reverse]
  apply congrArg (fun d : DR => glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)))
  apply congrArg BR.rightPath.darts.get
  apply Fin.ext
  simp only [List.length_map, BL.leftPath.darts_length, BR.rightPath.darts_length]
  omega

private theorem glue_outer_face_index (i : ℕ) (hi : i < ℓ + r) :
    (glueCombinatorialMap BL BR).faceSucc
        ((glueOuterWord BL BR).letters[i]'(by rw [glue_outer_length]; exact hi)) =
      (glueOuterWord BL BR).letters[(i + 1) % (ℓ + r)]'(by
        rw [glue_outer_length]
        exact Nat.mod_lt _ (by have := BL.left_length_pos; omega)) := by
  have hf := (glue_isOuterCycle BL BR).2.2
    ((glueOuterWord BL BR).letters[i]'(by rw [glue_outer_length]; exact hi))
    (List.getElem_mem _)
  simpa only [glueDirectedMap_toCombinatorialMap, List.formPerm_apply_getElem _
    (glueOuterWord BL BR).nodup, glue_outer_length] using hf




theorem glue_rot_source_outer_corner :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inl (BL.leftPath.firstDart
          (by have := BL.left_length_pos; omega)))) =
      glueIdentify BL BR (.inr (BR.rightPath.firstDart
        (by have := BR.right_length_pos; omega))) := by
  have hl := BL.left_length_pos
  have hr := BR.right_length_pos
  have hf := glue_outer_face_index BL BR (ℓ + (r - 1)) (by omega)
  have hm : (ℓ + (r - 1) + 1) % (ℓ + r) = 0 := by
    have he : ℓ + (r - 1) + 1 = ℓ + r := by omega
    rw [he, Nat.mod_self]
  simp only [hm, glue_outer_get_left BL BR 0 (by omega),
    glue_outer_get_right BL BR (r - 1) (by omega), Nat.sub_self] at hf
  have h := congrArg (glueCombinatorialMap BL BR).rot hf
  rw [glue_rot_faceSucc, glueCombinatorialMap_edgeInv, glueEdgeInv_identify] at h
  simpa only [Sum.map_inr, BR.map.toCombinatorialMap.edgeInv_invol,
    SimpleDirectedDartPath.firstDart] using h.symm




theorem glue_rot_sink_outer_corner :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv
          (BR.rightPath.darts.get ⟨r - 1, by
            rw [BR.rightPath.darts_length]
            have := BR.right_length_pos
            omega⟩)))) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv
        (BL.leftPath.darts.get ⟨ℓ - 1, by
          rw [BL.leftPath.darts_length]
          have := BL.left_length_pos
          omega⟩))) := by
  have hl := BL.left_length_pos
  have hr := BR.right_length_pos
  have hf := glue_outer_face_index BL BR (ℓ - 1) (by omega)
  have hm : (ℓ - 1 + 1) % (ℓ + r) = ℓ + 0 := by
    have he : ℓ - 1 + 1 = ℓ := by omega
    rw [he, Nat.mod_eq_of_lt (by omega), Nat.add_zero]
  simp only [hm, glue_outer_get_left BL BR (ℓ - 1) (by omega),
    glue_outer_get_right BL BR 0 (by omega), Nat.sub_zero] at hf
  have h := congrArg (glueCombinatorialMap BL BR).rot hf
  rw [glue_rot_faceSucc, glueCombinatorialMap_edgeInv, glueEdgeInv_identify] at h
  exact h.symm




theorem glue_rot_left_boundary_corner (i : ℕ) (hi : i + 1 < ℓ) :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inl (BL.leftPath.darts.get
          ⟨i + 1, by rw [BL.leftPath.darts_length]; exact hi⟩))) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv
        (BL.leftPath.darts.get ⟨i, by rw [BL.leftPath.darts_length]; omega⟩))) := by
  have hf := glue_outer_face_index BL BR i (by omega)
  have hm : (i + 1) % (ℓ + r) = i + 1 := Nat.mod_eq_of_lt (by omega)
  simp only [hm, glue_outer_get_left BL BR i (by omega),
    glue_outer_get_left BL BR (i + 1) hi] at hf
  have h := congrArg (glueCombinatorialMap BL BR).rot hf
  rw [glue_rot_faceSucc, glueCombinatorialMap_edgeInv, glueEdgeInv_identify] at h
  exact h.symm




theorem glue_rot_right_boundary_corner (i : ℕ) (hi : i + 1 < r) :
    (glueCombinatorialMap BL BR).rot
        (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv
          (BR.rightPath.darts.get ⟨i, by rw [BR.rightPath.darts_length]; omega⟩)))) =
      glueIdentify BL BR (.inr (BR.rightPath.darts.get
        ⟨i + 1, by rw [BR.rightPath.darts_length]; exact hi⟩)) := by
  have hf := glue_outer_face_index BL BR (ℓ + (r - 2 - i)) (by omega)
  have hm : (ℓ + (r - 2 - i) + 1) % (ℓ + r) = ℓ + (r - 1 - i) := by
    have he : ℓ + (r - 2 - i) + 1 = ℓ + (r - 1 - i) := by omega
    rw [he, Nat.mod_eq_of_lt (by omega)]
  have h₁ : r - 1 - (r - 2 - i) = i + 1 := by omega
  have h₂ : r - 1 - (r - 1 - i) = i := by omega
  simp only [hm, glue_outer_get_right BL BR (r - 2 - i) (by omega),
    glue_outer_get_right BL BR (r - 1 - i) (by omega), h₁, h₂] at hf
  have h := congrArg (glueCombinatorialMap BL BR).rot hf
  rw [glue_rot_faceSucc, glueCombinatorialMap_edgeInv, glueEdgeInv_identify] at h
  simpa only [Sum.map_inr, BR.map.toCombinatorialMap.edgeInv_invol] using h.symm

private theorem glue_cycle_delete_one {A Q : Type*} [Finite A]
    (f : Equiv.Perm A) (q : A → Q) (bad : A → Prop)
    (hbad : ∀ x y, bad x → bad y → f.SameCycle x y → x = y)
    (hgood : ∀ x, ¬ bad x → q x = q (f x)) :
    ∀ x y, f.SameCycle x y → q x = q y := by
  classical
  have hstep (x : A) : q x = q (f x) := by
    by_cases hx : bad x
    · have hex : ∃ n : ℕ, (f ^ n) (f x) = x :=
        ((Equiv.Perm.SameCycle.refl f x).apply_left).exists_nat_pow_eq
      let n := Nat.find hex
      have hmin : ∀ k < n, (f ^ k) (f x) ≠ x := fun k hk => Nat.find_min hex hk
      have hseq : ∀ k, k ≤ n → q (f x) = q ((f ^ k) (f x)) := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ k ih =>
          intro hk
          rw [pow_succ', Equiv.Perm.mul_apply]
          refine (ih (by omega)).trans (hgood _ ?_)
          intro hb
          exact hmin k (by omega) (hbad _ _ hb hx
            (((Equiv.Perm.SameCycle.refl f (f x)).pow_right).symm.trans
              ((Equiv.Perm.SameCycle.refl f x).apply_left)))
      have h := hseq n le_rfl
      rw [Nat.find_spec hex] at h
      exact h.symm
    · exact hgood x hx
  intro x y hxy
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (hstep _)

private def glue_left_cut_corner (i : Fin (s + 1)) : DL :=
  if hi : i.val < s then
    BL.map.toCombinatorialMap.faceSucc (BL.map.toCombinatorialMap.edgeInv
      (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩))
  else BL.map.toCombinatorialMap.faceSucc
    (BL.leftPath.darts.get ⟨ℓ - 1, by
      rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩)

private theorem glue_left_cut_corner_vertex (i : Fin (s + 1)) :
    dartTailVertex BL.map (glue_left_cut_corner BL i) =
      dartTailVertex BL.map (glueLeftSeamVertexDart BL i) := by
  unfold glue_left_cut_corner
  split
  · rename_i hi
    apply Quotient.sound
    apply Equiv.Perm.sameCycle_apply_left.mp
    rw [glue_rot_faceSucc, BL.map.toCombinatorialMap.edgeInv_invol]
    simpa only [glueLeftSeamVertexDart, dite_eq_left hi] using
      (Equiv.Perm.SameCycle.refl BL.map.toCombinatorialMap.rot
        (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩))
  · rename_i hi
    have his : i.val = s := by omega
    have hrot : dartTailVertex BL.map
        (BL.map.toCombinatorialMap.faceSucc
          (BL.leftPath.darts.get ⟨ℓ - 1, by
            rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩)) =
        dartHeadVertex BL.map
          (BL.leftPath.darts.get ⟨ℓ - 1, by
            rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glue_rot_faceSucc]
    rw [hrot, glueLeftSeamVertexDart_vertex]
    have hv := (BL.leftPath.edge_step ⟨ℓ - 1, by
      rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩).2.2.2.symm
    have hlast : ℓ - 1 + 1 = ℓ := by have := BL.left_length_pos; omega
    simp only [hlast] at hv
    exact hv.trans (BL.leftPath.end_vertex.trans (by simpa only [his] using
      BL.rightPath.end_vertex.symm))

private theorem glue_left_cut_corner_unique (x y : DL)
    (hx : ∃ i, x = glue_left_cut_corner BL i)
    (hy : ∃ i, y = glue_left_cut_corner BL i)
    (hxy : BL.map.toCombinatorialMap.rot.SameCycle x y) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hv : dartTailVertex BL.map (glue_left_cut_corner BL i) =
      dartTailVertex BL.map (glue_left_cut_corner BL j) := Quotient.sound hxy
  rw [glue_left_cut_corner_vertex, glue_left_cut_corner_vertex] at hv
  have hij := (glueLeftSeamVertexDart_sameCycle_iff BL i j).mp (Quotient.exact hv)
  rw [hij]

private theorem glue_rot_left_except_cut (d : DL)
    (hd : ¬ ∃ i, d = glue_left_cut_corner BL i) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inl d)) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)) := by
  let e := BL.map.toCombinatorialMap.faceSucc.symm d
  have hed : BL.map.toCombinatorialMap.faceSucc e = d :=
    BL.map.toCombinatorialMap.faceSucc.apply_symm_apply d
  by_cases he : BL.map.IsOuter e
  · have hm := BL.outerSplit.2.1.mem_iff.mp (BL.outerSplit.1.2.1 e he)
    simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with hm | ⟨a, ha, hae⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      have hjl : j.val < ℓ := by simpa only [BL.leftPath.darts_length] using j.isLt
      by_cases hjlast : j.val + 1 < ℓ
      · have hsucc := outerFace_leftPath_successor BL j.val hjlast
        have heq : e = BL.leftPath.darts.get j := hj.symm
        have hdeq : d = BL.leftPath.darts.get
            ⟨j.val + 1, by simpa only [BL.leftPath.darts_length] using hjlast⟩ := by
          rw [← hed, heq]
          exact hsucc
        have hr := glue_rot_left_boundary_corner BL BR j.val hjlast
        have hrot : BL.map.toCombinatorialMap.rot d =
            BL.map.toCombinatorialMap.edgeInv (BL.leftPath.darts.get j) := by
          rw [← hed, glue_rot_faceSucc, heq]
        rw [hrot, hdeq]
        exact hr
      · exfalso
        apply hd
        refine ⟨⟨s, by omega⟩, ?_⟩
        simp only [glue_left_cut_corner, Nat.lt_irrefl, ↓reduceDIte]
        rw [← hed, ← hj]
        congr 2
        apply Fin.ext
        dsimp
        omega
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
      have hjs : j.val < s := by simpa only [BL.rightPath.darts_length] using j.isLt
      exfalso
      apply hd
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [glue_left_cut_corner, dite_eq_left hjs, ← hed, ← hae, ← hj]
  · rw [← hed, glue_rot_left_inner_corner BL BR e he, glue_rot_faceSucc]




theorem glueIdentify_left_sameCycle (d e : DL)
    (hde : BL.map.toCombinatorialMap.rot.SameCycle d e) :
    (glueCombinatorialMap BL BR).rot.SameCycle
      (glueIdentify BL BR (.inl d)) (glueIdentify BL BR (.inl e)) := by
  apply Quotient.exact (s := Equiv.Perm.SameCycle.setoid (glueCombinatorialMap BL BR).rot)
  apply glue_cycle_delete_one BL.map.toCombinatorialMap.rot
    (fun a => vertexClass (glueCombinatorialMap BL BR) (glueIdentify BL BR (.inl a)))
    (fun a => ∃ i, a = glue_left_cut_corner BL i)
    (glue_left_cut_corner_unique BL) _ d e hde
  intro a ha
  apply Quotient.sound
  rw [← glue_rot_left_except_cut BL BR a ha]
  exact (Equiv.Perm.SameCycle.refl _ _).apply_right


private def glue_right_cut_corner (i : Fin (s + 1)) : DR :=
  if hi : i.val = 0 then
    BR.map.toCombinatorialMap.faceSucc (BR.map.toCombinatorialMap.edgeInv
      (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)))
  else BR.map.toCombinatorialMap.faceSucc
    (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩)

private theorem glue_right_cut_corner_vertex (i : Fin (s + 1)) :
    dartTailVertex BR.map (glue_right_cut_corner BR i) =
      dartTailVertex BR.map (glueRightSeamVertexDart BR i) := by
  unfold glue_right_cut_corner
  split
  · rename_i hi
    have hv : dartTailVertex BR.map
        (BR.map.toCombinatorialMap.faceSucc (BR.map.toCombinatorialMap.edgeInv
          (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)))) =
        dartTailVertex BR.map
          (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glue_rot_faceSucc, BR.map.toCombinatorialMap.edgeInv_invol]
    rw [hv, glueRightSeamVertexDart_vertex]
    have hs := (BR.rightPath.edge_step ⟨0, by
      rw [BR.rightPath.darts_length]; have := BR.right_length_pos; omega⟩).2.2.1.symm
    exact hs.trans (BR.rightPath.start_vertex.trans (by simpa only [hi] using
      BR.leftPath.start_vertex.symm))
  · rename_i hi
    have hv : dartTailVertex BR.map
        (BR.map.toCombinatorialMap.faceSucc
          (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩)) =
        dartHeadVertex BR.map
          (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glue_rot_faceSucc]
    rw [hv, glueRightSeamVertexDart_vertex]
    have hs := (BR.leftPath.edge_step ⟨i.val - 1, by
      rw [BR.leftPath.darts_length]; omega⟩).2.2.2.symm
    have hadd : i.val - 1 + 1 = i.val := by omega
    simpa only [hadd] using hs

private theorem glue_right_cut_corner_unique (x y : DR)
    (hx : ∃ i, x = glue_right_cut_corner BR i)
    (hy : ∃ i, y = glue_right_cut_corner BR i)
    (hxy : BR.map.toCombinatorialMap.rot.SameCycle x y) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hv : dartTailVertex BR.map (glue_right_cut_corner BR i) =
      dartTailVertex BR.map (glue_right_cut_corner BR j) := Quotient.sound hxy
  rw [glue_right_cut_corner_vertex, glue_right_cut_corner_vertex] at hv
  have hij := (glueRightSeamVertexDart_sameCycle_iff BR i j).mp (Quotient.exact hv)
  rw [hij]

private theorem glue_rot_right_except_cut (d : DR)
    (hd : ¬ ∃ i, d = glue_right_cut_corner BR i) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)) := by
  let e := BR.map.toCombinatorialMap.faceSucc.symm d
  have hed : BR.map.toCombinatorialMap.faceSucc e = d :=
    BR.map.toCombinatorialMap.faceSucc.apply_symm_apply d
  by_cases he : BR.map.IsOuter e
  · have hm := BR.outerSplit.2.1.mem_iff.mp (BR.outerSplit.1.2.1 e he)
    simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with hm | ⟨a, ha, hae⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      have hjs : j.val < s := by simpa only [BR.leftPath.darts_length] using j.isLt
      exfalso
      apply hd
      refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
      simp only [glue_right_cut_corner, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceDIte, Nat.add_sub_cancel]
      rw [← hed, ← hj]
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
      have hjr : j.val < r := by simpa only [BR.rightPath.darts_length] using j.isLt
      by_cases hjzero : j.val = 0
      · exfalso
        apply hd
        refine ⟨⟨0, by omega⟩, ?_⟩
        simp only [glue_right_cut_corner, ↓reduceDIte]
        rw [← hed, ← hae, ← hj]
        congr 3
        exact Fin.ext hjzero
      · have hsucc := outerFace_rightPath_successor BR (j.val - 1) (by omega)
        have hadd : j.val - 1 + 1 = j.val := by omega
        simp only [hadd] at hsucc
        have hdeq : d = BR.map.toCombinatorialMap.edgeInv
            (BR.rightPath.darts.get ⟨j.val - 1, by
              simpa only [BR.rightPath.darts_length] using (show j.val - 1 < r by omega)⟩) := by
          rw [← hed, ← hae, ← hj]
          exact hsucc
        have hrot : BR.map.toCombinatorialMap.rot d = BR.rightPath.darts.get j := by
          rw [← hed, glue_rot_faceSucc, ← hae, ← hj,
            BR.map.toCombinatorialMap.edgeInv_invol]
        rw [hrot, hdeq]
        simpa only [hadd] using glue_rot_right_boundary_corner BL BR (j.val - 1) (by omega)
  · rw [← hed, glue_rot_right_inner_corner BL BR e he, glue_rot_faceSucc]




theorem glueIdentify_right_sameCycle (d e : DR)
    (hde : BR.map.toCombinatorialMap.rot.SameCycle d e) :
    (glueCombinatorialMap BL BR).rot.SameCycle
      (glueIdentify BL BR (.inr d)) (glueIdentify BL BR (.inr e)) := by
  apply Quotient.exact (s := Equiv.Perm.SameCycle.setoid (glueCombinatorialMap BL BR).rot)
  apply glue_cycle_delete_one BR.map.toCombinatorialMap.rot
    (fun a => vertexClass (glueCombinatorialMap BL BR) (glueIdentify BL BR (.inr a)))
    (fun a => ∃ i, a = glue_right_cut_corner BR i)
    (glue_right_cut_corner_unique BR) _ d e hde
  intro a ha
  apply Quotient.sound
  rw [← glue_rot_right_except_cut BL BR a ha]
  exact (Equiv.Perm.SameCycle.refl _ _).apply_right




@[expose] noncomputable def glueVertexMap :
    MapVertex BL.map ⊕ MapVertex BR.map →
      CombinatorialMap.VertexQuotient (glueCombinatorialMap BL BR)
  | .inl v => Quotient.lift
      (fun d => vertexClass (glueCombinatorialMap BL BR) (glueIdentify BL BR (.inl d)))
      (fun d e h => Quotient.sound (glueIdentify_left_sameCycle BL BR d e h)) v
  | .inr v => Quotient.lift
      (fun d => vertexClass (glueCombinatorialMap BL BR) (glueIdentify BL BR (.inr d)))
      (fun d e h => Quotient.sound (glueIdentify_right_sameCycle BL BR d e h)) v



theorem glueVertexMap_surjective : Function.Surjective (glueVertexMap BL BR) := by
  intro v
  refine Quotient.inductionOn v ?_
  intro a
  obtain ⟨d, rfl⟩ := glueIdentify_surjective BL BR a
  cases d with
  | inl d => exact ⟨.inl (dartTailVertex BL.map d), rfl⟩
  | inr d => exact ⟨.inr (dartTailVertex BR.map d), rfl⟩





theorem glueVertexMap_seam (i : Fin (s + 1)) :
    glueVertexMap BL BR (.inl (dartTailVertex BL.map (glueLeftSeamVertexDart BL i))) =
      glueVertexMap BL BR (.inr (dartTailVertex BR.map (glueRightSeamVertexDart BR i))) := by
  change vertexClass (glueCombinatorialMap BL BR)
      (glueIdentify BL BR (.inl (glueLeftSeamVertexDart BL i))) =
    vertexClass (glueCombinatorialMap BL BR)
      (glueIdentify BL BR (.inr (glueRightSeamVertexDart BR i)))
  rw [glueIdentify_seamVertexDart]


private def glue_reach {A : Type*} [Fintype A] [DecidableEq A]
    (M : CombinatorialMap A) : A → A → Prop := Relation.ReflTransGen
  (fun x y => y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x)

private theorem glue_reach_sameCycle {A : Type*} [Fintype A] [DecidableEq A]
    (M : CombinatorialMap A) (x y : A) (h : M.rot.SameCycle x y) :
    glue_reach M x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.tail (Or.inl rfl)

private theorem glue_reach_transport {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : CombinatorialMap A) (N : CombinatorialMap B) (p : A → B)
    (hc : ∀ x y, M.rot.SameCycle x y → N.rot.SameCycle (p x) (p y))
    (he : ∀ x, N.edgeInv (p x) = p (M.edgeInv x))
    (x y : A) (hxy : glue_reach M x y) : glue_reach N (p x) (p y) := by
  apply Relation.ReflTransGen.lift' p _ x y hxy
  intro a b hab
  rcases hab with rfl | rfl | rfl | rfl
  · exact glue_reach_sameCycle N _ _ (hc _ _
      ((Equiv.Perm.SameCycle.refl M.rot a).apply_right))
  · exact glue_reach_sameCycle N _ _ (hc _ _
      ((Equiv.Perm.SameCycle.refl M.rot a).symm_apply_right))
  · change glue_reach N (p a) (p (M.edgeInv a))
    rw [← he]
    exact Relation.ReflTransGen.single (Or.inr (Or.inr (Or.inl rfl)))
  · have hinv : M.edgeInv.symm a = M.edgeInv a := by
      apply M.edgeInv.injective
      rw [Equiv.apply_symm_apply, M.edgeInv_invol]
    change glue_reach N (p a) (p (M.edgeInv.symm a))
    rw [hinv, ← he]
    exact Relation.ReflTransGen.single (Or.inr (Or.inr (Or.inl rfl)))




theorem glue_isConnected : (glueCombinatorialMap BL BR).IsConnected := by
  have hL (d e : DL) : glue_reach (glueCombinatorialMap BL BR)
      (glueIdentify BL BR (.inl d)) (glueIdentify BL BR (.inl e)) := by
    apply glue_reach_transport BL.map.toCombinatorialMap (glueCombinatorialMap BL BR)
      (fun a => glueIdentify BL BR (.inl a)) (glueIdentify_left_sameCycle BL BR)
      (fun a => ?_) d e (BL.planar.1 d e)
    rw [glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
    rfl
  have hR (d e : DR) : glue_reach (glueCombinatorialMap BL BR)
      (glueIdentify BL BR (.inr d)) (glueIdentify BL BR (.inr e)) := by
    apply glue_reach_transport BR.map.toCombinatorialMap (glueCombinatorialMap BL BR)
      (fun a => glueIdentify BL BR (.inr a)) (glueIdentify_right_sameCycle BL BR)
      (fun a => ?_) d e (BR.planar.1 d e)
    rw [glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
    rfl
  intro a b
  obtain ⟨d, rfl⟩ := glueIdentify_surjective BL BR a
  obtain ⟨e, rfl⟩ := glueIdentify_surjective BL BR b
  let i : Fin (s + 1) := ⟨0, by omega⟩
  cases d with
  | inl d =>
    cases e with
    | inl e => exact hL d e
    | inr e =>
      have h := hL d (glueLeftSeamVertexDart BL i)
      rw [glueIdentify_seamVertexDart BL BR i] at h
      exact h.trans (hR (glueRightSeamVertexDart BR i) e)
  | inr d =>
    cases e with
    | inr e => exact hR d e
    | inl e =>
      have h := hR d (glueRightSeamVertexDart BR i)
      rw [← glueIdentify_seamVertexDart BL BR i] at h
      exact h.trans (hL (glueLeftSeamVertexDart BL i) e)


private theorem glue_inner_left_kept (d : DL) (hd : ¬ BL.map.IsOuter d) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
  intro h
  apply hd
  apply BL.outerSplit.1.1 d
  apply BL.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse]
  exact Or.inr ⟨BL.map.toCombinatorialMap.edgeInv d, h,
    BL.map.toCombinatorialMap.edgeInv_invol d⟩

private theorem glue_inner_right_kept (d : DR) (hd : ¬ BR.map.IsOuter d) :
    d ∉ BR.leftPath.darts := by
  intro h
  apply hd
  apply BR.outerSplit.1.1 d
  apply BR.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl h

private theorem glue_inner_left_injective (d e : DL)
    (hd : ¬ BL.map.IsOuter d) (he : ¬ BL.map.IsOuter e)
    (h : glueIdentify BL BR (.inl d) = glueIdentify BL BR (.inl e)) : d = e := by
  have hd' := glue_inner_left_kept BL d hd
  have he' := glue_inner_left_kept BL e he
  rw [glueIdentify_inl_kept BL BR ⟨d, hd'⟩,
    glueIdentify_inl_kept BL BR ⟨e, he'⟩] at h
  exact congrArg Subtype.val (Sum.inl.inj h)

private theorem glue_inner_right_injective (d e : DR)
    (hd : ¬ BR.map.IsOuter d) (he : ¬ BR.map.IsOuter e)
    (h : glueIdentify BL BR (.inr d) = glueIdentify BL BR (.inr e)) : d = e := by
  have hd' := glue_inner_right_kept BR d hd
  have he' := glue_inner_right_kept BR e he
  rw [glueIdentify_inr_kept BL BR ⟨d, hd'⟩,
    glueIdentify_inr_kept BL BR ⟨e, he'⟩] at h
  exact congrArg Subtype.val (Sum.inr.inj h)

private theorem glue_inner_succ {A : Type*} [Fintype A] [DecidableEq A]
    (M : DirectedMapWithMissing A) (d : A) (hd : ¬ M.IsOuter d) :
    ¬ M.IsOuter (M.toCombinatorialMap.faceSucc d) :=
  fun h => hd (Equiv.Perm.sameCycle_apply_right.mp h)

private theorem glue_left_triangle (d : DL) (hd : ¬ BL.map.IsOuter d) :
    let f := (glueCombinatorialMap BL BR).faceSucc
    let a := glueIdentify BL BR (.inl d)
    f (f (f a)) = a ∧ f a ≠ a ∧ f (f a) ≠ a := by
  dsimp only
  have h1 := glue_inner_succ BL.map d hd
  have h2 := glue_inner_succ BL.map _ h1
  have ht := BL.innerFacesDegreeThree d hd
  rw [glue_faceSucc_left_inner BL BR d hd,
    glue_faceSucc_left_inner BL BR _ h1, glue_faceSucc_left_inner BL BR _ h2, ht.1]
  refine ⟨rfl, ?_, ?_⟩
  · intro heq
    exact ht.2.1 (glue_inner_left_injective BL BR _ _ h1 hd heq)
  · intro heq
    exact ht.2.2 (glue_inner_left_injective BL BR _ _ h2 hd heq)

private theorem glue_right_triangle (d : DR) (hd : ¬ BR.map.IsOuter d) :
    let f := (glueCombinatorialMap BL BR).faceSucc
    let a := glueIdentify BL BR (.inr d)
    f (f (f a)) = a ∧ f a ≠ a ∧ f (f a) ≠ a := by
  dsimp only
  have h1 := glue_inner_succ BR.map d hd
  have h2 := glue_inner_succ BR.map _ h1
  have ht := BR.innerFacesDegreeThree d hd
  rw [glue_faceSucc_right_inner BL BR d hd,
    glue_faceSucc_right_inner BL BR _ h1, glue_faceSucc_right_inner BL BR _ h2, ht.1]
  refine ⟨rfl, ?_, ?_⟩
  · intro heq
    exact ht.2.1 (glue_inner_right_injective BL BR _ _ h1 hd heq)
  · intro heq
    exact ht.2.2 (glue_inner_right_injective BL BR _ _ h2 hd heq)




theorem glue_innerFacesDegreeThree (a : GlueDart BL BR)
    (ha : ¬ (glueDirectedMap BL BR).IsOuter a) :
    (glueCombinatorialMap BL BR).faceSucc
        ((glueCombinatorialMap BL BR).faceSucc
          ((glueCombinatorialMap BL BR).faceSucc a)) = a ∧
      (glueCombinatorialMap BL BR).faceSucc a ≠ a ∧
      (glueCombinatorialMap BL BR).faceSucc
        ((glueCombinatorialMap BL BR).faceSucc a) ≠ a := by
  rcases glue_dart_partition BL BR a with h | ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact False.elim (ha h)
  · exact glue_left_triangle BL BR d hd
  · exact glue_right_triangle BL BR d hd


private def glue_face_fiber {A : Type*} [Fintype A] [DecidableEq A]
    (M : DirectedMapWithMissing A)
    (q : CombinatorialMap.FaceQuotient M.toCombinatorialMap) :=
  {d : A // faceClass M.toCombinatorialMap d = q}

private theorem glue_triangular_fiber_card {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D)
    (tri : ∀ d, ¬ M.IsOuter d →
      M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc
        (M.toCombinatorialMap.faceSucc d)) = d ∧
      M.toCombinatorialMap.faceSucc d ≠ d ∧
      M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc d) ≠ d)
    (q : CombinatorialMap.FaceQuotient M.toCombinatorialMap)
    (hq : q ≠ faceClass M.toCombinatorialMap M.outer) :
    Nat.card (glue_face_fiber M q) = 3 := by
  classical
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hinner : ¬ M.IsOuter d := by
    intro hd
    apply hq
    apply Quotient.sound
    exact hd.symm
  let f := M.toCombinatorialMap.faceSucc
  have htri := tri d hinner
  let s : Finset D := {d, f d, f (f d)}
  have hfd : f d ≠ d := htri.2.1
  have hffd : f (f d) ≠ d := htri.2.2
  have hfdffd : f d ≠ f (f d) := fun h => hfd (f.injective h.symm)
  have hbij : Set.BijOn f (s : Set D) (s : Set D) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change x ∈ s at hx
      change f x ∈ s
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl htri.1
    · intro x hx y hy hxy
      exact f.injective hxy
    · intro y hy
      change y ∈ s at hy
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h
      · refine ⟨f (f d), by simp [s], ?_⟩
        rw [h]
        exact htri.1
      · exact ⟨d, by simp [s], h.symm⟩
      · exact ⟨f d, by simp [s], h.symm⟩
  let fiberEquiv : glue_face_fiber M (Quotient.mk
      (Equiv.Perm.SameCycle.setoid f) d) ≃ {x : D // x ∈ s} := {
    toFun := fun x => by
      refine ⟨x.1, ?_⟩
      have hrel : f.SameCycle x.1 d := by
        exact Quotient.exact x.2
      rcases hrel.symm with ⟨i, hi⟩
      have hpow : (f ^ i) d ∈ (s : Set D) :=
        (hbij.perm_zpow i).1 (by simp [s] : d ∈ (s : Set D))
      rw [hi] at hpow
      exact Finset.mem_coe.mp hpow
    invFun := fun x => by
      refine ⟨x.1, ?_⟩
      apply Quotient.sound
      change f.SameCycle x.1 d
      have hx := x.2
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · simpa [h] using Equiv.Perm.SameCycle.rfl (f := f) (x := d)
      · rw [h]
        exact ⟨2, by change f (f (f d)) = d; exact htri.1⟩
      · rw [h]
        exact ⟨1, by change f (f (f d)) = d; exact htri.1⟩
    left_inv x := by
      apply Subtype.ext
      rfl
    right_inv x := by
      apply Subtype.ext
      rfl }
  have hs : s.card = 3 := by
    change (insert d (insert (f d) ({f (f d)} : Finset D))).card = 3
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hfd h.symm, fun h => hffd h.symm⟩),
      Finset.card_insert_of_notMem (by simpa using hfdffd)]
    simp
  calc
    Nat.card (glue_face_fiber M (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d)) =
        Nat.card {x : D // x ∈ s} := Nat.card_congr fiberEquiv
    _ = s.card := Nat.subtype_card s (by intro x; rfl)
    _ = 3 := hs


private theorem glue_face_fiber_card_sum {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) :
    Fintype.card D = ∑ q : CombinatorialMap.FaceQuotient M.toCombinatorialMap,
      Nat.card (glue_face_fiber M q) := by
  classical
  let fiber := fun q : CombinatorialMap.FaceQuotient M.toCombinatorialMap =>
    glue_face_fiber M q
  let fiberFintype : ∀ q, Fintype (fiber q) := fun q =>
    Fintype.subtype
      (Finset.univ.filter (fun d : D =>
        Quotient.mk
          (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d = q))
      (by intro d; simp [faceClass])
  let sigmaFintype : Fintype (Σ q, fiber q) :=
    @Sigma.instFintype _ fiber fiberFintype inferInstance
  let faceOf : D → CombinatorialMap.FaceQuotient M.toCombinatorialMap :=
    fun d => Quotient.mk
      (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d
  let e : D ≃ Σ q, fiber q := (Equiv.sigmaFiberEquiv faceOf).symm
  calc
    Fintype.card D = @Fintype.card (Σ q, fiber q) sigmaFintype :=
      @Fintype.card_congr D (Σ q, fiber q) inferInstance sigmaFintype e
    _ = ∑ q, @Fintype.card (fiber q) (fiberFintype q) :=
      @Fintype.card_sigma _ fiber inferInstance fiberFintype
    _ = ∑ q, Nat.card (glue_face_fiber M q) := by
      apply Finset.sum_congr rfl
      intro q hq
      change @Fintype.card (fiber q) (fiberFintype q) = Nat.card (fiber q)
      exact (@Nat.card_eq_fintype_card (fiber q) (fiberFintype q)).symm


private theorem glue_outer_fiber_card {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (W : NonemptyWord D) (hw : IsOuterCycle M W) :
    Nat.card (glue_face_fiber M (faceClass M.toCombinatorialMap M.outer)) =
      W.letters.length := by
  classical
  let e : glue_face_fiber M (faceClass M.toCombinatorialMap M.outer) ≃
      {d : D // d ∈ W.letters} := {
    toFun := fun d => ⟨d.val, hw.2.1 d.val (Quotient.exact d.property).symm⟩
    invFun := fun d => ⟨d.val, Quotient.sound (hw.1 d.val d.property).symm⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }
  calc
    Nat.card (glue_face_fiber M (faceClass M.toCombinatorialMap M.outer)) =
        Nat.card {d : D // d ∈ W.letters} := Nat.card_congr e
    _ = W.letters.toFinset.card := Nat.subtype_card _ (by intro d; simp)
    _ = W.letters.length := List.toFinset_card_of_nodup W.nodup

private theorem glue_triangular_dart_count {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (W : NonemptyWord D) (hw : IsOuterCycle M W)
    (tri : ∀ d, ¬ M.IsOuter d →
      M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc
        (M.toCombinatorialMap.faceSucc d)) = d ∧
      M.toCombinatorialMap.faceSucc d ≠ d ∧
      M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc d) ≠ d) :
    Fintype.card D = 3 * (M.toCombinatorialMap.numFaces - 1) + W.letters.length := by
  classical
  let outerQ := faceClass M.toCombinatorialMap M.outer
  let c := fun q => Nat.card (glue_face_fiber M q)
  have hnum : (Finset.univ.erase outerQ).card = M.toCombinatorialMap.numFaces - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ outerQ), Finset.card_univ,
      CombinatorialMap.numFaces]
  calc
    Fintype.card D = ∑ q, c q := glue_face_fiber_card_sum M
    _ = c outerQ + ∑ q ∈ Finset.univ.erase outerQ, c q := by
      rw [← Finset.sum_erase_add (a := outerQ) Finset.univ c (Finset.mem_univ outerQ)]
      exact add_comm _ _
    _ = W.letters.length + ∑ q ∈ Finset.univ.erase outerQ, 3 := by
      congr 1
      · exact glue_outer_fiber_card M W hw
      · apply Finset.sum_congr rfl
        intro q hq
        exact glue_triangular_fiber_card M tri q (Finset.mem_erase.mp hq).1
    _ = 3 * (M.toCombinatorialMap.numFaces - 1) + W.letters.length := by
      rw [Finset.sum_const_nat (fun q hq => rfl), hnum]
      omega




theorem numFaces_glueCombinatorialMap :
    (glueCombinatorialMap BL BR).numFaces + 1 =
      BL.map.toCombinatorialMap.numFaces + BR.map.toCombinatorialMap.numFaces := by
  classical
  have hg := glue_triangular_dart_count (glueDirectedMap BL BR) (glueOuterWord BL BR)
    (glue_isOuterCycle BL BR) (by
      intro d hd
      simpa only [glueDirectedMap_toCombinatorialMap] using
        glue_innerFacesDegreeThree BL BR d hd)
  rw [glueDirectedMap_toCombinatorialMap, glue_outer_length] at hg
  have hl := dartCount_eq_innerFaces BL
  have hr := dartCount_eq_innerFaces BR
  have he := numEdges_glueCombinatorialMap BL BR
  have hdg := (glueCombinatorialMap BL BR).two_mul_numEdges
  have hdl := BL.map.toCombinatorialMap.two_mul_numEdges
  have hdr := BR.map.toCombinatorialMap.two_mul_numEdges
  have hgp : 0 < (glueCombinatorialMap BL BR).numFaces :=
    Fintype.card_pos_iff.mpr ⟨faceClass (glueCombinatorialMap BL BR)
      (glueDirectedMap BL BR).outer⟩
  have hlp : 0 < BL.map.toCombinatorialMap.numFaces :=
    Fintype.card_pos_iff.mpr ⟨faceClass BL.map.toCombinatorialMap BL.map.outer⟩
  have hrp : 0 < BR.map.toCombinatorialMap.numFaces :=
    Fintype.card_pos_iff.mpr ⟨faceClass BR.map.toCombinatorialMap BR.map.outer⟩
  change Fintype.card DL = 3 * (BL.map.toCombinatorialMap.numFaces - 1) + (ℓ + s) at hl
  change Fintype.card DR = 3 * (BR.map.toCombinatorialMap.numFaces - 1) + (s + r) at hr
  omega


private theorem glue_right_seam_vertex_card :
    Fintype.card {v : MapVertex BR.map //
      ∃ i : Fin (s + 1), v = dartTailVertex BR.map (glueRightSeamVertexDart BR i)} =
      s + 1 := by
  classical
  let f : Fin (s + 1) → {v : MapVertex BR.map //
      ∃ i : Fin (s + 1), v = dartTailVertex BR.map (glueRightSeamVertexDart BR i)} :=
    fun i => ⟨dartTailVertex BR.map (glueRightSeamVertexDart BR i), i, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hv := congrArg Subtype.val hij
      exact (glueRightSeamVertexDart_sameCycle_iff BR i j).mp (Quotient.exact hv)
    · rintro ⟨v, i, rfl⟩
      exact ⟨i, rfl⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans (Fintype.card_fin _)





theorem numVertices_glueCombinatorialMap_le :
    (glueCombinatorialMap BL BR).numVertices + (s + 1) ≤
      BL.map.toCombinatorialMap.numVertices + BR.map.toCombinatorialMap.numVertices := by
  classical
  let seam : MapVertex BR.map → Prop := fun v =>
    ∃ i : Fin (s + 1), v = dartTailVertex BR.map (glueRightSeamVertexDart BR i)
  let A := MapVertex BL.map ⊕ {v : MapVertex BR.map // ¬ seam v}
  let f : A → CombinatorialMap.VertexQuotient (glueCombinatorialMap BL BR) :=
    fun v => glueVertexMap BL BR (v.map id Subtype.val)
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, hv⟩ := glueVertexMap_surjective BL BR w
    cases v with
    | inl v => exact ⟨.inl v, hv⟩
    | inr v =>
      by_cases hs : seam v
      · obtain ⟨i, rfl⟩ := hs
        exact ⟨.inl (dartTailVertex BL.map (glueLeftSeamVertexDart BL i)),
          (glueVertexMap_seam BL BR i).trans hv⟩
      · exact ⟨.inr ⟨v, hs⟩, hv⟩
  have hc := Fintype.card_le_of_surjective f hf
  have hs : Fintype.card {v : MapVertex BR.map // seam v} = s + 1 :=
    glue_right_seam_vertex_card BR
  have hbound := Fintype.card_subtype_le seam
  change (glueCombinatorialMap BL BR).numVertices ≤ Fintype.card (_ ⊕ _) at hc
  rw [Fintype.card_sum, Fintype.card_subtype_compl, hs] at hc
  rw [hs] at hbound
  change s + 1 ≤ BR.map.toCombinatorialMap.numVertices at hbound
  change (glueCombinatorialMap BL BR).numVertices ≤
    BL.map.toCombinatorialMap.numVertices + (BR.map.toCombinatorialMap.numVertices - (s + 1)) at hc
  omega





theorem glue_left_inner_face_cycle (d : DL) (hd : ¬ BL.map.IsOuter d)
    (a : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).faceSucc.SameCycle
      (glueIdentify BL BR (.inl d)) a ↔
      ∃ e : DL, BL.map.toCombinatorialMap.faceSucc.SameCycle d e ∧
        glueIdentify BL BR (.inl e) = a := by
  exact glue_stable_orbit_iff BL.map.toCombinatorialMap.faceSucc
    (glueCombinatorialMap BL BR).faceSucc (fun e => glueIdentify BL BR (.inl e)) d
    (fun e he => glue_faceSucc_left_inner BL BR e
      (fun ho => hd (ho.trans he.symm))) a





theorem glue_right_inner_face_cycle (d : DR) (hd : ¬ BR.map.IsOuter d)
    (a : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).faceSucc.SameCycle
      (glueIdentify BL BR (.inr d)) a ↔
      ∃ e : DR, BR.map.toCombinatorialMap.faceSucc.SameCycle d e ∧
        glueIdentify BL BR (.inr e) = a := by
  exact glue_stable_orbit_iff BR.map.toCombinatorialMap.faceSucc
    (glueCombinatorialMap BL BR).faceSucc (fun e => glueIdentify BL BR (.inr e)) d
    (fun e he => glue_faceSucc_right_inner BL BR e
      (fun ho => hd (ho.trans he.symm))) a


private theorem glue_path_tail_of_mem {A : Type*} [Fintype A] [DecidableEq A]
    {M : DirectedMapWithMissing A} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) {d : A} (hd : d ∈ P.darts) : M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (P.edge_step i).2.1

private theorem glue_left_boundary_kept {d : DL} (hd : d ∈ BL.leftPath.darts) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
  intro h
  exact (BL.map.tail_iff d (BL.noMissingDarts d)).mp
    (glue_path_tail_of_mem BL.leftPath hd) (glue_path_tail_of_mem BL.rightPath h)

private theorem glue_right_boundary_reverse_kept {d : DR} (hd : d ∈ BR.rightPath.darts) :
    BR.map.toCombinatorialMap.edgeInv d ∉ BR.leftPath.darts := by
  intro h
  exact (BR.map.tail_iff d (BR.noMissingDarts d)).mp
    (glue_path_tail_of_mem BR.rightPath hd) (glue_path_tail_of_mem BR.leftPath h)




theorem glue_inner_faces_not_outer :
    (∀ d : DL, ¬ BL.map.IsOuter d →
      ¬ (glueDirectedMap BL BR).IsOuter (glueIdentify BL BR (.inl d))) ∧
    (∀ d : DR, ¬ BR.map.IsOuter d →
      ¬ (glueDirectedMap BL BR).IsOuter (glueIdentify BL BR (.inr d))) := by
  constructor
  · intro d hd ho
    have hm := (glue_isOuterCycle BL BR).2.1 _ ho
    rw [glueOuterWord_letters, glueOuterDarts] at hm
    simp only [List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with ⟨e, he, heq⟩ | ⟨e, he, heq⟩
    · rw [glueIdentify_inl_kept BL BR ⟨e, glue_left_boundary_kept BL he⟩,
        glueIdentify_inl_kept BL BR ⟨d, glue_inner_left_kept BL d hd⟩] at heq
      have hed : e = d := congrArg Subtype.val (Sum.inl.inj heq)
      apply hd
      apply BL.outerSplit.1.1
      apply BL.outerSplit.2.1.mem_iff.mpr
      simp only [List.append_nil, List.mem_append]
      exact Or.inl (hed ▸ he)
    · rw [glueIdentify_inr_kept BL BR
          ⟨BR.map.toCombinatorialMap.edgeInv e, glue_right_boundary_reverse_kept BR he⟩,
        glueIdentify_inl_kept BL BR ⟨d, glue_inner_left_kept BL d hd⟩] at heq
      cases heq
  · intro d hd ho
    have hm := (glue_isOuterCycle BL BR).2.1 _ ho
    rw [glueOuterWord_letters, glueOuterDarts] at hm
    simp only [List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with ⟨e, he, heq⟩ | ⟨e, he, heq⟩
    · rw [glueIdentify_inl_kept BL BR ⟨e, glue_left_boundary_kept BL he⟩,
        glueIdentify_inr_kept BL BR ⟨d, glue_inner_right_kept BR d hd⟩] at heq
      cases heq
    · rw [glueIdentify_inr_kept BL BR
          ⟨BR.map.toCombinatorialMap.edgeInv e, glue_right_boundary_reverse_kept BR he⟩,
        glueIdentify_inr_kept BL BR ⟨d, glue_inner_right_kept BR d hd⟩] at heq
      have hed : BR.map.toCombinatorialMap.edgeInv e = d :=
        congrArg Subtype.val (Sum.inr.inj heq)
      apply hd
      apply BR.outerSplit.1.1
      apply BR.outerSplit.2.1.mem_iff.mpr
      simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse]
      exact Or.inr ⟨e, he, hed⟩

private abbrev glue_lv (i : Fin (s + 1)) : MapVertex BL.map :=
  dartTailVertex BL.map (glueLeftSeamVertexDart BL i)

private abbrev glue_rv (i : Fin (s + 1)) : MapVertex BR.map :=
  dartTailVertex BR.map (glueRightSeamVertexDart BR i)

private noncomputable def glue_right_label (v : MapVertex BR.map) :
    MapVertex BL.map ⊕ MapVertex BR.map :=
  if h : ∃ i, v = glue_rv BR i then .inl (glue_lv BL h.choose) else .inr v

private theorem glue_right_label_seam (i : Fin (s + 1)) :
    glue_right_label BL BR (glue_rv BR i) = .inl (glue_lv BL i) := by
  unfold glue_right_label
  split
  · rename_i h
    have hi : h.choose = i :=
      (glueRightSeamVertexDart_sameCycle_iff BR _ _).mp
        (Quotient.exact h.choose_spec.symm)
    rw [hi]
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

private noncomputable def glue_vertex_label : GlueDart BL BR →
    MapVertex BL.map ⊕ MapVertex BR.map
  | .inl d => .inl (dartTailVertex BL.map d.val)
  | .inr d => glue_right_label BL BR (dartTailVertex BR.map d.val)

private theorem glue_path_head_index {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (j : Fin n) :
    dartTailVertex M (M.toCombinatorialMap.edgeInv
      (P.darts.get ⟨j.val, by rw [P.darts_length]; exact j.isLt⟩)) =
      P.vertices.get ⟨j.val + 1, by rw [P.vertices_length]; omega⟩ :=
  (P.edge_step _).2.2.2.symm

private theorem glue_label_identify_right (d : DR) :
    glue_vertex_label BL BR (glueIdentify BL BR (.inr d)) =
      glue_right_label BL BR (dartTailVertex BR.map d) := by
  by_cases hd : d ∈ BR.leftPath.darts
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    let i : Fin (s + 1) := ⟨j.val, by
      have hjl : j.val < s := by simpa only [BR.leftPath.darts_length] using j.isLt
      omega⟩
    have hi : i.val < s := by have := j.isLt; simpa only [BR.leftPath.darts_length] using this
    have hr : d = glueRightSeamVertexDart BR i := by
      rw [glueRightSeamVertexDart, dite_eq_left hi]; exact hj.symm
    have hl : BL.map.toCombinatorialMap.edgeInv (glueLeftSeamVertexDart BL i) ∉
        BL.rightPath.darts := by
      have ht := (BL.rightPath.edge_step ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩).2.1
      rw [glueLeftSeamVertexDart, dite_eq_left hi]
      intro hm
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hm
      exact (BL.map.tail_iff _ (BL.noMissingDarts _)).mp ht
        (hk ▸ (BL.rightPath.edge_step k).2.1)
    rw [hr, ← glueIdentify_seamVertexDart BL BR i,
      glueIdentify_inl_kept BL BR ⟨_, hl⟩]
    exact (glue_right_label_seam BL BR i).symm
  · rw [glueIdentify_inr_kept BL BR ⟨d, hd⟩]
    rfl

private theorem glue_label_identify_left (d : DL) :
    glue_vertex_label BL BR (glueIdentify BL BR (.inl d)) =
      .inl (dartTailVertex BL.map d) := by
  by_cases hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    let k : Fin s := ⟨j.val, by simpa only [BL.rightPath.darts_length] using j.isLt⟩
    let i : Fin (s + 1) := ⟨j.val + 1, by have := k.isLt; dsimp [k] at this; omega⟩
    have he : d = BL.map.toCombinatorialMap.edgeInv
        (BL.rightPath.darts.get ⟨k.val, by rw [BL.rightPath.darts_length]; exact k.isLt⟩) := by
      rw [hj]; exact (BL.map.toCombinatorialMap.edgeInv_invol d).symm
    have h := congrArg (glueEdgeInv BL BR) (glueIdentify_seam BL BR k)
    simp only [glueEdgeInv_identify, Sum.map_inl, Sum.map_inr] at h
    rw [he, h, glue_label_identify_right]
    have hl : dartTailVertex BL.map (BL.map.toCombinatorialMap.edgeInv
        (BL.rightPath.darts.get ⟨k.val, by rw [BL.rightPath.darts_length]; exact k.isLt⟩)) =
        glue_lv BL i := by
      change _ = dartTailVertex BL.map (glueLeftSeamVertexDart BL i)
      rw [glue_path_head_index BL.rightPath k, glueLeftSeamVertexDart_vertex]
    have hr : dartTailVertex BR.map (BR.map.toCombinatorialMap.edgeInv
        (BR.leftPath.darts.get ⟨k.val, by rw [BR.leftPath.darts_length]; exact k.isLt⟩)) =
        glue_rv BR i := by
      change _ = dartTailVertex BR.map (glueRightSeamVertexDart BR i)
      rw [glue_path_head_index BR.leftPath k, glueRightSeamVertexDart_vertex]
    rw [hl, hr, glue_right_label_seam]
  · rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩]
    rfl

private theorem glue_path_tail_first {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (hn : 0 < n) :
    dartTailVertex M (P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩) = a :=
  (P.edge_step _).2.2.1.symm.trans P.start_vertex

private theorem glue_path_head_last {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (hn : 0 < n) :
    dartTailVertex M (M.toCombinatorialMap.edgeInv
      (P.darts.get ⟨n - 1, by rw [P.darts_length]; omega⟩)) = b := by
  rw [glue_path_head_index P ⟨n - 1, by omega⟩]
  have he : n - 1 + 1 = n := by omega
  simpa only [he] using P.end_vertex

private theorem glue_path_adjacent {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (j : ℕ) (hj : j + 1 < n) :
    dartTailVertex M (P.darts.get ⟨j + 1, by rw [P.darts_length]; exact hj⟩) =
      dartTailVertex M (M.toCombinatorialMap.edgeInv
        (P.darts.get ⟨j, by rw [P.darts_length]; omega⟩)) := by
  rw [glue_path_head_index P ⟨j, by omega⟩]
  exact (P.edge_step _).2.2.1.symm

private theorem glue_label_source :
    glue_right_label BL BR BR.source = .inl BL.source := by
  have hl : glue_lv BL ⟨0, by omega⟩ = BL.source := by
    change dartTailVertex BL.map (glueLeftSeamVertexDart BL _) = _
    rw [glueLeftSeamVertexDart_vertex]
    exact BL.rightPath.start_vertex
  have hr : glue_rv BR ⟨0, by omega⟩ = BR.source := by
    change dartTailVertex BR.map (glueRightSeamVertexDart BR _) = _
    rw [glueRightSeamVertexDart_vertex]
    exact BR.leftPath.start_vertex
  rw [← hr, glue_right_label_seam, hl]

private theorem glue_label_sink :
    glue_right_label BL BR BR.sink = .inl BL.sink := by
  have hl : glue_lv BL ⟨s, by omega⟩ = BL.sink := by
    change dartTailVertex BL.map (glueLeftSeamVertexDart BL _) = _
    rw [glueLeftSeamVertexDart_vertex]
    exact BL.rightPath.end_vertex
  have hr : glue_rv BR ⟨s, by omega⟩ = BR.sink := by
    change dartTailVertex BR.map (glueRightSeamVertexDart BR _) = _
    rw [glueRightSeamVertexDart_vertex]
    exact BR.leftPath.end_vertex
  rw [← hr, glue_right_label_seam, hl]

private theorem glue_label_outer_index (i : ℕ) (hi : i < ℓ + r) :
    glue_vertex_label BL BR ((glueCombinatorialMap BL BR).faceSucc
      ((glueOuterWord BL BR).letters[i]'(by rw [glue_outer_length]; exact hi))) =
    glue_vertex_label BL BR (glueEdgeInv BL BR
      ((glueOuterWord BL BR).letters[i]'(by rw [glue_outer_length]; exact hi))) := by
  have hl := BL.left_length_pos
  have hr := BR.right_length_pos
  rw [glue_outer_face_index BL BR i hi]
  by_cases hil : i < ℓ
  · rw [glue_outer_get_left BL BR i hil, glueEdgeInv_identify]
    simp only [Sum.map_inl]
    rw [glue_label_identify_left]
    by_cases hn : i + 1 < ℓ
    · simp only [Nat.mod_eq_of_lt (show i + 1 < ℓ + r by omega)]
      rw [glue_outer_get_left BL BR (i + 1) hn,
        glue_label_identify_left, glue_path_adjacent BL.leftPath i hn]
    · have he : i + 1 = ℓ + 0 := by omega
      have he' : i = ℓ - 1 := by omega
      simp only [he]
      simp only [Nat.mod_eq_of_lt (show ℓ + 0 < ℓ + r by omega)]
      simp only [he']
      rw [glue_outer_get_right BL BR 0 (by omega), glue_label_identify_right]
      simp only [Nat.sub_zero]
      rw [glue_path_head_last BR.rightPath (by omega),
        glue_path_head_last BL.leftPath (by omega), glue_label_sink]
  · let j := i - ℓ
    have hj : j < r := by dsimp [j]; omega
    have he : i = ℓ + j := by dsimp [j]; omega
    simp only [he]
    rw [glue_outer_get_right BL BR j hj, glueEdgeInv_identify]
    simp only [Sum.map_inr, BR.map.toCombinatorialMap.edgeInv_invol]
    rw [glue_label_identify_right]
    by_cases hn : j + 1 < r
    · have hm : (ℓ + j + 1) % (ℓ + r) = ℓ + (j + 1) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp only [hm]
      rw [glue_outer_get_right BL BR (j + 1) (by omega), glue_label_identify_right]
      have ha : r - 1 - j = (r - 1 - (j + 1)) + 1 := by omega
      have hv := glue_path_adjacent BR.rightPath (r - 1 - (j + 1)) (by omega)
      simp only [ha]
      exact congrArg (glue_right_label BL BR) hv.symm
    · have hm : (ℓ + j + 1) % (ℓ + r) = 0 := by
        have h : ℓ + j + 1 = ℓ + r := by omega
        rw [h, Nat.mod_self]
      have hz : r - 1 - j = 0 := by omega
      simp only [hm, hz]
      rw [glue_outer_get_left BL BR 0 (by omega), glue_label_identify_left,
        glue_path_tail_first BL.leftPath (by omega),
        glue_path_tail_first BR.rightPath (by omega), glue_label_source]

private theorem glue_label_rot (a : GlueDart BL BR) :
    glue_vertex_label BL BR a =
      glue_vertex_label BL BR ((glueCombinatorialMap BL BR).rot a) := by
  have hc := (glueVertexCorner_iff_rot BL BR a _).mpr rfl
  rcases hc with ⟨d, _, ha, hb⟩ | ⟨d, _, ha, hb⟩ | ⟨d, hd, ha, hb⟩
  · rw [hb, ha, glue_label_identify_left, glue_label_identify_left]
    congr 1
    apply Quotient.sound
    apply Equiv.Perm.sameCycle_apply_left.mp
    rw [glue_rot_faceSucc]
  · rw [hb, ha, glue_label_identify_right, glue_label_identify_right]
    congr 1
    apply Quotient.sound
    apply Equiv.Perm.sameCycle_apply_left.mp
    rw [glue_rot_faceSucc]
  · rw [hb, ha]
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    have hi : i.val < ℓ + r := by simpa only [glue_outer_length] using i.isLt
    have hf := (glue_isOuterCycle BL BR).2.2 _ (List.get_mem _ i)
    rw [glueDirectedMap_toCombinatorialMap] at hf
    rw [← hf]
    exact glue_label_outer_index BL BR i.val hi

private theorem glue_label_sameCycle (a b : GlueDart BL BR)
    (h : (glueCombinatorialMap BL BR).rot.SameCycle a b) :
    glue_vertex_label BL BR a = glue_vertex_label BL BR b := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (glue_label_rot BL BR _)

private noncomputable def glue_vertex_recover :
    CombinatorialMap.VertexQuotient (glueCombinatorialMap BL BR) →
      MapVertex BL.map ⊕ MapVertex BR.map :=
  Quotient.lift (glue_vertex_label BL BR)
    (fun a b h => glue_label_sameCycle BL BR a b h)

private theorem glue_recover_left (v : MapVertex BL.map) :
    glue_vertex_recover BL BR (glueVertexMap BL BR (.inl v)) = .inl v := by
  refine Quotient.inductionOn v ?_
  intro d
  exact glue_label_identify_left BL BR d

private theorem glue_recover_right (v : MapVertex BR.map) :
    glue_vertex_recover BL BR (glueVertexMap BL BR (.inr v)) =
      glue_right_label BL BR v := by
  refine Quotient.inductionOn v ?_
  intro d
  exact glue_label_identify_right BL BR d

private theorem glue_right_label_injective : Function.Injective (glue_right_label BL BR) := by
  intro v w h
  unfold glue_right_label at h
  split at h <;> split at h
  · rename_i hv hw
    have hi : hv.choose = hw.choose :=
      (glueLeftSeamVertexDart_sameCycle_iff BL _ _).mp
        (Quotient.exact (Sum.inl.inj h))
    exact hv.choose_spec.trans ((congrArg (glue_rv BR) hi).trans hw.choose_spec.symm)
  · cases h
  · cases h
  · exact Sum.inr.inj h



theorem glueVertexMap_left_injective :
    Function.Injective (fun v : MapVertex BL.map => glueVertexMap BL BR (.inl v)) := by
  intro v w h
  have he := congrArg (glue_vertex_recover BL BR) h
  rw [glue_recover_left, glue_recover_left] at he
  exact Sum.inl.inj he



theorem glueVertexMap_right_injective :
    Function.Injective (fun v : MapVertex BR.map => glueVertexMap BL BR (.inr v)) := by
  intro v w h
  apply glue_right_label_injective BL BR
  have he := congrArg (glue_vertex_recover BL BR) h
  rwa [glue_recover_right, glue_recover_right] at he



theorem glueVertexMap_cross_iff (v : MapVertex BL.map) (w : MapVertex BR.map) :
    glueVertexMap BL BR (.inl v) = glueVertexMap BL BR (.inr w) ↔
      ∃ i : Fin (s + 1),
        v = dartTailVertex BL.map (glueLeftSeamVertexDart BL i) ∧
        w = dartTailVertex BR.map (glueRightSeamVertexDart BR i) := by
  constructor
  · intro h
    have he := congrArg (glue_vertex_recover BL BR) h
    rw [glue_recover_left, glue_recover_right] at he
    unfold glue_right_label at he
    split at he
    · rename_i hw
      exact ⟨hw.choose, Sum.inl.inj he, hw.choose_spec⟩
    · cases he
  · rintro ⟨i, rfl, rfl⟩
    exact glueVertexMap_seam BL BR i



theorem numVertices_glueCombinatorialMap :
    (glueCombinatorialMap BL BR).numVertices + (s + 1) =
      BL.map.toCombinatorialMap.numVertices + BR.map.toCombinatorialMap.numVertices := by
  classical
  let seam : MapVertex BR.map → Prop := fun v =>
    ∃ i : Fin (s + 1), v = dartTailVertex BR.map (glueRightSeamVertexDart BR i)
  let A := MapVertex BL.map ⊕ {v : MapVertex BR.map // ¬ seam v}
  let f : A → CombinatorialMap.VertexQuotient (glueCombinatorialMap BL BR) :=
    fun v => glueVertexMap BL BR (v.map id Subtype.val)
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      cases v with
      | inl v =>
        cases w with
        | inl w => exact congrArg Sum.inl (glueVertexMap_left_injective BL BR h)
        | inr w =>
          obtain ⟨i, _, hi⟩ := (glueVertexMap_cross_iff BL BR v w.val).mp h
          exact False.elim (w.property ⟨i, hi⟩)
      | inr v =>
        cases w with
        | inl w =>
          obtain ⟨i, _, hi⟩ := (glueVertexMap_cross_iff BL BR w v.val).mp h.symm
          exact False.elim (v.property ⟨i, hi⟩)
        | inr w =>
          exact congrArg Sum.inr (Subtype.ext (glueVertexMap_right_injective BL BR h))
    · intro w
      obtain ⟨v, hv⟩ := glueVertexMap_surjective BL BR w
      cases v with
      | inl v => exact ⟨.inl v, hv⟩
      | inr v =>
        by_cases hs : seam v
        · obtain ⟨i, rfl⟩ := hs
          exact ⟨.inl (dartTailVertex BL.map (glueLeftSeamVertexDart BL i)),
            (glueVertexMap_seam BL BR i).trans hv⟩
        · exact ⟨.inr ⟨v, hs⟩, hv⟩
  have hc := Fintype.card_of_bijective hf
  have hs : Fintype.card {v : MapVertex BR.map // seam v} = s + 1 :=
    glue_right_seam_vertex_card BR
  have hbound := Fintype.card_subtype_le seam
  change Fintype.card (_ ⊕ _) = (glueCombinatorialMap BL BR).numVertices at hc
  rw [Fintype.card_sum, Fintype.card_subtype_compl, hs] at hc
  rw [hs] at hbound
  change s + 1 ≤ BR.map.toCombinatorialMap.numVertices at hbound
  change BL.map.toCombinatorialMap.numVertices +
    (BR.map.toCombinatorialMap.numVertices - (s + 1)) =
      (glueCombinatorialMap BL BR).numVertices at hc
  omega



theorem eulerChar_glueCombinatorialMap :
    (glueCombinatorialMap BL BR).eulerChar = 2 := by
  have hv := numVertices_glueCombinatorialMap BL BR
  have he := numEdges_glueCombinatorialMap BL BR
  have hf := numFaces_glueCombinatorialMap BL BR
  have hl := BL.planar.2
  have hr := BR.planar.2
  unfold CombinatorialMap.eulerChar at hl hr ⊢
  omega



theorem glue_isPlanar : (glueCombinatorialMap BL BR).IsPlanar :=
  ⟨glue_isConnected BL BR, eulerChar_glueCombinatorialMap BL BR⟩



@[expose] noncomputable def glueDirectedVertexMap :
    MapVertex BL.map ⊕ MapVertex BR.map → MapVertex (glueDirectedMap BL BR)
  | .inl v => Quotient.lift
      (fun d => dartTailVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inl d)))
      (by
        intro d e h
        apply Quotient.sound
        change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _
        rw [glueDirectedMap_toCombinatorialMap]
        exact glueIdentify_left_sameCycle BL BR d e h) v
  | .inr v => Quotient.lift
      (fun d => dartTailVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inr d)))
      (by
        intro d e h
        apply Quotient.sound
        change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _
        rw [glueDirectedMap_toCombinatorialMap]
        exact glueIdentify_right_sameCycle BL BR d e h) v

private theorem glue_directed_vertex_eq (v w : MapVertex BL.map ⊕ MapVertex BR.map) :
    glueDirectedVertexMap BL BR v = glueDirectedVertexMap BL BR w ↔
      glueVertexMap BL BR v = glueVertexMap BL BR w := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
    | inr w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
  | inr v =>
    cases w with
    | inl w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
    | inr w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl

private theorem glue_directed_left_injective :
    Function.Injective (fun v : MapVertex BL.map => glueDirectedVertexMap BL BR (.inl v)) :=
  fun _ _ h => glueVertexMap_left_injective BL BR ((glue_directed_vertex_eq BL BR _ _).mp h)

private theorem glue_directed_right_injective :
    Function.Injective (fun v : MapVertex BR.map => glueDirectedVertexMap BL BR (.inr v)) :=
  fun _ _ h => glueVertexMap_right_injective BL BR ((glue_directed_vertex_eq BL BR _ _).mp h)

private theorem glue_directed_surjective : Function.Surjective (glueDirectedVertexMap BL BR) := by
  intro v
  refine Quotient.inductionOn v ?_
  intro a
  obtain ⟨d | d, rfl⟩ := glueIdentify_surjective BL BR a
  · exact ⟨.inl (dartTailVertex BL.map d), rfl⟩
  · exact ⟨.inr (dartTailVertex BR.map d), rfl⟩

private theorem glue_left_tail_retained (d : DL) (ht : BL.map.tail d) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
  exact (BL.map.tail_iff d (BL.noMissingDarts d)).mp ht
    (hj ▸ (BL.rightPath.edge_step j).2.1)

private theorem glue_tail_identify_left (d : DL) (ht : BL.map.tail d) :
    (glueDirectedMap BL BR).tail (glueIdentify BL BR (.inl d)) := by
  rw [glueIdentify_inl_kept BL BR ⟨d, glue_left_tail_retained BL d ht⟩,
    glueDirectedMap_tail]
  exact ht

private theorem glue_tail_identify_right (d : DR) (ht : BR.map.tail d) :
    (glueDirectedMap BL BR).tail (glueIdentify BL BR (.inr d)) := by
  by_cases hd : d ∈ BR.leftPath.darts
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    let k : Fin s := ⟨j.val, by simpa only [BR.leftPath.darts_length] using j.isLt⟩
    have h := glueIdentify_seam BL BR k
    have he : BR.leftPath.darts.get
        ⟨k.val, by rw [BR.leftPath.darts_length]; exact k.isLt⟩ = d := hj
    rw [← he, ← h]
    exact glue_tail_identify_left BL BR _ (BL.rightPath.edge_step _).2.1
  · rw [glueIdentify_inr_kept BL BR ⟨d, hd⟩, glueDirectedMap_tail]
    exact ht

private theorem glue_tail_vertex_left (d : DL) :
    dartTailVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inl d)) =
      glueDirectedVertexMap BL BR (.inl (dartTailVertex BL.map d)) := rfl

private theorem glue_tail_vertex_right (d : DR) :
    dartTailVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inr d)) =
      glueDirectedVertexMap BL BR (.inr (dartTailVertex BR.map d)) := rfl

private theorem glue_head_vertex_left (d : DL) :
    dartHeadVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inl d)) =
      glueDirectedVertexMap BL BR (.inl (dartHeadVertex BL.map d)) := by
  change dartTailVertex (glueDirectedMap BL BR)
    ((glueDirectedMap BL BR).toCombinatorialMap.edgeInv (glueIdentify BL BR (.inl d))) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private theorem glue_head_vertex_right (d : DR) :
    dartHeadVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inr d)) =
      glueDirectedVertexMap BL BR (.inr (dartHeadVertex BR.map d)) := by
  change dartTailVertex (glueDirectedMap BL BR)
    ((glueDirectedMap BL BR).toCombinatorialMap.edgeInv (glueIdentify BL BR (.inr d))) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl




theorem glue_directedStep_iff (v w : MapVertex (glueDirectedMap BL BR)) :
    (glueDirectedMap BL BR).directedStep v w ↔
      (∃ a b : MapVertex BL.map, BL.map.directedStep a b ∧
        glueDirectedVertexMap BL BR (.inl a) = v ∧ glueDirectedVertexMap BL BR (.inl b) = w) ∨
      (∃ a b : MapVertex BR.map, BR.map.directedStep a b ∧
        glueDirectedVertexMap BL BR (.inr a) = v ∧ glueDirectedVertexMap BL BR (.inr b) = w) := by
  constructor
  · rintro ⟨d, _, ht, hv, hw⟩
    cases d with
    | inl d =>
      have htail : BL.map.tail d.val := (glueDirectedMap_tail BL BR _).mp ht
      refine Or.inl ⟨dartTailVertex BL.map d.val, dartHeadVertex BL.map d.val,
        ⟨d.val, BL.noMissingDarts _, htail, rfl, rfl⟩, ?_, ?_⟩
      · rw [← glue_tail_vertex_left, glueIdentify_inl_kept BL BR d]; exact hv
      · rw [← glue_head_vertex_left, glueIdentify_inl_kept BL BR d]; exact hw
    | inr d =>
      have htail : BR.map.tail d.val := (glueDirectedMap_tail BL BR _).mp ht
      refine Or.inr ⟨dartTailVertex BR.map d.val, dartHeadVertex BR.map d.val,
        ⟨d.val, BR.noMissingDarts _, htail, rfl, rfl⟩, ?_, ?_⟩
      · rw [← glue_tail_vertex_right, glueIdentify_inr_kept BL BR d]; exact hv
      · rw [← glue_head_vertex_right, glueIdentify_inr_kept BL BR d]; exact hw
  · rintro (⟨a, b, ⟨d, _, ht, rfl, rfl⟩, rfl, rfl⟩ |
      ⟨a, b, ⟨d, _, ht, rfl, rfl⟩, rfl, rfl⟩)
    · exact ⟨glueIdentify BL BR (.inl d), glueDirectedMap_noMissing BL BR _,
        glue_tail_identify_left BL BR d ht, glue_tail_vertex_left BL BR d,
        glue_head_vertex_left BL BR d⟩
    · exact ⟨glueIdentify BL BR (.inr d), glueDirectedMap_noMissing BL BR _,
        glue_tail_identify_right BL BR d ht, glue_tail_vertex_right BL BR d,
        glue_head_vertex_right BL BR d⟩

private theorem glue_source_pair :
    glueDirectedVertexMap BL BR (.inl BL.source) = glueDirectedVertexMap BL BR (.inr BR.source) := by
  have h := glueVertexMap_seam BL BR ⟨0, by omega⟩
  rw [glueLeftSeamVertexDart_vertex, glueRightSeamVertexDart_vertex,
    BL.rightPath.start_vertex, BR.leftPath.start_vertex] at h
  exact (glue_directed_vertex_eq BL BR _ _).mpr h

private theorem glue_sink_pair :
    glueDirectedVertexMap BL BR (.inl BL.sink) = glueDirectedVertexMap BL BR (.inr BR.sink) := by
  have h := glueVertexMap_seam BL BR ⟨s, by omega⟩
  rw [glueLeftSeamVertexDart_vertex, glueRightSeamVertexDart_vertex,
    BL.rightPath.end_vertex, BR.leftPath.end_vertex] at h
  exact (glue_directed_vertex_eq BL BR _ _).mpr h



theorem glue_isSource : ¬ ∃ u, (glueDirectedMap BL BR).directedStep u
    (glueDirectedVertexMap BL BR (.inl BL.source)) := by
  rintro ⟨u, hu⟩
  rcases (glue_directedStep_iff BL BR _ _).mp hu with ⟨a, b, hab, _, hb⟩ |
    ⟨a, b, hab, _, hb⟩
  · have he := glue_directed_left_injective BL BR hb
    exact BL.isSource ⟨a, he ▸ hab⟩
  · rw [glue_source_pair] at hb
    have he := glue_directed_right_injective BL BR hb
    exact BR.isSource ⟨a, he ▸ hab⟩



theorem glue_isSink : ¬ ∃ w, (glueDirectedMap BL BR).directedStep
    (glueDirectedVertexMap BL BR (.inl BL.sink)) w := by
  rintro ⟨w, hw⟩
  rcases (glue_directedStep_iff BL BR _ _).mp hw with ⟨a, b, hab, ha, _⟩ |
    ⟨a, b, hab, ha, _⟩
  · have he := glue_directed_left_injective BL BR ha
    exact BL.isSink ⟨b, he ▸ hab⟩
  · rw [glue_sink_pair] at ha
    have he := glue_directed_right_injective BL BR ha
    exact BR.isSink ⟨b, he ▸ hab⟩



theorem glue_source_unique (v : MapVertex (glueDirectedMap BL BR))
    (hv : ¬ ∃ u, (glueDirectedMap BL BR).directedStep u v) :
    v = glueDirectedVertexMap BL BR (.inl BL.source) := by
  obtain ⟨a | a, rfl⟩ := glue_directed_surjective BL BR v
  · have he := BL.source_unique a (by
      rintro ⟨b, hb⟩
      exact hv ⟨_, (glue_directedStep_iff BL BR _ _).mpr
        (Or.inl ⟨b, a, hb, rfl, rfl⟩)⟩)
    rw [he]
  · have he := BR.source_unique a (by
      rintro ⟨b, hb⟩
      exact hv ⟨_, (glue_directedStep_iff BL BR _ _).mpr
        (Or.inr ⟨b, a, hb, rfl, rfl⟩)⟩)
    rw [he, ← glue_source_pair]



theorem glue_sink_unique (v : MapVertex (glueDirectedMap BL BR))
    (hv : ¬ ∃ w, (glueDirectedMap BL BR).directedStep v w) :
    v = glueDirectedVertexMap BL BR (.inl BL.sink) := by
  obtain ⟨a | a, rfl⟩ := glue_directed_surjective BL BR v
  · have he := BL.sink_unique a (by
      rintro ⟨b, hb⟩
      exact hv ⟨_, (glue_directedStep_iff BL BR _ _).mpr
        (Or.inl ⟨a, b, hb, rfl, rfl⟩)⟩)
    rw [he]
  · have he := BR.sink_unique a (by
      rintro ⟨b, hb⟩
      exact hv ⟨_, (glue_directedStep_iff BL BR _ _).mpr
        (Or.inr ⟨a, b, hb, rfl, rfl⟩)⟩)
    rw [he, ← glue_sink_pair]



@[expose] noncomputable def glueMapSimpleDirectedDartPath
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    {a b : MapVertex M} {c d : MapVertex N} {n : ℕ}
    (f : MapVertex M → MapVertex N) (g : D → E) (hf : Function.Injective f)
    (hm : ∀ x, ¬ N.missing (g x)) (ht : ∀ x, M.tail x → N.tail (g x))
    (hv : ∀ x, dartTailVertex N (g x) = f (dartTailVertex M x))
    (hh : ∀ x, dartHeadVertex N (g x) = f (dartHeadVertex M x))
    (ha : f a = c) (hb : f b = d) (P : SimpleDirectedDartPath M a b n) :
    SimpleDirectedDartPath N c d n where
  darts := P.darts.map g
  vertices := P.vertices.map f
  darts_length := by rw [List.length_map, P.darts_length]
  vertices_length := by rw [List.length_map, P.vertices_length]
  vertices_nodup := P.vertices_nodup.map hf
  start_vertex := by
    simp only [List.get_eq_getElem, List.getElem_map]
    exact (congrArg f P.start_vertex).trans ha
  end_vertex := by
    simp only [List.get_eq_getElem, List.getElem_map]
    exact (congrArg f P.end_vertex).trans hb
  edge_step := by
    intro i
    let j : Fin P.darts.length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    have hs := P.edge_step j
    simp only [List.get_eq_getElem] at hs
    simp only [List.get_eq_getElem, List.getElem_map]
    exact ⟨hm _, ht _ hs.2.1, (congrArg f hs.2.2.1).trans (hv _).symm,
      (congrArg f hs.2.2.2).trans (hh _).symm⟩



@[expose] noncomputable def glueLeftPath :
    SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) ℓ :=
  glueMapSimpleDirectedDartPath (fun v => glueDirectedVertexMap BL BR (.inl v))
    (fun d => glueIdentify BL BR (.inl d)) (by exact glue_directed_left_injective BL BR)
    (fun _ => glueDirectedMap_noMissing BL BR _) (by exact glue_tail_identify_left BL BR)
    (by exact glue_tail_vertex_left BL BR) (by exact glue_head_vertex_left BL BR) rfl rfl BL.leftPath



@[expose] noncomputable def glueRightPath :
    SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) r :=
  glueMapSimpleDirectedDartPath (fun v => glueDirectedVertexMap BL BR (.inr v))
    (fun d => glueIdentify BL BR (.inr d)) (by exact glue_directed_right_injective BL BR)
    (fun _ => glueDirectedMap_noMissing BL BR _) (by exact glue_tail_identify_right BL BR)
    (by exact glue_tail_vertex_right BL BR) (by exact glue_head_vertex_right BL BR)
    (by exact (glue_source_pair BL BR).symm) (by exact (glue_sink_pair BL BR).symm) BR.rightPath

private theorem glue_right_outer_arc :
    (glueRightPath BL BR).darts.reverse.map (glueDirectedMap BL BR).toCombinatorialMap.edgeInv =
      BR.rightPath.darts.reverse.map
        (fun d => glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))) := by
  change (BR.rightPath.darts.map (fun d => glueIdentify BL BR (.inr d))).reverse.map _ = _
  simp only [List.map_reverse, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d _
  change (glueDirectedMap BL BR).toCombinatorialMap.edgeInv
    (glueIdentify BL BR (.inr d)) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private theorem glue_outer_left_tail {a : GlueDart BL BR}
    (ha : a ∈ (glueLeftPath BL BR).darts) : (glueDirectedMap BL BR).tail a := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ha
  exact ((glueLeftPath BL BR).edge_step j).2.1

private theorem glue_outer_right_nontail {a : GlueDart BL BR}
    (ha : a ∈ (glueRightPath BL BR).darts.reverse.map
      (glueDirectedMap BL BR).toCombinatorialMap.edgeInv) :
    ¬ (glueDirectedMap BL BR).tail a := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_reverse.mp hd)
  exact ((glueDirectedMap BL BR).tail_iff _ (glueDirectedMap_noMissing BL BR _)).mp
    ((glueRightPath BL BR).edge_step j).2.1



theorem glue_outerSplit :
    FourArcsWitness (glueDirectedMap BL BR) (glueOuterWord BL BR)
      (glueLeftPath BL BR).darts []
      ((glueRightPath BL BR).darts.reverse.map
        (glueDirectedMap BL BR).toCombinatorialMap.edgeInv) [] := by
  have he : (glueOuterWord BL BR).letters = (glueLeftPath BL BR).darts ++
      (glueRightPath BL BR).darts.reverse.map
        (glueDirectedMap BL BR).toCombinatorialMap.edgeInv := by
    rw [glueOuterWord_letters, glue_right_outer_arc]
    rfl
  have hm (a : GlueDart BL BR) : (glueDirectedMap BL BR).IsOuter a ↔
      a ∈ (glueLeftPath BL BR).darts ∨
        a ∈ (glueRightPath BL BR).darts.reverse.map
          (glueDirectedMap BL BR).toCombinatorialMap.edgeInv := by
    constructor
    · intro ho
      have hmem := (glue_isOuterCycle BL BR).2.1 a ho
      rwa [he, List.mem_append] at hmem
    · intro ha
      apply (glue_isOuterCycle BL BR).1 a
      rwa [he, List.mem_append]
  refine ⟨glue_isOuterCycle BL BR, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_nil, List.nil_append, he] using
      List.IsRotated.refl (glueOuterWord BL BR).letters
  · intro a
    constructor
    · intro ha
      exact ⟨glueDirectedMap_noMissing BL BR a, glue_outer_left_tail BL BR ha,
        (hm a).mpr (Or.inl ha)⟩
    · rintro ⟨_, ht, ho⟩
      rcases (hm a).mp ho with ha | ha
      · exact ha
      · exact False.elim (glue_outer_right_nontail BL BR ha ht)
  · intro a
    constructor
    · intro ha
      exact ⟨glueDirectedMap_noMissing BL BR a, glue_outer_right_nontail BL BR ha,
        (hm a).mpr (Or.inr ha)⟩
    · rintro ⟨_, ht, ho⟩
      rcases (hm a).mp ho with ha | ha
      · exact False.elim (ht (glue_outer_left_tail BL BR ha))
      · exact ha
  · intro a ha
    exact False.elim (List.not_mem_nil ha)
  · intro a ha
    exact False.elim (List.not_mem_nil ha)

end DirectedDistances.PlanarMap
