/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLCutVertexFace
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12
public import DirectedDistances.PlanarMap.PermutationSplitCount

/-! # Vertex-avoiding drawing paths toward cut vertices

Helpers toward Proposition 5.16. The repeated-vertex cut condition is proved
to the sole coordinator; this is not a paper-completion claim. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: an edge with both endpoints away from
a vertex misses that vertex on its entire closed arc. -/
theorem pos_not_mem_arc_image_of_endpoints_ne (d : D) (v : V)
    (hs : vert d ≠ v) (ht : vert (flip d) ≠ v) :
    P.pos v ∉ (P.arc d).image := by
  intro hv
  have hstart : P.pos v ≠ (P.arc d).start := by
    rw [P.arc_start]
    exact fun h => hs (P.pos_injective h).symm
  have hfinish : P.pos v ≠ (P.arc d).finish := by
    rw [P.arc_finish]
    exact fun h => ht (P.pos_injective h).symm
  exact P.interior_avoids_vertices d v
    ⟨hv, by simp only [mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨hstart, hfinish⟩⟩

/-- Helper toward Proposition 5.16: a chain of rotation and reversal steps
whose endpoints avoid a vertex yields an actual polyline avoiding its drawing
point, including all intermediate arc points and bends. -/
theorem exists_polyline_of_vertex_avoiding_eqvGen (v : V) (d e : D)
    (hd : vert d ≠ v) (he : vert e ≠ v)
    (h : Relation.EqvGen
      (fun x y => vert x ≠ v ∧ vert y ≠ v ∧ (rot x = y ∨ flip x = y)) d e) :
    ∃ c : Polyline, c.start = P.pos (vert d) ∧ c.finish = P.pos (vert e) ∧
      c.image ⊆ P.image ∧ P.pos v ∉ c.image := by
  have hconstant (x : D) (hx : vert x ≠ v) :
      ∃ c : Polyline, c.start = P.pos (vert x) ∧ c.finish = P.pos (vert x) ∧
        c.image ⊆ P.image ∧ P.pos v ∉ c.image := by
    refine ⟨Polyline.ofHead (P.pos (vert x)) [], rfl, rfl, ?_, ?_⟩
    · intro z hz
      have hz' : z = P.pos (vert x) := by
        simpa [Polyline.image, Polyline.ofHead, Polyline.start] using hz
      exact Or.inl ⟨vert x, hz'.symm⟩
    · intro hz
      have hz' : P.pos v = P.pos (vert x) := by
        simpa [Polyline.image, Polyline.ofHead, Polyline.start] using hz
      exact hx (P.pos_injective hz').symm
  have hpres {x y : D}
      (hxy : Relation.EqvGen
        (fun a b => vert a ≠ v ∧ vert b ≠ v ∧ (rot a = b ∨ flip a = b)) x y) :
      vert x ≠ v ↔ vert y ≠ v := by
    induction hxy with
    | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  induction h with
  | rel x y hstep =>
    obtain ⟨hx, hy, hxy⟩ := hstep
    rcases hxy with rfl | rfl
    · simpa only [P.vert_rotation] using hconstant x hx
    · exact ⟨P.arc x, P.arc_start x, P.arc_finish x,
        fun z hz => Or.inr ⟨x, hz⟩,
        P.pos_not_mem_arc_image_of_endpoints_ne x v hx hy⟩
  | refl x => exact hconstant x hd
  | symm x y _ ih =>
    obtain ⟨c, hcs, hcf, hci, hcv⟩ := ih he hd
    refine ⟨c.reverse, (Polyline.start_reverse c).trans hcf,
      (Polyline.finish_reverse c).trans hcs, ?_, ?_⟩
    · rw [Polyline.image_reverse_transfer]
      exact hci
    · rw [Polyline.image_reverse_transfer]
      exact hcv
  | trans x y z hxy hyz ih₁ ih₂ =>
    have hy : vert y ≠ v := (hpres hxy).mp hd
    obtain ⟨c, hcs, hcf, hci, hcv⟩ := ih₁ hd hy
    obtain ⟨q, hqs, hqf, hqi, hqv⟩ := ih₂ hy he
    have hjoin : c.finish = q.start := hcf.trans hqs.symm
    refine ⟨Polyline.boundaryConcat c q,
      (Polyline.start_boundaryConcat c q).trans hcs,
      (Polyline.finish_boundaryConcat_of_join c q hjoin).trans hqf, ?_, ?_⟩
    · rw [Polyline.image_boundaryConcat c q hjoin]
      exact union_subset hci hqi
    · rw [Polyline.image_boundaryConcat c q hjoin]
      exact fun h => h.elim hcv hqv

end PLDrawing

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.16: if deletion leaves all surviving darts
connected in a loopless map, changing rotation only at the deleted vertex
still leaves the whole map connected. Every deleted dart reaches a surviving
dart by its own geometric edge. -/
theorem isConnected_of_not_isCutVertex_of_rotation_eq
    (M N : CombinatorialMap D) (v : VertexQuotient M)
    (hflip : N.edgeInv = M.edgeInv)
    (hrot : ∀ d, vertexClass M d ≠ v → N.rot d = M.rot d)
    (hloop : ∀ d, vertexClass M d ≠ vertexClass M (M.edgeInv d))
    (hnot : ¬ M.isCutVertex v) : N.IsConnected := by
  let R : D → D → Prop := fun x y => N.rot x = y ∨ N.edgeInv x = y
  have hsurvive (d : D) :
      ∃ e : D, vertexClass M e ≠ v ∧ Relation.EqvGen R d e := by
    by_cases hd : vertexClass M d ≠ v
    · exact ⟨d, hd, Relation.EqvGen.refl d⟩
    · have hdv : vertexClass M d = v := not_ne_iff.mp hd
      refine ⟨M.edgeInv d, ?_, Relation.EqvGen.rel _ _ (Or.inr ?_)⟩
      · intro he
        exact hloop d (hdv.trans he.symm)
      · exact congrArg (fun σ : Equiv.Perm D => σ d) hflip
  apply N.isConnected_of_eqvGen
  intro d e
  obtain ⟨x, hx, hdx⟩ := hsurvive d
  obtain ⟨y, hy, hey⟩ := hsurvive e
  have hxy : Relation.EqvGen (M.vertexAvoidingStep v) x y := by
    by_contra hn
    exact hnot ⟨x, y, hx, hy, hn⟩
  have hxyN : Relation.EqvGen R x y := by
    apply Relation.EqvGen.mono (fun a b hab => ?_) x y hxy
    rcases hab.2.2 with hr | hf
    · exact Or.inl ((hrot a hab.1).trans hr)
    · exact Or.inr ((congrArg (fun σ : Equiv.Perm D => σ a) hflip).trans hf)
  exact (hdx.trans _ _ _ hxyN).trans _ _ _ hey.symm

/-- Helper toward Proposition 5.16: two distinct darts in the same vertex
and face cycles force a cut vertex in a loopless map of Euler characteristic
two. The proof splits both cycles and applies the proved combinatorial
Euler bound to the resulting connected map. -/
theorem isCutVertex_of_same_vertex_same_face
    (M : CombinatorialMap D) (a b : D) (hab : a ≠ b)
    (hv : M.rot.SameCycle a b) (hf : M.faceSucc.SameCycle a b)
    (hloop : ∀ d, vertexClass M d ≠ vertexClass M (M.edgeInv d))
    (hEuler : M.eulerChar = 2) : M.isCutVertex (vertexClass M a) := by
  classical
  by_contra hnot
  let N : CombinatorialMap D :=
    { edgeInv := M.edgeInv
      edgeInv_invol := M.edgeInv_invol
      edgeInv_ne := M.edgeInv_ne
      rot := M.rot * Equiv.swap a b }
  have hba : vertexClass M b = vertexClass M a := (Quotient.sound hv).symm
  have hNconn : N.IsConnected :=
    M.isConnected_of_not_isCutVertex_of_rotation_eq N (vertexClass M a) rfl
      (by
        intro d hd
        have hda : d ≠ a := fun h => hd (h ▸ rfl)
        have hdb : d ≠ b := fun h => hd (h ▸ hba)
        exact rightSwap_apply_of_ne M.rot hda hdb)
      hloop hnot
  have hV : N.numVertices = M.numVertices + 1 := by
    simpa only [numVertices, ← Nat.card_eq_fintype_card] using
      sameCycle_split_orbit_count M.rot hab hv
  have hface : N.faceSucc = M.faceSucc *
      Equiv.swap (M.faceSucc.symm a) (M.faceSucc.symm b) := by
    ext d
    change (Equiv.swap a b) (M.faceSucc d) =
      M.faceSucc (Equiv.swap (M.faceSucc.symm a) (M.faceSucc.symm b) d)
    by_cases hda : d = M.faceSucc.symm a
    · subst d
      simp only [Equiv.apply_symm_apply, Equiv.swap_apply_left]
    · by_cases hdb : d = M.faceSucc.symm b
      · subst d
        simp only [Equiv.apply_symm_apply, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hda hdb]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          exact hda ((M.faceSucc.eq_symm_apply).mpr h)
        · intro h
          exact hdb ((M.faceSucc.eq_symm_apply).mpr h)
  have hF : N.numFaces = M.numFaces + 1 := by
    simp only [numFaces, ← Nat.card_eq_fintype_card]
    change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid N.faceSucc)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid M.faceSucc)) + 1
    rw [hface]
    have hne : M.faceSucc.symm a ≠ M.faceSucc.symm b :=
      fun h => hab (M.faceSucc.symm.injective h)
    have hsame : M.faceSucc.SameCycle (M.faceSucc.symm a) (M.faceSucc.symm b) :=
      Equiv.Perm.sameCycle_symm_apply_left.mpr
        (Equiv.Perm.sameCycle_symm_apply_right.mpr hf)
    simpa only [← Nat.card_eq_fintype_card] using
      sameCycle_split_orbit_count M.faceSucc hne hsame
  have hE : N.numEdges = M.numEdges := rfl
  let : Nonempty D := ⟨a⟩
  have hbound := eulerChar_le_two_of_isConnected N hNconn
  unfold eulerChar at hbound hEuler
  rw [hV, hF, hE] at hbound
  omega

end CombinatorialMap

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the exact combinatorial deletion
relation yields a drawing polyline missing the deleted vertex point. The
vertex is represented by a dart, without assuming incidence surjectivity. -/
theorem exists_polyline_of_vertexAvoidingStep {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a d e : B.D)
    (hd : vertexClass B.map d ≠ vertexClass B.map a)
    (he : vertexClass B.map e ≠ vertexClass B.map a)
    (h : Relation.EqvGen (B.map.vertexAvoidingStep (vertexClass B.map a)) d e) :
    ∃ c : Polyline, c.start = P.pos (vert d) ∧ c.finish = P.pos (vert e) ∧
      c.image ⊆ P.image ∧ P.pos (vert a) ∉ c.image := by
  have havoid (x : B.D) (hx : vertexClass B.map x ≠ vertexClass B.map a) :
      vert x ≠ vert a := by
    intro heq
    exact hx (Quotient.sound (P.rot_sameCycle_of_vert_eq x a heq))
  apply P.exists_polyline_of_vertex_avoiding_eqvGen (vert a) d e
    (havoid d hd) (havoid e he)
  exact Relation.EqvGen.mono
    (fun x y hxy => ⟨havoid x hxy.1, havoid y hxy.2.1, hxy.2.2⟩) d e h

/-- Helper toward Proposition 5.16: the proved drawing Euler theorem
also applies when the geometric vertex carrier contains isolated points.
Restricting that carrier to the incidence range retains every dart, arc,
rotation and geometric edge identity. -/
theorem eulerChar_eq_two_of_drawing_connected {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    B.map.eulerChar = 2 := by
  let vert' : B.D → Set.range vert := fun d => ⟨vert d, ⟨d, rfl⟩⟩
  let Q : PLDrawing B.D (Set.range vert) B.map.edgeInv B.map.rot vert' :=
    { flip_involutive := P.flip_involutive
      flip_ne := P.flip_ne
      vert_rotation := fun d => Subtype.ext (P.vert_rotation d)
      pos := fun v => P.pos v.val
      pos_injective := fun _ _ h => Subtype.ext (P.pos_injective h)
      arc := P.arc
      arc_simple := P.arc_simple
      arc_length := P.arc_length
      arc_start := P.arc_start
      arc_finish := P.arc_finish
      arc_flip := P.arc_flip
      interior_disjoint := P.interior_disjoint
      interior_avoids_vertices := fun d v => P.interior_avoids_vertices d v.val
      locally_finite := P.locally_finite
      initial_nonzero := P.initial_nonzero
      initial_arg_injective := fun d e h =>
        P.initial_arg_injective d e (congrArg Subtype.val h)
      rotation_agreement := fun d => by
        simpa only [CcwSuccessor, Subtype.ext_iff] using P.rotation_agreement d }
  have hvert' : Function.Surjective vert' := by
    intro v
    obtain ⟨d, hd⟩ := v.property
    exact ⟨d, Subtype.ext hd⟩
  exact (B.common_face_orbit_unique_and_eulerChar_eq_two vert' Q hvert' hconn).2

/-- Helper toward Proposition 5.16: in an actual finite PL drawing,
two distinct darts belonging to both the same vertex and the same face
force the vertex to be a cut vertex. No connectedness, incidence-surjectivity
or Euler premise is added: failure of the cut condition supplies connectivity,
and the proved drawing theorem then supplies Euler characteristic two. -/
theorem isCutVertex_of_same_vertex_same_face {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a b : B.D) (hab : a ≠ b)
    (hv : vertexClass B.map a = vertexClass B.map b)
    (hf : B.map.faceSucc.SameCycle a b) :
    B.map.isCutVertex (vertexClass B.map a) := by
  classical
  have hloop (d : B.D) :
      vertexClass B.map d ≠ vertexClass B.map (B.map.edgeInv d) := by
    intro heq
    exact P.vert_ne_flip d
      (P.vert_eq_of_rot_sameCycle d (B.map.edgeInv d) (Quotient.exact heq))
  by_cases hcut : B.map.isCutVertex (vertexClass B.map a)
  · exact hcut
  · have hconn : B.map.IsConnected :=
      B.map.isConnected_of_not_isCutVertex_of_rotation_eq B.map
        (vertexClass B.map a) rfl (fun _ _ => rfl) hloop hcut
    have hconn' : ∀ d e : B.D, Relation.EqvGen
        (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e := by
      intro d e
      have hpath := hconn d e
      refine Relation.ReflTransGen.head_induction_on
        (motive := fun x _ => Relation.EqvGen
          (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) x e) hpath ?_ ?_
      · exact Relation.EqvGen.refl e
      · intro x y hstep _ ih
        have hxy : Relation.EqvGen
            (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) x y := by
          rcases hstep with hr | hr | hf | hf
          · exact Relation.EqvGen.rel _ _ (Or.inl hr.symm)
          · exact (Relation.EqvGen.rel y x
              (Or.inl (by rw [hr, Equiv.apply_symm_apply]))).symm
          · exact Relation.EqvGen.rel _ _ (Or.inr hf.symm)
          · exact (Relation.EqvGen.rel y x
              (Or.inr (by rw [hf, Equiv.apply_symm_apply]))).symm
        exact hxy.trans _ _ _ ih
    exact B.map.isCutVertex_of_same_vertex_same_face a b hab (Quotient.exact hv) hf
      hloop (B.eulerChar_eq_two_of_drawing_connected vert P hconn')

/-- Helper toward Proposition 5.16: repeated visits to a combinatorial
vertex before completion of one face-successor cycle force that vertex to
be a cut vertex, with exactly the binders of the previously open obligation. -/
theorem faceWalk_repeatedVertex_isCutVertex {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D)
    (i j : ℕ) (hij : i < j)
    (hj : j < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d)
    (hvertex :
      vertexClass B.map ((B.map.faceSucc : B.D → B.D)^[i] d) =
        vertexClass B.map ((B.map.faceSucc : B.D → B.D)^[j] d)) :
    CombinatorialMap.isCutVertex B.map
      (vertexClass B.map ((B.map.faceSucc : B.D → B.D)^[i] d)) := by
  have hne : (B.map.faceSucc : B.D → B.D)^[i] d ≠
      (B.map.faceSucc : B.D → B.D)^[j] d := by
    intro heq
    exact (Nat.ne_of_lt hij)
      ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (hij.trans hj) hj).mp heq)
  have hcycle (k : ℕ) :
      B.map.faceSucc.SameCycle d ((B.map.faceSucc : B.D → B.D)^[k] d) := by
    rw [permIterateEqPow]
    exact Equiv.Perm.sameCycle_pow_right.mpr Equiv.Perm.SameCycle.rfl
  exact B.isCutVertex_of_same_vertex_same_face vert P _ _ hne hvertex
    ((hcycle i).symm.trans (hcycle j))

end D39FiniteBall

end DirectedDistances.PlanarMap
