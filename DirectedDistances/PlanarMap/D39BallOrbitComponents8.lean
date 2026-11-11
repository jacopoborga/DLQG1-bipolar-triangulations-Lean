/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents7

/-! # Face counting under nonbridge insertion

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`, -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

namespace PLDrawing

/-- Helper toward Proposition 5.16: under image inclusion, a new face is
contained in the old face containing any one of its points. -/
theorem face_subset_face_of_image_subset
    {D' D V : Type*} {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P' : PLDrawing D' V flip' rot' vert') (P : PLDrawing D V flip rot vert)
    (hvert : Function.Surjective vert) (him : P'.image ⊆ P.image)
    (G : P'.Face) (H : P.Face) {z : ℂ} (hzG : z ∈ G.val) (hzH : z ∈ H.val) :
    H.val ⊆ G.val := by
  obtain ⟨w, _, hG⟩ := G.property
  rw [hG] at hzG ⊢
  rw [connectedComponentIn_eq hzG]
  exact (P.face_isPathConnected hvert H).isConnected.isPreconnected.subset_connectedComponentIn
    hzH (fun x hx hxold => P.face_subset_compl H hx (him hxold))

/-- Helper toward Proposition 5.16: an old face disjoint from an inserted
arc remains exactly one face of the new complement. -/
theorem exists_face_eq_of_image_union_of_disjoint
    {D' D V : Type*} {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P' : PLDrawing D' V flip' rot' vert') (P : PLDrawing D V flip rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (c : Polyline) (him : P.image = P'.image ∪ c.image)
    (G : P'.Face) (hdis : Disjoint G.val c.image) :
    ∃ H : P.Face, H.val = G.val := by
  obtain ⟨z, hz, hG⟩ := G.property
  have hzG : z ∈ G.val := by rw [hG]; exact mem_connectedComponentIn hz
  have hzS : z ∈ G.val \ c.image := ⟨hzG, fun hzc => Set.disjoint_left.mp hdis hzG hzc⟩
  obtain ⟨H, hH⟩ := P'.exists_face_eq_component_face_diff P hvert c him G z hzS
  refine ⟨H, hH.trans ?_⟩
  have heq : G.val \ c.image = G.val := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, fun hx => Set.disjoint_left.mp hdis h hx⟩⟩
  rw [heq]
  exact ((P'.face_isPathConnected hvert' G).isConnected.isPreconnected.connectedComponentIn hzG)

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: geometric faces of a finite ball
form a finite type, using the already proved dart-face surjection. -/
theorem finite_plFace_of_dart_surjection {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) : Finite P.Face :=
  Finite.of_surjective _ (B.plDartFace_surjective vert P hvert)


/-- Helper toward Proposition 5.16: inserting a nonbridge edge increases
the number of actual geometric complementary faces by exactly one. -/
theorem natCard_plFace_eq_add_one_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F.val) :
    Nat.card P.Face = Nat.card P'.Face + 1 := by
  classical
  let L := B.plDartFace vert P hvert newDart
  let R := B.plDartFace vert P hvert (B.map.edgeInv newDart)
  have hLR : L ≠ R := plDartFace_new_ne_flip_of_nonbridge_edge_insertion
    B' B vert' vert P' P hvert' hvert hconn' newDart ι himage hflip hvertι hpos harcs F hinterior
  have him := plImage_eq_union_of_edge_insertion B' B vert' vert P' P newDart ι himage hpos harcs
  have hsplit : F.val \ (P.arc newDart).image = L.val ∪ R.val :=
    face_diff_eq_union_plDartFaces_of_edge_insertion
      B' B vert' vert P' P hvert' hvert newDart ι himage hpos harcs F hinterior
  have hLF : L.val ⊆ F.val := by
    intro z hz
    have hzS : z ∈ F.val \ (P.arc newDart).image := by rw [hsplit]; exact Or.inl hz
    exact hzS.1
  have hRF : R.val ⊆ F.val := by
    intro z hz
    have hzS : z ∈ F.val \ (P.arc newDart).image := by rw [hsplit]; exact Or.inr hz
    exact hzS.1
  have hunchanged (G : P'.Face) (hG : G ≠ F) : ∃ H : P.Face, H.val = G.val := by
    apply P'.exists_face_eq_of_image_union_of_disjoint P hvert' hvert (P.arc newDart) him G
    apply Set.disjoint_left.mpr
    intro z hzG hzc
    by_cases hs : z = (P.arc newDart).start
    · exact P'.face_subset_compl G hzG (Or.inl ⟨vert newDart,
        ((P.arc_start newDart).trans (hpos _)).symm.trans hs.symm⟩)
    by_cases ht : z = (P.arc newDart).finish
    · exact P'.face_subset_compl G hzG (Or.inl ⟨vert (B.map.edgeInv newDart),
        ((P.arc_finish newDart).trans (hpos _)).symm.trans ht.symm⟩)
    have hzF := hinterior ⟨hzc, by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hs ht⟩
    exact hG (P'.faces_eq_of_mem hzG hzF)
  let f : P'.Face → P.Face := fun G => if h : G = F then L else (hunchanged G h).choose
  have hfval (G : P'.Face) (hG : G ≠ F) : (f G).val = G.val := by
    dsimp [f]
    rw [dite_eq_right hG]
    exact (hunchanged G hG).choose_spec
  have hfF : f F = L := by simp only [f, dite_eq_left rfl]
  have hfsub (G : P'.Face) : (f G).val ⊆ G.val := by
    by_cases hG : G = F
    · subst G; rw [hfF]; exact hLF
    · rw [hfval G hG]
  have hfinj : Function.Injective f := by
    intro G K heq
    obtain ⟨z, hz⟩ := (P.face_isPathConnected hvert (f G)).isConnected.nonempty
    exact P'.faces_eq_of_mem (hfsub G hz) (hfsub K (heq ▸ hz))
  have hRnot (G : P'.Face) : f G ≠ R := by
    intro heq
    by_cases hG : G = F
    · subst G; exact hLR (hfF.symm.trans heq)
    obtain ⟨z, hz⟩ := (P.face_isPathConnected hvert R).isConnected.nonempty
    exact hG (P'.faces_eq_of_mem (hfsub G (heq.symm ▸ hz)) (hRF hz))
  have hcover (H : P.Face) : (∃ G, f G = H) ∨ H = R := by
    obtain ⟨z, hz⟩ := (P.face_isPathConnected hvert H).isConnected.nonempty
    have hzold : z ∈ P'.imageᶜ := fun h => P.face_subset_compl H hz (him ▸ Or.inl h)
    obtain ⟨G, hzG⟩ := (P'.faces_cover_compl z).mpr hzold
    by_cases hG : G = F
    · subst G
      have hzarc : z ∉ (P.arc newDart).image := fun h =>
        P.face_subset_compl H hz (Or.inr ⟨newDart, h⟩)
      have hzs : z ∈ L.val ∪ R.val := hsplit ▸ And.intro hzG hzarc
      rcases hzs with hzL | hzR
      · exact Or.inl ⟨F, hfF.trans (P.faces_eq_of_mem hzL hz)⟩
      · exact Or.inr (P.faces_eq_of_mem hz hzR)
    · exact Or.inl ⟨G, P.faces_eq_of_mem ((hfval G hG).symm ▸ hzG) hz⟩
  let g : P'.Face ⊕ Unit → P.Face := Sum.elim f (fun _ => R)
  have hginj : Function.Injective g := by
    intro a b hab
    cases a with
    | inl G =>
      cases b with
      | inl K => exact congrArg Sum.inl (hfinj hab)
      | inr u => exact (hRnot G hab).elim
    | inr u =>
      cases b with
      | inl K => exact (hRnot K hab.symm).elim
      | inr v => cases u; cases v; rfl
  have hgsurj : Function.Surjective g := by
    intro H
    rcases hcover H with ⟨G, hG⟩ | rfl
    · exact ⟨Sum.inl G, hG⟩
    · exact ⟨Sum.inr (), rfl⟩
  let : Finite P'.Face := B'.finite_plFace vert' P' hvert'
  calc
    Nat.card P.Face = Nat.card (P'.Face ⊕ Unit) :=
      (Nat.card_eq_of_bijective g ⟨hginj, hgsurj⟩).symm
    _ = Nat.card P'.Face + 1 := by rw [Nat.card_sum, Nat.card_unique (α := Unit)]


/-- Helper toward Proposition 5.16: the dart-face map descends to the
finite quotient by the actual face-successor cycles. -/
@[expose] def plFaceQuotientMap {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) : CombinatorialMap.FaceQuotient B.map → P.Face :=
  Quotient.lift (B.plDartFace vert P hvert)
    (fun d e h => B.plDartFace_eq_of_sameCycle vert P hvert d e h)

/-- Helper toward Proposition 5.16: every geometric face is reached by
the face quotient map, without assuming common-face orbit uniqueness. -/
theorem plFaceQuotientMap_surjective {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) : Function.Surjective (B.plFaceQuotientMap vert P hvert) := by
  intro F
  obtain ⟨d, hd⟩ := B.plDartFace_surjective vert P hvert F
  exact ⟨Quotient.mk _ d, hd⟩

/-- Helper toward Proposition 5.16: common-face orbit uniqueness is
precisely injectivity of the face quotient map. -/
theorem plFaceQuotientMap_injective_iff {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) :
    Function.Injective (B.plFaceQuotientMap vert P hvert) ↔
      ∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
        B.map.faceSucc.SameCycle d e := by
  classical
  constructor
  · intro h d e hde
    exact Quotient.exact (h (a₁ := Quotient.mk _ d) (a₂ := Quotient.mk _ e) hde)
  · intro h a b
    induction a using Quotient.inductionOn with
    | _ d =>
      induction b using Quotient.inductionOn with
      | _ e =>
        intro hde
        exact Quotient.sound (h d e hde)

/-- Helper toward Proposition 5.16: U1 gives exact equality of orbit
count and geometric face count, using the proved surjection. -/
theorem numFaces_eq_natCard_plFace_of_common_face_orbit_unique
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hU1 : ∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) : B.map.numFaces = Nat.card P.Face := by
  classical
  rw [CombinatorialMap.numFaces, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective _
    ⟨(B.plFaceQuotientMap_injective_iff vert P hvert).mpr hU1,
      B.plFaceQuotientMap_surjective vert P hvert⟩

/-- Helper toward Proposition 5.16: geometric face count never exceeds
the number of face-successor orbits. -/
theorem natCard_plFace_le_numFaces {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) : Nat.card P.Face ≤ B.map.numFaces := by
  classical
  rw [CombinatorialMap.numFaces, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ (B.plFaceQuotientMap_surjective vert P hvert)

/-- Helper toward Proposition 5.16: equality of geometric and
combinatorial face counts forces common-face orbit uniqueness. -/
theorem common_face_orbit_unique_of_numFaces_eq_natCard_plFace
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (hcount : B.map.numFaces = Nat.card P.Face) :
    ∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e := by
  classical
  apply (B.plFaceQuotientMap_injective_iff vert P hvert).mp
  have hc : Nat.card (CombinatorialMap.FaceQuotient B.map) ≤ Nat.card P.Face := by
    simpa only [Nat.card_eq_fintype_card, CombinatorialMap.numFaces] using hcount.le
  exact ((B.plFaceQuotientMap_surjective vert P hvert).bijective_of_nat_card_le hc).injective

/-- Helper toward Proposition 5.16: the complete joint induction state
holds for a connected tree drawing: U1 and Euler characteristic two. -/
theorem common_face_orbit_unique_and_eulerChar_eq_two_of_tree
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) :
    (∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) ∧ B.map.eulerChar = 2 := by
  classical
  refine ⟨fun d e h => B.plDartFace_sameCycle_of_eq_of_tree vert P hvert hconn htree d e h, ?_⟩
  have hF := B.numFaces_eq_one_of_tree hconn htree
  have hV : 0 < B.map.numVertices :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ B.rootDart⟩
  unfold CombinatorialMap.eulerChar
  omega


end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: a rotation cycle preserves its
incident geometric vertex in a finite drawing. -/
theorem vert_eq_of_rot_sameCycle
    {D V : Type*} [Finite D] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d e : D) (h : rot.SameCycle d e) :
    vert d = vert e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  symm
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, P.vert_rotation]
    exact ih

/-- Helper toward Proposition 5.16: the angular successor condition
forces all darts at one geometric vertex into a single rotation cycle. -/
theorem rot_sameCycle_of_vert_eq
    {D V : Type*} [Fintype D] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d e : D) (he : vert d = vert e) :
    rot.SameCycle d e := by
  classical
  let s := Finset.univ.filter (fun x => rot.SameCycle d x)
  have hs : s.Nonempty := by
    refine ⟨d, ?_⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Equiv.Perm.SameCycle.rfl
  obtain ⟨x, hx, hmin⟩ := s.exists_min_image
    (fun x => ccwTurn (P.arc x).initialDirection (P.arc e).initialDirection) hs
  have hdx : rot.SameCycle d x := (Finset.mem_filter.mp hx).2
  have hxe : vert x = vert e := (P.vert_eq_of_rot_sameCycle d x hdx).symm.trans he
  have hbound := P.rotation_turn_le x e hxe.symm
  by_cases ht : ccwTurn (P.arc x).initialDirection (P.arc (rot x)).initialDirection =
      ccwTurn (P.arc x).initialDirection (P.arc e).initialDirection
  · have hrxe : rot x = e := P.initial_arg_injective (rot x) e
      ((P.vert_rotation x).trans hxe) (ccwTurn_left_injective ht)
    exact hrxe ▸ hdx.apply_right
  · have hlt := lt_of_le_of_ne hbound ht
    have hadd := ccwTurn_comp_add hlt
    have hxrot : rot x ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdx.apply_right
    have hm := hmin (rot x) hxrot
    have hp := ccwTurn_pos (P.arc x).initialDirection (P.arc (rot x)).initialDirection
    linarith only [hadd, hm, hp]

/-- Helper toward Proposition 5.16: with surjective incidence, the
number of rotation-cycle vertices is exactly the cardinality of the
geometric vertex carrier. -/
theorem numVertices_eq_natCard
    {D V : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (vert : D → V)
    (P : PLDrawing D V M.edgeInv M.rot vert) (hvert : Function.Surjective vert) :
    M.numVertices = Nat.card V := by
  classical
  let f : CombinatorialMap.VertexQuotient M → V := Quotient.lift vert
    (fun d e h => P.vert_eq_of_rot_sameCycle d e h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn with
      | _ d =>
        induction b using Quotient.inductionOn with
        | _ e =>
          intro h
          exact Quotient.sound (P.rot_sameCycle_of_vert_eq d e h)
    · intro v
      obtain ⟨d, hd⟩ := hvert v
      exact ⟨Quotient.mk _ d, hd⟩
  rw [CombinatorialMap.numVertices, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective f hf

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: retaining all old darts and adding
exactly one reversal pair adds exactly one edge orbit. -/
theorem numEdges_eq_add_one_of_edge_insertion
    (B' B : D39FiniteBall) (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart) :
    B.map.numEdges = B'.map.numEdges + 1 := by
  classical
  let s : Finset B.D := Finset.univ.map ι
  have hmem (d : B.D) : d ∈ s ↔ d ∈ Set.range ι := by
    simp only [s, Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range]
  have hn : newDart ∉ s := fun h => ((himage _).mp ((hmem _).mp h)).1 rfl
  have hf : B.map.edgeInv newDart ∉ s := fun h =>
    ((himage _).mp ((hmem _).mp h)).2 rfl
  have hne : newDart ≠ B.map.edgeInv newDart := (B.map.edgeInv_ne newDart).symm
  have hu : Finset.univ = insert newDart (insert (B.map.edgeInv newDart) s) := by
    ext d
    simp only [Finset.mem_univ, Finset.mem_insert, hmem, himage, true_iff]
    by_cases h₁ : d = newDart
    · exact Or.inl h₁
    by_cases h₂ : d = B.map.edgeInv newDart
    · exact Or.inr (Or.inl h₂)
    exact Or.inr (Or.inr ⟨h₁, h₂⟩)
  have hcard : Fintype.card B.D = Fintype.card B'.D + 2 := by
    rw [← Finset.card_univ, hu, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, not_or]; exact ⟨hne, hn⟩),
      Finset.card_insert_of_notMem hf]
    simp only [s, Finset.card_map, Finset.card_univ]
  have hb := B.map.two_mul_numEdges
  have hb' := B'.map.two_mul_numEdges
  omega


/-- Helper toward Proposition 5.16: the joint induction hypothesis U1
and Euler characteristic two propagates through nonbridge edge insertion.
Only the old drawing's displayed induction state is assumed. -/
theorem common_face_orbit_unique_and_eulerChar_eq_two_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F.val)
    (hH : (∀ d e : B'.D,
      B'.plDartFace vert' P' hvert' d = B'.plDartFace vert' P' hvert' e →
        B'.map.faceSucc.SameCycle d e) ∧ B'.map.eulerChar = 2) :
    (∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) ∧ B.map.eulerChar = 2 := by
  classical
  let : Nonempty B.D := ⟨B.rootDart⟩
  have hgeom := natCard_plFace_eq_add_one_of_nonbridge_edge_insertion
    B' B vert' vert P' P hvert' hvert hconn' newDart ι himage hflip hvertι hpos harcs F hinterior
  have hold := B'.numFaces_eq_natCard_plFace_of_common_face_orbit_unique vert' P' hvert' hH.1
  have hV : B.map.numVertices = B'.map.numVertices :=
    (P.numVertices_eq_natCard B.map vert hvert).trans
      (P'.numVertices_eq_natCard B'.map vert' hvert').symm
  have hE := numEdges_eq_add_one_of_edge_insertion B' B newDart ι himage
  have hupper := eulerChar_le_two_of_isConnected B.map (B.map.isConnected_of_eqvGen hconn)
  have hlower := B.natCard_plFace_le_numFaces vert P hvert
  have hchiold := hH.2
  unfold CombinatorialMap.eulerChar at hupper hchiold
  have hF : B.map.numFaces = B'.map.numFaces + 1 := by omega
  have hcount : B.map.numFaces = Nat.card P.Face := by omega
  refine ⟨B.common_face_orbit_unique_of_numFaces_eq_natCard_plFace vert P hvert hcount, ?_⟩
  unfold CombinatorialMap.eulerChar
  omega


/-- Helper toward Proposition 5.16: U1 upgrades the actual orbit-to-face
surjection to a bijection, with orbit sets as the combinatorial carrier. -/
theorem plOrbitFace_bijective_of_common_face_orbit_unique
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hU1 : ∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) : Function.Bijective (B.plOrbitFace vert P hvert) := by
  refine ⟨?_, B.plOrbitFace_surjective vert P hvert⟩
  intro O Q h
  obtain ⟨d, hO⟩ := O.property
  obtain ⟨e, hQ⟩ := Q.property
  have hd : d ∈ O.val := by rw [hO]; exact Equiv.Perm.SameCycle.rfl
  have he : e ∈ Q.val := by rw [hQ]; exact Equiv.Perm.SameCycle.rfl
  rw [B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hd,
    B.plOrbitFace_eq_plDartFace_of_mem vert P hvert Q e he] at h
  have hde := hU1 d e h
  apply Subtype.ext
  rw [hO, hQ]
  ext z
  exact ⟨fun hz => hde.symm.trans hz, fun hz => hde.trans hz⟩


end D39FiniteBall

namespace Polyline

/-- Helper toward Proposition 5.16: the interior of a simple nontrivial
polyline is connected, as the continuous image of the open path interval. -/
theorem isConnected_interior_of_isSimple (c : Polyline)
    (hlen : 2 ≤ c.points.length) (hc : c.IsSimple) : IsConnected c.interior := by
  rw [← c.toPath_image_openParams hlen hc]
  have hparams : IsConnected openParams := by
    change IsConnected (Ioo (0 : unitInterval) 1)
    exact isConnected_Ioo zero_lt_one
  exact hparams.image c.toPath c.toPath.continuous.continuousOn

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: for an exact deletion of one dart
pair, the removed arc's entire interior automatically lies in a single
old face; this geometric input needs no connectivity or U1 assumption. -/
theorem exists_face_arc_interior_subset_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d) :
    ∃ F : P'.Face, (P.arc newDart).interior ⊆ F.val := by
  have hsub : (P.arc newDart).interior ⊆ P'.imageᶜ := by
    intro z hz hzold
    rcases hzold with ⟨v, hv⟩ | ⟨d, hd⟩
    · exact P.interior_avoids_vertices newDart v ((hpos v).trans hv ▸ hz)
    have hdarc : z ∈ (P.arc (ι d)).image := (harcs d).symm ▸ hd
    have havoid (v : V) (h : z = P.pos v) : False :=
      P.interior_avoids_vertices newDart v (h ▸ hz)
    by_cases hs : z = (P.arc (ι d)).start
    · exact havoid _ (hs.trans (P.arc_start (ι d)))
    by_cases ht : z = (P.arc (ι d)).finish
    · exact havoid _ (ht.trans (P.arc_finish (ι d)))
    have hdint : z ∈ (P.arc (ι d)).interior :=
      ⟨hdarc, by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hs ht⟩
    have hne := (himage (ι d)).mp ⟨d, rfl⟩
    exact Set.disjoint_left.mp (P.interior_disjoint newDart (ι d) hne.1 hne.2) hz hdint
  have hconn := (P.arc newDart).isConnected_interior_of_isSimple
    (P.arc_length newDart) (P.arc_simple newDart)
  obtain ⟨z, hz⟩ := hconn.nonempty
  obtain ⟨F, hzF⟩ := (P'.faces_cover_compl z).mpr (hsub hz)
  refine ⟨F, ?_⟩
  obtain ⟨w, _, hF⟩ := F.property
  rw [hF] at hzF ⊢
  rw [connectedComponentIn_eq hzF]
  exact hconn.isPreconnected.subset_connectedComponentIn hz hsub

end D39FiniteBall
end DirectedDistances.PlanarMap
end

/- OPEN optional full induction (no additional premise is assumed above):

  D39FiniteBall.common_face_orbit_unique_and_eulerChar_eq_two
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    (∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) ∧ B.map.eulerChar = 2

The tree base, exact geometric count and joint nonbridge insertion step
are proved in this file. The missing input is construction, for every
non-tree connected drawing, of a smaller connected drawing on the same
vertex carrier by deleting exactly one reversal pair. No such input is
added as a premise to the full-induction statement.

Three approaches investigated for that remaining construction:
1. Backward restriction: EdgeRestrictedDrawing.restrictDrawing and
   FiniteStarFirstReturn.drawingFirstReturnPerm construct a restricted PL
   drawing and its angular rotation. Their inspected statements do not
   select a removable pair or prove connectivity after removing it; the
   restricted vertex type must also be identified with the original V.
   The removed-arc-in-one-face obligation itself is discharged above by
   exists_face_arc_interior_subset_of_edge_insertion.
2. Forward spanning tree: inspected SimpleGraph.Connected.exists_isTree_le
   in Mathlib/Combinatorics/SimpleGraph/Acyclic.lean. Using it here still
   requires constructing the vertex graph, selecting actual dart pairs for
   its tree edges, preserving parallel-edge identity outside the tree, and
   proving the exact quotient edge count. A simple graph alone is not the
   carrier of the result, and no such identification is asserted.
3. Cycle-space counting: inspected cycleSpace_finrank_connected and
   planar_range_faceBoundary_eq_cycleSpace in PlanarFaceCycleSpace.lean.
   The latter takes IsPlanar, which already includes Euler characteristic
   two. It cannot supply the missing deletion construction without a new
   argument. The independent upper bound is used only in the proved step.

5.16 or assert paper completion. -/

