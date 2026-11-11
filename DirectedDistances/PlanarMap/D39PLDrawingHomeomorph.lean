/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents12
public import DirectedDistances.PlanarMap.D39PLFaceExtension

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! # Drawing homeomorphisms and face boundaries

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
belong to the sole coordinator. No numbered result completion is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: the prescribed map of two drawing
images, retaining every dart arc and every named vertex. This data does
not assert that the map extends to the plane or preserves its orientation. -/
structure PLImageHomeomorph where
  /-- Helper toward Proposition 5.16: the homeomorphism on drawing images. -/
  toHomeomorph : P.image ≃ₜ P'.image
  /-- Helper toward Proposition 5.16: each labeled geometric arc maps onto
  precisely its counterpart, including its endpoints. -/
  arc_image : ∀ d : B.D,
    (fun x : P.image => (toHomeomorph x : ℂ)) ''
      {x : P.image | (x : ℂ) ∈ (P.arc d).image} = (P'.arc d).image
  /-- Helper toward Proposition 5.16: named vertices have their prescribed
  target positions. -/
  vertex_image : ∀ v : V,
    (toHomeomorph ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) = P'.pos v

/-- Helper toward Proposition 5.16: every orbit boundary lies in the
complete drawing image, including its endpoints. -/
theorem plOrbitBoundary_subset_image (O : D39BallFaceCycleOrbit B) :
    B.plOrbitBoundary vert P O ⊆ P.image := by
  intro z hz
  obtain ⟨d, _, hd⟩ := mem_iUnion₂.mp hz
  exact Or.inr ⟨d, hd⟩

/-- Helper toward Proposition 5.16: an image homeomorphism taking each
labeled dart arc onto its counterpart preserves membership in every
whole orbit boundary in both directions. -/
theorem mem_plOrbitBoundary_iff_of_arc_image
    (f : P.image ≃ₜ P'.image)
    (harc : ∀ d : B.D,
      (fun x : P.image => (f x : ℂ)) ''
        {x : P.image | (x : ℂ) ∈ (P.arc d).image} = (P'.arc d).image)
    (O : D39BallFaceCycleOrbit B) (x : P.image) :
    (x : ℂ) ∈ B.plOrbitBoundary vert P O ↔
      (f x : ℂ) ∈ B.plOrbitBoundary vert P' O := by
  constructor
  · intro hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨d, hd, (harc d) ▸ ⟨x, hxd, rfl⟩⟩
  · intro hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
    rw [← harc d] at hxd
    obtain ⟨y, hy, he⟩ := hxd
    have hyx : y = x := f.injective (Subtype.ext he)
    exact mem_iUnion₂.mpr ⟨d, hd, hyx ▸ hy⟩

/-- Helper toward Proposition 5.16: restriction of an arc-preserving
drawing image homeomorphism to the boundary of the same face orbit. -/
@[expose] def plOrbitBoundaryHomeomorph
    (f : P.image ≃ₜ P'.image)
    (harc : ∀ d : B.D,
      (fun x : P.image => (f x : ℂ)) ''
        {x : P.image | (x : ℂ) ∈ (P.arc d).image} = (P'.arc d).image)
    (O : D39BallFaceCycleOrbit B) :
    B.plOrbitBoundary vert P O ≃ₜ B.plOrbitBoundary vert P' O := by
  let F : B.plOrbitBoundary vert P O → B.plOrbitBoundary vert P' O :=
    fun x => ⟨f ⟨x, B.plOrbitBoundary_subset_image vert P O x.property⟩,
      (B.mem_plOrbitBoundary_iff_of_arc_image vert P P' f harc O _).mp x.property⟩
  let G : B.plOrbitBoundary vert P' O → B.plOrbitBoundary vert P O :=
    fun y => ⟨f.symm ⟨y, B.plOrbitBoundary_subset_image vert P' O y.property⟩, by
      apply (B.mem_plOrbitBoundary_iff_of_arc_image vert P P' f harc O _).mpr
      simpa only [f.apply_symm_apply] using y.property⟩
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change (f.symm (f ⟨x, _⟩) : ℂ) = (x : ℂ)
    exact congrArg Subtype.val (f.symm_apply_apply ⟨x, _⟩)
  · intro y
    apply Subtype.ext
    change (f (f.symm ⟨y, _⟩) : ℂ) = (y : ℂ)
    exact congrArg Subtype.val (f.apply_symm_apply ⟨y, _⟩)
  · exact (continuous_subtype_val.comp (f.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _
  · exact (continuous_subtype_val.comp (f.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

/-- Helper toward Proposition 5.16: the orbit-boundary restriction has
exactly the prescribed drawing image values. -/
theorem plOrbitBoundaryHomeomorph_apply
    (f : P.image ≃ₜ P'.image)
    (harc : ∀ d : B.D,
      (fun x : P.image => (f x : ℂ)) ''
        {x : P.image | (x : ℂ) ∈ (P.arc d).image} = (P'.arc d).image)
    (O : D39BallFaceCycleOrbit B) (x : B.plOrbitBoundary vert P O) :
    (B.plOrbitBoundaryHomeomorph vert P P' f harc O x : ℂ) =
      (f ⟨x, B.plOrbitBoundary_subset_image vert P O x.property⟩ : ℂ) := rfl

/-- Helper toward Proposition 5.16: cyclically simple polygon images
tracing corresponding orbit boundaries admit an inside extension with
the exact values of the original drawing image homeomorphism. This
statement concerns polygon insides, without identifying either face side. -/
theorem exists_orbit_polygon_inside_homeomorph
    (f : P.image ≃ₜ P'.image)
    (harc : ∀ d : B.D,
      (fun x : P.image => (f x : ℂ)) ''
        {x : P.image | (x : ℂ) ∈ (P.arc d).image} = (P'.arc d).image)
    (O : D39BallFaceCycleOrbit B) (q q' : Polyline)
    (hc : q.IsCyclicSimple) (hc' : q'.IsCyclicSimple)
    (hq : q.image = B.plOrbitBoundary vert P O)
    (hq' : q'.image = B.plOrbitBoundary vert P' O) :
    ∃ H : closure q.inside ≃ₜ closure q'.inside,
      ∀ x : q.image,
        (H ⟨x, q.image_subset_closure_inside_cyclic hc x.property⟩ : ℂ) =
          (f ⟨x, B.plOrbitBoundary_subset_image vert P O
            (hq ▸ x.property)⟩ : ℂ) := by
  let e : q.image ≃ₜ q'.image := (Homeomorph.setCongr hq).trans
    ((B.plOrbitBoundaryHomeomorph vert P P' f harc O).trans
      (Homeomorph.setCongr hq'.symm))
  obtain ⟨H, hH⟩ := q.exists_inside_homeomorph_extending_boundary q' hc hc' e
  refine ⟨H, ?_⟩
  intro x
  exact hH x

end D39FiniteBall

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: distinct complementary faces are
disjoint as actual component sets. -/
theorem disjoint_faces (F G : P.Face) (hne : F ≠ G) : Disjoint F.val G.val := by
  apply Set.disjoint_left.mpr
  intro x hxF hxG
  apply hne
  apply Subtype.ext
  obtain ⟨a, _, hF⟩ := F.property
  obtain ⟨b, _, hG⟩ := G.property
  exact hF.trans ((connectedComponentIn_eq (hF ▸ hxF)).trans
    ((connectedComponentIn_eq (hG ▸ hxG)).symm.trans hG.symm))

/-- Helper toward Proposition 5.16: two distinct closed faces meet only
in the drawing image. This holds for bounded and unbounded faces alike. -/
theorem closure_face_inter_subset_image (hvert : Function.Surjective vert)
    (F G : P.Face) (hne : F ≠ G) : closure F.val ∩ closure G.val ⊆ P.image := by
  intro x hx
  have hdis := (P.disjoint_faces F G hne).closure_left
    (P.face_open_frontier_subset_image hvert G).1
  have hxnot : x ∉ G.val := fun h => Set.disjoint_left.mp hdis hx.1 h
  exact (P.face_open_frontier_subset_image hvert G).2
    (by rw [frontier, (P.face_open_frontier_subset_image hvert G).1.interior_eq]
        exact ⟨hx.2, hxnot⟩)

/-- Helper toward Proposition 5.16: the portion of a closed face in the
drawing image is exactly its frontier. -/
theorem closure_face_inter_image_eq_frontier (hvert : Function.Surjective vert)
    (F : P.Face) : closure F.val ∩ P.image = frontier F.val := by
  ext x
  constructor
  · intro hx
    rw [frontier, (P.face_open_frontier_subset_image hvert F).1.interior_eq]
    exact ⟨hx.1, fun h => P.face_subset_compl F h hx.2⟩
  · intro hx
    exact ⟨frontier_subset_closure hx,
      (P.face_open_frontier_subset_image hvert F).2 hx⟩

/-- Helper toward Proposition 5.16: maps on distinct closed faces which
agree with one drawing map on their frontiers agree on every overlap. -/
theorem face_extensions_agree_on_overlap
    (hvert : Function.Surjective vert) {Y : Type*}
    (f : P.image → Y) (F G : P.Face) (hne : F ≠ G)
    (gF : closure F.val → Y) (gG : closure G.val → Y)
    (hF : ∀ (x : ℂ) (hx : x ∈ frontier F.val),
      gF ⟨x, frontier_subset_closure hx⟩ =
        f ⟨x, (P.face_open_frontier_subset_image hvert F).2 hx⟩)
    (hG : ∀ (x : ℂ) (hx : x ∈ frontier G.val),
      gG ⟨x, frontier_subset_closure hx⟩ =
        f ⟨x, (P.face_open_frontier_subset_image hvert G).2 hx⟩)
    (x : ℂ) (hxF : x ∈ closure F.val) (hxG : x ∈ closure G.val) :
    gF ⟨x, hxF⟩ = gG ⟨x, hxG⟩ := by
  have hximage := P.closure_face_inter_subset_image hvert F G hne ⟨hxF, hxG⟩
  have hxfrontF : x ∈ frontier F.val :=
    (P.closure_face_inter_image_eq_frontier hvert F) ▸
      (show x ∈ closure F.val ∩ P.image from ⟨hxF, hximage⟩)
  have hxfrontG : x ∈ frontier G.val :=
    (P.closure_face_inter_image_eq_frontier hvert G) ▸
      (show x ∈ closure G.val ∩ P.image from ⟨hxG, hximage⟩)
  exact (hF x hxfrontF).trans (hG x hxfrontG).symm

end PLDrawing






























































































































end DirectedDistances.PlanarMap
end
