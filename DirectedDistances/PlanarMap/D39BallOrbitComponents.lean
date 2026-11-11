/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalConnected2
public import DirectedDistances.PlanarMap.D39BallBoundaryPolyline
public import DirectedDistances.PlanarMap.D39FacedBallConnectivity

/-! # Face-successor orbits and complementary components

Helpers toward Proposition 5.16. The correspondence between face-successor
orbits and complementary components is a separate geometric proof obligation. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)

include hvert

/-- Helper toward Proposition 5.16: each retained dart has exactly one
complementary face immediately to its left. -/
theorem plDartBorders_existsUnique (d : B.D) :
    ∃! F : P.Face, P.dartBorders d F := by
  obtain ⟨F, hF⟩ := P.dartBorders_exists_of_wedge_compl d
    (P.wedgeIn_compl_image hvert (P.arc d).start
      (P.arc d).initialDirection (P.initial_nonzero d))
  exact ⟨F, hF, fun G hG => P.dartBorders_face_unique d G F hG hF⟩

/-- Helper toward Proposition 5.16: the face to the left of a retained dart,
chosen after its existence and uniqueness have been proved. -/
@[expose] def plDartFace (d : B.D) : P.Face :=
  (B.plDartBorders_existsUnique vert P hvert d).exists.choose

/-- Helper toward Proposition 5.16: the chosen dart face satisfies exactly
the geometric left-wedge bordering predicate. -/
theorem plDartFace_eq_iff (d : B.D) (F : P.Face) :
    B.plDartFace vert P hvert d = F ↔ P.dartBorders d F := by
  have hs : P.dartBorders d (B.plDartFace vert P hvert d) :=
    (B.plDartBorders_existsUnique vert P hvert d).exists.choose_spec
  constructor
  · intro h
    exact h ▸ hs
  · intro h
    exact P.dartBorders_face_unique d _ F hs h

/-- Helper toward Proposition 5.16: every complementary face is the chosen
left face of at least one retained dart. -/
theorem plDartFace_surjective :
    Function.Surjective (B.plDartFace vert P hvert) := by
  intro F
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart hvert B.rootDart F
  exact ⟨d, (B.plDartFace_eq_iff vert P hvert d F).mpr hd⟩

/-- Helper toward Proposition 5.16: each face-successor orbit contains a
dart whose left face exists uniquely. This does not yet assert that every
dart of that orbit has the same left face. -/
theorem exists_mem_orbit_dartBorders (O : D39BallFaceCycleOrbit B) :
    ∃ d ∈ O.val, ∃! F : P.Face, P.dartBorders d F := by
  obtain ⟨d, hd⟩ := O.property
  refine ⟨d, ?_, B.plDartBorders_existsUnique vert P hvert d⟩
  rw [hd]
  exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16: every complementary face has a
bordering dart in an actual face-successor orbit. Uniqueness of this orbit
is a further geometric obligation. -/
theorem exists_orbit_mem_dartBorders (F : P.Face) :
    ∃ O : D39BallFaceCycleOrbit B, ∃ d ∈ O.val, P.dartBorders d F := by
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart hvert B.rootDart F
  exact ⟨⟨{e | B.map.faceSucc.SameCycle d e}, d, rfl⟩,
    d, Equiv.Perm.SameCycle.rfl, hd⟩

/-- Helper toward Proposition 5.16: the entire arc of a dart is contained
in the closure of its uniquely determined left face, including endpoints. -/
theorem plDartFace_arc_subset_closure (d : B.D) :
    (P.arc d).image ⊆ closure (B.plDartFace vert P hvert d).val := by
  apply P.dartBorders_arc_subset_closure hvert d
  exact (B.plDartFace_eq_iff vert P hvert d _).mp rfl

/-- Helper toward Proposition 5.16: a finite retained dart set supplies
finitely many complementary faces through the proved dart-face surjection. -/
theorem finite_plFace : Finite P.Face :=
  Finite.of_surjective (B.plDartFace vert P hvert)
    (B.plDartFace_surjective vert P hvert)

omit hvert in
/-- Helper toward Proposition 5.16: rotation-adjacent or reversed darts
have intersecting closed arc images. -/
theorem plArcImages_inter_of_step (d e : B.D)
    (h : B.map.rot d = e ∨ B.map.edgeInv d = e) :
    ((P.arc d).image ∩ (P.arc e).image).Nonempty := by
  rcases h with rfl | rfl
  · refine ⟨(P.arc d).start, Or.inl rfl, ?_⟩
    have hs : (P.arc d).start = (P.arc (B.map.rot d)).start := by
      rw [P.arc_start, P.arc_start, P.vert_rotation]
    exact Or.inl hs
  · refine ⟨(P.arc d).start, Or.inl rfl, ?_⟩
    rw [P.arc_image_flip]
    exact Or.inl rfl

/-- Helper toward Proposition 5.16: surjective dart incidence places every
drawn vertex on an actual retained arc. -/
theorem plImage_eq_union_arcs : P.image = ⋃ d, (P.arc d).image := by
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · obtain ⟨d, rfl⟩ := hvert v
      exact Set.mem_iUnion.mpr ⟨d, Or.inl (P.arc_start d).symm⟩
    · exact Set.mem_iUnion.mpr ⟨d, hd⟩
  · intro hz
    exact Or.inr (Set.mem_iUnion.mp hz)

/-- Helper toward Proposition 5.16: combinatorial dart connectivity makes
the complete PL drawing image connected, with geometric edge identity
preserved throughout the rotation and reversal steps. -/
theorem plImage_isConnected
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    IsConnected P.image := by
  let : Nonempty B.D := ⟨B.rootDart⟩
  let R : B.D → B.D → Prop :=
    fun d e => ((P.arc d).image ∩ (P.arc e).image).Nonempty
  let : Std.Symm R := ⟨fun d e h => by
    simpa only [R, Set.inter_comm] using h⟩
  rw [B.plImage_eq_union_arcs vert P hvert]
  apply IsConnected.iUnion_of_reflTransGen
  · intro d
    rw [← Polyline.range_toPath]
    exact isConnected_range (P.arc d).toPath.continuous
  · intro d e
    have h : Relation.EqvGen R d e :=
      Relation.EqvGen.mono
        (fun x y hxy => B.plArcImages_inter_of_step vert P x y hxy)
        d e (hconn d e)
    rwa [Relation.EqvGen.eqvGen_eq_reflTransGen] at h

/-- Helper toward Proposition 5.16: the complement of a locally finite PL
drawing with surjective dart incidence is dense. Narrow wedge avoidance
provides a complementary point in every nonempty open set. -/
theorem dense_compl_plImage : Dense P.imageᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨a, ha⟩ := hUne
  obtain ⟨δ, hδ, hw⟩ := P.wedgeIn_compl_image hvert a 1 one_ne_zero
  obtain ⟨η, hη, hu⟩ :=
    PLDrawing.wedgeIn_of_mem_nhds a 1 (hU.mem_nhds ha)
  let t := min δ η / 2
  have ht : 0 < t := half_pos (lt_min hδ hη)
  have htδ : t < δ := (half_lt_self (lt_min hδ hη)).trans_le (min_le_left _ _)
  have htη : t < η := (half_lt_self (lt_min hδ hη)).trans_le (min_le_right _ _)
  exact ⟨wedgePoint a 1 t t, hu t t ht htη ht htη, hw t t ht htδ ht htδ⟩

omit hvert in
/-- Helper toward Proposition 5.16: a drawing face containing a point
inside a closed polygon in the drawing stays entirely inside that polygon.
No simplicity of the whole face boundary is assumed. -/
theorem plFace_subset_inside_of_mem (c : Polyline)
    (hclosed : c.start = c.finish) (himage : c.image ⊆ P.image)
    (F : P.Face) {a : ℂ} (haF : a ∈ F.val) (ha : a ∈ c.inside) :
    F.val ⊆ c.inside := by
  obtain ⟨z, _, hF⟩ := F.property
  have heq : F.val = connectedComponentIn P.imageᶜ a :=
    hF.trans (connectedComponentIn_eq (hF ▸ haF))
  rw [heq]
  exact (connectedComponentIn_mono a (Set.compl_subset_compl.mpr himage)).trans
    (c.component_subset_inside hclosed a ha)

omit hvert in
/-- Helper toward Proposition 5.16: a drawing face containing a point
outside a closed polygon in the drawing stays entirely outside it. -/
theorem plFace_subset_outside_of_mem (c : Polyline)
    (hclosed : c.start = c.finish) (himage : c.image ⊆ P.image)
    (F : P.Face) {a : ℂ} (haF : a ∈ F.val) (ha : a ∈ c.outside) :
    F.val ⊆ c.outside := by
  obtain ⟨z, _, hF⟩ := F.property
  have heq : F.val = connectedComponentIn P.imageᶜ a :=
    hF.trans (connectedComponentIn_eq (hF ▸ haF))
  rw [heq]
  exact (connectedComponentIn_mono a (Set.compl_subset_compl.mpr himage)).trans
    (c.component_subset_outside hclosed a ha)

/-- Helper toward Proposition 5.16: a cyclically simple polygon contained
in the drawing separates at least two drawing faces, one on each winding
side. This does not treat a repeated-vertex face walk as a simple polygon. -/
theorem exists_distinct_plFaces_of_cyclicSimple (c : Polyline)
    (hc : c.IsCyclicSimple) (himage : c.image ⊆ P.image) :
    ∃ F G : P.Face, F ≠ G ∧ F.val ⊆ c.inside ∧ G.val ⊆ c.outside := by
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  obtain ⟨a, ha, hna⟩ := (B.dense_compl_plImage vert P hvert).inter_open_nonempty
    c.inside (c.isOpen_inside hclosed) (c.inside_nonempty_cyclic hc)
  obtain ⟨b₀, hb₀, _⟩ := c.outside_unbounded hclosed 0
  obtain ⟨b, hb, hnb⟩ := (B.dense_compl_plImage vert P hvert).inter_open_nonempty
    c.outside (c.isOpen_outside hclosed) ⟨b₀, hb₀⟩
  obtain ⟨F, haF⟩ := (P.faces_cover_compl a).mpr hna
  obtain ⟨G, hbG⟩ := (P.faces_cover_compl b).mpr hnb
  have hF := B.plFace_subset_inside_of_mem vert P c hclosed himage F haF ha
  have hG := B.plFace_subset_outside_of_mem vert P c hclosed himage G hbG hb
  refine ⟨F, G, ?_, hF, hG⟩
  intro heq
  have haG : a ∈ G.val := heq ▸ haF
  exact ha.2 (hG haG).2

end D39FiniteBall

/-- Helper toward Proposition 5.16: the drawing of an actual positive-radius
faced ball is connected; the required dart connectivity is proved by the -/
theorem d39FacedBall_plImage_isConnected {V : Type*} (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r) (vert : (d39FacedBall M r hr).D → V)
    (P : PLDrawing (d39FacedBall M r hr).D V
      (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).map.rot vert)
    (hvert : Function.Surjective vert) : IsConnected P.image :=
  (d39FacedBall M r hr).plImage_isConnected vert P hvert
    (d39FacedBall_connected M r hr)

/- Remaining geometric obligations (not declarations or assumptions):

1. Face-successor invariance:
   B.plDartFace vert P hvert (B.map.faceSucc d) =
     B.plDartFace vert P hvert d.
   The direct wedge route above proves existence and uniqueness at a dart
   and coverage of every face, but still needs a connected local sector
   between consecutive rays at an arbitrary graph vertex. The polygonal
   two-incident-segment theorem alone does not cover higher-degree stars.

2. Common-face orbit uniqueness, under the specified dart connectivity:
   B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
     B.map.faceSucc.SameCycle d e.
   The spanning-tree/insertion route has connected drawing image and
   simple-cycle face separation above. It still needs the exact component
   change under edge insertion, including the bridge case. Separation into
   at least two faces is insufficient to assert exactly one face splits.
   The Euler route has finite geometric faces above; the inspected
   CombinatorialMapEulerBound counts combinatorial face orbits, not the
   complementary components. A geometric V - E + F = 2 theorem remains
   necessary before that count could prove uniqueness.

3. After both preceding obligations, descend plDartFace to the orbit type
   and combine the proved dart-face surjection with common-face uniqueness:

   D39FiniteBall.plFaceOrbitEquiv
     {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
     (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
     (hvert : Function.Surjective vert)
     (hconn : ∀ d e : B.D, Relation.EqvGen
       (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
     D39BallFaceCycleOrbit B ≃ P.toPlaneGraphDrawing.Face

The closed orbit polylines supplied by D39BallBoundaryPolyline may repeat
vertices and edges. No cyclic-simplicity assertion about them is made here. -/

end DirectedDistances.PlanarMap

end
