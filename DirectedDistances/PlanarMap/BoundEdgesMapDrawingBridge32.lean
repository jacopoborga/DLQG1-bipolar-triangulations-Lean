/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32
public import DirectedDistances.PlanarMap.GeneralPlaneMapSides
public import DirectedDistances.PlanarMap.GeneralPlaneMapExternalBoundary
public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier

/-! # A map-drawing bridge for bound edges

The drawing relation below matches all vertex positions and each geometric
edge identity, including missing edges, by its trace. It therefore identifies
complementary components without imposing a parameterization on the map arcs.
This does not assert that every map admits such a PL drawing.

Three routes were assessed for the present-side claims. (1) Requiring equality
of parameterized paths after an increasing interval homeomorphism would make
the winding-side transport available, but would restrict the arbitrary
continuous map arcs to PL traces and still would not establish endpoint
incidence surjectivity. (2) Matching each edge trace, as done here, preserves
edge identity and faces but does not preserve the parametrized winding test.
(3) Stating the boundary conditions directly with `Drawing M` and its
`LeftAt`/`RightAt` predicates is faithful for arbitrary map arcs, but does not
follow from the present PL `IsBoundEdges32` predicate without a proved local
side bridge. The open statements below retain that gap explicitly. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}

/-- Helper toward Definition 3.2: `G` draws `M` when it has the same vertex
positions and every dart over edge `e` has exactly the geometric trace of
`M.arc e`. The trace comparison is independent of traversal parameterization;
it retains edge identity and includes missing edges. -/
@[expose] def DrawsMap (M : DirectedPlaneMapWithMissing V E)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) : Prop :=
  G.pos = M.toPlaneMapWithMissing.pos ∧
    ∀ d, Set.range (G.arc d).toPath =
      Set.range (M.toPlaneMapWithMissing.arc d.1)

/-- Helper toward Definition 3.2: package the existing v7 boundary predicate
with the explicit drawing correspondence. -/
@[expose] def IsBoundEdges32Map (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  DrawsMap M G ∧ IsBoundEdges32 M B G U S

namespace DrawsMap

variable {M : DirectedPlaneMapWithMissing V E}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}

/-- Helper toward Definition 3.2: matching every edge trace and every vertex
position identifies the complete drawing image. -/
theorem image_eq (h : DrawsMap M G) :
    G.image = M.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
  rcases h with ⟨hpos, harc⟩
  ext z
  simp only [PLDrawing.image, PlaneGraphDrawing.image, Set.mem_union,
    Set.mem_range, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro (hz | ⟨d, hz⟩)
    · exact Or.inl (by simpa only [hpos] using hz)
    · right
      have hz' : z ∈ Set.range (G.arc d).toPath := by
        rw [Polyline.range_toPath]
        exact hz
      rw [harc d] at hz'
      rcases hz' with ⟨t, ht⟩
      exact ⟨d.1, t, ht⟩
  · rintro (hz | ⟨e, t, ht⟩)
    · exact Or.inl (by simpa only [hpos] using hz)
    · right
      refine ⟨(e, true), ?_⟩
      have hz' : z ∈ Set.range (G.arc (e, true)).toPath := by
        rw [harc (e, true)]
        exact ⟨t, ht⟩
      simpa only [← Polyline.range_toPath] using hz'

/-- Helper toward Definition 3.2: every face of `G` is the same subset of the
plane as a complementary component of `M`'s drawing. -/
theorem face_to_map (h : DrawsMap M G) (F : G.Face) :
    ∃ F' : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      F'.val = F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  have hzM : z ∉ M.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
    rw [← h.image_eq]
    exact hz
  refine ⟨⟨connectedComponentIn
      M.toPlaneMapWithMissing.toPlaneGraphDrawing.imageᶜ z, z, hzM, rfl⟩, ?_⟩
  change connectedComponentIn
    M.toPlaneMapWithMissing.toPlaneGraphDrawing.imageᶜ z = F.val
  rw [hF, h.image_eq]

/-- Helper toward Definition 3.2: every complementary component of `M`'s
drawing is represented by a face of `G`. -/
theorem face_from_map (h : DrawsMap M G)
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    ∃ F' : G.Face, F'.val = F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  have hzG : z ∉ G.image := by
    rw [h.image_eq]
    exact hz
  refine ⟨⟨connectedComponentIn G.imageᶜ z, z, hzG, rfl⟩, ?_⟩
  change connectedComponentIn G.imageᶜ z = F.val
  rw [hF, ← h.image_eq]

end DrawsMap

namespace DrawsMap

variable {M : DirectedPlaneMapWithMissing V E}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}

/-- Helper toward Definition 3.2: an unbounded face transfers to an external
face of the map drawing under the edge-trace correspondence. -/
theorem unbounded_face_to_external (h : DrawsMap M G) (U : G.Face)
    (hU : G.IsUnbounded U) :
    ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      F.val = U.val ∧
        M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F := by
  obtain ⟨F, hF⟩ := h.face_to_map U
  refine ⟨F, hF, ?_⟩
  change ¬ Bornology.IsBounded F.val
  rw [hF, isBounded_iff_forall_norm_le]
  push Not
  exact hU

end DrawsMap

namespace IsBoundEdges32

variable {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: either branch of v7 supplies an unbounded
face. -/
theorem isUnbounded (h : IsBoundEdges32 M B G U S) : G.IsUnbounded U := by
  by_cases hf : (externalBoundaryDartSet4 M).Finite
  · have h' := (IsExternalFaceIntervalOrder7.finite_iff hf).mp h
    rcases h'.1 with ⟨_, _, _, hgeom, _⟩
    exact hgeom.1
  · have h' := (IsExternalFaceIntervalOrder7.infinite_iff hf).mp h
    rcases h'.2.1.1 with ⟨_, _, hgeom, _⟩
    exact hgeom.1

end IsBoundEdges32

namespace IsBoundEdges32Map

variable {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: `U` corresponds to an external face of
`M`'s drawing, where externality means unboundedness in the sense of Q-EXT-FACE.
The image defining these components includes every edge, also when missing. -/
theorem externalFace_correspondence (h : IsBoundEdges32Map M B G U S) :
    ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      F.val = U.val ∧
        M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F := by
  exact h.1.unbounded_face_to_external U
    (IsBoundEdges32.isUnbounded h.2)

end IsBoundEdges32Map

/-- Helper toward Definition 3.2: the supplied upper-left side still has its
proved PL dart-border characterization under the map-drawing package. -/
theorem IsBoundEdges32Map.mem_upperLeft_iff_dartBorders
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32Map M B G U S) (e : E) :
    e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U :=
  mem_upperLeftBoundary32_iff_forward_dartBorders h.2 e

/-- Helper toward Definition 3.2: the supplied lower-right side still has its
proved PL dart-border characterization under the map-drawing package. -/
theorem IsBoundEdges32Map.mem_lowerRight_iff_dartBorders
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32Map M B G U S) (e : E) :
    e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U :=
  mem_lowerRightBoundary32_iff_reverse_dartBorders h.2 e






































end DirectedDistances.PlanarMap

end
