/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact5

/-! # Locally finite vertex images and closed-arc coverage

Local finiteness of vertex positions is an explicit additional hypothesis.
The closed-discrete formulation includes nonincident vertices and prevents
sole coordinator; no paper-completion claim is made. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: the full vertex-position image is closed
and discrete, including vertices which have no incident dart. -/
@[expose] def LocallyFiniteVertexImage
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) : Prop :=
  IsClosed (Set.range G.pos) ∧ IsDiscrete (Set.range G.pos)

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: every drawing point outside all arc images
is a vertex position, without requiring that vertices have incident darts. -/
theorem uncovered_image_subset_vertexImage32 (G : PLDrawing D V flip rot vert) :
    (G.image \ ⋃ d, (G.arc d).image) ⊆ Set.range G.pos := by
  intro z hz
  rcases hz.1 with hv | ⟨d, hd⟩
  · exact hv
  · exact (hz.2 (Set.mem_iUnion.mpr ⟨d, hd⟩)).elim

/-- Helper toward Definition 3.2: under local finiteness of all vertex
positions the uncovered image is closed, even for nonincident vertices. -/
theorem isClosed_uncovered_image32 (G : PLDrawing D V flip rot vert)
    (hfinite : LocallyFiniteVertexImage G) :
    IsClosed (G.image \ ⋃ d, (G.arc d).image) := by
  exact isClosed_of_subset_discrete_closed G.uncovered_image_subset_vertexImage32
    hfinite.2 hfinite.1

/-- Helper toward Definition 3.2: a locally finite vertex image gives an
open neighborhood of every complete closed arc on which all drawing points
belong to some arc image. -/
theorem exists_local_image_of_locallyFiniteVertexImage32
    (G : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage G) (d : D) :
    ∃ N : Set ℂ, IsOpen N ∧ Set.range (G.arc d).toPath ⊆ N ∧
      ∀ z, z ∈ G.image → z ∈ N → z ∈ ⋃ e, (G.arc e).image := by
  apply (G.exists_local_image_iff_disjoint_closure_uncovered d).mpr
  rw [(G.isClosed_uncovered_image32 hfinite).closure_eq]
  apply Set.disjoint_left.mpr
  intro z hz hbad
  exact hbad.2 (Set.mem_iUnion.mpr ⟨d, Polyline.range_toPath (G.arc d) ▸ hz⟩)

end PLDrawing

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: local finiteness of all vertex positions
implies the closed-arc coverage condition for both supplied present sides. -/
theorem isLocallyArcCovered32_of_locallyFiniteVertexImage
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (hfinite : LocallyFiniteVertexImage G) : IsLocallyArcCovered32 M B G := by
  exact ⟨fun i => G.exists_local_image_of_locallyFiniteVertexImage32 hfinite
    (B.presentation.upperLeft.darts i),
    fun i => G.exists_local_image_of_locallyFiniteVertexImage32 hfinite
    (B.presentation.lowerRight.darts i)⟩

/-- Helper toward Definition 3.2: the closed-discrete vertex condition
ensures that every bounded set meets the vertex image in finitely many points. -/
theorem LocallyFiniteVertexImage.finite_inter_of_isBounded
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {G : PLDrawing D V flip rot vert} (hfinite : LocallyFiniteVertexImage G)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    (K ∩ Set.range G.pos).Finite :=
  Metric.finite_isBounded_inter_isClosed hfinite.2 hK hfinite.1

/-- Helper toward Definition 3.2: in particular every compact set meets
the full vertex image in finitely many points. -/
theorem LocallyFiniteVertexImage.finite_inter_of_isCompact
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {G : PLDrawing D V flip rot vert} (hfinite : LocallyFiniteVertexImage G)
    (K : Set ℂ) (hK : IsCompact K) :
    (K ∩ Set.range G.pos).Finite :=
  hfinite.finite_inter_of_isBounded K hK.isBounded

/-- Helper toward Definition 3.2: a supplied upper-left boundary edge has
all the forward-arc left winding tests under the displayed vertex hypothesis. -/
theorem mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) (e : E) :
    e ∈ upperLeftBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s :=
  mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyArcCovered32
    M B G U S h (isLocallyArcCovered32_of_locallyFiniteVertexImage M B G hfinite) e

/-- Helper toward Definition 3.2: a supplied lower-right boundary edge has
all the forward-arc right winding tests under the displayed vertex hypothesis. -/
theorem mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) (e : E) :
    e ∈ lowerRightBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s :=
  mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyArcCovered32
    M B G U S h (isLocallyArcCovered32_of_locallyFiniteVertexImage M B G hfinite) e

/-- Helper toward Definition 3.2: the closed-discrete formulation is
exactly finiteness of the vertex-image intersection with every compact set. -/
theorem locallyFiniteVertexImage_iff_finite_inter_isCompact
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) :
    LocallyFiniteVertexImage G ↔
      ∀ K : Set ℂ, IsCompact K → (K ∩ Set.range G.pos).Finite := by
  constructor
  · intro h K hK
    exact h.finite_inter_of_isCompact K hK
  · intro h
    apply compl_mem_codiscrete_iff.mp
    rw [Filter.codiscrete, codiscreteWithin_iff_locallyFiniteComplementWithin]
    intro z _
    refine ⟨closedBall z 1, closedBall_mem_nhds z zero_lt_one, ?_⟩
    simpa only [← Set.compl_eq_univ_sdiff, compl_compl] using
      h (closedBall z 1) (isCompact_closedBall z 1)

/-- Helper toward Definition 3.2: equivalently every bounded set meets
the vertex-position image in finitely many points. -/
theorem locallyFiniteVertexImage_iff_finite_inter_isBounded
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) :
    LocallyFiniteVertexImage G ↔
      ∀ K : Set ℂ, Bornology.IsBounded K → (K ∩ Set.range G.pos).Finite := by
  constructor
  · intro h K hK
    exact h.finite_inter_of_isBounded K hK
  · intro h
    apply (locallyFiniteVertexImage_iff_finite_inter_isCompact G).mpr
    intro K hK
    exact h K hK.isBounded































































































end DirectedDistances.PlanarMap

end

