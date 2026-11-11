/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact10

/-! # Boundary converses away from the opposite present side

The converses below cover edges absent from the opposite present side.
The remaining exclusive wrong-side case is recorded with full binders below.
integration remain with the sole coordinator; no paper-completion claim is made. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)

/-- Helper toward Definition 3.2: the left winding converse holds for every
edge absent from the lower-right side. The extra hypothesis describes only
this proved subcase, rather than the unrestricted source characterization. -/
theorem mapFaceU_leftAtOn_imp_mem_upperLeftBoundary32_of_not_mem_lowerRight
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hnot : e ∉ lowerRightBoundary32 B)
    (hleft : ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∀ s : {t : I // t ∈ openParams},
        LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) :
    e ∈ upperLeftBoundary32 B := by
  obtain ⟨hp, htests⟩ := hleft
  rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
      M B G U S h hfinite e ⟨hp, fun s => Or.inl (htests s)⟩ with hul | hlr
  · exact hul
  · exact (hnot hlr).elim

/-- Helper toward Definition 3.2: the right winding converse holds for every
edge absent from the upper-left side, with local finiteness displayed. -/
theorem mapFaceU_rightAtOn_imp_mem_lowerRightBoundary32_of_not_mem_upperLeft
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hnot : e ∉ upperLeftBoundary32 B)
    (hright : ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∀ s : {t : I // t ∈ openParams},
        RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) :
    e ∈ lowerRightBoundary32 B := by
  obtain ⟨hp, htests⟩ := hright
  rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
      M B G U S h hfinite e ⟨hp, fun s => Or.inr (htests s)⟩ with hul | hlr
  · exact (hnot hul).elim
  · exact hlr

/-- Helper toward Definition 3.2: exact upper-left characterization on the
complement of the lower-right side; it retains the shared presence witness. -/
theorem mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_not_mem_lowerRight
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hnot : e ∉ lowerRightBoundary32 B) :
    e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  exact ⟨mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e,
    mapFaceU_leftAtOn_imp_mem_upperLeftBoundary32_of_not_mem_lowerRight
      M B G U S h hfinite e hnot⟩

/-- Helper toward Definition 3.2: exact lower-right characterization on the
complement of the upper-left side; it retains the shared presence witness. -/
theorem mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_not_mem_upperLeft
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hnot : e ∉ upperLeftBoundary32 B) :
    e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  exact ⟨mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e,
    mapFaceU_rightAtOn_imp_mem_lowerRightBoundary32_of_not_mem_upperLeft
      M B G U S h hfinite e hnot⟩

/-- Helper toward Definition 3.2: any failure of the unrestricted left
converse lies exclusively on LR, satisfies every right test as well, and has
a forward bordering face distinct from U. In particular, it is not the case
where both geometric sides border U. This records a necessary configuration,
without asserting that the configuration exists. -/
theorem exists_other_forward_face_of_leftAtOn_not_mem_upperLeftBoundary32
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E)
    (hleft : ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∀ s : {t : I // t ∈ openParams},
        LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s)
    (hnot : e ∉ upperLeftBoundary32 B) :
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      e ∈ lowerRightBoundary32 B ∧
      (∀ s : {t : I // t ∈ openParams},
        RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) ∧
      ∃ F : G.Face, F ≠ U ∧
        G.dartBorders (e, M.forward ⟨e, hp⟩) F ∧
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U := by
  obtain ⟨hp, htests⟩ := hleft
  have hlr : e ∈ lowerRightBoundary32 B := by
    rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
        M B G U S h hfinite e ⟨hp, fun s => Or.inl (htests s)⟩ with hul | hlr
    · exact (hnot hul).elim
    · exact hlr
  obtain ⟨_, hright⟩ :=
    mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e hlr
  obtain ⟨_, hreverse⟩ := (mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mp hlr
  obtain ⟨F, hF, _⟩ := G.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    hfinite (e, M.forward ⟨e, hp⟩)
  refine ⟨hp, hlr, hright, F, ?_, hF, hreverse⟩
  intro hFU
  exact hnot ((mem_upperLeftBoundary32_iff_forward_dartBorders h e).mpr
    ⟨hp, hFU ▸ hF⟩)

/-- Helper toward Definition 3.2: any failure of the unrestricted right
converse lies exclusively on UL, satisfies every left test as well, and has
a reverse bordering face distinct from U. This records the mirrored residual
configuration without a side-equivalence assumption. -/
theorem exists_other_reverse_face_of_rightAtOn_not_mem_lowerRightBoundary32
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E)
    (hright : ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∀ s : {t : I // t ∈ openParams},
        RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s)
    (hnot : e ∉ lowerRightBoundary32 B) :
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      e ∈ upperLeftBoundary32 B ∧
      (∀ s : {t : I // t ∈ openParams},
        LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) ∧
      ∃ F : G.Face, F ≠ U ∧
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) F ∧
        G.dartBorders (e, M.forward ⟨e, hp⟩) U := by
  obtain ⟨hp, htests⟩ := hright
  have hul : e ∈ upperLeftBoundary32 B := by
    rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
        M B G U S h hfinite e ⟨hp, fun s => Or.inr (htests s)⟩ with hul | hlr
    · exact hul
    · exact (hnot hlr).elim
  obtain ⟨_, hleft⟩ :=
    mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e hul
  obtain ⟨_, hforward⟩ := (mem_upperLeftBoundary32_iff_forward_dartBorders h e).mp hul
  obtain ⟨F, hF, _⟩ := G.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    hfinite (e, !(M.forward ⟨e, hp⟩))
  refine ⟨hp, hul, hleft, F, ?_, hF, hforward⟩
  intro hFU
  exact hnot ((mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mpr
    ⟨hp, hFU ▸ hF⟩)







































































































end DirectedDistances.PlanarMap

end
