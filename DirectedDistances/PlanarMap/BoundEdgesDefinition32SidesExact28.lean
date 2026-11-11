/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact27

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: unrestricted upper-left boundary
characterization under local finiteness. -/
theorem mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) (e : E) :
    e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  constructor
  · exact mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e
  · rintro ⟨hp, hleft⟩
    rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
        M B G U S h hfinite e ⟨hp, fun s => Or.inl (hleft s)⟩ with hul | hlr
    · exact hul
    · by_cases hul : e ∈ upperLeftBoundary32 B
      · exact hul
      · exact False.elim
          ((not_forall_leftAtOn_of_mem_lowerRight_not_mem_upperLeft32
            M B G U S h hfinite e hp hlr hul) hleft)

/-- Helper toward Definition 3.2: unrestricted lower-right boundary
characterization under local finiteness. -/
theorem mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) (e : E) :
    e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  constructor
  · exact mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e
  · rintro ⟨hp, hright⟩
    rcases mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
        M B G U S h hfinite e ⟨hp, fun s => Or.inr (hright s)⟩ with hul | hlr
    · by_cases hlr : e ∈ lowerRightBoundary32 B
      · exact hlr
      · exact False.elim
          ((not_forall_rightAtOn_of_mem_upperLeft_not_mem_lowerRight32
            M B G U S h hfinite e hp hul hlr) hright)
    · exact hlr

end DirectedDistances.PlanarMap

end
