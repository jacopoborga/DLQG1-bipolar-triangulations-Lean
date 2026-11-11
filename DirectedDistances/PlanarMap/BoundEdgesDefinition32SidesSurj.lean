/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides

/-! # Surjective-vertex winding implications for the supplied Definition 3.2 boundary

implications use the explicitly displayed surjectivity of the dart initial
vertex map. They do not establish the converse implications or the full
boundary equivalences. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: upper-left boundary membership gives the
left winding-side test along every open parameter when dart initial vertices
surject onto the map vertices. -/
theorem mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_surjective
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (hsurj : Function.Surjective (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ upperLeftBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro he
  obtain ⟨hp, hborder⟩ :=
    (mem_upperLeftBoundary32_iff_forward_dartBorders h e).mp he
  refine ⟨hp, ?_⟩
  intro s
  exact G.dartBorders_toPath_leftAtOn hsurj
    (e, M.forward ⟨e, hp⟩) U hborder s

/-- Helper toward Definition 3.2: lower-right boundary membership gives the
right winding-side test along every open parameter when dart initial vertices
surject onto the map vertices. -/
theorem mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_surjective
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (hsurj : Function.Surjective (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ lowerRightBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro he
  obtain ⟨hp, hborder⟩ :=
    (mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mp he
  refine ⟨hp, ?_⟩
  intro s
  exact G.dartBorders_flip_toPath_rightAtOn hsurj
    (e, M.forward ⟨e, hp⟩) U hborder s




















































end DirectedDistances.PlanarMap

end
