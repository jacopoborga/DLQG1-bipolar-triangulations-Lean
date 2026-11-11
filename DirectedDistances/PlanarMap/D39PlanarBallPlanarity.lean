/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PlanarRootedMap

public section
namespace DirectedDistances.PlanarMap

/-! # Positive-radius planarity of local topology balls

The source defines balls for rooted directed planar maps. Here the existing finite combinatorial
predicate `IsPlanar` is related to the wrapper's positive-radius genus-zero field by
`d39Ball_isPlanar_iff`; this does not establish a plane-embedding or homeomorphism correspondence. -/

/-- Helper toward Definition 3.8. Every positive-radius ball of a `D39PlanarRootedMap` satisfies
the existing `D39Ball` combinatorial `IsPlanar` predicate, by the genus-zero characterization. -/
theorem D39PlanarRootedMap.ball_isPlanar
    (M : D39PlanarRootedMap) (r : ℕ) (hr : 0 < r) :
    letI : DecidableEq
        {d : M.toD39RootedMap.core.D //
          d ∈ d39BallDarts M.toD39RootedMap r} := Classical.decEq _
    (d39BallMap M.toD39RootedMap r).IsPlanar := by
  exact (d39Ball_isPlanar_iff M.toD39RootedMap r hr).2
    (M.positiveBallGenusZero r hr)

/-- Helper toward Definition 3.8. If every positive-radius ball of a `D39RootedMap` satisfies the
existing combinatorial `IsPlanar` predicate, the map has a `D39PlanarRootedMap` wrapper with the
same underlying map. -/
theorem D39PlanarRootedMap.exists_of_positiveBall_isPlanar
    (M : D39RootedMap)
    (h : ∀ r, 0 < r →
      letI : DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} :=
        Classical.decEq _
      (d39BallMap M r).IsPlanar) :
    ∃ P : D39PlanarRootedMap, P.toD39RootedMap = M := by
  classical
  refine ⟨⟨M, ?_⟩, rfl⟩
  intro r hr
  exact (d39Ball_isPlanar_iff M r hr).1 (h r hr)

/-- Helper toward Definition 3.8. Radius zero's internal vertex set consists exactly of the first
vertex of the ordered root mark. This carrier uses radius zero as a recursion base rather than a -/
theorem d39BallVertices_zero_mem_iff
    (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    v ∈ d39BallVertices M 0 ↔ v = M.rootMark.firstVertex := by
  rw [d39BallVertices_zero]
  simp

end DirectedDistances.PlanarMap
