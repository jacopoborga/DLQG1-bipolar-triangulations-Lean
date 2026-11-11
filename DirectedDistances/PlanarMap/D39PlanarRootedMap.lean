/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39Ball

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. This wrapper encodes the source's planar-map requirement by requiring
every positive-radius combinatorial ball to have genus zero. Its equivalence to
the paper's literal plane-map representation up to orientation-preserving
homeomorphism remains a separate obligation. The rooted map already carries -/
structure D39PlanarRootedMap where
  /-- The rooted locally finite combinatorial map. -/
  toD39RootedMap : D39RootedMap
  /-- Every source-radius ball has the genus-zero condition that characterizes
  planarity of its finite combinatorial map. -/
  positiveBallGenusZero : ∀ r, 0 < r →
    D39BallGenusZero toD39RootedMap r

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. A rooted combinatorial map has this planar wrapper exactly when all
its positive-radius balls satisfy the genus-zero condition. This is the
finite-ball characterization encoded by the wrapper; the plane-map
homeomorphism correspondence remains separate. Source: -/
theorem D39PlanarRootedMap.exists_iff_positiveBallGenusZero
    (M : D39RootedMap) :
    (∃ P : D39PlanarRootedMap, P.toD39RootedMap = M) ↔
      ∀ r, 0 < r → D39BallGenusZero M r := by
  constructor
  · rintro ⟨P, hPM⟩
    cases hPM
    exact P.positiveBallGenusZero
  · intro h
    exact ⟨⟨M, h⟩, rfl⟩

end DirectedDistances.PlanarMap
