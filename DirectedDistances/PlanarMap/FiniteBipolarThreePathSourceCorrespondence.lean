/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarThreePathWalk






public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

namespace BipolarMapWithBoundaryBase

/-- every departure of `Q` at a vertex of `P` lies in the closed clockwise sector
from `P`'s outgoing dart to the rightmost outgoing dart, with clockwise
right endpoint ray is included unless it is the same dart as `P`'s ray.
Arrivals and re-joins are handled by the departure condition at each shared
vertex; the filled-region correspondence proves this suffices, including
empty paths and their vertices. -/
def WeaklyRightOf (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) : Prop :=
  ∀ (i : Fin P.darts.length) (q : D), q ∈ Q.darts →
    dartTailVertex B.map q = dartTailVertex B.map (P.darts.get i) →
    ∀ ht : dartTailVertex B.map (P.darts.get i) ≠ B.sink,
      q = P.darts.get i ∨
        q ∈ openRotationInterval_three_path B.map.rot.symm
          (P.darts.get i)
          (B.out (dartTailVertex B.map (P.darts.get i)) ht) ∨
        (q = B.out (dartTailVertex B.map (P.darts.get i)) ht ∧
          q ≠ P.darts.get i)

/-- a connector lies in the three-path filled submap, in both its dart and vertex
incidences, exactly when every departure from `P` is weakly to its right.
Arrivals or re-joins add no separate condition: at a shared vertex the next
departure is covered, while the path and boundary vertex incidences are
included in the filled-set theorem. -/
theorem connector_subset_threePathFilledSubmap_iff_weaklyRight
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map}
    {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) :
    ((∀ q ∈ Q.darts, q ∈ B.threePathFilledDarts P) ∧
      (∀ v ∈ Q.vertices, v ∈ B.threePathFilledVertices P)) ↔
        B.WeaklyRightOf P Q := by
  simpa only [WeaklyRightOf] using
    B.connector_subset_threePathFilledSubmap_iff_clockwise_departures P Q

end BipolarMapWithBoundaryBase
end DirectedDistances.PlanarMap
