/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLSimpleFaceWalk
public import DirectedDistances.PlanarMap.D39PLFaceExtension4
public import DirectedDistances.PlanarMap.D39PolygonWindingBridge2

/-! Helpers toward Proposition 5.16: winding of a bounded orbit face. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)

include hconn

/-- Helper toward Proposition 5.16: on the bounded face of a cyclically
simple full-period face walk, the angle sum has one common sign, either `1`
or `-1`. -/
theorem faceWalkPolyline_fullPeriod_angleSum_sign_of_isBounded
    (O : D39BallFaceCycleOrbit B)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hclosed : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).finish)
    (hc : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ z ∈ (B.plOrbitFace vert P hvert O).val,
        (faceWalkPolyline B vert P d
          (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).angleSum z = ε := by
  let q := faceWalkPolyline B vert P d
    (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)
  have hboundary : q.image = B.plOrbitBoundary vert P O := by
    dsimp [q]
    exact B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd
  have hinside : (B.plOrbitFace vert P hvert O).val = q.inside :=
    B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
      vert P hvert hconn O q (by simpa only [q] using hclosed) hc hboundary hbounded
  obtain ⟨ε, hε, hsign⟩ := q.exists_inside_angleSum_sign hc
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hzq : z ∈ q.inside := by simpa only [hinside] using hz
  simpa only [q] using hsign z hzq

/-- Helper toward Proposition 5.16: every point of a bounded orbit face
inside a cyclically simple full-period walk has angle sum of absolute value
one. -/
theorem faceWalkPolyline_fullPeriod_abs_angleSum_eq_one_of_isBounded
    (O : D39BallFaceCycleOrbit B)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hclosed : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).finish)
    (hc : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple)
    (z : ℂ) (hz : z ∈ (B.plOrbitFace vert P hvert O).val) :
    |(faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).angleSum z| = 1 := by
  obtain ⟨ε, hε, hsign⟩ := B.faceWalkPolyline_fullPeriod_angleSum_sign_of_isBounded
    vert P hvert hconn O hbounded d hd hclosed hc
  rw [hsign z hz]
  rcases hε with hε | hε <;> simp [hε]

/-- Helper toward Proposition 5.16: for a point in a bounded orbit face,
the winding of the closed full-period walk is equivalent to its angle sum
being one. -/
theorem faceWalkPolyline_fullPeriod_hasWinding_iff_angleSum_eq_one
    (O : D39BallFaceCycleOrbit B)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hclosed : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).finish)
    (hc : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple)
    (z : ℂ) (hz : z ∈ (B.plOrbitFace vert P hvert O).val) :
    HasWinding
        ((faceWalkPolyline B vert P d
          (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
          rfl hclosed)
        z 1 ↔
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).angleSum z = 1 := by
  let q := faceWalkPolyline B vert P d
    (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)
  have hboundary : q.image = B.plOrbitBoundary vert P O := by
    dsimp [q]
    exact B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd
  have hinside : (B.plOrbitFace vert P hvert O).val = q.inside :=
    B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
      vert P hvert hconn O q (by simpa only [q] using hclosed) hc hboundary hbounded
  have hzq : z ∉ q.image := by
    have hzinside : z ∈ q.inside := by simpa only [hinside] using hz
    exact hzinside.1
  simpa only [q, Int.cast_one] using hasWinding_iff_angleSum_eq_int q hclosed z 1 hzq

end D39FiniteBall

end DirectedDistances.PlanarMap

end











































