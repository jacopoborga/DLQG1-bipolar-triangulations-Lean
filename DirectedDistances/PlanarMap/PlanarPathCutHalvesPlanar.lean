/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutVertexSum
public import DirectedDistances.PlanarMap.ClosedHalfEdges
public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfFaces
public import DirectedDistances.PlanarMap.PlanarPathCutHalfConnected
public import DirectedDistances.PlanarMap.CombinatorialMapEulerBound
public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

/-! # Planarity of the two closed halves

paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)
variable (P : SimpleDirectedDartPath B.map B.source B.sink n)

variable [leftHalfDartsDecidable :
  DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
variable [rightHalfDartsDecidable :
  DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
variable [vertexSameCycleDecidable :
  DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot)]
variable [leftHalfVerticesDecidable : DecidablePred
  (fun v : CombinatorialMap.VertexQuotient B.map.toCombinatorialMap =>
    ∃ d : D, d ∈ pathCutLeftHalfDarts B P ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid
        B.map.toCombinatorialMap.rot) d = v)]
variable [rightHalfVerticesDecidable : DecidablePred
  (fun v : CombinatorialMap.VertexQuotient B.map.toCombinatorialMap =>
    ∃ d : D, d ∈ pathCutRightHalfDarts B P ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid
        B.map.toCombinatorialMap.rot) d = v)]
variable [edgeInvSameCycleDecidable :
  DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv)]
variable [edgeQuotientFintype :
  Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)]
variable [leftAllDartsDecidable : DecidablePred
  (fun q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap =>
    ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
      d ∈ pathCutLeftHalfDarts B P)]
variable [rightAllDartsDecidable : DecidablePred
  (fun q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap =>
    ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
      d ∈ pathCutRightHalfDarts B P)]
variable [leftHalfEdgesDecidable : DecidablePred
  (fun q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap =>
    q ∈ pathCutLeftHalfEdges B P)]
variable [rightHalfEdgesDecidable : DecidablePred
  (fun q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap =>
    q ∈ pathCutRightHalfEdges B P)]

/-- The two closed-half Euler characteristics sum to the base Euler
characteristic plus two. Helper toward `lem-lr-ind` -/
theorem pathCutHalfMaps_eulerChar_sum :
    (pathCutLeftHalfMap B P).eulerChar +
        (pathCutRightHalfMap B P).eulerChar =
      B.map.toCombinatorialMap.eulerChar + 2 := by
  have hV := pathCutHalfMaps_numVertices_sum B P
  have hE := pathCutHalfMaps_numEdges_sum B P
  have hF := pathCutHalves_numFaces_sum B P
  unfold CombinatorialMap.eulerChar
  omega

/-- The left closed half is planar. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfMap_isPlanar :
    (pathCutLeftHalfMap B P).IsPlanar := by
  obtain ⟨dL, hdL⟩ := pathCutLeftHalfDarts_nonempty B P
  obtain ⟨dR, hdR⟩ := pathCutRightHalfDarts_nonempty B P
  have hnonemptyL : Nonempty {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    ⟨⟨dL, hdL⟩⟩
  have hnonemptyR : Nonempty {d : D // d ∈ pathCutRightHalfDarts B P} :=
    ⟨⟨dR, hdR⟩⟩
  have hsum : (pathCutLeftHalfMap B P).eulerChar +
      (pathCutRightHalfMap B P).eulerChar = 4 := by
    rw [pathCutHalfMaps_eulerChar_sum B P, B.planar.2]
    norm_num
  have hplanar := @isPlanar_of_eulerChar_sum _ _ _ _ _ _
    (pathCutLeftHalfMap B P) (pathCutRightHalfMap B P) hnonemptyL hnonemptyR
    (pathCutLeftHalfMap_isConnected B P)
    (pathCutRightHalfMap_isConnected B P) hsum
  exact hplanar.1

/-- The right closed half is planar. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfMap_isPlanar :
    (pathCutRightHalfMap B P).IsPlanar := by
  obtain ⟨dL, hdL⟩ := pathCutLeftHalfDarts_nonempty B P
  obtain ⟨dR, hdR⟩ := pathCutRightHalfDarts_nonempty B P
  have hnonemptyL : Nonempty {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    ⟨⟨dL, hdL⟩⟩
  have hnonemptyR : Nonempty {d : D // d ∈ pathCutRightHalfDarts B P} :=
    ⟨⟨dR, hdR⟩⟩
  have hsum : (pathCutLeftHalfMap B P).eulerChar +
      (pathCutRightHalfMap B P).eulerChar = 4 := by
    rw [pathCutHalfMaps_eulerChar_sum B P, B.planar.2]
    norm_num
  have hplanar := @isPlanar_of_eulerChar_sum _ _ _ _ _ _
    (pathCutLeftHalfMap B P) (pathCutRightHalfMap B P) hnonemptyL hnonemptyR
    (pathCutLeftHalfMap_isConnected B P)
    (pathCutRightHalfMap_isConnected B P) hsum
  exact hplanar.2

/-- The directed left half's underlying combinatorial map is planar. Helper
result. -/
theorem pathCutLeftHalfDirectedMap_toCombinatorialMap_isPlanar :
    (pathCutLeftHalfDirectedMap B P).toCombinatorialMap.IsPlanar := by
  change (pathCutLeftHalfMap B P).IsPlanar
  exact pathCutLeftHalfMap_isPlanar B P

/-- The directed right half's underlying combinatorial map is planar. Helper
result. -/
theorem pathCutRightHalfDirectedMap_toCombinatorialMap_isPlanar :
    (pathCutRightHalfDirectedMap B P).toCombinatorialMap.IsPlanar := by
  change (pathCutRightHalfMap B P).IsPlanar
  exact pathCutRightHalfMap_isPlanar B P

end DirectedDistances.PlanarMap
