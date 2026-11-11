/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointClass
public import DirectedDistances.PlanarMap.KMSWMapChanneled

/-! # Dart-path naturality for restricted left endpoint reversal

restricted reversal carrier; S7-inverse direction; simple-boundary restriction not assumed; not the
paper result. -/

public section
namespace DirectedDistances.PlanarMap

private theorem leftPathDarts_map_of_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b : ℕ}
    {B : BipolarTriangulationWithBoundary D a b}
    {B' : BipolarTriangulationWithBoundary D' a b}
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase) :
    B.leftPath.darts.map I.toEquiv = B'.leftPath.darts := by
  simpa only [BipolarTriangulationWithBoundary.toBase] using I.leftDarts

private theorem rightPathDarts_map_of_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b : ℕ}
    {B : BipolarTriangulationWithBoundary D a b}
    {B' : BipolarTriangulationWithBoundary D' a b}
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase) :
    B.rightPath.darts.map I.toEquiv = B'.rightPath.darts := by
  simpa only [BipolarTriangulationWithBoundary.toBase] using I.rightDarts

private theorem map_edgeInv_of_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b : ℕ}
    {B : BipolarTriangulationWithBoundary D a b}
    {B' : BipolarTriangulationWithBoundary D' a b}
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase) (xs : List D) :
    (xs.map B.map.toCombinatorialMap.edgeInv).map I.toEquiv =
      (xs.map I.toEquiv).map B'.map.toCombinatorialMap.edgeInv := by
  induction xs with
  | nil => rfl
  | cons d xs ih =>
      have hcomm : I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
          B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := by
        change I.toEquiv (B.toBase.map.toCombinatorialMap.edgeInv d) =
          B'.toBase.map.toCombinatorialMap.edgeInv (I.toEquiv d)
        exact I.edgeInv_comm d
      simp only [List.map_cons, hcomm, ih]

/-- Under a base-carrier isomorphism, the left boundary dart list after
restricted left-prefix reversal is the image of the original reversed left
path under the same dart equivalence. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem leftPrefixReversal_leftPath_darts_map
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (B' : BipolarTriangulationWithBoundary D' a b)
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase)
    (hk : 1 ≤ k) (hka : k < a)
    (hbc : B.IsBoundaryChanneled) (hbc' : B'.IsBoundaryChanneled) :
    ((leftPrefixReversal B k hk hka hbc).leftPath.darts).map I.toEquiv =
      (leftPrefixReversal B' k hk hka hbc').leftPath.darts := by
  rw [leftPrefixReversal_leftPath_darts, leftPrefixReversal_leftPath_darts]
  calc
    (B.leftPath.darts.drop k).map I.toEquiv =
        (B.leftPath.darts.map I.toEquiv).drop k := by simp
    _ = B'.leftPath.darts.drop k := by rw [leftPathDarts_map_of_baseIso I]

/-- Under a base-carrier isomorphism, the right boundary dart list after
restricted left-prefix reversal is the image of the reversed, orientation-
flipped left prefix followed by the old right path. Helper toward
simple-boundary restriction not assumed; not the paper result. -/
theorem leftPrefixReversal_rightPath_darts_map
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (B' : BipolarTriangulationWithBoundary D' a b)
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase)
    (hk : 1 ≤ k) (hka : k < a)
    (hbc : B.IsBoundaryChanneled) (hbc' : B'.IsBoundaryChanneled) :
    ((leftPrefixReversal B k hk hka hbc).rightPath.darts).map I.toEquiv =
      (leftPrefixReversal B' k hk hka hbc').rightPath.darts := by
  rw [leftPrefixReversal_rightPath_darts, leftPrefixReversal_rightPath_darts]
  have htake : (B.leftPath.darts.take k).map I.toEquiv =
      B'.leftPath.darts.take k := by
    calc
      (B.leftPath.darts.take k).map I.toEquiv =
          (B.leftPath.darts.map I.toEquiv).take k := by simp
      _ = B'.leftPath.darts.take k := by rw [leftPathDarts_map_of_baseIso I]
  simp only [List.map_append, List.map_reverse]
  rw [map_edgeInv_of_baseIso I]
  rw [htake, rightPathDarts_map_of_baseIso I]

end DirectedDistances.PlanarMap
