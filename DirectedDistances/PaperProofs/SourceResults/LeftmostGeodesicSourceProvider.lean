/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.LeftmostGeodesicSourceCorrespondence

/- This file only packages the proved clauses of `def_leftmost_geodesic_provider`
together with the proved source correspondence -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- not counted.

* (i) On every finite acyclic map, an XDP geodesic is a directed path whose
  length equals the ordinary XDP distance (LDP with its bottom convention).
* (ii) On a finite bipolar map with arbitrary endpoints `x, y`, the leftmost
  XDP geodesic is an XDP geodesic such that every XDP geodesic from `x` to `y`
  lies weakly to its right, in the map's orientation.
* (iii) Equivalently, every XDP geodesic from `x` to `y` lies, with its darts
  and its vertices, in the closed submap bounded by the path, the rightmost
  directed path from `x` and the rightmost directed path to `y`.
* (iv) If a directed path from `x` to `y` exists, a leftmost XDP geodesic
  exists.
* (v) Two leftmost XDP geodesics from `x` to `y` have the same dart list.

No geometric, simplicity, extremality or identification premise is added. -/
theorem def_geodesic_source_provider (choice : XDP) :
    (∀ (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
      {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n),
      GeneralEndpointGeodesic.IsXDPGeodesic M hM choice P ↔
        (match choice with
         | .ldp => ((n : ℕ∞) : WithBot ℕ∞) = DirectedDistances.ldp x y
         | .sdp => (n : ℕ∞) = DirectedDistances.sdp x y)) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r)
      {x y : MapVertex B.map} {n : ℕ}
      (P : SimpleDirectedDartPath B.map x y n),
      IsLeftmostXDPGeodesic B choice P ↔
        GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
          (mapPathOfSimplePath P) ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
          GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
            (mapPathOfSimplePath Q) →
          B.WeaklyRightOf P Q) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r)
      {x y : MapVertex B.map} {n : ℕ}
      (P : SimpleDirectedDartPath B.map x y n),
      IsLeftmostXDPGeodesic B choice P ↔
        GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
          (mapPathOfSimplePath P) ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
          GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
            (mapPathOfSimplePath Q) →
          (∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P) ∧
            ∀ v ∈ Q.vertices, v ∈ B.threePathFilledVertices P) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map},
      Quiver.Reachable x y →
      ∃ n, ∃ P : SimpleDirectedDartPath B.map x y n,
        IsLeftmostXDPGeodesic B choice P) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r)
      {x y : MapVertex B.map} {n m : ℕ}
      (P : SimpleDirectedDartPath B.map x y n)
      (Q : SimpleDirectedDartPath B.map x y m),
      IsLeftmostXDPGeodesic B choice P →
      IsLeftmostXDPGeodesic B choice Q → P.darts = Q.darts) := by
  obtain ⟨hdist, -, hex, huniq⟩ := def_leftmost_geodesic_provider (D := D) (ℓ := ℓ)
    (r := r) choice
  refine ⟨hdist, ?_, ?_, hex, huniq⟩
  · intro B x y n P
    exact IsLeftmostXDPGeodesic_iff_weaklyRight B choice P
  · intro B x y n P
    rw [IsLeftmostXDPGeodesic_iff_weaklyRight B choice P]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h m Q hQ
      exact (B.connector_subset_threePathFilledSubmap_iff_weaklyRight P Q).mpr (h Q hQ)
    · intro h m Q hQ
      exact (B.connector_subset_threePathFilledSubmap_iff_weaklyRight P Q).mp (h Q hQ)

end DirectedDistances.PaperProofs.SourceResults
