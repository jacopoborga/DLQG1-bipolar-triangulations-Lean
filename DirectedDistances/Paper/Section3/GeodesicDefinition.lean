 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.LeftmostGeodesicSourceProvider

/-!
# Definition 3.13 (`def-geodesic`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/



















public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

 
theorem def_geodesic {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
    (choice : XDP) :
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
      IsLeftmostXDPGeodesic B choice Q → P.darts = Q.darts) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_geodesic_source_provider choice
 
 

end DirectedDistances.Paper.Section3
 
