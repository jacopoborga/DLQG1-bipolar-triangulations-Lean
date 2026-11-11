 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2

/-!
# Definition 3.8 (`def-bs-topology`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




















public section
namespace DirectedDistances.Paper.Section3

open Set
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open scoped ENNReal Topology

universe uD39V2 uV' uE'

 
theorem def_bs_topology :
    ∀ A B C : D39DomainRootedMapV2.{uD39V2},
      (∀ (r : ℕ) (v : A.V),
        v ∈ d39GeomBallVertices A.map A.root r ↔
          d39GeomGraphDistance A.map (d39GeomRootVertex A.map A.root) v ≤ (r : ℕ∞)) ∧
      (∀ (r : ℕ) (e : A.E),
        e ∈ d39GeomBallEdges A.map A.root r ↔
          A.map.toPlaneMapWithMissing.src e ∈ d39GeomBallVertices A.map A.root r ∧
          A.map.toPlaneMapWithMissing.tgt e ∈ d39GeomBallVertices A.map A.root r) ∧
      (∀ (r : ℕ) (F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face),
        F ∈ d39GeomRetainedFaces A.map A.root r ↔
          ∀ v, A.map.toPlaneMapWithMissing.pos v ∈ closure F.val →
            v ∈ d39GeomBallVertices A.map A.root r) ∧
      (∀ (r : ℕ),
        (d39GeomBallVertices A.map A.root r).Finite ∧
        (d39GeomBallEdges A.map A.root r).Finite) ∧
      d39LocalDistanceV2 A B =
        ⨅ r : {r : ℕ // 0 < r},
          ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 A.map A.root B.map B.root)),
            (1 / 2 : ENNReal) ^ r.1 ∧
      (∀ r : ℕ, 0 < r →
        (d39LocalDistanceV2 A B ≤ (1 / 2 : ENNReal) ^ r ↔
          Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root))) ∧
      d39LocalDistanceV2 A A = 0 ∧
      d39LocalDistanceV2 A B = d39LocalDistanceV2 B A ∧
      d39LocalDistanceV2 A C ≤ max (d39LocalDistanceV2 A B) (d39LocalDistanceV2 B C) ∧
      (d39LocalDistanceV2 A B = 0 ↔
        ∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root)) ∧
      (Nonempty (D39GeomRootedMapIsoV2 A.map A.root B.map B.root) →
        d39LocalDistanceV2 A C = d39LocalDistanceV2 B C ∧
        d39LocalDistanceV2 C A = d39LocalDistanceV2 C B) ∧
      (∀ {V' : Type uV'} {E' : Type uE'}
          (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool),
        Nonempty (D39GeomRootedMapIsoV2 A.map A.root M' rho') →
          D39GeomDomain M' rho') ∧
      (∀ S : Set A.E,
        D39GeomDomain (flipEdges A.map S)
            (A.root.1, Bool.xor A.root.2 (d39GeomEdgeFlipBit S A.root.1)) ∧
        d39GeomDistanceV2 A.map A.root (flipEdges A.map S)
            (A.root.1, Bool.xor A.root.2 (d39GeomEdgeFlipBit S A.root.1)) = 0 ∧
        d39GeomDistanceV2 (flipEdges A.map S)
            (A.root.1, Bool.xor A.root.2 (d39GeomEdgeFlipBit S A.root.1)) C.map C.root =
          d39LocalDistanceV2 A C ∧
        d39GeomDistanceV2 C.map C.root (flipEdges A.map S)
            (A.root.1, Bool.xor A.root.2 (d39GeomEdgeFlipBit S A.root.1)) =
          d39LocalDistanceV2 C A) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_bs_topology_source_provider_v2
 
 

end DirectedDistances.Paper.Section3
 
