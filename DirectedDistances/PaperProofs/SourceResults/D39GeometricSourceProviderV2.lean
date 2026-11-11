/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDomain
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartInvariance2
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIsoSymm
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso5
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso6

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/










public section

noncomputable section

namespace DirectedDistances.PaperProofs.SourceResults

open Set
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open scoped ENNReal Topology

universe uD39V2 uV' uE'




structure D39DomainRootedMapV2 where
  V : Type uD39V2
  E : Type uD39V2
  map : DirectedPlaneMapWithMissing V E
  root : E × Bool
  domain : D39GeomDomain map root

/-- Helper toward Definition 3.8 (`def-bs-topology`) provider V2; not installed, not counted.
The Benjamini-Schramm local distance of the two rooted maps. -/
@[expose] noncomputable def d39LocalDistanceV2
    (A B : D39DomainRootedMapV2.{uD39V2}) : ENNReal :=
  d39GeomDistanceV2 A.map A.root B.map B.root









theorem def_bs_topology_source_provider_v2 :
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
          d39LocalDistanceV2 C A) := by
  intro A B C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v
    rfl
  · intro r e
    rfl
  · intro r F
    rfl
  · intro r
    exact ⟨D39GeomDomain.ballVertices_finite A.domain r,
      D39GeomDomain.ballEdges_finite A.domain r⟩
  · rfl
  · intro r hr
    exact d39GeomDistanceV2_le_iff_nonempty hr
  · exact d39GeomDistanceV2_self A.map A.root
  · exact d39GeomDistanceV2_comm A.map A.root B.map B.root
  · exact d39GeomDistanceV2_ultrametric
  · exact d39GeomDistanceV2_eq_zero_iff
  · rintro ⟨h⟩
    exact ⟨D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_left h,
      D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_right h⟩
  · rintro V' E' M' rho' ⟨h⟩
    exact h.domain_map A.domain
  · intro S
    exact ⟨D39GeomDomain.storeFlip A.map A.root S A.domain,
      d39GeomDistanceV2_storeFlip_eq_zero A.map A.root S,
      d39GeomDistanceV2_storeFlip_congr_left A.map A.root S C.map C.root,
      d39GeomDistanceV2_storeFlip_congr_right C.map C.root A.map A.root S⟩

end DirectedDistances.PaperProofs.SourceResults

end
