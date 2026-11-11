/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso

/-! # Geometric-to-combinatorial ball isomorphism helpers

Helpers toward Proposition 5.16. This file records finite directed-edge and
root-dart transport available from a geometric ball isomorphism. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. The edge equivalence of a geometric ball
isomorphism, together with its endpoint-order bit, is a bijection of the
directed geometric edges in the two balls. -/
@[expose] def d39GeomBallIsoV2DirectedEdgeEquiv
    {B C : D39DomainRootedMapV2}
    {r : ℕ} (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    ({a : B.E // a ∈ d39GeomBallEdges B.map B.root r} × Bool) ≃
      ({a : C.E // a ∈ d39GeomBallEdges C.map C.root r} × Bool) where
  toFun p := (e.edgeEquiv p.1, Bool.xor p.2 (e.edgeFlip p.1))
  invFun p :=
    (e.edgeEquiv.symm p.1,
      Bool.xor p.2 (e.edgeFlip (e.edgeEquiv.symm p.1)))
  left_inv := by
    rintro ⟨a, b⟩
    cases b <;> cases hf : e.edgeFlip a <;> simp [hf]
  right_inv := by
    rintro ⟨a, b⟩
    cases b <;> cases hf : e.edgeFlip (e.edgeEquiv.symm a) <;>
      simp [hf]

/-- Helper toward Proposition 5.16. The directed geometric edge bijection
commutes with reversal of the endpoint-order bit. -/
theorem d39GeomBallIsoV2DirectedEdgeEquiv_edgeInv
    {B C : D39DomainRootedMapV2}
    {r : ℕ} (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r}) (b : Bool) :
    d39GeomBallIsoV2DirectedEdgeEquiv e (a, !b) =
      ((d39GeomBallIsoV2DirectedEdgeEquiv e (a, b)).1,
        !(d39GeomBallIsoV2DirectedEdgeEquiv e (a, b)).2) := by
  cases b <;> cases hf : e.edgeFlip a <;>
    simp [d39GeomBallIsoV2DirectedEdgeEquiv, hf]

/-- Helper toward Proposition 5.16. The representations and geometric ball
isomorphism give a dart equivalence on the preimages of their geometric edge
balls. This identifies the directed-edge part of the proposed combinatorial
ball map; combinatorial radius membership is a separate obligation. -/
@[expose] def d39GeomBallIsoV2RepresentationDartEquiv
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    {r : ℕ} (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    {d : M.core.D // (x.dartEquiv d).1 ∈ d39GeomBallEdges B.map B.root r} ≃
      {d : N.core.D // (y.dartEquiv d).1 ∈ d39GeomBallEdges C.map C.root r} where
  toFun d := by
    let p := d39GeomBallIsoV2DirectedEdgeEquiv e
      (⟨(x.dartEquiv d.1).1, d.2⟩, (x.dartEquiv d.1).2)
    refine ⟨y.dartEquiv.symm (p.1.1, p.2), ?_⟩
    rw [Equiv.apply_symm_apply]
    exact p.1.2
  invFun d := by
    let p := (d39GeomBallIsoV2DirectedEdgeEquiv e).symm
      (⟨(y.dartEquiv d.1).1, d.2⟩, (y.dartEquiv d.1).2)
    refine ⟨x.dartEquiv.symm (p.1.1, p.2), ?_⟩
    rw [Equiv.apply_symm_apply]
    exact p.1.2
  left_inv := by
    intro d
    apply Subtype.ext
    simp [d39GeomBallIsoV2DirectedEdgeEquiv]
  right_inv := by
    intro d
    apply Subtype.ext
    simp [d39GeomBallIsoV2DirectedEdgeEquiv]

/-- Helper toward Proposition 5.16. The representation of the target map
identifies the image of the ordered geometric root dart with its combinatorial
root dart. -/
theorem d39GeomBallIsoV2_representation_root_dart
    {N : D39RootedMap} {B C : D39DomainRootedMapV2}
    {r : ℕ} (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    y.dartEquiv.symm
        ((d39GeomBallIsoV2DirectedEdgeEquiv e
          (⟨B.root.1, d39GeomRootEdge_mem B.map B.root e.radius_pos⟩,
            B.root.2)).1.1,
          (d39GeomBallIsoV2DirectedEdgeEquiv e
            (⟨B.root.1, d39GeomRootEdge_mem B.map B.root e.radius_pos⟩,
              B.root.2)).2) = N.rootMark.dart := by
  let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
    ⟨B.root.1, d39GeomRootEdge_mem B.map B.root e.radius_pos⟩
  have hedge : (e.edgeEquiv a).1 = C.root.1 := by
    simpa [a] using e.root_edge_map
  have hbit : C.root.2 = Bool.xor B.root.2 (e.edgeFlip a) := by
    simpa [a] using e.root_bool_map
  apply y.dartEquiv.injective
  rw [Equiv.apply_symm_apply, y.root_mark]
  change ((e.edgeEquiv a).1, Bool.xor B.root.2 (e.edgeFlip a)) = C.root
  exact Prod.ext hedge hbit.symm

































end DirectedDistances.PaperProofs.Section5

end
