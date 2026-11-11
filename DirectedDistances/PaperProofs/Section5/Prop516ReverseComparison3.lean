/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison2
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorTransportSettle







public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.ReverseComparison3

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

/-- Helper toward Proposition 5.16: the ambient face of an original dart
is one of the two restricted orbit faces incident to its geometric edge.
Both alternatives are retained; no oriented identification is asserted. -/
theorem represented_original_face_eq_forward_or_reverse
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original) :
    (x.data.faceOfDart d.1).val =
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
          (plBallDartOrbit (d39FacedBall M r hr) d)).val ∨
      (x.data.faceOfDart d.1).val =
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
          (plBallDartOrbit (d39FacedBall M r hr)
            ((d39FacedBall M r hr).map.edgeInv d))).val := by
  obtain ⟨O, ⟨hO, hinc⟩, _⟩ :=
    d39PLRepresentation_original_face_unique_adjacent_orbit
      x.data x.drawing x.pos_eq x.arc_eq r hr d hd
  rcases hinc with hforward | hreverse
  · have heq := plBallFaceCycleOrbit_eq_of_mem O
      (plBallDartOrbit (d39FacedBall M r hr) d) d hforward
      Equiv.Perm.SameCycle.rfl
    exact Or.inl (hO.symm.trans (congrArg (fun Q =>
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M x.drawing r hr)
        (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) Q).val) heq))
  · have heq := plBallFaceCycleOrbit_eq_of_mem O
      (plBallDartOrbit (d39FacedBall M r hr)
        ((d39FacedBall M r hr).map.edgeInv d))
      ((d39FacedBall M r hr).map.edgeInv d) hreverse Equiv.Perm.SameCycle.rfl
    exact Or.inr (hO.symm.trans (congrArg (fun Q =>
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M x.drawing r hr)
        (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) Q).val) heq))




theorem represented_original_orbitFace_of_reverse_mem
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr))
    (hdO : d ∈ O.val)
    (hreverse : (d39FacedBall M r hr).map.edgeInv d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
        (x.data.faceOfDart d.1).val := by
  obtain ⟨Q, ⟨hQ, hinc⟩, _⟩ :=
    d39PLRepresentation_original_face_unique_adjacent_orbit
      x.data x.drawing x.pos_eq x.arc_eq r hr d hd
  have hOQ : O = Q := by
    rcases hinc with hforward | hbackward
    · exact plBallFaceCycleOrbit_eq_of_mem O Q d hdO hforward
    · exact plBallFaceCycleOrbit_eq_of_mem O Q
        ((d39FacedBall M r hr).map.edgeInv d) hreverse hbackward
  exact hOQ.symm ▸ hQ

/-- Helper toward Proposition 5.16: with exterior transport as the only
input beyond a represented ball isomorphism, a single plane homeomorphism
maps all original ambient faces whose incident dart and reversal lie in
the same restricted face orbit. The general retained-face case is open. -/
theorem exists_represented_face_homeomorph_of_external_transport
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hexterior_transport :
      plBallFaceOrbitMap I
          (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      ∀ (d : (d39FacedBall M r hr).D)
        (_hd : d ∈ (d39FacedBall M r hr).original),
        (d39FacedBall M r hr).map.faceSucc.SameCycle d
          ((d39FacedBall M r hr).map.edgeInv d) →
        H '' (x.data.faceOfDart d.1).val =
          (y.data.faceOfDart (I.toEquiv d).1).val := by
  obtain ⟨H, hor, _hp, _ha, hfaces⟩ :=
    ReverseComparison2.exists_represented_plane_homeomorph_of_external_transport
      x y r hr I hexterior_transport
  refine ⟨H, hor, ?_⟩
  intro d hd hsame
  let O := plBallDartOrbit (d39FacedBall M r hr) d
  have hdO : d ∈ O.val := Equiv.Perm.SameCycle.rfl
  have hreverse : (d39FacedBall M r hr).map.edgeInv d ∈ O.val := hsame
  have hx := represented_original_orbitFace_of_reverse_mem x r hr d hd O hdO hreverse
  have hy := represented_original_orbitFace_of_reverse_mem y r hr (I.toEquiv d)
    ((I.original_iff d).mpr hd) (plBallFaceOrbitMap I O)
    ((plBallFaceOrbitMap_mem_iff I O d).mpr hdO) (by
      rw [← I.edgeInv_comm d]
      exact (plBallFaceOrbitMap_mem_iff I O _).mpr hreverse)
  rw [← hx, hfaces O, hy]



































































































































































end DirectedDistances.PaperProofs.Section5.ReverseComparison3

end
