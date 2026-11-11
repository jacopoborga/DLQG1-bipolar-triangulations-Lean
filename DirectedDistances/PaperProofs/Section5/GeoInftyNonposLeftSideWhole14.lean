/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole12

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: intrinsic code rotation transports under the
induced dart action by naturality of the spliced permutation. -/
theorem lMinusCodeRelation2_rotation_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .rotation u v ↔
      lMinusCodeRelation2 x r q' hf .rotation
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => simp only [lMinusCodeRelation2.eq_7, lMinusCodeSide2TransportEquiv_inl]
    | inr e => simp only [lMinusCodeRelation2.eq_7, lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr]
  | inr d =>
    cases v with
    | inl b => simp only [lMinusCodeRelation2.eq_7, lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr]
    | inr e =>
      have hd : lMinusCodeGluedDartTransportEquiv x r q q' phi d =
          (lMinusCodeGluedEdgeMap x r q q' phi d.1, d.2) := by
        exact Sum.inr.inj (lMinusCodeSide2TransportEquiv_inr x r q q' phi d)
      have he : lMinusCodeGluedDartTransportEquiv x r q q' phi e =
          (lMinusCodeGluedEdgeMap x r q q' phi e.1, e.2) := by
        exact Sum.inr.inj (lMinusCodeSide2TransportEquiv_inr x r q q' phi e)
      simpa only [lMinusCodeRelation2.eq_7, lMinusCodeSide2TransportEquiv_inr, hd, he] using
        (lMinusCodeInitialSplicedRotation_transport_iff x r q q' phi hf d e)

/-- Helper toward Lemma 5.5: intrinsic retained-face succession transports
by the code-side whole-face relation equivalence. -/
theorem lMinusCodeRelation2_faceNext_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .faceNext u v ↔
      lMinusCodeRelation2 x r q' hf .faceNext
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => simp only [lMinusCodeRelation2.eq_8, lMinusCodeSide2TransportEquiv_inl]
    | inr e => simp only [lMinusCodeRelation2.eq_8, lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr]
  | inr d =>
    cases v with
    | inl b => simp only [lMinusCodeRelation2.eq_8, lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr]
    | inr e =>
      have hd : lMinusCodeGluedDartTransportEquiv x r q q' phi d =
          (lMinusCodeGluedEdgeMap x r q q' phi d.1, d.2) := by
        exact Sum.inr.inj (lMinusCodeSide2TransportEquiv_inr x r q q' phi d)
      have he : lMinusCodeGluedDartTransportEquiv x r q q' phi e =
          (lMinusCodeGluedEdgeMap x r q q' phi e.1, e.2) := by
        exact Sum.inr.inj (lMinusCodeSide2TransportEquiv_inr x r q q' phi e)
      simpa only [lMinusCodeRelation2.eq_8, lMinusCodeSide2TransportEquiv_inr, hd, he] using
        (lMinusCodeWholeFaceNext_transport_iff x r q q' phi hf d e)

end DirectedDistances.PaperProofs.Section5
