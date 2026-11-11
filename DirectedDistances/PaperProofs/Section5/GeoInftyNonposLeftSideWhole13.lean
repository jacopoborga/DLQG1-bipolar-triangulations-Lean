/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole12

/-! transport of the unchanged incidence, opposite, orientation and marking relations. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

section IncidentCases

variable (x : XDP) (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)

/-- Helper toward Lemma 5.5: two vertices cannot form an incidence pair. -/
theorem lMinusCodeRelation2_incident_transport_iff_inl_inl
    (a b : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRelation2 x r q hf .incident (.inl a) (.inl b) ↔
      lMinusCodeRelation2 x r q' hf .incident
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inl a))
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inl b)) := by
  simp only [lMinusCodeSide2TransportEquiv_inl, lMinusCodeRelation2]

/-- Helper toward Lemma 5.5: incidence cannot start at a vertex. -/
theorem lMinusCodeRelation2_incident_transport_iff_inl_inr
    (a : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRelation2 x r q hf .incident (.inl a) (.inr d) ↔
      lMinusCodeRelation2 x r q' hf .incident
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inl a))
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr d)) := by
  simp only [lMinusCodeSide2TransportEquiv_inl,
    lMinusCodeSide2TransportEquiv_inr, lMinusCodeRelation2]

/-- Helper toward Lemma 5.5: dart-to-vertex incidence is endpoint equality. -/
theorem lMinusCodeRelation2_incident_transport_iff_inr_inl
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))
    (a : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRelation2 x r q hf .incident (.inr d) (.inl a) ↔
      lMinusCodeRelation2 x r q' hf .incident
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr d))
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inl a)) := by
  rw [lMinusCodeSide2TransportEquiv_inr, lMinusCodeSide2TransportEquiv_inl]
  exact lMinusCodeEndpointVertex_transport_iff x r q q' phi d a

/-- Helper toward Lemma 5.5: two darts cannot form an incidence pair. -/
theorem lMinusCodeRelation2_incident_transport_iff_inr_inr
    (d e : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRelation2 x r q hf .incident (.inr d) (.inr e) ↔
      lMinusCodeRelation2 x r q' hf .incident
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr d))
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr e)) := by
  simp only [lMinusCodeSide2TransportEquiv_inr, lMinusCodeRelation2]

end IncidentCases

/-- Helper toward Lemma 5.5: opposite dart equality is reflected by the dart bijection. -/
theorem lMinusCodeRelation2_opposite_transport_iff_inr_inr (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d e : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRelation2 x r q hf .opposite (.inr d) (.inr e) ↔
      lMinusCodeRelation2 x r q' hf .opposite
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr d))
        (lMinusCodeSide2TransportEquiv x r q q' phi (.inr e)) := by
  rw [lMinusCodeSide2TransportEquiv_inr, lMinusCodeSide2TransportEquiv_inr]
  exact (lMinusCodeGluedDartTransportEquiv x r q q' phi).injective.eq_iff.symm

/-- Helper toward Lemma 5.5: incidence transports by endpoint equality and
injectivity of the allocated vertex action. -/
theorem lMinusCodeRelation2_incident_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .incident u v ↔
      lMinusCodeRelation2 x r q' hf .incident
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact lMinusCodeRelation2_incident_transport_iff_inl_inl x r q q' phi hf a b
    | inr d => exact lMinusCodeRelation2_incident_transport_iff_inl_inr x r q q' phi hf a d
  | inr d =>
    cases v with
    | inl a => exact lMinusCodeRelation2_incident_transport_iff_inr_inl x r q q' phi hf d a
    | inr e => exact lMinusCodeRelation2_incident_transport_iff_inr_inr x r q q' phi hf d e

/-- Helper toward Lemma 5.5: the glued dart bijection preserves opposite darts. -/
theorem lMinusCodeRelation2_opposite_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .opposite u v ↔
      lMinusCodeRelation2 x r q' hf .opposite
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u with
  | inl a =>
    cases v <;>
      simp only [lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr, lMinusCodeRelation2]
  | inr d =>
    cases v with
    | inl a =>
      simp only [lMinusCodeSide2TransportEquiv_inl,
        lMinusCodeSide2TransportEquiv_inr, lMinusCodeRelation2]
    | inr e =>
      exact lMinusCodeRelation2_opposite_transport_iff_inr_inr x r q q' phi hf d e

/-- Helper toward Lemma 5.5: transport preserves directed presence and the
endpoint bit specifying orientation. -/
theorem lMinusCodeRelation2_oriented_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .oriented u v ↔
      lMinusCodeRelation2 x r q' hf .oriented
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u with
  | inl a => rfl
  | inr d =>
    rw [lMinusCodeSide2TransportEquiv_inr]
    exact and_congr_left (fun _ =>
      lMinusCodeEdgePresent_transport_iff x r q q' phi _ d.1)

/-- Helper toward Lemma 5.5: each indexed boundary dart transports under
the glued dart bijection. -/
theorem lMinusCodeRelation2_boundary_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (i : ℕ)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf (.boundary i) u v ↔
      lMinusCodeRelation2 x r q' hf (.boundary i)
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  cases u with
  | inl a => rfl
  | inr d =>
    rw [lMinusCodeSide2TransportEquiv_inr]
    have hb := lMinusCodeGluedDartTransportEquiv_boundary x r q q' phi (i, false)
    change lMinusCodeBoundaryDart r q (i, false) = d ↔
      lMinusCodeBoundaryDart r q' (i, false) = T d
    exact ⟨fun he => hb.symm.trans (congrArg T he),
      fun he => T.injective (hb.trans he)⟩

/-- Helper toward Lemma 5.5: each indexed seam dart transports under the
glued dart bijection. -/
theorem lMinusCodeRelation2_seam_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (i : ℕ)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf (.seam i) u v ↔
      lMinusCodeRelation2 x r q' hf (.seam i)
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  cases u with
  | inl a => rfl
  | inr d =>
    rw [lMinusCodeSide2TransportEquiv_inr]
    have hs := lMinusCodeGluedDartTransportEquiv_seam x r q q' phi i
    change lMinusCodeHattedDart r _
        ⟨(lMinusCoherentLeftSide x q).seam i, lMinus_hatted_seam_mem x q i⟩ = d ↔
      lMinusCodeHattedDart r _
        ⟨(lMinusCoherentLeftSide x q').seam i, lMinus_hatted_seam_mem x q' i⟩ = T d
    exact ⟨fun he => hs.symm.trans (congrArg T he),
      fun he => T.injective (hs.trans he)⟩

end DirectedDistances.PaperProofs.Section5

