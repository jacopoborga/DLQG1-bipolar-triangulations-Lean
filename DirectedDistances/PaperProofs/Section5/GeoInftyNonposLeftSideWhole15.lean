/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole13
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole14

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: all intrinsic marked relations transport under
the same code and hatted marked action. -/
theorem lMinusCodeRelation2_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (t : TruncationRelation)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf t u v ↔
      lMinusCodeRelation2 x r q' hf t
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases t with
  | vertex => exact lMinusCodeRelation2_vertex_transport_iff x r q q' phi hf u v
  | root => exact lMinusCodeRelation2_root_transport_iff x r q q' phi hf u v
  | target => exact lMinusCodeRelation2_target_transport_iff x r q q' phi hf u v
  | incident => exact lMinusCodeRelation2_incident_transport_iff x r q q' phi hf u v
  | opposite => exact lMinusCodeRelation2_opposite_transport_iff x r q q' phi hf u v
  | oriented => exact lMinusCodeRelation2_oriented_transport_iff x r q q' phi hf u v
  | rotation => exact lMinusCodeRelation2_rotation_transport_iff x r q q' phi hf u v
  | faceNext => exact lMinusCodeRelation2_faceNext_transport_iff x r q q' phi hf u v
  | boundary i => exact lMinusCodeRelation2_boundary_transport_iff x r q q' phi hf i u v
  | seam i => exact lMinusCodeRelation2_seam_transport_iff x r q q' phi hf i u v

/-- Helper toward Lemma 5.5: corrected code-only sides are marked-isomorphic
under the hatted marked action, with every geometric and marking tag checked. -/
theorem lMinusCodeSide2_markedIso (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1) :
    Nonempty (GeometricSideMarkedIso (lMinusCodeSide2 x r q hf)
      (lMinusCodeSide2 x r q' hf)) := by
  let E := lMinusCodeSide2CellEquiv x r q hf
  let E' := lMinusCodeSide2CellEquiv x r q' hf
  let T := lMinusCodeSide2TransportEquiv x r q q' phi
  refine ⟨{ equiv := E.symm.trans (T.trans E'), relation_iff := ?_ }⟩
  intro t u v
  have hsource := lMinusCodeSide2CellEquiv_relation_iff x r q hf t (E.symm u) (E.symm v)
  have htransport := lMinusCodeRelation2_transport_iff x r q q' phi hf t
    (E.symm u) (E.symm v)
  have htarget := lMinusCodeSide2CellEquiv_relation_iff x r q' hf t
    (T (E.symm u)) (T (E.symm v))
  calc
    geometricSideRelation (lMinusCodeSide2 x r q hf) t u v ↔
        geometricSideRelation (lMinusCodeSide2 x r q hf)
          t (E (E.symm u)) (E (E.symm v)) := by
      rw [E.apply_symm_apply u, E.apply_symm_apply v]
    _ ↔ geometricSideRelation (lMinusCodeSide2 x r q' hf)
        t (E' (T (E.symm u))) (E' (T (E.symm v))) :=
      hsource.trans (htransport.trans htarget.symm)
    _ ↔ geometricSideRelation (lMinusCodeSide2 x r q' hf) t
        ((E.symm.trans (T.trans E')) u) ((E.symm.trans (T.trans E')) v) := by
      simp only [Equiv.trans_apply]

/-- Helper toward Lemma 5.5: equal presentation codes give marked-isomorphic
corrected decoded sides by passing through their common code-only side. -/
theorem lMinusDecodedSide2_markedIso_of_code_eq
    {x : XDP} (q q' : LMinusPreimage x)
    (hc : lMinusCodeOf q = lMinusCodeOf q') :
    Nonempty (GeometricSideMarkedIso
      (lMinusDecodedSide2 (W := q.W) (h := q.h) (k := q.k)
        (longest := q.longest) q.hτ q.hqMode q.hfin)
      (lMinusDecodedSide2 (W := q'.W) (h := q'.h) (k := q'.k)
        (longest := q'.longest) q'.hτ q'.hqMode q'.hfin)) := by
  let phi := (lMinusPreimage_hatted_markedIso_of_code_eq q q' hc).some
  rcases q with ⟨W, h, H, hLL, longest, hmode, k, hk, hp, hτ, hqMode,
    hfin, P, Tpath, hleft⟩
  cases hmode
  rcases q' with ⟨W', h', H', hLL', longest', hmode', k', hk', hp', hτ',
    hqMode', hfin', P', Tpath', hleft'⟩
  have hlong : longest = longest' := by
    cases longest <;> cases longest'
    · rfl
    · simp at hmode'
    · simp at hmode'
    · rfl
  cases hlong
  change leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W =
    leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k' W' at hc
  let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
  let r' := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k'
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k' W')
  let Q : Coherent (if longest then XDP.ldp else XDP.sdp) := ⟨
    boundaryFutureHattedPath k W, hqMode⟩
  let Q' : Coherent (if longest then XDP.ldp else XDP.sdp) := ⟨
    boundaryFutureHattedPath k' W', hqMode'⟩
  let hf : KMSWFiniteIncidence r.code.1 :=
    lMinus_primed_observation_finiteIncidence hτ hfin
  let hf' : KMSWFiniteIncidence r'.code.1 :=
    lMinus_primed_observation_finiteIncidence hτ' hfin'
  have hcode := lMinusCodeSide2_markedIso (if longest then XDP.ldp else XDP.sdp)
    r Q Q' phi hf
  have hq : lMinusDecodedSide2 hτ hqMode hfin =
      lMinusCodeSide2 (if longest then XDP.ldp else XDP.sdp) r Q hf := by
    rw [lMinusDecodedSide2_eq_codeSide2]
  have hq' : lMinusDecodedSide2 hτ' hqMode' hfin' =
      lMinusCodeSide2 (if longest then XDP.ldp else XDP.sdp) r' Q' hf' := by
    rw [lMinusDecodedSide2_eq_codeSide2]
  rw [hq, hq']
  simpa [r, r', decodeLMinus, hc.symm] using hcode

end DirectedDistances.PaperProofs.Section5
