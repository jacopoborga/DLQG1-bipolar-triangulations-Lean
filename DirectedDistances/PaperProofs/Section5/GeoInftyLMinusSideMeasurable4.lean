/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable3

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The coherent hatted preimage at the common mode. -/
@[expose] noncomputable def LMinusPreimage.hattedCoherent {x : XDP}
    (q : LMinusPreimage x) :
    selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
  by
    refine ⟨boundaryFutureHattedPath q.k q.W, ?_⟩
    simpa only [← q.mode_eq] using q.hqMode

/-- Helper toward Lemma 5.5. Primed directed presence is read from the
missing-root stages of the first presentation code; the missing root is retained
as a geometric edge and is not declared directed by this predicate. -/
theorem lMinusPreimage_primedEdgePresent_iff {x : XDP}
    (q : LMinusPreimage x) (e : ℕ) :
    PrimedEdgePresent (boundaryGluingFutureStream q.W q.h q.k) q.hτ e ↔
      ∃ m, e < (kmswMissingRootStage (lMinusCodeOf q).1 m).nextEdge ∧
        (kmswMissingRootStage (lMinusCodeOf q).1 m).present e = true := by
  have hc : (lMinusCodeOf q).1 =
      primedCode (primedSimInput (boundaryGluingFutureStream q.W q.h q.k)) q.hτ := by
    have hx : (lMinusCodeOf q).1 =
        (leftSideObsNonpos (if q.longest then XDP.ldp else XDP.sdp) q.k q.W).1 :=
      congrArg (fun y : XDP => (leftSideObsNonpos y q.k q.W).1) q.mode_eq
    exact hx.trans (lMinus_primed_observation_code (longest := q.longest) q.hτ)
  rw [hc]
  rfl

/-- Helper toward Lemma 5.5. Equal presentation codes give equal primed
presence predicates even for different whole-plane preimages. -/
theorem lMinusPreimage_primedEdgePresent_eq_of_code_eq {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    PrimedEdgePresent (boundaryGluingFutureStream q.W q.h q.k) q.hτ =
      PrimedEdgePresent (boundaryGluingFutureStream q'.W q'.h q'.k) q'.hτ := by
  funext e
  apply propext
  rw [lMinusPreimage_primedEdgePresent_iff, lMinusPreimage_primedEdgePresent_iff, hc]

/-- Helper toward Lemma 5.5. The second presentation block is the code of
the coherent hatted left side at the common mode. -/
theorem lMinusPreimage_hattedCode {x : XDP} (q : LMinusPreimage x) :
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        q.hattedCoherent.val = (lMinusCodeOf q).2 := by
  rfl

/-- Helper toward Lemma 5.5. Equal presentation codes determine the entire
hatted block up to marked isomorphism, without assuming any isomorphism. -/
theorem lMinusPreimage_hatted_markedIso_of_code_eq {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
        q.hattedCoherent)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
        q'.hattedCoherent)) := by
  apply leftSideCode_markedIso_of_eq
  rw [lMinusPreimage_hattedCode, lMinusPreimage_hattedCode, hc]


/-- Helper toward Lemma 5.5. In the complete decoded side, the primed
contribution to directed presence can be replaced by a predicate on the first
presentation block alone. This eliminates the extra stream and hit witness
from that contribution, including its missing-root convention. -/
theorem lMinusDecodedSide_present_eq_code
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    let x := if longest then XDP.ldp else XDP.sdp
    let r := decodeLMinus x k (leftSideObsNonpos x k W)
    let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
      ⟨boundaryFutureHattedPath k W, hqMode⟩
    let Q := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
    (lMinusDecodedSide hτ hqMode hfin).present =
      {i | ∃ e, lMinusCodeEdgeId r Q e = i ∧
        lMinusCodeEdgePresent r Q
          (fun a => ∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
            (kmswMissingRootStage r.code.1 m).present a = true) e} := by
  dsimp only
  have hp : PrimedEdgePresent (boundaryGluingFutureStream W h k) hτ =
      (fun a => ∃ m,
        a < (kmswMissingRootStage
          (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W).1 m).nextEdge ∧
        (kmswMissingRootStage
          (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W).1 m).present a =
            true) := by
    rw [lMinus_primed_observation_code hτ]
    rfl
  change {i | ∃ e, _ = i ∧
      lMinusCodeEdgePresent _ _
        (PrimedEdgePresent (boundaryGluingFutureStream W h k) hτ) e} = _
  rw [hp]
  rfl

/-- Helper toward Lemma 5.5. The hatted marked-isomorphism class is
independent of the whole-plane preimage of a fixed presentation code. -/
theorem lMinusPreimage_hatted_class_eq_of_code_eq {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
          q.hattedCoherent) =
      geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
          q'.hattedCoherent) :=
  (geometricSideClass_eq_iff _ _).2
    (lMinusPreimage_hatted_markedIso_of_code_eq q q' hc)





































end DirectedDistances.PaperProofs.Section5
