/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso3

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section ActualFaceSeam

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "p" => primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
local notation "z" => hatCodes (boundaryGluingFutureStream W h k) hτ
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "E" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hqMode hfin in
/-- Helper toward Lemma 5.5: if a primed creation triangle and a retained
hatted creation triangle contain darts with the same glued orientation, their
common edge is on the beta seam. -/
theorem lMinusActualSideSharedTriangleDart_mem_beta
    (jP : TriangleCreationTime p) (jH : TriangleCreationTime z)
    (hRetH : ∀ d ∈ stageTriangleDartList z jH, d.1 ∈ (Q).edges)
    (dP dH : ℕ × Bool)
    (hdP : dP ∈ stageTriangleDartList p jP)
    (hdH : dH ∈ stageTriangleDartList z jH)
    (heq : lMinusPrimedDartImage hτ dP = (EH dH.1, dH.2)) :
    (lMinusPrimedDartImage hτ dP).1 ∈ boundaryGluingBetaEdges W h k hτ :=
  lMinusPrimedHattedTriangle_intersection_only_boundary hτ hqMode hfin
    jP jH hRetH dP dH hdP hdH heq

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: on a shared beta dart, the two retained
block triangles on its left have the same actual face successor. -/
theorem lMinusActualSideSharedTriangle_successors_eq
    (jP : TriangleCreationTime p) (jH : TriangleCreationTime z)
    (hRetH : ∀ d ∈ stageTriangleDartList z jH, d.1 ∈ (Q).edges)
    (dP dH : ℕ × Bool)
    (hdP : dP ∈ stageTriangleDartList p jP)
    (hdH : dH ∈ stageTriangleDartList z jH)
    (heq : lMinusPrimedDartImage hτ dP = (EH dH.1, dH.2)) :
    (lMinusPrimedDartImage hτ dP).1 ∈ boundaryGluingBetaEdges W h k hτ ∧
    lMinusPrimedDartImage hτ
        (kmswInfFaceSucc p
          (primedCode_finiteIncidence (boundaryGluingFutureStream W h k)
            hτ hfin) dP) =
      (EH (kmswInfFaceSucc
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
        (sourceAncestor_finite_incidence X renewalTime
          renewalTime_positiveSuccessTime qL) dH).1,
       (kmswInfFaceSucc
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
        (sourceAncestor_finite_incidence X renewalTime
          renewalTime_positiveSuccessTime qL) dH).2) := by
  have hbeta := lMinusActualSideSharedTriangleDart_mem_beta hτ hqMode hfin
    jP jH hRetH dP dH hdP hdH heq
  let U := boundaryGluingFutureStream W h k
  let z' := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hstream : z' = z := boundaryGluing_decoded_stream W h k hτ
  let j' : TriangleCreationTime z' := ⟨jH.val, by rw [hstream]; exact jH.property⟩
  have hlist : stageTriangleDartList z jH = stageTriangleDartList z' j' := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, j', hstream]
  have hdH' : dH ∈ stageTriangleDartList z' j' := hlist.symm ▸ hdH
  have hRetH' : ∀ d ∈ stageTriangleDartList z' j', d.1 ∈ (Q).edges := by
    intro d hd
    exact hRetH d (hlist ▸ hd)
  let hfH := sourceAncestor_finite_incidence X renewalTime
    renewalTime_positiveSuccessTime qL
  let c := kmswInfFaceSucc z' hfH dH
  have hc : c ∈ stageTriangleDartList z' j' :=
    rMinusWhole_triangle_succ_mem z' hfH j' dH hdH'
  let a : {a : ℕ × Bool // a.1 ∈ (Q).edges} := ⟨dH, hRetH' dH hdH'⟩
  let b : {a : ℕ × Bool // a.1 ∈ (Q).edges} := ⟨c, hRetH' c hc⟩
  have hQ : (Q).faceNext a.val b.val := ⟨⟨j', hdH', hRetH'⟩, rfl⟩
  have hcode : lMinusCodeWholeFaceNext rL qL hf
      (lMinusCodeHattedDart rL Q a) (lMinusCodeHattedDart rL Q b) :=
    Or.inr ⟨a, b, rfl, rfl, hQ⟩
  have hforward := lMinusCodeWholeFaceNext_actual_forward hτ hp P hqMode
    Tpath hfin hleft hk _ _ hcode
  rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk a,
    lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk b] at hforward
  have hprimed := lMinusPrimedCodeFaceNext_actual hτ hp P hqMode Tpath
    hfin hleft hk jP dP hdP
  refine ⟨hbeta, ?_⟩
  calc
    lMinusPrimedDartImage hτ
        (kmswInfFaceSucc p
          (primedCode_finiteIncidence U hτ hfin) dP) =
        kmswInfFaceSucc w (H.1 0) (lMinusPrimedDartImage hτ dP) := hprimed.2.symm
    _ = kmswInfFaceSucc w (H.1 0) (EH dH.1, dH.2) := congrArg _ heq
    _ = (EH c.1, c.2) := hforward.2

end ActualFaceSeam























































































end DirectedDistances.PaperProofs.Section5
