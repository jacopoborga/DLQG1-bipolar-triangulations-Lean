/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideMarkedIso

 

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: retained face successors supplied by the two
code blocks, carried to the edge-quotient darts. Primed faces are the finite
creation triangles of the observed primed code; hatted faces are exactly the
retained triangles in its `GeometricSideSubmap`. No face crossing the gluing
seam is inserted by this block-wise relation: each source face is in one block.
At an identified boundary edge both block successors are recorded until the
seam successor is identified with the geometric whole-side successor. -/
@[expose] def lMinusCodeWholeFaceNext {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1)
    (d e : LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) : Prop :=
  (∃ a b : ℕ × Bool,
    lMinusCodePrimedDart r _ a = d ∧ lMinusCodePrimedDart r _ b = e ∧
      (∃ j : TriangleCreationTime r.code.1,
        a ∈ stageTriangleDartList r.code.1 j ∧
          kmswInfFaceSucc r.code.1 hf a = b)) ∨
  (∃ a b : {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges},
    lMinusCodeHattedDart r _ a = d ∧ lMinusCodeHattedDart r _ b = e ∧
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).faceNext
        a.val b.val)

section WholeFaceTransport

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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
    (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
      selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

/-- Helper toward Lemma 5.5: the code-side cell carrier for the face tag is
transported to the existing glued cell carrier by its proved vertex and dart
equivalences. This relation supplies only the `.faceNext` tag. -/
@[expose] noncomputable def lMinusCodeCellEquiv :
    Sum (LMinusGluedVertex hτ hqMode) (LMinusCodeGluedDart rL Q) ≃
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) :=
  Equiv.sumCongr (Equiv.refl _) (lMinusCodeToGluedDartEquiv
    hτ hp P hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: the code-built face-successor branch on cells.
Other tags are intentionally outside this face-only helper. -/
@[expose] def lMinusCodeWholeSideRelation :
    TruncationRelation →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusCodeGluedDart rL Q) →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusCodeGluedDart rL Q) → Prop
  | .faceNext, .inr d, .inr e => lMinusCodeWholeFaceNext rL qL hf d e
  | _, _, _ => False



































end WholeFaceTransport

end DirectedDistances.PaperProofs.Section5
