/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole6
public import DirectedDistances.PaperProofs.Section5.GeometricSideClass

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section DecodedEdgeIdentification

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

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "U" => boundaryGluingFutureStream W h k
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "w0" => shiftedStream W 0

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic endpoint code is the run-zero
vertex at either side of every encoded edge class. -/
theorem lMinusCodeEndpointVertex_image (s : Bool)
    (e : LMinusCodeGluedEdge rL Q) :
    lMinusCodeVertexImage hτ hp P hqMode Tpath hfin hleft hk
        (lMinusCodeEndpointVertex X rL qL s e).val =
      kmswLimitDartVertex w0
        (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (e, s)).val := by
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a =>
      have hflip := lMinusCodePrimedSideFlip_observation (longest := longest) hτ hfin a
      change lMinusCodeVertexImage hτ hp P hqMode Tpath hfin hleft hk
          (lMinusCodeEndpoint rL Q s (⟦Sum.inl a⟧ : LMinusCodeGluedEdge rL Q)) =
        kmswLimitDartVertex w0
          (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
            (⟦Sum.inl a⟧, s)).val
      change lMinusCodeRawVertexImage hτ
          (lMinusCodeRawEndpoint rL Q s (.inl a)) = _
      have hprimed : lMinusCodePrimedDart rL Q
          (a, s ^^ lMinusCodePrimedSideFlip rL a) =
            (⟦Sum.inl a⟧, s) := by
        simp [lMinusCodePrimedDart]
      rw [← hprimed, lMinusCodeGluedDartEquiv_primed
        hτ hp P hqMode Tpath hfin hleft hk]
      rw [hflip]
      simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      have himage := lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath hfin hleft hk
        s (.inl a)
      simpa [lMinusCodeRawEndpoint, lMinusBlockEdgeImage] using himage
  | inr a =>
      change lMinusCodeRawVertexImage hτ
          (lMinusCodeRawEndpoint rL Q s (.inr a)) = _
      change lMinusCodeRawVertexImage hτ
          (lMinusCodeRawEndpoint rL Q s (.inr a)) =
        kmswLimitDartVertex w0
          (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
            (lMinusCodeHattedDart rL Q ⟨(a.1, s), a.2⟩)).val
      rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk]
      exact lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath hfin hleft hk s
        (.inr a)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the vertex equivalence evaluates by the
intrinsic vertex code. -/
theorem lMinusCodeToGluedVertexEquiv_image
    (v : LMinusCodeGluedVertex rL Q) :
    Setoid.kerLift (lMinusBlockVertexImage hτ hqMode)
        (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk v) =
      lMinusCodeVertexImage hτ hp P hqMode Tpath hfin hleft hk v.val := by
  have hh := lMinusGluedToCodeVertex_image hτ hp P hqMode Tpath hfin hleft hk
    (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk v)
  change lMinusCodeVertexImage hτ hp P hqMode Tpath hfin hleft hk
      ((lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
        (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk v)).val = _ at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh.symm

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the code-to-gluing dart equivalence commutes
with both endpoint maps under the code-to-gluing vertex equivalence. -/
theorem lMinusCodeToGluedDartEndpoint_compat
    (d : LMinusCodeGluedDart rL Q) :
    lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk
        (lMinusCodeEndpointVertex X rL qL d.2 d.1) =
      lMinusGluedDartEndpoint hτ hqMode
        (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d) := by
  apply (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
  apply Subtype.ext
  rw [lMinusGluedVertexEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
  rw [lMinusCodeToGluedVertexEquiv_image hτ hp P hqMode Tpath hfin hleft hk]
  rw [lMinusGluedDartEndpoint_equiv hτ hp P hqMode Tpath hfin hleft hk]
  rw [lMinusCodeToGluedDartEquiv_equiv hτ hp P hqMode Tpath hfin hleft hk]
  exact lMinusCodeEndpointVertex_image hτ hp P hqMode Tpath hfin hleft hk
    d.2 d.1











































end DecodedEdgeIdentification

end DirectedDistances.PaperProofs.Section5
