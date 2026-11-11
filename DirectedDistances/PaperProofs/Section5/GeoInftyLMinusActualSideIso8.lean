/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso6

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section ActualFaceCycle

variable {W : ℤ → Fin 3}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left

/-- Helper toward Lemma 5.5: an actual retained face successor stays in the
same run-zero creation triangle, and every dart of that triangle is retained. -/
theorem lMinusActualFaceNext_triangle_cycle
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    ∃ j : TriangleCreationTime w,
      d ∈ stageTriangleDartList w j ∧
      e ∈ stageTriangleDartList w j ∧
      ∀ a ∈ stageTriangleDartList w j, a.1 ∈ (S).edges := by
  obtain ⟨j, hd, hall⟩ := lMinusActualFaceNext_triangle hp P d e hde
  have he := rMinusWhole_triangle_succ_mem w (H.1 0) j d hd
  rw [hde.2] at he
  exact ⟨j, hd, he, hall⟩

end ActualFaceCycle

section FaceTransport

variable {W : ℤ → Fin 3}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
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
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "C" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: an actual face successor whose first dart is
known to lie in one complete code-block triangle transports back to the
branchwise code face relation. This isolates the remaining seam classification. -/
theorem lMinusCodeWholeFaceNext_actual_reverse_of_block_triangle
    (d e : LMinusCodeGluedDart rL Q)
    (hde : (S).faceNext (D d).val (D e).val)
    (hblock :
      (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
          (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ),
        d = lMinusCodePrimedDart rL Q a ∧
          a ∈ stageTriangleDartList
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) j) ∨
      (∃ a : {a : ℕ × Bool // a.1 ∈ (Q).edges},
        ∃ j : TriangleCreationTime (hatCodes (boundaryGluingFutureStream W h k) hτ),
          d = lMinusCodeHattedDart rL Q a ∧
            a.val ∈ stageTriangleDartList
              (hatCodes (boundaryGluingFutureStream W h k) hτ) j ∧
            ∀ c ∈ stageTriangleDartList
              (hatCodes (boundaryGluingFutureStream W h k) hτ) j,
              c.1 ∈ (Q).edges)) :
    lMinusCodeWholeFaceNext rL qL hf d e := by
  rcases hblock with ⟨a, j, hd, ha⟩ | ⟨a, j, hd, ha, hall⟩
  · exact lMinusCodeWholeFaceNext_actual_reverse_of_primed_triangle
      hτ hp P hqMode Tpath hfin hleft hk d e hde a j hd ha
  · exact lMinusCodeWholeFaceNext_actual_reverse_of_hatted_triangle
      hτ hp P hqMode Tpath hfin hleft hk d e hde a j hd ha hall

include hτ hp P hqMode Tpath hfin hleft hk in



theorem lMinusGluedCellEquiv_faceNext_transport_forward
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode))
    (hcode : lMinusCodeWholeSideRelation hτ hqMode hfin
        .faceNext
        ((lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u)
        ((lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v)) :
    geometricSideRelation S .faceNext
      (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
      (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  cases u with
  | inl u => simp [lMinusCodeCellEquiv, lMinusCodeWholeSideRelation] at hcode ⊢
  | inr u =>
    cases v with
    | inl v => simp [lMinusCodeCellEquiv, lMinusCodeWholeSideRelation] at hcode ⊢
    | inr v =>
      have hu :
          (lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
              (Sum.inr u) = Sum.inr
                ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u) := by
        simp [lMinusCodeCellEquiv]
      have hv :
          (lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
              (Sum.inr v) = Sum.inr
                ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v) := by
        simp [lMinusCodeCellEquiv]
      rw [hu, hv] at hcode
      change lMinusCodeWholeFaceNext rL qL hf
        ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u)
        ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v) at hcode
      have hforward := lMinusCodeWholeFaceNext_actual_forward
        hτ hp P hqMode Tpath hfin hleft hk
        ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u)
        ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v) hcode
      have hcomp (d : LMinusGluedDart hτ hqMode) :
          (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
            ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm d)).val =
            (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val := by
        simp [lMinusCodeGluedDartEquiv, lMinusCodeToGluedDartEquiv]
      change (S).faceNext
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk u).val
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk v).val
      rw [← hcomp u, ← hcomp v]
      exact hforward

end FaceTransport













































end DirectedDistances.PaperProofs.Section5
