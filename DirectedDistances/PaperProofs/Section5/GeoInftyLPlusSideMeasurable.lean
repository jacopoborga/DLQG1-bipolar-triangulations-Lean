/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff11

/-! # Measurability of the nonnegative left code-built side

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "V" => lPlusBlockVertexImage (M := MH) hτ
local notation "D" => lPlusBlockDartImage (M := MH) hτ
local notation "E" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "C" => lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5. The nonnegative L+ block assembly keeps the
permanent vertex and edge IDs of the deleted prefix, primed block, and hatted
left block. Its dart rotation is the corrected code-glued permutation. The
remaining geometric markings use the fixed IDs in the source whole-plane
realization. This is the explicit block object before an observation-level
decoder from `LPlusSidePresentation` has been established. -/
@[expose] noncomputable def lPlusCodeBlockSide : GeometricSideSubmap where
  vertices := Set.range V
  edges := {e | ∃ b : Bool, (e, b) ∈ Set.range D}
  west := edgeWest (shiftedStream W 0)
  east := edgeEast (shiftedStream W 0)
  present := {e | EdgePresent (shiftedStream W 0) e}
  rotation d e := ∃ a b : Q, (E a).val = d ∧ C a = b ∧ (E b).val = e
  faceNext := (m0GeodesicSide hp P .left).faceNext
  root := boundaryVertex (shiftedStream W 0) h k
  boundary := m0GeodesicBoundaryDart (shiftedStream W 0) h k .left
  seam := m0GeodesicSeam P

/-- Helper toward Lemma 5.5. The assembled vertex field consists exactly of
the fixed-ID block images. -/
theorem lPlusCodeBlockSide_vertices :
    (lPlusCodeBlockSide (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) (hk := hk)).vertices =
      Set.range V := rfl

/-- Helper toward Lemma 5.5. The assembled edge field retains the geometric
edge IDs in the block dart images, including missing edges. -/
theorem lPlusCodeBlockSide_edges :
    (lPlusCodeBlockSide (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) (hk := hk)).edges =
      {e | ∃ b : Bool, (e, b) ∈ Set.range D} := rfl



























end DirectedDistances.PaperProofs.Section5
