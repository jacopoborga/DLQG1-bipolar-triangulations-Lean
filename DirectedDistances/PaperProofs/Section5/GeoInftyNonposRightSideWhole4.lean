/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable9
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE

/-! module records the observed whole-realization existence and the remaining
observation-level identification obligations. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.Probability
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: the finite KMSW rotations intertwine under the
identity-on-edge-IDs stage equivalence induced by a shared code prefix. -/
theorem stageRot_comm_of_prefix {u v : ℕ → Fin 3} (n : ℕ)
    (hp : ∀ i < n, u i = v i) :
    let Φ := (kmswStageDirectedMapIsoOfPrefix u v n hp).toEquiv
    ∀ d, Φ (stageRot u n d) = stageRot v n (Φ d) := by
  intro Φ d
  have h := (kmswStageDirectedMapIsoOfPrefix u v n hp).rot_comm d
  change Φ ((kmswMap u n).rot d) = (kmswMap v n).rot (Φ d) at h
  change Φ (stageRot u n d) = stageRot v n (Φ d)
  simpa [kmswMap] using h

/-- Helper toward Lemma 5.5: the stopped observed prefix agrees coordinatewise
with the source stream before its boundary stopping time. -/
theorem rightSideObsNonpos_prefix_eq_source
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (x : XDP) (i : ℕ)
    (hi : i < boundaryHitTime (shiftedStream W 0) h k) :
    (rightSideObsNonpos x k W).1 i = shiftedStream W 0 i := by
  have hω : BoundaryHitWitnesses (fun j => shiftedCodePath W 0 (j + 1)) := by
    simpa only [shiftedCodePath, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel] using h
  have ht := rMinus_boundaryCodeStoppingTime_eq_boundaryHitTime k
    (shiftedCodePath W 0) hω
  have ht' : boundaryCodeStoppingTime k (shiftedCodePath W 0) =
      (boundaryHitTime (shiftedStream W 0) h k : ℕ∞) := by
    simpa only [shiftedCodePath, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel] using ht
  change boundaryPrefixCode k W i = shiftedStream W 0 i
  simp only [boundaryPrefixCode, codePastVector, ht', ENat.natCast_lt_natCast,
    ite_eq_left hi, shiftedCodePath]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

/-- Helper toward Lemma 5.5: for a source-coherent hatted path and a
nonpositive boundary index, the observed R-minus presentation has a complete
whole-side realization. This follows from the two observed block realizations. -/
theorem decodeRMinus_rightSideObsNonpos_wholeRealization_isSome_of_coherent
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      Coherent (if longest then XDP.ldp else XDP.sdp))
    (hk : k ≤ 0) :
    (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
      (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).wholeRealization.isSome := by
  exact RMinusSidePresentation.wholeRealization_isSome_of_blocks
    (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
      (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W))
    (by rw [decodeRMinus_boundaryIndex]; exact hk)
    (decodeRMinus_rightSideObsNonpos_blocksRealization_isSome
      (x := if longest then XDP.ldp else XDP.sdp) (W := W) (h := h) (k := k) hqMode)
































































end DirectedDistances.PaperProofs.Section5
