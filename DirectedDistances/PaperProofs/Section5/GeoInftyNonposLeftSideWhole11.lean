/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole10

/-! initial-port and whole-side rotation transport for the reconnected splice.

The raw splice's fixed-point requirement is not supplied by
`GeoInftyNonposLeftInitialStarNonfixed`: that module proves transport in
both cases. The fixed point is equivalent to a singleton retained hatted
source star. We therefore use `lMinusInitialSplicedRotationRelation` in
the corrected initial-port and whole-side statements, without an additional
fixed-point or geometric-rotation premise. The raw relation retains its
separate name. These are rotation helpers, not a proof of Lemma 5.5. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section GeometricGluing

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
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "C" => lMinusCodeBoundaryDart rL qL (0, false)
local notation "p₀" => lMinusCodePrimedDart rL Q (0, true)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the raw splice reaches the geometric root
successor exactly when the retained hatted source star is a singleton. -/
theorem lMinusSpliceRotationRelation_initial_root_iff_singleton :
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
      (.inr (E C)) (.inr (E p₀)) ↔
      {e : ℕ × Bool | e.1 ∈ (Q).edges ∧
        kmswLimitDartVertex
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e = 0} =
        {(((Q).boundary 0).1, false)} := by
  exact (lMinusSpliceRotationRelation_initial_root_fixed_iff
    hτ hp P hqMode Tpath hfin hleft hk).trans
      (lMinusHattedRotation_initial_eq_self_iff_singleton hqMode)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the exact counterexample criterion for the
raw initial-port iff is an additional retained hatted source dart. The
failing target cell is the reverse dart of the retained missing primed root.
This criterion does not assert existence of a nonfixed configuration. -/
theorem lMinusSpliceRotationRelation_initial_boundary_counterexample_iff :
    (geometricSideRelation S .rotation
        (Φ (.inr (E C))) (Φ (.inr (E p₀))) ∧
      ¬ lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E C)) (.inr (E p₀))) ↔
      ∃ e : ℕ × Bool, e.1 ∈ (Q).edges ∧
        kmswLimitDartVertex
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e = 0 ∧
        e ≠ (((Q).boundary 0).1, false) := by
  constructor
  · rintro ⟨_, hn⟩
    by_contra hex
    apply hn
    apply (lMinusSpliceRotationRelation_initial_root_iff_singleton
      hτ hp P hqMode Tpath hfin hleft hk).mpr
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨lMinus_hatted_boundary_mem _ qL 0,
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩⟩, ?_⟩
    intro e he
    by_contra hne
    exact hex ⟨e, he.1, he.2, hne⟩
  · rintro ⟨e, hedge, hvertex, hne⟩
    refine ⟨lMinusGluedCellEquiv_initial_root_rotation
      hτ hp P hqMode Tpath hfin hleft hk, ?_⟩
    intro hr
    have hs := (lMinusSpliceRotationRelation_initial_root_iff_singleton
      hτ hp P hqMode Tpath hfin hleft hk).mp hr
    exact hne ((Set.eq_singleton_iff_unique_mem.mp hs).2 e ⟨hedge, hvertex⟩)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the reconnected initial boundary port has
the geometric rotation relation for every target vertex or dart cell. -/
theorem lMinusInitialSplicedRotationRelation_rotation_iff_initial_boundary
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
      (.inr (E C)) v ↔
      geometricSideRelation S .rotation (Φ (.inr (E C))) (Φ v) := by
  exact (lMinusGluedCellEquiv_rotation_spliced_transport_iff
    hτ hp P hqMode Tpath hfin hleft hk C).mpr
      (lMinusCodeInitialSplicedRotation_initial_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk) v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: all-target transport at the raw initial
boundary port is equivalent to a singleton retained hatted source star.
The singleton condition is a conclusion of this equivalence, not a premise. -/
theorem lMinusSpliceRotationRelation_initial_boundary_transport_iff_singleton :
    (∀ v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode),
      lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E C)) v ↔
        geometricSideRelation S .rotation (Φ (.inr (E C))) (Φ v)) ↔
      {e : ℕ × Bool | e.1 ∈ (Q).edges ∧
        kmswLimitDartVertex
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e = 0} =
        {(((Q).boundary 0).1, false)} := by
  have hroot := lMinusGluedCellEquiv_initial_root_rotation
    hτ hp P hqMode Tpath hfin hleft hk
  constructor
  · intro ht
    exact (lMinusSpliceRotationRelation_initial_root_iff_singleton
      hτ hp P hqMode Tpath hfin hleft hk).mp ((ht (.inr (E p₀))).mpr hroot)
  · intro hs v
    have hraw : lMinusGluedSpliceRotation
        hτ hp P hqMode Tpath hfin hleft hk (E C) = E p₀ :=
      (lMinusSpliceRotationRelation_initial_root_iff_singleton
        hτ hp P hqMode Tpath hfin hleft hk).mpr hs
    have hrec : lMinusGluedInitialSplicedRotation
        hτ hp P hqMode Tpath hfin hleft hk (E C) = E p₀ :=
      (lMinusInitialSplicedRotationRelation_rotation_iff_initial_boundary
        hτ hp P hqMode Tpath hfin hleft hk (.inr (E p₀))).mpr hroot
    cases v with
    | inl v => rfl
    | inr e =>
      have ht := lMinusInitialSplicedRotationRelation_rotation_iff_initial_boundary
        hτ hp P hqMode Tpath hfin hleft hk (.inr e)
      change lMinusGluedInitialSplicedRotation
          hτ hp P hqMode Tpath hfin hleft hk (E C) = e ↔ _ at ht
      change lMinusGluedSpliceRotation
          hτ hp P hqMode Tpath hfin hleft hk (E C) = e ↔ _
      rw [hraw, ← hrec]
      exact ht

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the full rotation iff recorded in Whole9,
with the raw splice replaced explicitly by the reconnected rotation. -/
theorem lMinusInitialSplicedRotationRelation_rotation_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  exact lMinusGluedCellEquiv_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk u v

end GeometricGluing














































end DirectedDistances.PaperProofs.Section5
