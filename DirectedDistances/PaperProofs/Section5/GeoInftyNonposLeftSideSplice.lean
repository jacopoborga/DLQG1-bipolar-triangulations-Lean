/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSide


















public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a first return before the end of a gap in
another set is also first return to their union. This is a set-theoretic
calculation; the concrete block gap and return are proved below. -/
theorem firstReturn_union_of_gap {α : Type*} (σ : α → α)
    (A B : Set α) (x z : α) (n t : ℕ)
    (ht : 0 < t) (hz : σ^[t] x = z) (hzB : z ∈ B)
    (hB : ∀ j : ℕ, 0 < j → j < t → σ^[j] x ∉ B)
    (hn : 0 < n) (hnB : σ^[n] x ∈ B)
    (hA : ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A) :
    0 < t ∧ σ^[t] x = z ∧ z ∈ A ∪ B ∧
      ∀ j : ℕ, 0 < j → j < t → σ^[j] x ∉ A ∪ B := by
  have htn : t ≤ n := by
    by_contra hnot
    exact hB n hn (by omega) hnB
  refine ⟨ht, hz, Or.inr hzB, ?_⟩
  intro j hj hjt hmem
  rcases hmem with ha | hb
  · exact hA j hj (lt_of_lt_of_le hjt htn) ha
  · exact hB j hj hjt hb

/-- Helper toward Lemma 5.5: a minimal positive return has a unique
endpoint among retained darts. -/
theorem firstReturn_endpoint_unique {α : Type*} (σ : α → α) (A : Set α)
    {x y z : α} (hy : y ∈ A) (hz : z ∈ A)
    (hyret : ∃ n : ℕ, 0 < n ∧ σ^[n] x = y ∧
      ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A)
    (hzret : ∃ n : ℕ, 0 < n ∧ σ^[n] x = z ∧
      ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A) : y = z := by
  obtain ⟨n, hn, hny, hngap⟩ := hyret
  obtain ⟨m, hm, hmz, hmgap⟩ := hzret
  have hnm : n = m := by
    apply Nat.le_antisymm
    · by_contra hnot
      exact hngap m hm (by omega) (hmz.symm ▸ hz)
    · by_contra hnot
      exact hmgap n hn (by omega) (hny.symm ▸ hy)
  exact hny.symm.trans (hnm ▸ hmz)

/-- Helper toward Lemma 5.5: a drawing's induced rotation fixes a retained
dart exactly when it is the only retained dart at its vertex. Edge identities,
rather than just pairs of endpoints, occur in the singleton condition. -/
theorem drawingFirstReturn_eq_self_iff_singleton {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (A : Set D) (d : A) :
    drawingFirstReturnPerm P A d = d ↔
      {e | e ∈ A ∧ vert e = vert d.val} = {d.val} := by
  have hccw := drawingFirstReturnCcwObligation_holds P A d
  change CcwSuccessor _ _ _ _ at hccw
  constructor
  · intro he
    rw [he] at hccw
    rcases hccw.2.2.2 with h | h
    · exact h.2
    · exact False.elim (h.1 rfl)
  · intro he
    apply Subtype.ext
    have hm := hccw.2.2.1
    rw [he] at hm
    exact Set.mem_singleton_iff.mp hm

/-- Helper toward Lemma 5.5: an initial-only adjustment cutting the initial
shared dart out of the hatted cycle before applying the two-block splice.
Swapping the inputs also handles a fixed initial dart. This uses only the
block codes and interface; it is not asserted to be the whole-side rotation. -/
@[expose] noncomputable def lMinusCodeInitialAdjustedRotation {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1) :
    Equiv.Perm (LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :=
  let c := lMinusCodeBoundaryDart r q (0, false)
  let H := (lMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
  lMinusCodeSpliceRotation r q hf * Equiv.swap c (H.symm c)

/-- Helper toward Lemma 5.5: the initial adjustment preserves bijectivity
without a fixed-point, side-rotation, or geometric-layout hypothesis. -/
theorem lMinusCodeInitialAdjustedRotation_bijective {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1) :
    Function.Bijective (lMinusCodeInitialAdjustedRotation r q hf) :=
  (lMinusCodeInitialAdjustedRotation r q hf).bijective

/-- Helper toward Lemma 5.5: the adjustment changes only the initial dart
and its hatted predecessor, keeping the original splice at every other dart. -/
theorem lMinusCodeInitialAdjustedRotation_apply_of_ne {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q))
    (hc : d ≠ lMinusCodeBoundaryDart r q (0, false))
    (hp : d ≠ ((lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))).symm
        (lMinusCodeBoundaryDart r q (0, false))) :
    lMinusCodeInitialAdjustedRotation r q hf d = lMinusCodeSpliceRotation r q hf d := by
  change lMinusCodeSpliceRotation r q hf (Equiv.swap _ _ d) = _
  rw [Equiv.swap_apply_of_ne_of_ne hc hp]

/-- Helper toward Lemma 5.5: the second input changed by the initial
adjustment is precisely the image of the hatted predecessor, retaining
its complete geometric edge identity and endpoint bit. -/
theorem lMinusCodeHattedRotation_initial_predecessor {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
    let d : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((M.boundary 0).1, false), lMinus_hatted_boundary_mem x q 0⟩
    ((lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))).symm
        (lMinusCodeBoundaryDart r q (0, false)) =
      lMinusCodeHattedDart r M ((lMinusHattedRotation x q).symm d) := by
  rw [Equiv.Perm.extendDomain_symm]
  exact Equiv.Perm.extendDomain_apply_image (lMinusHattedRotation x q).symm
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q)) _

/-- Helper toward Lemma 5.5: the hatted predecessor used in the adjustment
is based at the initial shared vertex. Hence the correction is confined to
that vertex, rather than to an endpoint-based identification of edges. -/
theorem lMinusHattedRotation_initial_predecessor_vertex (x : XDP)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
    let d : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((M.boundary 0).1, false), lMinus_hatted_boundary_mem x q 0⟩
    kmswLimitDartVertex (boltzmannKMSWStream (pathCode q.val))
      ((lMinusHattedRotation x q).symm d).val = 0 := by
  let w := boltzmannKMSWStream (pathCode q.val)
  let d : {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges} :=
    ⟨(((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).boundary 0).1,
      false), lMinus_hatted_boundary_mem x q 0⟩
  have hv := drawingFirstReturn_sameVertex
    (monotoneFamilyDrawing w
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (monotone_family_all w))
    {e : ℕ × Bool | e.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges}
    ((lMinusHattedRotation x q).symm d)
  change kmswLimitDartVertex w
      (lMinusHattedRotation x q ((lMinusHattedRotation x q).symm d)).val =
    kmswLimitDartVertex w ((lMinusHattedRotation x q).symm d).val at hv
  rw [Equiv.apply_symm_apply] at hv
  exact hv.symm.trans
    (kmswLeftBoundary_infinite_present_path w
      (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)).2.2.1

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
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "B" => primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "F" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the initial fixed-point question is exactly
whether the retained hatted source star has one geometric dart. -/
theorem lMinusHattedRotation_initial_eq_self_iff_singleton :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d = d ↔
      {e : ℕ × Bool | e.1 ∈ (Q).edges ∧
        kmswLimitDartVertex
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e = 0} =
        {(((Q).boundary 0).1, false)} := by
  let w := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hs : kmswLimitDartVertex w (((Q).boundary 0).1, false) = 0 :=
    (kmswLeftBoundary_infinite_present_path w
      (sourceAncestor_left_transient _ renewalTime renewalTime_positiveSuccessTime qL)
      (sourceAncestor_left_nonneg _ renewalTime renewalTime_positiveSuccessTime qL)
      (sourceAncestor_right_unbounded _ renewalTime renewalTime_positiveSuccessTime qL)).2.2.1
  have he := drawingFirstReturn_eq_self_iff_singleton
    (monotoneFamilyDrawing w
      (sourceAncestor_finite_incidence _ renewalTime renewalTime_positiveSuccessTime qL)
      (monotone_family_all w)) {e : ℕ × Bool | e.1 ∈ (Q).edges}
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  change _ ↔ {e | e.1 ∈ (Q).edges ∧ kmswLimitDartVertex w e =
    kmswLimitDartVertex w (((Q).boundary 0).1, false)} = _ at he
  rw [hs] at he
  exact he

/-- Helper toward Lemma 5.5: the initial shared port is immediately
followed, in the full future rotation, by the reverse dart of the retained
missing primed root. This uses the actual first source-exit triangle. -/
theorem lMinus_initial_future_rotation :
    kmswInfRot U hfin
        (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
      primedLimitDartMap U hτ (0, true) := by
  let t := sourceFlowNL U hτ 0
  have hc : U (t - 1) = 0 := by
    dsimp only [t]
    rw [sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code U hτ 0
  obtain ⟨hbase, hnext, _⟩ := sourceFlow_firstLeftExit_triangle U hτ
  have hUL : (kmswStage U (t - 1)).UL.dropLast.reverse = [] := hbase.2.2.2.1
  let j : TriangleCreationTime U := ⟨t - 1, Or.inl hc⟩
  have hcycle := kmswInfFaceSucc_stageTriangle_cycle U hfin j
  rw [stageTriangleDartTriple_left_fresh U j hc hUL] at hcycle
  have hm : kmswLLCreatedEdge U (walkNL U hτ 0) =
      (kmswStage U (t - 1)).nextEdge + 1 := by
    rw [← sourceFlowNL_eq_walkNL]
    change kmswLLCreatedEdge U t = _
    dsimp only [kmswLLCreatedEdge]
    change (kmswStage U t).nextEdge = (kmswStage U (t - 1)).nextEdge + 2 at hnext
    omega
  have hcorner : (kmswInfRot U hfin).symm
      (kmswLLCreatedEdge U (walkNL U hτ 0), true) = (act U (t - 1), false) := by
    rw [hm]
    exact hcycle.2.2.1
  have hr := congrArg (kmswInfRot U hfin) hcorner
  rw [Equiv.apply_symm_apply] at hr
  rw [hattedLeftBoundaryBeta0EdgeCorrespondence_proved U hτ hfin
      (hatBoundaryHitWitnesses U hτ) 0,
    beta0_westBoundary_stream_eq_left_exit U hfin (hatBoundaryHitWitnesses U hτ) hτ 0]
  change kmswInfRot U hfin (act U (t - 1), false) =
    (primedLimitEdgeMap U hτ 0, true ^^ primedLimitSideFlip U hτ 0)
  rw [primedLimitEdgeMap_zero, primedLimitSideFlip_zero]
  exact hr.symm

/-- Helper toward Lemma 5.5: the primed initial exterior corner goes
from the shared port to the reverse dart of its retained missing root. -/
theorem lMinusPrimedRotation_initial_corner :
    kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) (B 0, true) = (0, true) := by
  have hd : primedLimitDartMap U hτ (B 0, true) =
      (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) := by
    change (primedLimitEdgeMap U hτ (B 0), true ^^ primedLimitSideFlip U hτ (B 0)) = _
    rw [lMinusPrimedLimitSideFlip_beta hτ hfin 0]
    exact Prod.ext
      (gluingBoundary_same_index U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0
        (primedIntervalBase (primedSimInput U) hτ 0 + 1) le_rfl).1.symm rfl
  apply primedLimitDartMap_injective U hτ
  apply firstReturn_endpoint_unique (kmswInfRot U hfin : _ → _)
    (Set.range (primedLimitDartMap U hτ))
    (Set.mem_range_self _) (Set.mem_range_self _)
    (lMinus_primed_future_firstReturn hτ hfin (B 0, true))
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · rw [Function.iterate_one, hd]
    exact lMinus_initial_future_rotation hτ hfin
  · intro j hj hj1
    omega

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the actual side successor at the initial
shared port is the reverse dart of the retained missing primed root. The
run-zero scan skips only darts outside the entire future image. -/
theorem lMinus_initial_side_rotation :
    (S).rotation (EH ((Q).boundary 0).1, false)
      (lMinusPrimedDartImage hτ (0, true)) := by
  let J : (ℕ × Bool) → ℕ × Bool :=
    fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  let d : ℕ × Bool :=
    (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false)
  have hd : (EH ((Q).boundary 0).1, false) = J d := by
    change (EH (kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) 0), false) = _
    rw [boundaryGluing_decoded_stream W h k hτ]
    rfl
  have hr : J (kmswInfRot U hfin d) = lMinusPrimedDartImage hτ (0, true) := by
    rw [show kmswInfRot U hfin d = primedLimitDartMap U hτ (0, true) from
      lMinus_initial_future_rotation hτ hfin]
    rfl
  obtain ⟨n, hn, hne, hgap⟩ := lMinus_future_firstReturn (H := H) hfin d
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hd]
    exact hne.trans hr
  · intro j hj hjn hmem
    apply hgap j hj hjn
    have hset := Set.ext_iff.mp
      (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk)
      ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
        (EH ((Q).boundary 0).1, false))
    rcases hset.mp hmem with ⟨a, ha⟩ | ⟨a, ha⟩
    · refine ⟨primedLimitDartMap U hτ a, ?_⟩
      change lMinusPrimedDartImage hτ a = _
      exact ha.trans (congrArg ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]) hd)
    · refine ⟨(hatLimitEdgeMap U hτ a.val.1, a.val.2), ?_⟩
      change (EH a.val.1, a.val.2) = _
      exact ha.trans (congrArg ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]) hd)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at a positive shared vertex, first return to
the entire retained side from the incoming port is the hatted block return.
No condition about the splice or the side rotation is assumed. -/
theorem lMinus_positive_incoming_side_rotation (i : ℕ) :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
    let e := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d
    (S).rotation (EH d.val.1, d.val.2) (EH e.val.1, e.val.2) := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let A := Set.range (lMinusPrimedDartImage hτ)
  let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  obtain ⟨n, m, hn, _, hna, _, hgap, _⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ :=
    lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  have hnD : (σ : _ → _)^[n] (D d) ∈ Set.range D := by
    rw [hna]
    exact ⟨⟨(((Q).boundary (i + 1)).1, false),
      lMinus_hatted_boundary_mem _ qL (i + 1)⟩, rfl⟩
  have hret := firstReturn_union_of_gap (σ : _ → _) A (Set.range D) (D d)
    (D (lMinusHattedRotation _ qL d)) n t ht hte
    ⟨lMinusHattedRotation _ qL d, rfl⟩ htgap hn hnD hgap
  refine ⟨t, hret.1, hret.2.1, ?_⟩
  intro j hj hjt hmem
  apply hret.2.2.2 j hj hjt
  rw [← lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
  exact hmem

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: at a positive shared vertex, first return to
the entire retained side from the outgoing port is the primed block return.
This uses geometric edge IDs and the proved endpoint-bit correction. -/
theorem lMinus_positive_outgoing_side_rotation (i : ℕ) :
    let e := kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) (B (i + 1), true)
    (S).rotation (EH ((Q).boundary (i + 1)).1, false)
      (lMinusPrimedDartImage hτ e) := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  have hb (j : ℕ) : ((Q).boundary j).1 =
      kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  obtain ⟨n, hn, hna, hgap⟩ :=
    lMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ :=
    lMinusPrimedDartImage_firstReturn (H := H) hτ hfin (B (i + 1), true)
  rw [lMinusPrimedDartImage_boundary hτ hfin (i + 1) true,
    ← hb (i + 1)] at hte htgap
  have hnP : (σ : _ → _)^[n] (EH ((Q).boundary (i + 1)).1, false) ∈
      Set.range (lMinusPrimedDartImage hτ) := by
    rw [hna]
    refine ⟨(B i, false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin i false, ← hb i]
    rfl
  have hret := firstReturn_union_of_gap (σ : _ → _) (Set.range D)
    (Set.range (lMinusPrimedDartImage hτ))
    (EH ((Q).boundary (i + 1)).1, false) _ n t ht hte
    ⟨_, rfl⟩ htgap hn hnP hgap
  refine ⟨t, hret.1, hret.2.1, ?_⟩
  intro j hj hjt hmem
  apply hret.2.2.2 j hj hjt
  rw [Set.union_comm, ← lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
  exact hmem

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic shared port is precisely the
primed port with the reversed endpoint bit, also at boundary index zero. -/
theorem lMinusCodeBoundaryDart_eq_primed (i : ℕ) (b : Bool) :
    lMinusCodeBoundaryDart rL qL (i, b) =
      lMinusCodePrimedDart rL Q (B i, !b) := by
  apply (F).injective
  apply Subtype.ext
  rw [lMinusCodeGluedDartEquiv_primed]
  change (F (lMinusCodeHattedDart rL Q
    ⟨(((Q).boundary i).1, b), lMinus_hatted_boundary_mem _ qL i⟩)).val = _
  rw [lMinusCodeGluedDartEquiv_hatted]
  change (EH ((Q).boundary i).1, b) = lMinusPrimedDartImage hτ (B i, !b)
  rw [lMinusPrimedDartImage_boundary hτ hfin i (!b), Bool.not_not]
  congr 2
  change kmswLeftBoundaryEdge
    (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
  rw [boundaryGluing_decoded_stream W h k hτ]

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: because the boundary correction fixes the
initial port, the prescribed splice has the actual initial successor
exactly when the hatted rotation fixes its initial boundary dart.
This is an equivalence of explicit permutation calculations, not an
assumed fixed-point or rotation assertion. -/
theorem lMinusCodeSpliceRotation_initial_eq_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (0, false)) =
      lMinusCodePrimedDart rL Q (0, true) ↔
        lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d = d := by
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  have hH : Hrot.extendDomain Hemb c = lMinusCodeHattedDart rL Q (Hrot d) :=
    Hrot.extendDomain_apply_image Hemb d
  have hC : lMinusBoundaryCornerPerm.extendDomain Cemb c = c :=
    lMinusBoundaryCornerPerm.extendDomain_apply_image Cemb (0, false)
  have hP : Prot.extendDomain Pemb c = lMinusCodePrimedDart rL Q (0, true) := by
    dsimp only [c]
    rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk 0 false]
    have he : Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B 0, true)) =
        lMinusCodePrimedDart rL Q (Prot (B 0, true)) :=
      Prot.extendDomain_apply_image Pemb (B 0, true)
    change Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B 0, true)) = _
    rw [he]
    have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) := by
      dsimp only [Prot]
      congr 1
      exact lMinus_primed_observation_code hτ
    rw [hrot, lMinusPrimedRotation_initial_corner hτ hfin]
  change Prot.extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb c)) = lMinusCodePrimedDart rL Q (0, true) ↔ Hrot d = d
  constructor
  · intro he
    have h1 := (Prot.extendDomain Pemb).injective (he.trans hP.symm)
    have h2 := (lMinusBoundaryCornerPerm.extendDomain Cemb).injective (h1.trans hC.symm)
    apply lMinusCodeHattedDart_injective rL qL
    exact hH.symm.trans h2
  · intro he
    have hfix : Hrot.extendDomain Hemb c = c := by
      rw [hH, he]
      rfl
    rw [hfix, hC]
    exact hP

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate always has the actual
initial successor, the reverse dart of the retained missing primed root.
No assertion about the hatted initial fixed point enters the proof. -/
theorem lMinusCodeInitialAdjustedRotation_initial :
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (0, false)) =
      lMinusCodePrimedDart rL Q (0, true) := by
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  have hC : lMinusBoundaryCornerPerm.extendDomain Cemb c = c :=
    lMinusBoundaryCornerPerm.extendDomain_apply_image Cemb (0, false)
  change Prot.extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb (Equiv.swap c ((Hrot.extendDomain Hemb).symm c) c))) = _
  rw [Equiv.swap_apply_left, Equiv.apply_symm_apply, hC]
  dsimp only [c]
  rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk 0 false]
  have he : Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B 0, true)) =
      lMinusCodePrimedDart rL Q (Prot (B 0, true)) :=
    Prot.extendDomain_apply_image Pemb (B 0, true)
  change Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B 0, true)) = _
  rw [he]
  have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) := by
    dsimp only [Prot]
    congr 1
    exact lMinus_primed_observation_code hτ
  rw [hrot, lMinusPrimedRotation_initial_corner hτ hfin]

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: at each outgoing positive-interface port,
the hatted exterior corner and the boundary correction cancel. The splice
then applies the primed block rotation to that very same port. -/
theorem lMinusCodeSpliceRotation_outgoing (i : ℕ) :
    lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
      lMinusCodePrimedDart rL Q
        (kmswInfRot (rL).code.1 (lMinus_primed_observation_finiteIncidence hτ hfin)
          (B (i + 1), true)) := by
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  have hH : Hrot.extendDomain Hemb
      (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
        lMinusCodeBoundaryDart rL qL (i, true) := by
    have he := Hrot.extendDomain_apply_image Hemb
      ⟨(((Q).boundary (i + 1)).1, false), lMinus_hatted_boundary_mem _ qL (i + 1)⟩
    dsimp only [Hemb, Equiv.ofInjective, Equiv.ofBijective] at he
    rw [show Hrot = lMinusHattedRotation _ qL from rfl,
      lMinusHattedRotation_boundary_corner _ qL i] at he
    exact he
  have hC : lMinusBoundaryCornerPerm.extendDomain Cemb
      (lMinusCodeBoundaryDart rL qL (i, true)) =
        lMinusCodeBoundaryDart rL qL (i + 1, false) :=
    lMinusBoundaryCornerPerm.extendDomain_apply_image Cemb (i, true)
  change Prot.extendDomain Pemb
    (lMinusBoundaryCornerPerm.extendDomain Cemb
      (Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (i + 1, false)))) = _
  rw [hH, hC, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
  exact Prot.extendDomain_apply_image Pemb (B (i + 1), true)

include hτ Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: if the hatted successor of an incoming
interface port is also primed, it is the outgoing interface port. This
follows from the open ambient gap and minimality of the hatted return. -/
theorem lMinusHattedRotation_incoming_mem_primed_iff (i : ℕ) :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
    let y := lMinusCodeHattedDart rL Q
      (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d)
    y ∈ Set.range (lMinusCodePrimedDart rL Q) ↔
      y = lMinusCodeBoundaryDart rL qL (i + 1, false) := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  let y := lMinusCodeHattedDart rL Q
    (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d)
  obtain ⟨n, m, hn, _, hna, _, hgap, _⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ :=
    lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  have hnD : (σ : _ → _)^[n] (D d) ∈ Set.range D := by
    rw [hna]
    exact ⟨⟨(((Q).boundary (i + 1)).1, false),
      lMinus_hatted_boundary_mem _ qL (i + 1)⟩, rfl⟩
  have htn : t ≤ n := by
    by_contra hnot
    exact htgap n hn (by omega) hnD
  constructor
  · rintro ⟨p, hpcode⟩
    have hyp : D (lMinusHattedRotation _ qL d) ∈
        Set.range (lMinusPrimedDartImage hτ) := by
      refine ⟨p, ?_⟩
      have he := congrArg (fun a => (F a).val) hpcode
      rw [lMinusCodeGluedDartEquiv_primed,
        lMinusCodeGluedDartEquiv_hatted] at he
      exact he
    have hnt : n ≤ t := by
      by_contra hnot
      apply hgap t ht (by omega)
      exact hte.symm ▸ hyp
    have hteq : t = n := Nat.le_antisymm htn hnt
    apply (F).injective
    apply Subtype.ext
    change (F (lMinusCodeHattedDart rL Q
      (lMinusHattedRotation _ qL d))).val =
        (F (lMinusCodeHattedDart rL Q
          ⟨(((Q).boundary (i + 1)).1, false),
            lMinus_hatted_boundary_mem _ qL (i + 1)⟩)).val
    rw [lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_hatted]
    exact hte.symm.trans (hteq ▸ hna)
  · intro he
    rw [he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an incoming positive-interface port,
the splice product is exactly the hatted successor. Its only possible
primed successor is the outgoing port, where the correction cancels the
primed exterior corner. -/
theorem lMinusCodeSpliceRotation_incoming (i : ℕ) :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
    lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i, true)) =
      lMinusCodeHattedDart rL Q
        (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d) := by
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  let y := lMinusCodeHattedDart rL Q (Hrot d)
  have hH : Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (i, true)) = y :=
    Hrot.extendDomain_apply_image Hemb d
  change Prot.extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (i, true)))) = y
  rw [hH]
  by_cases hy : y ∈ Set.range (lMinusCodePrimedDart rL Q)
  · have he : y = lMinusCodeBoundaryDart rL qL (i + 1, false) :=
      (lMinusHattedRotation_incoming_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk i).mp hy
    rw [he]
    have hC : lMinusBoundaryCornerPerm.extendDomain Cemb
        (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
          lMinusCodeBoundaryDart rL qL (i, true) :=
      lMinusBoundaryCornerPerm.extendDomain_apply_image Cemb (i + 1, false)
    rw [hC, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk i true]
    have hP : Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B i, false)) =
        lMinusCodePrimedDart rL Q (Prot (B i, false)) :=
      Prot.extendDomain_apply_image Pemb (B i, false)
    change Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q (B i, false)) = _
    rw [hP]
    have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) := by
      dsimp only [Prot]
      congr 1
      exact lMinus_primed_observation_code hτ
    rw [hrot, lMinusPrimedRotation_boundary_corner hτ hfin i]
    exact (lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk
      (i + 1) false).symm
  · have hC : y ∉ Set.range (lMinusCodeBoundaryDart rL qL) := by
      rintro ⟨⟨j, b⟩, hport⟩
      apply hy
      rw [← hport, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hC,
      Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hy]

/-- Helper toward Lemma 5.5: the outgoing-port splice successor is the
actual first return to the entire geometric side. -/
theorem lMinusCodeSpliceRotation_outgoing_side_rotation (i : ℕ) :
    (S).rotation
      (F (lMinusCodeBoundaryDart rL qL (i + 1, false))).val
      (F (lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i + 1, false)))).val := by
  rw [lMinusCodeSpliceRotation_outgoing hτ hp P hqMode Tpath hfin hleft hk i,
    lMinusCodeGluedDartEquiv_primed]
  change (S).rotation
    (F (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary (i + 1)).1, false),
        lMinus_hatted_boundary_mem _ qL (i + 1)⟩)).val _
  rw [lMinusCodeGluedDartEquiv_hatted]
  have hcode : (rL).code.1 = primedCode (primedSimInput U) hτ :=
    lMinus_primed_observation_code hτ
  have hrot : kmswInfRot (rL).code.1
      (lMinus_primed_observation_finiteIncidence hτ hfin) =
      kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) := by
    congr 1
  rw [hrot]
  exact lMinus_positive_outgoing_side_rotation hτ hp P hqMode Tpath hfin hleft hk i

local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "G" => lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the candidate initial-to-root relation
holds exactly when the hatted initial boundary dart is fixed. -/
theorem lMinusSpliceRotationRelation_initial_root_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
      (.inr (E (lMinusCodeBoundaryDart rL qL (0, false))))
      (.inr (E (lMinusCodePrimedDart rL Q (0, true)))) ↔
      lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d = d := by
  let R := lMinusCodeSpliceRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  change E (R ((E).symm (E c))) = E (lMinusCodePrimedDart rL Q (0, true)) ↔ _
  rw [Equiv.symm_apply_apply]
  exact (E).injective.eq_iff.trans
    (lMinusCodeSpliceRotation_initial_eq_iff hτ hp P hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: the actual initial-to-root relation always
holds under the standing hypotheses. Together with the preceding
calculation, this isolates the initial fixed-point obligation of the
prescribed splice, without asserting or assuming that obligation. -/
theorem lMinusGluedCellEquiv_initial_root_rotation :
    geometricSideRelation S .rotation
      (Φ (.inr (E (lMinusCodeBoundaryDart rL qL (0, false)))))
      (Φ (.inr (E (lMinusCodePrimedDart rL Q (0, true))))) := by
  change (S).rotation
    (G (E (lMinusCodeBoundaryDart rL qL (0, false)))).val
    (G (E (lMinusCodePrimedDart rL Q (0, true)))).val
  rw [lMinusCodeToGluedDartEquiv_equiv, lMinusCodeToGluedDartEquiv_equiv]
  change (S).rotation
    (F (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val
    (F (lMinusCodePrimedDart rL Q (0, true))).val
  rw [lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_primed]
  exact lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the incoming-port splice successor is the
actual first return to the entire geometric side. -/
theorem lMinusCodeSpliceRotation_incoming_side_rotation (i : ℕ) :
    (S).rotation
      (F (lMinusCodeBoundaryDart rL qL (i, true))).val
      (F (lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i, true)))).val := by
  rw [lMinusCodeSpliceRotation_incoming hτ hp P hqMode Tpath hfin hleft hk i]
  change (S).rotation
    (F (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩)).val _
  rw [lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_hatted]
  exact lMinus_positive_incoming_side_rotation hτ hp P hqMode Tpath hfin hleft hk i

/-- Helper toward Lemma 5.5: the rotation-relation transport holds for
every incoming positive-interface port and every target cell. -/
theorem lMinusGluedCellEquiv_rotation_incoming_iff (i : ℕ)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (i, true)))
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  let d := lMinusCodeBoundaryDart rL qL (i, true)
  let R := lMinusCodeSpliceRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  have hrotation :=
    lMinusCodeSpliceRotation_incoming_side_rotation hτ hp P hqMode Tpath hfin hleft hk i
  cases v with
  | inl v => rfl
  | inr e =>
    change lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) = e ↔
      (S).rotation (G (E d)).val (G e).val
    have hconj : lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) =
        E (R d) := by
      change E (R ((E).symm (E d))) = E (R d)
      rw [Equiv.symm_apply_apply]
    rw [hconj, lMinusCodeToGluedDartEquiv_equiv]
    constructor
    · intro he
      rw [← he, lMinusCodeToGluedDartEquiv_equiv]
      exact hrotation
    · intro he
      apply (G).injective
      rw [lMinusCodeToGluedDartEquiv_equiv]
      apply Subtype.ext
      exact firstReturn_endpoint_unique
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
        {a : ℕ × Bool | a.1 ∈ (S).edges}
        (F (R d)).property (G e).property hrotation he

/-- Helper toward Lemma 5.5: the rotation-relation transport holds for
every outgoing positive-interface port and every target cell. -/
theorem lMinusGluedCellEquiv_rotation_outgoing_iff (i : ℕ)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (i + 1, false)))
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  let d := lMinusCodeBoundaryDart rL qL (i + 1, false)
  let R := lMinusCodeSpliceRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  have hrotation :=
    lMinusCodeSpliceRotation_outgoing_side_rotation hτ hp P hqMode Tpath hfin hleft hk i
  cases v with
  | inl v => rfl
  | inr e =>
    change lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) = e ↔
      (S).rotation (G (E d)).val (G e).val
    have hconj : lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) =
        E (R d) := by
      change E (R ((E).symm (E d))) = E (R d)
      rw [Equiv.symm_apply_apply]
    rw [hconj, lMinusCodeToGluedDartEquiv_equiv]
    constructor
    · intro he
      rw [← he, lMinusCodeToGluedDartEquiv_equiv]
      exact hrotation
    · intro he
      apply (G).injective
      rw [lMinusCodeToGluedDartEquiv_equiv]
      apply Subtype.ext
      exact firstReturn_endpoint_unique
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
        {a : ℕ × Bool | a.1 ∈ (S).edges}
        (F (R d)).property (G e).property hrotation he

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: the initial adjustment leaves every incoming
positive-interface port unchanged. The open primed gap rules out sending
such a port to the initial dart under the hatted rotation. -/
theorem lMinusCodeInitialAdjustedRotation_incoming (i : ℕ) :
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i, true)) =
      lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i, true)) := by
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  apply lMinusCodeInitialAdjustedRotation_apply_of_ne
  · intro he
    have h := lMinusCodeBoundaryDart_injective rL qL he
    exact Bool.noConfusion (congrArg Prod.snd h)
  · intro he
    have hy : lMinusCodeHattedDart rL Q (Hrot d) =
        lMinusCodeBoundaryDart rL qL (0, false) := by
      have h := congrArg (Hrot.extendDomain Hemb) he
      rw [Equiv.apply_symm_apply] at h
      exact (Hrot.extendDomain_apply_image Hemb d).symm.trans h
    have hm : lMinusCodeHattedDart rL Q (Hrot d) ∈
        Set.range (lMinusCodePrimedDart rL Q) := by
      rw [hy, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    have hout := (lMinusHattedRotation_incoming_mem_primed_iff
      hτ hp P hqMode Tpath hfin hleft hk i).mp hm
    have hidx := lMinusCodeBoundaryDart_injective rL qL (hy.symm.trans hout)
    have hi := congrArg Prod.fst hidx
    omega

/-- Helper toward Lemma 5.5: the initial adjustment leaves every outgoing
positive-interface port unchanged, by the hatted exterior-corner formula. -/
theorem lMinusCodeInitialAdjustedRotation_outgoing (i : ℕ) :
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
      lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i + 1, false)) := by
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  apply lMinusCodeInitialAdjustedRotation_apply_of_ne
  · intro he
    have h := congrArg Prod.fst (lMinusCodeBoundaryDart_injective rL qL he)
    omega
  · intro he
    have hh : Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
        lMinusCodeBoundaryDart rL qL (i, true) := by
      have h := Hrot.extendDomain_apply_image Hemb
        ⟨(((Q).boundary (i + 1)).1, false), lMinus_hatted_boundary_mem _ qL (i + 1)⟩
      rw [show Hrot = lMinusHattedRotation _ qL from rfl,
        lMinusHattedRotation_boundary_corner _ qL i] at h
      exact h
    have h := congrArg (Hrot.extendDomain Hemb) he
    rw [Equiv.apply_symm_apply, hh] at h
    have hb := congrArg Prod.snd (lMinusCodeBoundaryDart_injective rL qL h)
    exact Bool.noConfusion hb

/-- Helper toward Lemma 5.5: the adjusted candidate also transports the
actual side rotation at every incoming positive-interface port. -/
theorem lMinusCodeInitialAdjustedRotation_incoming_side_rotation (i : ℕ) :
    (S).rotation
      (F (lMinusCodeBoundaryDart rL qL (i, true))).val
      (F (lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i, true)))).val := by
  rw [lMinusCodeInitialAdjustedRotation_incoming hτ hp P hqMode Tpath hfin hleft hk i]
  exact lMinusCodeSpliceRotation_incoming_side_rotation hτ hp P hqMode Tpath hfin hleft hk i

/-- Helper toward Lemma 5.5: the adjusted candidate also transports the
actual side rotation at every outgoing positive-interface port. -/
theorem lMinusCodeInitialAdjustedRotation_outgoing_side_rotation (i : ℕ) :
    (S).rotation
      (F (lMinusCodeBoundaryDart rL qL (i + 1, false))).val
      (F (lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (i + 1, false)))).val := by
  rw [lMinusCodeInitialAdjustedRotation_outgoing hτ hqMode hfin i]
  exact lMinusCodeSpliceRotation_outgoing_side_rotation hτ hp P hqMode Tpath hfin hleft hk i

/-- Helper toward Lemma 5.5: transport the adjusted intrinsic permutation
to the previously constructed glued dart carrier. -/
@[expose] noncomputable def lMinusGluedInitialAdjustedRotation :
    Equiv.Perm (LMinusGluedDart hτ hqMode) :=
  Equiv.permCongr E (lMinusCodeInitialAdjustedRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin))

/-- Helper toward Lemma 5.5: the rotation relation for the candidate with
the unconditional initial correction. -/
@[expose] noncomputable def lMinusInitialAdjustedRotationRelation :
    Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) → Prop
  | .inr d, .inr e =>
      lMinusGluedInitialAdjustedRotation hτ hp P hqMode Tpath hfin hleft hk d = e
  | _, _ => False

/-- Helper toward Lemma 5.5: the adjusted candidate transports rotation
from the initial shared dart to every target cell. -/
theorem lMinusGluedCellEquiv_rotation_initial_adjusted_iff
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (0, false)))
    lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  let p := lMinusCodePrimedDart rL Q (0, true)
  have hr : (S).rotation (F c).val (F p).val := by
    change (S).rotation
      (F (lMinusCodeHattedDart rL Q
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val
      (F (lMinusCodePrimedDart rL Q (0, true))).val
    rw [lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_primed]
    exact lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft hk
  cases v with
  | inl v => rfl
  | inr e =>
    change E (lMinusCodeInitialAdjustedRotation rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) ((E).symm (E c))) = e ↔
      (S).rotation (G (E c)).val (G e).val
    rw [Equiv.symm_apply_apply,
      lMinusCodeInitialAdjustedRotation_initial hτ hp P hqMode Tpath hfin hleft hk,
      lMinusCodeToGluedDartEquiv_equiv]
    constructor
    · intro he
      rw [← he, lMinusCodeToGluedDartEquiv_equiv]
      exact hr
    · intro he
      apply (G).injective
      rw [lMinusCodeToGluedDartEquiv_equiv]
      apply Subtype.ext
      exact firstReturn_endpoint_unique
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
        {a : ℕ × Bool | a.1 ∈ (S).edges} (F p).property (G e).property hr he

/-- Helper toward Lemma 5.5: the adjusted rotation relation transports
every incoming interface port and every target cell. -/
theorem lMinusGluedCellEquiv_rotation_incoming_adjusted_iff (i : ℕ)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (i, true)))
    lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  have hsame :
      lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E (lMinusCodeBoundaryDart rL qL (i, true)))) v ↔
      lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E (lMinusCodeBoundaryDart rL qL (i, true)))) v := by
    cases v with
    | inl v => rfl
    | inr e =>
      change E (lMinusCodeInitialAdjustedRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          ((E).symm (E (lMinusCodeBoundaryDart rL qL (i, true))))) = e ↔
        E (lMinusCodeSpliceRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          ((E).symm (E (lMinusCodeBoundaryDart rL qL (i, true))))) = e
      rw [Equiv.symm_apply_apply,
        lMinusCodeInitialAdjustedRotation_incoming hτ hp P hqMode Tpath hfin hleft hk i]
  exact hsame.trans
    (lMinusGluedCellEquiv_rotation_incoming_iff hτ hp P hqMode Tpath hfin hleft hk i v)

/-- Helper toward Lemma 5.5: the adjusted rotation relation transports
every outgoing positive-interface port and every target cell. -/
theorem lMinusGluedCellEquiv_rotation_outgoing_adjusted_iff (i : ℕ)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (i + 1, false)))
    lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  have hsame :
      lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E (lMinusCodeBoundaryDart rL qL (i + 1, false)))) v ↔
      lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E (lMinusCodeBoundaryDart rL qL (i + 1, false)))) v := by
    cases v with
    | inl v => rfl
    | inr e =>
      change E (lMinusCodeInitialAdjustedRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          ((E).symm (E (lMinusCodeBoundaryDart rL qL (i + 1, false))))) = e ↔
        E (lMinusCodeSpliceRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          ((E).symm (E (lMinusCodeBoundaryDart rL qL (i + 1, false))))) = e
      rw [Equiv.symm_apply_apply,
        lMinusCodeInitialAdjustedRotation_outgoing hτ hqMode hfin i]
  exact hsame.trans
    (lMinusGluedCellEquiv_rotation_outgoing_iff hτ hp P hqMode Tpath hfin hleft hk i v)

/-- Helper toward Lemma 5.5: the adjusted candidate transports rotation
at all indexed shared darts, including the initial dart, for every target
vertex or dart cell. Interior darts remain a separate obligation. -/
theorem lMinusGluedCellEquiv_rotation_boundary_adjusted_iff (i : ℕ) (b : Bool)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (lMinusCodeBoundaryDart rL qL (i, b)))
    lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  cases b with
  | false =>
    cases i with
    | zero =>
      exact lMinusGluedCellEquiv_rotation_initial_adjusted_iff
        hτ hp P hqMode Tpath hfin hleft hk v
    | succ i =>
      exact lMinusGluedCellEquiv_rotation_outgoing_adjusted_iff
        hτ hp P hqMode Tpath hfin hleft hk i v
  | true =>
    exact lMinusGluedCellEquiv_rotation_incoming_adjusted_iff
      hτ hp P hqMode Tpath hfin hleft hk i v

/-- Helper toward Lemma 5.5: the adjusted relation and geometric rotation
both have an empty branch on a source vertex cell, for every target cell. -/
theorem lMinusGluedCellEquiv_rotation_vertex_adjusted_iff
    (u : LMinusGluedVertex hτ hqMode)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusInitialAdjustedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
      (.inl u) v ↔ geometricSideRelation S .rotation (Φ (.inl u)) (Φ v) := by
  cases v <;> rfl

/-- Helper toward Lemma 5.5: every intrinsic dart has a representative in
one of the two edge-ID blocks, with its full endpoint bit. -/
theorem lMinusCodeGluedDart_mem_block (d : LMinusCodeGluedDart rL Q) :
    d ∈ Set.range (lMinusCodePrimedDart rL Q) ∪
      Set.range (lMinusCodeHattedDart rL Q) := by
  obtain ⟨e, b⟩ := d
  induction e using Quotient.inductionOn with
  | h e =>
    cases e with
    | inl e =>
      refine Or.inl ⟨(e, b ^^ lMinusCodePrimedSideFlip rL e), ?_⟩
      change (_, (b ^^ lMinusCodePrimedSideFlip rL e) ^^
        lMinusCodePrimedSideFlip rL e) = (_, b)
      cases b <;> cases lMinusCodePrimedSideFlip rL e <;> rfl
    | inr e => exact Or.inr ⟨⟨(e.val, b), e.property⟩, rfl⟩

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic dart images meet exactly at
indexed shared darts. No equality of endpoint pairs is used to glue edges. -/
theorem lMinusCodeHattedDart_mem_primed_iff
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    lMinusCodeHattedDart rL Q d ∈ Set.range (lMinusCodePrimedDart rL Q) ↔
      ∃ i : ℕ, ∃ b : Bool,
        lMinusCodeHattedDart rL Q d = lMinusCodeBoundaryDart rL qL (i, b) := by
  constructor
  · rintro ⟨p, he⟩
    have he' := congrArg (fun a => (F a).val.1) he
    have heP := lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk p
    have heH := lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk d
    have heEdge := (congrArg Prod.fst heP).symm.trans
      (he'.trans (congrArg Prod.fst heH))
    obtain ⟨i, _, hi⟩ := (lMinus_cross_edge_eq_iff hτ hfin p.1 d.val.1).mp heEdge
    refine ⟨i, d.val.2, ?_⟩
    apply congrArg (lMinusCodeHattedDart rL Q)
    apply Subtype.ext
    apply Prod.ext
    · change d.val.1 = ((Q).boundary i).1
      change d.val.1 = kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i
      rw [boundaryGluing_decoded_stream W h k hτ]
      exact hi
    · rfl
  · rintro ⟨i, b, he⟩
    rw [he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: on a primed dart outside the indexed shared
boundary, the adjusted candidate is exactly the primed block rotation.
This is a permutation calculation, not yet geometric first-return transport. -/
theorem lMinusCodeInitialAdjustedRotation_primed_interior (d : ℕ × Bool)
    (hd : ∀ i : ℕ, ∀ b : Bool,
      lMinusCodePrimedDart rL Q d ≠ lMinusCodeBoundaryDart rL qL (i, b)) :
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodePrimedDart rL Q d) =
      lMinusCodePrimedDart rL Q
        (kmswInfRot (rL).code.1 (lMinus_primed_observation_finiteIncidence hτ hfin) d) := by
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  have hnH : lMinusCodePrimedDart rL Q d ∉ Set.range (lMinusCodeHattedDart rL Q) := by
    rintro ⟨a, ha⟩
    have hm : lMinusCodeHattedDart rL Q a ∈ Set.range (lMinusCodePrimedDart rL Q) :=
      ⟨d, ha.symm⟩
    obtain ⟨i, b, he⟩ :=
      (lMinusCodeHattedDart_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk a).mp hm
    exact hd i b (ha.symm.trans he)
  have hnC : lMinusCodePrimedDart rL Q d ∉ Set.range (lMinusCodeBoundaryDart rL qL) := by
    rintro ⟨⟨i, b⟩, he⟩
    exact hd i b he.symm
  have hsame := lMinusCodeInitialAdjustedRotation_apply_of_ne rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
    (lMinusCodePrimedDart rL Q d) (hd 0 false) (by
    intro he
    apply hnH
    rw [he, lMinusCodeHattedRotation_initial_predecessor]
    exact ⟨_, rfl⟩)
  rw [hsame]
  change Prot.extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb (lMinusCodePrimedDart rL Q d))) = _
  rw [Equiv.Perm.extendDomain_apply_not_subtype Hrot Hemb hnH,
    Equiv.Perm.extendDomain_apply_not_subtype lMinusBoundaryCornerPerm Cemb hnC]
  exact Prot.extendDomain_apply_image Pemb d

/-- Helper toward Lemma 5.5: among indexed boundary darts, only the
initial forward dart is based at the hatted source. -/
theorem lMinus_hatted_boundary_source_iff (i : ℕ) (b : Bool) :
    kmswLimitDartVertex
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
      (((Q).boundary i).1, b) = 0 ↔ i = 0 ∧ b = false := by
  let w := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hL := sourceAncestor_left_nonneg _ renewalTime renewalTime_positiveSuccessTime qL
  have hR := sourceAncestor_right_unbounded _ renewalTime renewalTime_positiveSuccessTime qL
  have hb := kmswLeftBoundary_infinite_present_path w
    (sourceAncestor_left_transient _ renewalTime renewalTime_positiveSuccessTime qL) hL hR
  change kmswLimitDartVertex w (kmswLeftBoundaryEdge w i, b) = 0 ↔ _
  constructor
  · intro hv
    have hout := (source_dart_iff_outgoing w hL hR _).mp hv
    refine ⟨?_, hout.1⟩
    cases i with
    | zero => rfl
    | succ i =>
      have hi : edgeEast w (kmswLeftBoundaryEdge w i) = 0 := hb.2.1 i |>.trans hout.2.2
      have hfalse := (source_dart_iff_outgoing w hL hR
        (kmswLeftBoundaryEdge w i, true)).mp hi
      exact False.elim (Bool.noConfusion hfalse.1)
  · rintro ⟨rfl, rfl⟩
    exact hb.2.2.1

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the initial hatted successor lies in the
primed image exactly when it is the initial dart itself. This does not
decide whether the retained source star is a singleton. -/
theorem lMinusHattedRotation_initial_mem_primed_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    lMinusCodeHattedDart rL Q
        (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d) ∈
      Set.range (lMinusCodePrimedDart rL Q) ↔
        lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d = d := by
  let w := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  have hv := drawingFirstReturn_sameVertex
    (monotoneFamilyDrawing w
      (sourceAncestor_finite_incidence _ renewalTime renewalTime_positiveSuccessTime qL)
      (monotone_family_all w)) {a : ℕ × Bool | a.1 ∈ (Q).edges} d
  change kmswLimitDartVertex w (Hrot d).val = kmswLimitDartVertex w d.val at hv
  have hz : kmswLimitDartVertex w d.val = 0 :=
    (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩
  constructor
  · intro hm
    obtain ⟨i, b, he⟩ :=
      (lMinusCodeHattedDart_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk _).mp hm
    have heD := lMinusCodeHattedDart_injective rL qL he
    have heval : (Hrot d).val = (((Q).boundary i).1, b) := congrArg Subtype.val heD
    have hsource : kmswLimitDartVertex w (((Q).boundary i).1, b) = 0 :=
      (congrArg (kmswLimitDartVertex w) heval).symm.trans (hv.trans hz)
    obtain ⟨rfl, rfl⟩ := (lMinus_hatted_boundary_source_iff hqMode i b).mp hsource
    exact heD
  · intro he
    rw [he]
    change lMinusCodeBoundaryDart rL qL (0, false) ∈ _
    rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩

/-- Helper toward Lemma 5.5: the input additionally changed by the initial
adjustment is an indexed shared dart exactly in the singleton-star case.
Otherwise that input is an interior dart, so Target B must cover it. -/
theorem lMinusCodeHattedRotation_initial_predecessor_mem_boundary_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    (∃ i : ℕ, ∃ b : Bool, lMinusCodeHattedDart rL Q (Hrot.symm d) =
      lMinusCodeBoundaryDart rL qL (i, b)) ↔ Hrot d = d := by
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  constructor
  · rintro ⟨i, b, he⟩
    have heD := lMinusCodeHattedDart_injective rL qL he
    have hv := lMinusHattedRotation_initial_predecessor_vertex
      (if longest then XDP.ldp else XDP.sdp) qL
    change kmswLimitDartVertex
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
      (Hrot.symm d).val = 0 at hv
    have heval : (Hrot.symm d).val = (((Q).boundary i).1, b) := congrArg Subtype.val heD
    rw [heval] at hv
    obtain ⟨rfl, rfl⟩ := (lMinus_hatted_boundary_source_iff hqMode i b).mp hv
    have hh := congrArg Hrot heD
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm
  · intro he
    refine ⟨0, false, ?_⟩
    have hh := congrArg Hrot.symm he
    rw [Equiv.symm_apply_apply] at hh
    exact congrArg (lMinusCodeHattedDart rL Q) hh.symm

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate never sends the
hatted predecessor of the initial dart to its own hatted return. This
isolates an interior obstruction without assuming a fixed-point decision. -/
theorem lMinusCodeInitialAdjustedRotation_initial_predecessor_ne :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeHattedDart rL Q (Hrot.symm d)) ≠
      lMinusCodeHattedDart rL Q d := by
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Prot := kmswInfRot (rL).code.1
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  let R := lMinusCodeSpliceRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  have hpred : lMinusCodeHattedDart rL Q (Hrot.symm d) =
      (Hrot.extendDomain Hemb).symm c :=
    (lMinusCodeHattedRotation_initial_predecessor rL qL).symm
  have hadj : lMinusCodeInitialAdjustedRotation rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin)
      (lMinusCodeHattedDart rL Q (Hrot.symm d)) = R c := by
    rw [hpred]
    change R (Equiv.swap c ((Hrot.extendDomain Hemb).symm c)
      ((Hrot.extendDomain Hemb).symm c)) = R c
    rw [Equiv.swap_apply_right]
  change lMinusCodeInitialAdjustedRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
    (lMinusCodeHattedDart rL Q (Hrot.symm d)) ≠ lMinusCodeHattedDart rL Q d
  rw [hadj]
  by_cases hfix : Hrot d = d
  · have hR := (lMinusCodeSpliceRotation_initial_eq_iff
      hτ hp P hqMode Tpath hfin hleft hk).mpr hfix
    change R c = lMinusCodePrimedDart rL Q (0, true) at hR
    rw [hR]
    change lMinusCodePrimedDart rL Q (0, true) ≠ c
    dsimp only [c]
    rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    intro he
    have he' := congrArg Prod.fst (lMinusCodePrimedDart_injective rL qL he)
    change 0 = B 0 at he'
    have htwo : B 0 = 2 := primedBeta0EdgeIndex_zero_eq_two U hτ hfin
      (hatBoundaryHitWitnesses U hτ) hfin
    have hzero : (0 : ℕ) = 2 := he'.trans htwo
    omega
  · have hnP : lMinusCodeHattedDart rL Q (Hrot d) ∉
        Set.range (lMinusCodePrimedDart rL Q) := by
      intro hm
      exact hfix ((lMinusHattedRotation_initial_mem_primed_iff
        hτ hp P hqMode Tpath hfin hleft hk).mp hm)
    have hnC : lMinusCodeHattedDart rL Q (Hrot d) ∉
        Set.range (lMinusCodeBoundaryDart rL qL) := by
      rintro ⟨⟨i, b⟩, he⟩
      apply hnP
      rw [← he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    have hH : Hrot.extendDomain Hemb c = lMinusCodeHattedDart rL Q (Hrot d) :=
      Hrot.extendDomain_apply_image Hemb d
    change Prot.extendDomain Pemb
      (lMinusBoundaryCornerPerm.extendDomain Cemb (Hrot.extendDomain Hemb c)) ≠ _
    rw [hH, Equiv.Perm.extendDomain_apply_not_subtype lMinusBoundaryCornerPerm Cemb hnC,
      Equiv.Perm.extendDomain_apply_not_subtype Prot Pemb hnP]
    exact fun he => hfix (lMinusCodeHattedDart_injective rL qL he)

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: a precise obstruction at the hatted
predecessor. It is an interior input at which the adjusted permutation
disagrees with its owning block if and only if the initial hatted dart is
not fixed. The hatted block return at this input is the initial dart. -/
theorem lMinusCodeInitialAdjustedRotation_interior_predecessor_obstruction_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    ((∀ i : ℕ, ∀ b : Bool,
        lMinusCodeHattedDart rL Q (Hrot.symm d) ≠ lMinusCodeBoundaryDart rL qL (i, b)) ∧
      lMinusCodeInitialAdjustedRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          (lMinusCodeHattedDart rL Q (Hrot.symm d)) ≠
        lMinusCodeHattedDart rL Q (Hrot (Hrot.symm d))) ↔ Hrot d ≠ d := by
  dsimp only
  rw [Equiv.apply_symm_apply]
  constructor
  · intro hn hfix
    obtain ⟨i, b, he⟩ :=
      (lMinusCodeHattedRotation_initial_predecessor_mem_boundary_iff hqMode).mpr hfix
    exact hn.1 i b he
  · intro hn
    refine ⟨?_, lMinusCodeInitialAdjustedRotation_initial_predecessor_ne
      hτ hp P hqMode Tpath hfin hleft hk⟩
    intro i b he
    exact hn ((lMinusCodeHattedRotation_initial_predecessor_mem_boundary_iff hqMode).mp
      ⟨i, b, he⟩)











































































end GeometricGluing

end DirectedDistances.PaperProofs.Section5
