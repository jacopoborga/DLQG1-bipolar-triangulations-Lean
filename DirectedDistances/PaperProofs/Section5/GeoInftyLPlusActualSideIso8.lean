/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso7

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

The five initial-root obligations recorded in Iso7 are proved here with
their unchanged statements. Empty attachment forces index zero, where the
first source-exit triangle and the complete-side return identify the beta
successor. Completeness of primed rotation orbits classifies the primed root
star using its proved two-dart cycle. For nonbeta hatted root inputs, an
outgoing ambient arc excludes prefix incoming darts and the primed root;
first-return uniqueness also excludes the terminal repair's other input.

or whole-paper completion is asserted. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))

include hfin in
/-- Helper toward Lemma 5.5: the retained primed root is outside the entire
hatted block, since every common edge has a positive creation index. -/
theorem lPlusPrimedGluedDart_root_not_hatted (b : Bool) :
    lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, b) ∉
      Set.range (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)) := by
  rintro ⟨a, ha⟩
  have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
    (.inr (.inl (0, b))) (.inr (.inr a))).mp ha.symm
  have hedge : boundaryGluingPrimedEdgeMap W h k hτ 0 =
      boundaryGluingHatEdgeMap W h k hτ a.val.1 := congrArg Prod.fst he
  obtain ⟨i, hi, _⟩ := (lMinus_cross_edge_eq_iff hτ hfin 0 a.val.1).mp hedge
  have hc := primedBeta0EdgeIndex_eq_creation
    (boundaryGluingFutureStream W h k) hτ hfin
    (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin i
  have hz := hi.trans hc
  omega

include hfin in
/-- Helper toward Lemma 5.5: both remaining correction factors fix the
east dart of the retained primed root. -/
theorem lPlus_initial_primed_root_corrections :
    lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true))) =
      lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true) := by
  let d := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true)
  have hnotH : d ∉ Set.range
      (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)) :=
    lPlusPrimedGluedDart_root_not_hatted hτ hqMode hfin true
  have hnotB : d ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨p, hp⟩
    exact hnotH ⟨⟨((_, p.2)), lMinus_hatted_boundary_mem _
      ⟨boundaryFutureHattedPath k W, hqMode⟩ p.1⟩, hp⟩
  have hCB : lPlusBetaCornerRotation hτ hqMode d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB
  have hHE : lPlusHattedExtendedRotation hτ hqMode d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  exact (congrArg (lPlusHattedExtendedRotation hτ hqMode) hCB).trans hHE

/-- Helper toward Lemma 5.5: the empty attachment beta successor agrees
with the initial primed corner, with the complete side as return set. -/
theorem lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff_empty
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
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
    (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k)
    (hzero : (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusBetaGluedDart hτ hqMode p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusBetaGluedDart hτ hqMode p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  have hk0 : k = 0 := by
    by_contra hne
    have hn := lPlus_upperLeft_length_pos_of_pos
      (W := W) (h := h) (show 0 < k by omega)
    omega
  have hcanonical := lPlusBetaGluedDart_initial_root_eq_canonical
    hτ hp P hqMode Tpath hfin hleft hk p hd
  rw [hcanonical]
  let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let beta := lPlusBetaGluedDart hτ hqMode (0, false)
  let out := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true)
  have hblock : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
      beta = out := by
    rw [lPlusGluedCorrectedRotation2_eq_blockRotation2
      hτ hqMode hfin hk hp P Tpath hleft]
    exact (lPlusGluedBlockRotation2_beta_output_of_upperLeft_empty
      hτ hp P hqMode Tpath hfin hleft hk hzero).trans
      (lPlus_initial_primed_root_corrections hτ hqMode hfin)
  have hrot : (m0GeodesicSide hp P .left).rotation (D beta).val (D out).val := by
    subst k
    exact lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft (le_refl 0)
  intro e
  constructor
  · intro he
    have hout : out = e := hblock.symm.trans he
    exact hout ▸ hrot
  · intro he
    have hval : (D out).val = (D e).val :=
      firstReturn_endpoint_unique
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
        {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P .left).edges}
        (D out).property (D e).property hrot he
    exact hblock.trans ((D).injective (Subtype.ext hval))

/-- Helper toward Lemma 5.5: the beta rotation comparison in both attachment
cases, using the same geometric dart equivalence and side carrier. -/
theorem lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
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
    (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusBetaGluedDart hτ hqMode p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusBetaGluedDart hτ hqMode p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  by_cases hzero : (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0
  · exact lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff_empty
      hτ hp P hqMode Tpath hfin hleft hk p hd hzero
  · exact lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff_nonempty
      hτ hp P hqMode Tpath hfin hleft hk p hd (Nat.pos_of_ne_zero hzero)

/-- Helper toward Lemma 5.5: the primed initial interface dart is the
canonical beta dart, including its reversed endpoint bit. -/
theorem lPlusPrimedGluedDart_initial_beta_eq :
    lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
      (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
        (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin 0,
        true) = lPlusBetaGluedDart hτ hqMode (0, false) := by
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  rw [show lPlusBlockDartImage hτ (.inr (.inl
      (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
        (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin 0,
        true))) = _ from lMinusPrimedDartImage_boundary hτ hfin 0 true]
  change (boundaryGluingHatEdgeMap W h k hτ
      (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) 0),
      false) = _
  rw [← boundaryGluing_decoded_stream W h k hτ]
  rfl

/-- Helper toward Lemma 5.5: the canonical beta dart is incident to the
initial actual-side vertex. -/
theorem lPlusBetaGluedDart_initial_vertex
    {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode (0, false))).val =
      boundaryVertex (shiftedStream W 0) h k := by
  change kmswLimitDartVertex (shiftedStream W 0)
    (boundaryGluingHatEdgeMap W h k hτ
      ((lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode).boundary 0).1,
      false) = _
  change edgeWest (shiftedStream W 0) _ = _
  rw [(boundaryGluing_hat_edge_endpoints W h k hτ _).1]
  have hsource : edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ)
      ((lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode).boundary 0).1 = 0 := by
    rw [← boundaryGluing_decoded_stream W h k hτ]
    exact (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩
  rw [hsource, boundaryGluingHatVertexMap_zero]

/-- Helper toward Lemma 5.5: the complete primed root star consists of
the two darts of the proved initial corner cycle. Orbit completeness, rather
than a restriction on quotient representatives, gives the classification. -/
theorem lPlusPrimedGluedDart_initial_vertex_cases
    {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) (p : LPlusPrimedDart)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p)).val =
      boundaryVertex (shiftedStream W 0) h k) :
    p = (0, true) ∨
      lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p =
        lPlusBetaGluedDart hτ hqMode (0, false) := by
  let U := boundaryGluingFutureStream W h k
  let u := primedCode (primedSimInput U) hτ
  let b₀ := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0
  let R := kmswInfRot u (primedCode_finiteIncidence U hτ hfin)
  have hb := lPlusBetaGluedDart_initial_vertex hτ hqMode hfin hp P Tpath hleft hk
  rw [← lPlusPrimedGluedDart_initial_beta_eq hτ hqMode hfin] at hb
  have hv : kmswLimitDartVertex u p = kmswLimitDartVertex u (b₀, true) := by
    apply lPlusPrimedVertexImage_injective hτ hqMode
    change boundaryGluingPrimedVertexMap W h k hτ
      (kmswLimitDartVertex (primedCode (primedSimInput
        (boundaryGluingFutureStream W h k)) hτ) p) =
      boundaryGluingPrimedVertexMap W h k hτ
        (kmswLimitDartVertex (primedCode (primedSimInput
          (boundaryGluingFutureStream W h k)) hτ) (b₀, true))
    rw [← lMinusPrimedDartImage_endpoint hτ p,
      ← lMinusPrimedDartImage_endpoint hτ (b₀, true)]
    exact hd.trans hb.symm
  have h0 : R (0, true) = (b₀, true) := lPlusPrimedRotation_initial_root_corner hτ hfin
  have h1 : R (b₀, true) = (0, true) := lMinusPrimedRotation_initial_corner hτ hfin
  obtain ⟨n, hn⟩ := (kmswInfRot_exists_pow_iff_endpoint u
    (primedCode_finiteIncidence U hτ hfin) (b₀, true) p).2 hv.symm
  have horbit (n : ℕ) : (R : _ → _)^[n] (b₀, true) = (0, true) ∨
      (R : _ → _)^[n] (b₀, true) = (b₀, true) := by
    induction n with
    | zero => exact Or.inr rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with he | he
      · exact Or.inr ((congrArg R he).trans h0)
      · exact Or.inl ((congrArg R he).trans h1)
  have hnp : (R : _ → _)^[n] (b₀, true) = p := by
    simpa only [Equiv.Perm.coe_pow] using hn
  rcases horbit n with he | he
  · exact Or.inl (hnp.symm.trans he)
  · right
    rw [hnp.symm.trans he]
    exact lPlusPrimedGluedDart_initial_beta_eq hτ hqMode hfin

section InitialPrimedCorner

variable {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "beta" => lPlusBetaGluedDart hτ hqMode (0, false)

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: at index zero the ambient beta successor is
the retained primed root, by the first source-exit triangle. -/
theorem lPlus_initial_beta_ambient_successor_zero (hk0 : k = 0) :
    kmswInfRot (shiftedStream W 0) (H.1 0) (D beta).val =
      (D (IT (0, true))).val := by
  change kmswInfRot (shiftedStream W 0) (H.1 0)
    (boundaryGluingHatEdgeMap W h k hτ (((MH).boundary 0).1), false) =
      lMinusPrimedDartImage hτ (0, true)
  have hb : ((MH).boundary 0).1 =
      kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) 0 := by
    change kmswLeftBoundaryEdge (boltzmannKMSWStream
      (pathCode (boundaryFutureHattedPath k W))) 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [hb]
  subst k
  have he := lMinus_initial_future_rotation hτ hfin
  have hU : boundaryGluingFutureStream W h 0 = shiftedStream W 0 := by
    funext i
    simp only [boundaryGluingFutureStream, boundaryHitTime_zero, Nat.zero_add]
  have hr : kmswInfRot (boundaryGluingFutureStream W h 0) hfin =
      kmswInfRot (shiftedStream W 0) (H.1 0) := by
    congr 1
  rw [hr] at he
  simp only [boundaryGluingHatEdgeMap, lMinusPrimedDartImage,
    boundaryGluingPrimedEdgeMap, boundaryGluingEdgeMap, boundaryHitTime_zero,
    kmswWindowEdgeMapInf_zero_start, Function.comp_apply, id_eq]
  exact he

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: at the empty-prefix index the primed root
first returns to the complete side at the hatted successor of beta. -/
theorem lPlus_initial_primed_root_zero_side_rotation (hk0 : k = 0) :
    (m0GeodesicSide hp P .left).rotation (D (IT (0, true))).val
      (D (lPlusHattedExtendedRotation hτ hqMode beta)).val := by
  let c : LPlusHattedDart MH := ⟨(((MH).boundary 0).1, false),
    lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool := fun a =>
    (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let x := (D (IT (0, true))).val
  have hcx : σ (J c) = x :=
    lPlus_initial_beta_ambient_successor_zero hτ hqMode hfin hp P Tpath hleft hk hk0
  have hxnot : x ∉ Set.range J := by
    rintro ⟨a, ha⟩
    apply lPlusPrimedGluedDart_root_not_hatted hτ hqMode hfin true
    refine ⟨a, (D).injective (Subtype.ext ha)⟩
  obtain ⟨p, hp', hpret, hpgap⟩ :=
    lMinusPrimedDartImage_firstReturn (H := H) hτ hfin (0, true)
  rw [lPlusPrimedRotation_initial_root_corner hτ hfin,
    lMinusPrimedDartImage_boundary hτ hfin] at hpret
  have hb : ((MH).boundary 0).1 =
      kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) 0 := by
    change kmswLeftBoundaryEdge (boltzmannKMSWStream
      (pathCode (boundaryFutureHattedPath k W))) 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [← hb] at hpret
  change (σ : _ → _)^[p] x = J c at hpret
  change ∀ j : ℕ, 0 < j → j < p →
    (σ : _ → _)^[j] x ∉ Set.range (lMinusPrimedDartImage hτ) at hpgap
  obtain ⟨t, ht, htret, htgap⟩ :=
    lPlusHattedDartImage_firstReturn (H := H) hτ hqMode hfin c
  change (σ : _ → _)^[t] (J c) = J (HR c) at htret
  change ∀ j : ℕ, 0 < j → j < t →
    (σ : _ → _)^[j] (J c) ∉ Set.range J at htgap
  have htone : 1 < t := by
    by_contra hh
    have he : t = 1 := by omega
    rw [he, Function.iterate_one, hcx] at htret
    exact hxnot ⟨HR c, htret.symm⟩
  have hperiod : (σ : _ → _)^[p + 1] (J c) = J c := by
    rw [Function.iterate_succ_apply, hcx, hpret]
  have htbound : t ≤ p + 1 := by
    by_contra hh
    exact htgap (p + 1) (by omega) (by omega) ⟨c, hperiod.symm⟩
  have hshift (j : ℕ) : (σ : _ → _)^[j] x =
      (σ : _ → _)^[j + 1] (J c) := by
    rw [Function.iterate_succ_apply, hcx]
  have hout : (D (lPlusHattedExtendedRotation hτ hqMode beta)).val = J (HR c) := by
    rw [show beta = IH c from rfl, lPlusHattedExtendedRotation_apply_hatted]
    rfl
  refine ⟨t - 1, by omega, ?_, ?_⟩
  · change (σ : _ → _)^[t - 1] x = _
    rw [hout, hshift, Nat.sub_add_cancel (by omega)]
    exact htret
  · intro j hj hjn hmem
    have himage : (σ : _ → _)^[j] x ∈ Set.range
        (lPlusBlockDartImage (M := MH) hτ) := by
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
      exact hmem
    obtain ⟨a, ha⟩ := himage
    rcases a with a | (a | a)
    · subst k
      exact ((Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h))
        a.val.1).mp a.property).elim
    · exact hpgap j hj (by omega) ⟨a, ha⟩
    · apply htgap (j + 1) (by omega) (by omega)
      rw [← hshift]
      exact ⟨a, ha⟩

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: at index zero the block permutation sends
the primed root to the retained hatted successor of the beta dart. -/
theorem lPlus_initial_primed_root_zero_output (hk0 : k = 0) :
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
      (IT (0, true)) = lPlusHattedExtendedRotation hτ hqMode beta := by
  let d := IT (0, true)
  have hzero : (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0 := by
    subst k
    rw [boundaryHitTime_zero]
    rfl
  have hnotP : d ∉ Set.range
      (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)) := by
    rintro ⟨a, _⟩
    subst k
    exact ((Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h))
      a.val.1).mp a.property).elim
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨i, _⟩
    have hi := i.1.isLt
    omega
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = beta := by
    exact (lPlusPrimedExtendedRotation_initial_root_corners hτ hqMode hfin).1.trans
      (lPlusPrimedGluedDart_initial_beta_eq hτ hqMode hfin)
  have hCB : lPlusBetaCornerRotation hτ hqMode beta = beta :=
    lMinusBoundaryCornerPerm.extendDomain_apply_image
      (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (0, false)
  rw [lPlusGluedCorrectedRotation2_eq_blockRotation2
    hτ hqMode hfin hk hp P Tpath hleft]
  unfold lPlusGluedBlockRotation2
  rw [dite_eq_right (by omega : ¬ 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length)]
  change lPlusHattedExtendedRotation hτ hqMode
    (lPlusBetaCornerRotation hτ hqMode
      (lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
          (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = _
  rw [hPE, hCU, hTE, hCB]

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: each retained hatted dart incident to the
initial actual vertex is an outgoing dart there. -/
theorem lPlus_initial_hatted_outgoing (a : LPlusHattedDart MH)
    (hd : kmswLimitDartVertex (shiftedStream W 0) (D (IH a)).val =
      boundaryVertex (shiftedStream W 0) h k) :
    (D (IH a)).val.2 = false ∧ EdgePresent (shiftedStream W 0) (D (IH a)).val.1 := by
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hv : kmswLimitDartVertex z a.val = 0 := by
    apply boundaryGluingHatVertexMap_injective W h k hτ
    rw [boundaryGluingHatVertexMap_zero]
    have hend : kmswLimitDartVertex (shiftedStream W 0)
        (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2) =
        boundaryGluingHatVertexMap W h k hτ (kmswLimitDartVertex z a.val) := by
      have he := boundaryGluing_hat_edge_endpoints W h k hτ a.val.1
      rw [← boundaryGluing_decoded_stream W h k hτ] at he
      cases hb : a.val.2
      · simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using he.1
      · simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using he.2
    exact hend.symm.trans hd
  have ho := (source_dart_iff_outgoing z
    (sourceAncestor_left_nonneg _ renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩)
    (sourceAncestor_right_unbounded _ renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩) a.val).mp hv
  refine ⟨ho.1, ?_⟩
  have hpresent : EdgePresent (boundaryGluingFutureStream W h k)
      (hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ a.val.1) :=
    ((hatLimitEdgeMap_range_iff (boundaryGluingFutureStream W h k) hτ _).mp
      ⟨a.val.1, rfl⟩).1
  obtain ⟨n, he, hp'⟩ := hpresent
  change EdgePresent (shiftedStream W 0)
    (boundaryGluingEdgeMap W h k
      (hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ a.val.1))
  rw [boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage _ _ n _ he]
  exact ⟨boundaryHitTime (shiftedStream W 0) h k + n,
    (kmswWindowPatchData_rel _ _ n).edge_bound _ he,
    (kmswWindowPatchData_rel _ _ n).present _ he hp'⟩

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: every nonbeta hatted root dart has an
outgoing ambient arc to beta; the opposite arc hits the incoming primed root. -/
theorem lPlus_initial_hatted_outgoing_arc (a : LPlusHattedDart MH)
    (hd : kmswLimitDartVertex (shiftedStream W 0) (D (IH a)).val =
      boundaryVertex (shiftedStream W 0) h k)
    (hne : IH a ≠ beta) :
    RotationArc (kmswInfRot (shiftedStream W 0) (H.1 0))
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent (shiftedStream W 0) d.1)
      (D (IH a)).val (D beta).val := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let c : LPlusHattedDart MH := ⟨(((MH).boundary 0).1, false),
    lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool := fun d => (D (IH d)).val
  have hcroot := lPlusBetaGluedDart_initial_vertex hτ hqMode hfin hp P Tpath hleft hk
  have hoa := lPlus_initial_hatted_outgoing hτ hqMode hfin hp P Tpath hleft hk a hd
  have hoc := lPlus_initial_hatted_outgoing hτ hqMode hfin hp P Tpath hleft hk c hcroot
  have hneJ : J a ≠ J c := by
    intro he
    exact hne ((D).injective (Subtype.ext he))
  have hw : edgeWest (shiftedStream W 0) (J a).1 =
      edgeWest (shiftedStream W 0) (J c).1 := by
    have ha := hd
    have hc := hcroot
    change (if (J a).2 then _ else _) = _ at ha
    change (if (J c).2 then _ else _) = _ at hc
    rw [hoa.1] at ha
    rw [hoc.1] at hc
    exact ha.trans hc.symm
  have ha : J a = ((J a).1, false) := Prod.ext rfl hoa.1
  have hc : J c = ((J c).1, false) := Prod.ext rfl hoc.1
  change RotationArc σ
    (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent (shiftedStream W 0) d.1)
    (J a) (J c)
  rcases kmswInfRot_outgoing_interval_all (shiftedStream W 0) (H.1 0)
      (J a).1 (J c).1 hw hoa.2 hoc.2 with hf | hb
  · simpa only [← ha, ← hc] using hf
  · have hbad : RotationArc σ
        (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent (shiftedStream W 0) d.1)
        (J c) (J a) := by simpa only [← ha, ← hc] using hb
    obtain ⟨m, hm, hall⟩ := hbad
    simp only [Equiv.Perm.coe_pow] at hm hall
    have hmpos : 0 < m := by
      by_contra hn
      have hz : m = 0 := by omega
      rw [hz, Function.iterate_zero_apply] at hm
      exact hneJ hm.symm
    let U := boundaryGluingFutureStream W h k
    let FJ : (ℕ × Bool) → ℕ × Bool := fun b =>
      (boundaryGluingEdgeMap W h k b.1, b.2)
    let cU : ℕ × Bool :=
      (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false)
    have hce : FJ cU = J c := by
      change (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
        (boundaryGluingHatEdgeMap W h k hτ
          (kmswLeftBoundaryEdge (boltzmannKMSWStream
            (pathCode (boundaryFutureHattedPath k W))) 0), false)
      rw [boundaryGluing_decoded_stream W h k hτ]
    obtain ⟨t, ht, hte, hgap⟩ := lMinus_future_firstReturn (H := H) hfin cU
    change (σ : _ → _)^[t] (FJ cU) = FJ (kmswInfRot U hfin cU) at hte
    rw [hce] at hte
    have hnout : (FJ (kmswInfRot U hfin cU)).2 ≠ false := by
      rw [show kmswInfRot U hfin cU = primedLimitDartMap U hτ (0, true) from
        lMinus_initial_future_rotation hτ hfin]
      change (true ^^ primedLimitSideFlip U hτ 0) ≠ false
      rw [primedLimitSideFlip_zero, Bool.xor_false]
      decide
    by_cases hmt : m < t
    · apply False.elim
      apply hgap m hmpos hmt
      refine ⟨(hatLimitEdgeMap U hτ a.val.1, a.val.2), ?_⟩
      change J a = (σ : _ → _)^[m] (FJ cU)
      rw [hce]
      exact hm.symm
    · exact (hnout (hte ▸ (hall t (by omega)).1)).elim

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: a nonbeta hatted root input returns to the
complete side at its own hatted successor, with all three blocks excluded
from the open interval. -/
theorem lPlus_initial_hatted_nonbeta_side_rotation (a : LPlusHattedDart MH)
    (hd : kmswLimitDartVertex (shiftedStream W 0) (D (IH a)).val =
      boundaryVertex (shiftedStream W 0) h k)
    (hne : IH a ≠ beta) :
    (m0GeodesicSide hp P .left).rotation (D (IH a)).val
      (D (lPlusHattedExtendedRotation hτ hqMode (IH a))).val := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let J : LPlusHattedDart MH → ℕ × Bool := fun d => (D (IH d)).val
  let c : LPlusHattedDart MH := ⟨(((MH).boundary 0).1, false),
    lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  obtain ⟨m, hm, hall⟩ := lPlus_initial_hatted_outgoing_arc
    hτ hqMode hfin hp P Tpath hleft hk a hd hne
  simp only [Equiv.Perm.coe_pow] at hm hall
  obtain ⟨n, hn, hend, hgap⟩ :=
    lPlusHattedDartImage_firstReturn (H := H) hτ hqMode hfin a
  change ∀ j : ℕ, 0 < j → j < n →
    (σ : _ → _)^[j] (J a) ∉ Set.range J at hgap
  have hmpos : 0 < m := by
    by_contra hh
    have hz : m = 0 := by omega
    rw [hz, Function.iterate_zero_apply] at hm
    exact hne ((D).injective (Subtype.ext hm))
  have hnm : n ≤ m := by
    by_contra hh
    exact hgap m hmpos (by omega) ⟨c, hm.symm⟩
  refine ⟨n, hn, ?_, ?_⟩
  · rw [lPlusHattedExtendedRotation_apply_hatted]
    exact hend
  · intro j hj hjn hmem
    have hout := hall j (by omega)
    have hvj : kmswLimitDartVertex (shiftedStream W 0)
        ((σ : _ → _)^[j] (J a)) = boundaryVertex (shiftedStream W 0) h k := by
      have hv := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0)
        (H.1 0) (J a) ((σ : _ → _)^[j] (J a))).mp
        ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact hv.symm.trans hd
    have himage : (σ : _ → _)^[j] (J a) ∈ Set.range
        (lPlusBlockDartImage (M := MH) hτ) := by
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
      exact hmem
    obtain ⟨b, hb⟩ := himage
    rcases b with b | (b | b)
    · change b.val = (σ : _ → _)^[j] (J a) at hb
      have hbroot : kmswLimitDartVertex (shiftedStream W 0) b.val =
          boundaryVertex (shiftedStream W 0) h k := by rw [hb]; exact hvj
      have hbit := (lPlusPrefixDart_initial_vertex_old_incoming hk b hbroot).1
      have hout' : b.val.2 = false := by rw [hb]; exact hout.1
      rw [hbit] at hout'
      cases hout'
    · change (D (IT b)).val = (σ : _ → _)^[j] (J a) at hb
      have hbroot : kmswLimitDartVertex (shiftedStream W 0) (D (IT b)).val =
          boundaryVertex (shiftedStream W 0) h k := by rw [hb]; exact hvj
      rcases lPlusPrimedGluedDart_initial_vertex_cases
        hτ hqMode hfin hp P Tpath hleft hk b hbroot with hroot | hbeta
      · subst b
        change lMinusPrimedDartImage hτ (0, true) = (σ : _ → _)^[j] (J a) at hb
        have hout' : (lMinusPrimedDartImage hτ (0, true)).2 = false := by
          rw [hb]
          exact hout.1
        simp only [lMinusPrimedDartImage, primedLimitSideFlip_zero,
          Bool.xor_false, Bool.true_eq_false] at hout'
      · apply hgap j hj hjn
        refine ⟨c, ?_⟩
        exact (congrArg (fun q => (D q).val) hbeta).symm.trans hb
    · exact hgap j hj hjn ⟨b, hb⟩

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the full corrected permutation has the actual
side successor on every nonbeta hatted root input. -/
theorem lPlus_initial_hatted_nonbeta_corrected_side_rotation (a : LPlusHattedDart MH)
    (hd : kmswLimitDartVertex (shiftedStream W 0) (D (IH a)).val =
      boundaryVertex (shiftedStream W 0) h k)
    (hne : IH a ≠ beta) :
    (m0GeodesicSide hp P .left).rotation (D (IH a)).val
      (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk (IH a))).val := by
  let d := IH a
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hnotP : d ∉ Set.range
      (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)) := by
    rintro ⟨b, hb⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hb
    have hm : b.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨b.property, ⟨a.val.1, (congrArg Prod.fst he).symm⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨i, hi⟩
    exact hnotP ⟨⟨(_, i.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i.1⟩, hi⟩
  have hnotT : d ∉ Set.range (IT) := by
    rintro ⟨p, hp'⟩
    have hpRoot := hd
    change kmswLimitDartVertex (shiftedStream W 0) (D d).val = _ at hpRoot
    rw [← hp'] at hpRoot
    rcases lPlusPrimedGluedDart_initial_vertex_cases
      hτ hqMode hfin hp P Tpath hleft hk p hpRoot with hroot | hbeta
    · subst p
      exact lPlusPrimedGluedDart_root_not_hatted hτ hqMode hfin true ⟨a, hp'.symm⟩
    · exact hne (hp'.symm.trans hbeta)
  have hnotB : d ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨p, hp'⟩
    have hpRoot := hd
    change kmswLimitDartVertex (shiftedStream W 0) (D d).val = _ at hpRoot
    rw [← hp'] at hpRoot
    have he := lPlusBetaGluedDart_root_port_unique
      hτ hp P hqMode Tpath hfin hleft hk p hpRoot
    exact hne (hp'.symm.trans (congrArg (lPlusBetaGluedDart hτ hqMode) he))
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT
  have hCB : lPlusBetaCornerRotation hτ hqMode d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB
  have hC : C d = lPlusHattedExtendedRotation hτ hqMode d := by
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode
        (lPlusPrimedExtendedRotation hτ hqMode hfin
          (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
            (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = _
    rw [hPE, hCU, hTE, hCB]
  have hrot := lPlus_initial_hatted_nonbeta_side_rotation
    hτ hqMode hfin hp P Tpath hleft hk a hd hne
  have hret : C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
    apply (D).injective
    apply Subtype.ext
    rw [hC]
    apply firstReturn_endpoint_unique
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
      {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P .left).edges}
      (D _).property (D _).property hrot
    obtain ⟨n, hn, hend, hgap⟩ :=
      lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d
    refine ⟨n, hn, hend, ?_⟩
    intro j hj hjn hm
    apply hgap j hj hjn
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hm
  have heq : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
    by_cases hn : 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k))))).length
    · apply lPlusGluedCorrectedRotation2_eq_of_ne
        hτ hp P hqMode Tpath hfin hleft hk hn d
      · intro he
        exact hnotUL ⟨(_, false), he.symm⟩
      · intro he
        have hdt := lPlusGluedCodeReturn_injective (H := H) hτ hqMode
          (hret.symm.trans he)
        exact hnotUL ⟨(_, false), hdt.symm⟩
    · rw [lPlusGluedCorrectedRotation2_eq_blockRotation2
        hτ hqMode hfin hk hp P Tpath hleft]
      unfold lPlusGluedBlockRotation2
      rw [dite_eq_right hn]
  rw [heq, hC]
  exact hrot

end InitialPrimedCorner

/-- Helper toward Lemma 5.5: every primed representative at the initial
vertex has the corrected actual-side rotation successor. -/
theorem lPlusGluedCorrectedRotation2_primed_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
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
    (p : LPlusPrimedDart)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  rcases lPlusPrimedGluedDart_initial_vertex_cases
      hτ hqMode hfin hp P Tpath hleft hk p hd with hroot | hbeta
  · subst p
    by_cases hk0 : k = 0
    · let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
      let out := lPlusHattedExtendedRotation hτ hqMode
        (lPlusBetaGluedDart hτ hqMode (0, false))
      have hblock := lPlus_initial_primed_root_zero_output
        hτ hqMode hfin hp P Tpath hleft hk hk0
      have hrot := lPlus_initial_primed_root_zero_side_rotation
        hτ hqMode hfin hp P Tpath hleft hk hk0
      intro e
      constructor
      · intro he
        have hout : out = e := hblock.symm.trans he
        exact hout ▸ hrot
      · intro he
        have hval : (D out).val = (D e).val :=
          firstReturn_endpoint_unique
            (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
            {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P .left).edges}
            (D out).property (D e).property hrot he
        exact hblock.trans ((D).injective (Subtype.ext hval))
    · have hn := lPlus_upperLeft_length_pos_of_pos
        (W := W) (h := h) (show 0 < k by omega)
      let a : LPlusPrefixDart W h k := ⟨(_, true),
        lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
      have hEq : lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true) =
          lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode) a :=
        (lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn).symm
      rw [hEq] at hd ⊢
      exact lPlusGluedCorrectedRotation2_prefix_initial_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk a hd
  · rw [hbeta] at hd ⊢
    exact lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk (0, false) hd

/-- Helper toward Lemma 5.5: every hatted quotient representative at the
initial vertex has exactly the corrected actual-side rotation successor. -/
theorem lPlusGluedCorrectedRotation2_hatted_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
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
    (a : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  by_cases heq : lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a =
      lPlusBetaGluedDart hτ hqMode (0, false)
  · rw [heq] at hd ⊢
    exact lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk (0, false) hd
  · let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
    let out := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
      (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a)
    have hrot := lPlus_initial_hatted_nonbeta_corrected_side_rotation
      hτ hqMode hfin hp P Tpath hleft hk a hd heq
    intro e
    constructor
    · intro hout
      exact hout ▸ hrot
    · intro hrot'
      have hval : (D out).val = (D e).val :=
        firstReturn_endpoint_unique
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
          {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P .left).edges}
          (D out).property (D e).property hrot hrot'
      exact (D).injective (Subtype.ext hval)

/-- Helper toward Lemma 5.5: the corrected rotation and the actual left
side rotation agree at every initial-vertex dart, across all three blocks. -/
theorem lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
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
    (d : LPlusGluedDart longest hqMode hτ)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d).val =
        boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  induction d using Quotient.inductionOn with
  | h d =>
    rcases d with a | (p | a)
    · exact lPlusGluedCorrectedRotation2_prefix_initial_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk a hd
    · exact lPlusGluedCorrectedRotation2_primed_initial_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk p hd
    · exact lPlusGluedCorrectedRotation2_hatted_initial_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk a hd

end DirectedDistances.PaperProofs.Section5
