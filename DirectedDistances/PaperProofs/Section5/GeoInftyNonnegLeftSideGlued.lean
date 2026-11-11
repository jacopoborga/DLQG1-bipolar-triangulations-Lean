/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRange




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 < k)

local notation "F" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the block dart image descends through the
existing gluing quotient to the geometric left-side dart subtype. -/
@[expose] noncomputable def lPlusGluedDartMap :
    LPlusGluedDart longest hqMode hτ →
      {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges} :=
  Quotient.lift (fun d : LPlusBlockDart W h k
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) =>
    ⟨F d, lPlusBlockDartImage_mem hτ hp P hqMode Tpath hfin hleft
      (by omega) d⟩) (by
        intro a b hab
        apply Subtype.ext
        change F a = F b at hab
        exact hab)

/-- Helper toward Lemma 5.5: the quotient identifies two block darts exactly
when their geometric edge IDs and endpoint bits agree. -/
theorem lPlusGluedDart_eq_iff (a b : LPlusBlockDart W h k
    (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    (⟦a⟧ : LPlusGluedDart longest hqMode hτ) = ⟦b⟧ ↔ F a = F b := by
  constructor
  · exact Quotient.exact
  · intro hab
    apply Quotient.sound
    exact hab

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the induced map from the L+ dart quotient is
injective, since its defining relation is the kernel of the block image. -/
theorem lPlusGluedDartMap_injective :
    Function.Injective (lPlusGluedDartMap hτ hp P hqMode Tpath hfin hleft hk) := by
  intro q r hqr
  revert hqr
  refine Quotient.inductionOn₂ q r ?_
  intro a b hab
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) a b).2
  exact congrArg Subtype.val hab

include hfin hk in
/-- Helper toward Lemma 5.5: prefix and primed darts are identified exactly
on their shared upper-left boundary edges, with the primed endpoint bit flipped
by the geometric embedding. -/
theorem lPlusPrefixPrimedGluedDart_eq_iff
    (a : LPlusPrefixDart W h k) (b : LPlusPrimedDart) :
    (⟦Sum.inl a⟧ : LPlusGluedDart longest hqMode hτ) =
        ⟦Sum.inr (Sum.inl b)⟧ ↔
      a.val.1 = boundaryGluingPrimedEdgeMap W h k hτ b.1 ∧
        a.val.2 = (b.2 ^^ primedLimitSideFlip
          (boundaryGluingFutureStream W h k) hτ b.1) ∧
        a.val.1 ∈ boundaryGluingUpperLeftEdges W h k := by
  rw [lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)]
  constructor
  · intro he
    change (a.val.1, a.val.2) =
      (boundaryGluingPrimedEdgeMap W h k hτ b.1,
        b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ b.1) at he
    rcases Prod.mk.inj he with ⟨he, hb⟩
    have hshared : a.val.1 ∈
        boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ :=
      ⟨a.property, ⟨b.1, he.symm⟩⟩
    rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin
      (by omega)] at hshared
    exact ⟨he, hb, hshared⟩
  · rintro ⟨he, hb, _⟩
    change (a.val.1, a.val.2) =
      (boundaryGluingPrimedEdgeMap W h k hτ b.1,
        b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ b.1)
    exact Prod.ext he hb

include hk in
/-- Helper toward Lemma 5.5: the deleted prefix and hatted block share no
geometric dart for positive k, since their edge carriers are disjoint. -/
theorem lPlusPrefixHattedGluedDart_ne
    (a : LPlusPrefixDart W h k)
    (b : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    (⟦Sum.inl a⟧ : LPlusGluedDart longest hqMode hτ) ≠
      ⟦Sum.inr (Sum.inr b)⟧ := by
  intro he
  have himage := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
    (Sum.inl a) (Sum.inr (Sum.inr b))).mp he
  have hedge := congrArg Prod.fst himage
  have hshared : a.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
      Set.range (boundaryGluingHatEdgeMap W h k hτ) := by
    refine ⟨a.property, ⟨b.val.1, ?_⟩⟩
    exact hedge.symm
  rw [boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ (by omega)] at hshared
  simp at hshared

include hfin in
/-- Helper toward Lemma 5.5: primed and hatted darts are identified exactly
on the beta boundary; the primed endpoint bit is transported by its side flip. -/
theorem lPlusPrimedHattedGluedDart_eq_iff
    (a : LPlusPrimedDart)
    (b : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    (⟦Sum.inr (Sum.inl a)⟧ : LPlusGluedDart longest hqMode hτ) =
        ⟦Sum.inr (Sum.inr b)⟧ ↔
      boundaryGluingPrimedEdgeMap W h k hτ a.1 =
          boundaryGluingHatEdgeMap W h k hτ b.val.1 ∧
        (a.2 ^^ primedLimitSideFlip
          (boundaryGluingFutureStream W h k) hτ a.1) = b.val.2 ∧
        boundaryGluingPrimedEdgeMap W h k hτ a.1 ∈
          boundaryGluingBetaEdges W h k hτ := by
  rw [lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)]
  constructor
  · intro he
    change (boundaryGluingPrimedEdgeMap W h k hτ a.1,
        a.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ a.1) =
      (boundaryGluingHatEdgeMap W h k hτ b.val.1, b.val.2) at he
    rcases Prod.mk.inj he with ⟨heEdge, heBit⟩
    have hshared : boundaryGluingPrimedEdgeMap W h k hτ a.1 ∈
        boundaryGluingPrimedEdges W h k hτ ∩
          boundaryGluingLeftHatEdges W h k hτ
            (ite (longest = true) XDP.ldp XDP.sdp) hqMode := by
      refine ⟨⟨a.1, rfl⟩, ?_⟩
      refine ⟨b.val.1, b.property, ?_⟩
      exact heEdge.symm
    rw [boundaryGluingPrimedEdges_inter_leftHatEdges
      (W := W) (h := h) (k := k) (hτ := hτ)
      (x := ite (longest = true) XDP.ldp XDP.sdp) (hq := hqMode) hfin] at hshared
    exact ⟨heEdge, heBit, hshared⟩
  · rintro ⟨heEdge, heBit, _⟩
    change (boundaryGluingPrimedEdgeMap W h k hτ a.1,
        a.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ a.1) =
      (boundaryGluingHatEdgeMap W h k hτ b.val.1, b.val.2)
    exact Prod.ext heEdge heBit

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the quotient dart map is bijective onto the
geometric left-side dart carrier, using the proved block-image range. -/
@[expose] noncomputable def lPlusGluedDartEquiv :
    LPlusGluedDart longest hqMode hτ ≃
      {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges} :=
  (Setoid.quotientKerEquivRange F).trans
    (Set.equivOfEq (lPlusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft
      (by omega)))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the Equiv evaluates as the quotient-lifted
geometric dart map on every quotient class. -/
theorem lPlusGluedDartEquiv_apply (q : LPlusGluedDart longest hqMode hτ) :
    lPlusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk q =
      lPlusGluedDartMap hτ hp P hqMode Tpath hfin hleft hk q := by
  refine Quotient.inductionOn q ?_
  intro d
  rfl

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every geometric left-side dart is represented by
a block dart modulo the stated boundary gluing. -/
theorem lPlusGluedDartMap_surjective :
    Function.Surjective (lPlusGluedDartMap hτ hp P hqMode Tpath hfin hleft hk) := by
  intro d
  have hd : d.val ∈ Set.range F := by
    rw [lPlusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft (by omega)]
    exact d.property
  rcases hd with ⟨a, ha⟩
  refine ⟨⟦a⟧, ?_⟩
  apply Subtype.ext
  change F a = d.val
  exact ha

end DirectedDistances.PaperProofs.Section5
