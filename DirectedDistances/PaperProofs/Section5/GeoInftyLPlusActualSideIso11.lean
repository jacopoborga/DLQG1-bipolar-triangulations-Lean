/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso10

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),
This file records positive-interface cyclic separation and further
rotation transport for the nonnegative left-side gluing. The beta stars
and interior upper-left stars are transported completely. A conditional
terminal non-port obstruction to corrected rotation 2 is proved below. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "B" => lPlusCodeBlockSide hτ hp P hqMode Tpath hfin hleft hk
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "C" => lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
local notation "E" => lPlusActualCodeBlockCellEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "F" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
local notation "BV" => (Set.ofPred fun v : ℕ => ∃ e : ℕ,
  e ∈ boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingBetaEdges W h k hτ ∧
    (kmswLimitDartVertex (shiftedStream W 0) (e, false) = v ∨
      kmswLimitDartVertex (shiftedStream W 0) (e, true) = v))

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))

local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IP" => lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "J" => (fun d : LPlusHattedDart MH => F (Sum.inr (Sum.inr d)))
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)

include H hfin in
/-- Helper toward Lemma 5.5: the positive beta-interface rotation consists
of two finite open arcs, excluding respectively the primed and hatted blocks.
The separation theorem for the two future blocks has no sign restriction on k. -/
theorem lPlus_positive_boundary_rotation_separation (i : ℕ) :
    let σ := kmswInfRot w (H.1 0)
    let a : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
    let b : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (∀ j : ℕ, 0 < j → j < n →
        (σ : _ → _)^[j] a ∉ Set.range (lMinusPrimedDartImage hτ)) ∧
      (∀ j : ℕ, 0 < j → j < m → (σ : _ → _)^[j] b ∉ Set.range J) ∧
      (σ : _ → _)^[n + m] a = a ∧
      ∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a := by
  exact lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at a noninitial beta vertex the prefix block
is absent, and the two open rotation arcs contain exactly the retained
hatted and primed darts respectively. Every incident dart lies on this cycle. -/
theorem lPlus_positive_boundary_side_separation (i : ℕ)
    (hroot : kmswLimitDartVertex w
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true) ≠
        boundaryVertex w h k) :
    let σ := kmswInfRot w (H.1 0)
    let a : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
    let b : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (σ : _ → _)^[n + m] a = a ∧
      (∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a) ∧
      (∀ x : ℕ × Bool, kmswLimitDartVertex w x = kmswLimitDartVertex w a →
        x ∉ Set.range (fun p : LPlusPrefixDart W h k => p.val)) ∧
      (∀ j : ℕ, 0 < j → j < n →
        (((σ : _ → _)^[j] a).1 ∈ (S).edges ↔
          (σ : _ → _)^[j] a ∈ Set.range J)) ∧
      (∀ j : ℕ, 0 < j → j < m →
        (((σ : _ → _)^[j] b).1 ∈ (S).edges ↔
          (σ : _ → _)^[j] b ∈ Set.range (lMinusPrimedDartImage hτ))) ∧
      ∀ x : ℕ × Bool, kmswLimitDartVertex w x = kmswLimitDartVertex w a →
        x = a ∨ x = b ∨
          (∃ j : ℕ, 0 < j ∧ j < n ∧ (σ : _ → _)^[j] a = x) ∨
          (∃ j : ℕ, 0 < j ∧ j < m ∧ (σ : _ → _)^[j] b = x) := by
  let σ := kmswInfRot w (H.1 0)
  let a : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
  let b : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapH, hperiod, hminimal⟩ :=
    lPlus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  change (σ : _ → _)^[n + m] a = a at hperiod
  have hprefix (x : ℕ × Bool)
      (hv : kmswLimitDartVertex w x = kmswLimitDartVertex w a) :
      x ∉ Set.range (fun p : LPlusPrefixDart W h k => p.val) := by
    rintro ⟨p, rfl⟩
    exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk p (((MH).boundary i).1, true) hv)
  have hmem (x : ℕ × Bool)
      (hv : kmswLimitDartVertex w x = kmswLimitDartVertex w a) :
      x.1 ∈ (S).edges ↔
        x ∈ Set.range (lMinusPrimedDartImage hτ) ∨ x ∈ Set.range J := by
    change x ∈ {d : ℕ × Bool | d.1 ∈ (S).edges} ↔ _
    rw [← lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    constructor
    · rintro ⟨p | (p | d), he⟩
      · exact (hprefix x hv ⟨p, he⟩).elim
      · exact Or.inl ⟨p, he⟩
      · exact Or.inr ⟨d, he⟩
    · rintro (⟨p, he⟩ | ⟨d, he⟩)
      · exact ⟨Sum.inr (Sum.inl p), he⟩
      · exact ⟨Sum.inr (Sum.inr d), he⟩
  have hvertex (j : ℕ) (x : ℕ × Bool) :
      kmswLimitDartVertex w ((σ : _ → _)^[j] x) = kmswLimitDartVertex w x := by
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x
      ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩).symm
  have hba : kmswLimitDartVertex w b = kmswLimitDartVertex w a := by
    rw [← hna]
    exact hvertex n a
  refine ⟨n, m, hn, hm, hna, hmb, hperiod, hminimal, hprefix, ?_, ?_, ?_⟩
  · intro j hj hjn
    exact (hmem _ (hvertex j a)).trans (or_iff_right (hgapP j hj hjn))
  · intro j hj hjm
    exact (hmem _ ((hvertex j b).trans hba)).trans (or_iff_left (hgapH j hj hjm))
  · intro x hv
    obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hv.symm
    have hr' : (σ : _ → _)^[r % (n + m)] a = x :=
      (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
        (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
    let s := r % (n + m)
    have hslt : s < n + m := Nat.mod_lt _ (by omega)
    change (σ : _ → _)^[s] a = x at hr'
    by_cases hs0 : s = 0
    · exact Or.inl (by simpa only [hs0, Function.iterate_zero_apply] using hr'.symm)
    by_cases hsn : s = n
    · exact Or.inr (Or.inl (hr'.symm.trans (hsn ▸ hna)))
    by_cases hs : s < n
    · exact Or.inr (Or.inr (Or.inl ⟨s, by omega, hs, hr'⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨s - n, by omega, by omega, ?_⟩))
      change (σ : _ → _)^[s - n] b = x
      rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hr'

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at a noninitial beta vertex, the corrected
product sends a non-port primed dart to its own primed successor. -/
theorem lPlusGluedCorrectedRotation_primed_nonport_beta (p : ℕ × Bool) (i : ℕ)
    (hvertex : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true))
    (hroot : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) ≠ boundaryVertex w h k)
    (hport : ∀ j : ℕ, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary j).1, b)) :
    lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk (IT p) =
      IT (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p) := by
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let d := IT p
  let y := IT (TR p)
  have hrot := lPlus_primed_nonport_beta_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk p i hvertex hroot hport
  change (S).rotation (D d).val (D y).val at hrot
  have hyv : kmswLimitDartVertex w (D y).val =
      kmswLimitDartVertex w (D d).val := by
    obtain ⟨t, _, ht, _⟩ := hrot
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨t, by simpa only [Equiv.Perm.coe_pow] using ht⟩).symm
  have hnotP : d ∉ Set.range IP := by
    rintro ⟨a, ha⟩
    have he := congrArg (fun q => (D q).val) ha
    have hv := (congrArg (kmswLimitDartVertex w) he).trans hvertex
    exact hroot ((congrArg (kmswLimitDartVertex w) he).symm.trans
      (lPlus_prefix_hatted_shared_endpoint_initial
        (H := H) hτ hqMode hfin hk a (((MH).boundary i).1, true) hv))
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = y :=
    TR.extendDomain_apply_image _ p
  change lPlusHattedExtendedRotation hτ hqMode
    (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
      (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
        (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = y
  rw [hPE, hCU, hTE]
  by_cases hy : y ∈ Set.range IH
  · obtain ⟨a, ha⟩ := hy
    have he := congrArg (fun q => (D q).val) ha
    have hedge : boundaryGluingPrimedEdgeMap W h k hτ (TR p).1 =
        boundaryGluingHatEdgeMap W h k hτ a.val.1 := (congrArg Prod.fst he).symm
    obtain ⟨j, _, hj⟩ := (lMinus_cross_edge_eq_iff hτ hfin (TR p).1 a.val.1).mp hedge
    have hbdy : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    have hyb : y = lPlusBetaGluedDart hτ hqMode (j, a.val.2) := by
      rw [← ha]
      apply congrArg IH
      apply Subtype.ext
      exact Prod.ext (hj.trans hbdy.symm) rfl
    cases hb : a.val.2 with
    | true =>
      rw [hb] at hyb
      rw [hyb]
      have hCB : lPlusBetaCornerRotation hτ hqMode
          (lPlusBetaGluedDart hτ hqMode (j, true)) =
          lPlusBetaGluedDart hτ hqMode (j + 1, false) :=
        lMinusBoundaryCornerPerm.extendDomain_apply_image
          (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (j, true)
      rw [hCB]
      unfold lPlusBetaGluedDart
      rw [lPlusHattedExtendedRotation_apply_hatted]
      exact congrArg IH (lMinusHattedRotation_boundary_corner _ qL j)
    | false =>
      rw [hb] at hyb
      exfalso
      cases j with
      | zero =>
        apply hroot
        change kmswLimitDartVertex w (D d).val = _
        rw [← hyv, hyb]
        exact lPlusBetaGluedDart_initial_vertex hτ hqMode hfin hp P Tpath hleft hk
      | succ j =>
        have hc : lPlusPrimedExtendedRotation hτ hqMode hfin
            (lPlusBetaGluedDart hτ hqMode (j, true)) =
            lPlusBetaGluedDart hτ hqMode (j + 1, false) := by
          rw [lPlusBetaGluedDart_eq_primed hτ hqMode hfin j true]
          simp only [Bool.not_true]
          rw [show lPlusPrimedExtendedRotation hτ hqMode hfin
            (IT (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin j, false)) =
              IT (TR (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin j, false))
            from TR.extendDomain_apply_image _ _]
          change IT (kmswInfRot (primedCode (primedSimInput U) hτ)
            (primedCode_finiteIncidence U hτ hfin)
              (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin j, false)) = _
          rw [lMinusPrimedRotation_boundary_corner hτ hfin j]
          exact (lPlusBetaGluedDart_eq_primed hτ hqMode hfin (j + 1) false).symm
        have hd : d = lPlusBetaGluedDart hτ hqMode (j, true) :=
          (lPlusPrimedExtendedRotation hτ hqMode hfin).injective
            (hTE.trans (hyb.trans hc.symm))
        exact hport j true (congrArg (fun q => (D q).val) hd)
  · have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
      rintro ⟨j, hj⟩
      exact hy ⟨_, hj⟩
    rw [show lPlusBetaCornerRotation hτ hqMode y = y from
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hy

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports arbitrary
non-port primed darts at noninitial beta vertices, including the repair. -/
theorem lPlusGluedCorrectedRotation2_primed_nonport_beta_rotation_iff
    (p : ℕ × Bool) (i : ℕ)
    (hvertex : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true))
    (hroot : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) ≠ boundaryVertex w h k)
    (hport : ∀ j : ℕ, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary j).1, b))
    (e : Q) :
    C (IT p) = e ↔ (S).rotation (D (IT p)).val (D e).val := by
  let d := IT p
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hnotP : d ∉ Set.range IP := by
    rintro ⟨a, ha⟩
    have he := congrArg (fun q => (D q).val) ha
    have hv := (congrArg (kmswLimitDartVertex w) he).trans hvertex
    exact hroot ((congrArg (kmswLimitDartVertex w) he).symm.trans
      (lPlus_prefix_hatted_shared_endpoint_initial
        (H := H) hτ hqMode hfin hk a (((MH).boundary i).1, true) hv))
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hrot : (S).rotation (D d).val (D (R d)).val := by
    rw [lPlusGluedCorrectedRotation_primed_nonport_beta
      hτ hp P hqMode Tpath hfin hleft hk p i hvertex hroot hport]
    exact lPlus_primed_nonport_beta_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk p i hvertex hroot hport
  have hret : R d = lPlusGluedCodeReturn (H := H) hτ hqMode d :=
    ((lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk d (R d)).mpr
      hrot).symm
  have heq : C d = R d := by
    by_cases hn : 0 < (ULedges).length
    · apply lPlusGluedCorrectedRotation2_eq_of_ne hτ hp P hqMode Tpath hfin hleft hk hn d
      · intro he
        exact hnotUL ⟨(_, false), he.symm⟩
      · intro he
        have hdt := lPlusGluedCodeReturn_injective (H := H) hτ hqMode
          (hret.symm.trans he)
        exact hnotUL ⟨(_, false), hdt.symm⟩
    · rw [lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
      unfold lPlusGluedBlockRotation2
      rw [dite_eq_right hn]
  rw [heq, hret]
  exact lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk d e

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every glued dart at a noninitial beta vertex
has the actual side rotation, with no restriction to boundary edges. -/
theorem lPlusGluedCorrectedRotation2_beta_vertex_rotation_iff
    (d : Q) (i : ℕ)
    (hvertex : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true))
    (hroot : kmswLimitDartVertex w (D d).val ≠ boundaryVertex w h k)
    (e : Q) : C d = e ↔ (S).rotation (D d).val (D e).val := by
  revert hvertex hroot
  induction d using Quotient.inductionOn with
  | h a =>
    intro hvertex hroot
    rcases a with a | (p | a)
    · exact (hroot (lPlus_prefix_hatted_shared_endpoint_initial
        (H := H) hτ hqMode hfin hk a (((MH).boundary i).1, true) hvertex)).elim
    · change C (IT p) = e ↔ (S).rotation (D (IT p)).val (D e).val
      by_cases hport : ∃ j : ℕ, ∃ b : Bool,
          lMinusPrimedDartImage hτ p =
            (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary j).1, b)
      · obtain ⟨j, b, hj⟩ := hport
        have heq : IT p = lPlusBetaGluedDart hτ hqMode (j, b) := by
          apply (D).injective
          exact Subtype.ext hj
        rw [heq]
        exact lPlusGluedCorrectedRotation2_hatted_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk _ e
      · exact lPlusGluedCorrectedRotation2_primed_nonport_beta_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk p i hvertex hroot
            (fun j b hj => hport ⟨j, b, hj⟩) e
    · exact lPlusGluedCorrectedRotation2_hatted_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk a e

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: rotation transport holds for every dart at
either endpoint of every beta edge, including its initial endpoint. -/
theorem lPlusGluedCorrectedRotation2_beta_boundary_rotation_iff
    (d : Q)
    (hd : ∃ f : ℕ, f ∈ boundaryGluingBetaEdges W h k hτ ∧
      (kmswLimitDartVertex w (f, false) = kmswLimitDartVertex w (D d).val ∨
        kmswLimitDartVertex w (f, true) = kmswLimitDartVertex w (D d).val))
    (e : Q) : C d = e ↔ (S).rotation (D d).val (D e).val := by
  by_cases hroot : kmswLimitDartVertex w (D d).val = boundaryVertex w h k
  · exact lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d hroot e
  obtain ⟨f, ⟨j, rfl⟩, hj⟩ := hd
  dsimp only at hj
  have hbdy (j : ℕ) : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [← hbdy j] at hj
  rcases hj with hj | hj
  · cases j with
    | zero =>
      exact (hroot (hj.symm.trans
        (lPlusBetaGluedDart_initial_vertex hτ hqMode hfin hp P Tpath hleft hk))).elim
    | succ j =>
      obtain ⟨n, _, _, _, hn, _⟩ :=
        lPlus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin j
      have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
        ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩
      exact lPlusGluedCorrectedRotation2_beta_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk d j (hj.symm.trans hv.symm) hroot e
  · exact lPlusGluedCorrectedRotation2_beta_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d j hj.symm hroot e

include hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a non-port primed dart at an interior
upper-left attachment vertex first returns to the side in its primed block. -/
theorem lPlus_primed_nonport_upperLeft_side_rotation
    (p : ℕ × Bool) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length)
    (hvertex : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (ULedges[i.val], false))
    (hport : ∀ j : Fin (ULedges).length, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠ (ULedges[j.val], b)) :
    (S).rotation (lMinusPrimedDartImage hτ p)
      (lMinusPrimedDartImage hτ (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)) := by
  let σ := kmswInfRot w (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  let a : ℕ × Bool := (ULedges[i.val], false)
  let b : ℕ × Bool := (ULedges[i.val + 1], true)
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapT, hperiod, _⟩ :=
    lPlus_upperLeft_rotation_separation (H := H) hτ hqMode hfin
      (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk
        (by have := i.isLt; omega)) i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  change (σ : _ → _)^[n + m] a = a at hperiod
  obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hvertex.symm
  let s := r % (n + m)
  have hslt : s < n + m := Nat.mod_lt _ (by omega)
  have hr' : (σ : _ → _)^[s] a = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
      (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
  have hs0 : 0 < s := by
    by_contra hh
    have hz : s = 0 := by omega
    exact hport i false (by simpa only [hz, Function.iterate_zero_apply] using hr'.symm)
  have hsn : s < n := by
    by_contra hh
    by_cases hs : s = n
    · exact hport ⟨i.val + 1, hi⟩ true (hr'.symm.trans (hs ▸ hna))
    · apply hgapT (s - n) (by omega) (by omega)
      refine ⟨p, ?_⟩
      change x = (σ : _ → _)^[s - n] b
      rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hr'.symm
  have hxb : (σ : _ → _)^[n - s] x = b := by
    rw [← hr', ← Function.iterate_add_apply, Nat.sub_add_cancel hsn.le, hna]
  obtain ⟨q, hq, _⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk ⟨i.val + 1, hi⟩ true
  obtain ⟨t, ht, hte, htgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  have htle : t ≤ n - s := by
    by_contra hh
    exact htgap (n - s) (by omega) (by omega) ⟨q, hq.trans hxb.symm⟩
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hmem : (σ : _ → _)^[j] x ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hmem
  rcases c with q | (q | d)
  · apply hgapP (s + j) (by omega) (by omega)
    refine ⟨q, ?_⟩
    rw [Nat.add_comm s j, Function.iterate_add_apply, hr']
    exact hc
  · exact htgap j hj hjt ⟨q, hc⟩
  · have hv : kmswLimitDartVertex w (J d) = kmswLimitDartVertex w x := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hc).trans he.symm
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) d.val (hvertex.symm.trans hv.symm)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports every
non-port primed dart at an interior upper-left attachment vertex. -/
theorem lPlusGluedCorrectedRotation2_primed_nonport_upperLeft_rotation_iff
    (p : ℕ × Bool) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length)
    (hvertex : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (ULedges[i.val], false))
    (hport : ∀ j : Fin (ULedges).length, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠ (ULedges[j.val], b))
    (e : Q) : C (IT p) = e ↔ (S).rotation (D (IT p)).val (D e).val := by
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let d := IT p
  let y := IT (TR p)
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hrot := lPlus_primed_nonport_upperLeft_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk p i hi hvertex hport
  change (S).rotation (D d).val (D y).val at hrot
  have hyv : kmswLimitDartVertex w (D y).val =
      kmswLimitDartVertex w (D d).val := by
    obtain ⟨t, _, ht, _⟩ := hrot
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨t, by simpa only [Equiv.Perm.coe_pow] using ht⟩).symm
  have hnotP : d ∉ Set.range IP := by
    rintro ⟨a, ha⟩
    have he := congrArg (fun q => (D q).val.1) ha
    have hm : (lMinusPrimedDartImage hτ p).1 ∈
        boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ :=
      ⟨he ▸ a.property, ⟨p.1, rfl⟩⟩
    rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk] at hm
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (List.mem_reverse.mpr hm)
    exact hport ⟨j, hj⟩ (lMinusPrimedDartImage hτ p).2 (Prod.ext hje.symm rfl)
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hnotH : y ∉ Set.range IH := by
    rintro ⟨a, ha⟩
    have hv := congrArg (fun q => kmswLimitDartVertex w (D q).val) ha
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) a.val
      (hvertex.symm.trans (hyv.symm.trans hv.symm))
  have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  have hR : R d = y := by
    have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = d :=
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
    have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d :=
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
    have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = y :=
      TR.extendDomain_apply_image _ p
    have hCB : lPlusBetaCornerRotation hτ hqMode y = y :=
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB
    have hHE : lPlusHattedExtendedRotation hτ hqMode y = y :=
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
          (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = y
    rw [hPE, hCU, hTE, hCB, hHE]
  have hret : R d = lPlusGluedCodeReturn (H := H) hτ hqMode d :=
    hR.trans ((lPlusGluedCodeReturn_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d y).mpr hrot).symm
  have heq : C d = R d := by
    by_cases hn : 0 < (ULedges).length
    · apply lPlusGluedCorrectedRotation2_eq_of_ne hτ hp P hqMode Tpath hfin hleft hk hn d
      · intro he
        exact hnotUL ⟨(_, false), he.symm⟩
      · intro he
        have hdt := lPlusGluedCodeReturn_injective (H := H) hτ hqMode
          (hret.symm.trans he)
        exact hnotUL ⟨(_, false), hdt.symm⟩
    · rw [lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
      unfold lPlusGluedBlockRotation2
      rw [dite_eq_right hn]
  rw [heq, hret]
  exact lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk d e

include hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a non-port prefix dart at an interior
upper-left attachment vertex first returns to the side in its prefix block. -/
theorem lPlus_prefix_nonport_upperLeft_side_rotation
    (p : LPlusPrefixDart W h k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length)
    (hvertex : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (ULedges[i.val], false))
    (hport : ∀ j : Fin (ULedges).length, ∀ b : Bool,
      p.val ≠ (ULedges[j.val], b)) :
    (S).rotation p.val
      (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
        (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk p).val := by
  have hkpos := lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk
    (show 0 < (ULedges).length by have := i.isLt; omega)
  rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos]
  let σ := kmswInfRot w (H.1 0)
  let x := p.val
  let a : ℕ × Bool := (ULedges[i.val], false)
  let b : ℕ × Bool := (ULedges[i.val + 1], true)
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapT, hperiod, _⟩ :=
    lPlus_upperLeft_rotation_separation (H := H) hτ hqMode hfin hkpos i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  change (σ : _ → _)^[n + m] a = a at hperiod
  obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hvertex.symm
  let s := r % (n + m)
  have hslt : s < n + m := Nat.mod_lt _ (by omega)
  have hr' : (σ : _ → _)^[s] a = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
      (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
  have hns : n < s := by
    by_cases hs : s = 0
    · exact (hport i false
        (by simpa only [hs, Function.iterate_zero_apply] using hr'.symm)).elim
    by_cases hs : s < n
    · exact (hgapP s (by omega) hs ⟨p, hr'.symm⟩).elim
    by_cases hs : s = n
    · exact (hport ⟨i.val + 1, hi⟩ true (hr'.symm.trans (hs ▸ hna))).elim
    omega
  have hxb : (σ : _ → _)^[s - n] b = x := by
    rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel hns.le]
    exact hr'
  have hxa : (σ : _ → _)^[n + m - s] x = a := by
    rw [← hr', ← Function.iterate_add_apply, Nat.sub_add_cancel hslt.le]
    exact hperiod
  obtain ⟨t, ht, hte, htgap⟩ :=
    lPlusPrefixDartImage_firstReturn (H := H) hτ longest hqMode hkpos p
  have htle : t ≤ n + m - s := by
    by_contra hh
    exact htgap (n + m - s) (by omega) (by omega)
      ⟨⟨a, lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩, hxa.symm⟩
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hmem : (σ : _ → _)^[j] x ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hmem
  rcases c with q | (q | d)
  · exact htgap j hj hjt ⟨q, hc⟩
  · apply hgapT (s - n + j) (by omega) (by omega)
    refine ⟨q, ?_⟩
    rw [Nat.add_comm (s - n) j, Function.iterate_add_apply, hxb]
    exact hc
  · have hv : kmswLimitDartVertex w (J d) = kmswLimitDartVertex w x := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hc).trans he.symm
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) d.val (hvertex.symm.trans hv.symm)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: all rotation transport outside the finite
upper-left vertex stars follows from the initial, interior and beta cases. -/
theorem lPlusGluedCorrectedRotation2_rotation_iff_of_not_upperLeft_vertex
    (d e : Q)
    (hd : ¬ ∃ f : ℕ, f ∈ boundaryGluingUpperLeftEdges W h k ∧
      (kmswLimitDartVertex w (f, false) = kmswLimitDartVertex w (D d).val ∨
        kmswLimitDartVertex w (f, true) = kmswLimitDartVertex w (D d).val)) :
    C d = e ↔ (S).rotation (D d).val (D e).val := by
  by_cases hb : kmswLimitDartVertex w (D d).val ∈ BV
  · obtain ⟨f, hf | hf, hend⟩ := hb
    · exact (hd ⟨f, hf, hend⟩).elim
    · exact lPlusGluedCorrectedRotation2_beta_boundary_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk d ⟨f, hf, hend⟩ e
  · exact lPlusGluedCorrectedRotation2_interior
      hτ hp P hqMode Tpath hfin hleft hk d hb e

include H hqMode hfin hk in
/-- Helper toward Lemma 5.5: at an interior upper-left vertex, a dart
shared by prefix and primed blocks is one of the two indexed ports. -/
theorem lPlus_upperLeft_shared_dart_eq_ports
    (i : Fin (ULedges).length) (hi : i.val + 1 < (ULedges).length)
    (x : ℕ × Bool)
    (hvertex : kmswLimitDartVertex w x = kmswLimitDartVertex w (ULedges[i.val], false))
    (hpref : x ∈ Set.range (fun p : LPlusPrefixDart W h k => p.val))
    (hprime : x ∈ Set.range (lMinusPrimedDartImage hτ)) :
    x = (ULedges[i.val], false) ∨ x = (ULedges[i.val + 1], true) := by
  let σ := kmswInfRot w (H.1 0)
  let a : ℕ × Bool := (ULedges[i.val], false)
  let b : ℕ × Bool := (ULedges[i.val + 1], true)
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapT, hperiod, _⟩ :=
    lPlus_upperLeft_rotation_separation (H := H) hτ hqMode hfin
      (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk
        (by have := i.isLt; omega)) i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[n + m] a = a at hperiod
  obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hvertex.symm
  let s := r % (n + m)
  have hslt : s < n + m := Nat.mod_lt _ (by omega)
  have hr' : (σ : _ → _)^[s] a = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
      (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
  by_cases hs0 : s = 0
  · exact Or.inl (by simpa only [hs0, Function.iterate_zero_apply] using hr'.symm)
  by_cases hsn : s = n
  · exact Or.inr (hr'.symm.trans (hsn ▸ hna))
  by_cases hs : s < n
  · exact (hgapP s (by omega) hs (hr'.symm ▸ hpref)).elim
  · apply False.elim
    apply hgapT (s - n) (by omega) (by omega)
    have he : (σ : _ → _)^[s - n] b = x := by
      rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hr'
    exact he.symm ▸ hprime

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports arbitrary
non-port prefix darts at interior upper-left attachment vertices. -/
theorem lPlusGluedCorrectedRotation2_prefix_nonport_upperLeft_rotation_iff
    (p : LPlusPrefixDart W h k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length)
    (hvertex : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (ULedges[i.val], false))
    (hport : ∀ j : Fin (ULedges).length, ∀ b : Bool, p.val ≠ (ULedges[j.val], b))
    (e : Q) : C (IP p) = e ↔ (S).rotation (D (IP p)).val (D e).val := by
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  let d := IP p
  let y := IP (PR p)
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  have hrot := lPlus_prefix_nonport_upperLeft_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk p i hi hvertex hport
  change (S).rotation (D d).val (D y).val at hrot
  have hyv : kmswLimitDartVertex w (D y).val = kmswLimitDartVertex w p.val := by
    obtain ⟨t, _, ht, _⟩ := hrot
    change (kmswInfRot w (H.1 0) : _ → _)^[t] p.val = (D y).val at ht
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨t, by simpa only [Equiv.Perm.coe_pow] using ht⟩).symm
  have hnotUL : d ∉ Set.range UL := by
    rintro ⟨j, hj⟩
    exact hport j.1 j.2 (congrArg (fun q => (D q).val) hj.symm)
  have hnotH : y ∉ Set.range IH := by
    rintro ⟨a, ha⟩
    have hv := congrArg (fun q => kmswLimitDartVertex w (D q).val) ha
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) a.val
      (hvertex.symm.trans (hyv.symm.trans hv.symm))
  have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  have hCT : lPlusPrimedExtendedRotation hτ hqMode hfin
      (lPlusUpperLeftCornerRotation hτ hqMode hfin hk y) = y := by
    by_cases hy : y ∈ Set.range IT
    · obtain ⟨q, hq⟩ := hy
      have he := congrArg (fun q => (D q).val) hq
      have hports := lPlus_upperLeft_shared_dart_eq_ports
        (H := H) hτ hqMode hfin hk i hi (PR p).val
        (hyv.trans hvertex) ⟨PR p, rfl⟩ ⟨q, he⟩
      rcases hports with ha | hb
      · have hya : y = UL (i, false) := by
          apply (D).injective
          exact Subtype.ext ha
        rw [hya]
        have hcorner : lPlusUpperLeftCornerPerm (ULedges).length (i, false) =
            (⟨i.val + 1, hi⟩, true) := by
          change lPlusUpperLeftCorner (ULedges).length (i, false) = _
          simp only [lPlusUpperLeftCorner,
            Bool.false_eq_true, ↓reduceIte, hi, ↓reduceDIte]
        have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk (UL (i, false)) =
            UL (⟨i.val + 1, hi⟩, true) := by
          exact ((lPlusUpperLeftCornerPerm (ULedges).length).extendDomain_apply_image
            (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
              (i, false)).trans (congrArg UL hcorner)
        rw [hCU]
        exact lPlusPrimedExtendedRotation_upperLeft_east (H := H) hτ hqMode hfin hk i hi
      · have hye : y = UL (⟨i.val + 1, hi⟩, true) := by
          apply (D).injective
          exact Subtype.ext hb
        have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = y :=
          PR.extendDomain_apply_image _ p
        have hcorner := lPlusPrefixExtendedRotation_upperLeft_west
          hτ hp P hqMode Tpath hfin hleft hk
            (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk
              (by have := i.isLt; omega)) i hi
        have hd : d = UL (i, false) :=
          (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk).injective
            (hPE.trans (hye.trans hcorner.symm))
        exact (hnotUL ⟨(i, false), hd.symm⟩).elim
    · have hyUL : y ∉ Set.range UL := by
        rintro ⟨j, hj⟩
        obtain ⟨q, _, hq⟩ := lPlusUpperLeftGluedDart_primed_representative
          hτ hqMode hfin hk j.1 j.2
        exact hy ⟨q, hq.symm.trans hj⟩
      rw [show lPlusUpperLeftCornerRotation hτ hqMode hfin hk y = y from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hyUL]
      exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hy
  have hR : R d = y := by
    have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = y :=
      PR.extendDomain_apply_image _ p
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
          (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = y
    rw [hPE, hCT,
      show lPlusBetaCornerRotation hτ hqMode y = y from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  have hret : R d = lPlusGluedCodeReturn (H := H) hτ hqMode d :=
    hR.trans ((lPlusGluedCodeReturn_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d y).mpr hrot).symm
  have heq : C d = R d := by
    by_cases hn : 0 < (ULedges).length
    · apply lPlusGluedCorrectedRotation2_eq_of_ne hτ hp P hqMode Tpath hfin hleft hk hn d
      · intro he
        exact hnotUL ⟨(_, false), he.symm⟩
      · intro he
        have hdt := lPlusGluedCodeReturn_injective (H := H) hτ hqMode
          (hret.symm.trans he)
        exact hnotUL ⟨(_, false), hdt.symm⟩
    · rw [lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
      unfold lPlusGluedBlockRotation2
      rw [dite_eq_right hn]
  rw [heq, hret]
  exact lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk d e

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every dart at an interior upper-left
attachment vertex has the actual side rotation under corrected rotation 2. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_vertex_rotation_iff
    (d : Q) (i : Fin (ULedges).length) (hi : i.val + 1 < (ULedges).length)
    (hvertex : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (ULedges[i.val], false))
    (e : Q) : C d = e ↔ (S).rotation (D d).val (D e).val := by
  by_cases hport : ∃ j : Fin (ULedges).length, ∃ b : Bool,
      (D d).val = (ULedges[j.val], b)
  · obtain ⟨j, b, hj⟩ := hport
    have heq : d = lPlusUpperLeftGluedDart hτ hqMode hfin hk (j, b) := by
      apply (D).injective
      exact Subtype.ext hj
    rw [heq]
    exact lPlusGluedCorrectedRotation2_upperLeft_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk j b e
  have hn : ∀ j : Fin (ULedges).length, ∀ b : Bool, (D d).val ≠ (ULedges[j.val], b) :=
    fun j b hj => hport ⟨j, b, hj⟩
  revert hvertex hn
  induction d using Quotient.inductionOn with
  | h a =>
    intro hvertex hn
    rcases a with p | (p | a)
    · exact lPlusGluedCorrectedRotation2_prefix_nonport_upperLeft_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk p i hi hvertex hn e
    · exact lPlusGluedCorrectedRotation2_primed_nonport_upperLeft_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk p i hi hvertex hn e
    · exact lPlusGluedCorrectedRotation2_hatted_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk a e

include H in
/-- Helper toward Lemma 5.5: the first left triangle fixes the successor
of the old lower-left dart in both finite and ambient rotations. -/
theorem lPlus_first_left_lowerLeft_rotations (hc₀ : w 0 = 0) :
    kmswInfRot w (H.1 0) (2, false) = (1, false) ∧
    ∃ ha : 1 < (kmswStage w 1).nextEdge, ∃ hb : 2 < (kmswStage w 1).nextEdge,
      stageRot w 1 (⟨2, hb⟩, false) = (⟨1, ha⟩, false) := by
  let j : TriangleCreationTime w := ⟨0, Or.inl hc₀⟩
  have ht : stageTriangleDartTriple w j = ((0, false), (1, true), (2, false)) := by
    simp [stageTriangleDartTriple, j, kmswStage, hc₀, kmswInit]
  have hi := (kmswInfFaceSucc_stageTriangle_cycle w (H.1 0) j).2.1
  rw [ht] at hi
  change (kmswInfRot w (H.1 0)).symm (1, false) = (2, false) at hi
  have hsize : (kmswStage w 1).nextEdge = 3 := by
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  have ha : 1 < (kmswStage w 1).nextEdge := by omega
  have hb : 2 < (kmswStage w 1).nextEdge := by omega
  have hf := (stageTriangle_isFace w j 1 (by dsimp [j]; omega)).2.1
  simp only [stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt, ht] at hf
  change (stageRot w 1).symm (⟨1, ha⟩, false) = (⟨2, hb⟩, false) at hf
  exact ⟨((kmswInfRot w (H.1 0)).symm_apply_eq.mp hi).symm,
    ha, hb, ((stageRot w 1).symm_apply_eq.mp hf).symm⟩

include hp P Tpath hfin hleft hk in



theorem lPlusGluedCorrectedRotation2_terminal_nonport_obstruction
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    ∃ d : Q, (D d).val = (2, false) ∧ C d = d ∧
      ¬ (S).rotation (D d).val (D (C d)).val := by
  subst k
  let Q₁ := LPlusGluedDart longest hqMode hτ
  let D₁ := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let C₁ := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
  let S₁ := m0GeodesicSide hp P ThinMapSide.left
  let IP₁ := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH₁ := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let es := List.reverse (List.dropLast (State.UL
    (kmswStage w (boundaryHitTime w h 1))))
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  have ht := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
  have hUL : es = [1] := by
    dsimp only [es]
    rw [ht]
    simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hn : 0 < es.length := by rw [hUL]; decide
  let i : Fin es.length := ⟨es.length - 1, by omega⟩
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  have htv : (D₁ t).val = (1, false) := by
    change (es[i.val], false) = _
    simp [i, hUL]
  have hmem (f : ℕ) (hf : f < 3) : f ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h) (by omega : 0 < (1 : ℤ))]
    change f < (kmswStage w (boundaryHitTime w h 1 - 1)).nextEdge
    rw [hprev]
    simpa [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge] using hf
  let p : LPlusPrefixDart W h 1 := ⟨(2, false), hmem 2 (by omega)⟩
  let a : LPlusPrefixDart W h 1 := ⟨(1, false), hmem 1 (by omega)⟩
  let d := IP₁ p
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := 1) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  obtain ⟨hσ, ha, hb, hstage⟩ := lPlus_first_left_lowerLeft_rotations (H := H) hc₀
  have hPR : PR p = a := by
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk (by omega : 0 < (1 : ℤ))]
    apply Subtype.ext
    have hlocal : ∀ (n : ℕ) (hn : n = 1) (he : 2 < (kmswStage w n).nextEdge),
        ((stageRot w n (⟨2, he⟩, false)).1.val,
          (stageRot w n (⟨2, he⟩, false)).2) = (1, false) := by
      intro n hn he
      subst n
      exact congrArg (fun q : StageDart (kmswStage w 1).nextEdge => (q.1.val, q.2)) hstage
    exact hlocal _ hprev _
  have hat : IP₁ a = t := by
    apply (D₁).injective
    exact Subtype.ext htv.symm
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = t :=
    (PR.extendDomain_apply_image _ p).trans ((congrArg IP₁ hPR).trans hat)
  have hcorner : lPlusUpperLeftCornerPerm es.length (i, false) = (i, false) := by
    change lPlusUpperLeftCorner es.length (i, false) = _
    simp only [lPlusUpperLeftCorner, Bool.false_eq_true, ↓reduceIte,
      dite_eq_right (show ¬ i.val + 1 < es.length by dsimp [i]; omega)]
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk t = t :=
    ((lPlusUpperLeftCornerPerm es.length).extendDomain_apply_image
      (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
        (i, false)).trans (congrArg (lPlusUpperLeftGluedDart hτ hqMode hfin hk) hcorner)
  have hcode : lPlusGluedCodeReturn (H := H) hτ hqMode t = TE t :=
    lPlusGluedCodeReturn_upperLeft_west (H := H) hτ hqMode hfin hk i
  have hyv : kmswLimitDartVertex w (D₁ (TE t)).val = kmswLimitDartVertex w (D₁ t).val := by
    obtain ⟨n, _, he, _⟩ := lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk t
    rw [hcode] at he
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using he⟩).symm
  have hnotH : TE t ∉ Set.range IH₁ := by
    rintro ⟨q, hq⟩
    have hv := congrArg (fun q => kmswLimitDartVertex w (D₁ q).val) hq
    have hv' := hyv.symm.trans hv.symm
    change kmswLimitDartVertex w (es[i.val], false) =
      kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h 1 hτ q.val.1, q.val.2) at hv'
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) q.val hv'
  have hnotB : TE t ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  have hRd : R d = lPlusGluedCodeReturn (H := H) hτ hqMode t := by
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode (TE
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
          (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = _
    rw [hPE, hCU, ← hcode]
    rw [hcode,
      show lPlusBetaCornerRotation hτ hqMode (TE t) = TE t from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  obtain ⟨t', ht', hRt'⟩ := lPlus_terminal_corrected_of_left_down
    hτ hp P hqMode Tpath hfin hleft hk rfl hc₀ hc₁
  have hteq : t' = t := (D₁).injective (Subtype.ext (ht'.trans htv.symm))
  have hRt : R t = d := by
    apply (D₁).injective
    apply Subtype.ext
    exact hteq ▸ hRt'
  have hfix : C₁ d = d := by
    have hpre : R.symm (lPlusGluedCodeReturn (H := H) hτ hqMode t) = d :=
      R.symm_apply_eq.mpr hRd.symm
    have he := lPlusGluedCorrectedRotation2_terminal_preimage
      hτ hp P hqMode Tpath hfin hleft hk hn
    change C₁ (R.symm (lPlusGluedCodeReturn (H := H) hτ hqMode t)) = R t at he
    rw [hpre, hRt] at he
    exact he
  have hrot : (S₁).rotation (D₁ d).val (D₁ t).val := by
    refine ⟨1, by omega, ?_, ?_⟩
    · change kmswInfRot w (H.1 0) (2, false) = (D₁ t).val
      exact hσ.trans htv.symm
    · intro j hj hj1
      omega
  refine ⟨d, rfl, hfix, ?_⟩
  rw [hfix]
  intro hself
  have he := firstReturn_endpoint_unique
    (kmswInfRot w (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S₁).edges}
      (D₁ t).property (D₁ d).property hrot hself
  rw [htv] at he
  have hh := congrArg Prod.fst he
  change (1 : ℕ) = 2 at hh
  omega

include hp P Tpath hfin hleft hk in


theorem lPlusGluedCorrectedRotation2_not_all_dart_rotation_iff_of_left_down
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    ¬ (∀ d e : Q, C d = e ↔ (S).rotation (D d).val (D e).val) := by
  obtain ⟨d, _, _, hbad⟩ := lPlusGluedCorrectedRotation2_terminal_nonport_obstruction
    hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁
  intro hall
  exact hbad ((hall d (C d)).mp rfl)

end DirectedDistances.PaperProofs.Section5















































































































/- Validation: development checks had exits 0 and 1; every reported
axiom-probe compile exited 0 for all sixteen declarations, each reporting
exactly [propext, Classical.choice, Quot.sound]. Probes were removed.
Only the prescribed single-file compile wrapper was used. No separate
were introduced. This is no claim of completion of Lemma 5.5. -/
