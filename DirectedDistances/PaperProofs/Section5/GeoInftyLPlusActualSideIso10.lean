/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso9
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideInterior2







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

include H hqMode hfin hk in
/-- Helper toward Lemma 5.5: away from the initial vertex, no endpoint
of the finite upper-left attachment is incident to any hatted dart. -/
theorem lPlus_upperLeft_endpoint_not_hatted_of_ne_initial
    (i : Fin (ULedges).length) (b : Bool)
    (hroot : kmswLimitDartVertex w (ULedges[i.val], b) ≠ boundaryVertex w h k)
    (d : ℕ × Bool) :
    kmswLimitDartVertex w (ULedges[i.val], b) ≠
      kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h k hτ d.1, d.2) := by
  cases b with
  | false =>
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) d
  | true =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      exfalso
      apply hroot
      obtain ⟨a, as, hs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hi)
      have he := lPlusPrefixUpperLeftDarts_first_starts_at_xk (W := W) (h := h) hs
      simpa only [Fin.val_mk, hs, List.getElem_cons_zero, kmswLimitDartVertex,
        ↓reduceIte] using he
    | succ i =>
      have hip : i < (ULedges).length := by omega
      obtain ⟨n, _, _, _, hn, _⟩ := lPlus_upperLeft_rotation_separation
        (H := H) hτ hqMode hfin (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk (by omega)) i
        (ULedges[i]) (ULedges[i + 1])
        (List.getElem?_eq_getElem hip) (List.getElem?_eq_getElem hi)
      have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        (ULedges[i], false) (ULedges[i + 1], true)).mp
          ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩
      change kmswLimitDartVertex w (ULedges[i], false) =
        kmswLimitDartVertex w (ULedges[i + 1], true) at hv
      change kmswLimitDartVertex w (ULedges[i + 1], true) ≠ _
      rw [← hv]
      exact lPlus_upperLeft_west_not_hatted hτ i _
        (List.getElem?_eq_getElem hip) d

include H hqMode hfin hk in
/-- Helper toward Lemma 5.5: a vertex common to the prefix and hatted
blocks must be the initial attachment vertex; incident edges need not be ports. -/
theorem lPlus_prefix_hatted_shared_endpoint_initial
    (a : LPlusPrefixDart W h k) (d : ℕ × Bool)
    (hv : kmswLimitDartVertex w a.val =
      kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)) :
    kmswLimitDartVertex w a.val = boundaryVertex w h k := by
  by_contra hroot
  obtain ⟨e, he, hend⟩ := lPlus_prefix_future_shared_endpoint hτ hk a
    (hatLimitEdgeMap U hτ d.1, d.2) hv
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem (List.mem_reverse.mpr he)
  rcases hend with hend | hend
  · exact lPlus_upperLeft_endpoint_not_hatted_of_ne_initial
      (H := H) hτ hqMode hfin hk ⟨i, hi⟩ false
      (by rw [hie, hend]; exact hroot) d (by rw [hie, hend]; exact hv)
  · exact lPlus_upperLeft_endpoint_not_hatted_of_ne_initial
      (H := H) hτ hqMode hfin hk ⟨i, hi⟩ true
      (by rw [hie, hend]; exact hroot) d (by rw [hie, hend]; exact hv)

local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IP" => lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "J" => (fun d : LPlusHattedDart MH => F (Sum.inr (Sum.inr d)))
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "HR" => lPlusHattedRotation (ite (longest = true) XDP.ldp XDP.sdp) qL

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: an arbitrary non-port hatted dart away from
the initial vertex has its own block successor in the complete left side,
including when its vertex lies on the beta gluing boundary. -/
theorem lPlus_hatted_nonport_side_rotation (a : LPlusHattedDart MH)
    (hroot : kmswLimitDartVertex w (J a) ≠ boundaryVertex w h k)
    (hport : ∀ i : ℕ, ∀ b : Bool,
      J a ≠ (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, b)) :
    (S).rotation (J a) (J (HR a)) := by
  let σ := kmswInfRot w (H.1 0)
  let x := J a
  have hbdy (i : ℕ) : ((MH).boundary i).1 = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  obtain ⟨t, ht, hte, htgap⟩ := lPlusHattedDartImage_firstReturn
    (H := H) hτ hqMode hfin a
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hm : (σ : _ → _)^[j] x ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hm
  have hv : kmswLimitDartVertex w (F c) = kmswLimitDartVertex w x := by
    have hv' := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
      x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
    exact (congrArg (kmswLimitDartVertex w) hc).trans hv'.symm
  rcases c with p | (p | d)
  · exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk p a.val hv)
  · obtain hz | ⟨i, hi⟩ := lMinus_shared_dart_endpoint_interface hτ hfin p a.val hv
    · apply hroot
      exact hv.symm.trans (hz.trans (by
        change boundaryGluingFutureVertexMap W h k (hatLimitVertexMap U hτ 0) = _
        rw [hatLimitVertexMap_root, boundaryGluingFutureVertexMap_zero]))
    rw [← hbdy i] at hi
    let u : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
    let v : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
    obtain ⟨n, m, hn, hm, hnu, hmv, hgapP, hgapH, hperiod, _⟩ :=
      lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
    change (σ : _ → _)^[n] u = v at hnu
    change (σ : _ → _)^[m] v = u at hmv
    change (σ : _ → _)^[n + m] u = u at hperiod
    have hvx : kmswLimitDartVertex w u = kmswLimitDartVertex w x := hi.symm.trans hv
    obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) u x).mpr hvx
    have hr' : (σ : _ → _)^[r % (n + m)] u = x :=
      (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
        (by simpa only [Equiv.Perm.coe_pow] using hr)
    let s := r % (n + m)
    change (σ : _ → _)^[s] u = x at hr'
    have hslt : s < n + m := Nat.mod_lt _ (by omega)
    have hspos : 0 < s := by
      by_contra hh
      have hs0 : s = 0 := by omega
      exact hport i true (by simpa only [hs0, Function.iterate_zero_apply] using hr'.symm)
    have hsn : s < n := by
      by_contra hh
      by_cases he : s = n
      · exact hport (i + 1) false (hr'.symm.trans (he ▸ hnu))
      · apply hgapH (s - n) (by omega) (by omega)
        refine ⟨a, ?_⟩
        change x = (σ : _ → _)^[s - n] v
        rw [← hnu, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hr'.symm
    have hxv : (σ : _ → _)^[n - s] x = v := by
      rw [← hr', ← Function.iterate_add_apply, Nat.sub_add_cancel hsn.le]
      exact hnu
    have hvH : v ∈ Set.range J :=
      ⟨⟨(((MH).boundary (i + 1)).1, false),
        lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ (i + 1)⟩, rfl⟩
    have htle : t ≤ n - s := by
      by_contra hh
      apply htgap (n - s) (by omega) (by omega)
      exact hxv.symm ▸ hvH
    apply hgapP (s + j) (by omega) (by omega)
    refine ⟨p, ?_⟩
    change lMinusPrimedDartImage hτ p = (σ : _ → _)^[s + j] u
    rw [Nat.add_comm s j, Function.iterate_add_apply, hr']
    exact hc
  · exact htgap j hj hjt ⟨d, hc⟩

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports every
non-port hatted input outside the initial star, even at gluing vertices. -/
theorem lPlusGluedCorrectedRotation2_hatted_nonport_rotation_iff
    (a : LPlusHattedDart MH)
    (hroot : kmswLimitDartVertex w (J a) ≠ boundaryVertex w h k)
    (hport : ∀ i : ℕ, ∀ b : Bool,
      J a ≠ (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, b))
    (e : Q) : C (IH a) = e ↔ (S).rotation (D (IH a)).val (D e).val := by
  let d := IH a
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hnotP : d ∉ Set.range IP := by
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
  have hnotT : d ∉ Set.range IT := by
    rintro ⟨p, hp'⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hp'
    obtain ⟨i, _, hi⟩ := (lMinus_cross_edge_eq_iff hτ hfin p.1 a.val.1).mp
      (congrArg Prod.fst he)
    apply hport i a.val.2
    change (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2) = _
    have hb : ((MH).boundary i).1 = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    rw [hi, hb]
  have hnotB : d ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨p, hp'⟩
    apply hport p.1 p.2
    exact congrArg (fun q => (D q).val) hp'.symm
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT
  have hCB : lPlusBetaCornerRotation hτ hqMode d = d :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB
  have hR : R d = lPlusHattedExtendedRotation hτ hqMode d := by
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode
        (lPlusPrimedExtendedRotation hτ hqMode hfin
          (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
            (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk d)))) = _
    rw [hPE, hCU, hTE, hCB]
  have hrot : (S).rotation (D d).val (D (R d)).val := by
    rw [hR, lPlusHattedExtendedRotation_apply_hatted]
    exact lPlus_hatted_nonport_side_rotation hτ hp P hqMode Tpath hfin hleft hk
      a hroot hport
  have hret : R d = lPlusGluedCodeReturn (H := H) hτ hqMode d :=
    (lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk d (R d)).mpr
      hrot |>.symm
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
/-- Helper toward Lemma 5.5: the incoming beta port returns to the whole
left side at its hatted successor; the prefix is excluded by vertex separation. -/
theorem lPlus_beta_incoming_side_rotation (i : ℕ)
    (hroot : kmswLimitDartVertex w
      (D (lPlusBetaGluedDart hτ hqMode (i, true))).val ≠ boundaryVertex w h k) :
    let a : LPlusHattedDart MH :=
      ⟨(((MH).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
    (S).rotation (J a) (J (HR a)) := by
  dsimp only
  let a : LPlusHattedDart MH :=
    ⟨(((MH).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  let σ := kmswInfRot w (H.1 0)
  obtain ⟨n, m, hn, _, hna, _, hgapP, _⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ :=
    lPlusHattedDartImage_firstReturn (H := H) hτ hqMode hfin a
  change (σ : _ → _)^[n] (J a) =
    (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false) at hna
  have hnH : (σ : _ → _)^[n] (J a) ∈ Set.range J := by
    rw [hna]
    exact ⟨⟨(((MH).boundary (i + 1)).1, false),
      lMinus_hatted_boundary_mem _ qL (i + 1)⟩, rfl⟩
  have htn : t ≤ n := by
    by_contra hh
    exact htgap n hn (by omega) hnH
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hm : (σ : _ → _)^[j] (J a) ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hm
  rcases c with p | (p | d)
  · have hv : kmswLimitDartVertex w p.val = kmswLimitDartVertex w (J a) := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        (J a) ((σ : _ → _)^[j] (J a))).mp
          ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hc).trans he.symm
    exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk p a.val hv)
  · exact hgapP j hj (lt_of_lt_of_le hjt htn) ⟨p, hc⟩
  · exact htgap j hj hjt ⟨d, hc⟩

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an incoming beta port the primed corner
and beta exchange cancel, leaving exactly the hatted block successor. -/
theorem lPlusGluedCorrectedRotation_beta_incoming (i : ℕ) :
    lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
      (lPlusBetaGluedDart hτ hqMode (i, true)) =
    lPlusHattedExtendedRotation hτ hqMode (lPlusBetaGluedDart hτ hqMode (i, true)) := by
  let a := lPlusBetaGluedDart hτ hqMode (i, true)
  let b := lPlusBetaGluedDart hτ hqMode (i + 1, false)
  let idx := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  have hbdy (j : ℕ) : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  have hrep (j : ℕ) (s : Bool) :
      IT (idx j, !s) = lPlusBetaGluedDart hτ hqMode (j, s) := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
    change lMinusPrimedDartImage hτ (idx j, !s) =
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary j).1, s)
    rw [lMinusPrimedDartImage_boundary hτ hfin j (!s), Bool.not_not, hbdy]
  have hnotP : a ∉ Set.range IP := by
    rintro ⟨p, hp'⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hp'
    have hm : p.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨p.property, ⟨((MH).boundary i).1, (congrArg Prod.fst he).symm⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  have hnotUL : a ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk a = a :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk a = a :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin a = b := by
    dsimp only [a]
    rw [← hrep i true]
    have hact : lPlusPrimedExtendedRotation hτ hqMode hfin (IT (idx i, false)) =
        IT (TR (idx i, false)) := TR.extendDomain_apply_image _ _
    simp only [Bool.not_true]
    rw [hact]
    change IT (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) (idx i, false)) = b
    rw [lMinusPrimedRotation_boundary_corner hτ hfin i]
    exact hrep (i + 1) false
  have hCB : lPlusBetaCornerRotation hτ hqMode b = a := by
    exact lMinusBoundaryCornerPerm.extendDomain_apply_image
      (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (i + 1, false)
  change lPlusHattedExtendedRotation hτ hqMode
    (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
      (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
        (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk a)))) = _
  rw [hPE, hCU, hTE, hCB]

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports each incoming
beta port outside the initial star to every output dart. -/
theorem lPlusGluedCorrectedRotation2_beta_incoming_rotation_iff (i : ℕ)
    (hroot : kmswLimitDartVertex w
      (D (lPlusBetaGluedDart hτ hqMode (i, true))).val ≠ boundaryVertex w h k)
    (e : Q) :
    C (lPlusBetaGluedDart hτ hqMode (i, true)) = e ↔
      (S).rotation (D (lPlusBetaGluedDart hτ hqMode (i, true))).val (D e).val := by
  let d := lPlusBetaGluedDart hτ hqMode (i, true)
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    let p : LPlusPrefixDart W h k :=
      ⟨(ULedges[j.1.val], j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩
    let a : LPlusHattedDart MH :=
      ⟨(((MH).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
    have he : p.val = J a := congrArg (fun q => (D q).val) hj
    have hv := congrArg (kmswLimitDartVertex w) he
    exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk p a.val hv)
  have hrot : (S).rotation (D d).val (D (R d)).val := by
    rw [lPlusGluedCorrectedRotation_beta_incoming]
    unfold lPlusBetaGluedDart
    rw [
      lPlusHattedExtendedRotation_apply_hatted]
    exact lPlus_beta_incoming_side_rotation hτ hp P hqMode Tpath hfin hleft hk i hroot
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

include hfin in
/-- Helper toward Lemma 5.5: a beta port has the primed representative
with reversed endpoint bit, in the three-block quotient. -/
theorem lPlusBetaGluedDart_eq_primed (i : ℕ) (b : Bool) :
    lPlusBetaGluedDart hτ hqMode (i, b) =
      IT (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, !b) := by
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  change (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, b) =
    lMinusPrimedDartImage hτ
      (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, !b)
  rw [lMinusPrimedDartImage_boundary hτ hfin i (!b), Bool.not_not]
  congr 2
  change kmswLeftBoundaryEdge
    (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
  rw [boundaryGluing_decoded_stream W h k hτ]

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the outgoing beta port returns to the whole
left side at its primed successor, with the prefix excluded by its vertex. -/
theorem lPlus_beta_outgoing_side_rotation (i : ℕ)
    (hroot : kmswLimitDartVertex w
      (D (lPlusBetaGluedDart hτ hqMode (i + 1, false))).val ≠ boundaryVertex w h k) :
    let p := (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin (i + 1), true)
    (S).rotation (D (lPlusBetaGluedDart hτ hqMode (i + 1, false))).val
      (lMinusPrimedDartImage hτ (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)) := by
  dsimp only
  let b := lPlusBetaGluedDart hτ hqMode (i + 1, false)
  let a : LPlusHattedDart MH :=
    ⟨(((MH).boundary (i + 1)).1, false), lMinus_hatted_boundary_mem _ qL (i + 1)⟩
  let p := (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin (i + 1), true)
  let σ := kmswInfRot w (H.1 0)
  have hbdy (j : ℕ) : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  obtain ⟨n, hn, hna, hgapH⟩ := lMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  dsimp only [p] at hte htgap
  rw [lMinusPrimedDartImage_boundary hτ hfin (i + 1) true, ← hbdy (i + 1)] at hte htgap
  have hnP : (σ : _ → _)^[n] (J a) ∈ Set.range (lMinusPrimedDartImage hτ) := by
    change (σ : _ → _)^[n]
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false) ∈ _
    change (σ : _ → _)^[n]
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false) = _ at hna
    rw [hna]
    refine ⟨(primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin i false, ← hbdy i]
    rfl
  have htn : t ≤ n := by
    by_contra hh
    exact htgap n hn (by omega) hnP
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hm : (σ : _ → _)^[j] (J a) ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hm
  rcases c with p | (p | d)
  · have hv : kmswLimitDartVertex w p.val = kmswLimitDartVertex w (J a) := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        (J a) ((σ : _ → _)^[j] (J a))).mp
          ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hc).trans he.symm
    exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk p a.val hv)
  · exact htgap j hj hjt ⟨p, hc⟩
  · exact hgapH j hj (lt_of_lt_of_le hjt htn) ⟨d, hc⟩

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the primed successor of an outgoing beta
port can lie in the hatted block only at the incoming port of that vertex. -/
theorem lPlusPrimedExtendedRotation_beta_outgoing_mem_hatted_iff (i : ℕ) :
    let b := lPlusBetaGluedDart hτ hqMode (i + 1, false)
    let y := lPlusPrimedExtendedRotation hτ hqMode hfin b
    y ∈ Set.range IH ↔ y = lPlusBetaGluedDart hτ hqMode (i, true) := by
  dsimp only
  let b := lPlusBetaGluedDart hτ hqMode (i + 1, false)
  let y := lPlusPrimedExtendedRotation hτ hqMode hfin b
  let p := (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin (i + 1), true)
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let σ := kmswInfRot w (H.1 0)
  have hby : y = IT (TR p) := by
    dsimp only [y, b]
    rw [lPlusBetaGluedDart_eq_primed hτ hqMode hfin]
    exact TR.extendDomain_apply_image _ p
  have hbdy (j : ℕ) : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  obtain ⟨n, hn, hna, hgapH⟩ := lMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  obtain ⟨t, ht, hte, htgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  dsimp only [p] at hte htgap
  rw [lMinusPrimedDartImage_boundary hτ hfin (i + 1) true, ← hbdy (i + 1)] at hte htgap
  have hnP : (σ : _ → _)^[n] (D b).val ∈ Set.range (lMinusPrimedDartImage hτ) := by
    change (σ : _ → _)^[n]
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false) ∈ _
    change (σ : _ → _)^[n]
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false) = _ at hna
    rw [hna]
    refine ⟨(primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin i false, ← hbdy i]
    rfl
  have htn : t ≤ n := by
    by_contra hh
    exact htgap n hn (by omega) hnP
  constructor
  · rintro ⟨d, hd⟩
    have hyH : (D y).val ∈ Set.range J := ⟨d, congrArg (fun q => (D q).val) hd⟩
    have hty : (σ : _ → _)^[t] (D b).val = (D y).val := by
      rw [hby]
      exact hte
    have hnt : n ≤ t := by
      by_contra hh
      apply hgapH t ht (by omega)
      exact hty.symm ▸ hyH
    have htnEq := Nat.le_antisymm htn hnt
    apply (D).injective
    apply Subtype.ext
    exact hty.symm.trans (htnEq ▸ hna)
  · intro he
    rw [he]
    exact ⟨⟨(((MH).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩, rfl⟩

include hk in
/-- Helper toward Lemma 5.5: no hatted dart belongs to the stopped
prefix block, retaining edge identity independently of its vertex. -/
theorem lPlusHattedGluedDart_not_prefix (a : LPlusHattedDart MH) :
    IH a ∉ Set.range IP := by
  rintro ⟨p, hp'⟩
  have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hp'
  have hm : p.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
      Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
    ⟨p.property, ⟨a.val.1, (congrArg Prod.fst he).symm⟩⟩
  exact (Set.ext_iff.mp
    (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the beta exchange and hatted exterior
corner cancel at an outgoing port's primed successor. -/
theorem lPlusGluedCorrectedRotation_beta_outgoing (i : ℕ) :
    lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
      (lPlusBetaGluedDart hτ hqMode (i + 1, false)) =
    lPlusPrimedExtendedRotation hτ hqMode hfin
      (lPlusBetaGluedDart hτ hqMode (i + 1, false)) := by
  let b := lPlusBetaGluedDart hτ hqMode (i + 1, false)
  let a := lPlusBetaGluedDart hτ hqMode (i, true)
  let y := lPlusPrimedExtendedRotation hτ hqMode hfin b
  have hnotP : b ∉ Set.range IP := lPlusHattedGluedDart_not_prefix hτ hqMode hk _
  have hnotUL : b ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hPE : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk b = b :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hCU : lPlusUpperLeftCornerRotation hτ hqMode hfin hk b = b :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL
  change lPlusHattedExtendedRotation hτ hqMode
    (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
      (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
        (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk b)))) = y
  rw [hPE, hCU]
  change lPlusHattedExtendedRotation hτ hqMode (lPlusBetaCornerRotation hτ hqMode y) = y
  by_cases hy : y ∈ Set.range IH
  · have he : y = a := (lPlusPrimedExtendedRotation_beta_outgoing_mem_hatted_iff
      hτ hp P hqMode Tpath hfin hleft hk i).mp hy
    rw [he]
    have hCB : lPlusBetaCornerRotation hτ hqMode a = b :=
      lMinusBoundaryCornerPerm.extendDomain_apply_image
        (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (i, true)
    rw [hCB]
    dsimp only [b, a, lPlusBetaGluedDart]
    rw [lPlusHattedExtendedRotation_apply_hatted]
    exact congrArg IH (lMinusHattedRotation_boundary_corner _ qL i)
  · have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
      rintro ⟨j, hj⟩
      exact hy ⟨_, hj⟩
    have hCB : lPlusBetaCornerRotation hτ hqMode y = y :=
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB
    rw [hCB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hy

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: corrected rotation 2 transports outgoing
beta ports outside the initial star, for every output dart. -/
theorem lPlusGluedCorrectedRotation2_beta_outgoing_rotation_iff (i : ℕ)
    (hroot : kmswLimitDartVertex w
      (D (lPlusBetaGluedDart hτ hqMode (i + 1, false))).val ≠ boundaryVertex w h k)
    (e : Q) :
    C (lPlusBetaGluedDart hτ hqMode (i + 1, false)) = e ↔
      (S).rotation (D (lPlusBetaGluedDart hτ hqMode (i + 1, false))).val (D e).val := by
  let d := lPlusBetaGluedDart hτ hqMode (i + 1, false)
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hnotP : d ∉ Set.range IP := lPlusHattedGluedDart_not_prefix hτ hqMode hk _
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hrot : (S).rotation (D d).val (D (R d)).val := by
    rw [lPlusGluedCorrectedRotation_beta_outgoing]
    have hact : lPlusPrimedExtendedRotation hτ hqMode hfin d =
        IT (kmswInfRot (primedCode (primedSimInput U) hτ)
          (primedCode_finiteIncidence U hτ hfin)
          (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin (i + 1), true)) := by
      dsimp only [d]
      rw [lPlusBetaGluedDart_eq_primed hτ hqMode hfin]
      exact Equiv.Perm.extendDomain_apply_image _ _ _
    rw [hact]
    exact lPlus_beta_outgoing_side_rotation hτ hp P hqMode Tpath hfin hleft hk i hroot
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
/-- Helper toward Lemma 5.5: corrected rotation 2 transports every
hatted representative, including arbitrary non-port darts at beta vertices. -/
theorem lPlusGluedCorrectedRotation2_hatted_rotation_iff
    (a : LPlusHattedDart MH) (e : Q) :
    C (IH a) = e ↔ (S).rotation (D (IH a)).val (D e).val := by
  by_cases hroot : kmswLimitDartVertex w (J a) = boundaryVertex w h k
  · exact lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk (IH a) hroot e
  by_cases hport : ∃ i : ℕ, ∃ b : Bool,
      J a = (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, b)
  · obtain ⟨i, b, hab⟩ := hport
    have heq : IH a = lPlusBetaGluedDart hτ hqMode (i, b) := by
      apply (D).injective
      exact Subtype.ext hab
    have hroot' : kmswLimitDartVertex w
        (D (lPlusBetaGluedDart hτ hqMode (i, b))).val ≠ boundaryVertex w h k := by
      rw [← heq]
      exact hroot
    rw [heq]
    cases b with
    | true =>
      exact lPlusGluedCorrectedRotation2_beta_incoming_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk i hroot' e
    | false =>
      cases i with
      | zero =>
        exact (hroot' (lPlusBetaGluedDart_initial_vertex
          hτ hqMode hfin hp P Tpath hleft hk)).elim
      | succ i =>
        exact lPlusGluedCorrectedRotation2_beta_outgoing_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk i hroot' e
  · apply lPlusGluedCorrectedRotation2_hatted_nonport_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk a hroot
    intro i b he
    exact hport ⟨i, b, he⟩

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: on the entire hatted block, corrected
rotation 2 equals the least positive return to the actual left side. -/
theorem lPlusGluedCorrectedRotation2_hatted_eq_codeReturn (a : LPlusHattedDart MH) :
    C (IH a) = lPlusGluedCodeReturn (H := H) hτ hqMode (IH a) := by
  apply (lPlusGluedCorrectedRotation2_hatted_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk a _).mpr
  exact (lPlusGluedCodeReturn_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk _ _).mp rfl

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the fixed-ID cell equivalence preserves
rotation from every hatted dart to every retained dart. -/
theorem lPlusActualCodeBlockCellEquiv_rotation_iff_hatted
    (a : LPlusHattedDart MH) (e : Q) :
    geometricSideRelation S .rotation (.inr (D (IH a))) (.inr (D e)) ↔
      geometricSideRelation B .rotation (E (.inr (D (IH a)))) (E (.inr (D e))) := by
  change (S).rotation _ _ ↔ (B).rotation _ _
  exact (lPlusGluedCorrectedRotation2_hatted_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk a e).symm.trans
      (lPlusCodeBlockSide_rotation_glued_iff
        hτ hp P hqMode Tpath hfin hleft hk (IH a) e).symm

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at a noninitial beta vertex, an arbitrary
non-port primed dart has its own block successor in the whole left side. -/
theorem lPlus_primed_nonport_beta_side_rotation (p : ℕ × Bool) (i : ℕ)
    (hvertex : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true))
    (hroot : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) ≠ boundaryVertex w h k)
    (hport : ∀ j : ℕ, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary j).1, b)) :
    (S).rotation (lMinusPrimedDartImage hτ p)
      (lMinusPrimedDartImage hτ (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)) := by
  let σ := kmswInfRot w (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  let u : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
  let v : ℕ × Bool := (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
  let a : LPlusHattedDart MH :=
    ⟨(((MH).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩
  obtain ⟨n, m, hn, hm, hnu, hmv, hgapP, hgapH, hperiod, _⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  change (σ : _ → _)^[n] u = v at hnu
  change (σ : _ → _)^[m] v = u at hmv
  change (σ : _ → _)^[n + m] u = u at hperiod
  obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) u x).mpr hvertex.symm
  have hr' : (σ : _ → _)^[r % (n + m)] u = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
      (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
  let s := r % (n + m)
  change (σ : _ → _)^[s] u = x at hr'
  have hslt : s < n + m := Nat.mod_lt _ (by omega)
  have hsge : n < s := by
    by_cases hs0 : s = 0
    · exact (hport i true (by simpa only [hs0, Function.iterate_zero_apply] using hr'.symm)).elim
    by_cases hsn : s < n
    · exact (hgapP s (by omega) hsn (hr'.symm ▸ Set.mem_range_self p)).elim
    by_cases hsn : s = n
    · exact (hport (i + 1) false (hr'.symm.trans (hsn ▸ hnu))).elim
    omega
  have hxv : (σ : _ → _)^[s - n] v = x := by
    rw [← hnu, ← Function.iterate_add_apply, Nat.sub_add_cancel hsge.le]
    exact hr'
  have hxu : (σ : _ → _)^[n + m - s] x = u := by
    rw [← hr', ← Function.iterate_add_apply, Nat.sub_add_cancel hslt.le]
    exact hperiod
  have huP : u ∈ Set.range (lMinusPrimedDartImage hτ) := by
    refine ⟨(primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin i false]
    change (boundaryGluingHatEdgeMap W h k hτ (kmswLeftBoundaryEdge (hatCodes U hτ) i), true) = _
    have hb : ((MH).boundary i).1 = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    rw [← hb]
  obtain ⟨t, ht, hte, htgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  have htle : t ≤ n + m - s := by
    by_contra hh
    exact htgap (n + m - s) (by omega) (by omega) (hxu.symm ▸ huP)
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  have hmem : (σ : _ → _)^[j] x ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨c, hc⟩ := hmem
  rcases c with q | (q | d)
  · have hv : kmswLimitDartVertex w q.val = kmswLimitDartVertex w x := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hc).trans he.symm
    have hva : kmswLimitDartVertex w q.val = kmswLimitDartVertex w (J a) := hv.trans hvertex
    exact hroot (hv ▸ lPlus_prefix_hatted_shared_endpoint_initial
      (H := H) hτ hqMode hfin hk q a.val hva)
  · exact htgap j hj hjt ⟨q, hc⟩
  · apply hgapH (s - n + j) (by omega) (by omega)
    refine ⟨d, ?_⟩
    change J d = (σ : _ → _)^[s - n + j] v
    rw [Nat.add_comm (s - n) j, Function.iterate_add_apply, hxv]
    exact hc


















































































































end DirectedDistances.PaperProofs.Section5

/- Validation: development checks included repaired failures (exit 1).
All seventeen declarations reported exactly
No separate checker, dependency build, cache retrieval, commit, or push ran. -/
