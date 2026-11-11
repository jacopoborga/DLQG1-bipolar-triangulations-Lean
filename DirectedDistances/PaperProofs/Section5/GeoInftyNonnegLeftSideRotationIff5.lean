/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff4

/-! Helper toward Lemma 5.5: return arcs at the finite upper-left attachment. -/

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

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))

/-- Helper toward Lemma 5.5: every finite attachment port has its actual
primed representative, with the same geometric dart and quotient class. -/
theorem lPlusUpperLeftGluedDart_primed_representative
    (i : Fin (ULedges).length) (b : Bool) :
    ∃ p : ℕ × Bool,
      lMinusPrimedDartImage hτ p = (ULedges[i.val], b) ∧
      lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b) =
        lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p := by
  have hu : ULedges[i.val] ∈ boundaryGluingUpperLeftEdges W h k :=
    List.mem_reverse.mp (List.getElem_mem i.isLt)
  obtain ⟨e, he⟩ := boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin hu
  let p := (e, b ^^ primedLimitSideFlip U hτ e)
  have hp' : lMinusPrimedDartImage hτ p = (ULedges[i.val], b) := by
    apply Prod.ext he
    change ((b ^^ primedLimitSideFlip U hτ e) ^^ primedLimitSideFlip U hτ e) = b
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  refine ⟨p, hp', ?_⟩
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  exact hp'.symm

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the extended prefix rotation takes the west
port of each interior attachment corner to the next east port. -/
theorem lPlusPrefixExtendedRotation_upperLeft_west (hkpos : 0 < k)
    (i : Fin (ULedges).length) (hi : i.val + 1 < (ULedges).length) :
    lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)) =
      lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨i.val + 1, hi⟩, true) := by
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[i.val], false), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩
  let b : LPlusPrefixDart W h k :=
    ⟨(ULedges[i.val + 1], true),
      lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨i.val + 1, hi⟩⟩
  have hrot : lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
      (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
      (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk a = b := by
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos]
    have ha : ULedges[i.val]? = some (ULedges[i.val]) :=
      List.getElem?_eq_getElem i.isLt
    have hb : ULedges[i.val + 1]? = some (ULedges[i.val + 1]) :=
      List.getElem?_eq_getElem hi
    have ha0 := (congrArg (fun es : List ℕ => es[i.val]?)
      (lPlus_attachment_upperLeft_eq_previous (W := W) (h := h) hkpos)).symm.trans ha
    have hb0 := (congrArg (fun es : List ℕ => es[i.val + 1]?)
      (lPlus_attachment_upperLeft_eq_previous (W := W) (h := h) hkpos)).symm.trans hb
    obtain ⟨ha', hb', hcorner⟩ := lPlusStageRotation_upperLeft_corner w
      (boundaryHitTime w h k - 1) i.val _ _ ha0 hb0
    have hstage : lPlusPrefixDartStage hkpos a = (⟨ULedges[i.val], ha'⟩, false) := rfl
    apply Subtype.ext
    rw [hstage, hcorner]
    rfl
  have he := (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk).extendDomain_apply_image
        (Equiv.ofInjective _ (lPlusPrefixGluedDart_injective
          (hτ := hτ) (hqMode := hqMode))) a
  change lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
      (lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)) =
    lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode) _ at he
  rw [hrot] at he
  exact he

include H in
/-- Helper toward Lemma 5.5: the extended primed rotation takes the east
port of an interior attachment corner to the preceding west port. -/
theorem lPlusPrimedExtendedRotation_upperLeft_east
    (i : Fin (ULedges).length) (hi : i.val + 1 < (ULedges).length) :
    lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨i.val + 1, hi⟩, true)) =
      lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false) := by
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  obtain ⟨p, hp', hclass⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk ⟨i.val + 1, hi⟩ true
  obtain ⟨q, hq', hclass'⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk i false
  have hret := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  rw [hp'] at hret
  have hgap := lPlus_primed_upperLeft_boundary_gap (H := H) hτ hfin i.val _ _
    (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  have he : lMinusPrimedDartImage hτ (TR p) = (ULedges[i.val], false) := by
    obtain ⟨t, ht, hte, htg⟩ := hret
    obtain ⟨m, hm, hme, hmg⟩ := hgap
    have htm : t = m := by
      apply Nat.le_antisymm
      · by_contra hh
        exact htg m hm (by omega) ⟨q, hq'.trans hme.symm⟩
      · by_contra hh
        exact hmg t ht (by omega) ⟨TR p, hte.symm⟩
    exact hte.symm.trans (htm ▸ hme)
  rw [hclass]
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin (IT p) = IT (TR p) :=
    TR.extendDomain_apply_image _ p
  rw [hTE]
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  exact he

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at every interior west attachment port, the
corrected permutation is the first ambient return to the complete glued
dart set. The finite corner correction cancels the prefix exterior corner. -/
theorem lPlusGluedCorrectedRotation_upperLeft_interior_west_firstReturn
    (hkpos : 0 < k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
    let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
    let F := lPlusBlockDartImage (M := MH) hτ
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val = (D (C d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  dsimp only
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  obtain ⟨p, hp', n, hn, hret, hgap⟩ := lPlus_upperLeft_interior_west_firstReturn
    (H := H) hτ hqMode hfin hkpos i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  have hclass : UL (i, false) = IT p := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
    exact hp'.symm
  have hPE : PE (UL (i, false)) = UL (⟨i.val + 1, hi⟩, true) :=
    lPlusPrefixExtendedRotation_upperLeft_west hτ hp P hqMode Tpath hfin hleft hk
      hkpos i hi
  have hcorner : lPlusUpperLeftCornerPerm (ULedges).length
      (⟨i.val + 1, hi⟩, true) = (i, false) := by
    change lPlusUpperLeftCorner (ULedges).length (⟨i.val + 1, hi⟩, true) = (i, false)
    simp only [lPlusUpperLeftCorner, Nat.zero_lt_succ, ↓reduceIte, ↓reduceDIte,
      Nat.add_sub_cancel]
  have hCU : CU (UL (⟨i.val + 1, hi⟩, true)) = UL (i, false) := by
    have he := (lPlusUpperLeftCornerPerm (ULedges).length).extendDomain_apply_image
      (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
      (⟨i.val + 1, hi⟩, true)
    change CU (UL (⟨i.val + 1, hi⟩, true)) =
      UL (lPlusUpperLeftCornerPerm (ULedges).length (⟨i.val + 1, hi⟩, true)) at he
    exact he.trans (congrArg UL hcorner)
  have hTE : TE (IT p) = IT (TR p) := TR.extendDomain_apply_image _ p
  have hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ (TR p)) =
      kmswLimitDartVertex w (ULedges[i.val], false) := by
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hret⟩).symm
  have hnot : IT (TR p) ∉ Set.range IH := by
    rintro ⟨a, ha⟩
    have he := congrArg (fun q : Q => (D q).val) ha
    change (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2) =
      lMinusPrimedDartImage hτ (TR p) at he
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) a.val
      (hv.symm.trans (congrArg (kmswLimitDartVertex w) he.symm))
  have hCB : CB (IT (TR p)) = IT (TR p) := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨a, ha⟩
    apply hnot
    exact ⟨_, ha⟩
  have hHE : HE (IT (TR p)) = IT (TR p) :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnot
  have hC : lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
      (UL (i, false)) = IT (TR p) := by
    change HE (CB (TE (CU (PE (UL (i, false)))))) = _
    rw [hPE, hCU, hclass, hTE, hCB, hHE]
  refine ⟨n, hn, ?_, hgap⟩
  rw [hC]
  exact hret

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at every interior east attachment port, the
corrected permutation is the first ambient return to the complete glued
dart set. The complementary primed arc controls both possible prefix returns. -/
theorem lPlusGluedCorrectedRotation_upperLeft_interior_east_firstReturn
    (hkpos : 0 < k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨i.val + 1, hi⟩, true)
    let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
    let F := lPlusBlockDartImage (M := MH) hτ
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val = (D (C d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  dsimp only
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  obtain ⟨q, hq', t, ht, hret, hgap⟩ := lPlus_upperLeft_interior_east_firstReturn
    (H := H) hτ hqMode hfin hkpos i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  let r := PR q
  have hr : r = lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos q)) :=
    lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos q
  have hret' : (kmswInfRot w (H.1 0) : _ → _)^[t]
      (ULedges[i.val + 1], true) = r.val := by
    rw [hr]
    exact hret
  have hclassq : UL (⟨i.val + 1, hi⟩, true) = IP q := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
    exact hq'.symm
  have hPE : PE (UL (⟨i.val + 1, hi⟩, true)) = IP r := by
    rw [hclassq]
    exact PR.extendDomain_apply_image _ q
  obtain ⟨m, hm, hmb, hgapT⟩ := lPlus_primed_upperLeft_boundary_gap
    (H := H) hτ hfin i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  have hbound : t ≤ m := by
    by_contra hh
    apply hgap m hm (by omega)
    refine ⟨.inl ⟨(ULedges[i.val], false),
      lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩, ?_⟩
    exact hmb.symm
  have hv : kmswLimitDartVertex w r.val =
      kmswLimitDartVertex w (ULedges[i.val], false) := by
    have hv1 := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨t, by simpa only [Equiv.Perm.coe_pow] using hret'⟩
    have hv2 := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨m, by simpa only [Equiv.Perm.coe_pow] using hmb⟩
    exact hv1.symm.trans hv2
  have hnotH : IP r ∉ Set.range IH := by
    rintro ⟨a, ha⟩
    have he := congrArg (fun d : Q => (D d).val) ha
    change (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2) = r.val at he
    exact lPlus_upperLeft_west_not_hatted hτ i.val _
      (List.getElem?_eq_getElem i.isLt) a.val
      (hv.symm.trans (congrArg (kmswLimitDartVertex w) he.symm))
  have hCB : CB (IP r) = IP r := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨a, ha⟩
    exact hnotH ⟨_, ha⟩
  have hHE : HE (IP r) = IP r :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  have hCT : TE (CU (IP r)) = IP r := by
    by_cases htm : t < m
    · have hnotT : IP r ∉ Set.range IT := by
        rintro ⟨p, hp'⟩
        have he := congrArg (fun d : Q => (D d).val) hp'
        change lMinusPrimedDartImage hτ p = r.val at he
        exact hgapT t ht htm ⟨p, he.trans hret'.symm⟩
      have hCU : CU (IP r) = IP r := by
        apply Equiv.Perm.extendDomain_apply_not_subtype
        rintro ⟨⟨j, b⟩, he⟩
        obtain ⟨p, _, hp'⟩ := lPlusUpperLeftGluedDart_primed_representative
          hτ hqMode hfin hk j b
        exact hnotT ⟨p, hp'.symm.trans he⟩
      rw [hCU]
      exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT
    · have htm' : t = m := by omega
      have hrv : r.val = (ULedges[i.val], false) := hret'.symm.trans (htm' ▸ hmb)
      have hclassr : IP r = UL (i, false) := by
        apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
        exact hrv
      have hcorner : lPlusUpperLeftCornerPerm (ULedges).length (i, false) =
          (⟨i.val + 1, hi⟩, true) := by
        change lPlusUpperLeftCorner (ULedges).length (i, false) = _
        simp only [lPlusUpperLeftCorner, Bool.false_eq_true, ↓reduceIte,
          ↓reduceDIte, hi]
      have hCU : CU (UL (i, false)) = UL (⟨i.val + 1, hi⟩, true) := by
        have he := (lPlusUpperLeftCornerPerm (ULedges).length).extendDomain_apply_image
          (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
          (i, false)
        change CU (UL (i, false)) =
          UL (lPlusUpperLeftCornerPerm (ULedges).length (i, false)) at he
        exact he.trans (congrArg UL hcorner)
      rw [hclassr, hCU]
      exact lPlusPrimedExtendedRotation_upperLeft_east (H := H)
        hτ hqMode hfin hk i hi
  have hC : lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
      (UL (⟨i.val + 1, hi⟩, true)) = IP r := by
    change HE (CB (TE (CU (PE (UL (⟨i.val + 1, hi⟩, true)))))) = _
    rw [hPE, hCT, hCB, hHE]
  refine ⟨t, ht, ?_, hgap⟩
  rw [hC]
  exact hret'

/-- Helper toward Lemma 5.5: after left/down, the first positive boundary
hit is exactly stage two. -/
theorem lPlus_hit_one_of_left_down (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    boundaryHitTime w h 1 = 2 := by
  have hr : R w 2 = -1 := by
    simp [R, Finset.sum_range_succ, hc₀, hc₁, lazyTwoDimensionalStep]
  have hf : Nat.find (h.rightHit 1 (by omega)) = 2 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ hr
    · have hs := Nat.find_spec (h.rightHit 1 (by omega))
      by_contra hn
      have he : Nat.find (h.rightHit 1 (by omega)) = 0 ∨
          Nat.find (h.rightHit 1 (by omega)) = 1 := by omega
      rcases he with he | he <;> rw [he] at hs
      · change (0 : ℤ) = -1 at hs
        omega
      · simp [R, hc₀, lazyTwoDimensionalStep] at hs
  simpa [boundaryHitTime] using hf

include H in
/-- Helper toward Lemma 5.5: the triangle created by the third step of
left/down/left fixes the ambient successor at its terminal attachment port. -/
theorem lPlus_terminal_ambient_of_left_down_left
    (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) (hc₂ : w 2 = 0) :
    kmswInfRot w (H.1 0) (1, false) = (4, false) := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle w (H.1 0) ⟨2, Or.inl hc₂⟩
  have ht : stageTriangleDartTriple w ⟨2, Or.inl hc₂⟩ =
      ((1, false), (3, false), (4, true)) := by
    simp [stageTriangleDartTriple, kmswStage, hc₀, hc₁, hc₂, kmswStep,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  rw [ht] at hc
  have hf : kmswInfFaceSucc w (H.1 0) (4, true) = (1, false) := hc.2.2.1
  change (kmswInfRot w (H.1 0)).symm (4, false) = (1, false) at hf
  exact (congrArg (kmswInfRot w (H.1 0)) hf).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- Helper toward Lemma 5.5: at the finite terminal port after an initial
left step, the prefix rotation returns to its missing lower-left edge. -/
theorem lPlus_terminal_stage_of_first_left (hc₀ : w 0 = 0) :
    ∃ ha : 1 < (kmswStage w 1).nextEdge,
      ∃ hb : 2 < (kmswStage w 1).nextEdge,
        stageRot w 1 (⟨1, ha⟩, false) = (⟨2, hb⟩, false) := by
  have hsize : (kmswStage w 1).nextEdge = 3 := by
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  refine ⟨by omega, by omega, ?_⟩
  have hword : stageOuterWordVal w 1 = [(1, false), (0, true), (2, true)] := by
    rw [stageOuterWordVal_eq_runs]
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  obtain ⟨d, e, hd, he, hde⟩ := outer_faceSucc_exists w 1
    (stageOuterWord_faceSucc w 1) 2 (by rw [hword]; decide)
  simp only [hword] at hd he
  norm_num at hd he
  have hd' : d = (⟨2, by omega⟩, true) :=
    Prod.ext (Fin.ext hd.1.symm) hd.2
  have he' : e = (⟨1, by omega⟩, false) :=
    Prod.ext (Fin.ext he.1.symm) he.2
  rw [hd', he'] at hde
  change (stageRot w 1).symm (⟨2, by omega⟩, false) = (⟨1, by omega⟩, false) at hde
  have heq := congrArg (stageRot w 1) hde
  rw [Equiv.apply_symm_apply] at heq
  exact heq.symm

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: after left/down, the corrected candidate sends
the terminal upper-left west port to the old missing lower-left dart. -/
theorem lPlus_terminal_corrected_of_left_down (hk₁ : k = 1)
    (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    ∃ d : Q, (D d).val = (1, false) ∧
      (D (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d)).val =
        (2, false) := by
  subst k
  let D' := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  have ht := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
  have hUL : (List.reverse (List.dropLast (State.UL
      (kmswStage w (boundaryHitTime w h 1))))) = [1] := by
    rw [ht]
    simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hmem (e : ℕ) (he : e < 3) : e ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h) (by omega : 0 < (1 : ℤ))]
    change e < (kmswStage w (boundaryHitTime w h 1 - 1)).nextEdge
    rw [hprev]
    simpa [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge] using he
  let p : LPlusPrefixDart W h 1 := ⟨(1, false), hmem 1 (by omega)⟩
  let r : LPlusPrefixDart W h 1 := ⟨(2, false), hmem 2 (by omega)⟩
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := 1) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  obtain ⟨ha, hb, hcorner⟩ := lPlus_terminal_stage_of_first_left hc₀
  have hPR : PR p = r := by
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk (by omega : 0 < (1 : ℤ))]
    apply Subtype.ext
    have hlocal : ∀ (n : ℕ) (hn : n = 1) (he : 1 < (kmswStage w n).nextEdge),
        ((stageRot w n (⟨1, he⟩, false)).1.val,
          (stageRot w n (⟨1, he⟩, false)).2) = (2, false) := by
      intro n hn he
      subst n
      exact congrArg (fun d : StageDart (kmswStage w 1).nextEdge => (d.1.val, d.2)) hcorner
    exact hlocal _ hprev _
  have hPE : PE (IP p) = IP r :=
    (PR.extendDomain_apply_image _ p).trans (congrArg IP hPR)
  have hnotT : IP r ∉ Set.range IT := by
    rintro ⟨a, ha'⟩
    have he := congrArg (fun d : LPlusGluedDart longest hqMode hτ => (D' d).val.1) ha'
    have hm : 2 ∈ boundaryGluingPrefixMinusEdges W h 1 ∩
        boundaryGluingPrimedEdges W h 1 hτ := ⟨r.property, ⟨a.1, he⟩⟩
    rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h 1 hτ hfin hk] at hm
    have hm' : 2 ∈ List.reverse (List.dropLast (State.UL
        (kmswStage w (boundaryHitTime w h 1)))) := List.mem_reverse.mpr hm
    rw [hUL] at hm'
    simp only [List.mem_singleton] at hm'
    omega
  have hCU : CU (IP r) = IP r := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨⟨j, b⟩, he⟩
    obtain ⟨a, _, ha'⟩ := lPlusUpperLeftGluedDart_primed_representative
      hτ hqMode hfin hk j b
    exact hnotT ⟨a, ha'.symm.trans he⟩
  have hTE : TE (IP r) = IP r :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT
  have hv : kmswLimitDartVertex w (2, false) = kmswLimitDartVertex w (1, false) := by
    change edgeWest w 2 = edgeWest w 1
    rw [← (edge_endpoints_eq w hb).1, ← (edge_endpoints_eq w ha).1]
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  have hnotH : IP r ∉ Set.range IH := by
    rintro ⟨a, ha'⟩
    have he := congrArg (fun d : LPlusGluedDart longest hqMode hτ => (D' d).val) ha'
    change (boundaryGluingHatEdgeMap W h 1 hτ a.val.1, a.val.2) = (2, false) at he
    exact lPlus_upperLeft_west_not_hatted hτ 0 1
      (by rw [hUL]; rfl) a.val
      (hv.symm.trans (congrArg (kmswLimitDartVertex w) he.symm))
  have hCB : CB (IP r) = IP r := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨a, ha'⟩
    exact hnotH ⟨_, ha'⟩
  have hHE : HE (IP r) = IP r :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  refine ⟨IP p, rfl, ?_⟩
  have hC : lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk (IP p) = IP r := by
    change HE (CB (TE (CU (PE (IP p))))) = _
    rw [hPE, hCU, hTE, hCB, hHE]
  rw [hC]
  rfl

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal port in left/down/left obstructs
the corrected candidate. The ambient next dart is retained in the primed
block, before the candidate's proposed lower-left return. -/
theorem lPlusGluedCorrectedRotation_terminal_obstruction
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) (hc₂ : w 2 = 0) :
    ∃ d : Q, (D d).val = (1, false) ∧
      d ∈ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) ∧
      ¬ (∃ n : ℕ, 0 < n ∧
        (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
          (D (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d)).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉
            Set.range (lPlusBlockDartImage (M := MH) hτ)) := by
  obtain ⟨d, hd, hCd⟩ := lPlus_terminal_corrected_of_left_down
    hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁
  subst k
  let M := lPlusHattedSide (W := W) (h := h) (k := 1) longest hqMode
  let F := lPlusBlockDartImage (M := M) hτ
  let D' := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  have ht := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hUL : (kmswStage w (boundaryHitTime w h 1)).UL.dropLast.reverse = [1] := by
    rw [ht]
    simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hσ := lPlus_terminal_ambient_of_left_down_left (H := H) hc₀ hc₁ hc₂
  have hv : kmswLimitDartVertex w (4, false) = kmswLimitDartVertex w (1, false) := by
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨1, by simpa only [pow_one] using hσ⟩).symm
  have hport : d ∈ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    have hi : 0 < (kmswStage w (boundaryHitTime w h 1)).UL.dropLast.reverse.length := by
      rw [hUL]
      decide
    let i : Fin (kmswStage w (boundaryHitTime w h 1)).UL.dropLast.reverse.length := ⟨0, hi⟩
    refine ⟨(i, false), ?_⟩
    apply D'.injective
    apply Subtype.ext
    rw [hd]
    change ((kmswStage w (boundaryHitTime w h 1)).UL.dropLast.reverse[0], false) = (1, false)
    have he := congrArg (fun es : List ℕ => es[0]?) hUL
    rw [List.getElem?_eq_getElem hi] at he
    exact congrArg (fun e : ℕ => (e, false)) (Option.some.inj he)
  have hfuture : 4 ∈ Set.range (boundaryGluingEdgeMap W h 1) := by
    have hc := (Set.ext_iff.mp (boundaryGluing_prefix_union_futureRange W h 1) 4).mpr
      (Set.mem_univ 4)
    rcases hc with hc | hc
    · change 4 < (kmswStage w (boundaryHitTime w h 1)).nextEdge at hc
      rw [ht] at hc
      simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswInit, State.addEdge] at hc
    · exact hc
  have hprimed : 4 ∈ boundaryGluingPrimedEdges W h 1 hτ := by
    have hc := (Set.ext_iff.mp
      (boundaryGluing_hatRange_union_primedEdges W h 1 hτ hfin) 4).mpr hfuture
    rcases hc with ⟨e, he⟩ | he
    · exact False.elim (lPlus_upperLeft_west_not_hatted hτ 0 1
        (by rw [hUL]; rfl) (e, false)
        (by rw [he]; exact hv.symm))
    · exact he
  have hF : (4, false) ∈ Set.range F := by
    obtain ⟨e, he⟩ := hprimed
    refine ⟨.inr (.inl (e, primedLimitSideFlip
      (boundaryGluingFutureStream W h 1) hτ e)), ?_⟩
    apply Prod.ext he
    exact Bool.xor_self _
  refine ⟨d, hd, hport, ?_⟩
  rintro ⟨n, hn, hret, hgap⟩
  rw [hd, hCd] at hret
  by_cases h1 : n = 1
  · rw [h1, Function.iterate_one, hσ] at hret
    have he := congrArg (fun z : ℕ × Bool => z.1) hret
    omega
  · apply hgap 1 (by omega) (by omega)
    rw [hd, Function.iterate_one, hσ]
    exact hF

include Tpath hfin hleft hk in



theorem lPlusGluedCorrectedRotation_upperLeft_not_firstReturn_of_left_down_left
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) (hc₂ : w 2 = 0) :
    ¬ (∀ (i : Fin (ULedges).length) (b : Bool),
      let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
          (D (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d)).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉
            Set.range (lPlusBlockDartImage (M := MH) hτ)) := by
  intro hall
  obtain ⟨d, _, ⟨⟨i, b⟩, he⟩, hnot⟩ := lPlusGluedCorrectedRotation_terminal_obstruction
    hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁ hc₂
  apply hnot
  rw [← he]
  exact hall i b
























































end DirectedDistances.PaperProofs.Section5
