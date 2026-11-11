/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff2

/-! Helper toward Lemma 5.5: corrections at the two nonnegative left interfaces.
The candidate below uses block rotations and attachment ports only. Its geometric
identification at attachment vertices is a separate obligation. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: exchange the adjacent ports of a finite
attachment chain, fixing the ports at its two endpoints. -/
@[expose] def lPlusUpperLeftCorner (N : ℕ) (d : Fin N × Bool) : Fin N × Bool :=
  if d.2 then
    if hi : 0 < d.1.val then
      (⟨d.1.val - 1, by have := d.1.isLt; omega⟩, false) else d
  else if hi : d.1.val + 1 < N then (⟨d.1.val + 1, hi⟩, true) else d

/-- Helper toward Lemma 5.5: the finite corner exchange is an involution. -/
theorem lPlusUpperLeftCorner_involutive (N : ℕ) :
    Function.Involutive (lPlusUpperLeftCorner N) := by
  rintro ⟨⟨i, hi⟩, b⟩
  cases b with
  | true =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [lPlusUpperLeftCorner, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        Nat.zero_lt_succ, Nat.add_sub_cancel, hi]
  | false =>
    by_cases hn : i + 1 < N
    · simp only [lPlusUpperLeftCorner, ↓reduceIte, ↓reduceDIte, hn, Bool.false_eq_true,
        Nat.zero_lt_succ, Nat.add_sub_cancel]
    · simp only [lPlusUpperLeftCorner, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, hn]

/-- Helper toward Lemma 5.5: the finite interface correction is a permutation. -/
@[expose] def lPlusUpperLeftCornerPerm (N : ℕ) : Equiv.Perm (Fin N × Bool) :=
  ⟨lPlusUpperLeftCorner N, lPlusUpperLeftCorner N,
    lPlusUpperLeftCorner_involutive N, lPlusUpperLeftCorner_involutive N⟩

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
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "B" => (Set.ofPred fun v : ℕ => ∃ e : ℕ,
  e ∈ boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingBetaEdges W h k hτ ∧
  (kmswLimitDartVertex w (e, false) = v ∨ kmswLimitDartVertex w (e, true) = v))
local notation "ULedges" => (List.reverse (List.dropLast (State.UL (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)))))

/-- Helper toward Lemma 5.5: both darts of every indexed beta edge in the
same glued carrier as the three block rotations. -/
@[expose] noncomputable def lPlusBetaGluedDart (d : ℕ × Bool) : Q :=
  lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
    ⟨(((MH).boundary d.1).1, d.2),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ d.1⟩

/-- Helper toward Lemma 5.5: beta ports retain their edge and endpoint identity. -/
theorem lPlusBetaGluedDart_injective :
    Function.Injective (lPlusBetaGluedDart hτ hqMode) := by
  intro a b hab
  have he := lPlusHattedGluedDart_injective (hτ := hτ) (hqMode := hqMode) hab
  exact Prod.ext
    (lMinus_hatted_boundary_edge_injective _
      ⟨boundaryFutureHattedPath k W, hqMode⟩ (congrArg (fun d => d.val.1) he))
    (congrArg (fun d => d.val.2) he)

include hτ hfin hk in
/-- Helper toward Lemma 5.5: each upper-left attachment edge belongs to
the deleted prefix on the complete nonnegative domain. -/
theorem lPlusUpperLeftEdge_mem_prefix (i : Fin (ULedges).length) :
    ULedges[i.val] ∈ boundaryGluingPrefixMinusEdges W h k := by
  have hu : ULedges[i.val] ∈ boundaryGluingUpperLeftEdges W h k :=
    List.mem_reverse.mp (List.getElem_mem i.isLt)
  have hm : ULedges[i.val] ∈ boundaryGluingPrefixMinusEdges W h k ∩
      boundaryGluingPrimedEdges W h k hτ := by
    rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk]
    exact hu
  exact hm.1

/-- Helper toward Lemma 5.5: the finite attachment ports use the corrected
ordered upper-left edge list, including the empty chain at zero. -/
@[expose] noncomputable def lPlusUpperLeftGluedDart (d : Fin (ULedges).length × Bool) : Q :=
  lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
    ⟨(ULedges[d.1.val], d.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk d.1⟩

/-- Helper toward Lemma 5.5: no finite attachment port is identified with
another port of the same chain. -/
theorem lPlusUpperLeftGluedDart_injective :
    Function.Injective (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
  intro a b hab
  have he := lPlusPrefixGluedDart_injective (hτ := hτ) (hqMode := hqMode) hab
  have hnd : (ULedges).Nodup :=
    List.nodup_reverse.mpr ((List.dropLast_sublist _).nodup
      (kmswStageFrontierChain_all w (boundaryHitTime w h k)).UL_nodup)
  apply Prod.ext
  · apply Fin.ext
    exact hnd.getElem_inj_iff.mp (congrArg (fun d => d.val.1) he)
  · exact congrArg (fun d => d.val.2) he

/-- Helper toward Lemma 5.5: extend the prefix code rotation by the identity. -/
@[expose] noncomputable def lPlusPrefixExtendedRotation : Equiv.Perm Q :=
  (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk).extendDomain
      (Equiv.ofInjective _ (lPlusPrefixGluedDart_injective
        (hτ := hτ) (hqMode := hqMode)))

/-- Helper toward Lemma 5.5: extend the primed code rotation by the identity. -/
@[expose] noncomputable def lPlusPrimedExtendedRotation : Equiv.Perm Q :=
  (kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)).extendDomain
      (Equiv.ofInjective _ (lPlusPrimedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode)))

/-- Helper toward Lemma 5.5: extend the retained hatted code rotation. -/
@[expose] noncomputable def lPlusHattedExtendedRotation : Equiv.Perm Q :=
  (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩).extendDomain
      (Equiv.ofInjective _ (lPlusHattedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode)))

/-- Helper toward Lemma 5.5: correct the two corners at every positive
beta vertex; the initial beta port is fixed by this corner exchange. -/
@[expose] noncomputable def lPlusBetaCornerRotation : Equiv.Perm Q :=
  lMinusBoundaryCornerPerm.extendDomain
    (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode))

/-- Helper toward Lemma 5.5: correct the interior corners of the finite
upper-left attachment, fixing the two endpoint ports. -/
@[expose] noncomputable def lPlusUpperLeftCornerRotation : Equiv.Perm Q :=
  (lPlusUpperLeftCornerPerm (ULedges).length).extendDomain
    (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))

/-- Helper toward Lemma 5.5: a candidate assembled exclusively from the
three code rotations and their indexed attachment corners. The action is
prefix, finite corner, primed, beta corner, hatted, in that order. Geometric
rotation is not used in the definition; boundary identification is separate. -/
@[expose] noncomputable def lPlusGluedCorrectedRotation : Equiv.Perm Q :=
  lPlusHattedExtendedRotation hτ hqMode * lPlusBetaCornerRotation hτ hqMode *
    lPlusPrimedExtendedRotation hτ hqMode hfin *
    lPlusUpperLeftCornerRotation hτ hqMode hfin hk *
    lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the corrected candidate is a genuine
permutation without an attachment or geometric rotation premise. -/
theorem lPlusGluedCorrectedRotation_bijective :
    Function.Bijective
      (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk) :=
  (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk).bijective


include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every beta correction port is based at an
attachment vertex, including the initial port. -/
theorem lPlusBetaGluedDart_endpoint_mem (d : ℕ × Bool) :
    kmswLimitDartVertex w (D (lPlusBetaGluedDart hτ hqMode d)).val ∈ B := by
  have hbdy : ((MH).boundary d.1).1 = kmswLeftBoundaryEdge (hatCodes U hτ) d.1 := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.1 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  refine ⟨boundaryGluingHatEdgeMap W h k hτ ((MH).boundary d.1).1,
    Or.inr ⟨d.1, congrArg (boundaryGluingHatEdgeMap W h k hτ) hbdy.symm⟩, ?_⟩
  cases hb : d.2
  · exact Or.inl (by simp only [lPlusBetaGluedDart,
      lPlusHattedGluedDart, lPlusGluedDartEquivNonneg_mk,
      lPlusBlockDartImage, hb])
  · exact Or.inr (by simp only [lPlusBetaGluedDart,
      lPlusHattedGluedDart, lPlusGluedDartEquivNonneg_mk,
      lPlusBlockDartImage, hb])

include Tpath hleft in
/-- Helper toward Lemma 5.5: every finite correction port is based at an
upper-left attachment vertex. -/
theorem lPlusUpperLeftGluedDart_endpoint_mem (d : Fin (ULedges).length × Bool) :
    kmswLimitDartVertex w
      (D (lPlusUpperLeftGluedDart hτ hqMode hfin hk d)).val ∈ B := by
  refine ⟨ULedges[d.1.val], Or.inl
    (List.mem_reverse.mp (List.getElem_mem d.1.isLt)), ?_⟩
  cases hb : d.2
  · exact Or.inl (by simp only [lPlusUpperLeftGluedDart,
      lPlusPrefixGluedDart, lPlusGluedDartEquivNonneg_mk,
      lPlusBlockDartImage, hb])
  · exact Or.inr (by simp only [lPlusUpperLeftGluedDart,
      lPlusPrefixGluedDart, lPlusGluedDartEquivNonneg_mk,
      lPlusBlockDartImage, hb])

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: both interface corner permutations fix every
dart based away from the two attachment boundaries. -/
theorem lPlusCornerRotations_fixed_outside (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) :
    lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d ∧
      lPlusBetaCornerRotation hτ hqMode d = d := by
  constructor
  · apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨a, ha⟩
    apply hd
    rw [← ha]
    exact lPlusUpperLeftGluedDart_endpoint_mem hτ hp P hqMode Tpath hfin hleft hk a
  · apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨a, ha⟩
    apply hd
    rw [← ha]
    exact lPlusBetaGluedDart_endpoint_mem hτ hp P hqMode Tpath hfin hleft hk a

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the candidate with both interface corner
corrections agrees with the original candidate off the attachment vertices. -/
theorem lPlusGluedCorrectedRotation_eq_spliced_outside (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) :
    lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d =
      lPlusGluedSplicedRotation (hτ := hτ) (hp := hp) (P := P)
        (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) (hk := hk) d := by
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let F := lPlusBlockDartImage (M := MH) hτ
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let CB := lPlusBetaCornerRotation hτ hqMode
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hPF (a : LPlusPrefixDart W h k)
      (b : Sum LPlusPrimedDart (LPlusHattedDart MH))
      (he : IP a = (⟦Sum.inr b⟧ : Q)) : kmswLimitDartVertex w a.val ∈ B := by
    exact lPlus_prefix_other_shared_endpoint hτ hqMode hk a b
      (congrArg (kmswLimitDartVertex w)
        ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) (.inl a) (.inr b)).mp he))
  have hTH (p : LPlusPrimedDart) (a : LPlusHattedDart MH)
      (he : IT p = IH a) : kmswLimitDartVertex w (F (.inr (.inl p))) ∈ B := by
    exact lPlus_primed_hatted_shared_endpoint_mem hτ hqMode hfin p a
      (congrArg (kmswLimitDartVertex w)
        ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
          (.inr (.inl p)) (.inr (.inr a))).mp he))
  have hPnot (a : LPlusPrefixDart W h k) (ha : kmswLimitDartVertex w a.val ∉ B) :
      IP a ∉ Set.range IT ∧ IP a ∉ Set.range IH := by
    constructor
    · rintro ⟨p, hp'⟩
      exact ha (hPF a (.inl p) hp'.symm)
    · rintro ⟨p, hp'⟩
      exact ha (hPF a (.inr p) hp'.symm)
  have hTnot (p : LPlusPrimedDart)
      (ha : kmswLimitDartVertex w (F (.inr (.inl p))) ∉ B) :
      IT p ∉ Set.range IP ∧ IT p ∉ Set.range IH := by
    constructor
    · rintro ⟨a, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hPF a (.inl p) he)
    · rintro ⟨a, he⟩
      exact ha (hTH p a he.symm)
  have hHnot (a : LPlusHattedDart MH)
      (ha : kmswLimitDartVertex w (F (.inr (.inr a))) ∉ B) :
      IH a ∉ Set.range IP ∧ IH a ∉ Set.range IT := by
    constructor
    · rintro ⟨p, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hPF p (.inr a) he)
    · rintro ⟨p, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hTH p a he)
  have hvertex {a b : ℕ × Bool} (hr : (S).rotation a b) :
      kmswLimitDartVertex w b = kmswLimitDartVertex w a := by
    obtain ⟨n, _, hn, _⟩ := hr
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a b).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩).symm
  have hr : (S).rotation (D d).val (D (C d)).val := by
    revert hd
    induction d using Quotient.inductionOn with
    | h a =>
      intro hd
      cases a with
      | inl a =>
        have ha : kmswLimitDartVertex w a.val ∉ B := hd
        have hrot := lPlus_prefix_interior_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk a ha
        have hv := hvertex hrot
        have ha' : kmswLimitDartVertex w (PR a).val ∉ B := hv ▸ ha
        obtain ⟨hT, hH⟩ := hPnot (PR a) ha'
        have hcorn := lPlusCornerRotations_fixed_outside
          hτ hp P hqMode Tpath hfin hleft hk (IP (PR a)) ha'
        have hPE : PE (IP a) = IP (PR a) :=
          PR.extendDomain_apply_image _ a
        have hTE : TE (IP (PR a)) = IP (PR a) :=
          Equiv.Perm.extendDomain_apply_not_subtype _ _ hT
        have hHE : HE (IP (PR a)) = IP (PR a) :=
          Equiv.Perm.extendDomain_apply_not_subtype _ _ hH
        have hC : C (IP a) = IP (PR a) := by
          change HE (CB (TE (CU (PE (IP a))))) = _
          rw [hPE, hcorn.1, hTE, hcorn.2, hHE]
        change (S).rotation (D (IP a)).val (D (C (IP a))).val
        rw [hC]
        exact hrot
      | inr a =>
        cases a with
        | inl p =>
          have ha : kmswLimitDartVertex w (F (.inr (.inl p))) ∉ B := hd
          have hrot := lPlus_primed_interior_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk p ha
          have hv := hvertex hrot
          have ha' : kmswLimitDartVertex w (F (.inr (.inl (TR p)))) ∉ B := hv ▸ ha
          have hP := (hTnot p ha).1
          have hH := (hTnot (TR p) ha').2
          have hcorn := lPlusCornerRotations_fixed_outside
            hτ hp P hqMode Tpath hfin hleft hk (IT p) ha
          have hcorn' := lPlusCornerRotations_fixed_outside
            hτ hp P hqMode Tpath hfin hleft hk (IT (TR p)) ha'
          have hPE : PE (IT p) = IT p :=
            Equiv.Perm.extendDomain_apply_not_subtype _ _ hP
          have hTE : TE (IT p) = IT (TR p) :=
            TR.extendDomain_apply_image _ p
          have hHE : HE (IT (TR p)) = IT (TR p) :=
            Equiv.Perm.extendDomain_apply_not_subtype _ _ hH
          have hC : C (IT p) = IT (TR p) := by
            change HE (CB (TE (CU (PE (IT p))))) = _
            rw [hPE, hcorn.1, hTE, hcorn'.2, hHE]
          change (S).rotation (D (IT p)).val (D (C (IT p))).val
          rw [hC]
          exact hrot
        | inr a =>
          have ha : kmswLimitDartVertex w (F (.inr (.inr a))) ∉ B := hd
          have hrot := lPlus_hatted_interior_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk a ha
          obtain ⟨hP, hT⟩ := hHnot a ha
          have hcorn := lPlusCornerRotations_fixed_outside
            hτ hp P hqMode Tpath hfin hleft hk (IH a) ha
          have hPE : PE (IH a) = IH a :=
            Equiv.Perm.extendDomain_apply_not_subtype _ _ hP
          have hTE : TE (IH a) = IH a :=
            Equiv.Perm.extendDomain_apply_not_subtype _ _ hT
          have hHE : HE (IH a) = IH (HR a) :=
            HR.extendDomain_apply_image _ a
          have hC : C (IH a) = IH (HR a) := by
            change HE (CB (TE (CU (PE (IH a))))) = _
            rw [hPE, hcorn.1, hTE, hcorn.2, hHE]
          change (S).rotation (D (IH a)).val (D (C (IH a))).val
          rw [hC]
          exact hrot
  exact ((lPlusGluedSplicedRotation_interior
    hτ hp P hqMode Tpath hfin hleft hk d hd (C d)).mpr hr).symm

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the established interior rotation equivalence
transfers to the candidate with corrections at both interfaces, including zero. -/
theorem lPlusGluedCorrectedRotation_interior (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) (e : Q) :
    lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  rw [lPlusGluedCorrectedRotation_eq_spliced_outside
    hτ hp P hqMode Tpath hfin hleft hk d hd]
  exact lPlusGluedSplicedRotation_interior hτ hp P hqMode Tpath hfin hleft hk d hd e





































































end DirectedDistances.PaperProofs.Section5
