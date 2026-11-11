/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideInterior2

/-! Helper toward Lemma 5.5: rotation transport for the nonpositive left side. -/

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

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "R" => lMinusCodeInitialSplicedRotation rL qL
  (lMinus_primed_observation_finiteIncidence hτ hfin)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a nonshared retained hatted dart outside the
initial vertex has no intervening primed dart before its hatted first return. -/
theorem lMinus_hatted_interior_side_rotation
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hinit : kmswLimitDartVertex w (EH d.val.1, d.val.2) ≠ VH 0)
    (hboundary : ∀ i : ℕ, ∀ b : Bool,
      (EH d.val.1, d.val.2) ≠ (EH ((Q).boundary i).1, b)) :
    (S).rotation (EH d.val.1, d.val.2)
      (EH (lMinusHattedRotation _ qL d).val.1,
        (lMinusHattedRotation _ qL d).val.2) := by
  let σ := kmswInfRot w (H.1 0)
  let x : ℕ × Bool := (EH d.val.1, d.val.2)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  obtain ⟨t, ht, hte, htgap⟩ := lMinusHattedDartImage_firstReturn
    (H := H) hτ hqMode hfin d
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  rcases (Set.ext_iff.mp (lMinus_side_darts_union
    hτ hp P hqMode Tpath hfin hleft hk) _).mp hs with ⟨p, hp'⟩ | hH
  · have hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
        kmswLimitDartVertex w x := by
      have he := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      exact (congrArg (kmswLimitDartVertex w) hp').trans he.symm
    obtain hzero | ⟨i, hi⟩ := lMinus_shared_dart_endpoint_interface hτ hfin p d.val hv
    · exact hinit (hv.symm.trans hzero)
    have hbdy (i : ℕ) : ((Q).boundary i).1 =
        kmswLeftBoundaryEdge (hatCodes U hτ) i := by
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    rw [← hbdy i] at hi
    let a : ℕ × Bool := (EH ((Q).boundary i).1, true)
    let b : ℕ × Bool := (EH ((Q).boundary (i + 1)).1, false)
    obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapH, hperiod, _⟩ :=
      lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
    change (σ : _ → _)^[n] a = b at hna
    change (σ : _ → _)^[m] b = a at hmb
    change (σ : _ → _)^[n + m] a = a at hperiod
    have hax : kmswLimitDartVertex w a = kmswLimitDartVertex w x :=
      hi.symm.trans hv
    obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hax
    let s := r % (n + m)
    have hsr : (σ : _ → _)^[s] a = x :=
      (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
        (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
    have hslt : s < n + m := Nat.mod_lt _ (by omega)
    have hspos : 0 < s := by
      by_contra hh
      have hz : s = 0 := by omega
      exact hboundary i true (by simpa only [hz, Function.iterate_zero_apply] using hsr.symm)
    have hsn : s < n := by
      by_contra hh
      by_cases he : s = n
      · exact hboundary (i + 1) false (hsr.symm.trans (by simpa only [he] using hna))
      · apply hgapH (s - n) (by omega) (by omega)
        refine ⟨d, ?_⟩
        change x = (σ : _ → _)^[s - n] b
        rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hsr.symm
    have htle : t ≤ n - s := by
      by_contra hh
      apply htgap (n - s) (by omega) (by omega)
      refine ⟨⟨(((Q).boundary (i + 1)).1, false),
        lMinus_hatted_boundary_mem _ qL (i + 1)⟩, ?_⟩
      change b = (σ : _ → _)^[n - s] x
      rw [← hsr, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), hna]
    apply hgapP (j + s) (by omega) (by omega)
    refine ⟨p, ?_⟩
    rw [Function.iterate_add_apply, hsr]
    exact hp'
  · exact htgap j hj hjt hH

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: outside the initial vertex, a nonshared
hatted input has exactly its own block successor under the spliced candidate. -/
theorem lMinusCodeInitialSplicedRotation_hatted_interior
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex w (D (lMinusCodeHattedDart rL Q d)).val ≠ VH 0)
    (hboundary : ∀ i : ℕ, ∀ b : Bool,
      lMinusCodeHattedDart rL Q d ≠ lMinusCodeBoundaryDart rL qL (i, b)) :
    R (lMinusCodeHattedDart rL Q d) =
      lMinusCodeHattedDart rL Q (lMinusHattedRotation _ qL d) := by
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
  have hpred : lMinusCodeHattedDart rL Q d ≠
      (Hrot.extendDomain Hemb).symm (lMinusCodeBoundaryDart rL qL (0, false)) := by
    intro he
    apply hv
    rw [he, lMinusCodeHattedRotation_initial_predecessor,
      lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ]
    exact congrArg VH (lMinusHattedRotation_initial_predecessor_vertex _ qL)
  rw [lMinusCodeInitialSplicedRotation_eq_adjusted_outside_initial
      hτ hp P hqMode Tpath hfin hleft hk _ hv,
    lMinusCodeInitialAdjustedRotation_apply_of_ne rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) _ (hboundary 0 false) hpred]
  change Prot.extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb (lMinusCodeHattedDart rL Q d))) = y
  have hH : Hrot.extendDomain Hemb (lMinusCodeHattedDart rL Q d) = y :=
    Hrot.extendDomain_apply_image Hemb d
  rw [hH]
  by_cases hy : y ∈ Set.range (lMinusCodePrimedDart rL Q)
  · obtain ⟨i, b, he⟩ := (lMinusCodeHattedDart_mem_primed_iff
      hτ hp P hqMode Tpath hfin hleft hk (Hrot d)).mp hy
    cases b with
    | true =>
      have he' : Hrot d =
          ⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩ :=
        lMinusCodeHattedDart_injective rL qL he
      have hd : d =
          ⟨(((Q).boundary (i + 1)).1, false),
            lMinus_hatted_boundary_mem _ qL (i + 1)⟩ := by
        apply Hrot.injective
        exact he'.trans (lMinusHattedRotation_boundary_corner _ qL i).symm
      exact (hboundary (i + 1) false (congrArg (lMinusCodeHattedDart rL Q) hd)).elim
    | false =>
      cases i with
      | zero =>
        apply False.elim
        apply hpred
        apply (Hrot.extendDomain Hemb).injective
        rw [hH, Equiv.apply_symm_apply]
        exact he
      | succ i =>
        change y = lMinusCodeBoundaryDart rL qL (i + 1, false) at he
        rw [he]
        have hC : lMinusBoundaryCornerPerm.extendDomain Cemb
            (lMinusCodeBoundaryDart rL qL (i + 1, false)) =
              lMinusCodeBoundaryDart rL qL (i, true) :=
          lMinusBoundaryCornerPerm.extendDomain_apply_image Cemb (i + 1, false)
        rw [hC, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk i true]
        have hP : Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q
            (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false)) =
              lMinusCodePrimedDart rL Q (Prot
                (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false)) :=
          Prot.extendDomain_apply_image Pemb _
        change Prot.extendDomain Pemb (lMinusCodePrimedDart rL Q
          (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i, false)) = _
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
      rintro ⟨⟨i, b⟩, he⟩
      apply hy
      rw [← he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hC,
      Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hy]

/-- Helper toward Lemma 5.5: every retained hatted dart outside the
initial star has the actual side successor, including shared interface ports. -/
theorem lMinus_hatted_outside_initial_side_rotation
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex w (D (lMinusCodeHattedDart rL Q d)).val ≠ VH 0) :
    (S).rotation (D (lMinusCodeHattedDart rL Q d)).val
      (D (R (lMinusCodeHattedDart rL Q d))).val := by
  by_cases hb : ∃ i : ℕ, ∃ b : Bool,
      lMinusCodeHattedDart rL Q d = lMinusCodeBoundaryDart rL qL (i, b)
  · obtain ⟨i, b, he⟩ := hb
    rw [he] at hv ⊢
    exact lMinusCodeInitialSplicedRotation_boundary_outside_initial
      hτ hp P hqMode Tpath hfin hleft hk i b hv
  have hboundary : ∀ i : ℕ, ∀ b : Bool,
      lMinusCodeHattedDart rL Q d ≠ lMinusCodeBoundaryDart rL qL (i, b) := by
    intro i b he
    exact hb ⟨i, b, he⟩
  rw [lMinusCodeInitialSplicedRotation_hatted_interior
      hτ hp P hqMode Tpath hfin hleft hk d hv hboundary,
    lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_hatted]
  apply lMinus_hatted_interior_side_rotation hτ hp P hqMode Tpath hfin hleft hk d
  · rw [lMinusCodeGluedDartEquiv_hatted] at hv
    exact hv
  · intro i b he
    apply hboundary i b
    apply (D).injective
    apply Subtype.ext
    rw [lMinusCodeGluedDartEquiv_hatted]
    change (EH d.val.1, d.val.2) = (D (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary i).1, b), lMinus_hatted_boundary_mem _ qL i⟩)).val
    rw [lMinusCodeGluedDartEquiv_hatted]
    exact he

/-- Helper toward Lemma 5.5: the spliced candidate realizes geometric
side rotation on every dart of the nonpositive left side. -/
theorem lMinusCodeInitialSplicedRotation_side_rotation
    (d : LMinusCodeGluedDart rL Q) :
    (S).rotation (D d).val (D (R d)).val := by
  by_cases hv : kmswLimitDartVertex w (D d).val = VH 0
  · let E := lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    have hi := (lMinusGluedCellEquiv_rotation_initial_star_spliced_iff
      hτ hp P hqMode Tpath hfin hleft hk d hv (Sum.inr (E (R d)))).mp
    have he : lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (Sum.inr (E d)) (Sum.inr (E (R d))) := by
      change Equiv.permCongr E R (E d) = E (R d)
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    have hr := hi he
    change (S).rotation
      (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk (E d)).val
      (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk (E (R d))).val at hr
    simpa only [E, lMinusCodeToGluedDartEquiv_equiv] using hr
  · obtain ⟨p, rfl⟩ | ⟨a, rfl⟩ := lMinusCodeGluedDart_mem_block hqMode d
    · exact lMinus_primed_outside_initial_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk p hv
    · exact lMinus_hatted_outside_initial_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk a hv

end GeometricGluing

/-- Helper toward Lemma 5.5: the spliced code rotation agrees in both
directions, on all vertex and dart cell branches, with geometric left-side rotation. -/
theorem lMinusGluedCellEquiv_rotation_iff
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
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0)
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
      (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
    let E := lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    let R := Equiv.permCongr E
      (lMinusCodeInitialSplicedRotation r q
        (lMinus_primed_observation_finiteIncidence hτ hfin))
    (match u, v with
      | .inr d, .inr e => R d = e
      | _, _ => False) ↔
      geometricSideRelation (m0GeodesicSide hp P .left) .rotation
        (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  dsimp only
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
  let E := lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let D := lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let G := lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let R := lMinusCodeInitialSplicedRotation r q
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  cases u with
  | inl u => cases v <;> rfl
  | inr u =>
    obtain ⟨d, rfl⟩ := E.surjective u
    have hr := lMinusCodeInitialSplicedRotation_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk d
    cases v with
    | inl v => rfl
    | inr e =>
      change Equiv.permCongr E R (E d) = e ↔
        (m0GeodesicSide hp P .left).rotation (G (E d)).val (G e).val
      have hR : Equiv.permCongr E R (E d) = E (R d) := by
        simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rw [hR, lMinusCodeToGluedDartEquiv_equiv]
      constructor
      · intro he
        rw [← he, lMinusCodeToGluedDartEquiv_equiv]
        exact hr
      · intro he
        apply G.injective
        rw [lMinusCodeToGluedDartEquiv_equiv]
        apply Subtype.ext
        obtain ⟨t, htpos, hte, htgap⟩ := hr
        obtain ⟨s, hspos, hse, hsgap⟩ := he
        have hts : t = s := by
          apply Nat.le_antisymm
          · by_contra hn
            exact htgap s hspos (by omega) (hse.symm ▸ (G e).property)
          · by_contra hn
            exact hsgap t htpos (by omega) (hte.symm ▸ (D (R d)).property)
        exact hte.symm.trans (hts ▸ hse)

end DirectedDistances.PaperProofs.Section5
