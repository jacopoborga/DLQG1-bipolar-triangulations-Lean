/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff5
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice

/-! Helper toward Lemma 5.5: a terminal-port repair of the code permutation. -/

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
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "F" => lPlusBlockDartImage (M := MH) hτ
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "B" => (Set.ofPred fun v : ℕ => ∃ e : ℕ,
  e ∈ boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingBetaEdges W h k hτ ∧
  (kmswLimitDartVertex w (e, false) = v ∨ kmswLimitDartVertex w (e, true) = v))

/-- Helper toward Lemma 5.5: the code quotient identifies exactly equal
geometric darts. This equivalence uses only the three block code images. -/
@[expose] noncomputable def lPlusGluedCodeImageEquiv : Q ≃ Set.range F :=
  Setoid.quotientKerEquivRange F

include H in
/-- Helper toward Lemma 5.5: finite-incidence ambient rotation has a
positive return to every retained code dart. No side identification is used. -/
theorem lPlusGluedCodeReturn_exists (d : Set.range F) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] d.val ∈ Set.range F := by
  let σ := kmswInfRot w (H.1 0)
  have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) d.val (σ d.val)).mp
    ⟨1, by simp only [pow_one]; rfl⟩
  obtain ⟨m, hm⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
    (σ d.val) d.val).mpr hv.symm
  refine ⟨m + 1, by omega, ?_⟩
  have he : (σ ^ (m + 1)) d.val = d.val := by
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact hm
  rw [← Equiv.Perm.coe_pow, he]
  exact d.property

/-- Helper toward Lemma 5.5: compute the least positive ambient return
to the retained code image, then recover its unique quotient representative. -/
@[expose] noncomputable def lPlusGluedCodeReturn (d : Q) : Q :=
  (lPlusGluedCodeImageEquiv hτ hqMode).symm
    (subsetFirstReturn (kmswInfRot w (H.1 0)) (Set.range F)
      (lPlusGluedCodeReturn_exists (H := H) hτ hqMode)
      (lPlusGluedCodeImageEquiv hτ hqMode d))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the independent code-image equivalence and
the established geometric dart equivalence have the same underlying dart. -/
theorem lPlusGluedCodeImageEquiv_val (d : Q) :
    (lPlusGluedCodeImageEquiv hτ hqMode d).val = (D d).val := by
  induction d using Quotient.inductionOn with
  | h a => rfl

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the code-defined return has the full positive
first-return characterization, with no assumed rotation or return equation. -/
theorem lPlusGluedCodeReturn_spec (d : Q) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
        (D (lPlusGluedCodeReturn (H := H) hτ hqMode d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  let J := lPlusGluedCodeImageEquiv hτ hqMode
  let hr := lPlusGluedCodeReturn_exists (H := H) hτ hqMode
  let n := subsetFirstReturnTime (kmswInfRot w (H.1 0)) (Set.range F) hr (J d)
  have hs := subsetFirstReturnTime_spec (kmswInfRot w (H.1 0))
    (Set.range F) hr (J d)
  have he : (J (lPlusGluedCodeReturn (H := H) hτ hqMode d)).val =
      (kmswInfRot w (H.1 0) : _ → _)^[n] (J d).val := by
    change (J (J.symm _)).val = _
    rw [J.apply_symm_apply]
    rfl
  rw [lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk,
    lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk] at he
  refine ⟨n, hs.1, he.symm, ?_⟩
  intro j hj hjn
  have hg := hs.2.2 j hj hjn
  rw [show (J d).val = (D d).val from
    lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk d] at hg
  exact hg

include H in
/-- Helper toward Lemma 5.5: the least positive code return is injective.
Backward return exists by the proved positive ambient period at each dart. -/
theorem lPlusGluedCodeReturn_injective :
    Function.Injective (lPlusGluedCodeReturn (H := H) hτ hqMode) := by
  let σ := kmswInfRot w (H.1 0)
  let J := lPlusGluedCodeImageEquiv hτ hqMode
  let hr := lPlusGluedCodeReturn_exists (H := H) hτ hqMode
  have hri : ∀ x : Set.range F, ∃ n : ℕ, 0 < n ∧
      ((σ⁻¹ : Equiv.Perm (ℕ × Bool)) : _ → _)^[n] x.val ∈ Set.range F := by
    intro x
    have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x.val (σ x.val)).mp
      ⟨1, by simp only [pow_one]; rfl⟩
    obtain ⟨m, hm⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
      (σ x.val) x.val).mpr hv.symm
    have he : (σ : _ → _)^[m + 1] x.val = x.val := by
      rw [← Equiv.Perm.coe_pow, pow_succ, Equiv.Perm.mul_apply]
      exact hm
    have hi := permIterateInvSub σ (Nat.le_refl (m + 1)) x.val
    rw [he] at hi
    simp only [Nat.sub_self, Function.iterate_zero_apply] at hi
    refine ⟨m + 1, by omega, ?_⟩
    rw [hi]
    exact x.property
  intro a b hab
  change J.symm (subsetFirstReturn σ (Set.range F) hr (J a)) =
    J.symm (subsetFirstReturn σ (Set.range F) hr (J b)) at hab
  have he := congrArg (subsetFirstReturn σ⁻¹ (Set.range F) hri)
    (J.symm.injective hab)
  rw [subsetFirstReturn_inv_apply, subsetFirstReturn_inv_apply] at he
  exact J.injective he

/-- Helper toward Lemma 5.5: repair only the terminal upper-left output
and the old preimage of its correct code return. The empty chain needs no
repair. This definition uses the ambient code rotation, not the side rotation. -/
@[expose] noncomputable def lPlusGluedCorrectedRotation2 : Equiv.Perm Q :=
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  if hn : 0 < (ULedges).length then
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    Equiv.swap (C t) (lPlusGluedCodeReturn (H := H) hτ hqMode t) * C
  else C

/-- Helper toward Lemma 5.5: the terminal repair remains a permutation. -/
theorem lPlusGluedCorrectedRotation2_bijective :
    Function.Bijective
      (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk) :=
  (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk).bijective

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at the terminal port, the repaired permutation
has exactly its computed code first return. -/
theorem lPlusGluedCorrectedRotation2_terminal
    (hn : 0 < (ULedges).length) :
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t =
      lPlusGluedCodeReturn (H := H) hτ hqMode t := by
  dsimp only
  rw [lPlusGluedCorrectedRotation2, dite_eq_left hn, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal port satisfies the complete
ambient first-return statement after repair. -/
theorem lPlusGluedCorrectedRotation2_terminal_firstReturn
    (hn : 0 < (ULedges).length) :
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D t).val =
        (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D t).val ∉ Set.range F := by
  dsimp only
  rw [lPlusGluedCorrectedRotation2_terminal hτ hp P hqMode Tpath hfin hleft hk hn]
  exact lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk _

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: outside the terminal port and the old preimage
of its computed return, the repaired permutation is unchanged. -/
theorem lPlusGluedCorrectedRotation2_eq_of_ne
    (hn : 0 < (ULedges).length) (d : Q)
    (hd : d ≠ lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false))
    (hr : lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d ≠
      lPlusGluedCodeReturn (H := H) hτ hqMode
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk
          (⟨(ULedges).length - 1, by omega⟩, false))) :
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d =
      lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d := by
  rw [lPlusGluedCorrectedRotation2, dite_eq_left hn, Equiv.Perm.mul_apply]
  apply Equiv.swap_apply_of_ne_of_ne _ hr
  exact fun he => hd ((lPlusGluedCorrectedRotation hτ hp P hqMode
    Tpath hfin hleft hk).injective he)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal repair agrees with the previous
candidate at every dart covered by the established interior equivalence. -/
theorem lPlusGluedCorrectedRotation2_eq_interior (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) :
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d =
      lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d := by
  by_cases hn : 0 < (ULedges).length
  · let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    have ht : kmswLimitDartVertex w (D t).val ∈ B :=
      lPlusUpperLeftGluedDart_endpoint_mem hτ hp P hqMode Tpath hfin hleft hk _
    have hdt : d ≠ t := by
      intro he
      exact hd (he ▸ ht)
    apply lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt
    intro he
    have hrot := (lPlusGluedCorrectedRotation_interior
      hτ hp P hqMode Tpath hfin hleft hk d hd
      (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk d)).mp rfl
    obtain ⟨m, _, hm, _⟩ := hrot
    have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨m, by simpa only [Equiv.Perm.coe_pow] using hm⟩
    obtain ⟨n, _, hnret, _⟩ := lPlusGluedCodeReturn_spec
      hτ hp P hqMode Tpath hfin hleft hk t
    have hvt := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hnret⟩
    have hv' : kmswLimitDartVertex w (D d).val =
        kmswLimitDartVertex w (D t).val := by
      exact hv.trans ((congrArg (fun q : Q => kmswLimitDartVertex w (D q).val)
        he).trans hvt.symm)
    exact hd (hv'.symm ▸ ht)
  · rw [lPlusGluedCorrectedRotation2, dite_eq_right hn]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the other changed input is exactly the old
preimage of the computed terminal return, and it receives the old terminal
output. This includes the case in which the exchange is trivial. -/
theorem lPlusGluedCorrectedRotation2_terminal_preimage
    (hn : 0 < (ULedges).length) :
    let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
        (C.symm (lPlusGluedCodeReturn (H := H) hτ hqMode t)) = C t := by
  dsimp only
  rw [lPlusGluedCorrectedRotation2, dite_eq_left hn, Equiv.Perm.mul_apply,
    Equiv.apply_symm_apply, Equiv.swap_apply_right]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the established interior iff transfers to
the repaired permutation on precisely the same interior domain. -/
theorem lPlusGluedCorrectedRotation2_interior (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) (e : Q) :
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (m0GeodesicSide hp P .left).rotation (D d).val (D e).val := by
  rw [lPlusGluedCorrectedRotation2_eq_interior
    hτ hp P hqMode Tpath hfin hleft hk d hd]
  exact lPlusGluedCorrectedRotation_interior
    hτ hp P hqMode Tpath hfin hleft hk d hd e

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal repair preserves the first-return
statement at every interior west attachment port. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_interior_west_firstReturn
    (hkpos : 0 < k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
        (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  dsimp only
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hn : 0 < (ULedges).length := by omega
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(ULedges).length - 1, by omega⟩, false)
  have hdt : d ≠ t := by
    intro he
    have he' := lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk he
    have hei := congrArg (fun p => p.1.val) he'
    change i.val = (ULedges).length - 1 at hei
    omega
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hCR : C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
    apply (D).injective
    apply Subtype.ext
    exact firstReturn_endpoint_unique
      (kmswInfRot w (H.1 0) : _ → _) (Set.range F)
      (hmem (C d)) (hmem _)
      (lPlusGluedCorrectedRotation_upperLeft_interior_west_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hkpos i hi)
      (lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d)
  have heq : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
    apply lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt
    intro he
    exact hdt (lPlusGluedCodeReturn_injective (H := H) hτ hqMode (hCR.symm.trans he))
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
      (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧ _
  rw [heq]
  exact lPlusGluedCorrectedRotation_upperLeft_interior_west_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk hkpos i hi

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal repair preserves the first-return
statement at every interior east attachment port. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_interior_east_firstReturn
    (hkpos : 0 < k) (i : Fin (ULedges).length)
    (hi : i.val + 1 < (ULedges).length) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨i.val + 1, hi⟩, true)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
        (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  dsimp only
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨i.val + 1, hi⟩, true)
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hn : 0 < (ULedges).length := by omega
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(ULedges).length - 1, by omega⟩, false)
  have hdt : d ≠ t := by
    intro he
    have he' := lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk he
    exact Bool.noConfusion (congrArg Prod.snd he')
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hCR : C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
    apply (D).injective
    apply Subtype.ext
    exact firstReturn_endpoint_unique
      (kmswInfRot w (H.1 0) : _ → _) (Set.range F)
      (hmem (C d)) (hmem _)
      (lPlusGluedCorrectedRotation_upperLeft_interior_east_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hkpos i hi)
      (lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d)
  have heq : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
    apply lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt
    intro he
    exact hdt (lPlusGluedCodeReturn_injective (H := H) hτ hqMode (hCR.symm.trans he))
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
      (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧ _
  rw [heq]
  exact lPlusGluedCorrectedRotation_upperLeft_interior_east_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk hkpos i hi










































































end DirectedDistances.PaperProofs.Section5
