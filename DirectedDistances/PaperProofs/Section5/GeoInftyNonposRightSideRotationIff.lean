/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideTerminalStar

/-! Interior nonshared rotation transport for the nonpositive right side. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section InteriorGeometry

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
local notation "n" => boundaryHitTime (shiftedStream W 0) h k
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
local notation "q" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q
local notation "N" => List.length (State.active F :: State.UR F)
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a nonshared prefix dart at an interior shared
vertex returns to the prefix before encountering any hatted dart. Its prefix
successor is either nonshared or the outgoing port of that vertex. -/
theorem rMinus_interior_prefix_nonshared_firstReturn
    (i : Fin N) (hi : i.val + 1 < N)
    (p : StageDart (F).nextEdge)
    (hnot : (p.1.val, p.2) ∉ Set.range
      (fun a : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)))
    (hv : stageEndpoint F p =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    (S).rotation (p.1.val, p.2)
      (rMinusPrefixDartImage (h := h) (stageRot w n p)) ∧
    (rMinusPrefixDartImage (h := h) (stageRot w n p) ∉ Set.range
      (fun a : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)) ∨
      stageRot w n p =
        rMinusPrefixBoundaryDart w n (⟨i.val + 1, hi⟩, false)) := by
  let σ := kmswInfRot w (H.1 0)
  let I := rMinusPrefixDartImage (h := h) (k := k)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let a : ℕ × Bool := (EH (((Q).boundary i.val).1), true)
  let b : ℕ × Bool := (EH (((Q).boundary (i.val + 1)).1), false)
  let x : ℕ × Bool := (p.1.val, p.2)
  have ha := rMinusPrefixDartImage_boundary hτ hqMode i.val _
    (List.getElem?_eq_getElem i.isLt) true
  have hb := rMinusPrefixDartImage_boundary hτ hqMode (i.val + 1) _
    (List.getElem?_eq_getElem hi) false
  obtain ⟨s, t, hs, ht, hsa, htb, hgapH, hgapP, hperiod, hminimal⟩ :=
    rMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[s] a = b at hsa
  change (σ : _ → _)^[t] b = a at htb
  change (σ : _ → _)^[s + t] a = a at hperiod
  change ∀ l, 0 < l → l < s → (σ : _ → _)^[l] a ∉ Set.range J at hgapH
  change ∀ l, 0 < l → l < t → (σ : _ → _)^[l] b ∉ Set.range I at hgapP
  change x ∉ Set.range J at hnot
  have hv' : kmswLimitDartVertex w a = kmswLimitDartVertex w x := by
    change kmswLimitDartVertex w (EH (((Q).boundary i.val).1), true) =
      kmswLimitDartVertex w (p.1.val, p.2)
    rw [← ha]
    have he := edge_endpoints_eq w p.1.isLt
    have he' := edge_endpoints_eq w (rMinusPrefixBoundaryDart w n (i, true)).1.isLt
    dsimp only [rMinusPrefixBoundaryDart] at he'
    change (if true then edgeEast w _ else edgeWest w _) =
      (if p.2 then edgeEast w _ else edgeWest w _)
    simpa only [stageEndpoint, rMinusPrefixBoundaryDart, he.1, he.2,
      he'.1, he'.2, ↓reduceIte] using hv.symm
  obtain ⟨j₀, hj₀⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hv'
  rw [Equiv.Perm.coe_pow] at hj₀
  let j := j₀ % (s + t)
  have hjlt : j < s + t := Nat.mod_lt _ (by omega)
  have hj : (σ : _ → _)^[j] a = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod j₀).trans hj₀
  have haH : a ∈ Set.range J :=
    ⟨⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩, rfl⟩
  have hbH : b ∈ Set.range J :=
    ⟨⟨(((Q).boundary (i.val + 1)).1, false),
      rMinus_hatted_boundary_mem _ q (i.val + 1)⟩, rfl⟩
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    rw [hz, Function.iterate_zero_apply] at hj
    exact hnot (hj ▸ haH)
  have hjs : j < s := by
    by_contra hn
    by_cases he : j = s
    · exact hnot ((hsa.symm.trans (he ▸ hj)) ▸ hbH)
    · have hshift : (σ : _ → _)^[j - s] b = x := by
        rw [← hsa, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hj
      apply hgapP (j - s) (by omega) (by omega)
      exact ⟨p, hshift.symm⟩
  obtain ⟨r, hr, hre, hrgap⟩ := rMinusPrefixDartImage_firstReturn (H := H) p
  change (σ : _ → _)^[r] x = I (stageRot w n p) at hre
  change ∀ l, 0 < l → l < r → (σ : _ → _)^[l] x ∉ Set.range I at hrgap
  have hbound : r ≤ s - j := by
    by_contra hn
    apply hrgap (s - j) (by omega) (by omega)
    refine ⟨rMinusPrefixBoundaryDart w n (⟨i.val + 1, hi⟩, false), ?_⟩
    rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), hsa]
    exact hb
  have hnoH (l : ℕ) (hl : 0 < l) (hlr : l < r) :
      (σ : _ → _)^[l] x ∉ Set.range J := by
    rw [← hj, ← Function.iterate_add_apply]
    exact hgapH (l + j) (by omega) (by omega)
  constructor
  · refine ⟨r, hr, hre, ?_⟩
    intro l hl hlr hm
    have hm' := (Set.ext_iff.mp
      (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
    exact hm'.elim (hrgap l hl hlr) (hnoH l hl hlr)
  · by_cases he : r + j < s
    · left
      change I (stageRot w n p) ∉ Set.range J
      rw [← hre, ← hj, ← Function.iterate_add_apply]
      exact hgapH (r + j) (by omega) he
    · right
      have heq : r + j = s := by omega
      have hend : I (stageRot w n p) = b := by
        rw [← hre, ← hj, ← Function.iterate_add_apply, heq, hsa]
      have hout : I (rMinusPrefixBoundaryDart w n (⟨i.val + 1, hi⟩, false)) = b := hb
      exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) (hend.trans hout.symm)))
        (congrArg (fun z : ℕ × Bool => z.2) (hend.trans hout.symm))

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the splice candidate at a nonshared interior
prefix dart is precisely its finite-prefix rotation successor. -/
theorem rMinusCodeSpliceRotation_interior_prefix_nonshared
    (i : Fin N) (hi : i.val + 1 < N)
    (p : StageDart (F).nextEdge)
    (hnot : (p.1.val, p.2) ∉ Set.range
      (fun a : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)))
    (hv : stageEndpoint F p =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    rMinusCodeSpliceRotation w n q (rMinusCodePrefixDart F Q p) =
      rMinusCodePrefixDart F Q (stageRot w n p) := by
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  let y := rMinusCodePrefixDart F Q (stageRot w n p)
  have hP : (stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p) = y :=
    (stageRot w n).extendDomain_apply_image Pemb p
  change Hrot.extendDomain Hemb ((rMinusBoundaryCornerPerm N).extendDomain Cemb
    ((stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p))) = y
  rw [hP]
  obtain ⟨_, hcases⟩ := rMinus_interior_prefix_nonshared_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk i hi p hnot hv
  rcases hcases with hnon | he
  · have hy : y ∉ Set.range (rMinusCodeHattedDart F Q) := by
      rintro ⟨a, ha⟩
      apply hnon
      refine ⟨a, ?_⟩
      have hh := congrArg (fun z => (D z).val) ha
      rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at hh
      exact hh
    have hC : y ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
      rintro ⟨⟨j, b⟩, he⟩
      apply hy
      rw [← he, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hC,
      Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hy]
  · have hy : y = rMinusCodeBoundaryDart w n Q (⟨i.val + 1, hi⟩, false) := by
      dsimp only [y]
      rw [he]
      rfl
    rw [hy]
    have hC : (rMinusBoundaryCornerPerm N).extendDomain Cemb
        (rMinusCodeBoundaryDart w n Q (⟨i.val + 1, hi⟩, false)) =
          rMinusCodeBoundaryDart w n Q (i, true) := by
      have hh := (rMinusBoundaryCornerPerm N).extendDomain_apply_image Cemb
        (⟨i.val + 1, hi⟩, false)
      change (rMinusBoundaryCornerPerm N).extendDomain Cemb
        (rMinusCodeBoundaryDart w n Q (⟨i.val + 1, hi⟩, false)) =
          rMinusCodeBoundaryDart w n Q
            (rMinusBoundaryCorner N (⟨i.val + 1, hi⟩, false)) at hh
      simpa only [rMinusBoundaryCornerPerm, rMinusBoundaryCorner, Bool.false_eq_true,
        ↓reduceIte, ↓reduceDIte, Nat.zero_lt_succ, Nat.add_sub_cancel] using hh
    rw [hC, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    have hh := Hrot.extendDomain_apply_image Hemb
      ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
    change Hrot.extendDomain Hemb
      (rMinusCodeHattedDart F Q
        ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩) =
      rMinusCodeHattedDart F Q
        (Hrot ⟨(((Q).boundary i.val).1, true),
          rMinus_hatted_boundary_mem _ q i.val⟩) at hh
    change Hrot.extendDomain Hemb (rMinusCodeHattedDart F Q _) = _
    rw [hh, show Hrot = rMinusHattedRotation _ q from rfl,
      rMinusHattedRotation_boundary_corner hqMode i.val]
    exact (rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk
      ⟨i.val + 1, hi⟩ false).symm

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the initial adjustment fixes every dart
at an interior shared vertex. -/
theorem rMinus_interior_initial_swap_fixed (hneg : k < 0)
    (i : Fin N) (d : RMinusCodeGluedDart F Q)
    (hv : kmswLimitDartVertex w (D d).val =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
    let A := rMinusCodeBoundaryDart w n Q (i₀, false)
    let B := rMinusCodePrefixDart F Q
      (stageRot w n (rMinusPrefixBoundaryDart w n (i₀, false)))
    Equiv.swap A B d = d := by
  dsimp only
  let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let a := rMinusPrefixBoundaryDart w n (i₀, false)
  let c := rMinusPrefixBoundaryDart w n (i, true)
  have hne : stageEndpoint F a ≠ stageEndpoint F c := by
    intro he
    have hc := rMinus_negative_initial_prefix_star w h hneg c he.symm
    rcases hc with hc | hc
    · exact Bool.false_ne_true (congrArg (fun z : ℕ × Bool => z.2) hc).symm
    · exact Bool.false_ne_true (congrArg (fun z : ℕ × Bool => z.2) hc).symm
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he
    apply hne
    rw [he, rMinusCodeBoundaryDart_eq_prefix] at hv
    exact (hvpref a).symm.trans hv
  · intro he
    apply hne
    have hrot := (stageRot_sameCycle_iff_endpoint_eq w n a (stageRot w n a)).mp ⟨1, rfl⟩
    rw [he] at hv
    exact hrot.trans ((hvpref (stageRot w n a)).symm.trans hv)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted glued candidate has the geometric
first return at every nonshared prefix dart at an interior shared vertex. -/
theorem rMinusCodeInitialAdjustedRotation_interior_prefix_nonshared_side_rotation
    (i : Fin N) (hi : i.val + 1 < N)
    (p : StageDart (F).nextEdge)
    (hnot : (p.1.val, p.2) ∉ Set.range
      (fun a : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)))
    (hv : stageEndpoint F p =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    (S).rotation (D (rMinusCodePrefixDart F Q p)).val
      (D (rMinusCodeInitialAdjustedRotation w n q
        (rMinusCodePrefixDart F Q p))).val := by
  by_cases hk0 : k = 0
  · have ht : n = 0 := by rw [hk0, boundaryHitTime_zero]
    have heq : rMinusCodeInitialAdjustedRotation w n q = rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [heq]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 _
  have hneg : k < 0 := by omega
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  have hin := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    hneg i (rMinusCodePrefixDart F Q p) ((hvpref p).trans hv)
  have hrotv : stageEndpoint F (stageRot w n p) =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) :=
    ((stageRot_sameCycle_iff_endpoint_eq w n p (stageRot w n p)).mp ⟨1, rfl⟩).symm.trans hv
  have hout := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    hneg i (rMinusCodePrefixDart F Q (stageRot w n p)) ((hvpref _).trans hrotv)
  change (S).rotation (D (rMinusCodePrefixDart F Q p)).val
    (D (Equiv.swap _ _ (rMinusCodeSpliceRotation w n q
      (Equiv.swap _ _ (rMinusCodePrefixDart F Q p))))).val
  rw [hin, rMinusCodeSpliceRotation_interior_prefix_nonshared
    hτ hp P hqMode Tpath hfin hleft hk i hi p hnot hv, hout,
    rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
  exact (rMinus_interior_prefix_nonshared_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk i hi p hnot hv).1

/-- Helper toward Lemma 5.5: ambient rotation iterates preserve the
geometric vertex of a dart. -/
theorem rMinus_dart_vertex_iterate (stream : ℕ → Fin 3) (hf : KMSWFiniteIncidence stream)
    (d : ℕ × Bool) (j : ℕ) :
    kmswLimitDartVertex stream ((kmswInfRot stream hf : _ → _)^[j] d) =
      kmswLimitDartVertex stream d := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (kmswLimitDartVertex_rot stream hf _).trans ih

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the hatted first return of a nonshared
interior hatted dart encounters no intervening prefix dart. -/
theorem rMinus_interior_hatted_nonshared_firstReturn
    (i : Fin N) (hi : i.val + 1 < N)
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hnot : (EH d.val.1, d.val.2) ∉
      Set.range (rMinusPrefixDartImage (h := h) (k := k)))
    (hv : kmswLimitDartVertex w (EH d.val.1, d.val.2) =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    (S).rotation (EH d.val.1, d.val.2)
      (EH (rMinusHattedRotation _ q d).val.1, (rMinusHattedRotation _ q d).val.2) := by
  let σ := kmswInfRot w (H.1 0)
  let I := rMinusPrefixDartImage (h := h) (k := k)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let a : ℕ × Bool := (EH (((Q).boundary i.val).1), true)
  let b : ℕ × Bool := (EH (((Q).boundary (i.val + 1)).1), false)
  let x := J d
  have ha := rMinusPrefixDartImage_boundary hτ hqMode i.val _
    (List.getElem?_eq_getElem i.isLt) true
  have hb := rMinusPrefixDartImage_boundary hτ hqMode (i.val + 1) _
    (List.getElem?_eq_getElem hi) false
  obtain ⟨s, t, hs, ht, hsa, htb, hgapH, hgapP, _, _⟩ :=
    rMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[s] a = b at hsa
  change (σ : _ → _)^[t] b = a at htb
  change ∀ l, 0 < l → l < s → (σ : _ → _)^[l] a ∉ Set.range J at hgapH
  change ∀ l, 0 < l → l < t → (σ : _ → _)^[l] b ∉ Set.range I at hgapP
  change x ∉ Set.range I at hnot
  have hperiod : (σ : _ → _)^[s + t] b = b := by
    rw [Function.iterate_add_apply, htb, hsa]
  have hav : kmswLimitDartVertex w a =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) := by
    change kmswLimitDartVertex w (EH (((Q).boundary i.val).1), true) = _
    rw [← ha]
    have he := edge_endpoints_eq w (rMinusPrefixBoundaryDart w n (i, true)).1.isLt
    dsimp only [rMinusPrefixBoundaryDart] at he
    exact he.2.symm
  have hv' : kmswLimitDartVertex w b = kmswLimitDartVertex w x :=
    (congrArg (kmswLimitDartVertex w) hsa).symm.trans
      ((rMinus_dart_vertex_iterate w (H.1 0) a s).trans (hav.trans hv.symm))
  obtain ⟨j₀, hj₀⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) b x).mpr hv'
  rw [Equiv.Perm.coe_pow] at hj₀
  let j := j₀ % (s + t)
  have hjlt : j < s + t := Nat.mod_lt _ (by omega)
  have hj : (σ : _ → _)^[j] b = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod j₀).trans hj₀
  have haP : a ∈ Set.range I := ⟨rMinusPrefixBoundaryDart w n (i, true), ha⟩
  have hbP : b ∈ Set.range I :=
    ⟨rMinusPrefixBoundaryDart w n (⟨i.val + 1, hi⟩, false), hb⟩
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    rw [hz, Function.iterate_zero_apply] at hj
    exact hnot (hj ▸ hbP)
  have hjt : j < t := by
    by_contra hn
    by_cases he : j = t
    · exact hnot ((htb.symm.trans (he ▸ hj)) ▸ haP)
    · have hshift : (σ : _ → _)^[j - t] a = x := by
        rw [← htb, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hj
      apply hgapH (j - t) (by omega) (by omega)
      exact ⟨d, hshift.symm⟩
  obtain ⟨r, hr, hre, hrgap⟩ := rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  change (σ : _ → _)^[r] x = J (rMinusHattedRotation _ q d) at hre
  change ∀ l, 0 < l → l < r → (σ : _ → _)^[l] x ∉ Set.range J at hrgap
  have hbound : r ≤ t - j := by
    by_contra hn
    apply hrgap (t - j) (by omega) (by omega)
    rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), htb]
    exact ⟨⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩, rfl⟩
  refine ⟨r, hr, hre, ?_⟩
  intro l hl hlr hm
  have hm' := (Set.ext_iff.mp
    (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
  rcases hm' with hmP | hmH
  · apply hgapP (l + j) (by omega) (by omega)
    rw [Function.iterate_add_apply, hj]
    exact hmP
  · exact hrgap l hl hlr hmH

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate has the geometric
first return at every nonshared hatted dart at an interior shared vertex. -/
theorem rMinusCodeInitialAdjustedRotation_interior_hatted_nonshared_side_rotation
    (i : Fin N) (hi : i.val + 1 < N)
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hnot : (EH d.val.1, d.val.2) ∉
      Set.range (rMinusPrefixDartImage (h := h) (k := k)))
    (hv : kmswLimitDartVertex w (EH d.val.1, d.val.2) =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    (S).rotation (D (rMinusCodeHattedDart F Q d)).val
      (D (rMinusCodeInitialAdjustedRotation w n q
        (rMinusCodeHattedDart F Q d))).val := by
  by_cases hk0 : k = 0
  · have ht : n = 0 := by rw [hk0, boundaryHitTime_zero]
    have heq : rMinusCodeInitialAdjustedRotation w n q = rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [heq]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 _
  have hneg : k < 0 := by omega
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hdP : rMinusCodeHattedDart F Q d ∉ Set.range (rMinusCodePrefixDart F Q) := by
    rintro ⟨p, hp⟩
    apply hnot
    refine ⟨p, ?_⟩
    have he := congrArg (fun z => (D z).val) hp
    rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at he
    exact he
  have hdC : rMinusCodeHattedDart F Q d ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
    rintro ⟨b, hb⟩
    exact hdP ⟨rMinusPrefixBoundaryDart w n b, hb⟩
  have hsplice : rMinusCodeSpliceRotation w n q (rMinusCodeHattedDart F Q d) =
      rMinusCodeHattedDart F Q (rMinusHattedRotation _ q d) := by
    change (rMinusHattedRotation _ q).extendDomain Hemb
      ((rMinusBoundaryCornerPerm N).extendDomain Cemb
        ((stageRot w n).extendDomain Pemb (rMinusCodeHattedDart F Q d))) = _
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hdP,
      Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hdC]
    exact (rMinusHattedRotation _ q).extendDomain_apply_image Hemb d
  have hgeom := rMinus_interior_hatted_nonshared_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk i hi d hnot hv
  have hin := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    hneg i (rMinusCodeHattedDart F Q d) (by
      rw [rMinusCodeGluedDartEquiv_hatted]; exact hv)
  have hvout : kmswLimitDartVertex w
      (EH (rMinusHattedRotation _ q d).val.1, (rMinusHattedRotation _ q d).val.2) =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) := by
    obtain ⟨r, _, he, _⟩ := hgeom
    exact (congrArg (kmswLimitDartVertex w) he).symm.trans
      ((rMinus_dart_vertex_iterate w (H.1 0) _ r).trans hv)
  have hout := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    hneg i (rMinusCodeHattedDart F Q (rMinusHattedRotation _ q d)) (by
      rw [rMinusCodeGluedDartEquiv_hatted]; exact hvout)
  change (S).rotation (D (rMinusCodeHattedDart F Q d)).val
    (D (Equiv.swap _ _ (rMinusCodeSpliceRotation w n q
      (Equiv.swap _ _ (rMinusCodeHattedDart F Q d))))).val
  rw [hin, hsplice, hout, rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_hatted]
  exact hgeom

include H hfin in
/-- Helper toward Lemma 5.5: a dart common to both blocks at an interior
shared vertex is one of the two shared ports of that vertex. -/
theorem rMinus_interior_common_dart (i : Fin N) (hi : i.val + 1 < N)
    (p : StageDart (F).nextEdge)
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (he : (p.1.val, p.2) = (EH d.val.1, d.val.2))
    (hv : stageEndpoint F p =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    p = rMinusPrefixBoundaryDart w n (i, true) ∨
      p = rMinusPrefixBoundaryDart w n (⟨i.val + 1, hi⟩, false) := by
  let σ := kmswInfRot w (H.1 0)
  let I := rMinusPrefixDartImage (h := h) (k := k)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let a : ℕ × Bool := (EH (((Q).boundary i.val).1), true)
  let b : ℕ × Bool := (EH (((Q).boundary (i.val + 1)).1), false)
  let x : ℕ × Bool := (p.1.val, p.2)
  have ha := rMinusPrefixDartImage_boundary hτ hqMode i.val _
    (List.getElem?_eq_getElem i.isLt) true
  have hb := rMinusPrefixDartImage_boundary hτ hqMode (i.val + 1) _
    (List.getElem?_eq_getElem hi) false
  obtain ⟨s, t, hs, ht, hsa, htb, hgapH, hgapP, hperiod, _⟩ :=
    rMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i.val _ _
      (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)
  change (σ : _ → _)^[s] a = b at hsa
  change (σ : _ → _)^[t] b = a at htb
  change (σ : _ → _)^[s + t] a = a at hperiod
  have hv' : kmswLimitDartVertex w a = kmswLimitDartVertex w x := by
    change kmswLimitDartVertex w (EH (((Q).boundary i.val).1), true) =
      kmswLimitDartVertex w (p.1.val, p.2)
    rw [← ha]
    have hep := edge_endpoints_eq w p.1.isLt
    have hec := edge_endpoints_eq w (rMinusPrefixBoundaryDart w n (i, true)).1.isLt
    dsimp only [rMinusPrefixBoundaryDart] at hec
    change (if true then edgeEast w _ else edgeWest w _) =
      (if p.2 then edgeEast w _ else edgeWest w _)
    simpa only [stageEndpoint, rMinusPrefixBoundaryDart, hep.1, hep.2,
      hec.1, hec.2, ↓reduceIte] using hv.symm
  obtain ⟨j₀, hj₀⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) a x).mpr hv'
  rw [Equiv.Perm.coe_pow] at hj₀
  let j := j₀ % (s + t)
  have hjlt : j < s + t := Nat.mod_lt _ (by omega)
  have hj : (σ : _ → _)^[j] a = x :=
    (Function.IsPeriodicPt.iterate_mod_apply hperiod j₀).trans hj₀
  have hx : x = a ∨ x = b := by
    by_cases hj0 : j = 0
    · left
      simpa only [hj0, Function.iterate_zero_apply] using hj.symm
    by_cases hjs : j = s
    · right
      exact hj.symm.trans (hjs ▸ hsa)
    by_cases hjless : j < s
    · exact False.elim (hgapH j (by omega) hjless ⟨d, he.symm.trans hj.symm⟩)
    · apply False.elim
      apply hgapP (j - s) (by omega) (by omega)
      refine ⟨p, ?_⟩
      change x = (σ : _ → _)^[j - s] b
      rw [← hsa, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hj.symm
  rcases hx with hx | hx
  · left
    have hh := hx.trans ha.symm
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hh))
      (congrArg (fun z : ℕ × Bool => z.2) hh)
  · right
    have hh := hx.trans hb.symm
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hh))
      (congrArg (fun z : ℕ × Bool => z.2) hh)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate transports rotation
throughout each interior shared vertex star. -/
theorem rMinusCodeInitialAdjustedRotation_interior_star_side_rotation
    (i : Fin N) (hi : i.val + 1 < N) (d : RMinusCodeGluedDart F Q)
    (hv : kmswLimitDartVertex w (D d).val =
      stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true))) :
    (S).rotation (D d).val (D (rMinusCodeInitialAdjustedRotation w n q d)).val := by
  by_cases hk0 : k = 0
  · have ht : n = 0 := by rw [hk0, boundaryHitTime_zero]
    have heq : rMinusCodeInitialAdjustedRotation w n q = rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [heq]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 d
  have hneg : k < 0 := by omega
  by_cases hdP : d ∈ Set.range (rMinusCodePrefixDart F Q)
  · obtain ⟨p, rfl⟩ := hdP
    have hpv : stageEndpoint F p =
        stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) := by
      rw [rMinusCodeGluedDartEquiv_prefix] at hv
      have he := edge_endpoints_eq w p.1.isLt
      simpa only [kmswLimitDartVertex, stageEndpoint, he.1, he.2] using hv
    by_cases hpH : (p.1.val, p.2) ∈ Set.range
        (fun a : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH a.val.1, a.val.2))
    · obtain ⟨a, ha⟩ := hpH
      have hports := rMinus_interior_common_dart (H := H) hτ hqMode hfin i hi p a ha.symm hpv
      have horig : (S).rotation (D (rMinusCodePrefixDart F Q p)).val
          (D (rMinusCodeSpliceRotation w n q (rMinusCodePrefixDart F Q p))).val := by
        rcases hports with he | he
        · rw [he]
          exact rMinusCodeSpliceRotation_incoming_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk i hi
        · rw [he]
          exact rMinusCodeSpliceRotation_outgoing_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk i hi
      have hin := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
        hneg i (rMinusCodePrefixDart F Q p) hv
      have hvout : kmswLimitDartVertex w
          (D (rMinusCodeSpliceRotation w n q (rMinusCodePrefixDart F Q p))).val =
          stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) := by
        obtain ⟨r, _, he, _⟩ := horig
        exact (congrArg (kmswLimitDartVertex w) he).symm.trans
          ((rMinus_dart_vertex_iterate w (H.1 0) _ r).trans hv)
      have hout := rMinus_interior_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
        hneg i (rMinusCodeSpliceRotation w n q (rMinusCodePrefixDart F Q p)) hvout
      change (S).rotation (D (rMinusCodePrefixDart F Q p)).val
        (D (Equiv.swap _ _ (rMinusCodeSpliceRotation w n q
          (Equiv.swap _ _ (rMinusCodePrefixDart F Q p))))).val
      rw [hin, hout]
      exact horig
    · exact rMinusCodeInitialAdjustedRotation_interior_prefix_nonshared_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk i hi p hpH hpv
  · have hm := (D d).property
    have hm' := (Set.ext_iff.mp
      (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
    rcases hm' with ⟨p, hp⟩ | ⟨a, ha⟩
    · apply False.elim
      apply hdP
      refine ⟨p, (D).injective (Subtype.ext ?_)⟩
      rw [rMinusCodeGluedDartEquiv_prefix]
      exact hp
    · have had : rMinusCodeHattedDart F Q a = d := by
        apply (D).injective
        apply Subtype.ext
        rw [rMinusCodeGluedDartEquiv_hatted]
        exact ha
      rw [← had]
      apply rMinusCodeInitialAdjustedRotation_interior_hatted_nonshared_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk i hi a
      · rintro ⟨p, hp⟩
        apply hdP
        refine ⟨p, (D).injective (Subtype.ext ?_)⟩
        rw [rMinusCodeGluedDartEquiv_prefix]
        exact hp.trans ha
      · exact (congrArg (kmswLimitDartVertex w) ha).trans hv

include hfin hk in
/-- Helper toward Lemma 5.5: a hatted dart cannot meet an old prefix
vertex away from all shared interface ports. -/
theorem rMinus_off_interface_no_hatted (v : ℕ) (hvlt : v < (F).nextVertex)
    (haway : ∀ b : StageDart N,
      v ≠ stageEndpoint F (rMinusPrefixBoundaryDart w n b))
    (a : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    kmswLimitDartVertex w (EH a.val.1, a.val.2) ≠ v := by
  intro hv
  have hUL : (F).UL = [(F).active] := by
    by_cases hk0 : k = 0
    · rw [hk0, boundaryHitTime_zero]
      rfl
    · exact (leftHit_UL_singleton_and_west_endpoint w h (by omega)).1
  have hfront : ¬ UpperFrontierEndpoint F v := by
    rintro (⟨e, he, hw | heast⟩ | hnew)
    · rw [hUL, List.singleton_append] at he
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
      have hjlt := (List.getElem?_eq_some_iff.mp hj).1
      apply haway (⟨j, hjlt⟩, false)
      simpa only [rMinusPrefixBoundaryDart, stageEndpoint, Bool.false_eq_true,
        ↓reduceIte, (List.getElem?_eq_some_iff.mp hj).2] using hw.symm
    · rw [hUL, List.singleton_append] at he
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
      have hjlt := (List.getElem?_eq_some_iff.mp hj).1
      apply haway (⟨j, hjlt⟩, true)
      simpa only [rMinusPrefixBoundaryDart, stageEndpoint, ↓reduceIte,
        (List.getElem?_eq_some_iff.mp hj).2] using heast.symm
    · exact Nat.not_le_of_gt hvlt hnew
  let e := EH a.val.1
  by_cases he : e < (F).nextEdge
  · obtain ⟨j, hj, _⟩ := (rMinus_cross_edge_eq_iff hτ hqMode hfin
      ⟨e, he⟩ ⟨a.val.1, a.property⟩).mp rfl
    have hjlt := (List.getElem?_eq_some_iff.mp hj).1
    apply haway (⟨j, hjlt⟩, a.val.2)
    have hend := edge_endpoints_eq w he
    dsimp only [rMinusPrefixBoundaryDart, stageEndpoint]
    change v = if a.val.2 then (F).east _ else (F).west _
    rw [(List.getElem?_eq_some_iff.mp hj).2]
    simpa only [kmswLimitDartVertex, hend.1, hend.2] using hv.symm
  · let m := max n e
    have hnm : n ≤ m := le_max_left _ _
    have hem : e < (kmswStage w m).nextEdge :=
      (kmsw_edge_allocated_by_self w e).trans_le
        (kmswStage_nextEdge_mono w (le_max_right _ _))
    have hno := kmswStage_no_new_incidence_of_not_upperFrontier w n v hfront m hnm e hem
      (Nat.le_of_not_gt he)
    have hend := edge_endpoints_eq w hem
    change (if a.val.2 then edgeEast w e else edgeWest w e) = v at hv
    cases hb : a.val.2 with
    | false => exact hno.1 (by simpa only [hb, Bool.false_eq_true, ↓reduceIte, hend.1] using hv)
    | true => exact hno.2 (by simpa only [hb, ↓reduceIte, hend.2] using hv)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the initial adjustment fixes darts whose
vertex is away from the shared interface. -/
theorem rMinus_off_interface_initial_swap_fixed (d : RMinusCodeGluedDart F Q)
    (haway : ∀ b : StageDart N, kmswLimitDartVertex w (D d).val ≠
      stageEndpoint F (rMinusPrefixBoundaryDart w n b)) :
    let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
    let A := rMinusCodeBoundaryDart w n Q (i₀, false)
    let B := rMinusCodePrefixDart F Q
      (stageRot w n (rMinusPrefixBoundaryDart w n (i₀, false)))
    Equiv.swap A B d = d := by
  dsimp only
  let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let a := rMinusPrefixBoundaryDart w n (i₀, false)
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he
    apply haway (i₀, false)
    rw [he, rMinusCodeBoundaryDart_eq_prefix]
    exact hvpref a
  · intro he
    apply haway (i₀, false)
    rw [he, hvpref]
    exact ((stageRot_sameCycle_iff_endpoint_eq w n a (stageRot w n a)).mp ⟨1, rfl⟩).symm

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: outside the shared vertex interface, the
adjusted candidate is first return in the unique incident block. -/
theorem rMinusCodeInitialAdjustedRotation_off_interface_side_rotation
    (d : RMinusCodeGluedDart F Q)
    (haway : ∀ b : StageDart N, kmswLimitDartVertex w (D d).val ≠
      stageEndpoint F (rMinusPrefixBoundaryDart w n b)) :
    (S).rotation (D d).val (D (rMinusCodeInitialAdjustedRotation w n q d)).val := by
  let σ := kmswInfRot w (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun a => (EH a.val.1, a.val.2)
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  have hprefix_bound (p : StageDart (F).nextEdge) : stageEndpoint F p < (F).nextVertex := by
    have he := kmswStage_endpoints_lt_nextVertex w n p.1.val p.1.isLt
    cases hb : p.2 with
    | false => simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using he.1
    | true => simpa only [stageEndpoint, hb, ↓reduceIte] using he.2
  have horig : (S).rotation (D d).val (D (rMinusCodeSpliceRotation w n q d)).val := by
    by_cases hdP : d ∈ Set.range (rMinusCodePrefixDart F Q)
    · obtain ⟨p, rfl⟩ := hdP
      have hnoH (a : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
          kmswLimitDartVertex w (J a) ≠ stageEndpoint F p :=
        rMinus_off_interface_no_hatted hτ hqMode hfin hk _ (hprefix_bound p)
          (by intro b; exact (hvpref p) ▸ haway b) a
      have hrotv : stageEndpoint F (stageRot w n p) = stageEndpoint F p :=
        ((stageRot_sameCycle_iff_endpoint_eq w n p (stageRot w n p)).mp ⟨1, rfl⟩).symm
      have hyH : rMinusCodePrefixDart F Q (stageRot w n p) ∉
          Set.range (rMinusCodeHattedDart F Q) := by
        rintro ⟨a, ha⟩
        apply hnoH a
        have he := congrArg (fun z => kmswLimitDartVertex w (D z).val) ha
        rw [rMinusCodeGluedDartEquiv_hatted, hvpref] at he
        exact he.trans hrotv
      have hyC : rMinusCodePrefixDart F Q (stageRot w n p) ∉
          Set.range (rMinusCodeBoundaryDart w n Q) := by
        rintro ⟨⟨j, b⟩, he⟩
        apply hyH
        rw [← he, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
        exact ⟨_, rfl⟩
      have hP : (stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p) =
          rMinusCodePrefixDart F Q (stageRot w n p) :=
        (stageRot w n).extendDomain_apply_image Pemb p
      change (S).rotation (D (rMinusCodePrefixDart F Q p)).val
        (D ((rMinusHattedRotation _ q).extendDomain Hemb
          ((rMinusBoundaryCornerPerm N).extendDomain Cemb
            ((stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p))))).val
      rw [hP, Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hyC,
        Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hyH,
        rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
      obtain ⟨r, hr, hre, hrgap⟩ := rMinusPrefixDartImage_firstReturn (H := H) p
      refine ⟨r, hr, hre, ?_⟩
      intro l hl hlr hm
      have hm' := (Set.ext_iff.mp
        (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
      rcases hm' with hmP | ⟨a, ha⟩
      · exact hrgap l hl hlr hmP
      · apply hnoH a
        exact (congrArg (kmswLimitDartVertex w) ha).trans
          ((rMinus_dart_vertex_iterate w (H.1 0) _ l).trans (by
            rw [← rMinusCodeGluedDartEquiv_prefix]; exact hvpref p))
    · have hm' := (Set.ext_iff.mp
        (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp (D d).property
      have hnotP : (D d).val ∉ Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
        rintro ⟨p, hp⟩
        apply hdP
        refine ⟨p, (D).injective (Subtype.ext ?_)⟩
        rw [rMinusCodeGluedDartEquiv_prefix]
        exact hp
      obtain ⟨a, ha⟩ := hm'.resolve_left hnotP
      have had : rMinusCodeHattedDart F Q a = d := by
        apply (D).injective
        apply Subtype.ext
        rw [rMinusCodeGluedDartEquiv_hatted]
        exact ha
      have hnotC : d ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
        rintro ⟨b, hb⟩
        exact hdP ⟨rMinusPrefixBoundaryDart w n b, hb⟩
      change (S).rotation (D d).val
        (D ((rMinusHattedRotation _ q).extendDomain Hemb
          ((rMinusBoundaryCornerPerm N).extendDomain Cemb
            ((stageRot w n).extendDomain Pemb d)))).val
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hdP,
        Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnotC, ← had]
      have hH : (rMinusHattedRotation _ q).extendDomain Hemb (rMinusCodeHattedDart F Q a) =
          rMinusCodeHattedDart F Q (rMinusHattedRotation _ q a) :=
        (rMinusHattedRotation _ q).extendDomain_apply_image Hemb a
      rw [hH, rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_hatted]
      obtain ⟨r, hr, hre, hrgap⟩ := rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin a
      refine ⟨r, hr, hre, ?_⟩
      intro l hl hlr hm
      have hm' := (Set.ext_iff.mp
        (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
      rcases hm' with ⟨p, hp⟩ | hmH
      · have hvp : stageEndpoint F p = kmswLimitDartVertex w (D d).val := by
          have hvp := congrArg (kmswLimitDartVertex w) hp
          have hpp : kmswLimitDartVertex w (rMinusPrefixDartImage (h := h) p) =
              stageEndpoint F p := by
            simpa only [rMinusCodeGluedDartEquiv_prefix, rMinusPrefixDartImage] using hvpref p
          exact hpp.symm.trans (hvp.trans
            ((rMinus_dart_vertex_iterate w (H.1 0) _ l).trans
              (congrArg (kmswLimitDartVertex w) ha)))
        exact rMinus_off_interface_no_hatted hτ hqMode hfin hk _
          (hvp ▸ hprefix_bound p) haway a
            (congrArg (kmswLimitDartVertex w) ha)
      · exact hrgap l hl hlr hmH
  have hin := rMinus_off_interface_initial_swap_fixed
    hτ hp P hqMode Tpath hfin hleft hk d haway
  have hvout : kmswLimitDartVertex w (D (rMinusCodeSpliceRotation w n q d)).val =
      kmswLimitDartVertex w (D d).val := by
    obtain ⟨r, _, he, _⟩ := horig
    exact (congrArg (kmswLimitDartVertex w) he).symm.trans
      (rMinus_dart_vertex_iterate w (H.1 0) _ r)
  have hout := rMinus_off_interface_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    (rMinusCodeSpliceRotation w n q d) (by intro b; exact hvout ▸ haway b)
  change (S).rotation (D d).val
    (D (Equiv.swap _ _ (rMinusCodeSpliceRotation w n q (Equiv.swap _ _ d)))).val
  rw [hin, hout]
  exact horig

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate has the actual
geometric successor at every glued code dart, for every nonpositive index. -/
theorem rMinusCodeInitialAdjustedRotation_side_rotation
    (d : RMinusCodeGluedDart F Q) :
    (S).rotation (D d).val (D (rMinusCodeInitialAdjustedRotation w n q d)).val := by
  by_cases hex : ∃ b : StageDart N, kmswLimitDartVertex w (D d).val =
      stageEndpoint F (rMinusPrefixBoundaryDart w n b)
  · obtain ⟨⟨i, bit⟩, hv⟩ := hex
    cases bit with
    | true =>
      by_cases hi : i.val + 1 < N
      · exact rMinusCodeInitialAdjustedRotation_interior_star_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk i hi d hv
      · have he : i = (⟨N - 1, by simp only [List.length_cons]; omega⟩ : Fin N) := by
          apply Fin.ext
          dsimp only
          have hibound := i.isLt
          omega
        apply rMinusCodeInitialAdjustedRotation_terminal_star_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk d
        simpa only [he] using hv
    | false =>
      by_cases hi0 : i.val = 0
      · apply rMinusCodeInitialAdjustedRotation_initial_star_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk d
        simpa only [rMinusPrefixBoundaryDart, stageEndpoint, Bool.false_eq_true,
          ↓reduceIte, hi0, List.getElem_cons_zero, act] using hv
      · let j : Fin N := ⟨i.val - 1, by omega⟩
        have hj : j.val + 1 = i.val := by dsimp only [j]; omega
        have hjlt : j.val + 1 < N := by rw [hj]; exact i.isLt
        have heq : (⟨j.val + 1, hjlt⟩ : Fin N) = i := Fin.ext hj
        have hcorner := rMinusPrefixRotation_boundary_indexed (W := W) (h := h) (k := k) j hjlt
        rw [heq] at hcorner
        have hvport : stageEndpoint F (rMinusPrefixBoundaryDart w n (i, false)) =
            stageEndpoint F (rMinusPrefixBoundaryDart w n (j, true)) := by
          have hh := (stageRot_sameCycle_iff_endpoint_eq w n
            (rMinusPrefixBoundaryDart w n (i, false))
            (stageRot w n (rMinusPrefixBoundaryDart w n (i, false)))).mp ⟨1, rfl⟩
          rw [hcorner] at hh
          exact hh
        exact rMinusCodeInitialAdjustedRotation_interior_star_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk j hjlt d (hv.trans hvport)
  · apply rMinusCodeInitialAdjustedRotation_off_interface_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk d
    intro b hb
    exact hex ⟨b, hb⟩

end InteriorGeometry

/-- Helper toward Lemma 5.5: the adjusted code rotation agrees, in both
directions and on every cell branch, with geometric right-side rotation. -/
theorem rMinusGluedCellEquiv_rotation_iff
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
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let E := rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    let R := Equiv.permCongr E
      (rMinusCodeInitialAdjustedRotation (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k) q)
    (match u, v with
      | .inr d, .inr e => R d = e
      | _, _ => False) ↔
      geometricSideRelation (m0GeodesicSide hp P .right) .rotation
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  dsimp only
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let E := rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let G := rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  let R := rMinusCodeInitialAdjustedRotation (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) q
  cases u with
  | inl u => cases v <;> rfl
  | inr u =>
    obtain ⟨d, rfl⟩ := E.surjective u
    have hr := rMinusCodeInitialAdjustedRotation_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk d
    cases v with
    | inl v => rfl
    | inr e =>
      change Equiv.permCongr E R (E d) = e ↔
        (m0GeodesicSide hp P .right).rotation (G (E d)).val (G e).val
      have hR : Equiv.permCongr E R (E d) = E (R d) := by
        simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rw [hR, rMinusCodeToGluedDartEquiv_equiv]
      constructor
      · intro he
        rw [← he, rMinusCodeToGluedDartEquiv_equiv]
        exact hr
      · intro he
        apply G.injective
        rw [rMinusCodeToGluedDartEquiv_equiv]
        apply Subtype.ext
        obtain ⟨r, hrpos, hre, hrgap⟩ := hr
        obtain ⟨s, hspos, hse, hsgap⟩ := he
        have hrs : r = s := by
          apply Nat.le_antisymm
          · by_contra hn
            exact hrgap s hspos (by omega) (hse.symm ▸ (G e).property)
          · by_contra hn
            exact hsgap r hrpos (by omega) (hre.symm ▸ (D (R d)).property)
        exact hre.symm.trans (hrs ▸ hse)

end DirectedDistances.PaperProofs.Section5
