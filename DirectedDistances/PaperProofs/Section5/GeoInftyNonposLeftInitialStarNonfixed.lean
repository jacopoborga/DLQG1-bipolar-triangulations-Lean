/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftInitialStarTransport

/-! nonfixed initial-star rotation calculations. The primed predecessor returns
to the hatted successor with both block gaps empty. All other initial block
returns and their candidate outputs are identified, giving transport on the
entire initial star. Whole-side transport and Lemma 5.5 remain separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "z" => boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "B" => primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin
local notation "Prot" => kmswInfRot (Prod.fst (LMinusSidePresentation.code rL))
  (lMinus_primed_observation_finiteIncidence hτ hfin)
local notation "C" => lMinusCodeBoundaryDart rL qL (0, false)
local notation "A" => lMinusCodeInitialAdjustedRotation rL qL
  (lMinus_primed_observation_finiteIncidence hτ hfin)
local notation "R" => lMinusCodeInitialSplicedRotation rL qL
  (lMinus_primed_observation_finiteIncidence hτ hfin)

include H hfin hk in
/-- Helper toward Lemma 5.5: every retained noninitial hatted source dart
has an entirely outgoing ambient rotation arc to the shared initial dart. -/
theorem lMinus_initial_hatted_outgoing_arc
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0)
    (hne : d.val ≠ (((Q).boundary 0).1, false)) :
    RotationArc (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswPresentOutgoingDart (shiftedStream W 0))
      (EH d.val.1, d.val.2) (EH ((Q).boundary 0).1, false) := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  have hneJ : J d ≠ J c := by
    intro he
    change (EH d.val.1, d.val.2) = (EH c.val.1, c.val.2) at he
    have hb := congrArg (fun p : ℕ × Bool => p.2) he
    have he' := congrArg (fun p : ℕ × Bool => p.1) he
    apply hne
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ he') hb
  have hc0 : kmswLimitDartVertex z c.val = 0 :=
    (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩
  have hod := lMinus_initial_hatted_outgoing hτ hqMode hk d hv
  have hoc := lMinus_initial_hatted_outgoing hτ hqMode hk c hc0
  have hvd : kmswDartEndpoint (shiftedStream W 0) (J d) = VH 0 :=
    (lMinus_hatted_dart_endpoint hτ d.val).trans (congrArg VH hv)
  have hvc : kmswDartEndpoint (shiftedStream W 0) (J c) = VH 0 :=
    (lMinus_hatted_dart_endpoint hτ c.val).trans (congrArg VH hc0)
  have hw : edgeWest (shiftedStream W 0) (J d).1 =
      edgeWest (shiftedStream W 0) (J c).1 := by
    change (if (J d).2 then _ else _) = _ at hvd
    change (if (J c).2 then _ else _) = _ at hvc
    rw [hod.1] at hvd
    rw [hoc.1] at hvc
    exact hvd.trans hvc.symm
  have hd : J d = ((J d).1, false) := Prod.ext rfl hod.1
  have hc : J c = ((J c).1, false) := Prod.ext rfl hoc.1
  rcases kmswInfRot_outgoing_interval_all (shiftedStream W 0) (H.1 0)
      (J d).1 (J c).1 hw hod.2 hoc.2 with hf | hb
  · simpa only [RotationArc, σ, kmswPresentOutgoingDart, ← hd, ← hc] using hf
  · have hbad : RotationArc σ (kmswPresentOutgoingDart (shiftedStream W 0))
        (J c) (J d) := by
      simpa only [RotationArc, σ, kmswPresentOutgoingDart, ← hd, ← hc] using hb
    obtain ⟨m, hm, hall⟩ := hbad
    simp only [Equiv.Perm.coe_pow] at hm hall
    have hmpos : 0 < m := by
      by_contra hn
      have hz : m = 0 := by omega
      rw [hz, Function.iterate_zero_apply] at hm
      exact hneJ hm.symm
    let FJ : (ℕ × Bool) → ℕ × Bool :=
      fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
    let cU : ℕ × Bool :=
      (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false)
    have hce : FJ cU = J c := by
      change (EH (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
        (EH (kmswLeftBoundaryEdge z 0), false)
      rw [boundaryGluing_decoded_stream W h k hτ]
    obtain ⟨t, ht, hte, hgap⟩ := lMinus_future_firstReturn (H := H) hfin cU
    change (σ : _ → _)^[t] (FJ cU) = FJ (kmswInfRot U hfin cU) at hte
    rw [hce] at hte
    have hnout : ¬ kmswPresentOutgoingDart (shiftedStream W 0)
        (FJ (kmswInfRot U hfin cU)) := by
      rw [show kmswInfRot U hfin cU = primedLimitDartMap U hτ (0, true) from
        lMinus_initial_future_rotation hτ hfin]
      intro ho
      have hh : true = false := by
        simpa only [FJ, primedLimitDartMap, primedLimitSideFlip_zero,
          Bool.xor_false] using ho.1
      exact Bool.noConfusion hh
    by_cases hmt : m < t
    · apply False.elim
      apply hgap m hmpos hmt
      refine ⟨(hatLimitEdgeMap U hτ d.val.1, d.val.2), ?_⟩
      change J d = (σ : _ → _)^[m] (FJ cU)
      rw [hce]
      exact hm.symm
    · exact (hnout (hte ▸ hall t (by omega))).elim

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: in the nonfixed case the primed predecessor
first returns to the hatted successor, avoiding both retained blocks. -/
theorem lMinus_initial_adjusted_predecessor_open_gap_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    if Hrot c = c then True else
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) = J (Hrot c) ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
            (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) ∉
              Set.range (lMinusPrimedDartImage hτ) ∧
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
            (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) ∉ Set.range J := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let p := (Prot).symm (B 0, true)
  let b := lMinusPrimedDartImage hτ p
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    trivial
  · rw [ite_eq_right hfix]
    have hc : lMinusPrimedDartImage hτ (B 0, true) = J c := by
      rw [lMinusPrimedDartImage_boundary hτ hfin]
      change (EH (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
        (EH (kmswLeftBoundaryEdge z 0), false)
      rw [boundaryGluing_decoded_stream W h k hτ]
    have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) := by
      congr 1
      exact lMinus_primed_observation_code hτ
    obtain ⟨n, hn, hnc, hngap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
    rw [← hrot, Equiv.apply_symm_apply, hc] at hnc
    change (σ : _ → _)^[n] b = J c at hnc
    change ∀ j : ℕ, 0 < j → j < n →
      (σ : _ → _)^[j] b ∉ Set.range (lMinusPrimedDartImage hτ) at hngap
    have hbne : b ≠ J c := by
      intro he
      have hecode : lMinusCodePrimedDart rL Q p = C := by
        apply (D).injective
        apply Subtype.ext
        change (D (lMinusCodePrimedDart rL Q p)).val =
          (D (lMinusCodeHattedDart rL Q c)).val
        rw [lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted]
        exact he
      have hpre := lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
        hτ hp P hqMode Tpath hfin hleft hk
      have hAC : A C = C := by
        have hh : (A).symm C = C := hpre.trans hecode
        exact (congrArg A hh.symm).trans (Equiv.apply_symm_apply A C)
      rw [lMinusCodeInitialAdjustedRotation_initial hτ hp P hqMode Tpath hfin hleft hk] at hAC
      exact lMinus_initial_primed_root_ne_boundary hτ hp P hqMode Tpath hfin hleft hk hAC
    have hbV : kmswDartEndpoint (shiftedStream W 0) b = VH 0 := by
      have hep := lMinus_primed_rotation_endpoint (H := H) (longest := longest) hτ hfin p
      rw [Equiv.apply_symm_apply, hc] at hep
      exact hep.symm.trans ((lMinus_hatted_dart_endpoint hτ c.val).trans
        (congrArg VH ((lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩)))
    have hbout : ¬ kmswPresentOutgoingDart (shiftedStream W 0) b := by
      intro ho
      exact hbne (lMinus_initial_primed_outgoing_unique hτ hqMode hfin hk p ho hbV)
    have hv : kmswLimitDartVertex z (Hrot c).val = 0 := by
      have hh := drawingFirstReturn_sameVertex
        (monotoneFamilyDrawing z
          (sourceAncestor_finite_incidence _ renewalTime renewalTime_positiveSuccessTime qL)
          (monotone_family_all z)) {a : ℕ × Bool | a.1 ∈ (Q).edges} c
      change kmswLimitDartVertex z (Hrot c).val = kmswLimitDartVertex z c.val at hh
      exact hh.trans ((lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩)
    have hne : (Hrot c).val ≠ (((Q).boundary 0).1, false) := by
      intro he
      exact hfix (Subtype.ext he)
    obtain ⟨m, hmc, hall⟩ := lMinus_initial_hatted_outgoing_arc (H := H)
      hτ hqMode hfin hk (Hrot c) hv hne
    obtain ⟨t, ht, htd, htgap⟩ := lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin c
    dsimp only at htd htgap
    change (σ : _ → _)^[t] (J c) = J (Hrot c) at htd
    change (σ ^ m) (J (Hrot c)) = J c at hmc
    change ∀ j : ℕ, j ≤ m → kmswPresentOutgoingDart (shiftedStream W 0)
      ((σ ^ j) (J (Hrot c))) at hall
    simp only [← Equiv.Perm.coe_pow] at hnc hngap htd htgap ⊢
    have hmn : m < n := by
      by_contra hh
      have hnm : n ≤ m := by omega
      have he : b = (σ ^ (m - n)) (J (Hrot c)) := by
        apply (σ ^ n).injective
        rw [hnc, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hnm, hmc]
      exact hbout (he ▸ hall (m - n) (by omega))
    have hqc : (σ ^ (n - m)) b = J (Hrot c) := by
      apply (σ ^ m).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hmn.le, hnc, hmc]
    have hcycle : (σ ^ (t + m)) (J c) = J c := by
      rw [show t + m = m + t from Nat.add_comm t m,
        pow_add, Equiv.Perm.mul_apply, htd, hmc]
    have hbcycle : (σ ^ (t + m)) b = b := by
      apply (σ ^ n).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm n (t + m), pow_add,
        Equiv.Perm.mul_apply, hnc, hcycle]
    have hnle : n ≤ t + m := by
      by_contra hh
      apply hngap (t + m) (by omega) (by omega)
      rw [hbcycle]
      exact ⟨p, rfl⟩
    have hcn : 0 < t + m - n := by
      by_contra hh
      have he : t + m = n := by omega
      rw [he, hnc] at hbcycle
      exact hbne hbcycle.symm
    have hcb : (σ ^ (t + m - n)) (J c) = b := by
      rw [← hnc, ← Equiv.Perm.mul_apply, ← pow_add,
        Nat.sub_add_cancel hnle, hbcycle]
    refine ⟨n - m, by omega, hqc, ?_⟩
    intro j hj hjq
    refine ⟨hngap j hj (by omega), ?_⟩
    have he : (σ ^ j) b = (σ ^ (t + m - n + j)) (J c) := by
      rw [← hcb, pow_add, Equiv.Perm.mul_apply]
      exact (Commute.pow_pow (Commute.refl σ) j (t + m - n)).eq
        |> congrArg (fun f => f (J c))
    rw [he]
    exact htgap (t + m - n + j) (by omega) (by omega)

/-- Helper toward Lemma 5.5: the adjusted predecessor has the geometric
first return in both branches, with the nonfixed open gaps proved above. -/
theorem lMinusCodeInitialSplicedRotation_adjusted_predecessor_side_rotation :
    (S).rotation (D ((A).symm C)).val (D (R ((A).symm C))).val := by
  apply (lMinus_initial_adjusted_predecessor_geometric_reduction
    hτ hp P hqMode Tpath hfin hleft hk).mpr
  exact lMinus_initial_adjusted_predecessor_open_gap_cases
    hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: an initial primed return other than the
adjusted predecessor avoids retained hatted darts in its open interval. -/
theorem lMinus_initial_primed_other_side_rotation (p : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodePrimedDart rL Q p)).val = VH 0)
    (hb : lMinusCodePrimedDart rL Q p ≠ (A).symm C) :
    (S).rotation (lMinusPrimedDartImage hτ p) (lMinusPrimedDartImage hτ (Prot p)) := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  have hc : J c ∈ Set.range (lMinusPrimedDartImage hτ) := by
    refine ⟨(B 0, true), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin]
    change (EH (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
      (EH (kmswLeftBoundaryEdge z 0), false)
    rw [boundaryGluing_decoded_stream W h k hτ]
  have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) := by
    congr 1
    exact lMinus_primed_observation_code hτ
  obtain ⟨n, hn, he, hgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  rw [← hrot] at he
  refine ⟨n, hn, he, ?_⟩
  intro j hj hjn hs
  rcases (Set.ext_iff.mp (lMinus_side_darts_union
    hτ hp P hqMode Tpath hfin hleft hk) _).mp hs with hP | ⟨d, hd⟩
  · exact hgap j hj hjn hP
  · change J d = (σ : _ → _)^[j] (lMinusPrimedDartImage hτ p) at hd
    rw [← Equiv.Perm.coe_pow] at hd
    have hvj : kmswLimitDartVertex (shiftedStream W 0)
        ((σ : _ → _)^[j] (lMinusPrimedDartImage hτ p)) = VH 0 := by
      have hh := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0) (H.1 0)
        (lMinusPrimedDartImage hτ p)
        ((σ : _ → _)^[j] (lMinusPrimedDartImage hτ p))).mp
        ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
      rw [lMinusCodeGluedDartEquiv_primed] at hv
      exact hh.symm.trans hv
    have hvd : kmswLimitDartVertex z d.val = 0 := by
      apply boundaryGluingHatVertexMap_injective W h k hτ
      exact (lMinus_hatted_dart_endpoint hτ d.val).symm.trans
        ((congrArg (kmswLimitDartVertex (shiftedStream W 0)) hd).trans
          (by simpa only [Equiv.Perm.coe_pow] using hvj))
    have hdne : d.val ≠ (((Q).boundary 0).1, false) := by
      intro hh
      have hdc : d = c := Subtype.ext hh
      apply hgap j hj hjn
      change (σ : _ → _)^[j] (lMinusPrimedDartImage hτ p) ∈ _
      rw [← Equiv.Perm.coe_pow, ← hd, hdc]
      exact hc
    obtain ⟨m, hmc, hall⟩ := lMinus_initial_hatted_outgoing_arc (H := H)
      hτ hqMode hfin hk d hvd hdne
    change (σ ^ m) (J d) = J c at hmc
    change ∀ i : ℕ, i ≤ m → kmswPresentOutgoingDart (shiftedStream W 0)
      ((σ ^ i) (J d)) at hall
    have htotal : (σ ^ (j + m)) (lMinusPrimedDartImage hτ p) = J c := by
      rw [Nat.add_comm j m, pow_add, Equiv.Perm.mul_apply]
      rw [← hd]
      exact hmc
    have hnle : n ≤ j + m := by
      by_contra hh
      apply hgap (j + m) (by omega) (by omega)
      change (σ : _ → _)^[j + m] (lMinusPrimedDartImage hτ p) ∈ _
      rw [← Equiv.Perm.coe_pow, htotal]
      exact hc
    have hnext : (σ ^ (n - j)) (J d) = lMinusPrimedDartImage hτ (Prot p) := by
      rw [hd, ← Equiv.Perm.mul_apply, ← pow_add,
        Nat.sub_add_cancel hjn.le]
      simpa only [Equiv.Perm.coe_pow] using he
    have hout : kmswPresentOutgoingDart (shiftedStream W 0)
        (lMinusPrimedDartImage hτ (Prot p)) :=
      hnext ▸ hall (n - j) (by omega)
    have hvnext := lMinus_primed_rotation_endpoint (H := H) (longest := longest) hτ hfin p
    rw [lMinusCodeGluedDartEquiv_primed] at hv
    have hnextc := lMinus_initial_primed_outgoing_unique hτ hqMode hfin hk
      (Prot p) hout (hvnext.trans hv)
    have hcode : lMinusCodePrimedDart rL Q (Prot p) = C := by
      apply (D).injective
      apply Subtype.ext
      change (D (lMinusCodePrimedDart rL Q (Prot p))).val =
        (D (lMinusCodeHattedDart rL Q c)).val
      rw [lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted]
      exact hnextc
    rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk] at hcode
    have hpe : p = (Prot).symm (B 0, true) := by
      have hh := (lMinusCodePrimedDart_injective rL qL) hcode
      exact (congrArg (Prot).symm hh).symm.trans (Equiv.symm_apply_apply Prot p) |>.symm
    apply hb
    rw [lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
      hτ hp P hqMode Tpath hfin hleft hk, hpe]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every noninitial retained hatted source
return avoids the primed block, hence is first return to the glued side. -/
theorem lMinus_initial_hatted_other_side_rotation
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0)
    (hne : d.val ≠ (((Q).boundary 0).1, false)) :
    (S).rotation (EH d.val.1, d.val.2)
      (EH ((lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d).val).1,
        ((lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d).val).2) := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  by_cases hpred : d = Hrot.symm c
  · have hnon : Hrot c ≠ c := by
      intro hfix
      have hcfix : Hrot.symm c = c :=
        (congrArg Hrot.symm hfix).symm.trans (Equiv.symm_apply_apply Hrot c)
      exact hne (congrArg Subtype.val (hpred.trans hcfix))
    have hg := lMinus_initial_predecessor_open_gap_cases
      hτ hp P hqMode Tpath hfin hleft hk
    dsimp only at hg
    rw [ite_eq_right hnon] at hg
    obtain ⟨n, hn, he, hgap⟩ := hg
    change (S).rotation (J d) (J (Hrot d))
    rw [hpred, Equiv.apply_symm_apply]
    refine ⟨n, hn, he, ?_⟩
    intro j hj hjn hs
    rcases (Set.ext_iff.mp (lMinus_side_darts_union
      hτ hp P hqMode Tpath hfin hleft hk) _).mp hs with hP | hH
    · exact (hgap j hj hjn).1 hP
    · exact (hgap j hj hjn).2 hH
  obtain ⟨m, hm, hall⟩ := lMinus_initial_hatted_outgoing_arc (H := H)
    hτ hqMode hfin hk d hv hne
  obtain ⟨n, hn, he, hgap⟩ := lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  dsimp only at he hgap
  change (σ ^ m) (J d) = J c at hm
  change ∀ j : ℕ, j ≤ m → kmswPresentOutgoingDart (shiftedStream W 0)
    ((σ ^ j) (J d)) at hall
  have hmpos : 0 < m := by
    by_contra hh
    have hz : m = 0 := by omega
    rw [hz, pow_zero, Equiv.Perm.one_apply] at hm
    change (EH d.val.1, d.val.2) = (EH c.val.1, c.val.2) at hm
    have he' := congrArg (fun p : ℕ × Bool => p.1) hm
    have hb' := congrArg (fun p : ℕ × Bool => p.2) hm
    apply hne
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ he') hb'
  have hnle : n ≤ m := by
    by_contra hh
    apply hgap m hmpos (by omega)
    refine ⟨c, ?_⟩
    simpa only [Equiv.Perm.coe_pow] using hm.symm
  refine ⟨n, hn, he, ?_⟩
  intro j hj hjn hs
  rcases (Set.ext_iff.mp (lMinus_side_darts_union
    hτ hp P hqMode Tpath hfin hleft hk) _).mp hs with ⟨p, hp'⟩ | hH
  · have hout := hall j (by omega)
    simp only [Equiv.Perm.coe_pow] at hout
    have hvj : kmswDartEndpoint (shiftedStream W 0)
        ((σ : _ → _)^[j] (J d)) = VH 0 := by
      have hh := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0) (H.1 0)
        (J d) ((σ : _ → _)^[j] (J d))).mp
        ⟨j, by simp only [Equiv.Perm.coe_pow]; rfl⟩
      exact hh.symm.trans ((lMinus_hatted_dart_endpoint hτ d.val).trans (congrArg VH hv))
    have hpc := lMinus_initial_primed_outgoing_unique hτ hqMode hfin hk p
      (hp'.symm ▸ hout) (hp'.symm ▸ hvj)
    apply hgap j hj hjn
    exact ⟨c, hpc.symm.trans hp'⟩
  · exact hgap j hj hjn hH

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: away from the shared initial port and its
hatted predecessor, the spliced candidate retains the hatted block output. -/
theorem lMinusCodeInitialSplicedRotation_initial_hatted_other
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0)
    (hc : lMinusCodeHattedDart rL Q d ≠ C)
    (ha : lMinusCodeHattedDart rL Q d ≠ lMinusCodeHattedDart rL Q
      ((lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL).symm
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)) :
    R (lMinusCodeHattedDart rL Q d) = lMinusCodeHattedDart rL Q
      (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d) := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
    (lMinusCodeHattedDart_injective rL qL)
  let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
    (lMinusCodeBoundaryDart_injective rL qL)
  let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
    (lMinusCodePrimedDart_injective rL qL)
  have hnP : lMinusCodeHattedDart rL Q d ∉ Set.range (lMinusCodePrimedDart rL Q) := by
    intro hm
    have he := (lMinus_initial_hatted_star_mem_primed_iff
      hτ hp P hqMode Tpath hfin hleft hk d hv).mp hm
    exact hc (congrArg (lMinusCodeHattedDart rL Q) (Subtype.ext he))
  have hb : lMinusCodeHattedDart rL Q d ≠ (A).symm C := by
    intro he
    apply hnP
    rw [he, lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
      hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  have ha' : lMinusCodeHattedDart rL Q d ≠ (Hrot.extendDomain Hemb).symm C := by
    rw [lMinusCodeHattedRotation_initial_predecessor]
    exact ha
  rw [lMinusCodeInitialSplicedRotation_apply_of_ne rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin) _ ha' hb,
    lMinusCodeInitialAdjustedRotation_apply_of_ne rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) _ hc ha']
  have hvnext : kmswLimitDartVertex z (Hrot d).val = 0 := by
    have hh := drawingFirstReturn_sameVertex
      (monotoneFamilyDrawing z
        (sourceAncestor_finite_incidence _ renewalTime renewalTime_positiveSuccessTime qL)
        (monotone_family_all z)) {a : ℕ × Bool | a.1 ∈ (Q).edges} d
    exact hh.trans hv
  have hnPnext : lMinusCodeHattedDart rL Q (Hrot d) ∉
      Set.range (lMinusCodePrimedDart rL Q) := by
    intro hm
    have he := (lMinus_initial_hatted_star_mem_primed_iff
      hτ hp P hqMode Tpath hfin hleft hk (Hrot d) hvnext).mp hm
    have hh : Hrot d = c := Subtype.ext he
    apply ha
    apply congrArg (lMinusCodeHattedDart rL Q)
    exact (congrArg Hrot.symm hh).symm.trans (Equiv.symm_apply_apply Hrot d) |>.symm
  have hnCnext : lMinusCodeHattedDart rL Q (Hrot d) ∉
      Set.range (lMinusCodeBoundaryDart rL qL) := by
    rintro ⟨⟨i, b⟩, he⟩
    apply hnPnext
    rw [← he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  change (Prot).extendDomain Pemb (lMinusBoundaryCornerPerm.extendDomain Cemb
    (Hrot.extendDomain Hemb (lMinusCodeHattedDart rL Q d))) = _
  have hH : Hrot.extendDomain Hemb (lMinusCodeHattedDart rL Q d) =
      lMinusCodeHattedDart rL Q (Hrot d) := Hrot.extendDomain_apply_image Hemb d
  rw [hH,
    Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnCnext,
    Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hnPnext]

/-- Helper toward Lemma 5.5: the spliced code permutation transports the
entire initial geometric star, for every target vertex or dart cell. -/
theorem lMinus_initial_star_spliced_transport :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .left q
    let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
      (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
    ∀ d : LMinusCodeGluedDart r M,
      kmswLimitDartVertex (shiftedStream W 0)
          (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
        boundaryGluingHatVertexMap W h k hτ 0 →
      ∀ v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode),
        let u := Sum.inr
          (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d)
        lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
          geometricSideRelation (m0GeodesicSide hp P .left) .rotation
            (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
            (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  apply (lMinusGluedCellEquiv_rotation_initial_star_spliced_reduction
    hτ hp P hqMode Tpath hfin hleft hk).mpr
  dsimp only
  intro d hv hfix hc ha
  obtain ⟨p, rfl⟩ | ⟨a, rfl⟩ := lMinusCodeGluedDart_mem_block hqMode d
  · by_cases hb : lMinusCodePrimedDart rL Q p = (A).symm C
    · rw [hb]
      exact lMinusCodeInitialSplicedRotation_adjusted_predecessor_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk
    · rw [lMinusCodeInitialSplicedRotation_initial_primed_other
        hτ hp P hqMode Tpath hfin hleft hk p hv hc hb,
        lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_primed]
      exact lMinus_initial_primed_other_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk p hv hb
  · have hva : kmswLimitDartVertex z a.val = 0 := by
      apply boundaryGluingHatVertexMap_injective W h k hτ
      rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ] at hv
      exact hv
    have hne : a.val ≠ (((Q).boundary 0).1, false) := by
      intro he
      exact hc (congrArg (lMinusCodeHattedDart rL Q) (Subtype.ext he))
    rw [lMinusCodeInitialSplicedRotation_initial_hatted_other
        hτ hp P hqMode Tpath hfin hleft hk a hva hc ha,
      lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_hatted]
    exact lMinus_initial_hatted_other_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk a hva hne

end GeometricGluing

/-- Helper toward Lemma 5.5: exact all-target rotation transport on the
initial geometric star for the spliced candidate, in both fixed-point cases. -/
theorem lMinusGluedCellEquiv_rotation_initial_star_spliced_iff
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
    (hk : k ≤ 0) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .left q
    let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
      (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
    ∀ d : LMinusCodeGluedDart r M,
      kmswLimitDartVertex (shiftedStream W 0)
          (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
        boundaryGluingHatVertexMap W h k hτ 0 →
      ∀ v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode),
        let u := Sum.inr
          (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d)
        lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
          geometricSideRelation (m0GeodesicSide hp P .left) .rotation
            (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
            (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  exact lMinus_initial_star_spliced_transport hτ hp P hqMode Tpath hfin hleft hk

end DirectedDistances.PaperProofs.Section5
