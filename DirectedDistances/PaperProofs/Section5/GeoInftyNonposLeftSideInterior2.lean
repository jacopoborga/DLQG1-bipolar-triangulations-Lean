/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideInterior
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftInitialStarNonfixed
import DirectedDistances.KMSW.MhatPrimeVertexForward

/-! Helpers toward Lemma 5.5: ambient rotation transport away from the initial star. -/

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

include hfin in
/-- Helper toward Lemma 5.5: a vertex shared by the two dart blocks is
either the initial vertex or the head of an indexed interface edge. -/
theorem lMinus_shared_dart_endpoint_interface
    (p : ℕ × Bool) (d : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex (shiftedStream W 0) (EH d.1, d.2)) :
    kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ p) = VH 0 ∨
      ∃ i : ℕ, kmswLimitDartVertex (shiftedStream W 0)
        (lMinusPrimedDartImage hτ p) =
        kmswLimitDartVertex (shiftedStream W 0)
          (EH (kmswLeftBoundaryEdge (hatCodes U hτ) i), true) := by
  let hb := hatBoundaryHitWitnesses U hτ
  let a := primedLimitDartMap U hτ p
  let b : ℕ × Bool := (hatLimitEdgeMap U hτ d.1, d.2)
  have heq : kmswDartEndpoint U a = kmswDartEndpoint U b := by
    apply boundaryGluingFutureVertexMap_injective W h k
    exact (lMinus_future_dart_endpoint (W := W) (h := h) (k := k) a).symm.trans
      (hv.trans (lMinus_future_dart_endpoint (W := W) (h := h) (k := k) b))
  have hreach : MhatVertex U (kmswDartEndpoint U a) := by
    rw [heq]
    have he := (hatExplicitEdgeEquiv U hτ
      ⟨d.1, hatCodes_edge_present U hτ d.1⟩).property
    cases hd : d.2
    · simpa only [MhatVertex, b, kmswDartEndpoint, hd, Bool.false_eq_true,
        ↓reduceIte, hatExplicitEdgeEquiv_apply] using he.2.1
    · simpa only [MhatVertex, b, kmswDartEndpoint, hd,
        ↓reduceIte, hatExplicitEdgeEquiv_apply] using he.2.2
  have hprime : primeVertex U hfin hb (kmswDartEndpoint U a) := by
    refine ⟨a.1, ?_, ?_⟩
    · exact (primeGeomEdge_iff_primedLimitEdge U hfin hb hτ a.1).mpr ⟨p.1, rfl⟩
    · cases ha : a.2
      · exact Or.inl (by simp only [kmswDartEndpoint, ha, Bool.false_eq_true, ↓reduceIte])
      · exact Or.inr (by simp only [kmswDartEndpoint, ha, ↓reduceIte])
  obtain hbad | ⟨e, ⟨i, hi⟩, hend⟩ :=
    primeVertexSourceCharacterization_forward U hfin hb _ hprime
  · exact (hbad hreach).elim
  have hbdy (j : ℕ) : hatLimitEdgeMap U hτ
      (kmswLeftBoundaryEdge (hatCodes U hτ) j) =
      (kmswBeta0Stream U hfin hb j).val :=
    hattedLeftBoundaryBeta0EdgeCorrespondence_proved U hτ hfin hb j
  have hstart : kmswDartEndpoint U a = 0 ∨ ∃ j : ℕ,
      kmswDartEndpoint U a = edgeEast U
        (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) j)) := by
    rcases hend with hw | he
    · rw [← hi] at hw
      cases i with
      | zero => exact Or.inl (hw.symm.trans (kmswBeta0Stream_start U hfin hb))
      | succ i =>
        exact Or.inr ⟨i, hw.symm.trans ((kmswBeta0Stream_chain U hfin hb i).trans
          (congrArg (edgeEast U) (hbdy i).symm))⟩
    · exact Or.inr ⟨i, he.symm.trans (congrArg (edgeEast U) (hi.symm.trans (hbdy i).symm))⟩
  rcases hstart with hz | ⟨i, hi⟩
  · left
    exact (lMinus_future_dart_endpoint (W := W) (h := h) (k := k) a).trans
      ((congrArg (boundaryGluingFutureVertexMap W h k) hz).trans
        (congrArg (boundaryGluingFutureVertexMap W h k)
          (hatLimitVertexMap_root U hτ).symm))
  · right
    refine ⟨i, ?_⟩
    exact (lMinus_future_dart_endpoint (W := W) (h := h) (k := k) a).trans
      ((congrArg (boundaryGluingFutureVertexMap W h k) hi).trans
        (lMinus_future_dart_endpoint (W := W) (h := h) (k := k)
          (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) i), true)).symm)

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: outside the initial vertex and indexed ports,
the primed block return has no retained hatted dart in its open ambient gap. -/
theorem lMinus_primed_interior_side_rotation
    (p : ℕ × Bool)
    (hinit : kmswLimitDartVertex (shiftedStream W 0)
      (lMinusPrimedDartImage hτ p) ≠ VH 0)
    (hboundary : ∀ i : ℕ, ∀ b : Bool,
      lMinusPrimedDartImage hτ p ≠ (EH ((Q).boundary i).1, b)) :
    (S).rotation (lMinusPrimedDartImage hτ p)
      (lMinusPrimedDartImage hτ
        (kmswInfRot (primedCode (primedSimInput U) hτ)
          (primedCode_finiteIncidence U hτ hfin) p)) := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  obtain ⟨t, ht, hte, htgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hs
  rcases (Set.ext_iff.mp (lMinus_side_darts_union
    hτ hp P hqMode Tpath hfin hleft hk) _).mp hs with hP | ⟨d, hd⟩
  · exact htgap j hj hjt hP
  have hv : kmswLimitDartVertex (shiftedStream W 0) x =
      kmswLimitDartVertex (shiftedStream W 0) (J d) := by
    have he := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0) (H.1 0)
      x ((σ : _ → _)^[j] x)).mp ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
    exact he.trans (congrArg (kmswLimitDartVertex (shiftedStream W 0)) hd.symm)
  obtain hzero | ⟨i, hi⟩ := lMinus_shared_dart_endpoint_interface hτ hfin p d.val hv
  · exact (hinit hzero).elim
  have hbdy (i : ℕ) : ((Q).boundary i).1 =
      kmswLeftBoundaryEdge (hatCodes U hτ) i := by
    change kmswLeftBoundaryEdge z i = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [← hbdy i] at hi
  let a : ℕ × Bool := (EH ((Q).boundary i).1, true)
  let b : ℕ × Bool := (EH ((Q).boundary (i + 1)).1, false)
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapH, hperiod, _⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  change (σ : _ → _)^[n + m] a = a at hperiod
  have haP : a ∈ Set.range (lMinusPrimedDartImage hτ) := by
    refine ⟨(primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i,
      false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin, ← hbdy i]
    rfl
  obtain ⟨r, hr⟩ := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0)
    (H.1 0) a x).mpr hi.symm
  have hr' : (σ : _ → _)^[r % (n + m)] a = x := by
    exact (Function.IsPeriodicPt.iterate_mod_apply hperiod r).trans
      (by simpa only [σ, Equiv.Perm.coe_pow] using hr)
  let s := r % (n + m)
  change (σ : _ → _)^[s] a = x at hr'
  have hslt : s < n + m := Nat.mod_lt _ (by omega)
  have hsge : n < s := by
    by_cases hs0 : s = 0
    · have hx : x = a := by simpa only [hs0, Function.iterate_zero_apply] using hr'.symm
      exact (hboundary i true hx).elim
    by_cases hsn : s < n
    · apply False.elim
      apply hgapP s (by omega) hsn
      exact hr'.symm ▸ Set.mem_range_self p
    by_cases hsn : s = n
    · have hx : x = b := hr'.symm.trans (by simpa only [hsn] using hna)
      exact (hboundary (i + 1) false hx).elim
    omega
  have hxb : (σ : _ → _)^[s - n] b = x := by
    rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel hsge.le]
    exact hr'
  have hxa : (σ : _ → _)^[n + m - s] x = a := by
    rw [← hr', ← Function.iterate_add_apply,
      Nat.sub_add_cancel (Nat.le_of_lt hslt)]
    exact hperiod
  have htle : t ≤ n + m - s := by
    by_contra hh
    apply htgap (n + m - s) (by omega) (by omega)
    exact hxa.symm ▸ haP
  apply hgapH (s - n + j) (by omega) (by omega)
  refine ⟨d, ?_⟩
  change J d = (σ : _ → _)^[s - n + j] b
  rw [Nat.add_comm (s - n) j, Function.iterate_add_apply, hxb]
  exact hd

/-- Helper toward Lemma 5.5: both inputs changed by the final reconnection
are based at the initial vertex, so all other stars retain the adjusted output. -/
theorem lMinusCodeInitialSplicedRotation_eq_adjusted_outside_initial
    (d : LMinusCodeGluedDart rL Q)
    (hv : kmswLimitDartVertex (shiftedStream W 0) (D d).val ≠ VH 0) :
    R d = A d := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  apply lMinusCodeInitialSplicedRotation_apply_of_ne
  · intro he
    apply hv
    rw [he, lMinusCodeHattedRotation_initial_predecessor,
      lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ]
    exact congrArg VH (lMinusHattedRotation_initial_predecessor_vertex _ qL)
  · intro he
    apply hv
    rw [he, lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
      hτ hp P hqMode Tpath hfin hleft hk, lMinusCodeGluedDartEquiv_primed]
    have hep := lMinus_primed_rotation_endpoint (H := H) (longest := longest)
      hτ hfin ((Prot).symm (B 0, true))
    rw [Equiv.apply_symm_apply] at hep
    change kmswLimitDartVertex (shiftedStream W 0)
      (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) = _
    rw [← hep]
    have hc : C = lMinusCodePrimedDart rL Q (B 0, true) :=
      lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk 0 false
    have hdc := congrArg (fun d => (D d).val) hc
    rw [lMinusCodeGluedDartEquiv_primed] at hdc
    change (D C).val = lMinusPrimedDartImage hτ (B 0, true) at hdc
    rw [← hdc]
    change kmswLimitDartVertex (shiftedStream W 0) (D (lMinusCodeHattedDart rL Q c)).val = _
    rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ,
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]

/-- Helper toward Lemma 5.5: every indexed interface port outside the
initial star has the actual geometric side rotation under the spliced candidate. -/
theorem lMinusCodeInitialSplicedRotation_boundary_outside_initial
    (i : ℕ) (b : Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodeBoundaryDart rL qL (i, b))).val ≠ VH 0) :
    (S).rotation (D (lMinusCodeBoundaryDart rL qL (i, b))).val
      (D (R (lMinusCodeBoundaryDart rL qL (i, b)))).val := by
  rw [lMinusCodeInitialSplicedRotation_eq_adjusted_outside_initial
    hτ hp P hqMode Tpath hfin hleft hk _ hv]
  cases b with
  | true =>
    exact lMinusCodeInitialAdjustedRotation_incoming_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk i
  | false =>
    cases i with
    | succ i =>
      exact lMinusCodeInitialAdjustedRotation_outgoing_side_rotation
        hτ hp P hqMode Tpath hfin hleft hk i
    | zero =>
      exfalso
      apply hv
      change kmswLimitDartVertex (shiftedStream W 0)
        (D (lMinusCodeHattedDart rL Q
          ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val = _
      rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ,
        (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]

/-- Helper toward Lemma 5.5: all primed darts outside the initial vertex
have the actual geometric side successor under the spliced code permutation. -/
theorem lMinus_primed_outside_initial_side_rotation
    (p : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodePrimedDart rL Q p)).val ≠ VH 0) :
    (S).rotation (D (lMinusCodePrimedDart rL Q p)).val
      (D (R (lMinusCodePrimedDart rL Q p))).val := by
  by_cases hb : ∃ i : ℕ, ∃ b : Bool,
      lMinusCodePrimedDart rL Q p = lMinusCodeBoundaryDart rL qL (i, b)
  · obtain ⟨i, b, he⟩ := hb
    rw [he] at hv ⊢
    exact lMinusCodeInitialSplicedRotation_boundary_outside_initial
      hτ hp P hqMode Tpath hfin hleft hk i b hv
  have hboundary : ∀ i : ℕ, ∀ b : Bool,
      lMinusCodePrimedDart rL Q p ≠ lMinusCodeBoundaryDart rL qL (i, b) := by
    intro i b he
    exact hb ⟨i, b, he⟩
  rw [lMinusCodeInitialSplicedRotation_eq_adjusted_outside_initial
    hτ hp P hqMode Tpath hfin hleft hk _ hv,
    lMinusCodeInitialAdjustedRotation_primed_interior
      hτ hp P hqMode Tpath hfin hleft hk p hboundary,
    lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_primed]
  have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) := by
    congr 1
    exact lMinus_primed_observation_code hτ
  change (S).rotation (lMinusPrimedDartImage hτ p) (lMinusPrimedDartImage hτ (Prot p))
  rw [hrot]
  apply lMinus_primed_interior_side_rotation hτ hp P hqMode Tpath hfin hleft hk p
  · rw [lMinusCodeGluedDartEquiv_primed] at hv
    exact hv
  · intro i b he
    apply hboundary i b
    apply (D).injective
    apply Subtype.ext
    rw [lMinusCodeGluedDartEquiv_primed]
    change lMinusPrimedDartImage hτ p = (D (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary i).1, b), lMinus_hatted_boundary_mem _ qL i⟩)).val
    rw [lMinusCodeGluedDartEquiv_hatted]
    exact he

end GeometricGluing





































































end DirectedDistances.PaperProofs.Section5

