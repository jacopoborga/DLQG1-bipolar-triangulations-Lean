/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice














public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: reconnect the initial adjusted splice by
exchanging its predecessor output with the shared initial dart. The fixed
case needs no reconnection. This definition uses only the two block codes;
agreement at the entire geometric initial star is a separate obligation. -/
@[expose] noncomputable def lMinusCodeInitialSplicedRotation {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1) :
    Equiv.Perm (LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :=
  let c := lMinusCodeBoundaryDart r q (0, false)
  let Hrot := (lMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
  let a := Hrot.symm c
  let A := lMinusCodeInitialAdjustedRotation r q hf
  if a = c then A else Equiv.swap (A a) c * A

/-- Helper toward Lemma 5.5: the reconnection is a permutation in both
cases, without a geometric rotation or fixed-point assumption. -/
theorem lMinusCodeInitialSplicedRotation_bijective {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1) :
    Function.Bijective (lMinusCodeInitialSplicedRotation r q hf) :=
  (lMinusCodeInitialSplicedRotation r q hf).bijective

/-- Helper toward Lemma 5.5: the reconnection changes only the hatted
predecessor and the adjusted predecessor of the initial shared dart. -/
theorem lMinusCodeInitialSplicedRotation_apply_of_ne {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q))
    (ha : d ≠ ((lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))).symm
        (lMinusCodeBoundaryDart r q (0, false)))
    (hc : d ≠ (lMinusCodeInitialAdjustedRotation r q hf).symm
      (lMinusCodeBoundaryDart r q (0, false))) :
    lMinusCodeInitialSplicedRotation r q hf d =
      lMinusCodeInitialAdjustedRotation r q hf d := by
  let c := lMinusCodeBoundaryDart r q (0, false)
  let Hext := (lMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
  let a := Hext.symm c
  let A := lMinusCodeInitialAdjustedRotation r q hf
  change (if a = c then A else Equiv.swap (A a) c * A) d = A d
  by_cases he : a = c
  · rw [ite_eq_left he]
  · rw [ite_eq_right he, Equiv.Perm.mul_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun h => ha (A.injective h)
    · intro h
      apply hc
      exact (congrArg A.symm h).symm.trans (Equiv.symm_apply_apply A d) |>.symm

/-- Helper toward Lemma 5.5: at the adjusted predecessor of the initial
dart the reconnection gives the old hatted output in the nonfixed case.
This states a permutation calculation, not its geometric identification. -/
theorem lMinusCodeInitialSplicedRotation_adjusted_predecessor {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hf : KMSWFiniteIncidence r.code.1) :
    let c := lMinusCodeBoundaryDart r q (0, false)
    let Hext := (lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
    let a := Hext.symm c
    let A := lMinusCodeInitialAdjustedRotation r q hf
    lMinusCodeInitialSplicedRotation r q hf (A.symm c) =
      if a = c then c else A a := by
  dsimp only
  unfold lMinusCodeInitialSplicedRotation
  dsimp only
  split
  · rw [Equiv.apply_symm_apply]
  · rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_right]

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
local notation "VP" => boundaryGluingPrimedVertexMap W h k hτ
local notation "z" => boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the hatted dart embedding preserves the
vertex even for missing edges and either endpoint bit. -/
theorem lMinus_hatted_dart_endpoint (d : ℕ × Bool) :
    kmswLimitDartVertex (shiftedStream W 0) (EH d.1, d.2) =
      VH (kmswLimitDartVertex z d) := by
  obtain ⟨e, b⟩ := d
  have he := boundaryGluing_hat_edge_endpoints W h k hτ e
  rw [boundaryGluing_decoded_stream W h k hτ]
  cases b
  · exact he.1
  · exact he.2

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the geometric initial star is the union of
the primed star at the identified vertex and the embedded retained hatted
source star. This is equality of darts with their edge identities. -/
theorem lMinus_initial_side_star_union :
    {d : ℕ × Bool | d.1 ∈ (S).edges ∧
      kmswLimitDartVertex (shiftedStream W 0) d = VH 0} =
    (lMinusPrimedDartImage hτ) ''
      {d : ℕ × Bool | VP (kmswLimitDartVertex
        (primedCode (primedSimInput U) hτ) d) = VH 0} ∪
    (fun d : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH d.val.1, d.val.2)) ''
      {d | kmswLimitDartVertex z d.val = 0} := by
  ext d
  have hset := Set.ext_iff.mp
    (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) d
  constructor
  · rintro ⟨hd, hv⟩
    rcases hset.mp hd with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, (lMinusPrimedDartImage_endpoint hτ a).symm.trans hv, rfl⟩
    · refine Or.inr ⟨a, ?_, rfl⟩
      apply boundaryGluingHatVertexMap_injective W h k hτ
      exact (lMinus_hatted_dart_endpoint hτ a.val).symm.trans hv
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨hset.mpr (Or.inl ⟨a, rfl⟩),
        (lMinusPrimedDartImage_endpoint hτ a).trans ha⟩
    · exact ⟨hset.mpr (Or.inr ⟨a, rfl⟩),
        (lMinus_hatted_dart_endpoint hτ a.val).trans (congrArg VH ha)⟩

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the source hatted star meets the primed
block at exactly the initial dart. No singleton-star assumption is used. -/
theorem lMinus_initial_hatted_star_mem_primed_iff
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0) :
    lMinusCodeHattedDart rL Q d ∈ Set.range (lMinusCodePrimedDart rL Q) ↔
      d.val = (((Q).boundary 0).1, false) := by
  constructor
  · intro hm
    obtain ⟨i, b, he⟩ :=
      (lMinusCodeHattedDart_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk d).mp hm
    have heval : d.val = (((Q).boundary i).1, b) :=
      congrArg Subtype.val (lMinusCodeHattedDart_injective rL qL he)
    have hb := (lMinus_hatted_boundary_source_iff hqMode i b).mp
      ((congrArg (kmswLimitDartVertex z) heval).symm.trans hv)
    obtain ⟨rfl, rfl⟩ := hb
    exact heval
  · intro he
    have hd : d = ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩ :=
      Subtype.ext he
    rw [hd]
    change lMinusCodeBoundaryDart rL qL (0, false) ∈ _
    rw [lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the same source-star overlap calculation
in the ambient geometric dart carrier, rather than the intrinsic quotient. -/
theorem lMinus_initial_hatted_image_mem_primed_iff
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0) :
    (EH d.val.1, d.val.2) ∈ Set.range (lMinusPrimedDartImage hτ) ↔
      d.val = (((Q).boundary 0).1, false) := by
  have hm : (EH d.val.1, d.val.2) ∈ Set.range (lMinusPrimedDartImage hτ) ↔
      lMinusCodeHattedDart rL Q d ∈ Set.range (lMinusCodePrimedDart rL Q) := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply (D).injective
      apply Subtype.ext
      rw [lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted]
      exact ha
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have he := congrArg (fun b => (D b).val) ha
      rw [lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted] at he
      exact he
  exact hm.trans
    (lMinus_initial_hatted_star_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk d hv)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the geometric initial star consists entirely
of primed darts exactly in the fixed-point case. In the other case it
contains additional hatted darts. This decides neither case by assumption. -/
theorem lMinus_initial_side_star_eq_primed_iff :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    {d : ℕ × Bool | d.1 ∈ (S).edges ∧
      kmswLimitDartVertex (shiftedStream W 0) d = VH 0} =
      {d | d ∈ Set.range (lMinusPrimedDartImage hτ) ∧
        kmswLimitDartVertex (shiftedStream W 0) d = VH 0} ↔
      lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL c = c := by
  dsimp only
  have hfix := lMinusHattedRotation_initial_eq_self_iff_singleton hqMode
  dsimp only at hfix
  rw [hfix]
  have hset := lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk
  constructor
  · intro he
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · exact ⟨lMinus_hatted_boundary_mem _ qL 0,
        (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩⟩
    · intro a ha
      let e : {d : ℕ × Bool // d.1 ∈ (Q).edges} := ⟨a, ha.1⟩
      have hv : kmswLimitDartVertex (shiftedStream W 0) (EH a.1, a.2) = VH 0 :=
        (lMinus_hatted_dart_endpoint hτ a).trans (congrArg VH ha.2)
      have hmem : (EH a.1, a.2) ∈
          {d : ℕ × Bool | d.1 ∈ (S).edges ∧
            kmswLimitDartVertex (shiftedStream W 0) d = VH 0} :=
        ⟨(Set.ext_iff.mp hset _).mpr (Or.inr ⟨e, rfl⟩), hv⟩
      rw [he] at hmem
      exact (lMinus_initial_hatted_image_mem_primed_iff
        hτ hp P hqMode Tpath hfin hleft hk e ha.2).mp hmem.1
  · intro hs
    ext a
    constructor
    · rintro ⟨ha, hv⟩
      refine ⟨?_, hv⟩
      rcases (Set.ext_iff.mp hset a).mp ha with hp | ⟨e, rfl⟩
      · exact hp
      · have hev : kmswLimitDartVertex z e.val = 0 := by
          apply boundaryGluingHatVertexMap_injective W h k hτ
          exact (lMinus_hatted_dart_endpoint hτ e.val).symm.trans hv
        have he : e.val = (((Q).boundary 0).1, false) := by
          have hm : e.val ∈ {a : ℕ × Bool | a.1 ∈ (Q).edges ∧
              kmswLimitDartVertex z a = 0} := ⟨e.property, hev⟩
          rw [hs] at hm
          exact Set.mem_singleton_iff.mp hm
        exact (lMinus_initial_hatted_image_mem_primed_iff
          hτ hp P hqMode Tpath hfin hleft hk e hev).mpr he
    · rintro ⟨ha, hv⟩
      exact ⟨(Set.ext_iff.mp hset a).mpr (Or.inl ha), hv⟩

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the original splice at the initial dart
returns to the primed root in the fixed case and to the hatted successor
otherwise. This is a case split, with no fixed-point premise. -/
theorem lMinusCodeSpliceRotation_initial_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    lMinusCodeSpliceRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (0, false)) =
      if Hrot c = c then lMinusCodePrimedDart rL Q (0, true)
      else lMinusCodeHattedDart rL Q (Hrot c) := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    exact (lMinusCodeSpliceRotation_initial_eq_iff
      hτ hp P hqMode Tpath hfin hleft hk).mpr hfix
  · rw [ite_eq_right hfix]
    let Hemb := Equiv.ofInjective (lMinusCodeHattedDart rL Q)
      (lMinusCodeHattedDart_injective rL qL)
    let Cemb := Equiv.ofInjective (lMinusCodeBoundaryDart rL qL)
      (lMinusCodeBoundaryDart_injective rL qL)
    let Prot := kmswInfRot (rL).code.1
      (lMinus_primed_observation_finiteIncidence hτ hfin)
    let Pemb := Equiv.ofInjective (lMinusCodePrimedDart rL Q)
      (lMinusCodePrimedDart_injective rL qL)
    have hnP : lMinusCodeHattedDart rL Q (Hrot c) ∉
        Set.range (lMinusCodePrimedDart rL Q) := by
      intro hm
      exact hfix ((lMinusHattedRotation_initial_mem_primed_iff
        hτ hp P hqMode Tpath hfin hleft hk).mp hm)
    have hnC : lMinusCodeHattedDart rL Q (Hrot c) ∉
        Set.range (lMinusCodeBoundaryDart rL qL) := by
      rintro ⟨⟨i, b⟩, he⟩
      apply hnP
      rw [← he, lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    have hH : Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (0, false)) =
        lMinusCodeHattedDart rL Q (Hrot c) :=
      Hrot.extendDomain_apply_image Hemb c
    change Prot.extendDomain Pemb
      (lMinusBoundaryCornerPerm.extendDomain Cemb
        (Hrot.extendDomain Hemb (lMinusCodeBoundaryDart rL qL (0, false)))) = _
    rw [hH, Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnC,
      Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hnP]

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the adjusted predecessor output, in both
cases. In the nonfixed case its output remains a hatted dart. -/
theorem lMinusCodeInitialAdjustedRotation_predecessor_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeHattedDart rL Q (Hrot.symm c)) =
      if Hrot c = c then lMinusCodePrimedDart rL Q (0, true)
      else lMinusCodeHattedDart rL Q (Hrot c) := by
  dsimp only
  rw [← lMinusCodeHattedRotation_initial_predecessor rL qL]
  change lMinusCodeSpliceRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
    (Equiv.swap _ _ _) = _
  rw [Equiv.swap_apply_right]
  exact lMinusCodeSpliceRotation_initial_cases hτ hp P hqMode Tpath hfin hleft hk

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the adjusted predecessor output is the
geometric first return exactly in the fixed case. In the nonfixed case,
return to the union cannot skip the earlier retained initial hatted dart
and land at another hatted dart. This compares with geometric rotation. -/
theorem lMinusCodeInitialAdjustedRotation_predecessor_side_rotation_iff :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    (S).rotation
      (D (lMinusCodeHattedDart rL Q (Hrot.symm c))).val
      (D (lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeHattedDart rL Q (Hrot.symm c)))).val ↔ Hrot c = c := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  have heval := lMinusCodeInitialAdjustedRotation_predecessor_cases
    hτ hp P hqMode Tpath hfin hleft hk
  dsimp only at heval
  rw [heval]
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    have hpred : Hrot.symm c = c := by
      exact (congrArg Hrot.symm hfix).symm.trans (Equiv.symm_apply_apply Hrot c)
    rw [hpred, lMinusCodeGluedDartEquiv_hatted, lMinusCodeGluedDartEquiv_primed]
    exact iff_of_true
      (lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft hk) hfix
  · rw [ite_eq_right hfix, lMinusCodeGluedDartEquiv_hatted,
      lMinusCodeGluedDartEquiv_hatted]
    refine iff_of_false ?_ hfix
    intro hr
    let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    have hret := lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin (Hrot.symm c)
    dsimp only at hret
    rw [Equiv.apply_symm_apply] at hret
    have hrH : ∃ n : ℕ, 0 < n ∧
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (J (Hrot.symm c)) = J (Hrot c) ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
            (J (Hrot.symm c)) ∉ Set.range J := by
      obtain ⟨n, hn, hne, hgap⟩ := hr
      refine ⟨n, hn, hne, ?_⟩
      intro j hj hjn hm
      apply hgap j hj hjn
      exact (Set.ext_iff.mp
        (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mpr (Or.inr hm)
    have he := firstReturn_endpoint_unique
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _) (Set.range J)
      (Set.mem_range_self c) (Set.mem_range_self (Hrot c)) hret hrH
    have hinj : Function.Injective J := by
      intro a b hab
      change (EH a.val.1, a.val.2) = (EH b.val.1, b.val.2) at hab
      have hb := congrArg (fun p : ℕ × Bool => p.2) hab
      have he := congrArg (fun p : ℕ × Bool => p.1) hab
      apply Subtype.ext
      exact Prod.ext
        (boundaryGluingHatEdgeMap_injective W h k hτ he) hb
    exact hfix (hinj he).symm

include hfin in
/-- Helper toward Lemma 5.5: among the primed geometric darts at the
future root, the only present outgoing dart is the shared initial port. -/
theorem lMinus_primed_initial_outgoing_unique (a : ℕ × Bool)
    (hout : kmswPresentOutgoingDart U (primedLimitDartMap U hτ a))
    (hv : kmswDartEndpoint U (primedLimitDartMap U hτ a) = 0) :
    primedLimitDartMap U hτ a =
      (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) := by
  let e := primedLimitEdgeMap U hτ a.1
  have he : EdgePresent U e := hout.2
  have hw : edgeWest U e = 0 := by
    have hb : (a.2 ^^ primedLimitSideFlip U hτ a.1) = false := hout.1
    simpa only [kmswDartEndpoint, primedLimitDartMap, hb, Bool.false_eq_true,
      ↓reduceIte, e] using hv
  have hgeom : MhatGeometricEdge U e := by
    have hr : MhatVertex U (edgeWest U e) := by
      rw [hw]
      exact Quiver.Reachable.refl _
    exact ⟨hr, hr.trans (show Quiver.Reachable
      (⟨edgeWest U e⟩ : PresentVertex U) ⟨edgeEast U e⟩ from
        (show (⟨edgeWest U e⟩ : PresentVertex U) ⟶ ⟨edgeEast U e⟩ from
          ⟨e, he, rfl, rfl⟩).reachable)⟩
  have hp : primeGeomEdge U hfin (hatBoundaryHitWitnesses U hτ) e :=
    (primeGeomEdge_iff_primedLimitEdge U hfin (hatBoundaryHitWitnesses U hτ) hτ e).mpr
      ⟨a.1, rfl⟩
  have hb : MhatWestBoundaryEdge U e := by
    rcases hp with hn | hb
    · exact (hn hgeom).elim
    · exact (primeBetaEdge_iff_MhatWestBoundaryEdge U hfin
        (hatBoundaryHitWitnesses U hτ) e).mp hb
  have heq := beta0_westBoundary_outgoing_unique U hfin
    (hatBoundaryHitWitnesses U hτ) e
    (kmswBeta0Stream U hfin (hatBoundaryHitWitnesses U hτ) 0).val hb
    (beta0_westBoundary_stream U hfin (hatBoundaryHitWitnesses U hτ) 0)
    (hw.trans (kmswBeta0Stream_start U hfin (hatBoundaryHitWitnesses U hτ)).symm)
  rw [← hattedLeftBoundaryBeta0EdgeCorrespondence_proved U hτ hfin
    (hatBoundaryHitWitnesses U hτ) 0] at heq
  exact Prod.ext heq hout.1

/-- Helper toward Lemma 5.5: the future dart embedding preserves the
geometric vertex, including both darts of missing edges. -/
theorem lMinus_future_dart_endpoint (a : ℕ × Bool) :
    kmswDartEndpoint (shiftedStream W 0)
      (boundaryGluingEdgeMap W h k a.1, a.2) =
      boundaryGluingFutureVertexMap W h k (kmswDartEndpoint U a) := by
  obtain ⟨e, b⟩ := a
  have he := boundaryGluing_future_edge_endpoints W h k e
  cases b
  · exact he.1
  · exact he.2

include hfin hk in
/-- Helper toward Lemma 5.5: in the ambient initial primed star the
shared initial port is still the only present outgoing dart. -/
theorem lMinus_initial_primed_outgoing_unique (a : ℕ × Bool)
    (hout : kmswPresentOutgoingDart (shiftedStream W 0) (lMinusPrimedDartImage hτ a))
    (hv : kmswDartEndpoint (shiftedStream W 0) (lMinusPrimedDartImage hτ a) = VH 0) :
    lMinusPrimedDartImage hτ a = (EH ((Q).boundary 0).1, false) := by
  let p := primedLimitDartMap U hτ a
  have hp : kmswPresentOutgoingDart U p :=
    ⟨hout.1, (lMinus_future_present_iff hτ hk p.1).mpr hout.2⟩
  have hvp : kmswDartEndpoint U p = 0 := by
    apply boundaryGluingFutureVertexMap_injective W h k
    have he := lMinus_future_dart_endpoint (W := W) (h := h) (k := k) p
    have hz : VH 0 = boundaryGluingFutureVertexMap W h k 0 := by
      change boundaryGluingFutureVertexMap W h k (hatLimitVertexMap U hτ 0) = _
      rw [hatLimitVertexMap_root]
    exact he.symm.trans (hv.trans hz)
  have he := lMinus_primed_initial_outgoing_unique hτ hfin a hp hvp
  have he' := congrArg (fun d : ℕ × Bool =>
    (boundaryGluingEdgeMap W h k d.1, d.2)) he
  change lMinusPrimedDartImage hτ a =
    (EH (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) at he'
  have hc : ((Q).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
    change kmswLeftBoundaryEdge z 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [hc]
  exact he'

include hk in
/-- Helper toward Lemma 5.5: every embedded retained hatted dart at the
initial vertex is a present outgoing dart in the ambient map. -/
theorem lMinus_initial_hatted_outgoing
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex z d.val = 0) :
    kmswPresentOutgoingDart (shiftedStream W 0) (EH d.val.1, d.val.2) := by
  have hd := (source_dart_iff_outgoing z
    (sourceAncestor_left_nonneg _ renewalTime renewalTime_positiveSuccessTime qL)
    (sourceAncestor_right_unbounded _ renewalTime renewalTime_positiveSuccessTime qL)
    d.val).mp hv
  refine ⟨hd.1, ?_⟩
  exact (lMinus_future_present_iff hτ hk _).mp
    ((hatLimitEdgeMap_range_iff U hτ _).mp ⟨d.val.1, rfl⟩).1

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the geometric return from the initial hatted
predecessor reaches the primed root in the fixed case and the initial shared
dart otherwise. The nonfixed open return interval contains no primed dart. -/
theorem lMinus_initial_predecessor_side_rotation_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    (S).rotation (J (Hrot.symm c))
      (if Hrot c = c then lMinusPrimedDartImage hτ (0, true) else J c) := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  have hJ : Function.Injective J := by
    intro a b hab
    change (EH a.val.1, a.val.2) = (EH b.val.1, b.val.2) at hab
    have hb := congrArg (fun p : ℕ × Bool => p.2) hab
    apply Subtype.ext
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst hab)) hb
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    have hpred : Hrot.symm c = c :=
      (congrArg Hrot.symm hfix).symm.trans (Equiv.symm_apply_apply Hrot c)
    rw [hpred]
    exact lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft hk
  · rw [ite_eq_right hfix]
    have hne : J (Hrot.symm c) ≠ J c := by
      intro he
      have he' := congrArg Hrot (hJ he)
      rw [Equiv.apply_symm_apply] at he'
      exact hfix he'.symm
    have hc0 : kmswLimitDartVertex z c.val = 0 :=
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩
    have ha0 : kmswLimitDartVertex z (Hrot.symm c).val = 0 :=
      lMinusHattedRotation_initial_predecessor_vertex _ qL
    have hcoa := lMinus_initial_hatted_outgoing hτ hqMode hk c hc0
    have haoa := lMinus_initial_hatted_outgoing hτ hqMode hk (Hrot.symm c) ha0
    have hva : kmswDartEndpoint (shiftedStream W 0) (J (Hrot.symm c)) = VH 0 :=
      (lMinus_hatted_dart_endpoint hτ (Hrot.symm c).val).trans (congrArg VH ha0)
    have hvc : kmswDartEndpoint (shiftedStream W 0) (J c) = VH 0 :=
      (lMinus_hatted_dart_endpoint hτ c.val).trans (congrArg VH hc0)
    have hw : edgeWest (shiftedStream W 0) (J (Hrot.symm c)).1 =
        edgeWest (shiftedStream W 0) (J c).1 := by
      have ha := hva
      have hc := hvc
      change (if (J (Hrot.symm c)).2 then _ else _) = _ at ha
      change (if (J c).2 then _ else _) = _ at hc
      rw [haoa.1] at ha
      rw [hcoa.1] at hc
      exact ha.trans hc.symm
    have harc : RotationArc σ (kmswPresentOutgoingDart (shiftedStream W 0))
        (J (Hrot.symm c)) (J c) := by
      have ha : J (Hrot.symm c) = ((J (Hrot.symm c)).1, false) :=
        Prod.ext rfl haoa.1
      have hc : J c = ((J c).1, false) := Prod.ext rfl hcoa.1
      rcases kmswInfRot_outgoing_interval_all (shiftedStream W 0) (H.1 0)
          (J (Hrot.symm c)).1 (J c).1 hw haoa.2 hcoa.2 with hforward | hbackward
      · simpa only [RotationArc, σ, kmswPresentOutgoingDart, ← ha, ← hc] using hforward
      · have hbad : RotationArc σ (kmswPresentOutgoingDart (shiftedStream W 0))
            (J c) (J (Hrot.symm c)) := by
          simpa only [RotationArc, σ, kmswPresentOutgoingDart, ← ha, ← hc] using hbackward
        obtain ⟨m, hm, hall⟩ := hbad
        simp only [Equiv.Perm.coe_pow] at hm hall
        have hmpos : 0 < m := by
          by_contra hn
          have hz : m = 0 := by omega
          rw [hz, Function.iterate_zero_apply] at hm
          exact hne hm.symm
        let FJ : (ℕ × Bool) → ℕ × Bool :=
          fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
        let cU : ℕ × Bool :=
          (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false)
        have hce : FJ cU = J c := by
          change (EH (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) = _
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
          refine ⟨(hatLimitEdgeMap U hτ (Hrot.symm c).val.1,
            (Hrot.symm c).val.2), ?_⟩
          change J (Hrot.symm c) = (σ : _ → _)^[m] (FJ cU)
          rw [hce]
          exact hm.symm
        · exact (hnout (hte ▸ hall t (by omega))).elim
    obtain ⟨m, hm, hall⟩ := harc
    simp only [Equiv.Perm.coe_pow] at hm hall
    obtain ⟨n, hn, hnep, hgap⟩ :=
      lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin (Hrot.symm c)
    dsimp only at hnep hgap
    rw [Equiv.apply_symm_apply] at hnep
    have hmpos : 0 < m := by
      by_contra hnot
      have hz : m = 0 := by omega
      rw [hz, Function.iterate_zero_apply] at hm
      exact hne hm
    have hnm : n ≤ m := by
      by_contra hnot
      apply hgap m hmpos (by omega)
      exact ⟨c, hm.symm⟩
    refine ⟨n, hn, hnep, ?_⟩
    intro j hj hjn hmem
    rcases (Set.ext_iff.mp
      (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hmem with
        ⟨p, hp⟩ | hh
    · have hout := hall j (by omega)
      have hvj : kmswDartEndpoint (shiftedStream W 0)
          ((σ : _ → _)^[j] (J (Hrot.symm c))) = VH 0 := by
        have he := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0)
          (H.1 0) (J (Hrot.symm c))
          ((σ : _ → _)^[j] (J (Hrot.symm c)))).mp
            ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩
        exact he.symm.trans hva
      have hpu := lMinus_initial_primed_outgoing_unique hτ hqMode hfin hk p
        (hp.symm ▸ hout) (hp.symm ▸ hvj)
      apply hgap j hj hjn
      exact ⟨c, hpu.symm.trans hp⟩
    · exact hgap j hj hjn hh

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: in the nonfixed case the open hatted return
interval excludes both retained blocks. The fixed case is split explicitly;
no rotation or first-return assertion is supplied as a premise. -/
theorem lMinus_initial_predecessor_open_gap_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    if Hrot c = c then True else
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (J (Hrot.symm c)) = J c ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
            (J (Hrot.symm c)) ∉ Set.range (lMinusPrimedDartImage hτ) ∧
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
            (J (Hrot.symm c)) ∉ Set.range J := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    trivial
  · rw [ite_eq_right hfix]
    have hr := lMinus_initial_predecessor_side_rotation_cases
      hτ hp P hqMode Tpath hfin hleft hk
    change (S).rotation (J (Hrot.symm c))
      (if Hrot c = c then lMinusPrimedDartImage hτ (0, true) else J c) at hr
    rw [ite_eq_right hfix] at hr
    obtain ⟨n, hn, he, hgap⟩ := hr
    refine ⟨n, hn, he, ?_⟩
    intro j hj hjn
    have hs := Set.ext_iff.mp
      (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk)
      ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (J (Hrot.symm c)))
    exact ⟨fun hm => hgap j hj hjn (hs.mpr (Or.inl hm)),
      fun hm => hgap j hj hjn (hs.mpr (Or.inr hm))⟩

/-- Helper toward Lemma 5.5: the extended hatted predecessor is the
initial port precisely in the fixed case. This decides neither case by
assumption. -/
theorem lMinus_initial_predecessor_eq_initial_iff :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    lMinusCodeHattedDart rL Q (Hrot.symm c) =
      lMinusCodeBoundaryDart rL qL (0, false) ↔ Hrot c = c := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  change lMinusCodeHattedDart rL Q (Hrot.symm c) =
    lMinusCodeHattedDart rL Q c ↔ Hrot c = c
  rw [(lMinusCodeHattedDart_injective rL qL).eq_iff]
  constructor
  · intro he
    exact (congrArg Hrot he).symm.trans (Equiv.apply_symm_apply Hrot c)
  · intro he
    exact (congrArg Hrot.symm he).symm.trans (Equiv.symm_apply_apply Hrot c)

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the reverse dart of the retained missing
primed root is distinct from the shared initial port, including its edge ID. -/
theorem lMinus_initial_primed_root_ne_boundary :
    lMinusCodePrimedDart rL Q (0, true) ≠ lMinusCodeBoundaryDart rL qL (0, false) := by
  intro he
  have hh := congrArg (fun d => (D d).val) he
  change (D (lMinusCodePrimedDart rL Q (0, true))).val =
    (D (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val at hh
  rw [lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted] at hh
  have hb := congrArg (fun d : ℕ × Bool => d.2) hh
  simp only [primedLimitSideFlip_zero, Bool.xor_false] at hb
  exact Bool.noConfusion hb

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the reconnected candidate preserves the
geometrically proved initial successor in both fixed and nonfixed cases. -/
theorem lMinusCodeInitialSplicedRotation_initial :
    lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (0, false)) =
      lMinusCodePrimedDart rL Q (0, true) := by
  let c := lMinusCodeBoundaryDart rL qL (0, false)
  let Hext := (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective rL qL))
  let a := Hext.symm c
  let A := lMinusCodeInitialAdjustedRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  have hAc : A c = lMinusCodePrimedDart rL Q (0, true) :=
    lMinusCodeInitialAdjustedRotation_initial hτ hp P hqMode Tpath hfin hleft hk
  change (if a = c then A else Equiv.swap (A a) c * A) c = _
  by_cases ha : a = c
  · rw [ite_eq_left ha]
    exact hAc
  · rw [ite_eq_right ha, Equiv.Perm.mul_apply]
    have hne : A c ≠ A a := fun he => ha ((A.injective he).symm)
    have hnc : A c ≠ c := by
      rw [hAc]
      exact lMinus_initial_primed_root_ne_boundary hτ hp P hqMode Tpath hfin hleft hk
    rw [Equiv.swap_apply_of_ne_of_ne hne hnc]
    exact hAc

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the reconnected candidate sends the initial
hatted predecessor to the actual geometric return in both cases. -/
theorem lMinusCodeInitialSplicedRotation_predecessor_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeHattedDart rL Q (Hrot.symm c)) =
      if Hrot c = c then lMinusCodePrimedDart rL Q (0, true)
      else lMinusCodeBoundaryDart rL qL (0, false) := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  let a := lMinusCodeHattedDart rL Q (Hrot.symm c)
  let c' := lMinusCodeBoundaryDart rL qL (0, false)
  let A := lMinusCodeInitialAdjustedRotation rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  have ha := lMinusCodeHattedRotation_initial_predecessor rL qL
  dsimp only at ha
  change lMinusCodeInitialSplicedRotation rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) a = _
  unfold lMinusCodeInitialSplicedRotation
  dsimp only
  rw [ha]
  change (if a = c' then A else Equiv.swap (A a) c' * A) a = _
  have heq := lMinus_initial_predecessor_eq_initial_iff hqMode
  dsimp only at heq
  by_cases hfix : Hrot c = c
  · have hac : a = c' := heq.mpr hfix
    rw [ite_eq_left hac, ite_eq_left hfix, hac]
    exact lMinusCodeInitialAdjustedRotation_initial hτ hp P hqMode Tpath hfin hleft hk
  · have hac : a ≠ c' := fun he => hfix (heq.mp he)
    rw [ite_eq_right hac, ite_eq_right hfix, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Helper toward Lemma 5.5: the reconnected candidate is geometrically
correct at the initial hatted predecessor, without a fixed-point premise. -/
theorem lMinusCodeInitialSplicedRotation_predecessor_side_rotation :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    (S).rotation (D (lMinusCodeHattedDart rL Q (Hrot.symm c))).val
      (D (lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeHattedDart rL Q (Hrot.symm c)))).val := by
  dsimp only
  rw [lMinusCodeInitialSplicedRotation_predecessor_cases hτ hp P hqMode Tpath hfin hleft hk]
  have hr := lMinus_initial_predecessor_side_rotation_cases
    hτ hp P hqMode Tpath hfin hleft hk
  dsimp only at hr
  rw [lMinusCodeGluedDartEquiv_hatted]
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  change (S).rotation (EH (Hrot.symm c).val.1, (Hrot.symm c).val.2)
    (if Hrot c = c then lMinusPrimedDartImage hτ (0, true)
      else (EH ((Q).boundary 0).1, false)) at hr
  change (S).rotation (EH (Hrot.symm c).val.1, (Hrot.symm c).val.2)
    (D (if Hrot c = c then lMinusCodePrimedDart rL Q (0, true)
      else lMinusCodeBoundaryDart rL qL (0, false))).val
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix, lMinusCodeGluedDartEquiv_primed]
    rw [ite_eq_left hfix] at hr
    exact hr
  · rw [ite_eq_right hfix]
    change (S).rotation _
      (D (lMinusCodeHattedDart rL Q
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val
    rw [lMinusCodeGluedDartEquiv_hatted]
    rw [ite_eq_right hfix] at hr
    exact hr

/-- Helper toward Lemma 5.5: the replacement also has the geometric
successor at the shared initial dart in both cases. -/
theorem lMinusCodeInitialSplicedRotation_initial_side_rotation :
    (S).rotation (D (lMinusCodeBoundaryDart rL qL (0, false))).val
      (D (lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodeBoundaryDart rL qL (0, false)))).val := by
  rw [lMinusCodeInitialSplicedRotation_initial hτ hp P hqMode Tpath hfin hleft hk,
    lMinusCodeGluedDartEquiv_primed]
  change (S).rotation (D (lMinusCodeHattedDart rL Q
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val _
  rw [lMinusCodeGluedDartEquiv_hatted]
  exact lMinus_initial_side_rotation hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: transport the reconnected intrinsic
permutation to the glued dart carrier. -/
@[expose] noncomputable def lMinusGluedInitialSplicedRotation :
    Equiv.Perm (LMinusGluedDart hτ hqMode) :=
  Equiv.permCongr
    (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (lMinusCodeInitialSplicedRotation rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin))



@[expose] noncomputable def lMinusInitialSplicedRotationRelation :
    Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) → Prop
  | .inr d, .inr e =>
      lMinusGluedInitialSplicedRotation hτ hp P hqMode Tpath hfin hleft hk d = e
  | _, _ => False

end GeometricGluing





















































end DirectedDistances.PaperProofs.Section5
