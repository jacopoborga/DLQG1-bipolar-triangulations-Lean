/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideRotation










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
local notation "VP" => boundaryGluingPrimedVertexMap W h k hτ
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

include H in
/-- Helper toward Lemma 5.5: the primed code rotation preserves the
embedded ambient vertex, with the primed side-bit correction included. -/
theorem lMinus_primed_rotation_endpoint (d : ℕ × Bool) :
    kmswLimitDartVertex (shiftedStream W 0)
      (lMinusPrimedDartImage hτ (Prot d)) =
    kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ d) := by
  have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) := by
    congr 1
    exact lMinus_primed_observation_code hτ
  rw [hrot]
  obtain ⟨n, hn, he, hgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin d
  exact ((kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0) (H.1 0)
    (lMinusPrimedDartImage hτ d) _).mp
    ⟨n, by simpa only [Equiv.Perm.coe_pow] using he⟩).symm

/-- Helper toward Lemma 5.5: every indexed shared dart at the initial
vertex is the initial forward dart, retaining its edge identity. -/
theorem lMinus_initial_boundary_unique (i : ℕ) (b : Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodeBoundaryDart rL qL (i, b))).val = VH 0) :
    i = 0 ∧ b = false := by
  have he := lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk
    (⟨(((Q).boundary i).1, b), lMinus_hatted_boundary_mem _ qL i⟩)
  change kmswLimitDartVertex (shiftedStream W 0)
    (D (lMinusCodeHattedDart rL Q
      ⟨(((Q).boundary i).1, b), lMinus_hatted_boundary_mem _ qL i⟩)).val = _ at hv
  rw [he, lMinus_hatted_dart_endpoint hτ] at hv
  exact (lMinus_hatted_boundary_source_iff hqMode i b).mp
    (boundaryGluingHatVertexMap_injective W h k hτ hv)

/-- Helper toward Lemma 5.5: a primed dart at the initial vertex other
than the shared initial dart is outside the entire indexed interface. -/
theorem lMinus_initial_primed_nonshared (d : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodePrimedDart rL Q d)).val = VH 0)
    (hne : lMinusCodePrimedDart rL Q d ≠ C) :
    ∀ i : ℕ, ∀ b : Bool,
      lMinusCodePrimedDart rL Q d ≠ lMinusCodeBoundaryDart rL qL (i, b) := by
  intro i b he
  rw [he] at hv
  obtain ⟨rfl, rfl⟩ := lMinus_initial_boundary_unique hτ hp P hqMode Tpath hfin hleft hk i b hv
  exact hne he

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: identify the adjusted predecessor of the
shared initial port as the embedded primed predecessor, in both hatted
fixed-point cases. This uses no geometric rotation-equivalence premise. -/
theorem lMinusCodeInitialAdjustedRotation_predecessor_eq_primed :
    (A).symm C = lMinusCodePrimedDart rL Q ((Prot).symm (B 0, true)) := by
  let b := lMinusCodePrimedDart rL Q ((Prot).symm (B 0, true))
  have hc : C = lMinusCodePrimedDart rL Q (B 0, true) :=
    lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk 0 false
  have hcorner : Prot (B 0, true) = (0, true) := by
    simp only [decodeLMinus_code, lMinus_primed_observation_code hτ]
    exact lMinusPrimedRotation_initial_corner hτ hfin
  have hne : b ≠ C := by
    intro he
    rw [hc] at he
    have hh := (lMinusCodePrimedDart_injective rL qL) he
    have hh' := congrArg Prot hh
    rw [Equiv.apply_symm_apply, hcorner] at hh'
    have hh'' : C = lMinusCodePrimedDart rL Q (0, true) := by
      rw [hc, hh']
    exact lMinus_initial_primed_root_ne_boundary hτ hp P hqMode Tpath hfin hleft hk hh''.symm
  have hv : kmswLimitDartVertex (shiftedStream W 0) (D b).val = VH 0 := by
    rw [lMinusCodeGluedDartEquiv_primed]
    have hep := lMinus_primed_rotation_endpoint (H := H) (longest := longest) hτ hfin ((Prot).symm (B 0, true))
    rw [Equiv.apply_symm_apply] at hep
    change kmswLimitDartVertex (shiftedStream W 0)
      (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) = _
    rw [← hep]
    have hdc := congrArg (fun d => (D d).val) hc
    rw [lMinusCodeGluedDartEquiv_primed] at hdc
    change (D C).val = lMinusPrimedDartImage hτ (B 0, true) at hdc
    rw [← hdc]
    change kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodeHattedDart rL Q
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val = _
    rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ]
    rw [(lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]
  have hd := lMinus_initial_primed_nonshared hτ hp P hqMode Tpath hfin hleft hk
    ((Prot).symm (B 0, true)) hv hne
  have hab : A b = C := by
    rw [lMinusCodeInitialAdjustedRotation_primed_interior hτ hp P hqMode Tpath hfin hleft hk
      ((Prot).symm (B 0, true)) hd, Equiv.apply_symm_apply]
    exact hc.symm
  exact (congrArg (A).symm hab).symm.trans (Equiv.symm_apply_apply A b)

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the reconnected adjusted predecessor returns
to the shared dart in the fixed case and to its hatted successor otherwise. -/
theorem lMinusCodeInitialSplicedRotation_adjusted_predecessor_cases :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    R ((A).symm C) = if Hrot c = c then C else lMinusCodeHattedDart rL Q (Hrot c) := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  have hr := lMinusCodeInitialSplicedRotation_adjusted_predecessor rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
  dsimp only at hr
  rw [lMinusCodeHattedRotation_initial_predecessor] at hr
  have heq := lMinus_initial_predecessor_eq_initial_iff hqMode
  dsimp only at heq
  have ha := lMinusCodeInitialAdjustedRotation_predecessor_cases
    hτ hp P hqMode Tpath hfin hleft hk
  dsimp only at ha
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    rw [ite_eq_left (heq.mpr hfix)] at hr
    exact hr
  · rw [ite_eq_right hfix]
    rw [ite_eq_right (fun he => hfix (heq.mp he)), ha, ite_eq_right hfix] at hr
    exact hr

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: in the fixed branch every initial primed
block return is already first return to the entire geometric side.
The singleton conclusion is derived from the fixed-point characterization. -/
theorem lMinus_initial_primed_side_rotation_of_fixed
    (hfix : lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩ =
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)
    (d : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ d) = VH 0) :
    (S).rotation (lMinusPrimedDartImage hτ d) (lMinusPrimedDartImage hτ (Prot d)) := by
  have hset := (lMinus_initial_side_star_eq_primed_iff
    hτ hp P hqMode Tpath hfin hleft hk).mpr hfix
  have hrot : Prot = kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) := by
    congr 1
    exact lMinus_primed_observation_code hτ
  obtain ⟨n, hn, he, hgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin d
  rw [hrot]
  refine ⟨n, hn, he, ?_⟩
  intro j hj hjn hs
  apply hgap j hj hjn
  have hvj : kmswLimitDartVertex (shiftedStream W 0)
      ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
        (lMinusPrimedDartImage hτ d)) = VH 0 := by
    have he' := (kmswInfRot_exists_pow_iff_endpoint (shiftedStream W 0) (H.1 0)
      (lMinusPrimedDartImage hτ d)
      ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
        (lMinusPrimedDartImage hτ d))).mp
      ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
    exact he'.symm.trans hv
  exact ((Set.ext_iff.mp hset _).mp ⟨hs, hvj⟩).1

/-- Helper toward Lemma 5.5: geometric identification at the adjusted
predecessor in the fixed branch. The nonfixed transition is not asserted. -/
theorem lMinusCodeInitialSplicedRotation_adjusted_predecessor_side_rotation_of_fixed
    (hfix : lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩ =
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩) :
    (S).rotation (D ((A).symm C)).val (D (R ((A).symm C))).val := by
  rw [lMinusCodeInitialSplicedRotation_adjusted_predecessor_cases
    hτ hp P hqMode Tpath hfin hleft hk, ite_eq_left hfix,
    lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
      hτ hp P hqMode Tpath hfin hleft hk,
    lMinusCodeGluedDartEquiv_primed]
  have hc := lMinusCodeBoundaryDart_eq_primed hτ hp P hqMode Tpath hfin hleft hk 0 false
  rw [hc, lMinusCodeGluedDartEquiv_primed]
  have hv : kmswLimitDartVertex (shiftedStream W 0)
      (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))) = VH 0 := by
    have hep := lMinus_primed_rotation_endpoint (H := H) (longest := longest)
      hτ hfin ((Prot).symm (B 0, true))
    rw [Equiv.apply_symm_apply] at hep
    rw [← hep]
    have hdc := congrArg (fun d => (D d).val) hc
    rw [lMinusCodeGluedDartEquiv_primed] at hdc
    change (D C).val = lMinusPrimedDartImage hτ (B 0, true) at hdc
    rw [← hdc]
    change kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodeHattedDart rL Q
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val = _
    rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ,
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]
  have hr := lMinus_initial_primed_side_rotation_of_fixed
    hτ hp P hqMode Tpath hfin hleft hk hfix ((Prot).symm (B 0, true)) hv
  rw [Equiv.apply_symm_apply] at hr
  exact hr

/-- Helper toward Lemma 5.5: the reconnection is inactive in the fixed
branch. No singleton-star assumption is required to identify this branch. -/
theorem lMinusCodeInitialSplicedRotation_eq_adjusted_of_fixed
    (hfix : lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩ =
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩) : R = A := by
  have he := lMinusCodeHattedRotation_initial_predecessor rL qL
  dsimp only at he
  have heq := lMinus_initial_predecessor_eq_initial_iff hqMode
  dsimp only at heq
  have he' := he.trans (heq.mpr hfix)
  unfold lMinusCodeInitialSplicedRotation
  dsimp only
  rw [ite_eq_left he']

/-- Helper toward Lemma 5.5: geometric agreement on the entire initial
star in the fixed branch, derived from the proved star characterization. -/
theorem lMinus_initial_star_spliced_side_rotation_of_fixed
    (hfix : lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩ =
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)
    (d : LMinusCodeGluedDart rL Q)
    (hv : kmswLimitDartVertex (shiftedStream W 0) (D d).val = VH 0) :
    (S).rotation (D d).val (D (R d)).val := by
  have hset := (lMinus_initial_side_star_eq_primed_iff
    hτ hp P hqMode Tpath hfin hleft hk).mpr hfix
  obtain ⟨p, hp'⟩ := ((Set.ext_iff.mp hset (D d).val).mp ⟨(D d).property, hv⟩).1
  have hdp : d = lMinusCodePrimedDart rL Q p := by
    apply (D).injective
    apply Subtype.ext
    rw [lMinusCodeGluedDartEquiv_primed]
    exact hp'.symm
  rw [hdp] at hv ⊢
  by_cases hc : lMinusCodePrimedDart rL Q p = C
  · rw [hc]
    exact lMinusCodeInitialSplicedRotation_initial_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk
  · have hd := lMinus_initial_primed_nonshared hτ hp P hqMode Tpath hfin hleft hk p hv hc
    rw [lMinusCodeInitialSplicedRotation_eq_adjusted_of_fixed hτ hqMode hfin hfix,
      lMinusCodeInitialAdjustedRotation_primed_interior
        hτ hp P hqMode Tpath hfin hleft hk p hd,
      lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_primed]
    change (S).rotation (lMinusPrimedDartImage hτ p) (lMinusPrimedDartImage hτ (Prot p))
    apply lMinus_initial_primed_side_rotation_of_fixed
      hτ hp P hqMode Tpath hfin hleft hk hfix p
    rw [lMinusCodeGluedDartEquiv_primed] at hv
    change kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ p) = _ at hv
    exact hv

local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "G" => lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: exact reduction of transport for all target
cells at a given dart to the candidate's geometric first-return assertion.
This equivalence assumes neither rotation transport nor a star condition. -/
theorem lMinusGluedCellEquiv_rotation_spliced_transport_iff
    (d : LMinusCodeGluedDart rL Q) :
    (∀ v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode),
      lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr (E d)) v ↔ geometricSideRelation S .rotation (Φ (.inr (E d))) (Φ v)) ↔
    (S).rotation (D d).val (D (R d)).val := by
  constructor
  · intro ht
    have hr := (ht (.inr (E (R d)))).mp (by
      change E (R ((E).symm (E d))) = E (R d)
      rw [Equiv.symm_apply_apply])
    change (S).rotation (G (E d)).val (G (E (R d))).val at hr
    rw [lMinusCodeToGluedDartEquiv_equiv, lMinusCodeToGluedDartEquiv_equiv] at hr
    exact hr
  · intro hr v
    cases v with
    | inl v => rfl
    | inr e =>
      change E (R ((E).symm (E d))) = e ↔ (S).rotation (G (E d)).val (G e).val
      rw [Equiv.symm_apply_apply, lMinusCodeToGluedDartEquiv_equiv]
      constructor
      · intro he
        rw [← he, lMinusCodeToGluedDartEquiv_equiv]
        exact hr
      · intro he
        apply (G).injective
        rw [lMinusCodeToGluedDartEquiv_equiv]
        apply Subtype.ext
        exact firstReturn_endpoint_unique
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
          {a : ℕ × Bool | a.1 ∈ (S).edges} (D (R d)).property (G e).property hr he

/-- Helper toward Lemma 5.5: the exact all-target initial-star transport
problem reduces to nonfixed inputs other than the two already certified
hatted ports. This is a reduction, not a claim that the right side is proved. -/
theorem lMinusGluedCellEquiv_rotation_initial_star_spliced_reduction :
    (∀ d : LMinusCodeGluedDart rL Q,
      kmswLimitDartVertex (shiftedStream W 0) (D d).val = VH 0 →
      ∀ v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode),
        let u := Sum.inr (E d)
        lMinusInitialSplicedRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
          geometricSideRelation S .rotation (Φ u) (Φ v)) ↔
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    ∀ d : LMinusCodeGluedDart rL Q,
      kmswLimitDartVertex (shiftedStream W 0) (D d).val = VH 0 →
      Hrot c ≠ c → d ≠ C → d ≠ lMinusCodeHattedDart rL Q (Hrot.symm c) →
      (S).rotation (D d).val (D (R d)).val := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  constructor
  · intro ht d hv hfix hc ha
    exact (lMinusGluedCellEquiv_rotation_spliced_transport_iff
      hτ hp P hqMode Tpath hfin hleft hk d).mp (ht d hv)
  · intro ht d hv
    apply (lMinusGluedCellEquiv_rotation_spliced_transport_iff
      hτ hp P hqMode Tpath hfin hleft hk d).mpr
    by_cases hfix : Hrot c = c
    · exact lMinus_initial_star_spliced_side_rotation_of_fixed
        hτ hp P hqMode Tpath hfin hleft hk hfix d hv
    · by_cases hc : d = C
      · rw [hc]
        exact lMinusCodeInitialSplicedRotation_initial_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk
      · by_cases ha : d = lMinusCodeHattedDart rL Q (Hrot.symm c)
        · rw [ha]
          exact lMinusCodeInitialSplicedRotation_predecessor_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk
        · exact ht d hv hfix hc ha

/-- Helper toward Lemma 5.5: exact remaining geometric reduction at the
adjusted predecessor. The fixed case is proved; in the nonfixed case the
endpoints are the primed predecessor and hatted successor of the initial
port, and the open ambient interval must avoid both retained block images. -/
theorem lMinus_initial_adjusted_predecessor_geometric_reduction :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
    let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    (S).rotation (D ((A).symm C)).val (D (R ((A).symm C))).val ↔
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
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    exact iff_of_true
      (lMinusCodeInitialSplicedRotation_adjusted_predecessor_side_rotation_of_fixed
        hτ hp P hqMode Tpath hfin hleft hk hfix) trivial
  · rw [ite_eq_right hfix,
      lMinusCodeInitialSplicedRotation_adjusted_predecessor_cases
        hτ hp P hqMode Tpath hfin hleft hk, ite_eq_right hfix,
      lMinusCodeInitialAdjustedRotation_predecessor_eq_primed
        hτ hp P hqMode Tpath hfin hleft hk,
      lMinusCodeGluedDartEquiv_primed, lMinusCodeGluedDartEquiv_hatted]
    change (∃ n : ℕ, 0 < n ∧ _ ∧ _) ↔ _
    constructor
    · rintro ⟨n, hn, he, hgap⟩
      refine ⟨n, hn, he, ?_⟩
      intro j hj hjn
      have hs := Set.ext_iff.mp
        (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk)
        ((kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (lMinusPrimedDartImage hτ ((Prot).symm (B 0, true))))
      exact ⟨fun hm => hgap j hj hjn (hs.mpr (Or.inl hm)),
        fun hm => hgap j hj hjn (hs.mpr (Or.inr hm))⟩
    · rintro ⟨n, hn, he, hgap⟩
      refine ⟨n, hn, he, ?_⟩
      intro j hj hjn hm
      have hs := (Set.ext_iff.mp
        (lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm
      rcases hs with hp' | hh'
      · exact (hgap j hj hjn).1 hp'
      · exact (hgap j hj hjn).2 hh'

/-- Helper toward Lemma 5.5: away from the initial port and the adjusted
predecessor, an initial primed input retains its primed block output in
both fixed-point cases. Geometric first-return agreement remains separate. -/
theorem lMinusCodeInitialSplicedRotation_initial_primed_other (d : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0)
      (D (lMinusCodePrimedDart rL Q d)).val = VH 0)
    (hc : lMinusCodePrimedDart rL Q d ≠ C)
    (hb : lMinusCodePrimedDart rL Q d ≠ (A).symm C) :
    R (lMinusCodePrimedDart rL Q d) = lMinusCodePrimedDart rL Q (Prot d) := by
  have hd := lMinus_initial_primed_nonshared hτ hp P hqMode Tpath hfin hleft hk d hv hc
  have hnH : lMinusCodePrimedDart rL Q d ∉ Set.range (lMinusCodeHattedDart rL Q) := by
    rintro ⟨a, ha⟩
    have hm : lMinusCodeHattedDart rL Q a ∈ Set.range (lMinusCodePrimedDart rL Q) :=
      ⟨d, ha.symm⟩
    obtain ⟨i, b, he⟩ :=
      (lMinusCodeHattedDart_mem_primed_iff hτ hp P hqMode Tpath hfin hleft hk a).mp hm
    exact hd i b (ha.symm.trans he)
  rw [lMinusCodeInitialSplicedRotation_apply_of_ne rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin) _ (by
      intro he
      apply hnH
      rw [he, lMinusCodeHattedRotation_initial_predecessor]
      exact ⟨_, rfl⟩) hb]
  exact lMinusCodeInitialAdjustedRotation_primed_interior
    hτ hp P hqMode Tpath hfin hleft hk d hd





































































end GeometricGluing
end DirectedDistances.PaperProofs.Section5
