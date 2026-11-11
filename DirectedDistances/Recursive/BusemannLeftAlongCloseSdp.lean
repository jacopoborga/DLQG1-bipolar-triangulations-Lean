module

public import DirectedDistances.Recursive.BusemannLeftAlongGeodesicSdp
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.BusemannRightSideLocality
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport








public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "SdpDomain" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "Q" q => sourceAncestorPath
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "SE" => fun (q : SdpDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a
local notation "SV" => fun (q : SdpDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The minimum lengths of paths in a specified closed-left edge carrier. -/
@[expose] def leftClosedSdpSidePathLengths (w : ℕ → Fin 3)
    (closedLeftEdges : Set ℕ) (x y : PresentVertex w) : Set ℕ :=
  {n | ∃ p : Path x y, p.length = n ∧
    ∀ e ∈ pathEdgeList p, e ∈ closedLeftEdges}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The precise left-profile formula for a raw shortest seam and its closed-left carrier.
The eventual boundary difference and the measurable representative share `c`. -/
@[expose] def LeftBusemannAlongSdpGeodesic (ω : ℕ → Fin 3)
    (P : InfinitePresentPath (fun i => ω (i + 1)) ⟨0⟩)
    (closedLeftEdges : Set ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ c : ℤ,
    busemannSDPMeasurableVersion ω (-(j : ℤ)) = c ∧
    (∀ᶠ m in Filter.atTop, boundarySdpDifference ω (-(j : ℤ)) m = c) ∧
    ∀ᶠ t in Filter.atTop, ∃ n : ℕ,
      IsLeast (leftClosedSdpSidePathLengths (fun i => ω (i + 1)) closedLeftEdges
        ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ (P.initial t).1) n ∧
      sdp (⟨0⟩ : PresentVertex (fun i => ω (i + 1))) (P.initial t).1 =
        (t : ℕ∞) ∧ (n : ℤ) - (t : ℤ) = c

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The almost-sure left-profile formula for the selected Section 4 SDP seam. -/
@[expose] def LeftAlongSdpBusemannFormulaAE : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : SdpDomain)
      (hw : (W q) = hatCodes w h),
      q.1 = integrateCodes (hatLawCodes ω) ∧
      LeftBusemannAlongSdpGeodesic ω
        (leftAlongRawSdpGeodesic w h q hw) (closedLeftSdpEdges w h q)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A strictly negative boundary vertex is outside the root-reachable hatted map. -/
private theorem closeSdpNegative_outside (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (j : ℕ) (hj : 1 ≤ j) :
    boundaryPresentVertex w hb (-(j : ℤ)) ∉ leftHatVertices w := by
  have hne : boundaryVertex w hb (-(j : ℤ)) ≠ 0 := by
    intro he
    have hh := boundaryVertex_injective w hb
      (he.trans (boundaryVertex_zero w hb).symm)
    omega
  have noReach (v : PresentVertex w) (hne : v.id ≠ 0)
      (hno : ∀ e, EdgePresent w e → edgeEast w e ≠ v.id) :
      ¬ Reachable (⟨0⟩ : PresentVertex w) v := by
    rintro ⟨p⟩
    cases p with
    | nil => exact hne rfl
    | cons p e => exact hno e.val e.property.1 e.property.2.2
  exact noReach _ hne
    (fun e he => boundaryVertex_nonpos_no_incoming w hb (by omega) e he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An allocated vertex reaches a tail of the nonnegative boundary. -/
private theorem closeSdpAlongReachesBoundaryTail (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (v : PresentVertex w)
    (hv : kmswVertexAllocated w v) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w hb l) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨k, hkrec, _⟩ :=
    (right_record_infinite w hb.R_unbounded_below).exists_gt n
  have hkpos : 0 < k := by omega
  have hrec : ∀ i < k, R w k < R w i := hkrec
  have hneg : R w k < 0 := by
    have hh := hrec 0 hkpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w k
  have hbpos : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w hb b = k := by
    have hle : boundaryHitTime w hb b ≤ k := by
      rw [boundaryHitTime_right_eq_find w hb hbpos]
      exact Nat.find_min' (hb.rightHit b hbpos) (by dsimp [b]; omega)
    have hge : k ≤ boundaryHitTime w hb b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w hb b) (by omega)
      have hh' := boundaryHitTime_right_spec w hb hbpos
      rw [hh'] at hh
      have hRb : R w k = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w k = boundaryPresentVertex w hb b := by
    apply congrArg PresentVertex.mk
    have he := edge_endpoints_eq w (act_lt_nextEdge w (le_refl k))
    rw [boundaryVertex_eq_edgeWest_hit w hb b, htime]
    exact he.1
  have hvk : v.id < (kmswStage w (k - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ k - 1))
  have hr : Reachable v (boundaryPresentVertex w hb b) := by
    have hh := allocated_vertex_reaches_strict_record w k
      (fun i hi => by have := hrec i hi; omega) hkpos v.id hvk
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w hb (by omega) (by omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite present path appears in every sufficiently late finite stage. -/
private theorem closeSdpPathInLateStages {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ q : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩,
        q.length = p.length := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨Path.nil, rfl⟩⟩
  | @cons b c p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := e.property.1.eventually_present
    refine ⟨max N M, fun n hn => ?_⟩
    obtain ⟨q, hq⟩ := hN n ((Nat.le_max_left _ _).trans hn)
    obtain ⟨he, hp⟩ := hM n ((Nat.le_max_right _ _).trans hn)
    let en : (⟨b.id⟩ : StagePresentVertex w n) ⟶ ⟨c.id⟩ :=
      ⟨e.val, he, hp,
        (edge_endpoints_eq w he).1.trans e.property.2.1,
        (edge_endpoints_eq w he).2.trans e.property.2.2⟩
    exact ⟨q.cons en, by simp only [Path.length_cons, hq]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
At reachable endpoints the finite-stage SDP code eventually equals raw SDP. -/
private theorem closeSdpStageCodeEventuallyEq (ω : ℕ → Fin 3)
    {a b : PresentVertex (fun i => ω (i + 1))} (hr : Reachable a b) :
    ∀ᶠ n in atTop, busemannStageSdpCode ω n a.id b.id =
      ((sdp a b).toNat : ℤ) := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
  obtain ⟨N, hN⟩ := closeSdpPathInLateStages p
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn
  have heq : sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
      ⟨b.id⟩ = sdp a b := by
    apply le_antisymm
    · calc
        sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩
            ≤ (q.length : ℕ∞) := sdp_le_length q
        _ = (p.length : ℕ∞) := by rw [hq]
        _ = sdp a b := hp
    · exact sdp_limit_le_sdp_stage (fun i => ω (i + 1)) n ⟨a.id⟩ ⟨b.id⟩
  unfold busemannStageSdpCode
  rw [heq]
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The stage-defined boundary difference equals its raw finite SDP difference. -/
private theorem closeSdpBoundaryDifferenceEq (ω : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) (m : ℕ)
    (hr0 : Reachable (boundaryPresentVertex _ hb 0)
      (boundaryPresentVertex _ hb (m : ℤ)))
    (hrk : Reachable (boundaryPresentVertex _ hb k)
      (boundaryPresentVertex _ hb (m : ℤ))) :
    boundarySdpDifference ω k m =
      ((sdp (boundaryPresentVertex _ hb k)
          (boundaryPresentVertex _ hb (m : ℤ))).toNat : ℤ) -
        ((sdp (boundaryPresentVertex _ hb 0)
          (boundaryPresentVertex _ hb (m : ℤ))).toNat : ℤ) := by
  unfold boundarySdpDifference
  rw [rightHat_boundaryIdTotal_eq ω hb k,
    rightHat_boundaryIdTotal_eq ω hb 0,
    rightHat_boundaryIdTotal_eq ω hb (m : ℤ)]
  apply eventualIntValue_eq
  filter_upwards [closeSdpStageCodeEventuallyEq ω hrk,
    closeSdpStageCodeEventuallyEq ω hr0] with n hk h0
  exact congrArg₂ (· - ·) hk h0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The boundary SDP differences eventually equal the characterized Busemann value. -/
private theorem closeSdpBoundaryEventually (ω : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) hb) X)
    (k : ℤ) : ∀ᶠ m in atTop, boundarySdpDifference ω k m = X k := by
  let w := fun i => ω (i + 1)
  obtain ⟨B0, hB0⟩ := closeSdpAlongReachesBoundaryTail w hb
    (boundaryPresentVertex w hb 0) (boundaryVertex_allocated w hb 0)
  obtain ⟨Bk, hBk⟩ := closeSdpAlongReachesBoundaryTail w hb
    (boundaryPresentVertex w hb k) (boundaryVertex_allocated w hb k)
  let B := max B0 Bk
  let y : ℕ → PresentVertex w := fun j =>
    boundaryPresentVertex w hb ((B + j : ℕ) : ℤ)
  have hy : Function.Injective y := by
    intro i j hij
    have hh := boundaryVertex_injective w hb (congrArg PresentVertex.id hij)
    dsimp [y, boundaryPresentVertex] at hh
    omega
  have hr : ∀ j, Reachable (boundaryPresentVertex w hb 0) (y j) ∧
      Reachable (boundaryPresentVertex w hb k) (y j) := by
    intro j
    exact ⟨hB0 _ (by dsimp [B]; omega), hBk _ (by dsimp [B]; omega)⟩
  obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
  refine eventually_atTop.mpr ⟨B + N, fun m hm => ?_⟩
  let j := m - B
  have hj : B + j = m := by dsimp [j]; omega
  have heq := closeSdpBoundaryDifferenceEq ω hb k (B + j)
    (hr j).1 (hr j).2
  have hx := hN j (by dsimp [j]; omega)
  rw [hX.1, sub_zero] at hx
  exact (congrArg (boundarySdpDifference ω k) hj).symm.trans (heq.trans hx.symm)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integrated compressed path lies in the selected SDP coherent domain almost surely. -/
private theorem closeSdpIntegratedCarrier_ae :
    ∀ᵐ ω ∂iidCodeMeasure, integrateCodes (hatLawCodes ω) ∈ SdpDomain := by
  have hd : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, p ∈ SdpDomain :=
    ae_iff.mpr (selectedCutCoherentDomain_measurable_conull
      XDP.sdp renewalTime renewalTime_positiveSuccessTime).2
  have hm : AEMeasurable (fun ω => integrateCodes (hatLawCodes ω)) iidCodeMeasure :=
    measurable_integrateCodes.comp_aemeasurable aemeasurable_hatLawCodes.1
  exact ae_of_ae_map hm (hatLawCodes_integrate_law.symm ▸ hd)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw vertex reaches some seam vertex by cut-vertex incidence. -/
theorem leftAlongRawSdpGeodesic_reachable_some (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (x : PresentVertex w) :
    ∃ i, Reachable x ((leftAlongRawSdpGeodesic w h q hw).initial i).1 := by
  let hb := hatBoundaryHitWitnesses w h
  obtain ⟨B, hB⟩ := closeSdpAlongReachesBoundaryTail w hb x
    (kmswVertexAllocated_all w x)
  obtain ⟨b, _, _, hbmap, _⟩ := rightHatBoundaryIdentification_proved w h hb
  have hcuts : {v : ℕ | mapCutVertex (W q) (HF q) v}.Infinite := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hcuts, _⟩ :=
      selectedCutCoherentDomain_spec XDP.sdp renewalTime
        renewalTime_positiveSuccessTime q
    exact hcuts
  obtain ⟨i, p⟩ := vertex_reachable_seam_of_infinite_cutVertices
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) hcuts (b B).id
  obtain ⟨p⟩ := p
  have hm : Reachable (⟨hatLimitVertexMap w h (b B).id⟩ : PresentVertex w)
      ((leftAlongRawSdpGeodesic w h q hw).initial i).1 := by
    rw [leftAlongRawSdpGeodesic_vertex]
    exact ⟨(alongSdpHatFunctor w h q hw).mapPath p⟩
  have hbv : (⟨hatLimitVertexMap w h (b B).id⟩ : PresentVertex w) =
      boundaryPresentVertex w hb (B : ℤ) := congrArg PresentVertex.mk (hbmap B)
  rw [hbv] at hm
  exact ⟨i, (hB (B : ℤ) le_rfl).trans hm⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw vertex reaches all sufficiently late seam vertices. -/
theorem leftAlongRawSdpGeodesic_eventually_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (x : PresentVertex w) :
    ∀ᶠ t in atTop, Reachable x ((leftAlongRawSdpGeodesic w h q hw).initial t).1 := by
  obtain ⟨i, hi⟩ := leftAlongRawSdpGeodesic_reachable_some w h q hw x
  refine eventually_atTop.mpr ⟨i, fun t ht => hi.trans ?_⟩
  have H := (leftAlongRawSdpGeodesic w h q hw).exists_shift_split i (t - i)
  rw [Nat.add_sub_of_le ht] at H
  obtain ⟨_, r, _, _, _, _⟩ := H
  exact r.reachable

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The attained closed-left minimum equals the finite raw SDP distance. -/
theorem leftAlongClosedLeftSdp_least (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (x : PresentVertex w)
    (hx : x ∈ closedLeftSdpVertices w h q) (t : ℕ)
    (hr : Reachable x ((leftAlongRawSdpGeodesic w h q hw).initial t).1) :
    ∃ n : ℕ, IsLeast (leftClosedSdpSidePathLengths w
      (closedLeftSdpEdges w h q) x
      ((leftAlongRawSdpGeodesic w h q hw).initial t).1) n ∧
      sdp x ((leftAlongRawSdpGeodesic w h q hw).initial t).1 = (n : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_isShortest hr
  have hyr : ((leftAlongRawSdpGeodesic w h q hw).initial t).1 ∈
      closedRightSdpVertices w h q := by
    rw [leftAlongRawSdpGeodesic_vertex]
    exact ⟨((Q q).initial t).1.id,
      seamVertex_mem_sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (Q q)
        .right t, rfl⟩
  obtain ⟨i, a, b, hlen, _, ha, _, ht⟩ :=
    leftAlongRawSdpGeodesicExchange_proved w h hfin q hw x hx _ hyr p hp
  have hti : t = i := ht t b.end_mem_vertices
  subst i
  have hb0 := presentVertex_acyclic w _ b
  have halen : a.length = p.length := by omega
  refine ⟨a.length, ⟨⟨a, rfl, ha⟩, ?_⟩, ?_⟩
  · rintro m ⟨r, rfl, _⟩
    rw [halen]
    exact hp r
  · calc
      sdp x ((leftAlongRawSdpGeodesic w h q hw).initial t).1 =
          (p.length : ℕ∞) := (isShortest_iff_length_eq_sdp p).mp hp |>.symm
      _ = (a.length : ℕ∞) := congrArg (fun n : ℕ => (n : ℕ∞)) halen.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Boundary Busemann differences give the closed-left minimum profile on the raw SDP seam. -/
private theorem closeSdpSeamFormula (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hfin : hatLimitFiniteIncidence (fun i => ω (i + 1)))
    (q : SdpDomain) (hw : (W q) = hatCodes (fun i => ω (i + 1)) h)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) hb) X)
    (hversion : busemannSDPMeasurableVersion ω = X) :
    LeftBusemannAlongSdpGeodesic ω
      (leftAlongRawSdpGeodesic (fun i => ω (i + 1)) h q hw)
      (closedLeftSdpEdges (fun i => ω (i + 1)) h q) := by
  let w := fun i => ω (i + 1)
  let P := leftAlongRawSdpGeodesic w h q hw
  intro j hj
  let k : ℤ := -(j : ℤ)
  rw [rightHat_boundaryIdTotal_eq ω hb k]
  let x := boundaryPresentVertex w hb k
  have hboundary := closeSdpBoundaryEventually ω hb X hX k
  have hx : x ∈ closedLeftSdpVertices w h q :=
    Or.inl (closeSdpNegative_outside w hb j hj)
  have hxreach := leftAlongRawSdpGeodesic_eventually_reachable w h q hw x
  obtain ⟨B, hB⟩ := eventually_atTop.mp hxreach
  let y : ℕ → PresentVertex w := fun i => (P.initial (B + i)).1
  have hy : Function.Injective y := by
    intro i l hil
    have hd := congrArg (fun z => sdp (⟨0⟩ : PresentVertex w) z) hil
    rw [leftAlongRawSdpGeodesic_root_distance w h q hw (B + i),
      leftAlongRawSdpGeodesic_root_distance w h q hw (B + l)] at hd
    have hnat := ENat.natCast_inj.mp hd
    omega
  have hr : ∀ i, Reachable (boundaryPresentVertex w hb 0) (y i) ∧
      Reachable x (y i) := by
    intro i
    refine ⟨?_, hB (B + i) (by omega)⟩
    simpa only [boundaryPresentVertex, boundaryVertex_zero] using
      (P.initial (B + i)).2.reachable
  obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
  have htail : ∀ᶠ m in atTop, boundarySdpDifference ω k m = X k := hboundary
  refine ⟨X k, congrFun hversion k, ?_, ?_⟩
  · simpa only [k] using htail
  · refine eventually_atTop.mpr ⟨B + N, fun t ht => ?_⟩
    let i := t - B
    have hi : B + i = t := by dsimp [i]; omega
    have hmin := leftAlongClosedLeftSdp_least
      w h hfin q hw x hx (B + i) (hB (B + i) (by omega))
    rw [hi] at hmin
    obtain ⟨n, hn, hnval⟩ := hmin
    rw [← hi] at hnval
    have hdiff := hN i (by dsimp [i]; omega)
    rw [hX.1, sub_zero] at hdiff
    have hsdp : sdp (boundaryPresentVertex w hb k) (y i) = (n : ℕ∞) := by
      simpa only [x, y, P, w] using hnval
    have hroot : sdp (boundaryPresentVertex w hb 0) (y i) =
        ((B + i : ℕ) : ℕ∞) := by
      simpa only [y, P, w, boundaryPresentVertex, boundaryVertex_zero] using
        leftAlongRawSdpGeodesic_root_distance w h q hw (B + i)
    have hdiff' : X k = (n : ℤ) - (B + i : ℕ) := by
      rw [hsdp, hroot, ENat.toNat_natCast, ENat.toNat_natCast] at hdiff
      exact hdiff
    refine ⟨n, hn, leftAlongRawSdpGeodesic_root_distance w h q hw t, ?_⟩
    rw [← hi]
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The almost-sure closed-left SDP profile follows from the source carrier and boundary -/
theorem leftAlongSdpBusemannFormulaAE_proved : LeftAlongSdpBusemannFormulaAE := by
  filter_upwards [closeSdpIntegratedCarrier_ae, iidCodeMeasure_ae_hasFlowLineHits,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryBusemannSDP_existsUnique,
    iidCodes_ae_busemannSDPMeasurableVersion_unique]
    with ω hq h hfinite hω hv
  let w := fun i => ω (i + 1)
  have hfin : hatLimitFiniteIncidence w := by
    intro v
    exact hfinite v
  obtain ⟨hb, X, hX, huniq⟩ := hω
  obtain ⟨hb', hversion', _⟩ := hv
  have hversionData :
      IsBoundaryBusemannSDP (boundaryPresentVertex w hb)
        (busemannSDPMeasurableVersion ω) := by
    have hh : hb' = hb := Subsingleton.elim _ _
    simpa only [hh] using hversion'
  have hversion : busemannSDPMeasurableVersion ω = X := huniq _ hversionData
  let q : SdpDomain := ⟨integrateCodes (hatLawCodes ω), hq⟩
  have hstream : (W q) = hatLawCodes ω := by
    obtain ⟨_, _, _, _, hc, _⟩ :=
      selectedCutCoherentDomain_spec XDP.sdp renewalTime
        renewalTime_positiveSuccessTime q
    exact integrateCodes_injective (hc.trans rfl)
  have hcode : hatLawCodes ω = hatCodes w h := by
    dsimp only [w]
    simp only [hatLawCodes, dite_eq_left h]
  have hw : (W q) = hatCodes w h := hstream.trans hcode
  exact ⟨h, q, hw, rfl,
    closeSdpSeamFormula ω h hfin q hw hb X hX hversion⟩

end DirectedDistances.Recursive
