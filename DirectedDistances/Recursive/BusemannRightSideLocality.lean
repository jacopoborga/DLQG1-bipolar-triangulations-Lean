module

public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.KMSW.FutureMapHatLaw
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
public import DirectedDistances.KMSW.InftyCutP1Compose
import DirectedDistances.KMSW.DirectedContainHat

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

The named propositions below record the dependency chain without assuming it.
`RightHatPathLengthIdentification`, `RightHatBoundaryIdentification`, and
`RightHatIntegratedCarrierIdentification` are proved here. They concern the entire
root-reachable hatted carrier, before cutting at a geodesic.
Downstream proofs cover the thin-boundary identification and closed-side localization:
Proved downstream: `rightHatThinBoundaryIdentification_proved` in
`Recursive/BusemannRightSideLocalization.lean`.
Proved downstream: `rightClosedSideLdpLocalization_proved` in
`Recursive/BusemannRightSideLocalization.lean`.
Proved downstream: `rightHatThinBoundarySdpIdentification_proved` in
`Recursive/BusemannRightSideLocalizationSdp.lean`.
Proved downstream: `rightClosedSideSdpLocalization_proved` in
`Recursive/BusemannRightSideLocalizationSdp.lean`.
Downstream proofs also cover the finite-code formula and measurable factorization:
Proved downstream: `rightTruncationLdpFormula_proved` in
`Recursive/BusemannRightTruncationFormula.lean`.
Proved downstream: `rightBusemannLdpLocality_proved` in
`Recursive/BusemannRightTruncationFormula.lean`.
Proved downstream: `rightTruncationSdpFormula_proved` in
`Recursive/BusemannRightTruncationFormulaSdp.lean`.
Proved downstream: `rightBusemannSdpLocality_proved` in
`Recursive/BusemannRightTruncationFormulaSdp.lean`. None is a theorem premise.

The finite quotient retains root, target, indexed boundary and seam relations
(`ThinHalfTruncate.truncationRelation`); no boundary-forgetting obstruction is asserted.
Those proofs identify the indexed markings with raw hit-indexed vertices and confine
the extremal distances to the side.
For SDP the carrier lemmas are unchanged, but the seam tag is `.sdp`, maxima become
minima, and `boundarySdpDifference` replaces `boundaryLdpDifference` in the code formula. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "RightDomain" =>
  selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "P" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "RB" => fun (q : RightDomain) (j : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.right j
local notation "Tldp" =>
  thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "Tsdp" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable lengths inside the literal closed right side at the canonical leftmost -/
@[expose] def rightSideLdpLengths (q : RightDomain) (j m : ℕ) : Set ℕ :=
  {n | ∃ p : Path (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩,
    p.length = n ∧ ∀ e ∈ pathEdgeList p,
      e ∈ sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
First carrier obligation: the coherent vertex map preserves every attainable length. -/
@[expose] def RightHatPathLengthIdentification : Prop :=
  ∀ (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : PresentVertex (hatCodes w h)),
    pathLengths a b = pathLengths
      (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w) ⟨hatLimitVertexMap w h b.id⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Positive boundary vertices have a rooted injective lift to the compressed carrier,
and all distances between these lifts have exactly the raw path-length sets.
This does not yet identify the lift with the thin code's boundary marking. -/
@[expose] def RightHatBoundaryIdentification : Prop :=
  ∀ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w),
    ∃ b : ℕ → PresentVertex (hatCodes w h),
      b 0 = ⟨0⟩ ∧ Function.Injective b ∧
      (∀ j, hatLimitVertexMap w h (b j).id = boundaryVertex w hb (j : ℤ)) ∧
      ∀ j k, pathLengths (b j) (b k) =
        pathLengths (boundaryPresentVertex w hb (j : ℤ))
          (boundaryPresentVertex w hb (k : ℤ))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integrated hatted path belongs to the thin-code domain, whose decoded stream is
exactly the compressed stream. The lifted boundary has the allocation IDs used by
the measurable Busemann representative. This is proved below, before any side cut. -/
@[expose] def RightHatIntegratedCarrierIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : RightDomain)
      (b : ℕ → PresentVertex (hatCodes w h)),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
      b 0 = ⟨0⟩ ∧ Function.Injective b ∧
      (∀ j, hatLimitVertexMap w h (b j).id = busemannBoundaryIdTotal ω (j : ℤ)) ∧
      ∀ j k, pathLengths (b j) (b k) =
        pathLengths
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (j : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (k : ℤ))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream: `rightHatThinBoundaryIdentification_proved` in
`Recursive/BusemannRightSideLocalization.lean`. The actual right boundary used by the
thin code maps to every nonnegative raw boundary index. -/
@[expose] def RightHatThinBoundaryIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : RightDomain),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
      ∀ j, hatLimitVertexMap w h (RB q j) =
        boundaryVertex w (hatBoundaryHitWitnesses w h) (j : ℤ)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream: `rightClosedSideLdpLocalization_proved` in
`Recursive/BusemannRightSideLocalization.lean`. The maxima are attained in the closed
right side and equal the raw LDP distances to sufficiently late boundary targets.
Their difference computes the representative's finite-target value, with no -/
@[expose] def RightClosedSideLdpLocalization : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : RightDomain),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
      (∀ j, hatLimitVertexMap w h (RB q j) =
        boundaryVertex w (hatBoundaryHitWitnesses w h) (j : ℤ)) ∧
      ∀ j : ℕ, ∀ᶠ m in atTop, ∃ nj n0 : ℕ,
        IsGreatest (rightSideLdpLengths q j m) nj ∧
        IsGreatest (rightSideLdpLengths q 0 m) n0 ∧
        ldpSup (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (j : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) =
          (nj : WithBot ℕ) ∧
        ldpSup (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) 0)
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) =
          (n0 : WithBot ℕ) ∧
        boundaryLdpDifference ω (j : ℤ) m = (nj : ℤ) - (n0 : ℤ)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream: `rightTruncationLdpFormula_proved` in
`Recursive/BusemannRightTruncationFormula.lean`. A measurable finite marked-map
decoder, followed by an eventual value in the truncation index, recovers each
sufficiently late finite-target difference. A second eventual value in `m` gives the
desired profile factorization. -/
@[expose] def RightTruncationLdpFormula : Prop :=
  ∃ d : ℕ → ℕ → ℕ → Option FiniteThinMap → ℤ,
    (∀ j m s, Measurable (d j m s)) ∧
    ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ, ∀ᶠ m in atTop,
      boundaryLdpDifference ω (j : ℤ) m =
        eventualIntValue 0 (fun s =>
          d j m s (Tldp .right (integrateCodes (hatLawCodes ω)) s))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream: `rightBusemannLdpLocality_proved` in
`Recursive/BusemannRightTruncationFormula.lean`. This is the exact LDP locality target,
on the original iid code space. -/
@[expose] def RightBusemannLdpLocality : Prop :=
  ∃ FR : ThinCode → ℕ → ℤ, Measurable FR ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      (fun j : ℕ => busemannLDPMeasurableVersion ω (j : ℤ)) =
        FR (Tldp .right (integrateCodes (hatLawCodes ω)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream: `rightBusemannSdpLocality_proved` in
`Recursive/BusemannRightTruncationFormulaSdp.lean`. The analogous SDP target uses the
`.sdp` seam code, not the LDP seam code. -/
@[expose] def RightBusemannSdpLocality : Prop :=
  ∃ FR : ThinCode → ℕ → ℤ, Measurable FR ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      (fun j : ℕ => busemannSDPMeasurableVersion ω (j : ℤ)) =
        FR (Tsdp .right (integrateCodes (hatLawCodes ω)))

private noncomputable def rightHatPrefunctor (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    Prefunctor (PresentVertex (hatCodes w h)) (PresentVertex w) where
  obj a := ⟨hatLimitVertexMap w h a.id⟩
  map {a b} e := by
    have hi := hatLimit_edge_incidence (hatLimitExplicitInput w h) e.property.1
    exact ⟨hatLimitEdgeMap w h e.val, hi.1,
      hi.2.1.trans (congrArg (hatLimitVertexMap w h) e.property.2.1),
      hi.2.2.trans (congrArg (hatLimitVertexMap w h) e.property.2.2)⟩

private theorem rightHat_map_length (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {a b : PresentVertex (hatCodes w h)} (p : Path a b) :
    ((rightHatPrefunctor w h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem rightHat_lift_aux (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {a : PresentVertex (hatCodes w h)} {y : PresentVertex w}
    (p : Path ((rightHatPrefunctor w h).obj a) y) :
    ∃ b : PresentVertex (hatCodes w h), ∃ q : Path a b,
      (rightHatPrefunctor w h).obj b = y ∧ q.length = p.length := by
  let D := hatLimitExplicitInput w h
  induction p with
  | nil => exact ⟨a, Path.nil, rfl, rfl⟩
  | @cons x y p e ih =>
    obtain ⟨b, q, hb, hlen⟩ := ih
    have hx : Reachable (⟨0⟩ : PresentVertex w) x := by
      rw [← hb]
      exact alloc_reachable D (kmswVertexAllocated_all _ b)
    have hy : Reachable (⟨0⟩ : PresentVertex w) y :=
      hx.trans e.toPath.reachable
    obtain ⟨j, hj, hje⟩ := edge_cover D e.property.1
      (by rw [e.property.2.1]; exact hx)
      (by rw [e.property.2.2]; exact hy)
    have hi := hatLimit_edge_incidence D hj
    have hw : hatLimitVertexMap w h (edgeWest (hatCodes w h) j) =
        hatLimitVertexMap w h b.id := by
      rw [← hi.2.1, hje, e.property.2.1]
      exact congrArg PresentVertex.id hb.symm
    have hs : edgeWest (hatCodes w h) j = b.id :=
      vertex_inj D (kmswVertexAllocated_all _ ⟨edgeWest (hatCodes w h) j⟩)
        (kmswVertexAllocated_all _ b) hw
    let c : PresentVertex (hatCodes w h) := ⟨edgeEast (hatCodes w h) j⟩
    let f : b ⟶ c := ⟨j, hj, hs, rfl⟩
    refine ⟨c, q.cons f, ?_, ?_⟩
    · apply congrArg PresentVertex.mk
      exact hi.2.2.symm.trans ((congrArg (edgeEast w) hje).trans e.property.2.2)
    · simp only [Path.length_cons, hlen]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw path between two hatted vertex images lifts with the same length.
The proof uses the exact present-edge image and injectivity of the vertex map. -/
theorem rightHat_path_lift (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : PresentVertex (hatCodes w h))
    (p : Path (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w)
      ⟨hatLimitVertexMap w h b.id⟩) :
    ∃ q : Path a b, q.length = p.length := by
  obtain ⟨c, q, hc, hlen⟩ := rightHat_lift_aux w h p
  have hcb : c = b := by
    have hid := vertex_inj (hatLimitExplicitInput w h)
      (kmswVertexAllocated_all _ c) (kmswVertexAllocated_all _ b)
      (congrArg PresentVertex.id hc)
    exact congrArg PresentVertex.mk hid
  subst c
  exact ⟨q, hlen⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proof of the first named carrier obligation, including unreachable endpoint pairs. -/
theorem rightHatPathLengthIdentification_proved : RightHatPathLengthIdentification := by
  intro w h a b
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(rightHatPrefunctor w h).mapPath p, rightHat_map_length w h p⟩
  · rintro ⟨p, rfl⟩
    exact rightHat_path_lift w h a b p

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted carrier has exactly the same LDP supremum at mapped endpoints.
This equality does not assert boundedness of an arbitrary infinite-quiver supremum. -/
theorem rightHat_ldpSup (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : PresentVertex (hatCodes w h)) :
    ldpSup a b = ldpSup
      (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w) ⟨hatLimitVertexMap w h b.id⟩ := by
  unfold ldpSup
  rw [rightHatPathLengthIdentification_proved w h a b]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The same path lift preserves SDP, including the unreachable value `⊤`. -/
theorem rightHat_sdp (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : PresentVertex (hatCodes w h)) :
    sdp a b = sdp
      (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w) ⟨hatLimitVertexMap w h b.id⟩ := by
  apply le_antisymm
  · apply le_iInf
    intro p
    obtain ⟨q, hq⟩ := rightHat_path_lift w h a b p
    exact (sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hq)
  · apply le_iInf
    intro p
    exact (sdp_le_length ((rightHatPrefunctor w h).mapPath p)).trans_eq
      (congrArg (fun n : ℕ => (n : ℕ∞)) (rightHat_map_length w h p))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The proper extended LDP is preserved, including bottom for unreachable endpoints and -/
theorem rightHat_presentLdp (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : PresentVertex (hatCodes w h)) :
    presentLdp a b = presentLdp
      (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w) ⟨hatLimitVertexMap w h b.id⟩ := by
  apply le_antisymm
  · apply iSup_le
    intro p
    have hlen := rightHat_map_length w h p
    exact (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hlen).symm.trans_le
      (le_iSup (fun q => ((q.length : ℕ∞) : WithBot ℕ∞))
        ((rightHatPrefunctor w h).mapPath p))
  · apply iSup_le
    intro p
    obtain ⟨q, hq⟩ := rightHat_path_lift w h a b p
    exact (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hq).symm.trans_le
      (le_iSup (fun q : Path a b => ((q.length : ℕ∞) : WithBot ℕ∞)) q)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Under ambient finite incidence, a reachable pair has one common attained finite LDP
value in both carriers. Thus later Busemann subtraction can use finite distances. -/
theorem rightHat_reachable_ldp_finite (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (a b : PresentVertex (hatCodes w h))
    (hr : Reachable a b) :
    ∃ n : ℕ, presentLdp a b = ((n : ℕ∞) : WithBot ℕ∞) ∧
      presentLdp (⟨hatLimitVertexMap w h a.id⟩ : PresentVertex w)
        ⟨hatLimitVertexMap w h b.id⟩ = ((n : ℕ∞) : WithBot ℕ∞) := by
  have hb := presentPathLengthsBounded_of_hfin (hatCodes w h)
    (hatCodes_finiteIncidence w h hfin)
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  refine ⟨p.length, presentLdp_eq_length hp, ?_⟩
  exact (rightHat_presentLdp w h a b).symm.trans (presentLdp_eq_length hp)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proof of the second named carrier obligation. Nonnegative raw boundary vertices
are root-reachable; the explicit vertex equivalence supplies their unique lifts. -/
theorem rightHatBoundaryIdentification_proved : RightHatBoundaryIdentification := by
  intro w h hb
  classical
  have hr (j : ℕ) : Reachable (⟨0⟩ : PresentVertex w)
      (boundaryPresentVertex w hb (j : ℤ)) := by
    have hh := boundaryVertex_nonneg_reachable w hb (k := 0) (l := (j : ℤ))
      le_rfl (Int.natCast_nonneg j)
    simpa only [boundaryPresentVertex, boundaryVertex_zero] using hh
  let E := hatExplicitVertexEquiv w h
  let b : ℕ → PresentVertex (hatCodes w h) := fun j =>
    (E.symm ⟨boundaryPresentVertex w hb (j : ℤ), hr j⟩).1
  have he (j : ℕ) : hatLimitVertexMap w h (b j).id =
      boundaryVertex w hb (j : ℤ) := by
    have hh := congrArg (fun v => v.1.id)
      (E.apply_symm_apply ⟨boundaryPresentVertex w hb (j : ℤ), hr j⟩)
    exact hh
  have hz : b 0 = ⟨0⟩ := by
    apply congrArg PresentVertex.mk
    apply vertex_inj (hatLimitExplicitInput w h)
      (kmswVertexAllocated_all _ (b 0)) (kmswVertexAllocated_all _ ⟨0⟩)
    rw [he 0, Nat.cast_zero, boundaryVertex_zero]
    exact (hatLimitExplicitInput w h).root.symm
  refine ⟨b, hz, ?_, he, ?_⟩
  · intro i j hij
    have hh : boundaryVertex w hb (i : ℤ) = boundaryVertex w hb (j : ℤ) := by
      rw [← he i, ← he j, hij]
    have hh' := boundaryVertex_injective w hb hh
    exact_mod_cast hh'
  · intro j k
    have hh := rightHatPathLengthIdentification_proved w h (b j) (b k)
    simpa only [he j, he k, boundaryPresentVertex] using hh

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The total boundary ID used by the measurable version equals the hit-indexed boundary
ID wherever boundary witnesses exist, including indices zero and one. -/
theorem rightHat_boundaryIdTotal_eq (ω : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) :
    busemannBoundaryIdTotal ω k = boundaryVertex (fun i => ω (i + 1)) hb k := by
  unfold busemannBoundaryIdTotal
  rw [boundaryHitTimeTotal_eq_boundaryHitTime ω hb k, ENat.toNat_natCast]
  rw [boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
On the coherent domain the stream read by the thin code is precisely the code stream -/
theorem rightHat_coherent_stream (q : RightDomain) (c : ℕ → Fin 3)
    (hc : q.1 = integrateCodes c) : (W q) = c := by
  obtain ⟨_, _, _, _, hw, _⟩ := selectedCutCoherentDomain_spec
    XDP.ldp renewalTime renewalTime_positiveSuccessTime q
  exact integrateCodes_injective (hw.trans hc)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost surely the integrated compressed path lies in the exact domain on which the -/
theorem rightHat_integrate_mem_coherent_ae :
    ∀ᵐ ω ∂iidCodeMeasure, integrateCodes (hatLawCodes ω) ∈ RightDomain := by
  have hd : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, p ∈ RightDomain :=
    ae_iff.mpr (selectedCutCoherentDomain_measurable_conull
      XDP.ldp renewalTime renewalTime_positiveSuccessTime).2
  have hm : AEMeasurable (fun ω => integrateCodes (hatLawCodes ω)) iidCodeMeasure :=
    measurable_integrateCodes.comp_aemeasurable aemeasurable_hatLawCodes.1
  exact ae_of_ae_map hm (hatLawCodes_integrate_law.symm ▸ hd)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proof of the integrated carrier and raw boundary-ID obligation. It uses the proved
law of the compressed path, not an additional side-locality assumption. -/
theorem rightHatIntegratedCarrierIdentification_proved :
    RightHatIntegratedCarrierIdentification := by
  filter_upwards [rightHat_integrate_mem_coherent_ae,
    iidCodeMeasure_ae_hasFlowLineHits] with ω hq h
  let w := fun i => ω (i + 1)
  let q : RightDomain := ⟨integrateCodes (hatLawCodes ω), hq⟩
  have hc : hatLawCodes ω = hatCodes w h := by
    dsimp only [w]
    simp only [hatLawCodes, dite_eq_left h]
  obtain ⟨b, hb0, hbinj, hbmap, hblen⟩ :=
    rightHatBoundaryIdentification_proved w h (hatBoundaryHitWitnesses w h)
  refine ⟨h, q, b, rfl, (rightHat_coherent_stream q _ rfl).trans hc,
    hb0, hbinj, ?_, hblen⟩
  intro j
  exact (hbmap j).trans
    (rightHat_boundaryIdTotal_eq ω (hatBoundaryHitWitnesses w h) (j : ℤ)).symm

end DirectedDistances.Recursive
