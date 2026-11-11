module

public import DirectedDistances.PaperProofs.Section4.Lemma414GeodesicFinish
import DirectedDistances.PaperProofs.Section4.SelectedCutGeodesicPrefix

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "RT" => Paper.Section4.renewalTime

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The selected past geodesic prefix exists almost surely on every positive selected-time branch. -/
theorem selectedCutPastCuts_geodesic_prefix_ae
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ p ∂μ,
      ∃ hq : p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime,
        0 < selectedCutTime RT k p →
          let q : selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime :=
    ⟨p, hq⟩
          let w := boltzmannKMSWStream (pathCode q.1)
          let t := (selectedCutTime RT k q.1).toNat
          let r := (-(q.1 t).2).toNat
          ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t)
            (hR : xdpLengthBase R.B x = d)
            (I : DirectedMapWithMissingIso R.B.map
              (kmswStageDirectedMap w (t - 1))),
            selectedCutPastSides x RT renewalTime_positiveSuccessTime k q.1 =
              (Sum.inr (selectedCutPastCuts x RT k q.1).1,
                Sum.inr (selectedCutPastCuts x RT k q.1).2) ∧
            selectedCutPastCuts x RT k q.1 =
              (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1,
                KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
               some ⟨r, ⟨d, ⟨(cutRRep R hR).1,
                KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
            (∀ a : ThinMapSide, (boundaryDarts R.B a).map
              (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
                (match a with
                  | .left => (kmswStage w (t - 1)).UL
                  | .right => (kmswStage w (t - 1)).LR).map
                    (fun e => (e, false))) ∧
            ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
              (fun d => d.1.val) =
                List.ofFn (fun j : Fin d =>
                  (sourceAncestorPath x RT renewalTime_positiveSuccessTime q).edge j.val) := by
  have hq : ∀ᵐ p ∂μ,
      p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime :=
    ae_iff.mpr
      (selectedCutCoherentDomain_measurable_conull x RT renewalTime_positiveSuccessTime).2
  filter_upwards [lemma414PositiveCutLeftBoundaryPos_holds k, hq]
    with p hleft hdomain
  refine ⟨hdomain, ?_⟩
  intro hpos
  let q : selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime := ⟨p, hdomain⟩
  have hleftq :
      0 < (q.1 (selectedCutTime RT k q.1).toNat).1 := by
    simpa only [q] using hleft hpos
  exact selectedCutPastCuts_geodesic_prefix_of_positive_left_boundary
    x RT renewalTime_positiveSuccessTime q k hk hleftq


/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The selected side classes have precisely the closed half-dart carriers cut along the
selected past geodesic, whose edge IDs agree with the source-ancestor prefix. Source: -/
@[expose] def SelectedCutPastClosedHalves
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) (q : selectedCutCoherentDomain x T hT) : Prop :=
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T k q.1).toNat
  let r := (-(q.1 t).2).toNat
  ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t)
    (hR : xdpLengthBase R.B x = d)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
    selectedCutPastSides x T hT k q.1 =
      (Sum.inr (selectedCutPastCuts x T k q.1).1,
        Sum.inr (selectedCutPastCuts x T k q.1).2) ∧
    selectedCutPastCuts x T k q.1 =
      (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1,
        KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨r, ⟨d, ⟨(cutRRep R hR).1,
        KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
    Set.range (cutLRepDartMap R hR) =
      pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR) ∧
    Set.range (cutRRepDartMap R hR) =
      pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) ∧
    (∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
    ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) =
        List.ofFn (fun j : Fin d => (sourceAncestorPath x T hT q).edge j.val)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The selected past classes are the closed left and right halves on a positive cut. -/
theorem selectedCutPastClosedHalves_of_positive_left_boundary
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k : ℕ) (hk : 1 ≤ k)
    (hleft : 0 < (q.1 (selectedCutTime T k q.1).toNat).1) :
    SelectedCutPastClosedHalves x T hT k q := by
  obtain ⟨ℓ, d, R, hR, I, hsides, hcuts, hboundary, hprefix⟩ :=
    selectedCutPastCuts_geodesic_prefix_of_positive_left_boundary
      x T hT q k hk hleft
  refine ⟨ℓ, d, R, hR, I, hsides, hcuts, ?_, ?_, hboundary, hprefix⟩
  · exact cutLRepDartMap_range R hR
  · exact cutRRepDartMap_range R hR

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
Almost surely, positive selected time yields the two closed past halves and the -/
theorem selectedCutPastClosedHalves_ae
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ p ∂μ,
      0 < selectedCutTime RT k p →
        ∃ hq : p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime,
          SelectedCutPastClosedHalves x RT renewalTime_positiveSuccessTime k
            ⟨p, hq⟩ := by
  have hdomain : ∀ᵐ p ∂μ,
      p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime :=
    ae_iff.mpr
      (selectedCutCoherentDomain_measurable_conull x RT renewalTime_positiveSuccessTime).2
  filter_upwards [lemma414PositiveCutLeftBoundaryPos_holds k, hdomain]
    with p hleft hq
  intro hpos
  refine ⟨hq, ?_⟩
  let q : selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime :=
    ⟨p, hq⟩
  have hleft' : 0 < (q.1 (selectedCutTime RT k q.1).toNat).1 := by
    simpa only [q] using hleft hpos
  exact selectedCutPastClosedHalves_of_positive_left_boundary
    x RT renewalTime_positiveSuccessTime q k hk hleft'


/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The selected past geodesic length is the first-visit index of the renewal cut
vertex, and both equal the XDP source distance in the KMSW limit map. Source: -/
@[expose] def SelectedCutPastFirstVisitDistance
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) (q : selectedCutCoherentDomain x T hT) : Prop :=
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T k q.1).toNat
  let r := (-(q.1 t).2).toNat
  ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t)
    (hR : xdpLengthBase R.B x = d)
    (_I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
    (i : ℕ),
    selectedCutPastCuts x T k q.1 =
      (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1,
        KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨r, ⟨d, ⟨(cutRRep R hR).1,
        KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
    i = d ∧
    ((sourceAncestorPath x T hT q).initial i).1 = recordVertex w t ∧
    (∀ j < i, ((sourceAncestorPath x T hT q).initial j).1 ≠ recordVertex w t) ∧
    (match x with
      | .ldp => presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t) =
          (((i : ℕ) : ℕ∞) : WithBot ℕ∞)
      | .sdp => sdp (⟨0⟩ : PresentVertex w) (recordVertex w t) = (i : ℕ∞))

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
At a positive selected cut, its representative length equals the source path's
first-visit index and the XDP distance to that cut vertex. Source: -/
theorem selectedCutPastFirstVisitDistance_of_positive_left_boundary
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k : ℕ) (hk : 1 ≤ k)
    (hleft : 0 < (q.1 (selectedCutTime T k q.1).toNat).1) :
    SelectedCutPastFirstVisitDistance x T hT k q := by
  cases k with
  | zero => omega
  | succ j =>
      let w := boltzmannKMSWStream (pathCode q.1)
      let t := (selectedCutTime T (j + 1) q.1).toNat
      let r := (-(q.1 t).2).toNat
      obtain ⟨ℓ, d, R, hR, I, _, hcuts, _, _, hboundary, _⟩ :=
        selectedCutPastClosedHalves_of_positive_left_boundary
          x T hT q (j + 1) (by omega) hleft
      have hfuture : selectedCutFuture T (j + 1) q.1 0 = q.1 t := by
        simp [selectedCutFuture, conditionedVectorShift, t]
      have hr : 1 ≤ r := by
        by_contra hn
        have hnone : selectedCutPastCuts x T (j + 1) q.1 = (none, none) := by
          simp [selectedCutPastCuts, hfuture, r, hn]
        rw [hnone] at hcuts
        simp at hcuts
      have hright : 0 < -(q.1 t).2 := by
        by_contra hn
        have hn' : -(q.1 t).2 ≤ 0 := by omega
        have hz : r = 0 := by
          dsimp [r]
          rw [Int.toNat_of_nonpos hn']
        rw [hz] at hr
        omega
      have hleft' : 0 < (q.1 t).1 := by simpa only [t] using hleft
      have hcoord : 1 ≤ min (q.1 t).1 (-(q.1 t).2) := by omega
      have hthreshold : ((0 : ℕ) : ℤ) + 1 ≤ min (q.1 t).1 (-(q.1 t).2) := by omega
      obtain ⟨ht, hA, hB⟩ := selectedCut_good_record x T hT q j 0 (by
        simpa only [t] using hthreshold)
      obtain ⟨c, hcode⟩ := selectedCutRep_exists_walkClass x T hT q j 0
        (by simpa only [t] using hthreshold) R hR hcuts
      let hfin := sourceAncestor_finite_incidence x T hT q
      let hL := sourceAncestor_left_nonneg x T hT q
      let htrans := sourceAncestor_left_transient x T hT q
      let hRneg := sourceAncestor_right_unbounded x T hT q
      obtain ⟨hgL, hgS⟩ := selectedCutCoherentDomain_infinite_extremal x T hT q
      let P := sourceAncestorPath x T hT q
      let Q (x₀ : XDP) : InfinitePresentPath w ⟨0⟩ := match x₀ with
        | .ldp => kmswLeftmostLdpPath w hfin hL htrans hRneg 0 hgL
        | .sdp => kmswLeftmostSdpPath w hfin hL htrans hRneg 0 hgS
      have hpath : P = Q x := by cases x <;> rfl
      cases x with
      | ldp =>
          obtain ⟨hlen, i, hlenI, hvertex, hfirst, _⟩ :=
            selectedCutRep_recordStage_edgeIds_eq_ldpPrefix ht hA hB hfin hL
              htrans hRneg c hcode R I hboundary hgL
          have hPlen :
              (selectedGeodesicOfLen R.B .ldp hlen).darts.length = d := by
            calc
              _ = xdpLengthBase (kmswWalkClassRep ht c).B .ldp :=
                (selectedGeodesicOfLen R.B .ldp hlen).darts_length
              _ = xdpLengthBase R.B .ldp := hlen.symm
              _ = d := hR
          have hdi : d = i := hPlen.symm.trans hlenI
          have hvertexP : (P.initial i).1 = recordVertex w t := by
            rw [hpath]
            exact hvertex
          have hfirstP : ∀ n < i, (P.initial n).1 ≠ recordVertex w t := by
            intro n hn
            rw [hpath]
            exact hfirst n hn
          let Qldp := kmswLeftmostLdpPath w hfin hL htrans hRneg 0 hgL
          have hLongest : Qldp.HasLongestSegments :=
            kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hRneg 0 hgL
          have hdist : presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t) =
              (((i : ℕ) : ℕ∞) : WithBot ℕ∞) := by
            rw [← hvertex]
            calc
              presentLdp (⟨0⟩ : PresentVertex w) (Qldp.initial i).1 =
                  (((Qldp.initial i).2.length : ℕ∞) : WithBot ℕ∞) :=
                    presentLdp_eq_length (Qldp.initial_isLongest w hLongest i)
              _ = (((i : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [Qldp.prefix_length]
          exact ⟨ℓ, d, R, hR, I, i, hcuts, hdi.symm, hvertexP, hfirstP, hdist⟩
      | sdp =>
          obtain ⟨hlen, i, hlenI, hvertex, hfirst, _⟩ :=
            selectedCutRep_recordStage_edgeIds_eq_sdpPrefix ht hA hB hfin hL
              htrans hRneg c hcode R I hboundary hgS
          have hPlen :
              (selectedGeodesicOfLen R.B .sdp hlen).darts.length = d := by
            calc
              _ = xdpLengthBase (kmswWalkClassRep ht c).B .sdp :=
                (selectedGeodesicOfLen R.B .sdp hlen).darts_length
              _ = xdpLengthBase R.B .sdp := hlen.symm
              _ = d := hR
          have hdi : d = i := hPlen.symm.trans hlenI
          have hvertexP : (P.initial i).1 = recordVertex w t := by
            rw [hpath]
            exact hvertex
          have hfirstP : ∀ n < i, (P.initial n).1 ≠ recordVertex w t := by
            intro n hn
            rw [hpath]
            exact hfirst n hn
          let Qsdp := kmswLeftmostSdpPath w hfin hL htrans hRneg 0 hgS
          have hShortest : Qsdp.HasShortestSegments :=
            kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hRneg 0 hgS
          have hdist : sdp (⟨0⟩ : PresentVertex w) (recordVertex w t) =
              (i : ℕ∞) := by
            rw [← hvertex]
            calc
              sdp (⟨0⟩ : PresentVertex w) (Qsdp.initial i).1 =
                  ((Qsdp.initial i).2.length : ℕ∞) :=
                    ((isShortest_iff_length_eq_sdp _).1
                      (Qsdp.initial_isShortest w hShortest i)).symm
              _ = (i : ℕ∞) := by rw [Qsdp.prefix_length]
          exact ⟨ℓ, d, R, hR, I, i, hcuts, hdi.symm, hvertexP, hfirstP, hdist⟩


/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
Almost surely on a positive selected-time branch, the selected past length is the
first-visit index and the source XDP distance to the cut vertex. Source: -/
theorem selectedCutPastFirstVisitDistance_ae
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ p ∂μ,
      0 < selectedCutTime RT k p →
        ∃ hq : p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime,
          SelectedCutPastFirstVisitDistance x RT renewalTime_positiveSuccessTime k
            ⟨p, hq⟩ := by
  have hdomain : ∀ᵐ p ∂μ,
      p ∈ selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime :=
    ae_iff.mpr
      (selectedCutCoherentDomain_measurable_conull x RT renewalTime_positiveSuccessTime).2
  filter_upwards [lemma414PositiveCutLeftBoundaryPos_holds k, hdomain]
    with p hleft hq
  intro hpos
  refine ⟨hq, ?_⟩
  let q : selectedCutCoherentDomain x RT renewalTime_positiveSuccessTime := ⟨p, hq⟩
  have hleft' : 0 < (q.1 (selectedCutTime RT k q.1).toNat).1 := by
    simpa only [q] using hleft hpos
  exact selectedCutPastFirstVisitDistance_of_positive_left_boundary
    x RT renewalTime_positiveSuccessTime q k hk hleft'

end DirectedDistances.PaperProofs.Section4
