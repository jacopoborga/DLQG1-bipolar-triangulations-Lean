module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfIdentification
public import DirectedDistances.PaperProofs.Section4.Lemma414SideCarrier

/-! Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.

At a selected cut with positive left boundary coordinate, the existing cut
representative and geodesic-prefix theorem identify the finite path with the
canonical infinite leftmost XDP path. The implication from positive selected
time alone to a positive left boundary coordinate remains isolated below. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The missing left-boundary positivity needed to invoke the existing finite
representative bridge on every positive selected-time branch. This proposition -/
@[expose] def Lemma414PositiveCutLeftBoundaryPos (k : ℕ) : Prop :=
  ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
    0 < selectedCutTime renewalTime k p →
      0 < (p (selectedCutTime renewalTime k p).toNat).1

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
On a selected cut with positive left boundary coordinate, the two selected
past outputs are cut representatives, and the selected XDP geodesic in their
common past representative has the edge-ID sequence of the canonical infinite
XDP path from the source through the cut. The source theorem supplies the -/
theorem selectedCutPastCuts_geodesic_prefix_of_positive_left_boundary
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k : ℕ) (hk : 1 ≤ k)
    (hleft : 0 < (q.1 (selectedCutTime T k q.1).toNat).1) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T k q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t)
      (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map
        (kmswStageDirectedMap w (t - 1))),
      selectedCutPastSides x T hT k q.1 =
        (Sum.inr (selectedCutPastCuts x T k q.1).1,
          Sum.inr (selectedCutPastCuts x T k q.1).2) ∧
      selectedCutPastCuts x T k q.1 =
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
            (sourceAncestorPath x T hT q).edge j.val) := by
  cases k with
  | zero => omega
  | succ j =>
      have hspec := selectedCutCoherentDomain_spec x T hT q
      have hlegal := hspec.2.1
      have hstart : q.1 0 = (0, 0) := hlegal.1
      have hfirst : (q.1 0).1 = 0 := congrArg Prod.fst hstart
      have hfirstR : (q.1 0).2 = 0 := congrArg Prod.snd hstart
      have htime : 0 < selectedCutTime T (j + 1) q.1 := by
        by_contra hnot
        have hzero : selectedCutTime T (j + 1) q.1 = 0 :=
          le_antisymm (not_lt.mp hnot) bot_le
        have hnat : (selectedCutTime T (j + 1) q.1).toNat = 0 := by
          simp [hzero]
        rw [hnat, hfirst] at hleft
        omega
      have hfinite : conditionedSecondCoordinateFirstHit (j + 1) q.1 < ⊤ :=
        hspec.2.2.1 (j + 1)
      have hbound : T (selectedCutRank T (j + 1) q.1) q.1 ≤
          conditionedSecondCoordinateFirstHit (j + 1) q.1 := by
        have hzero : T 0 q.1 = 0 :=
          (isPositiveSuccessTime_zero_iff _ _).mp (hT q.1 0)
        unfold selectedCutRank
        exact Nat.findGreatest_spec (m := 0)
          (n := (conditionedSecondCoordinateFirstHit (j + 1) q.1).toNat)
          (P := fun m => T m q.1 ≤ conditionedSecondCoordinateFirstHit (j + 1) q.1)
          (Nat.zero_le _) (by rw [hzero]; exact bot_le)
      have hcutFinite : selectedCutTime T (j + 1) q.1 < ⊤ := by
        rw [selectedCutTime, dite_eq_left hfinite]
        exact hbound.trans_lt hfinite
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hcutFinite.ne
      have hcast : T (selectedCutRank T (j + 1) q.1) q.1 = (n : ℕ∞) := by
        calc
          T (selectedCutRank T (j + 1) q.1) q.1 =
              selectedCutTime T (j + 1) q.1 := by
                rw [selectedCutTime, dite_eq_left hfinite]
          _ = (n : ℕ∞) := hn.symm
      have hrankNe : selectedCutRank T (j + 1) q.1 ≠ 0 := by
        intro hz
        have hzero : T 0 q.1 = 0 :=
          (isPositiveSuccessTime_zero_iff _ _).mp (hT q.1 0)
        rw [hz, hzero] at hcast
        have : n = 0 := by exact_mod_cast hcast.symm
        subst n
        have hnat : (selectedCutTime T (j + 1) q.1).toNat = 0 := by
          have h := congrArg ENat.toNat hn
          simpa using h.symm
        rw [hnat, hfirst] at hleft
        omega
      have hsuccess := (isPositiveSuccessTime_natCast_iff
        (literalSuccessGraph q.1) (Nat.pos_of_ne_zero hrankNe) n).mp (by
          rw [← hcast]
          exact hT q.1 (selectedCutRank T (j + 1) q.1))
      have hright : 1 ≤ -(q.1 n).2 := by
        have hnpos := hsuccess.1
        have hvert := hsuccess.2.1.1 0 hnpos
        rw [hfirstR] at hvert
        omega
      have hcoord : (0 : ℤ) + 1 ≤
          min ((q.1 (selectedCutTime T (j + 1) q.1).toNat).1)
            (-(q.1 (selectedCutTime T (j + 1) q.1).toNat).2) := by
        have hnat : (selectedCutTime T (j + 1) q.1).toNat = n := by
          have h := congrArg ENat.toNat hn.symm
          simpa using h
        rw [hnat]
        have hleft' : 0 < (q.1 n).1 := by simpa [hnat] using hleft
        have hmin : 0 < min
            ((q.1 n).1) (-(q.1 n).2) := lt_min hleft' hright
        omega
      obtain ⟨ℓ, d, R, hR, I, _, _, hb, _, hc⟩ :=
        selectedCutPastCuts_representatives_record_stageIso
          x T hT q j 0 hcoord
      refine ⟨ℓ, d, R, hR, I, ?_, hc, hb, ?_⟩
      · exact selectedCutPastSides_pos x T hT (j + 1) q.1 htime
      exact sourceAncestorPosHalf_path_prefix x T hT q 0 j hcoord R hR I hb hc

end DirectedDistances.PaperProofs.Section4
