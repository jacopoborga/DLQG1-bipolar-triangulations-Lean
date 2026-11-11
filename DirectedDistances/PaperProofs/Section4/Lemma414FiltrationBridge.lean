module

public import DirectedDistances.PaperProofs.Section4.FiltrationMonoAnchor

/-! Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
This identifies the selected-cut conditioning observation with the existing
Lemma 4.15 filtration on the coherent domain, including a zero selected time. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver
open scoped Classical ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "T" => (fun m p => Paper.Section4.renewalTime m p)
local notation "hT" =>
  (fun p m => And.left (Paper.Section4.renewalTime_characterization m p))

private theorem bridge_activeVertex_eq_record (w : ℕ → Fin 3) (n : ℕ) :
    (⟨activeInitial w n⟩ : PresentVertex w) = recordVertex w n := by
  exact congrArg (fun a => (⟨a⟩ : PresentVertex w)) (CutConverse.activeInitial_eq w n)

private theorem selectedCutObservation_eq_on_coherentDomain (x : XDP) (k : ℕ)
    (q : selectedCutCoherentDomain x T hT) :
    sourceCutObservation x k q.1 = selectedCutCodeDistanceConditioning x T k q.1 := by
  classical
  obtain ⟨_, hl, hf, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let p := q.1
  let t := (selectedCutTime T k p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  have hzero : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT p 0)
  have hrank : T (selectedCutRank T k p) p ≤ conditionedSecondCoordinateFirstHit k p := by
    unfold selectedCutRank
    exact Nat.findGreatest_spec (m := 0)
      (P := fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
      (Nat.zero_le _) (by rw [hzero]; exact bot_le)
  have hsel : selectedCutTime T k p = T (selectedCutRank T k p) p := by
    rw [selectedCutTime, dite_eq_left (hf k)]
  have hfin : selectedCutTime T k p < ⊤ := hsel ▸ hrank.trans_lt (hf k)
  have hcast : selectedCutTime T k p = (t : ℕ∞) :=
    (ENat.natCast_toNat hfin.ne).symm
  have hs (ht : t ≠ 0) : literalSuccessGraph p t := by
    have hm : 0 < selectedCutRank T k p := by
      by_contra h
      have hm0 : selectedCutRank T k p = 0 := by omega
      have ht0 : selectedCutTime T k p = 0 := by rw [hsel, hm0, hzero]
      exact ht (by simp [t, ht0])
    have hg : IsPositiveSuccessTime (literalSuccessGraph p)
        (selectedCutRank T k p) (t : ℕ∞) := by
      rw [← hcast, hsel]
      exact hT p (selectedCutRank T k p)
    exact ((isPositiveSuccessTime_natCast_iff _ hm _).mp hg).2.1
  apply Prod.ext
  · rfl
  · change (sourceCutObservation x k p).2 = _
    dsimp only [sourceCutObservation]
    rw [bridge_activeVertex_eq_record, bridge_activeVertex_eq_record]
    change (match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (recordVertex w 0) (recordVertex w t))
      | .sdp => (sdp (recordVertex w 0) (recordVertex w t)).toNat) = _
    by_cases ht : t = 0
    · have hp0 : p t = (0, 0) := ht ▸ hl.1
      have hr0 : (-(selectedCutFuture T k p 0).2).toNat = 0 := by
        change (-(p (t + 0)).2).toNat = 0
        simp only [Nat.add_zero, hp0, neg_zero, Int.toNat_zero]
      rw [selectedCutCodeDistanceConditioning, hr0, dite_eq_right (by omega)]
      simp only [ht]
      have hp : IsLongest (Path.nil : Path (recordVertex w 0) (recordVertex w 0)) :=
        fun r => Nat.le_of_eq (presentVertex_acyclic w _ r)
      cases x with
      | ldp => rw [presentLdp_eq_length hp]; rfl
      | sdp => rw [sdp_self]; rfl
    · have hrec := (hs ht).1
      have hn := hrec 0 (Nat.pos_of_ne_zero ht)
      have hp0 : p 0 = (0, 0) := hl.1
      rw [hp0] at hn
      change (p t).2 ≤ 0 - 1 at hn
      let r := (-(p t).2).toNat
      have hr : 1 ≤ r := by dsimp [r]; omega
      have hlevel : (p t).2 = -(r : ℤ) := by dsimp [r]; omega
      have hex : ∃ n, (p n).2 = -(r : ℤ) := ⟨t, hlevel⟩
      have hhit : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := by
        rw [conditionedSecondCoordinateFirstHit, dite_eq_left hex,
          Nat.cast_inj, Nat.find_eq_iff]
        refine ⟨hlevel, fun i hi he => ?_⟩
        have hh := hrec i hi
        omega
      have hlevel' : (-(selectedCutFuture T k p 0).2).toNat = r := by
        change (-(p (t + 0)).2).toNat = r
        rw [Nat.add_zero]
      rw [selectedCutCodeDistanceConditioning, hlevel', dite_eq_left hr]
      dsimp only [firstHitCodeDistanceConditioning, firstHitCodeXdpDistance]
      rw [hhit]
      simp only [ENat.toNat_natCast, recordVertex_zero_eq_source]
      cases x <;> rfl

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
is `selectedCutCodeDistanceConditioning`; its generated sigma-algebra agrees exactly
with the existing `sourceCutFiltration` after restriction to the coherent domain.
The pointwise identification includes both zero and positive selected times. -/
theorem selectedCutCodeDistance_comap_sourceCutFiltration (x : XDP) (j : ℕ) :
    MeasurableSpace.comap
      (fun q : selectedCutCoherentDomain x T hT =>
        selectedCutCodeDistanceConditioning x T (j + 1) q.1) inferInstance =
      MeasurableSpace.comap (Subtype.val :
        selectedCutCoherentDomain x T hT → Ω) (sourceCutFiltration x (j + 1)) := by
  have hsource : MeasurableSpace.comap (Subtype.val :
      selectedCutCoherentDomain x T hT → Ω) (sourceCutFiltration x (j + 1)) =
      selectedCutConditioningSigma x T hT j := by
    rw [sourceCutFiltration, MeasurableSpace.comap_comp,
      (selectedCutConditioningSigma_eq x T hT j).1]
    exact congrArg (fun f => MeasurableSpace.comap f inferInstance)
      (funext fun q => selectedCutObservation_eq_on_coherentDomain x (j + 1) q)
  exact (selectedCutConditioningSigma_eq x T hT j).1.symm |>.trans hsource.symm

end DirectedDistances.PaperProofs.Section4
