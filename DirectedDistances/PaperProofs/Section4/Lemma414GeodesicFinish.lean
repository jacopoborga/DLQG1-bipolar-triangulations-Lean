module

public import DirectedDistances.PaperProofs.Section4.Lemma414GeodesicIdentification

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "T" => (fun m p => Paper.Section4.renewalTime m p)
local notation "hT" => renewalTime_positiveSuccessTime

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
Every positive selected renewal time has positive left boundary coordinate -/
theorem lemma414PositiveCutLeftBoundaryPos_holds (k : ℕ) :
    Lemma414PositiveCutLeftBoundaryPos k := by
  have hnonneg : ∀ᵐ p ∂μ, ∀ n, 0 ≤ (p n).1 := by
    unfold conditionedVectorPathLaw
    apply ae_map_iff (by fun_prop) (by measurability) |>.2
    exact Filter.Eventually.of_forall fun p n => Int.natCast_nonneg _
  by_cases hk : 1 ≤ k
  · filter_upwards [conditionedVectorPathLaw_ae_legal, hnonneg,
      firstHitPastMap_finite_hit_ae k hk] with p hlegal hn hfinite
    intro hpos
    have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
    have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
      intro j
      obtain ⟨c, hc⟩ := hlegal.2 j
      have hs := congrArg Prod.snd hc
      fin_cases c <;>
        norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
    obtain ⟨m, hsel, _, _, _⟩ :=
      selectedCutTime_lastSuccessTime T p k hk hstep h0
        (fun j => hT p j) hfinite
    have hTzero : Paper.Section4.renewalTime 0 p = 0 :=
      (isPositiveSuccessTime_zero_iff _ _).mp (hT p 0)
    obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
    have htoNat : (conditionedSecondCoordinateFirstHit k p).toNat = K := by
      simpa using (congrArg ENat.toNat hK).symm
    have hbound : T (selectedCutRank T k p) p ≤
        conditionedSecondCoordinateFirstHit k p := by
      rw [selectedCutRank, htoNat]
      change Paper.Section4.renewalTime
        (Nat.findGreatest
          (fun j => Paper.Section4.renewalTime j p ≤
            conditionedSecondCoordinateFirstHit k p) K) p ≤
        conditionedSecondCoordinateFirstHit k p
      exact Nat.findGreatest_spec (m := 0) (n := K)
        (P := fun j => Paper.Section4.renewalTime j p ≤
          conditionedSecondCoordinateFirstHit k p)
        (Nat.zero_le _) (by rw [hTzero]; exact bot_le)
    have hselRank : selectedCutTime T k p = T (selectedCutRank T k p) p := by
      rw [selectedCutTime, dite_eq_left hfinite]
    have hselFinite : selectedCutTime T k p < ⊤ :=
      hselRank ▸ hbound.trans_lt hfinite
    have hcast : selectedCutTime T k p =
        ((selectedCutTime T k p).toNat : ℕ∞) :=
      (ENat.natCast_toNat hselFinite.ne).symm
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      have hsel0 : selectedCutTime T k p = Paper.Section4.renewalTime 0 p := by
        simpa [hm0] using hsel
      have htime0 : selectedCutTime T k p = 0 := hsel0.trans hTzero
      rw [htime0] at hpos
      exact (lt_irrefl 0 hpos)
    have hgraph : IsPositiveSuccessTime (literalSuccessGraph p) m
        ((selectedCutTime T k p).toNat : ℕ∞) := by
      rw [← hcast, hsel]
      exact hT p m
    have hrank :=
      (isPositiveSuccessTime_natCast_iff (literalSuccessGraph p) hmpos
        (selectedCutTime T k p).toNat).mp hgraph
    have hnpos : 0 < (selectedCutTime T k p).toNat := hrank.1
    have hindexPos : 1 ≤ (selectedCutTime T k p).toNat := by omega
    have hprev := hrank.2.1.1 ((selectedCutTime T k p).toNat - 1) (by omega)
    have hnsub : (selectedCutTime T k p).toNat - 1 + 1 =
        (selectedCutTime T k p).toNat := Nat.sub_add_cancel hindexPos
    have hlegalStep := hlegal.2 ((selectedCutTime T k p).toNat - 1)
    rw [hnsub] at hlegalStep
    obtain ⟨c, hc⟩ := hlegalStep
    have hv := congrArg Prod.snd hc
    have hu := congrArg Prod.fst hc
    have hleftNonneg := hn ((selectedCutTime T k p).toNat - 1)
    change 0 < (p (selectedCutTime T k p).toNat).1
    fin_cases c
    · simp [lazyTwoDimensionalStep, Prod.snd_sub] at hv
      omega
    · simp [lazyTwoDimensionalStep, Prod.snd_sub] at hv
      omega
    · simp [lazyTwoDimensionalStep, Prod.fst_sub] at hu
      omega
  · have hk0 : k = 0 := by omega
    subst k
    filter_upwards [conditionedVectorPathLaw_ae_legal] with p hlegal
    intro hpos
    have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
    have hhit : ∃ n, (p n).2 = -((0 : ℕ) : ℤ) := ⟨0, by rw [h0]; rfl⟩
    have hτ : conditionedSecondCoordinateFirstHit 0 p = 0 := by
      rw [conditionedSecondCoordinateFirstHit, dite_eq_left hhit]
      have hh0 : (p 0).2 = -((0 : ℕ) : ℤ) := by rw [h0]; rfl
      have hfind : Nat.find hhit = 0 := (Nat.find_eq_zero hhit).2 hh0
      rw [hfind]
      simp
    have hTzero : Paper.Section4.renewalTime 0 p = 0 :=
      (isPositiveSuccessTime_zero_iff _ _).mp (hT p 0)
    have hrank : selectedCutRank T 0 p = 0 := by
      unfold selectedCutRank
      rw [hτ]
      simp
    have htime : selectedCutTime T 0 p = 0 := by
      simp [selectedCutTime, hτ, hrank, hTzero]
    change 0 < selectedCutTime T 0 p at hpos
    rw [htime] at hpos
    exact False.elim (lt_irrefl 0 hpos)

end DirectedDistances.PaperProofs.Section4
