module

public import DirectedDistances.PaperProofs.Section4.SelectedCutPastMapLaw
import DirectedDistances.RandomWalk.BlockBoundUnconditional
import DirectedDistances.RandomWalk.ConditionedTransience
import Mathlib.MeasureTheory.Measure.Continuity

/-! good event eqn-min-coord, 376–377): P[E_k(s)] → 1 by divergence (the source's
The selector is supplied by its literal graph. No source renewal times are defined here,
and no assertion about the source's zero-cut interpretation is made. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Classical ENNReal Topology

private theorem hit_value (p : ℕ → ℤ × ℤ) (k t : ℕ)
    (ht : conditionedSecondCoordinateFirstHit k p = (t : ℕ∞)) :
    (p t).2 = -(k : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit at ht
  split at ht
  next h =>
    have heq : Nat.find h = t := by exact_mod_cast ht
    rw [← heq]
    exact Nat.find_spec h
  next h => exact (ENat.top_ne_natCast t ht).elim

private theorem hit_time_lower_bound (p : ℕ → ℤ × ℤ)
    (h0 : (p 0).2 = 0)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (k t : ℕ) (ht : conditionedSecondCoordinateFirstHit k p = (t : ℕ∞)) :
    k ≤ t := by
  have hlower : ∀ n : ℕ, -(n : ℤ) ≤ (p n).2 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      have hs := hstep n
      push_cast
      omega
  have hv := hit_value p k t ht
  have hb := hlower t
  omega

private theorem success_has_rank
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (n : ℕ) (hn : 0 < n) (hs : literalSuccessGraph p n) :
    ∃ m, 0 < m ∧ T m p = (n : ℕ∞) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let m := positiveSuccessCount (literalSuccessGraph p) (j + 1)
  have hm : 0 < m := by
    dsimp [m]
    rw [positiveSuccessCount_succ, ite_eq_left hs]
    omega
  have hg : IsPositiveSuccessTime (literalSuccessGraph p) m ((j + 1 : ℕ) : ℕ∞) :=
    (isPositiveSuccessTime_natCast_iff _ hm _).mpr ⟨by omega, hs, rfl⟩
  obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) m
  exact ⟨m, hm, (hu _ (hT m)).trans (hu _ hg).symm⟩

private theorem selected_after_success
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k n : ℕ) (hn : 0 < n) (hs : literalSuccessGraph p n)
    (hτ : conditionedSecondCoordinateFirstHit k p < ⊤)
    (hnτ : (n : ℕ∞) ≤ conditionedSecondCoordinateFirstHit k p) :
    n ≤ (selectedCutTime T k p).toNat ∧
      literalSuccessGraph p (selectedCutTime T k p).toNat := by
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hτ.ne
  have hτK : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞) := hK.symm
  have hzero : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
  have hKnat : (conditionedSecondCoordinateFirstHit k p).toNat = K := by
    rw [hτK]
    rfl
  obtain ⟨m, hm, hmn⟩ := success_has_rank T p hT n hn hs
  have hnK : n ≤ K := ENat.natCast_le_natCast.mp (hnτ.trans_eq hτK)
  have hmK : m ≤ K := positiveSuccessTime_le_index T p hT m K (by
    rw [hmn]
    exact ENat.natCast_le_natCast.mpr hnK)
  have hmrank : m ≤ selectedCutRank T k p := by
    rw [selectedCutRank, hKnat]
    apply Nat.le_findGreatest hmK
    exact hmn ▸ hnτ
  have hrank : T (selectedCutRank T k p) p ≤ (K : ℕ∞) := by
    rw [selectedCutRank, hKnat]
    rw [← hτK]
    apply Nat.findGreatest_spec (m := 0) (n := K)
      (P := fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
    · exact Nat.zero_le K
    · rw [hzero]
      exact bot_le
  have hfinite : T (selectedCutRank T k p) p ≠ ⊤ :=
    ne_of_lt (hrank.trans_lt (ENat.natCast_lt_top K))
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hsel : selectedCutTime T k p = (t : ℕ∞) := by
    rw [selectedCutTime, dite_eq_left hτ]
    exact ht.symm
  have hgraph : PositiveSuccessRank (literalSuccessGraph p)
      (selectedCutRank T k p) t := by
    apply (isPositiveSuccessTime_natCast_iff _ (by omega) t).mp
    rw [ht]
    exact hT _
  have hnt : n ≤ t := by
    have horder : T m p ≤ T (selectedCutRank T k p) p := by
      by_cases heq : m = selectedCutRank T k p
      · rw [heq]
      · exact (positiveSuccessTime_strictMono_of_finite T p hT (by omega)
          (by rw [hmn]; exact ENat.natCast_ne_top n) hfinite).le
    rw [hmn, ← ht] at horder
    exact ENat.natCast_le_natCast.mp horder
  simpa only [hsel, ENat.toNat_natCast] using And.intro hnt hgraph.2.1

/-- good event eqn-min-coord, 376–377): P[E_k(s)] → 1 by divergence (the source's
Only the literal success-enumeration graph is required of the supplied selector. -/
theorem selectedCutTime_ae_min_tendsto_atTop
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0),
      Tendsto (fun k => min ((p (selectedCutTime T k p).toNat).1)
        (-(p (selectedCutTime T k p).toNat).2)) atTop atTop := by
  have hfinite : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ k,
      conditionedSecondCoordinateFirstHit (k + 1) p < ⊤ :=
    ae_all_iff.mpr fun k => firstHitPastMap_finite_hit_ae (k + 1) (by omega)
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    conditionedVectorPathLaw_tendsto_fst_atTop 0 0,
    conditionedVectorPathLaw_ae_infinite_success, hfinite] with p hlegal hL hS hfinite
  have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
  have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
    intro j
    obtain ⟨c, hc⟩ := hlegal.2 j
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hL b
  let r := b.toNat + 1
  have hr : conditionedSecondCoordinateFirstHit r p < ⊤ := hfinite b.toNat
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hr.ne
  have htau : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := ht.symm
  have hRt := hit_value p r t htau
  obtain ⟨j, hj, hjbig⟩ := hS.exists_gt (max N t)
  have hsucc : literalSuccessGraph p (j + 1) := hj
  refine ⟨j + 1, fun k hk => ?_⟩
  have hkpos : 0 < k := by omega
  have hkfin : conditionedSecondCoordinateFirstHit k p < ⊤ := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    exact hfinite q
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hkfin.ne
  have hτK : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞) := hK.symm
  have hkK := hit_time_lower_bound p h0 hstep k K hτK
  have hnτ : ((j + 1 : ℕ) : ℕ∞) ≤ conditionedSecondCoordinateFirstHit k p := by
    rw [hτK]
    exact ENat.natCast_le_natCast.mpr (by omega)
  obtain ⟨hafter, hsuccess⟩ := selected_after_success T p (hT p) k (j + 1)
    (by omega) hsucc hkfin hnτ
  have hleft : b ≤ (p (selectedCutTime T k p).toNat).1 := hN _ (by omega)
  have hright := hsuccess.1 t (by omega)
  have hb : b ≤ (b.toNat : ℤ) := Int.self_le_toNat b
  apply le_min hleft
  dsimp [r] at hRt
  omega

/-- good event eqn-min-coord, 376–377): P[E_k(s)] → 1 by divergence (the source's
The good event is measurable without a measurability assumption on the selector. -/
theorem measurableSet_selectedCutTime_good_event
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s k : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ | (s : ℤ) + 1 ≤
      min ((p (selectedCutTime T k p).toNat).1)
        (-(p (selectedCutTime T k p).toNat).2)} := by
  have heval : Measurable (fun p : ℕ → ℤ × ℤ =>
      p (selectedCutTime T k p).toNat) := by
    simpa only [Function.comp_def, selectedCutFuture, conditionedVectorShift, Nat.add_zero] using
      (measurable_pi_apply 0).comp (measurable_selectedCutFuture T k hT)
  exact measurableSet_le measurable_const (heval.fst.min heval.snd.neg)

/-- good event eqn-min-coord, 376–377): P[E_k(s)] → 1 by divergence (the source's -/
theorem selectedCutTime_good_event_probability_tendsto_one
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s : ℕ) :
    Tendsto (fun k => conditionedVectorPathLaw 0 0
      {p | (s : ℤ) + 1 ≤ min ((p (selectedCutTime T k p).toNat).1)
        (-(p (selectedCutTime T k p).toNat).2)}) atTop (𝓝 1) := by
  let E : ℕ → Set (ℕ → ℤ × ℤ) := fun k =>
    {p | (s : ℤ) + 1 ≤ min ((p (selectedCutTime T k p).toNat).1)
      (-(p (selectedCutTime T k p).toNat).2)}
  let B : ℕ → Set (ℕ → ℤ × ℤ) := fun N => {p | ∀ k, N ≤ k → p ∈ E k}
  have hBmono : Monotone B := by
    intro i j hij p hp k hjk
    exact hp k (hij.trans hjk)
  have hunion : (⋃ N, B N) =ᵐ[conditionedVectorPathLaw 0 0] Set.univ := by
    filter_upwards [selectedCutTime_ae_min_tendsto_atTop T hT] with p hp
    apply propext
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
    exact tendsto_atTop_atTop.mp hp ((s : ℤ) + 1)
  have hlim : Tendsto (fun k => conditionedVectorPathLaw 0 0 (B k))
      atTop (𝓝 1) := by
    have ht := tendsto_measure_iUnion_atTop (μ := conditionedVectorPathLaw 0 0) hBmono
    rw [measure_congr hunion, measure_univ] at ht
    exact ht
  change Tendsto (fun k => conditionedVectorPathLaw 0 0 (E k)) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
  · intro k
    exact measure_mono (fun p hp => hp k le_rfl)
  · intro k
    exact prob_le_one

end DirectedDistances.PaperProofs.Section4
