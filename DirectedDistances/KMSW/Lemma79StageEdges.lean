module

public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLaw
public import DirectedDistances.KMSW.EdgesInMr
import DirectedDistances.KMSW.StoppedStageMap

/-! Helper toward lem-uiqbot-boltzmann / Lemma 7.9
τ̂_r − 1 has no missing edges, its edge count is the class edge count, and it
satisfies the uniform quadratic edge window (eq:edges-in-Mr). The identification
of the stopped class with the embedded source submap M̂(r) ⊂ M̂_{0,∞} is NOT
treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open MeasureTheory Filter

private theorem decoded_walk (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    codeWalk (pathCode p) = p := by
  funext n
  rw [codeWalk_pathCode p hp n, h0]
  exact sub_zero _

private theorem decoded_integrates (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    integrateCodes (boltzmannKMSWStream (pathCode p)) = p :=
  decoded_walk p h0 hp

private theorem ae_nonnegative :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ n, 0 ≤ (p n).1 := by
  unfold conditionedVectorPathLaw
  apply (ae_map_iff (by fun_prop) ?_).mpr
  · exact Eventually.of_forall fun p n => Int.natCast_nonneg (p n).1
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_le measurable_const (measurable_pi_apply n).fst

private theorem first_hit_data (r : ℕ) (p : ℕ → ℤ × ℤ)
    (hf : conditionedSecondCoordinateFirstHit r p < ⊤) :
    (p (conditionedSecondCoordinateFirstHit r p).toNat).2 = -(r : ℤ) ∧
      ∀ j < (conditionedSecondCoordinateFirstHit r p).toNat,
        (p j).2 ≠ -(r : ℤ) := by
  classical
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hh
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hh,
      lt_self_iff_false] at hf
  simp only [conditionedSecondCoordinateFirstHit, dite_eq_left hh, ENat.toNat_natCast]
  exact ⟨Nat.find_spec hh, fun j hj => Nat.find_min hh hj⟩

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
has no missing edges. The embedded source submap identification is NOT treated;
not the paper result. -/
theorem stoppedStage_edges_present_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      conditionedSecondCoordinateFirstHit r p < ⊤ ∧
      ∀ e < (kmswStage (boltzmannKMSWStream (pathCode p))
          ((conditionedSecondCoordinateFirstHit r p).toNat - 1)).nextEdge,
        (kmswStage (boltzmannKMSWStream (pathCode p))
          ((conditionedSecondCoordinateFirstHit r p).toNat - 1)).present e = true := by
  filter_upwards [conditionedVectorPathLaw_ae_legal, ae_nonnegative,
    firstHitPastMap_finite_hit_ae r hr] with p hp hL hf
  have hw := decoded_integrates p hp.1 hp.2
  refine ⟨hf, edges_present_of_first_hit _ _ r hr ?_ ?_⟩
  · intro j
    rw [kmsw_L_eq, hw]
    exact hL j
  · simpa only [kmsw_R_eq, hw] using first_hit_data r p hf

private theorem hit_of_downcrossing (q : ℕ → ℤ) (h0 : q 0 = 0)
    (hs : ∀ n, q n - 1 ≤ q (n + 1)) (r n : ℕ) (hn : q n ≤ -(r : ℤ)) :
    ∃ k ≤ n, q k = -(r : ℤ) := by
  induction n with
  | zero => exact ⟨0, le_rfl, by rw [h0] at hn ⊢; omega⟩
  | succ n ih =>
    by_cases h : q n ≤ -(r : ℤ)
    · obtain ⟨k, hk, he⟩ := ih h
      exact ⟨k, by omega, he⟩
    · exact ⟨n + 1, le_rfl, by have := hs n; omega⟩

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
(eq:edges-in-Mr) under P̂_(0,0). The embedded source submap identification is NOT
treated; not the paper result. -/
theorem stoppedStage_edges_window_tight (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ (conditionedVectorPathLaw 0 0).real {p | ∃ t : ℕ,
        (p t).2 = -(r : ℤ) ∧ (∀ j < t, (p j).2 ≠ -(r : ℤ)) ∧
        (r : ℝ) ^ 2 / A ≤
          ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ∧
        ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ≤
          A * (r : ℝ) ^ 2} := by
  classical
  obtain ⟨A0, hA0, hwindow⟩ := conditionedVectorPathLaw_hitting_window_tight ε hε
  have hApos : 0 < A0 := by linarith
  refine ⟨2 * A0, by linarith, ?_⟩
  intro r hr
  refine (hwindow r hr).trans ?_
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp hwindowp
  obtain ⟨⟨n, hn, hv⟩, hlow⟩ := hwindowp
  have hw := decoded_integrates p hp.1 hp.2
  let w := boltzmannKMSWStream (pathCode p)
  have hR : ∀ j, R w j = (p j).2 := by
    intro j
    rw [kmsw_R_eq, hw]
  have hzero : R w 0 = 0 := by simp only [R, Finset.range_zero, Finset.sum_empty]
  rw [← hR] at hv
  obtain ⟨k, hkn, hk⟩ := hit_of_downcrossing (R w) hzero
    (R_sub_one_le_succ w) r n hv
  have hex : ∃ k, R w k = -(r : ℤ) := ⟨k, hk⟩
  let t := Nat.find hex
  have ht : R w t = -(r : ℤ) := Nat.find_spec hex
  have hmin : ∀ j < t, R w j ≠ -(r : ℤ) := fun j hj => Nat.find_min hex hj
  have htk : t ≤ k := Nat.find_min' hex hk
  have htle : (t : ℝ) ≤ A0 * (r : ℝ) ^ 2 := by
    have htn : (t : ℝ) ≤ n := by exact_mod_cast htk.trans hkn
    linarith
  have htge : (r : ℝ) ^ 2 / A0 ≤ t := by
    by_contra h
    have hh := hlow t (not_le.mp h)
    rw [← hR, ht] at hh
    exact lt_irrefl _ hh
  have ht0 : t ≠ 0 := by
    rintro he
    rw [he, hzero] at ht
    omega
  obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  rw [hm] at ht hmin htle htge
  have hb := nextEdge_bounds w m
  have hb1 : ((m + 1 : ℕ) : ℝ) ≤ ((kmswStage w m).nextEdge : ℝ) := by
    exact_mod_cast hb.1
  have hb2 : ((kmswStage w m).nextEdge : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
    have hh : (kmswStage w m).nextEdge ≤ 2 * (m + 1) := by omega
    exact_mod_cast hh
  have hdiv : (r : ℝ) ^ 2 / (2 * A0) = ((r : ℝ) ^ 2 / A0) / 2 := by
    field_simp
  have hnn : 0 ≤ (r : ℝ) ^ 2 / A0 := by positivity
  refine ⟨m + 1, ?_, ?_, ?_, ?_⟩
  · rw [← hR]; exact ht
  · intro j hj; rw [← hR]; exact hmin j hj
  · change (r : ℝ) ^ 2 / (2 * A0) ≤
      ((kmswStage w (m + 1 - 1)).nextEdge : ℝ)
    rw [Nat.add_sub_cancel, hdiv]
    linarith
  · change ((kmswStage w (m + 1 - 1)).nextEdge : ℝ) ≤ _
    rw [Nat.add_sub_cancel]
    linarith

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
TOTAL edge index is the stopped stage edge count. The embedded source submap
identification is NOT treated; not the paper result. -/
theorem stoppedMarked_totalEdges_eq_stage_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (stoppedMarked r hr p).1.2.1 =
        (kmswStage (boltzmannKMSWStream (pathCode p))
          ((conditionedSecondCoordinateFirstHit r p).toNat - 1)).nextEdge := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_legal, ae_nonnegative,
    firstHitPastMap_finite_hit_ae r hr,
    stoppedMarked_clamp_inactive_ae r hr] with p hp hL hf hc
  have hw := decoded_walk p hp.1 hp.2
  have hd := first_hit_data r p hf
  have hh : ∃ n, (p n).2 = -(r : ℤ) :=
    ⟨(conditionedSecondCoordinateFirstHit r p).toNat, hd.1⟩
  have hE : pathCode p ∈ boltzmannEvent r := by
    refine ⟨(conditionedSecondCoordinateFirstHit r p).toNat, ?_, ?_⟩
    · rw [hw]
      exact hd.1
    · intro j _
      rw [hw]
      exact hL j
  have htau : boltzmannTau r (pathCode p) =
      (conditionedSecondCoordinateFirstHit r p).toNat := by
    simp only [boltzmannTau, hw, dite_eq_left hh,
      conditionedSecondCoordinateFirstHit, ENat.toNat_natCast]
  have hpos : 1 ≤ boltzmannTau r (pathCode p) :=
    (boltzmann_boundary_observable r hr (pathCode p) hE).1
  have he := congrArg
    (fun o : Option (AllBoltzmannSpace r) => o.map (fun q => q.2.1)) hc.2
  unfold stoppedMap stoppedIndex at he
  rw [dite_eq_left hE] at he
  dsimp only [Option.bind, stoppedWalkMapOption] at he
  rw [dite_eq_left hpos] at he
  change some (boltzmannTau r (pathCode p)) =
    some (stoppedMarked r hr p).1.2.1 at he
  have hcount := Option.some.inj he
  have hs := (stoppedStage_mem_sourceClass r hr (pathCode p) hE).2.2.2.2.2.2
  rw [kmswMap_numEdges, htau] at hs
  rw [htau] at hcount
  exact hcount.symm.trans hs.symm

end DirectedDistances.KMSW
