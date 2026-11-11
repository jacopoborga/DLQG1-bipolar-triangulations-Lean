module

public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitKernel
import DirectedDistances.KMSW.PathSpaceTransfer





public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open MeasureTheory ProbabilityTheory

private theorem exists_secondCoordinate_hit (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hstep : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hR : ∀ a : ℤ, ∃ n, (p n).2 ≤ a) :
    ∃ n, (p n).2 = -(r : ℤ) := by
  have hdown (n : ℕ) : (p n).2 - 1 ≤ (p (n + 1)).2 := by
    obtain ⟨c, hc⟩ := hstep n
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  have hhit (n : ℕ) : (p n).2 ≤ -(r : ℤ) → ∃ j, (p j).2 = -(r : ℤ) := by
    induction n with
    | zero =>
      intro hn
      have hz : (p 0).2 = 0 := congrArg Prod.snd h0
      omega
    | succ n ih =>
      intro hn
      by_cases hb : (p n).2 ≤ -(r : ℤ)
      · exact ih hb
      · refine ⟨n + 1, ?_⟩
        have hd := hdown n
        change (p (n + 1)).2 ≤ -(r : ℤ) at hn
        omega
  obtain ⟨n, hn⟩ := hR (-(r : ℤ))
  exact hhit n hn

/-- finiteness of the first hit τ_r (defined at :253–257) under the conditioned UIQBOT
law. The renewal-time selection T_{m_k} and the T_0 branch are not treated;
not the paper result. -/
theorem firstHitPastMap_finite_hit_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      conditionedSecondCoordinateFirstHit r p < ⊤ := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    conditionedVectorPathLaw_ae_legal] with p hp hlegal
  obtain ⟨w, hwp, _, _, hR, _⟩ := hp
  have hRp : ∀ a : ℤ, ∃ n, (p n).2 ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hR a
    refine ⟨n, ?_⟩
    rwa [kmsw_R_eq, hwp] at hn
  have hh := exists_secondCoordinate_hit r hr p hlegal.1 hlegal.2 hRp
  simp only [conditionedSecondCoordinateFirstHit, dite_eq_left hh]
  exact ENat.natCast_lt_top _

/-- finiteness of the first hit τ_r under the conditioned UIQBOT law, in mass-one form.
The renewal-time selection T_{m_k} and the T_0 branch are not treated;
not the paper result. -/
theorem firstHitPastMap_finite_hit_prob_one (r : ℕ) (hr : 1 ≤ r) :
    conditionedVectorPathLaw 0 0
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} = 1 := by
  calc
    _ = conditionedVectorPathLaw 0 0 Set.univ :=
      measure_congr (Filter.eventuallyEqSet_univ.mpr (firstHitPastMap_finite_hit_ae r hr))
    _ = 1 := measure_univ

/-- on finite τ_r leaves the conditioned UIQBOT law unchanged. The renewal-time selection
T_{m_k} and the T_0 branch are not treated; not the paper result. -/
theorem firstHitPastMap_cond_finite_hit_eq (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    μ[|{p | τ p < ⊤}] = μ := by
  dsimp only
  rw [ProbabilityTheory.cond, firstHitPastMap_finite_hit_prob_one r hr,
    inv_one, one_smul]
  exact Measure.restrict_eq_self_of_ae_mem (firstHitPastMap_finite_hit_ae r hr)

/-- kernel form at τ_r for the joint law of the future and past map. The renewal-time
selection T_{m_k} and the T_0 branch are not treated; not the paper result. -/
theorem firstHitPastMap_joint_kernel_law_unconditioned (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    μ.map (fun p => (Y p, stoppedMap r hr (pathCode p))) =
      μ.map Y ⊗ₘ firstHitPastMapKernel r hr := by
  have h := firstHitPastMap_joint_kernel_law r hr
  dsimp only at h ⊢
  rwa [firstHitPastMap_cond_finite_hit_eq r hr] at h

/-- kernel form at τ_r for the conditional law of the past map given the future.
The renewal-time selection T_{m_k} and the T_0 branch are not treated;
not the paper result. -/
theorem firstHitPastMap_condDistrib_kernel_unconditioned (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    condDistrib (fun p => stoppedMap r hr (pathCode p)) Y μ
      =ᵐ[μ.map Y] firstHitPastMapKernel r hr := by
  apply condDistrib_ae_eq_of_measure_eq_compProd
    (measurable_conditionedFirstHit_future r).aemeasurable
    (((measurable_stoppedMap r hr).comp measurable_pathCode).aemeasurable)
  exact firstHitPastMap_joint_kernel_law_unconditioned r hr

end DirectedDistances.PaperProofs.Section4
