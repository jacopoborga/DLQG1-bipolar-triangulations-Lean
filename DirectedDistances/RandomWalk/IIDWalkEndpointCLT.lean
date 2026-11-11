module

public import DirectedDistances.RandomWalk.IIDVectorWalk
public import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Endpoint analytic helpers for the iid vector walk

Helpers for the tube argument in the proof of `lem-walk-bdy-sum`,
increment law are those of `lem-quadrant-walk`, -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

/-- Measurability of an individual source increment (`lem-quadrant-walk`, -/
theorem measurable_codeWalk_increment (i : ℕ) :
    Measurable (fun ω => codeWalk ω (i + 1) - codeWalk ω i) := by
  exact (measurable_pi_apply (i + 1) |>.comp measurable_codeWalk).sub
    (measurable_pi_apply i |>.comp measurable_codeWalk)

/-- Stationarity of the whole sequence of increments, including arbitrary -/
theorem map_codeWalk_shifted_increments (s : ℕ) :
    iidCodeMeasure.map (fun ω => fun i =>
      codeWalk ω (s + i + 1) - codeWalk ω (s + i)) =
    iidCodeMeasure.map (fun ω => fun i => codeWalk ω (i + 1) - codeWalk ω i) := by
  have hi : Function.Injective (fun i : ℕ => s + i) := fun _ _ h => Nat.add_left_cancel h
  have hs := iIndepFun_codeWalk_increments.precomp hi
  rw [hs.map_fun_eq_infinitePi_map (fun i => measurable_codeWalk_increment (s + i)),
    iIndepFun_codeWalk_increments.map_fun_eq_infinitePi_map measurable_codeWalk_increment]
  simp only [map_codeWalk_increment]

/-- The block displacement is the sum of its literal increments -/
theorem codeWalk_block_eq_sum (ω : ℕ → Fin 3) (s m : ℕ) :
    codeWalk ω (s + m) - codeWalk ω s =
      ∑ i ∈ Finset.range m, (codeWalk ω (s + i + 1) - codeWalk ω (s + i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h : s + (m + 1) = s + m + 1 := by omega
    rw [h]
    abel

/-- Exact stationarity of block endpoints, before rescaling -/
theorem identDistrib_codeWalk_block (s m : ℕ) :
    IdentDistrib (fun ω => codeWalk ω (s + m) - codeWalk ω s)
      (fun ω => codeWalk ω m) iidCodeMeasure iidCodeMeasure := by
  have h : IdentDistrib
      (fun ω => fun i => codeWalk ω (s + i + 1) - codeWalk ω (s + i))
      (fun ω => fun i => codeWalk ω (i + 1) - codeWalk ω i)
      iidCodeMeasure iidCodeMeasure :=
    ⟨(Measurable.of_eval (fun i => measurable_codeWalk_increment (s + i))).aemeasurable,
      (Measurable.of_eval measurable_codeWalk_increment).aemeasurable,
      map_codeWalk_shifted_increments s⟩
  have hsum := h.comp (u := fun p : ℕ → ℤ × ℤ => ∑ i ∈ Finset.range m, p i)
    (by fun_prop)
  have hz (ω : ℕ → Fin 3) :
      (∑ i ∈ Finset.range m, (codeWalk ω (i + 1) - codeWalk ω i)) = codeWalk ω m := by
    simpa only [zero_add, codeWalk_zero, show ((0, 0) : ℤ × ℤ) = 0 from rfl, sub_zero] using
      (codeWalk_block_eq_sum ω 0 m).symm
  simpa only [Function.comp_def, ← codeWalk_block_eq_sum, hz] using hsum

/-- Rescaled block endpoints have a law independent of the start time -/
theorem identDistrib_codeWalk_normalized_block (s m : ℕ) :
    IdentDistrib
      (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)))
      (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ)))
      iidCodeMeasure iidCodeMeasure := by
  exact (identDistrib_codeWalk_block s m).comp
    (u := fun z : ℤ × ℤ => (Real.sqrt (m : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)))
    (measurable_of_countable _)

/-- Integrals of functions of a source increment are the literal three-point -/
theorem integral_codeWalk_increment (i : ℕ) (f : ℤ × ℤ → ℝ) :
    (∫ ω, f (codeWalk ω (i + 1) - codeWalk ω i) ∂iidCodeMeasure) =
      (f (1, -1) + f (-1, 0) + f (0, 1)) / 3 := by
  rw [← integral_map (measurable_codeWalk_increment i).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable, map_codeWalk_increment]
  rw [Measure.uniformOfFinset, integral_finsetSum_measure]
  · norm_num [integral_smul_measure, integral_dirac, Finset.sum_insert,
      Finset.sum_singleton]
    ring
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure (by norm_num)

/-- Measurability of each scalar source-increment projection -/
theorem measurable_codeWalk_increment_projection (a b : ℝ) (i : ℕ) :
    Measurable (fun ω => a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
      b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ)) :=
  (measurable_of_countable (fun z : ℤ × ℤ => a * (z.1 : ℝ) + b * (z.2 : ℝ))).comp
    (measurable_codeWalk_increment i)

/-- Any real linear projection of a source increment is square integrable -/
theorem memLp_codeWalk_increment_projection (a b : ℝ) (i : ℕ) :
    MemLp (fun ω => a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
      b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ)) 2 iidCodeMeasure := by
  refine MemLp.of_bound (measurable_codeWalk_increment_projection a b i).aestronglyMeasurable (|a| + |b|) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [codeWalk_succ_sub]
  have h := abs_sub a b
  generalize ω (i + 1) = c
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]
  simpa only [sub_eq_add_neg] using h

/-- Every real projection of a source increment is centered -/
theorem integral_codeWalk_increment_projection (a b : ℝ) (i : ℕ) :
    (∫ ω, a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
      b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ) ∂iidCodeMeasure) = 0 := by
  rw [integral_codeWalk_increment i (fun z => a * (z.1 : ℝ) + b * (z.2 : ℝ))]
  norm_num

/-- The exact covariance quadratic form of the raw source step -/
theorem variance_codeWalk_increment_projection (a b : ℝ) (i : ℕ) :
    Var[fun ω => a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
      b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ); iidCodeMeasure] =
      (2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2) := by
  rw [variance_eq_integral (measurable_codeWalk_increment_projection a b i).aemeasurable, integral_codeWalk_increment_projection]
  simp only [sub_zero]
  rw [integral_codeWalk_increment i (fun z => (a * (z.1 : ℝ) + b * (z.2 : ℝ)) ^ 2)]
  norm_num
  ring

/-- Identical distribution of every scalar increment projection -/
theorem identDistrib_codeWalk_increment_projection (a b : ℝ) (i j : ℕ) :
    IdentDistrib
      (fun ω => a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
        b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ))
      (fun ω => a * ((codeWalk ω (j + 1) - codeWalk ω j).1 : ℝ) +
        b * ((codeWalk ω (j + 1) - codeWalk ω j).2 : ℝ))
      iidCodeMeasure iidCodeMeasure := by
  exact (show IdentDistrib
    (fun ω => codeWalk ω (i + 1) - codeWalk ω i)
    (fun ω => codeWalk ω (j + 1) - codeWalk ω j) iidCodeMeasure iidCodeMeasure from
      ⟨(measurable_codeWalk_increment i).aemeasurable,
       (measurable_codeWalk_increment j).aemeasurable,
       by rw [map_codeWalk_increment, map_codeWalk_increment]⟩).comp
    (u := fun z : ℤ × ℤ => a * (z.1 : ℝ) + b * (z.2 : ℝ))
    (measurable_of_countable _)

/-- Telescoping of real scalar increment projections -/
theorem sum_codeWalk_increment_projection (a b : ℝ) (n : ℕ) (ω : ℕ → Fin 3) :
    (∑ i ∈ Finset.range n,
      (a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
       b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ))) =
      a * ((codeWalk ω n).1 : ℝ) + b * ((codeWalk ω n).2 : ℝ) := by
  induction n with
  | zero => simp [codeWalk_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring

/-- The scalar central limit theorem for every projection of the source walk, -/
theorem codeWalk_projection_clt (a b : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ *
        (a * ((codeWalk ω n).1 : ℝ) + b * ((codeWalk ω n).2 : ℝ)))
      atTop id (fun _ : ℕ => iidCodeMeasure)
      (gaussianReal 0 (((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal)) := by
  have hi := iIndepFun_codeWalk_increments.comp
    (fun _ z => a * (z.1 : ℝ) + b * (z.2 : ℝ)) (fun _ => measurable_of_countable _)
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω => a * ((codeWalk ω (i + 1) - codeWalk ω i).1 : ℝ) +
      b * ((codeWalk ω (i + 1) - codeWalk ω i).2 : ℝ))
    (Y := id) (P' := gaussianReal 0
      (((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal))
    (by rw [variance_codeWalk_increment_projection]; exact HasLaw.id)
    (memLp_codeWalk_increment_projection a b 0) hi
    (fun i => identDistrib_codeWalk_increment_projection a b i 0)
  simpa only [integral_codeWalk_increment_projection, mul_zero, sub_zero,
    sum_codeWalk_increment_projection] using h

/-- Product Gaussian in the diagonal coordinates `(L, L + 2R)` -/
@[expose] noncomputable def iidEndpointLimitLaw : Measure (ℝ × ℝ) :=
  (gaussianReal 0 ((2 : ℝ≥0) / 3)).prod (gaussianReal 0 (2 : ℝ≥0))

instance : IsProbabilityMeasure iidEndpointLimitLaw := by
  unfold iidEndpointLimitLaw
  infer_instance

/-- Every nonempty open set has positive mass for a real Gaussian of positive -/
theorem gaussianReal_open_pos (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (U : Set ℝ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < gaussianReal μ v U := by
  by_contra h
  have hz : gaussianReal μ v U = 0 := le_antisymm (not_lt.mp h) zero_le
  have := gaussianReal_absolutelyContinuous' μ hv hz
  exact (hU.measure_pos volume hne).ne' this

/-- The diagonal Gaussian gives positive mass to every nonempty open set, -/
theorem iidEndpointLimitLaw_open_pos (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < iidEndpointLimitLaw U := by
  have : Measure.IsOpenPosMeasure (gaussianReal 0 ((2 : ℝ≥0) / 3)) :=
    ⟨fun V hV hn => (gaussianReal_open_pos _ _ (by norm_num) V hV hn).ne'⟩
  have : Measure.IsOpenPosMeasure (gaussianReal 0 (2 : ℝ≥0)) :=
    ⟨fun V hV hn => (gaussianReal_open_pos _ _ (by norm_num) V hV hn).ne'⟩
  unfold iidEndpointLimitLaw
  exact hU.measure_pos _ hne

/-- The raw-coordinate projection of the diagonal Gaussian has exactly the -/
theorem hasLaw_iidEndpointLimit_projection (a b : ℝ) :
    HasLaw (fun z : ℝ × ℝ => a * z.1 + b * ((z.2 - z.1) / 2))
      (gaussianReal 0 (((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal))
      iidEndpointLimitLaw := by
  have hf : HasLaw Prod.fst (gaussianReal 0 ((2 : ℝ≥0) / 3)) iidEndpointLimitLaw :=
    ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩
  have hs : HasLaw Prod.snd (gaussianReal 0 (2 : ℝ≥0)) iidEndpointLimitLaw :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have hi : IndepFun (fun z : ℝ × ℝ => (a - b / 2) * z.1)
      (fun z : ℝ × ℝ => (b / 2) * z.2) iidEndpointLimitLaw :=
    indepFun_prod (by fun_prop) (by fun_prop)
  have h := gaussianReal_add_gaussianReal_of_indepFun hi
    (gaussianReal_const_mul hf (a - b / 2)) (gaussianReal_const_mul hs (b / 2))
  have hvar :
      (NNReal.mk ((a - b / 2) ^ 2) (sq_nonneg _) * ((2 : ℝ≥0) / 3) +
       NNReal.mk ((b / 2) ^ 2) (sq_nonneg _) * (2 : ℝ≥0)) =
      ((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b])]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div,
      NNReal.coe_ofNat]
    ring
  refine ⟨by fun_prop, ?_⟩
  have he : (fun z : ℝ × ℝ => a * z.1 + b * ((z.2 - z.1) / 2)) =
      (fun z : ℝ × ℝ => (a - b / 2) * z.1) + (fun z : ℝ × ℝ => (b / 2) * z.2) := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [he, h, hvar]
  simp only [mul_zero, add_zero]

/-- The two-dimensional endpoint CLT, with the inverse diagonal change of
coordinates applied to the limit (`lem-walk-bdy-sum`, -/
theorem codeWalk_endpoint_clt :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ •
        (((codeWalk ω n).1 : ℝ), ((codeWalk ω n).2 : ℝ)))
      atTop (fun z : ℝ × ℝ => (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
  have hm (n : ℕ) : Measurable (fun ω => (Real.sqrt (n : ℝ))⁻¹ •
      (((codeWalk ω n).1 : ℝ), ((codeWalk ω n).2 : ℝ))) :=
    (measurable_of_countable (fun z : ℤ × ℤ =>
      (Real.sqrt (n : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)))).comp
      (measurable_pi_apply n |>.comp measurable_codeWalk)
  have hclt : TendstoInDistribution
      (fun (n : ℕ) ω => WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ •
        (((codeWalk ω n).1 : ℝ), ((codeWalk ω n).2 : ℝ))))
      atTop (fun z : ℝ × ℝ => WithLp.toLp 2 (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
    refine TendstoInDistribution.of_inner (by fun_prop) (fun n => ?_) ?_
    · exact ((WithLp.measurable_toLp 2 (ℝ × ℝ)).comp (hm n)).aemeasurable
    · intro t
      have h := codeWalk_projection_clt (WithLp.ofLp t).1 (WithLp.ofLp t).2
      have hY := hasLaw_iidEndpointLimit_projection (WithLp.ofLp t).1 (WithLp.ofLp t).2
      have hsource : (fun (n : ℕ) ω =>
          inner (𝕜 := ℝ)
            (WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ •
              (((codeWalk ω n).1 : ℝ), ((codeWalk ω n).2 : ℝ)))) t) =
          (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ *
            ((WithLp.ofLp t).1 * ((codeWalk ω n).1 : ℝ) +
             (WithLp.ofLp t).2 * ((codeWalk ω n).2 : ℝ))) := by
        funext n ω
        simp [WithLp.prod_inner_apply, mul_add, mul_left_comm]
      have hlimit : (fun z : ℝ × ℝ =>
          inner (𝕜 := ℝ) (WithLp.toLp 2 (z.1, (z.2 - z.1) / 2)) t) =
          (fun z : ℝ × ℝ =>
            (WithLp.ofLp t).1 * z.1 + (WithLp.ofLp t).2 * ((z.2 - z.1) / 2)) := by
        funext z
        simp [WithLp.prod_inner_apply]
      rw [hsource, hlimit]
      refine ⟨h.forall_aemeasurable, hY.aemeasurable, ?_⟩
      simpa only [hY.map_eq, Measure.map_id] using h.tendsto
  simpa only [Function.comp_def, WithLp.ofLp_toLp] using
    hclt.continuous_comp (WithLp.prod_continuous_ofLp 2 ℝ ℝ)

/-- Every nonempty open endpoint window has an eventually positive lower
bound, uniformly over all block starting times. This is the endpoint analytic -/
theorem iidCodeWalk_endpoint_open_lower_bound (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      c ≤ iidCodeMeasure.real {ω | (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ U} := by
  let Y : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, (z.2 - z.1) / 2)
  have hY : Measurable Y := by fun_prop
  let ν : Measure (ℝ × ℝ) := iidEndpointLimitLaw.map Y
  have hpos : 0 < ν U := by
    rw [show ν U = iidEndpointLimitLaw (Y ⁻¹' U) from Measure.map_apply hY hU.measurableSet]
    apply iidEndpointLimitLaw_open_pos _ (hU.preimage (by fun_prop))
    obtain ⟨⟨x, y⟩, hxy⟩ := hne
    refine ⟨(x, x + 2 * y), ?_⟩
    change (x, (x + 2 * y - x) / 2) ∈ U
    convert hxy using 1
    congr 1
    ring
  have hfinite : ν U ≠ ⊤ := measure_ne_top _ _
  let c : ℝ := (ν U).toReal / 2
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hpos.ne' hfinite)
  have hsmall : ENNReal.ofReal c < ν U := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfinite).mpr
    exact half_lt_self (ENNReal.toReal_pos hpos.ne' hfinite)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    codeWalk_endpoint_clt.tendsto hU
  have hevent : ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal c <
        (iidCodeMeasure.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ)))) U :=
    eventually_lt_of_lt_liminf (hsmall.trans_le hport)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hevent
  refine ⟨c, hc, m₀, fun m hm s => ?_⟩
  have h := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
    (hm₀ m hm).le
  have hmmeas : Measurable (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ))) :=
    (measurable_of_countable (fun z : ℤ × ℤ =>
      (Real.sqrt (m : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)))).comp
      (measurable_pi_apply m |>.comp measurable_codeWalk)
  rw [Measure.map_apply hmmeas hU.measurableSet] at h
  have hstat := (identDistrib_codeWalk_normalized_block s m).measure_mem_eq hU.measurableSet
  change iidCodeMeasure {ω | (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
       ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ U} =
    iidCodeMeasure {ω | (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ)) ∈ U} at hstat
  simpa only [measureReal_def, hstat, Set.preimage] using h

end DirectedDistances.RandomWalk
