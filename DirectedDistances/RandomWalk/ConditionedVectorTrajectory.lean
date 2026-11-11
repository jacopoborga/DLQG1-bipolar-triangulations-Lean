module

public import DirectedDistances.RandomWalk.ConditionedVectorTransition
public import DirectedDistances.Probability.CountableMarkovTrajectory
public import DirectedDistances.RandomWalk.ConditionedVectorLawUniqueness
import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange
import DirectedDistances.RandomWalk.ConditionedVectorFactorization

/-! # The actual conditioned vector trajectory

Explicit Markov-chain construction and all-horizon RN characterization for -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The actual conditioned vector chain on the nonnegative carrier -/
@[expose] noncomputable def conditionedVectorTrajectory (x : ℕ) (y : ℤ) :
    Measure (ℕ → ℕ × ℤ) :=
  DirectedDistances.Probability.markovTrajectory conditionedVectorKernel (x, y)

instance (x : ℕ) (y : ℤ) : IsProbabilityMeasure (conditionedVectorTrajectory x y) := by
  unfold conditionedVectorTrajectory
  infer_instance

/-- Its path law in the source coordinates `ℤ × ℤ` -/
@[expose] noncomputable def conditionedVectorPathLaw (x : ℕ) (y : ℤ) :
    Measure (ℕ → ℤ × ℤ) :=
  (conditionedVectorTrajectory x y).map (fun r n => (((r n).1 : ℤ), (r n).2))

instance (x : ℕ) (y : ℤ) : IsProbabilityMeasure (conditionedVectorPathLaw x y) := by
  unfold conditionedVectorPathLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

private def castVectorPrefix {n : ℕ} (q : Fin (n + 1) → ℕ × ℤ) :
    Fin (n + 1) → ℤ × ℤ := fun j => (((q j).1 : ℤ), (q j).2)

private theorem castVectorPrefix_injective {n : ℕ} :
    Function.Injective (@castVectorPrefix n) := by
  intro p q h
  funext j
  have hj := congrFun h j
  change (((p j).1 : ℤ), (p j).2) = (((q j).1 : ℤ), (q j).2) at hj
  apply Prod.ext
  · have hfirst : ((p j).1 : ℤ) = ((q j).1 : ℤ) :=
      congrArg (fun z : ℤ × ℤ => z.1) hj
    exact_mod_cast hfirst
  · exact congrArg (fun z : ℤ × ℤ => z.2) hj

private theorem vectorPrefix_map_cast (x : ℕ) (y : ℤ) (n : ℕ) :
    (conditionedVectorPathLaw x y).map (fun q => fun j : Fin (n + 1) => q j.val) =
      ((conditionedVectorTrajectory x y).map
        (fun r => fun j : Fin (n + 1) => r j.val)).map castVectorPrefix := by
  rw [conditionedVectorPathLaw, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (measurable_of_countable _) (by fun_prop)]
  rfl

private theorem vectorPrefix_cast_atom (x : ℕ) (y : ℤ) (n : ℕ)
    (q : Fin (n + 1) → ℕ × ℤ) :
    ((conditionedVectorPathLaw x y).map (fun r => fun j : Fin (n + 1) => r j.val))
        {castVectorPrefix q} =
      if q 0 = (x, y) then
        ∏ i : Fin n, conditionedVectorStep (q i.castSucc) (q i.succ) else 0 := by
  classical
  rw [vectorPrefix_map_cast, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have he : castVectorPrefix ⁻¹' {castVectorPrefix q} = {q} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, castVectorPrefix_injective.eq_iff]
  rw [he]
  change ((DirectedDistances.Probability.markovTrajectory conditionedVectorKernel (x, y)).map
    (fun r => fun j : Fin (n + 1) => r j.val)) {q} = _
  rw [DirectedDistances.Probability.markovTrajectory_map_fin_prefix_singleton]
  simp only [conditionedVectorKernel_singleton]

private theorem vectorStep_legal_iff (s t : ℕ × ℤ) :
    (∃ c : Fin 3, (t.1 : ℤ) = (s.1 : ℤ) + (lazyTwoDimensionalStep c).1 ∧
      t.2 = s.2 + (lazyTwoDimensionalStep c).2) ↔
    ∃ c : Fin 3, ((t.1 : ℤ), t.2) = ((s.1 : ℤ), s.2) + lazyTwoDimensionalStep c := by
  constructor
  · rintro ⟨c, h₁, h₂⟩
    exact ⟨c, Prod.ext h₁ h₂⟩
  · rintro ⟨c, h⟩
    exact ⟨c, congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem vectorPrefix_product (x : ℕ) (y : ℤ) (n : ℕ)
    (q : Fin (n + 1) → ℕ × ℤ)
    (h : castVectorPrefix q ∈ Set.range (@lazyTwoDimensionalPrefix n (x : ℤ) y)) :
    (if q 0 = (x, y) then
      ∏ i : Fin n, conditionedVectorStep (q i.castSucc) (q i.succ) else 0) =
      ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) *
        ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  obtain ⟨h0, hs⟩ := (mem_range_lazyTwoDimensionalPrefix_iff (x : ℤ) y _).mp h
  have hstart : q 0 = (x, y) := by
    change (((q 0).1 : ℤ), (q 0).2) = ((x : ℤ), y) at h0
    apply Prod.ext
    · have hfirst : ((q 0).1 : ℤ) = (x : ℤ) :=
        congrArg (fun z : ℤ × ℤ => z.1) h0
      exact_mod_cast hfirst
    · exact congrArg (fun z : ℤ × ℤ => z.2) h0
  rw [ite_eq_left hstart]
  have hlegal (i : Fin n) := (vectorStep_legal_iff (q i.castSucc) (q i.succ)).mpr (hs i)
  have hweight (i : Fin n) : conditionedVectorStep (q i.castSucc) (q i.succ) =
      ENNReal.ofReal (conditionedLazyWeight (q i.castSucc).1 (q i.succ).1) := by
    change conditionedVectorStep ((q i.castSucc).1, (q i.castSucc).2) (q i.succ) = _
    rw [conditionedVectorStep_apply, ite_eq_left (hlegal i)]
  have hnear (i : Fin n) : |((q i.succ).1 : ℤ) - ((q i.castSucc).1 : ℤ)| ≤ 1 := by
    obtain ⟨c, hc, _⟩ := hlegal i
    simp only [lazyTwoDimensionalStep] at hc
    have := c.isLt
    rw [abs_le]
    omega
  simp_rw [hweight]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      conditioned_lazy_weight_nonneg (q i.castSucc).1 (q i.succ).1),
    prod_fin_conditionedLazyWeight (fun j => (q j).1) hnear]
  rw [show (q 0).1 = x from congrArg Prod.fst hstart,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos, ENNReal.inv_pow]

private theorem vectorPrefix_product_zero (x : ℕ) (y : ℤ) (n : ℕ)
    (q : Fin (n + 1) → ℕ × ℤ)
    (h : castVectorPrefix q ∉ Set.range (@lazyTwoDimensionalPrefix n (x : ℤ) y)) :
    (if q 0 = (x, y) then
      ∏ i : Fin n, conditionedVectorStep (q i.castSucc) (q i.succ) else 0) = 0 := by
  classical
  split_ifs with h0
  · have hbad : ¬ ∀ i : Fin n, ∃ c : Fin 3,
        castVectorPrefix q i.succ = castVectorPrefix q i.castSucc + lazyTwoDimensionalStep c := by
      intro hs
      apply h
      apply (mem_range_lazyTwoDimensionalPrefix_iff (x : ℤ) y _).mpr
      exact ⟨by simp only [castVectorPrefix, h0], hs⟩
    obtain ⟨i, hi⟩ := not_forall.mp hbad
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change conditionedVectorStep ((q i.castSucc).1, (q i.castSucc).2) (q i.succ) = _
    rw [conditionedVectorStep_apply]
    exact ite_eq_right (fun hc => hi ((vectorStep_legal_iff _ _).mp hc))
  · rfl

/-- Exact all-horizon source RN identity, including start and horizon zero -/
theorem conditionedVectorPathLaw_map_prefix (x : ℕ) (y : ℤ) (n : ℕ) :
    (conditionedVectorPathLaw x y).map (fun q => fun j : Fin (n + 1) => q j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0) := by
  classical
  apply Measure.ext_of_singleton
  intro q
  by_cases hnonneg : ∀ j, 0 ≤ (q j).1
  · let p : Fin (n + 1) → ℕ × ℤ := fun j => ((q j).1.toNat, (q j).2)
    have hp : castVectorPrefix p = q := by
      funext j
      exact Prod.ext (Int.toNat_of_nonneg (hnonneg j)) rfl
    rw [← hp, vectorPrefix_cast_atom]
    by_cases hr : castVectorPrefix p ∈ Set.range (@lazyTwoDimensionalPrefix n (x : ℤ) y)
    · rw [vectorPrefix_product x y n p hr]
      obtain ⟨w, hw⟩ := hr
      rw [← hw, conditionedTwoDimensionalPrefix_atom]
      have hn : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 := by
        rw [hw, hp]
        exact hnonneg
      rw [ite_eq_left hn, hw]
      simp only [castVectorPrefix, Int.cast_natCast]
    · rw [vectorPrefix_product_zero x y n p hr,
        withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
      have he : lazyTwoDimensionalPrefix (x : ℤ) y ⁻¹' {castVectorPrefix p} = ∅ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        exact fun hw => hr ⟨w, hw⟩
      rw [he, measure_empty, mul_zero]
  · rw [vectorPrefix_map_cast, Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton _)]
    have he : castVectorPrefix ⁻¹' {q} = ∅ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hp
      apply hnonneg
      intro j
      rw [← hp]
      exact Int.natCast_nonneg _
    rw [he, measure_empty, withDensity_apply _ (measurableSet_singleton _),
      lintegral_singleton, ite_eq_right hnonneg, zero_mul]

/-- Existence and uniqueness of the source-characterized law -/
theorem existsUnique_conditionedVectorLaw (x : ℕ) (y : ℤ) :
    ∃! μ : Measure (ℕ → ℤ × ℤ), IsProbabilityMeasure μ ∧
      ∀ n : ℕ, μ.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0) := by
  refine ⟨conditionedVectorPathLaw x y,
    ⟨inferInstance, conditionedVectorPathLaw_map_prefix x y⟩, ?_⟩
  intro μ hμ
  have : IsProbabilityMeasure μ := hμ.1
  exact conditioned_vector_law_unique x y μ (conditionedVectorPathLaw x y)
    hμ.2 (conditionedVectorPathLaw_map_prefix x y)

end DirectedDistances.RandomWalk
