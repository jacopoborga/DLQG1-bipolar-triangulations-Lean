module

public import DirectedDistances.RandomWalk.ConditionedHitting
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Supported two-dimensional conditioned transition

The second increment is selected only on the actual scalar transition support. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Restriction to the actual support, preserving all masses. Infrastructure for -/
@[expose] noncomputable def pmfOnSupport {α : Type*} (p : PMF α) : PMF p.support := by
  refine ⟨fun a => p a.val, ?_⟩
  apply CompleteLattice.summable.hasSum_iff.mpr
  calc
    (∑' a : p.support, p a.val) = ∑' a, p a :=
      tsum_subtype_eq_of_support_subset (by intro a ha; exact ha)
    _ = 1 := p.tsum_coe

/-- Support restriction preserves each mass (`eqn-cond-walk-rn`, -/
theorem pmfOnSupport_apply {α : Type*} (p : PMF α) (a : p.support) :
    pmfOnSupport p a = p a.val := rfl

/-- Forgetting support membership recovers the law (`eqn-cond-walk-rn`, -/
theorem pmfOnSupport_map_val {α : Type*} (p : PMF α) :
    (pmfOnSupport p).map Subtype.val = p := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.map_apply]
  by_cases ha : a ∈ p.support
  · let a' : p.support := ⟨a, ha⟩
    rw [tsum_eq_single a']
    · simp [pmfOnSupport_apply, a']
    · intro b hb
      have hne : a ≠ b.val := by
        intro h
        exact hb (Subtype.ext h.symm)
      simp [hne]
  · have hzero : p a = 0 := by
      by_contra h
      exact ha h
    rw [hzero]
    apply (tsum_congr ?_).trans tsum_zero
    intro b
    have hne : a ≠ b.val := by
      intro h
      exact ha (h.symm ▸ b.property)
    simp [hne]

/-- Supported targets are nearest neighbors (`eqn-cond-walk-rn`, -/
theorem conditionedLazyStep_supported_neighbor (x : ℕ)
    (z : (conditionedLazyStep x).support) : |(z.val : ℤ) - (x : ℤ)| ≤ 1 := by
  by_contra h
  have hn : conditionedLazyStep x z.val ≠ 0 := z.property
  apply hn
  rw [conditionedLazyStep_apply]
  simp [h]

/-- The actual source code of a supported target (`eqn-cond-walk-rn`, -/
@[expose] def conditionedSupportedCode (x : ℕ)
    (z : (conditionedLazyStep x).support) : Fin 3 :=
  ⟨(((z.val : ℤ) - (x : ℤ)) + 1).toNat, by
    have h := conditionedLazyStep_supported_neighbor x z
    rw [abs_le] at h
    omega⟩

/-- The selected source code has exactly the required first increment -/
theorem conditionedSupportedCode_spec (x : ℕ) (z : (conditionedLazyStep x).support) :
    (z.val : ℤ) = (x : ℤ) + (lazyTwoDimensionalStep (conditionedSupportedCode x z)).1 := by
  have h := conditionedLazyStep_supported_neighbor x z
  rw [abs_le] at h
  simp only [lazyTwoDimensionalStep, conditionedSupportedCode]
  omega

private theorem supportedCode_unique (x : ℕ) (z : (conditionedLazyStep x).support)
    (c : Fin 3) (h : (z.val : ℤ) = (x : ℤ) + (lazyTwoDimensionalStep c).1) :
    conditionedSupportedCode x z = c := by
  have hs := conditionedSupportedCode_spec x z
  simp only [lazyTwoDimensionalStep] at h hs
  apply Fin.ext
  omega

/-- Normalized transition using only actual supported scalar targets -/
@[expose] noncomputable def conditionedVectorStep (s : ℕ × ℤ) : PMF (ℕ × ℤ) :=
  (pmfOnSupport (conditionedLazyStep s.1)).map
    (fun z => (z.val, s.2 + (lazyTwoDimensionalStep (conditionedSupportedCode s.1 z)).2))

/-- Whole-carrier characterization, including illegal targets and the killed -/
theorem conditionedVectorStep_apply (x : ℕ) (y : ℤ) (t : ℕ × ℤ) :
    conditionedVectorStep (x, y) t =
      if ∃ c : Fin 3, (t.1 : ℤ) = (x : ℤ) + (lazyTwoDimensionalStep c).1 ∧
          t.2 = y + (lazyTwoDimensionalStep c).2
      then ENNReal.ofReal (conditionedLazyWeight x t.1) else 0 := by
  classical
  rw [conditionedVectorStep, PMF.map_apply]
  by_cases ht : t.1 ∈ (conditionedLazyStep x).support
  · let z₀ : (conditionedLazyStep x).support := ⟨t.1, ht⟩
    rw [tsum_eq_single z₀]
    · have he : (t = (z₀.val,
          y + (lazyTwoDimensionalStep (conditionedSupportedCode x z₀)).2)) ↔
          ∃ c : Fin 3, (t.1 : ℤ) = (x : ℤ) + (lazyTwoDimensionalStep c).1 ∧
            t.2 = y + (lazyTwoDimensionalStep c).2 := by
        constructor
        · intro h
          exact ⟨conditionedSupportedCode x z₀, conditionedSupportedCode_spec x z₀,
            congrArg Prod.snd h⟩
        · rintro ⟨c, hc, hy⟩
          have hz := supportedCode_unique x z₀ c hc
          exact Prod.ext rfl (by simpa only [hz] using hy)
      simp only [he, pmfOnSupport_apply, conditionedLazyStep_apply]
      rfl
    · intro z hz
      have hne : t ≠ (z.val,
          y + (lazyTwoDimensionalStep (conditionedSupportedCode x z)).2) := by
        intro he
        apply hz
        exact Subtype.ext (congrArg Prod.fst he).symm
      simp only [hne, ↓reduceIte]
  · have hzero : ENNReal.ofReal (conditionedLazyWeight x t.1) = 0 := by
      have hp : conditionedLazyStep x t.1 = 0 := by
        by_contra h
        exact ht h
      exact hp
    simp only [hzero, ite_self]
    apply (tsum_congr ?_).trans tsum_zero
    intro z
    have hne : t ≠ (z.val,
        y + (lazyTwoDimensionalStep (conditionedSupportedCode x z)).2) := by
      intro he
      apply ht
      exact (congrArg Prod.fst he).symm ▸ z.property
    simp only [hne, ↓reduceIte]

/-- The supported vector transition as a kernel (`eqn-cond-walk-rn`, -/
@[expose] noncomputable def conditionedVectorKernel : Kernel (ℕ × ℤ) (ℕ × ℤ) where
  toFun s := (conditionedVectorStep s).toMeasure
  measurable' := measurable_of_countable _

instance : IsMarkovKernel conditionedVectorKernel where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure (conditionedVectorStep s).toMeasure
    infer_instance

/-- Singleton masses agree with the PMF (`eqn-cond-walk-rn`, -/
theorem conditionedVectorKernel_singleton (s t : ℕ × ℤ) :
    conditionedVectorKernel s {t} = conditionedVectorStep s t := by
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)

/-- The history kernel reads the actual last state (`eqn-cond-walk-rn`, -/
@[expose] noncomputable def conditionedVectorHistoryKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℕ × ℤ) (ℕ × ℤ) where
  toFun p := conditionedVectorKernel (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _

instance (n : ℕ) : IsMarkovKernel (conditionedVectorHistoryKernel n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure
      (conditionedVectorKernel (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    infer_instance

/-- Explicit evaluation at the last state (`eqn-cond-walk-rn`, -/
theorem conditionedVectorHistoryKernel_apply (n : ℕ) (p : (i : Finset.Iic n) → ℕ × ℤ) :
    conditionedVectorHistoryKernel n p = conditionedVectorKernel (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
  rfl

/-- The first marginal is exactly the scalar conditioned transition -/
theorem conditionedVectorStep_map_fst (s : ℕ × ℤ) :
    (conditionedVectorStep s).map Prod.fst = conditionedLazyStep s.1 := by
  rw [conditionedVectorStep, PMF.map_comp]
  exact pmfOnSupport_map_val (conditionedLazyStep s.1)

end DirectedDistances.RandomWalk
