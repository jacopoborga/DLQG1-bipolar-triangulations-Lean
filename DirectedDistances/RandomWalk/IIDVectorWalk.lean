module

public import DirectedDistances.RandomWalk.VectorPitman
public import DirectedDistances.Probability.CountableMarkovTrajectory
public import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # An explicit iid vector walk and its Pitman image

Helpers for the unnumbered assertion in the proof of `lem-quadrant-walk`, -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private instance : IsProbabilityMeasure
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Uniform source-code law for `lem-quadrant-walk` -/
@[expose] noncomputable def uniformCodeMeasure : Measure (Fin 3) :=
  Measure.uniformOfFinset Finset.univ

instance : IsProbabilityMeasure uniformCodeMeasure := by
  unfold uniformCodeMeasure
  infer_instance

/-- Uniform independent transition codes for `lem-quadrant-walk`
only the coordinates `ω (i + 1)` are used as source codes. -/
@[expose] noncomputable def iidCodeMeasure : Measure (ℕ → Fin 3) :=
  DirectedDistances.Probability.markovTrajectory (Kernel.const (Fin 3) uniformCodeMeasure) 0

instance : IsProbabilityMeasure iidCodeMeasure := by
  unfold iidCodeMeasure
  infer_instance

private noncomputable def codeMarginal (i : ℕ) : Measure (Fin 3) :=
  if i = 0 then Measure.dirac 0 else uniformCodeMeasure

private instance (i : ℕ) : IsProbabilityMeasure (codeMarginal i) := by
  unfold codeMarginal
  split <;> infer_instance

/-- Finite trajectory marginals, including the deterministic time-zero code.
This is derived from the Markov trajectory prefix formula, for -/
theorem iidCodeMeasure_map_prefix (n : ℕ) :
    iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => ω j.val) =
      Measure.pi (fun j : Fin (n + 1) =>
        if j.val = 0 then Measure.dirac 0 else uniformCodeMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro q
  rw [iidCodeMeasure,
    DirectedDistances.Probability.markovTrajectory_map_fin_prefix_singleton,
    Measure.pi_singleton, Fin.prod_univ_succ]
  simp only [Kernel.const_apply, Fin.val_zero, ↓reduceIte, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false]
  by_cases h : q 0 = 0
  · simp [h]
  · simp [h, Ne.symm h]

private theorem map_code_coordinate (i : ℕ) :
    iidCodeMeasure.map (fun ω => ω (i + 1)) = uniformCodeMeasure := by
  let j : Fin (i + 1 + 1) := ⟨i + 1, by omega⟩
  have h := congrArg (fun μ : Measure (Fin (i + 1 + 1) → Fin 3) =>
    μ.map (Function.eval j)) (iidCodeMeasure_map_prefix (i + 1))
  rw [Measure.map_map (measurable_pi_apply j) (by fun_prop)] at h
  have hp : (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginal j.val)).map
      (Function.eval j) = codeMarginal j.val := (measurePreserving_eval _ j).map_eq
  change _ = (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginal j.val)).map
    (Function.eval j) at h
  rw [hp] at h
  simpa [codeMarginal, j, Function.comp_def, Function.eval] using h

private theorem iIndepFun_code_coordinates :
    iIndepFun (fun i (ω : ℕ → Fin 3) => ω (i + 1)) iidCodeMeasure := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  let n := s.sup id + 1
  let e (i : s) : Fin (n + 1) := ⟨i.val + 1, by
    have := Finset.le_sup (f := id) i.property
    change i.val ≤ s.sup id at this
    dsimp [n]
    omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    have := congrArg Fin.val h
    dsimp [e] at this
    omega
  let μ := Measure.pi (fun j : Fin (n + 1) => codeMarginal j.val)
  have hind : iIndepFun (fun i : s => fun q : Fin (n + 1) → Fin 3 => q (e i)) μ :=
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).precomp he
  have hm : iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => ω j.val) = μ :=
    iidCodeMeasure_map_prefix n
  have hmass (t : Set (Fin (n + 1) → Fin 3)) :
      μ t = iidCodeMeasure ((fun ω => fun j : Fin (n + 1) => ω j.val) ⁻¹' t) := by
    rw [← hm, Measure.map_apply (by fun_prop) ((Set.to_countable t).measurableSet)]
  have h := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : s => sets i.val) (fun _ _ => (Set.to_countable _).measurableSet)
  simp only [hmass] at h
  rw [← Finset.prod_coe_sort]
  convert h using 1
  · congr 1
    ext ω
    simp [e]
  · apply Finset.prod_congr rfl
    intro i _
    congr 1

/-- The integrated source walk from `(0,0)` for `lem-quadrant-walk`
skipping the deterministic time-zero state of the trajectory. -/
@[expose] def codeWalk (ω : ℕ → Fin 3) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, lazyTwoDimensionalStep (ω (i + 1))

/-- Measurability of the source walk in `lem-quadrant-walk` -/
theorem measurable_codeWalk : Measurable (fun ω : ℕ → Fin 3 => fun n => codeWalk ω n) := by
  apply Measurable.of_eval
  intro n
  exact (Finset.range n).measurable_sum (fun i _ =>
    (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply (i + 1)))

/-- The source walk starts at zero in `lem-quadrant-walk` -/
theorem codeWalk_zero (ω : ℕ → Fin 3) : codeWalk ω 0 = (0, 0) := by
  simp only [codeWalk, Finset.range_zero, Finset.sum_empty]
  rfl

/-- Each increment is the literal source step in `lem-quadrant-walk` -/
theorem codeWalk_succ_sub (ω : ℕ → Fin 3) (i : ℕ) :
    codeWalk ω (i + 1) - codeWalk ω i = lazyTwoDimensionalStep (ω (i + 1)) := by
  simp only [codeWalk, Finset.sum_range_succ]
  abel

/-- Independence of the source increments in `lem-quadrant-walk` -/
theorem iIndepFun_codeWalk_increments :
    iIndepFun (fun i ω => codeWalk ω (i + 1) - codeWalk ω i) iidCodeMeasure := by
  simp only [codeWalk_succ_sub]
  exact iIndepFun_code_coordinates.comp (fun _ => lazyTwoDimensionalStep)
    (fun _ => measurable_of_countable _)

/-- The exact uniform source increment law in `lem-quadrant-walk` -/
theorem map_codeWalk_increment (i : ℕ) :
    iidCodeMeasure.map (fun ω => codeWalk ω (i + 1) - codeWalk ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ)) := by
  simp only [codeWalk_succ_sub]
  change iidCodeMeasure.map (lazyTwoDimensionalStep ∘ (fun ω => ω (i + 1))) = _
  rw [← Measure.map_map (measurable_of_countable lazyTwoDimensionalStep)
    (measurable_pi_apply (i + 1)), map_code_coordinate, uniformCodeMeasure,
    map_uniform_lazyTwoDimensionalStep]
  congr 1
  decide

/-- Explicit representation of the constructed conditioned law in -/
theorem map_vectorPitman_codeWalk :
    iidCodeMeasure.map (fun ω k => vectorPitman (codeWalk ω) k) =
      conditionedVectorPathLaw 0 0 := by
  exact vectorPitman_law_eq_conditionedVectorPathLaw measurable_codeWalk
    (Filter.Eventually.of_forall codeWalk_zero) iIndepFun_codeWalk_increments
    map_codeWalk_increment

end DirectedDistances.RandomWalk
