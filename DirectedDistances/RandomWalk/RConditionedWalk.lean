module

public import DirectedDistances.RandomWalk.IIDVectorWalk

/-! # Second-coordinate conditioning by rotation -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

 
@[expose] def stepRotate (z : ℤ × ℤ) : ℤ × ℤ := (z.2, -z.1 - z.2)

 
@[expose] def stepRotateInv (z : ℤ × ℤ) : ℤ × ℤ := (-z.1 - z.2, z.1)

 
theorem stepRotateInv_stepRotate (z : ℤ × ℤ) : stepRotateInv (stepRotate z) = z := by
  apply Prod.ext <;> dsimp [stepRotateInv, stepRotate]; omega

 
theorem stepRotate_stepRotateInv (z : ℤ × ℤ) : stepRotate (stepRotateInv z) = z := by
  apply Prod.ext <;> dsimp [stepRotateInv, stepRotate]; omega

 
theorem stepRotate_step (c : Fin 3) :
    stepRotate (lazyTwoDimensionalStep c) = lazyTwoDimensionalStep (c + 1) := by
  fin_cases c <;> decide

private theorem stepRotate_add (z w : ℤ × ℤ) :
    stepRotate (z + w) = stepRotate z + stepRotate w := by
  apply Prod.ext <;> dsimp [stepRotate]; omega

private theorem stepRotate_sub (z w : ℤ × ℤ) :
    stepRotate (z - w) = stepRotate z - stepRotate w := by
  apply Prod.ext <;> dsimp [stepRotate]; omega

 
theorem stepRotate_prefix {n : ℕ} (x y : ℤ) (w : Fin n → Fin 3)
    (j : Fin (n + 1)) :
    stepRotate (lazyTwoDimensionalPrefix x y w j) =
      lazyTwoDimensionalPrefix y (-x-y) (fun i => w i + 1) j := by
  induction j using Fin.induction with
  | zero => rw [lazyTwoDimensionalPrefix_zero, lazyTwoDimensionalPrefix_zero]; rfl
  | succ i ih =>
    rw [lazyTwoDimensionalPrefix_succ, stepRotate_add, ih,
      stepRotate_step, lazyTwoDimensionalPrefix_succ]

/-- The conjugate flip has the displayed formula on every path, hence also zero-start paths -/
theorem rPitman_pathwise (z : ℕ → ℤ × ℤ) (n : ℕ) :
    stepRotateInv (vectorPitman (fun k => stepRotate (z k)) n) =
      ((z n).1 + globalLazyRunningMinimum (fun k => (z k).2) n,
       (z n).2 - 2 * globalLazyRunningMinimum (fun k => (z k).2) n) := by
  apply Prod.ext <;> dsimp [stepRotateInv, vectorPitman, globalLazyPhi, stepRotate]; omega

 
@[expose] noncomputable def rConditionedPathLaw (x : ℤ) (y : ℕ) :
    Measure (ℕ → ℤ × ℤ) :=
  (conditionedVectorPathLaw y (-x - (y : ℤ))).map (fun p n => stepRotateInv (p n))

instance (x : ℤ) (y : ℕ) : IsProbabilityMeasure (rConditionedPathLaw x y) := by
  unfold rConditionedPathLaw
  have hm : Measurable (fun p : ℕ → ℤ × ℤ => fun n => stepRotateInv (p n)) :=
    Measurable.of_eval (fun n =>
      (measurable_of_countable stepRotateInv).comp (measurable_pi_apply n))
  exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance

private theorem uniform_map_equiv {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (e : α ≃ α) :
    (Measure.uniformOfFinset (Finset.univ : Finset α)).map e =
      Measure.uniformOfFinset Finset.univ := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : e ⁻¹' {a} = {e.symm a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Equiv.eq_symm_apply]
  rw [he]
  simp only [Measure.uniformOfFinset_apply_singleton, Finset.mem_univ, ite_true]

private def rotateWord (n : ℕ) : (Fin n → Fin 3) ≃ (Fin n → Fin 3) where
  toFun w i := w i + 1
  invFun w i := w i - 1
  left_inv w := by funext i; exact add_sub_cancel_right (w i) 1
  right_inv w := by funext i; exact sub_add_cancel (w i) 1

private theorem map_uniform_vectorSteps_rotate :
    (Measure.uniformOfFinset
      ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))).map stepRotate =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ)) := by
  have hmap (c : ℝ≥0∞) (z : ℤ × ℤ) :
      (c • Measure.dirac z).map stepRotate = c • Measure.dirac (stepRotate z) := by
    rw [Measure.map_smul c (measurable_of_countable _).aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset]
  norm_num [Measure.map_add, measurable_of_countable stepRotate, hmap, stepRotate]
  ac_rfl


private theorem map_prefix_rotate (x y : ℤ) (n : ℕ) :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix x y)).map (fun q j => stepRotate (q j)) =
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix y (-x-y)) := by
  have ht :
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix x y)).map (fun q j => stepRotate (q j)) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (rotateWord n)).map (lazyTwoDimensionalPrefix y (-x-y)) := by
    simp only [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext w j
    exact stepRotate_prefix x y w j
  rw [uniform_map_equiv] at ht
  exact ht

private theorem map_prefix_rotateInv (x y : ℤ) (n : ℕ) :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix y (-x-y))).map (fun q j => stepRotateInv (q j)) =
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix x y) := by
  rw [← map_prefix_rotate x y n,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [Function.comp_def, stepRotateInv_stepRotate, Measure.map_id']

private theorem map_density_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {f : α → β} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (ν.withDensity (fun x => g (f x))).map f = (ν.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hg hf]

/-- The exact second-coordinate all-horizon RN law (`eqn-cond-walk-rn` with R for L, -/
theorem rConditionedPathLaw_map_prefix (x : ℤ) (y : ℕ) (n : ℕ) :
    (rConditionedPathLaw x y).map (fun q => fun j : Fin (n + 1) => q j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix x (y : ℤ))).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).2 then
          ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) / ((y : ℝ) + 1)) else 0) := by
  classical
  have hm : Measurable (fun p : ℕ → ℤ × ℤ => fun n => stepRotateInv (p n)) :=
    Measurable.of_eval (fun n =>
      (measurable_of_countable stepRotateInv).comp (measurable_pi_apply n))
  have he : (rConditionedPathLaw x y).map (fun q => fun j : Fin (n + 1) => q j.val) =
      ((conditionedVectorPathLaw y (-x-(y : ℤ))).map
        (fun q => fun j : Fin (n + 1) => q j.val)).map
        (fun q j => stepRotateInv (q j)) := by
    rw [rConditionedPathLaw, Measure.map_map (by fun_prop) hm,
      Measure.map_map (measurable_of_countable _) (by fun_prop)]
    rfl
  rw [he, conditionedVectorPathLaw_map_prefix]
  change (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
    (lazyTwoDimensionalPrefix (y : ℤ) (-x-(y : ℤ)))).withDensity
      (fun q => (fun p => if ∀ j, 0 ≤ (p j).2 then
        ENNReal.ofReal ((((p (Fin.last n)).2 : ℝ) + 1) / ((y : ℝ) + 1)) else 0)
        (fun j => stepRotateInv (q j)))).map _ = _
  rw [map_density_comp
    (f := fun q : Fin (n + 1) → ℤ × ℤ => fun j => stepRotateInv (q j))
    (g := fun p : Fin (n + 1) → ℤ × ℤ => if ∀ j, 0 ≤ (p j).2 then
      ENNReal.ofReal ((((p (Fin.last n)).2 : ℝ) + 1) / ((y : ℝ) + 1)) else 0)
    (measurable_of_countable _) (measurable_of_countable _), map_prefix_rotateInv]

/-- The R-Pitman flip of an iid source walk has the R-conditioned law -/
theorem rPitman_law_eq_rConditionedPathLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℕ → ℤ × ℤ}
    (hZ : Measurable Z) (hzero : ∀ᵐ ω ∂μ, Z ω 0 = (0, 0))
    (hind : iIndepFun (fun i ω => Z ω (i + 1) - Z ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    μ.map (fun ω k => stepRotateInv (vectorPitman (fun n => stepRotate (Z ω n)) k)) =
        rConditionedPathLaw 0 0 := by
  have hrot : Measurable (fun ω n => stepRotate (Z ω n)) :=
    Measurable.of_eval (fun n => (measurable_of_countable stepRotate).comp
      ((measurable_pi_apply n).comp hZ))
  have hz : ∀ᵐ ω ∂μ, stepRotate (Z ω 0) = (0, 0) := by
    filter_upwards [hzero] with ω hω
    rw [hω]
    rfl
  have hi : iIndepFun (fun i ω => stepRotate (Z ω (i + 1)) - stepRotate (Z ω i)) μ := by
    simp only [← stepRotate_sub]
    exact hind.comp (fun _ => stepRotate) (fun _ => measurable_of_countable _)
  have hl (i : ℕ) :
      μ.map (fun ω => stepRotate (Z ω (i + 1)) - stepRotate (Z ω i)) =
        Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ)) := by
    simp only [← stepRotate_sub]
    rw [show (fun ω => stepRotate (Z ω (i + 1) - Z ω i)) =
      stepRotate ∘ (fun ω => Z ω (i + 1) - Z ω i) from rfl,
      ← Measure.map_map (measurable_of_countable _) (by fun_prop), hlaw i,
      map_uniform_vectorSteps_rotate]
  have h := vectorPitman_law_eq_conditionedVectorPathLaw hrot hz hi hl
  have hflip : Measurable (fun ω k => vectorPitman (fun n => stepRotate (Z ω n)) k) := by
    apply Measurable.of_eval
    intro n
    exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp
      (show Measurable (fun ω k => (stepRotate (Z ω k)).1) by fun_prop)).prodMk
      (show Measurable (fun ω => (stepRotate (Z ω n)).2 +
        globalLazyRunningMinimum (fun k => (stepRotate (Z ω k)).1) n) from
        (show Measurable (fun ω => (stepRotate (Z ω n)).2) by
          exact (measurable_pi_apply n |>.comp hrot).snd).add
          ((measurable_globalLazyRunningMinimum n).comp
            (show Measurable (fun ω k => (stepRotate (Z ω k)).1) by fun_prop)))
  have hinv : Measurable (fun p : ℕ → ℤ × ℤ => fun n => stepRotateInv (p n)) :=
    Measurable.of_eval (fun n =>
      (measurable_of_countable stepRotateInv).comp (measurable_pi_apply n))
  have hh := congrArg (fun ρ : Measure (ℕ → ℤ × ℤ) =>
    ρ.map (fun p n => stepRotateInv (p n))) h
  rw [Measure.map_map hinv hflip] at hh
  simpa only [rConditionedPathLaw, Nat.cast_zero, neg_zero, sub_zero,
    Function.comp_def] using hh

/-- Explicit iid realization of the R-conditioned law -/
theorem map_rPitman_codeWalk :
    iidCodeMeasure.map (fun ω k =>
      stepRotateInv (vectorPitman (fun n => stepRotate (codeWalk ω n)) k)) =
        rConditionedPathLaw 0 0 := by
  exact rPitman_law_eq_rConditionedPathLaw measurable_codeWalk
    (Filter.Eventually.of_forall codeWalk_zero) iIndepFun_codeWalk_increments
    map_codeWalk_increment

end DirectedDistances.RandomWalk
