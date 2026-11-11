/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantWalkLaw

/-! # Assembled code-level quadrant walk laws

Witness-independent versions of the interval-coded paths and consequences of
shifted-path clause remains conditional on the separate primed identity -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW

/-- Totalized unprimed interval path, using the hit witness when it exists -/
@[expose] noncomputable def quadrantHatWalk (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  by
    classical
    exact if h : HasFlowLineHits (fun i => ω (i + 1)) then quadrantHatIntervalWalk ω h
      else fun _ => 0

/-- Totalized primed interval path, using the hit witness when it exists -/
@[expose] noncomputable def quadrantPrimedWalk (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  by
    classical
    exact if h : HasFlowLineHits (fun i => ω (i + 1)) then quadrantPrimedIntervalWalk ω h
      else fun _ => 0

/-- The interval path is independent of the particular proof of the hit
property, since `HasFlowLineHits` is proposition-valued -/
theorem quadrantHatIntervalWalk_witness_irrel (ω : ℕ → Fin 3)
    (h₁ h₂ : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantHatIntervalWalk ω h₁ = quadrantHatIntervalWalk ω h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- The primed interval path is independent of the particular proof of the -/
theorem quadrantPrimedIntervalWalk_witness_irrel (ω : ℕ → Fin 3)
    (h₁ h₂ : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantPrimedIntervalWalk ω h₁ = quadrantPrimedIntervalWalk ω h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- The totalized path agrees with every interval witness whenever one exists -/
theorem quadrantHatWalk_eq_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantHatWalk ω = quadrantHatIntervalWalk ω h := by
  classical
  simp [quadrantHatWalk, h]

/-- The totalized primed path agrees with every interval witness whenever one -/
theorem quadrantPrimedWalk_eq_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantPrimedWalk ω = quadrantPrimedIntervalWalk ω h := by
  classical
  simp [quadrantPrimedWalk, h]

/-- Almost surely the totalized unprimed walk is the split-stream L-Pitman -/
theorem iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk :
    ∀ᵐ ω ∂iidCodeMeasure,
      quadrantHatWalk ω = vectorPitmanCodeWalk ((phaseSplit ω).1) := by
  filter_upwards [iidCodeMeasure_ae_quadrantHatIntervalWalk_eq_vectorPitmanCodeWalk]
    with ω h
  rcases h with ⟨w, hw⟩
  exact (quadrantHatWalk_eq_interval ω w).trans hw

/-- Measurability of the vector Pitman transform on a measurable path-valued -/
private theorem measurable_vectorPitmanMap_total {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℕ → ℤ × ℤ) (hZ : Measurable Z) :
    Measurable (fun ω k => vectorPitman (Z ω) k) := by
  have hL : Measurable (fun ω k => (Z ω k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp hZ).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL))

private theorem measurableVectorPitmanCodeWalk_total :
    Measurable vectorPitmanCodeWalk := by
  change Measurable (fun ω k => vectorPitman (codeWalk ω) k)
  exact measurable_vectorPitmanMap_total codeWalk measurable_codeWalk

/-- The totalized unprimed path is almost surely measurable as a path-valued -/
theorem aemeasurable_quadrantHatWalk : AEMeasurable quadrantHatWalk iidCodeMeasure := by
  have hF : Measurable (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) :=
    measurableVectorPitmanCodeWalk_total.comp
      (measurable_fst.comp measurable_phaseSplit)
  have hae : (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) =ᵐ[iidCodeMeasure]
      quadrantHatWalk := by
    filter_upwards [iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk] with ω h
    exact h.symm
  exact hF.aemeasurable.congr hae

/-- The all-horizon L-conditioned prefix law for the totalized unprimed walk -/
theorem quadrantHatWalk_prefix_law (n : ℕ) :
    iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) => quadrantHatWalk ω j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0) := by
  have hprefix : (fun ω => fun j : Fin (n + 1) => quadrantHatWalk ω j.val) =ᵐ[iidCodeMeasure]
      (fun ω => fun j : Fin (n + 1) => vectorPitmanCodeWalk ((phaseSplit ω).1) j.val) := by
    filter_upwards [iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk] with ω h
    funext j
    exact congrFun h j.val
  rw [Measure.map_congr hprefix]
  exact quadrant_walk_split_pitman_prefix_laws n |>.1

/-- Almost surely the totalized primed path has the C13 initial values -/
theorem iidCodeMeasure_ae_quadrantPrimedWalk_initial :
    ∀ᵐ ω ∂iidCodeMeasure,
      quadrantPrimedWalk ω 0 = (0, 0) ∧ quadrantPrimedWalk ω 1 = (0, 1) := by
  filter_upwards [iidCodeMeasure_ae_quadrantPrimedIntervalWalk_initial] with ω h
  rcases h with ⟨w, hzero, hone⟩
  have heq := quadrantPrimedWalk_eq_interval ω w
  exact ⟨(congrFun heq 0).trans hzero, (congrFun heq 1).trans hone⟩

/-- Independence is unchanged when both random variables are replaced by -/
theorem indepFun_congr_ae_total {Ω β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω}
    {f f' : Ω → β} {g g' : Ω → γ}
    (hfg : f ⟂ᵢ[μ] g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    f' ⟂ᵢ[μ] g' := hfg.congr hf hg

/-- A.e.-equal random variables have identical pushforward laws -/
theorem measure_map_congr_ae_total {Ω β : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace β] {μ : Measure[mΩ] Ω} {f g : Ω → β}
    (h : f =ᵐ[μ] g) : μ.map f = μ.map g := Measure.map_congr h

/-- Reconstruct a path from its increments after time one and its prescribed -/
@[expose] def quadrantPrimedReconstruct (p : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun n => match n with
    | 0 => (0, 0)
    | k + 1 => p k + (0, 1)

private theorem measurableQuadrantPrimedReconstruct :
    Measurable quadrantPrimedReconstruct := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_const
  | succ k => exact (measurable_pi_apply k).add measurable_const

/-- Under the primed identity, the unprimed totalized walk is independent of -/
theorem quadrantHatWalk_indep_shiftedPrimedWalk
    (Hprimed : ∀ᵐ ω ∂iidCodeMeasure, ∀ m,
      quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m) :
    quadrantHatWalk ⟂ᵢ[iidCodeMeasure]
      (fun ω m => quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1) := by
  have hL : (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) =ᵐ[iidCodeMeasure]
      quadrantHatWalk := by
    filter_upwards [iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk] with ω h
    exact h.symm
  have hR : (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) =ᵐ[iidCodeMeasure]
      (fun ω m => quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1) := by
    filter_upwards [Hprimed] with ω hω
    funext m
    exact (hω m).symm
  exact quadrant_walk_split_pitman_independent.congr hL hR

/-- The shifted primed totalized walk has the all-horizon R-conditioned -/
theorem quadrantPrimedShift_prefix_law
    (Hprimed : ∀ᵐ ω ∂iidCodeMeasure, ∀ m,
      quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m)
    (n : ℕ) :
    iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      quadrantPrimedWalk ω (j.val + 1) - quadrantPrimedWalk ω 1) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0) := by
  have hprefix : (fun ω => fun j : Fin (n + 1) =>
      quadrantPrimedWalk ω (j.val + 1) - quadrantPrimedWalk ω 1) =ᵐ[iidCodeMeasure]
      (fun ω => fun j : Fin (n + 1) =>
        rPitmanCodeWalk ((phaseSplit ω).2) j.val) := by
    filter_upwards [Hprimed] with ω hω
    funext j
    exact hω j.val
  rw [Measure.map_congr hprefix]
  exact (quadrant_walk_split_pitman_prefix_laws n).2

/-- Independence also holds for the unshifted primed path: C13 supplies the
first step needed to reconstruct it from the shifted path -/
theorem quadrantHatWalk_indep_quadrantPrimedWalk
    (Hprimed : ∀ᵐ ω ∂iidCodeMeasure, ∀ m,
      quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m) :
    quadrantHatWalk ⟂ᵢ[iidCodeMeasure] quadrantPrimedWalk := by
  have hshift := quadrantHatWalk_indep_shiftedPrimedWalk Hprimed
  have hrec : (quadrantPrimedReconstruct ∘
      (fun ω m => quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1)) =ᵐ[iidCodeMeasure]
      quadrantPrimedWalk := by
    filter_upwards [iidCodeMeasure_ae_quadrantPrimedWalk_initial] with ω hω
    funext n
    cases n with
    | zero => simpa [quadrantPrimedReconstruct] using hω.1.symm
    | succ k => simp [quadrantPrimedReconstruct, hω.2]
  have hrecIndep := hshift.comp measurable_id measurableQuadrantPrimedReconstruct
  exact hrecIndep.congr ae_eq_rfl hrec

/-- Conditional assembly of the code-level clauses of `lem-quadrant-walk` -/
theorem quadrant_walk_law_of_primed_identity
    (Hprimed : ∀ᵐ ω ∂iidCodeMeasure, ∀ m,
      quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m) :
    (∀ᵐ ω ∂iidCodeMeasure,
      quadrantHatWalk ω = vectorPitmanCodeWalk ((phaseSplit ω).1)) ∧
    AEMeasurable quadrantHatWalk iidCodeMeasure ∧
    (∀ n, iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => quadrantHatWalk ω j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0)) ∧
    (∀ᵐ ω ∂iidCodeMeasure,
      quadrantPrimedWalk ω 0 = (0, 0) ∧ quadrantPrimedWalk ω 1 = (0, 1)) ∧
    quadrantHatWalk ⟂ᵢ[iidCodeMeasure]
      (fun ω m => quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1) ∧
    quadrantHatWalk ⟂ᵢ[iidCodeMeasure] quadrantPrimedWalk ∧
    (∀ n, iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      quadrantPrimedWalk ω (j.val + 1) - quadrantPrimedWalk ω 1) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0)) := by
  refine ⟨iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk,
    aemeasurable_quadrantHatWalk, ?_, iidCodeMeasure_ae_quadrantPrimedWalk_initial,
    quadrantHatWalk_indep_shiftedPrimedWalk Hprimed,
    quadrantHatWalk_indep_quadrantPrimedWalk Hprimed, ?_⟩
  · intro n
    exact quadrantHatWalk_prefix_law n
  · intro n
    exact quadrantPrimedShift_prefix_law Hprimed n

end DirectedDistances.RandomWalk
