/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantLaws
public import DirectedDistances.KMSW.QuadKMSWHatFlipped
public import DirectedDistances.KMSW.PrimedLPhaseRecode
public import DirectedDistances.KMSW.WindowModelHatCodes

/-! # Code-level provider toward corrected Lemma 5.14

processes and their path laws are available here. They have not been
identified with the walks defined by `eqn-walk-quadrant` and
`eqn-walk-quadrant'`; the remaining boundary/index reconciliation is recorded
in the declaration documentation below and in `PhaseTimesBridge2`.

The intended `quadrant_walk_law_corrected` target has four source-level
clauses: independence of `Ẑ` and `Ẑ'`; for every `n`, the law of `Ẑ(0..n)` is
the uniform source-prefix law weighted by
`1{∀ j ≤ n, 0 ≤ Ẑ_L(j)} (Ẑ_L(n)+1)`; almost surely `Ẑ'(0)=(0,0)` and, by C13,
`Ẑ'(1)=(0,1)`; and for every `n`, the prefix law of
`Ẑ'(·+1)-Ẑ'(1)` is weighted by
`1{∀ j ≤ n, 0 ≤ R(j)} (R(n)+1)`. No theorem with that name is stated here:
the current Lean interval producers do not define the printed `S_m,S'_m`
paths. The confirmed but unapproved positive-time counting convention issue is that the printed count
includes `n=0`, giving `S_1=0` and the undefined increment
primed code-level bridge is recorded alongside the proved C13 initial clause. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW

/-- Integrated interval-coded walk from `eqn-quad-pre2`: each `hatCodes`
entry supplies the arriving step, with exit steps replaced by the next R
candidate code-level representation of `Ẑ`; the source's `S_m` count and its
boundary index have not been reconciled with these interval indices in Lean. -/
@[expose] noncomputable def quadrantHatIntervalWalk (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) : ℕ → ℤ × ℤ :=
  integrateCodes (hatCodes (fun i => ω (i + 1)) h)

/-- Integrated interval-coded primed walk from `eqn-quad-pre3`, using the
C13 replacement code `1` and hence the corrected first step `(0,1)`
candidate is parameterized by a flow-line-hit witness; its equality to the
printed `S'_m` definition is not asserted. -/
@[expose] noncomputable def quadrantPrimedIntervalWalk (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) : ℕ → ℤ × ℤ :=
  integrateCodes (primedCode ω h)

/-- primed interval path takes first step `(0,1)` (`eqn-quad-pre3` and C13,
needed for the R-conditioned clause is
`quadrantPrimedIntervalWalk ω h (m+1) - quadrantPrimedIntervalWalk ω h 1 =
rPitmanCodeWalk ((phaseSplit ω).2) m`; it is not established here, and positive-time counting convention
still prevents replacing the interval path by the printed `S'_m` path. -/
theorem quadrantIntervalWalk_initial (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantHatIntervalWalk ω h 0 = (0, 0) ∧
      quadrantPrimedIntervalWalk ω h 0 = (0, 0) ∧
      quadrantPrimedIntervalWalk ω h 1 = (0, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · change (0 : ℤ × ℤ) = (0, 0)
    rfl
  · change (0 : ℤ × ℤ) = (0, 0)
    rfl
  · change integrateCodes (primedCode ω h) 1 = (0, 1)
    rw [show integrateCodes (primedCode ω h) 1 =
      lazyTwoDimensionalStep (primedCode ω h 0) by simp [integrateCodes]]
    exact lazyTwoDimensionalStep_primedCode_zero ω h

/-- Almost surely there is a flow-line-hit witness for which the interval
primed path has the C13 initial values. This is the interval-code clause only, -/
theorem iidCodeMeasure_ae_quadrantPrimedIntervalWalk_initial :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      quadrantPrimedIntervalWalk ω h 0 = (0, 0) ∧
        quadrantPrimedIntervalWalk ω h 1 = (0, 1) := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hhits
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa using hhits 0
  exact ⟨h, (quadrantIntervalWalk_initial ω h).2⟩

/-- The unprimed interval-coded path is the split-stream L-Pitman path when
the input has its fixed time-zero code. This identifies the interval code
producer `hatCodes` with the Pitman path, but does not reconcile the source's
printed `S_m` count (positive-time counting convention) with the interval indexing -/
theorem quadrantHatIntervalWalk_eq_vectorPitmanCodeWalk (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (hzero : ω 0 = 0) :
    quadrantHatIntervalWalk ω h =
      vectorPitmanCodeWalk ((phaseSplit ω).1) := by
  have htraj : quadrantTrajectoryOfStageCodes (fun i => ω (i + 1)) = ω := by
    funext n
    cases n with
    | zero => simpa [quadrantTrajectoryOfStageCodes] using hzero.symm
    | succ n => rfl
  change integrateCodes (hatCodes (fun i => ω (i + 1)) h) = _
  rw [← rCodeSequence_quadrantTrajectory_eq_hatCodes
    (fun i => ω (i + 1)) h]
  rw [htraj]
  funext n
  rw [show rCodeSequence ω =
    pitmanCode (fun i => (phaseSplit ω).1 (i + 1)) from rfl,
    integrateCodes_pitmanCode]
  change vectorPitman (integrateCodes
      (fun i => (phaseSplit ω).1 (i + 1))) n =
    vectorPitman (codeWalk ((phaseSplit ω).1)) n
  congr 1

private theorem iidCodeMeasure_ae_codeZero :
    ∀ᵐ ω ∂iidCodeMeasure, ω 0 = (0 : Fin 3) := by
  simpa only [iidCodeMeasure] using
    DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)

/- Almost surely, the interval-coded unprimed walk agrees with the L-Pitman
code walk for a flow-line-hit witness. This remains a code/interval identity;
the printed `S_m` zero-time defect (positive-time counting convention) prevents identifying it with the -/
theorem iidCodeMeasure_ae_quadrantHatIntervalWalk_eq_vectorPitmanCodeWalk :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      quadrantHatIntervalWalk ω h =
        vectorPitmanCodeWalk ((phaseSplit ω).1) := by
  filter_upwards [iidCodeMeasure_ae_codeZero,
    iidCodes_ae_hasFlowLineHits_all_future_times] with ω hzero hhits
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa using hhits 0
  exact ⟨h, quadrantHatIntervalWalk_eq_vectorPitmanCodeWalk ω h hzero⟩

/-- Independence of the phase-split Pitman code walks, a provider clause
Identifying these paths with the source walks `eqn-walk-quadrant` and
`eqn-walk-quadrant'` remains a separate boundary/index obligation. -/
theorem quadrant_walk_split_pitman_independent :
    (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) ⟂ᵢ[iidCodeMeasure]
      (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) :=
  indepFun_phaseSplit_pitmanProcesses

private theorem measurable_vectorPitman_map_local {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℕ → ℤ × ℤ) (hZ : Measurable Z) :
    Measurable (fun ω k => vectorPitman (Z ω) k) := by
  have hL : Measurable (fun ω k => (Z ω k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp hZ).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL))

private theorem measurable_vectorPitmanCodeWalk_local :
    Measurable vectorPitmanCodeWalk := by
  change Measurable (fun ω k => vectorPitman (codeWalk ω) k)
  exact measurable_vectorPitman_map_local codeWalk measurable_codeWalk

private theorem measurable_rPitmanCodeWalk_local :
    Measurable rPitmanCodeWalk := by
  have hrot : Measurable (fun ω : ℕ → Fin 3 =>
      fun n => stepRotate (codeWalk ω n)) :=
    Measurable.of_eval fun n =>
      (measurable_of_countable stepRotate).comp
        ((measurable_pi_apply n).comp measurable_codeWalk)
  have hpit := measurable_vectorPitman_map_local
    (fun ω n => stepRotate (codeWalk ω n)) hrot
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable stepRotateInv).comp
    ((measurable_pi_apply n).comp hpit)

private theorem measurable_pathPrefix (n : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ =>
      fun j : Fin (n + 1) => p j.val) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply j.val

/-- The vector Pitman image of one iid code stream has the exact all-horizon
L-conditioned prefix identity, with the source density
`1{L(j) ≥ 0 for all j ≤ n} (L(n)+1)` at start `(0,0)` -/
theorem vectorPitmanCodeWalk_prefix_law (n : ℕ) :
    iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) => vectorPitmanCodeWalk ω j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0) := by
  have hp := measurable_pathPrefix n
  have hlaw : iidCodeMeasure.map vectorPitmanCodeWalk =
      conditionedVectorPathLaw 0 0 := by
    change iidCodeMeasure.map
      (fun ω k => vectorPitman (codeWalk ω) k) = _
    exact map_vectorPitman_codeWalk
  calc
    iidCodeMeasure.map (fun ω =>
        fun j : Fin (n + 1) => vectorPitmanCodeWalk ω j.val) =
        (iidCodeMeasure.map vectorPitmanCodeWalk).map
          (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) := by
            rw [Measure.map_map hp measurable_vectorPitmanCodeWalk_local]
            rfl
    _ = (conditionedVectorPathLaw 0 0).map
          (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) := by
            rw [hlaw]
    _ = _ := by
      simpa using conditionedVectorPathLaw_map_prefix 0 0 n

/-- The R-Pitman image of one iid code stream has the exact all-horizon
R-conditioned prefix identity, with the source density
`1{R(j) ≥ 0 for all j ≤ n} (R(n)+1)` at start `(0,0)` -/
theorem rPitmanCodeWalk_prefix_law (n : ℕ) :
    iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) => rPitmanCodeWalk ω j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).2 then
          ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0) := by
  have hp := measurable_pathPrefix n
  have hlaw : iidCodeMeasure.map rPitmanCodeWalk =
      rConditionedPathLaw 0 0 := by
    change iidCodeMeasure.map (fun ω k =>
      stepRotateInv (vectorPitman (fun n => stepRotate (codeWalk ω n)) k)) = _
    exact map_rPitman_codeWalk
  calc
    iidCodeMeasure.map (fun ω =>
        fun j : Fin (n + 1) => rPitmanCodeWalk ω j.val) =
        (iidCodeMeasure.map rPitmanCodeWalk).map
          (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) := by
            rw [Measure.map_map hp measurable_rPitmanCodeWalk_local]
            rfl
    _ = (rConditionedPathLaw 0 0).map
          (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) := by
            rw [hlaw]
    _ = _ := by
      simpa using rConditionedPathLaw_map_prefix 0 0 n

/-- All-horizon L- and R-conditioned prefix laws for the two independent
phase-split Pitman code paths. These are code-level providers toward corrected
Lemma 5.14; the interval-coded paths above still require their source -/
theorem quadrant_walk_split_pitman_prefix_laws (n : ℕ) :
    iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      vectorPitmanCodeWalk ((phaseSplit ω).1) j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0) ∧
    iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      rPitmanCodeWalk ((phaseSplit ω).2) j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0) := by
  constructor
  · have hmap : iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
        vectorPitmanCodeWalk ((phaseSplit ω).1) j.val) =
      iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
        vectorPitmanCodeWalk ω j.val) :=
      map_phaseSplit_fst_comp ((measurable_pathPrefix n).comp
        measurable_vectorPitmanCodeWalk_local)
    rw [hmap]
    exact vectorPitmanCodeWalk_prefix_law n
  · have hmap : iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
        rPitmanCodeWalk ((phaseSplit ω).2) j.val) =
      iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
        rPitmanCodeWalk ω j.val) :=
      map_phaseSplit_snd_comp ((measurable_pathPrefix n).comp
        measurable_rPitmanCodeWalk_local)
    rw [hmap]
    exact rPitmanCodeWalk_prefix_law n

end DirectedDistances.RandomWalk
