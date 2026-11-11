/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedLimitPathLaw2
public import DirectedDistances.RandomWalk.IIDWalkInterpolationMoments3
public import DirectedDistances.RandomWalk.IIDWalkFDDConvergence
public import DirectedDistances.Probability.MomentTightnessContinuous2
import Mathlib.Data.Finset.Sort

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open DirectedDistances.Probability
open scoped Topology NNReal ENNReal

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the entire interpolated iid walk is a Borel
measurable random continuous path, for every index including zero. -/
theorem measurable_codeWalk_diffusiveInterpolation_path (n : ℕ) :
    Measurable (fun ω => diffusiveInterpolation n (codeWalk ω)) := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ℝ≥0
  let : Countable D := hDc.to_subtype
  let ev : C(ℝ≥0, ℝ × ℝ) → D → ℝ × ℝ := fun f t => f t
  have hevc : Continuous ev := continuous_pi (fun t => continuous_eval_const t.val)
  have hev : MeasurableEmbedding ev := hevc.measurableEmbedding (by
    intro f g h
    apply DFunLike.ext'
    apply f.continuous.ext_on hDd g.continuous
    intro t ht
    exact congrFun h ⟨t, ht⟩)
  apply hev.measurable_comp_iff.mp
  exact Measurable.of_eval (fun t => measurable_codeWalk_diffusiveInterpolation n t.val)

/-- Helper toward Lemma 4.11: the interpolated iid walk starts at zero,
including the degenerate scaling index zero. -/
theorem codeWalk_diffusiveInterpolation_zero (n : ℕ) (ω : ℕ → Fin 3) :
    diffusiveInterpolation n (codeWalk ω) 0 = 0 := by
  rw [(diffusiveStep_interpolation_zero n (codeWalk ω)).2, codeWalk_zero]
  simp only [Int.cast_zero, zero_div, Prod.zero_eq_mk]

/-- Helper toward Lemma 4.11: compact restriction of the iid random path
is measurable in the same Borel structure as the path assembly criterion. -/
theorem measurable_codeWalk_compactPathRestriction (n : ℕ) (T : ℝ≥0) :
    Measurable (fun ω => compactPathRestriction T
      (diffusiveInterpolation n (codeWalk ω))) :=
  (continuous_compactPathRestriction T).measurable.comp
    (measurable_codeWalk_diffusiveInterpolation_path n)

/-- Helper toward Lemma 4.11: the laws of the iid polygonal walk restricted
to each compact initial time interval are tight, with index zero included. -/
theorem isTightMeasureSet_codeWalk_compactPathRestriction (T : ℝ≥0) :
    IsTightMeasureSet (range (fun n => Measure.map
      (fun ω => compactPathRestriction T (diffusiveInterpolation n (codeWalk ω)))
      iidCodeMeasure)) := by
  obtain ⟨C, hC, hm⟩ := iidCodeWalk_diffusiveInterpolation_fourth_moment_bound
  apply isTightMeasureSet_restrict_of_norm_fourth_moment iidCodeMeasure
    (fun n ω => diffusiveInterpolation n (codeWalk ω)) C hC.le T
    codeWalk_diffusiveInterpolation_zero
  · intro n s t
    by_cases hn : n = 0
    · subst n
      simpa only [diffusiveInterpolation, ContinuousMap.coe_mk, Nat.cast_zero,
        Real.sqrt_zero, div_zero, Prod.mk_zero_zero, sub_self, norm_zero,
        zero_pow (by decide : 4 ≠ 0)] using (integrable_const (0 : ℝ))
    · rcases le_total s t with hst | hts
      · exact (hm n (by omega) s t hst).1
      · simpa only [norm_sub_rev] using (hm n (by omega) t s hts).1
  · intro n s t hst
    by_cases hn : n = 0
    · subst n
      simp only [diffusiveInterpolation, ContinuousMap.coe_mk, Nat.cast_zero,
        Real.sqrt_zero, div_zero, Prod.mk_zero_zero, sub_self, norm_zero,
        zero_pow (by decide : 4 ≠ 0), integral_zero]
      exact mul_nonneg hC.le (sq_nonneg _)
    · exact (hm n (by omega) s t hst).2
  · intro n
    exact measurable_codeWalk_compactPathRestriction n T

/-- Helper toward Lemma 4.11: partial sums of a finite tuple of planar
increments depend continuously on that tuple. -/
theorem continuous_planar_partialSum {k : ℕ} :
    Continuous (Fin.partialSum : (Fin k → ℝ × ℝ) → Fin (k + 1) → ℝ × ℝ) := by
  apply continuous_pi
  intro j
  induction j using Fin.inductionOn with
  | zero => simpa only [Fin.partialSum_zero] using
      (continuous_const : Continuous (fun _ : Fin k → ℝ × ℝ => (0 : ℝ × ℝ)))
  | succ j ih =>
      simp only [Fin.partialSum_succ]
      exact continuous_add.comp (ih.prodMk (continuous_apply j))

/-- Helper toward Lemma 4.11: at ordered times starting at zero, the
polygonal iid walk converges jointly to partial sums of independent, correctly
scaled planar Gaussian increments. -/
theorem codeWalk_interpolation_ordered_evaluations_clt {k : ℕ}
    (t : Fin (k + 1) → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => diffusiveInterpolation n (codeWalk ω) (t i)) atTop
      (fun z : Fin k → ℝ × ℝ => Fin.partialSum (fun i =>
        Real.sqrt ((t i.succ : ℝ) - t i.castSucc) •
          ((z i).1, ((z i).2 - (z i).1) / 2)))
      (fun _ : ℕ => iidCodeMeasure)
      (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  have h := (codeWalk_interpolation_consecutive_blocks_clt t ht).continuous_comp
    continuous_planar_partialSum
  refine h.congr (fun n => ae_of_all _ (fun ω => ?_)) (ae_of_all _ (fun _ => rfl))
  funext j
  dsimp only [Function.comp_apply]
  induction j using Fin.inductionOn with
  | zero => rw [Fin.partialSum_zero, ht0, codeWalk_diffusiveInterpolation_zero]
  | succ j ih =>
      rw [Fin.partialSum_succ, ih]
      abel

/-- Helper toward Lemma 4.11: every finite family of nonnegative times
is obtained by selecting, possibly repeatedly, from a strictly ordered grid
whose first time is zero. -/
theorem exists_ordered_time_refinement {k : ℕ} (t : Fin k → ℝ≥0) :
    ∃ (m : ℕ) (u : Fin (m + 1) → ℝ≥0) (r : Fin k → Fin (m + 1)),
      StrictMono u ∧ u 0 = 0 ∧ ∀ i, u (r i) = t i := by
  classical
  let S : Finset ℝ≥0 := insert 0 (Finset.univ.image t)
  have hz : 0 ∈ S := Finset.mem_insert_self _ _
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, hz⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let e : Fin (m + 1) ≃o S := S.orderIsoOfFin hm
  let u : Fin (m + 1) → ℝ≥0 := fun j => (e j).val
  have hti (i : Fin k) : t i ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let r : Fin k → Fin (m + 1) := fun i => e.symm ⟨t i, hti i⟩
  refine ⟨m, u, r, ?_, ?_, ?_⟩
  · exact e.strictMono
  · have hle : u 0 ≤ 0 := by
      have he0 := e.monotone (show (0 : Fin (m + 1)) ≤ e.symm ⟨0, hz⟩ from bot_le)
      rw [e.apply_symm_apply] at he0
      exact he0
    exact le_antisymm hle bot_le
  · intro i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨t i, hti i⟩)

/-- Helper toward Lemma 4.11: arbitrary finite evaluations of the iid
polygonal walk converge to a selected partial-sum Gaussian law. The grid
selection retains repeated times and time zero. -/
theorem codeWalk_interpolation_evaluations_clt {k : ℕ} (t : Fin k → ℝ≥0) :
    ∃ (m : ℕ) (u : Fin (m + 1) → ℝ≥0) (r : Fin k → Fin (m + 1)),
      StrictMono u ∧ u 0 = 0 ∧ (∀ i, u (r i) = t i) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω i => diffusiveInterpolation n (codeWalk ω) (t i)) atTop
        (fun z : Fin m → ℝ × ℝ => fun j => Fin.partialSum (fun i =>
          Real.sqrt ((u i.succ : ℝ) - u i.castSucc) •
            ((z i).1, ((z i).2 - (z i).1) / 2)) (r j))
        (fun _ : ℕ => iidCodeMeasure)
        (Measure.pi (fun _ : Fin m => iidEndpointLimitLaw)) := by
  obtain ⟨m, u, r, hu, hu0, hr⟩ := exists_ordered_time_refinement t
  refine ⟨m, u, r, hu, hu0, hr, ?_⟩
  have h := (codeWalk_interpolation_ordered_evaluations_clt u hu hu0).continuous_comp
    (g := fun v : Fin (m + 1) → ℝ × ℝ => fun j => v (r j))
    (continuous_pi (fun j => continuous_apply (r j)))
  simpa only [Function.comp_def, hr] using h

/-- Helper toward Lemma 4.11: one Brownian coordinate has the full product
law of its scaled consecutive increments, including zero-length increments. -/
theorem hasLaw_brownian_coordinate_increment_array {k : ℕ}
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (j : Fin 4) (c : ℝ) (u : Fin (k + 1) → ℝ≥0) (hu : Monotone u) :
    HasLaw (fun p i => c * (p (u i.succ) j - p (u i.castSucc) j))
      (Measure.pi (fun i : Fin k => gaussianReal 0
        (NNReal.mk (c ^ 2) (sq_nonneg _) *
          nndist (u i.succ : ℝ) (u i.castSucc : ℝ)))) W₄ := by
  have hi := (hB j).hasIndepIncrements k u hu
  have hs := hi.comp (fun (_ : Fin k) (x : ℝ) => c * x)
    (fun _ => (measurable_const.mul measurable_id : Measurable (fun x : ℝ => c * x)))
  apply hs.hasLaw_pi
  intro i
  have hl := gaussianReal_const_mul ((hB j).hasLaw_sub (u i.succ) (u i.castSucc)) c
  simp only [mul_zero] at hl
  apply hl.congr
  exact ae_of_all _ (fun p => by simp only [Function.comp_def, Pi.sub_apply])

/-- Helper toward Lemma 4.11: two independent Brownian coordinate paths
give the product law of the entire array of planar diagonal increments. -/
theorem hasLaw_brownian_pair_increment_array {k : ℕ}
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (hI : iIndepFun (fun j (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p j) W₄)
    (c d : ℝ) (u : Fin (k + 1) → ℝ≥0) (hu : Monotone u) :
    HasLaw (fun p i => (c * (p (u i.succ) 0 - p (u i.castSucc) 0),
        d * (p (u i.succ) 3 - p (u i.castSucc) 3)))
      (Measure.pi (fun i : Fin k =>
        (gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg _) *
          nndist (u i.succ : ℝ) (u i.castSucc : ℝ))).prod
        (gaussianReal 0 (NNReal.mk (d ^ 2) (sq_nonneg _) *
          nndist (u i.succ : ℝ) (u i.castSucc : ℝ))))) W₄ := by
  let μ (i : Fin k) := gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg _) *
    nndist (u i.succ : ℝ) (u i.castSucc : ℝ))
  let ν (i : Fin k) := gaussianReal 0 (NNReal.mk (d ^ 2) (sq_nonneg _) *
    nndist (u i.succ : ℝ) (u i.castSucc : ℝ))
  have hi := (hI.indepFun (show (0 : Fin 4) ≠ 3 by decide)).comp
    (show Measurable (fun f : C(ℝ≥0, ℝ) => fun i : Fin k =>
      c * (f (u i.succ) - f (u i.castSucc))) from
      (continuous_pi (fun i => continuous_const.mul
        ((continuous_eval_const _).sub (continuous_eval_const _)))).measurable)
    (show Measurable (fun f : C(ℝ≥0, ℝ) => fun i : Fin k =>
      d * (f (u i.succ) - f (u i.castSucc))) from
      (continuous_pi (fun i => continuous_const.mul
        ((continuous_eval_const _).sub (continuous_eval_const _)))).measurable)
  have hp := hi.hasLaw_prod
    (hasLaw_brownian_coordinate_increment_array W₄ hB 0 c u hu)
    (hasLaw_brownian_coordinate_increment_array W₄ hB 3 d u hu)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)
  have he : MeasurePreserving e.symm ((Measure.pi μ).prod (Measure.pi ν))
      (Measure.pi (fun i => (μ i).prod (ν i))) :=
    MeasurePreserving.symm e (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k) μ ν)
  exact he.hasLaw.comp hp

private theorem hasLaw_gaussianReal_sqrt_duration (v : ℝ≥0) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun x : ℝ => Real.sqrt ((t : ℝ) - s) * x)
      (gaussianReal 0 (v * nndist (t : ℝ) (s : ℝ))) (gaussianReal 0 v) := by
  have hid : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) (gaussianReal 0 v) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have h := gaussianReal_const_mul hid (Real.sqrt ((t : ℝ) - s))
  have hnon : 0 ≤ (t : ℝ) - s := sub_nonneg.mpr (by exact_mod_cast hst)
  have hv : NNReal.mk (Real.sqrt ((t : ℝ) - s) ^ 2) (sq_nonneg _) * v =
      v * nndist (t : ℝ) (s : ℝ) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nndist, Real.dist_eq,
      abs_of_nonneg hnon, Real.sq_sqrt hnon]
    exact mul_comm _ _
  simpa only [mul_zero, hv, id_eq] using h

/-- Helper toward Lemma 4.11: the product endpoint Gaussian law has the
correct scaled product law on an entire array of consecutive increments. -/
theorem hasLaw_iidEndpoint_scaled_array {k : ℕ}
    (u : Fin (k + 1) → ℝ≥0) (hu : Monotone u) :
    HasLaw (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((u i.succ : ℝ) - u i.castSucc) • z i)
      (Measure.pi (fun i : Fin k =>
        (gaussianReal 0 ((2 / 3 : ℝ≥0) *
          nndist (u i.succ : ℝ) (u i.castSucc : ℝ))).prod
        (gaussianReal 0 ((2 : ℝ≥0) *
          nndist (u i.succ : ℝ) (u i.castSucc : ℝ)))))
      (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  have hi : iIndepFun (fun i (z : Fin k → ℝ × ℝ) =>
      Real.sqrt ((u i.succ : ℝ) - u i.castSucc) • z i)
      (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) :=
    iIndepFun_pi (fun i => (show Continuous (fun z : ℝ × ℝ =>
      Real.sqrt ((u i.succ : ℝ) - u i.castSucc) • z) from by fun_prop).measurable.aemeasurable)
  apply hi.hasLaw_pi
  intro i
  have hf : HasLaw Prod.fst (gaussianReal 0 (2 / 3 : ℝ≥0)) iidEndpointLimitLaw :=
    ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩
  have hg : HasLaw Prod.snd (gaussianReal 0 (2 : ℝ≥0)) iidEndpointLimitLaw :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have hf' := (hasLaw_gaussianReal_sqrt_duration (2 / 3) (u i.castSucc) (u i.succ)
    (hu i.castSucc_le_succ)).comp hf
  have hg' := (hasLaw_gaussianReal_sqrt_duration 2 (u i.castSucc) (u i.succ)
    (hu i.castSucc_le_succ)).comp hg
  have hi' : IndepFun
      (fun z : ℝ × ℝ => Real.sqrt ((u i.succ : ℝ) - u i.castSucc) * z.1)
      (fun z : ℝ × ℝ => Real.sqrt ((u i.succ : ℝ) - u i.castSucc) * z.2)
      iidEndpointLimitLaw := indepFun_prod (by fun_prop) (by fun_prop)
  have hp := hi'.hasLaw_prod hf' hg'
  have he := (measurePreserving_eval (fun _ : Fin k => iidEndpointLimitLaw) i).hasLaw
  exact hp.comp he

/-- Helper toward Lemma 4.11: the Brownian candidate's joint consecutive
increment law is the same scaled inverse-diagonal product Gaussian law as
the iid walk CLT. -/
theorem identDistrib_iidBrownianPath_increments {k : ℕ}
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (hI : iIndepFun (fun j (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p j) W₄)
    (u : Fin (k + 1) → ℝ≥0) (hu : Monotone u) :
    IdentDistrib
      (fun p i => iidBrownianPath p (u i.succ) - iidBrownianPath p (u i.castSucc))
      (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((u i.succ : ℝ) - u i.castSucc) •
          ((z i).1, ((z i).2 - (z i).1) / 2))
      W₄ (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  have hc : NNReal.mk (Real.sqrt (2 / 3 : ℝ) ^ 2) (sq_nonneg _) = (2 / 3 : ℝ≥0) := by
    apply NNReal.coe_injective
    change Real.sqrt (2 / 3 : ℝ) ^ 2 = (2 / 3 : ℝ≥0)
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hd : NNReal.mk (Real.sqrt (2 : ℝ) ^ 2) (sq_nonneg _) = (2 : ℝ≥0) := by
    apply NNReal.coe_injective
    norm_num [Real.sq_sqrt]
  have hb := hasLaw_brownian_pair_increment_array W₄ hB hI
    (Real.sqrt (2 / 3)) (Real.sqrt 2) u hu
  rw [hc, hd] at hb
  have h := (hb.identDistrib (hasLaw_iidEndpoint_scaled_array u hu)).comp
    (u := fun v : Fin k → ℝ × ℝ => fun i => ((v i).1, ((v i).2 - (v i).1) / 2))
    (by fun_prop)
  have hs : Real.sqrt (2 / 3 : ℝ) * Real.sqrt 3 = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    norm_num
  convert h using 1
  · funext p i
    ext <;> simp only [Function.comp_def, iidBrownianPath, brownianMix,
      pathCoordinate, ContinuousMap.coe_mk, Prod.fst_sub, Prod.snd_sub]
    · ring
    · rw [← hs]
      ring
  · funext z i
    ext <;> dsimp; all_goals ring

/-- Helper toward Lemma 4.11: the candidate Brownian path starts at zero
almost surely under the stated coordinate Brownian laws. -/
theorem iidBrownianPath_zero_ae
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄) :
    ∀ᵐ p ∂W₄, iidBrownianPath p 0 = 0 := by
  filter_upwards [(hB 0).eval_zero_ae_eq_zero, (hB 3).eval_zero_ae_eq_zero] with p hp hq
  simp only [iidBrownianPath, brownianMix, pathCoordinate, ContinuousMap.coe_mk,
    hp, hq, mul_zero, zero_div, sub_self, Prod.zero_eq_mk]

/-- Helper toward Lemma 4.11: the entire joint evaluation law on a grid
starting at zero equals the partial-sum image of the product endpoint laws. -/
theorem identDistrib_iidBrownianPath_ordered_evaluations {k : ℕ}
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (hI : iIndepFun (fun j (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p j) W₄)
    (u : Fin (k + 1) → ℝ≥0) (hu : Monotone u) (hu0 : u 0 = 0) :
    IdentDistrib (fun p i => iidBrownianPath p (u i))
      (fun z : Fin k → ℝ × ℝ => Fin.partialSum (fun i =>
        Real.sqrt ((u i.succ : ℝ) - u i.castSucc) •
          ((z i).1, ((z i).2 - (z i).1) / 2)))
      W₄ (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  have h := (identDistrib_iidBrownianPath_increments W₄ hB hI u hu).comp
    continuous_planar_partialSum.measurable
  have heq : (fun p => Fin.partialSum (fun i : Fin k =>
      iidBrownianPath p (u i.succ) - iidBrownianPath p (u i.castSucc))) =ᵐ[W₄]
      (fun p i => iidBrownianPath p (u i)) := by
    filter_upwards [iidBrownianPath_zero_ae W₄ hB] with p hp
    funext j
    induction j using Fin.inductionOn with
    | zero => rw [Fin.partialSum_zero, hu0, hp]
    | succ j ih => rw [Fin.partialSum_succ, ih]; abel
  exact (IdentDistrib.of_ae_eq h.aemeasurable_fst heq).symm.trans h

/-- Helper toward Lemma 4.11: all finite evaluations of the iid
polygonal walk converge jointly to the specified Brownian candidate, with
arbitrary ordering, repetitions and zero observation times. -/
theorem codeWalk_interpolation_fdd_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (hI : iIndepFun (fun j (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p j) W₄)
    (k : ℕ) (t : Fin k → ℝ≥0) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => diffusiveInterpolation n (codeWalk ω) (t i)) atTop
      (fun p i => iidBrownianPath p (t i)) (fun _ => iidCodeMeasure) W₄ := by
  obtain ⟨m, u, r, hu, hu0, hr, hw⟩ := codeWalk_interpolation_evaluations_clt t
  have hb := (identDistrib_iidBrownianPath_ordered_evaluations W₄ hB hI u hu.monotone hu0).comp
    (u := fun v : Fin (m + 1) → ℝ × ℝ => fun j => v (r j))
    (continuous_pi (fun j => continuous_apply (r j))).measurable
  simp only [Function.comp_def, hr] at hb
  refine ⟨hw.forall_aemeasurable, hb.aemeasurable_fst, ?_⟩
  convert hw.tendsto using 1
  exact congrArg nhds (ProbabilityMeasure.toMeasure_injective hb.map_eq)

/-- Helper toward Lemma 4.11: the iid polygonal code walk converges in
distribution in the locally uniform continuous-path topology to the exact
covariance-normalized Brownian candidate under any independent four-coordinate
Brownian path law. This closes open item 1 of `ConditionedLimitPathLaw2`;
it does not assert the conditioned invariance principle. -/
theorem codeWalk_interpolation_functional_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ j : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t j) W₄)
    (hI : iIndepFun (fun j (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p j) W₄) :
    TendstoInDistribution (fun n ω => diffusiveInterpolation n (codeWalk ω)) atTop
      iidBrownianPath (fun _ => iidCodeMeasure) W₄ := by
  let μ : ℕ → ProbabilityMeasure C(ℝ≥0, ℝ × ℝ) := fun n =>
    ⟨iidCodeMeasure.map (fun ω => diffusiveInterpolation n (codeWalk ω)), inferInstance⟩
  let ν : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ) :=
    ⟨W₄.map iidBrownianPath, inferInstance⟩
  refine ⟨fun n => (measurable_codeWalk_diffusiveInterpolation_path n).aemeasurable,
    continuous_iidBrownianPath.measurable.aemeasurable, ?_⟩
  change Tendsto μ atTop (𝓝 ν)
  apply continuousPath_tendsto_of_compact_tight_of_fdd μ ν
  · intro T
    have he (n : ℕ) : (((μ n).map (compactPathRestriction T)) :
        Measure C(Icc (0 : ℝ≥0) T, ℝ × ℝ)) =
        iidCodeMeasure.map (fun ω => compactPathRestriction T
          (diffusiveInterpolation n (codeWalk ω))) := by
      exact Measure.map_map (continuous_compactPathRestriction T).measurable
        (measurable_codeWalk_diffusiveInterpolation_path n)
    simp only [he]
    exact isTightMeasureSet_codeWalk_compactPathRestriction T
  · intro k t
    have he (n : ℕ) : (μ n).map (fun f i => f (t i)) =
        (⟨iidCodeMeasure.map (fun ω i => diffusiveInterpolation n (codeWalk ω) (t i)),
          inferInstance⟩ : ProbabilityMeasure (Fin k → ℝ × ℝ)) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_map (continuous_pi (fun i => continuous_eval_const (t i))).measurable
        (measurable_codeWalk_diffusiveInterpolation_path n)
    have he' : ν.map (fun f i => f (t i)) =
        (⟨W₄.map (fun p i => iidBrownianPath p (t i)), inferInstance⟩ :
          ProbabilityMeasure (Fin k → ℝ × ℝ)) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_map (continuous_pi (fun i => continuous_eval_const (t i))).measurable
        continuous_iidBrownianPath.measurable
    simp only [he, he']
    exact (codeWalk_interpolation_fdd_tendsto W₄ hB hI k t).tendsto

end DirectedDistances.RandomWalk
