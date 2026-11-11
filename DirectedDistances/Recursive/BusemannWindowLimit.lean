module

public import DirectedDistances.Recursive.BusemannFddStable
public import DirectedDistances.Probability.ScaledWindowModulusGtOne
public import DirectedDistances.Probability.SkorokhodJ1WindowConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

private theorem sum_increments {Ω : Type*} (Y : Ω → ℤ → ℤ)
    (h0 : ∀ ω, Y ω 0 = 0) (r : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range r,
      ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)) = (Y ω (r : ℤ) : ℝ) := by
  induction r with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, h0,
      Int.cast_zero]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Int.cast_sub, Nat.cast_succ]
    ring

private theorem normalized_remainder {F : ℝ → ℝ} {C ν : ℝ}
    (h : (fun x => F x - C * x ^ (-ν)) =o[atTop] (fun x => x ^ (-ν))) :
    Tendsto (fun x => x ^ ν * F x) atTop (𝓝 C) := by
  have ht := h.tendsto_div_nhds_zero.add_const C
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hx _).ne',
    sub_add_cancel, Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm]

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannLDPMeasurableVersion



@[expose] noncomputable def ldpBusemannWindow (n : ℕ) {T : ℝ} (hT : 0 < T) :=
  scaledPartialSumWindow (fun j ω =>
    ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)) (2 / 3) n hT



theorem ldpBusemannWindow_apply (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) :
    (ldpBusemannWindow n hT ω).path.1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (Y ω ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ : ℝ) := by
  rw [ldpBusemannWindow, scaledPartialSumWindow_apply]
  rw [← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1)]
  have hnat (k : ℕ) : partialSumZ (fun j ω =>
      ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)) ω (k : ℤ) =
      (Y ω (k : ℤ) : ℝ) := by
    cases k with
    | zero => simp [partialSumZ, busemannLDPMeasurableVersion_zero]
    | succ k =>
      simp only [partialSumZ, Nat.cast_pos, Nat.succ_pos, ↓reduceIte, Int.toNat_natCast]
      exact sum_increments Y busemannLDPMeasurableVersion_zero _ ω
  rw [hnat]
  norm_num

private theorem ldp_increment_measurable (j : ℤ) : Measurable (ldpIncrement Y j) :=
  (measurable_busemannLDPMeasurableVersion j).sub
    (measurable_busemannLDPMeasurableVersion (j - 1))

private theorem ldp_positive_powerTail
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      iidCodeMeasure.real {ω | x < |(ldpIncrement Y 1 ω : ℝ)|} ≤ C * x ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨_, hminus, _⟩ := busemann_tail_ldp_strict_of_items hind
    busemannLDPMeasurableVersion_right_stationary
    busemannLDPMeasurableVersion_left_stationary hsym
  have hm := normalized_remainder hminus
  have heq : (fun x : ℝ => x ^ (2 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < -(ldpIncrement Y 1 ω : ℝ)}) =
      (fun x : ℝ => x ^ (2 / 3 : ℝ) *
        iidCodeMeasure.real {ω | ((Y ω 1 - Y ω 0 : ℤ) : ℝ) < -x}) := by
    funext x
    congr 2
    ext ω
    change (x < -((Y ω 1 - Y ω 0 : ℤ) : ℝ)) ↔
      (((Y ω 1 - Y ω 0 : ℤ) : ℝ) < -x)
    constructor <;> intro h <;> linarith only [h]
  rw [← heq] at hm
  have hplus : Tendsto (fun x : ℝ => x ^ (2 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < (ldpIncrement Y 1 ω : ℝ)}) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have he : μ {ω | x < (ldpIncrement Y 1 ω : ℝ)} = 0 := by
      have hn : ∀ᵐ ω ∂μ, ¬x < (ldpIncrement Y 1 ω : ℝ) := by
        filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_item_pos] with ω hω
        have hb : (ldpIncrement Y 1 ω : ℝ) ≤ -1 := by
          exact_mod_cast hω 1 le_rfl
        linarith only [hx, hb]
      simpa only [ae_iff, not_not] using hn
    simp only [measureReal_def, he, ENNReal.toReal_zero, mul_zero]
  exact exists_powerTailBound
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (ldp_increment_measurable 1)) (by norm_num : (0 : ℝ) < 2 / 3)
    hplus hm



theorem ldp_busemann_window_isTight
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    IsTightMeasureSet (Set.range fun n : ℕ => iidCodeMeasure.map (ldpBusemannWindow n hT)) := by
  let X : ℕ → (ℕ → Fin 3) → ℝ := fun j ω =>
    ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)
  have hc : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hX (j : ℕ) : Measurable (X j) :=
    hc.comp ((measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _))
  have hi : iIndepFun X μ := by
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + 1) := by
      intro a b hab
      exact_mod_cast (add_right_cancel hab)
    have hh := (iIndepFun.precomp hinj hind).comp (fun _ => fun z : ℤ => (z : ℝ))
      (fun _ => hc)
    simpa only [X, ldpIncrement, Function.comp_def, add_sub_cancel_right] using hh
  have hid (j : ℕ) : IdentDistrib (X j) (X 0) μ μ := by
    have hh : IdentDistrib (ldpIncrement Y ((j : ℤ) + 1)) (ldpIncrement Y 1) μ μ :=
      ⟨(ldp_increment_measurable _).aemeasurable,
        (ldp_increment_measurable _).aemeasurable,
        busemannLDPMeasurableVersion_right_stationary _ (by omega)⟩
    simpa only [X, ldpIncrement, Function.comp_def, add_sub_cancel_right, Nat.cast_zero,
      zero_add, sub_self] using hh.comp hc
  obtain ⟨C, hC, htail⟩ := ldp_positive_powerTail hind hsym
  exact scaledPartialSumWindow_isTight_lt_one' μ X hX hi hid
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num) hC htail hT




@[expose] noncomputable def ldpBusemannWindowLaw (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ProbabilityMeasure (J1WindowD T hT) :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (ldpBusemannWindow n hT)

private theorem measurable_ldpBusemannWindow (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Measurable (ldpBusemannWindow n hT) := by
  apply measurable_scaledPartialSumWindow
  intro j
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _))

private theorem pm_map_map {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : ProbabilityMeasure A) {f : A → B} {g : B → C}
    (hf : Measurable f) (hg : Measurable g) :
    (P.map f).map g = P.map (g ∘ f) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_map hg hf




theorem ldp_busemann_window_fdd
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    let a : ℝ := ((3 + ldpF μ Y 0) / 2) ^ (1 / 3 : ℝ)
    let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
    0 < a ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      Tendsto (fun n => (ldpBusemannWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1)))) atTop
        (𝓝 ((L.map (cumulativeSum (k := m))).map WithLp.ofLp)) := by
  dsimp only
  obtain ⟨ha, L, hchar, hlim⟩ := ldp_busemann_fdd_of_ind_sym hind hsym
    (m := m) (t := fun j => (t j : ℝ)) ht0 (fun i j hij => ht hij)
  refine ⟨ha, L, hchar, ?_⟩
  have hv := hlim.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))
  have hn := hv.tendsto.comp (tendsto_add_atTop_nat 1)
  have heval (n : ℕ) :
      (ldpBusemannWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
      ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (fun ω => fun i : Fin m => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
          (Y ω ⌊((n + 1 : ℕ) : ℝ) * (t (i.val + 1) : ℝ)⌋ : ℝ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (iidCodeMeasure.map (ldpBusemannWindow n hT)).map
      (windowEvalVec (fun i : Fin m => t (i.val + 1))) = _
    rw [Measure.map_map (measurable_windowEvalVec _) (measurable_ldpBusemannWindow n hT)]
    congr 1
    funext ω i
    exact ldpBusemannWindow_apply n hT ω _
  simp_rw [heval]
  convert hn using 1
  · funext n
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  · congr 1

private theorem ldp_window_eval_limit_exists
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) (k : ℕ) (t : Fin k → J1Window T) :
    ∃ L : ProbabilityMeasure (Fin k → ℝ),
      Tendsto (fun n => (ldpBusemannWindowLaw n hT).map (windowEvalVec t)) atTop
        (𝓝 L) := by
  classical
  let z : J1Window T := ⟨0, le_rfl, hT.le⟩
  let s : Finset (J1Window T) := insert z (Finset.univ.image t)
  have hs : 0 < s.card := Finset.card_pos.mpr ⟨z, Finset.mem_insert_self _ _⟩
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  let q : ℕ → J1Window T := fun j => if j = 0 then z else
    (e ⟨min (j - 1) (s.card - 1), by omega⟩).val
  have hq0 : (q 0 : ℝ) = 0 := by simp only [q, ↓reduceIte, z]
  have hqmono : Monotone q := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      change (q 0 : ℝ) ≤ (q j : ℝ)
      rw [hq0]
      exact (q j).property.1
    · have hj : j ≠ 0 := by omega
      simp only [q, hi, hj, ite_false]
      exact e.monotone (show (⟨min (i - 1) (s.card - 1), by omega⟩ : Fin s.card) ≤
        ⟨min (j - 1) (s.card - 1), by omega⟩ from by
          change min (i - 1) (s.card - 1) ≤ min (j - 1) (s.card - 1)
          omega)
  have hq (j : Fin s.card) : q (j.val + 1) = (e j).val := by
    have hj : j.val + 1 ≠ 0 := by omega
    simp only [q, hj, ite_false]
    congr 2
    apply Fin.ext
    have := j.isLt
    simp only [Nat.add_sub_cancel]
    omega
  let r : Fin k → Fin s.card := fun i => e.symm ⟨t i,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  have hr (i : Fin k) : q ((r i).val + 1) = t i := by
    rw [hq]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨_, L, _, hL⟩ := ldp_busemann_window_fdd hind hsym hT (m := s.card) hq0 hqmono
  let p : (Fin s.card → ℝ) → Fin k → ℝ := fun v i => v (r i)
  have hp : Continuous p := continuous_pi fun i => continuous_apply (r i)
  refine ⟨((L.map cumulativeSum).map WithLp.ofLp).map p, ?_⟩
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hL hp
  have heq (n : ℕ) :
      ((ldpBusemannWindowLaw n hT).map
        (windowEvalVec (fun i : Fin s.card => q (i.val + 1)))).map p =
      (ldpBusemannWindowLaw n hT).map (windowEvalVec t) := by
    rw [pm_map_map _ (measurable_windowEvalVec _) hp.measurable]
    congr 1
    funext x i
    change x.path.1 (q ((r i).val + 1)) = x.path.1 (t i)
    rw [hr]
  simpa only [heq] using hh



private theorem ldp_window_tendsto_exists
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => ldpBusemannWindowLaw n hT) atTop (𝓝 ν) := by
  classical
  let W : ℕ → ProbabilityMeasure (J1WindowD T hT) := fun n => ldpBusemannWindowLaw n hT
  have htight := ldp_busemann_window_isTight hind hsym hT
  have htight' : IsTightMeasureSet
      {((p : ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT)) |
        p ∈ Set.range W} := by
    convert htight using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨W n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, _, φ, hφ, hν⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight').tendsto_subseq
      (x := W) (fun n => subset_closure ⟨n, rfl⟩)
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let S : Set (J1Window T) := insert endpoint (continuityTimes (ν : Measure (J1WindowD T hT)))
  have hS : Sᶜ.Countable :=
    (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT))).mono
      (Set.compl_subset_compl.mpr (Set.subset_insert _ _))
  refine ⟨ν, tendsto_of_tight_of_fdd W ν htight S hS (Set.mem_insert _ _) ?_⟩
  intro k t
  obtain ⟨L, hL⟩ := ldp_window_eval_limit_exists hind hsym hT k (fun i => (t i).val)
  have hcont (i : Fin k) (hi : ((t i).val : ℝ) < T) :
      (t i).val ∈ continuityTimes (ν : Measure (J1WindowD T hT)) := by
    rcases (t i).property with he | hc
    · have he' : ((t i).val : ℝ) = T := congrArg Subtype.val he
      exact False.elim ((ne_of_lt hi) he')
    · exact hc
  have heq : ν.map (windowEvalVec (fun i => (t i).val)) = L :=
    tendsto_nhds_unique (tendsto_map_windowEvalVec (W ∘ φ) ν hν _ hcont)
      (hL.comp hφ.tendsto_atTop)
  rw [heq]
  exact hL






theorem ldp_busemann_window_tendsto
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => ldpBusemannWindowLaw n hT) atTop (𝓝 ν) ∧
      ∃ S : Set (J1Window T), Sᶜ.Countable ∧
        (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S ∧
        ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
          (∀ i : Fin m, t (i.val + 1) ∈ S) →
          let a : ℝ := ((3 + ldpF μ Y 0) / 2) ^ (1 / 3 : ℝ)
          let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
          0 < a ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
            (∀ θ : EuclideanSpace ℝ (Fin m),
              charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
                (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                  ((if 0 ≤ θ i then κ else star κ) *
                    (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
            ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
              (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  obtain ⟨ν, hν⟩ := ldp_window_tendsto_exists hind hsym hT
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let S : Set (J1Window T) := insert endpoint (continuityTimes (ν : Measure (J1WindowD T hT)))
  have hS : Sᶜ.Countable :=
    (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT))).mono
      (Set.compl_subset_compl.mpr (Set.subset_insert _ _))
  refine ⟨ν, hν, S, hS, Set.mem_insert _ _, ?_⟩
  intro m t ht0 ht htS
  obtain ⟨ha, L, hchar, hL⟩ := ldp_busemann_window_fdd hind hsym hT ht0 ht
  refine ⟨ha, L, hchar, ?_⟩
  apply tendsto_nhds_unique _ hL
  apply tendsto_map_windowEvalVec _ ν hν
  intro i hi
  rcases htS i with he | hc
  · have he' : (t (i.val + 1) : ℝ) = T := congrArg Subtype.val he
    exact False.elim ((ne_of_lt hi) he')
  · exact hc

end DirectedDistances.Recursive
