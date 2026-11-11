module

public import DirectedDistances.RandomWalk.PitmanProcessLaw
public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange
import DirectedDistances.RandomWalk.ConditionedVectorFactorization

/-! # The two-dimensional Pitman flip

Geometry-free helpers for the unnumbered assertion in the proof of -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

 
@[expose] noncomputable def vectorPitman (z : ℕ → ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  (globalLazyPhi (fun k => (z k).1) n,
    (z n).2 + globalLazyRunningMinimum (fun k => (z k).1) n)

 
private theorem measurable_vectorPitman : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Uniform vector increments belong to the literal source set almost surely -/
private theorem ae_mem_vectorSteps {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : Ω → ℤ × ℤ} (hd : Measurable d)
    (hlaw : μ.map d =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    ∀ᵐ ω ∂μ, d ω ∈ ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
  have ha : ∀ᵐ z ∂Measure.uniformOfFinset
      ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ)),
      z ∈ ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
    rw [ae_iff, Measure.uniformOfFinset_apply]
    norm_num
  rw [← hlaw] at ha
  exact (ae_map_iff hd.aemeasurable ((Set.to_countable _).measurableSet)).mp ha

/-- The first marginal of the actual uniform vector-step law -/
private theorem map_uniform_vectorSteps_fst :
    (Measure.uniformOfFinset
      ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))).map Prod.fst =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
  have hmap (c : ℝ≥0∞) (z : ℤ × ℤ) :
      (c • Measure.dirac z).map Prod.fst = c • Measure.dirac z.1 := by
    rw [Measure.map_smul c measurable_fst.aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset]
  norm_num [Measure.map_add, measurable_fst, hmap]
  ac_rfl

/-- Projection retains the scalar iid source increments -/
private theorem vectorProcess_firstCoordinate_data {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℕ → ℤ × ℤ} (hZ : Measurable Z)
    (hind : iIndepFun (fun i ω => Z ω (i + 1) - Z ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    Measurable (fun ω k => (Z ω k).1) ∧
    iIndepFun (fun i ω => (Z ω (i + 1)).1 - (Z ω i).1) μ ∧
    (∀ i, μ.map (fun ω => (Z ω (i + 1)).1 - (Z ω i).1) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) := by
  refine ⟨by fun_prop, hind.comp (fun _ => Prod.fst) (fun _ => measurable_fst), ?_⟩
  intro i
  have hd : Measurable (fun ω => Z ω (i + 1) - Z ω i) := by fun_prop
  change μ.map (Prod.fst ∘ (fun ω => Z ω (i + 1) - Z ω i)) = _
  rw [← Measure.map_map measurable_fst hd, hlaw i, map_uniform_vectorSteps_fst]

/-- The prefix minimum recursion used by the flip -/
private theorem globalLazyRunningMinimum_succ (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p (n + 1) = min (globalLazyRunningMinimum p n) (p (n + 1)) := by
  have h := runningMinimum_succ (fun j : Fin (n + 1 + 1) => p j.val)
    (⟨n, by omega⟩ : Fin (n + 1))
  simpa only [runningMinimum_prefix_eq_global, Fin.val_succ, Fin.val_castSucc] using h

/-- Pathwise the literal flip retains exactly the three legal vector steps -/
private theorem vectorPitman_step {z : ℕ → ℤ × ℤ}
    (hs : ∀ i, z (i + 1) - z i ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ))) (n : ℕ) :
    vectorPitman z (n + 1) - vectorPitman z n ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
  have hm := globalLazyRunningMinimum_le (fun k => (z k).1) (i := n) le_rfl
  have h := hs n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h | h
  all_goals
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂
    simp only [vectorPitman, globalLazyPhi, globalLazyRunningMinimum_succ]
  · left
    apply Prod.ext <;> dsimp <;> rw [min_eq_left (by omega)] <;> omega
  · by_cases hh : globalLazyRunningMinimum (fun k => (z k).1) n ≤ (z (n + 1)).1
    · right; left
      apply Prod.ext <;> dsimp <;> rw [min_eq_left hh] <;> omega
    · left
      apply Prod.ext <;> dsimp <;> rw [min_eq_right (by omega)] <;> omega
  · right; right
    apply Prod.ext <;> dsimp <;> rw [min_eq_left (by omega)] <;> omega

/-- A scalar prefix is lifted by reading the uniquely determined step codes -/
private def vectorPrefixLift {n : ℕ} (p : Fin (n + 1) → ℤ) :
    Fin (n + 1) → ℤ × ℤ :=
  lazyTwoDimensionalPrefix 0 0 (fun i => lazyIntegerStepCode (p i.succ - p i.castSucc))

/-- On the actual source-word support the scalar projection loses no data -/
private theorem vectorPrefixLift_fst {n : ℕ} {q : Fin (n + 1) → ℤ × ℤ}
    (hq : q ∈ Set.range (@lazyTwoDimensionalPrefix n 0 0)) :
    vectorPrefixLift (fun j => (q j).1) = q := by
  obtain ⟨w, rfl⟩ := hq
  unfold vectorPrefixLift
  congr 1
  funext i
  have h := lazyTwoDimensionalPrefix_succ 0 0 w i
  have hf := congrArg Prod.fst h
  have hd : (lazyTwoDimensionalPrefix 0 0 w i.succ).1 -
      (lazyTwoDimensionalPrefix 0 0 w i.castSucc).1 = (w i : ℤ) - 1 := by
    simpa only [Prod.fst_add, lazyTwoDimensionalStep, add_sub_cancel_left] using
      congrArg (fun a : ℤ => a - (lazyTwoDimensionalPrefix 0 0 w i.castSucc).1) hf
  rw [hd]
  have hc (c : Fin 3) : lazyIntegerStepCode ((c : ℤ) - 1) = c := by
    fin_cases c <;> rfl
  exact hc (w i)

/-- Every legal zero-start vector prefix is recovered from its first coordinate -/
private theorem vectorPitman_prefix_lift {z : ℕ → ℤ × ℤ} (hz : z 0 = (0, 0))
    (hs : ∀ i, z (i + 1) - z i ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ))) (n : ℕ) :
    vectorPrefixLift (fun j : Fin (n + 1) => globalLazyPhi (fun k => (z k).1) j.val) =
      (fun j : Fin (n + 1) => vectorPitman z j.val) := by
  apply vectorPrefixLift_fst (n := n)
    (q := fun j : Fin (n + 1) => vectorPitman z j.val)
  apply (mem_range_lazyTwoDimensionalPrefix_iff 0 0 _).mpr
  constructor
  · simp [vectorPitman, hz]
  · intro i
    have h := vectorPitman_step hs i.val
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · refine ⟨2, ?_⟩
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · refine ⟨0, ?_⟩
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · refine ⟨1, ?_⟩
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- The simultaneous legal-step event follows from the actual increment laws -/
private theorem ae_vectorProcess_steps {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℕ → ℤ × ℤ} (hZ : Measurable Z)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    ∀ᵐ ω ∂μ, ∀ i, Z ω (i + 1) - Z ω i ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
  exact ae_all_iff.mpr (fun i => ae_mem_vectorSteps (by fun_prop) (hlaw i))

/-- The actual iid vector process has the uniform source-word prefix law -/
private theorem vectorProcess_prefix_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℕ → ℤ × ℤ}
    (hZ : Measurable Z) (hzero : ∀ᵐ ω ∂μ, Z ω 0 = (0, 0))
    (hind : iIndepFun (fun i ω => Z ω (i + 1) - Z ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) (n : ℕ) :
    μ.map (fun ω => fun j : Fin (n + 1) => Z ω j.val) =
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0) := by
  obtain ⟨hL, hiL, hlL⟩ := vectorProcess_firstCoordinate_data hZ hind hlaw
  obtain ⟨hc, hic, hlc⟩ := integerLazyProcess_code_law hL hiL hlL
  let ξ : ℕ → Ω → Fin 3 := fun i ω =>
    lazyIntegerStepCode ((Z ω (i + 1)).1 - (Z ω i).1)
  have he : (fun ω => fun j : Fin (n + 1) => Z ω j.val) =ᵐ[μ]
      (fun ω => lazyTwoDimensionalPrefix 0 0 (fun i : Fin n => ξ i.val ω)) := by
    filter_upwards [hzero, ae_vectorProcess_steps hZ hlaw] with ω hz hs
    funext j
    induction j using Fin.induction with
    | zero => exact hz.trans (lazyTwoDimensionalPrefix_zero 0 0 _).symm
    | succ i ih =>
      rw [lazyTwoDimensionalPrefix_succ, ← ih]
      have h := hs i.val
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      have hd : lazyTwoDimensionalStep (ξ i.val ω) = Z ω (i.val + 1) - Z ω i.val := by
        dsimp only [ξ]
        rcases h with h | h | h
        all_goals
          have hf := congrArg Prod.fst h
          simp only [Prod.fst_sub] at hf
          rw [hf, h]
          rfl
      rw [hd]
      simp only [Fin.val_succ, Fin.val_castSucc]
      abel
  rw [Measure.map_congr he]
  rw [show (fun ω => lazyTwoDimensionalPrefix 0 0 (fun i : Fin n => ξ i.val ω)) =
    lazyTwoDimensionalPrefix 0 0 ∘ (fun ω => fun i : Fin n => ξ i.val ω) from rfl,
    ← Measure.map_map (measurable_of_countable _) (Measurable.of_eval (fun i : Fin n => show Measurable (fun ω => ξ i.val ω) from hc i.val)),
    map_lazy_prefix_eq_uniform hc hic hlc n]

private theorem vectorPrefix_measure_eq {n : ℕ}
    (μ ν : Measure (Fin (n + 1) → ℤ × ℤ))
    (hμ : ∀ᵐ q ∂μ, vectorPrefixLift (fun j => (q j).1) = q)
    (hν : ∀ᵐ q ∂ν, vectorPrefixLift (fun j => (q j).1) = q)
    (he : μ.map (fun q => fun j => (q j).1) =
      ν.map (fun q => fun j => (q j).1)) : μ = ν := by
  have hrec (ρ : Measure (Fin (n + 1) → ℤ × ℤ))
      (hr : ∀ᵐ q ∂ρ, vectorPrefixLift (fun j => (q j).1) = q) :
      (ρ.map (fun q => fun j => (q j).1)).map vectorPrefixLift = ρ := by
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    exact (Measure.map_congr hr).trans (Measure.map_id)
  rw [← hrec μ hμ, he, hrec ν hν]

/-- The vector flip satisfies the exact all-horizon RN law -/
theorem vectorPitman_prefix_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℕ → ℤ × ℤ}
    (hZ : Measurable Z) (hzero : ∀ᵐ ω ∂μ, Z ω 0 = (0, 0))
    (hind : iIndepFun (fun i ω => Z ω (i + 1) - Z ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    ∀ n : ℕ,
      μ.map (fun ω => fun j : Fin (n + 1) => vectorPitman (Z ω) j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0) := by
  classical
  intro n
  let B : Measure (Fin (n + 1) → ℤ × ℤ) :=
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix 0 0)
  let d : (Fin (n + 1) → ℤ × ℤ) → ℝ≥0∞ := fun q =>
    if ∀ j, 0 ≤ (q j).1 then
      ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0
  change μ.map (fun ω => fun j : Fin (n + 1) => vectorPitman (Z ω) j.val) = B.withDensity d
  have hm : Measurable (fun ω => fun j : Fin (n + 1) => vectorPitman (Z ω) j.val) :=
    .of_eval (fun j => (measurable_pi_apply j.val).comp (measurable_vectorPitman.comp hZ))
  apply vectorPrefix_measure_eq
  · apply (ae_map_iff hm.aemeasurable ((Set.to_countable _).measurableSet)).mpr
    filter_upwards [hzero, ae_vectorProcess_steps hZ hlaw] with ω hz hs
    exact vectorPitman_prefix_lift hz hs n
  · have hs : ∀ᵐ q ∂B, q ∈ Set.range (@lazyTwoDimensionalPrefix n 0 0) :=
      ae_map_mem_range ((Set.to_countable _).measurableSet) (by fun_prop)
    have ht := (withDensity_absolutelyContinuous B d).ae_le hs
    filter_upwards [ht] with q hq
    exact vectorPrefixLift_fst hq
  · obtain ⟨hL, hiL, hlL⟩ := vectorProcess_firstCoordinate_data hZ hind hlaw
    have hz : ∀ᵐ ω ∂μ, (Z ω 0).1 = 0 := by
      filter_upwards [hzero] with ω hω
      exact congrArg Prod.fst hω
    have hp := pitman_process_prefix_law hL hz hiL hlL n
    have hb := vectorProcess_prefix_law hZ hzero hind hlaw n
    have hproj := firstCoordinate_of_twoDimensional_prefix_RN n 0 0 (B.withDensity d) (by simp only [Nat.cast_zero]; rfl)
    rw [Measure.map_map (measurable_of_countable _) hm]
    change μ.map (fun ω => fun j : Fin (n + 1) =>
      globalLazyPhi (fun k => (Z ω k).1) j.val) = _
    rw [hp, hproj]
    have hbase : μ.map (fun ω => fun j : Fin (n + 1) => (Z ω j.val).1) =
        (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (fun w => fun j : Fin (n + 1) => (0 : ℤ) + lazyWordValues w j) := by
      have hh := congrArg (fun ρ : Measure (Fin (n + 1) → ℤ × ℤ) =>
        ρ.map (fun q => fun j => (q j).1)) hb
      rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
        Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
      exact hh
    rw [hbase]
    apply withDensity_congr_ae
    filter_upwards [] with p
    by_cases hn : ∀ j, 0 ≤ p j
    · rw [ite_eq_left hn, ite_eq_left hn]
      have he : (p (Fin.last n) : ℝ) = (p (Fin.last n)).toNat := by
        exact_mod_cast (Int.toNat_of_nonneg (hn (Fin.last n))).symm
      rw [he]
      norm_num [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast]
    · rw [ite_eq_right hn, ite_eq_right hn]

/-- The literal flipped process is the constructed conditioned vector path law -/
theorem vectorPitman_law_eq_conditionedVectorPathLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℕ → ℤ × ℤ}
    (hZ : Measurable Z) (hzero : ∀ᵐ ω ∂μ, Z ω 0 = (0, 0))
    (hind : iIndepFun (fun i ω => Z ω (i + 1) - Z ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => Z ω (i + 1) - Z ω i) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) :
    μ.map (fun ω k => vectorPitman (Z ω) k) = conditionedVectorPathLaw 0 0 := by
  have hm : Measurable (fun ω k => vectorPitman (Z ω) k) :=
    measurable_vectorPitman.comp hZ
  have : IsProbabilityMeasure (μ.map (fun ω k => vectorPitman (Z ω) k)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply conditioned_vector_law_unique 0 0
  · intro n
    rw [Measure.map_map (by fun_prop) hm]
    simpa only [Nat.cast_zero, Function.comp_def] using vectorPitman_prefix_law hZ hzero hind hlaw n
  · exact conditionedVectorPathLaw_map_prefix 0 0

end DirectedDistances.RandomWalk
