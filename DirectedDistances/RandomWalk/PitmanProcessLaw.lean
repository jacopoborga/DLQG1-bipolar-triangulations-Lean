/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.CanonicalPitmanLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Supporting lemmas for paper labels `lem-lazy-walk-flip` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A measurable arithmetic code for an integer step. On the source support
`{-1,0,1}` its decoded value is exactly the original integer. This auxiliary
arithmetic function is not used as a definition of an arbitrary lazy walk. -/
@[expose] def lazyIntegerStepCode (z : ℤ) : Fin 3 :=
  ⟨(z + 1).toNat % 3, Nat.mod_lt _ (by decide)⟩

/-- The code loses no information on the literal source step set. -/
theorem lazyIntegerStepCode_decode {z : ℤ}
    (hz : z ∈ ({-1, 0, 1} : Set ℤ)) :
    ((lazyIntegerStepCode z).val : ℤ) - 1 = z := by
  have hb := lazy_increment_iff.mp hz
  have hn : 0 ≤ z + 1 := by omega
  have hc := Int.toNat_of_nonneg hn
  have ht : (z + 1).toNat < 3 := by omega
  simp only [lazyIntegerStepCode, Nat.mod_eq_of_lt ht]
  omega

/-- The arithmetic code is measurable on all integers. -/
theorem measurable_lazyIntegerStepCode : Measurable lazyIntegerStepCode :=
  measurable_of_countable _

/-- The code carries the actual uniform integer-step law to the actual
uniform three-code law. -/
theorem map_uniform_lazyIntegerStepCode :
    (Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)).map lazyIntegerStepCode =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hmap (c : ℝ≥0∞) (z : ℤ) :
      (c • Measure.dirac z).map lazyIntegerStepCode =
        c • Measure.dirac (lazyIntegerStepCode z) := by
    rw [Measure.map_smul c measurable_lazyIntegerStepCode.aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset, hu]
  norm_num [Measure.map_add, measurable_lazyIntegerStepCode, hmap, lazyIntegerStepCode]

/-- Uniform integer increments lie in the source step set almost surely;
legality is derived from their actual law rather than assumed separately. -/
theorem ae_mem_lazyIntegerSteps {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : Ω → ℤ} (hd : Measurable d)
    (hlaw : μ.map d = Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) :
    ∀ᵐ ω ∂μ, d ω ∈ ({-1, 0, 1} : Set ℤ) := by
  have ha : ∀ᵐ z ∂Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ),
      z ∈ ({-1, 0, 1} : Set ℤ) := by
    rw [ae_iff]
    rw [Measure.uniformOfFinset_apply]
    norm_num
  rw [← hlaw] at ha
  exact (ae_map_iff hd.aemeasurable ((Set.to_countable _).measurableSet)).mp ha

/-- The actual integer increment process, after coding, retains independence
and the precise uniform marginal law. -/
theorem integerLazyProcess_code_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {L : Ω → ℕ → ℤ} (hL : Measurable L)
    (hind : iIndepFun (fun i ω => L ω (i + 1) - L ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => L ω (i + 1) - L ω i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) :
    (∀ i, Measurable (fun ω => lazyIntegerStepCode (L ω (i + 1) - L ω i))) ∧
    iIndepFun (fun i ω => lazyIntegerStepCode (L ω (i + 1) - L ω i)) μ ∧
    (∀ i, μ.map (fun ω => lazyIntegerStepCode (L ω (i + 1) - L ω i)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) := by
  have hd : ∀ i, Measurable (fun ω => L ω (i + 1) - L ω i) :=
    fun i => ((measurable_pi_apply (i + 1)).comp hL).sub
      ((measurable_pi_apply i).comp hL)
  refine ⟨fun i => measurable_lazyIntegerStepCode.comp (hd i), ?_, ?_⟩
  · exact hind.comp (fun _ => lazyIntegerStepCode) (fun _ => measurable_lazyIntegerStepCode)
  · intro i
    rw [show (fun ω => lazyIntegerStepCode (L ω (i + 1) - L ω i)) =
        lazyIntegerStepCode ∘ (fun ω => L ω (i + 1) - L ω i) from rfl,
      ← Measure.map_map measurable_lazyIntegerStepCode (hd i), hlaw i]
    exact map_uniform_lazyIntegerStepCode

/-- Every actual zero-start integer process with the source marginal laws is
almost surely equal as an ENTIRE countable path to its integrated codes.
The countable simultaneous legal-step event is produced explicitly. -/
theorem ae_integerLazyProcess_eq_integrated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {L : Ω → ℕ → ℤ} (hL : Measurable L)
    (hzero : ∀ᵐ ω ∂μ, L ω 0 = 0)
    (hlaw : ∀ i, μ.map (fun ω => L ω (i + 1) - L ω i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) :
    L =ᵐ[μ] globalIIDLazyWalk
      (fun i ω => lazyIntegerStepCode (L ω (i + 1) - L ω i)) := by
  have hd : ∀ i, Measurable (fun ω => L ω (i + 1) - L ω i) :=
    fun i => ((measurable_pi_apply (i + 1)).comp hL).sub
      ((measurable_pi_apply i).comp hL)
  have hlegal : ∀ᵐ ω ∂μ, ∀ i, L ω (i + 1) - L ω i ∈ ({-1, 0, 1} : Set ℤ) :=
    ae_all_iff.mpr (fun i => ae_mem_lazyIntegerSteps (hd i) (hlaw i))
  filter_upwards [hzero, hlegal] with ω hz hs
  apply globalIIDLazyWalk_unique _ ω _ hz
  intro i
  exact (lazyIntegerStepCode_decode (hs i)).symm

private theorem map_withDensity_comp_countable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {f : α → β} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (ν.withDensity (fun x => g (f x))).map f = (ν.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hg hf]

/-- The existing canonical same-Wn RN law transported to the literal raw
finite-vector carrier; invalid vectors retain zero mass rather than a fallback. -/
theorem canonicalPitman_raw_prefix_RN {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (fun ω => fun j : Fin (n + 1) =>
      globalLazyPhi (globalIIDLazyWalk ξ ω) j.val) =
      (μ.map (fun ω => fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val)).withDensity
        (fun p : Fin (n + 1) → ℤ => if ∀ j, 0 ≤ p j then
          (((p (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) := by
  classical
  let v : LazyPath n → (Fin (n + 1) → ℤ) := Subtype.val
  let d : (Fin (n + 1) → ℤ) → ℝ≥0∞ := fun p => if ∀ j, 0 ≤ p j then
    (((p (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0
  have hv : Measurable v := measurable_of_countable _
  have hd : Measurable d := measurable_of_countable _
  have hRN : μ.map (pitmanIIDPrefix ξ n) =
      (μ.map (lazyIIDPrefix ξ n)).withDensity (fun p => d (v p)) :=
    map_pitmanIIDPrefix_eq_withDensity hξ hind hlaw n
  calc
    _ = (μ.map (pitmanIIDPrefix ξ n)).map v := by
      rw [Measure.map_map hv (measurable_pitmanIIDPrefix hξ n)]
      congr 1
      funext ω j
      exact (pitmanIIDPrefix_apply_global ξ n ω j).symm
    _ = ((μ.map (lazyIIDPrefix ξ n)).withDensity (fun p => d (v p))).map v := by rw [hRN]
    _ = ((μ.map (lazyIIDPrefix ξ n)).map v).withDensity d :=
      map_withDensity_comp_countable hv hd
    _ = _ := by
      rw [Measure.map_map hv (measurable_lazyIIDPrefix hξ n)]
      congr 1
      congr 1
      funext ω j
      exact lazyIIDPrefix_apply ξ n ω j

/-- On one simultaneous probability-one event the actual transformed integer
process starts at zero, stays nonnegative, and has legal lazy increments. -/
theorem ae_integerLazyPitman_path_properties {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {L : Ω → ℕ → ℤ} (hL : Measurable L)
    (hzero : ∀ᵐ ω ∂μ, L ω 0 = 0)
    (hlaw : ∀ i, μ.map (fun ω => L ω (i + 1) - L ω i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) :
    ∀ᵐ ω ∂μ, globalLazyPhi (L ω) 0 = 0 ∧
      (∀ j, 0 ≤ globalLazyPhi (L ω) j) ∧
      (∀ j, globalLazyPhi (L ω) (j + 1) - globalLazyPhi (L ω) j ∈
        ({-1, 0, 1} : Set ℤ)) := by
  have hs := ae_integerLazyProcess_eq_integrated hL hzero hlaw
  filter_upwards [hs] with ω hω
  rw [hω]
  exact canonicalPitman_path_properties _ ω




theorem pitman_process_prefix_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : Ω → ℕ → ℤ}
    (hL : Measurable L) (hzero : ∀ᵐ ω ∂μ, L ω 0 = 0)
    (hind : iIndepFun (fun i ω => L ω (i + 1) - L ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => L ω (i + 1) - L ω i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)) :
    ∀ n : ℕ,
      μ.map (fun ω => fun j : Fin (n + 1) => globalLazyPhi (L ω) j.val) =
        (μ.map (fun ω => fun j : Fin (n + 1) => L ω j.val)).withDensity
          (fun p : Fin (n + 1) → ℤ => if ∀ j, 0 ≤ p j then
            (((p (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) := by
  let ξ : ℕ → Ω → Fin 3 := fun i ω => lazyIntegerStepCode (L ω (i + 1) - L ω i)
  obtain ⟨hξ, hiξ, hlξ⟩ := integerLazyProcess_code_law hL hind hlaw
  have hs : L =ᵐ[μ] globalIIDLazyWalk ξ :=
    ae_integerLazyProcess_eq_integrated hL hzero hlaw
  intro n
  have hbase : μ.map (fun ω => fun j : Fin (n + 1) => L ω j.val) =
      μ.map (fun ω => fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val) := by
    apply Measure.map_congr
    filter_upwards [hs] with ω hω
    rw [hω]
  have hphi : μ.map (fun ω => fun j : Fin (n + 1) => globalLazyPhi (L ω) j.val) =
      μ.map (fun ω => fun j : Fin (n + 1) =>
        globalLazyPhi (globalIIDLazyWalk ξ ω) j.val) := by
    apply Measure.map_congr
    filter_upwards [hs] with ω hω
    rw [hω]
  rw [hphi, hbase]
  exact canonicalPitman_raw_prefix_RN hξ hiξ hlξ n

end DirectedDistances.RandomWalk
