/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyPathLaw
public import DirectedDistances.RandomWalk.LazyPrefixLaw
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Supporting lemmas for paper labels `lem-lazy-walk-flip` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The actual zero-start finite path obtained by integrating the iid step word. -/
@[expose] def lazyIIDPrefix {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (n : ℕ)
    (ω : Ω) : LazyPath n := lazyPathOfWord (fun i : Fin n => ξ (i : ℕ) ω)

/-- The actual finite Pitman transform, viewed on the same source path carrier. -/
@[expose] noncomputable def pitmanIIDPrefix {Ω : Type*} (ξ : ℕ → Ω → Fin 3)
    (n : ℕ) (ω : Ω) : LazyPath n := (lazyPhi (lazyIIDPrefix ξ n ω)).val

/-- The actual prefix map is measurable, so its pushforward is genuine. -/
theorem measurable_lazyIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {ξ : ℕ → Ω → Fin 3} (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) :
    Measurable (lazyIIDPrefix ξ n) :=
  (measurable_of_countable (@lazyPathOfWord n)).comp
    (Measurable.of_eval (fun i : Fin n => hξ (i : ℕ)))

/-- The actual transformed prefix map is measurable as well. -/
theorem measurable_pitmanIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {ξ : ℕ → Ω → Fin 3} (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) :
    Measurable (pitmanIIDPrefix ξ n) :=
  (measurable_of_countable (fun p : LazyPath n => (lazyPhi p).val)).comp
    (measurable_lazyIIDPrefix hξ n)

/-- Every source path has the actual iid-prefix probability 3^(-n).
Uniformity on the path carrier is derived through the proved word bijection. -/
theorem measure_lazyIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)))
    (n : ℕ) (p : LazyPath n) :
    μ {ω | lazyIIDPrefix ξ n ω = p} = (1 / 3 : ℝ≥0∞) ^ n := by
  have hevent : {ω | lazyIIDPrefix ξ n ω = p} =
      {ω | (fun i : Fin n => ξ (i : ℕ) ω) = lazyPathWord p} := by
    ext ω
    constructor
    · intro h
      have hh := congrArg (@lazyPathWord n) h
      simpa only [Set.mem_ofPred_eq, lazyIIDPrefix, lazyPathWord_ofWord] using hh
    · intro h
      change lazyPathOfWord (fun i : Fin n => ξ (i : ℕ) ω) = p
      rw [h, lazyPathOfWord_word]
  rw [hevent, measure_lazy_prefix_word hξ hind hlaw n (lazyPathWord p)]
  simp only [one_div, ENNReal.inv_pow]

/-- The actual iid-prefix pushforward is the genuine uniform measure on Wn. -/
theorem map_lazyIIDPrefix_eq_uniform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (lazyIIDPrefix ξ n) = (uniformLazyPath n).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_lazyIIDPrefix hξ n) (measurableSet_singleton p),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), uniformLazyPath_apply_pow]
  exact measure_lazyIIDPrefix hξ hind hlaw n p

/-- The actual transformed prefix on the nonnegative carrier has the proved
Pitman image law; no transformed-law premise is assumed. -/
theorem map_nonnegative_pitmanIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (fun ω => lazyPhi (lazyIIDPrefix ξ n ω)) =
      (pitmanLazyPathLaw n).toMeasure := by
  have hphi : Measurable (@lazyPhi n) := measurable_of_countable _
  calc
    _ = (μ.map (lazyIIDPrefix ξ n)).map lazyPhi :=
      (Measure.map_map hphi (measurable_lazyIIDPrefix hξ n)).symm
    _ = (uniformLazyPath n).toMeasure.map lazyPhi := by
      rw [map_lazyIIDPrefix_eq_uniform hξ hind hlaw n]
    _ = (pitmanLazyPathLaw n).toMeasure := PMF.toMeasure_map _ _ hphi

/-- Forgetting only the nonnegativity proof keeps the transformed law on the
same actual source path carrier as the original iid prefix. -/
theorem map_pitmanIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (pitmanIIDPrefix ξ n) =
      (pitmanLazyPathLaw n).toMeasure.map (fun q : NonnegativeLazyPath n => q.val) := by
  have hval : Measurable (fun q : NonnegativeLazyPath n => q.val) :=
    measurable_of_countable _
  have hprefix : Measurable (fun ω => lazyPhi (lazyIIDPrefix ξ n ω)) :=
    (measurable_of_countable (@lazyPhi n)).comp (measurable_lazyIIDPrefix hξ n)
  calc
    _ = (μ.map (fun ω => lazyPhi (lazyIIDPrefix ξ n ω))).map
        (fun q : NonnegativeLazyPath n => q.val) := (Measure.map_map hval hprefix).symm
    _ = _ := by rw [map_nonnegative_pitmanIIDPrefix hξ hind hlaw n]

/-- Exact transformed point masses, including zero off the actual nonnegative
path event. The endpoint factor multiplies the original counting weight. -/
theorem measure_pitmanIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)))
    (n : ℕ) (p : LazyPath n) :
    μ {ω | pitmanIIDPrefix ξ n ω = p} =
      (if ∀ j : Fin (n + 1), 0 ≤ p.val j then
        (((p.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) * (1 / 3 : ℝ≥0∞) ^ n := by
  classical
  rw [show {ω | pitmanIIDPrefix ξ n ω = p} = (pitmanIIDPrefix ξ n) ⁻¹' {p} from rfl,
    ← Measure.map_apply (measurable_pitmanIIDPrefix hξ n) (measurableSet_singleton p),
    map_pitmanIIDPrefix hξ hind hlaw n,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  by_cases hp : ∀ j : Fin (n + 1), 0 ≤ p.val j
  · have he : (fun q : NonnegativeLazyPath n => q.val) ⁻¹' {p} = {⟨p, hp⟩} := by
      ext q
      change q.val = p ↔ q = ⟨p, hp⟩
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [he]
    calc
      _ = pitmanLazyPathLaw n (⟨p, hp⟩ : NonnegativeLazyPath n) :=
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
      _ = _ := by
        simpa only [ite_eq_left hp] using
          (pitmanLazyPathLaw_apply (⟨p, hp⟩ : NonnegativeLazyPath n))
  · have he : (fun q : NonnegativeLazyPath n => q.val) ⁻¹' {p} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have heq : q.val = p := hq
      exact hp (heq ▸ q.property)
    rw [he, measure_empty, ite_eq_right hp, zero_mul]

/-- The actual iid Pitman prefix satisfies the x=0 finite Radon–Nikodym law,
with both sides on the same literal Wn carrier. Uniformity and the endpoint
weight are produced by checked finite-law theorems inside the proof. -/
theorem map_pitmanIIDPrefix_eq_withDensity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (fun ω => (lazyPhi (lazyPathOfWord (fun i : Fin n => ξ (i : ℕ) ω))).val) =
      (μ.map (fun ω => lazyPathOfWord (fun i : Fin n => ξ (i : ℕ) ω))).withDensity
        (fun p : LazyPath n => if ∀ j : Fin (n + 1), 0 ≤ p.val j then
          (((p.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) := by
  classical
  change μ.map (pitmanIIDPrefix ξ n) = (μ.map (lazyIIDPrefix ξ n)).withDensity _
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_pitmanIIDPrefix hξ n) (measurableSet_singleton p),
    withDensity_apply _ (measurableSet_singleton p), lintegral_singleton,
    Measure.map_apply (measurable_lazyIIDPrefix hξ n) (measurableSet_singleton p)]
  change μ {ω | pitmanIIDPrefix ξ n ω = p} =
    (if ∀ j : Fin (n + 1), 0 ≤ p.val j then
      (((p.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) *
        μ {ω | lazyIIDPrefix ξ n ω = p}
  rw [measure_pitmanIIDPrefix hξ hind hlaw n p, measure_lazyIIDPrefix hξ hind hlaw n p]

/-- The transformed prefix pushforward is a probability measure, ruling out
any nonmeasurable-map default interpretation of the Radon–Nikodym equality. -/
theorem isProbabilityMeasure_map_pitmanIIDPrefix {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) :
    IsProbabilityMeasure (μ.map (pitmanIIDPrefix ξ n)) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_pitmanIIDPrefix hξ n).aemeasurable).2 inferInstance

end DirectedDistances.RandomWalk
