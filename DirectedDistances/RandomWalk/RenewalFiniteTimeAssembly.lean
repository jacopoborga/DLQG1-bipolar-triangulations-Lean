/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalStoppedSliceTransport
public import DirectedDistances.Probability.CountableRegenerationAssembly
public import DirectedDistances.Probability.ConditionalLawFromTests

/-! # Generic finite-time assembly from supplied slice laws

These are **conditional generic** measure theorems. The fixed-time laws
are explicit inputs; this file neither defines the manuscript renewal
times nor supplies their slice laws. No theorem here certifies Lemma 4.9

The actual finite-event subtype is retained, including zero total mass.
All finite slices, including time zero, enter the countable assembly. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Actual finite-subtype slice mass agrees with the ambient extended-time
fiber mass, also for arbitrary (possibly nonmeasurable) history tests. -/
theorem finiteTime_history_slice_mass
    (μ : Measure (ℕ → ℤ × ℤ))
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ) (hT : Measurable T)
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (n : ℕ) :
    (μ.comap (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ)))
      {ω | finiteTimeIndex T ω = n ∧
        stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val) ω ∈ H} =
      μ {p | T p = (n : WithTop ℕ) ∧
        (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
          Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} := by
  rw [finiteTime_history_slice_preimage]
  have he : MeasurableEmbedding
      (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ)) :=
    MeasurableEmbedding.subtype_coe (hT measurableSet_Iio)
  rw [he.comap_preimage]
  apply congrArg μ
  apply Set.inter_eq_left.mpr
  rintro p ⟨hp, _⟩
  apply Set.mem_range.mpr
  refine ⟨⟨p, ?_⟩, rfl⟩
  rw [hp]
  exact WithTop.coe_lt_top n

/-- Conditional generic assembly: supplied fixed-time tested laws imply
the full whole-history-tested common-future law on the finite-time subtype.
The slice-law premise must be proved at every source application. -/
theorem finiteTime_history_restrict_map_of_slice_laws
    (μ ρ : Measure (ℕ → ℤ × ℤ))
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ) (hT : Measurable T)
    (hslice : ∀ (n : ℕ) (A : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)),
      MeasurableSet A →
        (μ.restrict {p | T p = (n : WithTop ℕ) ∧
          (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
            Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ A}).map
          (fun p => fun k => p (n + k) - p n) =
        μ {p | T p = (n : WithTop ℕ) ∧
          (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
            Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ A} • ρ)
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (hH : MeasurableSet H) :
    let μf := μ.comap (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history := stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future := stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    (μf.restrict (history ⁻¹' H)).map future = μf (history ⁻¹' H) • ρ := by
  intro μf history future
  let s : ℕ → Set {p // T p < ⊤} := fun n => {ω | finiteTimeIndex T ω = n}
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (measurable_finiteTimeIndex T hT) (measurableSet_singleton n)
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (hi.symm.trans hj)
  have hhistory : Measurable history :=
    measurable_finiteTime_vectorHistory T (fun p => p) hT measurable_id
  have hfuture : Measurable future :=
    measurable_finiteTime_vectorFuture T (fun p => p) hT measurable_id
  have hpiece (n : ℕ) :
      (μf.restrict (s n ∩ history ⁻¹' H)).map future =
        μf (s n ∩ history ⁻¹' H) • ρ := by
    change (μf.restrict {ω | finiteTimeIndex T ω = n ∧ history ω ∈ H}).map
      future = μf {ω | finiteTimeIndex T ω = n ∧ history ω ∈ H} • ρ
    rw [finiteTime_vectorFuture_history_slice_map μ T hT H n,
      finiteTime_history_slice_mass μ T hT H n]
    exact hslice n H hH
  have hunion : (⋃ n, s n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact Set.mem_iUnion.mpr ⟨finiteTimeIndex T ω, rfl⟩
  have h := DirectedDistances.Probability.map_restrict_iUnion_inter_eq_smul
    μf ρ s hs hd (history ⁻¹' H) (hH.preimage hhistory) future hfuture hpiece
  simpa only [hunion, Set.univ_inter] using h

/-- Conditional generic assembly gives one simultaneous almost-everywhere
whole-future conditional-measure identity. Neither positivity nor
normalization of the finite-event mass is required. -/
theorem finiteTime_condDistrib_ae_eq_const_of_slice_laws
    (μ : Measure (ℕ → ℤ × ℤ)) [IsFiniteMeasure μ]
    (ρ : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ρ]
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ) (hT : Measurable T)
    (hslice : ∀ (n : ℕ) (A : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)),
      MeasurableSet A →
        (μ.restrict {p | T p = (n : WithTop ℕ) ∧
          (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
            Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ A}).map
          (fun p => fun k => p (n + k) - p n) =
        μ {p | T p = (n : WithTop ℕ) ∧
          (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
            Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ A} • ρ) :
    let μf := μ.comap (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history := stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future := stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    condDistrib future history μf =ᵐ[μf.map history]
      Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ρ := by
  intro μf history future
  exact DirectedDistances.Probability.condDistrib_ae_eq_const_of_restrict_map_eq_smul
    μf ρ history future
    (measurable_finiteTime_vectorHistory T (fun p => p) hT measurable_id)
    (measurable_finiteTime_vectorFuture T (fun p => p) hT measurable_id)
    (fun A hA => finiteTime_history_restrict_map_of_slice_laws μ ρ T hT hslice A hA)

end DirectedDistances.RandomWalk
