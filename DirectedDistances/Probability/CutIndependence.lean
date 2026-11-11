module

public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Max

/-! # Independence from every integer cut -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory








theorem iIndepFun_of_indepFun_int_cuts
    {Ω : Type*} [MeasurableSpace Ω] {β : ℤ → Type*}
    [mβ : ∀ j, MeasurableSpace (β j)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G : ∀ j, Ω → β j}
    (hcut : ∀ k : ℤ,
      IndepFun (fun ω (j : {j : ℤ // j ≤ k}) => G j ω)
        (fun ω (j : {j : ℤ // k + 1 ≤ j}) => G j ω) μ) :
    iIndepFun G μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
      intro sets hs
      simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ,
        measure_univ, Finset.prod_empty]
  | insert a s hmax ih =>
      intro sets hs
      have ha : a ∉ s := fun ha => (lt_irrefl a) (hmax a ha)
      have hleft (i : s) : (i : ℤ) ≤ a - 1 := by
        have := hmax i i.property
        omega
      have hright : a - 1 + 1 ≤ a := by omega
      have hind : IndepFun (fun ω (i : s) => G i ω) (G a) μ :=
        (hcut (a - 1)).comp
          (φ := fun (v : ∀ j : {j : ℤ // j ≤ a - 1}, β j) (i : s) =>
            v ⟨i, hleft i⟩)
          (ψ := fun (v : ∀ j : {j : ℤ // a - 1 + 1 ≤ j}, β j) => v ⟨a, hright⟩)
          (Measurable.of_eval fun i : s =>
            (measurable_pi_apply (X := fun j : {j : ℤ // j ≤ a - 1} => β j)
              ⟨i, hleft i⟩))
          (measurable_pi_apply (X := fun j : {j : ℤ // a - 1 + 1 ≤ j} => β j)
            ⟨a, hright⟩)
      let A : Set (∀ i : s, β i) := ⋂ i : s, (fun v => v i) ⁻¹' sets i
      have hA : MeasurableSet A :=
        MeasurableSet.iInter fun i : s =>
          (measurable_pi_apply i) (hs i (Finset.mem_insert_of_mem i.property))
      have hpre : (fun ω (i : s) => G i ω) ⁻¹' A =
          ⋂ i ∈ s, G i ⁻¹' sets i := by
        ext ω
        simp only [A, Set.mem_preimage, Set.mem_iInter, Subtype.forall]
      have hmul := hind.measure_inter_preimage_eq_mul A (sets a) hA
        (hs a (Finset.mem_insert_self a s))
      rw [hpre] at hmul
      simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left] at ⊢
      rw [Set.inter_comm, hmul,
        ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)), Finset.prod_insert ha,
        mul_comm]

end DirectedDistances.Probability
