module

public import DirectedDistances.RandomWalk.ConditionedStrongMarkov

/-! # First-hit past/future factorization with a fixed endpoint

past/future factorization at the first hit of R = −r for an arbitrary measurable
used; not the paper result. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem measurableSet_of_conditionedVectorPast (k : ℕ)
    (C : Set (ℕ → ℤ × ℤ)) (hC : MeasurableSet[conditionedVectorPast k] C) :
    MeasurableSet C := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hC
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

private theorem measurableSet_finite_event
    (τ : (ℕ → ℤ × ℤ) → ℕ∞) (C : Set (ℕ → ℤ × ℤ))
    (hC : ∀ k : ℕ, MeasurableSet (C ∩ {p | τ p = (k : ℕ∞)})) :
    MeasurableSet (C ∩ {p | τ p < ⊤}) := by
  have heq : C ∩ {p | τ p < ⊤} = ⋃ k : ℕ, C ∩ {p | τ p = (k : ℕ∞)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hp, hfin⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin.ne
      exact ⟨k, hp, hk.symm⟩
    · rintro ⟨k, hp, hk⟩
      exact ⟨hp, hk ▸ ENat.natCast_lt_top k⟩
  rw [heq]
  exact MeasurableSet.iUnion hC

private theorem measurableSet_firstHit_endpoint_slice (r ell k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      ({p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  have hend : MeasurableSet[conditionedVectorPast k]
      {p : ℕ → ℤ × ℤ | (p k).1 = (ell : ℤ)} := by
    refine ⟨{q : Fin (k + 1) → ℤ × ℤ | (q (Fin.last k)).1 = (ell : ℤ)},
      (Set.to_countable _).measurableSet, ?_⟩
    rfl
  exact (measurableSet_conditionedVectorPast_firstHit_eq r k).inter hend

private theorem firstHit_second_coordinate (r : ℕ) (p : ℕ → ℤ × ℤ)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    (p (conditionedSecondCoordinateFirstHit r p).toNat).2 = -(r : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit at hfin ⊢
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · rw [dite_eq_left h, ENat.toNat_natCast]
    exact Nat.find_spec h
  · rw [dite_eq_right h] at hfin
    exact (lt_irrefl _ hfin).elim

/-- past/future factorization at the first hit of R = −r for an arbitrary measurable
used; not the paper result. The shift retains the absolute endpoint (ell, −r). -/
theorem conditionedFirstHit_past_future_factorization
    (r ell : ℕ) (A B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B)
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let τ : (ℕ → ℤ × ℤ) → ℕ∞ := conditionedSecondCoordinateFirstHit r
    conditionedVectorPathLaw 0 0
      (A ∩ {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)} ∩
        {p | conditionedVectorShift (τ p).toNat p ∈ B}) =
    conditionedVectorPathLaw 0 0
      (A ∩ {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}) *
      conditionedVectorPathLaw ell (-(r : ℤ)) B := by
  classical
  dsimp only
  let τ := conditionedSecondCoordinateFirstHit r
  let C : Set (ℕ → ℤ × ℤ) := A ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have hC : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k] (C ∩ {p | τ p = (k : ℕ∞)}) := by
    intro k
    have heq : C ∩ {p | τ p = (k : ℕ∞)} =
        A ∩ {p | τ p = (k : ℕ∞)} ∩ {p | (p k).1 = (ell : ℤ)} := by
      ext p
      by_cases hp : τ p = (k : ℕ∞) <;> simp [C, hp]
    rw [heq]
    exact hA k
  have hR := measurableSet_finite_event τ C
    (fun k => measurableSet_of_conditionedVectorPast k _ (hC k))
  have hstrong := conditionedVectorPathLaw_strongMarkov 0 0 τ
    (fun k => measurableSet_conditionedVectorPast_firstHit_eq r k) C hC B hB
  have heq : C ∩ {p | τ p < ⊤} =
      A ∩ {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)} := by
    ext p
    simp only [C, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hconst :
      (∫⁻ p in C ∩ {p | τ p < ⊤},
        conditionedVectorPathLaw ((p (τ p).toNat).1.toNat) (p (τ p).toNat).2 B
          ∂conditionedVectorPathLaw 0 0) =
      conditionedVectorPathLaw ell (-(r : ℤ)) B *
        conditionedVectorPathLaw 0 0 (C ∩ {p | τ p < ⊤}) := by
    calc
      _ = ∫⁻ _ in C ∩ {p | τ p < ⊤},
          conditionedVectorPathLaw ell (-(r : ℤ)) B ∂conditionedVectorPathLaw 0 0 := by
        apply setLIntegral_congr_fun hR
        intro p hp
        have hleft : (p (τ p).toNat).1 = (ell : ℤ) := hp.1.2
        have hright : (p (τ p).toNat).2 = -(r : ℤ) :=
          firstHit_second_coordinate r p hp.2
        simp only [hleft, hright, Int.toNat_natCast]
      _ = _ := setLIntegral_const _ _
  rw [hconst, heq, mul_comm] at hstrong
  exact hstrong



theorem conditionedFirstHit_cond_past_future
    (r ell : ℕ) (A B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B)
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)}))
    (hpos : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)} ∩
        {p | conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
          ∈ B})) :
    let τ : (ℕ → ℤ × ℤ) → ℕ∞ := conditionedSecondCoordinateFirstHit r
    (conditionedVectorPathLaw 0 0)[A |
      {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)} ∩
        {p | conditionedVectorShift (τ p).toNat p ∈ B}] =
    (conditionedVectorPathLaw 0 0)[A |
      {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}] := by
  classical
  dsimp only
  let τ := conditionedSecondCoordinateFirstHit r
  let D : Set (ℕ → ℤ × ℤ) := {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let E : Set (ℕ → ℤ × ℤ) := {p | τ p < ⊤} ∩ D
  let F : Set (ℕ → ℤ × ℤ) := {p | conditionedVectorShift (τ p).toNat p ∈ B}
  let μ := conditionedVectorPathLaw 0 0
  let q := conditionedVectorPathLaw ell (-(r : ℤ)) B
  have hDslice (k : ℕ) : MeasurableSet (D ∩ {p | τ p = (k : ℕ∞)}) := by
    have heq : D ∩ {p | τ p = (k : ℕ∞)} =
        {p | τ p = (k : ℕ∞)} ∩ {p | (p k).1 = (ell : ℤ)} := by
      ext p
      by_cases hp : τ p = (k : ℕ∞) <;> simp [D, hp]
    rw [heq]
    exact measurableSet_of_conditionedVectorPast k _
      (measurableSet_firstHit_endpoint_slice r ell k)
  have hE : MeasurableSet E := by
    have h := measurableSet_finite_event τ D hDslice
    simpa only [E, Set.inter_comm] using h
  have hEF : MeasurableSet (E ∩ F) := by
    have h := measurableSet_finite_event τ (D ∩ F) (fun k => by
      have heq : (D ∩ F) ∩ {p | τ p = (k : ℕ∞)} =
          (D ∩ {p | τ p = (k : ℕ∞)}) ∩ conditionedVectorShift k ⁻¹' B := by
        ext p
        by_cases hp : τ p = (k : ℕ∞) <;> simp [D, F, hp]
      rw [heq]
      exact (hDslice k).inter (hB.preimage (measurable_conditionedVectorShift k)))
    convert h using 1
    ext p
    simp only [E, Set.mem_inter_iff]
    tauto
  have hfactor : μ (A ∩ E ∩ F) = μ (A ∩ E) * q := by
    simpa only [μ, E, D, F, q, Set.inter_assoc] using
      conditionedFirstHit_past_future_factorization r ell A B hB hA
  have hbase : μ (E ∩ F) = μ E * q := by
    have hUniv : ∀ k : ℕ,
        MeasurableSet[conditionedVectorPast k]
          (Set.univ ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
            {p | (p k).1 = (ell : ℤ)}) := by
      intro k
      simpa only [Set.univ_inter] using measurableSet_firstHit_endpoint_slice r ell k
    simpa only [μ, E, D, F, q, Set.univ_inter] using
      conditionedFirstHit_past_future_factorization r ell Set.univ B hB hUniv
  change μ[A | E ∩ F] = μ[A | E]
  apply (ENNReal.mul_left_inj hpos.ne' (measure_ne_top μ (E ∩ F))).mp
  calc
    μ[A | E ∩ F] * μ (E ∩ F) = μ ((E ∩ F) ∩ A) :=
      cond_mul_eq_inter hEF A μ
    _ = μ (A ∩ E ∩ F) := by congr 1; ext p; simp only [Set.mem_inter_iff]; tauto
    _ = μ (A ∩ E) * q := hfactor
    _ = (μ[A | E] * μ E) * q := by rw [cond_mul_eq_inter hE, Set.inter_comm E A]
    _ = μ[A | E] * μ (E ∩ F) := by rw [mul_assoc, ← hbase]

end DirectedDistances.RandomWalk
