module

public import DirectedDistances.RandomWalk.ConditionedFirstHitFutureFactorization
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib

/-! # Endpoint-conditioned independence at a first hit

stopped past and the uncentered future at the first hit of R = −r under the
endpoint-conditioned UIQBOT law, and the a.e. conditional-distribution form; the

The positive endpoint range is explicit. Positivity of the conditioning event is
also an explicit premise; no positivity assertion at the null endpoint ell = 0 is made.
The shift retains the absolute endpoint. At an infinite hit its existing `toNat`
convention gives the original path, and this branch has zero conditional mass. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem measurableSet_of_past (k : ℕ) (S : Set (ℕ → ℤ × ℤ))
    (hS : MeasurableSet[conditionedVectorPast k] S) : MeasurableSet S := by
  obtain ⟨T, hT, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [← hpre]
  exact hT.preimage (measurable_conditionedVectorPrefix k)

private theorem measurable_firstHit (r : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit r) := by
  apply ENat.measurable_iff.mpr
  intro k
  exact measurableSet_of_past k _
    (measurableSet_conditionedVectorPast_firstHit_eq r k)

private theorem measurable_firstHit_nat (r : ℕ) :
    Measurable (fun p => (conditionedSecondCoordinateFirstHit r p).toNat) :=
  (measurable_of_countable ENat.toNat).comp (measurable_firstHit r)

/-- of the uncentered whole future at the first hit, by its countable time decomposition; -/
theorem measurable_conditionedFirstHit_future (r : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ =>
      conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p) := by
  intro B hB
  have heq :
      (fun p : ℕ → ℤ × ℤ =>
        conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p) ⁻¹' B =
      ⋃ k : ℕ, {p | (conditionedSecondCoordinateFirstHit r p).toNat = k} ∩
        conditionedVectorShift k ⁻¹' B := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hp
      exact ⟨_, rfl, hp⟩
    · rintro ⟨k, hk, hp⟩
      simpa only [hk] using hp
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    ((measurable_firstHit_nat r) (measurableSet_singleton k)).inter
      (hB.preimage (measurable_conditionedVectorShift k))

private theorem measurableSet_endpoint_slice (r ell k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      ({p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  have hend : MeasurableSet[conditionedVectorPast k]
      {p : ℕ → ℤ × ℤ | (p k).1 = (ell : ℤ)} := by
    refine ⟨{q : Fin (k + 1) → ℤ × ℤ | (q (Fin.last k)).1 = (ell : ℤ)},
      (Set.to_countable _).measurableSet, ?_⟩
    rfl
  exact (measurableSet_conditionedVectorPast_firstHit_eq r k).inter hend

private theorem measurableSet_stopped_slice (r ell : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let τ := conditionedSecondCoordinateFirstHit r
    MeasurableSet
      (A ∩ ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)})) := by
  dsimp only
  have heq :
      A ∩ ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) =
      ⋃ k : ℕ, A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hp, hfin, hend⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin.ne
      refine ⟨k, ⟨hp, hk.symm⟩, ?_⟩
      simpa only [← hk, ENat.toNat_natCast] using hend
    · rintro ⟨k, ⟨hp, hk⟩, hend⟩
      exact ⟨hp, hk ▸ ENat.natCast_lt_top k, by
        simpa only [hk, ENat.toNat_natCast] using hend⟩
  rw [heq]
  exact MeasurableSet.iUnion fun k => measurableSet_of_past k _ (hA k)

private theorem univ_stopped_past (r ell k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      (Set.univ ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  simpa only [Set.univ_inter] using measurableSet_endpoint_slice r ell k

private theorem measurableSet_endpoint_event (r ell : ℕ) :
    MeasurableSet
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  simpa only [Set.univ_inter] using
    measurableSet_stopped_slice r ell Set.univ (univ_stopped_past r ell)

private theorem cond_test_factorization (r ell : ℕ) (A B : Set (ℕ → ℤ × ℤ))
    (hB : MeasurableSet B)
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    μ[|E] (A ∩ Y ⁻¹' B) = μ[|E] A * conditionedVectorPathLaw ell (-(r : ℤ)) B := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  change μ[|E] (A ∩ Y ⁻¹' B) = μ[|E] A * _
  rw [cond_apply (measurableSet_endpoint_event r ell),
    cond_apply (measurableSet_endpoint_event r ell)]
  have h := conditionedFirstHit_past_future_factorization r ell A B hB hA
  have hset : E ∩ (A ∩ Y ⁻¹' B) =
      A ∩ {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)} ∩
        {p | conditionedVectorShift (τ p).toNat p ∈ B} := by
    ext p
    simp only [E, Y, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  rw [hset, h]
  rw [Set.inter_comm E A]
  simp only [μ, τ, E, Set.inter_assoc, mul_assoc]



theorem conditionedFirstHit_endpoint_independent_events
    (r ell : ℕ) (_hr : 1 ≤ r) (_hell : 1 ≤ ell)
    (A B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B)
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E → μ[|E] (A ∩ Y ⁻¹' B) = μ[|E] A * μ[|E] (Y ⁻¹' B) := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have : IsProbabilityMeasure μ[|E] := cond_isProbabilityMeasure hpos.ne'
  have h := cond_test_factorization r ell A B hB hA
  have hu := cond_test_factorization r ell Set.univ B hB (univ_stopped_past r ell)
  simpa only [Set.univ_inter, measure_univ, one_mul] using h.trans
    (congrArg (fun q => μ[|E] A * q)
      (by simpa only [Set.univ_inter, measure_univ, one_mul] using hu.symm))

/-- uncentered whole future at the first hit of R = −r under the endpoint-conditioned
not the paper result. -/
theorem conditionedFirstHit_endpoint_future_law
    (r ell : ℕ) (_hr : 1 ≤ r) (_hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E → (μ[|E]).map Y = conditionedVectorPathLaw ell (-(r : ℤ)) := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have : IsProbabilityMeasure μ[|E] := cond_isProbabilityMeasure hpos.ne'
  ext B hB
  rw [Measure.map_apply (measurable_conditionedFirstHit_future r) hB]
  have hu := cond_test_factorization r ell Set.univ B hB (univ_stopped_past r ell)
  simpa only [Set.univ_inter, measure_univ, one_mul] using hu





theorem conditionedFirstHit_endpoint_indepFun
    {β : Type*} [MeasurableSpace β]
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) (X : (ℕ → ℤ × ℤ) → β)
    (hX : ∀ T : Set β, MeasurableSet T → ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (X ⁻¹' T ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E → IndepFun X Y μ[|E] := by
  dsimp only
  intro hpos
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro T B hT hB
  exact conditionedFirstHit_endpoint_independent_events r ell hr hell
    (X ⁻¹' T) B hB (hX T hT) hpos

private theorem aemeasurable_stopped_observable
    {β : Type*} [MeasurableSpace β]
    (r ell : ℕ) (X : (ℕ → ℤ × ℤ) → β)
    (hX : ∀ T : Set β, MeasurableSet T → ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (X ⁻¹' T ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    AEMeasurable X μ[|E] := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have hE : MeasurableSet E := measurableSet_endpoint_event r ell
  have hm : Measurable (fun p : E => X p) := by
    intro T hT
    have hs := measurableSet_stopped_slice r ell (X ⁻¹' T) (hX T hT)
    convert hs.preimage measurable_subtype_coe using 1
    ext p
    change X p.val ∈ T ↔ X p.val ∈ T ∧ p.val ∈ E
    simp only [p.property, and_true]
  have ha : AEMeasurable X (μ.restrict E) :=
    aemeasurable_restrict_of_measurable_subtype hE hm
  exact ha.mono_ac Measure.smul_absolutelyContinuous

/-- of the stopped past and the uncentered future at the first hit of R = −r under the
endpoint-conditioned UIQBOT law, and the a.e. conditional-distribution form; the
The equality is of whole measures on one simultaneous almost-everywhere event. -/
theorem conditionedFirstHit_endpoint_condDistrib
    {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [Nonempty β]
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) (X : (ℕ → ℤ × ℤ) → β)
    (hX : ∀ T : Set β, MeasurableSet T → ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (X ⁻¹' T ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E →
      condDistrib X Y μ[|E] =ᵐ[(μ[|E]).map Y] fun _ => (μ[|E]).map X := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  have hXm : AEMeasurable X μ[|E] := aemeasurable_stopped_observable r ell X hX
  have hYm : AEMeasurable Y μ[|E] :=
    (measurable_conditionedFirstHit_future r).aemeasurable
  have hI : IndepFun X Y μ[|E] :=
    conditionedFirstHit_endpoint_indepFun r ell hr hell X hX hpos
  have hk := condDistrib_ae_eq_of_measure_eq_compProd hYm hXm
    (κ := Kernel.const (ℕ → ℤ × ℤ) ((μ[|E]).map X)) (by
      rw [Measure.compProd_const]
      exact hI.symm.map_prod_eq_prod_map_map hYm hXm)
  exact hk

end DirectedDistances.RandomWalk
