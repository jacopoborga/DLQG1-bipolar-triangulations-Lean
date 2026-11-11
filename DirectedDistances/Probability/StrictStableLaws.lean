module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-lower`, `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/









public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory






@[expose] def SymmetricStrictStableLaw (α c : ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ 0 < c ∧
    ∀ u : ℝ, charFun μ u = Complex.exp (-(c * |u| ^ α : ℝ))






@[expose] def SpectrallyPositiveStableLaw (α c : ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  1 < α ∧ α < 2 ∧ 0 < c ∧
    ∀ u : ℝ, charFun μ u = Complex.exp
      (-((c * |u| ^ α : ℝ) : ℂ) *
        (1 - Complex.I *
          (((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) *
            Real.tan (Real.pi * α / 2) : ℝ) : ℂ)))







@[expose] def StableSubordinatorLaw (α c : ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 0 < c ∧
    (μ : Measure ℝ) (Set.Iio 0) = 0 ∧
    ∀ u : ℝ, charFun μ u = Complex.exp
      (-((c * |u| ^ α : ℝ) : ℂ) *
        (1 - Complex.I *
          (((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) *
            Real.tan (Real.pi * α / 2) : ℝ) : ℂ)))




theorem symmetric_strict_stable_law_unique {α c : ℝ} {μ ν : ProbabilityMeasure ℝ}
    (hμ : SymmetricStrictStableLaw α c μ) (hν : SymmetricStrictStableLaw α c ν) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext u
  exact (hμ.2.2.2 u).trans (hν.2.2.2 u).symm




theorem spectrally_positive_stable_law_unique {α c : ℝ}
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ)
    (hν : SpectrallyPositiveStableLaw α c ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext u
  exact (hμ.2.2.2 u).trans (hν.2.2.2 u).symm




theorem stable_subordinator_law_unique {α c : ℝ} {μ ν : ProbabilityMeasure ℝ}
    (hμ : StableSubordinatorLaw α c μ) (hν : StableSubordinatorLaw α c ν) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext u
  exact (hμ.2.2.2.2 u).trans (hν.2.2.2.2 u).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv) and Lemma 7.12
(lem-boltzmann-sdp-lower); not a paper result. -/
private theorem charFun_map_finOne_firstCoord
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) (u : ℝ) :
    charFun (μ.map (fun z => z (0 : Fin 1))) u =
      charFun μ (EuclideanSpace.single (0 : Fin 1) u) := by
  let p : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (β := fun _ : Fin 1 => ℝ) 0
  have hp : (fun z : EuclideanSpace ℝ (Fin 1) => z (0 : Fin 1)) = p := by
    funext z
    rfl
  rw [hp, charFun_map_eq_charFunDual_smul]
  have hdual : u • p =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace.single (0 : Fin 1) u) := by
    ext z
    simp [p, EuclideanSpace.inner_single_left]
  rw [hdual, ← charFun_eq_charFunDual_toDualMap]






theorem sdp_one_coordinate_marginal_spectrally_positive
    {b : ℝ} (hb : 0 < b) {κ : ℂ}
    (hκ : κ = ((1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) * (b : ℂ))
    (μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)))
    (hchar : ∀ θ : EuclideanSpace ℝ (Fin 1),
      charFun (μlim : Measure _) θ = ∏ i : Fin 1, Complex.exp
        (-((1 : ℂ) * ((if 0 ≤ θ i then κ else star κ) *
          (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) :
    SpectrallyPositiveStableLaw (4 / 3) (b / 2)
      (μlim.map (fun z => z (0 : Fin 1))) := by
  have htan : Real.tan (Real.pi * (4 / 3 : ℝ) / 2) = -Real.sqrt 3 := by
    calc
      _ = Real.tan (Real.pi - Real.pi / 3) := by congr 1; ring
      _ = -Real.tan (Real.pi / 3) := Real.tan_pi_sub _
      _ = -Real.sqrt 3 := by rw [Real.tan_pi_div_three]
  have hκ' : κ = ((b / 2 : ℝ) : ℂ) *
      (1 + (Real.sqrt 3 : ℂ) * Complex.I) := by
    rw [hκ]
    push_cast
    ring
  refine ⟨by norm_num, by norm_num, by positivity, ?_⟩
  intro u
  have hchar1 : charFun (μlim : Measure _)
      (EuclideanSpace.single (0 : Fin 1) u) =
      Complex.exp (-((if 0 ≤ u then κ else star κ) *
        (|u| ^ (4 / 3 : ℝ) : ℝ))) := by
    simpa using hchar (EuclideanSpace.single (0 : Fin 1) u)
  change charFun
    ((μlim : Measure (EuclideanSpace ℝ (Fin 1))).map
      (fun z : EuclideanSpace ℝ (Fin 1) => z (0 : Fin 1))) u = _
  rw [charFun_map_finOne_firstCoord]
  rw [hchar1]
  congr 1
  by_cases hu : u = 0
  · subst u
    simp [Real.zero_rpow, (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  · rcases lt_or_gt_of_ne hu with hul | hug
    · have hnotpos : ¬ 0 < u := not_lt.mpr (le_of_lt hul)
      simp [not_le_of_gt hul, abs_of_neg hul, hκ', htan, hul, hnotpos]
      ring
    · simp [le_of_lt hug, abs_of_pos hug, hκ', htan, hug]
      ring

end DirectedDistances.Probability
