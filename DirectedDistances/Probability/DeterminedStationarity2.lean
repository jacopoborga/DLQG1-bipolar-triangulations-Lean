module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Probability.Independence.Basic
public import DirectedDistances.Probability.SplitIndependenceComposition

/-! # Common laws and independence from determined observables -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- On an index set where the observable family `L` has a common law, a fixed
measurable function of `L` has a common law whenever it agrees almost
everywhere with `G`. The law and determination hypotheses remain explicit
obligations for any application. -/
theorem map_eq_of_ae_determined
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {L : ℤ → Ω → α} {G : ℤ → Ω → β}
    (S : Set ℤ) (k₀ : ℤ) (hk₀ : k₀ ∈ S)
    (Φ : α → β) (hΦ : Measurable Φ)
    (hL : ∀ k, AEMeasurable (L k) μ) (_hG : ∀ k, AEMeasurable (G k) μ)
    (hLaw : ∀ k ∈ S, μ.map (L k) = μ.map (L k₀))
    (hDet : ∀ k ∈ S, G k =ᵐ[μ] fun ω => Φ (L k ω)) :
    ∀ k ∈ S, μ.map (G k) = μ.map (G k₀) := by
  intro k hk
  calc
    μ.map (G k) = μ.map (fun ω => Φ (L k ω)) := Measure.map_congr (hDet k hk)
    _ = (μ.map (L k)).map Φ :=
      (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (hL k)).symm
    _ = (μ.map (L k₀)).map Φ :=
      congrArg (fun ν : Measure α => ν.map Φ) (hLaw k hk)
    _ = μ.map (fun ω => Φ (L k₀ ω)) :=
      AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (hL k₀)
    _ = μ.map (G k₀) := Measure.map_congr (hDet k₀ hk₀).symm

/-- If each slice at index `k ≥ 1` is almost everywhere a fixed measurable
function of the right-side observable at index `k - 1`, then the slices at
indices `k ≥ 1` have a common law, provided the right-side observables have a
common law at every index `j ≥ 0`. This law-agreement hypothesis is precisely
the right-side law clause of Lemma 5.5 in the intended application. It is an
explicit hypothesis of this generic helper, not an additional assumption of
Lemma 5.6. -/
theorem map_eq_of_ae_determined_right_range
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {R : ℤ → Ω → α} {G : ℤ → Ω → β}
    (Φ_R : α → β) (hΦ_R : Measurable Φ_R)
    (hR : ∀ j, AEMeasurable (R j) μ)
    (hLawR : ∀ j, 0 ≤ j → μ.map (R j) = μ.map (R 0))
    (hDetR : ∀ k, 1 ≤ k → G k =ᵐ[μ] fun ω => Φ_R (R (k - 1) ω)) :
    ∀ k, 1 ≤ k → μ.map (G k) = μ.map (G 1) := by
  intro k hk
  calc
    μ.map (G k) = μ.map (fun ω => Φ_R (R (k - 1) ω)) :=
      Measure.map_congr (hDetR k hk)
    _ = (μ.map (R (k - 1))).map Φ_R :=
      (AEMeasurable.map_map_of_aemeasurable hΦ_R.aemeasurable (hR (k - 1))).symm
    _ = (μ.map (R 0)).map Φ_R :=
      congrArg (fun ν : Measure α => ν.map Φ_R) (hLawR (k - 1) (by omega))
    _ = μ.map (fun ω => Φ_R (R 0 ω)) :=
      AEMeasurable.map_map_of_aemeasurable hΦ_R.aemeasurable (hR 0)
    _ = μ.map (G 1) := Measure.map_congr (hDetR 1 (by omega)).symm

/-- If each slice at index `k ≤ 0` is almost everywhere a fixed measurable
function of the left-side observable at index `k`, then the slices at indices
`k ≤ 0` have a common law, provided the left-side observables have a common
law at every index `k ≤ 0`. This law-agreement hypothesis is precisely the
left-side law clause of Lemma 5.5 in the intended application. It is an
explicit hypothesis of this generic helper, not an additional assumption of
Lemma 5.6. -/
theorem map_eq_of_ae_determined_left_range
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {L : ℤ → Ω → α} {G : ℤ → Ω → β}
    (Φ_L : α → β) (hΦ_L : Measurable Φ_L)
    (hL : ∀ k, AEMeasurable (L k) μ)
    (hLawL : ∀ k, k ≤ 0 → μ.map (L k) = μ.map (L 0))
    (hDetL : ∀ k, k ≤ 0 → G k =ᵐ[μ] fun ω => Φ_L (L k ω)) :
    ∀ k, k ≤ 0 → μ.map (G k) = μ.map (G 0) := by
  intro k hk
  calc
    μ.map (G k) = μ.map (fun ω => Φ_L (L k ω)) :=
      Measure.map_congr (hDetL k hk)
    _ = (μ.map (L k)).map Φ_L :=
      (AEMeasurable.map_map_of_aemeasurable hΦ_L.aemeasurable (hL k)).symm
    _ = (μ.map (L 0)).map Φ_L :=
      congrArg (fun ν : Measure α => ν.map Φ_L) (hLawL k hk)
    _ = μ.map (fun ω => Φ_L (L 0 ω)) :=
      AEMeasurable.map_map_of_aemeasurable hΦ_L.aemeasurable (hL 0)
    _ = μ.map (G 0) := Measure.map_congr (hDetL 0 (by omega)).symm

/-- For a probability measure, suppose that at every integer cut the two side
observables are independent, measurable functions of the left and right side
observables recover the corresponding past and future restrictions of an
indexed family almost everywhere, and every member of that family is
measurable. Then the indexed family is mutually independent. The per-cut
independence, measurable reconstruction maps, almost-everywhere
determinations, and measurability hypotheses are all explicit here; they
remain obligations in a slice application. -/
theorem iIndepFun_of_independent_cut_sides
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → β}
    {α γ : ℤ → Type*}
    [mα : ∀ k, MeasurableSpace (α k)] [mγ : ∀ k, MeasurableSpace (γ k)]
    (A : ∀ k, Ω → α k) (B : ∀ k, Ω → γ k)
    (hAB : ∀ k, IndepFun (A k) (B k) μ)
    (F : ∀ k, α k → (∀ _j : {j : ℤ // j ≤ k}, β))
    (G : ∀ k, γ k → (∀ _j : {j : ℤ // k + 1 ≤ j}, β))
    (hF : ∀ k, Measurable (F k)) (hG : ∀ k, Measurable (G k))
    (hdetL : ∀ k,
      (fun ω (j : {j : ℤ // j ≤ k}) => X j ω) =ᵐ[μ] fun ω => F k (A k ω))
    (hdetR : ∀ k,
      (fun ω (j : {j : ℤ // k + 1 ≤ j}) => X j ω) =ᵐ[μ] fun ω => G k (B k ω))
    (hX : ∀ j, Measurable (X j)) :
    iIndepFun X μ :=
  iIndepFun_of_cut_determination A B hAB F G hF hG hdetL hdetR hX

end DirectedDistances.Probability
end
