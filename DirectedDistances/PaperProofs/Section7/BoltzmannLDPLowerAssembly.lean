/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section7.BoltzmannLDPUpper
public import DirectedDistances.Paper.Section3.BoltzmannFinite
public import DirectedDistances.Paper.Section7.UIQBOTBoltzmann
public import DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerSegment

/-! # Conditional assembly toward Lemma 7.11

The statement below mirrors Lemma 7.11 (`lem-boltzmann-ldp-lower`,
The reduction is conditional on the separate shifted-segment estimate (step 2);
neither definition nor conditional theorem is a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.Paper.Section7
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4

/-- Exact statement shape for the helper toward Lemma 7.11
paper result; the reduction to it is conditional on step 2. -/
def lemma711Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
            (ldpLengthBase q.1.2.2.out.B : ℝ)}

/-- The shifted-window event in step 2 of the proof of Lemma 7.11. Its stopping
time is the first hit of `-⌊r/2⌋`; the segment must end strictly before the
first hit of `-r`, as required to embed it into the stopped KMSW stage. -/
def lemma711Step2Event (A C : ℝ) (r : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {p | let T := boltzmannTau (r / 2) (pathCode p)
    let N := ⌊(r : ℝ) ^ 2 / C⌋₊
    T + N < boltzmannTau r (pathCode p) ∧
      ∃ a b : StagePresentVertex
        (fun i => boltzmannKMSWStream (pathCode p) (T + i)) N,
        ∃ s : Path a b,
          A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (s.length : ℝ)}

/-- Step-2 input toward Lemma 7.11 (`lem-boltzmann-ldp-lower`); not a paper
result. For each error tolerance, one pair of constants works for all
sufficiently large radii under the conditioned walk law. -/
def lemma711Step2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A C : ℝ, 1 < A ∧ 1 < C ∧ ∃ r₀ : ℕ,
    ∀ r : ℕ, r₀ ≤ r →
      1 - δ ≤ (conditionedVectorPathLaw 0 0).real (lemma711Step2Event A C r)

/-- Helper toward Lemma 7.11: the conditioned walk has nonnegative first
coordinate almost surely. -/
private theorem conditionedPath_firstCoordinate_nonnegative_ae :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ n, 0 ≤ (p n).1 := by
  unfold conditionedVectorPathLaw
  apply ae_map_iff (by fun_prop) (by measurability) |>.2
  exact Filter.Eventually.of_forall fun p n => Int.natCast_nonneg _

private theorem pathCode_mem_boltzmannEvent_of_legal
    (r : ℕ) (p : ℕ → ℤ × ℤ)
    (hlegal : p 0 = (0, 0) ∧
      ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hnonneg : ∀ n, 0 ≤ (p n).1)
    (htau : 0 < boltzmannTau r (pathCode p)) :
    pathCode p ∈ boltzmannEvent r := by
  have hhit : ∃ n, (codeWalk (pathCode p) n).2 = -(r : ℤ) := by
    by_contra hn
    have hzero : boltzmannTau r (pathCode p) = 0 := by
      simp [boltzmannTau, hn]
    omega
  refine ⟨boltzmannTau r (pathCode p), boltzmann_tau_spec r (pathCode p) hhit, ?_⟩
  intro j _
  have hdecode := congrArg Prod.fst (codeWalk_pathCode p hlegal.2 j)
  have hfirst : (codeWalk (pathCode p) j).1 = (p j).1 := by
    simpa [hlegal.1] using hdecode
  rw [hfirst]
  exact hnonneg j

/-- Conditional reduction toward Lemma 7.11. The only probabilistic premise is
the step-2 eventual shifted-segment estimate above. The deterministic
segment inclusion supplies the LDP bound; Lemma 7.9 transfers it to the marked
Boltzmann law. For the finitely many smaller radii, the right-boundary path
gives LDP at least one, and the common constant is enlarged accordingly. -/
theorem lemma711_of_step2 (h2 : lemma711Step2) : lemma711Statement := by
  intro δ hδ hδlt
  obtain ⟨A₀, C, hA₀, hC, r₀, hh2⟩ := h2 δ hδ
  let A := max A₀ ((r₀ : ℝ) ^ (3 / 2 : ℝ))
  have hA : 1 < A := lt_of_lt_of_le hA₀ (le_max_left _ _)
  have hApos : 0 < A := lt_trans zero_lt_one hA
  refine ⟨A, hA, fun r hr => ?_⟩
  let S : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
      (ldpLengthBase q.1.2.2.out.B : ℝ)}
  change 1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real S
  by_cases hlarge : r₀ ≤ r
  · let E := lemma711Step2Event A₀ C r
    let L : Set (ℕ → ℤ × ℤ) := {p |
      p 0 = (0, 0) ∧
      (∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) ∧
      ∀ n, 0 ≤ (p n).1}
    have hlegalAE : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, p ∈ L := by
      filter_upwards [conditionedVectorPathLaw_ae_legal,
        conditionedPath_firstCoordinate_nonnegative_ae] with p hp hn
      exact ⟨hp.1, hp.2, hn⟩
    have hnull : (conditionedVectorPathLaw 0 0).real Lᶜ = 0 := by
      have hnull' : conditionedVectorPathLaw 0 0 Lᶜ = 0 := ae_iff.mp hlegalAE
      simp [Measure.real, hnull']
    have hpre :
        E ⊆ {p | stoppedMarked r hr p ∈ S} ∪ Lᶜ := by
      intro p hp
      by_cases hpL : p ∈ L
      · left
        simp only [E, lemma711Step2Event, Set.mem_ofPred_eq] at hp
        rcases hp with ⟨hTN, a, b, s, hpath⟩
        rcases hpL with ⟨hp0, hpstep, hpnonneg⟩
        have htau : 0 < boltzmannTau r (pathCode p) := by omega
        have hE : pathCode p ∈ boltzmannEvent r :=
          pathCode_mem_boltzmannEvent_of_legal r p ⟨hp0, hpstep⟩ hpnonneg htau
        have hseg := ldpLower_halfHit_segment r hr p hE
          ⌊(r : ℝ) ^ 2 / C⌋₊ s.length hTN ⟨a, b, s, rfl⟩
        have hnat : s.length ≤
            ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B :=
          (WithBot.coe_le_coe).mp hseg
        have hreal : (s.length : ℝ) ≤
            (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : ℝ) := by
          exact_mod_cast hnat
        have hA₀pos : 0 < A₀ := lt_trans zero_lt_one hA₀
        have hA₀A : A₀ ≤ A := le_max_left _ _
        have hinv : A⁻¹ ≤ A₀⁻¹ := (inv_le_inv₀ hApos hA₀pos).2 hA₀A
        have hpow_nonneg : 0 ≤ (r : ℝ) ^ (3 / 2 : ℝ) := by positivity
        change A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
          (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : ℝ)
        calc
          A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
              A₀⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hinv hpow_nonneg
          _ ≤ (s.length : ℝ) := hpath
          _ ≤ (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : ℝ) := hreal
      · exact Or.inr hpL
    have hgood : 1 - δ ≤
        (conditionedVectorPathLaw 0 0).real E := hh2 r hlarge
    have hpreProb : 1 - δ ≤
        (conditionedVectorPathLaw 0 0).real {p | stoppedMarked r hr p ∈ S} := by
      calc
        1 - δ ≤ (conditionedVectorPathLaw 0 0).real E := hgood
        _ ≤ (conditionedVectorPathLaw 0 0).real
            ({p | stoppedMarked r hr p ∈ S} ∪ Lᶜ) := measureReal_mono hpre
        _ ≤ (conditionedVectorPathLaw 0 0).real
              {p | stoppedMarked r hr p ∈ S} +
            (conditionedVectorPathLaw 0 0).real Lᶜ :=
          measureReal_union_le (μ := conditionedVectorPathLaw 0 0) _ _
        _ = (conditionedVectorPathLaw 0 0).real
              {p | stoppedMarked r hr p ∈ S} := by rw [hnull]; ring
    have hmeas : MeasurableSet S := by
      change MeasurableSet[⊤] S
      exact MeasurableSpace.measurableSet_top
    have hmapreal :
        (conditionedVectorPathLaw 0 0).real
          {p | stoppedMarked r hr p ∈ S} =
        (rightVertexMarkedBoltzmannLaw r).real S := by
      have hlaw := (uiqbot_boltzmann).1 r hr
      change ENNReal.toReal
          (conditionedVectorPathLaw 0 0 {p | stoppedMarked r hr p ∈ S}) =
        ENNReal.toReal ((rightVertexMarkedBoltzmannLaw r) S)
      rw [← hlaw, Measure.map_apply (measurable_stoppedMarked r hr) hmeas]
      rfl
    exact hpreProb.trans_eq hmapreal
  · have hrlt : r < r₀ := Nat.lt_of_not_ge hlarge
    have hprob : IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r) :=
      DirectedDistances.Paper.Section3.boltzmann_finite r hr |>.2.2.2
    have hrr₀ : (r : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast (Nat.le_of_lt hrlt)
    have hrnonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
    have hpow : (r : ℝ) ^ (3 / 2 : ℝ) ≤ (r₀ : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hrnonneg hrr₀ (by norm_num)
    have hpowA : (r : ℝ) ^ (3 / 2 : ℝ) ≤ A := hpow.trans (le_max_right _ _)
    have hratio : A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ 1 := by
      calc
        A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) =
            (r : ℝ) ^ (3 / 2 : ℝ) / A := by rw [div_eq_mul_inv]; ring
        _ ≤ 1 := (div_le_one₀ hApos).2 hpowA
    have hfull : S = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro q
      have hldp : 1 ≤ ldpLengthBase q.1.2.2.out.B :=
        (show 1 ≤ r from hr).trans (le_ldpLengthBase q.1.2.2.out.B
          q.1.2.2.out.B.rightPath)
      have hldpReal : (1 : ℝ) ≤ (ldpLengthBase q.1.2.2.out.B : ℝ) := by
        exact_mod_cast hldp
      change A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
        (ldpLengthBase q.1.2.2.out.B : ℝ)
      exact hratio.trans hldpReal
    have hmass : (rightVertexMarkedBoltzmannLaw r).real Set.univ = 1 := by
      simp [Measure.real, hprob.measure_univ]
    rw [hfull, hmass]
    linarith

end DirectedDistances.PaperProofs.Section7
