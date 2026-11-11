module

public import DirectedDistances.Recursive.BusemannWindowLimitSDP
import Mathlib.Probability.Independence.CharacteristicFunction

/- # Negative excursions in SDP window limits

Helpers toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
This file does not prove that a weak-limit path has negative values -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter WithLp
open DirectedDistances.RandomWalk
open DirectedDistances.Probability
open scoped Topology ENNReal

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Every weak limit has the stable finite-dimensional laws already established for
This file does not prove that a weak-limit path has negative values -/
theorem sdp_busemann_window_limit_fdd
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      (⟨1, by norm_num, le_rfl⟩ : J1Window 1) ∈ S ∧
      ∀ (m : ℕ) (t : ℕ → J1Window 1), (t 0 : ℝ) = 0 → Monotone t →
        (∀ i : Fin m, t (i.val + 1) ∈ S) →
        let b : ℝ := (SDPMasterFromLaw.sdpG μ Y (-1)) ^ (2 / 3 : ℝ)
        let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
        0 < b ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
          (∀ θ : EuclideanSpace ℝ (Fin m),
            charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
              (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                ((if 0 ≤ θ i then κ else star κ) *
                  (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
          ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
            (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  obtain ⟨ν', hν', S, hS, hEnd, hfdd⟩ :=
    sdp_busemann_window_tendsto hind hsym (by norm_num : (0 : ℝ) < 1)
  have hEq : ν = ν' := tendsto_nhds_unique hν hν'
  subst ν'
  exact ⟨S, hS, hEnd, hfdd⟩

private theorem sdp_charFun_map_fin_coordinate
    {m : ℕ} (L : Measure (EuclideanSpace ℝ (Fin m))) (i : Fin m) (u : ℝ) :
    charFun (L.map (fun z : EuclideanSpace ℝ (Fin m) => z i)) u =
      charFun L (EuclideanSpace.single i u) := by
  let p : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (β := fun _ : Fin m => ℝ) i
  have hp : (fun z : EuclideanSpace ℝ (Fin m) => z i) = p := by
    funext z
    rfl
  rw [hp, charFun_map_eq_charFunDual_smul]
  have hdual : u • p =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i u) := by
    ext z
    simp [p, EuclideanSpace.inner_single_left]
  rw [hdual, ← charFun_eq_charFunDual_toDualMap]

private theorem sdp_fdd_increment_coordinates_indep
    {m : ℕ} {t : ℕ → J1Window 1} {L : ProbabilityMeasure
      (EuclideanSpace ℝ (Fin m))} {κ : ℂ}
    (hchar : ∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ =
      ∏ i : Fin m, Complex.exp
        (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κ else star κ) *
            (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) :
    iIndepFun (fun i (z : EuclideanSpace ℝ (Fin m)) => z i) (L : Measure _) := by
  apply (iIndepFun_iff_charFun_pi (fun i => by fun_prop)).2
  intro θ
  have hjoint : (L : Measure (EuclideanSpace ℝ (Fin m))).map
      (fun z : EuclideanSpace ℝ (Fin m) => toLp 2 (fun i : Fin m => z i)) =
      (L : Measure _) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin m) =>
        toLp 2 (fun i : Fin m => z i)) = id by
      funext z
      ext i
      rfl]
    exact Measure.map_id
  have hcoord (i : Fin m) (u : ℝ) :
      charFun ((L : Measure _).map (fun z : EuclideanSpace ℝ (Fin m) => z i)) u =
        Complex.exp (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
          ((if 0 ≤ u then κ else star κ) * (|u| ^ (4 / 3 : ℝ) : ℝ)))) := by
    rw [sdp_charFun_map_fin_coordinate]
    rw [hchar (EuclideanSpace.single i u)]
    rw [Finset.prod_eq_single i]
    · simp [EuclideanSpace.single]
    · intro j hj hji
      simp [EuclideanSpace.single, hji]
    · simp
  calc
    charFun ((L : Measure _).map
        (fun z : EuclideanSpace ℝ (Fin m) => toLp 2 (fun i : Fin m => z i))) θ =
        charFun (L : Measure _) θ := by
      rw [hjoint]
    _ = ∏ i : Fin m, Complex.exp
        (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κ else star κ) *
            (|θ i| ^ (4 / 3 : ℝ) : ℝ)))) := hchar θ
    _ = ∏ i : Fin m,
        charFun ((L : Measure _).map (fun z : EuclideanSpace ℝ (Fin m) => z i))
          (θ i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hcoord i (θ i)).symm

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The increment coordinates in each finite-dimensional SDP window law are independent.
This file does not prove that a weak-limit path has negative values -/
theorem sdp_busemann_window_limit_fdd_indep_increments
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      (⟨1, by norm_num, le_rfl⟩ : J1Window 1) ∈ S ∧
      ∀ (m : ℕ) (t : ℕ → J1Window 1), (t 0 : ℝ) = 0 → Monotone t →
        (∀ i : Fin m, t (i.val + 1) ∈ S) →
        let b : ℝ := (SDPMasterFromLaw.sdpG μ Y (-1)) ^ (2 / 3 : ℝ)
        let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
        0 < b ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
          (∀ θ : EuclideanSpace ℝ (Fin m),
            charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
              (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                ((if 0 ≤ θ i then κ else star κ) *
                  (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
          iIndepFun (fun i (z : EuclideanSpace ℝ (Fin m)) => z i)
            (L : Measure _) ∧
          ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
            (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  obtain ⟨S, hS, hEnd, hfdd⟩ := sdp_busemann_window_limit_fdd hind hsym hν
  refine ⟨S, hS, hEnd, ?_⟩
  intro m t ht0 htm htS
  obtain ⟨hb, L, hchar, hEval⟩ := hfdd m t ht0 htm htS
  refine ⟨hb, L, hchar, ?_, hEval⟩
  exact sdp_fdd_increment_coordinates_indep hchar

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
A negative value at one interior time belongs to the negative-excursion event.
This file does not prove that a weak-limit path has negative values -/
theorem sdp_window_negative_excursion_ge_time
    (ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)))
    (t : J1Window 1) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x | x.path.1 t < 0} ≤
      (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧
            x.path.1 s < 0} := by
  apply measureReal_mono
  · intro x hx
    exact ⟨t, ht0, ht1, hx⟩
  · exact measure_ne_top _ _

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Positive mass at one interior time gives positive mass to a negative excursion.
This file does not prove that a weak-limit path has negative values -/
theorem sdp_window_negative_excursion_pos_of_time
    (ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)))
    (t : J1Window 1) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hneg : 0 < (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x | x.path.1 t < 0}) :
    0 < (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x.path.1 s < 0} :=
  lt_of_lt_of_le hneg (sdp_window_negative_excursion_ge_time ν t ht0 ht1)

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The germ event has probability one once it has positive mass and its probability
This file does not prove that a weak-limit path has negative values -/
theorem sdp_window_negative_germ_eq_one_of_zero_one
    (ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)))
    (hpos : 0 < (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0})
    (hzeroone : (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 0 ∨
      (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∀ n : ℕ, ∃ s : J1Window 1,
            0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1) :
    (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1 := by
  rcases hzeroone with hzero | hone
  · exact False.elim ((ne_of_gt hpos) hzero)
  · exact hone

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Self-independence of the negative germ event gives its zero-one alternative.
This file does not prove that a weak-limit path has negative values -/
theorem sdp_window_negative_germ_zero_or_one_of_self_indep
    (ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)))
    (hInd : ProbabilityTheory.IndepSet
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
      (ν : Measure (J1WindowD 1 (by norm_num)))) :
    (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 0 ∨
    (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1 := by
  let G : Set (J1WindowD 1 (by norm_num)) := {x |
    ∀ n : ℕ, ∃ s : J1Window 1,
      0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
  have hmul := hInd.measure_inter_eq_mul
  have hreal : (ν : Measure (J1WindowD 1 (by norm_num))).real G =
      ((ν : Measure (J1WindowD 1 (by norm_num))).real G) ^ 2 := by
    have h := congrArg ENNReal.toReal hmul
    simpa [G, measureReal_def, Set.inter_self, ENNReal.toReal_mul,
      measure_ne_top, pow_two] using h
  have hnonneg : 0 ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real G :=
    measureReal_nonneg
  have hle : (ν : Measure (J1WindowD 1 (by norm_num))).real G ≤ 1 :=
    measureReal_le_one
  rcases eq_or_ne ((ν : Measure (J1WindowD 1 (by norm_num))).real G) 0 with h0 | h0
  · exact Or.inl (by simpa [G] using h0)
  · right
    have hpos : 0 < (ν : Measure (J1WindowD 1 (by norm_num))).real G :=
      lt_of_le_of_ne hnonneg (Ne.symm h0)
    have hone : (ν : Measure (J1WindowD 1 (by norm_num))).real G = 1 := by
      nlinarith [hreal, hpos, hle]
    simpa [G] using hone

/- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Every path with negative values arbitrarily near zero has a negative value in
This file does not prove that a weak-limit path has negative values -/
theorem sdp_window_negative_excursion_eq_one_of_germ_eq_one
    (ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)))
    (hgerm : (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1) :
    (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x.path.1 s < 0} = 1 := by
  apply le_antisymm
  · calc
      _ ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
      _ = 1 := by simp
  · have hsub :
        {x : J1WindowD 1 (by norm_num) |
          ∀ n : ℕ, ∃ s : J1Window 1,
            0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} ⊆
        {x : J1WindowD 1 (by norm_num) |
          ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x.path.1 s < 0} := by
      intro x hx
      obtain ⟨s, hs0, hs1, hneg⟩ := hx 1
      refine ⟨s, hs0, ?_, hneg⟩
      norm_num at hs1
      linarith
    have hge : (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∀ n : ℕ, ∃ s : J1Window 1,
            0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧
              x.path.1 s < 0} ≤
      (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x.path.1 s < 0} := by
      exact measureReal_mono hsub (measure_ne_top _ _)
    rw [hgerm] at hge
    exact hge

end DirectedDistances.Recursive
