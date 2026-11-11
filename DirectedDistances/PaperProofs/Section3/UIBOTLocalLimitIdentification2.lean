/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization2
public import DirectedDistances.PaperProofs.Section3.UIBOTRootWindowConcentration
public import DirectedDistances.PaperProofs.Section3.UIBOTSubexponentialConditioning
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Independence.InfinitePi

/-! # Actual finite root-window convergence toward Proposition 3.9

The proved subexponential admissibility bound removes the denominator premise
from concentration. Bounded empirical frequencies then give convergence of the
actual optional finite-map window law along every nonempty size sequence.
This does not identify the geometric local topology local-limit law. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators

section WordLaw

local instance : MeasurableSpace (Fin 3) := ⊤

private instance uibotWordLaw_probability (n : ℕ) :
    IsProbabilityMeasure (uibotFiniteIIDWordLaw n) := by
  rw [uibotFiniteIIDWordLaw_eq_uniform]
  constructor
  simp [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_univ, ENat.card_eq_coe_fintype_card, ENNReal.inv_mul_cancel]

/-- Helper toward Proposition 3.9: empirical pattern deviations vanish under
the actual admissible word law, with the subexponential denominator bound
discharged by its proof and no added probability premise. -/
theorem uibotFiniteIIDWordLaw_cond_rootWindow_tendsto_zero
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (m : ℕ) (v : Fin (2 * m) → Fin 3) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ =>
      ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).real
        {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
          n - (3 : ℝ)^(-((2 * m : ℕ) : ℤ))|}) atTop (𝓝 0) :=
  uibotFiniteIIDWordLaw_cond_rootWindow_tendsto_zero_of_subexponential
    ℓ ρ m v δ hδ (uibotFiniteIIDWordLaw_admissible_subexponential ℓ ρ hℓ hρ)

private theorem finite_integral_abs_sub_le_deviation
    {Ω : Type*} [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (p δ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hδ : 0 ≤ δ)
    (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) :
    |(∫ x, X x ∂μ) - p| ≤ δ + μ.real {x | δ ≤ |X x - p|} := by
  classical
  let A := {x | δ ≤ |X x - p|}
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hpoint (x : Ω) : |X x - p| ≤ δ + A.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hb : |X x - p| ≤ 1 := abs_le.mpr ⟨by linarith [(hX x).1],
        by linarith [(hX x).2]⟩
      linarith
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact le_of_lt (lt_of_not_ge hx)
  calc
    |(∫ x, X x ∂μ) - p| = |∫ x, X x - p ∂μ| := by
      rw [integral_sub Integrable.of_finite (integrable_const p)]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ ∫ x, |X x - p| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => X x - p)
    _ ≤ ∫ x, δ + A.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = δ + μ.real A := by
      rw [integral_add (integrable_const δ) Integrable.of_finite,
        integral_const, integral_indicator_const 1 hA]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one,
        smul_eq_mul, mul_one, one_mul]

/-- Helper toward Proposition 3.9: the real pattern mass of the actual
finite uniform-map window is the mean empirical frequency over all edge roots. -/
theorem uibotFiniteRootWindowLaw_pattern_mass_real
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) (v : Fin (2 * m) → Fin 3) :
    letI : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
    (uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m).real {some v} =
      ∫ w, (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
        n ∂(uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}] := by
  let : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
  rw [measureReal_def, uibotFiniteRootWindowLaw_pattern_mass]
  rw [← integral_toReal (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => ENNReal.div_lt_top (by finiteness)
      (by exact_mod_cast (show n ≠ 0 by omega)))]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- Helper toward Proposition 3.9: the empirical frequency lies in the unit
interval even when some roots have unavailable windows; normalization uses all roots. -/
theorem uibotFiniteRootWindow_frequency_bounds {n m : ℕ}
    (w : Fin (n - 1) → Fin 3) (v : Fin (2 * m) → Fin 3) :
    0 ≤ (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) / n ∧
      (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) / n ≤ 1 := by
  classical
  have hc : Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} ≤ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Fintype.card_le_of_injective
        (fun j : {j : Fin n // uibotFiniteRootWindow m w j = some v} => j.val)
        Subtype.val_injective
  refine ⟨div_nonneg (by positivity) (by positivity), ?_⟩
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, div_zero, zero_le_one]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hn))).mpr
    exact_mod_cast hc

/-- Helper toward Proposition 3.9: every fixed optional window pattern has
the iid limiting mass along every diverging sequence of nonempty finite map
sizes. The source finite map law and its all-edge Peano root are used exactly. -/
theorem uibotFiniteRootWindowLaw_pattern_tendsto
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (m : ℕ) (v : Fin (2 * m) → Fin 3) :
    letI : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
    Tendsto (fun k =>
      (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) m).real {some v})
      atTop (𝓝 ((3 : ℝ)^(-((2 * m : ℕ) : ℤ)))) := by
  let : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
  have hp : 0 ≤ (3 : ℝ)^(-((2 * m : ℕ) : ℤ)) ∧
      (3 : ℝ)^(-((2 * m : ℕ) : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    constructor
    · positivity
    · exact pow_le_one₀ (by norm_num) (by norm_num)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht := (uibotFiniteIIDWordLaw_cond_rootWindow_tendsto_zero
    ℓ ρ hℓ hρ m v (ε / 2) (half_pos hε)).comp hns
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨K, fun k hk => ?_⟩
  rw [Real.dist_eq, uibotFiniteRootWindowLaw_pattern_mass_real]
  have hpos := uibotFiniteIIDWordLaw_admissible_pos ℓ ρ (ns k) (hsize k) (hne k)
  let μ := (uibotFiniteIIDWordLaw (ns k))[|{w | KMSWWalkAdmissible ℓ ρ (ns k) w}]
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure hpos.ne'
  have hb := finite_integral_abs_sub_le_deviation μ
    (fun w => (Nat.card {j : Fin (ns k) // uibotFiniteRootWindow m w j = some v} : ℝ) /
      ns k) _ (ε / 2) hp (half_pos hε).le
    (fun w => uibotFiniteRootWindow_frequency_bounds w v)
  have hsmall := hK k hk
  dsimp only [Function.comp_def] at hsmall
  exact hb.trans_lt (by linarith only [hsmall])

/-- Helper toward Proposition 3.9: the actual optional finite window law
is a probability measure, including its separate unavailable-window outcome. -/
theorem uibotFiniteRootWindowLaw_probability
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) :
    letI : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
    IsProbabilityMeasure (uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m) := by
  let : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
  let : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
  let : MeasurableSpace (Fin n) := ⊤
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := uibotFiniteUniformSampleLaw_probability ℓ ρ n hℓ hρ hn hne
  unfold uibotFiniteRootWindowLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable _).aemeasurable).mpr inferInstance

/-- Helper toward Proposition 3.9: the centered whole-plane iid window has
exactly the uniform pattern mass appearing in the finite-window limit. -/
theorem wholePlaneIID_rootWindow_pattern_real (m : ℕ) (v : Fin (2 * m) → Fin 3) :
    wholePlaneIIDCodeMeasure.real
      {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) = v} =
        (3 : ℝ)^(-((2 * m : ℕ) : ℤ)) := by
  let f : (ℤ → Fin 3) → (Fin (2 * m) → Fin 3) :=
    fun W i => shiftedStream W m i.val
  have hf : Measurable f := Measurable.of_eval fun i => measurable_pi_apply _
  have hi : Function.Injective (fun i : Fin (2 * m) => (i.val : ℤ) - m) := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast (sub_left_injective hij : (i.val : ℤ) = j.val)
  have hmap : wholePlaneIIDCodeMeasure.map f =
      Measure.pi (fun _ : Fin (2 * m) => uniformCodeMeasure) := by
    rw [← Measure.infinitePi_eq_pi]
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℤ => uniformCodeMeasure) hi
  have hs (a : Fin 3) : uniformCodeMeasure {a} = (3 : ℝ≥0∞)⁻¹ := by
    simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]
  change (wholePlaneIIDCodeMeasure (f ⁻¹' {v})).toReal = _
  rw [← Measure.map_apply hf (measurableSet_singleton _), hmap, Measure.pi_singleton]
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    zpow_neg, zpow_natCast, inv_pow]

/-- Helper toward Proposition 3.9: every event determined by a fixed successful
root window has its actual whole-plane iid limiting probability. This includes
the measurable finite capture certificates; it assumes no geometric comparison. -/
theorem uibotFiniteRootWindowLaw_event_tendsto
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (m : ℕ) (A : Set (Fin (2 * m) → Fin 3)) :
    letI : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
    Tendsto (fun k =>
      (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) m).real
        (Option.some '' A)) atTop
      (𝓝 (wholePlaneIIDCodeMeasure.real
        {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) ∈ A})) := by
  classical
  let : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
  let : Fintype A := Fintype.ofFinite A
  let μ k := uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) m
  let : ∀ k, IsProbabilityMeasure (μ k) := fun k =>
    uibotFiniteRootWindowLaw_probability ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) m
  have hA : Option.some '' A = ⋃ v : A, {some v.val} := by
    ext a
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
  have hdis : Pairwise (fun v z : A => Disjoint ({some v.val} : Set (Option _))
      {some z.val}) := by
    intro v z hvz
    rw [Set.disjoint_singleton]
    exact fun h => hvz (Subtype.ext (Option.some.inj h))
  have hmass (k : ℕ) : (μ k).real (Option.some '' A) =
      ∑ v : A, (μ k).real {some v.val} := by
    rw [hA]
    exact measureReal_iUnion_fintype hdis (fun _ => measurableSet_singleton _)
  have hW : {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) ∈ A} =
      ⋃ v : A, {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) = v.val} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨v, hv⟩ => hv ▸ v.property⟩
  have hdisW : Pairwise (fun v z : A => Disjoint
      {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) = v.val}
      {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) = z.val}) := by
    intro v z hvz
    apply Set.disjoint_left.mpr
    intro W hv hz
    exact hvz (Subtype.ext (hv.symm.trans hz))
  have hmeas (v : A) : MeasurableSet
      {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) = v.val} := by
    exact (measurableSet_singleton v.val).preimage
      (Measurable.of_eval fun i => measurable_pi_apply _)
  have hlimit : wholePlaneIIDCodeMeasure.real
      {W | (fun i : Fin (2 * m) => shiftedStream W m i.val) ∈ A} =
      ∑ _v : A, (3 : ℝ)^(-((2 * m : ℕ) : ℤ)) := by
    rw [hW, measureReal_iUnion_fintype hdisW hmeas]
    exact Finset.sum_congr rfl (fun v _ => wholePlaneIID_rootWindow_pattern_real m v.val)
  simp_rw [show (fun k => (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ
      (hsize k) (hne k) m).real (Option.some '' A)) =
      (fun k => ∑ v : A, (μ k).real {some v.val}) from funext hmass, hlimit]
  exact tendsto_finsetSum Finset.univ (fun v _ =>
    uibotFiniteRootWindowLaw_pattern_tendsto ℓ ρ hℓ hρ ns hns hsize hne m v.val)

/-- Helper toward Proposition 3.9: the unavailable-window probability tends
to zero along every diverging nonempty size sequence, including all-edge rooting. -/
theorem uibotFiniteRootWindowLaw_none_tendsto_zero
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) (m : ℕ) :
    letI : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
    Tendsto (fun k =>
      (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) m).real {none})
      atTop (𝓝 0) := by
  let : MeasurableSpace (Option (Fin (2 * m) → Fin 3)) := ⊤
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun k => uibotFiniteRootWindowLaw_none_bound_real ℓ ρ (ns k) hℓ hρ
      (hsize k) (hne k) m)
    ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * m : ℕ)).comp hns)

/-- Helper toward Proposition 3.9: the finite set of window patterns whose
literal finite extension certifies strong capture at the chronological root. -/
@[expose] def uibotRootCapturePatterns (N r : ℕ) : Set (Fin (2 * N) → Fin 3) :=
  {v | UIBOTRootWindowCapture (finiteCodeExtend (n := 2 * N + 1) v) N r}

/-- Helper toward Proposition 3.9: the pattern predicate is equivalent to
capture of the original stream, because the certificate uses only its window. -/
theorem uibotRootCapturePatterns_iff (W : ℤ → Fin 3) (N r : ℕ) :
    (fun i : Fin (2 * N) => shiftedStream W N i.val) ∈ uibotRootCapturePatterns N r ↔
      UIBOTRootWindowCapture (shiftedStream W N) N r := by
  apply uibotRootWindowCapture_congr
  intro i hi
  simp only [finiteCodeExtend, Nat.add_sub_cancel, dite_eq_left hi]

/-- Helper toward Proposition 3.9: a fixed finite capture certificate has
the actual whole-plane limiting probability under the finite uniform-map law. -/
theorem uibotFiniteRootWindowLaw_capture_tendsto
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) (N r : ℕ) :
    letI : MeasurableSpace (Option (Fin (2 * N) → Fin 3)) := ⊤
    Tendsto (fun k =>
      (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) N).real
        (Option.some '' uibotRootCapturePatterns N r)) atTop
      (𝓝 (wholePlaneIIDCodeMeasure.real
        {W | UIBOTRootWindowCapture (shiftedStream W N) N r})) := by
  let : MeasurableSpace (Option (Fin (2 * N) → Fin 3)) := ⊤
  simpa only [uibotRootCapturePatterns_iff] using
    uibotFiniteRootWindowLaw_event_tendsto ℓ ρ hℓ hρ ns hns hsize hne N
      (uibotRootCapturePatterns N r)

/-- Helper toward Proposition 3.9: for every radius and error tolerance,
one fixed finite window captures the sampled finite-map root ball with
probability greater than `1-ε` for all sufficiently large sizes in the sequence.
This transfers the actual iid eventual-capture theorem without a new premise. -/
theorem uibotFiniteRootWindowLaw_capture_eventually_large
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,
      letI : MeasurableSpace (Option (Fin (2 * N) → Fin 3)) := ⊤
      ∀ᶠ k in atTop, 1 - ε <
        (uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) N).real
          (Option.some '' uibotRootCapturePatterns N r) := by
  have hlarge := (wholePlaneIID_uibotRootWindowCapture_tendsto_one_real r).eventually
    (lt_mem_nhds (show (1 : ℝ) - ε < 1 by linarith only [hε]))
  obtain ⟨N, hN⟩ := hlarge.exists
  refine ⟨N, ?_⟩
  let : MeasurableSpace (Option (Fin (2 * N) → Fin 3)) := ⊤
  exact (uibotFiniteRootWindowLaw_capture_tendsto ℓ ρ hℓ hρ ns hns hsize hne N r).eventually
    (lt_mem_nhds hN)

end WordLaw





































end DirectedDistances.PaperProofs.Section3
