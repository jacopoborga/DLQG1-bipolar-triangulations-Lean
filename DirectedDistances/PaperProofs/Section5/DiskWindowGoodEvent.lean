module

public import DirectedDistances.PaperProofs.Section5.DiskWindowDecodeTV
public import DirectedDistances.PaperProofs.Section5.DiskBallIdentification

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
disk window event without prefix dip and disk ball identification with probability
at least `1 - 3 * ε`; not the paper result. The input `hE` is supplied separately
by `uibhbot_prob_windowEventK_ge` (k268). -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW

private theorem bridgeLevelLaw_finite (n ℓ : ℕ) :
    IsFiniteMeasure (bridgeLevelLaw n ℓ) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset (Finset.Icc 1 ℓ)) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    by_cases hz : (Finset.Icc 1 ℓ).card = 0
    · simp only [hz, Nat.cast_zero, ENNReal.zero_div]
      exact ENNReal.zero_lt_top
    · rw [ENNReal.div_self (by exact_mod_cast hz) (by finiteness)]
      exact ENNReal.one_lt_top
  have : IsFiniteMeasure (cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)) := inferInstance
  unfold bridgeLevelLaw
  infer_instance

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
transfer the window capture event by total variation, as a step toward the disk
window event without prefix dip and disk ball identification with probability
at least `1 - 3 * ε`; not the paper result.
The input `hE` is supplied by `uibhbot_prob_windowEventK_ge` (k268). -/
theorem diskWindow_prob_eventK_ge
    (A : ℝ) (hA : 1 < A) (N r K0 : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hE : 1 - ε ≤ (uibhbotEncodingWindowLaw N).real
      {x | kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)}) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      1 - 2 * ε ≤ (bridgeLevelLaw n ℓ).real
        {p | ∃ x, bridgeOptionWindow n N p = some x ∧
          kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)} := by
  obtain ⟨n₀, htv⟩ := diskWindow_id_tv A hA N ε hε
  refine ⟨n₀, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong
  let E : Set (Fin (2 * N + 1) → ℤ × ℤ) :=
    {x | kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)}
  let C : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)) := some '' E
  have hpre : bridgeOptionWindow n N ⁻¹' C =
      {p | ∃ x, bridgeOptionWindow n N p = some x ∧
        kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)} := by
    ext p
    constructor
    · rintro ⟨x, hx, hxp⟩
      exact ⟨x, hxp.symm, hx⟩
    · rintro ⟨x, hxp, hx⟩
      exact ⟨x, hx, hxp.symm⟩
  have hsome : some ⁻¹' C = E := by
    ext x
    simp only [C, Set.mem_preimage, Set.mem_image, Option.some.injEq, exists_eq_right]
  have htv' := htv n hn ℓ hlo hhi hℓn hcong C
  change |(bridgeLevelLaw n ℓ).real (bridgeOptionWindow n N ⁻¹' C) -
    (uibhbotEncodingWindowLaw N).real (some ⁻¹' C)| ≤ ε at htv'
  rw [hpre, hsome] at htv'
  have hlower := (abs_le.mp htv').1
  change 1 - ε ≤ (uibhbotEncodingWindowLaw N).real E at hE
  linarith only [hlower, hE]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
disk window event without prefix dip and disk ball identification with probability
at least `1 - 3 * ε`; not the paper result. This is the good-event bound.
The input `hE` is supplied by `uibhbot_prob_windowEventK_ge` (k268). -/
theorem diskWindow_prob_good_ge
    (A : ℝ) (hA : 1 < A) (r K0 N₀ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hE : ∀ N ≥ N₀, 1 - ε ≤ (uibhbotEncodingWindowLaw N).real
      {x | kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)}) :
    ∃ N ≥ N₀, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      1 - 3 * ε ≤ (bridgeLevelLaw n ℓ).real
        {p | ∃ x, bridgeOptionWindow n N p = some x ∧
          kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧ ¬ DiskDip N K0 p} := by
  classical
  obtain ⟨Ndip, hdip⟩ := diskPrefixDip_small A hA K0 ε hε
  let N := max N₀ Ndip
  have hN : N₀ ≤ N := le_max_left _ _
  obtain ⟨ndip, hndip⟩ := hdip N (le_max_right _ _)
  obtain ⟨ntv, hntv⟩ := diskWindow_prob_eventK_ge A hA N r K0 ε hε (hE N hN)
  refine ⟨N, hN, max ntv ndip, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong
  have : IsFiniteMeasure (bridgeLevelLaw n ℓ) := bridgeLevelLaw_finite n ℓ
  have hcapture := hntv n ((le_max_left _ _).trans hn) ℓ hlo hhi hℓn hcong
  have hsmall := hndip n ((le_max_right _ _).trans hn) ℓ hlo hhi hℓn hcong
  have hdip_eq : {p : (ℕ → Fin 3) × ℕ | DiskDip N K0 p} =
      {p | ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
        ∃ j : ℕ, j + N < T ∧
          (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)} := by
    ext p
    exact DiskDip_iff_diskPrefixDip N K0 p
  rw [← hdip_eq] at hsmall
  let G : Set ((ℕ → Fin 3) × ℕ) :=
    {p | ∃ x, bridgeOptionWindow n N p = some x ∧
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)}
  let H : Set ((ℕ → Fin 3) × ℕ) :=
    {p | ∃ x, bridgeOptionWindow n N p = some x ∧
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧ ¬ DiskDip N K0 p}
  have hsub : G ⊆ H ∪ {p | DiskDip N K0 p} := by
    rintro p ⟨x, hx, hev⟩
    by_cases hd : DiskDip N K0 p
    · exact Or.inr hd
    · exact Or.inl ⟨x, hx, hev, hd⟩
  have hsplit : (bridgeLevelLaw n ℓ).real G ≤
      (bridgeLevelLaw n ℓ).real H +
        (bridgeLevelLaw n ℓ).real {p | DiskDip N K0 p} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  change 1 - 2 * ε ≤ (bridgeLevelLaw n ℓ).real G at hcapture
  change 1 - 3 * ε ≤ (bridgeLevelLaw n ℓ).real H
  linarith only [hcapture, hsplit, hsmall]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
disk window event without prefix dip and disk ball identification with probability
at least `1 - 3 * ε`; not the paper result. On one event, identification holds
for every stage at or beyond the right endpoint of the window.
The input `hE` is supplied by `uibhbot_prob_windowEventK_ge` (k268). -/
theorem diskWindow_prob_ball_eq_image_ge
    (A : ℝ) (hA : 1 < A) (r K0 N₀ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hE : ∀ N ≥ N₀, 1 - ε ≤ (uibhbotEncodingWindowLaw N).real
      {x | kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)}) :
    ∃ N ≥ N₀, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      1 - 3 * ε ≤ (bridgeLevelLaw n ℓ).real
        {p | ∃ x, bridgeOptionWindow n N p = some x ∧
          ∀ n' : ℕ, (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n' →
            let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
            let w := fun i => p.1 (i + 1)
            kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r
                (activeInitial w T) =
              (kmswStageBallVertices (fun _ _ => True)
                (kmswStage (windowCodeDecode N x) (2 * N)) r
                (activeInitial (windowCodeDecode N x) N)).image
                  (kmswWindowPatchVertexMap w (T - N) (2 * N))} := by
  obtain ⟨N, hN, n₀, hgood⟩ := diskWindow_prob_good_ge A hA r K0 N₀ ε hε hE
  refine ⟨N, hN, n₀, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong
  have : IsFiniteMeasure (bridgeLevelLaw n ℓ) := bridgeLevelLaw_finite n ℓ
  refine (hgood n hn ℓ hlo hhi hℓn hcong).trans (measureReal_mono ?_)
  rintro p ⟨x, hx, hev, hnd⟩
  exact ⟨x, hx, fun n' hn' => diskBall_eq_image_of_eventK_noDip hx hev hnd n' hn'⟩

end DirectedDistances.PaperProofs.Section5
