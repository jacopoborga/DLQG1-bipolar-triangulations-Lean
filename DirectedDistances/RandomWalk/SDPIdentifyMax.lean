module

public import DirectedDistances.RandomWalk.HittingTightness

/-! # A stopped-coordinate maximum bound for the SDP identification argument

This is an iid-walk helper for the `\kappa > 0` exclusion argument,
paper result and uses no functional limit theorem. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- First-coordinate survival, transferred from the lazy second-coordinate
bound by rotating the iid code walk twice. Helper for `eqn-sdp-identify-max` -/
theorem iidCodeWalk_fst_survival_bound (k K N : ℕ) (hk : 1 ≤ k) (hK : k ≤ K)
    (hN : 0 < N) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).1} ≤
      (k : ℝ) / ((k : ℝ) + K) + (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 / N := by
  have hm : MeasurableSet {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).2} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (((measurable_pi_apply n).comp measurable_codeWalk).snd)
  have he : iidCodeMeasure.real {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).1} =
      iidCodeMeasure.real {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).2} := by
    have hmp := measurePreserving_codeRelabel.comp measurePreserving_codeRelabel
    have hh := map_measureReal_apply (μ := iidCodeMeasure) hmp.measurable hm
    rw [hmp.map_eq] at hh
    rw [hh]
    congr 1
    ext ω
    have hrot (n : ℕ) :
        (codeWalk (codeRelabel (codeRelabel ω)) n).2 = (codeWalk ω n).1 := by
      rw [codeWalk_codeRelabel, codeWalk_codeRelabel]
      dsimp only [stepRotate]
      omega
    change (∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).1) ↔
      (∀ n ≤ N, -(k : ℤ) < (codeWalk (codeRelabel (codeRelabel ω)) n).2)
    simp only [hrot]
  rw [he]
  exact lazy_survival_bound k K N hk hK hN

private theorem codeWalk_fst_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 - 1 ≤ (codeWalk ω (n + 1)).1 := by
  have h := (abs_le.mp (codeWalk_succ_sub_coord_abs_le_one ω n).1).1
  change (-1 : ℤ) ≤ (codeWalk ω (n + 1)).1 - (codeWalk ω n).1 at h
  omega

private theorem fst_survival_of_no_hit (ω : ℕ → Fin 3) (k N : ℕ) (hk : 1 ≤ k)
    (hno : ∀ j ≤ N, (codeWalk ω j).1 ≠ -(k : ℤ)) :
    ∀ j ≤ N, -(k : ℤ) < (codeWalk ω j).1 := by
  intro j hj
  induction j with
  | zero => simp [codeWalk_zero]; omega
  | succ j ih =>
      have hprev := ih (by omega)
      have hstep := codeWalk_fst_succ_ge ω j
      have hneq := hno (j + 1) hj
      omega

/-- The first hit of `-k` is later than a quadratic horizon with probability
at most `δ/2`, uniformly in `k`. The hitting time is `codeFstFirstHit`, which
is the `Nat.find` first hit on its a.s. finite event. Helper for
result. -/
theorem iidCodeWalk_fst_firstHit_tight (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ 16 < δ * B ∧ ∀ k : ℕ, 1 ≤ k →
      iidCodeMeasure.real
        {ω | codeFstFirstHit (-(k : ℤ)) ω > ((B * k ^ 2 : ℕ) : ℕ∞)} ≤ δ / 2 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (4 / δ)
  have hMposR : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  obtain ⟨B, hB⟩ := exists_nat_gt
    (max (24 * (M : ℝ) ^ 2 / δ) (16 / δ))
  have hBposR : (0 : ℝ) < B := lt_trans (by positivity) (lt_of_le_of_lt
    (le_max_right _ _) hB)
  have hBpos : 0 < B := by exact_mod_cast hBposR
  have hMscale : 4 < δ * (M : ℝ) := by
    calc
      4 < (M : ℝ) * δ := (div_lt_iff₀ hδ).mp hM
      _ = δ * M := by ring
  have hBscale : 24 * (M : ℝ) ^ 2 < δ * B := by
    calc
      24 * (M : ℝ) ^ 2 < (B : ℝ) * δ :=
        (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hB)
      _ = δ * B := by ring
  have hBexp : 16 < δ * B := by
    calc
      16 < (B : ℝ) * δ :=
        (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hB)
      _ = δ * B := by ring
  refine ⟨B, hBpos, hBexp, ?_⟩
  intro k hk
  let N := B * k ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : k ≤ k * M := by nlinarith
  have hsurv := iidCodeWalk_fst_survival_bound k (k * M) N hk hK hN
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfirst : (k : ℝ) / ((k : ℝ) + (k * M : ℕ)) ≤ δ / 4 := by
    have hcast : ((k * M : ℕ) : ℝ) = (k : ℝ) * M := by exact_mod_cast Nat.cast_mul k M
    rw [hcast]
    have hden : (k : ℝ) + (k : ℝ) * M = (k : ℝ) * (1 + M) := by ring
    rw [hden]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_pos hδ (show (0 : ℝ) < k by linarith)]
  have hsq : (((k * M : ℕ) : ℝ) + 1) ^ 2 ≤
      4 * (k : ℝ) ^ 2 * M ^ 2 := by
    have hcast : ((k * M : ℕ) : ℝ) = (k : ℝ) * M := by exact_mod_cast Nat.cast_mul k M
    rw [hcast]
    have hkm : (1 : ℝ) ≤ (k : ℝ) * M := by nlinarith
    nlinarith [sq_nonneg ((k : ℝ) * M - 1)]
  have hsecond : (3 / 2 : ℝ) * (((k * M : ℕ) : ℝ) + 1) ^ 2 / (N : ℝ) ≤
      6 * M ^ 2 / B := by
    have hNcast : (N : ℝ) = (B : ℝ) * (k : ℝ) ^ 2 := by
      dsimp [N]
      push_cast
      ring
    rw [hNcast]
    have hsq' := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ B by positivity)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hsq']
  have hsecond' : 6 * M ^ 2 / B ≤ δ / 4 := by
    apply (div_le_div_iff₀ hBposR (by positivity)).2
    nlinarith [hBscale]
  have hsurv' : iidCodeMeasure.real
      {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).1} ≤ δ / 2 := by
    calc
      _ ≤ (k : ℝ) / ((k : ℝ) + (k * M : ℕ)) +
          (3 / 2 : ℝ) * (((k * M : ℕ) : ℝ) + 1) ^ 2 / N := hsurv
      _ ≤ δ / 4 + δ / 4 := add_le_add hfirst (le_trans hsecond hsecond')
      _ = δ / 2 := by ring
  have hsub :
      {ω | codeFstFirstHit (-(k : ℤ)) ω > (N : ℕ∞)} ⊆
        {ω | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).1} := by
    intro ω hω
    apply fst_survival_of_no_hit ω k N hk
    intro j hj hhit
    have hh : ∃ n, (codeWalk ω n).1 = -(k : ℤ) := ⟨j, hhit⟩
    have hfind : Nat.find hh ≤ j := by
      by_contra hn
      exact (Nat.find_min hh (by omega)) hhit
    have htime : codeFstFirstHit (-(k : ℤ)) ω = (Nat.find hh : ℕ∞) := by
      simp [codeFstFirstHit, hh]
    change codeFstFirstHit (-(k : ℤ)) ω > (N : ℕ∞) at hω
    rw [htime] at hω
    have hNfind : N < Nat.find hh := by exact_mod_cast hω
    omega
  exact (measureReal_mono hsub).trans hsurv'

/-- A fixed-horizon second-coordinate maximum tail obtained from the iid block
maximum estimate. Helper for `eqn-sdp-identify-max` -/
theorem iidCodeWalk_snd_max_tail (A : ℝ) (hA : 0 < A) (B k : ℕ)
    (hB : 0 < B) (hk : 1 ≤ k) :
    iidCodeMeasure.real
      {ω | ∃ n ≤ B * k ^ 2, A * k < |((codeWalk ω n).2 : ℝ)|} ≤
        4 * Real.exp (-(A ^ 2) / (2 * (B : ℝ))) := by
  have hm : 0 < B * k ^ 2 := by positivity
  have htail := iidCodeWalk_blockMax_tail 0 (B * k ^ 2) hm (A * k)
    (by positivity)
  simp only [Nat.zero_add, codeWalk_zero, Prod.fst_sub, Prod.snd_sub, sub_zero] at htail
  have hsub :
      {ω | ∃ n ≤ B * k ^ 2, A * k < |((codeWalk ω n).2 : ℝ)|} ⊆
        {ω | ∃ n ≤ B * k ^ 2,
          A * k ≤ |((codeWalk ω n).1 : ℝ)| ∨ A * k ≤ |((codeWalk ω n).2 : ℝ)|} := by
    rintro ω ⟨n, hn, hgt⟩
    exact ⟨n, hn, Or.inr (le_of_lt hgt)⟩
  refine (measureReal_mono hsub).trans ?_
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ 4 * Real.exp (-(A * (k : ℝ)) ^ 2 / (2 * ((B * k ^ 2 : ℕ) : ℝ))) := htail
    _ = 4 * Real.exp (-(A ^ 2) / (2 * (B : ℝ))) := by
      congr 1
      push_cast
      field_simp [ne_of_gt hBR, ne_of_gt hkR]

private theorem measurableSet_sdpStoppedBound (k : ℕ) (A : ℝ) :
    MeasurableSet {ω | ∃ h : ∃ n : ℕ, (codeWalk ω n).1 = -(k : ℤ),
      ∀ n ≤ Nat.find h, |((codeWalk ω n).2 : ℝ)| ≤ A * k} := by
  classical
  let firstHitSet : Set (ℕ → Fin 3) :=
    {ω | ∃ n : ℕ, (∀ j < n, (codeWalk ω j).1 ≠ -(k : ℤ)) ∧
      (codeWalk ω n).1 = -(k : ℤ) ∧
      ∀ j ≤ n, |((codeWalk ω j).2 : ℝ)| ≤ A * k}
  have heq : {ω | ∃ h : ∃ n : ℕ, (codeWalk ω n).1 = -(k : ℤ),
      ∀ n ≤ Nat.find h, |((codeWalk ω n).2 : ℝ)| ≤ A * k} = firstHitSet := by
    ext ω
    constructor
    · rintro ⟨h, hb⟩
      let n := Nat.find h
      refine ⟨n, ?_, Nat.find_spec h, hb⟩
      intro j hj hhit
      exact (Nat.find_min h hj) hhit
    · rintro ⟨n, hfirst, hhit, hb⟩
      let h : ∃ j : ℕ, (codeWalk ω j).1 = -(k : ℤ) := ⟨n, hhit⟩
      have hfind : Nat.find h = n := by
        apply Nat.le_antisymm
        · by_contra hn
          exact (Nat.find_min h (by omega)) hhit
        · by_contra hn
          have hspec := Nat.find_spec h
          exact hfirst (Nat.find h) (by omega) hspec
      exact ⟨h, by simpa [hfind] using hb⟩
  rw [heq]
  change MeasurableSet {ω | ∃ n : ℕ,
    (∀ j < n, (codeWalk ω j).1 ≠ -(k : ℤ)) ∧
    (codeWalk ω n).1 = -(k : ℤ) ∧
    ∀ j ≤ n, |((codeWalk ω j).2 : ℝ)| ≤ A * k}
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (measurableSet_eq_fun
      (((measurable_pi_apply j).comp measurable_codeWalk).fst) measurable_const).compl
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        (((measurable_pi_apply n).comp measurable_codeWalk).fst) measurable_const
    ·
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro hj
      exact measurableSet_le
        (continuous_abs.measurable.comp
          ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
            ((measurable_pi_apply j).comp measurable_codeWalk).snd))
        measurable_const

/-- Uniform quadratic tightness of the first-coordinate hitting time, followed
by the finite-horizon block maximum bound, gives the stopped maximum estimate.
The displayed event uses `Nat.find h` for the first time `L` hits `-k`; the
input `codeFstFirstHit` is finite almost surely. Helper for
result. -/
theorem iidCodeWalk_sdpIdentifyMax (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, ∃ B : ℕ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 1 ≤ k →
      iidCodeMeasure.real
        {ω | ∃ h : ∃ n : ℕ, (codeWalk ω n).1 = -(k : ℤ),
          ∀ n ≤ Nat.find h, |((codeWalk ω n).2 : ℝ)| ≤ A * k} ≥ 1 - δ := by
  obtain ⟨B, hBpos, hBscale, hlate⟩ := iidCodeWalk_fst_firstHit_tight δ hδ
  let A : ℝ := B
  have hA : 0 < A := by
    change (0 : ℝ) < (B : ℝ)
    exact_mod_cast hBpos
  have hExp : 4 * Real.exp (-(A ^ 2) / (2 * (B : ℝ))) ≤ δ / 2 := by
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hBpos
    have harg : -(A ^ 2) / (2 * (B : ℝ)) = -((B : ℝ) / 2) := by
      dsimp [A]
      field_simp
    rw [harg]
    let x : ℝ := (B : ℝ) / 2
    have hx : 0 < x := by dsimp [x]; positivity
    have hexp : Real.exp (-x) ≤ 1 / (x + 1) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        (inv_le_inv₀ (Real.exp_pos x) (by positivity)).2 (Real.add_one_le_exp x)
    have hfrac : 4 * (1 / (x + 1)) ≤ δ / 2 := by
      have hfrac' : 4 / (x + 1) ≤ δ / 2 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < x + 1)).2
        dsimp [x]
        nlinarith [hBscale]
      simpa [div_eq_mul_inv] using hfrac'
    calc
      4 * Real.exp (-x) ≤ 4 * (1 / (x + 1)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ δ / 2 := hfrac
  refine ⟨A, B, hA, hBpos, ?_⟩
  intro k hk
  let N : ℕ := B * k ^ 2
  let G : Set (ℕ → Fin 3) :=
    {ω | ∃ h : ∃ n : ℕ, (codeWalk ω n).1 = -(k : ℤ),
      ∀ n ≤ Nat.find h, |((codeWalk ω n).2 : ℝ)| ≤ A * k}
  let Late : Set (ℕ → Fin 3) :=
    {ω | codeFstFirstHit (-(k : ℤ)) ω > (N : ℕ∞)}
  let Large : Set (ℕ → Fin 3) :=
    {ω | ∃ n ≤ N, A * k < |((codeWalk ω n).2 : ℝ)|}
  have hGmeas : MeasurableSet G := by
    simpa only [G] using measurableSet_sdpStoppedBound k A
  have hLate : iidCodeMeasure.real Late ≤ δ / 2 := by
    simpa only [Late, N] using hlate k hk
  have hLarge : iidCodeMeasure.real Large ≤ δ / 2 := by
    calc
      iidCodeMeasure.real Large ≤ 4 * Real.exp (-(A ^ 2) / (2 * (B : ℝ))) := by
        simpa only [Large, N] using iidCodeWalk_snd_max_tail A hA B k hBpos hk
      _ ≤ δ / 2 := hExp
  have hsub : Gᶜ ⊆ Late ∪ Large := by
    intro ω hω
    by_contra hnotUnion
    have hnotLate : ω ∉ Late := fun hh => hnotUnion (Or.inl hh)
    have hnotLarge : ω ∉ Large := fun hh => hnotUnion (Or.inr hh)
    have htime : codeFstFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞) := not_lt.mp hnotLate
    have hhit : ∃ n : ℕ, (codeWalk ω n).1 = -(k : ℤ) := by
      by_contra hhit
      simp [codeFstFirstHit, hhit] at htime
    have htimeEq : codeFstFirstHit (-(k : ℤ)) ω = (Nat.find hhit : ℕ∞) := by
      simp [codeFstFirstHit, hhit]
    have hfind : Nat.find hhit ≤ N := by
      have h' : (Nat.find hhit : ℕ∞) ≤ (N : ℕ∞) := htimeEq ▸ htime
      exact_mod_cast h'
    have hgood : ∀ n ≤ N, |((codeWalk ω n).2 : ℝ)| ≤ A * k := by
      intro n hn
      by_contra hgt
      exact hnotLarge ⟨n, hn, lt_of_not_ge hgt⟩
    apply hω
    exact ⟨hhit, fun n hn => hgood n (hn.trans hfind)⟩
  have hbad : iidCodeMeasure.real Gᶜ ≤ iidCodeMeasure.real Late + iidCodeMeasure.real Large :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have htotal := measureReal_add_measureReal_compl (μ := iidCodeMeasure) hGmeas
  rw [probReal_univ] at htotal
  linarith

end DirectedDistances.RandomWalk
