module

public import DirectedDistances.RandomWalk.Lemma518BridgeReduction
public import DirectedDistances.RandomWalk.ExcursionWords

/-! Supporting lemmas for paper labels `lem-disk-walk-conv` (see CORRESPONDENCE.md). -/

/-! # Cemetery convention for finite bridge windows

Helpers toward the finite bridge correction to `lem-disk-walk-conv`,
recorded as a separate cemetery outcome; every valid window retains all of its
centered coordinates. These helpers are not counted as paper results. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal symmDiff



@[expose] noncomputable def bridgeOptionWindow (n N : ℕ)
    (p : (ℕ → Fin 3) × ℕ) : Option (Fin (2 * N + 1) → ℤ × ℤ) := by
  classical
  exact if codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
      N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n then
    some (fun j => codeWalk p.1
      ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + j.val - N) -
      codeWalk p.1 (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat)
  else none

/-- Every non-cemetery finite bridge output is exactly the auxiliary raw centered
window. Helper toward corrected `lem-disk-walk-conv` and ruling finite bridge. -/
theorem bridgeOptionWindow_some_eq {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) : x = bridgeRawWindow N p := by
  classical
  unfold bridgeOptionWindow at h
  split at h
  · injection h with hx
    unfold bridgeRawWindow
    exact hx.symm
  · contradiction

/-- On the explicit validity branch, the finite bridge observable is the exact raw
centered vector. Helper toward corrected `lem-disk-walk-conv`; ruling finite bridge. -/
theorem bridgeOptionWindow_eq_some_of_valid (n N : ℕ)
    (p : (ℕ → Fin 3) × ℕ)
    (h : codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
      N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n) :
    bridgeOptionWindow n N p = some (bridgeRawWindow N p) := by
  classical
  unfold bridgeOptionWindow bridgeRawWindow
  simp [h]

/-- On an interior cone-bridge level, finite bridge records the exact raw centered
window; the endpoint bounds come from `coneEvent_fstFirstHit_window`.
Helper toward corrected `lem-disk-walk-conv` and ruling finite bridge. -/
theorem bridgeOptionWindow_eq_some_of_interior {n N ell K : ℕ}
    {ω : ℕ → Fin 3}
    (hω : ω ∈ coneEvent (ell : ℤ) 0 n)
    (hK : 1 ≤ K) (hKell : K ≤ ell) (hNK : N ≤ K)
    (hKNell : K + N ≤ ell) :
    bridgeOptionWindow n N (ω, K) = some (bridgeRawWindow N (ω, K)) := by
  classical
  obtain ⟨T, hT, hNT, hTn⟩ :=
    coneEvent_fstFirstHit_window (ell : ℤ) n N K hK (by exact_mod_cast hKell)
      hNK (by exact_mod_cast hKNell) ω hω
  apply bridgeOptionWindow_eq_some_of_valid
  rw [hT]
  exact ⟨by simp, by simpa using hNT, by simpa using hTn⟩

private theorem measurable_bridgeWindowAtTime (N T : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      fun j : Fin (2 * N + 1) =>
        codeWalk ω (T + j.val - N) - codeWalk ω T) := by
  apply measurable_pi_iff.mpr
  intro j
  exact ((measurable_pi_apply (T + j.val - N)).comp measurable_codeWalk).sub
    ((measurable_pi_apply T).comp measurable_codeWalk)

private theorem measurableSet_bridgeFirstHit_eq (K T : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | codeFstFirstHit (-(K : ℤ)) ω = T} := by
  exact codePast_le T _ (measurableSet_codePast_codeFstFirstHit_eq _ T)

/-- The actual finite-bridge product law with the one-based uniform level used -/
@[expose] noncomputable def bridgeLevelLaw (n ell : ℕ) :
    Measure ((ℕ → Fin 3) × ℕ) :=
  (cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
    (Measure.uniformOfFinset (Finset.Icc 1 ell))

/-- Every preimage under the finite bridge observable is measurable, without requiring a
measurable-space instance on `Option`. Helper toward corrected
`lem-disk-walk-conv` and ruling finite bridge. -/
theorem measurableSet_bridgeOptionWindow_preimage (n N : ℕ)
    (S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ))) :
    MeasurableSet (bridgeOptionWindow n N ⁻¹' S) := by
  classical
  let valid : Set ℕ∞ := {t | t ≠ ⊤ ∧ N ≤ t.toNat ∧ t.toNat + N ≤ n}
  have hh (K : ℕ) : Measurable (codeFstFirstHit (-(K : ℤ))) := by
    rw [ENat.measurable_iff]
    intro T
    exact codePast_le T _ (measurableSet_codePast_codeFstFirstHit_eq _ T)
  have hHit : Measurable (fun p : (ℕ → Fin 3) × ℕ =>
      codeFstFirstHit (-(p.2 : ℤ)) p.1) :=
    measurable_from_prod_countable_left fun K => hh K
  have hvalid : MeasurableSet {p : (ℕ → Fin 3) × ℕ |
      codeFstFirstHit (-(p.2 : ℤ)) p.1 ∈ valid} :=
    (Set.to_countable valid).measurableSet.preimage hHit
  have hnone : MeasurableSet {p : (ℕ → Fin 3) × ℕ |
      codeFstFirstHit (-(p.2 : ℤ)) p.1 ∉ valid} := hvalid.compl
  have hsomeSet : MeasurableSet (some ⁻¹' S : Set (Fin (2 * N + 1) → ℤ × ℤ)) :=
    (Set.to_countable _).measurableSet
  let good : Set ((ℕ → Fin 3) × ℕ) := ⋃ K : ℕ, ⋃ T : ℕ,
    {p | p.2 = K ∧ codeFstFirstHit (-(K : ℤ)) p.1 = T ∧
      N ≤ T ∧ T + N ≤ n ∧
      (fun j : Fin (2 * N + 1) =>
        codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S}
  have hgood : MeasurableSet good := by
    apply MeasurableSet.iUnion
    intro K
    apply MeasurableSet.iUnion
    intro T
    have hk : MeasurableSet {p : (ℕ → Fin 3) × ℕ | p.2 = K} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have ht : MeasurableSet {p : (ℕ → Fin 3) × ℕ |
        codeFstFirstHit (-(K : ℤ)) p.1 = T} :=
      (measurableSet_bridgeFirstHit_eq K T).preimage measurable_fst
    have hw : MeasurableSet {p : (ℕ → Fin 3) × ℕ |
        (fun j : Fin (2 * N + 1) =>
          codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S} := by
      exact hsomeSet.preimage ((measurable_bridgeWindowAtTime N T).comp measurable_fst)
    by_cases hNT : N ≤ T
    · by_cases hTn : T + N ≤ n
      · have hs : {p : (ℕ → Fin 3) × ℕ | p.2 = K ∧
            codeFstFirstHit (-(K : ℤ)) p.1 = T ∧ N ≤ T ∧ T + N ≤ n ∧
            (fun j : Fin (2 * N + 1) =>
              codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S} =
            {p | p.2 = K} ∩ {p | codeFstFirstHit (-(K : ℤ)) p.1 = T} ∩
              {p | (fun j : Fin (2 * N + 1) =>
                codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S} := by
          ext p
          simp [hNT, hTn, and_assoc]
        rw [hs]
        simpa [Set.inter_assoc] using hk.inter (ht.inter hw)
      · have hs : {p : (ℕ → Fin 3) × ℕ | p.2 = K ∧
            codeFstFirstHit (-(K : ℤ)) p.1 = T ∧ N ≤ T ∧ T + N ≤ n ∧
            (fun j : Fin (2 * N + 1) =>
              codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S} = ∅ := by
          ext p
          simp [hTn]
        rw [hs]
        exact MeasurableSet.empty
    · have hs : {p : (ℕ → Fin 3) × ℕ | p.2 = K ∧
          codeFstFirstHit (-(K : ℤ)) p.1 = T ∧ N ≤ T ∧ T + N ≤ n ∧
          (fun j : Fin (2 * N + 1) =>
            codeWalk p.1 (T + j.val - N) - codeWalk p.1 T) ∈ some ⁻¹' S} = ∅ := by
        ext p
        simp [hNT]
      rw [hs]
      exact MeasurableSet.empty
  have hcem : MeasurableSet {p : (ℕ → Fin 3) × ℕ |
      none ∈ S ∧ codeFstFirstHit (-(p.2 : ℤ)) p.1 ∉ valid} := by
    by_cases hn : none ∈ S
    · simpa [hn] using hnone
    · simp [hn]
  have heq : bridgeOptionWindow n N ⁻¹' S =
      {p | none ∈ S ∧ codeFstFirstHit (-(p.2 : ℤ)) p.1 ∉ valid} ∪ good := by
    ext p
    classical
    by_cases hv : codeFstFirstHit (-(p.2 : ℤ)) p.1 ∈ valid
    · change codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
        N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
        (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n at hv
      obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp hv.1
      have htoNat : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat = T := by
        simpa using congrArg ENat.toNat hT.symm
      change (if codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
        N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
        (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n then
        some (fun j : Fin (2 * N + 1) => codeWalk p.1
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + j.val - N) -
          codeWalk p.1 (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat) else none) ∈ S ↔ _
      rw [if_pos hv]
      simp only [Set.mem_union, good, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hp
        right
        refine ⟨p.2, T, rfl, ?_, ?_, ?_, ?_⟩
        · simpa using hT.symm
        · simpa [htoNat] using hv.2.1
        · simpa [htoNat] using hv.2.2
        · simpa [htoNat] using hp
      · rintro (⟨hs, hb⟩ | ⟨K, T, hpK, hpT, hNT, hTn, hpS⟩)
        · have hvSet : codeFstFirstHit (-(p.2 : ℤ)) p.1 ∈ valid := by
            simpa [valid] using hv
          exact (hb hvSet).elim
        · have hK : K = p.2 := hpK.symm
          subst K
          have htoNat : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat = T := by
            simpa using congrArg ENat.toNat hpT
          have hv' : codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
              N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
              (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
            refine ⟨by simp [hpT], ?_, ?_⟩
            · simpa [htoNat] using hNT
            · simpa [htoNat] using hTn
          simpa [htoNat] using hpS
    · change (bridgeOptionWindow n N p ∈ S) ↔ _
      change (if codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
        N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
        (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n then
        some (fun j : Fin (2 * N + 1) => codeWalk p.1
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + j.val - N) -
          codeWalk p.1 (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat) else none) ∈ S ↔ _
      have hv' : ¬ (codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
          N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
          (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n) := by
        simpa [valid] using hv
      rw [if_neg hv']
      simp only [Set.mem_union, good, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hp
        exact Or.inl ⟨hp, by simpa [valid] using hv⟩
      · rintro (⟨hp, _⟩ | ⟨K, T, hpK, hpT, hNT, hTn, hpS⟩)
        · exact hp
        · have : K = p.2 := hpK.symm
          subst K
          have hv'' : codeFstFirstHit (-(p.2 : ℤ)) p.1 ∈ valid := by
            change codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
              N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
              (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n
            refine ⟨by simp [hpT], ?_, ?_⟩
            · simpa [hpT] using hNT
            · simpa [hpT] using hTn
          exact (hv hv'').elim
  rw [heq]
  exact hcem.union hgood

private theorem measurableSet_bridgeCone (ell n : ℕ) :
    MeasurableSet (coneEvent (ell : ℤ) 0 n) := by
  simp only [coneEvent, Set.ofPred_and]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    have hj := (measurable_pi_apply j).comp measurable_codeWalk
    simp only [Set.ofPred_and]
    exact (measurableSet_le measurable_const (measurable_const.add hj.fst)).inter
      (measurableSet_le measurable_const (measurable_const.add hj.snd))
  · exact (measurable_const.add ((measurable_pi_apply n).comp measurable_codeWalk))
      (measurableSet_singleton (0, 0))

private theorem bridgeLevelLaw_boundary_bad_bound (n ell N : ℕ) (hell : 1 ≤ ell) :
    (bridgeLevelLaw n ell).real
      ((coneEvent (ell : ℤ) 0 n)ᶜ ×ˢ Set.univ ∪
        Set.univ ×ˢ ((Finset.Icc 1 ell : Set ℕ)ᶜ ∪
          {K : ℕ | K < N ∨ ell < K + N})) ≤
      2 * (N : ℝ) / (ell : ℝ) := by
  classical
  let E := coneEvent (ell : ℤ) 0 n
  let levels := Finset.Icc 1 ell
  let badFin := levels.filter (fun K => K < N ∨ ell < K + N)
  let boundary : Set ℕ := {K | K < N ∨ ell < K + N}
  let bad : Set ℕ := (levels : Set ℕ)ᶜ ∪ boundary
  let μc := cond iidCodeMeasure E
  let U := Measure.uniformOfFinset levels
  let P := μc.prod U
  have hE : MeasurableSet E := measurableSet_bridgeCone ell n
  have hlevels : levels.card = ell := by simp [levels]
  have hcondEcomp : μc.real Eᶜ = 0 := by
    change ((cond iidCodeMeasure E) Eᶜ).toReal = 0
    rw [ProbabilityTheory.cond_apply hE iidCodeMeasure Eᶜ]
    simp
  have hcondTotal : μc.real Set.univ ≤ 1 := by
    by_cases hzero : iidCodeMeasure E = 0
    · simp [μc, ProbabilityTheory.cond, hzero]
    · letI : IsProbabilityMeasure μc := by
        simpa [μc] using ProbabilityTheory.cond_isProbabilityMeasure hzero
      simp
  have hUprob : IsProbabilityMeasure U := by
    constructor
    change U Set.univ = 1
    dsimp [U]
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    rw [hlevels]
    exact ENNReal.div_self (by exact_mod_cast (show ell ≠ 0 by omega)) (by finiteness)
  have hUboundary : U.real boundary ≤ (2 * (N : ℝ)) / (ell : ℝ) := by
    change (Measure.uniformOfFinset levels boundary).toReal ≤ _
    rw [Measure.uniformOfFinset_apply, ENNReal.toReal_div]
    · simp only [ENNReal.toReal_natCast]
      simp only [boundary, Set.mem_setOf_eq]
      change ((levels.filter (fun K => K < N ∨ ell < K + N)).card : ℝ) /
          (levels.card : ℝ) ≤ _
      rw [hlevels]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc : (levels.filter (fun K => K < N ∨ ell < K + N)).card ≤ 2 * N := by
        simpa [levels] using uniformLevelWindow_badLevels_card ell N
      exact_mod_cast hc
  have hUcomp : U.real (levels : Set ℕ)ᶜ = 0 := by
    change (Measure.uniformOfFinset levels (levels : Set ℕ)ᶜ).toReal = 0
    rw [Measure.uniformOfFinset_apply]
    simp
  have hUbad : U.real bad ≤ (2 * (N : ℝ)) / (ell : ℝ) := by
    calc
      U.real bad = U.real ((levels : Set ℕ)ᶜ ∪ boundary) := rfl
      _ ≤ U.real (levels : Set ℕ)ᶜ + U.real boundary := measureReal_union_le _ _
      _ ≤ (2 * (N : ℝ)) / (ell : ℝ) := by rw [hUcomp]; simp; exact hUboundary
  have hμczero_of_zero (hzero : iidCodeMeasure E = 0) : μc = 0 := by
    simp [μc, ProbabilityTheory.cond, hzero]
  haveI : IsFiniteMeasure μc := by
    by_cases hzero : iidCodeMeasure E = 0
    · rw [hμczero_of_zero hzero]
      infer_instance
    · letI : IsProbabilityMeasure μc := by
        simpa [μc] using ProbabilityTheory.cond_isProbabilityMeasure hzero
      infer_instance
  letI : IsProbabilityMeasure U := hUprob
  haveI : IsFiniteMeasure U := inferInstance
  haveI : IsFiniteMeasure P := by dsimp [P]; infer_instance
  have hmass : P.real (Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad) ≤
      (2 * (N : ℝ)) / (ell : ℝ) := by
    calc
      P.real (Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad) ≤
          P.real (Eᶜ ×ˢ Set.univ) + P.real (Set.univ ×ˢ bad) :=
        measureReal_union_le _ _
      _ = μc.real Eᶜ * U.real Set.univ + μc.real Set.univ * U.real bad := by
        rw [MeasureTheory.measureReal_prod_prod, MeasureTheory.measureReal_prod_prod]
      _ ≤ (2 * (N : ℝ)) / (ell : ℝ) := by
        rw [hcondEcomp]
        simp only [zero_mul, zero_add]
        calc
          μc.real Set.univ * U.real bad ≤ 1 * U.real bad :=
            mul_le_mul_of_nonneg_right hcondTotal measureReal_nonneg
          _ = U.real bad := by ring
          _ ≤ (2 * (N : ℝ)) / (ell : ℝ) := hUbad
  simpa [P, μc, U, bridgeLevelLaw, E, levels, bad] using hmass

/-- The cemetery outcome has mass at most the fraction of boundary levels.
This is the finite bridge exceptional-probability obligation from ruling -/
theorem bridgeOptionWindow_none_bound {n ell N : ℕ} (hell : 1 ≤ ell) :
    (bridgeLevelLaw n ell).real
      (bridgeOptionWindow n N ⁻¹' ({none} : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)))) ≤
      2 * (N : ℝ) / (ell : ℝ) := by
  classical
  let E := coneEvent (ell : ℤ) 0 n
  let levels := Finset.Icc 1 ell
  let bad : Set ℕ := (levels : Set ℕ)ᶜ ∪ {K | K < N ∨ ell < K + N}
  let μc := cond iidCodeMeasure E
  let U := Measure.uniformOfFinset levels
  have hE : MeasurableSet E := measurableSet_bridgeCone ell n
  have hlevels : levels.card = ell := by simp [levels]
  letI : IsFiniteMeasure μc := by
    by_cases hzero : iidCodeMeasure E = 0
    · have hz : μc = 0 := by simp [μc, ProbabilityTheory.cond, hzero]
      rw [hz]
      infer_instance
    · letI : IsProbabilityMeasure μc := by
        simpa [μc] using ProbabilityTheory.cond_isProbabilityMeasure hzero
      infer_instance
  letI : IsProbabilityMeasure U := by
    constructor
    dsimp [U]
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    rw [hlevels]
    exact ENNReal.div_self (by exact_mod_cast (show ell ≠ 0 by omega)) (by finiteness)
  haveI : IsFiniteMeasure (bridgeLevelLaw n ell) := by
    dsimp [bridgeLevelLaw, E, levels]
    infer_instance
  have hsub : bridgeOptionWindow n N ⁻¹' ({none} : Set (Option _)) ⊆
      Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad := by
    intro p hp
    rcases p with ⟨ω, K⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
    by_cases hω : ω ∈ E
    · by_cases hbad : K ∈ bad
      · exact Or.inr ⟨Set.mem_univ _, hbad⟩
      · have hK : K ∈ levels := by
          by_contra hk
          exact hbad (Or.inl hk)
        have hKmem := Finset.mem_Icc.mp hK
        have hboundary : ¬ (K < N ∨ ell < K + N) := by
          intro hb
          exact hbad (Or.inr hb)
        have hNK : N ≤ K := by
          apply Nat.le_of_not_gt
          intro h
          exact hboundary (Or.inl h)
        have hKN : K + N ≤ ell := by
          apply Nat.le_of_not_gt
          intro h
          exact hboundary (Or.inr h)
        have hwindow := bridgeOptionWindow_eq_some_of_interior hω hKmem.1
          hKmem.2 hNK hKN
        rw [hwindow] at hp
        cases hp
    · exact Or.inl ⟨hω, Set.mem_univ _⟩
  change (bridgeLevelLaw n ell).real
      (bridgeOptionWindow n N ⁻¹' ({none} : Set (Option _))) ≤ _
  calc
    (bridgeLevelLaw n ell).real _ ≤
        (bridgeLevelLaw n ell).real
          (Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad) := measureReal_mono hsub
    _ ≤ 2 * (N : ℝ) / (ell : ℝ) := by
      change (bridgeLevelLaw n ell).real
        ((coneEvent (ell : ℤ) 0 n)ᶜ ×ˢ Set.univ ∪
          Set.univ ×ˢ ((Finset.Icc 1 ell : Set ℕ)ᶜ ∪
            {K : ℕ | K < N ∨ ell < K + N})) ≤ _
      exact bridgeLevelLaw_boundary_bad_bound n ell N hell

/-- Transfer from the cemetery observable to any measurable total extension
that agrees with the raw centered vector on interior bridge levels. The error
is the boundary-level mass in the finite bridge ruling. Helper, not a paper result. -/
theorem bridgeOptionWindow_transfer {n ell N : ℕ} (hell : 1 ≤ ell)
    (W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ))
    (hW : Measurable W)
    (hagree : ∀ ω K, ω ∈ coneEvent (ell : ℤ) 0 n → 1 ≤ K → K ≤ ell →
      N ≤ K → K + N ≤ ell → W (ω, K) = bridgeRawWindow N (ω, K))
    (S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ))) :
    |(bridgeLevelLaw n ell).real (bridgeOptionWindow n N ⁻¹' S) -
      (bridgeLevelLaw n ell).real (W ⁻¹' (some ⁻¹' S))| ≤
      2 * (N : ℝ) / (ell : ℝ) := by
  classical
  let E := coneEvent (ell : ℤ) 0 n
  let levels := Finset.Icc 1 ell
  let bad : Set ℕ := (levels : Set ℕ)ᶜ ∪ {K | K < N ∨ ell < K + N}
  let μc := cond iidCodeMeasure E
  let U := Measure.uniformOfFinset levels
  let P := bridgeLevelLaw n ell
  have hE : MeasurableSet E := measurableSet_bridgeCone ell n
  letI : IsFiniteMeasure μc := by
    by_cases hzero : iidCodeMeasure E = 0
    · have hz : μc = 0 := by simp [μc, ProbabilityTheory.cond, hzero]
      rw [hz]
      infer_instance
    · letI : IsProbabilityMeasure μc := by
        simpa [μc] using ProbabilityTheory.cond_isProbabilityMeasure hzero
      infer_instance
  have hlevels : levels.card = ell := by simp [levels]
  letI : IsProbabilityMeasure U := by
    constructor
    dsimp [U]
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    rw [hlevels]
    exact ENNReal.div_self (by exact_mod_cast (show ell ≠ 0 by omega)) (by finiteness)
  haveI : IsFiniteMeasure P := by dsimp [P, bridgeLevelLaw, E, levels]; infer_instance
  let A := bridgeOptionWindow n N ⁻¹' S
  let B := W ⁻¹' (some ⁻¹' S)
  have hA : MeasurableSet A := measurableSet_bridgeOptionWindow_preimage n N S
  have hsome : MeasurableSet (some ⁻¹' S : Set (Fin (2 * N + 1) → ℤ × ℤ)) :=
    (Set.to_countable _).measurableSet
  have hB : MeasurableSet B := hsome.preimage hW
  have hpre : A ∆ B ⊆ Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad := by
    intro p hp
    rcases p with ⟨ω, K⟩
    simp only [A, B, Set.mem_symmDiff, Set.mem_preimage] at hp
    by_cases hω : ω ∈ E
    · by_cases hbad : K ∈ bad
      · exact Or.inr ⟨Set.mem_univ _, hbad⟩
      · have hK : K ∈ levels := by
          by_contra hk
          exact hbad (Or.inl hk)
        have hIcc := Finset.mem_Icc.mp hK
        have hboundary : ¬ (K < N ∨ ell < K + N) := by
          intro hb
          exact hbad (Or.inr hb)
        have hNK : N ≤ K := Nat.le_of_not_gt (fun h => hboundary (Or.inl h))
        have hKN : K + N ≤ ell := Nat.le_of_not_gt (fun h => hboundary (Or.inr h))
        have hwindow := bridgeOptionWindow_eq_some_of_interior hω hIcc.1 hIcc.2 hNK hKN
        have htotal := hagree ω K hω hIcc.1 hIcc.2 hNK hKN
        rw [hwindow, htotal] at hp
        rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact (h₂ (by simpa using h₁)).elim
        · exact (h₂ (by simpa using h₁)).elim
    · exact Or.inl ⟨hω, Set.mem_univ _⟩
  calc
    |P.real A - P.real B| ≤ P.real (A ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hB.nullMeasurableSet
    _ ≤ P.real (Eᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ bad) := measureReal_mono hpre
    _ ≤ 2 * (N : ℝ) / (ell : ℝ) := by
      change (bridgeLevelLaw n ell).real
        ((coneEvent (ell : ℤ) 0 n)ᶜ ×ˢ Set.univ ∪
          Set.univ ×ˢ ((Finset.Icc 1 ell : Set ℕ)ᶜ ∪
            {K : ℕ | K < N ∨ ell < K + N})) ≤ _
      exact bridgeLevelLaw_boundary_bad_bound n ell N hell

/-- Any total extension that agrees with finite bridge on every valid outcome agrees
with the raw vector on interior bridge outcomes. Helper toward corrected
`lem-disk-walk-conv` and the finite bridge ruling. -/
theorem agree_interior_of_agree_valid {n ell N : ℕ}
    (W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ))
    (hW : ∀ p x, bridgeOptionWindow n N p = some x → W p = x) :
    ∀ ω K, ω ∈ coneEvent (ell : ℤ) 0 n → 1 ≤ K → K ≤ ell →
      N ≤ K → K + N ≤ ell → W (ω, K) = bridgeRawWindow N (ω, K) := by
  intro ω K hω hK hKell hNK hKN
  exact hW (ω, K) (bridgeRawWindow N (ω, K))
    (bridgeOptionWindow_eq_some_of_interior hω hK hKell hNK hKN)



@[expose] noncomputable def cemeteryTargetReal (N : ℕ)
    (S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ))) : ℝ :=
  (uibhbotExcursionWindowLaw N).real (some ⁻¹' S)

/-- Unfolding the cemetery target recovers the target excursion-window law. -/
theorem cemeteryTargetReal_eq (N : ℕ)
    (S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ))) :
    cemeteryTargetReal N S = (uibhbotExcursionWindowLaw N).real (some ⁻¹' S) := rfl

/-- The target excursion-window law gives zero mass to the cemetery point. -/
theorem cemeteryTargetReal_none (N : ℕ) :
    cemeteryTargetReal N {none} = 0 := by
  have hset : some ⁻¹' ({none} : Set (Option (Fin (2 * N + 1) → ℤ × ℤ))) = ∅ := by
    ext x
    simp
  simp [cemeteryTargetReal, hset]

end DirectedDistances.RandomWalk
