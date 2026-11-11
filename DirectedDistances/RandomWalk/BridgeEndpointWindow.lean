/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDCodeRelabel
public import DirectedDistances.RandomWalk.QuadrantReturnProb
public import Mathlib.Probability.ConditionalProbability

/-! # Endpoint and boundary-window helpers for finite cone bridges

Helpers for the first-level time and the finite-domain boundary discussion in
At a uniform level, the radius-`N` window is inside the finite bridge domain
except on a level set of size at most `2N`. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped Classical
open scoped symmDiff

/-- Every source step changes the first coordinate by at most one. Helper for -/
theorem lazyTwoDimensionalStep_fst_abs_le_one (c : Fin 3) :
    |(lazyTwoDimensionalStep c).1| ≤ 1 := by
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

private theorem codeWalk_fst_step_abs_le_one (ω : ℕ → Fin 3) (t : ℕ) :
    |(codeWalk ω (t + 1)).1 - (codeWalk ω t).1| ≤ 1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω t)
  rw [Prod.fst_sub] at h
  rw [h]
  exact lazyTwoDimensionalStep_fst_abs_le_one (ω (t + 1))

private theorem codeWalk_fst_lower_bound (ω : ℕ → Fin 3) :
    ∀ t : ℕ, -(t : ℤ) ≤ (codeWalk ω t).1 := by
  intro t
  induction t with
  | zero => simp [codeWalk_zero]
  | succ t ih =>
      have hs := codeWalk_fst_step_abs_le_one ω t
      rw [abs_le] at hs
      omega

private theorem codeWalk_fst_tail_lower_bound (ω : ℕ → Fin 3) :
    ∀ s t : ℕ, s ≤ t → (codeWalk ω s).1 - ((t - s : ℕ) : ℤ) ≤
      (codeWalk ω t).1 := by
  intro s t hst
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst s
      simp [codeWalk_zero]
  | succ t ih =>
      by_cases heq : s = t + 1
      · subst s
        simp
      · have hst' : s ≤ t := by omega
        have hi := ih hst'
        have hs := codeWalk_fst_step_abs_le_one ω t
        rw [abs_le] at hs
        omega

/-- The first hit of level `-K` on a finite cone bridge occurs by time `n`,
`K` steps after time zero, and leaves at least `l-K` steps before the endpoint. -/
theorem coneEvent_fstFirstHit (l : ℤ) (n : ℕ) (K : ℕ)
    (hK1 : 1 ≤ K) (hKl : (K : ℤ) ≤ l) (ω : ℕ → Fin 3)
    (hω : ω ∈ coneEvent l 0 n) :
    ∃ T : ℕ, codeFstFirstHit (-(K : ℤ)) ω = T ∧ K ≤ T ∧ T ≤ n ∧
      (l - K) + T ≤ n := by
  classical
  have hend : (codeWalk ω n).1 = -l := by
    have h := hω.2
    change (l, 0) + codeWalk ω n = (0, 0) at h
    have := congrArg Prod.fst h
    simp only [Prod.fst_add] at this
    omega
  let P : ℕ → Prop := fun j => (codeWalk ω j).1 ≤ -(K : ℤ)
  have hcross : ∃ j, P j := ⟨n, by dsimp [P]; rw [hend]; omega⟩
  let T := Nat.find hcross
  have hTle : T ≤ n := Nat.find_min' hcross (by dsimp [P]; rw [hend]; omega)
  have hTbelow : (codeWalk ω T).1 ≤ -(K : ℤ) := Nat.find_spec hcross
  have hTlow : (-(T : ℤ)) ≤ (codeWalk ω T).1 := codeWalk_fst_lower_bound ω T
  have hTK : K ≤ T := by omega
  have hTeq : (codeWalk ω T).1 = -(K : ℤ) := by
    let t := T - 1
    have ht : T = t + 1 := by dsimp [t]; omega
    have hbefore : -(K : ℤ) < (codeWalk ω t).1 := by
      have hidx : t < Nat.find hcross := by
        have : t < T := by omega
        simpa [T] using this
      have hnot := Nat.find_min hcross hidx
      dsimp [P] at hnot
      omega
    have hbelow' : (codeWalk ω (t + 1)).1 ≤ -(K : ℤ) := by
      simpa [ht] using hTbelow
    have hs := codeWalk_fst_step_abs_le_one ω t
    rw [abs_le] at hs
    simpa [ht] using (show (codeWalk ω (t + 1)).1 = -(K : ℤ) by omega)
  have hex : ∃ j, (codeWalk ω j).1 = -(K : ℤ) := ⟨T, hTeq⟩
  have hfind_le : Nat.find hex ≤ T := Nat.find_min' hex hTeq
  have hT_le_find : T ≤ Nat.find hex := by
    have hhitP : P (Nat.find hex) := by
      dsimp [P]
      rw [Nat.find_spec hex]
    have hmin := Nat.find_min' hcross hhitP
    exact hmin
  have htime : codeFstFirstHit (-(K : ℤ)) ω = T := by
    have hfind : Nat.find hex = T := Nat.le_antisymm hfind_le hT_le_find
    simp [codeFstFirstHit, hex, hfind]
  have htail := codeWalk_fst_tail_lower_bound ω T n hTle
  have hlastime : (l - K : ℤ) + T ≤ n := by
    rw [hTeq, hend] at htail
    omega
  exact ⟨T, htime, hTK, hTle, by exact_mod_cast hlastime⟩

/-- If the selected level is at least `N` from both level boundaries, the
radius-`N` time window around its first hit lies in `[0,n]`. Helper for -/
theorem coneEvent_fstFirstHit_window (l : ℤ) (n N K : ℕ)
    (hK1 : 1 ≤ K) (hKl : (K : ℤ) ≤ l) (hNK : N ≤ K)
    (hKNl : (K : ℤ) + N ≤ l) (ω : ℕ → Fin 3)
    (hω : ω ∈ coneEvent l 0 n) :
    ∃ T : ℕ, codeFstFirstHit (-(K : ℤ)) ω = T ∧ N ≤ T ∧ T + N ≤ n := by
  obtain ⟨T, htime, hKT, hTn, hrem⟩ :=
    coneEvent_fstFirstHit l n K hK1 hKl ω hω
  refine ⟨T, htime, ?_, ?_⟩
  · omega
  · have hKN : (N : ℤ) ≤ l - K := by omega
    omega

/-- At most `2N` levels in `{1,…,l}` are within `N` of either boundary.
This is the exceptional-level count for the radius-`N` window in -/
theorem uniformLevelWindow_badLevels_card (l N : ℕ) :
    ((Finset.Icc 1 l).filter (fun K => K < N ∨ l < K + N)).card ≤ 2 * N := by
  classical
  let L := (Finset.Icc 1 l).filter (fun K => K < N)
  let R := (Finset.Icc 1 l).filter (fun K => l < K + N)
  let S := (Finset.Icc 1 l).filter (fun K => K < N ∨ l < K + N)
  have hsub : S ⊆ L ∪ R := by
    intro K hK
    simp only [S, L, R, Finset.mem_filter, Finset.mem_Icc] at hK ⊢
    rcases hK with ⟨⟨h1, hl⟩, hbad⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    rcases hbad with hbad | hbad
    · exact Or.inl ⟨⟨h1, hl⟩, hbad⟩
    · exact Or.inr ⟨⟨h1, hl⟩, hbad⟩
  have hLsub : L ⊆ Finset.Ico 0 N := by
    intro K hK
    simp only [L, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hK ⊢
    omega
  have hRsub : R ⊆ Finset.Ioc (l - N) l := by
    intro K hK
    simp only [R, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hK ⊢
    omega
  have hLcard : L.card ≤ N := by
    calc
      L.card ≤ (Finset.Ico 0 N).card := Finset.card_le_card hLsub
      _ = N := by simp
  have hRcard : R.card ≤ N := by
    calc
      R.card ≤ (Finset.Ioc (l - N) l).card := Finset.card_le_card hRsub
      _ = l - (l - N) := by simp
      _ ≤ N := by omega
  calc
    S.card ≤ (L ∪ R).card := Finset.card_le_card hsub
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ 2 * N := by omega

private theorem measurableSet_coneEvent_bridge (l : ℤ) (n : ℕ) :
    MeasurableSet (coneEvent l 0 n) := by
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

/-- Two measurable total extensions of the finite bridge window have laws that
differ by at most the probability of selecting a boundary level. This is the
convention-independence estimate for `lem-disk-walk-conv`,
hypothesis is needed: if the conditioning event has zero mass, its `cond`
measure is zero and the asserted estimate is immediate. The corrected lower
bound for Lemma 5.17 supplies positivity on the source domain when a genuine
conditional probability law is needed. -/
theorem bridgeWindow_extension_independent (l n N : ℕ) (hl : 1 ≤ l)
    (W W' : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ))
    (hW : Measurable W) (hW' : Measurable W')
    (hagree : ∀ ω K, ω ∈ coneEvent (l : ℤ) 0 n → K ∈ Finset.Icc 1 l →
      N ≤ K → K + N ≤ l → W (ω, K) = W' (ω, K))
    (B : Set (Fin (2 * N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    |(((ProbabilityTheory.cond iidCodeMeasure (coneEvent (l : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 l))).real (W ⁻¹' B)) -
      (((ProbabilityTheory.cond iidCodeMeasure (coneEvent (l : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 l))).real (W' ⁻¹' B))| ≤
      (2 * (N : ℝ)) / (l : ℝ) := by
  classical
  let E := coneEvent (l : ℤ) 0 n
  let levels : Finset ℕ := Finset.Icc 1 l
  let edge : Finset ℕ := levels.filter (fun K => K < N ∨ l < K + N)
  let μc := ProbabilityTheory.cond iidCodeMeasure E
  let U := Measure.uniformOfFinset levels
  let P := μc.prod U
  have hE : MeasurableSet E := by
    exact measurableSet_coneEvent_bridge (l : ℤ) n
  have hlevels : levels.card = l := by
    simp [levels]
  have hEdgeCount : edge.card ≤ 2 * N := by
    dsimp [edge, levels]
    exact uniformLevelWindow_badLevels_card l N
  have hcondEcomp : μc.real Eᶜ = 0 := by
    change ((ProbabilityTheory.cond iidCodeMeasure E) Eᶜ).toReal = 0
    rw [ProbabilityTheory.cond_apply hE iidCodeMeasure Eᶜ]
    simp
  have hcondTotal : μc.real Set.univ ≤ 1 := by
    by_cases hzero : iidCodeMeasure E = 0
    · simp [μc, Measure.real, ProbabilityTheory.cond, hzero]
    · letI : IsProbabilityMeasure (ProbabilityTheory.cond iidCodeMeasure E) :=
        ProbabilityTheory.cond_isProbabilityMeasure hzero
      simp [μc]
  have hUcomp : U.real (levels : Set ℕ)ᶜ = 0 := by
    change (Measure.uniformOfFinset levels ((levels : Set ℕ)ᶜ)).toReal = 0
    rw [Measure.uniformOfFinset_apply]
    simp
  have hUedge : U.real (edge : Set ℕ) = (edge.card : ℝ) / (l : ℝ) := by
    have hnum : levels.filter (fun K => K ∈ edge) = edge := by
      ext K
      simp [edge, Finset.mem_filter]
    change (Measure.uniformOfFinset levels (edge : Set ℕ)).toReal = _
    rw [Measure.uniformOfFinset_apply, ENNReal.toReal_div]
    · norm_cast
      rw [hnum, hlevels]
  have hUedge_le : U.real (edge : Set ℕ) ≤ (2 * (N : ℝ)) / (l : ℝ) := by
    rw [hUedge]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hEdgeCount
  have hUunion : U.real ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)) ≤
      (2 * (N : ℝ)) / (l : ℝ) := by
    calc
      U.real ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)) ≤
          U.real (levels : Set ℕ)ᶜ + U.real (edge : Set ℕ) :=
        measureReal_union_le _ _
      _ ≤ (2 * (N : ℝ)) / (l : ℝ) := by rw [hUcomp, zero_add]; exact hUedge_le
  let bad : Set ((ℕ → Fin 3) × ℕ) :=
    (Eᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)))
  have hpre : (W ⁻¹' B) ∆ (W' ⁻¹' B) ⊆ bad := by
    intro p hp
    rcases p with ⟨ω, K⟩
    simp only [Set.mem_symmDiff, Set.mem_preimage] at hp
    by_cases hω : ω ∈ E
    · by_cases hK : K ∈ levels
      · by_cases hKbad : K ∈ edge
        · right
          simp [bad, hKbad]
        · have hnot : ¬ (K < N ∨ l < K + N) := by
            intro hbad
            apply hKbad
            exact Finset.mem_filter.mpr ⟨hK, hbad⟩
          have hgoodN : N ≤ K := by omega
          have hgoodL : K + N ≤ l := by omega
          have hK' : K ∈ Finset.Icc 1 l := by simpa [levels] using hK
          have heq := hagree ω K (by simpa [E] using hω) hK'
            hgoodN hgoodL
          rcases hp with hp | hp
          · exact False.elim (hp.2 (heq ▸ hp.1))
          · exact False.elim (hp.2 (heq.symm ▸ hp.1))
      · right
        simp [bad, hK]
    · left
      simp [bad, hω]
  have hbadMeas : MeasurableSet bad := by
    apply MeasurableSet.union
    · exact hE.compl.prod MeasurableSet.univ
    · apply MeasurableSet.prod MeasurableSet.univ
      apply MeasurableSet.union
      · exact (Set.to_countable _).measurableSet
      · exact (Set.to_countable _).measurableSet
  have hbadMass : P.real bad ≤ (2 * (N : ℝ)) / (l : ℝ) := by
    calc
      P.real bad ≤ P.real (Eᶜ ×ˢ Set.univ) +
          P.real (Set.univ ×ˢ ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ))) := by
        dsimp [bad]
        exact measureReal_union_le _ _
      _ = μc.real Eᶜ * U.real Set.univ +
          μc.real Set.univ * U.real ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)) := by
        rw [MeasureTheory.measureReal_prod_prod, MeasureTheory.measureReal_prod_prod]
      _ ≤ (2 * (N : ℝ)) / (l : ℝ) := by
        rw [hcondEcomp]
        simp only [zero_mul, zero_add]
        calc
          μc.real Set.univ * U.real ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)) ≤
              1 * U.real ((levels : Set ℕ)ᶜ ∪ (edge : Set ℕ)) :=
            mul_le_mul_of_nonneg_right hcondTotal measureReal_nonneg
          _ ≤ (2 * (N : ℝ)) / (l : ℝ) := by simpa using hUunion
  have hμczero_of_zero (hzero : iidCodeMeasure E = 0) : μc = 0 := by
    simp [μc, ProbabilityTheory.cond, hzero]
  haveI : IsFiniteMeasure μc := by
    by_cases hzero : iidCodeMeasure E = 0
    · rw [hμczero_of_zero hzero]
      infer_instance
    · haveI : IsProbabilityMeasure μc := by
        simpa [μc] using ProbabilityTheory.cond_isProbabilityMeasure hzero
      infer_instance
  haveI : IsProbabilityMeasure U := by
    constructor
    change U Set.univ = 1
    dsimp [U]
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    rw [hlevels]
    exact ENNReal.div_self (by exact_mod_cast (show l ≠ 0 by omega)) (by finiteness)
  haveI : IsFiniteMeasure P := by
    dsimp [P]
    infer_instance
  have hsymmMeas : MeasurableSet ((W ⁻¹' B) ∆ (W' ⁻¹' B)) := by
    exact (hW hB).symmDiff (hW' hB)
  calc
    |P.real (W ⁻¹' B) - P.real (W' ⁻¹' B)| ≤
        P.real ((W ⁻¹' B) ∆ (W' ⁻¹' B)) :=
      abs_measureReal_sub_le_measureReal_symmDiff (hW hB).nullMeasurableSet
        (hW' hB).nullMeasurableSet
    _ ≤ P.real bad := measureReal_mono hpre
    _ ≤ (2 * (N : ℝ)) / (l : ℝ) := hbadMass

end DirectedDistances.RandomWalk
