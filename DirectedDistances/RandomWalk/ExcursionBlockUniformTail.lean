module

public import DirectedDistances.RandomWalk.UIBHBOTBackwardRUnboundedAE
public import DirectedDistances.KMSW.UIBHBOTBackwardNonrecord
import DirectedDistances.RandomWalk.ExcursionSkeletonReindex
import DirectedDistances.RandomWalk.ExcursionPassageCounts
import DirectedDistances.Probability.GeometricGapAntiConcentration




public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open DirectedDistances.Probability
open scoped ENNReal BigOperators

private theorem lintegral_event {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : α → Prop) [DecidablePred P] (hP : MeasurableSet {a | P a}) :
    (∫⁻ a, (if P a then (1 : ℝ≥0∞) else 0) ∂μ) = μ {a | P a} := by
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    (lintegral_indicator_one (μ := μ) hP)

private theorem passage_gap_gt {A k : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage k u) (hAk : 2 * A ≤ k)
    (hg : ((excursionSkeleton u).length : ℝ) / 2 <
      ((excursionSkeletonGapLengths u).sum : ℝ)) :
    (A : ℤ) < uibhbotWordRDisplacement u := by
  have hr := congrArg (fun z : ℤ => (z : ℝ)) (excursionPassage_rdisp hu)
  push_cast at hr
  simp only [List.map_map, Function.comp_def, Int.cast_natCast, ← Nat.cast_list_sum] at hr
  have hAk' : 2 * (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast hAk
  have hlt : (A : ℝ) < (uibhbotWordRDisplacement u : ℝ) := by linarith
  exact_mod_cast hlt

private theorem validSkel_length_ge {k : ℕ} {s : List (Fin 3)}
    (hs : ValidSkel k s) : k ≤ s.length := by
  have he : excursionSkeleton s = s := by
    exact List.filter_eq_self.mpr (by simpa using hs.1)
  have hl := excursionPassage_skeleton_length hs.2
  rw [he] at hl
  omega

private theorem gap_lintegral_lower {c : ℝ}
    (hc : ∀ M : ℕ, 1 ≤ M → c ≤
      ((Measure.pi (fun _ : Fin M => geomTwoThirds))
        {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)}).toReal)
    (M : ℕ) (hM : 1 ≤ M) :
    ENNReal.ofReal c ≤ ∫⁻ g,
      (if (M : ℝ) / 2 < ∑ i, (g i : ℝ) then (1 : ℝ≥0∞) else 0)
        ∂(Measure.pi fun _ : Fin M => geomTwoThirds) := by
  classical
  rw [lintegral_event _ _ MeasurableSet.of_discrete]
  have hset : {g : Fin M → ℕ | (M : ℝ) / 2 < ∑ i, (g i : ℝ)} =
      {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)} := by
    ext g
    change ((M : ℝ) / 2 < ∑ i, (g i : ℝ)) ↔
      0 < ∑ i, ((g i : ℝ) - 1 / 2)
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact ENNReal.ofReal_le_of_le_toReal (hc M hM)

open Classical in
private theorem validSkel_mass {k : ℕ} (hk : 1 ≤ k) :
    (∑' s : List (Fin 3),
      if ValidSkel k s then (1 / 2 : ℝ≥0∞) ^ s.length else 0) = 1 := by
  classical
  calc
    _ = ∑' u : List (Fin 3),
        if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0 := by
      simpa using (tsum_passage_eq hk (fun _ _ => 1)).symm
    _ = 1 := by simpa using (lintegral_flat hk (fun _ => 1)).symm



theorem exists_uniform_pos_prob_partialSum_gt :
    ∃ c : ℝ, 0 < c ∧ ∀ A k : ℕ, 1 ≤ k → 2 * A ≤ k →
      c ≤ (Measure.pi (fun _ : Fin k => excursionWordLaw)
        {w | (A : ℤ) < ∑ j, uibhbotWordRDisplacement (w j)}).toReal := by
  classical
  obtain ⟨c, hc, hgap⟩ := exists_uniform_gap_sum_pos
  refine ⟨c, hc, ?_⟩
  intro A k hk hAk
  let F : ℕ → ℝ → ℝ≥0∞ := fun M x => if (M : ℝ) / 2 < x then 1 else 0
  let weight : List (Fin 3) → ℝ≥0∞ := fun s =>
    if ValidSkel k s then (1 / 2 : ℝ≥0∞) ^ s.length else 0
  have hpoint (u : List (Fin 3)) (hu : excursionPassage k u) :
      F (excursionSkeleton u).length ((excursionSkeletonGapLengths u).sum : ℝ) ≤
        (if (A : ℤ) < uibhbotWordRDisplacement u then (1 : ℝ≥0∞) else 0) := by
    dsimp [F]
    split_ifs with hg hr hr
    · exact le_rfl
    · exact (hr (passage_gap_gt hu hAk hg)).elim
    · exact bot_le
    · exact le_rfl
  have hmass : (∑' s, weight s) = 1 := validSkel_mass hk
  have hbound : ENNReal.ofReal c ≤
      ∑' s, weight s * ∫⁻ g, F s.length (∑ i, (g i : ℝ))
        ∂(Measure.pi fun _ : Fin s.length => geomTwoThirds) := by
    calc
      ENNReal.ofReal c = (∑' s, weight s) * ENNReal.ofReal c := by rw [hmass, one_mul]
      _ = ∑' s, weight s * ENNReal.ofReal c := ENNReal.tsum_mul_right.symm
      _ ≤ _ := by
        apply tsum_le_tsum
        intro s
        by_cases hs : ValidSkel k s
        · have hlen : 1 ≤ s.length := hk.trans (validSkel_length_ge hs)
          exact mul_le_mul_right (gap_lintegral_lower hgap s.length hlen) (weight s)
        · simp only [weight, ite_eq_right hs, zero_mul, le_refl]
  have hflat :
      (Measure.pi (fun _ : Fin k => excursionWordLaw))
        {w | (A : ℤ) < ∑ j, uibhbotWordRDisplacement (w j)} =
      ∑' u, (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
        (if (A : ℤ) < uibhbotWordRDisplacement u then (1 : ℝ≥0∞) else 0) := by
    calc
      _ = ∫⁻ w, (if (A : ℤ) < ∑ j, uibhbotWordRDisplacement (w j)
          then (1 : ℝ≥0∞) else 0)
            ∂(Measure.pi fun _ : Fin k => excursionWordLaw) :=
        (lintegral_event _ _ MeasurableSet.of_discrete).symm
      _ = ∫⁻ w, (if (A : ℤ) < uibhbotWordRDisplacement ((List.ofFn w).flatten)
          then (1 : ℝ≥0∞) else 0)
            ∂(Measure.pi fun _ : Fin k => excursionWordLaw) := by
        simp_rw [partialSum_eq_rdisp_cat]
      _ = _ := lintegral_flat hk
        (fun u => if (A : ℤ) < uibhbotWordRDisplacement u then 1 else 0)
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  rw [hflat]
  calc
    ENNReal.ofReal c ≤
        ∑' s, weight s * ∫⁻ g, F s.length (∑ i, (g i : ℝ))
          ∂(Measure.pi fun _ : Fin s.length => geomTwoThirds) := hbound
    _ = ∑' u, (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
        F (excursionSkeleton u).length ((excursionSkeletonGapLengths u).sum : ℝ) :=
      (tsum_passage_eq hk F).symm
    _ ≤ _ := by
      apply tsum_le_tsum
      intro u
      by_cases hu : excursionPassage k u
      · exact mul_le_mul_right (hpoint u hu) _
      · simp only [ite_eq_right hu, zero_mul, le_refl]



theorem uibhbotWordFamilyLaw_backwardRUnbounded :
    uibhbotWordFamilyLaw
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} = 1 := by
  exact uibhbotWordFamilyLaw_backwardRUnbounded_of_uniformTail
    exists_uniform_pos_prob_partialSum_gt



theorem uibhbotWordFamilyLaw_ae_hP2 :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
          0 ≤ t + (M : ℤ) ∧
          (let k := (t + (M : ℤ)).toNat
           KMSW.minR (KMSW.shiftedStream (KMSW.uibhbotCodeWord w
             (fun k => (hw k).1)) M) k <
             KMSW.R (KMSW.shiftedStream (KMSW.uibhbotCodeWord w
               (fun k => (hw k).1)) M) k) := by
  apply KMSW.uibhbotWordFamilyLaw_ae_hP2_of_pos
  rw [uibhbotWordFamilyLaw_backwardRUnbounded]
  exact zero_lt_one

end DirectedDistances.RandomWalk
