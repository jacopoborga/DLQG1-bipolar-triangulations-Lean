module

public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.PaperProofs.Section7.CellSDPLowerBoundary
import DirectedDistances.PaperProofs.Section7.SDPTri
import DirectedDistances.PaperProofs.Section7.CellSDPUpperSeam
import DirectedDistances.Recursive.CellSDPLowerConditional

/-! Supporting lemmas for paper labels `lem-cell-sdp-lower` (see CORRESPONDENCE.md). -/

/-! an explicit hypothesis. The hit-indexed carrier remains subject to F1/F4 of the imported
Busemann characterization. Probability comparisons use outer-measure monotonicity; no
measurability assertion about the final existential witness event is required. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.Recursive

private theorem negative_busemann_stage :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n k : ℕ, 1 ≤ k →
      codeSndFirstHit (-(k : ℤ)) ω ≤ (n : ℕ∞) →
      ∀ t : ℝ, 0 < t →
      (∃ r : ℕ, r ≤ k ∧ (busemannSDPMeasurableVersion ω r : ℝ) ≤ -t) →
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
          t ≤
            ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
              StagePresentVertex (fun i => ω (i + 1)) n)
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ) := by
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion, lem_sdp_tri] with ω hω htri
  obtain ⟨h, hX⟩ := hω
  intro n k hk ht t htpos hr
  obtain ⟨r, hrk, hr⟩ := hr
  have hr1 : 1 ≤ r := by
    by_contra hh
    have hr0 : r = 0 := by omega
    subst r
    rw [Nat.cast_zero, hX.1, Int.cast_zero] at hr
    linarith
  have htk := boundaryHitTime_le_of_codeSndFirstHit_le ω h k n hk ht
  have htr : boundaryHitTime (fun i => ω (i + 1)) h (r : ℤ) ≤ n :=
    (boundaryHitTime_right_mono _ h (by exact_mod_cast hr1)
      (by exact_mod_cast hrk)).trans htk
  have hreach := stage_boundary_reachable _ h r n htr
  have hfin : sdp (⟨boundaryVertex _ h 0⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
      ⟨boundaryVertex _ h (r : ℤ)⟩ ≠ ⊤ := by
    intro hh
    exact sdp_eq_top_iff_not_reachable.mp hh hreach
  have hcmpNat := ENat.toNat_le_toNat
    (sdp_stage_ge_sdp_limit (fun i => ω (i + 1)) n
      ⟨boundaryVertex _ h 0⟩ ⟨boundaryVertex _ h (r : ℤ)⟩) hfin
  have hb := (htri h _ hX 0 (r : ℤ) (by omega) (by omega)).2
  rw [hX.1, zero_sub] at hb
  have hbReal : -(busemannSDPMeasurableVersion ω r : ℝ) ≤
      ((sdp (boundaryPresentVertex _ h 0)
        (boundaryPresentVertex _ h (r : ℤ))).toNat : ℝ) := by
    exact_mod_cast hb
  have hcmpReal :
      ((sdp (boundaryPresentVertex _ h 0)
        (boundaryPresentVertex _ h (r : ℤ))).toNat : ℝ) ≤
      ((sdp (⟨boundaryVertex _ h 0⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
        ⟨boundaryVertex _ h (r : ℤ)⟩).toNat : ℝ) := by
    exact_mod_cast hcmpNat
  exact ⟨h, r, hr1, boundaryVertex_mem_LR_endpoint_of_hit h hr1 hrk htk,
    by linarith⟩

private theorem stage_small_bound (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n : ℕ) (t : ℝ) (ht : t ≤ 1) :
    ∃ r : ℕ, 1 ≤ r ∧
      (∃ e ∈ (kmswStage w n).LR,
        (kmswStage w n).west e = boundaryVertex w h (r : ℤ) ∨
          (kmswStage w n).east e = boundaryVertex w h (r : ℤ)) ∧
      t ≤ ((sdp (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
        ⟨boundaryVertex w h (r : ℤ)⟩).toNat : ℝ) := by
  have hLR : 0 ∈ (kmswStage w n).LR := by
    rw [kmswStage_LR_eq]
    exact List.mem_map.mpr ⟨0, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩
  refine ⟨1, le_rfl, ⟨0, hLR, Or.inr ?_⟩, ?_⟩
  · exact (initial_edge_endpoints w n).2.trans (boundaryVertex_one w h).symm
  · simpa only [Nat.cast_one, boundaryVertex_zero, boundaryVertex_one,
      sdp_stage_x0_x1, ENat.toNat_one, Nat.cast_one] using ht





theorem cell_sdp_lower_conditional
    (hstable : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)}) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real
        {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
              StagePresentVertex (fun i => ω (i + 1)) n)
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)} := by
  intro δ hδ
  classical
  let E := fun (t : ℝ) (n : ℕ) =>
    {ω : ℕ → Fin 3 | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
          t ≤
            ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
              StagePresentVertex (fun i => ω (i + 1)) n)
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)}
  have hE_mono (n : ℕ) {s t : ℝ} (hst : s ≤ t) : E t n ⊆ E s n := by
    rintro ω ⟨h, r, hr, he, hd⟩
    exact ⟨h, r, hr, he, hst.trans hd⟩
  obtain ⟨As, hAs, kstar, hstable⟩ := hstable δ hδ
  obtain ⟨Ab, hAb, n₀, hbdy⟩ := exists_boundary_time_le_prob δ hδ
  let a : ℝ := As ^ (-(1 / 2 : ℝ))
  let b : ℝ := Ab ^ (-(1 / 2 : ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos (by linarith) _
  have hb : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  let c : ℝ := a * b ^ (3 / 4 : ℝ)
  have hc : 0 < c := mul_pos ha (Real.rpow_pos_of_pos hb _)
  let q : ℝ := ((kstar : ℝ) + 1) / b
  let N : ℕ := max n₀ ⌈q ^ 2⌉₊ + 1
  have hlarge : ∀ n : ℕ, N ≤ n → 1 - δ ≤ iidCodeMeasure.real (E (c *
      (n : ℝ) ^ (3 / 8 : ℝ)) n) := by
    intro n hn
    have hn₀ : n₀ ≤ n := by dsimp [N] at hn; omega
    have hqn : q ^ 2 ≤ (n : ℝ) := by
      have hceil := Nat.le_ceil (q ^ 2)
      have hle : ⌈q ^ 2⌉₊ ≤ n := by dsimp [N] at hn; omega
      exact hceil.trans (by exact_mod_cast hle)
    have hqsqrt : q ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hqn
    have hksqrt : (kstar : ℝ) + 1 ≤ b * Real.sqrt n := by
      have hh := (div_le_iff₀ hb).mp hqsqrt
      simpa only [mul_comm] using hh
    let k : ℕ := ⌈b * Real.sqrt n⌉₊
    have hkle : b * Real.sqrt n ≤ (k : ℝ) := Nat.le_ceil _
    have hkstar : kstar ≤ k := by
      have hh : (kstar : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast hh
    have hk : 1 ≤ k := by
      have hh : (1 : ℝ) ≤ (k : ℝ) := by
        have : (0 : ℝ) ≤ kstar := Nat.cast_nonneg _
        linarith
      exact_mod_cast hh
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hscale : c * (n : ℝ) ^ (3 / 8 : ℝ) ≤ a * (k : ℝ) ^ (3 / 4 : ℝ) := by
      have hh := Real.rpow_le_rpow (mul_nonneg hb.le (Real.sqrt_nonneg _))
        hkle (by norm_num : (0 : ℝ) ≤ 3 / 4)
      have heq : (Real.sqrt (n : ℝ)) ^ (3 / 4 : ℝ) =
          (n : ℝ) ^ (3 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
      rw [Real.mul_rpow hb.le (Real.sqrt_nonneg _), heq] at hh
      dsimp [c]
      calc a * b ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ) =
          a * (b ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ)) := by ring
        _ ≤ a * (k : ℝ) ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hh ha.le
    let S : Set (ℕ → Fin 3) := {ω | ∃ r : ℕ, r ≤ k ∧
      (busemannSDPMeasurableVersion ω r : ℝ) ≤ -(a * (k : ℝ) ^ (3 / 4 : ℝ))}
    let B : Set (ℕ → Fin 3) := {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (n : ℕ∞)}
    have hS : MeasurableSet S := by
      dsimp [S]
      simp only [Set.ofPred_exists]
      refine MeasurableSet.iUnion fun r => ?_
      by_cases hr : r ≤ k
      · simp only [hr, true_and]
        exact measurableSet_le
          ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
            (measurable_busemannSDPMeasurableVersion r)) measurable_const
      · simp only [hr, false_and, Set.ofPred_false, MeasurableSet.empty]
    have hprobS : 1 - δ / 2 ≤ iidCodeMeasure.real S := by
      simpa only [S, a, neg_mul] using hstable k hkstar
    have hprobB : 1 - δ / 2 ≤ iidCodeMeasure.real B := hbdy n hn₀
    have hsum := measureReal_union_add_inter' (μ := iidCodeMeasure) (t := B) hS
    have hunion : iidCodeMeasure.real (S ∪ B) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := iidCodeMeasure) (Set.subset_univ (S ∪ B)))
    have hinter : 1 - δ ≤ iidCodeMeasure.real (S ∩ B) := by linarith
    have hincl : S ∩ B ≤ᵐ[iidCodeMeasure] E (c * (n : ℝ) ^ (3 / 8 : ℝ)) n := by
      filter_upwards [negative_busemann_stage] with ω hω
      intro hωSB
      apply hE_mono n hscale
      exact hω n k hk hωSB.2 _ (mul_pos ha (Real.rpow_pos_of_pos hkpos _)) hωSB.1
    have hmeasure : iidCodeMeasure.real (S ∩ B) ≤
        iidCodeMeasure.real (E (c * (n : ℝ) ^ (3 / 8 : ℝ)) n) :=
      ENNReal.toReal_mono (by finiteness) (measure_mono_ae hincl)
    exact hinter.trans hmeasure
  let A : ℝ := 2 + c⁻¹ + (N : ℝ) ^ (3 / 8 : ℝ)
  have hNpow : 0 ≤ (N : ℝ) ^ (3 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA : 1 < A := by
    dsimp [A]
    have : 0 < c⁻¹ := inv_pos.mpr hc
    linarith
  have hApos : 0 < A := by linarith
  have hcinv : c⁻¹ ≤ A := by dsimp [A]; linarith
  have hNleA : (N : ℝ) ^ (3 / 8 : ℝ) ≤ A := by
    dsimp [A]
    have : 0 < c⁻¹ := inv_pos.mpr hc
    linarith
  have hAc : A⁻¹ ≤ c := by
    calc A⁻¹ ≤ (c⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hc) hcinv
      _ = c := inv_inv c
  refine ⟨A, hA, fun n _hn => ?_⟩
  change 1 - δ ≤ iidCodeMeasure.real (E (A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ)) n)
  by_cases hn : N ≤ n
  · have hs : A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤ c * (n : ℝ) ^ (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right hAc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact (hlarge n hn).trans (measureReal_mono (hE_mono n hs))
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) hnN
      (by norm_num : (0 : ℝ) ≤ 3 / 8)
    have ht : A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤ 1 := by
      calc A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤ A⁻¹ * A :=
          mul_le_mul_of_nonneg_left (hp.trans hNleA) (inv_nonneg.mpr hApos.le)
        _ = 1 := inv_mul_cancel₀ hApos.ne'
    have hfull : Set.univ ≤ᵐ[iidCodeMeasure]
        E (A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ)) n := by
      filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω _
      obtain ⟨r, hr, he, hd⟩ := stage_small_bound _ hω n _ ht
      exact ⟨hω, r, hr, he, hd⟩
    have hprob : 1 ≤ iidCodeMeasure.real
        (E (A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ)) n) := by
      have hh := ENNReal.toReal_mono (by finiteness :
        iidCodeMeasure (E (A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ)) n) ≠ ⊤)
        (measure_mono_ae hfull)
      simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using hh
    linarith

end DirectedDistances.PaperProofs.Section7
