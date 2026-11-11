module

public import DirectedDistances.Recursive.LDPFluctuationOfItems
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperShiftedBusemann
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryTail
import DirectedDistances.KMSW.KMSWMeasurability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

private theorem process_event_measurable (k : ℕ) (t : ℝ) :
    MeasurableSet {f : ℤ → ℤ | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(f l : ℝ)| ≤ t} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp (measurable_pi_apply l))
    measurable_const

private theorem three_events (B E F : Set (ℕ → Fin 3))
    (hB : MeasurableSet B) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (b e f : ℝ) (hb : 1 - b ≤ iidCodeMeasure.real B)
    (he : 1 - e ≤ iidCodeMeasure.real E) (hf : 1 - f ≤ iidCodeMeasure.real F) :
    1 - (b + e + f) ≤ iidCodeMeasure.real (B ∩ E ∩ F) := by
  have hu := measureReal_union_le (μ := iidCodeMeasure) (Bᶜ ∪ Eᶜ) Fᶜ
  have hv := measureReal_union_le (μ := iidCodeMeasure) Bᶜ Eᶜ
  have hc := measureReal_compl (μ := iidCodeMeasure) ((hB.inter hE).inter hF)
  rw [probReal_univ] at hc
  have hsets : (B ∩ E ∩ F)ᶜ = Bᶜ ∪ Eᶜ ∪ Fᶜ := by simp only [Set.compl_inter]
  rw [hsets] at hc
  rw [measureReal_compl hB, measureReal_compl hE, probReal_univ] at hv
  rw [measureReal_compl hF, probReal_univ] at hu
  linarith only [hu, hv, hc, hb, he, hf]

private theorem cutoff_scale (ε A : ℝ) (n : ℕ) (hε : 0 < ε) (hA : 1 < A)
    (hn : 1 ≤ n) (hlarge : 36 ≤ A ^ (ε / 4)) :
    A ^ (1 - ε) *
        ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
      A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 := by
  have hA0 : 0 < A := by linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let T := A ^ (ε / 2) * Real.sqrt (n : ℝ)
  have hT : 1 ≤ T := by
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hA.le (by linarith)) ((Real.le_sqrt (by norm_num) hn0).2 (by nlinarith))
  have hk : ((⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * T := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ T)
    push_cast
    linarith only [hh, hT]
  have hp := Real.rpow_le_rpow (by positivity :
    0 ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ)) hk (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hthree : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 9 := by
    calc
      (3 : ℝ) ^ (3 / 2 : ℝ) ≤ (3 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by norm_num
  have hpow : (3 * T) ^ (3 / 2 : ℝ) =
      (3 : ℝ) ^ (3 / 2 : ℝ) * A ^ (3 * ε / 4) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    dsimp [T]
    rw [Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hA0.le, ← Real.rpow_mul hn0]
    rw [show ε / 2 * (3 / 2 : ℝ) = 3 * ε / 4 by ring,
      show (1 / (2 : ℝ)) * (3 / 2) = 3 / 4 by norm_num]
    ring
  have hcombine : A ^ (1 - ε) * A ^ (3 * ε / 4) = A ^ (1 - ε / 4) := by
    rw [← Real.rpow_add hA0]
    congr 1; ring
  have hcancel : A ^ (1 - ε / 4) * A ^ (ε / 4) = A := by
    rw [← Real.rpow_add hA0]
    convert Real.rpow_one A using 1; congr 1; ring
  have hbound : 36 * A ^ (1 - ε / 4) ≤ A := by
    calc
      36 * A ^ (1 - ε / 4) ≤ A ^ (ε / 4) * A ^ (1 - ε / 4) := by
        exact mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hA0.le _)
      _ = A := by rw [mul_comm, hcancel]
  change A ^ (1 - ε) * ((⌈T⌉₊ + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ _
  calc
    _ ≤ A ^ (1 - ε) * (3 * T) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hA0.le _)
    _ ≤ 9 * A ^ (1 - ε / 4) * (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hpow, ← mul_assoc, ← mul_assoc]
      calc
        _ ≤ A ^ (1 - ε) * 9 * A ^ (3 * ε / 4) * (n : ℝ) ^ (3 / 4 : ℝ) := by
          gcongr
        _ = _ := by rw [mul_assoc (A ^ (1 - ε)) 9, mul_comm 9, ← mul_assoc,
          hcombine]; ring
    _ ≤ A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 := by
      nlinarith only [mul_le_mul_of_nonneg_right hbound
        (Real.rpow_nonneg hn0 (3 / 4 : ℝ))]

private theorem gaussian_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ A : ℝ in atTop,
      Real.exp (-((A ^ (ε / 2)) ^ 2 / 32)) ≤ A ^ (-(2 / 3 : ℝ) + ε) := by
  have hh := ((isLittleO_exp_neg_mul_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 32) ((-(2 / 3 : ℝ) + ε) / ε)).comp_tendsto
    (tendsto_rpow_atTop hε)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with A hA hpos
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hpos.le _) _), one_mul] at hA
  have he : (A ^ (ε / 2)) ^ 2 = A ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [← Real.rpow_mul hpos.le,
    show ε * ((-(2 / 3 : ℝ) + ε) / ε) = -(2 / 3 : ℝ) + ε by
      field_simp] at hA
  have hexp : -((A ^ (ε / 2)) ^ 2 / 32) = -(1 / 32 : ℝ) * A ^ ε := by
    rw [he]
    ring
  rw [hexp]
  exact hA




theorem cell_ldp_upper_good_event
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0))
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω : ℕ → Fin 3 |
            (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
            ∀ l : ℤ,
              |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
              |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
                  A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
              |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
                  A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} := by
  classical
  intro ε hε hεlt
  obtain ⟨C₀, htail⟩ := ldp_fluctuation_of_items hind hstatL hsym
  let D := max C₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hCD : C₀ ≤ D := le_max_left _ _
  have hlarge : ∀ᶠ A : ℝ in atTop, 36 ≤ A ^ (ε / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < ε / 4)).eventually
      (eventually_ge_atTop 36)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlarge.and (gaussian_eventually ε hε))
  let C := max (4 + 2 * D) ((max T 1) ^ ((2 / 3 : ℝ) - ε))
  have hC : 0 < C := lt_of_lt_of_le (by linarith only [hD] : 0 < 4 + 2 * D)
    (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn A hA
  have hA0 : 0 < A := by linarith
  by_cases hAT : max T 1 ≤ A
  · have hcut := (hT A ((le_max_left T 1).trans hAT)).1
    have hgauss := (hT A ((le_max_left T 1).trans hAT)).2
    let k : ℕ := ⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1
    let t : ℝ := A * (n : ℝ) ^ (3 / 4 : ℝ) / 4
    let S : Set (ℤ → ℤ) := {f | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k → |(f l : ℝ)| ≤ t}
    let E : Set (ℕ → Fin 3) := {ω | busemannLDPMeasurableVersion ω ∈ S}
    let F : Set (ℕ → Fin 3) :=
      {ω | busemannLDPMeasurableVersion (codeShift n ω) ∈ S}
    let B : Set (ℕ → Fin 3) := {ω |
      ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ)}
    have hS : MeasurableSet S := process_event_measurable k t
    have hm : Measurable busemannLDPMeasurableVersion :=
      measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion
    have hE : MeasurableSet E := hS.preimage hm
    have hF : MeasurableSet F := hS.preimage (hm.comp (measurable_codeShift n))
    have hB : MeasurableSet B := by
      exact measurableSet_kmswStage_shift n (fun s =>
        (s.UL.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        (s.UR.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        (s.LL.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        (s.LR.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ))
    have hparam : 1 < A ^ (1 - ε) := Real.one_lt_rpow hA (by linarith)
    have hfluc := htail k (by dsimp [k]; omega) (A ^ (1 - ε)) hparam
    have hscale := cutoff_scale ε A n hε hA hn hcut
    have hsub : {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
          A ^ (1 - ε) * (k : ℝ) ^ (3 / 2 : ℝ)} ⊆ E := by
      intro ω hω l hl hl'
      exact (hω l hl hl').trans hscale
    have hpow : (A ^ (1 - ε)) ^ (-(2 / 3 : ℝ)) ≤ A ^ (-(2 / 3 : ℝ) + ε) := by
      rw [← Real.rpow_mul hA0.le]
      exact Real.rpow_le_rpow_of_exponent_le hA.le (by linarith)
    have hp : 1 - D * A ^ (-(2 / 3 : ℝ) + ε) ≤ iidCodeMeasure.real E := by
      have hmul := mul_le_mul hCD hpow
        (Real.rpow_nonneg (Real.rpow_nonneg hA0.le _) _) hD
      have hmono := measureReal_mono (μ := iidCodeMeasure) hsub
      linarith only [hfluc, hmul, hmono]
    have hpF : 1 - D * A ^ (-(2 / 3 : ℝ) + ε) ≤ iidCodeMeasure.real F := by
      have heq : iidCodeMeasure.real F = iidCodeMeasure.real E :=
        congrArg ENNReal.toReal (iidCodeMeasure_busemannCodeShift_preimage n hS)
      rw [heq]
      exact hp
    have hpB : 1 - 4 * A ^ (-(2 / 3 : ℝ) + ε) ≤ iidCodeMeasure.real B := by
      have hb := kmswBoundary_lengths_source_scale_tail A (ε / 2) n hA
        (by linarith) hn
      change _ ≤ iidCodeMeasure.real B at hb
      linarith only [hb, hgauss]
    have hj := three_events B E F hB hE hF _ _ _ hpB hp hpF
    have hsubfinal : B ∩ E ∩ F ⊆ {ω : ℕ → Fin 3 | ω ∈ B ∧
        ∀ l : ℤ, |l| ≤ (k : ℤ) →
          |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ t ∧
          |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤ t} := by
      rintro ω ⟨⟨hb, he⟩, hf⟩
      refine ⟨hb, fun l hl => ?_⟩
      have hh := abs_le.mp hl
      exact ⟨he l hh.1 hh.2, hf l hh.1 hh.2⟩
    have hmono := measureReal_mono (μ := iidCodeMeasure) hsubfinal
    have hcoef : (4 + 2 * D) * A ^ (-(2 / 3 : ℝ) + ε) ≤
        C * A ^ (-(2 / 3 : ℝ) + ε) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hA0.le _)
    change _ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 | ω ∈ B ∧
      ∀ l : ℤ, |l| ≤ (k : ℤ) →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ t ∧
        |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤ t}
    linarith only [hj, hmono, hcoef]
  · have hTpos : 0 < max T 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hsmall := Real.rpow_le_rpow_of_nonpos hA0 (le_of_not_ge hAT)
      (by linarith : -(2 / 3 : ℝ) + ε ≤ 0)
    have hproduct : (max T 1) ^ ((2 / 3 : ℝ) - ε) *
        (max T 1) ^ (-(2 / 3 : ℝ) + ε) = 1 := by
      rw [← Real.rpow_add hTpos]
      convert Real.rpow_zero (max T 1) using 1; congr 1; ring
    have hone : 1 ≤ C * A ^ (-(2 / 3 : ℝ) + ε) := by
      calc
        1 = (max T 1) ^ ((2 / 3 : ℝ) - ε) *
            (max T 1) ^ (-(2 / 3 : ℝ) + ε) := hproduct.symm
        _ ≤ C * A ^ (-(2 / 3 : ℝ) + ε) :=
          mul_le_mul (le_max_right _ _) hsmall
            (Real.rpow_nonneg hTpos.le _) hC.le
    exact (sub_nonpos.mpr hone).trans measureReal_nonneg

end DirectedDistances.PaperProofs.Section7
