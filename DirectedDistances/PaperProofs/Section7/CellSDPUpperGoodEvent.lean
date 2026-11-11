module

public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryTail
import DirectedDistances.KMSW.KMSWMeasurability

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Filter
open Topology
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

private theorem process_event_measurable (k : ℕ) (t : ℝ) :
    MeasurableSet {f : ℤ → ℤ | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(f l : ℝ)| ≤ t} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      (measurable_pi_apply l)) measurable_const

private theorem three_events (B E F : Set (ℕ → Fin 3))
    (hB : MeasurableSet B) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (b e f : ℝ) (hb : 1 - b ≤ iidCodeMeasure.real B)
    (he : 1 - e ≤ iidCodeMeasure.real E) (hf : 1 - f ≤ iidCodeMeasure.real F) :
    1 - (b + e + f) ≤ iidCodeMeasure.real (B ∩ E ∩ F) := by
  have hu := measureReal_union_le (μ := iidCodeMeasure) (Bᶜ ∪ Eᶜ) Fᶜ
  have hv := measureReal_union_le (μ := iidCodeMeasure) Bᶜ Eᶜ
  have hc := measureReal_compl (μ := iidCodeMeasure) ((hB.inter hE).inter hF)
  rw [probReal_univ] at hc
  have hsets : (B ∩ E ∩ F)ᶜ = Bᶜ ∪ Eᶜ ∪ Fᶜ := by
    simp only [Set.compl_inter]
  rw [hsets] at hc
  rw [measureReal_compl hB, measureReal_compl hE, probReal_univ] at hv
  rw [measureReal_compl hF, probReal_univ] at hu
  linarith only [hu, hv, hc, hb, he, hf]

private theorem fluctuation_scale (A : ℝ) (n : ℕ) (hA : 1 < A)
    (hn : 1 ≤ n) :
    (A ^ (1 / 4 : ℝ) / 16) *
        ((⌈A * Real.sqrt (n : ℝ)⌉₊ : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      A * (n : ℝ) ^ (3 / 8 : ℝ) / 8 := by
  have hA0 : 0 < A := by linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let T : ℝ := A * Real.sqrt (n : ℝ)
  have hT : 1 ≤ T := by
    dsimp [T]
    exact one_le_mul_of_one_le_of_one_le hA.le
      ((Real.le_sqrt (by norm_num) hn0).2 (by nlinarith [hn1]))
  have hk : ((⌈T⌉₊ : ℕ) : ℝ) ≤ 2 * T := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ T)
    linarith only [hh, hT]
  have hp := Real.rpow_le_rpow (by positivity :
    0 ≤ ((⌈T⌉₊ : ℕ) : ℝ)) hk (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have htwo : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  have hpow : (2 * T) ^ (3 / 4 : ℝ) =
      (2 : ℝ) ^ (3 / 4 : ℝ) * A ^ (3 / 4 : ℝ) *
        (n : ℝ) ^ (3 / 8 : ℝ) := by
    dsimp [T]
    rw [Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn0]
    rw [show (1 / (2 : ℝ)) * (3 / 4) = 3 / 8 by norm_num]
    ring
  have hAexp : A ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ) = A := by
    rw [← Real.rpow_add hA0]
    convert Real.rpow_one A using 1
    congr 1
    ring
  change (A ^ (1 / 4 : ℝ) / 16) *
      ((⌈T⌉₊ : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ _
  calc
    _ ≤ (A ^ (1 / 4 : ℝ) / 16) * (2 * T) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (A ^ (1 / 4 : ℝ) / 16) *
        ((2 : ℝ) ^ (3 / 4 : ℝ) * A ^ (3 / 4 : ℝ) *
          (n : ℝ) ^ (3 / 8 : ℝ)) := by rw [hpow]
    _ ≤ (A ^ (1 / 4 : ℝ) / 16) *
        (2 * A ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ)) := by
      gcongr
    _ = A * (n : ℝ) ^ (3 / 8 : ℝ) / 8 := by
      calc
        _ = (A ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)) *
            (n : ℝ) ^ (3 / 8 : ℝ) / 8 := by ring
        _ = _ := by rw [hAexp]

private theorem boundary_error_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ A : ℝ in atTop, 4 * Real.exp (-(A ^ 2) / 32) ≤ δ / 2 := by
  have hpow : Tendsto (fun A : ℝ => A ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have harg : Tendsto (fun A : ℝ => -(A ^ 2) / 32) atTop atBot := by
    have hn := tendsto_neg_atTop_atBot.comp hpow
    simpa [div_eq_mul_inv] using hn.atBot_div_const (by norm_num : (0 : ℝ) < 32)
  have hexp : Tendsto (fun A : ℝ => Real.exp (-(A ^ 2) / 32)) atTop
      (𝓝 0) := Real.tendsto_exp_atBot.comp harg
  have hevent := hexp.eventually
    (Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 8))
  filter_upwards [hevent] with A hA
  have hmul := mul_lt_mul_of_pos_left hA (by norm_num : (0 : ℝ) < 4)
  nlinarith







theorem cell_sdp_bdy_good_event
    (hfluc : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ B : ℝ, C ≤ B →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
            |(busemannSDPMeasurableVersion ω i : ℝ)| ≤
              B * (k : ℝ) ^ (3 / 4 : ℝ)})
    (hstat : ∀ n : ℕ,
      iidCodeMeasure.map (fun ω =>
        busemannSDPMeasurableVersion (codeShift n ω)) =
          iidCodeMeasure.map busemannSDPMeasurableVersion) :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          let K := A * Real.sqrt (n : ℝ)
          let σ₀ := ((kmswStage w n).LR.length : ℤ)
          let σₙ := ((kmswStage w n).UR.length : ℤ) + 1
          ((kmswStage w n).LR.length : ℝ) ≤ K ∧
            ((kmswStage w n).UR.length : ℝ) + 1 ≤ K ∧
            ((kmswStage w n).LL.length : ℝ) ≤ K ∧
            (((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ K ∧
          (∀ ℓ : ℤ, |(ℓ : ℝ)| ≤ K →
            |(busemannSDPMeasurableVersion ω ℓ : ℝ) -
              (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 8 : ℝ) / 2) ∧
          (∀ k : ℤ, |(k : ℝ)| ≤ K →
            |(busemannSDPMeasurableVersion (codeShift n ω) k : ℝ) -
              (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 8 : ℝ) / 2)} := by
  classical
  intro δ hδ
  obtain ⟨C, hC, hflucBound⟩ := hfluc (δ / 4) (by linarith)
  have htail := boundary_error_eventually δ hδ
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp
    (htail.and (eventually_ge_atTop (max 2 ((16 * C) ^ 4))))
  let A₁ := max A₀ (max 2 ((16 * C) ^ 4))
  have hA₁ : 1 < A₁ := by
    dsimp [A₁]
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      ((le_max_left 2 ((16 * C) ^ 4)).trans
        (le_max_right A₀ (max 2 ((16 * C) ^ 4))))
  refine ⟨A₁, hA₁, ?_⟩
  intro A hA n hn
  have hA₁le : max A₀ (max 2 ((16 * C) ^ 4)) ≤ A := by
    simpa [A₁] using hA
  have htwo : 2 ≤ A := by
    exact (le_max_left 2 ((16 * C) ^ 4)).trans
      ((le_max_right A₀ (max 2 ((16 * C) ^ 4))).trans hA₁le)
  have hAgt : 1 < A := by linarith
  have hA0 : 0 < A := by linarith
  have hn0 : 0 < n := by omega
  let K : ℝ := A * Real.sqrt (n : ℝ)
  let k : ℕ := ⌈K⌉₊
  let B : ℝ := A ^ (1 / 4 : ℝ) / 16
  have hK : 1 ≤ K := by
    dsimp [K]
    exact one_le_mul_of_one_le_of_one_le hAgt.le
      ((Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).2
        (by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]))
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (le_trans hK (Nat.le_ceil K))
  have hB : C ≤ B := by
    have hAhigh : (16 * C) ^ 4 ≤ A := by
      exact (le_max_right 2 ((16 * C) ^ 4)).trans
        ((le_max_right A₀ (max 2 ((16 * C) ^ 4))).trans hA₁le)
    have hpow := Real.rpow_le_rpow (by positivity) hAhigh
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hroot : ((16 * C) ^ 4) ^ (1 / 4 : ℝ) = 16 * C := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (by positivity : 0 ≤ 16 * C)]
      convert Real.rpow_one (16 * C) using 1
      congr 1
      norm_num
    dsimp [B]
    rw [hroot] at hpow
    nlinarith
  have hscale := fluctuation_scale A n hAgt hn
  have hscale' : B * (k : ℝ) ^ (3 / 4 : ℝ) ≤
      A * (n : ℝ) ^ (3 / 8 : ℝ) / 8 := by
    simpa [B, k, K] using hscale
  let E : Set (ℕ → Fin 3) := {ω | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
    |(busemannSDPMeasurableVersion ω i : ℝ)| ≤
      B * (k : ℝ) ^ (3 / 4 : ℝ)}
  let F : Set (ℕ → Fin 3) := {ω | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
    |(busemannSDPMeasurableVersion (codeShift n ω) i : ℝ)| ≤
      B * (k : ℝ) ^ (3 / 4 : ℝ)}
  let O : Set (ℕ → Fin 3) := {ω |
    ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ K ∧
    ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) + 1 ≤ K ∧
    ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ K ∧
    (((kmswStage (fun i => ω (i + 1)) n).UL.length - 1 : ℕ) : ℝ) ≤ K}
  have hS : MeasurableSet {f : ℤ → ℤ | ∀ i : ℤ, -(k : ℤ) ≤ i →
      i ≤ k → |(f i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)} :=
    process_event_measurable k (B * (k : ℝ) ^ (3 / 4 : ℝ))
  have hm : Measurable busemannSDPMeasurableVersion :=
    measurable_pi_iff.mpr measurable_busemannSDPMeasurableVersion
  have hE : MeasurableSet E := hS.preimage hm
  have hF : MeasurableSet F := hS.preimage
    (hm.comp (measurable_codeShift n))
  have hO : MeasurableSet O := by
    exact measurableSet_kmswStage_shift n (fun s =>
      (s.LR.length : ℝ) ≤ K ∧ (s.UR.length : ℝ) + 1 ≤ K ∧
      (s.LL.length : ℝ) ≤ K ∧ (((s.UL.length - 1 : ℕ) : ℝ) ≤ K))
  have hflucE := hflucBound k hk B hB
  have hflucF : 1 - δ / 4 ≤ iidCodeMeasure.real F := by
    have hmeasure : iidCodeMeasure F = iidCodeMeasure E := by
      change iidCodeMeasure
          ((busemannSDPMeasurableVersion ∘ codeShift n) ⁻¹'
            {f : ℤ → ℤ | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
              |(f i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)}) =
        iidCodeMeasure (busemannSDPMeasurableVersion ⁻¹'
          {f : ℤ → ℤ | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
            |(f i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)})
      rw [← Measure.map_apply
        (hm.comp (measurable_codeShift n)) hS,
        ← Measure.map_apply hm hS]
      exact congrArg (fun μ : Measure (ℤ → ℤ) => μ
        {f : ℤ → ℤ | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
          |(f i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)}) (hstat n)
    have hreal : iidCodeMeasure.real F = iidCodeMeasure.real E :=
      congrArg ENNReal.toReal hmeasure
    rw [hreal]
    exact hflucE
  have hoff := kmswBoundary_offsets_source_scale_tail A 1 n hAgt
    (by norm_num) (by omega)
  have hoff' : 1 - 4 * Real.exp (-((A ^ (1 : ℝ)) ^ 2 / 32)) ≤
      iidCodeMeasure.real O := by
    simpa [O, K] using hoff
  have hprobO : 1 - δ / 2 ≤ iidCodeMeasure.real O := by
    have hsmallPair := hA₀ A
      ((le_max_left A₀ (max 2 ((16 * C) ^ 4))).trans hA₁le)
    have hsmall' : 4 * Real.exp (-((A ^ (1 : ℝ)) ^ 2 / 32)) ≤ δ / 2 := by
      have harg : -((A ^ (1 : ℝ)) ^ 2 / 32) = -A ^ 2 / 32 := by
        rw [Real.rpow_one]
        ring
      simpa only [harg] using hsmallPair.1
    linarith only [hoff', hsmall']
  have hgood := three_events O E F hO hE hF (δ / 2) (δ / 4) (δ / 4)
    hprobO hflucE hflucF
  have hdelta : δ / 2 + δ / 4 + δ / 4 = δ := by ring
  rw [hdelta] at hgood
  have hsubset : O ∩ E ∩ F ⊆ {ω : ℕ → Fin 3 |
      let w := fun i => ω (i + 1)
      let σ₀ := ((kmswStage w n).LR.length : ℤ)
      let σₙ := ((kmswStage w n).UR.length : ℤ) + 1
      ((kmswStage w n).LR.length : ℝ) ≤ K ∧
        ((kmswStage w n).UR.length : ℝ) + 1 ≤ K ∧
        ((kmswStage w n).LL.length : ℝ) ≤ K ∧
        (((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ K ∧
      (∀ ℓ : ℤ, |(ℓ : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion ω ℓ : ℝ) -
          (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 8 : ℝ) / 2) ∧
      (∀ j : ℤ, |(j : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion (codeShift n ω) j : ℝ) -
          (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 8 : ℝ) / 2)} := by
    rintro ω ⟨⟨hOω, hEω⟩, hFω⟩
    dsimp [O] at hOω
    dsimp [E, F] at hEω hFω
    dsimp
    refine ⟨hOω.1, hOω.2.1, hOω.2.2.1, hOω.2.2.2, ?_, ?_⟩
    · intro ℓ hℓ
      let w := fun i => ω (i + 1)
      let σ₀ : ℤ := ((kmswStage w n).LR.length : ℤ)
      have hσ : |(σ₀ : ℝ)| ≤ K := by
        dsimp [σ₀]
        exact_mod_cast hOω.1
      have hℓk : -(k : ℤ) ≤ ℓ ∧ ℓ ≤ k := by
        have hKk : K ≤ (k : ℝ) := by
          dsimp [k]
          exact_mod_cast Nat.le_ceil K
        have hh := abs_le.mp hℓ
        have hlow : -(k : ℝ) ≤ (ℓ : ℝ) := by linarith
        have hup : (ℓ : ℝ) ≤ (k : ℝ) := by linarith
        exact ⟨by exact_mod_cast hlow, by exact_mod_cast hup⟩
      have hσk : -(k : ℤ) ≤ σ₀ ∧ σ₀ ≤ k := by
        have hh : -(k : ℝ) ≤ (σ₀ : ℝ) ∧ (σ₀ : ℝ) ≤ k := by
          have ha := abs_le.mp hσ
          have hKk : K ≤ (k : ℝ) := by
            dsimp [k]
            exact_mod_cast Nat.le_ceil K
          constructor <;> linarith
        exact_mod_cast hh
      calc
        |(busemannSDPMeasurableVersion ω ℓ : ℝ) -
            (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤
              |(busemannSDPMeasurableVersion ω ℓ : ℝ)| +
                |(busemannSDPMeasurableVersion ω σ₀ : ℝ)| := by
          simpa [abs_neg] using (abs_sub_le
            (busemannSDPMeasurableVersion ω ℓ : ℝ) 0
            (busemannSDPMeasurableVersion ω σ₀ : ℝ))
        _ ≤ B * (k : ℝ) ^ (3 / 4 : ℝ) + B * (k : ℝ) ^ (3 / 4 : ℝ) :=
          add_le_add (hEω ℓ hℓk.1 hℓk.2) (hEω σ₀ hσk.1 hσk.2)
        _ ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by
          calc
            _ = 2 * (B * (k : ℝ) ^ (3 / 4 : ℝ)) := by ring
            _ ≤ 2 * (A * (n : ℝ) ^ (3 / 8 : ℝ) / 8) := by
              exact mul_le_mul_of_nonneg_left hscale' (by norm_num)
            _ ≤ _ := by
              have hnpos : 0 ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) :=
                mul_nonneg hA0.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              nlinarith
    · intro j hj
      let w := fun i => ω (i + 1)
      let σₙ : ℤ := ((kmswStage w n).UR.length : ℤ) + 1
      have hσ : |(σₙ : ℝ)| ≤ K := by
        have hh : 0 ≤ ((kmswStage w n).UR.length : ℝ) + 1 := by positivity
        have hcast : (σₙ : ℝ) =
            ((kmswStage w n).UR.length : ℝ) + 1 := by simp [σₙ]
        rw [hcast, abs_of_nonneg hh]
        exact hOω.2.1
      have hjk : -(k : ℤ) ≤ j ∧ j ≤ k := by
        have hKk : K ≤ (k : ℝ) := by
          dsimp [k]
          exact_mod_cast Nat.le_ceil K
        have hh := abs_le.mp hj
        have hlow : -(k : ℝ) ≤ (j : ℝ) := by linarith
        have hup : (j : ℝ) ≤ (k : ℝ) := by linarith
        exact ⟨by exact_mod_cast hlow, by exact_mod_cast hup⟩
      have hσk : -(k : ℤ) ≤ σₙ ∧ σₙ ≤ k := by
        have hh : -(k : ℝ) ≤ (σₙ : ℝ) ∧ (σₙ : ℝ) ≤ k := by
          have ha := abs_le.mp hσ
          have hKk : K ≤ (k : ℝ) := by
            dsimp [k]
            exact_mod_cast Nat.le_ceil K
          constructor <;> linarith
        exact_mod_cast hh
      calc
        |(busemannSDPMeasurableVersion (codeShift n ω) j : ℝ) -
            (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤
              |(busemannSDPMeasurableVersion (codeShift n ω) j : ℝ)| +
                |(busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| :=
          by
            simpa [abs_neg] using (abs_sub_le
              (busemannSDPMeasurableVersion (codeShift n ω) j : ℝ) 0
              (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ))
        _ ≤ B * (k : ℝ) ^ (3 / 4 : ℝ) + B * (k : ℝ) ^ (3 / 4 : ℝ) :=
          add_le_add (hFω j hjk.1 hjk.2) (hFω σₙ hσk.1 hσk.2)
        _ ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by
          calc
            _ = 2 * (B * (k : ℝ) ^ (3 / 4 : ℝ)) := by ring
            _ ≤ 2 * (A * (n : ℝ) ^ (3 / 8 : ℝ) / 8) := by
              exact mul_le_mul_of_nonneg_left hscale' (by norm_num)
            _ ≤ _ := by
              have hnpos : 0 ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) :=
                mul_nonneg hA0.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              nlinarith
  have hmono := measureReal_mono (μ := iidCodeMeasure) hsubset
  have hfinal := hgood.trans hmono
  exact hfinal

end DirectedDistances.PaperProofs.Section7
