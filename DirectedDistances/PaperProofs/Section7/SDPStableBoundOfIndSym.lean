module

public import DirectedDistances.Recursive.BusemannWindowLimitSDP
import DirectedDistances.Probability.SkorokhodJ1WindowDEvalInterior
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum









public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.Probability
open scoped Topology ENNReal

private theorem measurable_sdpWindow (k : ℕ) {hT : 0 < (1 : ℝ)} :
    Measurable (sdpBusemannWindow k hT) := by
  apply measurable_scaledPartialSumWindow
  intro j
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _))

private theorem isOpen_sdpWindow_negative {hT : 0 < (1 : ℝ)} (a : ℝ) :
    IsOpen {x : J1WindowD 1 hT |
      ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        x.path.1 t < -a} := by
  rw [Metric.isOpen_iff]
  rintro x ⟨t, ht0, ht1, hx⟩
  let d := min (t : ℝ) (min (1 - (t : ℝ)) (-a - x.path.1 t))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min ht0 (lt_min (sub_pos.mpr ht1) (sub_pos.mpr hx))
  refine ⟨d, hd, ?_⟩
  intro y hy
  change j1WindowDist hT y.path x.path < d at hy
  change (⨅ φ : J1TimeChange 1,
      max (⨆ s : J1Window 1, |((φ s : ℝ) - (s : ℝ))|)
        (⨆ s : J1Window 1, |y.path.1 (φ s) - x.path.1 s|)) < d at hy
  obtain ⟨φ, hcost⟩ := exists_lt_of_ciInf_lt hy
  have htime : |((φ t : ℝ) - (t : ℝ))| < d :=
    ((le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) t le_rfl).trans
      (le_max_left _ _)).trans_lt hcost
  have hvalue : |y.path.1 (φ t) - x.path.1 t| < d :=
    ((le_ciSup_of_le (j1WindowValueError_bddAbove y.path x.path φ) t le_rfl).trans
      (le_max_right _ _)).trans_lt hcost
  have hdleft : d ≤ (t : ℝ) := min_le_left _ _
  have hdright : d ≤ 1 - (t : ℝ) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdlow : -d < (φ t : ℝ) - (t : ℝ) := (abs_lt.mp htime).1
  have hdup : (φ t : ℝ) - (t : ℝ) < d := (abs_lt.mp htime).2
  have hφlow : 0 < (φ t : ℝ) := by linarith
  have hφup : (φ t : ℝ) < 1 := by linarith
  have hdval : d ≤ -a - x.path.1 t :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hval : y.path.1 (φ t) - x.path.1 t < d := (abs_lt.mp hvalue).2
  refine ⟨φ t, hφlow, hφup, ?_⟩
  linarith

private theorem sdp_window_negative_preimage_subset
    {hT : 0 < (1 : ℝ)} (k : ℕ) (A : ℝ) (hA : 1 < A) :
    (sdpBusemannWindow k hT) ⁻¹'
        {x : J1WindowD 1 hT |
          ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
            x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))} ⊆
      {ω | ∃ r : ℕ, r ≤ k ∧
        (busemannSDPMeasurableVersion ω r : ℝ) ≤
          -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  rintro ω ⟨t, ht0, ht1, hnegative⟩
  let q : ℝ := ((k + 1 : ℕ) : ℝ) * (t : ℝ)
  let r : ℕ := ⌊q⌋₊
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hrfloor : (r : ℤ) = ⌊q⌋ := by
    exact Int.natCast_floor_eq_floor hq0
  have hrle : (r : ℝ) ≤ q := by
    dsimp [r]
    exact Nat.floor_le hq0
  let m : ℝ := ((k + 1 : ℕ) : ℝ)
  have hqbound : q < m := by
    have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hh := mul_lt_mul_of_pos_left ht1 hkpos
    simpa [q, m] using hh
  have hrlt : (r : ℝ) < m := hrle.trans_lt hqbound
  have hrltNat : r < k + 1 := by
    change (r : ℝ) < ((k + 1 : ℕ) : ℝ) at hrlt
    exact_mod_cast hrlt
  have hrk : r ≤ k := by omega
  have hformula : (sdpBusemannWindow k hT ω).path.1 t =
      m ^ (-(3 / 4 : ℝ)) *
        (busemannSDPMeasurableVersion ω (r : ℤ) : ℝ) := by
    rw [sdpBusemannWindow_apply]
    rw [show ((k + 1 : ℕ) : ℝ) * (t : ℝ) = q by rfl, ← hrfloor]
    dsimp only [m]
    norm_num
  have ha : 0 < A ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hm : 0 < m := by dsimp [m]; positivity
  have hmp : 0 < m ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hm _
  have hscale : m ^ (-(3 / 4 : ℝ)) = 1 / (m ^ (3 / 4 : ℝ)) := by
    rw [Real.rpow_neg hm.le]
    norm_num
  have hquot :
      (busemannSDPMeasurableVersion ω (r : ℤ) : ℝ) /
        (m ^ (3 / 4 : ℝ)) <
          -(A ^ (-(1 / 2 : ℝ))) := by
    rw [hformula] at hnegative
    rw [hscale] at hnegative
    simpa [div_eq_mul_inv, mul_comm] using hnegative
  have hy : (busemannSDPMeasurableVersion ω (r : ℤ) : ℝ) <
      -(A ^ (-(1 / 2 : ℝ))) * (m ^ (3 / 4 : ℝ)) :=
    (div_lt_iff₀ hmp).mp hquot
  have hkp : (k : ℝ) ^ (3 / 4 : ℝ) ≤
      m ^ (3 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg k)
    · dsimp [m]
      exact_mod_cast Nat.le_succ k
    · norm_num
  have htarget : (busemannSDPMeasurableVersion ω (r : ℤ) : ℝ) ≤
      -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ) := by
    exact le_of_lt (hy.trans_le (mul_le_mul_of_nonpos_left hkp
      (neg_nonpos.mpr ha.le)))
  exact ⟨r, hrk, htarget⟩








theorem sdp_hstable_of_window_negative_limit
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment
        busemannSDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (hnegative : ∀ ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)),
      Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num)) atTop (𝓝 ν) →
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 < A ∧
        1 - ε ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real
          {x : J1WindowD 1 (by norm_num) |
            ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
              x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))}) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  intro δ hδ
  by_cases hδlarge : 2 ≤ δ
  · refine ⟨2, by norm_num, 0, ?_⟩
    intro k _
    have hnonneg : 0 ≤ iidCodeMeasure.real
        {ω | ∃ r : ℕ, r ≤ k ∧
        (busemannSDPMeasurableVersion ω r : ℝ) ≤
          -(2 ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)} :=
      measureReal_nonneg
    linarith
  · have hδlt : δ < 2 := by linarith
    have hT : 0 < (1 : ℝ) := by norm_num
    obtain ⟨ν, hν, _⟩ :=
      sdp_busemann_window_tendsto hind_sdp hsym_sdp hT
    obtain ⟨A, hA, hνnegative⟩ := hnegative ν hν (δ / 4) (by linarith)
    let U : Set (J1WindowD 1 hT) :=
      {x | ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))}
    have hUopen : IsOpen U := by
      simpa only [U] using isOpen_sdpWindow_negative (hT := hT)
        (A ^ (-(1 / 2 : ℝ)))
    have hU : MeasurableSet U := hUopen.measurableSet
    have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hUopen
    let c : ℝ := 1 - δ / 2
    let m : ℝ≥0∞ := (ν : Measure (J1WindowD 1 hT)) U
    have hc : 0 < c := by dsimp [c]; linarith
    have hmfin : m ≠ ∞ := measure_ne_top (ν : Measure _) U
    have hsmall : ENNReal.ofReal c < m := by
      apply (ENNReal.ofReal_lt_iff_lt_toReal hc.le hmfin).mpr
      change c < (ν : Measure (J1WindowD 1 hT)).real U
      dsimp [c]
      change 1 - δ / 4 ≤ (ν : Measure (J1WindowD 1 hT)).real U at hνnegative
      exact lt_of_lt_of_le (by linarith) hνnegative
    have hevent : ∀ᶠ k : ℕ in atTop,
        ENNReal.ofReal c < (sdpBusemannWindowLaw k hT : Measure _) U :=
      eventually_lt_of_lt_liminf (hsmall.trans_le (by simpa [m] using hport))
    obtain ⟨kstar, hkstar⟩ := eventually_atTop.1 hevent
    refine ⟨A, hA, kstar, ?_⟩
    intro k hk
    have hmap : (sdpBusemannWindowLaw k hT : Measure _) U =
        iidCodeMeasure ((sdpBusemannWindow k hT) ⁻¹' U) := by
      rw [sdpBusemannWindowLaw]
      rw [ProbabilityMeasure.map_apply'
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (measurable_sdpWindow k).aemeasurable hU]
      rfl
    have hcprob : c ≤ ((sdpBusemannWindowLaw k hT : Measure _).real U) := by
      have := (ENNReal.ofReal_le_iff_le_toReal
        (measure_ne_top (sdpBusemannWindowLaw k hT : Measure _) U)).mp
        (le_of_lt (hkstar k hk))
      simpa [c, Measure.real_def] using this
    have hsubset := sdp_window_negative_preimage_subset (hT := hT) k A hA
    have hpre : c ≤ iidCodeMeasure.real
        ((sdpBusemannWindow k hT) ⁻¹' U) := by
      change c ≤ (iidCodeMeasure ((sdpBusemannWindow k hT) ⁻¹' U)).toReal
      rw [← hmap]
      exact hcprob
    have hmeasure := measureReal_mono (μ := iidCodeMeasure) hsubset
    have htarget : c ≤ iidCodeMeasure.real
        {ω | ∃ r : ℕ, r ≤ k ∧
          (busemannSDPMeasurableVersion ω r : ℝ) ≤
            -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)} := by
      exact hpre.trans hmeasure
    simpa [c] using htarget

end DirectedDistances.PaperProofs.Section7
