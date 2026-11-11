module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperFirstBulletProb
public import DirectedDistances.Recursive.BusemannSdpUnconditional
import DirectedDistances.Recursive.BusemannIncrementPowerTail
import DirectedDistances.Probability.HeavyTailNoCenter

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter Asymptotics Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.Probability
open scoped Topology

local notation "Y" => busemannSDPMeasurableVersion
local notation "ξ" => (fun (k : ℤ) (ω : ℕ → Fin 3) =>
  (SDPMasterFromLaw.increment Y k ω : ℝ))

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
theorem busemannSDP_codeShift_law_sdpCode (n : ℕ) :
    iidCodeMeasure.map (fun ω => Y (codeShift n ω)) = iidCodeMeasure.map Y := by
  change iidCodeMeasure.map (Y ∘ codeShift n) = _
  rw [← Measure.map_map (measurable_pi_iff.mpr measurable_busemannSDPMeasurableVersion)
    (measurable_codeShift n), map_codeShift]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem power_bound_of_remainder
    (P : ℝ → ℝ) (hP : ∀ t, P t ≤ 1) {a α : ℝ} (hα : 0 ≤ α)
    (hasym : (fun t => P t - a * t ^ (-α)) =o[atTop]
      (fun t : ℝ => t ^ (-α))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → P t ≤ C * t ^ (-α) := by
  obtain ⟨r, hr⟩ := (hasym.def zero_lt_one).exists_forall_of_atTop
  let R : ℝ := max 1 r
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := |a| + 1 + 1 / R ^ (-α)
  have hRpow : 0 < R ^ (-α) := Real.rpow_pos_of_pos hR _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have htpow : 0 ≤ t ^ (-α) := (Real.rpow_pos_of_pos ht _).le
  by_cases hRt : R ≤ t
  · have hh := hr t (le_trans (le_max_right 1 r) hRt)
    simp only [Real.norm_eq_abs, abs_of_nonneg htpow, one_mul] at hh
    have hup : P t - a * t ^ (-α) ≤ t ^ (-α) := (le_abs_self _).trans hh
    have ha : a ≤ |a| := le_abs_self a
    have hcoef : a + 1 ≤ C := by
      dsimp [C]
      have : 0 ≤ 1 / R ^ (-α) := by positivity
      linarith
    calc
      P t ≤ (a + 1) * t ^ (-α) := by linarith
      _ ≤ C * t ^ (-α) := mul_le_mul_of_nonneg_right hcoef htpow
  · have hpow : R ^ (-α) ≤ t ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos ht (le_of_not_ge hRt) (neg_nonpos.mpr hα)
    have hsmall : 1 ≤ C * t ^ (-α) := by
      calc
        1 = (1 / R ^ (-α)) * R ^ (-α) := by field_simp
        _ ≤ (1 / R ^ (-α)) * t ^ (-α) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C * t ^ (-α) := by
          apply mul_le_mul_of_nonneg_right _ htpow
          dsimp [C]
          have := abs_nonneg a
          linarith
    exact (hP t).trans hsmall

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem positive_increment_power_tail :
    ∃ C > 0, ∀ t : ℝ, 1 ≤ t →
      iidCodeMeasure.real {ω | t < |ξ 1 ω|} ≤ C * t ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨c, _, htail, _⟩ := busemann_tail_sdp_sdpCode
  obtain ⟨C, hC, hbound⟩ := power_bound_of_remainder
    (fun t => iidCodeMeasure.real {ω | t ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)})
    (fun _ => measureReal_le_one) (by norm_num : (0 : ℝ) ≤ 4 / 3) htail
  refine ⟨C + 1, by linarith, ?_⟩
  intro t ht
  have heq : iidCodeMeasure.real {ω | t < |ξ 1 ω|} =
      iidCodeMeasure.real {ω | t < ξ 1 ω} := by
    apply measureReal_congr
    filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion_item_pos] with ω hω
    have hlo : (-1 : ℝ) ≤ ξ 1 ω := by
      change (-1 : ℝ) ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)
      have hb : (-1 : ℤ) ≤ Y ω 1 - Y ω 0 := hω 1 le_rfl
      exact_mod_cast hb
    apply propext
    constructor
    · intro h
      rcases lt_abs.mp h with h | h
      · exact h
      · linarith
    · intro h
      exact h.trans_le (le_abs_self _)
  rw [heq]
  calc
    iidCodeMeasure.real {ω | t < ξ 1 ω} ≤
        iidCodeMeasure.real {ω | t ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} :=
      measureReal_mono (fun ω hω => by
        change t < ((Y ω 1 - Y ω 0 : ℤ) : ℝ) at hω
        exact le_of_lt hω)
    _ ≤ C * t ^ (-(4 / 3 : ℝ)) := hbound t (by linarith)
    _ ≤ (C + 1) * t ^ (-(4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem twoSidedWalk_sdp_eq (ω : ℕ → Fin 3) (l : ℤ) :
    twoSidedWalk ξ l ω = (Y ω l : ℝ) := by
  have hzero : twoSidedWalk ξ 0 ω = (Y ω 0 : ℝ) := by
    rw [twoSidedWalk_zero, busemannSDPMeasurableVersion_zero, Int.cast_zero]
  have hstep (k : ℤ) : twoSidedWalk ξ k ω - twoSidedWalk ξ (k - 1) ω =
      (Y ω k : ℝ) - (Y ω (k - 1) : ℝ) := by
    rw [twoSidedWalk_sub]
    exact Int.cast_sub _ _
  have hp : ∀ n : ℕ, twoSidedWalk ξ (n : ℤ) ω = (Y ω (n : ℤ) : ℝ) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have hs := hstep ((n : ℤ) + 1)
      simp only [add_sub_cancel_right] at hs
      simp only [Nat.cast_succ]
      linarith only [hs, ih]
  have hn : ∀ n : ℕ, twoSidedWalk ξ (-(n : ℤ)) ω = (Y ω (-(n : ℤ)) : ℝ) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, neg_zero] using hzero
    | succ n ih =>
      have hs := hstep (-(n : ℤ))
      have he : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
      rw [he]
      linarith only [hs, ih]
  by_cases hl : 0 ≤ l
  · simpa only [Int.toNat_of_nonneg hl] using hp l.toNat
  · have hl' : 0 ≤ -l := by omega
    simpa only [Int.toNat_of_nonneg hl', neg_neg] using hn (-l).toNat

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
theorem sdp_fluctuation_power_tail_sdpCode :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ B : ℝ, 1 ≤ B →
      1 - C * B ^ (-(4 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
          |(Y ω i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  have hm (k : ℤ) : Measurable (SDPMasterFromLaw.increment Y k) :=
    (measurable_busemannSDPMeasurableVersion k).sub
      (measurable_busemannSDPMeasurableVersion (k - 1))
  have hc : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hξ (k : ℤ) : Measurable (ξ k) := hc.comp (hm k)
  have hi : iIndepFun ξ iidCodeMeasure :=
    sdpIncrements_iIndep_sdpCode.comp (fun _ z => (z : ℝ)) (fun _ => hc)
  have hpos (k : ℤ) (hk : 1 ≤ k) :
      IdentDistrib (ξ k) (ξ 1) iidCodeMeasure iidCodeMeasure :=
    (show IdentDistrib (SDPMasterFromLaw.increment Y k)
      (SDPMasterFromLaw.increment Y 1) iidCodeMeasure iidCodeMeasure from
        ⟨(hm k).aemeasurable, (hm 1).aemeasurable,
          busemannSDPMeasurableVersion_right_stationary k hk⟩).comp hc
  have hneg (k : ℤ) (hk : k ≤ 0) :
      IdentDistrib (ξ k) (ξ 0) iidCodeMeasure iidCodeMeasure :=
    (show IdentDistrib (SDPMasterFromLaw.increment Y k)
      (SDPMasterFromLaw.increment Y 0) iidCodeMeasure iidCodeMeasure from
        ⟨(hm k).aemeasurable, (hm 0).aemeasurable,
          busemannSDPMeasurableVersion_left_stationary k hk⟩).comp hc
  obtain ⟨Cp, hCp, hp⟩ := positive_increment_power_tail
  obtain ⟨Cn, hCn, hn⟩ := sdp_increment_powerTail_of_ind_sym
    sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode
  have hmean (k : ℤ) : Integrable (ξ k) iidCodeMeasure ∧
      (∫ ω, ξ k ω ∂iidCodeMeasure) = 0 :=
    busemann_sdp_increment_mean_zero_sdpCode k
  obtain ⟨C, hC, hbound⟩ := twoSidedWalk_max_le hξ hi hpos hneg
    (4 / 3) Cp Cn (by norm_num) (by norm_num) hCp hCn hp hn
    (Or.inr ⟨by norm_num, (hmean 1).1, (hmean 1).2⟩)
    (Or.inr ⟨by norm_num, (hmean 0).1, (hmean 0).2⟩)
  refine ⟨C, hC, ?_⟩
  intro k hk B hB
  simpa only [twoSidedWalk_sdp_eq, show (1 / (4 / 3) : ℝ) = 3 / 4 by norm_num]
    using hbound k hk B hB

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
theorem sdp_fluctuation_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ B : ℝ, C ≤ B →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
            |(Y ω i : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  obtain ⟨D, _, hbound⟩ := sdp_fluctuation_power_tail_sdpCode
  intro δ hδ
  have ht : Tendsto (fun B : ℝ => D * B ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).const_mul D
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hδ))
  refine ⟨max 2 R, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro k hk B hB
  have hB1 : 1 ≤ B := le_trans (by norm_num : (1 : ℝ) ≤ 2)
    ((le_max_left 2 R).trans hB)
  have hsmall := hR B ((le_max_right 2 R).trans hB)
  have hle : 1 - δ ≤ 1 - D * B ^ (-(4 / 3 : ℝ)) := by
    linarith only [hsmall]
  exact hle.trans (hbound k hk B hB1)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
@[expose] def cellSdpUpper_selectedTargetConfinement : Prop :=
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ hseparator : ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
        ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ ℓ k : ℤ,
          ∃ y : ℕ → PresentVertex (fun i => w (n + i)),
            Function.Injective y ∧
            (∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k)
                (y j) ∧
              Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
                (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
            (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
              (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)),
        ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
          ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ ℓ : ℤ,
            -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
            ∀ k : ℤ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
              (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k)
                ((Classical.choose (hseparator n h0 hn ℓ k)) j)).toNat ≤
              (sdp
                (⟨kmswWindowVertexMapInf w n
                  (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
                (⟨kmswWindowVertexMapInf w n
                  ((Classical.choose (hseparator n h0 hn ℓ k)) j).id⟩ :
                    PresentVertex w)).toNat

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
theorem cell_sdp_bdy_good_event_sdpCode :
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
                A * (n : ℝ) ^ (3 / 8 : ℝ) / 2)} :=
  cell_sdp_bdy_good_event sdp_fluctuation_sdpCode busemannSDP_codeShift_law_sdpCode

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
named selected-target confinement obligation; fluctuation and shift laws are proved. -/
theorem cellSdpUpper_first_bullet_prob_sdpRest
    (hconf : cellSdpUpper_selectedTargetConfinement) :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
            -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
            ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
              ∃ k : ℤ,
                -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
                k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
                sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
                  ⟨kmswWindowVertexMapInf w n
                    (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
                    (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)} :=
  cellSdpUpper_first_bullet_prob sdp_fluctuation_sdpCode
    busemannSDP_codeShift_law_sdpCode hconf

end DirectedDistances.PaperProofs.Section7
