module

public import DirectedDistances.PaperProofs.Section7.CellLDPLowerIncrementTail
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerAlignment
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerCutoff
public import DirectedDistances.RandomWalk.CellLDPLowerBoundaryTime
public import DirectedDistances.KMSW.LeftStationaryGeometry

/-! Supporting lemmas for paper labels `lem-cell-ldp-lower` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW
open DirectedDistances.Recursive DirectedDistances.RandomWalk
open Quiver



theorem cell_ldp_lower_conditional
    (Y : (ℕ → Fin 3) → ℤ → ℤ)
    (hmeasInc : ∀ k, Measurable (fun ω => ldpIncrement Y k ω))
    (hmeas : ∀ j : ℕ,
      Measurable (fun ω => (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)))
    (hind : iIndepFun
      (fun (j : ℕ) ω => (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)) iidCodeMeasure)
    (hstat : ∀ k : ℤ, k ≤ 0 →
      iidCodeMeasure.map (ldpIncrement Y k) = iidCodeMeasure.map (ldpIncrement Y 0))
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|})
    (h71 : ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hw : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ ℓ k : ℕ, 1 ≤ ℓ → ℓ < k →
          ∃ a b : StagePresentVertex (fun i => ω (i + 1))
            (boundaryHitTime (fun i => ω (i + 1)) hw (-(k : ℤ))),
            ∃ q : Path a b,
              (max (Y ω (-(ℓ : ℤ)) - Y ω (-(k : ℤ))) 0).toNat ≤ q.length)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  let c' : ℝ := c * min 1 (x₀ ^ (-(2 / 3 : ℝ)))
  have hc' : 0 < c' := by
    dsimp [c']
    exact mul_pos hc (lt_min one_pos (Real.rpow_pos_of_pos hx₀ _))
  have habsOne : ∀ x ≥ (1 : ℝ),
      2 * c' * x ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|} := by
    intro x hx
    by_cases htailRange : x₀ ≤ x
    · have hscale : 2 * c' * x ^ (-(2 / 3 : ℝ)) ≤
          2 * c * x ^ (-(2 / 3 : ℝ)) := by
        have hcm : c * min 1 (x₀ ^ (-(2 / 3 : ℝ))) ≤ c := by
          calc
            c * min 1 (x₀ ^ (-(2 / 3 : ℝ))) ≤ c * 1 :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hc)
            _ = c := by ring
        have hcm2 : 2 * (c * min 1 (x₀ ^ (-(2 / 3 : ℝ)))) ≤ 2 * c :=
          mul_le_mul_of_nonneg_left hcm (by norm_num)
        have hp : 0 ≤ x ^ (-(2 / 3 : ℝ)) := by positivity
        dsimp [c']
        exact mul_le_mul_of_nonneg_right hcm2 hp
      exact hscale.trans (habs x htailRange)
    · have hxlt : x < x₀ := lt_of_not_ge htailRange
      have hsubset : {ω | x₀ ≤ |(ldpIncrement Y 0 ω : ℝ)|} ⊆
          {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|} := by
        intro ω hω
        exact le_trans hxlt.le hω
      have hmono := MeasureTheory.measureReal_mono hsubset
        (measure_ne_top iidCodeMeasure _)
      have htail := habs x₀ le_rfl
      have hxpow : x ^ (-(2 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
      have hscale : c' * x ^ (-(2 / 3 : ℝ)) ≤
          c * x₀ ^ (-(2 / 3 : ℝ)) := by
        dsimp [c']
        calc
          c * min 1 (x₀ ^ (-(2 / 3 : ℝ))) * x ^ (-(2 / 3 : ℝ))
              ≤ c * x₀ ^ (-(2 / 3 : ℝ)) * 1 := by
            gcongr
            exact min_le_right _ _
          _ = c * x₀ ^ (-(2 / 3 : ℝ)) := by ring
      change 2 * c * x₀ ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x₀ ≤ |(ldpIncrement Y 0 ω : ℝ)|} at htail
      change iidCodeMeasure.real {ω | x₀ ≤ |(ldpIncrement Y 0 ω : ℝ)|} ≤
        iidCodeMeasure.real {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|} at hmono
      calc
        2 * c' * x ^ (-(2 / 3 : ℝ)) ≤
            2 * c * x₀ ^ (-(2 / 3 : ℝ)) := by nlinarith [hscale]
        _ ≤ iidCodeMeasure.real
            {ω | x₀ ≤ |(ldpIncrement Y 0 ω : ℝ)|} := htail
        _ ≤ iidCodeMeasure.real
            {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|} := hmono
  obtain ⟨c₂, c₃, hc₂, hc₃, hprod⟩ :=
    ldp_lower_product_step (μ := iidCodeMeasure) (Y := Y)
      hmeasInc hmeas hind hstat hsym hc' one_pos habsOne ε
  refine ⟨8, c₂, c₃, hc₂, hc₃, ?_⟩
  intro n hn A hA
  let x : ℝ := A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)
  let target : Set (ℕ → Fin 3) := {ω | ∃ a b : StagePresentVertex
    (fun i => ω (i + 1)) n, ∃ q : Path a b, x ≤ (q.length : ℝ)}
  change 1 - (8 * A ^ (-(2 / 3 : ℝ) + ε) +
      c₂ * Real.exp (-(c₃ * A ^ ε))) ≤ iidCodeMeasure.real target
  by_cases hsmall : x ≤ 1
  · have hall : target = Set.univ := by
      ext ω
      constructor
      · intro; trivial
      · intro
        obtain ⟨a, b, q, hq⟩ := stage_has_present_directed_edge
          (fun i => ω (i + 1)) hn
        refine ⟨a, b, q, ?_⟩
        exact le_trans hsmall (by exact_mod_cast hq)
    rw [hall]
    have hpowpos : 0 ≤ A ^ (-(2 / 3 : ℝ) + ε) := by positivity
    have hexppos : 0 ≤ c₂ * Real.exp (-(c₃ * A ^ ε)) := by positivity
    have hterm : 0 ≤ 8 * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε)) := by positivity
    rw [probReal_univ]
    linarith
  · have hxlarge : 1 < x := lt_of_not_ge hsmall
    let K : ℕ := ⌊A ^ (-(2 / 3 : ℝ) + ε) *
      (n : ℝ) ^ (1 / 2 : ℝ)⌋₊
    let incEvent : Set (ℕ → Fin 3) := {ω | ∃ j ∈ Finset.range K,
      x ≤ (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)}
    let hitEvent : Set (ℕ → Fin 3) :=
      {ω | codeFstFirstHit (-(K + 1 : ℕ)) ω ≤ (n : ℕ∞)}
    have hinc : 1 - c₂ * Real.exp (-(c₃ * A ^ ε)) ≤
        iidCodeMeasure.real incEvent := by
      have hexp : (-2 / 3 : ℝ) + ε = -(2 / 3 : ℝ) + ε := by ring
      have hpow : A ^ (-2 / 3 + ε : ℝ) = A ^ (-(2 / 3 : ℝ) + ε) := by
        rw [hexp]
      have hK :
          ⌊A ^ (-2 / 3 + ε : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊ = K := by
        simp [K, hpow]
      have hxthreshold :
          1 ≤ A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) := by
        dsimp [x] at hxlarge
        exact hxlarge.le
      simpa only [incEvent, K, x, hK] using
        hprod n hn A hA hxthreshold
    have hincMeas : MeasurableSet incEvent := by
      have hset : incEvent = ⋃ j ∈ Finset.range K,
          {ω | x ≤ (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)} := by
        ext ω
        simp [incEvent]
      rw [hset]
      exact Finset.measurableSet_biUnion _ fun j _ =>
        (hmeas j) measurableSet_Ici
    have hhitMeas : MeasurableSet hitEvent := by
      have heq : hitEvent = ⋃ m : ℕ, ⋃ (_ : m ≤ n),
          {ω | codeFstFirstHit (-(K + 1 : ℕ)) ω = (m : ℕ∞)} := by
        ext ω
        simp only [hitEvent, Set.mem_iUnion, Set.mem_ofPred_eq,
          ENat.le_natCast_iff]
        exact exists_congr fun m =>
          ⟨fun h => ⟨h.2, h.1⟩, fun ⟨hm, he⟩ => ⟨he, hm⟩⟩
      rw [heq]
      exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
        codePast_le m _
          (measurableSet_codePast_codeFstFirstHit_eq (-(K + 1 : ℕ)) m)
    have hhit := codeFstFirstHit_le_prob_ge (K + 1) n (by omega) hn
    have hIntLower : 1 - (c₂ * Real.exp (-(c₃ * A ^ ε)) +
          4 * ((K : ℝ) + 1) / Real.sqrt n) ≤
        iidCodeMeasure.real (incEvent ∩ hitEvent) := by
      have hcomp := MeasureTheory.measureReal_compl
        (μ := iidCodeMeasure) hincMeas
      have hcompHit := MeasureTheory.measureReal_compl
        (μ := iidCodeMeasure) hhitMeas
      have hhit' : 1 - 4 * ((K : ℝ) + 1) / Real.sqrt n ≤
          iidCodeMeasure.real hitEvent := by
        simpa [hitEvent] using hhit
      have hcomplbound : iidCodeMeasure.real (incEventᶜ ∪ hitEventᶜ) ≤
          c₂ * Real.exp (-(c₃ * A ^ ε)) +
            4 * ((K : ℝ) + 1) / Real.sqrt n := by
        calc
          iidCodeMeasure.real (incEventᶜ ∪ hitEventᶜ) ≤
              iidCodeMeasure.real incEventᶜ + iidCodeMeasure.real hitEventᶜ :=
            MeasureTheory.measureReal_union_le (μ := iidCodeMeasure) _ _
          _ = (1 - iidCodeMeasure.real incEvent) +
              (1 - iidCodeMeasure.real hitEvent) := by
            rw [hcomp, hcompHit, probReal_univ]
          _ ≤ c₂ * Real.exp (-(c₃ * A ^ ε)) +
              4 * ((K : ℝ) + 1) / Real.sqrt n := by linarith [hinc, hhit']
      have hcomplset : (incEvent ∩ hitEvent)ᶜ = incEventᶜ ∪ hitEventᶜ := by
        classical
        ext ω
        simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
        tauto
      have hcompInter := MeasureTheory.measureReal_compl (μ := iidCodeMeasure)
        (hincMeas.inter hhitMeas)
      rw [hcomplset] at hcompInter
      rw [probReal_univ] at hcompInter
      linarith
    have hhitSubset : incEvent ∩ hitEvent ≤ᵐ[iidCodeMeasure] target := by
      filter_upwards [h71] with ω hgood hω
      obtain ⟨hw, hpaths⟩ := hgood
      obtain ⟨j, hjK, hjx⟩ := hω.1
      have hjlt : j < K := Finset.mem_range.mp hjK
      have htimeK := boundaryHitTime_le_of_codeFstFirstHit_le ω hw
        (K + 1) n (by omega) hω.2
      have hlevel : -((K + 1 : ℕ) : ℤ) ≤ -((j + 2 : ℕ) : ℤ) := by omega
      have htimeMono := boundaryHitTime_left_antitone
        (fun i => ω (i + 1)) hw (by omega) hlevel
      have htime : boundaryHitTime (fun i => ω (i + 1)) hw
          (-((j + 2 : ℕ) : ℤ)) ≤ n := htimeMono.trans htimeK
      obtain ⟨a, b, q, hq⟩ := hpaths (j + 1) (j + 2) (by omega) (by omega)
      have hqidx : boundaryHitTime (fun i => ω (i + 1)) hw
          (-((j + 2 : ℕ) : ℤ)) ≤ n := htime
      obtain ⟨q', hq'⟩ := stage_path_mono_length_ge hqidx q hq
      refine ⟨⟨a.id⟩, ⟨b.id⟩, q', ?_⟩
      have harg1 : -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      have harg2 : -((j : ℤ) + 1) - 1 = -((j + 2 : ℕ) : ℤ) := by omega
      have hdiff : x ≤ (Y ω (-((j + 1 : ℕ) : ℤ)) -
          Y ω (-((j + 2 : ℕ) : ℤ)) : ℤ) := by
        change x ≤ (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ) at hjx
        rw [ldpIncrement, harg2, harg1] at hjx
        exact hjx
      have hdiffR : x ≤ (Y ω (-((j + 1 : ℕ) : ℤ)) : ℝ) -
          (Y ω (-((j + 2 : ℕ) : ℤ)) : ℝ) := by
        exact_mod_cast hdiff
      have hdiffNonneg : 0 ≤ Y ω (-((j + 1 : ℕ) : ℤ)) -
          Y ω (-((j + 2 : ℕ) : ℤ)) := by
        exact_mod_cast (show 0 ≤ (Y ω (-((j + 1 : ℕ) : ℤ)) : ℝ) -
          (Y ω (-((j + 2 : ℕ) : ℤ)) : ℝ) by linarith [hxlarge, hdiffR])
      have hmaxEq : max (Y ω (-((j + 1 : ℕ) : ℤ)) -
          Y ω (-((j + 2 : ℕ) : ℤ))) 0 =
          Y ω (-((j + 1 : ℕ) : ℤ)) - Y ω (-((j + 2 : ℕ) : ℤ)) :=
        max_eq_left hdiffNonneg
      rw [hmaxEq] at hq'
      have hpathNatR : ((Int.toNat (Y ω (-((j + 1 : ℕ) : ℤ)) -
          Y ω (-((j + 2 : ℕ) : ℤ)) : ℤ) : ℕ) : ℝ) ≤ (q'.length : ℝ) := by
        exact_mod_cast hq'
      have hnatCast : ((Int.toNat (Y ω (-((j + 1 : ℕ) : ℤ)) -
          Y ω (-((j + 2 : ℕ) : ℤ)) : ℤ) : ℕ) : ℝ) =
          (Y ω (-((j + 1 : ℕ) : ℤ)) : ℝ) -
            (Y ω (-((j + 2 : ℕ) : ℤ)) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hdiffNonneg)
      rw [hnatCast] at hpathNatR
      exact hdiffR.trans hpathNatR
    have houter := MeasureTheory.measure_mono_ae hhitSubset
    have hrealmono : iidCodeMeasure.real (incEvent ∩ hitEvent) ≤
        iidCodeMeasure.real target :=
      ENNReal.toReal_mono (by finiteness) houter
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
    have hnquarter : A < (n : ℝ) ^ (3 / 4 : ℝ) := by
      have hmul := (show A = A * 1 by ring)
      calc
        A = A * 1 := hmul
        _ < A * (A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) :=
          mul_lt_mul_of_pos_left hxlarge (by linarith)
        _ = (n : ℝ) ^ (3 / 4 : ℝ) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (by linarith : 0 < A)), one_mul]
    have hnhalf : A ^ (2 / 3 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        A ^ (2 / 3 : ℝ) < ((n : ℝ) ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) :=
          Real.rpow_lt_rpow (by linarith) hnquarter (by norm_num)
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1; ring
    have hnroot : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have hrecip : 1 / Real.sqrt (n : ℝ) < A ^ (-(2 / 3 : ℝ)) := by
      have hpospow : 0 < A ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hpowlt : A ^ (2 / 3 : ℝ) < Real.sqrt (n : ℝ) := by
        rwa [hnroot]
      rw [one_div, Real.rpow_neg (by linarith : 0 ≤ A)]
      exact (inv_lt_inv₀ hsqrt hpospow).2 hpowlt
    have hexpmon : A ^ (-(2 / 3 : ℝ)) ≤ A ^ (-(2 / 3 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ A) (by linarith)
    have hfloor : (K : ℝ) ≤
        A ^ (-(2 / 3 : ℝ) + ε) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      dsimp [K]
      exact Nat.floor_le (by positivity)
    have htimeErr : 4 * ((K : ℝ) + 1) / Real.sqrt n ≤
        8 * A ^ (-(2 / 3 : ℝ) + ε) := by
      have hdecomp : 4 * ((K : ℝ) + 1) / Real.sqrt n =
          4 * (K : ℝ) / Real.sqrt n + 4 / Real.sqrt n := by ring
      have hKbound : 4 * (K : ℝ) / Real.sqrt n ≤
          4 * A ^ (-(2 / 3 : ℝ) + ε) := by
        rw [hnroot] at *
        have hrootpos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
        calc
          4 * (K : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) ≤
              4 * (A ^ (-(2 / 3 : ℝ) + ε) * (n : ℝ) ^ (1 / 2 : ℝ)) /
                (n : ℝ) ^ (1 / 2 : ℝ) := by gcongr
          _ = 4 * A ^ (-(2 / 3 : ℝ) + ε) := by field_simp
      have hsmallerr : 4 / Real.sqrt n ≤ 4 * A ^ (-(2 / 3 : ℝ) + ε) := by
        have hrecip' : 1 / Real.sqrt n ≤ A ^ (-(2 / 3 : ℝ) + ε) := by
          exact le_of_lt (hrecip.trans_le hexpmon)
        calc
          4 / Real.sqrt n = 4 * (1 / Real.sqrt n) := by ring
          _ ≤ 4 * A ^ (-(2 / 3 : ℝ) + ε) :=
            mul_le_mul_of_nonneg_left hrecip' (by norm_num)
      rw [hdecomp]
      linarith
    calc
      1 - (8 * A ^ (-(2 / 3 : ℝ) + ε) +
          c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
          iidCodeMeasure.real (incEvent ∩ hitEvent) := by
            have := hIntLower
            linarith [htimeErr]
      _ ≤ iidCodeMeasure.real target := hrealmono

end DirectedDistances.PaperProofs.Section7
