module

public import DirectedDistances.PaperProofs.Section7.BoltzmannRightBoundarySDP
public import DirectedDistances.PaperProofs.Section7.CellSDPLowerInfinite
public import DirectedDistances.PaperProofs.Section7.HitCoupling
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLawFull
public import DirectedDistances.RandomWalk.QuadrantWalkTotal
import DirectedDistances.PaperProofs.Section7.BoltzmannLDPUpperConditional
import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound

/-! # Conditional Boltzmann right-boundary SDP lower bound

Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`,
`StoppedRightBoundaryTransfer`; not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive
open DirectedDistances.PlanarMap Quiver
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. The lazy
walk maximal estimate bounds an early second-coordinate hit -/
theorem iidCodeWalk_snd_hit_by_time_probability_upper
    (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    iidCodeMeasure.real {ω | ∃ k ≤ n,
      (codeWalk ω k).2 = -(r : ℤ)} ≤
      4 * Real.exp (-((r : ℝ) ^ 2) / (2 * (n : ℝ))) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have htail := iidCodeWalk_blockMax_tail 0 n hn (r : ℝ) hrpos
  simp only [Nat.zero_add, codeWalk_zero, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at htail
  have hsub : {ω | ∃ k ≤ n, (codeWalk ω k).2 = -(r : ℤ)} ⊆
      {ω | ∃ k ≤ n,
        (r : ℝ) ≤ |((codeWalk ω k).1 : ℝ)| ∨
          (r : ℝ) ≤ |((codeWalk ω k).2 : ℝ)|} := by
    rintro ω ⟨k, hk, he⟩
    refine ⟨k, hk, Or.inr ?_⟩
    rw [he]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
    exact le_abs_self _
  exact (measureReal_mono hsub).trans htail

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. This is the
same early-hit estimate in the shifted source stream. -/
theorem iidSourceRightHitByTime_probability_upper
    (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    iidCodeMeasure.real {ω | ∃ k ≤ n,
      R (fun i => ω (i + 1)) k = -(r : ℤ)} ≤
      4 * Real.exp (-((r : ℝ) ^ 2) / (2 * (n : ℝ))) := by
  have hR (ω : ℕ → Fin 3) (k : ℕ) :
      R (fun i => ω (i + 1)) k = (codeWalk ω k).2 := by
    simp [R, codeWalk, Prod.snd_sum]
  have hset : {ω | ∃ k ≤ n,
      R (fun i => ω (i + 1)) k = -(r : ℤ)} =
      {ω | ∃ k ≤ n, (codeWalk ω k).2 = -(r : ℤ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, by rw [← hR ω k]; exact he⟩
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, by rw [hR ω k]; exact he⟩
  rw [hset]
  exact iidCodeWalk_snd_hit_by_time_probability_upper r n hr hn

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. The first
two source boundary vertices have limiting SDP one. -/
theorem boundaryPresent_initial_sdp_eq_one
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    DirectedDistances.sdp (boundaryPresentVertex w h 0)
      (boundaryPresentVertex w h 1) = 1 := by
  let x := boundaryPresentVertex w h 0
  let y := boundaryPresentVertex w h 1
  have hle : DirectedDistances.sdp x y ≤ 1 := by
    have hstage := sdp_limit_le_sdp_stage w 0
      (⟨boundaryVertex w h 0⟩ : StagePresentVertex w 0)
      ⟨boundaryVertex w h 1⟩
    simpa [x, y, boundaryPresentVertex, boundaryVertex_zero,
      boundaryVertex_one, sdp_stage_x0_x1] using hstage
  have hxy : x ≠ y := by
    intro hxy
    have hid := congrArg PresentVertex.id hxy
    simp [x, y, boundaryPresentVertex, boundaryVertex_zero,
      boundaryVertex_one] at hid
  have hne : DirectedDistances.sdp x y ≠ 0 := by
    intro hz
    exact hxy (sdp_eq_zero_iff.mp hz)
  have hge : (1 : ℕ∞) ≤ DirectedDistances.sdp x y :=
    Order.one_le_iff_ne_zero.mpr hne
  exact le_antisymm hle hge

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. This
probability bookkeeping allows the cell event to be nonmeasurable. -/
theorem probability_intersection_compl_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E H : Set Ω) {a b : ℝ}
    (hE : 1 - a ≤ μ.real E) (hH : μ.real H ≤ b) :
    1 - (a + b) ≤ μ.real (E ∩ Hᶜ) := by
  have hsub : E ⊆ (E ∩ Hᶜ) ∪ H := by
    intro x hx
    by_cases hh : x ∈ H
    · exact Or.inr hh
    · exact Or.inl ⟨hx, hh⟩
  have hmono := measureReal_mono (μ := μ) hsub
  have hunion := measureReal_union_le (μ := μ) (E ∩ Hᶜ) H
  linarith

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. Before the
right hit at radius `R`, every positive label incident to the finite LR list -/
theorem stageLR_endpoint_label_le_of_before_right_hit
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n e s K : ℕ) (hs : 1 ≤ s) (hK : 1 ≤ K)
    (he : e ∈ (kmswStage w n).LR)
    (hend : (kmswStage w n).west e = boundaryVertex w h (s : ℤ) ∨
      (kmswStage w n).east e = boundaryVertex w h (s : ℤ))
    (hn : n < boundaryHitTime w h (K : ℤ)) : s ≤ K := by
  rw [kmswStage_LR_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmle : m ≤ n := by
    have hmem := List.mem_range.mp (List.mem_filter.mp hm).1
    omega
  have hrecord : ∀ j, j < m → R w m < R w j :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  by_cases hm0 : m = 0
  · subst m
    have hroot := boundaryVertex_root_edge w h
    have hbound : act w 0 < (kmswStage w 0).nextEdge :=
      act_lt_nextEdge w (Nat.le_refl 0)
    have hstable := kmswStage_endpoints_stable w hmle hbound
    have hwest : (kmswStage w n).west (act w 0) = boundaryVertex w h 0 := by
      calc
        _ = (kmswStage w 0).west (act w 0) := hstable.1
        _ = boundaryVertex w h 0 := by
          simpa [act, kmswStage, kmswInit] using hroot.2.1
    have heast : (kmswStage w n).east (act w 0) = boundaryVertex w h 1 := by
      calc
        _ = (kmswStage w 0).east (act w 0) := hstable.2
        _ = boundaryVertex w h 1 := by
          simpa [act, kmswStage, kmswInit] using hroot.2.2.1
    rcases hend with hw | he'
    · have hlabel : boundaryVertex w h 0 = boundaryVertex w h (s : ℤ) :=
        hwest.symm.trans hw
      have hs0 := (boundaryVertex_injective w h) hlabel
      omega
    · have hlabel : boundaryVertex w h 1 = boundaryVertex w h (s : ℤ) :=
        heast.symm.trans he'
      have hs1 := (boundaryVertex_injective w h) hlabel
      omega
  · have hmpos : 0 < m := by omega
    let q : ℤ := -R w m
    have hq : 1 ≤ q := by
      have hrec := hrecord 0 (by omega)
      have hzero : R w 0 = 0 := by simp [R]
      dsimp [q]
      omega
    have hvalue : R w m = -q := by dsimp [q]; omega
    have hfind : boundaryHitTime w h q = Nat.find (h.rightHit q hq) := by
      unfold boundaryHitTime
      simp only [dite_eq_right (by omega : q ≠ 0),
        dite_eq_left (by omega : 0 < q)]
    have htime : boundaryHitTime w h q = m := by
      apply Nat.le_antisymm
      · rw [hfind]
        exact Nat.find_min' (h.rightHit q hq) hvalue
      · by_contra hnot
        have hlt : boundaryHitTime w h q < m := by omega
        have hbad := hrecord (boundaryHitTime w h q) hlt
        rw [hvalue, boundaryHitTime_right_spec w h hq] at hbad
        exact (lt_irrefl (-q)) hbad
    obtain ⟨N, hN, hEdge⟩ := boundaryVertex_right_edge w h hq
    have hNm : m ≤ N := by rw [← htime]; exact hN
    have hbound : act w m < (kmswStage w m).nextEdge :=
      act_lt_nextEdge w (Nat.le_refl m)
    have hstableN := kmswStage_endpoints_stable w hNm hbound
    have hstable := kmswStage_endpoints_stable w hmle hbound
    have hEdgeN := hEdge N le_rfl
    have hwestN : (kmswStage w N).west (act w m) = boundaryVertex w h q := by
      simpa [htime] using hEdgeN.2.2.1
    have heastN : (kmswStage w N).east (act w m) = boundaryVertex w h (q + 1) := by
      simpa [htime] using hEdgeN.2.2.2
    have hwest : (kmswStage w n).west (act w m) = boundaryVertex w h q := by
      calc
        _ = (kmswStage w m).west (act w m) := hstable.1
        _ = (kmswStage w N).west (act w m) := hstableN.1.symm
        _ = boundaryVertex w h q := hwestN
    have heast : (kmswStage w n).east (act w m) = boundaryVertex w h (q + 1) := by
      calc
        _ = (kmswStage w m).east (act w m) := hstable.2
        _ = (kmswStage w N).east (act w m) := hstableN.2.symm
        _ = boundaryVertex w h (q + 1) := heastN
    rcases hend with hw | he'
    · have hlabel : boundaryVertex w h q = boundaryVertex w h (s : ℤ) :=
        hwest.symm.trans hw
      have hqs := (boundaryVertex_injective w h) hlabel
      by_contra hnot
      have hsK : (K : ℤ) < (s : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hnot)
      have hmono := boundaryHitTime_right_mono w h
        (by exact_mod_cast hK) (by omega : (K : ℤ) ≤ (s : ℤ))
      have htimeS : boundaryHitTime w h (s : ℤ) = m := by
        rw [← hqs]
        exact htime
      omega
    · have hlabel : boundaryVertex w h (q + 1) = boundaryVertex w h (s : ℤ) :=
        heast.symm.trans he'
      have hqs := (boundaryVertex_injective w h) hlabel
      by_contra hnot
      have hsK : (K : ℤ) < (s : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hnot)
      have hKq : (K : ℤ) ≤ q := by omega
      have hmono := boundaryHitTime_right_mono w h
        (by exact_mod_cast hK) hKq
      omega

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. This is the
recorded local stopped-map transfer obligation from -/
@[expose] def StoppedRightBoundaryTransfer : Prop :=
  ∀ (ω : ℕ → Fin 3) (R : ℕ) (hR : 1 ≤ R)
    (_h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (n s : ℕ) (c : ℕ∞),
    n < boundaryHitTime (fun i => ω (i + 1)) hb (R : ℤ) →
    1 ≤ s →
    s ≤ R →
    (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
      (kmswStage (fun i => ω (i + 1)) n).west e =
          boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ) ∨
        (kmswStage (fun i => ω (i + 1)) n).east e =
          boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
    c ≤ DirectedDistances.sdp
      (boundaryPresentVertex (fun i => ω (i + 1)) hb 0)
      (boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
    let q := stoppedMarked R hR (quadrantHatWalk ω)
    ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map)
        (PresentVertex (fun i => ω (i + 1))),
      Function.Injective F.obj ∧
        F.obj q.1.2.2.out.B.source =
          boundaryPresentVertex (fun i => ω (i + 1)) hb 0 ∧
        ∃ i : Fin (R + 1),
          F.obj (rightBoundaryVertex q i) =
            boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ) ∧
          c ≤ presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
            (rightBoundaryVertex q i)

/-! Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. -/

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. The
constants and large-radius estimate follow the assembly at -/
theorem boltzmann_sdp_lower_conditional_constants
    (hstable : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)})
    (htransfer : StoppedRightBoundaryTransfer)
    {δ : ℝ} (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∃ r₀ : ℕ,
      2 * (r₀ : ℝ) ^ (3 / 4 : ℝ) ≤ A ∧ ∀ r : ℕ, r₀ ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  classical
  let κ : ℝ := δ / 64
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκlt : κ < 1 := by dsimp [κ]; linarith
  obtain ⟨A₀, hA₀, hcell⟩ :=
    cell_sdp_lower_infinite_conditional hstable (δ / 2) (by linarith)
  have hA₀pos : 0 < A₀ := by linarith
  let r₀ : ℕ := ⌈Real.sqrt (2 / κ)⌉₊
  have hr₀ : 1 ≤ r₀ := by
    have hsqrt : 1 ≤ Real.sqrt (2 / κ) := by
      apply Real.one_le_sqrt.mpr
      rw [le_div_iff₀ hκ]
      norm_num
      linarith
    have hceil : Real.sqrt (2 / κ) ≤ (r₀ : ℝ) := by
      dsimp [r₀]
      exact Nat.le_ceil _
    exact_mod_cast hsqrt.trans hceil
  let c : ℝ := A₀⁻¹ * (κ / 2) ^ (3 / 8 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr hA₀pos)
      (Real.rpow_pos_of_pos (by positivity) _)
  let A : ℝ := max (2 : ℝ) (max c⁻¹ (2 * (r₀ : ℝ) ^ (3 / 4 : ℝ)))
  have hA : 1 < A := by
    dsimp [A]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAc : A⁻¹ ≤ c := by
    have hbound : c⁻¹ ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc) hbound
  have hAr₀ : 2 * (r₀ : ℝ) ^ (3 / 4 : ℝ) ≤ A :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨A, hA, r₀, hAr₀, fun r hr => ?_⟩
  let n : ℕ := ⌊κ * (r : ℝ) ^ 2⌋₊
  have hrreal : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : 1 ≤ r := le_trans hr₀ hr
  have hr1 : 1 ≤ r := le_trans hr₀ hr
  have hrpow : 2 / κ ≤ (r : ℝ) ^ 2 := by
    have hsqrt : Real.sqrt (2 / κ) ≤ (r : ℝ) := by
      calc
        Real.sqrt (2 / κ) ≤ (r₀ : ℝ) := by
          dsimp [r₀]
          exact Nat.le_ceil _
        _ ≤ (r : ℝ) := hrreal
    have hsqrt_nonneg := Real.sqrt_nonneg (2 / κ)
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 / κ),
      sq_nonneg ((r : ℝ) - Real.sqrt (2 / κ))]
  have hx : 2 ≤ κ * (r : ℝ) ^ 2 := by
    rw [div_le_iff₀ hκ] at hrpow
    nlinarith
  have hnlo : κ * (r : ℝ) ^ 2 / 2 ≤ (n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (κ * (r : ℝ) ^ 2)
    dsimp [n]
    linarith
  have hn : 1 ≤ n := by
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by nlinarith [hnlo, hx]
    exact_mod_cast hnr
  have hnhi : (n : ℝ) ≤ κ * (r : ℝ) ^ 2 := by
    dsimp [n]
    exact Nat.floor_le (by positivity)
  have htailScale : 1 / (2 * κ) ≤ (r : ℝ) ^ 2 / (2 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * κ)
      (by positivity : 0 < 2 * (n : ℝ))]
    nlinarith [hnhi]
  have hexp : 4 * Real.exp (-1 / (2 * κ)) ≤ δ / 2 := by
    have hden : 1 + 32 / δ ≤ Real.exp (32 / δ) := by
      have := Real.add_one_le_exp (32 / δ)
      linarith
    have hfrac : 4 / Real.exp (32 / δ) ≤ δ / 2 := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      have hprod : (δ / 2) * (1 + 32 / δ) = δ / 2 + 16 := by
        rw [mul_add]
        have hcancel : (δ / 2) * (32 / δ) = 16 := by
          field_simp
          norm_num
        rw [hcancel]
        ring
      have hfour : 4 ≤ (δ / 2) * (1 + 32 / δ) := by
        rw [hprod]
        linarith [hδ]
      have hmul := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ δ / 2)
      exact hfour.trans hmul
    have hexpid : -1 / (2 * κ) = -(32 / δ) := by
      dsimp [κ]
      field_simp
      ring
    rw [hexpid, Real.exp_neg]
    simpa [one_div, div_eq_mul_inv] using hfrac
  have hhit : iidCodeMeasure.real
      {ω | ∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)} ≤ δ / 2 := by
    have hr1 : 1 ≤ r := le_trans hr₀ hr
    have hbound := iidSourceRightHitByTime_probability_upper r n hr1 hn
    have harg : -(r : ℝ) ^ 2 / (2 * (n : ℝ)) ≤ -1 / (2 * κ) := by
      have hneg := neg_le_neg htailScale
      simpa only [neg_div] using hneg
    calc
      _ ≤ 4 * Real.exp (-((r : ℝ) ^ 2) / (2 * (n : ℝ))) := hbound
      _ ≤ 4 * Real.exp (-1 / (2 * κ)) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
      _ ≤ δ / 2 := hexp
  let E : Set (ℕ → Fin 3) := {ω |
    ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ s : ℕ,
      1 ≤ s ∧
        (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
          ((kmswStage (fun i => ω (i + 1)) n).west e =
              boundaryVertex (fun i => ω (i + 1)) h (s : ℤ)) ∨
            (kmswStage (fun i => ω (i + 1)) n).east e =
              boundaryVertex (fun i => ω (i + 1)) h (s : ℤ)) ∧
        A₀⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
          ((DirectedDistances.sdp
            (boundaryPresentVertex (fun i => ω (i + 1)) h 0)
            (boundaryPresentVertex (fun i => ω (i + 1)) h (s : ℤ))).toNat : ℝ)}
  let H : Set (ℕ → Fin 3) := {ω |
    ∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)}
  have hcellprob : 1 - δ / 2 ≤ iidCodeMeasure.real E := by
    simpa [E] using hcell n hn
  have hinter : 1 - δ ≤ iidCodeMeasure.real (E ∩ Hᶜ) := by
    have hh := probability_intersection_compl_lower_bound iidCodeMeasure E H
      hcellprob hhit
    linarith
  let f : (ℕ → Fin 3) → RightVertexMarkedBoltzmannSpace r := fun ω =>
    stoppedMarked r hr1 (quadrantHatWalk ω)
  let T : Set (RightVertexMarkedBoltzmannSpace r) :=
    rightBoundarySDPEvent r (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))
  have hsub : E ∩ Hᶜ ≤ᵐ[iidCodeMeasure] {ω | f ω ∈ T} := by
    filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hflows hω
    change ω ∈ E ∩ Hᶜ at hω
    rcases hω with ⟨⟨h, s, hs, hedge, hsdp⟩, hno⟩
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    have hwflow : HasFlowLineHits w := by
      simpa [w, Nat.zero_add] using hflows 0
    have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
    have htime : n < boundaryHitTime w h (r : ℤ) := by
      by_contra hnot
      have hle : boundaryHitTime w h (r : ℤ) ≤ n := Nat.le_of_not_gt hnot
      have hhitval := boundaryHitTime_right_spec w h hrZ
      exact hno ⟨boundaryHitTime w h (r : ℤ), hle, hhitval⟩
    rcases hedge with ⟨e, he, hend⟩
    have hsle : s ≤ r :=
      stageLR_endpoint_label_le_of_before_right_hit w h n e s r hs hr1 he hend htime
    have hpow : (κ / 2) * (r : ℝ) ^ 2 ≤ (n : ℝ) := by
      linarith [hnlo]
    have hroot := Real.rpow_le_rpow (by positivity :
      0 ≤ (κ / 2) * (r : ℝ) ^ 2) hpow
      (by norm_num : (0 : ℝ) ≤ 3 / 8)
    have heq : ((κ / 2) * (r : ℝ) ^ 2) ^ (3 / 8 : ℝ) =
        (κ / 2) ^ (3 / 8 : ℝ) * (r : ℝ) ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast (r : ℝ) 2,
        ← Real.rpow_mul (by positivity : 0 ≤ (r : ℝ))]
      congr 1
      norm_num
    have hbase : (κ / 2) ^ (3 / 8 : ℝ) *
        (r : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 8 : ℝ) := by
      rw [← heq]
      exact hroot
    have hscale : A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ) ≤
        A₀⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) := by
      calc
        A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ) ≤
            c * (r : ℝ) ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hAc (Real.rpow_nonneg (by positivity) _)
        _ = A₀⁻¹ * ((κ / 2) ^ (3 / 8 : ℝ) *
              (r : ℝ) ^ (3 / 4 : ℝ)) := by dsimp [c]; ring
        _ ≤ A₀⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hA₀pos.le)
    have hsdp' : A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ) ≤
        ((DirectedDistances.sdp (boundaryPresentVertex w h 0)
          (boundaryPresentVertex w h (s : ℤ))).toNat : ℝ) := hscale.trans hsdp
    let D := DirectedDistances.sdp (boundaryPresentVertex w h 0)
      (boundaryPresentVertex w h (s : ℤ))
    have hDtop : D ≠ ⊤ := by
      intro htop
      have hpos : 0 < A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ) :=
        mul_pos (inv_pos.mpr (by linarith))
          (Real.rpow_pos_of_pos (by positivity) _)
      simp [D, htop] at hsdp'
      linarith
    have hDcast : D = (D.toNat : ℕ∞) := (ENat.natCast_toNat hDtop).symm
    have hthreshold : ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤
        ENat.toENNReal D := by
      calc
        _ ≤ ENNReal.ofReal ((D.toNat : ℕ) : ℝ) :=
          ENNReal.ofReal_le_ofReal hsdp'
        _ = ENat.toENNReal D := by rw [hDcast]; simp
    obtain ⟨_, _, _, i, _, hdist⟩ :=
      htransfer ω r hr1 hwflow h n s D htime hs hsle ⟨e, he, hend⟩
        (by dsimp [D]; exact le_rfl)
    have hdist' := ENat.toENNReal_mono hdist
    change f ω ∈ T
    refine ⟨i, ?_⟩
    exact hthreshold.trans hdist'
  have hmeas : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_rightBoundarySDPEvent _ _
  have hf : AEMeasurable f iidCodeMeasure :=
    (measurable_stoppedMarked r hr1).comp_aemeasurable aemeasurable_quadrantHatWalk
  have hmapreal : iidCodeMeasure.real {ω | f ω ∈ T} =
      (rightVertexMarkedBoltzmannLaw r).real T := by
    have hmap := iidCodeMeasure_map_quadrantHatWalk_stoppedMarked r hr1
    change ENNReal.toReal (iidCodeMeasure {ω | f ω ∈ T}) =
      ENNReal.toReal ((rightVertexMarkedBoltzmannLaw r) T)
    rw [← hmap, Measure.map_apply_of_aemeasurable hf hmeas]
    rfl
  have hmono : iidCodeMeasure.real (E ∩ Hᶜ) ≤
      iidCodeMeasure.real {ω | f ω ∈ T} := by
    apply ENNReal.toReal_mono (by finiteness)
    exact measure_mono_ae hsub
  calc
    1 - δ ≤ iidCodeMeasure.real (E ∩ Hᶜ) := hinter
    _ ≤ iidCodeMeasure.real {ω | f ω ∈ T} := hmono
    _ = (rightVertexMarkedBoltzmannLaw r).real T := hmapreal

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); conditional on
`hstable` and `StoppedRightBoundaryTransfer`; not a paper result. This is the
per-radius conclusion after the small-radius sink case -/
theorem boltzmann_sdp_lower_conditional
    (hstable : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)})
    (htransfer : StoppedRightBoundaryTransfer) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  classical
  intro δ hδ
  by_cases hδlt : δ < 1
  · obtain ⟨A, hA, r₀, hAr₀, hlarge⟩ :=
      boltzmann_sdp_lower_conditional_constants hstable htransfer hδ hδlt
    refine ⟨A, hA, fun r hr => ?_⟩
    by_cases hrlarge : r₀ ≤ r
    · exact hlarge r hrlarge
    · have hrsmall : r < r₀ := Nat.lt_of_not_ge hrlarge
      have hrpow : (r : ℝ) ^ (3 / 4 : ℝ) ≤
          (r₀ : ℝ) ^ (3 / 4 : ℝ) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _
          (by norm_num : (0 : ℝ) ≤ 3 / 4)
        exact_mod_cast (Nat.le_of_lt hrsmall)
      have hApos : 0 < A := by linarith
      have hmul : A⁻¹ * (2 * (r₀ : ℝ) ^ (3 / 4 : ℝ)) ≤ A⁻¹ * A :=
        mul_le_mul_of_nonneg_left hAr₀ (inv_nonneg.mpr hApos.le)
      have hmul' : 2 * (A⁻¹ * (r₀ : ℝ) ^ (3 / 4 : ℝ)) ≤ 1 := by
        calc
          2 * (A⁻¹ * (r₀ : ℝ) ^ (3 / 4 : ℝ)) =
              A⁻¹ * (2 * (r₀ : ℝ) ^ (3 / 4 : ℝ)) := by ring
          _ ≤ A⁻¹ * A := hmul
          _ = 1 := inv_mul_cancel₀ hApos.ne'
      have hsmall : A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ) ≤ 1 := by
        have hpow' := mul_le_mul_of_nonneg_left hrpow
          (inv_nonneg.mpr hApos.le)
        nlinarith [hmul']
      let T : Set (RightVertexMarkedBoltzmannSpace r) :=
        rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))
      have hfull : Set.univ ⊆ T := by
        intro q _
        have hthreshold : ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤ 1 := by
          calc
            _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hsmall
            _ = 1 := ENNReal.ofReal_one
        change ∃ i : Fin (r + 1),
          ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤
            ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
              q.1.2.2.out.B.source (rightBoundaryVertex q i))
        refine ⟨⟨r, by omega⟩, ?_⟩
        let B := q.1.2.2.out.B
        have hsource : B.source ≠ B.sink := bipolar_source_ne_sink B
        have hnonzero : presentDartSDP B.map B.source B.sink ≠ 0 := by
          intro hz
          exact hsource (sdp_eq_zero_iff.mp (by simpa [presentDartSDP] using hz))
        have hdist : (1 : ℝ≥0∞) ≤
            ENat.toENNReal (presentDartSDP B.map B.source B.sink) :=
          by
            simpa only [ENat.toENNReal_one] using
              ENat.toENNReal_mono (Order.one_le_iff_ne_zero.mpr hnonzero)
        rw [rightBoundaryVertex_last]
        exact hthreshold.trans hdist
      have hpre : {ω | (stoppedMarked r hr (quadrantHatWalk ω)) ∈ T} =
          Set.univ := by
        apply Set.eq_univ_iff_forall.mpr
        intro ω
        exact hfull (Set.mem_univ _)
      have hmeas : MeasurableSet T := by
        dsimp [T]
        exact measurableSet_rightBoundarySDPEvent _ _
      let f : (ℕ → Fin 3) → RightVertexMarkedBoltzmannSpace r := fun ω =>
        stoppedMarked r hr (quadrantHatWalk ω)
      have hf : AEMeasurable f iidCodeMeasure :=
        (measurable_stoppedMarked r hr).comp_aemeasurable
          aemeasurable_quadrantHatWalk
      have hmapreal : iidCodeMeasure.real {ω | f ω ∈ T} =
          (rightVertexMarkedBoltzmannLaw r).real T := by
        have hmap := iidCodeMeasure_map_quadrantHatWalk_stoppedMarked r hr
        change ENNReal.toReal (iidCodeMeasure {ω | f ω ∈ T}) =
          ENNReal.toReal ((rightVertexMarkedBoltzmannLaw r) T)
        rw [← hmap, Measure.map_apply_of_aemeasurable hf hmeas]
        rfl
      have hprob : 1 ≤ iidCodeMeasure.real {ω | f ω ∈ T} := by
        rw [show {ω | f ω ∈ T} = Set.univ by simpa only [f] using hpre]
        simp
      have hlargeprob : 1 ≤ (rightVertexMarkedBoltzmannLaw r).real T :=
        hmapreal ▸ hprob
      linarith
  · refine ⟨2, by norm_num, fun r hr => ?_⟩
    have hprob : 0 ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (2⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) :=
      ENNReal.toReal_nonneg
    have hδle : 1 - δ ≤ 0 := by linarith
    exact hδle.trans hprob

end DirectedDistances.PaperProofs.Section7
