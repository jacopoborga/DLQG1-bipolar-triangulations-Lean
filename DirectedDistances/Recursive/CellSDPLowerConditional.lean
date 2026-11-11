module

public import DirectedDistances.RandomWalk.CellSDPLowerBdy
public import DirectedDistances.KMSW.BusemannItemForms
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.KMSW.InftyCutEastChain
import DirectedDistances.KMSW.DirectedContainHat

/-! Supporting lemmas for paper labels `lem-cell-sdp-lower`, `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver MeasureTheory ProbabilityTheory

private theorem right_step_abs (w : ℕ → Fin 3) (i : ℕ) :
    |R w (i + 1) - R w i| ≤ 1 := by
  have hr : R w (i + 1) = R w i +
      (lazyTwoDimensionalStep (w i)).2 := Finset.sum_range_succ _ _
  rw [hr, add_sub_cancel_left]
  have hc : ∀ c : Fin 3, |(lazyTwoDimensionalStep c).2| ≤ 1 := by
    intro c
    fin_cases c <;> norm_num [lazyTwoDimensionalStep]
  exact hc _

private theorem hit_strict_record (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {r : ℕ} (hr : 1 ≤ r) :
    ∀ j < boundaryHitTime w h (r : ℤ),
      R w (boundaryHitTime w h (r : ℤ)) < R w j := by
  have hrz : 1 ≤ (r : ℤ) := by exact_mod_cast hr
  have hfind : boundaryHitTime w h (r : ℤ) = Nat.find (h.rightHit _ hrz) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : (r : ℤ) ≠ 0),
      dite_eq_left (by omega : 0 < (r : ℤ))]
  have hc := (strict_running_minimum_iff_first_hit (R w) (by simp [R])
    (right_step_abs w) (boundaryHitTime w h (r : ℤ))
    (boundaryHitTime w h (r : ℤ)) (-(r : ℤ)) (by omega)
    (h.rightHit _ hrz)).2
    ⟨le_rfl, boundaryHitTime_right_spec w h hrz, hfind⟩
  exact (Finset.mem_filter.mp hc.1).2

private theorem hit_mono (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    boundaryHitTime w h (r : ℤ) ≤ boundaryHitTime w h (k : ℤ) := by
  by_contra hnot
  have hh := hit_strict_record w h hr (boundaryHitTime w h (k : ℤ)) (by omega)
  rw [boundaryHitTime_right_spec w h (by omega : 1 ≤ (r : ℤ)),
    boundaryHitTime_right_spec w h (by omega : 1 ≤ (k : ℤ))] at hh
  omega

/-- Deterministic helper for `lem-cell-sdp-lower`
`x_r` is an allocated stage vertex and the west endpoint of an LR edge.
The comparison uses extended-natural SDP, preserving unreachable `⊤`. -/
theorem boundary_vertex_stage_lower_right (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (r n : ℕ) (hr : 1 ≤ r)
    (ht : boundaryHitTime w h (r : ℤ) ≤ n) :
    boundaryVertex w h (r : ℤ) < (kmswStage w n).nextVertex ∧
    (∃ e ∈ (kmswStage w n).LR,
      (kmswStage w n).west e = boundaryVertex w h (r : ℤ)) ∧
    sdp (boundaryPresentVertex w h 0) (boundaryPresentVertex w h (r : ℤ)) ≤
      sdp (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
        ⟨boundaryVertex w h (r : ℤ)⟩ := by
  let t := boundaryHitTime w h (r : ℤ)
  have he : act w t ∈ (kmswStage w n).LR := by
    rw [kmswStage_LR_eq]
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by dsimp [t]; omega),
        decide_eq_true (hit_strict_record w h hr)⟩, rfl⟩
  have heid := act_lt_nextEdge w ht
  have hw : (kmswStage w n).west (act w t) = boundaryVertex w h (r : ℤ) := by
    rw [boundaryVertex_eq_edgeWest_hit]
    exact (edge_endpoints_eq w heid).1
  refine ⟨?_, ⟨_, he, hw⟩, ?_⟩
  · rw [← hw]
    exact (kmswStage_endpoints_lt_nextVertex w n _ heid).1
  · exact sdp_limit_le_sdp_stage w n ⟨boundaryVertex w h 0⟩
      ⟨boundaryVertex w h (r : ℤ)⟩

private theorem stage_boundary_arrow (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (j n : ℕ) (ht : boundaryHitTime w h (j : ℤ) ≤ n) :
    Nonempty ((⟨boundaryVertex w h (j : ℤ)⟩ : StagePresentVertex w n) ⟶
      ⟨boundaryVertex w h ((j : ℤ) + 1)⟩) := by
  by_cases hj : j = 0
  · subst j
    simpa only [Nat.cast_zero, zero_add, boundaryVertex_zero, boundaryVertex_one] using
      (show Nonempty ((⟨0⟩ : StagePresentVertex w n) ⟶ ⟨1⟩) from
        ⟨initialEdgeArrow w n⟩)
  · have hj1 : 1 ≤ j := by omega
    have heid := act_lt_nextEdge w ht
    have hmem : act w (boundaryHitTime w h (j : ℤ)) ∈ (kmswStage w n).LR := by
      rw [kmswStage_LR_eq]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), decide_eq_true (hit_strict_record w h hj1)⟩, rfl⟩
    have he := boundaryHitTime_right_boundary_edge w h hj1
    have hend := edge_endpoints_eq w heid
    exact ⟨⟨_, heid, (kmswStage_status w n).2.2.1 _ hmem,
      hend.1.trans he.2.1, hend.2.trans he.2.2⟩⟩

/-- The finite LR chain reaches `x_r` already at stage `n` when `τ_r ≤ n`.
This supplies finiteness before taking `toNat` in the conditional SDP helper -/
theorem stage_boundary_reachable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (r n : ℕ) (ht : boundaryHitTime w h (r : ℤ) ≤ n) :
    Reachable (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
      ⟨boundaryVertex w h (r : ℤ)⟩ := by
  have hchain : ∀ j ≤ r,
      Reachable (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
        ⟨boundaryVertex w h (j : ℤ)⟩ := by
    intro j hj
    induction j with
    | zero => exact Reachable.refl _
    | succ j ih =>
      have htj : boundaryHitTime w h (j : ℤ) ≤ n := by
        by_cases hj0 : j = 0
        · subst j; simpa only [Nat.cast_zero, boundaryHitTime_zero] using Nat.zero_le n
        · exact (hit_mono w h (by omega) (by omega : j ≤ r)).trans ht
      obtain ⟨e⟩ := stage_boundary_arrow w h j n htj
      obtain ⟨p⟩ := ih (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using (show Reachable
        (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
        ⟨boundaryVertex w h ((j : ℤ) + 1)⟩ from ⟨p.cons e⟩)
  exact hchain r le_rfl

private theorem negative_busemann_stage :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n k : ℕ, 1 ≤ k →
      codeSndFirstHit (-(k : ℤ)) ω ≤ (n : ℕ∞) →
      ∀ t : ℝ, 0 < t →
      (∃ r : ℕ, r ≤ k ∧ (busemannSDPMeasurableVersion ω r : ℝ) ≤ -t) →
      ∃ y : StagePresentVertex (fun i => ω (i + 1)) n,
        y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex ∧
        (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
          (kmswStage (fun i => ω (i + 1)) n).west e = y.id ∨
          (kmswStage (fun i => ω (i + 1)) n).east e = y.id) ∧
        Reachable (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y ∧
        t ≤ ((sdp (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y).toNat : ℝ) := by
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
  have htk : boundaryHitTime (fun i => ω (i + 1)) h (k : ℤ) ≤ n := by
    rw [codeSndFirstHit_eq_boundaryHitTime ω h (by exact_mod_cast hk)] at ht
    exact_mod_cast ht
  have htr := (hit_mono _ h hr1 hrk).trans htk
  obtain ⟨halloc, ⟨e, he, hw⟩, hcmp⟩ :=
    boundary_vertex_stage_lower_right _ h r n hr1 htr
  have hreach := stage_boundary_reachable _ h r n htr
  have hfin : sdp (⟨boundaryVertex _ h 0⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
      ⟨boundaryVertex _ h (r : ℤ)⟩ ≠ ⊤ := by
    intro hh
    exact sdp_eq_top_iff_not_reachable.mp hh hreach
  have hcmpNat := ENat.toNat_le_toNat hcmp hfin
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
  refine ⟨⟨boundaryVertex _ h (r : ℤ)⟩, halloc,
    ⟨e, he, Or.inl hw⟩, ?_, ?_⟩
  · simpa only [boundaryVertex_zero] using hreach
  · have hh : t ≤ ((sdp (⟨boundaryVertex _ h 0⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
        ⟨boundaryVertex _ h (r : ℤ)⟩).toNat : ℝ) := by linarith
    simpa only [boundaryVertex_zero] using hh

private theorem stage_small_bound (w : ℕ → Fin 3) (n : ℕ) (t : ℝ) (ht : t ≤ 1) :
    ∃ y : StagePresentVertex w n, y.id < (kmswStage w n).nextVertex ∧
      (∃ e ∈ (kmswStage w n).LR,
        (kmswStage w n).west e = y.id ∨ (kmswStage w n).east e = y.id) ∧
      Reachable (⟨0⟩ : StagePresentVertex w n) y ∧
      t ≤ ((sdp (⟨0⟩ : StagePresentVertex w n) y).toNat : ℝ) := by
  have he := initial_edge_present w n
  have hend := initial_edge_endpoints w n
  have hv := (kmswStage_endpoints_lt_nextVertex w n 0 he.1).2
  rw [hend.2] at hv
  have hLR : 0 ∈ (kmswStage w n).LR := by
    rw [kmswStage_LR_eq]
    exact List.mem_map.mpr ⟨0, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩
  refine ⟨⟨1⟩, hv, ⟨0, hLR, Or.inr hend.2⟩,
    ⟨Hom.toPath (initialEdgeArrow w n)⟩, ?_⟩
  simpa only [sdp_stage_x0_x1, ENat.toNat_one, Nat.cast_one] using ht







theorem cell_sdp_lower_of_stable
    (hstable : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)}) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ,
      1 - δ ≤ iidCodeMeasure.real
        {ω | ∃ y : StagePresentVertex (fun i => ω (i + 1)) n,
          y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e = y.id ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = y.id) ∧
          Reachable (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y).toNat : ℝ)} := by
  intro δ hδ
  classical
  let E := fun (t : ℝ) (n : ℕ) =>
    {ω : ℕ → Fin 3 | ∃ y : StagePresentVertex (fun i => ω (i + 1)) n,
      y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex ∧
      (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
        (kmswStage (fun i => ω (i + 1)) n).west e = y.id ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = y.id) ∧
      Reachable (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y ∧
      t ≤ ((sdp (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) n) y).toNat : ℝ)}
  have hE_mono (n : ℕ) {s t : ℝ} (hst : s ≤ t) : E t n ⊆ E s n := by
    rintro ω ⟨y, hy, he, hr, hd⟩
    exact ⟨y, hy, he, hr, hst.trans hd⟩
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
  refine ⟨A, hA, fun n => ?_⟩
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
    have hfull : E (A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ)) n = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact stage_small_bound _ n _ ht
    rw [hfull, probReal_univ]
    linarith

end DirectedDistances.Recursive
