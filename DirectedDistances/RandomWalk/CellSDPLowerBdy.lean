module

public import DirectedDistances.RandomWalk.SharpSurvival
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.KMSW.InfiniteGeodesic

/-! Supporting lemmas for paper labels `lem-cell-sdp-lower`, `lem-sdp-tri`, `thm-busemann` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem cellsdp_codeWalk_snd_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).2 - 1 ≤ (codeWalk ω (n + 1)).2 := by
  have h := (abs_le.mp (codeWalk_succ_sub_coord_abs_le_one ω n).2).1
  change (-1 : ℤ) ≤ (codeWalk ω (n + 1)).2 - (codeWalk ω n).2 at h
  omega

private theorem cellsdp_snd_survival_of_no_hit (ω : ℕ → Fin 3) (k N : ℕ) (hk : 1 ≤ k)
    (hno : ∀ j ≤ N, (codeWalk ω j).2 ≠ -(k : ℤ)) :
    ∀ j ≤ N, -(k : ℤ) < (codeWalk ω j).2 := by
  intro j hj
  induction j with
  | zero => simp [codeWalk_zero]; omega
  | succ j ih =>
      have hprev := ih (by omega)
      have hstep := cellsdp_codeWalk_snd_succ_ge ω j
      have hneq := hno (j + 1) hj
      omega

private theorem cellsdp_measurableSet_snd_survival (r N : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (((measurable_pi_apply n).comp measurable_codeWalk).snd)

/-- Sharp hitting form for the second coordinate: the first hit time of `-k` is at most `N`
with probability at least `1 - 4 k / √N`. Helper for `eqn-cell-sdp-lower-bdy` -/
theorem codeSndFirstHit_le_prob_ge (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    1 - 4 * (k : ℝ) / Real.sqrt N ≤
      iidCodeMeasure.real {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} := by
  classical
  have hsub : {ω : ℕ → Fin 3 | ∀ n ≤ N, -(k : ℤ) < (codeWalk ω n).2}ᶜ ⊆
      {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} := by
    intro ω hω
    by_contra hnot
    apply hω
    apply cellsdp_snd_survival_of_no_hit ω k N hk
    intro j hj hhit
    have hh : ∃ n, (codeWalk ω n).2 = -(k : ℤ) := ⟨j, hhit⟩
    have hfind : Nat.find hh ≤ j := Nat.find_min' hh hhit
    have htime : codeSndFirstHit (-(k : ℤ)) ω = (Nat.find hh : ℕ∞) := by
      simp [codeSndFirstHit, hh]
    apply hnot
    change codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)
    rw [htime]
    exact_mod_cast hfind.trans hj
  have htotal := measureReal_add_measureReal_compl (μ := iidCodeMeasure)
    (cellsdp_measurableSet_snd_survival k N)
  rw [probReal_univ] at htotal
  have h1 := lazy_survival_sharp_bound k N hk hN
  have h2 := measureReal_mono (μ := iidCodeMeasure) hsub
  linarith

/-- With `A = (16/δ)^2 + 2` and `n₀ = ⌈(16/δ)^2⌉₊ + 1` (both depending only on `δ`), for all
`n ≥ n₀` the second coordinate of the iid code walk first hits `-⌈A^{-1/2} √n⌉` by time `n`
with probability at least `1 - δ/2`. This is `eqn-cell-sdp-lower-bdy` -/
theorem exists_boundary_time_le_prob (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      1 - δ / 2 ≤ iidCodeMeasure.real
        {ω | codeSndFirstHit (-(⌈A ^ (-(1 / 2 : ℝ)) * Real.sqrt n⌉₊ : ℤ)) ω ≤ (n : ℕ∞)} := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 16 / δ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcδ : 8 / c = δ / 2 := by rw [hc]; field_simp; ring
  refine ⟨c ^ 2 + 2, by nlinarith, ⌈c ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hnc : c ^ 2 ≤ (n : ℝ) := by
    have h1 : c ^ 2 ≤ (⌈c ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈c ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn1 : 1 ≤ n := by omega
  have hs : c ≤ Real.sqrt n := by
    calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hcpos.le).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hnc
  have hspos : 0 < Real.sqrt n := lt_of_lt_of_le hcpos hs
  have hA : c ≤ Real.sqrt (c ^ 2 + 2) := by
    calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hcpos.le).symm
      _ ≤ Real.sqrt (c ^ 2 + 2) := Real.sqrt_le_sqrt (by linarith)
  have ha : (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (c ^ 2 + 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  have hale : (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) ≤ 1 / c := by
    rw [ha, one_div]
    exact inv_anti₀ hcpos hA
  have hapos : 0 < (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  set k : ℕ := ⌈(c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt n⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.ceil_pos.mpr (mul_pos hapos hspos)
  have hklt : (k : ℝ) < (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt n + 1 :=
    Nat.ceil_lt_add_one (mul_pos hapos hspos).le
  have hb := codeSndFirstHit_le_prob_ge k n hk1 hn1
  have hbound : 4 * (k : ℝ) / Real.sqrt n ≤ δ / 2 := by
    rw [div_le_iff₀ hspos]
    have h1 : (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt n ≤ Real.sqrt n / c := by
      calc (c ^ 2 + 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt n ≤ 1 / c * Real.sqrt n :=
            mul_le_mul_of_nonneg_right hale hspos.le
        _ = Real.sqrt n / c := by ring
    have h2 : 1 ≤ Real.sqrt n / c := by rw [le_div_iff₀ hcpos]; linarith
    have h3 : Real.sqrt n / c * (8 / c) ≤ 0 + Real.sqrt n / c * (8 / c) := by linarith
    have h4 : 8 / c * Real.sqrt n = 8 * (Real.sqrt n / c) := by ring
    rw [← hcδ, h4]
    nlinarith
  linarith

end DirectedDistances.RandomWalk

namespace DirectedDistances.KMSW
open Quiver

/-- if `xk` is reachable from `xl` and `w0` from `xk`, then
`sdp xl w0 ≤ sdp xk w0 + sdp xl xk`. -/
theorem present_sdp_concat_le {w : ℕ → Fin 3} {xl xk w0 : PresentVertex w}
    (_hlk : Reachable xl xk) (_hkw : Reachable xk w0) :
    DirectedDistances.sdp xl w0 ≤
      DirectedDistances.sdp xk w0 + DirectedDistances.sdp xl xk := by
  rw [add_comm]
  exact DirectedDistances.sdp_triangle xl xk w0

/-- Reachable pairs have finite shortest directed distance (used in `lem-sdp-tri`, -/
theorem present_sdp_ne_top {w : ℕ → Fin 3} {x z : PresentVertex w} (h : Reachable x z) :
    DirectedDistances.sdp x z ≠ ⊤ := fun ht =>
  DirectedDistances.sdp_eq_top_iff_not_reachable.1 ht h




theorem present_sdp_ge_of_busemann_identity {w : ℕ → Fin 3} {xl xk w0 : PresentVertex w}
    (Xl Xk : ℤ) (hlk : Reachable xl xk) (hkw : Reachable xk w0)
    (hbus : Xk - Xl =
      ((DirectedDistances.sdp xk w0).toNat : ℤ) - ((DirectedDistances.sdp xl w0).toNat : ℤ)) :
    Xl - Xk ≤ ((DirectedDistances.sdp xl xk).toNat : ℤ) := by
  have hconc := present_sdp_concat_le hlk hkw
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (present_sdp_ne_top hlk)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (present_sdp_ne_top hkw)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1
    (present_sdp_ne_top (hlk.trans hkw))
  rw [← ha, ← hb, ← hc, ← ENat.natCast_add] at hconc
  rw [← hb, ← hc] at hbus
  rw [← ha]
  have hle : c ≤ b + a := by exact_mod_cast hconc
  simp only [ENat.toNat_natCast] at hbus ⊢
  omega

end DirectedDistances.KMSW
