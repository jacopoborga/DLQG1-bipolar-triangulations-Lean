/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingTransferCoupledGerm
public import DirectedDistances.PlanarMap.PLDrawingUniformCones
public import DirectedDistances.PlanarMap.PLDrawingDartBordersTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Dart borders under the past drawing transfer

Helpers toward the Q-M0-repr face correspondence; not paper results.
The actual coupled germ gives uniform forward and inverse left-wedge
containments, with the explicit radii of `pastConeRadius`. -/

public section

namespace DirectedDistances.KMSW.WholePlanePastGlueData

open DirectedDistances.PlanarMap

/-- Helper toward Q-M0-repr; not a paper result. A single coordinate piece
is continuous. -/
private theorem dartBordersIff_linear_continuous (a b : ℝ) :
    Continuous (pastLinear a b) := by
  have heq : pastLinear a b = fun z : ℂ =>
      ((-a * z.re : ℝ) : ℂ) + ((-z.im + b * z.re : ℝ) : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [pastLinear]
  rw [heq]
  exact (Complex.continuous_ofReal.comp (continuous_const.mul Complex.continuous_re)).add
    ((Complex.continuous_ofReal.comp
      (Complex.continuous_im.neg.add (continuous_const.mul Complex.continuous_re))).mul
        continuous_const)

/-- Helper toward Q-M0-repr; not a paper result. The two direction pieces
join continuously on the vertical axis. -/
private theorem dartBordersIff_direction_continuous (aPos aNeg bPos bNeg : ℝ) :
    Continuous (pastDirection aPos aNeg bPos bNeg) := by
  have heq : pastDirection aPos aNeg bPos bNeg = fun z : ℂ =>
      pastLinear aNeg bNeg z + ((max z.re 0 : ℝ) : ℂ) *
        (⟨aNeg - aPos, bPos - bNeg⟩ : ℂ) := by
    funext z
    by_cases hp : 0 < z.re
    · apply Complex.ext <;>
        simp [pastDirection, pastLinear, hp, max_eq_left hp.le] <;> ring
    · apply Complex.ext <;>
        simp [pastDirection, pastLinear, hp, max_eq_right (not_lt.mp hp)]
  rw [heq]
  exact (dartBordersIff_linear_continuous aNeg bNeg).add
    ((Complex.continuous_ofReal.comp
      (Complex.continuous_re.max continuous_const)).mul continuous_const)

/-- Helper toward Q-M0-repr; not a paper result. Recover the meaning of the
hidden `pastConeV` body from the exported small-wedge identities, by continuity
at aperture zero. This does not unfold any hidden definition. -/
private theorem dartBordersIff_coneV_eq_direction
    (aPos aNeg bPos bNeg : ℝ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (u : ℂ) (hu : u ≠ 0) :
    pastConeV aPos aNeg bPos bNeg u = pastDirection aPos aNeg bPos bNeg u := by
  let rho := pastConeRadius aPos aNeg bPos bNeg 1 1 1 u
  obtain ⟨hrho, h1, heta, _⟩ := pastConeRadius_pos_caps
    aPos aNeg bPos bNeg 1 1 1 u haPos haNeg zero_lt_one zero_lt_one zero_lt_one hu
  have heq : Set.EqOn
      (fun e : ℝ => pastDirection aPos aNeg bPos bNeg (u + (e : ℂ) * Complex.I * u))
      (fun e : ℝ => pastLinear (pastConeSlopeA aPos aNeg u)
        (pastConeSlopeB bPos bNeg u) (u + (e : ℂ) * Complex.I * u))
      (Set.Ioo 0 rho) := by
    intro e he
    exact pastDirection_perturbed_selected aPos aNeg bPos bNeg u hu e he.1
      (he.2.trans_le h1).le (he.2.trans_le heta)
  have harg : Continuous (fun e : ℝ => u + (e : ℂ) * Complex.I * u) :=
    continuous_const.add ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo 0 rho) := by
    rw [closure_Ioo (ne_of_lt hrho)]
    exact ⟨le_rfl, hrho.le⟩
  have hstart := heq.closure
    ((dartBordersIff_direction_continuous aPos aNeg bPos bNeg).comp harg)
    ((dartBordersIff_linear_continuous _ _).comp harg) hzero
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hstart
  exact (pastConeV_eq_selectedLinear aPos aNeg bPos bNeg u).trans hstart.symm

/-- Helper toward Q-M0-repr; not a paper result. A certified strip germ
transfers every sufficiently small left wedge with one explicit bound. -/
private theorem dartBordersIff_wedge_of_germ
    (T : ℂ ≃ₜ ℂ) (p u q : ℂ) (r aPos aNeg bPos bNeg c Delta : ℝ)
    (hr : 0 < r) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hc : 0 < c) (hDelta : 0 < Delta) (hu : u ≠ 0)
    (hg : ∀ h : ℂ, |h.re| < r →
      T (p + h) = T p + pastDirection aPos aNeg bPos bNeg h)
    (hq : q = (c : ℂ) * pastDirection aPos aNeg bPos bNeg u) :
    0 < pastConeRadius aPos aNeg bPos bNeg c r Delta u ∧
      ∀ t eps : ℝ, 0 < t →
        t < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
        0 < eps → eps < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
        ∃ s eps' : ℝ, 0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
          T (p + (t : ℂ) * (u + (eps : ℂ) * Complex.I * u)) =
            T p + (s : ℂ) * (q + (eps' : ℂ) * Complex.I * q) := by
  obtain ⟨hcaps, hw⟩ := pastCone_uniform_forward aPos aNeg bPos bNeg c r Delta u
    haPos haNeg hc hr hDelta hu
  refine ⟨hcaps.1, ?_⟩
  intro t eps ht htr he her
  obtain ⟨hstrip, _, _, hs, hsD, he', he'D, hmap⟩ := hw t eps ht htr he her
  refine ⟨_, _, hs, hsD, he', he'D, ?_⟩
  rw [hg _ hstrip, hmap]
  rw [dartBordersIff_coneV_eq_direction aPos aNeg bPos bNeg haPos haNeg u hu, ← hq]
  simp only [mul_assoc]

/-- Helper toward Q-M0-repr; not a paper result. The explicit inverse
direction map is also a right inverse, including on the vertical axis. -/
private theorem dartBordersIff_direction_right_inverse
    (aPos aNeg bPos bNeg : ℝ) (haPos : 0 < aPos) (haNeg : 0 < aNeg) (h : ℂ) :
    pastDirection aPos aNeg bPos bNeg
      (pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) h) = h := by
  have hpos : -(-bPos / aPos) / (1 / aPos) = bPos := by
    field_simp
  have hneg : -(-bNeg / aNeg) / (1 / aNeg) = bNeg := by
    field_simp
  have hi := pastDirection_inverse (1 / aNeg) (1 / aPos)
    (-bNeg / aNeg) (-bPos / aPos) (one_div_pos.mpr haNeg) (one_div_pos.mpr haPos) h
  simpa only [one_div_one_div, hpos, hneg] using hi

/-- Helper toward Q-M0-repr; not a paper result. The same actual slopes
give the inverse transfer germ on the explicit smaller vertical strip. -/
private theorem dartBordersIff_inverse_germ
    (T : ℂ ≃ₜ ℂ) (p : ℂ) (r aPos aNeg bPos bNeg : ℝ)
    (hr : 0 < r) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hg : ∀ h : ℂ, |h.re| < r →
      T (p + h) = T p + pastDirection aPos aNeg bPos bNeg h) :
    ∀ h : ℂ, |h.re| < r * min aPos aNeg →
      T.symm (T p + h) = p +
        pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) h := by
  intro h hh
  have hstrip : |(pastDirection (1 / aNeg) (1 / aPos)
      (-bNeg / aNeg) (-bPos / aPos) h).re| < r := by
    by_cases hp : 0 < h.re
    · have hbound : |h.re| < r * aNeg :=
        hh.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le)
      have he : |-(1 / aNeg) * h.re| = |h.re| / aNeg := by
        rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos haNeg]
        ring
      simp only [pastDirection, ite_eq_left hp]
      rw [he]
      exact (div_lt_iff₀ haNeg).mpr hbound
    · have hbound : |h.re| < r * aPos :=
        hh.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hr.le)
      have he : |-(1 / aPos) * h.re| = |h.re| / aPos := by
        rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos haPos]
        ring
      simp only [pastDirection, ite_eq_right hp]
      rw [he]
      exact (div_lt_iff₀ haPos).mpr hbound
  apply T.injective
  rw [T.apply_symm_apply, hg _ hstrip,
    dartBordersIff_direction_right_inverse aPos aNeg bPos bNeg haPos haNeg]

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "wp" => kmswPastCode W
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)

/-- Helper toward Q-M0-repr; not a paper result. For every positive output
bound, the forward wedge containment holds uniformly with the explicit
`pastConeRadius` for the actual coupled germ. -/
theorem pastDrawing_wedge_uniform_forward (d : ℕ × Bool) (Delta : ℝ) (hDelta : 0 < Delta) :
    ∃ r aPos aNeg bPos bNeg c : ℝ,
      0 < r ∧ 0 < aPos ∧ 0 < aNeg ∧ 0 < c ∧
      let rho := pastConeRadius aPos aNeg bPos bNeg c r Delta
        ((Pp).arc d).initialDirection
      0 < rho ∧ ∀ t eps : ℝ, 0 < t → t < rho → 0 < eps → eps < rho →
        ∃ s eps' : ℝ, 0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
          (T) (((Pp).arc d).start + (t : ℂ) *
            (((Pp).arc d).initialDirection + (eps : ℂ) * Complex.I *
              ((Pp).arc d).initialDirection)) =
            ((Pt).arc d).start + (s : ℂ) *
              (((Pt).arc d).initialDirection + (eps' : ℂ) * Complex.I *
                ((Pt).arc d).initialDirection) := by
  obtain ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, hg, hq⟩ :=
    transferArcDirection_coupledGerm W h0 hp H d
  refine ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, ?_⟩
  rw [transferArcDirection_start W h0 hp H d]
  exact dartBordersIff_wedge_of_germ (T) _ _ _ r aPos aNeg bPos bNeg c Delta
    hr haPos haNeg hc hDelta ((Pp).initial_nonzero d) hg hq

/-- Helper toward Q-M0-repr; not a paper result. For every positive output
bound, the inverse wedge containment holds uniformly with reciprocal slopes,
scale `1/c`, and strip radius `r * min aPos aNeg`. -/
theorem pastDrawing_wedge_uniform_inverse (d : ℕ × Bool) (Delta : ℝ) (hDelta : 0 < Delta) :
    ∃ r aPos aNeg bPos bNeg c : ℝ,
      0 < r ∧ 0 < aPos ∧ 0 < aNeg ∧ 0 < c ∧
      let rho := pastConeRadius (1 / aNeg) (1 / aPos)
        (-bNeg / aNeg) (-bPos / aPos) (1 / c) (r * min aPos aNeg) Delta
        ((Pt).arc d).initialDirection
      0 < rho ∧ ∀ t eps : ℝ, 0 < t → t < rho → 0 < eps → eps < rho →
        ∃ s eps' : ℝ, 0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
          (T).symm (((Pt).arc d).start + (t : ℂ) *
            (((Pt).arc d).initialDirection + (eps : ℂ) * Complex.I *
              ((Pt).arc d).initialDirection)) =
            ((Pp).arc d).start + (s : ℂ) *
              (((Pp).arc d).initialDirection + (eps' : ℂ) * Complex.I *
                ((Pp).arc d).initialDirection) := by
  obtain ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, hg, hq⟩ :=
    transferArcDirection_coupledGerm W h0 hp H d
  have hreverse := pastCone_uniform_reverse aPos aNeg bPos bNeg c r Delta
    ((Pp).arc d).initialDirection haPos haNeg hc hr hDelta ((Pp).initial_nonzero d)
  have hq' : ((Pt).arc d).initialDirection =
      (c : ℂ) * pastConeV aPos aNeg bPos bNeg ((Pp).arc d).initialDirection := by
    rw [dartBordersIff_coneV_eq_direction aPos aNeg bPos bNeg haPos haNeg _
      ((Pp).initial_nonzero d)]
    exact hq
  have hdir : ((Pp).arc d).initialDirection = ((1 / c : ℝ) : ℂ) *
      pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos)
        ((Pt).arc d).initialDirection := by
    rw [← dartBordersIff_coneV_eq_direction (1 / aNeg) (1 / aPos)
      (-bNeg / aNeg) (-bPos / aPos) (one_div_pos.mpr haNeg) (one_div_pos.mpr haPos)
      _ ((Pt).initial_nonzero d), hq']
    exact hreverse.1.symm
  have hgInv := dartBordersIff_inverse_germ (T) (((Pp).arc d).start)
    r aPos aNeg bPos bNeg hr haPos haNeg hg
  have hresult := dartBordersIff_wedge_of_germ (T).symm
    ((T) (((Pp).arc d).start)) (((Pt).arc d).initialDirection)
    (((Pp).arc d).initialDirection) (r * min aPos aNeg)
    (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) (1 / c) Delta
    (mul_pos hr (lt_min haPos haNeg)) (one_div_pos.mpr haNeg) (one_div_pos.mpr haPos)
    (one_div_pos.mpr hc) hDelta ((Pt).initial_nonzero d)
    (by intro h hh; simpa only [(T).symm_apply_apply] using hgInv h hh) hdir
  refine ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, ?_⟩
  rw [transferArcDirection_start W h0 hp H d]
  simpa only [(T).symm_apply_apply] using hresult

/-- Helper toward Q-M0-repr; not a paper result. Pulling back a uniform
target wedge is equivalent to the source dart bordering its face. -/
theorem pastDrawing_inverseWedge_iff (d : ℕ × Bool) (F : (Pp).Face) :
    (∃ Delta : ℝ, 0 < Delta ∧ ∀ t eps : ℝ,
      0 < t → t < Delta → 0 < eps → eps < Delta →
        (T).symm (((Pt).arc d).start + (t : ℂ) *
          (((Pt).arc d).initialDirection + (eps : ℂ) * Complex.I *
            ((Pt).arc d).initialDirection)) ∈ F.val) ↔ (Pp).dartBorders d F := by
  constructor
  · rintro ⟨Delta, hDelta, hw⟩
    obtain ⟨r, aPos, aNeg, bPos, bNeg, c, _, _, _, _, hrho, hf⟩ :=
      pastDrawing_wedge_uniform_forward W h0 hp H d Delta hDelta
    refine ⟨_, hrho, ?_⟩
    intro t eps ht htr he her
    obtain ⟨s, eps', hs, hsD, he', he'D, hmap⟩ := hf t eps ht htr he her
    have hmem := hw s eps' hs hsD he' he'D
    rw [← hmap, (T).symm_apply_apply] at hmem
    exact hmem
  · rintro ⟨Delta, hDelta, hw⟩
    obtain ⟨r, aPos, aNeg, bPos, bNeg, c, _, _, _, _, hrho, hi⟩ :=
      pastDrawing_wedge_uniform_inverse W h0 hp H d Delta hDelta
    refine ⟨_, hrho, ?_⟩
    intro t eps ht htr he her
    obtain ⟨s, eps', hs, hsD, he', he'D, hmap⟩ := hi t eps ht htr he her
    rw [hmap]
    exact hw s eps' hs hsD he' he'D

/-- Helper toward Q-M0-repr; not a paper result. The transferred component
exists as a face and preserves the dart border predicate exactly. -/
theorem pastDrawing_dartBorders_face_exists (d : ℕ × Bool) (F : (Pp).Face) :
    ∃ Ft : (Pt).Face, Ft.val = (T) '' F.val ∧
      ((Pt).dartBorders d Ft ↔ (Pp).dartBorders d F) := by
  obtain ⟨Ft, hFt, hw⟩ := pastDrawing_dartBorders_inverseWedge W h0 hp H d F
  exact ⟨Ft, hFt, hw.trans (pastDrawing_inverseWedge_iff W h0 hp H d F)⟩

/-- Helper toward Q-M0-repr; not a paper result. Any target face whose
component set is the transferred source face has exactly its dart borders. -/
theorem pastDrawing_dartBorders_iff (d : ℕ × Bool) (F : (Pp).Face)
    (Ft : (Pt).Face) (hFt : Ft.val = (T) '' F.val) :
    (Pt).dartBorders d Ft ↔ (Pp).dartBorders d F := by
  obtain ⟨Ft', hFt', hb⟩ := pastDrawing_dartBorders_face_exists W h0 hp H d F
  have heq : Ft = Ft' := Subtype.ext (hFt.trans hFt'.symm)
  rw [heq]
  exact hb

end DirectedDistances.KMSW.WholePlanePastGlueData
