/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingTransferArcDirection
import Mathlib.Topology.Compactness.Compact

/-! # Coupled germ and direction for the past drawing transfer

Helpers toward the Q-M0-repr face correspondence; not paper results.
The same slopes certify both the local transfer formula and the selected arc direction. -/

public section

namespace DirectedDistances.KMSW.WholePlanePastGlueData

open DirectedDistances.PlanarMap

/-- Helper toward the Q-M0-repr face correspondence; not a paper result.
A closed line segment is compact. -/
private theorem transferCoupledGerm_segment_compact (a b : ℂ) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- Helper toward the Q-M0-repr face correspondence; not a paper result.
A nonzero ray lying locally on a simple polyline is its initial positive ray. -/
private theorem transferCoupledGerm_initial_ray (p : Polyline)
    (hp : p.IsSimple) (hlenP : 2 ≤ p.points.length) (v : ℂ) (hv : v ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (htrace : ∀ t : ℝ, 0 < t → t < r →
      p.start + (t : ℂ) * v ∈ p.image) :
    ∃ c : ℝ, 0 < c ∧ p.initialDirection = (c : ℂ) * v := by
  let n : ℕ := p.points.length - 2
  let K : Set ℂ := ⋃ i : Fin n, p.segmentAt (i.val + 1)
  have hK : IsCompact K := by
    have hfinite : IsCompact
        (⋃ i ∈ (Finset.univ : Finset (Fin n)), p.segmentAt (i.val + 1)) :=
      (Finset.univ : Finset (Fin n)).isCompact_biUnion fun i _ => by
        apply transferCoupledGerm_segment_compact
    simpa [K, n] using hfinite
  have hstart0 : p.start ∈ p.segmentAt 0 := by
    change p.start ∈ segment ℝ (p.point 0) (p.point 1)
    rw [p.point_zero_eq_start]
    exact left_mem_segment ℝ p.start (p.point 1)
  have hstartK : p.start ∉ K := by
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨i, hi⟩
    have hj : i.val + 2 < p.points.length := by
      dsimp [n] at i
      omega
    by_cases hi0 : i.val = 0
    · have hi1 : p.start ∈ p.segmentAt 1 := by simpa [hi0] using hi
      have hmeet := hp.2.1 0 (by dsimp [n] at i; omega)
      have hpoint : p.start ∈ ({p.point 1} : Set ℂ) := by
        rw [← hmeet]
        exact ⟨hstart0, hi1⟩
      have hstartEq : p.start = p.point 1 := by simpa using hpoint
      exact hp.1 0 (by omega : 0 + 1 < p.points.length)
        (p.point_zero_eq_start ▸ hstartEq)
    · have hdisj := hp.2.2 0 (i.val + 1)
        (by omega : 0 + 1 < p.points.length) (by omega : i.val + 2 < p.points.length)
        (by omega : 0 + 1 < i.val + 1)
      exact (Set.disjoint_left.mp hdisj) hstart0 hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hK.isClosed.isOpen_compl.mem_nhds hstartK)
  let u := v
  let t := min (r / 2) (δ / (2 * (‖u‖ + 1)))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (half_pos hr) (div_pos hδ (by positivity))
  have htr : t < r := by
    dsimp [t]
    exact (min_le_left _ _).trans_lt (half_lt_self hr)
  have hprod : t * (2 * (‖u‖ + 1)) ≤ δ := by
    apply (le_div_iff₀ (by positivity)).mp
    dsimp [t]
    exact min_le_right _ _
  have htnorm : t * ‖u‖ < δ := by
    nlinarith [norm_nonneg u]
  let z := p.start + (t : ℂ) * u
  have hzP : z ∈ p.image := htrace t ht htr
  have hzball : z ∈ Metric.ball p.start δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [z, u]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    exact htnorm
  have hznotK : z ∉ K := fun hz => hball hzball hz
  have hzne : z ≠ p.start := by
    intro heq
    have hmul : (t : ℂ) * u = 0 := by
      have := congrArg (fun w : ℂ => w - p.start) heq
      simpa [z] using this
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    exact hv ((mul_eq_zero.mp hmul).resolve_left htC)
  change z = p.start ∨ ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i at hzP
  rcases hzP with heq | ⟨i, hi, hzi⟩
  · exact (hzne heq).elim
  · have hi0 : i = 0 := by
      by_contra hne
      have hi' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hne
      have hzK : z ∈ K := by
        change z ∈ ⋃ j : Fin n, p.segmentAt (j.val + 1)
        refine Set.mem_iUnion.mpr ⟨⟨i - 1, by dsimp [n]; omega⟩, ?_⟩
        change z ∈ p.segmentAt (i - 1 + 1)
        rw [show i - 1 + 1 = i by omega]
        exact hzi
      exact hznotK hzK
    subst i
    have hzi' : z ∈ segment ℝ p.start (p.point 1) := by
      change z ∈ segment ℝ (p.point 0) (p.point 1) at hzi
      simpa only [p.point_zero_eq_start] using hzi
    rw [segment_eq_image'] at hzi'
    obtain ⟨s, hs, hzs⟩ := hzi'
    have hzs' : z = p.start + (s : ℂ) * p.initialDirection := by
      calc
        z = p.start + s • (p.point 1 - p.start) := hzs.symm
        _ = p.start + (s : ℂ) * p.initialDirection := by
          simp [Polyline.initialDirection, Complex.real_smul]
    have hspos : 0 < s := by
      rcases eq_or_lt_of_le hs.1 with heq | hpos
      · have hzEq : z = p.start := by
          rw [hzs', heq.symm]
          simp
        exact (hzne hzEq).elim
      · exact hpos
    have hscale : (t : ℂ) * u = (s : ℂ) * p.initialDirection := by
      apply add_left_cancel
      calc
        p.start + (t : ℂ) * u = z := by simp [z]
        _ = p.start + (s : ℂ) * p.initialDirection := hzs'
    refine ⟨t / s, div_pos ht hspos, ?_⟩
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hspos)
    calc
      p.initialDirection = (s : ℂ)⁻¹ * ((s : ℂ) * p.initialDirection) := by
        field_simp [hsC]
      _ = (s : ℂ)⁻¹ * ((t : ℂ) * u) := by rw [hscale]
      _ = (t / s : ℝ) * v := by
        rw [Complex.ofReal_div]
        dsimp [u]
        field_simp [hsC]

/-- Helper toward the Q-M0-repr face correspondence; not a paper result.
The piecewise linear direction map is homogeneous for positive real scales. -/
private theorem transferCoupledGerm_homogeneous (aPos aNeg bPos bNeg t : ℝ)
    (ht : 0 < t) (u : ℂ) :
    pastDirection aPos aNeg bPos bNeg ((t : ℂ) * u) =
      (t : ℂ) * pastDirection aPos aNeg bPos bNeg u := by
  have hsign : 0 < ((t : ℂ) * u).re ↔ 0 < u.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos_iff_of_pos_left ht
  simp only [pastDirection, hsign]
  split <;> apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] <;> ring

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

/-- Helper toward the Q-M0-repr face correspondence; not a paper result.
One choice of radius and slopes simultaneously certifies the local affine transfer on
an entire vertical strip and the positive proportionality of the selected arc direction. -/
theorem transferArcDirection_coupledGerm (d : ℕ × Bool) :
    ∃ r aPos aNeg bPos bNeg c : ℝ,
      0 < r ∧ 0 < aPos ∧ 0 < aNeg ∧ 0 < c ∧
      (∀ h : ℂ, |h.re| < r →
        (T) (((Pp).arc d).start + h) = (T) (((Pp).arc d).start) +
          pastDirection aPos aNeg bPos bNeg h) ∧
      ((Pt).arc d).initialDirection = (c : ℂ) *
        pastDirection aPos aNeg bPos bNeg ((Pp).arc d).initialDirection := by
  let C := PastDrawingTransfer.cuts (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let hC := PastDrawingTransfer.cuts_inter_Icc_finite (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let hA := PastDrawingTransfer.transfer_affine (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let p := ((Pp).arc d).start
  let u := ((Pp).arc d).initialDirection
  obtain ⟨r, aPos, aNeg, bPos, bNeg, cPos, cNeg, dPos, dNeg,
      hr, haPos, haNeg, hgPos, hgNeg⟩ := Polyline.transfer_germs (T) C hC hA p.re
  let D := pastDirection aPos aNeg bPos bNeg
  have hg : ∀ h : ℂ, |h.re| < r → (T) (p + h) = (T) p + D h := by
    intro h hh
    have hbounds := abs_lt.mp hh
    by_cases hpos : 0 < h.re
    · have he := hgPos (p + h) (by simp only [Complex.add_re]; linarith)
        (by simp only [Complex.add_re]; linarith)
      have he0 := hgPos p le_rfl (by linarith)
      rw [he, he0]
      dsimp [D]
      rw [pastDirection, ite_eq_left hpos]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> ring
    · have he := hgNeg (p + h) (by simp only [Complex.add_re]; linarith)
        (by simp only [Complex.add_re]; linarith)
      have he0 := hgNeg p (by linarith) le_rfl
      rw [he, he0]
      dsimp [D]
      rw [pastDirection, ite_eq_right hpos]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> ring
  have hu : u ≠ 0 := (Pp).initial_nonzero d
  have hDu : D u ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    dsimp [D, pastDirection] at hre him
    by_cases hpos : 0 < u.re
    all_goals
      simp only [hpos, ↓reduceIte] at hre
      simp only [hpos, ↓reduceIte] at him
      apply hu
      apply Complex.ext
      · change u.re = 0
        nlinarith
      · change u.im = 0
        have hur : u.re = 0 := by nlinarith
        simpa only [hur, mul_zero, add_zero, neg_eq_zero] using him
  let e := min 1 (r / (|u.re| + 1))
  have he : 0 < e := lt_min zero_lt_one (div_pos hr (by positivity))
  have htrace : ∀ t : ℝ, 0 < t → t < e →
      ((Pt).arc d).start + (t : ℂ) * D u ∈ ((Pt).arc d).image := by
    intro t ht hte
    have ht1 : t < 1 := hte.trans_le (min_le_left _ _)
    have htr : t * (|u.re| + 1) < r :=
      (lt_div_iff₀ (by positivity)).mp (hte.trans_le (min_le_right _ _))
    have hstrip : |((t : ℂ) * u).re| < r := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, abs_mul, abs_of_pos ht]
      nlinarith only [htr, ht]
    have hzseg : p + (t : ℂ) * u ∈ ((Pp).arc d).segmentAt 0 := by
      change p + (t : ℂ) * u ∈ segment ℝ (((Pp).arc d).point 0)
        (((Pp).arc d).point 1)
      rw [Polyline.point_zero_eq_start]
      have hline : p + (t : ℂ) * u =
          AffineMap.lineMap (((Pp).arc d).start) (((Pp).arc d).point 1) t := by
        rw [AffineMap.lineMap_apply_module']
        dsimp [p, u]
        simp only [Polyline.initialDirection]
        abel
      rw [hline]
      exact lineMap_mem_segment ℝ _ _ ⟨ht.le, ht1.le⟩
    have hzimage : p + (t : ℂ) * u ∈ ((Pp).arc d).image :=
      Polyline.segmentAt_subset_image _ (by have := (Pp).arc_length d; omega) hzseg
    rw [transferArcDirection_arc_image W h0 hp H d,
      transferArcDirection_start W h0 hp H d]
    refine ⟨p + (t : ℂ) * u, hzimage, ?_⟩
    rw [hg _ hstrip]
    change (T) p + D ((t : ℂ) * u) = (T) p + (t : ℂ) * D u
    exact congrArg (fun z : ℂ => (T) p + z)
      (transferCoupledGerm_homogeneous aPos aNeg bPos bNeg t ht u)
  obtain ⟨c, hc, hdir⟩ := transferCoupledGerm_initial_ray ((Pt).arc d)
    ((Pt).arc_simple d) ((Pt).arc_length d) (D u) hDu e he htrace
  exact ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, hg, hdir⟩

end DirectedDistances.KMSW.WholePlanePastGlueData
