/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingDartBordersTransfer
import Mathlib.Topology.Compactness.Compact

public section

namespace DirectedDistances.KMSW.WholePlanePastGlueData

open DirectedDistances.PlanarMap

/-- not a paper result. A compact tail stays away from the first vertex. -/
private theorem transferArcDirection_segment_compact (a b : ℂ) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- not a paper result. A simple trace fixes the positive ray of its first segment. -/
private theorem transferArcDirection_initial_ray (p q : Polyline)
    (hp : p.IsSimple) (hlenP : 2 ≤ p.points.length)
    (hlenQ : 2 ≤ q.points.length) (hstart : p.start = q.start)
    (himage : p.image = q.image) (hqdir : q.initialDirection ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ q.initialDirection = (c : ℂ) * p.initialDirection := by
  let n : ℕ := p.points.length - 2
  let K : Set ℂ := ⋃ i : Fin n, p.segmentAt (i.val + 1)
  have hK : IsCompact K := by
    have hfinite : IsCompact
        (⋃ i ∈ (Finset.univ : Finset (Fin n)), p.segmentAt (i.val + 1)) :=
      (Finset.univ : Finset (Fin n)).isCompact_biUnion fun i _ => by
        apply transferArcDirection_segment_compact
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
  let u := q.initialDirection
  let t := min (1 / 2) (δ / (2 * (‖u‖ + 1)))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hδ (by positivity))
  have ht1 : t < 1 := by
    dsimp [t]
    exact (min_le_left _ _).trans_lt (by norm_num)
  have hprod : t * (2 * (‖u‖ + 1)) ≤ δ := by
    apply (le_div_iff₀ (by positivity)).mp
    dsimp [t]
    exact min_le_right _ _
  have htnorm : t * ‖u‖ < δ := by
    nlinarith [norm_nonneg u]
  let z := p.start + (t : ℂ) * u
  have hzseg : z ∈ q.segmentAt 0 := by
    change z ∈ segment ℝ (q.point 0) (q.point 1)
    rw [q.point_zero_eq_start]
    have hline : z = AffineMap.lineMap q.start (q.point 1) t := by
      rw [AffineMap.lineMap_apply_module']
      dsimp [z, u]
      rw [hstart]
      simp only [Polyline.initialDirection]
      abel
    rw [hline]
    exact lineMap_mem_segment ℝ q.start (q.point 1) ⟨ht.le, ht1.le⟩
  have hzq : z ∈ q.image := Polyline.segmentAt_subset_image q (by omega) hzseg
  have hzP : z ∈ p.image := by rw [himage]; exact hzq
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
    exact hqdir ((mul_eq_zero.mp hmul).resolve_left htC)
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
    have hpdir : p.point 1 - p.point 0 = p.initialDirection := by
      simp only [Polyline.initialDirection, p.point_zero_eq_start]
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
    refine ⟨s / t, div_pos hspos ht, ?_⟩
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    have hfinal : u = (s / t : ℝ) * p.initialDirection := by
      calc
        u = (t : ℂ)⁻¹ * ((t : ℂ) * u) := by field_simp [htC]
        _ = (t : ℂ)⁻¹ * ((s : ℂ) * p.initialDirection) := by rw [hscale]
        _ = (s / t : ℝ) * p.initialDirection := by
          rw [Complex.ofReal_div]
          field_simp [htC]
    simpa only [u] using hfinal

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

/-- not a paper result. The selected target arc starts at the transferred source start. -/
theorem transferArcDirection_start (d : ℕ × Bool) :
    ((Pt).arc d).start = (T) (((Pp).arc d).start) := by
  calc
    ((Pt).arc d).start = (Pt).pos (kmswLimitDartVertex wp d) := (Pt).arc_start d
    _ = (T) ((Pp).pos (kmswLimitDartVertex wp d)) := by
      rw [pastDrawing_pos]
      rfl
    _ = (T) (((Pp).arc d).start) := congrArg (T) ((Pp).arc_start d).symm

/-- not a paper result. The selected target arc has the transferred source arc as its image. -/
theorem transferArcDirection_arc_image (d : ℕ × Bool) :
    ((Pt).arc d).image = (T) '' ((Pp).arc d).image :=
  (pastDrawing_arc W h0 hp H d).1

/-- not a paper result. The two arc images agree in every neighborhood of their common start. -/
theorem transferArcDirection_image_germ (d : ℕ × Bool) (r : ℝ) :
    Metric.ball ((T) (((Pp).arc d).start)) r ∩ ((Pt).arc d).image =
      Metric.ball ((T) (((Pp).arc d).start)) r ∩
        (T) '' ((Pp).arc d).image := by
  rw [transferArcDirection_arc_image W h0 hp H d]

/-- not a paper result. The selected arc direction is the transferred source direction
up to positive scale. -/
theorem transferArcDirection_initialDirection (d : ℕ × Bool) :
    ∃ aPos aNeg bPos bNeg c : ℝ, 0 < aPos ∧ 0 < aNeg ∧ 0 < c ∧
      ((Pt).arc d).initialDirection = (c : ℂ) *
        pastDirection aPos aNeg bPos bNeg ((Pp).arc d).initialDirection := by
  let C := PastDrawingTransfer.cuts (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let hC := PastDrawingTransfer.cuts_inter_Icc_finite (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let hA := PastDrawingTransfer.transfer_affine (shiftedStream W 0) wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)
  let hmono := fun e => PastDrawingTransfer.drawing_arc_monotone wp
    (past_finiteIncidence W H) e
  let q := Polyline.transferArc (T) C hC ((Pp).arc d)
  have hsimple : q.IsSimple := by
    exact Polyline.isSimple_transferArc (T) C hC hA ((Pp).arc d)
      (hmono d) ((Pp).arc_length d)
  have hlen : 2 ≤ q.points.length :=
    Polyline.length_transferArc (T) C hC ((Pp).arc d) (hmono d) ((Pp).arc_length d)
  have hstart : q.start = ((Pt).arc d).start := by
    rw [Polyline.start_transferArc]
    exact (transferArcDirection_start W h0 hp H d).symm
  have himage : q.image = ((Pt).arc d).image := by
    rw [Polyline.image_transferArc (T) C hC hA ((Pp).arc d)
      (hmono d) ((Pp).arc_length d), transferArcDirection_arc_image W h0 hp H d]
  obtain ⟨c₂, hc₂, hselected⟩ := transferArcDirection_initial_ray
    q ((Pt).arc d) hsimple hlen ((Pt).arc_length d) hstart himage
    ((Pt).initial_nonzero d)
  obtain ⟨aPos, aNeg, bPos, bNeg, hPos, hNeg, hstar⟩ :=
    PLDrawing.transferArc_initialDirections (Pp)
      (fun e => PastDrawingTransfer.drawing_arc_monotone wp
        (past_finiteIncidence W H) e) (T) C hC hA
      (kmswLimitDartVertex wp d)
  obtain ⟨c₁, hc₁, _, hexplicit⟩ := hstar d rfl
  refine ⟨aPos, aNeg, bPos, bNeg, c₂ * c₁, hPos, hNeg,
    mul_pos hc₂ hc₁, ?_⟩
  calc
    ((Pt).arc d).initialDirection = (c₂ : ℂ) * q.initialDirection := hselected
    _ = (c₂ * c₁ : ℝ) *
        pastDirection aPos aNeg bPos bNeg ((Pp).arc d).initialDirection := by
      rw [hexplicit, Complex.ofReal_mul]
      ring

end DirectedDistances.KMSW.WholePlanePastGlueData
