/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyCapFaces
import DirectedDistances.PlanarMap.PLDrawingFaceTransfer
import all DirectedDistances.KMSW.StageReversalEdges
import all DirectedDistances.PlanarMap.PLDrawingUniformCones
import all DirectedDistances.KMSW.UIBHBOTAssemblySeamTrace
import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsIff
import all DirectedDistances.KMSW.RunInfDartPartition
import all DirectedDistances.KMSW.MonotoneLimitFaces
import all DirectedDistances.KMSW.PastFaceSucc
import all DirectedDistances.KMSW.BoundaryEnumeration
import all DirectedDistances.KMSW.UIBHBOTWholePlaneWord
import all DirectedDistances.KMSW.UIBHBOTRotationHypothesis
import all DirectedDistances.KMSW.WholePlaneLeftBoundaryTerminal
import DirectedDistances.KMSW.UIBHBOTClosedHalfPlaneDrawing
import DirectedDistances.KMSW.WholePlaneLLRecordEdges
import DirectedDistances.KMSW.WholePlaneRootedMapFields

/-! # Left-face bordering in the UIBHBOT assembly

Helpers toward Definition 5.8 -/

public section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Definition 5.8:
A closed line segment is compact. -/
private theorem assemblyBorder_segment_compact (a b : ℂ) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- Helper toward Definition 5.8:
A nonzero ray lying locally on a simple polyline is its initial positive ray. -/
private theorem assemblyBorder_initial_ray (p : Polyline)
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
        apply assemblyBorder_segment_compact
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


/-- Helper toward Definition 5.8: the first segment contains its small positive ray. -/
private theorem assemblyBorder_initial_mem (p : Polyline) (hlen : 2 ≤ p.points.length)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    p.start + (t : ℂ) * p.initialDirection ∈ p.image := by
  apply Polyline.segmentAt_subset_image p (by omega : 0 + 1 < p.points.length)
  change _ ∈ segment ℝ (p.point 0) (p.point 1)
  rw [p.point_zero_eq_start]
  have heq : p.start + (t : ℂ) * p.initialDirection =
      AffineMap.lineMap p.start (p.point 1) t := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Polyline.initialDirection]
    abel
  rw [heq]
  exact lineMap_mem_segment ℝ _ _ ⟨ht.le, ht1.le⟩

/-- Helper toward Definition 5.8: equal simple traces with the same start
have positively proportional initial directions. -/
private theorem assemblyBorder_direction_of_trace (p q : Polyline)
    (hp : 2 ≤ p.points.length) (hq : 2 ≤ q.points.length) (hsq : q.IsSimple)
    (hstart : q.start = p.start) (htrace : q.image = p.image)
    (hu : p.initialDirection ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ q.initialDirection = (c : ℂ) * p.initialDirection := by
  apply assemblyBorder_initial_ray q hsq hq p.initialDirection hu 1 zero_lt_one
  intro t ht ht1
  rw [hstart, htrace]
  exact assemblyBorder_initial_mem p hp t ht ht1

/-- Helper toward Definition 5.8: positive rescaling of the tangent preserves
the left-wedge predicate. -/
private theorem assemblyBorder_wedge_scale {p u : ℂ} {S : Set ℂ}
    (c : ℝ) (hc : 0 < c) (hw : WedgeIn p u S) :
    WedgeIn p ((c : ℂ) * u) S := by
  obtain ⟨δ, hδ, hw⟩ := hw
  refine ⟨min δ (δ / c), lt_min hδ (div_pos hδ hc), ?_⟩
  intro t eps ht htr he her
  have htc : t * c < δ := by
    exact (lt_div_iff₀ hc).mp (htr.trans_le (min_le_right _ _))
  have hm := hw (t * c) eps (mul_pos ht hc) htc he
    (her.trans_le (min_le_left _ _))
  simp only [wedgePoint] at hm ⊢
  convert hm using 1
  push_cast
  ring

/-- Helper toward Definition 5.8: a common oriented simple trace preserves a
left wedge even when its subdivision changes. -/
private theorem assemblyBorder_wedge_of_trace (p q : Polyline)
    (hp : 2 ≤ p.points.length) (hq : 2 ≤ q.points.length) (hsq : q.IsSimple)
    (hstart : q.start = p.start) (htrace : q.image = p.image)
    (hu : p.initialDirection ≠ 0) {S : Set ℂ}
    (hw : WedgeIn p.start p.initialDirection S) :
    WedgeIn q.start q.initialDirection S := by
  obtain ⟨c, hc, hd⟩ := assemblyBorder_direction_of_trace p q hp hq hsq hstart htrace hu
  rw [hstart, hd]
  exact assemblyBorder_wedge_scale c hc hw

/-- Helper toward Definition 5.8: the affine strip data fixes both the local
plane map and the direction of any simple polyline with its transported trace. -/
private theorem assemblyBorder_coupled_germ (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
    (hcuts : ∀ s t, (cuts ∩ Icc s t).Finite)
    (haff : ∀ s t : ℝ, s < t → (∀ c ∈ cuts, c ∉ Ioo s t) →
      ∃ a b c d : ℝ, 0 < a ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
        T z = ⟨-(a * z.re) + c, -z.im + b * z.re + d⟩)
    (p q : Polyline) (hp : 2 ≤ p.points.length) (hq : 2 ≤ q.points.length)
    (hsq : q.IsSimple) (hu : p.initialDirection ≠ 0)
    (hstart : q.start = T p.start) (htrace : q.image = T '' p.image) :
    ∃ r aPos aNeg bPos bNeg c : ℝ,
      0 < r ∧ 0 < aPos ∧ 0 < aNeg ∧ 0 < c ∧
      (∀ h : ℂ, |h.re| < r → T (p.start + h) = T p.start +
        pastDirection aPos aNeg bPos bNeg h) ∧
      q.initialDirection = (c : ℂ) *
        pastDirection aPos aNeg bPos bNeg p.initialDirection := by
  obtain ⟨r, aPos, aNeg, bPos, bNeg, cPos, cNeg, dPos, dNeg,
      hr, haPos, haNeg, hgPos, hgNeg⟩ := Polyline.transfer_germs T cuts hcuts haff p.start.re
  have hg : ∀ h : ℂ, |h.re| < r → T (p.start + h) = T p.start +
      pastDirection aPos aNeg bPos bNeg h := by
    intro h hh
    have hb := abs_lt.mp hh
    by_cases hpos : 0 < h.re
    · rw [hgPos (p.start + h) (by simp only [Complex.add_re]; linarith)
        (by simp only [Complex.add_re]; linarith),
        hgPos p.start le_rfl (by linarith)]
      simp only [pastDirection, ite_eq_left hpos]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> ring
    · rw [hgNeg (p.start + h) (by simp only [Complex.add_re]; linarith)
        (by simp only [Complex.add_re]; linarith),
        hgNeg p.start (by linarith) le_rfl]
      simp only [pastDirection, ite_eq_right hpos]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> ring
  let u := p.initialDirection
  let e := min 1 (r / (|u.re| + 1))
  have he : 0 < e := lt_min zero_lt_one (div_pos hr (by positivity))
  have hray : ∀ t : ℝ, 0 < t → t < e →
      q.start + (t : ℂ) * pastDirection aPos aNeg bPos bNeg u ∈ q.image := by
    intro t ht hte
    have ht1 : t < 1 := hte.trans_le (min_le_left _ _)
    have htr : t * (|u.re| + 1) < r :=
      (lt_div_iff₀ (by positivity)).mp (hte.trans_le (min_le_right _ _))
    have hstrip : |((t : ℂ) * u).re| < r := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, abs_mul, abs_of_pos ht]
      nlinarith only [htr, ht]
    rw [hstart, htrace]
    refine ⟨p.start + (t : ℂ) * u, assemblyBorder_initial_mem p hp t ht ht1, ?_⟩
    rw [hg _ hstrip, pastDirection_smul_pos _ _ _ _ t ht]
  obtain ⟨c, hc, hd⟩ := assemblyBorder_initial_ray q hsq hq
    (pastDirection aPos aNeg bPos bNeg u) (pastDirection_ne_zero haPos haNeg hu) e he hray
  exact ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, hg, hd⟩

/-- Helper toward Definition 5.8: the inverse of an oriented strip germ has
the reciprocal slopes, on a smaller strip. -/
private theorem assemblyBorder_inverse_germ
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
    by_cases hpos : 0 < h.re
    · have hb : |h.re| < r * aNeg :=
        hh.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le)
      simp only [pastDirection, ite_eq_left hpos]
      rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos haNeg]
      rw [show 1 / aNeg * |h.re| = |h.re| / aNeg by ring]
      exact (div_lt_iff₀ haNeg).mpr hb
    · have hb : |h.re| < r * aPos :=
        hh.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hr.le)
      simp only [pastDirection, ite_eq_right hpos]
      rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos haPos]
      rw [show 1 / aPos * |h.re| = |h.re| / aPos by ring]
      exact (div_lt_iff₀ haPos).mpr hb
  have hright : pastDirection aPos aNeg bPos bNeg
      (pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) h) = h := by
    have hpos : -(-bPos / aPos) / (1 / aPos) = bPos := by field_simp
    have hneg : -(-bNeg / aNeg) / (1 / aNeg) = bNeg := by field_simp
    have hi := pastDirection_inverse (1 / aNeg) (1 / aPos)
      (-bNeg / aNeg) (-bPos / aPos) (one_div_pos.mpr haNeg) (one_div_pos.mpr haPos) h
    simpa only [one_div_one_div, hpos, hneg] using hi
  apply T.injective
  rw [T.apply_symm_apply, hg _ hstrip, hright]

/-- Helper toward Definition 5.8: an oriented strip germ sends a sufficiently
small left wedge into any prescribed left wedge of its image direction. -/
private theorem assemblyBorder_wedge_germ (T : ℂ ≃ₜ ℂ) (p u q : ℂ)
    (r aPos aNeg bPos bNeg c Delta : ℝ)
    (hr : 0 < r) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hc : 0 < c) (hDelta : 0 < Delta) (hu : u ≠ 0)
    (hg : ∀ h : ℂ, |h.re| < r →
      T (p + h) = T p + pastDirection aPos aNeg bPos bNeg h)
    (hq : q = (c : ℂ) * pastDirection aPos aNeg bPos bNeg u) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ t eps : ℝ,
      0 < t → t < rho → 0 < eps → eps < rho →
      ∃ s eps' : ℝ, 0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
        T (p + (t : ℂ) * (u + (eps : ℂ) * Complex.I * u)) =
          T p + (s : ℂ) * (q + (eps' : ℂ) * Complex.I * q) := by
  obtain ⟨hcaps, hw⟩ := pastCone_uniform_forward aPos aNeg bPos bNeg c r Delta u
    haPos haNeg hc hr hDelta hu
  refine ⟨_, hcaps.1, ?_⟩
  intro t eps ht htr he her
  obtain ⟨hstrip, _, _, hs, hsD, he', he'D, hmap⟩ := hw t eps ht htr he her
  refine ⟨_, _, hs, hsD, he', he'D, ?_⟩
  rw [hg _ hstrip, hmap]
  change T p + (↑_ : ℂ) * ((c : ℂ) * pastDirection aPos aNeg bPos bNeg u +
    (↑_ : ℂ) * (Complex.I * ((c : ℂ) * pastDirection aPos aNeg bPos bNeg u))) = _
  rw [← hq]
  simp only [mul_assoc]

/-- Helper toward Definition 5.8: piecewise affine orientation-preserving
seam transport preserves the left side of any simple transported arc. -/
private theorem assemblyBorder_wedge_transfer (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
    (hcuts : ∀ s t, (cuts ∩ Icc s t).Finite)
    (haff : ∀ s t : ℝ, s < t → (∀ c ∈ cuts, c ∉ Ioo s t) →
      ∃ a b c d : ℝ, 0 < a ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
        T z = ⟨-(a * z.re) + c, -z.im + b * z.re + d⟩)
    (p q : Polyline) (hp : 2 ≤ p.points.length) (hq : 2 ≤ q.points.length)
    (hsq : q.IsSimple) (hu : p.initialDirection ≠ 0)
    (hstart : q.start = T p.start) (htrace : q.image = T '' p.image)
    {S : Set ℂ} (hw : WedgeIn p.start p.initialDirection S) :
    WedgeIn q.start q.initialDirection (T '' S) := by
  obtain ⟨r, aPos, aNeg, bPos, bNeg, c, hr, haPos, haNeg, hc, hg, hd⟩ :=
    assemblyBorder_coupled_germ T cuts hcuts haff p q hp hq hsq hu hstart htrace
  obtain ⟨Delta, hDelta, hw⟩ := hw
  have hreverse := pastCone_uniform_reverse aPos aNeg bPos bNeg c r Delta
    p.initialDirection haPos haNeg hc hr hDelta hu
  have hdir : p.initialDirection = ((1 / c : ℝ) : ℂ) *
      pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos)
        q.initialDirection := by
    rw [hd]
    exact hreverse.1.symm
  have hInv := assemblyBorder_inverse_germ T p.start r aPos aNeg bPos bNeg
    hr haPos haNeg hg
  have hqne : q.initialDirection ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (by exact_mod_cast hc.ne') (pastDirection_ne_zero haPos haNeg hu)
  obtain ⟨rho, hrho, hmap⟩ := assemblyBorder_wedge_germ T.symm (T p.start)
    q.initialDirection p.initialDirection (r * min aPos aNeg)
    (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) (1 / c) Delta
    (mul_pos hr (lt_min haPos haNeg)) (one_div_pos.mpr haNeg) (one_div_pos.mpr haPos)
    (one_div_pos.mpr hc) hDelta hqne
    (by intro h hh; simpa only [T.symm_apply_apply] using hInv h hh) hdir
  refine ⟨rho, hrho, ?_⟩
  intro t eps ht htr he her
  obtain ⟨s, eps', hs, hsD, he', he'D, hm⟩ := hmap t eps ht htr he her
  rw [T.symm_apply_apply] at hm
  rw [hstart]
  refine ⟨T.symm (T p.start + (t : ℂ) *
    (q.initialDirection + (eps : ℂ) * Complex.I * q.initialDirection)), ?_,
    T.apply_symm_apply _⟩
  rw [hm]
  exact hw s eps' hs hsD he' he'D

end DirectedDistances.PlanarMap

namespace DirectedDistances.PlanarMap.PLDrawing

/-- Helper toward Definition 5.8: overlapping sufficiently small left wedges
force any two faces bordered by the same dart to coincide. -/
theorem dartBorders_face_unique {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) (d : D) (F F' : G.Face)
    (hF : G.dartBorders d F) (hF' : G.dartBorders d F') : F = F' := by
  obtain ⟨δ₁, hδ₁, hmem₁⟩ := hF
  obtain ⟨δ₂, hδ₂, hmem₂⟩ := hF'
  let t := min δ₁ δ₂ / 2
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht₁ : t < δ₁ := by
    have hmin := min_le_left δ₁ δ₂
    dsimp [t]
    linarith
  have ht₂ : t < δ₂ := by
    have hmin := min_le_right δ₁ δ₂
    dsimp [t]
    linarith
  apply G.faces_eq_of_mem
  · exact hmem₁ t t ht ht₁ ht ht₁
  · exact hmem₂ t t ht ht₂ ht ht₂

/-- Helper toward Definition 5.8: a sufficiently small left wedge avoiding
the trace belongs to one complementary component, so its dart borders a face. -/
theorem dartBorders_exists_of_wedge_compl {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) (d : D)
    (hw : WedgeIn (G.arc d).start (G.arc d).initialDirection G.imageᶜ) :
    ∃ K : G.Face, G.dartBorders d K := by
  obtain ⟨δ, hδ, hw⟩ := hw
  let f : ℝ × ℝ → ℂ := fun p =>
    PlanarMap.wedgePoint (G.arc d).start (G.arc d).initialDirection p.1 p.2
  let S := f '' (Set.Ioo 0 δ ×ˢ Set.Ioo 0 δ)
  have hf : Continuous f := by
    dsimp [f, PlanarMap.wedgePoint]
    fun_prop
  have hconn : IsConnected S :=
    ((isConnected_Ioo hδ).prod (isConnected_Ioo hδ)).image f hf.continuousOn
  have hsub : S ⊆ G.imageᶜ := by
    rintro z ⟨⟨t, eps⟩, ⟨ht, he⟩, rfl⟩
    exact hw t eps ht.1 ht.2 he.1 he.2
  let c := f (δ / 2, δ / 2)
  have hc : c ∈ S := ⟨(δ / 2, δ / 2),
    ⟨⟨half_pos hδ, half_lt_self hδ⟩, ⟨half_pos hδ, half_lt_self hδ⟩⟩, rfl⟩
  let K : G.Face := ⟨connectedComponentIn G.imageᶜ c, c, hsub hc, rfl⟩
  have hSK : S ⊆ K.val :=
    hconn.isPreconnected.subset_connectedComponentIn hc hsub
  refine ⟨K, δ, hδ, ?_⟩
  intro t eps ht htd he hed
  exact hSK ⟨(t, eps), ⟨⟨ht, htd⟩, ⟨he, hed⟩⟩, rfl⟩

end DirectedDistances.PlanarMap.PLDrawing

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap WholePlanePastGlueData Set

/-- Helper toward Definition 5.8: the attaching half-turn carries a left
wedge to a left wedge, with the same positive parameters. -/
private theorem uibhbot_assembly_halfTurn_wedge (p : Polyline) {S : Set ℂ}
    (hw : PlanarMap.WedgeIn p.start p.initialDirection S) :
    PlanarMap.WedgeIn (Polyline.mapPoints uibhbotAssemblyHalfTurn p).start
      (Polyline.mapPoints uibhbotAssemblyHalfTurn p).initialDirection
      (uibhbotAssemblyHalfTurn '' S) := by
  have hd : (Polyline.mapPoints uibhbotAssemblyHalfTurn p).initialDirection =
      -p.initialDirection := by
    simp only [Polyline.initialDirection, Polyline.point_mapPoints,
      Polyline.start_mapPoints, uibhbotAssemblyHalfTurn]
    ring
  obtain ⟨δ, hδ, hw⟩ := hw
  refine ⟨δ, hδ, ?_⟩
  intro t eps ht htδ he heδ
  refine ⟨wedgePoint p.start p.initialDirection t eps, hw t eps ht htδ he heδ, ?_⟩
  simp only [wedgePoint, PlanarMap.wedgePoint, Polyline.start_mapPoints, hd,
    uibhbotAssemblyHalfTurn]
  ring

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "Q0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Qp" => uibhbotPastMonotoneDrawing W hfin
local notation "Tf" => uibhbotGlueFutureTransfer w0 h0 ((And.left H) 0)
local notation "Tp" => uibhbotPastStraightTransfer W hL hR
local notation "A" => uibhbotAssemblyHalfTurn
local notation "C0" => fun j : TriangleCreationTime w0 =>
  Tf '' Subtype.val (capFace w0 ((And.left H) 0) j)
local notation "Cp" => fun j : TriangleCreationTime wp =>
  A '' (Tp '' Subtype.val (capFace wp hfin j))

/-- Helper toward Definition 5.8 (B1): each assembly dart borders at most
one geometric face, with exactly the existing assembly witnesses. -/
theorem uibhbot_assembly_dartBorders_unique (d : WholePlaneDart W)
    (K K' : (G).Face) (hK : (G).dartBorders d K)
    (hK' : (G).dartBorders d K') : K = K' :=
  (G).dartBorders_face_unique d K K' hK hK'

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8 (B2a): a future base dart bordering a
creation cap borders its exact transported cap in the assembly. -/
theorem uibhbot_assembly_future_cap_dartBorders (j : TriangleCreationTime w0)
    (d : ℕ × Bool) (hd : (Q0).dartBorders d (capFace w0 (H.1 0) j)) :
    ∃ K : (G).Face, K.val = C0 j ∧
      (G).dartBorders (wholePlaneDartι W 0 d) K := by
  have haff (s t : ℝ) (hst : s < t)
      (hno : ∀ c ∈ seamCutSet w0 h0 (H.1 0), c ∉ Ioo s t) :
      ∃ a b c e : ℝ, 0 < a ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
        Tf z = ⟨-(a * z.re) + c, -z.im + b * z.re + e⟩ := by
    obtain ⟨m, c, hc⟩ := seamFun_affine_of_noCut w0 h0 (H.1 0) s t hst hno
    refine ⟨1, m, 0, c, zero_lt_one, ?_⟩
    intro z hs ht
    change (⟨-z.re, -z.im + 0 + seamFun w0 h0 (H.1 0) z.re⟩ : ℂ) = _
    rw [hc z.re ⟨hs, ht⟩]
    apply Complex.ext <;> dsimp <;> ring
  have hstart : (F.arc d).start = Tf ((Q0).arc d).start := by
    rw [F.arc_start, (Q0).arc_start, hf]
    rfl
  have hw := assemblyBorder_wedge_transfer Tf (seamCutSet w0 h0 (H.1 0))
    (seamCutSet_inter_Icc_finite w0 h0 (H.1 0)) haff ((Q0).arc d) (F.arc d)
    ((Q0).arc_length d) (F.arc_length d) (F.arc_simple d) ((Q0).initial_nonzero d)
    hstart (hFa d) hd
  obtain ⟨K, hK⟩ := uibhbot_assembly_future_cap_face W H h0 hL hR hfin P hp ha F hf hFim hFa j
  refine ⟨K, hK, ?_⟩
  change PlanarMap.WedgeIn ((G).arc (wholePlaneDartι W 0 d)).start
    ((G).arc (wholePlaneDartι W 0 d)).initialDirection K.val
  rw [uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_future, hK]
  exact hw

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8 (B2a): a past base dart bordering a creation
cap borders its transported cap after attachment, including seam darts. -/
theorem uibhbot_assembly_past_cap_dartBorders (j : TriangleCreationTime wp)
    (d : ℕ × Bool) (hd : (Qp).dartBorders d (capFace wp hfin j)) :
    ∃ K : (G).Face, K.val = Cp j ∧
      (G).dartBorders (kmswPastDart W d) K := by
  have hstartP : (P.arc d).start = Tp ((Qp).arc d).start := by
    rw [P.arc_start, (Qp).arc_start, hp]
    rfl
  have hw := assemblyBorder_wedge_transfer Tp (uibhbotPastSeamCuts W hfin)
    (uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin)
    (uibhbotPastStraightTransfer_affine W hL hR hfin) ((Qp).arc d) (P.arc d)
    ((Qp).arc_length d) (P.arc_length d) (P.arc_simple d) ((Qp).initial_nonzero d)
    hstartP (ha d) hd
  have hwA := uibhbot_assembly_halfTurn_wedge (P.arc d) hw
  have hp' : A ∘ P.pos = uibhbotSeparationPastPos W hL hR hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v → F.pos u = A (P.pos v) := by
    intro u v huv
    change F.pos u = (A ∘ P.pos) v
    rw [hp', hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR hfin u v huv
  have hstart : ((G).arc (kmswPastDart W d)).start =
      (Polyline.mapPoints A (P.arc d)).start := by
    rw [(G).arc_start, pastDart_vertex, uibhbotCcw_assemblyDrawing_pos,
      uibhbotAssemblyPos_past W (A ∘ P.pos) F.pos hc,
      Polyline.start_mapPoints, P.arc_start]
    rfl
  have htrace : ((G).arc (kmswPastDart W d)).image =
      (Polyline.mapPoints A (P.arc d)).image := by
    rw [uibhbot_assembly_past_arc_trace W H h0 hL hR hfin P hp ha F hf hFim hFa,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)]
  have hdir : (Polyline.mapPoints A (P.arc d)).initialDirection ≠ 0 := by
    have heq : (Polyline.mapPoints A (P.arc d)).initialDirection = -(P.arc d).initialDirection := by
      simp only [Polyline.initialDirection, Polyline.point_mapPoints,
        Polyline.start_mapPoints, uibhbotAssemblyHalfTurn]
      ring
    rw [heq]
    exact neg_ne_zero.mpr (P.initial_nonzero d)
  have hwG := assemblyBorder_wedge_of_trace (Polyline.mapPoints A (P.arc d))
    ((G).arc (kmswPastDart W d))
    (by rw [Polyline.length_mapPoints]; exact P.arc_length d)
    ((G).arc_length _) ((G).arc_simple _) hstart htrace hdir hwA
  obtain ⟨K, hK⟩ := uibhbot_assembly_past_cap_face W H h0 hL hR hfin P hp ha F hf hFim hFa j
  refine ⟨K, hK, ?_⟩
  change PlanarMap.WedgeIn ((G).arc (kmswPastDart W d)).start
    ((G).arc (kmswPastDart W d)).initialDirection K.val
  rw [hK]
  exact hwG

include hp ha in
/-- Helper toward Definition 5.8: after the half-turn, the entire past trace
lies to the left of the imaginary axis. -/
theorem uibhbot_assembly_attached_past_re_nonpos :
    A '' P.image ⊆ {z : ℂ | z.re ≤ 0} := by
  rw [(Qp).image_of_transfer Tp P hp ha]
  rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩
  have hx := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hy
  change y.re ≤ 1 at hx
  change -(-y.re) - 1 ≤ 0
  linarith only [hx]

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the complete assembly trace avoids the
open upper-right quadrant, without a past right-hit or root-capture witness. -/
theorem uibhbot_assembly_image_outside_quadrant :
    (G).image ⊆ {z : ℂ | z.re ≤ 0 ∨ z.im ≤ 0} := by
  rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa]
  rintro z (hz | hz)
  · exact Or.inr (hFim hz)
  · exact Or.inl (uibhbot_assembly_attached_past_re_nonpos W hL hR hfin P hp ha hz)

/-- Helper toward Definition 5.8: the open upper-right quadrant is connected. -/
theorem uibhbot_assembly_quadrant_isConnected :
    IsConnected {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2⟩
  have hT : Continuous T := Complex.equivRealProdCLM.symm.continuous
  have heq : T '' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) =
      {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact hxy
    · intro hz
      exact ⟨(z.re, z.im), hz, Complex.ext rfl rfl⟩
  rw [← heq]
  exact (isConnected_Ioi.prod isConnected_Ioi).image T hT.continuousOn

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: exactly one assembly face contains the
open upper-right quadrant. This face is unbounded; identifying its bordering
darts remains a separate obligation. -/
theorem uibhbot_assembly_quadrant_face_existsUnique :
    ∃! U : (G).Face, {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val ∧
      (G).IsUnbounded U := by
  let O : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im}
  let c : ℂ := ⟨1, 1⟩
  have hc : c ∈ O := ⟨zero_lt_one, zero_lt_one⟩
  have hO : O ⊆ (G).imageᶜ := by
    intro z hz hzG
    rcases uibhbot_assembly_image_outside_quadrant W H h0 hL hR hfin
        P hp ha F hf hFim hFa hzG with hx | hy
    · exact (not_le_of_gt hz.1) hx
    · exact (not_le_of_gt hz.2) hy
  let U : (G).Face := ⟨connectedComponentIn (G).imageᶜ c, c, hO hc, rfl⟩
  have hOU : O ⊆ U.val :=
    uibhbot_assembly_quadrant_isConnected.isPreconnected.subset_connectedComponentIn hc hO
  refine ⟨U, ⟨hOU, ?_⟩, ?_⟩
  · intro R
    let z : ℂ := ⟨max R 0 + 1, 1⟩
    have hz : z ∈ O := ⟨by dsimp [z]; positivity, zero_lt_one⟩
    refine ⟨z, hOU hz, ?_⟩
    have hr : R < z.re := by
      dsimp [z]
      linarith only [le_max_left R 0]
    exact hr.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  · intro U' hU'
    exact (G).faces_eq_of_mem (hU'.1 hc) (hOU hc)

include hf hFa in
/-- Helper toward Definition 5.8: the future boundary dart with label `-1`
has its left wedge in the open upper-right quadrant. -/
theorem uibhbot_assembly_future_minus_one_wedge :
    WedgeIn (F.arc (futureMapBoundaryDart w0 h0 (-1))).start
      (F.arc (futureMapBoundaryDart w0 h0 (-1))).initialDirection
      {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
  let d := futureMapBoundaryDart w0 h0 (-1)
  let p := F.arc d
  have hstart : p.start = 0 := by
    rw [F.arc_start, (futureMapBoundaryDart_endpoints w0 h0 (-1)).1, hf,
      uibhbotSeparation_future_boundary_pos]
    apply Complex.ext <;> norm_num
  have hline : ∀ z ∈ p.image, 0 ≤ z.re ∧ z.im = 0 := by
    intro z hz
    rw [hFa d] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨g, hg⟩ := seam_arc_image_graph w0 h0 (H.1 0) (-1)
    have hybounds := hg ▸ hy
    have hyre : y.re ≤ 0 := by
      have h := hybounds.2.1
      rw [uibhbotGlue_seamX_eq_int] at h
      norm_num at h
      exact h
    have hyim := uibhbotAssembly_future_seam_graph w0 h0 (H.1 0) (-1) true hy
    change 0 ≤ -y.re ∧ -y.im + 0 + seamFun w0 h0 (H.1 0) y.re = 0
    exact ⟨neg_nonneg.mpr hyre, by rw [← hyim]; ring⟩
  have hlen : 2 ≤ p.points.length := F.arc_length d
  have hpoint := hline (p.point 1) (Polyline.point_mem_image p (by omega))
  have him : p.initialDirection.im = 0 := by
    rw [Polyline.initialDirection, hstart, sub_zero]
    exact hpoint.2
  have hre : 0 < p.initialDirection.re := by
    have hnonneg : 0 ≤ p.initialDirection.re := by
      simpa only [Polyline.initialDirection, hstart, sub_zero] using hpoint.1
    have hne : p.initialDirection.re ≠ 0 := by
      intro heq
      exact F.initial_nonzero d (Complex.ext heq him)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  refine ⟨1, zero_lt_one, ?_⟩
  intro t eps ht _ he _
  change 0 < (PlanarMap.wedgePoint p.start p.initialDirection t eps).re ∧
    0 < (PlanarMap.wedgePoint p.start p.initialDirection t eps).im
  rw [wedgePoint_re, wedgePoint_im, hstart, Complex.zero_re, Complex.zero_im, him]
  constructor
  · simpa only [mul_zero, sub_zero, zero_add] using mul_pos ht hre
  · simpa only [zero_add] using mul_pos ht (mul_pos he hre)

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: a concrete future boundary dart borders
the unbounded assembly face containing the open upper-right quadrant. -/
theorem uibhbot_assembly_quadrant_face_future_minus_one :
    ∃ U : (G).Face, {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val ∧
      (G).IsUnbounded U ∧
      (G).dartBorders (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 (-1))) U := by
  obtain ⟨U, hU, _⟩ := uibhbot_assembly_quadrant_face_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa
  refine ⟨U, hU.1, hU.2, ?_⟩
  change WedgeIn ((G).arc _).start ((G).arc _).initialDirection U.val
  rw [uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_future]
  obtain ⟨δ, hδ, hw⟩ := uibhbot_assembly_future_minus_one_wedge W H h0 F hf hFa
  exact ⟨δ, hδ, fun t eps ht htr he her => hU.1 (hw t eps ht htr he her)⟩

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the concrete boundary dart bordering the
quadrant face has neither a future nor a past creation-cap representative. -/
theorem uibhbot_assembly_future_minus_one_noncap :
    let d := wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 (-1))
    (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)) ∧
    (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)) := by
  dsimp only
  obtain ⟨U, _, hUnb, hdU⟩ := uibhbot_assembly_quadrant_face_future_minus_one
    W H h0 hL hR hfin P hp ha F hf hFim hFa
  have hnot (K : (G).Face)
      (hdK : (G).dartBorders
        (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 (-1))) K)
      (hK : Bornology.IsBounded K.val) : False := by
    have hKU := (G).dartBorders_face_unique _ K U hdK hdU
    rw [hKU] at hK
    obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : ℂ)
    obtain ⟨z, hz, hnorm⟩ := hUnb R
    have hle : ‖z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
    exact hnorm.not_ge hle
  constructor
  · rintro ⟨e, j, he, hj⟩
    obtain ⟨K, hK, hdK⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    rw [← he] at hdK
    apply hnot K hdK
    rw [hK]
    exact uibhbot_future_transported_cap_bounded W H h0 j
  · rintro ⟨e, j, he, hj⟩
    obtain ⟨K, hK, hdK⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    rw [← he] at hdK
    apply hnot K hdK
    rw [hK]
    exact uibhbot_past_transported_cap_bounded W hL hR hfin j

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: if the letter immediately before zero is
`1`, the designated outer dart instead borders the bounded first past cap.
This records a support obstruction; it does not change the root convention. -/
theorem uibhbot_assembly_outer_bounded_of_previous_up (hstep : W (-1) = 1) :
    ∃ K : (G).Face, (G).dartBorders (uibhbotWholePlaneOuterDart W) K ∧
      Bornology.IsBounded K.val := by
  have hwp : wp 0 = 0 := by
    simp [kmswPastCode, hstep]
  have hw0 : shiftedStream W 1 0 = 1 := by
    simpa only [shiftedStream, Nat.cast_zero, Nat.cast_one, zero_sub] using hstep
  have hb : 2 < (kmswStage wp 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hwp, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hrecord : kmswRevLeftRecord wp 1 2 0 :=
    ⟨by decide, hwp, rfl, rfl⟩
  have hmap : kmswPastStageEdge W 1 2 = 2 := by
    change kmswRevEdge (shiftedStream W 1) wp 1 2 = 2
    rw [kmswRevEdge_left _ _ 1 2 0 hrecord]
    rfl
  have hedge : uibhbotRootEdge W = kmswPastEdge W 2 := by
    rw [kmswPastEdge_eq_stage W 1 2 hb, hmap]
    unfold uibhbotRootEdge
    congr 1
    simp [kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep, hw0,
      kmswStepOfStep, kmswInit, State.addEdge]
  have hdart : uibhbotWholePlaneOuterDart W = kmswPastDart W (2, false) := by
    change (uibhbotRootEdge W, true) = (kmswPastEdge W 2, true)
    rw [hedge]
  let j : TriangleCreationTime wp := ⟨0, Or.inl hwp⟩
  have hj : (Qp).dartBorders (2, false) (capFace wp hfin j) := by
    apply (capFace_spec wp hfin j).2
    simp [stageTriangleDartList, stageTriangleDartTriple, j, hwp, kmswStage, kmswInit]
  obtain ⟨K, hK, hdK⟩ := uibhbot_assembly_past_cap_dartBorders
    W H h0 hL hR hfin P hp ha F hf hFim hFa j (2, false) hj
  refine ⟨K, hdart ▸ hdK, ?_⟩
  rw [hK]
  exact uibhbot_past_transported_cap_bounded W hL hR hfin j

/-- Helper toward Definition 5.8: the previous-up case has zero past
right coordinate at time one, so strict positivity would exclude this case. -/
theorem uibhbot_assembly_previous_up_past_R_one (hstep : W (-1) = 1) :
    R wp 1 = 0 := by
  simp [R, kmswPastCode, hstep, DirectedDistances.RandomWalk.lazyTwoDimensionalStep]

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the precise B2b assertion is incompatible
with a previous up letter. The designated outer dart then borders a bounded
cap, whereas an explicitly exhibited non-cap dart borders an unbounded face. -/
theorem uibhbot_assembly_B2b_not_of_previous_up (hstep : W (-1) = 1) :
    ¬ ∃ U : (G).Face, (G).dartBorders (uibhbotWholePlaneOuterDart W) U ∧
      ∀ d : WholePlaneDart W,
        (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
          d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)) →
        (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
          d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)) →
        (G).dartBorders d U := by
  rintro ⟨U, hrootU, hnoncapU⟩
  obtain ⟨K, hrootK, hKbdd⟩ := uibhbot_assembly_outer_bounded_of_previous_up
    W H h0 hL hR hfin P hp ha F hf hFim hFa hstep
  obtain ⟨V, _, hVunb, hdV⟩ := uibhbot_assembly_quadrant_face_future_minus_one
    W H h0 hL hR hfin P hp ha F hf hFim hFa
  obtain ⟨hfuture, hpast⟩ := uibhbot_assembly_future_minus_one_noncap
    W H h0 hL hR hfin P hp ha F hf hFim hFa
  have hdU := hnoncapU _ hfuture hpast
  have hKU := (G).dartBorders_face_unique _ K U hrootK hrootU
  have hUV := (G).dartBorders_face_unique _ U V hdU hdV
  rw [hKU, hUV] at hKbdd
  obtain ⟨R, hR⟩ := hKbdd.subset_closedBall (0 : ℂ)
  obtain ⟨z, hz, hnorm⟩ := hVunb R
  have hle : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact hnorm.not_ge hle

variable (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

include hRpos in
/-- Helper toward Definition 5.8: strict positivity of the past right coordinate
excludes a previous up letter. The hypothesis `hRpos` is discharged almost surely
by the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_previous_ne_up : W (-1) ≠ 1 := by
  intro hstep
  have hpos := hRpos 1 zero_lt_one
  rw [uibhbot_assembly_previous_up_past_R_one W hstep] at hpos
  exact (lt_irrefl 0) hpos

include hRpos in
/-- Helper toward Definition 5.8: the support condition fixes the letter before
zero to a left step. `hRpos` holds almost surely by the second clause of
`uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_previous_left : W (-1) = 0 := by
  have h := uibhbotCcw_past_first_up W hRpos
  have heq : Equiv.swap (0 : Fin 3) 1 (W (-1)) = 1 := by
    simpa only [kmswPastCode, Nat.cast_zero, sub_zero] using h
  apply (Equiv.swap (0 : Fin 3) 1).injective
  simpa only [Equiv.swap_apply_left] using heq

include hRpos in
/-- Helper toward Definition 5.8: on the strictly positive past support the
designated outer dart is the west dart of the first past missing up-edge.
`hRpos` is discharged almost surely by the second clause of
`uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_outer_eq_past_two :
    uibhbotWholePlaneOuterDart W = kmswPastDart W (2, false) := by
  have hc := uibhbotCcw_past_first_up W hRpos
  have hw0 : shiftedStream W 1 0 = 0 := by
    simpa only [shiftedStream, Nat.cast_zero, Nat.cast_one, zero_sub] using
      uibhbot_assembly_previous_left W hRpos
  have hb : 2 < (kmswStage wp 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hrecord : kmswRevUpRecord wp 1 2 0 := by
    refine ⟨by decide, hc, ?_, rfl⟩
    intro j hj hj1
    have hj' : j = 1 := by omega
    subst j
    simpa only [R, Finset.range_zero, Finset.sum_empty] using hRpos 1 zero_lt_one
  have hmap : kmswPastStageEdge W 1 2 = 2 := by
    change kmswRevEdge (shiftedStream W 1) wp 1 2 = 2
    rw [kmswRevEdge_up _ _ 1 2 0 hrecord]
    rfl
  have hedge : uibhbotRootEdge W = kmswPastEdge W 2 := by
    rw [kmswPastEdge_eq_stage W 1 2 hb, hmap]
    unfold uibhbotRootEdge
    congr 1
    simp [kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep, hw0,
      kmswStepOfStep, kmswInit, State.addEdge]
  change (uibhbotRootEdge W, true) = (kmswPastEdge W 2, true)
  rw [hedge]

include hfin in
/-- Helper toward Definition 5.8: the past straightening height vanishes on
the whole initial root interval. -/
theorem uibhbot_assembly_past_seamHeight_initial (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    uibhbotPastSeamHeight W hL hR x = 0 := by
  have hz : (⟨x, 0⟩ : ℂ) ∈ ((Qp).arc (0, false)).image := by
    rw [uibhbotPastMonotoneDrawing_arc_layout W hfin 0 0 (by change 0 < 1; omega) false]
    have hzero : layoutPos wp 0 0 = 0 := by
      apply Complex.ext <;> norm_num [layoutPos, kmswStageRank, layoutHeight]
    have hone : layoutPos wp 0 1 = 1 := by
      apply Complex.ext <;> norm_num [layoutPos, kmswStageRank, layoutHeight]
    simp only [Bool.false_eq_true, ↓reduceIte, layoutArc, hzero, hone]
    rw [segmentArc_image (by norm_num : (0 : ℂ).re < (1 : ℂ).re)]
    change 0 ≤ x ∧ x ≤ 1 ∧ (0 : ℝ) = segmentHeight 0 1 x
    exact ⟨hx, hx1, by simp [segmentHeight]⟩
  have hs := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin 0 0
    (by simp [kmswStage, kmswInit]) hz
  exact (uibhbotPastSeamHeight_eq_of_mem W hL hR hs).symm

include hR hRpos in
/-- Helper toward Definition 5.8: right of its first new vertex, the entire
past monotone trace has height at most one. The persistent first upper-right
edge supplies the bound, with `hRpos` almost surely supplied by the second
clause of `uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_past_right_height_le_one {z : ℂ}
    (hz : z ∈ (Qp).image) (hx : (1 / 2 : ℝ) ≤ z.re) : z.im ≤ 1 := by
  let w := kmswPastCode W
  let Q := familyQ w (monotone_family_all w)
  let I := familyG w (monotone_family_all w)
  have hc : w 0 = 1 := uibhbotCcw_past_first_up W hRpos
  have halloc : 2 < (kmswStage w 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  have hends : (layoutArc w 1 2).start.re = 1 / 2 ∧
      (layoutArc w 1 2).finish.re = 1 := by
    rw [layoutArc_start w 1 2 halloc, layoutArc_finish w 1 2 halloc]
    norm_num [layoutPos, kmswStageRank, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, kmswInit, State.addEdge]
  have hx1 : z.re ≤ 1 := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hz
  obtain ⟨y, hy, hyr⟩ := polyline_x_image_surjective (layoutArc w 1 2)
    (layoutArc_points_pairwise w 1 2 halloc) (layoutArc_length_two_le w 1 2)
    (hends.1 ▸ hx) (hends.2 ▸ hx1)
  have hyQ : y ∈ (Q 1).image := by
    apply Or.inr
    refine ⟨(⟨2, halloc⟩, false), ?_⟩
    rw [(I 1).arc_layout]
    exact hy
  have hy1 : y.im ≤ 1 := by simpa using (I 1).image_height_le y hyQ
  have hz' : z ∈ ⋃ n, (Q n).image :=
    (monotoneFamilyDrawing_image w hfin (monotone_family_all w)) ▸ hz
  obtain ⟨n, hzn⟩ := mem_iUnion.mp hz'
  let m := max n 1
  have hnm : n ≤ m := le_max_left _ _
  have h1m : 1 ≤ m := le_max_right _ _
  have hznRegion : z ∈ closedGraphRegion (I n).xmin (I n).xmax (I n).lower (I n).upper := by
    rw [← (I n).cover]
    exact Or.inl hzn
  have hzm : z ∈ closedGraphRegion (I m).xmin (I m).xmax (I m).lower (I m).upper :=
    monotone_region_mono_of_le w Q I hnm hznRegion
  have hym : y ∈ graphOver (I m).xmin (I m).xmax (I m).upper := by
    rw [(I m).upper_trace]
    refine mem_iUnion₂.mpr ⟨2, List.mem_append_right _
      (uibhbotCcw_past_two_mem_UR W hRpos m (by omega)), ?_⟩
    have ham := halloc.trans_le (kmswStage_nextEdge_mono w h1m)
    simp only [stageEdgeTrace, dite_eq_left ham, (I m).arc_layout,
      Bool.false_eq_true, ite_false]
    have hstable' (k : ℕ) (hk : 1 ≤ k) : layoutArc w k 2 = layoutArc w 1 2 := by
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [layoutArc_old w k 2 (halloc.trans_le (kmswStage_nextEdge_mono w hk)), ih]
    rwa [hstable' m h1m]
  have hupper : y.im = (I m).upper z.re := by simpa only [hyr] using hym.2.2
  exact hzm.2.2.2.trans (hupper ▸ hy1)

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the open strip right of the first past
vertex and above height one is disjoint from the assembly trace. Here `hRpos`
is discharged almost surely by the second clause of
`uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_upper_right_strip_compl :
    {z : ℂ | -(1 / 2 : ℝ) < z.re ∧ 1 < z.im} ⊆ (G).imageᶜ := by
  intro z hz hzG
  rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
  rcases hzG with hzF | ⟨x, hx, rfl⟩
  · have hb := hFim hzF
    change z.im ≤ 0 at hb
    linarith only [hz.2, hb]
  · rw [(Qp).image_of_transfer Tp P hp ha] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [pastStraightHalfTurn_apply W hL hR] at hz
    change -(1 / 2 : ℝ) < y.re - 1 ∧
      1 < y.im - uibhbotPastSeamHeight W hL hR y.re at hz
    have hx : (1 / 2 : ℝ) ≤ y.re := by
      linarith only [hz.1]
    have hx1 := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hy
    have hb := uibhbot_assembly_past_right_height_le_one W hR hfin hRpos hy hx
    have hs := uibhbot_assembly_past_seamHeight_initial W hL hR hfin y.re
      (by linarith only [hx]) hx1
    rw [hs] at hz
    linarith only [hz.2, hb]

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the whole open strip above the first past
edge belongs to the face containing the quadrant. `hRpos` is almost surely
supplied by the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_upper_right_strip_subset (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) :
    {z : ℂ | -(1 / 2 : ℝ) < z.re ∧ 1 < z.im} ⊆ U.val := by
  let S : Set ℂ := {z | -(1 / 2 : ℝ) < z.re ∧ 1 < z.im}
  let c : ℂ := ⟨1, 2⟩
  have hc : c ∈ S := by constructor <;> norm_num [c]
  have hcU : c ∈ U.val := hU (by constructor <;> norm_num [c])
  have hconn : IsConnected S := by
    let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2⟩
    have heq : T '' (Ioi (-(1 / 2 : ℝ)) ×ˢ Ioi (1 : ℝ)) = S := by
      ext z
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        exact hxy
      · intro hz
        exact ⟨(z.re, z.im), hz, Complex.ext rfl rfl⟩
    rw [← heq]
    exact (isConnected_Ioi.prod isConnected_Ioi).image T
      Complex.equivRealProdCLM.symm.continuous.continuousOn
  have hsub : S ⊆ (G).imageᶜ := uibhbot_assembly_upper_right_strip_compl
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hcomp : S ⊆ connectedComponentIn (G).imageᶜ c :=
    hconn.isPreconnected.subset_connectedComponentIn hc hsub
  obtain ⟨a, ha, heq⟩ := U.property
  have hccomp : c ∈ connectedComponentIn (G).imageᶜ a := heq ▸ hcU
  rw [← connectedComponentIn_eq hccomp] at hcomp
  exact heq ▸ hcomp

include hRpos in
/-- Helper toward Definition 5.8: the first past missing edge has its exact
creation roof, with no change to its subdivision. The positivity input is
almost surely supplied by `uibhbotCodeLawRel_ae_past_R_nonneg`'s second clause. -/
theorem uibhbot_assembly_past_two_roof :
    (Qp).arc (2, false) =
      roofArc (⟨(1 / 2 : ℝ), 1⟩ : ℂ) 1 1 (rampSlope wp 0) := by
  have hc := uibhbotCcw_past_first_up W hRpos
  have he : 2 < (kmswStage wp 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin 1 2 he false]
  norm_num [layoutArc, freshEdges, isFreshLeftMissing, kmswStage, kmswStep,
    kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge,
    layoutPos, kmswStageRank, layoutHeight]
  congr 1

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the designated outer dart borders the face
containing the open first quadrant. The support hypothesis `hRpos` is discharged
almost surely by the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`.
This asserts no uniqueness among all unbounded complementary components. -/
theorem uibhbot_assembly_outer_dartBorders_quadrant (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) :
    (G).dartBorders (uibhbotWholePlaneOuterDart W) U := by
  let p := (Qp).arc (2, false)
  let trans : ℂ → ℂ := fun z => z - 1
  let q := Polyline.mapPoints trans p
  have hpRoof := uibhbot_assembly_past_two_roof W hfin hRpos
  have hc := uibhbotCcw_past_first_up W hRpos
  have he2 : 2 < (kmswStage wp 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  have hpLayout : p = layoutArc wp 1 2 := by
    simpa only [Bool.false_eq_true, ite_false] using
      uibhbotPastMonotoneDrawing_arc_layout W hfin 1 2 he2 false
  have hmono : p.XMonotone := hpLayout ▸ layoutArc_points_pairwise wp 1 2 he2
  have hbounds {y : ℂ} (hy : y ∈ p.image) : (1 / 2 : ℝ) ≤ y.re ∧ y.re ≤ 1 := by
    rw [hpLayout, (layoutArc_image_graph wp 1 2 he2).choose_spec] at hy
    norm_num [layoutPos, kmswStageRank, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, kmswInit, State.addEdge] at hy
    exact ⟨hy.1, hy.2.1⟩
  have hlen : 2 ≤ p.points.length := (Qp).arc_length _
  have hpstart : p.start = (⟨(1 / 2 : ℝ), 1⟩ : ℂ) := by
    rw [show p = _ from hpRoof, roofArc_start]
  have hdirIm : p.initialDirection.im = 0 := by
    have hs := roofArc_initialSlope_top
      (a := (⟨(1 / 2 : ℝ), 1⟩ : ℂ)) (b := (1 : ℂ))
      (M := rampSlope wp 0) (by rfl : (1 : ℝ) = 1)
    have hpos : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos hmono hlen
    have hs' : p.initialDirection.im / p.initialDirection.re = 0 := by
      simpa only [p, hpRoof] using hs
    exact (div_eq_zero_iff.mp hs').resolve_right (ne_of_gt hpos)
  have hdirRe : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos hmono hlen
  have htrans : p.AffineOnSegments trans := by
    intro i hi
    refine ⟨AffineMap.id ℝ ℂ - AffineMap.const ℝ ℂ (1 : ℂ), ?_⟩
    intro z hz
    rfl
  have hqstart : q.start = (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) := by
    rw [Polyline.start_mapPoints, hpstart]
    apply Complex.ext <;> norm_num [trans]
  have hqdir : q.initialDirection = p.initialDirection := by
    simp only [q, Polyline.initialDirection, Polyline.point_mapPoints,
      Polyline.start_mapPoints, trans]
    ring
  have hwq : WedgeIn q.start q.initialDirection
      {z : ℂ | -(1 / 2 : ℝ) < z.re ∧ 1 < z.im} := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro t eps ht _ he _
    change -(1 / 2 : ℝ) < (PlanarMap.wedgePoint q.start q.initialDirection t eps).re ∧
      1 < (PlanarMap.wedgePoint q.start q.initialDirection t eps).im
    rw [wedgePoint_re, wedgePoint_im, hqstart, hqdir, hdirIm]
    constructor <;> dsimp
    · nlinarith only [mul_pos ht hdirRe]
    · nlinarith only [mul_pos ht (mul_pos he hdirRe)]
  have hroot := uibhbot_assembly_outer_eq_past_two W hRpos
  let r := (G).arc (uibhbotWholePlaneOuterDart W)
  have hrEq : r = Polyline.mapPoints A (P.arc (2, false)) := by
    dsimp only [r]
    rw [hroot, uibhbotCcw_assemblyDrawing_arc,
      uibhbotAssemblyArc_past W h0 _ _ (2, false)
        (uibhbotCcw_past_two_not_seam W hR (uibhbotCcw_past_first_up W hRpos))]
  have hrstart : r.start = q.start := by
    rw [hrEq, Polyline.start_mapPoints, P.arc_start, hp]
    have hv : kmswLimitDartVertex wp (2, false) = 2 := by
      have hc := uibhbotCcw_past_first_up W hRpos
      have he : 2 < (kmswStage wp 1).nextEdge := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
      change edgeWest wp 2 = 2
      rw [← (edge_endpoints_eq wp he).1]
      simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
    rw [Function.comp_apply, hv,
      uibhbotCcw_pastStraight_pos_two W hL hR hfin (uibhbotCcw_past_first_up W hRpos), hqstart]
    apply Complex.ext <;> norm_num [uibhbotAssemblyHalfTurn]
  have hrtrace : r.image = q.image := by
    rw [hrEq, Polyline.image_mapPoints A _ (uibhbotAssemblyHalfTurn_affine _),
      ha, Polyline.image_mapPoints trans p htrans]
    ext z
    simp only [mem_image]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      rw [pastStraightHalfTurn_apply W hL hR]
      have hybounds := hbounds hy
      rw [uibhbot_assembly_past_seamHeight_initial W hL hR hfin y.re
        (by linarith only [hybounds.1]) hybounds.2]
      apply Complex.ext <;> simp [trans]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Tp y, ⟨y, hy, rfl⟩, ?_⟩
      rw [pastStraightHalfTurn_apply W hL hR]
      have hyl := hbounds hy
      rw [uibhbot_assembly_past_seamHeight_initial W hL hR hfin y.re
        (by linarith only [hyl.1]) hyl.2]
      apply Complex.ext <;> simp [trans]
  have hw := assemblyBorder_wedge_of_trace q r
    (by rw [Polyline.length_mapPoints]; exact hlen)
    ((G).arc_length _) ((G).arc_simple _) hrstart hrtrace
    (by rw [hqdir]; exact (Qp).initial_nonzero _) hwq
  obtain ⟨δ, hδ, hw⟩ := hw
  refine ⟨δ, hδ, ?_⟩
  intro t eps ht htd he hed
  exact uibhbot_assembly_upper_right_strip_subset
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU (hw t eps ht htd he hed)

include hR hRpos in
/-- Helper toward Definition 5.8: every eastward past lower-seam dart already
borders a creation cap. Strict past positivity (almost surely the second clause
of `uibhbotCodeLawRel_ae_past_R_nonneg`) excludes the initial uncapped case. -/
theorem uibhbot_assembly_past_seam_west_cap (e : ℕ) (hs : kmswPastSeamEdge W e) :
    ∃ j : TriangleCreationTime wp, (Qp).dartBorders (e, false) (capFace wp hfin j) := by
  classical
  obtain ⟨N, hN⟩ := hs
  rcases List.mem_append.mp hN with hLL | hLR
  · obtain ⟨s, hrec⟩ := kmswStage_LL_exists_revLeftRecord wp N e hLL
    obtain ⟨hsN, hc, hm, he⟩ := hrec
    have hnil : (kmswStage wp s).UL.dropLast.reverse = [] := by
      have hl := kmswStage_UL_length wp s
      apply List.length_eq_zero_iff.mp
      simp only [List.length_reverse, List.length_dropLast]
      omega
    let j : TriangleCreationTime wp := ⟨s, Or.inl hc⟩
    refine ⟨j, (capFace_spec wp hfin j).2 _ ?_⟩
    simp [stageTriangleDartList, stageTriangleDartTriple, j, hc, hnil, he]
  · rw [uibhbotPastStage_LR_eq_root W hR N] at hLR
    have he : e = 0 := List.mem_singleton.mp hLR
    subst e
    have hc := uibhbotCcw_past_first_up W hRpos
    let j : TriangleCreationTime wp := ⟨0, Or.inr hc⟩
    refine ⟨j, (capFace_spec wp hfin j).2 _ ?_⟩
    simp [stageTriangleDartList, stageTriangleDartTriple, j, hc, kmswStage, kmswInit]

include hf hFa in
/-- Helper toward Definition 5.8: each negative-label future boundary dart
has its left wedge in the open first quadrant. -/
theorem uibhbot_assembly_future_negative_wedge (k : ℤ) (hk : k ≤ -1) :
    WedgeIn (F.arc (futureMapBoundaryDart w0 h0 k)).start
      (F.arc (futureMapBoundaryDart w0 h0 k)).initialDirection
      {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
  let d := futureMapBoundaryDart w0 h0 k
  let p := F.arc d
  have hstart : p.start = (⟨-((k : ℝ) + 1), 0⟩ : ℂ) := by
    rw [F.arc_start, (futureMapBoundaryDart_endpoints w0 h0 k).1, hf,
      uibhbotSeparation_future_boundary_pos]
    congr 1
    push_cast
    ring
  have hline : ∀ z ∈ p.image, -((k : ℝ) + 1) ≤ z.re ∧ z.im = 0 := by
    intro z hz
    rw [hFa d] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨g, hg⟩ := seam_arc_image_graph w0 h0 (H.1 0) k
    have hb := hg ▸ hy
    have hyre : y.re ≤ (k : ℝ) + 1 := by
      have hh := hb.2.1
      rw [uibhbotGlue_seamX_eq_int] at hh
      exact_mod_cast hh
    have hyim := uibhbotAssembly_future_seam_graph w0 h0 (H.1 0) k true hy
    change -((k : ℝ) + 1) ≤ -y.re ∧ -y.im + 0 + seamFun w0 h0 (H.1 0) y.re = 0
    exact ⟨neg_le_neg hyre, by rw [← hyim]; ring⟩
  have hlen : 2 ≤ p.points.length := F.arc_length d
  have hpoint := hline (p.point 1) (Polyline.point_mem_image p (by omega))
  have him : p.initialDirection.im = 0 := by
    rw [Polyline.initialDirection, hstart, Complex.sub_im]
    exact sub_eq_zero.mpr hpoint.2
  have hre : 0 < p.initialDirection.re := by
    have hnonneg : 0 ≤ p.initialDirection.re := by
      rw [Polyline.initialDirection, Complex.sub_re, hstart]
      exact sub_nonneg.mpr hpoint.1
    have hne : p.initialDirection.re ≠ 0 := by
      intro heq
      exact F.initial_nonzero d (Complex.ext heq him)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hstartRe : 0 ≤ p.start.re := by
    rw [hstart]
    have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    dsimp
    linarith only [hk']
  refine ⟨1, zero_lt_one, ?_⟩
  intro t eps ht _ he _
  change 0 < (PlanarMap.wedgePoint p.start p.initialDirection t eps).re ∧
    0 < (PlanarMap.wedgePoint p.start p.initialDirection t eps).im
  rw [wedgePoint_re, wedgePoint_im, him]
  constructor
  · nlinarith only [hstartRe, mul_pos ht hre]
  · rw [hstart]
    simpa only [zero_add] using mul_pos ht (mul_pos he hre)

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (future part of B2b): every future dart with
neither cap representative borders the quadrant face. `hRpos` is discharged
almost surely by the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_future_noncap_dartBorders (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) (d : ℕ × Bool)
    (hfuture : ¬ ∃ j : TriangleCreationTime w0, (Q0).dartBorders d (capFace w0 (H.1 0) j))
    (hpast : ¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      wholePlaneDartι W 0 d = kmswPastDart W e ∧
        (Qp).dartBorders e (capFace wp hfin j)) :
    (G).dartBorders (wholePlaneDartι W 0 d) U := by
  have ho : (kmswInfFaceSucc w0 (H.1 0)).SameCycle futureMapOuterDart d := by
    rcases dart_outer_or_creation w0 (H.1 0) h0 d with ⟨ho, _⟩ | ⟨⟨j, hj⟩, _⟩
    · exact ho
    · exact (hfuture ⟨j, (capFace_spec w0 (H.1 0) j).2 d hj⟩).elim
  obtain ⟨k, hk, _⟩ := (futureMap_outerOrbit_iff_existsUnique w0 (H.1 0) h0 d).mp ho
  have hkneg : k ≤ -1 := by
    by_contra hkneg
    obtain ⟨e, hs, he⟩ := uibhbotCcw_nonneg_boundary_in_past W h0 hL hR hfin k (by omega)
    obtain ⟨j, hj⟩ := uibhbot_assembly_past_seam_west_cap W hR hfin hRpos e hs
    apply hpast
    refine ⟨(e, false), j, ?_, hj⟩
    rw [hk]
    change (wholePlaneEdgeι W 0 (boundaryOuterEdge w0 h0 k), true) = (kmswPastEdge W e, true)
    rw [he]
  change WedgeIn ((G).arc _).start ((G).arc _).initialDirection U.val
  rw [hk, uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_future]
  obtain ⟨δ, hδ, hw⟩ := uibhbot_assembly_future_negative_wedge W H h0 F hf hFa k hkneg
  exact ⟨δ, hδ, fun t eps ht htd he hed => hU (hw t eps ht htd he hed)⟩

include hL in
/-- Helper toward Definition 5.8: an off-seam past dart with no creation cap
is a west dart on a persistent upper-right boundary edge. Only the left-hit
condition is used; no right-hit or component witness is assumed. -/
theorem uibhbot_assembly_past_noncap_persistent_UR (d : ℕ × Bool)
    (hs : ¬ kmswPastSeamEdge W d.1)
    (hcap : ¬ ∃ j : TriangleCreationTime wp, (Qp).dartBorders d (capFace wp hfin j)) :
    d.2 = false ∧ ∃ N, ∀ n, N ≤ n → d.1 ∈ (kmswStage wp n).UR := by
  have hLu : ∀ a : ℤ, ∃ n, L wp n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hL (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  obtain ⟨M, hM⟩ := kmswRun_UL_eventually_absent wp hLu d.1
  rcases run_outer_or_triangle wp d with ⟨N, hN⟩ | ⟨j, hj, _⟩
  · have hUR (n : ℕ) (hn : max N M ≤ n) :
        d.2 = false ∧ d.1 ∈ (kmswStage wp n).UR := by
      rcases (run_outer_mem_iff wp n d).mp (hN n ((le_max_left _ _).trans hn)) with
        ⟨hb, hu | hu⟩ | ⟨_, hl | hl⟩
      · exact (hM n ((le_max_right _ _).trans hn) hu).elim
      · exact ⟨hb, hu⟩
      · exact (hs ⟨n, List.mem_append_right _ hl⟩).elim
      · exact (hs ⟨n, List.mem_append_left _ hl⟩).elim
    exact ⟨(hUR (max N M) le_rfl).1, max N M, fun n hn => (hUR n hn).2⟩
  · exact (hcap ⟨j, (capFace_spec wp hfin j).2 d hj⟩).elim

include hL in
/-- Helper toward Definition 5.8: the left wedge of an off-seam past non-cap
dart lies outside every finite-stage filled region, simultaneously. This is a
local exterior assertion; identification of its connected component is separate. -/
theorem uibhbot_assembly_past_noncap_wedge_exterior (d : ℕ × Bool)
    (hs : ¬ kmswPastSeamEdge W d.1)
    (hcap : ¬ ∃ j : TriangleCreationTime wp, (Qp).dartBorders d (capFace wp hfin j)) :
    WedgeIn ((Qp).arc d).start ((Qp).arc d).initialDirection
      (monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
        (familyG wp (monotone_family_all wp))) := by
  obtain ⟨hb, N₀, hN₀⟩ :=
    uibhbot_assembly_past_noncap_persistent_UR W hL hfin d hs hcap
  rcases d with ⟨e, b⟩
  dsimp only at hb
  subst b
  let Q := familyQ wp (monotone_family_all wp)
  let I := familyG wp (monotone_family_all wp)
  let N := max N₀ e
  have hN (m : ℕ) (hm : N ≤ m) : e ∈ (kmswStage wp m).UR :=
    hN₀ m ((le_max_left _ _).trans hm)
  have heN : e < (kmswStage wp N).nextEdge :=
    (kmsw_edge_allocated_by_self wp e).trans_le
      (kmswStage_nextEdge_mono wp (le_max_right _ _))
  have harc : (Qp).arc (e, false) = layoutArc wp N e := by
    simpa only [Bool.false_eq_true, ite_false] using
      uibhbotPastMonotoneDrawing_arc_layout W hfin N e heN false
  have hstable (m : ℕ) (hm : N ≤ m) : layoutArc wp m e = layoutArc wp N e := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [layoutArc_old wp m e (heN.trans_le (kmswStage_nextEdge_mono wp hm)), ih]
  let p := layoutArc wp N e
  have hd : 0 < p.initialDirection.re := Polyline.initialDirection_re_pos
    (layoutArc_points_pairwise wp N e heN) (layoutArc_length_two_le wp N e)
  obtain ⟨δ, hδ, hw⟩ := wedge_compl_closedGraphRegion_east_upper_uniform
    p.start p.initialDirection p.initialDirection.re hd hd
  have havoid (m : ℕ) (hm : N ≤ m) (t eps : ℝ)
      (ht : 0 < t) (htd : t < δ) (he : 0 < eps) (hed : eps < δ) :
      PlanarMap.wedgePoint p.start p.initialDirection t eps ∉
        monotoneLimitStageRegion wp Q I m := by
    have hem := heN.trans_le (kmswStage_nextEdge_mono wp hm)
    exact hw (I m).xmin (I m).xmax (I m).lower (I m).upper
      (monotoneLimit_upper_initialLine Q I heN hem
        (List.mem_append_right _ (hN m hm)) (hstable m hm)) t eps ht htd he hed
  rw [harc]
  refine ⟨δ, hδ, ?_⟩
  intro t eps ht htd he hed hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  by_cases hNm : N ≤ m
  · exact havoid m hNm t eps ht htd he hed hm
  · have hNmem : PlanarMap.wedgePoint p.start p.initialDirection t eps ∈
        monotoneLimitStageRegion wp Q I N :=
      monotone_region_mono_of_le wp Q I (Nat.le_of_not_ge hNm) hm
    exact havoid N le_rfl t eps ht htd he hed hNmem

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: there is exactly one face containing the
quadrant, and the designated outer dart borders it. The positivity support is
almost surely the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`.
Uniqueness here concerns faces containing the quadrant, not all unbounded faces. -/
theorem uibhbot_assembly_quadrant_face_outer_existsUnique :
    ∃! U : (G).Face, {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val ∧
      (G).IsUnbounded U ∧ (G).dartBorders (uibhbotWholePlaneOuterDart W) U := by
  obtain ⟨U, hU, huniq⟩ := uibhbot_assembly_quadrant_face_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa
  refine ⟨U, ⟨hU.1, hU.2, ?_⟩, ?_⟩
  · exact uibhbot_assembly_outer_dartBorders_quadrant
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU.1
  · intro V hV
    exact huniq V ⟨hV.1, hV.2.1⟩

include hL in
/-- Helper toward Definition 5.8: an off-seam past non-cap dart is the
eastward whole-plane side of a globally missing geometric edge. This follows
from persistent upper-right membership, not from a face-classification premise. -/
theorem uibhbot_assembly_past_noncap_missing (d : ℕ × Bool)
    (hs : ¬ kmswPastSeamEdge W d.1)
    (hcap : ¬ ∃ j : TriangleCreationTime wp, (Qp).dartBorders d (capFace wp hfin j)) :
    (kmswPastDart W d).2 = true ∧ ¬ wholePlaneEdgePresent W (kmswPastEdge W d.1) := by
  obtain ⟨hb, N, hN⟩ :=
    uibhbot_assembly_past_noncap_persistent_UR W hL hfin d hs hcap
  constructor
  · change !d.2 = true
    rw [hb]
    rfl
  · intro hpresent
    rcases (kmswPastEdge_present_iff_present_or_LL W d.1).mp hpresent with
      ⟨n, hn, hp⟩ | ⟨n, hn, _⟩
    · obtain ⟨_, hpm⟩ := present_mono wp hn hp (max n N) (le_max_left _ _)
      exact kmswStage_UR_LL_not_present wp (max n N) d.1
        (Or.inl (hN (max n N) (le_max_right _ _))) hpm
    · exact hs ⟨n, List.mem_append_left _ hn⟩

/-- Helper toward Definition 5.8: every eastward past arc has a small left
wedge strictly above the past seam. No component identification is assumed. -/
theorem uibhbot_assembly_past_west_wedge_above_seam (e : ℕ) :
    WedgeIn ((Qp).arc (e, false)).start ((Qp).arc (e, false)).initialDirection
      {z : ℂ | uibhbotPastSeamHeight W hL hR z.re < z.im} := by
  let p := (Qp).arc (e, false)
  have he := kmsw_edge_allocated_by_self wp e
  have hpLayout : p = layoutArc wp e e := by
    simpa only [Bool.false_eq_true, ite_false] using
      uibhbotPastMonotoneDrawing_arc_layout W hfin e e he false
  have hlen : 2 ≤ p.points.length := (Qp).arc_length _
  have hmono : p.XMonotone := hpLayout ▸ layoutArc_points_pairwise wp e e he
  have hd := Polyline.initialDirection_re_pos hmono hlen
  let s := p.initialDirection.im / p.initialDirection.re
  let f : ℝ → ℝ := fun x => p.start.im + s * (x - p.start.re)
  let g : ℝ → ℝ := fun x => p.start.im + (s + 1) * (x - p.start.re)
  have hw := wedgeIn_graphRegion_east_lower_slope
    (a := p.start.re) (b := p.start.re + p.initialDirection.re) (f := f) (g := g)
    p.start p.initialDirection p.initialDirection.re (s + 1) hd le_rfl hd le_rfl
    (by intro x hx; rfl) (by dsimp [s]; linarith) (by intro x hx; rfl)
  obtain ⟨δ, hδ, hw⟩ := hw
  refine ⟨δ, hδ, ?_⟩
  intro t eps ht htd heps hepd
  let z := PlanarMap.wedgePoint p.start p.initialDirection t eps
  have hz := hw t eps ht htd heps hepd
  change p.start.re < z.re ∧ z.re < p.start.re + p.initialDirection.re ∧
    f z.re < z.im ∧ z.im < g z.re at hz
  let y : ℂ := ⟨z.re, f z.re⟩
  have hy : y ∈ p.image := by
    apply Or.inr
    refine ⟨0, by omega, ?_⟩
    change y ∈ segment ℝ (p.point 0) (p.point 1)
    rw [p.point_zero_eq_start]
    have hdx : p.initialDirection.re = (p.point 1).re - p.start.re := by
      simp only [Polyline.initialDirection, Complex.sub_re]
    have hdy : p.initialDirection.im = (p.point 1).im - p.start.im := by
      simp only [Polyline.initialDirection, Complex.sub_im]
    rw [mem_segment_iff_height (by linarith only [hd, hdx])]
    refine ⟨hz.1.le, by linarith only [hz.2.1, hdx], ?_⟩
    dsimp [y, f, s, segmentHeight]
    rw [← hdy, ← hdx]
  have hyle : y.re ≤ 1 := uibhbotPastMonotoneDrawing_image_re_le_one
    W hfin hR (Or.inr ⟨(e, false), hy⟩)
  have hseam := uibhbotPastSeamHeight_mem W hL hR y.re
  rw [min_eq_left hyle] at hseam
  have habove := uibhbotPastMonotoneDrawing_above_seam W hfin
    (Or.inr ⟨(e, false), hy⟩) hseam
  exact habove.trans_lt hz.2.2.1

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: an off-seam past non-cap dart has its entire
small left wedge in the assembly trace complement. The remaining B2b obligation
is to join this wedge to the quadrant component, not merely to avoid the trace. -/
theorem uibhbot_assembly_past_noncap_wedge_compl (d : ℕ × Bool)
    (hs : ¬ kmswPastSeamEdge W d.1)
    (hcap : ¬ ∃ j : TriangleCreationTime wp, (Qp).dartBorders d (capFace wp hfin j)) :
    WedgeIn ((G).arc (kmswPastDart W d)).start
      ((G).arc (kmswPastDart W d)).initialDirection (G).imageᶜ := by
  let E := monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
    (familyG wp (monotone_family_all wp))
  let S : Set ℂ := E ∩ {z | uibhbotPastSeamHeight W hL hR z.re < z.im}
  have hE : E ⊆ (Qp).imageᶜ := by
    intro y hy hyQ
    have hy' : y ∈ ⋃ n, (familyQ wp (monotone_family_all wp) n).image :=
      (monotoneFamilyDrawing_image wp hfin (monotone_family_all wp)) ▸ hyQ
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hy'
    apply hy
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change y ∈ closedGraphRegion (familyG wp (monotone_family_all wp) n).xmin
      (familyG wp (monotone_family_all wp) n).xmax
      (familyG wp (monotone_family_all wp) n).lower
      (familyG wp (monotone_family_all wp) n).upper
    rw [← (familyG wp (monotone_family_all wp) n).cover]
    exact Or.inl hyn
  have hb := (uibhbot_assembly_past_noncap_persistent_UR W hL hfin d hs hcap).1
  have hwE := uibhbot_assembly_past_noncap_wedge_exterior W hL hfin d hs hcap
  have hwS : WedgeIn ((Qp).arc d).start ((Qp).arc d).initialDirection S := by
    have hwAbove : WedgeIn ((Qp).arc d).start ((Qp).arc d).initialDirection
        {z : ℂ | uibhbotPastSeamHeight W hL hR z.re < z.im} := by
      have hd : d = (d.1, false) := Prod.ext rfl hb
      rw [hd]
      exact uibhbot_assembly_past_west_wedge_above_seam W hL hR hfin d.1
    obtain ⟨δ, hδ, hwE⟩ := hwE
    obtain ⟨ρ, hρ, hwAbove⟩ := hwAbove
    refine ⟨min δ ρ, lt_min hδ hρ, ?_⟩
    intro t eps ht htd he hed
    exact ⟨hwE t eps ht (htd.trans_le (min_le_left _ _)) he
      (hed.trans_le (min_le_left _ _)),
      hwAbove t eps ht (htd.trans_le (min_le_right _ _)) he
      (hed.trans_le (min_le_right _ _))⟩
  have hstartP : (P.arc d).start = Tp ((Qp).arc d).start := by
    rw [P.arc_start, (Qp).arc_start, hp]
    rfl
  have hwP := assemblyBorder_wedge_transfer Tp (uibhbotPastSeamCuts W hfin)
    (uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin)
    (uibhbotPastStraightTransfer_affine W hL hR hfin) ((Qp).arc d) (P.arc d)
    ((Qp).arc_length d) (P.arc_length d) (P.arc_simple d) ((Qp).initial_nonzero d)
    hstartP (ha d) hwS
  have hwA := uibhbot_assembly_halfTurn_wedge (P.arc d) hwP
  have harc : (G).arc (kmswPastDart W d) = Polyline.mapPoints A (P.arc d) := by
    rw [uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_past W h0 _ _ d hs]
  have hSafe : A '' (Tp '' S) ⊆ (G).imageᶜ := by
    rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩ hzG
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
    rcases hzG with hzF | ⟨x, hx, heq⟩
    · have him := hFim hzF
      rw [pastStraightHalfTurn_apply W hL hR] at him
      change y.im - uibhbotPastSeamHeight W hL hR y.re ≤ 0 at him
      exact (not_le_of_gt (sub_pos.mpr hy.2)) him
    · have hxEq : x = Tp y := uibhbotAssemblyHalfTurn_involutive.injective heq
      rw [hxEq, (Qp).image_of_transfer Tp P hp ha] at hx
      obtain ⟨v, hv, heq⟩ := hx
      have hvEq : v = y := (uibhbotPastStraightTransfer W hL hR).injective heq
      exact hE hy.1 (hvEq ▸ hv)
  rw [harc]
  obtain ⟨δ, hδ, hwA⟩ := hwA
  exact ⟨δ, hδ, fun t eps ht htd he hed => hSafe (hwA t eps ht htd he hed)⟩

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: every assembly dart borders exactly one
geometric face. This establishes existence and uniqueness without classifying
all non-cap darts into the same face. The hypothesis `hRpos` holds almost surely
by the second clause of `uibhbotCodeLawRel_ae_past_R_nonneg`. -/
theorem uibhbot_assembly_dartBorders_existsUnique (d : WholePlaneDart W) :
    ∃! K : (G).Face, (G).dartBorders d K := by
  classical
  suffices hex : ∃ K : (G).Face, (G).dartBorders d K by
    obtain ⟨K, hK⟩ := hex
    exact ⟨K, hK, fun V hV => (G).dartBorders_face_unique d V K hV hK⟩
  by_cases hfCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)
  · obtain ⟨e, j, rfl, hj⟩ := hfCap
    obtain ⟨K, _, hdK⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    exact ⟨K, hdK⟩
  by_cases hpCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)
  · obtain ⟨e, j, rfl, hj⟩ := hpCap
    obtain ⟨K, _, hdK⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    exact ⟨K, hdK⟩
  rcases dart_cover_off_seam W h0 d with ⟨e, rfl⟩ | ⟨e, hs, rfl⟩
  · obtain ⟨U, hU, _⟩ := uibhbot_assembly_quadrant_face_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa
    refine ⟨U, uibhbot_assembly_future_noncap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU.1 e ?_ hpCap⟩
    rintro ⟨j, hj⟩
    exact hfCap ⟨e, j, rfl, hj⟩
  · apply (G).dartBorders_exists_of_wedge_compl
    apply uibhbot_assembly_past_noncap_wedge_compl
      W H h0 hL hR hfin P hp ha F hf hFim hFa e hs
    rintro ⟨j, hj⟩
    exact hpCap ⟨e, j, rfl, hj⟩

/-- Helper toward Definition 5.8: an exterior point above the past seam can
move arbitrarily far upward while staying exterior and above the seam.
This supplies the vertical part of the remaining path construction. -/
theorem uibhbot_assembly_past_exterior_above_seam_up {z p : ℂ}
    (hz : z ∈ monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
      (familyG wp (monotone_family_all wp)))
    (habove : uibhbotPastSeamHeight W hL hR z.re < z.im)
    (hpre : p.re = z.re) (hpim : z.im ≤ p.im) :
    p ∈ monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
      (familyG wp (monotone_family_all wp)) ∧
      uibhbotPastSeamHeight W hL hR p.re < p.im := by
  constructor
  · intro hp
    obtain ⟨n, hpn⟩ := mem_iUnion.mp hp
    let I := familyG wp (monotone_family_all wp) n
    change I.xmin ≤ p.re ∧ p.re ≤ I.xmax ∧ I.lower p.re ≤ p.im ∧ p.im ≤ I.upper p.re at hpn
    have hh := uibhbotPastSeamHeight_eq_lower W hL hR n p.re ⟨hpn.1, hpn.2.1⟩
    have hzn : z ∈ monotoneLimitStageRegion wp (familyQ wp (monotone_family_all wp))
        (familyG wp (monotone_family_all wp)) n := by
      change I.xmin ≤ z.re ∧ z.re ≤ I.xmax ∧ I.lower z.re ≤ z.im ∧ z.im ≤ I.upper z.re
      rw [hpre] at hpn hh
      exact ⟨hpn.1, hpn.2.1, hh ▸ habove.le, hpim.trans hpn.2.2.2⟩
    exact hz (mem_iUnion.mpr ⟨n, hzn⟩)
  · rw [hpre]
    exact habove.trans_le hpim

/-- Helper toward Definition 5.8: the finite suffix starting at a persistent
upper-right edge survives unchanged. -/
theorem assemblyBorder_UR_suffix_persistent (w : ℕ → Fin 3) (N e : ℕ)
    (b : List ℕ) (hN : ∃ a, (kmswStage w N).UR = a ++ e :: b)
    (hkeep : ∀ m, N ≤ m → e ∈ (kmswStage w m).UR) :
    ∀ m, N ≤ m → ∃ a, (kmswStage w m).UR = a ++ e :: b := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hN
  | succ m hm ih =>
    obtain ⟨a, ha⟩ := ih
    generalize hc : w m = c
    fin_cases c
    · refine ⟨a, ?_⟩
      cases hp : (kmswStage w m).UL.dropLast.reverse <;>
        simpa [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hp,
          State.addEdge] using ha
    · refine ⟨((kmswStage w m).nextEdge + 1) :: a, ?_⟩
      simpa [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
        State.addEdge] using congrArg (List.cons ((kmswStage w m).nextEdge + 1)) ha
    · cases a with
      | nil =>
        have hafter := hkeep (m + 1) (by omega)
        have heNot : e ∉ b := by
          have hnd := (kmswStage_status w m).2.2.2.1
          rw [ha] at hnd
          exact (List.nodup_cons.mp hnd).1
        have hafter' : e ∈ b := by
          simpa [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, ha] using hafter
        exact (heNot hafter').elim
      | cons f a =>
        refine ⟨a, ?_⟩
        simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, ha]

/-- Helper toward Definition 5.8: consecutive increasing intervals cover the
interval between the first and last endpoints. -/
private theorem assemblyBorder_chain_cover (l r : ℕ → ℝ) (e : ℕ) (b : List ℕ)
    (hc : (e :: b).IsChain (fun i j => r i = l j))
    (hinc : ∀ i ∈ e :: b, l i < r i) (x : ℝ)
    (hx : l e ≤ x)
    (hxlast : x ≤ r ((e :: b).getLast (by simp))) :
    ∃ i ∈ e :: b, l i ≤ x ∧ x ≤ r i := by
  induction b generalizing e with
  | nil => exact ⟨e, by simp, hx, by simpa using hxlast⟩
  | cons f b ih =>
    by_cases hxe : x ≤ r e
    · exact ⟨e, by simp, hx, hxe⟩
    · have hcf := List.isChain_cons_cons.mp hc
      obtain ⟨i, hi, hil, hir⟩ := ih f hcf.2
        (fun i hi => hinc i (List.mem_cons_of_mem _ hi))
        (by linarith only [hcf.1, not_le.mp hxe]) (by simpa using hxlast)
      exact ⟨i, List.mem_cons_of_mem _ hi, hil, hir⟩

include hR in
/-- Helper toward Definition 5.8: to the right of a persistent upper-right
edge, the whole past trace has a uniform finite height bound. The bound is
proved from the surviving finite suffix, with no additional support premise. -/
theorem uibhbot_assembly_past_persistent_UR_height_le (N e : ℕ)
    (heN : e < (kmswStage wp N).nextEdge)
    (hkeep : ∀ m, N ≤ m → e ∈ (kmswStage wp m).UR)
    {z : ℂ} (hz : z ∈ (Qp).image)
    (hx : (layoutArc wp N e).start.re ≤ z.re) : z.im ≤ N := by
  let Q := familyQ wp (monotone_family_all wp)
  let I := familyG wp (monotone_family_all wp)
  obtain ⟨a, b, hsplit⟩ := List.mem_iff_append.mp (hkeep N le_rfl)
  have hsuf := assemblyBorder_UR_suffix_persistent wp N e b ⟨a, hsplit⟩ hkeep
  have hbnd (i : ℕ) (hi : i ∈ e :: b) : i < (kmswStage wp N).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge wp N).2 i
      (by simp only [List.mem_append]; exact Or.inl (Or.inl
        (Or.inr (hsplit ▸ List.mem_append_right a hi))))
  have hc : (e :: b).IsChain (fun i j =>
      (layoutPos wp N ((kmswStage wp N).east i)).re =
        (layoutPos wp N ((kmswStage wp N).west j)).re) := by
    have hc := (kmswStage_upper_chain wp N).right_of_append
    rw [hsplit] at hc
    exact hc.right_of_append.imp (fun i j hij => congrArg (fun v => (layoutPos wp N v).re) hij)
  have hlast : (layoutPos wp N ((kmswStage wp N).east
      ((e :: b).getLast (by simp)))).re = 1 := by
    have hh := (I N).xmax_eq_upper_end
    simp only [hsplit, ← List.append_assoc] at hh
    simp only [List.getLast_append_of_right_ne_nil
      ((kmswStage wp N).UL ++ a) (e :: b) (by simp)] at hh
    exact hh.symm.trans (uibhbotPastStage_xmax_eq_one W hR N)
  have hxstart : (layoutPos wp N ((kmswStage wp N).west e)).re ≤ z.re := by
    rwa [layoutArc_start wp N e heN] at hx
  obtain ⟨i, hi, hxi, hix⟩ := assemblyBorder_chain_cover
    (fun i => (layoutPos wp N ((kmswStage wp N).west i)).re)
    (fun i => (layoutPos wp N ((kmswStage wp N).east i)).re) e b hc
    (fun i hi => by
      change (kmswStageRank wp N ((kmswStage wp N).west i) : ℝ) <
        (kmswStageRank wp N ((kmswStage wp N).east i) : ℝ)
      exact_mod_cast kmswStageRank_strict wp N i (hbnd i hi)) z.re hxstart
    (hlast ▸ uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hz)
  have hiN := hbnd i hi
  obtain ⟨y, hy, hyr⟩ := polyline_x_image_surjective (layoutArc wp N i)
    (layoutArc_points_pairwise wp N i hiN) (layoutArc_length_two_le wp N i)
    (x := z.re)
    (by rw [layoutArc_start wp N i hiN]; exact hxi)
    (by rw [layoutArc_finish wp N i hiN]; exact hix)
  have hyN : y ∈ (Q N).image := by
    apply Or.inr
    refine ⟨(⟨i, hiN⟩, false), ?_⟩
    rw [(I N).arc_layout]
    exact hy
  have hyheight : y.im ≤ N := (I N).image_height_le y hyN
  have hz' : z ∈ ⋃ n, (Q n).image :=
    (monotoneFamilyDrawing_image wp hfin (monotone_family_all wp)) ▸ hz
  obtain ⟨n, hzn⟩ := mem_iUnion.mp hz'
  let m := max n N
  have hNm : N ≤ m := le_max_right _ _
  have hzm : z ∈ closedGraphRegion (I m).xmin (I m).xmax (I m).lower (I m).upper := by
    apply monotone_region_mono_of_le wp Q I (le_max_left n N)
    rw [← (I n).cover]
    exact Or.inl hzn
  have him : i ∈ (kmswStage wp m).UR := by
    obtain ⟨c, hc⟩ := hsuf m hNm
    rw [hc]
    exact List.mem_append_right _ hi
  have histable : layoutArc wp m i = layoutArc wp N i := by
    have hstable (k : ℕ) (hk : N ≤ k) : layoutArc wp k i = layoutArc wp N i := by
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [layoutArc_old wp k i (hiN.trans_le (kmswStage_nextEdge_mono wp hk)), ih]
    exact hstable m hNm
  have hym : y ∈ graphOver (I m).xmin (I m).xmax (I m).upper := by
    rw [(I m).upper_trace]
    refine mem_iUnion₂.mpr ⟨i, List.mem_append_right _ him, ?_⟩
    have hib := hiN.trans_le (kmswStage_nextEdge_mono wp hNm)
    simp only [stageEdgeTrace, dite_eq_left hib, (I m).arc_layout,
      Bool.false_eq_true, ite_false, histable]
    exact hy
  have heq : y.im = (I m).upper z.re := by simpa only [hyr] using hym.2.2
  exact hzm.2.2.2.trans (heq ▸ hyheight)

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the region above a persistent finite
upper-right suffix belongs to the quadrant face. -/
theorem uibhbot_assembly_past_persistent_UR_strip_subset (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) (N e : ℕ)
    (heN : e < (kmswStage wp N).nextEdge)
    (hkeep : ∀ m, N ≤ m → e ∈ (kmswStage wp m).UR) :
    {z : ℂ | (layoutArc wp N e).start.re - 1 ≤ z.re ∧ (N : ℝ) < z.im} ⊆ U.val := by
  let s := (layoutArc wp N e).start.re - 1
  let S : Set ℂ := {z | s ≤ z.re ∧ (N : ℝ) < z.im}
  let c : ℂ := ⟨max 1 s, (N : ℝ) + 1⟩
  have hc : c ∈ S := ⟨le_max_right _ _, by dsimp [c]; linarith⟩
  have hcU : c ∈ U.val := hU ⟨lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    by dsimp [c]; positivity⟩
  have hconn : IsConnected S := by
    let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2⟩
    have heq : T '' (Ici s ×ˢ Ioi (N : ℝ)) = S := by
      ext z
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        exact hxy
      · intro hz
        exact ⟨(z.re, z.im), hz, Complex.ext rfl rfl⟩
    rw [← heq]
    exact (isConnected_Ici.prod isConnected_Ioi).image T
      Complex.equivRealProdCLM.symm.continuous.continuousOn
  have hsafe : S ⊆ (G).imageᶜ := by
    intro z hz hzG
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
    rcases hzG with hzF | ⟨x, hx, rfl⟩
    · have him := hFim hzF
      exact (not_lt_of_ge (him.trans (Nat.cast_nonneg N))) hz.2
    · rw [(Qp).image_of_transfer Tp P hp ha] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [pastStraightHalfTurn_apply W hL hR] at hz
      have hx : (layoutArc wp N e).start.re ≤ y.re := by
        have hh := hz.1
        change (layoutArc wp N e).start.re - 1 ≤ y.re - 1 at hh
        linarith only [hh]
      have hb := uibhbot_assembly_past_persistent_UR_height_le W hR hfin N e heN hkeep hy hx
      have hs : 0 ≤ uibhbotPastSeamHeight W hL hR y.re :=
        uibhbotPastMonotoneDrawing_image_im_nonneg W hfin
          (uibhbotPastSeamGraph_subset_image W hfin (uibhbotPastSeamHeight_mem W hL hR y.re))
      have hh := hz.2
      change (N : ℝ) < y.im - uibhbotPastSeamHeight W hL hR y.re at hh
      linarith only [hb, hs, hh]
  have hcomp : S ⊆ connectedComponentIn (G).imageᶜ c :=
    hconn.isPreconnected.subset_connectedComponentIn hc hsafe
  obtain ⟨a, ha, heq⟩ := U.property
  have hccomp : c ∈ connectedComponentIn (G).imageᶜ a := heq ▸ hcU
  rw [← connectedComponentIn_eq hccomp] at hcomp
  exact heq ▸ hcomp

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the attached past exterior strictly above
the seam avoids the full assembly trace. -/
theorem uibhbot_assembly_past_exterior_above_seam_compl {z : ℂ}
    (hz : z ∈ monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
      (familyG wp (monotone_family_all wp)))
    (habove : uibhbotPastSeamHeight W hL hR z.re < z.im) :
    A (Tp z) ∈ (G).imageᶜ := by
  intro hzG
  rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
  rcases hzG with hzF | ⟨x, hx, heq⟩
  · have him := hFim hzF
    rw [pastStraightHalfTurn_apply W hL hR] at him
    change z.im - uibhbotPastSeamHeight W hL hR z.re ≤ 0 at him
    exact (not_le_of_gt (sub_pos.mpr habove)) him
  · have hxEq : x = Tp z := uibhbotAssemblyHalfTurn_involutive.injective heq
    rw [hxEq, (Qp).image_of_transfer Tp P hp ha] at hx
    obtain ⟨v, hv, heq⟩ := hx
    have hvEq : v = z := (uibhbotPastStraightTransfer W hL hR).injective heq
    have hzQ : z ∈ (Qp).image := hvEq ▸ hv
    have hz' : z ∈ ⋃ n, (familyQ wp (monotone_family_all wp) n).image :=
      (monotoneFamilyDrawing_image wp hfin (monotone_family_all wp)) ▸ hzQ
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hz'
    apply hz
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change z ∈ closedGraphRegion (familyG wp (monotone_family_all wp) n).xmin
      (familyG wp (monotone_family_all wp) n).xmax
      (familyG wp (monotone_family_all wp) n).lower
      (familyG wp (monotone_family_all wp) n).upper
    rw [← (familyG wp (monotone_family_all wp) n).cover]
    exact Or.inl hzn

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: an exterior point above the seam and to
the right of a persistent edge joins the quadrant face along its upward ray. -/
theorem uibhbot_assembly_past_exterior_above_seam_mem (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) (N e : ℕ)
    (heN : e < (kmswStage wp N).nextEdge)
    (hkeep : ∀ m, N ≤ m → e ∈ (kmswStage wp m).UR)
    {z : ℂ} (hz : z ∈ monotoneLimitExteriorRegion wp (familyQ wp (monotone_family_all wp))
      (familyG wp (monotone_family_all wp)))
    (habove : uibhbotPastSeamHeight W hL hR z.re < z.im)
    (hx : (layoutArc wp N e).start.re ≤ z.re) : A (Tp z) ∈ U.val := by
  let T : ℂ → ℂ := fun p => A (Tp p)
  let B : Set ℂ := {p | p.re = z.re ∧ z.im ≤ p.im}
  let y : ℂ := ⟨z.re, max z.im ((N : ℝ) + uibhbotPastSeamHeight W hL hR z.re + 1)⟩
  have hy : y ∈ B := ⟨rfl, le_max_left _ _⟩
  have hyU : T y ∈ U.val := by
    apply uibhbot_assembly_past_persistent_UR_strip_subset
      W H h0 hL hR hfin P hp ha F hf hFim hFa U hU N e heN hkeep
    dsimp [T]
    rw [pastStraightHalfTurn_apply W hL hR]
    constructor
    · exact sub_le_sub_right hx 1
    · change (N : ℝ) < max z.im ((N : ℝ) + uibhbotPastSeamHeight W hL hR z.re + 1) -
        uibhbotPastSeamHeight W hL hR z.re
      linarith only [le_max_right z.im ((N : ℝ) + uibhbotPastSeamHeight W hL hR z.re + 1)]
  have hB : IsConnected B := by
    let f : ℝ → ℂ := fun t => ⟨z.re, t⟩
    have heq : f '' Ici z.im = B := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨rfl, ht⟩
      · rintro ⟨hre, him⟩
        exact ⟨p.im, him, Complex.ext hre.symm rfl⟩
    rw [← heq]
    exact isConnected_Ici.image f
      (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_const.prodMk continuous_id)).continuousOn
  have hT : Continuous T := by
    change Continuous (fun p : ℂ => -Tp p - 1)
    exact (uibhbotPastStraightTransfer W hL hR).continuous.neg.sub continuous_const
  have hsafe : T '' B ⊆ (G).imageᶜ := by
    rintro p ⟨q, hq, rfl⟩
    obtain ⟨hqE, hqAbove⟩ := uibhbot_assembly_past_exterior_above_seam_up
      W hL hR hz habove hq.1 hq.2
    exact uibhbot_assembly_past_exterior_above_seam_compl
      W H h0 hL hR hfin P hp ha F hf hFim hFa hqE hqAbove
  have hcomp : T '' B ⊆ connectedComponentIn (G).imageᶜ (T y) :=
    (hB.image T hT.continuousOn).isPreconnected.subset_connectedComponentIn
      (mem_image_of_mem T hy) hsafe
  obtain ⟨a, ha, heq⟩ := U.property
  have hycomp : T y ∈ connectedComponentIn (G).imageᶜ a := heq ▸ hyU
  rw [← connectedComponentIn_eq hycomp] at hcomp
  exact heq ▸ hcomp (mem_image_of_mem T ⟨rfl, le_rfl⟩)

/-- Helper toward Definition 5.8: an eastward tangent has a small left
wedge strictly to the right of its base point. -/
private theorem assemblyBorder_east_wedge_re (p v : ℂ) (hv : 0 < v.re) :
    WedgeIn p v {z | p.re ≤ z.re} := by
  let δ := v.re / (|v.im| + 1)
  have hden : 0 < |v.im| + 1 := by positivity
  refine ⟨δ, div_pos hv hden, ?_⟩
  intro t eps ht _ he hed
  have hprod : eps * (|v.im| + 1) < v.re := (lt_div_iff₀ hden).mp hed
  have hsmall : eps * v.im < v.re :=
    (mul_le_mul_of_nonneg_left (by linarith only [le_abs_self v.im]) he.le).trans_lt hprod
  change p.re ≤ (PlanarMap.wedgePoint p v t eps).re
  rw [wedgePoint_re]
  nlinarith only [ht, hsmall]

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8 (past part of B2b): every off-seam past
non-cap dart borders the face containing the open first quadrant. -/
theorem uibhbot_assembly_past_noncap_dartBorders (U : (G).Face)
    (hU : {z : ℂ | 0 < z.re ∧ 0 < z.im} ⊆ U.val) (d : ℕ × Bool)
    (hs : ¬ kmswPastSeamEdge W d.1)
    (hcap : ¬ ∃ j : TriangleCreationTime wp, (Qp).dartBorders d (capFace wp hfin j)) :
    (G).dartBorders (kmswPastDart W d) U := by
  obtain ⟨hb, N₀, hN₀⟩ := uibhbot_assembly_past_noncap_persistent_UR W hL hfin d hs hcap
  let N := max N₀ d.1
  have hkeep : ∀ m, N ≤ m → d.1 ∈ (kmswStage wp m).UR :=
    fun m hm => hN₀ m ((le_max_left _ _).trans hm)
  have heN : d.1 < (kmswStage wp N).nextEdge :=
    (kmsw_edge_allocated_by_self wp d.1).trans_le
      (kmswStage_nextEdge_mono wp (le_max_right _ _))
  have hd : d = (d.1, false) := Prod.ext rfl hb
  have harc : (Qp).arc d = layoutArc wp N d.1 := by
    rw [hd]
    simpa only [Bool.false_eq_true, ite_false] using
      uibhbotPastMonotoneDrawing_arc_layout W hfin N d.1 heN false
  have hdir : 0 < ((Qp).arc d).initialDirection.re := by
    rw [harc]
    exact Polyline.initialDirection_re_pos
      (layoutArc_points_pairwise wp N d.1 heN) (layoutArc_length_two_le wp N d.1)
  let S : Set ℂ := {z | z ∈ monotoneLimitExteriorRegion wp
      (familyQ wp (monotone_family_all wp)) (familyG wp (monotone_family_all wp)) ∧
      uibhbotPastSeamHeight W hL hR z.re < z.im ∧ ((Qp).arc d).start.re ≤ z.re}
  obtain ⟨δ, hδ, hwE⟩ := uibhbot_assembly_past_noncap_wedge_exterior W hL hfin d hs hcap
  have hwAbove : WedgeIn ((Qp).arc d).start ((Qp).arc d).initialDirection
      {z | uibhbotPastSeamHeight W hL hR z.re < z.im} := by
    rw [hd]
    exact uibhbot_assembly_past_west_wedge_above_seam W hL hR hfin d.1
  obtain ⟨ρ, hρ, hwAbove⟩ := hwAbove
  obtain ⟨η, hη, hwRight⟩ := assemblyBorder_east_wedge_re
    ((Qp).arc d).start ((Qp).arc d).initialDirection hdir
  have hwS : WedgeIn ((Qp).arc d).start ((Qp).arc d).initialDirection S := by
    refine ⟨min δ (min ρ η), lt_min hδ (lt_min hρ hη), ?_⟩
    intro t eps ht htd he hed
    have htδ := htd.trans_le (min_le_left δ (min ρ η))
    have heδ := hed.trans_le (min_le_left δ (min ρ η))
    have htρ := htd.trans_le ((min_le_right δ _).trans (min_le_left ρ η))
    have heρ := hed.trans_le ((min_le_right δ _).trans (min_le_left ρ η))
    have htη := htd.trans_le ((min_le_right δ _).trans (min_le_right ρ η))
    have heη := hed.trans_le ((min_le_right δ _).trans (min_le_right ρ η))
    exact ⟨hwE t eps ht htδ he heδ, hwAbove t eps ht htρ he heρ,
      hwRight t eps ht htη he heη⟩
  have hstartP : (P.arc d).start = Tp ((Qp).arc d).start := by
    rw [P.arc_start, (Qp).arc_start, hp]
    rfl
  have hwP := assemblyBorder_wedge_transfer Tp (uibhbotPastSeamCuts W hfin)
    (uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin)
    (uibhbotPastStraightTransfer_affine W hL hR hfin) ((Qp).arc d) (P.arc d)
    ((Qp).arc_length d) (P.arc_length d) (P.arc_simple d) ((Qp).initial_nonzero d)
    hstartP (ha d) hwS
  have hwA := uibhbot_assembly_halfTurn_wedge (P.arc d) hwP
  have hsafe : A '' (Tp '' S) ⊆ U.val := by
    rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    apply uibhbot_assembly_past_exterior_above_seam_mem
      W H h0 hL hR hfin P hp ha F hf hFim hFa U hU N d.1 heN hkeep hy.1 hy.2.1
    simpa only [harc] using hy.2.2
  change WedgeIn ((G).arc _).start ((G).arc _).initialDirection U.val
  rw [uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_past W h0 _ _ d hs]
  obtain ⟨δ, hδ, hwA⟩ := hwA
  exact ⟨δ, hδ, fun t eps ht htd he hed => hsafe (hwA t eps ht htd he hed)⟩

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (B2b): every dart with neither creation-cap
representative borders the face of the designated outer dart. The only extra
support hypothesis is the almost surely discharged `hRpos`. -/
theorem uibhbot_assembly_noncap_dartBorders_outer :
    ∃ U : (G).Face, (G).dartBorders (uibhbotWholePlaneOuterDart W) U ∧
      ∀ d : WholePlaneDart W,
        (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
          d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)) →
        (¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
          d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)) →
        (G).dartBorders d U := by
  obtain ⟨U, hU, _⟩ := uibhbot_assembly_quadrant_face_outer_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨U, hU.2.2, ?_⟩
  intro d hfCap hpCap
  rcases dart_cover_off_seam W h0 d with ⟨e, rfl⟩ | ⟨e, hs, rfl⟩
  · apply uibhbot_assembly_future_noncap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU.1 e
    · rintro ⟨j, hj⟩
      exact hfCap ⟨e, j, rfl, hj⟩
    · exact hpCap
  · apply uibhbot_assembly_past_noncap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa U hU.1 e hs
    rintro ⟨j, hj⟩
    exact hpCap ⟨e, j, rfl, hj⟩

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (B2): every assembly dart borders either
the designated outer face or an exact transported future or past creation cap. -/
theorem uibhbot_assembly_dartBorders_classification :
    ∃ U : (G).Face, (G).dartBorders (uibhbotWholePlaneOuterDart W) U ∧
      ∀ d : WholePlaneDart W,
        (G).dartBorders d U ∨
        (∃ (j : TriangleCreationTime w0) (K : (G).Face),
          K.val = C0 j ∧ (G).dartBorders d K) ∨
        (∃ (j : TriangleCreationTime wp) (K : (G).Face),
          K.val = Cp j ∧ (G).dartBorders d K) := by
  classical
  obtain ⟨U, hroot, hnoncap⟩ := uibhbot_assembly_noncap_dartBorders_outer
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨U, hroot, ?_⟩
  intro d
  by_cases hfCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)
  · obtain ⟨e, j, rfl, hj⟩ := hfCap
    obtain ⟨K, hK, hdK⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    exact Or.inr (Or.inl ⟨j, K, hK, hdK⟩)
  by_cases hpCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)
  · obtain ⟨e, j, rfl, hj⟩ := hpCap
    obtain ⟨K, hK, hdK⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    exact Or.inr (Or.inr ⟨j, K, hK, hdK⟩)
  · exact Or.inl (hnoncap d hfCap hpCap)

/-- Helper toward Definition 5.8: creation-cap bordering is invariant under
the one-sided face successor, without a boundary-hit hypothesis. -/
private theorem assemblyBorder_cap_successor (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j)) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders
      (kmswInfFaceSucc w hfin d) (capFace w hfin j) := by
  have hm := (cap_border_iff w hfin j d).mp hd
  apply (cap_border_iff w hfin j _).mpr
  rw [pastFace_inf_triangle w hfin j d hm]
  exact List.formPerm_apply_mem_of_mem hm

/-- Helper toward Definition 5.8: every creation-cap dart has a predecessor
in the same creation cap. -/
private theorem assemblyBorder_cap_predecessor (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j)) :
    ∃ a, (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders a
      (capFace w hfin j) ∧ kmswInfFaceSucc w hfin a = d := by
  let a := (stageTriangleDartList w j).formPerm.symm d
  have hm : a ∈ stageTriangleDartList w j := by
    apply List.mem_of_formPerm_apply_mem
    rw [Equiv.apply_symm_apply]
    exact (cap_border_iff w hfin j d).mp hd
  refine ⟨a, (cap_border_iff w hfin j a).mpr hm, ?_⟩
  rw [pastFace_inf_triangle w hfin j a hm]
  exact (stageTriangleDartList w j).formPerm.apply_symm_apply d

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (B3): every assembly dart borders a face. -/
theorem uibhbot_assembly_dartBorders_exists (d : WholePlaneDart W) :
    ∃ K : (G).Face, (G).dartBorders d K :=
  (uibhbot_assembly_dartBorders_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d).exists

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (B4): whole-plane face succession preserves
the actual geometric face bordered by an assembly dart. -/
theorem uibhbot_assembly_faceSucc_dartBorders (d : WholePlaneDart W) (K : (G).Face)
    (hdK : (G).dartBorders d K) :
    (G).dartBorders (wholePlaneFaceSucc W H d) K := by
  classical
  by_cases hfCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)
  · obtain ⟨e, j, rfl, hj⟩ := hfCap
    have hjs := assemblyBorder_cap_successor w0 (H.1 0) j e hj
    obtain ⟨K₀, hK₀, heK₀⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    obtain ⟨K₁, hK₁, heK₁⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j _ hjs
    have hKK₀ := (G).dartBorders_face_unique _ K K₀ hdK heK₀
    have hK₀K₁ : K₀ = K₁ := Subtype.ext (hK₀.trans hK₁.symm)
    rw [wholePlaneFaceSucc_run_of_triangle W H 0 e
      ⟨j, (cap_border_iff w0 (H.1 0) j e).mp hj⟩, hKK₀, hK₀K₁]
    exact heK₁
  by_cases hpCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)
  · obtain ⟨e, j, rfl, hj⟩ := hpCap
    have hjs := assemblyBorder_cap_successor wp hfin j e hj
    obtain ⟨K₀, hK₀, heK₀⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    obtain ⟨K₁, hK₁, heK₁⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j _ hjs
    have hKK₀ := (G).dartBorders_face_unique _ K K₀ hdK heK₀
    have hK₀K₁ : K₀ = K₁ := Subtype.ext (hK₀.trans hK₁.symm)
    rw [kmswPastDart_faceSucc_of_triangle W H hfin e
      ⟨j, (cap_border_iff wp hfin j e).mp hj⟩, hKK₀, hK₀K₁]
    exact heK₁
  obtain ⟨U, _, hnoncap⟩ := uibhbot_assembly_noncap_dartBorders_outer
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hKU := (G).dartBorders_face_unique d K U hdK (hnoncap d hfCap hpCap)
  rw [hKU]
  apply hnoncap
  · rintro ⟨e, j, he, hj⟩
    obtain ⟨a, ha, hsa⟩ := assemblyBorder_cap_predecessor w0 (H.1 0) j e hj
    have hcomm := wholePlaneFaceSucc_run_of_triangle W H 0 a
      ⟨j, (cap_border_iff w0 (H.1 0) j a).mp ha⟩
    rw [hsa] at hcomm
    have hde : d = wholePlaneDartι W 0 a :=
      (wholePlaneFaceSucc W H).injective (he.trans hcomm.symm)
    exact hfCap ⟨a, j, hde, ha⟩
  · rintro ⟨e, j, he, hj⟩
    obtain ⟨a, ha, hsa⟩ := assemblyBorder_cap_predecessor wp hfin j e hj
    have hcomm := kmswPastDart_faceSucc_of_triangle W H hfin a
      ⟨j, (cap_border_iff wp hfin j a).mp ha⟩
    rw [hsa] at hcomm
    have hde : d = kmswPastDart W a :=
      (wholePlaneFaceSucc W H).injective (he.trans hcomm.symm)
    exact hpCap ⟨a, j, hde, ha⟩

include hR in
/-- Helper toward Definition 5.8: every negatively labelled future boundary
edge remains globally missing. Nonnegative past right coordinates discharge
the earlier-window strict-record condition. -/
theorem uibhbot_assembly_future_negative_missing (k : ℤ) (hk : k ≤ -1) :
    ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W 0 (boundaryOuterEdge w0 h0 k)) := by
  let n := boundaryHitTime w0 h0 k
  have hnlevel : L w0 n = k := boundaryHitTime_left_spec w0 h0 hk
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hnlevel
    simp only [L, Finset.range_zero, Finset.sum_empty] at hnlevel
    omega
  have hrecord (M : ℕ) : ∀ j < M + n,
      L (shiftedStream W M) (M + n) < L (shiftedStream W M) j := by
    intro j hj
    have hshift : (fun i => shiftedStream W M (M + i)) = w0 := by
      simpa only [Nat.sub_zero] using shiftedStream_shift W 0 M (Nat.zero_le M)
    have hLn : L (shiftedStream W M) (M + n) = L (shiftedStream W M) M + k := by
      rw [terminal_L_shift_add, hshift, hnlevel]
    by_cases hjM : j < M
    · have hi := window_integral_fst W M j
      have hc := (kmswPastCode_coordinates W (M - j)).2
      have hidx : -((M - j : ℕ) : ℤ) = (j : ℤ) - M := by omega
      rw [hidx] at hc
      have hpos := hR (M - j)
      rw [hc] at hpos
      linarith only [hi, hpos, hLn, hk]
    · have hjEq : j = M + (j - M) := by omega
      have hLj : L (shiftedStream W M) j = L (shiftedStream W M) M + L w0 (j - M) := by
        conv_lhs => rw [hjEq, terminal_L_shift_add]
        rw [hshift]
      have hstrict := boundaryHitTime_strict_left w0 h0 hk (j - M) (by omega)
      linarith only [hLn, hLj, hstrict]
  rw [boundaryOuterEdge_of_negative w0 h0 hk]
  intro hpresent
  obtain ⟨M, _, hM⟩ := (wholePlaneEdgePresent_ι W 0 _).mp hpresent
  have hp := hM M le_rfl
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hr : ∀ j < M + (m + 1),
      L (shiftedStream W M) (M + (m + 1)) < L (shiftedStream W M) j := by
    simpa only [hm] using hrecord M
  have hmap := windowMap_LL_created (shiftedStream W M) M m hr
  have hshift : (fun i => shiftedStream W M (M + i)) = w0 := by
    simpa only [Nat.sub_zero] using shiftedStream_shift W 0 M (Nat.zero_le M)
  rw [hshift] at hmap
  change EdgePresent (shiftedStream W M)
    (kmswWindowEdgeMapInf (shiftedStream W M) M (kmswLLCreatedEdge w0 n)) at hp
  rw [hm, hmap] at hp
  exact kmswLLCreatedEdge_not_present_of_record _ _ (by omega) hr hp

include h0 hL hR hRpos in
/-- Helper toward Definition 5.8: a dart without either cap representative
is the east side of a globally missing edge. -/
theorem uibhbot_assembly_noncap_missing (d : WholePlaneDart W)
    (hfCap : ¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j))
    (hpCap : ¬ ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)) :
    d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1 := by
  rcases dart_cover_off_seam W h0 d with ⟨e, rfl⟩ | ⟨e, hs, rfl⟩
  · have ho : (kmswInfFaceSucc w0 (H.1 0)).SameCycle futureMapOuterDart e := by
      rcases dart_outer_or_creation w0 (H.1 0) h0 e with ⟨ho, _⟩ | ⟨⟨j, hj⟩, _⟩
      · exact ho
      · exact (hfCap ⟨e, j, rfl, (capFace_spec w0 (H.1 0) j).2 e hj⟩).elim
    obtain ⟨k, hk, _⟩ := (futureMap_outerOrbit_iff_existsUnique w0 (H.1 0) h0 e).mp ho
    have hkneg : k ≤ -1 := by
      by_contra hkn
      obtain ⟨a, ha, he⟩ := uibhbotCcw_nonneg_boundary_in_past W h0 hL hR hfin k (by omega)
      obtain ⟨j, hj⟩ := uibhbot_assembly_past_seam_west_cap W hR hfin hRpos a ha
      apply hpCap
      refine ⟨(a, false), j, ?_, hj⟩
      rw [hk]
      change (wholePlaneEdgeι W 0 (boundaryOuterEdge w0 h0 k), true) = (kmswPastEdge W a, true)
      rw [he]
    rw [hk]
    exact ⟨rfl, uibhbot_assembly_future_negative_missing W h0 hR k hkneg⟩
  · apply uibhbot_assembly_past_noncap_missing W hL hfin e hs
    rintro ⟨j, hj⟩
    exact hpCap ⟨e, j, rfl, hj⟩

/-- Helper toward Definition 5.8: transporting a creation cap's successor
rule puts all its bordered darts in one target permutation orbit. -/
private theorem assemblyBorder_map_cap_sameCycle {D : Type*}
    (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) (j : TriangleCreationTime w)
    (f : Equiv.Perm D) (ι : (ℕ × Bool) → D)
    (hcomm : ∀ a, a ∈ stageTriangleDartList w j →
      f (ι a) = ι (kmswInfFaceSucc w hfin a)) (d e : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d (capFace w hfin j))
    (he : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders e (capFace w hfin j)) :
    f.SameCycle (ι d) (ι e) := by
  let t := stageTriangleDartTriple w j
  obtain ⟨h1, h2, _, _, _, _⟩ := capFace_triangle_darts_sameCycle w hfin j
  have hs1 : f (ι t.1) = ι t.2.1 :=
    (hcomm t.1 (by simp [t, stageTriangleDartList])).trans (congrArg ι h1)
  have hs2 : f (ι t.2.1) = ι t.2.2 :=
    (hcomm t.2.1 (by simp [t, stageTriangleDartList])).trans (congrArg ι h2)
  have hc1 : f.SameCycle (ι t.1) (ι t.2.1) := by
    rw [← hs1]
    exact Equiv.Perm.SameCycle.rfl.apply_right
  have hc2 : f.SameCycle (ι t.1) (ι t.2.2) := by
    rw [← hs2]
    exact hc1.apply_right
  have hall (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList w j) :
      f.SameCycle (ι t.1) (ι a) := by
    change a ∈ [t.1, t.2.1, t.2.2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact hc1
    · exact hc2
  exact (hall d ((cap_border_iff w hfin j d).mp hd)).symm.trans
    (hall e ((cap_border_iff w hfin j e).mp he))

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: a bordered face is unbounded with a
missing east dart, or has the exact source cap representative of that dart. -/
theorem uibhbot_assembly_bordered_face_cases (d : WholePlaneDart W) (K : (G).Face)
    (hd : (G).dartBorders d K) :
    ((G).IsUnbounded K ∧ d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1) ∨
    (∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j) ∧ K.val = C0 j) ∨
    (∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j) ∧ K.val = Cp j) := by
  classical
  by_cases hfCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime w0),
      d = wholePlaneDartι W 0 e ∧ (Q0).dartBorders e (capFace w0 (H.1 0) j)
  · obtain ⟨e, j, rfl, hj⟩ := hfCap
    obtain ⟨K', hK', heK'⟩ := uibhbot_assembly_future_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    have hKK' := (G).dartBorders_face_unique _ K K' hd heK'
    exact Or.inr (Or.inl ⟨e, j, rfl, hj, hKK' ▸ hK'⟩)
  by_cases hpCap : ∃ (e : ℕ × Bool) (j : TriangleCreationTime wp),
      d = kmswPastDart W e ∧ (Qp).dartBorders e (capFace wp hfin j)
  · obtain ⟨e, j, rfl, hj⟩ := hpCap
    obtain ⟨K', hK', heK'⟩ := uibhbot_assembly_past_cap_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa j e hj
    have hKK' := (G).dartBorders_face_unique _ K K' hd heK'
    exact Or.inr (Or.inr ⟨e, j, rfl, hj, hKK' ▸ hK'⟩)
  obtain ⟨U, hU, _⟩ := uibhbot_assembly_quadrant_face_outer_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hdU : (G).dartBorders d U := by
    rcases dart_cover_off_seam W h0 d with ⟨e, rfl⟩ | ⟨e, hs, rfl⟩
    · apply uibhbot_assembly_future_noncap_dartBorders
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU.1 e
      · rintro ⟨j, hj⟩
        exact hfCap ⟨e, j, rfl, hj⟩
      · exact hpCap
    · apply uibhbot_assembly_past_noncap_dartBorders
        W H h0 hL hR hfin P hp ha F hf hFim hFa U hU.1 e hs
      rintro ⟨j, hj⟩
      exact hpCap ⟨e, j, rfl, hj⟩
  have hKU := (G).dartBorders_face_unique d K U hd hdU
  exact Or.inl ⟨hKU ▸ hU.2.1,
    uibhbot_assembly_noncap_missing W H h0 hL hR hfin hRpos d hfCap hpCap⟩

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8 (B5): two darts bordering the same
geometric assembly face lie in the same whole-plane face-successor orbit. -/
theorem uibhbot_assembly_common_face_sameCycle (d e : WholePlaneDart W)
    (hcommon : ∃ K : (G).Face, (G).dartBorders d K ∧ (G).dartBorders e K) :
    (wholePlaneFaceSucc W H).SameCycle d e := by
  obtain ⟨K, hd, he⟩ := hcommon
  have hfuture (j : TriangleCreationTime w0) (hv : K.val = C0 j) :
      Bornology.IsBounded K.val := hv ▸ uibhbot_future_transported_cap_bounded W H h0 j
  have hpast (j : TriangleCreationTime wp) (hv : K.val = Cp j) :
      Bornology.IsBounded K.val := hv ▸ uibhbot_past_transported_cap_bounded W hL hR hfin j
  have hnotunbounded (hb : Bornology.IsBounded K.val) : ¬ (G).IsUnbounded K := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    intro hu
    obtain ⟨z, hz, hnorm⟩ := hu R
    have hzR := hR hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzR
    exact (not_le_of_gt hnorm) hzR
  have hcross (j : TriangleCreationTime w0) (j' : TriangleCreationTime wp)
      (hv : K.val = C0 j) (hv' : K.val = Cp j') : False := by
    obtain ⟨z, hz, heq⟩ := K.property
    have hzK : z ∈ K.val := heq ▸ mem_connectedComponentIn hz
    have hneg := uibhbot_future_transported_cap_im_neg W H h0 j (hv ▸ hzK)
    have hpos := uibhbot_past_transported_cap_im_pos W hL hR hfin j' (hv' ▸ hzK)
    change z.im < 0 at hneg
    change 0 < z.im at hpos
    exact (not_lt_of_gt hneg) hpos
  rcases uibhbot_assembly_bordered_face_cases
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K hd with
    hdM | ⟨a, j, rfl, haCap, hva⟩ | ⟨a, j, rfl, haCap, hva⟩
  · rcases uibhbot_assembly_bordered_face_cases
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e K he with
      heM | ⟨b, j', rfl, hb, hvb⟩ | ⟨b, j', rfl, hb, hvb⟩
    · have hdEq : d = (d.1, true) := Prod.ext rfl hdM.2.1
      have heEq : e = (e.1, true) := Prod.ext rfl heM.2.1
      rw [hdEq, heEq]
      exact wholePlane_missing_east_sameCycle W H
        (fun N => boundaryHitWitnesses_of_le W (Nat.zero_le N) h0)
        d.1 e.1 hdM.2.2 heM.2.2
    · exact (hnotunbounded (hfuture j' hvb) hdM.1).elim
    · exact (hnotunbounded (hpast j' hvb) hdM.1).elim
  · rcases uibhbot_assembly_bordered_face_cases
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e K he with
      heM | ⟨b, j', rfl, hb, hvb⟩ | ⟨b, j', rfl, hb, hvb⟩
    · exact (hnotunbounded (hfuture j hva) heM.1).elim
    · have hcaps : capFace w0 (H.1 0) j = capFace w0 (H.1 0) j' :=
        Subtype.ext ((Set.image_injective.mpr
          (uibhbotGlueFutureTransfer w0 h0 (H.1 0)).injective) (hva.symm.trans hvb))
      rw [← hcaps] at hb
      apply assemblyBorder_map_cap_sameCycle w0 (H.1 0) j
        (wholePlaneFaceSucc W H) (wholePlaneDartι W 0) ?_ a b haCap hb
      intro x hx
      exact wholePlaneFaceSucc_run_of_triangle W H 0 x ⟨j, hx⟩
    · exact (hcross j j' hva hvb).elim
  · rcases uibhbot_assembly_bordered_face_cases
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e K he with
      heM | ⟨b, j', rfl, hb, hvb⟩ | ⟨b, j', rfl, hb, hvb⟩
    · exact (hnotunbounded (hpast j hva) heM.1).elim
    · exact (hcross j' j hvb hva).elim
    · have himage := (Set.image_injective.mpr
        uibhbotAssemblyHalfTurn_involutive.injective) (hva.symm.trans hvb)
      have hcaps : capFace wp hfin j = capFace wp hfin j' :=
        Subtype.ext ((Set.image_injective.mpr
          (uibhbotPastStraightTransfer W hL hR).injective) himage)
      rw [← hcaps] at hb
      apply assemblyBorder_map_cap_sameCycle wp hfin j
        (wholePlaneFaceSucc W H) (kmswPastDart W) ?_ a b haCap hb
      intro x hx
      exact kmswPastDart_faceSucc_of_triangle W H hfin x ⟨j, hx⟩

/- B2b, B2, B3, B4 and B5 are proved above, under the original assembly variables
and the authorized hRpos. Its almost-sure discharge remains the second clause
of uibhbotCodeLawRel_ae_past_R_nonneg. Earlier declarations are preserved.

The horizontal-connection obligation is resolved by the finite UR suffix:
the suffix beginning at a persistent edge survives unchanged, covers every
abscissa from that edge to the past right endpoint, and bounds the full past
trace there by the finite stage N. The attached strip above height N is
connected and meets the quadrant. Upward rays from the relevant exterior
wedges therefore belong to the quadrant component.

Successor invariance uses the forward and backward creation-cap rules.
For B5, every non-cap dart is proved to be a globally missing east dart.
Negatively labelled future boundary edges remain strict records in every
earlier-start window by hR; all missing east darts share one successor orbit.
Boundedness separates transported caps from the unbounded quadrant face,
and strict height signs separate future caps from past caps.

No component, trace-height, root-capture, face-classification or additional
support premise has been introduced. No uniqueness of arbitrary unbounded
components is assumed. In particular this file does not yet prove the
separate global face-coverage statement

  ∀ K : (G).Face, ∃ d : WholePlaneDart W, (G).dartBorders d K.

That downstream obligation and construction of a surjective face-orbit
completion of Definition 5.8 or of the paper. -/

end DirectedDistances.KMSW
