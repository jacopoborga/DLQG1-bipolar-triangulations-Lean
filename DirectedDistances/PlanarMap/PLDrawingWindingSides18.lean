/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides17
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Straight bends and winding sides -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Metric
open scoped Topology ComplexConjugate

namespace PLDrawing

/-- Helper toward Definition 3.2: opposite incident directions would
make the two segments of a simple polyline overlap away from their shared
vertex. -/
theorem bend_directions_not_neg_smul (p : Polyline) (hp : p.IsSimple)
    {i : ℕ} (hi : i + 2 < p.points.length) (α : ℝ) (hα : α < 0) :
    p.point (i + 2) - p.point (i + 1) ≠
      α • (p.point (i + 1) - p.point i) := by
  let a := p.point i
  let b := p.point (i + 1)
  let c := p.point (i + 2)
  let u := b - a
  let v := c - b
  intro hvu
  change v = α • u at hvu
  have hv : v ≠ 0 := sub_ne_zero.mpr (hp.1 (i + 1) (by omega)).symm
  let t := 1 / (1 - α)
  have ht : 0 < t := div_pos zero_lt_one (by linarith only [hα])
  have ht1 : t < 1 := (div_lt_one (by linarith only [hα])).mpr (by linarith only [hα])
  have htα : 1 + t * α = t := by
    have hd : 1 - α ≠ 0 := ne_of_gt (by linarith only [hα])
    dsimp [t]
    field_simp [hd]
    ring
  have heq : b + t • v = a + t • u := by
    rw [hvu, smul_smul]
    have hba : b = a + u := by dsimp [u]; abel
    calc
      b + (t * α) • u = a + (1 + t * α) • u := by rw [hba]; module
      _ = a + t • u := by rw [htα]
  have hleft : b + t • v ∈ p.segmentAt i := by
    change b + t • v ∈ segment ℝ a b
    rw [heq, segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hright : b + t • v ∈ p.segmentAt (i + 1) := by
    change b + t • v ∈ segment ℝ b c
    rw [segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hmeet : b + t • v = b := by
    have hm : b + t • v ∈ p.segmentAt i ∩ p.segmentAt (i + 1) := ⟨hleft, hright⟩
    rw [hp.2.1 i hi] at hm
    exact hm
  have hz : t • v = 0 := by simpa only [add_eq_left] using hmeet
  exact (smul_ne_zero ht.ne' hv) hz

/-- Helper toward Definition 3.2: simplicity excludes reversal at a
collinear bend, so its outgoing direction is a positive multiple of its
incoming direction. -/
theorem bend_directions_pos_parallel (p : Polyline) (hp : p.IsSimple)
    {i : ℕ} (hi : i + 2 < p.points.length)
    (hcross : (star (p.point (i + 1) - p.point i) *
      (p.point (i + 2) - p.point (i + 1))).im = 0) :
    ∃ α : ℝ, 0 < α ∧ p.point (i + 2) - p.point (i + 1) =
      α • (p.point (i + 1) - p.point i) := by
  let u := p.point (i + 1) - p.point i
  let v := p.point (i + 2) - p.point (i + 1)
  have hu : u ≠ 0 := sub_ne_zero.mpr (hp.1 i (by omega)).symm
  have hv : v ≠ 0 := sub_ne_zero.mpr (hp.1 (i + 1) (by omega)).symm
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  let α := (star u * v).re / Complex.normSq u
  have hparallel : v = α • u := by
    apply mul_left_cancel₀ (star_ne_zero.mpr hu)
    have hprod : star u * v = ((star u * v).re : ℂ) := Complex.ext rfl hcross
    rw [hprod, mul_smul_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
    apply Complex.ext <;>
      simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
    dsimp [α]
    exact (div_mul_cancel₀ _ hn.ne').symm
  have hαne : α ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hparallel
    exact hv hparallel
  have hα : 0 < α := by
    by_contra h
    exact bend_directions_not_neg_smul p hp hi α
      (lt_of_le_of_ne (not_lt.mp h) hαne) hparallel
  exact ⟨α, hα, hparallel⟩

/-- Helper toward Definition 3.2: the left half-disk at a straight bend
lies in the face bordering the dart. -/
theorem dartBorders_bend_straight_left_halfDisk
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ ball b r →
      0 < (star u * (y - b)).im → y ∈ F.val := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨α, hα, hv⟩ := bend_directions_pos_parallel (P.arc d) (P.arc_simple d) hi hturn
  change v = α • u at hv
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  obtain ⟨r, hr, hlocal⟩ := P.bend_contact_local_image hvert d hi
  let W := {y : ℂ | y ∈ ball b r ∧ 0 < (star u * (y - b)).im}
  have hWc : Convex ℝ W := by
    simpa only [one_mul] using signed_halfDisk_convex b u r 1
  have hWsafe : W ⊆ P.imageᶜ := by
    intro y hy hyP
    rcases (hlocal y hy.1).mp hyP with hleft | hright
    · have hz := segment_contact_side_eq_zero ((P.arc d).point i) b b y
        (right_mem_segment ℝ _ _) hleft
      exact (ne_of_gt hy.2) hz
    · have hz := segment_contact_side_eq_zero b ((P.arc d).point (i + 2)) b y
        (left_mem_segment ℝ _ _) hright
      change (star v * (y - b)).im = 0 at hz
      rw [hv, star_smul, star_trivial, smul_mul_assoc, Complex.smul_im,
        smul_eq_mul] at hz
      exact (ne_of_gt (mul_pos hα hy.2)) hz
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face hvert d F hborder hi
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεδ : ε < δ := half_lt_self hδ
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using mem_ball_self hr))
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hfr : f t ∈ ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : W ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hWc.isPreconnected.subset_connectedComponentIn ⟨hfr, hfu⟩ hWsafe
  exact ⟨r, hr, fun y hyr hyu => hWF ⟨hyr, hyu⟩⟩

/-- Helper toward Definition 3.2: two equal, collinear half-diameters
traverse the same path as their full diameter. -/
theorem segment_trans_midpoint (b u : ℂ) :
    (Path.segment (b - u) b).trans (Path.segment b (b + u)) =
      Path.segment (b - u) (b + u) := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;>
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.real_smul] <;> push_cast <;> ring

/-- Helper toward Definition 3.2: every sufficiently small semicircle
centered at a straight bend returns through the bordering face, and its
winding-one face points accumulate at the bend. -/
theorem dartBorders_bend_straight_semicircleLoop
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Function.Injective (leftSemicircle b (ε • u)) ∧
      (∀ t : I, t ∈ openParams → leftSemicircle b (ε • u) t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop b (ε • u)) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  obtain ⟨R, hR, hhalf⟩ :=
    P.dartBorders_bend_straight_left_halfDisk hvert d F hborder hi hturn
  refine ⟨R / (‖u‖ + 1), div_pos hR (by positivity), ?_⟩
  intro ε hε hεδ
  let v := ε • u
  have hv : v ≠ 0 := smul_ne_zero hε.ne' hu
  have hvr : ‖v‖ < R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have h := (lt_div_iff₀ (by positivity : 0 < ‖u‖ + 1)).mp hεδ
    nlinarith only [h, hε]
  refine ⟨leftSemicircle_injective b v hv, ?_, Metric.mem_closure_iff.mpr ?_⟩
  · intro t ht
    apply hhalf _
    · rw [Metric.mem_ball, leftSemicircle_dist]
      exact hvr
    · have hp := leftSemicircle_side_pos b v hv t ht
      have he : (star v * (leftSemicircle b v t - b)).im =
          ε * (star u * (leftSemicircle b v t - b)).im := by
        dsimp only [v]
        rw [star_smul, star_trivial, smul_mul_assoc, Complex.smul_im, smul_eq_mul]
      rw [he] at hp
      exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_gt hε) h.1) |>.2
  · intro η hη
    let τ := min (1 / 2) (η / (2 * (‖v‖ + 1)))
    have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
    have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hτη : τ * (2 * (‖v‖ + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    let w := b + v * (τ * Complex.I)
    have hwx : dist w b = τ * ‖v‖ := by
      rw [dist_eq_norm]
      change ‖b + v * (τ * Complex.I) - b‖ = _
      rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one, mul_comm]
    have hwF : w ∈ F.val := by
      apply hhalf _
      · rw [Metric.mem_ball, hwx]
        exact (mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) hτ1).trans hvr
      · have he : star u * (w - b) =
            ((ε * τ : ℝ) : ℂ) * Complex.I * (star u * u) := by
          dsimp [w, v]
          push_cast
          ring
        rw [he, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          sub_zero, add_zero, mul_one, zero_add]
        exact mul_pos (mul_pos hε hτ) (Complex.normSq_pos.mpr hu)
    refine ⟨w, ⟨hwF, hasWinding_semicircleLoop b v hv τ hτ hτ1⟩, ?_⟩
    rw [dist_comm, hwx]
    nlinarith only [hτη, hτ, norm_nonneg v]

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with zero turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_turn_eq_zero
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) (i : ℕ)
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨α, hα, hv⟩ := bend_directions_pos_parallel p (P.arc_simple d) hi hturn
  change v = α • u at hv
  obtain ⟨δ, hδ, hreturn⟩ :=
    P.dartBorders_bend_straight_semicircleLoop hvert d F hborder hi hturn
  let r := min (δ / 2) (min (1 / 2) (α / 2))
  have hr : 0 < r := lt_min (half_pos hδ) (lt_min (by norm_num) (half_pos hα))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hrα : r < α := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hα)
  let ρ := r / α
  have hρ : 0 < ρ := div_pos hr hα
  have hρ1 : ρ < 1 := (div_lt_one hα).mpr hrα
  have hρv : ρ • v = r • u := by
    rw [hv, smul_smul]
    dsimp only [ρ]
    rw [div_mul_cancel₀ _ hα.ne']
  obtain ⟨hinj, hqface, hcl⟩ := hreturn r hr hrδ
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + ρ * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hρ (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hρ1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = ρ := by
      change (M + ρ * (H - M) - M) / (H - M) = ρ
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    change p.toPath b = B + ρ • v at hf
    rw [hf, hρv]
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q : Path (p.toPath b) (p.toPath a) :=
    (leftSemicircle B (r • u)).cast hbEval haEval
  have hqinj : Function.Injective q := by
    intro t t' htt'
    exact hinj htt'
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    exact hqface t ht
  have hpairfun (t : I) :
      ((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))) t =
      Path.segment (B - r • u) (B + r • u) t := by
    rw [haEval, hsEval, hbEval, segment_trans_midpoint]
  have hwind (w : ℂ) (hw : HasWinding (semicircleLoop B (r • u)) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      apply (hasWinding_congr_fun _ (semicircleLoop B (r • u)) w 1 ?_).mpr hw
      intro t
      change (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) t =
        ((Path.segment (B - r • u) (B + r • u)).trans (leftSemicircle B (r • u))) t
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact hpairfun _
      · rfl
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop B (r • u)) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at every interior bend, including straight subdivisions. -/
theorem dartBorders_toPath_leftAtOn_of_bend
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) (i : ℕ)
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1)) :
    LeftAtOn F.val (P.arc d).toPath s := by
  by_cases hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0
  · exact P.dartBorders_toPath_leftAtOn_of_bend_turn_eq_zero
      hvert d F hborder s i hi hbend hturn
  · exact P.dartBorders_toPath_leftAtOn_of_bend_turn_ne_zero
      hvert d F hborder s hi hbend hturn

end PLDrawing

namespace Polyline

/-- Helper toward Definition 3.2: the half-open segment parameter
intervals cover every parameter below one of a polyline with at least two
vertices. -/
theorem exists_segment_parameter_interval {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ i : ℕ, i + 1 < n ∧ segmentParameterStart i ≤ t ∧
      t < segmentParameterEnd n i := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨0, by omega, ?_, ?_⟩
    · simpa only [segmentParameterStart_zero] using ht0
    · simpa only [segmentParameterEnd_last (by omega : 0 + 2 = 2)] using ht1
  | succ n hn ih =>
    by_cases ht : t < segmentParameterStart (n - 1)
    · obtain ⟨i, hi, hstart, hend⟩ := ih
      refine ⟨i, by omega, hstart, ?_⟩
      rw [segmentParameterEnd_eq_start_succ (by omega : i + 2 ≠ n + 1)]
      by_cases hlast : i + 2 = n
      · have heq : i + 1 = n - 1 := by omega
        simpa only [heq] using ht
      · rw [segmentParameterEnd_eq_start_succ hlast] at hend
        exact hend
    · refine ⟨n - 1, by omega, le_of_not_gt ht, ?_⟩
      rw [segmentParameterEnd_last (by omega : n - 1 + 2 = n + 1)]
      exact ht1

end Polyline

namespace PLDrawing

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at every open parameter of the dart's PL arc. -/
theorem dartBorders_toPath_leftAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) :
    LeftAtOn F.val (P.arc d).toPath s := by
  obtain ⟨i, hi, hstart, hend⟩ := Polyline.exists_segment_parameter_interval
    (P.arc_length d) (s.1 : ℝ) s.1.property.1 s.property.2
  rcases eq_or_lt_of_le hstart with heq | hlt
  · have hi0 : i ≠ 0 := by
      intro hz
      rw [hz, Polyline.segmentParameterStart_zero] at heq
      exact (ne_of_gt s.property.1) heq.symm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    exact P.dartBorders_toPath_leftAtOn_of_bend hvert d F hborder s j (by omega) heq.symm
  · exact P.dartBorders_toPath_leftAtOn_of_strictSegment hvert d F hborder s hi hlt hend

end PLDrawing

end DirectedDistances.PlanarMap

end
