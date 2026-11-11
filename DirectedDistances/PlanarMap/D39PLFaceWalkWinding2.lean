/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceWalkWinding
import DirectedDistances.PlanarMap.D39PolygonalSeparation5
import DirectedDistances.PlanarMap.D39BallOrbitComponents4

/-! Helpers toward Proposition 5.16: fixing the face-walk winding orientation. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set
open scoped ComplexConjugate

namespace Polyline

open Filter Topology

/-- Helper toward Proposition 5.16: the signed angle-sum jump is `+1` when
the first point is on the left of an oriented edge and the second is on its
right. -/
theorem angleSum_edge_jump_cyclic_signed (p : Polyline)
    (hcyclic : p.IsCyclicSimple) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (u v : ℂ), u ∉ p.image → v ∉ p.image →
        dist u x < ε → dist v x < ε →
        0 < (conj (p.point (i + 1) - p.point i) * (u - x)).im →
        (conj (p.point (i + 1) - p.point i) * (v - x)).im < 0 →
        p.angleSum u - p.angleSum v = 1 := by
  have hroot := hcyclic.2.1
  have hclosed : p.start = p.finish := by
    rw [← point_zero_eq_start p, ← point_last_eq_finish p]
    exact hroot
  let s := Finset.range (p.points.length - 1)
  let Lpos := (∑ j ∈ s, if j = i then Real.pi else p.edgeAngle x j) /
    (2 * Real.pi)
  let Lneg := (∑ j ∈ s, if j = i then -Real.pi else p.edgeAngle x j) /
    (2 * Real.pi)
  have hiMem : i ∈ s := by
    simp [s]
    omega
  have hsumdiff :
      (∑ j ∈ s, if j = i then Real.pi else p.edgeAngle x j) -
        (∑ j ∈ s, if j = i then -Real.pi else p.edgeAngle x j) =
      2 * Real.pi := by
    calc
      _ = ∑ j ∈ s,
          ((if j = i then Real.pi else p.edgeAngle x j) -
            (if j = i then -Real.pi else p.edgeAngle x j)) := by
              rw [Finset.sum_sub_distrib]
      _ = (if i = i then Real.pi else p.edgeAngle x i) -
            (if i = i then -Real.pi else p.edgeAngle x i) := by
              apply Finset.sum_eq_single_of_mem i hiMem
              intro j hj hji
              simp [hji]
      _ = 2 * Real.pi := by simp; ring
  have hLdiff : Lpos - Lneg = 1 := by
    dsimp [Lpos, Lneg]
    rw [← sub_div, hsumdiff]
    field_simp [Real.pi_ne_zero]
  have hpos := tendsto_angleSum_nhdsWithin_pos_cyclic p hcyclic i hi x hx hxi hxi1
  have hneg := tendsto_angleSum_nhdsWithin_neg_cyclic p hcyclic i hi x hx hxi hxi1
  have hevpos : ∀ᶠ z : ℂ in 𝓝 x,
      z ∈ {z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im} →
        dist (p.angleSum z) Lpos < 1 / 4 := by
    have hb := Metric.ball_mem_nhds Lpos (by norm_num : 0 < (1 / 4 : ℝ))
    have hevent := hpos.eventually hb
    have hwithin : ∀ᶠ z : ℂ in
        𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x,
        dist (p.angleSum z) Lpos < 1 / 4 := by
      simpa [Metric.mem_ball, Lpos, s] using hevent
    exact eventually_nhdsWithin_iff.mp hwithin
  have hevneg : ∀ᶠ z : ℂ in 𝓝 x,
      z ∈ {z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0} →
        dist (p.angleSum z) Lneg < 1 / 4 := by
    have hb := Metric.ball_mem_nhds Lneg (by norm_num : 0 < (1 / 4 : ℝ))
    have hevent := hneg.eventually hb
    have hwithin : ∀ᶠ z : ℂ in
        𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x,
        dist (p.angleSum z) Lneg < 1 / 4 := by
      simpa [Metric.mem_ball, Lneg, s] using hevent
    exact eventually_nhdsWithin_iff.mp hwithin
  obtain ⟨εp, hεp, hnearpos⟩ := Metric.eventually_nhds_iff.mp hevpos
  obtain ⟨εn, hεn, hnearneg⟩ := Metric.eventually_nhds_iff.mp hevneg
  refine ⟨min εp εn, lt_min hεp hεn, ?_⟩
  intro u v hu hv hux hvx huPos hvNeg
  have hux' : dist u x < εp := lt_of_lt_of_le hux (min_le_left _ _)
  have hvx' : dist v x < εn := lt_of_lt_of_le hvx (min_le_right _ _)
  have huNear := hnearpos hux' (by simpa using huPos)
  have hvNear := hnearneg hvx' (by simpa using hvNeg)
  have huClose : |p.angleSum u - Lpos| < 1 / 4 := by
    simpa [Real.dist_eq] using huNear
  have hvClose : |p.angleSum v - Lneg| < 1 / 4 := by
    simpa [Real.dist_eq] using hvNear
  have hclose : |(p.angleSum u - p.angleSum v) - 1| < 1 / 2 := by
    have heq : (p.angleSum u - p.angleSum v) - 1 =
        (p.angleSum u - Lpos) + -(p.angleSum v - Lneg) := by linarith [hLdiff]
    calc
      _ = |(p.angleSum u - Lpos) + -(p.angleSum v - Lneg)| := by rw [heq]
      _ ≤ |p.angleSum u - Lpos| + |p.angleSum v - Lneg| := by
        calc
          |(p.angleSum u - Lpos) + -(p.angleSum v - Lneg)| ≤
              |p.angleSum u - Lpos| + |-(p.angleSum v - Lneg)| := abs_add_le _ _
          _ = |p.angleSum u - Lpos| + |p.angleSum v - Lneg| := by rw [abs_neg]
      _ < 1 / 2 := by linarith
  obtain ⟨m, hm⟩ := angleSum_isInt p hclosed u hu
  obtain ⟨n, hn⟩ := angleSum_isInt p hclosed v hv
  have hcast : |((m - n : ℤ) : ℝ) - 1| < 1 / 2 := by
    simpa [hm, hn, Int.cast_sub] using hclose
  have hmn := int_sub_eq_one_of_abs_lt_half_cyclic m n hcast
  rw [hm, hn, ← Int.cast_sub, hmn]
  norm_num

end Polyline

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)

include hconn

omit hconn in
/-- Helper toward Proposition 5.16: every finite initial face walk retains
at least the two vertices of its first dart. -/
theorem faceWalkPolyline_points_length_ge_two (d : B.D) :
    ∀ n : ℕ, 2 ≤ (faceWalkPolyline B vert P d n).points.length := by
  intro n
  induction n with
  | zero => exact P.arc_length d
  | succ n ih =>
      rw [faceWalkPolyline, Polyline.length_boundaryConcat]
      have harc := P.arc_length ((B.map.faceSucc : B.D → B.D)^[n + 1] d)
      omega

/-- Helper toward Proposition 5.16: the first two vertices of a face walk
retain those of its first dart arc. -/
theorem faceWalkPolyline_point_one (d : B.D) (n : ℕ) :
    (faceWalkPolyline B vert P d n).point 1 = (P.arc d).point 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [faceWalkPolyline, Polyline.point_boundaryConcat_left]
      · exact ih
      · have hlen := faceWalkPolyline_points_length_ge_two B vert P d n
        omega

/-- Helper toward Proposition 5.16: the full-period walk around a bounded
face has angle sum `+1` throughout that face when its first dart borders it. -/
theorem faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded
    (O : D39BallFaceCycleOrbit B)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hclosed : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).finish)
    (hc : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple) :
    ∀ z ∈ (B.plOrbitFace vert P hvert O).val,
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).angleSum z = 1 := by
  intro z hz
  let q := faceWalkPolyline B vert P d
    (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)
  have hboundary : q.image = B.plOrbitBoundary vert P O := by
    dsimp [q]
    exact B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd
  have hinside : (B.plOrbitFace vert P hvert O).val = q.inside :=
    B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
      vert P hvert hconn O q (by simpa only [q] using hclosed) hc hboundary hbounded
  obtain ⟨sgn, hsgn, hsum⟩ := q.exists_inside_angleSum_sign hc
  have hborder : P.dartBorders d (B.plOrbitFace vert P hvert O) :=
    (B.dartBorders_plOrbitFace_iff vert P hvert hconn O d).2 hd
  rcases hborder with ⟨δ, hδ, hface⟩
  let t : ℝ := min δ 1 / 2
  have ht : 0 < t := by
    dsimp [t]
    linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1)]
  have htδ : t < δ := by
    dsimp [t]
    linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1), min_le_left δ 1]
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1), min_le_right δ 1]
  let u : ℂ := (P.arc d).initialDirection
  have hu : u ≠ 0 := by
    exact P.initial_nonzero d
  have hq0 : q.point 0 = (P.arc d).point 0 := by
    rw [Polyline.point_zero_eq_start, start_faceWalkPolyline,
      Polyline.point_zero_eq_start]
  have hq1 : q.point 1 = (P.arc d).point 1 := by
    dsimp [q]
    exact faceWalkPolyline_point_one B vert P hconn d _
  have hdir : q.point 1 - q.point 0 = u := by
    rw [hq0, hq1, Polyline.point_zero_eq_start]
    rfl
  let x : ℂ := (P.arc d).start + (t : ℂ) * u
  have hxform : x = q.point 0 + (t : ℂ) * (q.point 1 - q.point 0) := by
    dsimp [x]
    calc
      (P.arc d).start + (t : ℂ) * u =
          (P.arc d).point 0 + (t : ℂ) * ((P.arc d).point 1 - (P.arc d).point 0) := by
            simp [u, Polyline.initialDirection, Polyline.point_zero_eq_start]
      _ = q.point 0 + (t : ℂ) * (q.point 1 - q.point 0) := by
            rw [← hq0, ← hq1]
  have hx : x ∈ q.segmentAt 0 := by
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨t, ⟨le_of_lt ht, ht1.le⟩, ?_⟩
    change q.point 0 + (t : ℝ) • (q.point 1 - q.point 0) = x
    rw [RCLike.real_smul_eq_coe_mul]
    exact hxform.symm
  have hxsub : x - q.point 0 = (t : ℂ) * (q.point 1 - q.point 0) := by
    rw [hxform]
    ring
  have hxi : x ≠ q.point 0 := by
    intro heq
    have hz : (t : ℂ) * (q.point 1 - q.point 0) = 0 := by
      rw [← hxsub, heq]
      simp
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    exact (mul_ne_zero ht0 (show q.point 1 - q.point 0 ≠ 0 by rw [hdir]; exact hu)) hz
  have hxsub1 : x - q.point 1 = ((t - 1 : ℝ) : ℂ) * (q.point 1 - q.point 0) := by
    rw [hxform]
    push_cast
    ring
  have hxi1 : x ≠ q.point 1 := by
    intro heq
    have hz : ((t - 1 : ℝ) : ℂ) * (q.point 1 - q.point 0) = 0 := by
      rw [← hxsub1, heq]
      simp
    have htne : ((t - 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (sub_ne_zero.mpr (ne_of_lt ht1))
    exact (mul_ne_zero htne (show q.point 1 - q.point 0 ≠ 0 by rw [hdir]; exact hu)) hz
  obtain ⟨rjump, hrjump, hjump⟩ :=
    Polyline.angleSum_edge_jump_cyclic_signed q hc 0 (by
      have hlen : 4 ≤ q.points.length := by simpa only [q] using hc.1
      omega) x hx hxi hxi1
  obtain ⟨rside, hrside, hdisjoint⟩ :=
    Polyline.exists_rightHalfDisc_disjoint_image_cyclic q hc 0
      (by
        have hlen : 4 ≤ q.points.length := by simpa only [q] using hc.1
        omega)
      x hx hxi hxi1
  let ε : ℝ := min (δ / 2) (min rjump rside / (2 * (t * ‖u‖)))
  have hnormu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have heps : 0 < ε := by
    dsimp [ε]
    positivity
  have hepsδ : ε < δ := by
    dsimp [ε]
    have hδ2 : δ / 2 < δ := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hδ2
  have hdist : t * ε * ‖u‖ < min rjump rside := by
    dsimp [ε]
    have hcpos : 0 < t * ‖u‖ := mul_pos ht hnormu
    have hbound : ε ≤ min rjump rside / (2 * (t * ‖u‖)) := min_le_right _ _
    have hprod := mul_le_mul_of_nonneg_left hbound hcpos.le
    have hminpos : 0 < min rjump rside := lt_min hrjump hrside
    have hcancel : (t * ‖u‖) * (min rjump rside / (2 * (t * ‖u‖))) =
        min rjump rside / 2 := by
      field_simp [ne_of_gt hcpos]
    calc
      t * ε * ‖u‖ = (t * ‖u‖) * ε := by ring
      _ ≤ (t * ‖u‖) * (min rjump rside / (2 * (t * ‖u‖))) := hprod
      _ = min rjump rside / 2 := hcancel
      _ < min rjump rside := half_lt_self hminpos
  let zL : ℂ := (P.arc d).start + (t : ℂ) *
    (u + (ε : ℂ) * Complex.I * u)
  let zR : ℂ := x - (t * ε : ℂ) * Complex.I * u
  have hzLface : zL ∈ (B.plOrbitFace vert P hvert O).val := by
    dsimp [zL]
    exact hface t ε ht htδ heps hepsδ
  have hzLinside : zL ∈ q.inside := by
    simpa only [hinside] using hzLface
  have hzLoff : zL ∉ q.image := hzLinside.1
  have hnormal : (conj u * (Complex.I * u)).im = Complex.normSq u := by
    rw [show conj u * (Complex.I * u) = Complex.I * (conj u * u) by ring,
      ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
  have hzLsub : zL - x = (t * ε : ℝ) • (Complex.I * u) := by
    dsimp [zL, x]
    push_cast
    ring
  have hzRsub : zR - x = -((t * ε : ℝ) • (Complex.I * u)) := by
    dsimp [zR]
    push_cast
    ring
  have hdistL : dist zL x = t * ε * ‖u‖ := by
    rw [dist_eq_norm, hzLsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos ht heps), norm_mul, Complex.norm_I, one_mul]
  have hdistR : dist zR x = t * ε * ‖u‖ := by
    rw [dist_eq_norm, hzRsub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos ht heps), norm_mul, Complex.norm_I, one_mul]
  have hleft : 0 < (conj (q.point 1 - q.point 0) * (zL - x)).im := by
    rw [hdir, hzLsub, mul_smul_comm, Complex.smul_im, hnormal]
    exact mul_pos (mul_pos ht heps) (Complex.normSq_pos.mpr hu)
  have hright : (conj (q.point 1 - q.point 0) * (zR - x)).im < 0 := by
    have hpos : 0 < (conj u * ((t * ε : ℝ) • (Complex.I * u))).im := by
      rw [mul_smul_comm, Complex.smul_im, hnormal]
      exact mul_pos (mul_pos ht heps) (Complex.normSq_pos.mpr hu)
    rw [hdir, hzRsub]
    have hneg : (conj u * -((t * ε : ℝ) • (Complex.I * u))).im =
        -((conj u * ((t * ε : ℝ) • (Complex.I * u))).im) := by simp
    rw [hneg]
    exact neg_lt_zero.mpr hpos
  have hzRside : zR ∈ Polyline.rightHalfDisc x (q.point 1 - q.point 0) rside := by
    change dist zR x < rside ∧ (conj (q.point 1 - q.point 0) * (zR - x)).im < 0
    rw [hdistR]
    exact ⟨lt_of_lt_of_le hdist (min_le_right _ _), hright⟩
  have hzRoff : zR ∉ q.image := by
    intro hz
    exact (Set.disjoint_left.mp hdisjoint) hzRside hz
  have hdistLjump : dist zL x < rjump :=
    lt_of_lt_of_le (by rw [hdistL]; exact hdist) (min_le_left _ _)
  have hdistRjump : dist zR x < rjump :=
    lt_of_lt_of_le (by rw [hdistR]; exact hdist) (min_le_left _ _)
  have hjump' := hjump zL zR hzLoff hzRoff hdistLjump hdistRjump hleft hright
  have hL : q.angleSum zL = sgn := hsum zL hzLinside
  have hRvalues : q.angleSum zR = 0 ∨ q.angleSum zR = sgn := by
    rcases hsgn with hs | hs
    · have hsumOne : ∀ w ∈ q.inside, q.angleSum w = 1 := by
        intro w hw
        simpa [hs] using hsum w hw
      rcases (q.angleSum_zero_or_one_of_counterclockwise hsumOne zR hzRoff).1 with
        hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (hone.trans hs.symm)
    · have hccw : ∀ w ∈ q.reverse.inside, q.reverse.angleSum w = 1 := by
        intro w hw
        have hwq : w ∈ q.inside := by simpa only [Polyline.inside_reverse] using hw
        rw [Polyline.angleSum_reverse q w hwq.1, hsum w hwq, hs]
        norm_num
      have hvals := q.reverse.angleSum_zero_or_one_of_counterclockwise hccw zR
        (by simpa only [Polyline.image_reverse_transfer] using hzRoff)
      rcases hvals.1 with hzero | hone
      · left
        have hrev := Polyline.angleSum_reverse q zR hzRoff
        rw [hzero] at hrev
        linarith
      · right
        have hrev := Polyline.angleSum_reverse q zR hzRoff
        rw [hone] at hrev
        have hq : q.angleSum zR = -1 := by linarith
        exact hq.trans hs.symm
  have hsone : sgn = 1 := by
    rcases hsgn with hs | hs
    · exact hs
    · rcases hRvalues with hzero | hone
      · rw [hL, hzero, hs] at hjump'
        norm_num at hjump'
      · rw [hL, hone, hs] at hjump'
        norm_num at hjump'
  have hzq : z ∈ q.inside := by simpa only [hinside] using hz
  have hfinal : q.angleSum z = 1 := by
    calc
      q.angleSum z = sgn := hsum z hzq
      _ = 1 := hsone
  simpa only [q] using hfinal

end D39FiniteBall

end DirectedDistances.PlanarMap

end
