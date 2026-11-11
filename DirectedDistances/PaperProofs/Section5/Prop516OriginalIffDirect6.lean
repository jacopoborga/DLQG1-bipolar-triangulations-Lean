/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect5
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact20
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact9
import DirectedDistances.PlanarMap.PLDrawingWindingSides17

/-! Helpers toward Proposition 5.16 and the signed local interpretation of -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap Set unitInterval Metric
open scoped Topology

/-- Helper toward Proposition 5.16: splitting an affine subarc into three
ordered pieces preserves its full image, including the split endpoints. -/
theorem range_affineSubarc_three {x y : ℂ} (γ : Path x y)
    (a u v b : I) (hau : a < u) (huv : u < v) (hvb : v < b) :
    Set.range ((affineSubarc γ a u).trans
      ((affineSubarc γ u v).trans (affineSubarc γ v b))) =
      Set.range (affineSubarc γ a b) := by
  have hab := hau.trans (huv.trans hvb)
  simp only [Path.trans_range,
    affineSubarc_range_eq_edgeSubarc γ a u hau,
    affineSubarc_range_eq_edgeSubarc γ u v huv,
    affineSubarc_range_eq_edgeSubarc γ v b hvb,
    affineSubarc_range_eq_edgeSubarc γ a b hab,
    range_edgeSubarc_eq_image_Icc32]
  rw [← Set.image_union, ← Set.image_union]
  congr 1
  ext t
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro (⟨hat, htu⟩ | ⟨hut, htv⟩ | ⟨hvt, htb⟩)
    · exact ⟨hat, htu.trans (huv.le.trans hvb.le)⟩
    · exact ⟨hau.le.trans hut, htv.trans hvb.le⟩
    · exact ⟨(hau.le.trans huv.le).trans hvt, htb⟩
  · rintro ⟨hat, htb⟩
    by_cases htu : t ≤ u
    · exact Or.inl ⟨hat, htu⟩
    · by_cases htv : t ≤ v
      · exact Or.inr (Or.inl ⟨(le_of_not_ge htu), htv⟩)
      · exact Or.inr (Or.inr ⟨(le_of_not_ge htv), htb⟩)

/-- Helper toward Proposition 5.16: cyclically rebase the exact paused
edge-subarc loop onto any interior subarc. This holds at every viewpoint
and for every integer, including viewpoints on the trace. Only the source
arc is required to be injective; the continuous return is arbitrary. -/
theorem hasWinding_edgeSubarc_trans_iff_cyclic_rebase
    {x y : ℂ} (γ : Path x y) (hγ : Function.Injective γ)
    (a u v b : I) (hau : a < u) (huv : u < v) (hvb : v < b)
    (q : Path (γ b) (γ a)) (z : ℂ) (n : ℤ) :
    HasWinding ((edgeSubarc γ a b (hau.trans (huv.trans hvb)).le).trans q) z n ↔
      HasWinding ((affineSubarc γ u v).trans
        ((affineSubarc γ v b).trans (q.trans (affineSubarc γ a u)))) z n := by
  have hab := hau.trans (huv.trans hvb)
  rw [hasWinding_edgeSubarc_trans_iff_affineSubarc γ a b hab q z n]
  rw [hasWinding_trans_iff_of_same_injective_arc_image32
    (affineSubarc γ a b) (affineSubarc_injective γ hγ a b hab)
    ((affineSubarc γ a u).trans
      ((affineSubarc γ u v).trans (affineSubarc γ v b)))
    (range_affineSubarc_three γ a u v b hau huv hvb) q z n]
  change HasLiftIncrement _ z (2 * Real.pi * Complex.I * n) ↔
    HasLiftIncrement _ z (2 * Real.pi * Complex.I * n)
  simp only [hasLiftIncrement_trans_iff]
  constructor
  · rintro ⟨c, cq, ⟨ca, cst, hA, ⟨cs, ct, hS, hT, hst⟩, hc⟩, hq, hn⟩
    refine ⟨cs, ct + (cq + ca), hS, ⟨ct, cq + ca, hT,
      ⟨cq, ca, hq, hA, rfl⟩, rfl⟩, ?_⟩
    rw [hn, hc, hst]
    ring
  · rintro ⟨cs, ctr, hS, ⟨ct, cqa, hT, ⟨cq, ca, hq, hA, hqa⟩, htr⟩, hn⟩
    refine ⟨ca + (cs + ct), cq,
      ⟨ca, cs + ct, hA, ⟨cs, ct, hS, hT, rfl⟩, rfl⟩, hq, ?_⟩
    rw [hn, htr, hqa]
    ring

/-- Helper toward Proposition 5.16: a strict geometric segment point has
its unique path parameter strictly between that segment's dyadic endpoints. -/
theorem parameter_in_segment_of_toPath_eq
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hsimple : p.IsSimple)
    {i : ℕ} (hi : i + 1 < p.points.length) {z : ℂ}
    (hz : z ∈ openSegment ℝ (p.point i) (p.point (i + 1)))
    (s : I) (hs : p.toPath s = z) :
    Polyline.segmentParameterStart i < (s : ℝ) ∧
      (s : ℝ) < Polyline.segmentParameterEnd p.points.length i := by
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨c, hc, hcz⟩ := hz
  let α := Polyline.segmentParameterStart i
  let β := Polyline.segmentParameterEnd p.points.length i
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end p.points.length i
  have htα : α < α + c * (β - α) := by nlinarith [hc.1]
  have htβ : α + c * (β - α) < β := by nlinarith [hc.2]
  let t : I := ⟨α + c * (β - α),
    ⟨(Polyline.segmentParameterStart_mem_Icc i).1.trans htα.le,
      htβ.le.trans (Polyline.segmentParameterEnd_mem_Icc p.points.length i).2⟩⟩
  have ht : p.toPath t = z := by
    rw [p.toPath_segment_affine_apply hi t htα.le htβ.le, ← hcz]
    simp only [AffineMap.lineMap_apply_module', Complex.real_smul]
    have hcoeff : ((t : ℝ) - α) / (β - α) = c := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hαβ)]
      ring
    change p.point i + (((((t : ℝ) - α) / (β - α)) : ℝ) : ℂ) *
      (p.point (i + 1) - p.point i) = _
    rw [hcoeff]
    ring
  have hts : t = s := p.toPath_injective hlen hsimple (ht.trans hs.symm)
  subst s
  exact ⟨htα, htβ⟩

/-- Helper toward Proposition 5.16: the affine subarc within a single
polyline leg is the straight segment with those exact endpoints. -/
theorem affineSubarc_eq_segment_of_subinterval
    (p : Polyline) {i : ℕ} (hi : i + 1 < p.points.length)
    (u v : I) (huv : u < v)
    (hu : Polyline.segmentParameterStart i ≤ (u : ℝ))
    (hv : (v : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
    affineSubarc p.toPath u v = Path.segment (p.toPath u) (p.toPath v) := by
  apply Path.ext
  funext t
  change p.toPath (Set.Icc.convexComb u v t) = _
  rw [p.toPath_affine_on_segment_subinterval hi u v huv hu hv _
    (Set.Icc.le_convexComb huv.le t) (Set.Icc.convexComb_le huv.le t)]
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module', Complex.real_smul]
  have hc : (((Set.Icc.convexComb u v t : I) : ℝ) - u) /
      ((v : ℝ) - u) = (t : ℝ) := by
    rw [Set.Icc.coe_convexComb]
    field_simp [ne_of_gt (sub_pos.mpr (show (u : ℝ) < v from huv))]
    ring
  rw [hc]
  ring

/-- Helper toward Proposition 5.16: the direction of a subinterval of a
polyline leg is a positive real multiple of the original leg direction. -/
theorem toPath_subinterval_direction
    (p : Polyline) {i : ℕ} (hi : i + 1 < p.points.length)
    (u v : I) (huv : u < v)
    (hu : Polyline.segmentParameterStart i ≤ (u : ℝ))
    (hv : (v : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
    ∃ c : ℝ, 0 < c ∧ p.toPath v - p.toPath u =
      (c : ℂ) * (p.point (i + 1) - p.point i) := by
  let α := Polyline.segmentParameterStart i
  let β := Polyline.segmentParameterEnd p.points.length i
  have hden : 0 < β - α := sub_pos.mpr
    (Polyline.segmentParameterStart_lt_end p.points.length i)
  refine ⟨((v : ℝ) - u) / (β - α), div_pos (sub_pos.mpr huv) hden, ?_⟩
  have huvR : (u : ℝ) < v := huv
  rw [p.toPath_segment_affine_apply hi v (hu.trans huvR.le) hv,
    p.toPath_segment_affine_apply hi u hu (huvR.le.trans hv)]
  change _ = (((((v : ℝ) - u) / (β - α)) : ℝ) : ℂ) * _
  have hc : ((v : ℝ) - α) / (β - α) - ((u : ℝ) - α) / (β - α) =
      ((v : ℝ) - u) / (β - α) := by ring
  rw [← hc]
  push_cast
  ring

/-- Helper toward Proposition 5.16: a parameter strictly between two
parameters on the same polyline leg maps to the strict chord interior. -/
theorem toPath_mem_openSegment_subinterval
    (p : Polyline) {i : ℕ} (hi : i + 1 < p.points.length)
    (u s v : I) (hus : u < s) (hsv : s < v)
    (hu : Polyline.segmentParameterStart i ≤ (u : ℝ))
    (hv : (v : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
    p.toPath s ∈ openSegment ℝ (p.toPath u) (p.toPath v) := by
  have huv := hus.trans hsv
  have hden : 0 < (v : ℝ) - u := sub_pos.mpr huv
  rw [openSegment_eq_image_lineMap]
  refine ⟨((s : ℝ) - u) / ((v : ℝ) - u),
    ⟨div_pos (sub_pos.mpr hus) hden, (div_lt_one hden).mpr (by
      exact sub_lt_sub_right (show (s : ℝ) < v from hsv) _)⟩, ?_⟩
  rw [p.toPath_affine_on_segment_subinterval hi u v huv hu hv s hus.le hsv.le]
  simp only [AffineMap.lineMap_apply_module', Complex.real_smul]
  ring

/-- Helper toward Proposition 5.16: the exact winding-left witness selects
the geometric left half-disc at a strict point of a polygonal leg.
No distinction between the two bordering faces is required. -/
theorem exists_leftHalfDisc_subset_of_leftAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (s : {t : unitInterval // t ∈ openParams})
    (hsp : (P.arc d).toPath s.val = p)
    (hleft : LeftAtOn F.val (P.arc d).toPath s) :
    ∃ r : ℝ, 0 < r ∧
      Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
        ⊆ F.val := by
  let γ := (P.arc d).toPath
  have hγ : Function.Injective γ :=
    (P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)
  obtain ⟨hαs, hsβ⟩ := parameter_in_segment_of_toPath_eq
    (P.arc d) (P.arc_length d) (P.arc_simple d) hi hp s.1 hsp
  let α : I := ⟨Polyline.segmentParameterStart i,
    Polyline.segmentParameterStart_mem_Icc i⟩
  let β : I := ⟨Polyline.segmentParameterEnd (P.arc d).points.length i,
    Polyline.segmentParameterEnd_mem_Icc (P.arc d).points.length i⟩
  have hαsI : α < s.1 := hαs
  have hsβI : s.1 < β := hsβ
  obtain ⟨a, b, _ha, has, hsb, _hb, q, _hqi, hqF, hcl, hbound⟩ :=
    leftAtOn_witness_with_bounded_winding P d F s hleft
  obtain ⟨u, hu, hus⟩ := exists_between (max_lt has hαsI)
  obtain ⟨v, hsv, hv⟩ := exists_between (lt_min hsb hsβI)
  have hau : a < u := (le_max_left a α).trans_lt hu
  have hαu : α < u := (le_max_right a α).trans_lt hu
  have hvb : v < b := hv.trans_le (min_le_left b β)
  have hvβ : v < β := hv.trans_le (min_le_right b β)
  have huv : u < v := hus.trans hsv
  let R := (affineSubarc γ v b).trans (q.trans (affineSubarc γ a u))
  have hS : affineSubarc γ u v = Path.segment (γ u) (γ v) :=
    affineSubarc_eq_segment_of_subinterval (P.arc d) hi u v huv hαu.le hvβ.le
  have hpchord : p ∈ openSegment ℝ (γ u) (γ v) := by
    rw [← hsp]
    exact toPath_mem_openSegment_subinterval (P.arc d) hi u s.1 v hus hsv
      hαu.le hvβ.le
  have hchord : γ u ≠ γ v := fun h => huv.ne (hγ h)
  have hrebase (w : ℂ) (n : ℤ) :
      HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w n ↔
        HasWinding ((Path.segment (γ u) (γ v)).trans R) w n := by
    have h := hasWinding_edgeSubarc_trans_iff_cyclic_rebase
      γ hγ a u v b hau huv hvb q w n
    rw [hS] at h
    exact h
  have hpq : p ∉ Set.range q := by
    intro hpq
    have himage : p ∈ P.image := by
      rw [← hsp]
      exact Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸ Set.mem_range_self s.1⟩
    have hends : p ∈ ({γ b, γ a} : Set ℂ) := by
      rw [← returnPath_inter_drawing P d F a b q hqF]
      exact ⟨hpq, himage⟩
    rcases hends with h | h
    · exact hsb.ne (hγ (hsp.trans h))
    · exact has.ne (hγ (h.symm.trans hsp.symm))
  have havoidpiece (l r : I) (hlr : l < r) (hout : s.1 ∉ Set.Icc l r) :
      p ∉ Set.range (affineSubarc γ l r) := by
    rw [affineSubarc_range_eq_edgeSubarc γ l r hlr,
      range_edgeSubarc_eq_image_Icc32]
    rintro ⟨t, ht, htp⟩
    have hts : t = s.1 := hγ (htp.trans hsp.symm)
    exact hout (hts ▸ ht)
  have hpR : p ∉ Set.range R := by
    dsimp [R]
    rw [Path.trans_range, Path.trans_range]
    rintro (hT | hq | hA)
    · exact havoidpiece v b hvb (fun h => (not_le_of_gt hsv) h.1) hT
    · exact hpq hq
    · exact havoidpiece a u hau (fun h => (not_le_of_gt hus) h.2) hA
  have hclosed : IsClosed (Set.range R) := (isCompact_range R.continuous).isClosed
  have hr : 0 < infDist p (Set.range R) :=
    (hclosed.notMem_iff_infDist_pos (Set.range_nonempty R)).mp hpR
  have hball : Disjoint (ball p (infDist p (Set.range R))) (Set.range R) := by
    apply Set.disjoint_left.mpr
    intro w hw hwr
    have hdist := infDist_le_dist_of_mem (x := p) hwr
    exact (not_lt_of_ge hdist) (by simpa only [mem_ball, dist_comm] using hw)
  obtain ⟨c, hc, hdir⟩ := toPath_subinterval_direction
    (P.arc d) hi u v huv hαu.le hvβ.le
  have hsign (w : ℂ) :
      (star (γ v - γ u) * (w - p)).im =
        c * (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (w - p)).im := by
    rw [hdir]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [mul_assoc, Complex.mul_im]
    simp
    ring
  have hborder : P.dartBorders d F := by
    rw [hsp] at hcl
    rcases P.mem_closure_winding_border_cases_of_openSegment32
        hfinite d F hi hp _ 1 hcl with hpos | hneg
    · exact hpos.1
    · exfalso
      have hright : p ∈ closure {w : ℂ |
          HasWinding ((Path.segment (γ u) (γ v)).trans R) w 1 ∧
            (star (γ v - γ u) * (w - p)).im < 0} := by
        apply closure_mono _ hneg.2
        intro w hw
        exact ⟨(hrebase w 1).mp hw.2.1, by rw [hsign]; exact mul_neg_of_pos_of_neg hc hw.2.2⟩
      have htwo := (mem_closure_segment_return_winding_iff32
        hchord hpchord hr R hball 1).mpr hright
      obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp htwo 1 (by norm_num)
      have hbnd := hbound w 2 ((hrebase w 2).mpr hw.1)
      norm_num at hbnd
  obtain ⟨r, hr, hleftDisc, _⟩ :=
    exists_openSegment_halfDiscs_face_classification P hfinite d hi hp
  exact ⟨r, hr, (hleftDisc F).mpr hborder⟩
































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
