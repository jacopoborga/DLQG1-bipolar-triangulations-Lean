/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion5
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set Filter
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
open scoped Topology

/-- Helper toward Proposition 3.9: a set strictly above a graph fails
the left winding test on a simple polygonal arc whose first segment points
west. The graph domain may have a finite limiting abscissa. -/
theorem intrinsicConsumersFinal_not_forall_leftAtOn_of_above_graph
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hsimple : p.IsSimple)
    (hwest : (p.point 1).re < (p.point 0).re)
    {D : Set ℝ} {f : ℝ → ℝ}
    (htrace : p.image ⊆ {z : ℂ | z.re ∈ D ∧ z.im = f z.re})
    (F : Set ℂ) (habove : ∀ w ∈ F, w.re ∈ D → f w.re < w.im) :
    ¬ ∀ s, LeftAtOn F p.toPath s := by
  have hi : 0 + 1 < p.points.length := by omega
  let α := Polyline.segmentParameterStart 0
  let β := Polyline.segmentParameterEnd p.points.length 0
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end _ _
  let tval : ℝ := (α + β) / 2
  have hαt : α < tval := by dsimp only [tval]; linarith only [hαβ]
  have htβ : tval < β := by dsimp only [tval]; linarith only [hαβ]
  have hα0 : 0 ≤ α := (Polyline.segmentParameterStart_mem_Icc 0).1
  have hβ1 : β ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length 0).2
  let t : unitInterval := ⟨tval, hα0.trans hαt.le, htβ.le.trans hβ1⟩
  let s : {t : unitInterval // t ∈ openParams} :=
    ⟨t, hα0.trans_lt hαt, htβ.trans_le hβ1⟩
  let z := p.toPath t
  let a := p.point 0
  let b := p.point 1
  have hab : b.re < a.re := hwest
  have hz : z ∈ openSegment ℝ a b :=
    Polyline.toPath_mem_openSegment_of_parameter p hi t hαt htβ
  have hzseg : z ∈ segment ℝ b a := by
    rw [segment_symm]
    exact openSegment_subset_segment ℝ a b hz
  have hzheight := (mem_segment_iff_height hab).mp hzseg
  have hxz : b.re < z.re ∧ z.re < a.re := by
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨r, hr, heq⟩ := hz
    have hre := congrArg Complex.re heq
    simp only [AffineMap.lineMap_apply_module', Complex.add_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero] at hre
    constructor <;> nlinarith only [hr.1, hr.2, hab, hre]
  have hdisj : Disjoint F p.image := by
    apply disjoint_left.mpr
    intro w hw hwp
    have hh := htrace hwp
    exact (habove w hw hh.1).ne' hh.2
  let ε := min (z.re - b.re) (a.re - z.re)
  have hε : 0 < ε := lt_min (sub_pos.mpr hxz.1) (sub_pos.mpr hxz.2)
  have hright (w : ℂ) (hw : w ∈ F) (hwdist : dist w z < ε) :
      (star (p.point (0 + 1) - p.point 0) * (w - z)).im < 0 := by
    have hre : |w.re - z.re| ≤ dist w z := by
      simpa only [Complex.sub_re, Complex.dist_eq] using Complex.abs_re_le_norm (w - z)
    have hleft := neg_le_abs (w.re - z.re)
    have hright := le_abs_self (w.re - z.re)
    have hεb : ε ≤ z.re - b.re := min_le_left _ _
    have hεa : ε ≤ a.re - z.re := min_le_right _ _
    have hwb : b.re ≤ w.re := by linarith only [hre, hleft, hwdist, hεb]
    have hwa : w.re ≤ a.re := by linarith only [hre, hright, hwdist, hεa]
    let q : ℂ := ⟨w.re, segmentHeight b a w.re⟩
    have hqseg : q ∈ segment ℝ b a :=
      (mem_segment_iff_height hab).mpr ⟨hwb, hwa, rfl⟩
    have hqp : q ∈ p.image := by
      refine Or.inr ⟨0, hi, ?_⟩
      change q ∈ segment ℝ a b
      rwa [segment_symm]
    have hqf := htrace hqp
    have hwlt : segmentHeight b a w.re < w.im := by
      exact hqf.2.trans_lt (habove w hw hqf.1)
    have hden : a.re - b.re ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hzlin : (a.re - b.re) * (z.im - b.im) =
        (a.im - b.im) * (z.re - b.re) := by
      rw [hzheight.2.2]
      unfold segmentHeight
      field_simp
      ring
    have hflin : (a.re - b.re) * (segmentHeight b a w.re - b.im) =
        (a.im - b.im) * (w.re - b.re) := by
      unfold segmentHeight
      field_simp
      ring
    have hmul := mul_lt_mul_of_pos_left hwlt (sub_pos.mpr hab)
    change (star (b - a) * (w - z)).im < 0
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith only [hmul, hzlin, hflin]
  intro h
  exact intrinsicBetween5_not_leftAtOn_of_locally_right p hlen hsimple F hdisj hi hz
    s rfl ε hε hright (h s)

/-- Helper toward Proposition 3.9: a set strictly above a west-to-east
simple graph arc cannot touch the left side of its reversed traversal,
that is, the right side of the directed arc. -/
theorem intrinsicConsumersFinal_not_forall_reverse_leftAtOn_of_above_graph
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hsimple : p.IsSimple)
    (hp : p.XMonotone) {D : Set ℝ} {f : ℝ → ℝ}
    (htrace : p.image ⊆ {z : ℂ | z.re ∈ D ∧ z.im = f z.re})
    (F : Set ℂ) (habove : ∀ w ∈ F, w.re ∈ D → f w.re < w.im) :
    ¬ ∀ s, LeftAtOn F p.reverse.toPath s := by
  have hwest : (p.reverse.point 1).re < (p.reverse.point 0).re := by
    rw [p.reverse_point_one hlen, p.reverse.point_zero_eq_start,
      Polyline.start_reverse, ← p.point_last_eq_finish]
    exact p.point_re_lt hp (by omega) (by omega)
  apply intrinsicConsumersFinal_not_forall_leftAtOn_of_above_graph p.reverse
    (by simpa only [Polyline.reverse, List.length_reverse] using hlen)
    (p.isSimple_reverse_transfer hsimple) hwest
  · simpa only [Polyline.image_reverse_transfer] using htrace
  · exact habove

/-- Helper toward Proposition 3.9: an actual source ray cannot touch
its right side from a component strictly above its graph. This is the
second wrong-side exclusion and retains finite limiting abscissas. -/
theorem intrinsicConsumersFinal_source_not_right_of_above_graph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v)
    {D : Set ℝ} {f : ℝ → ℝ}
    (hgraph : intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
        {z : ℂ | z.re ∈ D ∧ z.im = f z.re})
    (F : Set ℂ) (habove : ∀ w ∈ F, w.re ∈ D → f w.re < w.im) :
    ¬ intrinsicRayTouchesSide
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)) F true := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  intro hside
  obtain ⟨n, hn⟩ :=
    (intrinsicBetween_source_ray_touches_side_iff W H h hpast hp P F true).mp hside
  have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hpast H (P.edge n, false)
  change G.arc (wholePlaneDartι W 0 (P.edge n, false)) = M.arc (P.edge n, false) at harc
  have hflip : G.arc (wholePlaneDartι W 0 (P.edge n, true)) =
      (M.arc (P.edge n, false)).reverse := by
    rw [← harc]
    exact G.arc_flip (wholePlaneDartι W 0 (P.edge n, false))
  rw [hflip] at hn
  have htrace : (M.arc (P.edge n, false)).image ⊆
      {z : ℂ | z.re ∈ D ∧ z.im = f z.re} := by
    intro z hz
    rw [← hgraph, intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change z ∈ (G.arc (wholePlaneDartι W 0 (P.edge n, false))).image
    rw [harc]
    exact hz
  have hmono : (M.arc (P.edge n, false)).XMonotone :=
    infinitePresentPath_arc_xMonotone (H.1 0)
      (fun j => ⟨monotoneLayoutDrawing (shiftedStream W 0) j
        ((monotone_family_all (shiftedStream W 0)) j).choose,
        ((monotone_family_all (shiftedStream W 0)) j).choose_spec⟩) P n
  exact intrinsicConsumersFinal_not_forall_reverse_leftAtOn_of_above_graph
    (M.arc (P.edge n, false)) (M.arc_length _) (M.arc_simple _) hmono htrace F habove hn

/-- Helper toward Proposition 3.9: every complementary component inside
the source vertical-fiber region fails both opposite-side winding tests.
The upper and lower ray domains have independently varying endpoints;
no component-classification or positive-incidence premise is introduced. -/
theorem intrinsicConsumersFinal_source_component_wrong_sides
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {vP vR : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) vP)
    (R : InfinitePresentPath (shiftedStream W 0) vR)
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
        {z : ℂ | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (R.edge n)) =
        {z : ℂ | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀)
    {z : ℂ} (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let C := connectedComponentIn
      (intrinsicEdgeRayTrace A pe ∪ intrinsicEdgeRayTrace A re)ᶜ z
    ¬ intrinsicRayTouchesSide A pe C false ∧
      ¬ intrinsicRayTouchesSide A re C true := by
  dsimp only
  have hproperR : ProperGraphRay
      (intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (R.edge n))) x₀ :=
    ⟨XR, fR, hXR, hcR, hR, hescR⟩
  have hsub := intrinsicBetween5_component_subset_strictRegion
    hP hR hXP hcP hcR hescP hproperR hstart hz
  constructor
  · apply intrinsicBetween5_source_not_left_of_below_graph W H h hpast hp P hP
    intro w hw hwd
    exact (hsub hw).2.2.2 hwd
  · apply intrinsicConsumersFinal_source_not_right_of_above_graph W H h hpast hp R hR
    intro w hw _hwd
    exact (hsub hw).2.2.1

/-- Helper toward Proposition 3.9: for any two actual source rays from
the same vertex, every complementary component meeting the vertical-fiber
region away from the traces satisfies both wrong-side exclusions. Proper
graph data and their common start are proved from the paths, not assumed. -/
theorem intrinsicConsumersFinal_source_region_component_wrong_sides
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v) (z : ℂ) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let PT := intrinsicEdgeRayTrace A pe
    let RT := intrinsicEdgeRayTrace A re
    z ∈ closedBetween PT RT \ (PT ∪ RT) →
    let C := connectedComponentIn (PT ∪ RT)ᶜ z
    ¬ intrinsicRayTouchesSide A pe C false ∧
      ¬ intrinsicRayTouchesSide A re C true := by
  dsimp only
  intro hz
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hwest (Q : InfinitePresentPath (shiftedStream W 0) v) :
      edgeWest (shiftedStream W 0) (Q.edge 0) = v.id := by
    have hzero := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
    exact (Q.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
      (congrArg PresentVertex.id hzero.symm)
  have hstartarc : (M.arc (P.edge 0, false)).start =
      (M.arc (R.edge 0, false)).start := by
    rw [M.arc_start, M.arc_start]
    change M.pos (edgeWest (shiftedStream W 0) (P.edge 0)) =
      M.pos (edgeWest (shiftedStream W 0) (R.edge 0))
    rw [hwest P, hwest R]
  have hproperP := intrinsicBetween_source_trace_properGraphRay W H h hpast hp P
  have hproperR := intrinsicBetween_source_trace_properGraphRay W H h hpast hp R
  change ProperGraphRay _ (M.arc (P.edge 0, false)).start.re at hproperP
  change ProperGraphRay _ (M.arc (R.edge 0, false)).start.re at hproperR
  rw [← hstartarc] at hproperR
  obtain ⟨XP, fP, hXP, hcP, hP, hescP⟩ := hproperP
  obtain ⟨XR, fR, hXR, hcR, hR, hescR⟩ := hproperR
  have hmem (Q : InfinitePresentPath (shiftedStream W 0) v) :
      (M.arc (Q.edge 0, false)).start ∈ intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H G hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n)) := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    change (M.arc (Q.edge 0, false)).start ∈
      (G.arc (wholePlaneDartι W 0 (Q.edge 0, false))).image
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
    exact Or.inl rfl
  have hpmem := hmem P
  have hrmem := hmem R
  rw [hP] at hpmem
  rw [hR, ← hstartarc] at hrmem
  have hstart : fP (M.arc (P.edge 0, false)).start.re =
      fR (M.arc (P.edge 0, false)).start.re := hpmem.2.symm.trans hrmem.2
  have hstrict := intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
  have hz' := hstrict ▸ hz
  exact intrinsicConsumersFinal_source_component_wrong_sides W H h hpast hp P R
    hP hR hXP hXR hcP hcR hescP hescR hstart hz'

/-- Helper toward Proposition 3.9: the two source-component exclusions
hold in every representative under every geometric source isomorphism.
The complementary component is taken in the representative itself. -/
theorem intrinsicConsumersFinal_image_region_component_wrong_sides
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v) (z : ℂ) :
    let S := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let PT := intrinsicEdgeRayTrace S pe
    let RT := intrinsicEdgeRayTrace S re
    z ∈ I.h '' (closedBetween PT RT \ (PT ∪ RT)) →
    let C := connectedComponentIn
      (intrinsicEdgeRayTrace A (fun n => I.edgeEquiv (pe n)) ∪
        intrinsicEdgeRayTrace A (fun n => I.edgeEquiv (re n)))ᶜ z
    ¬ intrinsicRayTouchesSide A (fun n => I.edgeEquiv (pe n)) C false ∧
      ¬ intrinsicRayTouchesSide A (fun n => I.edgeEquiv (re n)) C true := by
  dsimp only
  rintro ⟨w, hw, rfl⟩
  let S := uibotWholePlaneSourceDomain W H
    (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
  let pe : ℕ → S.E := fun n => wholePlaneEdgeι W 0 (P.edge n)
  let re : ℕ → S.E := fun n => wholePlaneEdgeι W 0 (R.edge n)
  let T := intrinsicEdgeRayTrace S pe ∪ intrinsicEdgeRayTrace S re
  have hcomp : I.h '' connectedComponentIn Tᶜ w =
      connectedComponentIn
        (intrinsicEdgeRayTrace A (fun n => I.edgeEquiv (pe n)) ∪
          intrinsicEdgeRayTrace A (fun n => I.edgeEquiv (re n)))ᶜ (I.h w) := by
    rw [I.h.image_connectedComponentIn hw.2, I.h.image_compl]
    dsimp only [T]
    rw [← intrinsicBetween_trace_union_map (A := S) (B := A) I pe re]
    rfl
  have hwrong := intrinsicConsumersFinal_source_region_component_wrong_sides
    W H h hpast hp P R w hw
  change ¬ intrinsicRayTouchesSide A (fun n => I.edgeEquiv (pe n)) _ false ∧
    ¬ intrinsicRayTouchesSide A (fun n => I.edgeEquiv (re n)) _ true
  rw [← hcomp]
  exact ⟨fun hs => hwrong.1
      ((intrinsicRayTouchesSide_map (A := S) (B := A) I pe _ false).mp hs),
    fun hs => hwrong.2
      ((intrinsicRayTouchesSide_map (A := S) (B := A) I re _ true).mp hs)⟩















































































































































end DirectedDistances.PaperProofs.Section3
end
