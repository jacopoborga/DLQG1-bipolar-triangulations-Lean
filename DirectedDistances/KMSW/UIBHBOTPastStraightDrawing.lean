/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTHalfPlaneGlueDrawing
public import DirectedDistances.PlanarMap.PLDrawingTransfer
public import DirectedDistances.PlanarMap.PastTransferMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Straightening the one-sided conditioned past seam

Extend the persistent lower graph constantly to the right of its endpoint,
then straighten and rotate it by an orientation-preserving PL homeomorphism. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5 Set
open scoped Topology

noncomputable section

variable (W : ℤ → Fin 3)
variable (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
variable (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)

/-- The uniquely characterized seam height, extended constantly beyond its endpoint. -/
@[expose] def uibhbotPastSeamHeight (x : ℝ) : ℝ :=
  (uibhbotPastSeamGraph_existsUnique_height W hL hR (min x 1) (min_le_right _ _)).choose

/-- The chosen height is on the persistent seam at the capped abscissa. -/
theorem uibhbotPastSeamHeight_mem (x : ℝ) :
    (⟨min x 1, uibhbotPastSeamHeight W hL hR x⟩ : ℂ) ∈ uibhbotPastSeamGraph W :=
  (uibhbotPastSeamGraph_existsUnique_height W hL hR (min x 1)
    (min_le_right _ _)).choose_spec.1

/-- The extension agrees with every finite lower graph on its domain. -/
theorem uibhbotPastSeamHeight_eq_lower (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (familyG (kmswPastCode W) (monotone_family_all _) n).xmin
      (familyG (kmswPastCode W) (monotone_family_all _) n).xmax) :
    uibhbotPastSeamHeight W hL hR x =
      (familyG (kmswPastCode W) (monotone_family_all _) n).lower x := by
  have hx1 : x ≤ 1 := by
    simpa only [uibhbotPastStage_xmax_eq_one W hR n] using hx.2
  have hh := uibhbotPastSeamHeight_mem W hL hR x
  rw [min_eq_left hx1] at hh
  exact ((uibhbotPastSeamGraph_existsUnique_height W hL hR x hx1).unique hh
    (mem_iUnion.mpr ⟨n, hx.1, hx.2, rfl⟩))

/-- A seam point has exactly the chosen height. -/
theorem uibhbotPastSeamHeight_eq_of_mem {z : ℂ} (hz : z ∈ uibhbotPastSeamGraph W) :
    z.im = uibhbotPastSeamHeight W hL hR z.re := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  exact hn.2.2.trans (uibhbotPastSeamHeight_eq_lower W hL hR n z.re
    ⟨hn.1, hn.2.1⟩).symm

/-- The extension is constant on the right half-line. -/
theorem uibhbotPastSeamHeight_right (x : ℝ) (hx : 1 ≤ x) :
    uibhbotPastSeamHeight W hL hR x = uibhbotPastSeamHeight W hL hR 1 := by
  unfold uibhbotPastSeamHeight
  simp only [min_eq_right hx, min_self]

include hL hR in
/-- Every capped abscissa has a stage with a strictly smaller left endpoint. -/
private theorem straight_stage_at (x : ℝ) :
    ∃ n, (familyG (kmswPastCode W) (monotone_family_all _) n).xmin < min x 1 := by
  obtain ⟨n, hn⟩ := uibhbotPastStage_seam_interval_cover W hL hR
    (min x 1 - 1) (by linarith only [min_le_right x (1 : ℝ)])
  exact ⟨n, lt_of_le_of_lt hn.1 (by linarith)⟩

/-- The constant extension is continuous, including at its right endpoint. -/
theorem uibhbotPastSeamHeight_continuous : Continuous (uibhbotPastSeamHeight W hL hR) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n, hn⟩ := straight_stage_at W hL hR x
  let G := familyG (kmswPastCode W) (monotone_family_all _) n
  have hc : Continuous (fun y : ℝ => min y 1) := continuous_id.min continuous_const
  have hnh : ∀ᶠ y in nhds x, G.xmin < min y 1 :=
    (isOpen_lt continuous_const hc).mem_nhds hn
  have hmap : Set.MapsTo (fun y : ℝ => min y 1) (Ioi G.xmin) (Icc G.xmin G.xmax) := by
    intro y hy
    refine ⟨?_, ?_⟩
    · exact le_min (le_of_lt hy) (hn.le.trans (min_le_right _ _))
    · rw [uibhbotPastStage_xmax_eq_one W hR n]
      exact min_le_right _ _
  have hlocal : ContinuousOn (fun y : ℝ => G.lower (min y 1)) (Ioi G.xmin) :=
    G.lower_continuous.comp hc.continuousOn hmap
  have hxmin : G.xmin < x := hn.trans_le (min_le_left _ _)
  apply (hlocal.continuousAt (Ioi_mem_nhds hxmin)).congr_of_eventuallyEq
  filter_upwards [hnh] with y hy
  have hyI : min y 1 ∈ Icc G.xmin G.xmax := by
    refine ⟨hy.le, ?_⟩
    rw [uibhbotPastStage_xmax_eq_one W hR n]
    exact min_le_right _ _
  have heq : uibhbotPastSeamHeight W hL hR y =
      uibhbotPastSeamHeight W hL hR (min y 1) := by
    unfold uibhbotPastSeamHeight
    simp only [min_assoc, min_self]
  exact heq.trans (uibhbotPastSeamHeight_eq_lower W hL hR n _ hyI)

/-- Every lower edge trace lies on the persistent seam. -/
theorem uibhbotPastMonotoneDrawing_lower_arc_subset (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (n e : ℕ) (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    ((uibhbotPastMonotoneDrawing W hfin).arc (e, false)).image ⊆ uibhbotPastSeamGraph W := by
  have heb : e < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge _ n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
  intro z hz
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e heb false] at hz
  let hg := familyG (kmswPastCode W) (monotone_family_all _) n
  have ha := hg.arc_layout (⟨e, heb⟩, false)
  simp only [Bool.false_eq_true, ite_false] at ha
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  rw [hg.lower_trace]
  exact mem_iUnion₂.mpr ⟨e, he, by
    simpa only [stageEdgeTrace, dite_eq_left heb, ha, Bool.false_eq_true, ite_false] using hz⟩

/-- Every seam point lies on some lower edge in the limit drawing. -/
theorem uibhbotPastSeamGraph_mem_arc (hfin : KMSWFiniteIncidence (kmswPastCode W))
    {z : ℂ} (hz : z ∈ uibhbotPastSeamGraph W) :
    ∃ e, (∃ n, e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) ∧
      z ∈ ((uibhbotPastMonotoneDrawing W hfin).arc (e, false)).image := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  rw [(familyG (kmswPastCode W) (monotone_family_all _) n).lower_trace] at hn
  obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hn
  have heb : e < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge _ n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
  refine ⟨e, ⟨n, he⟩, ?_⟩
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e heb false]
  have ha := (familyG (kmswPastCode W) (monotone_family_all _) n).arc_layout
    (⟨e, heb⟩, false)
  simpa only [stageEdgeTrace, dite_eq_left heb, ha, Bool.false_eq_true, ite_false] using hz

variable (hfin : KMSWFiniteIncidence (kmswPastCode W))

/-- The cuts are exactly the listed lower-edge abscissas, together with the endpoint. -/
@[expose] def uibhbotPastSeamCuts : Set ℝ :=
  insert 1 {x | ∃ e, (∃ n, e ∈ (kmswStage (kmswPastCode W) n).LL ++
    (kmswStage (kmswPastCode W) n).LR) ∧
    ∃ z ∈ ((uibhbotPastMonotoneDrawing W hfin).arc (e, false)).points, z.re = x}

/-- A listed polyline point belongs to the polyline image. -/
private theorem straight_point_mem_image (p : Polyline) {z : ℂ} (hz : z ∈ p.points) :
    z ∈ p.image := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  have heq : p.point i.val = z := by
    change p.points.getD i.val p.start = z
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact hi
  rw [← heq]
  exact Polyline.point_mem_image p i.isLt

include hL hR in
/-- There are finitely many lower-seam cuts in every bounded horizontal interval. -/
theorem uibhbotPastSeamCuts_inter_Icc_finite (s t : ℝ) :
    (uibhbotPastSeamCuts W hfin ∩ Icc s t).Finite := by
  classical
  let P := uibhbotPastMonotoneDrawing W hfin
  let f := uibhbotPastSeamHeight W hL hR
  let g : ℝ → ℂ := fun x => ⟨x, f x⟩
  have hg : Continuous g := by
    dsimp [g]
    simp_rw [Complex.mk_eq_add_mul_I]
    exact Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp (uibhbotPastSeamHeight_continuous W hL hR)).mul continuous_const)
  let K := g '' Icc s t
  have hK : Bornology.IsBounded K := (isCompact_Icc.image hg).isBounded
  let D := {d | (K ∩ (P.arc d).image).Nonempty}
  have hD : D.Finite := P.locally_finite K hK
  have hB : (⋃ d ∈ D, Complex.re '' (↑(P.arc d).points.toFinset : Set ℂ)).Finite :=
    hD.biUnion (fun d _ => (P.arc d).points.toFinset.finite_toSet.image Complex.re)
  apply (hB.insert 1).subset
  rintro x ⟨hx, hxt⟩
  rcases hx with rfl | ⟨e, ⟨n, he⟩, z, hz, rfl⟩
  · exact mem_insert 1 _
  · have hzarc : z ∈ (P.arc (e, false)).image := straight_point_mem_image _ hz
    have hzseam := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n e he hzarc
    have hzh : z.im = f z.re := uibhbotPastSeamHeight_eq_of_mem W hL hR hzseam
    have hzK : z ∈ K := ⟨z.re, hxt, Complex.ext rfl hzh.symm⟩
    apply mem_insert_of_mem
    exact mem_iUnion₂.mpr ⟨(e, false), ⟨z, hzK, hzarc⟩,
      ⟨z, List.mem_toFinset.mpr hz, rfl⟩⟩

/-- Elementary affine geometry for seam straightening. -/
private theorem straight_affine_point_mem (p : Polyline) (i : ℕ) (hi : i < p.points.length) :
    p.point i ∈ p.points := by
  change p.points.getD i p.start ∈ p.points
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- Elementary affine geometry for seam straightening. -/
private theorem straight_affine_segment_spans {a b z : ℂ} {s t : ℝ}
    (hz : z ∈ segment ℝ a b) (hmid : z.re ∈ Ioo s t)
    (ha : a.re ∉ Ioo s t) (hb : b.re ∉ Ioo s t) :
    (a.re ≤ s ∧ t ≤ b.re) ∨ (b.re ≤ s ∧ t ≤ a.re) := by
  by_cases hab : a.re ≤ b.re
  · have hbounds := Polyline.segment_re_bounds hab hz
    left
    constructor
    · exact le_of_not_gt (fun hs => ha ⟨hs, hbounds.1.trans_lt hmid.2⟩)
    · exact le_of_not_gt (fun ht => hb ⟨hmid.1.trans_le hbounds.2, ht⟩)
  · have hz' : z ∈ segment ℝ b a := by
      rwa [segment_symm]
    have hbounds := Polyline.segment_re_bounds (le_of_not_ge hab) hz'
    right
    constructor
    · exact le_of_not_gt (fun hs => hb ⟨hs, hbounds.1.trans_lt hmid.2⟩)
    · exact le_of_not_gt (fun ht => ha ⟨hmid.1.trans_le hbounds.2, ht⟩)

/-- Elementary affine geometry for seam straightening. -/
private theorem straight_affine_of_segment_graph (f : ℝ → ℝ) (a b : ℂ) (s t : ℝ)
    (hst : s < t) (ha : a.re ≤ s) (hb : t ≤ b.re)
    (hgraph : ∀ z ∈ segment ℝ a b, z.im = f z.re) :
    ∃ m c0 : ℝ, ∀ x ∈ Icc s t, f x = m * x + c0 := by
  have hdx : 0 < b.re - a.re := by linarith only [hst, ha, hb]
  let m := (b.im - a.im) / (b.re - a.re)
  let c0 := a.im - m * a.re
  refine ⟨m, c0, ?_⟩
  intro x hx
  let r := (x - a.re) / (b.re - a.re)
  let z : ℂ := (1 - r) • a + r • b
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr (ha.trans hx.1)) hdx.le
    · exact (div_le_one hdx).mpr (by linarith only [hx.2, hb])
  have hz : z ∈ segment ℝ a b := by
    rw [segment_eq_image]
    exact ⟨r, hr, rfl⟩
  have hrx : r * (b.re - a.re) = x - a.re := div_mul_cancel₀ _ hdx.ne'
  have hre : z.re = x := by
    dsimp [z]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hrx]
  have him : z.im = m * x + c0 := by
    have hmul : r * (b.im - a.im) = m * (x - a.re) := by
      dsimp [r, m]
      ring
    dsimp [z, c0]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    linarith only [hmul]
  have hh := hgraph z hz
  rw [hre] at hh
  exact hh.symm.trans him

/-- The extended seam is affine between consecutive cuts, including strip endpoints. -/
theorem uibhbotPastSeamHeight_affine_of_noCut (s t : ℝ) (hst : s < t)
    (hno : ∀ c ∈ uibhbotPastSeamCuts W hfin, c ∉ Ioo s t) :
    ∃ m c0 : ℝ, ∀ x ∈ Icc s t, uibhbotPastSeamHeight W hL hR x = m * x + c0 := by
  by_cases hs : 1 ≤ s
  · refine ⟨0, uibhbotPastSeamHeight W hL hR 1, ?_⟩
    intro x hx
    simpa only [zero_mul, zero_add] using
      uibhbotPastSeamHeight_right W hL hR x (hs.trans hx.1)
  have ht : t ≤ 1 := le_of_not_gt (fun ht =>
    hno 1 (Or.inl rfl) ⟨lt_of_not_ge hs, ht⟩)
  let q := (s + t) / 2
  let z : ℂ := ⟨q, uibhbotPastSeamHeight W hL hR q⟩
  have hmid : z.re ∈ Ioo s t := by
    change s < (s + t) / 2 ∧ (s + t) / 2 < t
    constructor <;> linarith only [hst]
  have hq1 : q ≤ 1 := hmid.2.le.trans ht
  have hzgraph : z ∈ uibhbotPastSeamGraph W := by
    have hh := uibhbotPastSeamHeight_mem W hL hR q
    rwa [min_eq_left hq1] at hh
  obtain ⟨e, he, hz⟩ := uibhbotPastSeamGraph_mem_arc W hfin hzgraph
  let p := (uibhbotPastMonotoneDrawing W hfin).arc (e, false)
  have hcut : ∀ v ∈ p.points, v.re ∈ uibhbotPastSeamCuts W hfin :=
    fun v hv => Or.inr ⟨e, he, v, hv, rfl⟩
  have himage : ∀ v ∈ p.image, v.im = uibhbotPastSeamHeight W hL hR v.re := by
    obtain ⟨n, hn⟩ := he
    intro v hv
    exact uibhbotPastSeamHeight_eq_of_mem W hL hR
      (uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n e hn hv)
  change z ∈ p.image at hz
  rcases hz with hzstart | ⟨i, hi, hzseg⟩
  · have heq : z = p.start := hzstart
    have hc := hcut p.start (List.head_mem p.nonempty)
    exact (hno z.re (heq.symm ▸ hc) hmid).elim
  · have ha := straight_affine_point_mem p i (by omega)
    have hb := straight_affine_point_mem p (i + 1) hi
    have hspan := straight_affine_segment_spans hzseg hmid
      (hno _ (hcut _ ha)) (hno _ (hcut _ hb))
    have hg : ∀ v ∈ segment ℝ (p.point i) (p.point (i + 1)),
        v.im = uibhbotPastSeamHeight W hL hR v.re := by
      intro v hv
      exact himage v (Or.inr ⟨i, hi, hv⟩)
    rcases hspan with hspan | hspan
    · exact straight_affine_of_segment_graph (uibhbotPastSeamHeight W hL hR)
        _ _ s t hst hspan.1 hspan.2 hg
    · apply straight_affine_of_segment_graph (uibhbotPastSeamHeight W hL hR)
        (p.point (i + 1)) (p.point i) s t hst hspan.1 hspan.2
      intro v hv
      exact hg v (by rwa [segment_symm])

/-- The orientation-preserving map straightening and rotating the past seam. -/
@[expose] def uibhbotPastStraightTransfer : ℂ ≃ₜ ℂ :=
  pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) (uibhbotPastSeamHeight W hL hR)
    continuous_const (uibhbotPastSeamHeight_continuous W hL hR)

/-- The straightening map has positive determinant on every cut-free strip. -/
theorem uibhbotPastStraightTransfer_affine (s t : ℝ) (hst : s < t)
    (hno : ∀ c ∈ uibhbotPastSeamCuts W hfin, c ∉ Ioo s t) :
    ∃ m0 m1 c0 c1 : ℝ, 0 < m0 ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
      uibhbotPastStraightTransfer W hL hR z =
        ⟨-(m0 * z.re) + c0, -z.im + m1 * z.re + c1⟩ := by
  obtain ⟨m, c, hf⟩ := uibhbotPastSeamHeight_affine_of_noCut W hL hR hfin s t hst hno
  refine ⟨1, m, 0, c, zero_lt_one, ?_⟩
  intro z hs ht
  change (⟨-z.re, -z.im + 0 + uibhbotPastSeamHeight W hL hR z.re⟩ : ℂ) = _
  rw [hf z.re ⟨hs, ht⟩]
  apply Complex.ext <;> dsimp <;> ring

/-- Every past arc is horizontally monotone in one of its orientations. -/
theorem uibhbotPastMonotoneDrawing_arc_monotone (d : ℕ × Bool) :
    ((uibhbotPastMonotoneDrawing W hfin).arc d).XMonotone ∨
      ((uibhbotPastMonotoneDrawing W hfin).arc d).reverse.XMonotone := by
  rcases d with ⟨e, b⟩
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin e e
    (kmsw_edge_allocated_by_self (kmswPastCode W) e) b]
  cases b
  · exact Or.inl (layoutArc_points_pairwise _ e e (kmsw_edge_allocated_by_self _ e))
  · right
    change (layoutArc (kmswPastCode W) e e).reverse.reverse.XMonotone
    rw [Polyline.reverse_reverse]
    exact layoutArc_points_pairwise _ e e (kmsw_edge_allocated_by_self _ e)

/-- Straightening gives a PL drawing with the same rotation and exact transported geometry. -/
theorem uibhbotPastStraightDrawing_exists :
    ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
      P.pos = uibhbotPastStraightTransfer W hL hR ∘ (uibhbotPastMonotoneDrawing W hfin).pos ∧
      ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
        ((uibhbotPastMonotoneDrawing W hfin).arc d).image := by
  obtain ⟨P, hp, ha⟩ := PLDrawing.transfer (uibhbotPastMonotoneDrawing W hfin)
    (uibhbotPastMonotoneDrawing_arc_monotone W hfin)
    (uibhbotPastStraightTransfer W hL hR) (uibhbotPastSeamCuts W hfin)
    (uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin)
    (uibhbotPastStraightTransfer_affine W hL hR hfin)
  exact ⟨P, hp, fun d => (ha d).1⟩

/-- The lower-edge endpoint positions lie on the persistent seam. -/
theorem uibhbotPastMonotoneDrawing_seam_endpoint_mem (n e : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    (uibhbotPastMonotoneDrawing W hfin).pos ((kmswStage (kmswPastCode W) n).west e) ∈
        uibhbotPastSeamGraph W ∧
      (uibhbotPastMonotoneDrawing W hfin).pos ((kmswStage (kmswPastCode W) n).east e) ∈
        uibhbotPastSeamGraph W := by
  have heb : e < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge _ n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
  obtain ⟨hw, ht, _⟩ := uibhbotPastMonotoneDrawing_seam_endpoints W hfin n e he
  rw [hw, ht]
  have hsub : (layoutArc (kmswPastCode W) n e).image ⊆ uibhbotPastSeamGraph W := by
    have hh := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n e he
    simpa only [uibhbotPastMonotoneDrawing_arc_layout W hfin n e heb false,
      Bool.false_eq_true, ite_false] using hh
  constructor
  · apply hsub
    rw [← layoutArc_start (kmswPastCode W) n e heb]
    exact Or.inl rfl
  · apply hsub
    rw [← layoutArc_finish (kmswPastCode W) n e heb,
      ← Polyline.point_last_eq_finish]
    exact Polyline.point_mem_image _ (by
      have := List.length_pos_iff.mpr (layoutArc (kmswPastCode W) n e).nonempty
      omega)

include hL hR in
/-- The straightened past drawing is below the real line and every lower-seam
endpoint has exactly its negated finite-stage rank and height zero. -/
theorem uibhbotPastStraightDrawing_halfPlane :
    ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
      P.image ⊆ {z : ℂ | z.im ≤ 0} ∧
      ∀ n e, let s := kmswStage (kmswPastCode W) n
        e ∈ s.LL ++ s.LR →
          P.pos (s.west e) = ⟨-(kmswStageRank (kmswPastCode W) n (s.west e) : ℝ), 0⟩ ∧
          P.pos (s.east e) = ⟨-(kmswStageRank (kmswPastCode W) n (s.east e) : ℝ), 0⟩ := by
  obtain ⟨P, hp, ha⟩ := uibhbotPastStraightDrawing_exists W hL hR hfin
  let P0 := uibhbotPastMonotoneDrawing W hfin
  let T := uibhbotPastStraightTransfer W hL hR
  have him : ∀ z ∈ P0.image, (T z).im ≤ 0 := by
    intro z hz
    have hx : z.re ≤ 1 := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hz
    have hseam := uibhbotPastSeamHeight_mem W hL hR z.re
    rw [min_eq_left hx] at hseam
    have hbelow := uibhbotPastMonotoneDrawing_above_seam W hfin hz hseam
    change -z.im + 0 + uibhbotPastSeamHeight W hL hR z.re ≤ 0
    linarith only [hbelow]
  refine ⟨P, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
    · rw [hp]
      exact him (P0.pos v) (Or.inl ⟨v, rfl⟩)
    · rw [ha d] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact him y (Or.inr ⟨d, hy⟩)
  · intro n e
    dsimp only
    intro he
    obtain ⟨hw, ht, _⟩ := uibhbotPastMonotoneDrawing_seam_endpoints W hfin n e he
    obtain ⟨hws, hts⟩ := uibhbotPastMonotoneDrawing_seam_endpoint_mem W hfin n e he
    have hyw := uibhbotPastSeamHeight_eq_of_mem W hL hR hws
    have hyt := uibhbotPastSeamHeight_eq_of_mem W hL hR hts
    rw [hp]
    dsimp only [Function.comp_apply]
    constructor
    · change (⟨-((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).west e)).re,
          -((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).west e)).im + 0 +
          uibhbotPastSeamHeight W hL hR
          ((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).west e)).re⟩ : ℂ) = _
      rw [← hyw, hw]
      apply Complex.ext <;> dsimp [layoutPos]; ring
    · change (⟨-((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).east e)).re,
          -((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).east e)).im + 0 +
          uibhbotPastSeamHeight W hL hR
          ((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).east e)).re⟩ : ℂ) = _
      rw [← hyt, ht]
      apply Complex.ext <;> dsimp [layoutPos]; ring

/-- Almost surely the conditioned past has a PL drawing in the closed lower
half-plane, with every stage lower-seam endpoint at its exact negated rank. -/
theorem uibhbotCodeLawRel_ae_past_straightDrawing :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hfin : KMSWFiniteIncidence (kmswPastCode W),
      ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
        P.image ⊆ {z : ℂ | z.im ≤ 0} ∧
        ∀ n e, let s := kmswStage (kmswPastCode W) n
          e ∈ s.LL ++ s.LR →
            P.pos (s.west e) = ⟨-(kmswStageRank (kmswPastCode W) n (s.west e) : ℝ), 0⟩ ∧
            P.pos (s.east e) = ⟨-(kmswStageRank (kmswPastCode W) n (s.east e) : ℝ), 0⟩ := by
  filter_upwards [uibhbotCodeLawRel_ae_past_finiteIncidence,
    uibhbotCodeLawRel_ae_past_leftHit, uibhbotCodeLawRel_ae_past_R_nonneg] with W hfin hL hR
  exact ⟨hfin, uibhbotPastStraightDrawing_halfPlane W hL hR.1 hfin⟩

end
end DirectedDistances.KMSW
