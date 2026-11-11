/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueSeamFaces
public import DirectedDistances.PlanarMap.PLDrawingDartBordersIff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Face correspondence for the glued whole-plane drawing

Helpers toward Q-M0-repr, continuing legal-step convention (past dart-border transfer) with both-mode scope
(the seam converse). These are supporting results, not numbered paper results. -/

public section
namespace DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondence

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open WholePlaneGlueSeamStar WholePlaneGlueSeamMerge WholePlaneGlueSeamSectors

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "vertp" => kmswLimitDartVertex wp

section Seam
variable (k : ℤ)
local notation "x0" => seamX w0 h0 ((And.left H) 0) k





private theorem seam_arc_bounds (j : ℤ) (b : Bool) {z : ℂ}
    (hz : z ∈ ((Pt).arc (boundaryOuterEdge wp hp j, b)).image) :
    seamX w0 h0 (H.1 0) (-j) ≤ z.re ∧
      z.re ≤ seamX w0 h0 (H.1 0) (1 - j) ∧ z.im = f0 z.re := by
  rw [(pastDrawing_arc W h0 hp H _).1] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hqt : q ∈ ((Pp).arc (futureMapBoundaryDart wp hp j)).image := by
    cases b with
    | false =>
      have he := (Pp).arc_flip (boundaryOuterEdge wp hp j, true)
      change (Pp).arc (boundaryOuterEdge wp hp j, false) = _ at he
      rw [he, Polyline.image_reverse_transfer] at hq
      exact hq
    | true => exact hq
  have hgraph : q.im = seamFun wp hp (past_finiteIncidence W H) q.re := by
    change q ∈ {z : ℂ | z.im = seamFun wp hp (past_finiteIncidence W H) z.re}
    rw [seamFun_graph wp hp (past_finiteIncidence W H)]
    exact Set.mem_iUnion.mpr ⟨j, hqt⟩
  obtain ⟨g, hg⟩ := seam_arc_image_graph wp hp (past_finiteIncidence W H) j
  rw [hg] at hqt
  let phi := PastDrawingTransfer.phi w0 wp h0 hp (H.1 0) (past_finiteIncidence W H)
  have hphi (i : ℤ) : phi (seamX wp hp (past_finiteIncidence W H) i) =
      -(seamX w0 h0 (H.1 0) (1 - i)) :=
    PastDrawingTransfer.phi_breakpoint w0 wp h0 hp (H.1 0)
      (past_finiteIncidence W H) i
  have hl := neg_le_neg (phi.monotone hqt.2.1)
  have hr := neg_le_neg (phi.monotone hqt.1)
  rw [hphi, neg_neg, show 1 - (j + 1) = -j by omega] at hl
  rw [hphi, neg_neg] at hr
  refine ⟨hl, hr, ?_⟩
  change -q.im + f0 (-(phi q.re)) +
    seamFun wp hp (past_finiteIncidence W H) q.re = f0 (-(phi q.re))
  linarith only [hgraph]





private theorem seam_arc_args :
    Complex.arg (dir W h0 hp H (dL W h0 k)) =
      Complex.arg ((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).initialDirection ∧
    Complex.arg (dir W h0 hp H (dR W h0 k)) =
      Complex.arg ((Pt).arc (boundaryOuterEdge wp hp (-k), true)).initialDirection := by
  have hstart (d : ℕ × Bool) (hv : vertp d = boundaryVertex wp hp (1 - k)) :
      ((Pt).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    rw [(Pt).arc_start, hv, pastDrawing_seam_pos,
      show 1 - (1 - k) = k by omega]
    exact boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k
  have hw := seamWindow_spec W h0 H k
  have hleftV : vertp (boundaryOuterEdge wp hp (1 - k), false) =
      boundaryVertex wp hp (1 - k) := (boundaryOuterEdge_endpoints wp hp (1 - k)).1
  have hrightV : vertp (boundaryOuterEdge wp hp (-k), true) =
      boundaryVertex wp hp (1 - k) := by
    change edgeEast wp (boundaryOuterEdge wp hp (-k)) = _
    rw [(boundaryOuterEdge_endpoints wp hp (-k)).2.1, show -k + 1 = 1 - k by omega]
  have hdata (j : ℤ) (b : Bool)
      (hv : vertp (boundaryOuterEdge wp hp j, b) = boundaryVertex wp hp (1 - k)) :=
    initialDirection_on_graph_sign f0 x0 (seamWindowR W h0 H k)
      (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
      ((Pt).arc (boundaryOuterEdge wp hp j, b)) (hstart _ hv) ((Pt).arc_length _)
      (fun he => (Pt).initial_nonzero _ (sub_eq_zero.mpr he))
      (fun z hz => (seam_arc_bounds W h0 hp H j b hz).2.2)
  constructor
  · have hd := hdata (1 - k) false hleftV
    have hlen := (Pt).arc_length (boundaryOuterEdge wp hp (1 - k), false)
    have hmem := ((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).point_mem_image
      (i := 1) (by omega)
    have hb := seam_arc_bounds W h0 hp H (1 - k) false hmem
    rw [show 1 - (1 - k) = k by omega] at hb
    have hle : (((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).initialDirection).re
        ≤ 0 := by
      change (((Pt).arc _).point 1).re - (((Pt).arc _).start).re ≤ 0
      rw [hstart _ hleftV]
      exact sub_nonpos.mpr hb.2.1
    obtain ⟨c, hc, he⟩ := hd.2.1 (lt_of_le_of_ne hle hd.2.2)
    obtain ⟨a, ha, hea⟩ := dir_dL W h0 hp H k
    rw [hea, he, Complex.arg_real_mul _ ha, Complex.arg_real_mul _ hc]
  · have hd := hdata (-k) true hrightV
    have hlen := (Pt).arc_length (boundaryOuterEdge wp hp (-k), true)
    have hmem := ((Pt).arc (boundaryOuterEdge wp hp (-k), true)).point_mem_image
      (i := 1) (by omega)
    have hb := seam_arc_bounds W h0 hp H (-k) true hmem
    rw [neg_neg] at hb
    have hle : 0 ≤ (((Pt).arc (boundaryOuterEdge wp hp (-k), true)).initialDirection).re := by
      change 0 ≤ (((Pt).arc _).point 1).re - (((Pt).arc _).start).re
      rw [hstart _ hrightV]
      exact sub_nonneg.mpr hb.1
    obtain ⟨c, hc, he⟩ := hd.1 (lt_of_le_of_ne hle (Ne.symm hd.2.2))
    obtain ⟨a, ha, hea⟩ := dir_dR W h0 hp H k
    rw [hea, he, Complex.arg_real_mul _ ha, Complex.arg_real_mul _ hc]





private theorem past_arc_arg_at_boundary (d : ℕ × Bool)
    (hv : vertp d = boundaryVertex wp hp (1 - k)) :
    Complex.arg (dir W h0 hp H (kmswPastDart W d)) =
      Complex.arg ((Pt).arc d).initialDirection := by
  by_cases hn : kmswPastSeamEdge W d.1
  · obtain ⟨j, hj⟩ := kmswPastSeamEdge_image_boundary W h0 d.1 hn
    have he : d.1 = boundaryOuterEdge wp hp (-j) := by
      apply kmswPastEdge_injective W
      rw [hj, kmswPastEdge_seam_match_neg W h0 hp (-j), neg_neg]
    rcases past_seam_darts W hp k d hv ⟨-j, he⟩ with rfl | rfl
    · rw [(past_seam_representatives W h0 hp k).1]
      exact (seam_arc_args W h0 hp H k).1
    · rw [(past_seam_representatives W h0 hp k).2]
      exact (seam_arc_args W h0 hp H k).2
  · rw [dir, gluedArc_past W h0 hp H d hn]

end Seam

/-- Helper toward Q-M0-repr; not a paper result. Every embedded past dart,
including seam darts, has the same initial argument in the glued drawing. -/
theorem past_arc_arg (d : ℕ × Bool) :
    Complex.arg ((G).arc (kmswPastDart W d)).initialDirection =
      Complex.arg ((Pt).arc d).initialDirection := by
  by_cases hs : kmswPastSeamEdge W d.1
  · obtain ⟨j, hj⟩ := kmswPastSeamEdge_image_boundary W h0 d.1 hs
    have he : d.1 = boundaryOuterEdge wp hp (-j) := by
      apply kmswPastEdge_injective W
      rw [hj, kmswPastEdge_seam_match_neg W h0 hp (-j), neg_neg]
    have hv : ∃ k : ℤ, vertp d = boundaryVertex wp hp (1 - k) := by
      cases hb : d.2
      · refine ⟨1 + j, ?_⟩
        simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ite_false, he,
          show 1 - (1 + j) = -j by omega] using (boundaryOuterEdge_endpoints wp hp (-j)).1
      · refine ⟨j, ?_⟩
        simpa only [kmswLimitDartVertex, hb, ite_true, he,
          show -j + 1 = 1 - j by omega] using (boundaryOuterEdge_endpoints wp hp (-j)).2.1
    obtain ⟨k, hk⟩ := hv
    exact past_arc_arg_at_boundary W h0 hp H k d hk
  · change Complex.arg (gluedArc W h0 hp H (kmswPastDart W d)).initialDirection = _
    rw [gluedArc_past W h0 hp H d hs]

/-- Helper toward Q-M0-repr; not a paper result. Positive scaling of a
left-wedge direction preserves eventual membership in any set. -/
private theorem wedge_of_pos_mul (p u : ℂ) (S : Set ℂ) (c : ℝ) (hc : 0 < c)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ t eps : ℝ,
      0 < t → t < δ → 0 < eps → eps < δ →
      p + (t : ℂ) * (u + (eps : ℂ) * Complex.I * u) ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t eps : ℝ,
      0 < t → t < δ → 0 < eps → eps < δ →
      p + (t : ℂ) * ((c : ℂ) * u +
        (eps : ℂ) * Complex.I * ((c : ℂ) * u)) ∈ S := by
  obtain ⟨δ, hδ, hw⟩ := h
  refine ⟨min δ (δ / c), lt_min hδ (div_pos hδ hc), ?_⟩
  intro t eps ht htδ he heδ
  have htc : t * c < δ :=
    (lt_div_iff₀ hc).mp (htδ.trans_le (min_le_right _ _))
  have hm := hw (t * c) eps (mul_pos ht hc) htc he
    (heδ.trans_le (min_le_left _ _))
  have heq : p + (t : ℂ) * ((c : ℂ) * u +
      (eps : ℂ) * Complex.I * ((c : ℂ) * u)) =
      p + ((t * c : ℝ) : ℂ) * (u + (eps : ℂ) * Complex.I * u) := by
    rw [Complex.ofReal_mul]
    ring
  rw [heq]
  exact hm

/-- Helper toward Q-M0-repr; not a paper result. Every past dart, including
seam darts, borders the transferred face exactly when its glued image does.
The face-set equality is identification data, not an additional geometric premise. -/
theorem past_dartBorders_iff (d : ℕ × Bool) (Fp : (Pp).Face)
    (F : (G).Face) (hF : F.val = T '' Fp.val) :
    (G).dartBorders (kmswPastDart W d) F ↔ (Pp).dartBorders d Fp := by
  obtain ⟨Ft, hFt, hb⟩ := pastDrawing_dartBorders_face_exists W h0 hp H d Fp
  have hs : ((G).arc (kmswPastDart W d)).start = ((Pt).arc d).start := by
    rw [(G).arc_start, pastDart_vertex, (Pt).arc_start]
    exact gluedPos_pastDrawing W h0 hp H _
  have ha := past_arc_arg W h0 hp H d
  let u := ((G).arc (kmswPastDart W d)).initialDirection
  let v := ((Pt).arc d).initialDirection
  have hu : u ≠ 0 := (G).initial_nonzero _
  have hv : v ≠ 0 := (Pt).initial_nonzero _
  let c : ℝ := ‖v‖ / ‖u‖
  have hscale : v = (c : ℂ) * u := by
    simpa only [c, Complex.ofReal_div] using
      ((Complex.arg_eq_arg_iff hu hv).mp ha).symm
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu)
  have hinv : u = ((1 / c : ℝ) : ℂ) * v := by
    rw [hscale, Complex.ofReal_div, Complex.ofReal_one, one_div, inv_mul_cancel_left₀]
    exact_mod_cast (ne_of_gt hc)
  have hface : F.val = Ft.val := hF.trans hFt.symm
  rw [← hb]
  constructor
  · intro hd
    have hw := wedge_of_pos_mul _ u F.val c hc hd
    change ∃ δ : ℝ, 0 < δ ∧ ∀ t eps : ℝ,
      0 < t → t < δ → 0 < eps → eps < δ →
      ((Pt).arc d).start + (t : ℂ) *
        (v + (eps : ℂ) * Complex.I * v) ∈ Ft.val
    rw [hscale, ← hs, ← hface]
    exact hw
  · intro hd
    have hw := wedge_of_pos_mul _ v Ft.val (1 / c) (one_div_pos.mpr hc) hd
    change ∃ δ : ℝ, 0 < δ ∧ ∀ t eps : ℝ,
      0 < t → t < δ → 0 < eps → eps < δ →
      ((G).arc (kmswPastDart W d)).start + (t : ℂ) *
        (u + (eps : ℂ) * Complex.I * u) ∈ F.val
    rw [hinv, hs, hface]
    exact hw

/-- both-mode scope of the glued face correspondence, toward Q-M0-repr; not a paper result.
A run-zero outer seam dart borders exactly the transferred bounded past face
bordered by its paired past dart. -/
theorem runZero_outer_dartBorders_iff (k : ℤ) (Fp : (Pp).Face)
    (F : (G).Face) (hF : F.val = T '' Fp.val) :
    (G).dartBorders (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k)) F ↔
      (Pp).dartBorders (boundaryOuterEdge wp hp (-k), false) Fp := by
  rw [(wholePlaneDart_runZero_outer_splice W H
    (past_finiteIncidence W H) hp h0 k).1]
  exact past_dartBorders_iff W h0 hp H _ Fp F hF

/-- both-mode scope existence and converse, toward Q-M0-repr; not a paper result.
Each run-zero outer seam dart actually borders its identified transferred past face. -/
theorem runZero_outer_dartBorders_exists (k : ℤ) :
    ∃ Fp : (Pp).Face, ∃ F : (G).Face,
      ¬ (Pp).IsUnbounded Fp ∧
      (Pp).dartBorders (boundaryOuterEdge wp hp (-k), false) Fp ∧
      F.val = T '' Fp.val ∧
      (G).dartBorders (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k)) F := by
  obtain ⟨Fp, F, hFp, hdFp, hF, _⟩ :=
    WholePlaneGlueSeamFaces.glueSeamFaces_past_outer_dart_has_bounded_sourceFace W h0 hp H k
  exact ⟨Fp, F, hFp, hdFp, hF,
    (runZero_outer_dartBorders_iff W h0 hp H k Fp F hF).mpr hdFp⟩

end DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondence
