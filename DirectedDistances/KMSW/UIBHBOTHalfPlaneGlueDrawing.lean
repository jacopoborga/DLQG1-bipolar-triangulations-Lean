/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTClosedHalfPlaneDrawing
public import DirectedDistances.KMSW.MonotoneSeamStabilization
import DirectedDistances.KMSW.AllocatedVertices

/-! # The conditioned past drawing before seam straightening

The monotone union gives an actual locally finite PL drawing on the past dart
and vertex carriers, without a past `BoundaryHitWitnesses` premise. All its
geometry is in the closed upper half-plane, with exact finite-stage positions
and arcs. Its lower seam is a coherent piecewise linear graph, not yet a line.
Straightening that graph and gluing it to the future remain separate obligations. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5 Set

noncomputable section

/-- The monotone drawing of the past, using only finite geometric incidence. -/
@[expose] def uibhbotPastMonotoneDrawing (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)) :=
  monotoneFamilyDrawing (kmswPastCode W) hfin (monotone_family_all (kmswPastCode W))

/-- Every allocated past vertex retains its explicit finite-stage coordinates. -/
theorem uibhbotPastMonotoneDrawing_pos_layout (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (n v : ℕ)
    (hv : v < (kmswStage (kmswPastCode W) n).nextVertex) :
    (uibhbotPastMonotoneDrawing W hfin).pos v =
      ⟨(kmswStageRank (kmswPastCode W) n v : ℝ),
        layoutHeight (kmswPastCode W) n v⟩ :=
  monotoneLimitDrawing_pos_layout (kmswPastCode W) hfin
    (fun m => ⟨familyQ (kmswPastCode W) (monotone_family_all _) m,
      ⟨familyG (kmswPastCode W) (monotone_family_all _) m⟩⟩) n v hv

/-- Both orientations of each geometric edge, including missing edges, retain their
finite-stage polylines. -/
theorem uibhbotPastMonotoneDrawing_arc_layout (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (n e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) n).nextEdge) (b : Bool) :
    (uibhbotPastMonotoneDrawing W hfin).arc (e, b) =
      if b then (layoutArc (kmswPastCode W) n e).reverse
      else layoutArc (kmswPastCode W) n e :=
  monotoneLimitDrawing_arc_layout (kmswPastCode W) hfin
    (fun m => ⟨familyQ (kmswPastCode W) (monotone_family_all _) m,
      ⟨familyG (kmswPastCode W) (monotone_family_all _) m⟩⟩) n e he b

/-- All past vertices have nonnegative height. -/
theorem uibhbotPastMonotoneDrawing_pos_im_nonneg (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (v : ℕ) :
    0 ≤ ((uibhbotPastMonotoneDrawing W hfin).pos v).im := by
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence (kmswPastCode W) hfin v
  rw [uibhbotPastMonotoneDrawing_pos_layout W hfin n v hn]
  exact layoutHeight_nonneg (kmswPastCode W) n v

/-- The entire past drawing lies in the closed upper half-plane. -/
theorem uibhbotPastMonotoneDrawing_image_im_nonneg (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    (uibhbotPastMonotoneDrawing W hfin).image ⊆ {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  rcases hz with ⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩
  · exact uibhbotPastMonotoneDrawing_pos_im_nonneg W hfin v
  · rw [uibhbotPastMonotoneDrawing_arc_layout W hfin e e
      (kmsw_edge_allocated_by_self (kmswPastCode W) e) b] at hz
    have hz' : z ∈ (layoutArc (kmswPastCode W) e e).image := by
      cases b with
      | false => exact hz
      | true => exact (Polyline.image_reverse_transfer _).subset hz
    have h := layoutArc_height_lower (kmswPastCode W) e e
      (kmsw_edge_allocated_by_self (kmswPastCode W) e) z hz'
    exact (le_min (layoutHeight_nonneg _ _ _) (layoutHeight_nonneg _ _ _)).trans h

/-- Every finite lower-seam endpoint has its explicit position in the same drawing;
the two endpoint abscissas are strictly ordered. -/
theorem uibhbotPastMonotoneDrawing_seam_endpoints (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (n e : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    let s := kmswStage (kmswPastCode W) n
    let P := uibhbotPastMonotoneDrawing W hfin
    P.pos (s.west e) = layoutPos (kmswPastCode W) n (s.west e) ∧
      P.pos (s.east e) = layoutPos (kmswPastCode W) n (s.east e) ∧
      (P.pos (s.west e)).re < (P.pos (s.east e)).re := by
  have heb : e < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge _ n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
  obtain ⟨hw, hh⟩ := kmswStage_endpoints_lt_nextVertex (kmswPastCode W) n e heb
  dsimp only
  have hpw := uibhbotPastMonotoneDrawing_pos_layout W hfin n _ hw
  have hpe := uibhbotPastMonotoneDrawing_pos_layout W hfin n _ hh
  refine ⟨hpw, hpe, ?_⟩
  rw [hpw, hpe]
  change (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).west e) : ℝ) <
    (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict (kmswPastCode W) n e heb

/-- On every allocated lower-seam interval its graph height remains unchanged at
all later stages. This statement uses no two-sided past hit witness. -/
theorem uibhbotPastMonotoneDrawing_seam_stable (W : ℤ → Fin 3) (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (familyG (kmswPastCode W) (monotone_family_all _) n).xmin
      (familyG (kmswPastCode W) (monotone_family_all _) n).xmax) :
    ∀ m, n ≤ m →
      x ∈ Icc (familyG (kmswPastCode W) (monotone_family_all _) m).xmin
        (familyG (kmswPastCode W) (monotone_family_all _) m).xmax ∧
      (familyG (kmswPastCode W) (monotone_family_all _) m).lower x =
        (familyG (kmswPastCode W) (monotone_family_all _) n).lower x :=
  monotoneSeam_lower_stable (kmswPastCode W) n x hx

/-- Nonnegative past R leaves just the initial edge on the lower-right chain. -/
theorem uibhbotPastStage_LR_eq_root (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (n : ℕ) :
    (kmswStage (kmswPastCode W) n).LR = [0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kmswStage_LR_eq, List.range_succ, List.filter_append, List.map_append,
      ← kmswStage_LR_eq, ih]
    have hnot : ¬ ∀ j, j < n + 1 →
        R (kmswPastCode W) (n + 1) < R (kmswPastCode W) j := by
      intro h
      have hh := h 0 (Nat.zero_lt_succ n)
      have hz : R (kmswPastCode W) 0 = 0 := by
        simp only [R, Finset.range_zero, Finset.sum_empty]
      rw [hz] at hh
      exact (not_lt_of_ge (hR (n + 1))) hh
    simp only [List.filter_cons, decide_eq_true_eq, hnot, ↓reduceIte,
      List.filter_nil, List.map_nil, List.append_nil]

/-- The right endpoint of every past layout interval is exactly one. -/
theorem uibhbotPastStage_xmax_eq_one (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (n : ℕ) :
    (familyG (kmswPastCode W) (monotone_family_all _) n).xmax = 1 := by
  let w := kmswPastCode W
  let G := familyG w (monotone_family_all w) n
  have hend := (kmswStage_boundary_endpoints w n).2
  have hLR := uibhbotPastStage_LR_eq_root W hR n
  have hlast : ((kmswStage w n).LL ++ (kmswStage w n).LR).getLast
      (kmswStage_boundary_nonempty w n).2 = 0 := by
    simp only [w, hLR, List.getLast_append_singleton]
  have he0 : 0 < (kmswStage w n).nextEdge :=
    (kmsw_edge_allocated_by_self w 0).trans_le
      (kmswStage_nextEdge_mono w (Nat.zero_le n))
  have heast : (kmswStage w n).east 0 = 1 :=
    ((edge_endpoints_eq w he0).2).trans (by rfl)
  have hv1 : 1 < (kmswStage w 0).nextVertex := by change 1 < 2; omega
  have hpos : layoutPos w n 1 = layoutPos w 0 1 := by
    clear G hend hLR hlast he0 heast
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [layoutPos_old_vertex w n 1
        (hv1.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le n))), ih]
  change G.xmax = 1
  rw [G.xmax_eq_upper_end, hend, hlast, heast, hpos]
  norm_num [layoutPos, kmswStageRank]

/-- Left hits make the lower-seam intervals cover every abscissa at most one; the
conditioned past requires no intervals to the right of this endpoint. -/
theorem uibhbotPastStage_seam_interval_cover (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (x : ℝ) (hx : x ≤ 1) :
    ∃ n, x ∈ Icc (familyG (kmswPastCode W) (monotone_family_all _) n).xmin
      (familyG (kmswPastCode W) (monotone_family_all _) n).xmax := by
  have hbelow : ∀ a : ℤ, ∃ n, L (kmswPastCode W) n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hL (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  obtain ⟨N, hN⟩ := monotoneStage_xmin_unbounded_below (kmswPastCode W)
    (infinitelyManyFreshLeft_of_L_unbounded_below _ hbelow)
    (familyQ (kmswPastCode W) (monotone_family_all _))
    (familyG (kmswPastCode W) (monotone_family_all _)) x
  exact ⟨N, hN N le_rfl, (uibhbotPastStage_xmax_eq_one W hR N).symm ▸ hx⟩

/-- The unstraightened past seam is the union of the persistent finite lower graphs. -/
@[expose] def uibhbotPastSeamGraph (W : ℤ → Fin 3) : Set ℂ :=
  ⋃ n, graphOver (familyG (kmswPastCode W) (monotone_family_all _) n).xmin
    (familyG (kmswPastCode W) (monotone_family_all _) n).xmax
    (familyG (kmswPastCode W) (monotone_family_all _) n).lower

/-- The persistent lower seam is an actual graph on the one-sided domain `x ≤ 1`.
Existence and uniqueness are established before any choice of its height. -/
theorem uibhbotPastSeamGraph_existsUnique_height (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (x : ℝ) (hx : x ≤ 1) :
    ∃! y : ℝ, (⟨x, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W := by
  obtain ⟨n, hn⟩ := uibhbotPastStage_seam_interval_cover W hL hR x hx
  let G := familyG (kmswPastCode W) (monotone_family_all (kmswPastCode W))
  refine ⟨(G n).lower x, mem_iUnion.mpr ⟨n, hn.1, hn.2, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨m, hm⟩ := mem_iUnion.mp hy
  have hm' : x ∈ Icc (G m).xmin (G m).xmax := ⟨hm.1, hm.2.1⟩
  have hsN := (uibhbotPastMonotoneDrawing_seam_stable W n x hn
    (max n m) (le_max_left n m)).2
  have hsM := (uibhbotPastMonotoneDrawing_seam_stable W m x hm'
    (max n m) (le_max_right n m)).2
  exact hm.2.2.trans (hsM.symm.trans hsN)

/-- Every point of the past lower seam belongs to the past PL drawing. -/
theorem uibhbotPastSeamGraph_subset_image (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    uibhbotPastSeamGraph W ⊆ (uibhbotPastMonotoneDrawing W hfin).image := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  rw [(familyG (kmswPastCode W) (monotone_family_all _) n).lower_trace] at hn
  obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hn
  have heb : e < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge _ n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
  have ha := (familyG (kmswPastCode W) (monotone_family_all _) n).arc_layout
    (⟨e, heb⟩, false)
  simp only [Bool.false_eq_true, ite_false] at ha
  have hzarc : z ∈ (layoutArc (kmswPastCode W) n e).image := by
    simpa only [stageEdgeTrace, dite_eq_left heb, ha] using hze
  refine Or.inr ⟨(e, false), ?_⟩
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e heb false]
  exact hzarc

/-- The seam has precisely the one-sided horizontal domain `x ≤ 1`. -/
theorem uibhbotPastSeamGraph_domain (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (x : ℝ) :
    (∃ y : ℝ, (⟨x, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W) ↔ x ≤ 1 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    have hle : x ≤ (familyG (kmswPastCode W) (monotone_family_all _) n).xmax := hn.2.1
    rwa [uibhbotPastStage_xmax_eq_one W hR n] at hle
  · intro hx
    exact (uibhbotPastSeamGraph_existsUnique_height W hL hR x hx).exists

/-- The whole past drawing is to the left of the seam's right endpoint. -/
theorem uibhbotPastMonotoneDrawing_image_re_le_one (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) :
    (uibhbotPastMonotoneDrawing W hfin).image ⊆ {z : ℂ | z.re ≤ 1} := by
  intro z hz
  change z ∈ (monotoneFamilyDrawing (kmswPastCode W) hfin (monotone_family_all _)).image at hz
  have hzU := (monotoneFamilyDrawing_image (kmswPastCode W) hfin
    (monotone_family_all _)).subset hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hzU
  have hle := ((familyG (kmswPastCode W) (monotone_family_all _) n).image_bounds hn).2.1
  rwa [uibhbotPastStage_xmax_eq_one W hR n] at hle

/-- Every point of the past drawing lies at or above its persistent lower graph.
No boundary-hit hypothesis, including a left-hit hypothesis, is needed here. -/
theorem uibhbotPastMonotoneDrawing_above_seam (W : ℤ → Fin 3)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) {z : ℂ}
    (hz : z ∈ (uibhbotPastMonotoneDrawing W hfin).image) {y : ℝ}
    (hy : (⟨z.re, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W) : y ≤ z.im := by
  let w := kmswPastCode W
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  change z ∈ (monotoneFamilyDrawing w hfin (monotone_family_all w)).image at hz
  have hzU := (monotoneFamilyDrawing_image w hfin (monotone_family_all w)).subset hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hzU
  obtain ⟨m, hm⟩ := mem_iUnion.mp hy
  have hmono : Monotone (fun k => (Q k).image) :=
    monotone_nat_of_le_succ (monotone_image_mono w Q G)
  have hzN : z ∈ (Q (max n m)).image := hmono (le_max_left n m) hn
  have hbelow := ((G (max n m)).image_bounds hzN).2.2.1
  have hm' : z.re ∈ Icc (G m).xmin (G m).xmax := ⟨hm.1, hm.2.1⟩
  have hstable := (uibhbotPastMonotoneDrawing_seam_stable W m z.re hm'
    (max n m) (le_max_right n m)).2
  exact (hm.2.2.trans hstable.symm).le.trans hbelow

/-- One almost-sure event provides finite incidence, one-sided hits, the actual past
drawing and a unique persistent seam height at every `x ≤ 1`, simultaneously. -/
theorem uibhbotCodeLawRel_ae_past_drawing_seam_graph :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hfin : KMSWFiniteIncidence (kmswPastCode W),
        let P := uibhbotPastMonotoneDrawing W hfin
        (∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a) ∧
        (∀ n, 0 ≤ R (kmswPastCode W) n) ∧
        P.image ⊆ {z : ℂ | 0 ≤ z.im ∧ z.re ≤ 1} ∧
        uibhbotPastSeamGraph W ⊆ P.image ∧
        (∀ x : ℝ, x ≤ 1 → ∃! y : ℝ, (⟨x, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W) ∧
        (∀ x : ℝ, (∃ y : ℝ, (⟨x, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W) ↔ x ≤ 1) ∧
        (∀ z ∈ P.image, ∀ y : ℝ,
          (⟨z.re, y⟩ : ℂ) ∈ uibhbotPastSeamGraph W → y ≤ z.im) := by
  filter_upwards [uibhbotCodeLawRel_ae_past_finiteIncidence,
    uibhbotCodeLawRel_ae_past_leftHit, uibhbotCodeLawRel_ae_past_R_nonneg] with W hfin hL hR
  refine ⟨hfin, hL, hR.1, ?_, uibhbotPastSeamGraph_subset_image W hfin,
    uibhbotPastSeamGraph_existsUnique_height W hL hR.1,
    uibhbotPastSeamGraph_domain W hL hR.1, ?_⟩
  · intro z hz
    exact ⟨uibhbotPastMonotoneDrawing_image_im_nonneg W hfin hz,
      uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR.1 hz⟩
  · intro z hz y hy
    exact uibhbotPastMonotoneDrawing_above_seam W hfin hz hy

/-- Almost surely there is a locally finite PL drawing of the conditioned past,
with all stage coordinates and arcs retained and its entire image in one closed
half-plane. This does not assert that its lower seam has been straightened. -/
theorem uibhbotCodeLawRel_ae_past_monotoneDrawing :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hfin : KMSWFiniteIncidence (kmswPastCode W),
        ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
            (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
          P = uibhbotPastMonotoneDrawing W hfin ∧
          P.image ⊆ {z : ℂ | 0 ≤ z.im} ∧
          (∀ n v, v < (kmswStage (kmswPastCode W) n).nextVertex →
            P.pos v = layoutPos (kmswPastCode W) n v) ∧
          (∀ n e, e < (kmswStage (kmswPastCode W) n).nextEdge → ∀ b,
            P.arc (e, b) = if b then (layoutArc (kmswPastCode W) n e).reverse
              else layoutArc (kmswPastCode W) n e) := by
  filter_upwards [uibhbotCodeLawRel_ae_past_finiteIncidence] with W hfin
  exact ⟨hfin, uibhbotPastMonotoneDrawing W hfin, rfl,
    uibhbotPastMonotoneDrawing_image_im_nonneg W hfin,
    uibhbotPastMonotoneDrawing_pos_layout W hfin,
    uibhbotPastMonotoneDrawing_arc_layout W hfin⟩

/-- The generic past seam-transfer premise is almost surely false for this law. -/
theorem uibhbotCodeLawRel_ae_not_past_boundaryHitWitnesses :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ¬ BoundaryHitWitnesses (kmswPastCode W) := by
  filter_upwards [uibhbotCodeLawRel_ae_past_R_nonneg] with W hR
  intro h
  obtain ⟨n, hn⟩ := h.rightHit 1 le_rfl
  have hnonneg := hR.1 n
  omega

end
end DirectedDistances.KMSW
