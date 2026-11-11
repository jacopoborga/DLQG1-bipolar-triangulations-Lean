/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39Domain
public import DirectedDistances.KMSW.UIBHBOTGlueDrawingCcw

/-! # Canonical geometric domain for the UIBHBOT assembly

Helper toward Proposition 5.9. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Set

noncomputable section

/-- Helper toward Proposition 5.9. This is the code-indexed transfer drawing
used for the past half of the UIBHBOT assembly. Its arcs are the explicit
`Polyline.transferArc` values, so their parametrizations are fixed. -/
@[expose] def uibhbotD39PastCanonicalDrawing (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)) := by
  let P := uibhbotPastMonotoneDrawing W hfin
  let T := uibhbotPastStraightTransfer W hL hR
  let cuts := uibhbotPastSeamCuts W hfin
  let hcuts := uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin
  let hmono := uibhbotPastMonotoneDrawing_arc_monotone W hfin
  let haff := uibhbotPastStraightTransfer_affine W hL hR hfin
  exact {
    flip_involutive := P.flip_involutive
    flip_ne := P.flip_ne
    vert_rotation := P.vert_rotation
    pos := T ∘ P.pos
    pos_injective := T.injective.comp P.pos_injective
    arc := fun d => Polyline.transferArc T cuts hcuts (P.arc d)
    arc_simple := fun d => Polyline.isSimple_transferArc T cuts hcuts haff _
      (hmono d) (P.arc_length d)
    arc_length := fun d => Polyline.length_transferArc T cuts hcuts _
      (hmono d) (P.arc_length d)
    arc_start := fun d => (Polyline.start_transferArc T cuts hcuts (P.arc d)).trans
      (congrArg T (P.arc_start d))
    arc_finish := fun d => (Polyline.finish_transferArc T cuts hcuts (P.arc d)).trans
      (congrArg T (P.arc_finish d))
    arc_flip := PLDrawing.transferArc_flip P hmono T cuts hcuts
    interior_disjoint := PLDrawing.transferArc_interior_disjoint P hmono T cuts hcuts haff
    interior_avoids_vertices :=
      PLDrawing.transferArc_interior_avoids_vertices P hmono T cuts hcuts haff
    locally_finite := PLDrawing.transferArc_locally_finite P hmono T cuts hcuts haff
    initial_nonzero := PLDrawing.transferArc_initial_nonzero P hmono T cuts hcuts haff
    initial_arg_injective :=
      PLDrawing.transferArc_initial_arg_injective P hmono T cuts hcuts haff
    rotation_agreement := PLDrawing.transferArc_rotation_agreement P hmono T cuts hcuts haff }

/-- Helper toward Proposition 5.9: the canonical past positions are the
straightening of the code-indexed monotone drawing. -/
theorem uibhbotD39PastCanonicalDrawing_pos (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    (uibhbotD39PastCanonicalDrawing W hL hR hfin).pos =
      uibhbotPastStraightTransfer W hL hR ∘
        (uibhbotPastMonotoneDrawing W hfin).pos := rfl

/-- Helper toward Proposition 5.9: the canonical past arcs are the explicit
piecewise-affine transfers of the code-indexed arcs. -/
theorem uibhbotD39PastCanonicalDrawing_arcImage (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (d : ℕ × Bool) :
    ((uibhbotD39PastCanonicalDrawing W hL hR hfin).arc d).image =
      uibhbotPastStraightTransfer W hL hR ''
        ((uibhbotPastMonotoneDrawing W hfin).arc d).image := by
  exact Polyline.image_transferArc (uibhbotPastStraightTransfer W hL hR)
    (uibhbotPastSeamCuts W hfin) (uibhbotPastSeamCuts_inter_Icc_finite W hL hR hfin)
    (uibhbotPastStraightTransfer_affine W hL hR hfin)
    ((uibhbotPastMonotoneDrawing W hfin).arc d)
    (uibhbotPastMonotoneDrawing_arc_monotone W hfin d)
    ((uibhbotPastMonotoneDrawing W hfin).arc_length d)

/-- Helper toward Proposition 5.9: the future transfer is affine between
successive seam cuts. -/
theorem uibhbotD39FutureTransfer_affine (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w)
    (s t : ℝ) (hst : s < t)
    (hno : ∀ c ∈ seamCutSet w h hfin, c ∉ Ioo s t) :
    ∃ m0 m1 c0 c1 : ℝ, 0 < m0 ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
      uibhbotGlueFutureTransfer w h hfin z =
        ⟨-(m0 * z.re) + c0, -z.im + m1 * z.re + c1⟩ := by
  obtain ⟨m, c, hf⟩ := seamFun_affine_of_noCut w h hfin s t hst hno
  refine ⟨1, m, 0, c, zero_lt_one, ?_⟩
  intro z hs ht
  change (⟨-z.re, -z.im + 0 + seamFun w h hfin z.re⟩ : ℂ) = _
  rw [hf z.re ⟨hs, ht⟩]
  apply Complex.ext <;> dsimp <;> ring

/-- Helper toward Proposition 5.9: the code-indexed future arcs are monotone
in one orientation, as required by the explicit transfer. -/
theorem uibhbotD39FutureCanonicalDrawing_arcMonotone (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (d : ℕ × Bool) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).XMonotone ∨
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).reverse.XMonotone := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  rcases d with ⟨e, b⟩
  have ha : P.arc (e, b) = if b then (layoutArc w e e).reverse else layoutArc w e e :=
    monotoneLimitDrawing_arc_layout w hfin _ e e (kmsw_edge_allocated_by_self w e) b
  rw [ha]
  cases b
  · exact Or.inl (layoutArc_points_pairwise _ e e (kmsw_edge_allocated_by_self _ e))
  · right
    change (layoutArc w e e).reverse.reverse.XMonotone
    rw [Polyline.reverse_reverse]
    exact layoutArc_points_pairwise _ e e (kmsw_edge_allocated_by_self _ e)

/-- Helper toward Proposition 5.9. This is the code-indexed transfer drawing
used for the future half of the assembly, with explicit transfer arcs. -/
@[expose] def uibhbotD39FutureCanonicalDrawing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) ((H.1) 0))
      (kmswLimitDartVertex (shiftedStream W 0)) := by
  let w := shiftedStream W 0
  let h := h0
  let hfin := (H.1) 0
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let T := uibhbotGlueFutureTransfer w h hfin
  let cuts := seamCutSet w h hfin
  let hcuts := seamCutSet_inter_Icc_finite w h hfin
  let hmono := uibhbotD39FutureCanonicalDrawing_arcMonotone w hfin
  let haff := uibhbotD39FutureTransfer_affine w h hfin
  exact {
    flip_involutive := P.flip_involutive
    flip_ne := P.flip_ne
    vert_rotation := P.vert_rotation
    pos := T ∘ P.pos
    pos_injective := T.injective.comp P.pos_injective
    arc := fun d => Polyline.transferArc T cuts hcuts (P.arc d)
    arc_simple := fun d => Polyline.isSimple_transferArc T cuts hcuts haff _
      (hmono d) (P.arc_length d)
    arc_length := fun d => Polyline.length_transferArc T cuts hcuts _
      (hmono d) (P.arc_length d)
    arc_start := fun d => (Polyline.start_transferArc T cuts hcuts (P.arc d)).trans
      (congrArg T (P.arc_start d))
    arc_finish := fun d => (Polyline.finish_transferArc T cuts hcuts (P.arc d)).trans
      (congrArg T (P.arc_finish d))
    arc_flip := PLDrawing.transferArc_flip P hmono T cuts hcuts
    interior_disjoint := PLDrawing.transferArc_interior_disjoint P hmono T cuts hcuts haff
    interior_avoids_vertices :=
      PLDrawing.transferArc_interior_avoids_vertices P hmono T cuts hcuts haff
    locally_finite := PLDrawing.transferArc_locally_finite P hmono T cuts hcuts haff
    initial_nonzero := PLDrawing.transferArc_initial_nonzero P hmono T cuts hcuts haff
    initial_arg_injective :=
      PLDrawing.transferArc_initial_arg_injective P hmono T cuts hcuts haff
    rotation_agreement := PLDrawing.transferArc_rotation_agreement P hmono T cuts hcuts haff }

/-- Helper toward Proposition 5.9: the canonical future positions agree with
the future positions used in the UIBHBOT assembly. -/
theorem uibhbotD39FutureCanonicalDrawing_pos (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) :
    (uibhbotD39FutureCanonicalDrawing W H h0).pos =
      uibhbotSeparationFuturePos W H h0 := by
  funext v
  change uibhbotGlueFutureTransfer (shiftedStream W 0) h0 ((H.1) 0)
    ((monotoneFamilyDrawing (shiftedStream W 0) ((H.1) 0)
      (monotone_family_all _)).pos v) = _
  rfl

/-- Helper toward Proposition 5.9: the canonical future arcs are the explicit
piecewise-affine transfers of the code-indexed future arcs. -/
theorem uibhbotD39FutureCanonicalDrawing_arcImage (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (d : ℕ × Bool) :
    ((uibhbotD39FutureCanonicalDrawing W H h0).arc d).image =
      uibhbotGlueFutureTransfer (shiftedStream W 0) h0 ((H.1) 0) ''
        ((monotoneFamilyDrawing (shiftedStream W 0) ((H.1) 0)
          (monotone_family_all _)).arc d).image := by
  exact Polyline.image_transferArc
    (uibhbotGlueFutureTransfer (shiftedStream W 0) h0 ((H.1) 0))
    (seamCutSet (shiftedStream W 0) h0 ((H.1) 0))
    (seamCutSet_inter_Icc_finite (shiftedStream W 0) h0 ((H.1) 0))
    (uibhbotD39FutureTransfer_affine (shiftedStream W 0) h0 ((H.1) 0))
    ((monotoneFamilyDrawing (shiftedStream W 0) ((H.1) 0)
      (monotone_family_all _)).arc d)
    (uibhbotD39FutureCanonicalDrawing_arcMonotone (shiftedStream W 0) ((H.1) 0) d)
    ((monotoneFamilyDrawing (shiftedStream W 0) ((H.1) 0)
      (monotone_family_all _)).arc_length d)

/-- Helper toward Proposition 5.9: the canonical future drawing stays below
the real axis. -/
theorem uibhbotD39FutureCanonicalDrawing_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) :
    (uibhbotD39FutureCanonicalDrawing W H h0).image ⊆ {z : ℂ | z.im ≤ 0} := by
  let w := shiftedStream W 0
  let hfin := (H.1) 0
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let T := uibhbotGlueFutureTransfer w h0 hfin
  have him (z : ℂ) (hz : z ∈ P.image) : (T z).im ≤ 0 := by
    have habove : seamFun w h0 hfin z.re ≤ z.im :=
      monotoneFamilyDrawing_above_seam w h0 hfin hz
    change -z.im + 0 + seamFun w h0 hfin z.re ≤ 0
    linarith only [habove]
  intro z hz
  rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
  · rw [uibhbotD39FutureCanonicalDrawing_pos W H h0]
    change (T (P.pos v)).im ≤ 0
    exact him (P.pos v) (Or.inl ⟨v, rfl⟩)
  · rw [uibhbotD39FutureCanonicalDrawing_arcImage W H h0 d] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact him y (Or.inr ⟨d, hy⟩)












































end

end DirectedDistances.PaperProofs.Section5
