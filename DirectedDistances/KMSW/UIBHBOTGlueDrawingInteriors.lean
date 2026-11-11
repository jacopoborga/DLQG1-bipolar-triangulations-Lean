/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingSeparation
import Mathlib.Tactic.Linarith

/-! # Interior separation for the half-line UIBHBOT gluing

The retained past interiors lie strictly above the attachment axis, so the
same candidate assembly has disjoint interiors. No past boundary-hit witness
is used. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap DirectedDistances.RandomWalk Set
open DirectedDistances.PaperProofs.Section5 WholePlanePastGlueData

noncomputable section

/-- A transported interior point comes from an interior point when images and
both endpoints are transported by the same map. -/
private theorem uibhbotInteriors_preimage (p q : Polyline) (T : ℂ → ℂ)
    (hi : q.image = T '' p.image) (hs : q.start = T p.start)
    (hf : q.finish = T p.finish) {z : ℂ} (hz : z ∈ q.interior) :
    ∃ y ∈ p.interior, T y = z := by
  obtain ⟨y, hy, rfl⟩ := hi ▸ hz.1
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  intro he
  apply hz.2
  rcases he with he | he
  · exact Or.inl ((congrArg T he).trans hs.symm)
  · exact Or.inr ((congrArg T he).trans hf.symm)

variable (W : ℤ → Fin 3)
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))

/-- A non-seam past edge has its entire interior strictly above the persistent
lower graph, using only the one-sided past hypotheses. -/
theorem uibhbotInteriors_past_nonseam_above (d : ℕ × Bool)
    (hd : ¬ kmswPastSeamEdge W d.1) {z : ℂ}
    (hz : z ∈ ((uibhbotPastMonotoneDrawing W hfin).arc d).interior) :
    uibhbotPastSeamHeight W hL hR z.re < z.im := by
  let P := uibhbotPastMonotoneDrawing W hfin
  have hx : z.re ≤ 1 :=
    uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR (Or.inr ⟨d, hz.1⟩)
  have hs := uibhbotPastSeamHeight_mem W hL hR z.re
  rw [min_eq_left hx] at hs
  have hle : uibhbotPastSeamHeight W hL hR z.re ≤ z.im :=
    uibhbotPastMonotoneDrawing_above_seam W hfin (Or.inr ⟨d, hz.1⟩) hs
  apply lt_of_le_of_ne hle
  intro heq
  rw [heq, Complex.eta] at hs
  obtain ⟨e, he, hze⟩ := uibhbotPastSeamGraph_mem_arc W hfin hs
  have hends : z ≠ (P.arc (e, false)).start ∧ z ≠ (P.arc (e, false)).finish := by
    constructor
    · intro hez
      apply P.interior_avoids_vertices d (kmswLimitDartVertex (kmswPastCode W) (e, false))
      rw [← P.arc_start, ← hez]
      exact hz
    · intro hez
      apply P.interior_avoids_vertices d (kmswLimitDartVertex (kmswPastCode W) (e, true))
      have hf := P.arc_finish (e, false)
      change (P.arc (e, false)).finish =
        P.pos (kmswLimitDartVertex (kmswPastCode W) (e, true)) at hf
      rw [← hf, ← hez]
      exact hz
  have hzi : z ∈ (P.arc (e, false)).interior :=
    ⟨hze, by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using hends⟩
  have hse : kmswPastSeamEdge W e := he
  have hdis := P.interior_disjoint d (e, false)
    (fun h => hd ((congrArg Prod.fst h : e = d.1) ▸ hse))
    (fun h => hd ((congrArg Prod.fst h : e = d.1) ▸ hse))
  exact disjoint_left.mp hdis hz hzi

variable
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)

include hp ha in
/-- After straightening and attaching the past, every retained interior lies
strictly above the real axis. -/
theorem uibhbotInteriors_past_attached_pos (d : ℕ × Bool)
    (hd : ¬ kmswPastSeamEdge W d.1) {z : ℂ}
    (hz : z ∈ (Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)).interior) :
    0 < z.im := by
  rw [Polyline.interior_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)
    uibhbotAssemblyHalfTurn_involutive.injective.injOn] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  let P0 := uibhbotPastMonotoneDrawing W hfin
  have hs : (P.arc d).start = uibhbotPastStraightTransfer W hL hR (P0.arc d).start := by
    rw [P.arc_start, P0.arc_start, hp]
    rfl
  have hf : (P.arc d).finish = uibhbotPastStraightTransfer W hL hR (P0.arc d).finish := by
    rw [P.arc_finish, P0.arc_finish, hp]
    rfl
  obtain ⟨q, hq, rfl⟩ := uibhbotInteriors_preimage (P0.arc d) (P.arc d)
    (uibhbotPastStraightTransfer W hL hR) (ha d) hs hf hy
  have hlt := uibhbotInteriors_past_nonseam_above W hL hR hfin d hd hq
  change 0 < -(-q.im + 0 + uibhbotPastSeamHeight W hL hR q.re) - 0
  linarith only [hlt]

variable (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})

local notation "arc" => uibhbotAssemblyArc W
  (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc

include hp ha h0 hFim in
/-- Future interiors and retained past interiors are disjoint. -/
theorem uibhbotInteriors_cross_disjoint (d e : ℕ × Bool)
    (he : ¬ kmswPastSeamEdge W e.1) :
    Disjoint (arc (wholePlaneDartι W 0 d)).interior
      (arc (kmswPastDart W e)).interior := by
  rw [uibhbotAssemblyArc_future, uibhbotAssemblyArc_past W h0 _ _ e he]
  apply disjoint_left.mpr
  intro z hz hz'
  exact not_lt_of_ge (hFim (Or.inr ⟨d, hz.1⟩))
    (uibhbotInteriors_past_attached_pos W hL hR hfin P hp ha e he hz')

include hp ha h0 hFim in
/-- G2: distinct geometric edges of this same candidate assembly have disjoint
interiors, without boundary-hit witnesses for the past. -/
theorem uibhbotInteriors_assembly_interior_disjoint (D E : WholePlaneDart W)
    (hne : E ≠ D) (hflip : E ≠ wholePlaneDartFlip W D) :
    Disjoint (arc D).interior (arc E).interior := by
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩ <;>
    rcases dart_cover_off_seam W h0 E with ⟨e, rfl⟩ | ⟨e, he, rfl⟩
  · rw [uibhbotAssemblyArc_future, uibhbotAssemblyArc_future]
    apply F.interior_disjoint d e
    · intro h
      exact hne (congrArg (wholePlaneDartι W 0) h)
    · intro h
      exact hflip (congrArg (wholePlaneDartι W 0) h)
  · exact uibhbotInteriors_cross_disjoint W hL hR hfin P hp ha H h0 F hFim d e he
  · exact (uibhbotInteriors_cross_disjoint W hL hR hfin P hp ha H h0 F hFim e d hd).symm
  · rw [uibhbotAssemblyArc_past W h0 _ _ d hd, uibhbotAssemblyArc_past W h0 _ _ e he]
    apply Polyline.interior_disjoint_mapPoints _ _ _
      (uibhbotAssemblyHalfTurn_affine _) (uibhbotAssemblyHalfTurn_affine _)
      uibhbotAssemblyHalfTurn_involutive.injective.injOn
    apply P.interior_disjoint d e
    · intro h
      exact hne (congrArg (kmswPastDart W) h)
    · intro h
      apply hflip
      rw [pastDart_flip]
      exact congrArg (kmswPastDart W) h

end

noncomputable section




theorem uibhbotCodeLawRel_ae_candidate_glue_geometry_disjoint :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ _H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
        Function.Injective pos ∧
        (∀ D E, E ≠ D → E ≠ wholePlaneDartFlip W D →
          Disjoint (arc D).interior (arc E).interior) ∧
        (∀ D, (arc D).IsSimple) ∧
        (∀ D, 2 ≤ (arc D).points.length) ∧
        (∀ D, (arc D).start = pos (wholePlaneDartVertex W D)) ∧
        (∀ D, (arc D).finish = pos (wholePlaneDartVertex W (wholePlaneDartFlip W D))) ∧
        (∀ D, arc (wholePlaneDartFlip W D) = (arc D).reverse) ∧
        (∀ D, (arc D).initialDirection ≠ 0) ∧
        (∀ K : Set ℂ, Bornology.IsBounded K →
          {D | (K ∩ (arc D).image).Nonempty}.Finite) ∧
        (∀ k : ℤ, pos (wholePlaneVertexι W 0
          (boundaryVertex (shiftedStream W 0) h0 k)) = ⟨-(k : ℝ), 0⟩) ∧
        (∀ v : ℕ, (pos (wholePlaneVertexι W 0 v)).im ≤ 0) ∧
        (∀ v : ℕ, 0 ≤ (pos (kmswPastVertex W v)).im) ∧
        (∀ k : ℤ, ∀ b : Bool,
          (arc (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, b))).image
            ⊆ {z : ℂ | z.im = 0}) ∧
        (∀ d : ℕ × Bool, ¬ kmswPastSeamEdge W d.1 →
          (arc (kmswPastDart W d)).image ⊆ {z : ℂ | 0 ≤ z.im}) ∧
        ∀ d : ℕ × Bool,
          (arc (wholePlaneDartι W 0 d)).image ⊆ {z : ℂ | z.im ≤ 0} := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses, uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg, uibhbotCodeLawRel_ae_past_finiteIncidence]
    with W hH hhit hL hR hfin
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨P, hPquad, hppos, hparc⟩ :=
    uibhbotAssembly_past_straightDrawing_quadrant W hL hR.1 hfin
  have hPim : P.image ⊆ {z : ℂ | z.im ≤ 0} := fun z hz => (hPquad hz).1
  obtain ⟨F, hFim, hFpos, hfpos, hFarc⟩ :=
    uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hp : uibhbotAssemblyHalfTurn ∘ P.pos =
      uibhbotSeparationPastPos W hL hR.1 hfin := by
    funext v
    rw [Function.comp_apply, hppos]
    rfl
  have hf : F.pos = uibhbotSeparationFuturePos W H h0 := by
    rw [hfpos]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    change F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v
    rw [hp, hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR.1 hfin u v huv
  let pos := uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
  let arc := uibhbotAssemblyArc W
    (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc
  refine ⟨H, h0, pos, arc, ?_, ?_,
    uibhbotAssemblyArc_simple W H hfin P F,
    uibhbotAssemblyArc_length W H hfin P F,
    uibhbotAssemblyArc_start W H hfin P F h0 hc,
    uibhbotAssemblyArc_finish W H hfin P F h0 hc,
    uibhbotAssemblyArc_flip W H hfin P F, ?_,
    uibhbotAssemblyArc_locally_finite W H hfin P F h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Function.Injective (uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos)
    rw [hp, hf]
    exact uibhbotSeparation_assembly_pos_injective W H h0 hL hR.1 hfin
  · exact uibhbotInteriors_assembly_interior_disjoint W hL hR.1 hfin P hppos hparc H h0 F hFim
  · intro D hz
    have hs := uibhbotAssemblyArc_simple W H hfin P F D
    have hl := uibhbotAssemblyArc_length W H hfin P F D
    apply hs.1 0 (by omega)
    rw [Polyline.point_zero_eq_start]
    exact (sub_eq_zero.mp hz).symm
  · intro k
    exact (uibhbotAssemblyPos_future W _ _ _).trans (hFpos k)
  · intro v
    change (uibhbotAssemblyPos W _ _ _).im ≤ 0
    rw [uibhbotAssemblyPos_future]
    exact hFim (Or.inl ⟨v, rfl⟩)
  · intro v
    change 0 ≤ (uibhbotAssemblyPos W _ _ _).im
    rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc]
    have hpv : (P.pos v).im ≤ 0 := hPim (Or.inl ⟨v, rfl⟩)
    change 0 ≤ -(P.pos v).im - 0
    linarith only [hpv]
  · intro k b z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 _)).image at hz
    rw [uibhbotAssemblyArc_future, hFarc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hg := uibhbotAssembly_future_seam_graph (shiftedStream W 0) h0 (H.1 0) k b hy
    change -y.im + 0 + seamFun (shiftedStream W 0) h0 (H.1 0) y.re = 0
    rw [← hg]
    ring
  · intro d hd z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (kmswPastDart W d)).image at hz
    rw [uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hpv : y.im ≤ 0 := hPim (Or.inr ⟨d, hy⟩)
    change 0 ≤ -y.im - 0
    linarith only [hpv]
  · intro d z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 d)).image at hz
    rw [uibhbotAssemblyArc_future] at hz
    exact hFim (Or.inr ⟨d, hz⟩)

end
end DirectedDistances.KMSW
