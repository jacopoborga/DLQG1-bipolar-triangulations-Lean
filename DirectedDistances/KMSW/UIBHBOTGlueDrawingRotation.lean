/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingInteriors
import Mathlib.Tactic.Linarith

/-! # Vertex avoidance for the half-line UIBHBOT gluing

The same assembled positions avoid all arc interiors. An attached past vertex
on the axis is a shared vertex, while every retained past interior is strictly
above the axis. No boundary-hit witness for the past is used. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap DirectedDistances.RandomWalk Set
open DirectedDistances.PaperProofs.Section5 WholePlanePastGlueData

noncomputable section

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
    (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})

local notation "pos" => uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
local notation "arc" => uibhbotAssemblyArc W
  (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc

include hp ha hf hFim in
/-- G3: the vertices of the concrete candidate assembly avoid every arc interior,
using the same past and future drawings as G1 and G2. -/
theorem uibhbotRotation_assembly_interior_avoids_vertices
    (D : WholePlaneDart W) (V : WholePlaneVertex W) :
    pos V ∉ (arc D).interior := by
  have hp' : uibhbotAssemblyHalfTurn ∘ P.pos =
      uibhbotSeparationPastPos W hL hR hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v := by
    intro u v huv
    rw [hp', hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR hfin u v huv
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩ <;>
    rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [uibhbotAssemblyPos_future, uibhbotAssemblyArc_future]
    exact F.interior_avoids_vertices d v
  · rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc,
      uibhbotAssemblyArc_future]
    intro hz
    have hle := hFim (Or.inr ⟨d, hz.1⟩)
    have hge := uibhbotSeparation_past_pos_im_nonneg W hL hR hfin v
    have hpos : (uibhbotAssemblyHalfTurn ∘ P.pos) v =
        uibhbotSeparationPastPos W hL hR hfin v := congrFun hp' v
    rw [hpos] at hle
    obtain ⟨u, huv⟩ := uibhbotSeparation_past_axis_shared W h0 hL hR hfin v
      (le_antisymm hle hge)
    rw [← hc u v huv] at hz
    exact F.interior_avoids_vertices d u hz
  · rw [uibhbotAssemblyPos_future, uibhbotAssemblyArc_past W h0 _ _ d hd]
    intro hz
    have hlt := uibhbotInteriors_past_attached_pos W hL hR hfin P hp ha d hd hz
    exact not_lt_of_ge (hFim (Or.inl ⟨v, rfl⟩)) hlt
  · rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc,
      uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.interior_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)
        uibhbotAssemblyHalfTurn_involutive.injective.injOn]
    rintro ⟨y, hy, he⟩
    have hyv : y = P.pos v := uibhbotAssemblyHalfTurn_involutive.injective he
    rw [hyv] at hy
    exact P.interior_avoids_vertices d v hy

end

noncomputable section



theorem uibhbotCodeLawRel_ae_candidate_glue_geometry_avoids_vertices :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ _H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
        Function.Injective pos ∧
        (∀ D E, E ≠ D → E ≠ wholePlaneDartFlip W D →
          Disjoint (arc D).interior (arc E).interior) ∧
        (∀ D V, pos V ∉ (arc D).interior) ∧
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
    uibhbotRotation_assembly_interior_avoids_vertices W H h0 hL hR.1 hfin
      P hppos hparc F hf hFim,
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
