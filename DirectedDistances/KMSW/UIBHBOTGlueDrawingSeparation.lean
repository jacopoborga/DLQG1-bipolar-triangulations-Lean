/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingAssembly
import DirectedDistances.KMSW.MonotoneSeamVertices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Vertex separation for the half-line UIBHBOT gluing

The straightened past and future positions are injective after gluing along
the covered half-line. No boundary-hit witness for the past is used. -/

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

/-- The future positions after straightening its entire lower boundary. -/
@[expose] def uibhbotSeparationFuturePos (v : ℕ) : ℂ :=
  uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0)
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).pos v)

/-- The past positions after straightening and attaching by a half-turn. -/
@[expose] def uibhbotSeparationPastPos (v : ℕ) : ℂ :=
  uibhbotAssemblyHalfTurn (uibhbotPastStraightTransfer W hL hR
    ((uibhbotPastMonotoneDrawing W hfin).pos v))

include h0 in
/-- Every endpoint of a covered past seam edge is a shared vertex. -/
theorem uibhbotSeparation_seam_incident_shared (d : ℕ × Bool)
    (hd : kmswPastSeamEdge W d.1) :
    kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∈
      range (wholePlaneVertexι W 0) := by
  obtain ⟨e, he⟩ := (kmswPastEdge_mem_runZero_iff W h0 d.1).mpr hd
  have hD : wholePlaneDartι W 0 (e, !d.2) = kmswPastDart W d := by
    rcases d with ⟨f, b⟩
    change (wholePlaneEdgeι W 0 e, !b) = (kmswPastEdge W f, !b)
    rw [he]
  have hv := congrArg (wholePlaneDartVertex W) hD
  rw [wholePlaneDartVertex_ι, pastDart_vertex] at hv
  exact ⟨_, hv⟩

include h0 in
/-- A past vertex on the attachment axis belongs to the covered half-line seam. -/
theorem uibhbotSeparation_past_axis_shared (v : ℕ)
    (hz : (uibhbotSeparationPastPos W hL hR hfin v).im = 0) :
    kmswPastVertex W v ∈ range (wholePlaneVertexι W 0) := by
  let P := uibhbotPastMonotoneDrawing W hfin
  have hx : (P.pos v).re ≤ 1 :=
    uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR (Or.inl ⟨v, rfl⟩)
  have hy : (P.pos v).im = uibhbotPastSeamHeight W hL hR (P.pos v).re := by
    change -(-(P.pos v).im + 0 +
      uibhbotPastSeamHeight W hL hR (P.pos v).re) - 0 = 0 at hz
    linarith only [hz]
  have hs := uibhbotPastSeamHeight_mem W hL hR (P.pos v).re
  rw [min_eq_left hx, ← hy] at hs
  have hp : (⟨(P.pos v).re, (P.pos v).im⟩ : ℂ) = P.pos v := Complex.eta _
  rw [hp] at hs
  obtain ⟨e, he, hve⟩ := uibhbotPastSeamGraph_mem_arc W hfin hs
  have hends : P.pos v = (P.arc (e, false)).start ∨
      P.pos v = (P.arc (e, false)).finish := by
    by_contra hn
    apply P.interior_avoids_vertices (e, false) v
    simp only [Polyline.interior, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    exact ⟨hve, hn⟩
  rcases hends with hs | ht
  · rw [P.arc_start] at hs
    have hv := P.pos_injective hs
    rw [hv]
    exact uibhbotSeparation_seam_incident_shared W h0 (e, false) he
  · rw [P.arc_finish] at ht
    have hv := P.pos_injective ht
    rw [hv]
    exact uibhbotSeparation_seam_incident_shared W h0 (e, true) he

/-- Future boundary labels have their exact positions after straightening. -/
theorem uibhbotSeparation_future_boundary_pos (k : ℤ) :
    uibhbotSeparationFuturePos W H h0
      (boundaryVertex (shiftedStream W 0) h0 k) = ⟨-(k : ℝ), 0⟩ := by
  unfold uibhbotSeparationFuturePos
  rw [boundaryVertex_pos_eq (shiftedStream W 0) h0 (H.1 0) k]
  change (⟨-(seamX (shiftedStream W 0) h0 (H.1 0) k),
    -seamFun (shiftedStream W 0) h0 (H.1 0)
      (seamX (shiftedStream W 0) h0 (H.1 0) k) + 0 +
      seamFun (shiftedStream W 0) h0 (H.1 0)
        (seamX (shiftedStream W 0) h0 (H.1 0) k)⟩ : ℂ) = _
  rw [uibhbotGlue_seamX_eq_int]
  apply Complex.ext
  · rfl
  · dsimp; ring

/-- Every attached past lower-seam endpoint has its rank minus one as abscissa. -/
theorem uibhbotSeparation_past_lower_pos (n e : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    uibhbotSeparationPastPos W hL hR hfin ((kmswStage (kmswPastCode W) n).west e) =
      ⟨(kmswStageRank (kmswPastCode W) n
        ((kmswStage (kmswPastCode W) n).west e) : ℝ) - 1, 0⟩ ∧
    uibhbotSeparationPastPos W hL hR hfin ((kmswStage (kmswPastCode W) n).east e) =
      ⟨(kmswStageRank (kmswPastCode W) n
        ((kmswStage (kmswPastCode W) n).east e) : ℝ) - 1, 0⟩ := by
  obtain ⟨hw, ht, _⟩ := uibhbotPastMonotoneDrawing_seam_endpoints W hfin n e he
  obtain ⟨hsw, hst⟩ := uibhbotPastMonotoneDrawing_seam_endpoint_mem W hfin n e he
  have hyw := uibhbotPastSeamHeight_eq_of_mem W hL hR hsw
  have hyt := uibhbotPastSeamHeight_eq_of_mem W hL hR hst
  constructor
  · change uibhbotAssemblyHalfTurn
      (⟨-((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).west e)).re,
        -((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).west e)).im + 0 +
          uibhbotPastSeamHeight W hL hR
            ((uibhbotPastMonotoneDrawing W hfin).pos
              ((kmswStage (kmswPastCode W) n).west e)).re⟩ : ℂ) = _
    rw [← hyw, hw]
    apply Complex.ext <;> dsimp [uibhbotAssemblyHalfTurn, layoutPos] <;> ring
  · change uibhbotAssemblyHalfTurn
      (⟨-((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).east e)).re,
        -((uibhbotPastMonotoneDrawing W hfin).pos
          ((kmswStage (kmswPastCode W) n).east e)).im + 0 +
          uibhbotPastSeamHeight W hL hR
            ((uibhbotPastMonotoneDrawing W hfin).pos
              ((kmswStage (kmswPastCode W) n).east e)).re⟩ : ℂ) = _
    rw [← hyt, ht]
    apply Complex.ext <;> dsimp [uibhbotAssemblyHalfTurn, layoutPos] <;> ring

/-- Straightened positions match at both endpoints of every covered seam edge. -/
theorem uibhbotSeparation_lower_match (n e : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    ∃ j : ℤ, 0 ≤ j ∧
      kmswPastEdge W e = wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h0 j) ∧
      uibhbotSeparationFuturePos W H h0 (boundaryVertex (shiftedStream W 0) h0 j) =
        uibhbotSeparationPastPos W hL hR hfin ((kmswStage (kmswPastCode W) n).east e) ∧
      uibhbotSeparationFuturePos W H h0
          (boundaryVertex (shiftedStream W 0) h0 (j + 1)) =
        uibhbotSeparationPastPos W hL hR hfin ((kmswStage (kmswPastCode W) n).west e) := by
  obtain ⟨j, hj, hje, hjw, hjt⟩ := uibhbotGlue_past_seam_match W h0 hR n e he
  obtain ⟨hw, ht⟩ := uibhbotSeparation_past_lower_pos W hL hR hfin n e he
  refine ⟨j, hj, hje, ?_, ?_⟩
  · rw [uibhbotSeparation_future_boundary_pos, ht, hjt]
    push_cast
    apply Complex.ext
    · dsimp; ring
    · rfl
  · rw [uibhbotSeparation_future_boundary_pos, hw, hjw]
    push_cast
    apply Complex.ext
    · dsimp; ring
    · rfl

/-- The concrete transferred positions agree at every identified vertex. -/
theorem uibhbotSeparation_positions_compatible (u v : ℕ)
    (huv : wholePlaneVertexι W 0 u = kmswPastVertex W v) :
    uibhbotSeparationFuturePos W H h0 u = uibhbotSeparationPastPos W hL hR hfin v := by
  obtain ⟨n, e, he, hev⟩ := uibhbotGlue_shared_vertex_mem_seam W v ⟨u, huv⟩
  obtain ⟨j, _, hje, hpt, hpw⟩ :=
    uibhbotSeparation_lower_match W H h0 hL hR hfin n e he
  have heb := (kmswStage_boundary_ids_lt_nextEdge (kmswPastCode W) n).2 e (by
    simp only [List.mem_append] at he ⊢
    tauto)
  have hends := edge_endpoints_eq (kmswPastCode W) heb
  rcases hev with hwest | heast
  · have hinc := congrArg (wholePlaneEdgeEast W) hje
    rw [kmswPastEdge_east, ← hends.1, hwest, wholePlaneEdgeEast_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).2.1, ← huv] at hinc
    have hu := wholePlaneVertexι_injective W 0 hinc
    rw [hwest, ← hu] at hpw
    exact hpw
  · have hinc := congrArg (wholePlaneEdgeWest W) hje
    rw [kmswPastEdge_west, ← hends.2, heast, wholePlaneEdgeWest_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).1, ← huv] at hinc
    have hu := wholePlaneVertexι_injective W 0 hinc
    rw [heast, ← hu] at hpt
    exact hpt

/-- The attached past positions lie in the closed upper half-plane. -/
theorem uibhbotSeparation_past_pos_im_nonneg (v : ℕ) :
    0 ≤ (uibhbotSeparationPastPos W hL hR hfin v).im := by
  let P := uibhbotPastMonotoneDrawing W hfin
  have hx : (P.pos v).re ≤ 1 :=
    uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR (Or.inl ⟨v, rfl⟩)
  have hs := uibhbotPastSeamHeight_mem W hL hR (P.pos v).re
  rw [min_eq_left hx] at hs
  have hy := uibhbotPastMonotoneDrawing_above_seam W hfin (Or.inl ⟨v, rfl⟩) hs
  change 0 ≤ -(-(P.pos v).im + 0 +
    uibhbotPastSeamHeight W hL hR (P.pos v).re) - 0
  change uibhbotPastSeamHeight W hL hR (P.pos v).re ≤ (P.pos v).im at hy
  linarith only [hy]

/-- The transferred future positions lie in the closed lower half-plane. -/
theorem uibhbotSeparation_future_pos_im_nonpos (v : ℕ) :
    (uibhbotSeparationFuturePos W H h0 v).im ≤ 0 := by
  have hy := monotoneFamilyDrawing_above_seam (shiftedStream W 0) h0 (H.1 0)
    (Or.inl ⟨v, rfl⟩)
  change seamFun (shiftedStream W 0) h0 (H.1 0)
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).pos v).re ≤
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).pos v).im at hy
  change -((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).pos v).im + 0 +
    seamFun (shiftedStream W 0) h0 (H.1 0)
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).pos v).re ≤ 0
  linarith only [hy]

/-- Each side's concrete transferred vertex positions are injective. -/
theorem uibhbotSeparation_side_positions_injective :
    Function.Injective (uibhbotSeparationFuturePos W H h0) ∧
      Function.Injective (uibhbotSeparationPastPos W hL hR hfin) := by
  constructor
  · exact (uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0)).injective.comp
      (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).pos_injective
  · exact uibhbotAssemblyHalfTurn_involutive.injective.comp
      ((uibhbotPastStraightTransfer W hL hR).injective.comp
        (uibhbotPastMonotoneDrawing W hfin).pos_injective)

/-- Positions from the two sides coincide only at an identified seam vertex. -/
theorem uibhbotSeparation_cross_pos_eq (u v : ℕ)
    (he : uibhbotSeparationFuturePos W H h0 u =
      uibhbotSeparationPastPos W hL hR hfin v) :
    wholePlaneVertexι W 0 u = kmswPastVertex W v := by
  have hp := uibhbotSeparation_past_pos_im_nonneg W hL hR hfin v
  have hf := uibhbotSeparation_future_pos_im_nonpos W H h0 u
  rw [he] at hf
  have hz := le_antisymm hf hp
  obtain ⟨u', hu'⟩ := uibhbotSeparation_past_axis_shared W h0 hL hR hfin v hz
  have hc := uibhbotSeparation_positions_compatible W H h0 hL hR hfin u' v hu'
  have huu := (uibhbotSeparation_side_positions_injective W H h0 hL hR hfin).1
    (he.trans hc.symm)
  exact (congrArg (wholePlaneVertexι W 0) huu).trans hu'

/-- G1: the assembled concrete vertex positions are injective, using only the
future boundary witnesses and the one-sided past hypotheses. -/
theorem uibhbotSeparation_assembly_pos_injective :
    Function.Injective (uibhbotAssemblyPos W (uibhbotSeparationPastPos W hL hR hfin)
      (uibhbotSeparationFuturePos W H h0)) := by
  have hc := uibhbotSeparation_positions_compatible W H h0 hL hR hfin
  obtain ⟨hfi, hpi⟩ := uibhbotSeparation_side_positions_injective W H h0 hL hR hfin
  intro U V he
  rcases vertex_cover W U with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
    rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [uibhbotAssemblyPos_future, uibhbotAssemblyPos_future] at he
    exact congrArg (wholePlaneVertexι W 0) (hfi he)
  · rw [uibhbotAssemblyPos_future, uibhbotAssemblyPos_past W _ _ hc] at he
    exact uibhbotSeparation_cross_pos_eq W H h0 hL hR hfin u v he
  · rw [uibhbotAssemblyPos_past W _ _ hc, uibhbotAssemblyPos_future] at he
    exact (uibhbotSeparation_cross_pos_eq W H h0 hL hR hfin v u he.symm).symm
  · rw [uibhbotAssemblyPos_past W _ _ hc, uibhbotAssemblyPos_past W _ _ hc] at he
    exact congrArg (kmswPastVertex W) (hpi he)

/-- G1 on the almost-sure candidate-assembly event: the assembled positions are
injective, with all previously assembled arc geometry retained. The remaining
drawing fields (G2--G4) are not asserted here. -/
theorem uibhbotCodeLawRel_ae_candidate_glue_geometry_injective :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ _H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
        Function.Injective pos ∧
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
  obtain ⟨P, hPquad, hppos, _⟩ :=
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
  refine ⟨H, h0, pos, arc, ?_,
    uibhbotAssemblyArc_simple W H hfin P F,
    uibhbotAssemblyArc_length W H hfin P F,
    uibhbotAssemblyArc_start W H hfin P F h0 hc,
    uibhbotAssemblyArc_finish W H hfin P F h0 hc,
    uibhbotAssemblyArc_flip W H hfin P F, ?_,
    uibhbotAssemblyArc_locally_finite W H hfin P F h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Function.Injective (uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos)
    rw [hp, hf]
    exact uibhbotSeparation_assembly_pos_injective W H h0 hL hR.1 hfin
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
