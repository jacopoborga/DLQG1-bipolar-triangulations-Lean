/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawing

/-! # Candidate geometry for the half-line UIBHBOT gluing

These constructions retain the future arcs and the off-seam past arcs. They
do not yet constitute a `WholePlaneDrawing`: separation, injectivity and
agreement with the whole-plane rotation remain proof obligations. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap Set
open DirectedDistances.PaperProofs.Section5
open WholePlanePastGlueData

noncomputable section

/-- The orientation-preserving half-turn and translation used to attach the past. -/
@[expose] def uibhbotAssemblyHalfTurn (z : ℂ) : ℂ := -z - 1

/-- The past attachment map is an involution. -/
theorem uibhbotAssemblyHalfTurn_involutive :
    Function.Involutive uibhbotAssemblyHalfTurn := by
  intro z
  simp [uibhbotAssemblyHalfTurn]

/-- The attachment map is affine on every polyline segment. -/
theorem uibhbotAssemblyHalfTurn_affine (p : Polyline) :
    p.AffineOnSegments uibhbotAssemblyHalfTurn := by
  intro i hi
  refine ⟨pastTransferAffine 1 1 0 0 0 0, ?_⟩
  intro z hz
  apply Complex.ext <;> dsimp [uibhbotAssemblyHalfTurn, pastTransferAffine] <;> ring

/-- The concrete PL map taking the complement of the open first quadrant to the
closed upper half-plane. Its two linear pieces meet on the diagonal. -/
@[expose] def uibhbotAssemblyWedgeMap (z : ℂ) : ℂ :=
  ⟨z.im - z.re, -min z.re z.im⟩

/-- The explicit inverse of the map used to open the boundary wedge. -/
@[expose] def uibhbotAssemblyWedgeMapInv (z : ℂ) : ℂ :=
  ⟨-z.im - min z.re 0, -z.im + max z.re 0⟩

/-- Opening the wedge has the stated left inverse. -/
theorem uibhbotAssemblyWedgeMap_leftInverse :
    Function.LeftInverse uibhbotAssemblyWedgeMapInv uibhbotAssemblyWedgeMap := by
  intro z
  by_cases h : z.re ≤ z.im
  · have hd : 0 ≤ z.im - z.re := sub_nonneg.mpr h
    apply Complex.ext <;>
      dsimp [uibhbotAssemblyWedgeMap, uibhbotAssemblyWedgeMapInv] <;>
      simp only [min_eq_left h, min_eq_right hd, max_eq_left hd] <;> ring
  · have h' : z.im ≤ z.re := le_of_not_ge h
    have hd : z.im - z.re ≤ 0 := sub_nonpos.mpr h'
    apply Complex.ext <;>
      dsimp [uibhbotAssemblyWedgeMap, uibhbotAssemblyWedgeMapInv] <;>
      simp only [min_eq_right h', min_eq_left hd, max_eq_right hd] <;> ring

/-- Opening the wedge has the stated right inverse. -/
theorem uibhbotAssemblyWedgeMap_rightInverse :
    Function.RightInverse uibhbotAssemblyWedgeMapInv uibhbotAssemblyWedgeMap := by
  intro z
  by_cases h : z.re ≤ 0
  · have hm : -z.im ≤ -z.im - z.re := by linarith only [h]
    apply Complex.ext <;>
      dsimp [uibhbotAssemblyWedgeMap, uibhbotAssemblyWedgeMapInv] <;>
      rw [min_eq_left h, max_eq_right h] <;>
      simp only [add_zero, min_eq_right hm] <;> ring
  · have h' : 0 ≤ z.re := le_of_not_ge h
    have hm : -z.im ≤ -z.im + z.re := by linarith only [h']
    apply Complex.ext <;>
      dsimp [uibhbotAssemblyWedgeMap, uibhbotAssemblyWedgeMapInv] <;>
      rw [min_eq_right h', max_eq_left h'] <;>
      simp only [sub_zero, min_eq_left hm] <;> ring

/-- Opening the wedge is a homeomorphism, with the explicit inverse above. -/
@[expose] def uibhbotAssemblyWedgeHomeomorph : ℂ ≃ₜ ℂ where
  toFun := uibhbotAssemblyWedgeMap
  invFun := uibhbotAssemblyWedgeMapInv
  left_inv := uibhbotAssemblyWedgeMap_leftInverse
  right_inv := uibhbotAssemblyWedgeMap_rightInverse
  continuous_toFun := by
    unfold uibhbotAssemblyWedgeMap
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp (Complex.continuous_im.sub
      Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp
        (Complex.continuous_re.min Complex.continuous_im).neg).mul continuous_const)
  continuous_invFun := by
    unfold uibhbotAssemblyWedgeMapInv
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp (Complex.continuous_im.neg.sub
      (Complex.continuous_re.min continuous_const))).add
      ((Complex.continuous_ofReal.comp (Complex.continuous_im.neg.add
        (Complex.continuous_re.max continuous_const))).mul continuous_const)

/-- The wedge maps exactly into the closed upper half-plane. -/
theorem uibhbotAssemblyWedgeMap_im_nonneg_iff (z : ℂ) :
    0 ≤ (uibhbotAssemblyWedgeMap z).im ↔ z.re ≤ 0 ∨ z.im ≤ 0 := by
  change 0 ≤ -min z.re z.im ↔ _
  rw [neg_nonneg, min_le_iff]

/-- The two nonnegative boundary rays become the entire real axis. -/
theorem uibhbotAssemblyWedgeMap_im_zero_iff (z : ℂ) :
    (uibhbotAssemblyWedgeMap z).im = 0 ↔
      (z.re = 0 ∧ 0 ≤ z.im) ∨ (z.im = 0 ∧ 0 ≤ z.re) := by
  change -min z.re z.im = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h
    have ha : 0 ≤ z.re := h ▸ min_le_left z.re z.im
    have hb : 0 ≤ z.im := h ▸ min_le_right z.re z.im
    by_cases hab : z.re ≤ z.im
    · exact Or.inl ⟨(min_eq_left hab).symm.trans h, hb⟩
    · exact Or.inr ⟨(min_eq_right (le_of_not_ge hab)).symm.trans h, ha⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rw [ha, min_eq_left hb]
    · rw [hb, min_eq_right ha]

/-- Vertex positions give precedence to run zero and otherwise use the past. -/
@[expose] def uibhbotAssemblyPos (W : ℤ → Fin 3) (p f : ℕ → ℂ)
    (V : WholePlaneVertex W) : ℂ := by
  classical
  exact if h : V ∈ range (wholePlaneVertexι W 0) then f (Classical.choose h)
    else p (Classical.choose ((vertex_cover W V).resolve_left h))

/-- Every future vertex keeps its position. -/
theorem uibhbotAssemblyPos_future (W : ℤ → Fin 3) (p f : ℕ → ℂ) (v : ℕ) :
    uibhbotAssemblyPos W p f (wholePlaneVertexι W 0 v) = f v := by
  classical
  have h : wholePlaneVertexι W 0 v ∈ range (wholePlaneVertexι W 0) := ⟨v, rfl⟩
  unfold uibhbotAssemblyPos
  rw [dite_eq_left h]
  exact congrArg f (wholePlaneVertexι_injective W 0 (Classical.choose_spec h))

/-- Compatible past positions are retained, including shared vertices. -/
theorem uibhbotAssemblyPos_past (W : ℤ → Fin 3) (p f : ℕ → ℂ)
    (hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v → f u = p v)
    (v : ℕ) : uibhbotAssemblyPos W p f (kmswPastVertex W v) = p v := by
  classical
  unfold uibhbotAssemblyPos
  by_cases h : kmswPastVertex W v ∈ range (wholePlaneVertexι W 0)
  · rw [dite_eq_left h]
    exact hc _ v (Classical.choose_spec h)
  · rw [dite_eq_right h]
    exact congrArg p (kmswPastVertex_injective W
      (Classical.choose_spec ((vertex_cover W (kmswPastVertex W v)).resolve_left h)))

/-- Future arcs take precedence; the remaining arcs use the reversed past dart. -/
@[expose] def uibhbotAssemblyArc (W : ℤ → Fin 3) (p f : (ℕ × Bool) → Polyline)
    (D : WholePlaneDart W) : Polyline := by
  classical
  exact if h : D.1 ∈ range (wholePlaneEdgeι W 0) then f (Classical.choose h, D.2)
    else p (Classical.choose ((kmswPastEdge_cover W D.1).resolve_right h), !D.2)

/-- All future polylines are retained exactly. -/
theorem uibhbotAssemblyArc_future (W : ℤ → Fin 3) (p f : (ℕ × Bool) → Polyline)
    (d : ℕ × Bool) :
    uibhbotAssemblyArc W p f (wholePlaneDartι W 0 d) = f d := by
  classical
  have h : (wholePlaneDartι W 0 d).1 ∈ range (wholePlaneEdgeι W 0) := ⟨d.1, rfl⟩
  unfold uibhbotAssemblyArc
  rw [dite_eq_left h]
  have he : Classical.choose h = d.1 :=
    wholePlaneEdgeι_injective W 0 (Classical.choose_spec h)
  rw [he]
  rfl

/-- The past polyline is retained exactly away from the shared half-line. -/
theorem uibhbotAssemblyArc_past (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (p f : (ℕ × Bool) → Polyline)
    (d : ℕ × Bool) (hd : ¬ kmswPastSeamEdge W d.1) :
    uibhbotAssemblyArc W p f (kmswPastDart W d) = p d := by
  classical
  have h : (kmswPastDart W d).1 ∉ range (wholePlaneEdgeι W 0) :=
    fun h => hd ((kmswPastEdge_mem_runZero_iff W h0 d.1).mp h)
  unfold uibhbotAssemblyArc
  rw [dite_eq_right h]
  have he : Classical.choose
      ((kmswPastEdge_cover W (kmswPastDart W d).1).resolve_right h) = d.1 :=
    kmswPastEdge_injective W (Classical.choose_spec
      ((kmswPastEdge_cover W (kmswPastDart W d).1).resolve_right h))
  rw [he]
  rcases d with ⟨e, b⟩
  cases b <;> rfl

section DrawingFields

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))

local notation "pos" => uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
local notation "arc" => uibhbotAssemblyArc W
  (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc

/-- Every candidate glued arc is simple. -/
theorem uibhbotAssemblyArc_simple (D : WholePlaneDart W) : (arc D).IsSimple := by
  classical
  unfold uibhbotAssemblyArc
  split
  · exact F.arc_simple _
  · exact Polyline.isSimple_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)
      uibhbotAssemblyHalfTurn_involutive.injective.injOn (P.arc_simple _)

/-- Every candidate glued arc has at least two points. -/
theorem uibhbotAssemblyArc_length (D : WholePlaneDart W) :
    2 ≤ (arc D).points.length := by
  classical
  unfold uibhbotAssemblyArc
  split
  · exact F.arc_length _
  · rw [Polyline.length_mapPoints]
    exact P.arc_length _

/-- The candidate arcs commute with geometric reversal. -/
theorem uibhbotAssemblyArc_flip (D : WholePlaneDart W) :
    arc (wholePlaneDartFlip W D) = (arc D).reverse := by
  classical
  rcases D with ⟨E, b⟩
  change uibhbotAssemblyArc W _ _ (E, !b) = _
  unfold uibhbotAssemblyArc
  by_cases h : E ∈ range (wholePlaneEdgeι W 0)
  · rw [dite_eq_left h, dite_eq_left h]
    exact F.arc_flip (_, b)
  · rw [dite_eq_right h, dite_eq_right h]
    dsimp only
    rw [P.arc_flip (_, !b)]
    exact Polyline.mapPoints_reverse _ _

variable (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
    F.pos u = uibhbotAssemblyHalfTurn (P.pos v))

include h0 hc in

/-- Each candidate arc starts at the assembled incident vertex. -/
theorem uibhbotAssemblyArc_start (D : WholePlaneDart W) :
    (arc D).start = pos (wholePlaneDartVertex W D) := by
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [uibhbotAssemblyArc_future, wholePlaneDartVertex_ι, uibhbotAssemblyPos_future]
    exact F.arc_start d
  · rw [uibhbotAssemblyArc_past W h0 _ _ d hd, Polyline.start_mapPoints,
      pastDart_vertex,
      uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc,
      P.arc_start]
    rfl

include h0 hc in
/-- Each candidate arc ends at the assembled reversed incident vertex. -/
theorem uibhbotAssemblyArc_finish (D : WholePlaneDart W) :
    (arc D).finish = pos (wholePlaneDartVertex W (wholePlaneDartFlip W D)) := by
  have hs := uibhbotAssemblyArc_start W H hfin P F h0 hc (wholePlaneDartFlip W D)
  rw [uibhbotAssemblyArc_flip W H hfin P F, Polyline.start_reverse] at hs
  exact hs

include h0 in
/-- Bounded sets meet only finitely many candidate glued arcs. -/
theorem uibhbotAssemblyArc_locally_finite (K : Set ℂ) (hK : Bornology.IsBounded K) :
    {D | (K ∩ (arc D).image).Nonempty}.Finite := by
  have hcont : Continuous uibhbotAssemblyHalfTurn :=
    continuous_id.neg.sub continuous_const
  have hb : Bornology.IsBounded (uibhbotAssemblyHalfTurn '' closure K) :=
    (hK.isCompact_closure.image hcont).isBounded
  have hf := (F.locally_finite K hK).image (wholePlaneDartι W 0)
  have hp := (P.locally_finite (uibhbotAssemblyHalfTurn '' closure K) hb).image
    (kmswPastDart W)
  apply (hf.union hp).subset
  intro D hD
  change (K ∩ (arc D).image).Nonempty at hD
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
  · apply Or.inl
    apply mem_image_of_mem
    rwa [uibhbotAssemblyArc_future] at hD
  · apply Or.inr
    apply mem_image_of_mem
    obtain ⟨z, hzK, hz⟩ := hD
    rw [uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, ⟨uibhbotAssemblyHalfTurn y, subset_closure hzK,
      uibhbotAssemblyHalfTurn_involutive y⟩, hy⟩

end DrawingFields

/-- Both orientations of a future boundary edge lie on the unstraightened seam graph. -/
theorem uibhbotAssembly_future_seam_graph (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w) (k : ℤ) (b : Bool) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (boundaryOuterEdge w h k, b)).image ⊆ {z : ℂ | z.im = seamFun w h hfin z.re} := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  intro z hz
  rw [seamFun_graph w h hfin]
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  cases b with
  | true => exact hz
  | false =>
      have hr := P.arc_flip (boundaryOuterEdge w h k, true)
      change P.arc (boundaryOuterEdge w h k, false) = _ at hr
      change z ∈ (P.arc (boundaryOuterEdge w h k, false)).image at hz
      rw [hr, Polyline.image_reverse_transfer] at hz
      exact hz

/-- The straight future drawing has every boundary arc, in either orientation,
on the real axis, as well as its exact integer boundary vertex positions. -/
theorem uibhbotAssembly_future_straightDrawing (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w) :
    ∃ F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot w hfin) (kmswLimitDartVertex w),
      F.image ⊆ {z : ℂ | z.im ≤ 0} ∧
      (∀ k : ℤ, F.pos (boundaryVertex w h k) = ⟨-(k : ℝ), 0⟩) ∧
      ∀ k : ℤ, ∀ b : Bool,
        (F.arc (boundaryOuterEdge w h k, b)).image ⊆ {z : ℂ | z.im = 0} := by
  obtain ⟨F, hFim, hFpos, hp, ha⟩ := uibhbotGlue_future_straightDrawing w h hfin
  refine ⟨F, hFim, hFpos, ?_⟩
  intro k b z hz
  rw [ha] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hg := uibhbotAssembly_future_seam_graph w h hfin k b hy
  change -y.im + 0 + seamFun w h hfin y.re = 0
  rw [← hg]
  ring

/-- A future vertex shared with the past has a future boundary label. This uses
only the one-sided past seam, rather than boundary-hit witnesses for the past. -/
theorem uibhbotAssembly_shared_vertex_future_boundary (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (u v : ℕ)
    (huv : wholePlaneVertexι W 0 u = kmswPastVertex W v) :
    ∃ k : ℤ, u = boundaryVertex (shiftedStream W 0) h0 k := by
  obtain ⟨n, e, he, hev⟩ := uibhbotGlue_shared_vertex_mem_seam W v ⟨u, huv⟩
  obtain ⟨j, hje⟩ := kmswPastSeamEdge_image_boundary W h0 e ⟨n, he⟩
  have heb := (kmswStage_boundary_ids_lt_nextEdge (kmswPastCode W) n).2 e (by
    simp only [List.mem_append] at he ⊢
    tauto)
  have hends := edge_endpoints_eq (kmswPastCode W) heb
  rcases hev with hw | ht
  · have hinc := congrArg (wholePlaneEdgeEast W) hje
    rw [kmswPastEdge_east, ← hends.1, hw, wholePlaneEdgeEast_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).2.1, ← huv] at hinc
    exact ⟨j + 1, wholePlaneVertexι_injective W 0 hinc⟩
  · have hinc := congrArg (wholePlaneEdgeWest W) hje
    rw [kmswPastEdge_west, ← hends.2, ht, wholePlaneEdgeWest_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).1, ← huv] at hinc
    exact ⟨j, wholePlaneVertexι_injective W 0 hinc⟩

/-- The concrete straight past drawing lies in a quadrant after the attachment
half-turn. Its exact transported vertex and arc geometry are retained. This
does not identify its remaining boundary with either ray of that quadrant. -/
theorem uibhbotAssembly_past_straightDrawing_quadrant (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
      P.image ⊆ {z : ℂ | z.im ≤ 0 ∧ -1 ≤ z.re} ∧
      P.pos = uibhbotPastStraightTransfer W hL hR ∘ (uibhbotPastMonotoneDrawing W hfin).pos ∧
      ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
        ((uibhbotPastMonotoneDrawing W hfin).arc d).image := by
  obtain ⟨P, hp, ha⟩ := uibhbotPastStraightDrawing_exists W hL hR hfin
  let P0 := uibhbotPastMonotoneDrawing W hfin
  let T := uibhbotPastStraightTransfer W hL hR
  have him (z : ℂ) (hz : z ∈ P0.image) : (T z).im ≤ 0 ∧ -1 ≤ (T z).re := by
    have hx : z.re ≤ 1 := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hz
    have hseam := uibhbotPastSeamHeight_mem W hL hR z.re
    rw [min_eq_left hx] at hseam
    have hbelow := uibhbotPastMonotoneDrawing_above_seam W hfin hz hseam
    change -z.im + 0 + uibhbotPastSeamHeight W hL hR z.re ≤ 0 ∧ -1 ≤ -z.re
    constructor <;> linarith only [hbelow, hx]
  refine ⟨P, ?_, hp, ha⟩
  intro z hz
  rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
  · rw [hp]
    exact him (P0.pos v) (Or.inl ⟨v, rfl⟩)
  · rw [ha d] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact him y (Or.inr ⟨d, hy⟩)

/-- Almost surely there are assembled vertex positions and locally finite simple
geometric arcs with the correct incidence and reversal. This deliberately does
not assert injectivity, disjoint interiors, rotation agreement or both-mode scope. -/
theorem uibhbotCodeLawRel_ae_candidate_glue_geometry :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ _H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
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
  filter_upwards [uibhbotCodeLawRel_ae_seam_compatible] with W h
  obtain ⟨H, h0, hfin, P, F0, hPim, _, hF0pos, _, hc, _⟩ := h
  obtain ⟨F, hFim, hFpos, hFarc⟩ :=
    uibhbotAssembly_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hcompat : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    obtain ⟨k, hk⟩ := uibhbotAssembly_shared_vertex_future_boundary W h0 u v huv
    calc
      F.pos u = ⟨-(k : ℝ), 0⟩ := hk ▸ hFpos k
      _ = F0.pos u := (hk ▸ hF0pos k).symm
      _ = uibhbotAssemblyHalfTurn (P.pos v) := hc u v huv
  let pos := uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
  let arc := uibhbotAssemblyArc W
    (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc
  refine ⟨H, h0, pos, arc,
    uibhbotAssemblyArc_simple W H hfin P F,
    uibhbotAssemblyArc_length W H hfin P F,
    uibhbotAssemblyArc_start W H hfin P F h0 hcompat,
    uibhbotAssemblyArc_finish W H hfin P F h0 hcompat,
    uibhbotAssemblyArc_flip W H hfin P F, ?_,
    uibhbotAssemblyArc_locally_finite W H hfin P F h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hcompat]
    have hp : (P.pos v).im ≤ 0 := hPim (Or.inl ⟨v, rfl⟩)
    change 0 ≤ -(P.pos v).im - 0
    linarith only [hp]
  · intro k b
    change (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 _)).image ⊆ _
    rw [uibhbotAssemblyArc_future]
    exact hFarc k b
  · intro d hd z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (kmswPastDart W d)).image at hz
    rw [uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hp : y.im ≤ 0 := hPim (Or.inr ⟨d, hy⟩)
    change 0 ≤ -y.im - 0
    linarith only [hp]
  · intro d z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 d)).image at hz
    rw [uibhbotAssemblyArc_future] at hz
    exact hFim (Or.inr ⟨d, hz⟩)

end
end DirectedDistances.KMSW
