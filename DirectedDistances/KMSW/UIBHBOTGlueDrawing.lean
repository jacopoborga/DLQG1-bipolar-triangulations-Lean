/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTPastStraightDrawing
public import DirectedDistances.KMSW.WholePlaneRootedMapFields
import DirectedDistances.KMSW.MonotoneSeamVertices
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Matching the one-sided UIBHBOT seam

The past seam is matched only where it is covered. No boundary-hit witness
for the conditioned past is used. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5 Set

noncomputable section

/-- Every finite lower-boundary edge has horizontal rank gap exactly one. -/
theorem uibhbotGlue_lower_rank_gap (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) :
    kmswStageRank w n ((kmswStage w n).east e) -
      kmswStageRank w n ((kmswStage w n).west e) = 1 := by
  induction n with
  | zero =>
      have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
      subst e
      norm_num [kmswStage, kmswInit, kmswStageRank]
  | succ n ih =>
      have hold (hm : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) :
          kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) -
            kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west e) = 1 := by
        have hb := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
          simp only [List.mem_append] at hm ⊢
          tauto)
        obtain ⟨hw, ht⟩ := kmswStage_endpoints_stable w (Nat.le_succ n) hb
        obtain ⟨hvw, hvt⟩ := kmswStage_endpoints_lt_nextVertex w n e hb
        rw [hw, ht, layoutRank_old_vertex w n _ hvt,
          layoutRank_old_vertex w n _ hvw]
        exact ih hm
      by_cases h0 : w n = 0
      · cases hs : (kmswStage w n).UL.dropLast.reverse with
        | cons a as =>
            apply hold
            simpa [kmswStage, kmswStep, kmswCodeStep, h0, hs, kmswStepOfStep,
              State.addEdge] using he
        | nil =>
            have hm : e = (kmswStage w n).nextEdge + 1 ∨
                e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR := by
              simpa [kmswStage, kmswStep, kmswCodeStep, h0, hs, kmswStepOfStep,
                State.addEdge, List.mem_append, List.mem_cons, or_assoc] using he
            rcases hm with rfl | hm
            · have hg := freshLeft_missing_edge_rank_gap w n h0 hs
              dsimp only [layoutPos] at hg
              exact_mod_cast hg
            · exact hold hm
      · by_cases h1 : w n = 1
        · apply hold
          simpa [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
            State.addEdge] using he
        · have h2 : w n = 2 := by
            apply Fin.ext
            have := (w n).isLt
            have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
            have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
            omega
          cases hs : (kmswStage w n).UR with
          | cons a as =>
              apply hold
              simpa [kmswStage, kmswStep, kmswCodeStep, h2, hs,
                kmswStepOfStep] using he
          | nil =>
              have hm : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR ∨
                  e = (kmswStage w n).nextEdge := by
                simpa [kmswStage, kmswStep, kmswCodeStep, h2, hs,
                  kmswStepOfStep, State.addEdge, List.mem_append, List.mem_singleton,
                  or_assoc] using he
              rcases hm with hm | rfl
              · exact hold hm
              · have hv := (kmswStage_endpoints_lt_nextVertex w n _
                    (kmswStage_boundary_ids_lt_nextEdge w n).1).2
                have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
                    (kmswStage w n).east (kmswStage w n).active := by
                  simp [kmswStage, kmswStep, kmswCodeStep, h2, hs,
                    kmswStepOfStep, State.addEdge]
                have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
                    (kmswStage w n).nextVertex := by
                  simp [kmswStage, kmswStep, kmswCodeStep, h2, hs,
                    kmswStepOfStep, State.addEdge]
                rw [hw, ht, layoutRank_old_vertex w n _ hv]
                simp [kmswStageRank, h2, hs]

/-- The future lower seam's hit labels have their exact integer abscissas. -/
theorem uibhbotGlue_seamX_eq_int (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hfin : KMSWFiniteIncidence w) (k : ℤ) : seamX w h hfin k = (k : ℝ) := by
  have hstep (j : ℤ) : seamX w h hfin (j + 1) - seamX w h hfin j = 1 := by
    obtain ⟨n, hn⟩ := boundaryOuterEdge_mem_finite_LL_LR w h j
    let e := boundaryOuterEdge w h j
    have he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR :=
      List.mem_append.mpr hn
    have hb := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
    obtain ⟨hw, ht⟩ := edge_endpoints_eq w hb
    obtain ⟨hvw, hvt⟩ := kmswStage_endpoints_lt_nextVertex w n e hb
    have hend := boundaryOuterEdge_endpoints w h j
    have hpw : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
        ((kmswStage w n).west e) = layoutPos w n ((kmswStage w n).west e) :=
      monotoneLimitDrawing_pos_layout w hfin
      (fun m => ⟨familyQ w (monotone_family_all w) m,
        ⟨familyG w (monotone_family_all w) m⟩⟩) n _ hvw
    have hpt : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
        ((kmswStage w n).east e) = layoutPos w n ((kmswStage w n).east e) :=
      monotoneLimitDrawing_pos_layout w hfin
      (fun m => ⟨familyQ w (monotone_family_all w) m,
        ⟨familyG w (monotone_family_all w) m⟩⟩) n _ hvt
    have hwe : (kmswStage w n).west e = boundaryVertex w h j := hw.trans hend.1
    have hte : (kmswStage w n).east e = boundaryVertex w h (j + 1) := ht.trans hend.2.1
    unfold seamX
    rw [← hwe, ← hte, hpw, hpt]
    dsimp only [layoutPos]
    exact_mod_cast uibhbotGlue_lower_rank_gap w n e he
  have hz : seamX w h hfin 0 = 0 := by
    unfold seamX
    rw [boundaryVertex_zero]
    have hp : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos 0 =
        layoutPos w 0 0 := monotoneLimitDrawing_pos_layout w hfin
      (fun m => ⟨familyQ w (monotone_family_all w) m,
        ⟨familyG w (monotone_family_all w) m⟩⟩) 0 0 (by change 0 < 2; omega)
    rw [hp]
    norm_num [layoutPos, kmswStageRank]
  induction k using Int.induction_on with
  | zero => simpa only [Int.cast_zero] using hz
  | succ n ih =>
      have hs := hstep (n : ℤ)
      rw [ih] at hs
      push_cast at hs ⊢
      linarith only [hs]
  | pred n ih =>
      have hs := hstep (-(n : ℤ) - 1)
      have hi : (-(n : ℤ) - 1) + 1 = -(n : ℤ) := by omega
      rw [hi, ih] at hs
      push_cast at hs ⊢
      linarith only [hs]


/-- On the covered past half-line, the future edge index is nonnegative and its
endpoints have complementary ranks. This uses only future boundary hits. -/
theorem uibhbotGlue_past_seam_match (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (n e : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
    ∃ j : ℤ, 0 ≤ j ∧
      kmswPastEdge W e = wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h0 j) ∧
      kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).west e) =
        -(j : ℚ) ∧
      kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).east e) =
        1 - (j : ℚ) := by
  let w := kmswPastCode W
  let s := kmswStage w n
  let es := s.LL ++ s.LR
  let p (f : ℕ) : Prop := ∃ j : ℤ, 0 ≤ j ∧
    kmswPastEdge W f = wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h0 j) ∧
    kmswStageRank w n (s.west f) = -(j : ℚ) ∧
    kmswStageRank w n (s.east f) = 1 - (j : ℚ)
  have hb (f : ℕ) (hf : f ∈ es) : f < s.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [es, s, List.mem_append] at hf ⊢
    tauto
  have hroot (v : ℕ) (hv : v < 2) :
      kmswStageRank w n v = kmswStageRank w 0 v := by
    have hv0 : v < (kmswStage w 0).nextVertex := hv
    have hp : layoutPos w n v = layoutPos w 0 v := by
      clear he hb p es s e
      induction n with
      | zero => rfl
      | succ m ih =>
          rw [layoutPos_old_vertex w m v
            (hv0.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le m))), ih]
    have hr := congrArg Complex.re hp
    dsimp only [layoutPos] at hr
    exact_mod_cast hr
  have he0 : 0 < s.nextEdge :=
    (kmsw_edge_allocated_by_self w 0).trans_le
      (kmswStage_nextEdge_mono w (Nat.zero_le n))
  have hends0 := edge_endpoints_eq w he0
  have hw0 : s.west 0 = 0 := hends0.1
  have ht0 : s.east 0 = 1 := hends0.2
  have hp0 : p 0 := by
    refine ⟨0, le_rfl, ?_, ?_, ?_⟩
    · rw [boundaryOuterEdge_zero, kmswPastEdge_root]
    · rw [hw0, hroot 0 (by omega)]
      norm_num [kmswStageRank]
    · rw [ht0, hroot 1 (by omega)]
      norm_num [kmswStageRank]
  have hchain : List.IsChain (fun x y => x ∈ es ∧ y ∈ es ∧ s.east x = s.west y) es :=
    ((kmswStage_boundary_chain_invariant w n).2.1).imp_of_mem_imp
      (fun x y hx hy hxy => ⟨hx, hy, hxy⟩)
  have hprop : ∀ ⦃x y : ℕ⦄, (x ∈ es ∧ y ∈ es ∧ s.east x = s.west y) → p y → p x := by
    intro x y hxy hy
    obtain ⟨j, hj, hje, hjw, hjt⟩ := hy
    obtain ⟨i, hie⟩ := kmswPastSeamEdge_image_boundary W h0 x ⟨n, hxy.1⟩
    have hendsx := edge_endpoints_eq w (hb x hxy.1)
    have hendsy := edge_endpoints_eq w (hb y hxy.2.1)
    have hsame : wholePlaneEdgeWest W (kmswPastEdge W x) =
        wholePlaneEdgeEast W (kmswPastEdge W y) := by
      rw [kmswPastEdge_west, kmswPastEdge_east, ← hendsx.2, ← hendsy.1]
      exact congrArg (kmswPastVertex W) hxy.2.2
    rw [hie, hje, wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 i).1,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).2.1] at hsame
    have hi : i = j + 1 := boundaryVertex_injective _ h0
      (wholePlaneVertexι_injective W 0 hsame)
    have hgap := uibhbotGlue_lower_rank_gap w n x hxy.1
    have hxe : kmswStageRank w n (s.east x) = -(j : ℚ) := by
      rw [hxy.2.2, hjw]
    refine ⟨i, by omega, hie, ?_, ?_⟩
    · rw [hi]
      push_cast
      linarith only [hgap, hxe]
    · rw [hi]
      push_cast
      linarith only [hxe]
  have hlast : ∀ hne : es ≠ [], p (es.getLast hne) := by
    intro hne
    have hLR : s.LR = [0] := uibhbotPastStage_LR_eq_root W hR n
    have hlast0 : es.getLast hne = 0 := by
      simp only [es, hLR, List.getLast_append_singleton]
    rw [hlast0]
    exact hp0
  exact hchain.backwards_induction p es hprop hlast e he

/-- An orientation-preserving straightening of the future seam. -/
@[expose] def uibhbotGlueFutureTransfer (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w) : ℂ ≃ₜ ℂ :=
  pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) (seamFun w h hfin)
    continuous_const (seamFun_continuous w h hfin)

/-- The future admits a straight-seam drawing, with unchanged rotation, lying
below the real axis. Its boundary vertex of label k is exactly (-k,0). -/
theorem uibhbotGlue_future_straightDrawing (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w) :
    ∃ F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot w hfin) (kmswLimitDartVertex w),
      F.image ⊆ {z : ℂ | z.im ≤ 0} ∧
      (∀ k : ℤ, F.pos (boundaryVertex w h k) = ⟨-(k : ℝ), 0⟩) ∧
      F.pos = uibhbotGlueFutureTransfer w h hfin ∘
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos ∧
      ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer w h hfin ''
        ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hmono (d : ℕ × Bool) : (P.arc d).XMonotone ∨ (P.arc d).reverse.XMonotone := by
    rcases d with ⟨e, b⟩
    have ha : P.arc (e, b) = if b then (layoutArc w e e).reverse else layoutArc w e e :=
      monotoneLimitDrawing_arc_layout w hfin _ e e (kmsw_edge_allocated_by_self w e) b
    rw [ha]
    cases b
    · exact Or.inl (layoutArc_points_pairwise w e e (kmsw_edge_allocated_by_self w e))
    · right
      rw [ite_eq_left rfl, Polyline.reverse_reverse]
      exact layoutArc_points_pairwise w e e (kmsw_edge_allocated_by_self w e)
  have haff (s t : ℝ) (hst : s < t)
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
  obtain ⟨F, hp, ha⟩ := PLDrawing.transfer P hmono (uibhbotGlueFutureTransfer w h hfin)
    (seamCutSet w h hfin) (seamCutSet_inter_Icc_finite w h hfin) haff
  have him : ∀ z ∈ P.image, (uibhbotGlueFutureTransfer w h hfin z).im ≤ 0 := by
    intro z hz
    have habove : seamFun w h hfin z.re ≤ z.im :=
      monotoneFamilyDrawing_above_seam w h hfin hz
    change -z.im + 0 + seamFun w h hfin z.re ≤ 0
    linarith only [habove]
  refine ⟨F, ?_, ?_, hp, fun d => (ha d).1⟩
  · intro z hz
    rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
    · rw [hp]
      exact him (P.pos v) (Or.inl ⟨v, rfl⟩)
    · rw [(ha d).1] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact him y (Or.inr ⟨d, hy⟩)
  · intro k
    rw [hp]
    change uibhbotGlueFutureTransfer w h hfin (P.pos (boundaryVertex w h k)) = _
    rw [boundaryVertex_pos_eq w h hfin k]
    change (⟨-(seamX w h hfin k),
      -seamFun w h hfin (seamX w h hfin k) + 0 +
        seamFun w h hfin (seamX w h hfin k)⟩ : ℂ) = _
    rw [uibhbotGlue_seamX_eq_int]
    exact Complex.ext rfl (by dsimp; ring)


/-- Every vertex shared by past and future is an endpoint of a finite past lower
seam edge. No two-sided boundary enumeration of the past is needed. -/
theorem uibhbotGlue_shared_vertex_mem_seam (W : ℤ → Fin 3) (v : ℕ)
    (hv0 : kmswPastVertex W v ∈ range (wholePlaneVertexι W 0)) :
    ∃ n e, e ∈ (kmswStage (kmswPastCode W) n).LL ++
        (kmswStage (kmswPastCode W) n).LR ∧
      ((kmswStage (kmswPastCode W) n).west e = v ∨
        (kmswStage (kmswPastCode W) n).east e = v) := by
  obtain ⟨u, hu⟩ := hv0
  let N := 4 * v + 1
  have hv : v < (kmswStage (kmswPastCode W) N).nextVertex := vertex_allocated_at _ v
  have hbound : kmswPastStageVertex W N v <
      (kmswStage (shiftedStream W N) N).nextVertex := by
    obtain ⟨S, hS, hSv⟩ := kmswSlotVertex_surjective (kmswPastCode W) N v hv
    change kmswReversalPhi (kmswPastCode W) (shiftedStream W N) N v < _
    rw [← hSv, kmswReversalPhi_slot _ _ N (kmswPastCode_rev W N) S hS]
    apply kmswSlotVertex_lt
    rw [KMSWSlot.time_mirror]
    exact Nat.sub_le _ _
  have hmap : kmswWindowVertexMapInf (shiftedStream W N) N u =
      kmswPastStageVertex W N v := by
    apply wholePlaneVertexι_injective W N
    change wholePlaneVertexι W N (wholePlaneVertexTrans W 0 N (Nat.zero_le N) u) = _
    exact (congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N)) u).trans
      (hu.trans (kmswPastVertex_eq_stage W N v hv))
  have hb := WholePlanePastGlueData.windowVertex_boundary_or_new
    (shiftedStream W N) N (4 * u + 1) u
  change (∃ e ∈ (kmswStage (shiftedStream W N) N).UL ++
    (kmswStage (shiftedStream W N) N).UR,
    (kmswStage (shiftedStream W N) N).west e =
      kmswWindowVertexMapInf (shiftedStream W N) N u ∨
    (kmswStage (shiftedStream W N) N).east e =
      kmswWindowVertexMapInf (shiftedStream W N) N u) ∨
    (kmswStage (shiftedStream W N) N).nextVertex ≤
      kmswWindowVertexMapInf (shiftedStream W N) N u at hb
  rw [hmap] at hb
  obtain hb | hb := hb
  · obtain ⟨z, hz, hphi⟩ := kmswReversalPhi_lower_preimage
      (kmswPastCode W) (shiftedStream W N) N (kmswPastCode_rev W N) _ hb
    have hzb : z < (kmswStage (kmswPastCode W) N).nextVertex := by
      obtain ⟨e, he, hez⟩ := hz
      have heb : e < (kmswStage (kmswPastCode W) N).nextEdge := by
        apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
        simp only [List.mem_append] at he ⊢
        tauto
      have hend := kmswStage_endpoints_lt_nextVertex (kmswPastCode W) N e heb
      rcases hez with hez | hez
      · exact hez ▸ hend.1
      · exact hez ▸ hend.2
    have hzv : z = v := by
      apply kmswPastVertex_injective W
      rw [kmswPastVertex_eq_stage W N z hzb, kmswPastVertex_eq_stage W N v hv]
      exact congrArg (wholePlaneVertexι W N) hphi
    obtain ⟨e, he, hev⟩ := hz
    exact ⟨N, e, he, hzv ▸ hev⟩
  · exact (not_le_of_gt hbound hb).elim

/-- Almost surely the straight future seam and the rotated straight past seam
agree at every shared vertex, with their reversed endpoint order explicit.
The past is moved by the orientation-preserving half-turn and translation
`z ↦ -z - 1`; the future label j then has position (-j,0). Only nonnegative
future edge labels are matched. This is seam compatibility, not a glued
whole-plane drawing or a face-correspondence assertion. -/
theorem uibhbotCodeLawRel_ae_seam_compatible :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hfin : KMSWFiniteIncidence (kmswPastCode W),
      ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
      ∃ F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (shiftedStream W 0) (H.1 0))
          (kmswLimitDartVertex (shiftedStream W 0)),
        P.image ⊆ {z : ℂ | z.im ≤ 0} ∧
        F.image ⊆ {z : ℂ | z.im ≤ 0} ∧
        (∀ k : ℤ, F.pos (boundaryVertex (shiftedStream W 0) h0 k) = ⟨-(k : ℝ), 0⟩) ∧
        StrictAnti (fun k : ℤ => (F.pos (boundaryVertex (shiftedStream W 0) h0 k)).re) ∧
        (∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
          F.pos u = -P.pos v - 1) ∧
        ∀ n e, e ∈ (kmswStage (kmswPastCode W) n).LL ++
            (kmswStage (kmswPastCode W) n).LR →
          ∃ j : ℤ, 0 ≤ j ∧
            kmswPastEdge W e = wholePlaneEdgeι W 0
              (boundaryOuterEdge (shiftedStream W 0) h0 j) ∧
            F.pos (boundaryVertex (shiftedStream W 0) h0 j) =
              -P.pos ((kmswStage (kmswPastCode W) n).east e) - 1 ∧
            F.pos (boundaryVertex (shiftedStream W 0) h0 (j + 1)) =
              -P.pos ((kmswStage (kmswPastCode W) n).west e) - 1 := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses,
    uibhbotCodeLawRel_ae_past_straightDrawing,
    uibhbotCodeLawRel_ae_past_R_nonneg] with W hH hhit hpast hR
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨hfin, P, hPim, hPpos⟩ := hpast
  obtain ⟨F, hFim, hFpos, _, _⟩ :=
    uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hmatch (n e : ℕ) (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++
      (kmswStage (kmswPastCode W) n).LR) :
      ∃ j : ℤ, 0 ≤ j ∧
        kmswPastEdge W e = wholePlaneEdgeι W 0
          (boundaryOuterEdge (shiftedStream W 0) h0 j) ∧
        F.pos (boundaryVertex (shiftedStream W 0) h0 j) =
          -P.pos ((kmswStage (kmswPastCode W) n).east e) - 1 ∧
        F.pos (boundaryVertex (shiftedStream W 0) h0 (j + 1)) =
          -P.pos ((kmswStage (kmswPastCode W) n).west e) - 1 := by
    obtain ⟨j, hj, hje, hjw, hjt⟩ := uibhbotGlue_past_seam_match W h0 hR.1 n e he
    obtain ⟨hwp, htp⟩ := hPpos n e he
    refine ⟨j, hj, hje, ?_, ?_⟩
    · rw [hFpos, htp, hjt]
      push_cast
      apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im] <;> ring
    · rw [hFpos, hwp, hjw]
      push_cast
      apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im] <;> ring
  refine ⟨H, h0, hfin, P, F, hPim, hFim, hFpos, ?_, ?_, hmatch⟩
  · intro i j hij
    change (F.pos (boundaryVertex (shiftedStream W 0) h0 j)).re <
      (F.pos (boundaryVertex (shiftedStream W 0) h0 i)).re
    rw [hFpos, hFpos]
    change -(j : ℝ) < -(i : ℝ)
    exact neg_lt_neg (by exact_mod_cast hij)
  · intro u v huv
    obtain ⟨n, e, he, hev⟩ := uibhbotGlue_shared_vertex_mem_seam W v ⟨u, huv⟩
    obtain ⟨j, hj, hje, hpt, hpw⟩ := hmatch n e he
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

end
end DirectedDistances.KMSW
