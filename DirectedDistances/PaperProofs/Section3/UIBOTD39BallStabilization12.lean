/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization11
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFaceTriangles

/-! # Centered triangle faces in the glued whole-plane drawing

The triangle labels refer to the centered run, while the faces are original
complementary components of the glued drawing. No geometric comparison is -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hpast H

/-- Helper toward Proposition 3.9: the original glued face of a triangle
created in any centered run, using the proved face-orbit equivalence. -/
@[expose] def uibotGluedWindowTriangleFace (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) : (G).toPlaneGraphDrawing.Face :=
  (G).toPlaneGraphDrawingFaceEquiv.symm
    (WholePlaneGlueFaceCorrespondenceFull.faceOrbitEquiv W h0 hpast H
      (Quotient.mk _ (wholePlaneDartι W N
        (stageTriangleDartTriple (shiftedStream W N) q).1)))

/-- Helper toward Proposition 3.9: all and only the three mapped triangle
darts border the selected original glued face. -/
theorem uibotGluedWindowTriangleFace_border (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) (d : WholePlaneDart W) :
    (G).dartBorders d ((G).toPlaneGraphDrawingFaceEquiv
      (uibotGluedWindowTriangleFace W H h0 hpast N q)) ↔
      ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
        wholePlaneDartι W N a = d := by
  unfold uibotGluedWindowTriangleFace
  rw [Equiv.apply_symm_apply,
    WholePlaneGlueFaceCorrespondenceFull.dartBorders_faceOrbitEquiv_iff]
  exact Set.ext_iff.mp (wholePlane_stageTriangle_faceOrbit_darts W H N q) d

/-- Helper toward Proposition 3.9: different centered creation labels
give different original glued faces, without a retention assumption. -/
theorem uibotGluedWindowTriangleFace_injective (N : ℕ) :
    Function.Injective (uibotGluedWindowTriangleFace W H h0 hpast N) := by
  intro q p he
  let a := (stageTriangleDartTriple (shiftedStream W N) q).1
  have ha : a ∈ stageTriangleDartList (shiftedStream W N) q := by
    simp only [a, stageTriangleDartList, List.mem_cons, List.not_mem_nil,
      or_false, true_or]
  have hd := (uibotGluedWindowTriangleFace_border W H h0 hpast N q
    (wholePlaneDartι W N a)).mpr ⟨a, ha, rfl⟩
  rw [he] at hd
  obtain ⟨b, hb, hba⟩ :=
    (uibotGluedWindowTriangleFace_border W H h0 hpast N p _).mp hd
  have hba' : b = a := wholePlaneDartι_injective W N hba
  have ham : a ∈ stageTriangleDartList (shiftedStream W N) p := hba' ▸ hb
  by_contra hne
  exact (List.disjoint_left.mp (stageTriangleDartLists_disjoint
    (shiftedStream W N) (max q.val p.val + 1) q p
    (by omega) (by omega) hne)) ha ham

private theorem window_vertex_mem (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r x : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    wholePlaneVertexι W N x ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r ↔
    x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
      (activeInitial (shiftedStream W N) N) := by
  rw [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap]
  constructor
  · rintro ⟨y, hy, he⟩
    exact wholePlaneVertexι_injective W N he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Helper toward Proposition 3.9: retention of an original glued triangle
face is exactly the finite centered-window test on all its dart endpoints.
The equivalence uses the full closure-based original-face definition. -/
theorem uibotGluedWindowTriangleFace_retained_iff
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (q : TriangleCreationTime (shiftedStream W N)) :
    uibotGluedWindowTriangleFace W H h0 hpast N q ∈
      d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r ↔
    ∀ a ∈ stageTriangleDartList (shiftedStream W N) q,
      kmswLimitDartVertex (shiftedStream W N) a ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N) ∧
      kmswLimitDartVertex (shiftedStream W N) (a.1, !a.2) ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N) := by
  rw [uibotWholePlane_face_retained_iff_borderEndpoints W H G hp N r hcap]
  have hend (a : ℕ × Bool) :
      wholePlaneDartFlip W (wholePlaneDartι W N a) =
        wholePlaneDartι W N (a.1, !a.2) := rfl
  constructor
  · intro h a ha
    have he := h _ ((uibotGluedWindowTriangleFace_border W H h0 hpast N q _).mpr
      ⟨a, ha, rfl⟩)
    rw [hend, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι] at he
    exact ⟨(window_vertex_mem W H h0 hpast hp N r _ hcap).mp he.1,
      (window_vertex_mem W H h0 hpast hp N r _ hcap).mp he.2⟩
  · intro h d hd
    obtain ⟨a, ha, rfl⟩ :=
      (uibotGluedWindowTriangleFace_border W H h0 hpast N q d).mp hd
    rw [hend, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    exact ⟨(window_vertex_mem W H h0 hpast hp N r _ hcap).mpr (h a ha).1,
      (window_vertex_mem W H h0 hpast hp N r _ hcap).mpr (h a ha).2⟩

private theorem endpoint_limit (u : ℕ → Fin 3) (m : ℕ)
    (a : StageDart (kmswStage u m).nextEdge) :
    stageEndpoint (kmswStage u m) a = kmswLimitDartVertex u (a.1.val, a.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq u a.1.isLt
  cases hb : a.2 <;> simp only [stageEndpoint, kmswLimitDartVertex,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem complete_of_not_frontier (u : ℕ → Fin 3) (m v : ℕ)
    (hv : ¬ UpperFrontierEndpoint (kmswStage u m) v) : kmswVertexComplete u m v := by
  intro e he
  by_contra hne
  let t := max m e
  have het : e < (kmswStage u t).nextEdge :=
    (kmsw_edge_allocated_by_self u e).trans_le (kmswStage_nextEdge_mono u (Nat.le_max_right _ _))
  have hno := kmswStage_no_new_incidence_of_not_upperFrontier u m v hv t
    (Nat.le_max_left _ _) e het (by omega)
  rw [(edge_endpoints_eq u het).1, (edge_endpoints_eq u het).2] at hno
  exact he.elim hno.1 hno.2

private theorem captured_faceSucc (N r : ℕ)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge)
    (ha : stageEndpoint (kmswStage (shiftedStream W N) (2 * N)) (edgeFlip _ a) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
        (activeInitial (shiftedStream W N) N)) :
    wholePlaneFaceSucc W H (wholePlaneDartι W N (a.1.val, a.2)) =
      wholePlaneDartι W N
        (((kmswMap (shiftedStream W N) (2 * N)).faceSucc a).1.val,
          ((kmswMap (shiftedStream W N) (2 * N)).faceSucc a).2) := by
  let v := stageEndpoint (kmswStage (shiftedStream W N) (2 * N)) (edgeFlip _ a)
  have hv := stageEndpoint_lt_nextVertex (shiftedStream W N) (2 * N) (edgeFlip _ a)
  have hlim : v = kmswLimitDartVertex (shiftedStream W N) (a.1.val, !a.2) :=
    endpoint_limit _ _ (edgeFlip _ a)
  have hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM v := by
    intro M hNM
    have hcode : ∀ i < 2 * N, shiftedStream W M (M - N + i) = shiftedStream W N i :=
      fun i _ => congrFun (shiftedStream_shift W N M hNM) i
    have hnew := kmswWindowPatchVertexMap_fresh_for_every_prefix
      (shiftedStream W N) (2 * N) v hv (hcap.1.2.1 v ha).1 (hcap.1.2.1 v ha).2
      (shiftedStream W M) (M - N) hcode
    change (kmswStage (shiftedStream W M) (M - N)).nextVertex ≤
      kmswWindowVertexMapInf (shiftedStream W M) (M - N) v
    rw [kmswWindowVertexMapInf_eq_stage _ _ (2 * N) v (by
      rw [shiftedStream_shift W N M hNM]; exact hv)]
    exact hnew
  have hc := complete_of_not_frontier (shiftedStream W N) (2 * N) v (hcap.2 v ha)
  have hrot := wholePlaneRotation_symm_ι_of_fresh W H N (a.1.val, !a.2)
    (by
      intro M hNM
      change wholePlaneFresh W N M hNM (kmswLimitDartVertex (shiftedStream W N) (a.1.val, !a.2))
      rw [← hlim]
      exact hf M hNM)
  have hs := kmswInfRot_symm_eq_stage (shiftedStream W N) (H.1 N) (2 * N)
    (edgeFlip _ a) hc
  change (wholePlaneRotation W H).symm (wholePlaneDartι W N (a.1.val, !a.2)) = _
  rw [hrot]
  exact congrArg (wholePlaneDartι W N) hs

/-- Helper toward Proposition 3.9: every retained original glued face
has exactly one triangle label created within the centered window. This
exhausts the retained faces, including faces crossing the gluing seam. -/
theorem uibotGlued_retainedFace_windowTriangle
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : (G).toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) :
    ∃! q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
      F = uibotGluedWindowTriangleFace W H h0 hpast N q := by
  let u := shiftedStream W N
  let m := 2 * N
  let f := (kmswMap u m).faceSucc
  let I := fun a : StageDart (kmswStage u m).nextEdge => wholePlaneDartι W N (a.1.val, a.2)
  let F' := (G).toPlaneGraphDrawingFaceEquiv F
  obtain ⟨d, hd⟩ := (G).face_has_bordering_dart (uibhbot_faceOrbit_dartVertex_surjective W H)
    (wholePlaneDartι W 0 (0, false)) F'
  obtain ⟨a, ha, _⟩ := uibotWholePlane_retainedFace_dart_allocated
    W H G hp N r hcap F hF d hd
  have hab : (G).dartBorders (I a) F' := by
    dsimp only [I]
    rw [ha]
    exact hd
  have hends (b : StageDart (kmswStage u m).nextEdge) (hb : (G).dartBorders (I b) F') :
      stageEndpoint (kmswStage u m) b ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) r (activeInitial u N) ∧
      stageEndpoint (kmswStage u m) (edgeFlip _ b) ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) r (activeInitial u N) := by
    have he := (uibotWholePlane_face_retained_iff_borderEndpoints W H G hp N r hcap F).mp hF
      (I b) hb
    have hfl : wholePlaneDartFlip W (I b) = wholePlaneDartι W N (b.1.val, !b.2) := rfl
    change wholePlaneDartVertex W (wholePlaneDartι W N (b.1.val, b.2)) ∈ _ ∧ _ at he
    rw [hfl, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι] at he
    rw [endpoint_limit, endpoint_limit]
    exact ⟨(window_vertex_mem W H h0 hpast hp N r _ hcap).mp he.1,
      (window_vertex_mem W H h0 hpast hp N r _ hcap).mp he.2⟩
  have hiter (k : ℕ) : (G).dartBorders (I ((f ^ k) a)) F' := by
    induction k with
    | zero => exact hab
    | succ k ih =>
      have hh := WholePlaneGlueFaceCorrespondenceFull.faceSucc_dartBorders
        W h0 hpast H (I ((f ^ k) a)) F' ih
      rw [captured_faceSucc W H N r hcap _ (hends _ ih).2] at hh
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hh
  have hnot : a ∉ stageOuterWord u m := by
    intro hao
    let C := familyQ u (monotone_family_all u) m
    obtain ⟨Uc, _, _, hbc⟩ := uibotCanonicalStage_exterior u m
    let b : StageDart (kmswStage u m).nextEdge :=
      (⟨act u m, act_lt_nextEdge u le_rfl⟩, false)
    have hbUL : b.1.val ∈ (kmswStage u m).UL := by
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
      rw [hxs]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hbo : (kmswStageDirectedMap u m).IsOuter b :=
      ((kmswStageDirectedMap_UL_bridge u m b.1).mp hbUL).2.2
    have hao' : (kmswStageDirectedMap u m).IsOuter a := by
      rw [kmswStage_isOuter_iff_boundary]
      have hh := (stageOuterWord_mem_iff u m a).mp hao
      simpa only [List.mem_append, or_comm] using hh
    have hfaces : kmswStageDrawing_leftFace C a = kmswStageDrawing_leftFace C b :=
      ((kmswStageDrawing_leftFace_eq_iff C a Uc).mpr ((hbc a).mpr hao')).trans
        ((kmswStageDrawing_leftFace_eq_iff C b Uc).mpr ((hbc b).mpr hbo)).symm
    have hcyc : f.SameCycle a b := kmswStageDrawing_sameCycle_of_leftFace_eq C a b hfaces
    obtain ⟨k, hk⟩ := hcyc.exists_nat_pow_eq
    have hbm := (hends b (hk ▸ hiter k)).1
    apply hcap.2 _ hbm
    exact Or.inl ⟨b.1.val, List.mem_append_left _ hbUL, Or.inl rfl⟩
  obtain ⟨q, ⟨hq, haq⟩, _⟩ := (stage_dart_partition u m a).resolve_left hnot
  have haq' := (uibotGluedWindowTriangleFace_border W H h0 hpast N q (I a)).mpr
    ⟨(a.1.val, a.2), haq, rfl⟩
  have he : F = uibotGluedWindowTriangleFace W H h0 hpast N q :=
    (G).toPlaneGraphDrawingFaceEquiv.injective ((G).dartBorders_face_unique (I a) _ _ hab haq')
  refine ⟨q, ⟨hq, he⟩, ?_⟩
  intro p hp'
  exact uibotGluedWindowTriangleFace_injective W H h0 hpast N (hp'.2.symm.trans he)

end DirectedDistances.PaperProofs.Section3
end

