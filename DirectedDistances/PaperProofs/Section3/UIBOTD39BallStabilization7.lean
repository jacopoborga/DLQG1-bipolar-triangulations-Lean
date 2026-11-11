/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization6

/-! # Captured-window tests for original glued faces

These statements test every boundary vertex of the original future and past
faces using the actual finite exterior-face ball, under hwindow and hcap.
They do not identify a face of that finite map or assert an ambient comparison. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open WholePlanePastGlueData Set

/-- Helper toward Proposition 3.9: the infinite window vertex map tests
membership in the captured finite ball for every natural label, without a
separate allocation premise. Injectivity excludes unallocated labels. -/
theorem uibotFiniteRootWindow_vertexInf_mem_iff {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) (x : ℕ) :
    kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N) x ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (finiteCodeExtend w) (n - 1)) r
        (activeInitial (finiteCodeExtend w) j.val) ↔
    x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N) := by
  classical
  obtain ⟨_, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hs := kmswStage_congr hcode
  have heq (y : ℕ) (hy : y ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage u (2 * N)) r (activeInitial u N)) :
      kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N) y =
        kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N) y := by
    apply kmswWindowVertexMapInf_eq_stage
    rw [hs]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  rw [← uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap,
    Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy := kmswWindowVertexMapInf_injective (finiteCodeExtend w) (j.val - N)
      ((heq y hy).trans hyx)
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, (heq x hx).symm⟩

/-- Helper toward Proposition 3.9: the allocation-free window label test
is exactly membership of an actual vertex of the exterior-face geometric
ball. This statement uses no StageGeom certificate. -/
theorem uibotFiniteRootWindow_exteriorVertexInf_mem_iff {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) (x : ℕ) :
    (∃ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
      v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N) x ∧
      v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) ↔
    x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N) := by
  classical
  rw [← uibotFiniteRootWindow_vertexInf_mem_iff w j u hwindow hcap x]
  constructor
  · rintro ⟨v, hv, hmem⟩
    rw [← hv]
    exact (uibotFiniteStageExteriorBallVertices_iff P U hU hborder
      j.val (by have := j.isLt; omega) r v).mp hmem
  · intro hx
    let v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex :=
      ⟨_, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩
    exact ⟨v, rfl, (uibotFiniteStageExteriorBallVertices_iff P U hU hborder
      j.val (by have := j.isLt; omega) r v).mpr hx⟩

private theorem windowVertex_mem_geometricBall_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r x : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    wholePlaneVertexι W N x ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r ↔
    x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
      (activeInitial (shiftedStream W N) N) := by
  rw [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact wholePlaneVertexι_injective W N hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Helper toward Proposition 3.9: every dart bordering an original
retained face has a unique allocated representative in the captured window.
This applies to every whole-plane drawing of the source rotation. -/
theorem uibotWholePlane_retainedFace_dart_allocated
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r)
    (d : WholePlaneDart W) (hd : G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv F)) :
    ∃! a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
      wholePlaneDartι W N (a.1.val, a.2) = d := by
  have hcl := G.dartBorders_arc_subset_closure
    (uibhbot_faceOrbit_dartVertex_surjective W H) d _ hd
  have hstart : G.pos (wholePlaneDartVertex W d) ∈ (G.arc d).image := by
    rw [← G.arc_start d]
    exact Or.inl rfl
  have hfinish : G.pos (wholePlaneDartVertex W (wholePlaneDartFlip W d)) ∈
      (G.arc d).image := by
    rw [← G.arc_image_flip d, ← G.arc_start (wholePlaneDartFlip W d)]
    exact Or.inl rfl
  have hs := hF _ (hcl hstart)
  have ht := hF _ (hcl hfinish)
  rw [uibotWholePlaneGeometricBallVertices_eq_colimit] at hs ht
  have hends : wholePlaneEdgeWest W d.1 ∈
        wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) ∧
      wholePlaneEdgeEast W d.1 ∈
        wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) := by
    rcases d with ⟨e, b⟩
    cases b
    · exact ⟨hs, ht⟩
    · exact ⟨ht, hs⟩
  obtain ⟨a, _, hae⟩ := (uibotWholePlane_rootBallEdges_bijOn W N r hcap).2.2 hends
  have hde : wholePlaneDartι W N (a.val, d.2) = d := Prod.ext hae rfl
  refine ⟨(a, d.2), hde, ?_⟩
  intro b hb
  apply Prod.ext
  · apply Fin.ext
    exact wholePlaneEdgeι_injective W N (congrArg Prod.fst (hb.trans hde.symm))
  · exact congrArg (fun x : WholePlaneDart W => x.2) (hb.trans hde.symm)

/-- Helper toward Proposition 3.9: the original retained whole-plane
faces have distinct labels among the captured finite-stage darts. Each
label actually borders its original face, so no induced-subgraph face is
substituted for a complementary component of the whole drawing. -/
theorem uibotWholePlane_retainedFaces_windowEmbedding
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ f : {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r} ↪
        StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
      ∀ F, G.dartBorders (wholePlaneDartι W N ((f F).1.val, (f F).2))
        (G.toPlaneGraphDrawingFaceEquiv F.val) := by
  have hex (F : {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r}) :
      ∃ a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
        G.dartBorders (wholePlaneDartι W N (a.1.val, a.2))
          (G.toPlaneGraphDrawingFaceEquiv F.val) := by
    obtain ⟨d, hd⟩ := G.face_has_bordering_dart
      (uibhbot_faceOrbit_dartVertex_surjective W H)
      (wholePlaneDartι W 0 (0, false)) (G.toPlaneGraphDrawingFaceEquiv F.val)
    obtain ⟨a, ha, _⟩ :=
      uibotWholePlane_retainedFace_dart_allocated W H G hp N r hcap F.val F.property d hd
    exact ⟨a, ha.symm ▸ hd⟩
  choose f hf using hex
  refine ⟨⟨f, ?_⟩, hf⟩
  intro F K hFK
  apply Subtype.ext
  apply G.toPlaneGraphDrawingFaceEquiv.injective
  exact G.dartBorders_face_unique _ _ _ (hf F) (hFK.symm ▸ hf K)

/-- Helper toward Proposition 3.9: the retained original faces are finite
on a captured ball, as witnessed by actual bordering finite-window darts. -/
theorem uibotWholePlane_retainedFaces_finite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    (d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r).Finite := by
  obtain ⟨f, _⟩ := uibotWholePlane_retainedFaces_windowEmbedding W H G hp N r hcap
  exact Set.finite_coe_iff.mp (Finite.of_injective f f.injective)

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
local notation "Qf" => familyQ (shiftedStream W 0) (monotone_family_all (shiftedStream W 0))
local notation "Qp" => familyQ (kmswPastCode W) (monotone_family_all (kmswPastCode W))
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
  h0 hpast ((And.left H) 0) (past_finiteIncidence W H)

/-- Helper toward Proposition 3.9: retention of any original bounded
future-patch face in the glued ball is equivalent to the explicit finite
exterior-ball tests on all of its finite-stage boundary vertices. -/
theorem uibotGlued_futureStage_face_retained_finiteWindow
    {n N r : ℕ} (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (m : ℕ) (F : (Qf m).Face) (hF : ¬ (Qf m).IsUnbounded F) :
    ∃ F' : (G).Face, F'.val = F.val ∧
      ((G).toPlaneGraphDrawingFaceEquiv.symm F' ∈
        d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H (G) hp)
          (uibotWholePlaneGeometricRoot W H (G)) r ↔
      ∀ a : Fin (kmswStage (shiftedStream W 0) m).nextVertex,
        (Qf m).pos a ∈ closure F.val →
        ∃ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
          v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
            (wholePlaneVertexTrans W 0 N (Nat.zero_le N) a.val) ∧
          v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
            (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) := by
  obtain ⟨F', hmap, hbd⟩ := uibotGlued_futureStage_boundedFace_boundary W h0 hpast H m F hF
  refine ⟨F', hmap, ?_⟩
  have hmem (a : Fin (kmswStage (shiftedStream W 0) m).nextVertex) :
      wholePlaneVertexι W 0 a.val ∈
        d39GeomBallVertices (uibotWholePlaneGeometricMap W H (G) hp)
          (uibotWholePlaneGeometricRoot W H (G)) r ↔
      ∃ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
        v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (wholePlaneVertexTrans W 0 N (Nat.zero_le N) a.val) ∧
        v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r := by
    rw [← congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N)) a.val]
    exact (windowVertex_mem_geometricBall_iff W H (G) hp N r _ hcap).trans
      (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
        P U hU hborder hwindow hcap _).symm
  change (∀ v, (G).pos v ∈ closure F'.val → _) ↔ _
  constructor
  · intro hret a ha
    exact (hmem a).mp (hret _ ((hbd _).mpr ⟨a, rfl, ha⟩))
  · intro hret v hv
    obtain ⟨a, rfl, ha⟩ := (hbd v).mp hv
    exact (hmem a).mpr (hret a ha)

/-- Helper toward Proposition 3.9: retention of an original bounded past
face has the same exact finite exterior-ball test, using the reversal label
at the capture depth. The past patch may be any stage at most that depth. -/
theorem uibotGlued_pastStage_face_retained_finiteWindow
    {n N r : ℕ} (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (m : ℕ) (hm : m ≤ N) (F : (Qp m).Face) (hF : ¬ (Qp m).IsUnbounded F) :
    ∃ F' : (G).Face, F'.val = T '' F.val ∧
      ((G).toPlaneGraphDrawingFaceEquiv.symm F' ∈
        d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H (G) hp)
          (uibotWholePlaneGeometricRoot W H (G)) r ↔
      ∀ a : Fin (kmswStage (kmswPastCode W) m).nextVertex,
        (Qp m).pos a ∈ closure F.val →
        ∃ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
          v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
            (kmswPastStageVertex W N a.val) ∧
          v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
            (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) := by
  obtain ⟨F', hmap, hbd⟩ := uibotGlued_pastStage_boundedFace_boundary W h0 hpast H m F hF
  refine ⟨F', hmap, ?_⟩
  have hmem (a : Fin (kmswStage (kmswPastCode W) m).nextVertex) :
      kmswPastVertex W a.val ∈
        d39GeomBallVertices (uibotWholePlaneGeometricMap W H (G) hp)
          (uibotWholePlaneGeometricRoot W H (G)) r ↔
      ∃ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
        v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (kmswPastStageVertex W N a.val) ∧
        v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r := by
    rw [kmswPastVertex_eq_stage W N a.val
      (a.isLt.trans_le (CutConverse.nextVertex_mono _ hm))]
    exact (windowVertex_mem_geometricBall_iff W H (G) hp N r _ hcap).trans
      (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
        P U hU hborder hwindow hcap _).symm
  change (∀ v, (G).pos v ∈ closure F'.val → _) ↔ _
  constructor
  · intro hret a ha
    exact (hmem a).mp (hret _ ((hbd _).mpr ⟨a, rfl, ha⟩))
  · intro hret v hv
    obtain ⟨a, rfl, ha⟩ := (hbd v).mp hv
    exact (hmem a).mpr (hret a ha)

/-- Helper toward Proposition 3.9: one finite past stage and one finite
future stage contain every retained original face of the captured glued
ball. The common stage is proved to exist; no bound by the capture depth is
asserted. Both face sets are the original open complementary components. -/
theorem uibotGlued_retainedFaces_finitePatch_cover
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ m : ℕ, ∀ F : (G).toPlaneGraphDrawing.Face,
      F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H (G) hp)
        (uibotWholePlaneGeometricRoot W H (G)) r →
      (∃ i : Fin (kmswStage (shiftedStream W 0) m).triangles.length,
        F.val = ((familyG _ (monotone_family_all _) m).cap i).region) ∨
      (∃ i : Fin (kmswStage (kmswPastCode W) m).triangles.length,
        F.val = T '' ((familyG _ (monotone_family_all _) m).cap i).region) := by
  classical
  let R := {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H (G) hp)
    (uibotWholePlaneGeometricRoot W H (G)) r}
  let : Fintype R := (uibotWholePlane_retainedFaces_finite W H (G) hp N r hcap).fintype
  have hex (F : R) : ∃ m : ℕ,
      (∃ i : Fin (kmswStage (shiftedStream W 0) m).triangles.length,
        F.val.val = ((familyG _ (monotone_family_all _) m).cap i).region) ∨
      (∃ i : Fin (kmswStage (kmswPastCode W) m).triangles.length,
        F.val.val = T '' ((familyG _ (monotone_family_all _) m).cap i).region) := by
    rcases uibotGlued_face_finitePatch W h0 hpast H
      ((G).toPlaneGraphDrawingFaceEquiv F.val) with ⟨m, i, hi⟩ | ⟨m, i, hi⟩
    · exact ⟨m, Or.inl ⟨i, hi⟩⟩
    · exact ⟨m, Or.inr ⟨i, hi⟩⟩
  choose stage hstage using hex
  let m := Finset.univ.sup stage
  refine ⟨m, ?_⟩
  intro F hF
  let f : R := ⟨F, hF⟩
  have hfm : stage f ≤ m := Finset.le_sup (Finset.mem_univ f)
  rcases hstage f with ⟨i, hi⟩ | ⟨i, hi⟩
  · obtain ⟨j, hj⟩ := family_cap_persistence (shiftedStream W 0)
      (monotone_family_all _) (stage f) i m hfm
    exact Or.inl ⟨j, hi.trans hj⟩
  · obtain ⟨j, hj⟩ := family_cap_persistence (kmswPastCode W)
      (monotone_family_all _) (stage f) i m hfm
    exact Or.inr ⟨j, hi.trans (congrArg (fun s : Set ℂ => T '' s) hj)⟩





























end DirectedDistances.PaperProofs.Section3
end
