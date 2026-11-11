/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization12

/-! # Matching retained finite faces to centered glued triangle faces

The finite drawing is arbitrary and exterior-certified. The whole-plane
drawing in this file is the proved glued realization. No ambient comparison -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

/-- Helper toward Proposition 3.9: code agreement transports every
allocated window dart and its endpoint through the infinite window maps.
The final-stage allocation bound is part of the conclusion. -/
theorem uibotWindowDart_endpoint_transport (w u : ℕ → Fin 3) (s m t : ℕ)
    (hst : s + m ≤ t) (hc : ∀ i < m, w (s + i) = u i)
    (a : ℕ × Bool) (ha : a.1 < (kmswStage u m).nextEdge) :
    kmswWindowEdgeMapInf w s a.1 < (kmswStage w t).nextEdge ∧
      kmswLimitDartVertex w (kmswWindowEdgeMapInf w s a.1, a.2) =
        kmswWindowVertexMapInf w s (kmswLimitDartVertex u a) := by
  have hs : kmswStage (fun i => w (s + i)) m = kmswStage u m := kmswStage_congr hc
  have ha' : a.1 < (kmswStage (fun i => w (s + i)) m).nextEdge := hs.symm ▸ ha
  have hb : kmswWindowEdgeMapInf w s a.1 < (kmswStage w (s + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w s m a.1 ha']
    exact (kmswWindowPatchData_rel w s m).edge_bound a.1 ha'
  refine ⟨hb.trans_le (kmswStage_nextEdge_mono w hst), ?_⟩
  have hw : edgeWest (fun i => w (s + i)) a.1 = edgeWest u a.1 := by
    rw [← (edge_endpoints_eq _ ha').1, hs, (edge_endpoints_eq _ ha).1]
  have he : edgeEast (fun i => w (s + i)) a.1 = edgeEast u a.1 := by
    rw [← (edge_endpoints_eq _ ha').2, hs, (edge_endpoints_eq _ ha).2]
  cases hb : a.2 <;> simp only [kmswLimitDartVertex, hb, Bool.false_eq_true,
    ↓reduceIte, kmswWindowEdgeMapInf_edgeWest, kmswWindowEdgeMapInf_edgeEast, hw, he]

private theorem stage_vertex_eq_limit (w : ℕ → Fin 3) (t : ℕ)
    (d : StageDart (kmswStage w t).nextEdge) :
    (stageVertex w t d).val = kmswLimitDartVertex w (d.1.val, d.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp only [stageVertex, stageEndpoint, kmswLimitDartVertex,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

/-- Helper toward Proposition 3.9: every retained original finite face
has a centered creation label whose original glued face is retained too.
The complete finite bordering-dart characterization is retained jointly. -/
theorem uibotFiniteRootWindow_retainedFace_gluedTriangle {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
      (∀ d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) ∧
      uibotGluedWindowTriangleFace W H h0 hpast N q ∈
        d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
          (uibotWholePlaneGeometricRoot W H G) r := by
  dsimp only
  obtain ⟨q, ⟨hq, hchar⟩, _⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
    w j (shiftedStream W N) P U hU hborder hwindow hcap F hF
  refine ⟨q, hq, hchar, ?_⟩
  apply (uibotGluedWindowTriangleFace_retained_iff W H h0 hpast hp N r hcap q).mpr
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hst : j.val - N + 2 * N ≤ n - 1 := by have := hv.1; have := hv.2; omega
  intro a ha
  have hab := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
  have htrans := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
    (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc a hab
  have hflip := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
    (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc (a.1, !a.2) hab
  let d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge :=
    (⟨kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, htrans.1⟩, a.2)
  have hd : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) :=
    (hchar d).mpr ⟨a, ha, rfl⟩
  obtain ⟨hs, ht⟩ := (uibotFiniteStage_face_retained_iff_borderEndpoints P U hU hborder
    j.val (by have := j.isLt; omega) r F).mp hF d hd
  constructor
  · apply (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
      P U hU hborder hwindow hcap _).mp
    exact ⟨stageVertex (finiteCodeExtend w) (n - 1) d,
      (stage_vertex_eq_limit _ _ d).trans htrans.2, hs⟩
  · apply (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
      P U hU hborder hwindow hcap _).mp
    exact ⟨stageVertex (finiteCodeExtend w) (n - 1) (edgeFlip _ d),
      (stage_vertex_eq_limit _ _ (edgeFlip _ d)).trans hflip.2, ht⟩

/-- Helper toward Proposition 3.9: retained original finite faces inject
into retained original glued faces. One centered triangle label identifies
the complete bordering-dart relation on both sides. -/
theorem uibotFiniteRootWindow_retainedFaces_gluedEmbedding {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    ∃ f : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ↪
      {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ F, ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
        (f F).val = uibotGluedWindowTriangleFace W H h0 hpast N q ∧
        (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) := by
  dsimp only
  let A := {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
    (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r}
  have hex (F : A) := uibotFiniteRootWindow_retainedFace_gluedTriangle
    w j W H h0 hpast hp P U hU hborder hwindow hcap F.val F.property
  choose q hq hchar hret using hex
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let B := {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G) r}
  let f : A → B := fun F => ⟨uibotGluedWindowTriangleFace W H h0 hpast N (q F), hret F⟩
  refine ⟨⟨f, ?_⟩, fun F => ⟨q F, hq F, rfl, hchar F⟩⟩
  intro F K he
  have hqeq : q F = q K := uibotGluedWindowTriangleFace_injective W H h0 hpast N
    (congrArg Subtype.val he)
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart (kmswStageDrawing_vertex_surjective _ _)
    (kmswRootedStage (finiteCodeExtend w) (n - 1)).root (P.toPlaneGraphDrawingFaceEquiv F.val)
  have hdK : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv K.val) := by
    apply (hchar K d).mpr
    rw [← hqeq]
    exact (hchar F d).mp hd
  apply Subtype.ext
  apply P.toPlaneGraphDrawingFaceEquiv.injective
  exact P.dartBorders_face_unique d _ _ hd hdK

private theorem finite_triangle_face {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (U : P.Face)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (q : TriangleCreationTime w) (hq : q.val < n) :
    ∃ F : P.toPlaneGraphDrawing.Face,
      ∀ d : StageDart (kmswStage w n).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          (d.1.val, d.2) ∈ stageTriangleDartList w q := by
  let d := stageTriangleDart₁ w n q hq
  have hdq : (d.1.val, d.2) ∈ stageTriangleDartList w q := by
    simp only [d, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
      List.mem_cons, List.not_mem_nil, or_false, true_or]
  let F := kmswStageDrawing_leftFace P d
  have hd : P.dartBorders d F := (kmswStageDrawing_leftFace_eq_iff P d F).mp rfl
  have hFU : F ≠ U := by
    intro he
    have ho := (hborder d).mp (he ▸ hd)
    have hon : d ∈ stageOuterWord w n := by
      rw [kmswStage_isOuter_iff_boundary] at ho
      apply (stageOuterWord_mem_iff w n d).mpr
      simpa only [List.mem_append, or_comm] using ho
    exact stageTriangleDart_not_outer w n q hq d hdq hon
  obtain ⟨k, ⟨hk, hchar⟩, _⟩ :=
    uibotFiniteStage_nonexteriorFace_triangle P U hborder F hFU
  have hkq : k = q := by
    by_contra hne
    exact (List.disjoint_left.mp (stageTriangleDartLists_disjoint w n k q hk hq hne))
      ((hchar d).mp hd) hdq
  exact ⟨P.toPlaneGraphDrawingFaceEquiv.symm F, by
    intro e
    rw [Equiv.apply_symm_apply]
    exact hkq ▸ hchar e⟩

private theorem window_triangle_mem (w u : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i)
    (q : TriangleCreationTime u) (hq : q.val < m)
    (hc : w (s + q.val) = 0 ∨ w (s + q.val) = 1) (d : ℕ × Bool) :
    d ∈ stageTriangleDartList w ⟨s + q.val, hc⟩ ↔
      ∃ a, a ∈ stageTriangleDartList u q ∧
        (kmswWindowEdgeMapInf w s a.1, a.2) = d := by
  have hs : kmswStage (fun i => w (s + i)) q.val = kmswStage u q.val :=
    kmswStage_congr (fun i hi => hcode i (hi.trans hq))
  have hsfull : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hl : stageTriangleDartList (fun i => w (s + i)) ⟨q.val, hc⟩ =
      stageTriangleDartList u q := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, hs, hcode q.val hq]
  have hr := kmswWindowPatchData_triangle_rotated w s m q.val hq hc
  rw [hl] at hr
  have hm (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList u q) :
      ((kmswWindowPatchData w s m).φ a.1, a.2) =
        (kmswWindowEdgeMapInf w s a.1, a.2) := by
    apply Prod.ext
    · symm
      apply kmswWindowEdgeMapInf_eq_stage
      rw [hsfull]
      exact stageTriangleDartList_lt u m q hq a ha
    · rfl
  constructor
  · intro hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (hr.mem_iff.mpr hd)
    exact ⟨a, ha, (hm a ha).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact hr.mem_iff.mp (List.mem_map.mpr ⟨a, ha, (hm a ha).trans he⟩)

/-- Helper toward Proposition 3.9: each centered triangle is realized by
an original face of every exterior-certified finite drawing. Its retention
is equivalent to retention of the original glued face with the same label. -/
theorem uibotFiniteRootWindow_triangleFace_correspondence {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (q : TriangleCreationTime (shiftedStream W N)) (hq : q.val < 2 * N) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    ∃ F : P.toPlaneGraphDrawing.Face,
      (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2)) ∧
      (F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r ↔
        uibotGluedWindowTriangleFace W H h0 hpast N q ∈
          d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
            (uibotWholePlaneGeometricRoot W H G) r) := by
  dsimp only
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hst : j.val - N + 2 * N ≤ n - 1 := by have := hv.1; have := hv.2; omega
  have hcode : finiteCodeExtend w (j.val - N + q.val) = 0 ∨
      finiteCodeExtend w (j.val - N + q.val) = 1 := by
    rw [hc q.val hq]
    exact q.property
  obtain ⟨F, hF⟩ := finite_triangle_face P U hborder
    ⟨j.val - N + q.val, hcode⟩ (by dsimp; omega)
  have hchar (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge) :
      P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2) :=
    (hF d).trans (window_triangle_mem _ _ _ _ hc q hq hcode _)
  refine ⟨F, hchar, ?_⟩
  constructor
  · intro hret
    obtain ⟨p, _, hpchar, hpret⟩ := uibotFiniteRootWindow_retainedFace_gluedTriangle
      w j W H h0 hpast hp P U hU hborder hwindow hcap F hret
    obtain ⟨p', ⟨hp', hpchar'⟩, huniq⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
      w j (shiftedStream W N) P U hU hborder hwindow hcap F hret
    have hqeq : q = p' := huniq q ⟨hq, hchar⟩
    have hpeq : p = p' := huniq p ⟨by assumption, hpchar⟩
    exact (hpeq.trans hqeq.symm) ▸ hpret
  · intro hret
    have hends := (uibotGluedWindowTriangleFace_retained_iff
      W H h0 hpast hp N r hcap q).mp hret
    apply (uibotFiniteStage_face_retained_iff_borderEndpoints P U hU hborder
      j.val (by have := j.isLt; omega) r F).mpr
    intro d hd
    obtain ⟨a, ha, he⟩ := (hchar d).mp hd
    have hab := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
    have htrans := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
      (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc a hab
    have hflip := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
      (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc (a.1, !a.2) hab
    have hvd : (stageVertex (finiteCodeExtend w) (n - 1) d).val =
        kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (kmswLimitDartVertex (shiftedStream W N) a) :=
      (stage_vertex_eq_limit _ _ d).trans ((congrArg (kmswLimitDartVertex _) he).symm.trans htrans.2)
    have heflip : (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, !a.2) =
        ((edgeFlip _ d).1.val, (edgeFlip _ d).2) := by
      exact congrArg (fun z : ℕ × Bool => (z.1, !z.2)) he
    have hvt : (stageVertex (finiteCodeExtend w) (n - 1) (edgeFlip _ d)).val =
        kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (kmswLimitDartVertex (shiftedStream W N) (a.1, !a.2)) :=
      (stage_vertex_eq_limit _ _ (edgeFlip _ d)).trans
        ((congrArg (kmswLimitDartVertex _) heflip).symm.trans hflip.2)
    constructor
    · obtain ⟨v, hv, hvm⟩ := (uibotFiniteRootWindow_exteriorVertexInf_mem_iff
        w j (shiftedStream W N) P U hU hborder hwindow hcap _).mpr (hends a ha).1
      exact (Fin.ext (hv.trans hvd.symm)) ▸ hvm
    · obtain ⟨v, hv, hvm⟩ := (uibotFiniteRootWindow_exteriorVertexInf_mem_iff
        w j (shiftedStream W N) P U hU hborder hwindow hcap _).mpr (hends a ha).2
      exact (Fin.ext (hv.trans hvt.symm)) ▸ hvm

/-- Helper toward Proposition 3.9: retained original finite faces and
retained original glued whole-plane faces are in bijection. The same
centered triangle label gives both complete bordering-dart relations. -/
theorem uibotFiniteRootWindow_retainedFaces_gluedEquiv {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    ∃ E : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ≃
      {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ F, ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
        (E F).val = uibotGluedWindowTriangleFace W H h0 hpast N q ∧
        (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) ∧
        (∀ d, G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv (E F).val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            wholePlaneDartι W N a = d) := by
  dsimp only
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  obtain ⟨f, hf⟩ := uibotFiniteRootWindow_retainedFaces_gluedEmbedding
    w j W H h0 hpast hp P U hU hborder hwindow hcap
  have hsurj : Function.Surjective f := by
    intro K
    obtain ⟨q, ⟨hq, hK⟩, _⟩ := uibotGlued_retainedFace_windowTriangle
      W H h0 hpast hp N r hcap K.val K.property
    obtain ⟨F, hchar, hret⟩ := uibotFiniteRootWindow_triangleFace_correspondence
      w j W H h0 hpast hp P U hU hborder hwindow hcap q hq
    have hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r :=
      hret.mpr (hK ▸ K.property)
    obtain ⟨p, hp', hfp, hpchar⟩ := hf ⟨F, hF⟩
    obtain ⟨q', _, huniq⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
      w j (shiftedStream W N) P U hU hborder hwindow hcap F hF
    have hpq : p = q := (huniq p ⟨hp', hpchar⟩).trans (huniq q ⟨hq, hchar⟩).symm
    exact ⟨⟨F, hF⟩, Subtype.ext (hfp.trans
      ((congrArg (uibotGluedWindowTriangleFace W H h0 hpast N) hpq).trans hK.symm))⟩
  let E := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  refine ⟨E, ?_⟩
  intro F
  obtain ⟨q, hq, he, hchar⟩ := hf F
  refine ⟨q, hq, he, hchar, ?_⟩
  intro d
  change G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv (f F).val) ↔ _
  rw [he]
  exact uibotGluedWindowTriangleFace_border W H h0 hpast N q d


























end DirectedDistances.PaperProofs.Section3
end


