/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization8

/-! # Captured finite faces and arbitrary drawing transport

The captured finite ball misses the upper frontier, hence does not retain
the original exterior face. Drawing independence transports the actual
retained complementary components between arbitrary finite drawings. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

/-- Helper toward Proposition 3.9: under the successful centered window
and strong capture, both endpoints of every final upper-frontier edge lie
outside the captured finite root ball. -/
theorem uibotFiniteRootWindow_upperFrontier_disjoint {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (e : ℕ) (he : e ∈ (kmswStage (finiteCodeExtend w) (n - 1)).UL ++
      (kmswStage (finiteCodeExtend w) (n - 1)).UR) :
    (kmswStage (finiteCodeExtend w) (n - 1)).west e ∉
      kmswStageBallVertices (fun _ _ => True) (kmswStage (finiteCodeExtend w) (n - 1))
        r (activeInitial (finiteCodeExtend w) j.val) ∧
    (kmswStage (finiteCodeExtend w) (n - 1)).east e ∉
      kmswStageBallVertices (fun _ _ => True) (kmswStage (finiteCodeExtend w) (n - 1))
        r (activeInitial (finiteCodeExtend w) j.val) := by
  classical
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hn : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  have hfront := kmswStage_upperFrontier_endpoints (finiteCodeExtend w)
    (j.val - N + 2 * N) (n - 1) hn e he
  have havoid (x : ℕ) (hx : x ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (finiteCodeExtend w) (n - 1)) r
      (activeInitial (finiteCodeExtend w) j.val)) :
      ¬ UpperFrontierEndpoint (kmswStage (finiteCodeExtend w) (j.val - N + 2 * N)) x := by
    rw [← uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap] at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix
      u (2 * N) a (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (hcap.1.2.1 a ha).1 (hcap.1.2.1 a ha).2 (hcap.2 a ha)
      (finiteCodeExtend w) (j.val - N) hc
  exact ⟨fun hx => havoid _ hx hfront.1, fun hx => havoid _ hx hfront.2⟩

/-- Helper toward Proposition 3.9: the original exterior face of any
finite drawing is not a retained face under hwindow and hcap. The excluded
boundary vertex is the initial endpoint of the final active edge. -/
theorem uibotFiniteRootWindow_exterior_not_retained {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    P.toPlaneGraphDrawingFaceEquiv.symm U ∉
      d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r := by
  let a : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge :=
    ⟨act (finiteCodeExtend w) (n - 1), act_lt_nextEdge _ le_rfl⟩
  have ha : a.val ∈ (kmswStage (finiteCodeExtend w) (n - 1)).UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last (finiteCodeExtend w) (n - 1)
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hb : P.dartBorders (a, false) U := (hborder _).mpr
    ((kmswStageDirectedMap_UL_bridge (finiteCodeExtend w) (n - 1) a).mp ha).2.2
  have hcl : P.pos (stageVertex (finiteCodeExtend w) (n - 1) (a, false)) ∈
      closure U.val := by
    apply P.dartBorders_arc_subset_closure
      (kmswStageDrawing_vertex_surjective _ _) _ U hb
    rw [← P.arc_start (a, false)]
    exact Or.inl rfl
  intro hret
  have hmem := hret _ hcl
  have hmem' := (uibotFiniteStageExteriorBallVertices_iff P U hU hborder
    j.val (by have := j.isLt; omega) r _).mp hmem
  exact (uibotFiniteRootWindow_upperFrontier_disjoint w j u hwindow hcap a.val
    (List.mem_append_left _ ha)).1 hmem'

/-- Helper toward Proposition 3.9: all retained original finite faces
are bounded under the exact centered capture premises, for arbitrary P. -/
theorem uibotFiniteRootWindow_retainedFace_bounded {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    Bornology.IsBounded F.val := by
  by_contra hnot
  have hFU : P.toPlaneGraphDrawingFaceEquiv F = U :=
    P.existsUnique_unbounded_face.unique
      ((P.isUnbounded_iff_not_isBounded _).mpr hnot) hU
  have hF' : F = P.toPlaneGraphDrawingFaceEquiv.symm U :=
    (Equiv.eq_symm_apply _).mpr hFU
  exact uibotFiniteRootWindow_exterior_not_retained w j u P U hU hborder
    hwindow hcap (hF' ▸ hF)

/-- Helper toward Proposition 3.9: arbitrary finite drawings with the
same source exterior orbit have matching positive-radius geometric balls,
including the bijection and image equation for original retained faces. -/
theorem uibotFiniteStageDrawing_ballIso
    {w : ℕ → Fin 3} {n : ℕ} (P P' : StageDrawing w n)
    (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w n).IsOuter d)
    (j : ℕ) (hj : j ≤ n) (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j hj)
      (uibotFiniteStageExteriorMap P' U' hU' hborder')
      (uibotFiniteStageExteriorRoot P' j hj)) := by
  obtain ⟨I⟩ := uibotFiniteStageDrawing_rootedIso P P' U U' hU hU' hborder hborder' j hj
  exact ⟨I.toBallIsoV2 r hr⟩

/-- Helper toward Proposition 3.9: one ambient homeomorphism identifies
all retained original faces of an arbitrary captured finite drawing with
caps of its canonical drawing. The cap index is proved to exist and is not
assumed as an additional face-identification premise. -/
theorem uibotFiniteRootWindow_retainedFaces_canonicalCaps {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      ∀ F : P.toPlaneGraphDrawing.Face,
        F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r →
        ∃ i : Fin (kmswStage (finiteCodeExtend w) (n - 1)).triangles.length,
          F.val = h '' ((familyG (finiteCodeExtend w)
            (monotone_family_all (finiteCodeExtend w)) (n - 1)).cap i).region := by
  let C := familyQ (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)
  obtain ⟨Uc, hUc, _, hbc⟩ := uibotCanonicalStage_exterior (finiteCodeExtend w) (n - 1)
  obtain ⟨I⟩ := uibotFiniteStageDrawing_rootedIso C P Uc U hUc hU hbc hborder
    j.val (by have := j.isLt; omega)
  refine ⟨I.h, I.orientationPreserving, ?_⟩
  intro F hF
  let Fc := I.faceEquiv.symm F
  have hFc : Fc ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap C Uc hUc hbc)
      (uibotFiniteStageExteriorRoot C j.val (by have := j.isLt; omega)) r := by
    apply (I.retainedFaces_map r Fc).mpr
    exact (I.faceEquiv.apply_symm_apply F).symm ▸ hF
  have hbounded := uibotFiniteRootWindow_retainedFace_bounded
    w j u C Uc hUc hbc hwindow hcap Fc hFc
  have hn : ¬ C.IsUnbounded (C.toPlaneGraphDrawingFaceEquiv Fc) := by
    intro hu
    exact (C.isUnbounded_iff_not_isBounded _).mp hu hbounded
  obtain ⟨i, hi⟩ := uibotCanonicalStage_boundedFace_is_cap (finiteCodeExtend w) (n - 1)
    (C.toPlaneGraphDrawingFaceEquiv Fc) hn
  refine ⟨i, ?_⟩
  calc
    F.val = (I.faceEquiv Fc).val :=
      congrArg Subtype.val (I.faceEquiv.apply_symm_apply F).symm
    _ = I.h '' Fc.val := I.faceEquiv_val Fc
    _ = I.h '' ((familyG (finiteCodeExtend w)
        (monotone_family_all (finiteCodeExtend w)) (n - 1)).cap i).region :=
      congrArg (fun s : Set ℂ => I.h '' s) hi












































end DirectedDistances.PaperProofs.Section3
end
