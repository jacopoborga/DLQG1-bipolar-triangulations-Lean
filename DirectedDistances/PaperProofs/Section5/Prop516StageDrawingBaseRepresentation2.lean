/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRotation

/-! # Finite stage drawing base representation continuation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval

/-- Helper toward Proposition 5.16. Missing edges of a finite stage drawing
are supported by the exterior face when its boundary darts are exactly the
stage map's outer darts. This uses only the drawing's exterior-face data. -/
theorem kmswStageDrawing_missingEdges_external_of_exteriorFace
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ e : P.GeometricEdge,
      (kmswStageDirectedMap w n).missing e.out →
        ∃ F : P.toPlaneGraphDrawing.Face,
          PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
            Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val := by
  intro e he
  have hvert : Function.Surjective (stageVertex w n) :=
    kmswStageDrawing_vertex_surjective w n
  rcases (kmswStageDirectedMap w n).missing_outer e.out he with ho | ho
  · refine ⟨P.toPlaneGraphDrawingFaceEquiv.symm U,
      (P.toPlaneGraphDrawing_isExternal_iff _).2 hU, ?_⟩
    rw [← Quotient.out_eq e, P.toPlaneGraphDrawing_arc_range]
    exact P.dartBorders_arc_subset_closure hvert e.out U (hborder e.out |>.2 ho)
  · have hflip : (kmswStageDirectedMap w n).IsOuter (edgeFlip _ e.out) := by
      change CombinatorialMap.IsOuter
        (kmswStageDirectedMap w n).toCombinatorialMap
        (kmswStageDirectedMap w n).outer
        ((kmswStageDirectedMap w n).toCombinatorialMap.edgeInv e.out) at ho
      change CombinatorialMap.IsOuter
        (kmswStageDirectedMap w n).toCombinatorialMap
        (kmswStageDirectedMap w n).outer (edgeFlip _ e.out)
      simpa [kmswStageDirectedMap, kmswDirectedMap, kmswMap] using ho
    have hsubset := P.dartBorders_arc_subset_closure hvert (edgeFlip _ e.out)
      U ((hborder (edgeFlip _ e.out)).2 hflip)
    have himage : (P.arc (edgeFlip _ e.out)).image = (P.arc e.out).image :=
      P.arc_image_flip e.out
    refine ⟨P.toPlaneGraphDrawingFaceEquiv.symm U,
      (P.toPlaneGraphDrawing_isExternal_iff _).2 hU, ?_⟩
    rw [← Quotient.out_eq e, P.toPlaneGraphDrawing_arc_range]
    exact himage.symm ▸ hsubset

/-- Helper toward Proposition 5.16. The finite stage drawing's geometric
graph is connected using only its dart quotient and the connected stage map.
The exterior-face witness is needed to form the directed plane map. -/
theorem kmswStageDrawing_geometricGraph_connected_of_external
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (missingExternal : ∀ e : P.GeometricEdge,
      (kmswStageDirectedMap w n).missing e.out →
        ∃ F : P.toPlaneGraphDrawing.Face,
          PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
            Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val) :
    ∀ v wv : Fin (kmswStage w n).nextVertex,
      (d39GeomGraph (finitePLDrawingDirectedMap P
        (fun e => (kmswStageDirectedMap w n).missing e.out)
        (fun e => !e.val.out.2) missingExternal)).Reachable v wv := by
  intro v wv
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
  let e := Classical.choose (stageEndpoint_exists w n wv.val wv.isLt)
  let M := finitePLDrawingDirectedMap P
    (fun f => (kmswStageDirectedMap w n).missing f.out)
    (fun f => !f.val.out.2) missingExternal
  let R := fun x y : Fin (kmswStage w n).nextVertex =>
    x = y ∨ d39GeomAdj M x y
  have hrot (x : StageDart (kmswStage w n).nextEdge) :
      stageVertex w n (stageRot w n x) = stageVertex w n x := by
    apply Fin.ext
    change stageEndpoint (kmswStage w n) (stageRot w n x) =
      stageEndpoint (kmswStage w n) x
    exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
      ⟨1, rfl⟩).symm
  have hedge (x : StageDart (kmswStage w n).nextEdge) :
      R (stageVertex w n x) (stageVertex w n (edgeFlip _ x)) := by
    by_cases heq : stageVertex w n x = stageVertex w n (edgeFlip _ x)
    · exact Or.inl heq
    · right
      let f : P.GeometricEdge := Quotient.mk P.edgeSetoid x
      change stageVertex w n x ≠ stageVertex w n (edgeFlip _ x) ∧
        ∃ f : P.GeometricEdge,
          (stageVertex w n f.out = stageVertex w n x ∧
            stageVertex w n (edgeFlip _ f.out) = stageVertex w n (edgeFlip _ x)) ∨
          (stageVertex w n f.out = stageVertex w n (edgeFlip _ x) ∧
            stageVertex w n (edgeFlip _ f.out) = stageVertex w n x)
      refine ⟨heq, f, ?_⟩
      rcases P.geometricEdge_out_mk x with hout | hout
      · left
        constructor <;> rw [hout]
      · right
        constructor
        · rw [hout]
        · rw [hout]
          simp [edgeFlip]
  have hstep {x y : StageDart (kmswStage w n).nextEdge}
      (hxy : y = stageRot w n x ∨ y = (stageRot w n).symm x ∨
        y = edgeFlip _ x ∨ y = (edgeFlip _).symm x) :
      R (stageVertex w n x) (stageVertex w n y) := by
    rcases hxy with hxy | hxy | hxy | hxy
    · subst y
      exact Or.inl (hrot x).symm
    · subst y
      exact Or.inl (by simpa using hrot ((stageRot w n).symm x))
    · subst y
      exact hedge x
    · subst y
      simpa [edgeFlip] using hedge x
  have hconn : Relation.ReflTransGen
      (fun x y : StageDart (kmswStage w n).nextEdge =>
        y = stageRot w n x ∨ y = (stageRot w n).symm x ∨
          y = edgeFlip _ x ∨ y = (edgeFlip _).symm x) d e := by
    change Relation.ReflTransGen
      (fun x y : StageDart (kmswStage w n).nextEdge =>
        y = (kmswMap w n).rot x ∨ y = (kmswMap w n).rot.symm x ∨
          y = (kmswMap w n).edgeInv x ∨ y = (kmswMap w n).edgeInv.symm x) d e
    exact kmswMap_isConnected w n d e
  have hvertices : Relation.ReflTransGen R
      (stageVertex w n d) (stageVertex w n e) := by
    exact Relation.ReflTransGen.lift
      (r := fun x y : StageDart (kmswStage w n).nextEdge =>
        y = stageRot w n x ∨ y = (stageRot w n).symm x ∨
          y = edgeFlip _ x ∨ y = (edgeFlip _).symm x)
      (p := R) (stageVertex w n) (fun _ _ hxy => hstep hxy) d e hconn
  have hreach : (d39GeomGraph M).Reachable
      (stageVertex w n d) (stageVertex w n e) := by
    exact kmswStageDrawing_reachable_of_eq_or_adj M hvertices
  have hstart : stageVertex w n d = v := Fin.ext hd
  have he : stageEndpoint (kmswStage w n) e = wv.val :=
    Classical.choose_spec (stageEndpoint_exists w n wv.val wv.isLt)
  have hfinish : stageVertex w n e = wv := by
    apply Fin.ext
    exact he
  simpa [M, hstart, hfinish] using hreach

/-- Helper toward Proposition 5.16. The ordered active-root edge and the
finite stage drawing form a local topology domain rooted map using only the drawing's
exterior-face data, with no `StageGeom` input. -/
@[expose] def kmswStageDrawingDomainRootedMapOfExteriorFace
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) : D39DomainRootedMapV2 := by
  let missing : P.GeometricEdge → Prop := fun e =>
    (kmswStageDirectedMap w n).missing e.out
  let forward : {e : P.GeometricEdge // ¬ missing e} → Bool :=
    fun e => !e.val.out.2
  let rootDart := (kmswRootedStage w n).root
  let rootEdge : P.GeometricEdge := Quotient.mk P.edgeSetoid rootDart
  let root : P.GeometricEdge × Bool := (rootEdge, !rootEdge.out.2)
  let hmissingExternal :=
    kmswStageDrawing_missingEdges_external_of_exteriorFace P U hU hborder
  let M := finitePLDrawingDirectedMap P missing forward hmissingExternal
  have hconn : ∀ v wv : Fin (kmswStage w n).nextVertex,
      (d39GeomGraph M).Reachable v wv := by
    simpa [M, missing, forward] using
      kmswStageDrawing_geometricGraph_connected_of_external P hmissingExternal
  have hroot : M.toPlaneMapWithMissing.missing root.1 ∨
      ∃ h : ¬ M.toPlaneMapWithMissing.missing root.1,
        M.forward ⟨root.1, h⟩ = root.2 := by
    apply Or.inr
    refine ⟨?_, rfl⟩
    dsimp [M, root, rootEdge, rootDart, missing,
      finitePLDrawingDirectedMap, finitePLDrawingDirectedMap]
    rcases P.geometricEdge_out_mk rootDart with hout | hout
    · rw [hout]
      exact (kmswRootedStage w n).root_present
    · rw [hout]
      exact ((kmswStageDirectedMap w n).missing_edgeInv rootDart).not.mpr
        (kmswRootedStage w n).root_present
  exact finitePLDrawingD39DomainRootedMapV2 P missing forward
    hmissingExternal root hconn hroot

/-- Helper toward Proposition 5.16. The finite stage drawing's darts are in
bijection with its geometric edge identities together with the direction of
the selected representative path. -/
@[expose] def kmswStageDrawingDartEdgeDirectionEquiv
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) :
    StageDart (kmswStage w n).nextEdge ≃ P.GeometricEdge × Bool where
  toFun d :=
    (Quotient.mk P.edgeSetoid d,
      decide (d = (Quotient.mk P.edgeSetoid d).out))
  invFun p := if p.2 then p.1.out else edgeFlip _ p.1.out
  left_inv d := by
    let e : P.GeometricEdge := Quotient.mk P.edgeSetoid d
    by_cases h : d = e.out
    · change (if decide (d = e.out) then e.out else edgeFlip _ e.out) = d
      rw [if_pos (decide_eq_true h)]
      exact h.symm
    · change (if decide (d = e.out) then e.out else edgeFlip _ e.out) = d
      have hdec : ¬ decide (d = e.out) = true := by
        intro htrue
        exact h (of_decide_eq_true htrue)
      rw [if_neg hdec]
      rcases P.geometricEdge_out_mk d with hout | hout
      · exact False.elim (h hout.symm)
      · have hd : d = edgeFlip _ e.out := by
          rw [hout]
          simp [edgeFlip]
        exact hd.symm
  right_inv p := by
    rcases p with ⟨e, b⟩
    cases b with
    | true =>
        apply Prod.ext
        · exact Quotient.out_eq e
        · have hout := congrArg Quotient.out (Quotient.out_eq e)
          change decide (e.out = (Quotient.mk P.edgeSetoid e.out).out) = true
          rw [hout]
          exact decide_eq_true rfl
    | false =>
        apply Prod.ext
        · exact (P.geometricEdge_flip e.out).trans (Quotient.out_eq e)
        · have hout₁ := congrArg Quotient.out (P.geometricEdge_flip e.out)
          have hout₂ := congrArg Quotient.out (Quotient.out_eq e)
          have hne : edgeFlip _ e.out ≠ e.out := by
            cases e.out with
            | mk i b => cases b <;> simp [edgeFlip]
          change decide
            (edgeFlip _ e.out = (Quotient.mk P.edgeSetoid
              (edgeFlip _ e.out)).out) = false
          rw [hout₁, hout₂]
          exact decide_eq_false_iff_not.mpr hne

/-- Helper toward Proposition 5.16. The quotient direction equivalence
reconstructs each stage dart from the selected geometric edge representative
and its path direction bit. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_reconstructs
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    d = if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
      (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out
    else edgeFlip _ (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out := by
  exact (kmswStageDrawingDartEdgeDirectionEquiv P).symm_apply_apply d |>.symm

/-- Helper toward Proposition 5.16. The drawing-side vertex and position
fields of the base representation are already supplied by the stage endpoint
equivalence and injective drawing positions. -/
theorem kmswStageDrawing_baseVertexAndPositionFields
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    let M := kmswStageD39RootedMap w n
    let B := kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder
    ∃ e : RootedLocallyFiniteVertex M.core.D M.core.rot ≃ B.V,
      Function.Injective B.map.toPlaneMapWithMissing.pos := by
  dsimp
  exact ⟨kmswStageD39RootedMap_vertexEquiv w n, P.pos_injective⟩

/-- Helper toward Proposition 5.16. The quotient dart/edge/direction
equivalence preserves the stage missing-edge tag on its geometric edge. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_missing
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (d : StageDart (kmswStage w n).nextEdge) :
    let B := kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder
    B.map.toPlaneMapWithMissing.missing
        (kmswStageDrawingDartEdgeDirectionEquiv P d).1 ↔
      (kmswStageDirectedMap w n).missing d := by
  dsimp
  change (kmswStageDirectedMap w n).missing
      (Quotient.mk P.edgeSetoid d).out ↔ _
  rcases P.geometricEdge_out_mk d with hout | hout
  · rw [hout]
  · rw [hout]
    exact (kmswStageDirectedMap w n).missing_edgeInv d

/-- Helper toward Proposition 5.16. The dart/edge/direction equivalence
preserves the active stage root as the ordered root of the domain drawing. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_root
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    kmswStageDrawingDartEdgeDirectionEquiv P
        (kmswRootedStage w n).root =
      (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).root := by
  let d := (kmswRootedStage w n).root
  have hd : d.2 = false := by
    have ht := (kmswRootedStage w n).root_tail
    change ((kmswStage w n).present d.1.val = true ∧ d.2 = false) at ht
    exact ht.2
  change (Quotient.mk P.edgeSetoid d,
      decide (d = (Quotient.mk P.edgeSetoid d).out)) =
    (Quotient.mk P.edgeSetoid d,
      !(Quotient.mk P.edgeSetoid d).out.2)
  apply Prod.ext
  · rfl
  · rcases P.geometricEdge_out_mk d with hout | hout
    · rw [hout, hd]
      simp
    · rw [hout]
      have hne : d ≠ edgeFlip _ d := by
        intro heq
        have hbits := congrArg Prod.snd heq
        cases hb : d.2 <;> simp [edgeFlip, hb] at hbits
      rw [decide_eq_false_iff_not.mpr hne]
      simp [edgeFlip, hd]


























































































end DirectedDistances.PaperProofs.Section5

end
