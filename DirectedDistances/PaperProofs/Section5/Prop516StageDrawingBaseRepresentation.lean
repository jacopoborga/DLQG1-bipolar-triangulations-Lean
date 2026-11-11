/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation4
public import DirectedDistances.PlanarMap.D39DrawingRepresentation
public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2

/-! # Finite stage drawing base representation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. Every vertex label of a finite KMSW
stage is the endpoint of a dart, so the stage drawing vertex map is
surjective. -/
theorem kmswStageDrawing_vertex_surjective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Surjective (stageVertex w n) := by
  intro v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
  exact ⟨d, Fin.ext (by simpa [stageVertex] using hd)⟩

/-- Helper toward Proposition 5.16. In a certified finite stage drawing,
every missing dart's whole geometric edge lies in the closure of the certified
unbounded face. The full-arc conclusion uses the PL drawing's dart-border
closure theorem, not only the local exterior-sector witness. -/
theorem kmswStageDrawing_missingArc_subset_unboundedFaceClosure
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    ∀ d : StageDart (kmswStage w n).nextEdge,
      (kmswStageDirectedMap w n).missing d →
        ∃ F : P.Face, P.IsUnbounded F ∧
          (P.arc d).image ⊆ closure F.val := by
  intro d hd
  have hsurj := kmswStageDrawing_vertex_surjective w n
  obtain ⟨F, hF, hborder⟩ :=
    kmswStage_missingDart_borders_exterior P G d hd
  rcases hborder with hborder | hborder
  · exact ⟨F, hF, P.dartBorders_arc_subset_closure hsurj d F hborder⟩
  · have hsubset := P.dartBorders_arc_subset_closure hsurj (edgeFlip _ d) F hborder
    have hflip : (P.arc (edgeFlip _ d)).image = (P.arc d).image :=
      P.arc_image_flip d
    rw [hflip] at hsubset
    exact ⟨F, hF, hsubset⟩

/-- Helper toward Proposition 5.16. The stage missing-edge predicate, viewed
on individual geometric edge identities of the drawing, satisfies the
external-face axiom required by `PlaneMapWithMissing`. -/
theorem kmswStageDrawing_missingEdges_external
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    ∀ e : P.GeometricEdge,
      (kmswStageDirectedMap w n).missing e.out →
        ∃ F : P.toPlaneGraphDrawing.Face,
          PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
            Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val := by
  intro e he
  let d := e.out
  have hd : (kmswStageDirectedMap w n).missing d := by
    simpa [d] using he
  obtain ⟨F, hF, hsubset⟩ :=
    kmswStageDrawing_missingArc_subset_unboundedFaceClosure P G d hd
  refine ⟨P.toPlaneGraphDrawingFaceEquiv.symm F,
    (P.toPlaneGraphDrawing_isExternal_iff _).2 hF, ?_⟩
  rw [← Quotient.out_eq e, P.toPlaneGraphDrawing_arc_range]
  change (P.arc e.out).image ⊆ closure F.val
  exact hsubset

/-- Helper toward Proposition 5.16. The directed geometric map on the finite
stage drawing retains each dart-flip orbit as an edge identity, uses the
stage missing tag, and orients a present edge according to the stage dart
stored by the quotient representative. -/
@[expose] def kmswStageDrawingDirectedPlaneMap
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex) P.GeometricEdge :=
  finitePLDrawingDirectedMap P
    (fun e => (kmswStageDirectedMap w n).missing e.out)
    (fun e => !e.val.out.2)
    (kmswStageDrawing_missingEdges_external P G)

/-- Helper toward Proposition 5.16. Package the finite KMSW stage's rooted
directed map as a local topology rooted map, retaining its active present tail dart as
the ordered root mark. -/
@[expose] def kmswStageD39RootedMap (w : ℕ → Fin 3) (n : ℕ) :
    D39RootedMap := by
  let R := kmswRootedStage w n
  let S := R.map
  let C : D39MapCore := {
    D := StageDart (kmswStage w n).nextEdge
    rot := S.toCombinatorialMap.rot
    edgeInv := S.toCombinatorialMap.edgeInv
    edgeInv_invol := S.toCombinatorialMap.edgeInv_invol
    edgeInv_ne := S.toCombinatorialMap.edgeInv_ne
    missing := S.missing
    missing_edgeInv := S.missing_edgeInv
    tail := S.tail
    tail_iff := S.tail_iff
    tail_missing := S.tail_missing
    outer := S.outer
    missing_outer := S.missing_outer
    locallyFinite := by
      intro d
      exact Set.toFinite _
    connected := by
      change (kmswMap w n).IsConnected
      exact kmswMap_isConnected w n
    acyclic := by
      change (kmswStageDirectedMap w n).IsAcyclic
      exact kmswStageDirectedMap_isAcyclic w n
  }
  exact ⟨C, .present R.root R.root_present R.root_tail⟩

/-- Helper toward Proposition 5.16. The rotation-orbit vertices of the
stage local topology rooted map are identified with the KMSW creation-order vertex IDs. -/
@[expose] noncomputable def kmswStageD39RootedMap_vertexEquiv
    (w : ℕ → Fin 3) (n : ℕ) :
    RootedLocallyFiniteVertex
        (kmswStageD39RootedMap w n).core.D
        (kmswStageD39RootedMap w n).core.rot ≃
      Fin (kmswStage w n).nextVertex := by
  change (kmswMap w n).VertexQuotient ≃ Fin (kmswStage w n).nextVertex
  exact stageVertexEquiv w n

/-- Helper toward Proposition 5.16. The geometric stage map inherits
injective vertex positions directly from the stage drawing. -/
theorem kmswStageDrawing_positions_injective
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    Function.Injective
      (kmswStageDrawingDirectedPlaneMap P G).toPlaneMapWithMissing.pos :=
  P.pos_injective

/-- Helper toward Proposition 5.16. Missing status on the geometric edge
quotient agrees with the KMSW stage missing tag on every dart representative. -/
theorem kmswStageDrawing_missing_mk
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) (d : StageDart (kmswStage w n).nextEdge) :
    (kmswStageDrawingDirectedPlaneMap P G).toPlaneMapWithMissing.missing
        (Quotient.mk P.edgeSetoid d) ↔
      (kmswStageDirectedMap w n).missing d := by
  change (kmswStageDirectedMap w n).missing
      (Quotient.mk P.edgeSetoid d).out ↔ _
  rcases P.geometricEdge_out_mk d with h | h
  · rw [h]
  · rw [h]
    exact ((kmswStageDirectedMap w n).missing_edgeInv d).symm

/-- Helper toward Proposition 5.16. The geometric edge represented by the
KMSW active root dart is present, and the representative-based forward bit
supplies a valid ordered root mark for the stage drawing map. -/
theorem kmswStageDrawing_root_valid
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    let M := kmswStageDrawingDirectedPlaneMap P G
    let e := Quotient.mk P.edgeSetoid (kmswRootedStage w n).root
    M.toPlaneMapWithMissing.missing e ∨
      ∃ h : ¬ M.toPlaneMapWithMissing.missing e,
        M.forward ⟨e, h⟩ = !e.out.2 := by
  dsimp
  apply Or.inr
  refine ⟨?_, rfl⟩
  rw [kmswStageDrawing_missing_mk P G]
  exact (kmswRootedStage w n).root_present

/-- Helper toward Proposition 5.16. Reflexive-transitive reachability using
equality steps and geometric graph edges implies graph reachability. -/
theorem kmswStageDrawing_reachable_of_eq_or_adj
    {V E : Type*} (M : DirectedPlaneMapWithMissing V E) {v w : V}
    (h : Relation.ReflTransGen
      (fun x y => x = y ∨ d39GeomAdj M x y) v w) :
    (d39GeomGraph M).Reachable v w := by
  apply (SimpleGraph.reachable_iff_reflTransGen _ _).2
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y hpath hxy ih =>
      rcases hxy with hEq | hAdj
      · subst y
        exact ih
      · exact Relation.ReflTransGen.tail ih hAdj

/-- Helper toward Proposition 5.16. The local topology geometric graph of the finite
stage drawing is connected, by transporting combinatorial dart connectedness
through the drawing's edge quotient. -/
theorem kmswStageDrawing_geometricGraph_connected
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    ∀ v w : Fin (kmswStage w n).nextVertex,
      (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P G)).Reachable v w := by
  intro v wv
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
  let e := Classical.choose (stageEndpoint_exists w n wv.val wv.isLt)
  let M := kmswStageDrawingDirectedPlaneMap P G
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
    by_cases hEq : stageVertex w n x = stageVertex w n (edgeFlip _ x)
    · exact Or.inl hEq
    · right
      let f : P.GeometricEdge := Quotient.mk P.edgeSetoid x
      change stageVertex w n x ≠ stageVertex w n (edgeFlip _ x) ∧
        ∃ f : P.GeometricEdge,
          (stageVertex w n f.out = stageVertex w n x ∧
            stageVertex w n (edgeFlip _ f.out) = stageVertex w n (edgeFlip _ x)) ∨
          (stageVertex w n f.out = stageVertex w n (edgeFlip _ x) ∧
            stageVertex w n (edgeFlip _ f.out) = stageVertex w n x)
      refine ⟨hEq, f, ?_⟩
      rcases P.geometricEdge_out_mk x with hout | hout
      · left
        constructor
        · rw [hout]
        ·
          rw [hout]
      · right
        constructor
        · rw [hout]
        ·
          rw [hout]
          simp [edgeFlip]
  have hstep {x y : StageDart (kmswStage w n).nextEdge}
      (hxy : y = stageRot w n x ∨ y = (stageRot w n).symm x ∨
        y = edgeFlip _ x ∨ y = (edgeFlip _).symm x) : R (stageVertex w n x) (stageVertex w n y) := by
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
  have hreach := kmswStageDrawing_reachable_of_eq_or_adj M hvertices
  have hstart : stageVertex w n d = v := Fin.ext hd
  have he : stageEndpoint (kmswStage w n) e = wv.val :=
    Classical.choose_spec (stageEndpoint_exists w n wv.val wv.isLt)
  have hfinish : stageVertex w n e = wv := Fin.ext he
  simpa [hstart, hfinish] using hreach

/-- Helper toward Proposition 5.16. Construct the local topology domain rooted map on a
finite stage drawing. Its vertex positions and individual geometric edge
identities come from `P`; its ordered root edge is the active dart of the
KMSW rooted stage, with the bit selected by the drawing's edge representative. -/
@[expose] def kmswStageDrawingDomainRootedMap
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) : D39DomainRootedMapV2 := by
  let missing : P.GeometricEdge → Prop := fun e =>
    (kmswStageDirectedMap w n).missing e.out
  let forward : {e : P.GeometricEdge // ¬ missing e} → Bool :=
    fun e => !e.val.out.2
  let rootDart := (kmswRootedStage w n).root
  let rootEdge : P.GeometricEdge := Quotient.mk P.edgeSetoid rootDart
  let root : P.GeometricEdge × Bool := (rootEdge, !rootEdge.out.2)
  refine finitePLDrawingD39DomainRootedMapV2 P missing forward
    (kmswStageDrawing_missingEdges_external P G) root ?_ ?_
  · exact kmswStageDrawing_geometricGraph_connected P G
  · simpa [root, rootEdge, rootDart, missing, forward,
      kmswStageDrawingDirectedPlaneMap, finitePLDrawingDirectedMap] using
      kmswStageDrawing_root_valid P G























































end DirectedDistances.PaperProofs.Section5

end
