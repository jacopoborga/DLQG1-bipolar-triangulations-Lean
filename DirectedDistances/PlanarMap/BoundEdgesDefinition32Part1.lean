/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact28
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect7
public import DirectedDistances.PaperProofs.Section4.UIQBOTOkInf
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry19
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry3






public section

namespace DirectedDistances.PlanarMap

open unitInterval
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: both exact winding characterizations hold
when every vertex is incident. The geometric condition is proved below for
the infinite construction carriers, rather than imposed on their results. -/
theorem boundEdges32_winding_characterizations_of_incident_part1
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S)
    (hincident : Function.Surjective (boundaryDartInitial M)) (e : E) :
    (e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) ∧
    (e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) := by
  have hfinite := locallyFiniteVertexImage_of_surjective G hincident
  exact ⟨mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e,
    mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e⟩

/-- Helper toward Definition 3.2: both exact winding characterizations hold
for every finite vertex carrier, with no incidence or vertex-image premise. -/
theorem boundEdges32_winding_characterizations_of_finite_part1
    {V : Type uV} {E : Type uE} [Finite V]
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (e : E) :
    (e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) ∧
    (e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) := by
  have hfinite := locallyFiniteVertexImage_of_finite_vertices G
  exact ⟨mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e,
    mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
    M B G U S h hfinite e⟩

/-- Helper toward Definition 3.2: every PL drawing on the canonical UIQBOT
map carrier has locally finite vertex image, by the proved dart incidence. -/
theorem uiqbot_boundEdges32_locallyFiniteVertexImage_part1
    (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    {rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)}
    (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)))) :
    LocallyFiniteVertexImage G :=
  locallyFiniteVertexImage_of_surjective G
    (uiqbotCanonicalQuotientDrawing_vert_surjective w hfin)

/-- Helper toward Definition 3.2: every finite KMSW-stage carrier has locally
finite vertex image, even for drawings other than the chosen realization. -/
theorem kmswStage_boundEdges32_locallyFiniteVertexImage_part1
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    {rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool)}
    (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
      (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) : LocallyFiniteVertexImage G :=
  locallyFiniteVertexImage_of_finite_vertices G

/- Helper toward Definition 3.2: every transported boundary-channeled
carrier drawing has locally finite vertex image. No outer-face hypothesis -/
theorem boundaryChanneled_boundEdges32_locallyFiniteVertexImage_part1
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (P : BoundaryChanneledPLDrawing R)
    {rot : Equiv.Perm (P.GeometricEdge × Bool)}
    (G : PLDrawing (P.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R P))) :
    LocallyFiniteVertexImage G := by
  apply locallyFiniteVertexImage_of_surjective G
  intro v
  obtain ⟨d, hd⟩ := boundaryChanneled_dartTailVertex_surjective R v
  exact ⟨boundaryChanneledDartPairEquiv19 P d,
    (boundaryChanneledDartPairEquiv19_initial R P d).trans hd⟩

section UIBHBOT

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
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "A" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: every PL drawing on the actual UIBHBOT
boundary carrier has locally finite vertex image, including the fixed
reversed presentation's drawing. This is a carrier statement, so no
agreement of the new drawing's positions with the assembly is needed. -/
theorem uibhbot_boundEdges32_locallyFiniteVertexImage_part1
    {rot : Equiv.Perm ((A).GeometricEdge × Bool)}
    (G : PLDrawing ((A).GeometricEdge × Bool) (WholePlaneVertex W)
      (fun d => (d.1, !d.2)) rot (boundaryDartInitial M)) :
    LocallyFiniteVertexImage G := by
  apply locallyFiniteVertexImage_of_surjective G
  intro v
  obtain ⟨d, hd⟩ := WholePlanePastGlueData.vertex_incident W v
  exact ⟨uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d,
    (uibhbotAssemblyBoundaryDartEquiv3_initialVertex
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d).trans hd⟩

end UIBHBOT

end DirectedDistances.PlanarMap



















































