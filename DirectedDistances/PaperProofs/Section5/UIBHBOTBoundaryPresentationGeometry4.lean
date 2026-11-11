/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry3
































public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk Filter
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults

noncomputable section

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

local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: if a lower-left ray is covered by the
external boundary, that boundary dart set is infinite. -/
theorem externalBoundaryDartSet4_infinite_of_lowerLeft_ray
    {V : Type _} {E : Type _} {N : DirectedPlaneMapWithMissing V E}
    {Q : InfiniteBoundaryPresentation N}
    (hmap : IsBoundaryOrderOfInf N Q)
    (ray : ℕ ↪ Q.lowerLeft.Index) :
    ¬ (externalBoundaryDartSet4 N).Finite := by
  intro hf
  let f : ℕ → E × Bool := fun n => Q.lowerLeft.darts (ray n)
  have hinj : Function.Injective f := Q.lowerLeft.darts.injective.comp ray.injective
  have hpre : (f ⁻¹' externalBoundaryDartSet4 N).Finite := hf.preimage hinj.injOn
  apply Set.infinite_univ (α := ℕ)
  apply hpre.subset
  intro n _
  apply (((IsBoundaryOrderOfInf_iff Q).mp hmap).1 _).mp
  refine ⟨InfiniteBoundaryDartIndex.lowerLeft (ray n), ?_⟩
  rw [InfiniteBoundaryDartIndex.dart_eq]

/-- Helper toward Definition 3.2: the UIBHBOT presentation has infinitely
many external darts whenever it has the source-certified boundary-order
property. -/
theorem uibhbotDefinition32Presentation_externalBoundaryInfinite
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj)) :
    ¬ (externalBoundaryDartSet4 M).Finite := by
  let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj
  have hidx : Q.lowerLeft.Index = ℤ := by
    dsimp only [Q]
    rw [uibhbotDefinition32Presentation_eq]
  let ray : ℕ ↪ Q.lowerLeft.Index :=
    ⟨fun n => cast hidx.symm (n : ℤ), by
      intro n m h
      have h' := congrArg (cast hidx) h
      have h'' : (n : ℤ) = (m : ℤ) := by simpa using h'
      exact_mod_cast h''⟩
  exact externalBoundaryDartSet4_infinite_of_lowerLeft_ray hmap ray

/-- Helper toward Definition 3.2: the required empty upper-left and
lower-right UIBHBOT presentation sides are simple. -/
theorem uibhbotDefinition32Presentation_emptySides_simple
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    IsSimpleBoundarySide M
        (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
          hRpos e hinj).upperLeft ∧
      IsSimpleBoundarySide M
        (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
          hRpos e hinj).lowerRight := by
  let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj
  have hul : IsEmpty Q.upperLeft.Index := by
    dsimp only [Q]
    rw [uibhbotDefinition32Presentation_eq]
    infer_instance
  have hlr : IsEmpty Q.lowerRight.Index := by
    dsimp only [Q]
    rw [uibhbotDefinition32Presentation_eq]
    infer_instance
  exact ⟨isSimpleBoundarySide_of_isEmpty5 Q.upperLeft,
    isSimpleBoundarySide_of_isEmpty5 Q.lowerRight⟩

/-- Helper toward Definition 3.2: the v7 predicate on the UIBHBOT wrapper
reduces to its v3 clause when the proved boundary-order data gives an
infinite external dart set. -/
theorem uibhbotDefinition32Presentation_externalFaceIntervalOrder7_iff
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj))
    {rot : Equiv.Perm
      ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
        × Bool)}
    (G' : PLDrawing
      ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
        × Bool) (WholePlaneVertex W) (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G'.Face)
    (S : ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
      × Bool) → ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
      × Bool)) :
    let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos e hinj
    let B : BoundaryPresentationWithJunctions M := ⟨Q, none⟩
    IsExternalFaceIntervalOrder7 M B G' U S ↔
      IsExternalFaceIntervalOrder3 M Q G' U S := by
  let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj
  let B : BoundaryPresentationWithJunctions M := ⟨Q, none⟩
  have hinfinite : ¬ (externalBoundaryDartSet4 M).Finite :=
    uibhbotDefinition32Presentation_externalBoundaryInfinite W H h0 hL hR hfin P hp ha
      F hf hFim hFa hRpos e hinj hmap
  change IsExternalFaceIntervalOrder7 M B G' U S ↔
    IsExternalFaceIntervalOrder3 M Q G' U S
  rw [IsExternalFaceIntervalOrder7.infinite_iff hinfinite]
  simp [B]

/-- Helper toward Definition 3.2: almost surely the UIBHBOT presentation
has an infinite external dart set and no finite-junction marks, alongside the
source-certified boundary and side clauses. -/
theorem ae_uibhbotDefinition32Presentation_infiniteExternalBoundary :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
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
        (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e),
        let M' := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
          hFim hFa hRpos e hinj
        let B : BoundaryPresentationWithJunctions M' := ⟨Q, none⟩
        (¬ (externalBoundaryDartSet4 M').Finite ∧ B.finiteJunctions? = none) ∧
          IsBoundaryOrderOfInf M' Q ∧
          ULOkInf Q ∧ UROkInf Q ∧ LROkInf Q ∧ LLOkInf Q ∧
          IsSimpleBoundarySide M' Q.upperLeft ∧
          IsSimpleBoundarySide M' Q.lowerRight ∧
          BoundarySideEndpointLabels M' Q.upperLeft ∧
          BoundarySideEndpointLabels M' Q.upperRight ∧
          BoundarySideEndpointLabels M' Q.lowerRight ∧
          BoundarySideEndpointLabels M' Q.lowerLeft := by
  filter_upwards [ae_uibhbotDefinition32Presentation_boundaryAndEndpointClauses]
    with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hboundary, hUL, hUR, hLR, hLL,
    hEL, hER, hELR, hELL⟩
  let M' := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj
  let B : BoundaryPresentationWithJunctions M' := ⟨Q, none⟩
  have hmap : IsBoundaryOrderOfInf M' Q := hboundary
  have hinfinite : ¬ (externalBoundaryDartSet4 M').Finite :=
    uibhbotDefinition32Presentation_externalBoundaryInfinite W H h0 hL hR hfin P hp ha
      F hf hFim hFa hRpos e hinj hmap
  have hnone : B.finiteJunctions? = none := rfl
  have hsimple := uibhbotDefinition32Presentation_emptySides_simple
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hinj,
    ⟨hinfinite, hnone⟩, hmap, hUL, hUR, hLR, hLL,
    hsimple.1, hsimple.2, hEL, hER, hELR, hELL⟩

/-- Helper toward Definition 3.2: project the transported geometric missing
dart classification and geometric-successor clause from Geometry3. -/
theorem uibhbotAssemblyBoundaryPresentationExternalFace3_geometryClauses :
    ∃ G' : PLDrawing
        ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
          × Bool) (WholePlaneVertex W) (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      ∃ U : G'.Face,
        (∀ d, G'.dartBorders d U ↔
          (((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).2 = true ∧
            ¬ wholePlaneEdgePresent W
              ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).1)) ∧
        IsGeometricExternalFaceSucc G' U
          (fun d => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
            (wholePlaneFaceSucc W H
              ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d))) := by
  obtain ⟨G', U, _, _, hborder, hsucc⟩ :=
    uibhbotAssemblyBoundaryPresentationExternalFace3 W H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos
  exact ⟨G', U, hborder, hsucc⟩





























































end
end DirectedDistances.PaperProofs.Section5

end
