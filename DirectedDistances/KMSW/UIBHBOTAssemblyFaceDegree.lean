/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyAlmostSure
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFaceTriangles
public import DirectedDistances.KMSW.MhatWestBoundarySide

/-! # Geometric face degree toward the UIBHBOT assembly

Helpers toward Definition 5.8. The face-orbit classification and created
triangle edge identities are the starting point; geometric multiplicity still
has to be read from the general plane carrier. -/

public section

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open MeasureTheory
open scoped Classical

/-- Helper toward Definition 5.8: the three geometric edge IDs in every
created triangle remain distinct after passage through the whole-plane
colimit and the drawing's dart-flip quotient. -/
theorem wholePlane_stageTriangle_geometricEdges_card
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    ((Finset.univ : Finset (Fin 3)).image
      (fun i : Fin 3 => Quotient.mk G.edgeSetoid
        (wholePlaneDartι W N
          (if i.val = 0 then
            (stageTriangleDartTriple (shiftedStream W N) j).1
          else if i.val = 1 then
            (stageTriangleDartTriple (shiftedStream W N) j).2.1
          else
            (stageTriangleDartTriple (shiftedStream W N) j).2.2)))).card = 3 := by
  let t := stageTriangleDartTriple (shiftedStream W N) j
  let raw : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  let edge : Fin 3 → G.GeometricEdge := fun i =>
    Quotient.mk G.edgeSetoid (wholePlaneDartι W N (raw i))
  have hids := stageTriangleDartTriple_edgeIds_distinct (shiftedStream W N) j
  have hinj : Function.Injective edge := by
    intro i k hik
    have hrel : wholePlaneDartι W N (raw i) = wholePlaneDartι W N (raw k) ∨
        wholePlaneDartι W N (raw i) = wholePlaneDartFlip W
          (wholePlaneDartι W N (raw k)) := by
      exact Quotient.exact hik
    have he : (raw i).1 = (raw k).1 := by
      have hq : wholePlaneEdgeι W N (raw i).1 =
          wholePlaneEdgeι W N (raw k).1 := by
        rcases hrel with h | h
        · change (wholePlaneEdgeι W N (raw i).1, (raw i).2) =
            (wholePlaneEdgeι W N (raw k).1, (raw k).2) at h
          exact congrArg Prod.fst h
        · change (wholePlaneEdgeι W N (raw i).1, (raw i).2) =
            (wholePlaneEdgeι W N (raw k).1, !(raw k).2) at h
          exact congrArg Prod.fst h
      exact wholePlaneEdgeι_injective W N hq
    fin_cases i <;> fin_cases k <;>
      simp_all [raw, t]
  rw [show (Finset.univ : Finset (Fin 3)).image
      (fun i => Quotient.mk G.edgeSetoid (wholePlaneDartι W N
        (if i.val = 0 then
          (stageTriangleDartTriple (shiftedStream W N) j).1
        else if i.val = 1 then
          (stageTriangleDartTriple (shiftedStream W N) j).2.1
        else
          (stageTriangleDartTriple (shiftedStream W N) j).2.2))) =
      Finset.univ.image edge by rfl]
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- Helper toward Definition 5.8: almost surely every internal assembly face
corresponds to a created triangle orbit whose three darts lie on three
distinct geometric edges. This records combinatorial edge degree; it does not
identify that count with the carrier's neighborhood-defined `faceDegree`. -/
theorem uibhbotCodeLawRel_ae_assembly_internal_face_triangle_edges :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (_hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
          (shiftedStream W 0) h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (G : WholePlaneDrawing W H)
        (faceOfOrbit : Quotient (Equiv.Perm.SameCycle.setoid
          (wholePlaneFaceSucc W H)) → G.Face),
        G = uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa ∧
        Function.Bijective faceOfOrbit ∧
        (∀ (d : WholePlaneDart W) (K : G.Face),
          faceOfOrbit (Quotient.mk _ d) = K ↔ G.dartBorders d K) ∧
        (∀ K : G.toPlaneGraphDrawing.Face,
          G.toPlaneGraphDrawing.IsInternal K →
            ∃ q : Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H)),
              faceOfOrbit q = G.toPlaneGraphDrawingFaceEquiv K ∧
              ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
              {d : WholePlaneDart W | Quotient.mk _ d = q} =
              wholePlaneDartι W N ''
                {a | a ∈ stageTriangleDartList (shiftedStream W N) j} ∧
            ((Finset.univ : Finset (Fin 3)).image
              (fun i : Fin 3 => Quotient.mk G.edgeSetoid
                (wholePlaneDartι W N
                  (if i.val = 0 then
                    (stageTriangleDartTriple (shiftedStream W N) j).1
                  else if i.val = 1 then
                    (stageTriangleDartTriple (shiftedStream W N) j).2.1
                  else
                    (stageTriangleDartTriple (shiftedStream W N) j).2.2)))).card = 3) := by
  filter_upwards [uibhbotCodeLawRel_ae_assembly_faces,
    uibhbotCodeLawRel_ae_faceOrbit_triangle] with W hfaces htri
  obtain ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa,
    G, faceOfOrbit, hG, _, hbij, hchar, hclassification, _, _⟩ := hfaces
  obtain ⟨Htri, _, _, htri⟩ := htri
  have hH : Htri = H := Subsingleton.elim _ _
  subst Htri
  obtain ⟨U, hU, hOuter, _⟩ := hclassification
  let E := Equiv.ofBijective faceOfOrbit hbij
  refine ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa,
    G, faceOfOrbit, hG, hbij, hchar, ?_⟩
  intro K hK
  let K' := G.toPlaneGraphDrawingFaceEquiv K
  let q : Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H)) := E.symm K'
  have hq : faceOfOrbit q = K' := E.apply_symm_apply K'
  have hroot : q ≠ Quotient.mk _ (uibhbotWholePlaneOuterDart W) := by
    intro heq
    have hborder : G.dartBorders (uibhbotWholePlaneOuterDart W) K' := by
      apply (hchar _ _).mp
      rw [← heq]
      exact hq
    have hKU : K' = U := G.dartBorders_face_unique _ _ _ hborder hOuter
    have hnotU : ¬ G.IsUnbounded K' := by
      intro hu
      exact hK ((G.toPlaneGraphDrawing_isExternal_iff K).mpr hu)
    exact hnotU (hKU ▸ hU)
  obtain ⟨N, j, hdarts, _⟩ := (htri q).mp hroot
  exact ⟨q, hq, N, j, by simpa only [q] using hdarts,
    wholePlane_stageTriangle_geometricEdges_card W H G N j⟩

end DirectedDistances.KMSW
