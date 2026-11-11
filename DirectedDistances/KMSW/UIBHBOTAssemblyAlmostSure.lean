/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceOrbits

/-! # Almost-sure geometric assembly for the UIBHBOT

Helpers toward Definition 5.8
The past and future PL drawings are constructed by the existing piecewise-affine
transport theorems. No straightening of the remaining past boundary is used. -/

public section

namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Definition 5.8: on one event of full code-law measure, all
assembly support conditions hold and the past and future PL drawings exist
with exactly the required transported positions and arc images. -/
theorem uibhbotCodeLawRel_ae_assembly_drawings :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W)),
        (∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) ∧
        ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
            (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)),
          P.pos = uibhbotPastStraightTransfer W hL hR ∘
            (uibhbotPastMonotoneDrawing W hfin).pos ∧
          (∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
            ((uibhbotPastMonotoneDrawing W hfin).arc d).image) ∧
          ∃ F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
              (kmswInfRot (shiftedStream W 0) (H.1 0))
              (kmswLimitDartVertex (shiftedStream W 0)),
            F.pos = uibhbotSeparationFuturePos W H h0 ∧
            F.image ⊆ {z : ℂ | z.im ≤ 0} ∧
            ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
              h0 (H.1 0) ''
                ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
                  (monotone_family_all _)).arc d).image := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses, uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg, uibhbotCodeLawRel_ae_past_finiteIncidence]
    with W hH hhit hL hR hfin
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨P, hp, ha⟩ := uibhbotPastStraightDrawing_exists W hL hR.1 hfin
  obtain ⟨F, hFim, _, hf', hFa⟩ :=
    uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hf : F.pos = uibhbotSeparationFuturePos W H h0 := by
    rw [hf']
    rfl
  exact ⟨H, h0, hL, hR.1, hfin, hR.2, P, hp, ha, F, hf, hFim, hFa⟩

/-- Helper toward Definition 5.8: almost surely the constructed assembly has
geometric face coverage, a characterized bijection from face-successor orbits,
the exact creation-cap classification, and a unique unbounded face bordered
precisely by the east darts of globally missing edges. All support conditions
and both transported PL drawings are existential conclusions. -/
theorem uibhbotCodeLawRel_ae_assembly_faces :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W)),
        (∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) ∧
        ∃ (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
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
            h0 (H.1 0) ''
              ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
                (monotone_family_all _)).arc d).image)
          (G : WholePlaneDrawing W H)
          (faceOfOrbit : Quotient (Equiv.Perm.SameCycle.setoid
            (wholePlaneFaceSucc W H)) → G.Face),
          G = uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa ∧
          (∀ K : G.Face, ∃ d : WholePlaneDart W, G.dartBorders d K) ∧
          Function.Bijective faceOfOrbit ∧
          (∀ (d : WholePlaneDart W) (K : G.Face),
            faceOfOrbit (Quotient.mk _ d) = K ↔ G.dartBorders d K) ∧
          (∃ U : G.Face, G.IsUnbounded U ∧
            G.dartBorders (uibhbotWholePlaneOuterDart W) U ∧
            ∀ K : G.Face, K = U ∨
              (∃ j : TriangleCreationTime (shiftedStream W 0),
                K.val = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
                  (capFace (shiftedStream W 0) (H.1 0) j).val) ∨
              (∃ j : TriangleCreationTime (kmswPastCode W),
                K.val = uibhbotAssemblyHalfTurn ''
                  (uibhbotPastStraightTransfer W hL hR ''
                    (capFace (kmswPastCode W) hfin j).val))) ∧
          (∃! U : G.Face, G.IsUnbounded U) ∧
          ∀ (K : G.Face), G.IsUnbounded K → ∀ d : WholePlaneDart W,
            G.dartBorders d K ↔ d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1 := by
  filter_upwards [uibhbotCodeLawRel_ae_assembly_drawings] with W hW
  obtain ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa⟩ := hW
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let faceOfOrbit :=
    uibhbot_assembly_faceOfOrbit W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa,
    G, faceOfOrbit, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact uibhbot_assembly_face_has_bordering_dart
      W H h0 hL hR hfin P hp ha F hf hFim hFa
  · exact uibhbot_assembly_faceOfOrbit_bijective
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  · exact uibhbot_assembly_faceOfOrbit_mk_eq_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  · exact uibhbot_assembly_face_classification
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  · exact uibhbot_assembly_unbounded_face_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  · exact uibhbot_assembly_unbounded_dartBorders_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

end DirectedDistances.KMSW
