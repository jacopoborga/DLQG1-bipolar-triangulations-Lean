/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyAlmostSure
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFaceTriangles
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrbit
public import DirectedDistances.RandomWalk.UIBHBOTWalkLaw

























public section

namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section5
open scoped Classical

























theorem def_uibhbot_provider :
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
          h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
      let M := uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      let E := uibhbot_assembly_faceOrbitEquiv
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      (∀ a, M.missing a → ∃ K : M.toPlaneGraphDrawing.Face,
        M.toPlaneGraphDrawing.IsExternal K ∧ Set.range (M.arc a) ⊆ closure K.val) ∧
      M.IsAcyclic ∧
      (∃! K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K) ∧
      (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K →
        ∀ d : WholePlaneDart W,
          G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv K) ↔
            d.2 = true ∧ M.missing (Quotient.mk G.edgeSetoid d)) ∧
      (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K →
        ∀ a : G.GeometricEdge,
          (∃ d : WholePlaneDart W, Quotient.mk G.edgeSetoid d = a ∧
            G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv K)) ↔ M.missing a) ∧
      (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsInternal K →
        ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
          {d : WholePlaneDart W | E (Quotient.mk _ d) =
              G.toPlaneGraphDrawingFaceEquiv K} =
            wholePlaneDartι W N '' {a | a ∈ stageTriangleDartList (shiftedStream W N) j} ∧
          ((stageTriangleDartList (shiftedStream W N) j).toFinset.image
            (wholePlaneDartι W N)).card = 3) ∧
      (∀ k : ℤ,
        wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
        wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
        ¬ wholePlaneEdgePresent W (e k) ∧
        ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
          e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
      Function.Injective e ∧ e 0 = uibhbotRootEdge W ∧
      (∀ k : ℤ, wholePlaneFaceSucc W H (e k, true) = (e (k - 1), true)) ∧
      (∀ a : WholePlaneEdge W, ¬ wholePlaneEdgePresent W a ↔ ∃! k : ℤ, a = e k) ∧
      (∀ k : ℤ, IsLeast {t : ℤ | (wholePlaneWordIntegral W t).1 = k}
        (uibhbotBoundaryHitTime k W)) ∧
      StrictAnti (fun k : ℤ => uibhbotBoundaryHitTime k W) ∧
      uibhbotBoundaryHitTime 0 W = 0 ∧
      M.missing (Quotient.mk G.edgeSetoid (uibhbotRootEdge W, false)) ∧
      (wholePlaneEdgeWest W (uibhbotRootEdge W),
        wholePlaneEdgeEast W (uibhbotRootEdge W)) =
        ((uibhbotBusemannSource 0 W).id, (uibhbotBusemannSource 1 W).id) ∧
      wholePlaneWordIntegral W 0 = 0 ∧
      (∀ t : ℤ, t ≤ -1 → 1 ≤ (wholePlaneWordIntegral W t).1) ∧
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun V : ℤ → Fin 3 => fun n : ℕ => wholePlaneWordIntegral V n) =
        iidCodeMeasure.map (fun ω => fun n : ℕ => codeWalk ω n) ∧
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun V : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral V t) =
        uibhbotWordFamilyLaw.map uibhbotConcatWalk := by
  filter_upwards [uibhbotCodeLawRel_ae_assembly_drawings,
    uibhbotCodeLawRel_ae_faceOrbit_triangle,
    uibhbotCodeLawRel_ae_sourceChainEastDarts_outerOrbit_iff,
    ae_uibhbotBoundaryHitTime_isLeast, ae_uibhbotBoundaryHitTime_strictAnti,
    ae_uibhbotBoundaryHitTime_zero, ae_uibhbotBoundaryHit_strictRecord]
    with W hdraw htri hchain hleast hanti hzero hrecord
  obtain ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa⟩ := hdraw
  obtain ⟨Htri, hhitTri, Ctri, htri⟩ := htri
  obtain ⟨Hchain, hhit, e, hedge, hinj, hroot, horbit, hexhaust⟩ := hchain
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let E := uibhbot_assembly_faceOrbitEquiv
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hmissing (d : WholePlaneDart W) :
      M.missing (Quotient.mk G.edgeSetoid d) ↔ ¬ wholePlaneEdgePresent W d.1 :=
    uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d
  have hext (K : M.toPlaneGraphDrawing.Face) :
      M.toPlaneGraphDrawing.IsExternal K ↔
        G.IsUnbounded (G.toPlaneGraphDrawingFaceEquiv K) :=
    G.toPlaneGraphDrawing_isExternal_iff K
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    M.missing_on_external, ?_, ?_, ?_, ?_, ?_, hedge, hinj, hroot, ?_, ?_,
    hleast, hanti, hzero, ?_, ?_, ?_, ?_, ?_, uibhbotCodeLawRel_map_walk⟩
  · exact uibhbotAssemblyDirectedPlaneMapWithMissing_isAcyclic
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  · obtain ⟨U, hU, huniq⟩ := uibhbot_assembly_unbounded_face_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
    refine ⟨G.toPlaneGraphDrawingFaceEquiv.symm U, (hext _).mpr hU, ?_⟩
    intro K hK
    apply G.toPlaneGraphDrawingFaceEquiv.injective
    exact (huniq _ ((hext K).mp hK)).trans
      (G.toPlaneGraphDrawingFaceEquiv.apply_symm_apply U).symm
  · intro K hK d
    rw [hmissing d]
    exact uibhbot_assembly_unbounded_dartBorders_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ ((hext K).mp hK) d
  · intro K hK a
    have hb (d : WholePlaneDart W) := uibhbot_assembly_unbounded_dartBorders_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ ((hext K).mp hK) d
    constructor
    · rintro ⟨d, rfl, hd⟩
      exact (hmissing d).mpr ((hb d).mp hd).2
    · intro ha
      let d : WholePlaneDart W := (a.out.1, true)
      have hd : Quotient.mk G.edgeSetoid d = a := by
        calc
          Quotient.mk G.edgeSetoid d = Quotient.mk G.edgeSetoid a.out := by
            apply Quotient.sound
            rcases ho : a.out with ⟨j, b⟩
            cases b with
            | false => exact Or.inr (by simp [d, ho, wholePlaneDartFlip]; rfl)
            | true => exact Or.inl (by simp [d, ho]; rfl)
          _ = a := Quotient.out_eq a
      refine ⟨d, hd, (hb d).mpr ⟨rfl, ?_⟩⟩
      exact (hmissing d).mp (hd.symm ▸ ha)
  · intro K hK
    let q := E.symm (G.toPlaneGraphDrawingFaceEquiv K)
    have hq : q ≠ Quotient.mk _ (uibhbotWholePlaneOuterDart W) := by
      intro hq
      apply hK
      apply (hext K).mpr
      apply (uibhbot_assembly_isUnbounded_iff_outer_dartBorders
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _).mpr
      apply (uibhbot_assembly_faceOrbitEquiv_mk_eq_iff
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ _).mp
      rw [← hq]
      exact E.apply_symm_apply _
    obtain ⟨N, j, hset, hcard⟩ := (htri q).mp hq
    refine ⟨N, j, ?_, hcard⟩
    have hs : {d : WholePlaneDart W | E (Quotient.mk _ d) =
          G.toPlaneGraphDrawingFaceEquiv K} =
        {d : WholePlaneDart W | (Quotient.mk _ d :
          Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H))) = q} := by
      ext d
      exact E.eq_symm_apply.symm
    exact hs.trans hset
  · intro k
    exact uibhbotSourceChainEastDart_faceSucc W H hhit e
      (fun j => (hedge j).1) (fun j => (hedge j).2.1)
      (fun j => (hedge j).2.2.1) k
  · intro a
    constructor
    · intro ha
      have ho : (wholePlaneFaceSucc W H).SameCycle
          (uibhbotWholePlaneOuterDart W) (a, true) :=
        wholePlane_missing_east_sameCycle W H hhit (uibhbotRootEdge W) a
          (hroot ▸ (hedge 0).2.2.1) ha
      obtain ⟨k, hk⟩ := hexhaust (a, true) ho
      refine ⟨k, congrArg Prod.fst hk, ?_⟩
      intro l hl
      exact hinj (hl.symm.trans (congrArg Prod.fst hk))
    · rintro ⟨k, rfl, _⟩
      exact (hedge k).2.2.1
  · exact (hmissing _).mpr (hroot ▸ (hedge 0).2.2.1)
  · rw [← hroot]
    exact Prod.ext (hedge 0).1 (by simpa using (hedge 0).2.1)
  · simp [wholePlaneWordIntegral]
  · intro t ht
    have hr := hrecord 0 t (by rw [hzero]; omega)
    omega
  · calc
      _ = ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
          (fun V : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral V t)).map
          (fun z : ℤ → ℤ × ℤ => fun n : ℕ => z n) := by
        rw [Measure.map_map (by fun_prop) measurable_wholePlaneWordIntegralPath]
        rfl
      _ = uibhbotWordFamilyLaw.map (fun w => fun n : ℕ => uibhbotConcatWalk w n) := by
        rw [uibhbotCodeLawRel_map_walk,
          Measure.map_map (by fun_prop) measurable_uibhbotConcatWalk]
        rfl
      _ = _ := uibhbotWordFamilyLaw_map_forward_path

end DirectedDistances.PaperProofs.SourceResults
