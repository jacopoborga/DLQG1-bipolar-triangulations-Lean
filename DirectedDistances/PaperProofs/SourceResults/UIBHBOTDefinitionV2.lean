/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinition
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceNeighborhood
public import DirectedDistances.PlanarMap.FaceDegreeFiniteSupport
public import DirectedDistances.RandomWalk.UIBHBOTConditionedRenewalSum
















public section

namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section5
open scoped Classical

/-- Helper toward Definition 5.8: for every choice of the exact assembly witnesses, an
internal face whose face-successor orbit is a created triangle has general-carrier face
degree three. Deterministic; the triangle hypothesis is the v1 provider's orbit clause. -/
theorem uibhbotAssembly_faceDegree_eq_three_of_triangle
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
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
    (K : (uibhbotAssemblyDirectedPlaneMapWithMissing
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos).toPlaneGraphDrawing.Face)
    (N : ℕ) (j : TriangleCreationTime (shiftedStream W N))
    (hdarts : {d : WholePlaneDart W |
        uibhbot_assembly_faceOrbitEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
          (Quotient.mk _ d) =
        (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
          ).toPlaneGraphDrawingFaceEquiv K} =
      wholePlaneDartι W N '' {a | a ∈ stageTriangleDartList (shiftedStream W N) j}) :
    (uibhbotAssemblyDirectedPlaneMapWithMissing
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos).toPlaneGraphDrawing.faceDegree K = 3 := by
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let E := uibhbot_assembly_faceOrbitEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let t := stageTriangleDartTriple (shiftedStream W N) j
  let raw : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  let darts : Fin 3 → WholePlaneDart W := fun i => wholePlaneDartι W N (raw i)
  let edges : Fin 3 → G.GeometricEdge := fun i => Quotient.mk G.edgeSetoid (darts i)
  have hinj : Function.Injective edges := by
    have hc : (Finset.univ.image edges).card = (Finset.univ : Finset (Fin 3)).card := by
      simpa only [edges, darts, raw, t, Finset.card_univ, Fintype.card_fin] using
        wholePlane_stageTriangle_geometricEdges_card W H G N j
    have hi := Finset.card_image_iff.mp hc
    intro i k hik
    exact hi (Finset.mem_univ i) (Finset.mem_univ k) hik
  let K' := G.toPlaneGraphDrawingFaceEquiv K
  have hb (a : WholePlaneDart W) : G.dartBorders a K' ↔ ∃ i : Fin 3, darts i = a := by
    have ho : G.dartBorders a K' ↔ a ∈ {d : WholePlaneDart W |
        E (Quotient.mk _ d) = K'} :=
      (uibhbot_assembly_faceOrbitEquiv_mk_eq_iff
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a K').symm
    rw [ho, hdarts]
    constructor
    · rintro ⟨b, hb, rfl⟩
      change b ∈ [t.1, t.2.1, t.2.2] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨raw i, ?_, rfl⟩
      fin_cases i <;> simp [raw, t, stageTriangleDartList]
  have hmult (e : G.GeometricEdge) :
      (uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos).toPlaneGraphDrawing.faceMult e K =
      if ∃ i : Fin 3, edges i = e then (1 : ℕ∞) else 0 := by
    have hc : (∃ i : Fin 3, edges i = e) ↔
        G.dartBorders e.out K' ∨ G.dartBorders (wholePlaneDartFlip W e.out) K' := by
      constructor
      · rintro ⟨i, hie⟩
        have hrel : darts i = e.out ∨ darts i = wholePlaneDartFlip W e.out :=
          Quotient.exact (hie.trans (Quotient.out_eq e).symm)
        have hbi := (hb (darts i)).mpr ⟨i, rfl⟩
        rcases hrel with he | he
        · exact Or.inl (he ▸ hbi)
        · exact Or.inr (he ▸ hbi)
      · rintro (he | he)
        · obtain ⟨i, hi⟩ := (hb e.out).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans (Quotient.out_eq e)⟩
        · obtain ⟨i, hi⟩ := (hb (wholePlaneDartFlip W e.out)).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans
            ((G.geometricEdge_flip e.out).trans (Quotient.out_eq e))⟩
    have hn : ¬ (G.dartBorders e.out K' ∧
        G.dartBorders (wholePlaneDartFlip W e.out) K') := by
      rintro ⟨hl, hr⟩
      obtain ⟨i, hi⟩ := (hb e.out).mp hl
      obtain ⟨k, hk⟩ := (hb (wholePlaneDartFlip W e.out)).mp hr
      have heq : edges i = edges k := by
        change Quotient.mk G.edgeSetoid (darts i) = Quotient.mk G.edgeSetoid (darts k)
        rw [hi, hk, G.geometricEdge_flip]
      have hik := hinj heq
      have hd : e.out = wholePlaneDartFlip W e.out := hi.symm.trans (hik ▸ hk)
      exact G.flip_ne e.out hd.symm
    rw [uibhbotAssembly_faceMult_eq_bordering_dart_count
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K e]
    change (if G.dartBorders e.out K' then (1 : ℕ∞) else 0) +
      (if G.dartBorders (wholePlaneDartFlip W e.out) K' then (1 : ℕ∞) else 0) = _
    by_cases hl : G.dartBorders e.out K'
    · have hr : ¬ G.dartBorders (wholePlaneDartFlip W e.out) K' := fun hr => hn ⟨hl, hr⟩
      have he := hc.mpr (Or.inl hl)
      simp only [hl, hr, he, ite_true, ite_false, add_zero]
    · by_cases hr : G.dartBorders (wholePlaneDartFlip W e.out) K'
      · have he := hc.mpr (Or.inr hr)
        simp only [hl, hr, he, ite_true, ite_false, zero_add]
      · have he : ¬ ∃ i : Fin 3, edges i = e := fun he => (hc.mp he).elim hl hr
        simp only [hl, hr, he, ite_false, zero_add]
  exact PlaneGraphDrawing.faceDegree_eq_three_of_injective _ K edges hinj hmult













theorem def_uibhbot_provider_v2 :
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
      (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsInternal K →
        M.toPlaneGraphDrawing.faceDegree K = 3) ∧
      uibhbotWordFamilyLaw.map
          (fun w : ℤ → List (Fin 3) => fun n : ℕ =>
            uibhbotConcatWalk w (-(n : ℤ))) =
        (rConditionedPathLaw 0 0).map
          (fun p : ℕ → ℤ × ℤ => fun n : ℕ =>
            if n = 0 then (0, 0) else (p (n - 1)).swap + (1, 0)) ∧
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
  filter_upwards [def_uibhbot_provider] with W hW
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hW⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, h6, hrest⟩ := hW
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    h1, h2, h3, h4, h5, h6, ?_, uibhbot_negative_pathLaw_eq_rConditioned, hrest⟩
  intro K hK
  obtain ⟨N, j, hset, _⟩ := h6 K hK
  exact uibhbotAssembly_faceDegree_eq_three_of_triangle
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K N j hset

end DirectedDistances.PaperProofs.SourceResults
