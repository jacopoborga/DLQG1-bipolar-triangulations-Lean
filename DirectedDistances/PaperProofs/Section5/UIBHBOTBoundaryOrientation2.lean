/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation

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

/-- Helper toward Definition 3.2: the corrected lower-left side satisfies
the endpoint-label predicate; its optional endpoint labels are both absent. -/
theorem uibhbotDefinition32ReversedPresentation_lowerLeft_endpointLabels
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    BoundarySideEndpointLabels
      (uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
      (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
        hFim hFa hRpos e hinj).lowerLeft := by
  simp [BoundarySideEndpointLabels, uibhbotDefinition32ReversedPresentation]

/-- Helper toward Definition 3.2: almost surely the corrected lower-left
side consists of missing edges, joins in its reversed integer order, and its
listed darts follow the transported external-face successor. The edge-chain
labels are taken from the existing source event, not added as hypotheses. -/
theorem ae_uibhbotDefinition32ReversedPresentation_lowerLeft_geometryClauses :
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
          (shiftedStream W 0) h0 (H.1 0) ''
          ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e),
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let G := uibhbotCcw_assemblyDrawing
          W H h0 hL hR hfin P hp ha F hf hFim hFa
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        LLOkInf Q ∧
        BoundarySideEndpointLabels M Q.lowerLeft ∧
        ∃ G' : PLDrawing (G.GeometricEdge × Bool) (WholePlaneVertex W)
            (fun d => (d.1, !d.2))
            (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
            (boundaryDartInitial M),
          ∃ U : G'.Face,
            IsGeometricExternalFaceSucc G' U
              (fun d =>
                uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                  (wholePlaneFaceSucc W H
                    ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d))) ∧
            (∀ i j : InfiniteBoundaryDartIndex Q,
              sideNext Q i = some j →
                (fun d =>
                  uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                    (wholePlaneFaceSucc W H
                      ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d)))
                    (InfiniteBoundaryDartIndex.dart Q i) =
                  InfiniteBoundaryDartIndex.dart Q j) := by
  filter_upwards [ae_uibhbotDefinition32Presentation_isBoundaryOrderOfInf]
    with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, hmap⟩
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos e hinj
  let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  have hwest (k : ℤ) := (hsource k).1
  have heast (k : ℤ) := (hsource k).2.1
  have hmissing (k : ℤ) := (hsource k).2.2
  have hll : LLOkInf Q := by
    rw [LLOkInf_iff]
    constructor
    · intro k
      change M.toPlaneMapWithMissing.missing (Q.lowerLeft.darts k).1
      rw [uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj k]
      have hm : M.toPlaneMapWithMissing.missing
          (Quotient.mk G.edgeSetoid (e k, true)) := by
        exact (uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)).2
            (hmissing k)
      have hedg : (φ (e k, true)).1 = Quotient.mk G.edgeSetoid (e k, true) := by
        change (uibhbotAssemblyBoundaryDartEquiv3
          W H h0 hL hR hfin P hp ha F hf hFim hFa (e k, true)).1 = _
        rfl
      rw [hedg]
      exact hm
    · intro i j hnext
      change ℤ at i
      change ℤ at j
      have hidx : j = i - 1 := by
        have hnext' : (some (i - 1) : Option ℤ) = some j := by
          simpa [Q, uibhbotDefinition32ReversedPresentation] using hnext
        exact (Option.some.inj hnext').symm
      subst j
      have hflip (k : ℤ) :
          ((φ (e k, true)).1, !(φ (e k, true)).2) = φ (e k, false) := by
        exact (uibhbotAssemblyBoundaryDartEquiv3_flip
          W H h0 hL hR hfin P hp ha F hf hFim hFa (e k, true)).symm
      have hterminalInitial (d : (G).GeometricEdge × Bool) :
          boundaryDartTerminal M d = boundaryDartInitial M (d.1, !d.2) := by
        rcases d with ⟨a, b⟩
        cases b <;> rw [boundaryDartTerminal_eq, boundaryDartInitial_eq] <;> rfl
      have hterm (k : ℤ) :
          boundaryDartTerminal M (φ (e k, true)) = wholePlaneEdgeWest W (e k) := by
        calc
          boundaryDartTerminal M (φ (e k, true)) =
              boundaryDartInitial M
                ((φ (e k, true)).1, !(φ (e k, true)).2) := hterminalInitial _
          _ = boundaryDartInitial M (φ (e k, false)) := by rw [hflip k]
          _ = wholePlaneDartVertex W (e k, false) :=
            uibhbotAssemblyBoundaryDartEquiv3_initialVertex
              W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, false)
          _ = wholePlaneEdgeWest W (e k) := rfl
      have hinit (k : ℤ) :
          boundaryDartInitial M (φ (e k, true)) = wholePlaneEdgeEast W (e k) := by
        rw [uibhbotAssemblyBoundaryDartEquiv3_initialVertex
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)]
        rfl
      rw [uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj i,
        uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj (i - 1)]
      calc
        boundaryDartTerminal M (φ (e i, true)) = wholePlaneEdgeWest W (e i) := hterm i
        _ = (uibhbotBusemannSource i W).id := hwest i
        _ = (uibhbotBusemannSource ((i - 1) + 1) W).id := by
          congr 2
          omega
        _ = wholePlaneEdgeEast W (e (i - 1)) := (heast (i - 1)).symm
        _ = boundaryDartInitial M (φ (e (i - 1), true)) := (hinit (i - 1)).symm
  have hlabels : BoundarySideEndpointLabels M Q.lowerLeft := by
    exact uibhbotDefinition32ReversedPresentation_lowerLeft_endpointLabels
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  have hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N) := fun N =>
    boundaryHitWitnesses_of_le W (Nat.zero_le N) h0
  obtain ⟨G', U, _hunique, _hunbounded, _hborder, hsucc⟩ :=
    uibhbotAssemblyBoundaryPresentationExternalFace3
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hwithin : ∀ i j : InfiniteBoundaryDartIndex Q,
      sideNext Q i = some j →
        (fun d => φ (wholePlaneFaceSucc W H (φ.symm d)))
          (InfiniteBoundaryDartIndex.dart Q i) =
        InfiniteBoundaryDartIndex.dart Q j := by
    intro i j hnext
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at k
        change ℤ at l
        have hnext' : (some (k - 1) : Option ℤ) = some l := by
          simpa [sideNext, Q, uibhbotDefinition32ReversedPresentation] using hnext
        have hidx : l = k - 1 := (Option.some.inj hnext').symm
        subst l
        simp only [InfiniteBoundaryDartIndex.dart_eq]
        rw [uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj k,
          uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
            W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj (k - 1)]
        let dk : WholePlaneDart W := (e k, true)
        let dnext : WholePlaneDart W := (e (k - 1), true)
        change φ (wholePlaneFaceSucc W H (φ.symm (φ dk))) = φ dnext
        rw [φ.symm_apply_apply]
        have hface := uibhbotSourceChainEastDart_faceSucc
          W H hhit e hwest heast hmissing k
        have hface' : wholePlaneFaceSucc W H dk = dnext := by
          simpa [dk, dnext] using hface
        rw [hface']
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hll, hlabels, G', U, ?_, hwithin⟩
  simpa [φ] using hsucc

end
end DirectedDistances.PaperProofs.Section5

end
