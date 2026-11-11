/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the constructed lower-left family consists
of missing edges whose successive darts join in traversal order. -/
theorem uibhbotDefinition32Presentation_lowerLeft_ok
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
      h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hwest : ∀ k, wholePlaneEdgeWest W (e k) =
      (uibhbotBusemannSource k W).id)
    (heast : ∀ k, wholePlaneEdgeEast W (e k) =
      (uibhbotBusemannSource (k + 1) W).id)
    (hmissing : ∀ k, ¬ wholePlaneEdgePresent W (e k)) :
    LLOkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) := by
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj]
  rw [LLOkInf_iff]
  change (∀ k : ℤ, M.missing (Quotient.mk G.edgeSetoid (e k, true))) ∧
    ∀ k j : ℤ, (some (k + 1) : Option ℤ) = some j →
      boundaryDartTerminal M
          (Quotient.mk G.edgeSetoid (e k, true),
            !(Quotient.mk G.edgeSetoid (e k, true)).out.2) =
        boundaryDartInitial M
          (Quotient.mk G.edgeSetoid (e j, true),
            !(Quotient.mk G.edgeSetoid (e j, true)).out.2)
  constructor
  · intro k
    let d : WholePlaneDart W := (e k, true)
    have hmiss : M.missing (Quotient.mk G.edgeSetoid d) ↔
        ¬ wholePlaneEdgePresent W (e k) := by
      simpa [d] using
        (uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d)
    rw [hmiss]
    exact hmissing k
  · intro k j hj
    have hj' : j = k + 1 := (Option.some.inj hj).symm
    subst j
    have hterm (k : ℤ) :
        boundaryDartTerminal M
          (Quotient.mk G.edgeSetoid (e k, true),
            !(Quotient.mk G.edgeSetoid (e k, true)).out.2) =
          wholePlaneEdgeEast W (e k) := by
      rcases G.geometricEdge_out_mk (e k, true) with hout | hout
      · rw [boundaryDartTerminal_eq]
        dsimp [M, uibhbotAssemblyDirectedPlaneMapWithMissing,
          PLDrawing.toPlaneGraphDrawing]
        rw [hout]
        simp [wholePlaneDartVertex]
      · have hflip : wholePlaneDartFlip W (e k, true) = (e k, false) := rfl
        rw [boundaryDartTerminal_eq]
        dsimp [M, uibhbotAssemblyDirectedPlaneMapWithMissing,
          PLDrawing.toPlaneGraphDrawing]
        rw [hout, hflip]
        have hflip2 : wholePlaneDartFlip W (e k, false) = (e k, true) := rfl
        rw [hflip2]
        simp [wholePlaneDartVertex]
    have hinit (k : ℤ) :
        boundaryDartInitial M
          (Quotient.mk G.edgeSetoid (e k, true),
            !(Quotient.mk G.edgeSetoid (e k, true)).out.2) =
          wholePlaneEdgeWest W (e k) := by
      rcases G.geometricEdge_out_mk (e k, true) with hout | hout
      · have hflip : wholePlaneDartFlip W (e k, true) = (e k, false) := rfl
        rw [boundaryDartInitial_eq]
        dsimp [M, uibhbotAssemblyDirectedPlaneMapWithMissing,
          PLDrawing.toPlaneGraphDrawing]
        rw [hout, hflip]
        simp [wholePlaneDartVertex]
      · have hflip : wholePlaneDartFlip W (e k, true) = (e k, false) := rfl
        rw [boundaryDartInitial_eq]
        dsimp [M, uibhbotAssemblyDirectedPlaneMapWithMissing,
          PLDrawing.toPlaneGraphDrawing]
        rw [hout, hflip]
        simp [wholePlaneDartVertex]
    calc
      boundaryDartTerminal M
          (Quotient.mk G.edgeSetoid (e k, true),
            !(Quotient.mk G.edgeSetoid (e k, true)).out.2) =
          wholePlaneEdgeEast W (e k) := hterm k
      _ = (uibhbotBusemannSource (k + 1) W).id := heast k
      _ = wholePlaneEdgeWest W (e (k + 1)) := (hwest (k + 1)).symm
      _ = boundaryDartInitial M
          (Quotient.mk G.edgeSetoid (e (k + 1), true),
            !(Quotient.mk G.edgeSetoid (e (k + 1), true)).out.2) := (hinit (k + 1)).symm









































end DirectedDistances.PaperProofs.Section5

end
