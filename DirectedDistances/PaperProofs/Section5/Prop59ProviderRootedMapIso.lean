/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinitionV2
public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence
public import DirectedDistances.PlanarMap.D39RootedMapQuotient

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.9. On the conull event, the code-selected
rooted planar map has exactly the whole-plane rotation system and canonical
missing root dart supplied by its source construction. -/
theorem uibhbotRootedPlanarMapOfCode_wholePlaneMap_on_event
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent) :
    ∃ (H : WholePlaneRotationHypothesis W)
      (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
      Nonempty (D39RootedMapIso
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
        ((uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
      ((uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap).toRootedLocallyFiniteMap).frameEdgeDart =
          uibhbotWholePlaneFrameEdgeDart W := by
  obtain ⟨H, hhit, C₀, hcap, hEq⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hW).1
  have hD39 :
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap =
        (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap).toRootedLocallyFiniteMap.toD39RootedMap :=
    congrArg (fun M : RootedLocallyFinitePlanarMap =>
      M.toRootedLocallyFiniteMap.toD39RootedMap) hEq
  refine ⟨H, hhit, C₀, hcap, ?_, rfl⟩
  rw [hD39]
  exact ⟨D39RootedMapIso.refl _⟩

/-- Helper toward Proposition 5.9. The source ordered-root convention identifies
the provider's zeroth edge with the west-side dart of the code root edge. -/
theorem uibhbotWholePlaneFrameEdgeDart_eq_provider_root
    (W : ℤ → Fin 3) (e : ℤ → WholePlaneEdge W)
    (he : e 0 = uibhbotRootEdge W) :
    uibhbotWholePlaneFrameEdgeDart W = (e 0, false) := by
  rw [uibhbotWholePlaneFrameEdgeDart, uibhbotWholePlaneRootDart, he]

/-- Helper toward Proposition 5.9. The code-selected local topology rooted map is
isomorphic to the combinatorial whole-plane rotation system built with any
provider rotation witness, while retaining the canonical ordered root dart. -/
theorem uibhbotRootedPlanarMapOfCode_d39_iso_for_provider_rotation
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (e : ℤ → WholePlaneEdge W)
    (he : e 0 = uibhbotRootEdge W) :
    Nonempty (D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
    uibhbotWholePlaneFrameEdgeDart W = (e 0, false) := by
  obtain ⟨Hc, hhitc, Cc, hcapc, hEq⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hW).1
  have hH : Hc = H := Subsingleton.elim _ _
  constructor
  ·
    have hD39 :
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap =
          (uibhbotRootedLocallyFinitePlanarMap W Hc hhitc Cc hcapc).toRootedLocallyFiniteMap.toD39RootedMap :=
      congrArg (fun M : RootedLocallyFinitePlanarMap =>
        M.toRootedLocallyFiniteMap.toD39RootedMap) hEq
    rw [hD39]
    refine ⟨{
      toEquiv := Equiv.refl _
      rot_comm := ?_
      edgeInv_comm := by intro d; rfl
      missing_iff := by intro d; exact Iff.rfl
      tail_iff := by intro d hd; exact Iff.rfl
      root_dart_comm := rfl }⟩
    intro d
    change wholePlaneRotation W H d = wholePlaneRotation W Hc d
    rw [hH]
  · exact uibhbotWholePlaneFrameEdgeDart_eq_provider_root W e he

/-- Helper toward Proposition 5.9. The geometric assembly's cyclic successor
is the whole-plane combinatorial rotation at every dart. -/
theorem uibhbotCcw_assembly_rotation_d39
    (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
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
    (d : WholePlaneDart W) :
    CcwSuccessor
      {E | wholePlaneDartVertex W E = wholePlaneDartVertex W d}
      (fun E => ((uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        ).arc E).initialDirection)
      d (wholePlaneRotation W H d) :=
  uibhbotCcw_assembly_rotation W H h0 hL hR hfin P hp ha F hf hFim hFa d

/-- Helper toward Proposition 5.9. The assembly's geometric face-orbit map
identifies the combinatorial face orbit of each dart with exactly its bordering
geometric face. -/
theorem uibhbotAssembly_faceOrbitEquiv_dartBorders
    (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
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
    (d : WholePlaneDart W)
    (K : (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).Face) :
    uibhbot_assembly_faceOrbitEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        (Quotient.mk _ d) = K ↔
      (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).dartBorders d K :=
  uibhbot_assembly_faceOrbitEquiv_mk_eq_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K

/-- Helper toward Proposition 5.9. The provider's geometric assembly induces
the same combinatorial local topology rooted map as the code-selected source map: the
rotation, edge tags, present-edge direction, face orbits, and ordered root all
agree on the shared whole-plane dart carrier. -/
theorem uibhbotProviderAssemblyD39_identification
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (H : WholePlaneRotationHypothesis W)
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
    (e : ℤ → WholePlaneEdge W)
    (he : e 0 = uibhbotRootEdge W) :
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0),
    let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
    let M := uibhbotAssemblyDirectedPlaneMapWithMissing
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
    Nonempty (D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
    (∀ d : WholePlaneDart W, CcwSuccessor
      {E | wholePlaneDartVertex W E = wholePlaneDartVertex W d}
      (fun E => (G.arc E).initialDirection) d (wholePlaneRotation W H d)) ∧
    (∀ d : WholePlaneDart W,
      M.missing (Quotient.mk G.edgeSetoid d) ↔ ¬ wholePlaneEdgePresent W d.1) ∧
    (∀ a : {a : G.GeometricEdge // ¬ M.missing a},
      M.forward a = !a.val.out.2) ∧
    (∀ d : WholePlaneDart W, ∀ K : G.Face,
      uibhbot_assembly_faceOrbitEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
          (Quotient.mk _ d) = K ↔ G.dartBorders d K) ∧
    uibhbotWholePlaneFrameEdgeDart W = (e 0, false) := by
  obtain ⟨_, hhit, C₀, _, _⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hW).1
  refine ⟨hhit, C₀, ?_⟩
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨(uibhbotRootedPlanarMapOfCode_d39_iso_for_provider_rotation
    W hW H hhit C₀ e he).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact uibhbotCcw_assembly_rotation_d39
      W H h0 hL hR hfin P hp ha F hf hFim hFa d
  · intro d
    exact uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d
  · intro a
    exact uibhbotAssemblyDirectedPlaneMapWithMissing_forward
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a
  · intro d K
    exact uibhbotAssembly_faceOrbitEquiv_dartBorders
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K
  · exact uibhbotWholePlaneFrameEdgeDart_eq_provider_root W e he

end DirectedDistances.PaperProofs.Section5
