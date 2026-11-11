/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation4
public import DirectedDistances.PlanarMap.GeneralPlaneMapExternalBoundary

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open scoped Classical

section Assembly

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

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: a whole-arc external-frontier witness for
an assembly edge yields a bordering dart of the same edge and an unbounded
face of the PL assembly drawing. -/
theorem uibhbotAssembly_externalFrontierEdge_has_borderingDart
    (a : (G).GeometricEdge) (hfront : ExternalFrontierEdge M a) :
    ∃ K : (G).Face, (G).IsUnbounded K ∧
      ∃ d : WholePlaneDart W, d.1 = a.out.1 ∧ (G).dartBorders d K := by
  rcases (externalFrontierEdge_iff M a).mp hfront with ⟨K, hK, harc⟩
  have hK' : (G).IsUnbounded ((G).toPlaneGraphDrawingFaceEquiv K) :=
    ((G).toPlaneGraphDrawing_isExternal_iff K).mp hK
  have hopen : (G).toPlaneGraphDrawing.openArc a ⊆
      closure K.val := by
    intro z hz
    change z ∈ (M).toPlaneGraphDrawing.arc a '' openParams at hz
    rcases hz with ⟨t, ht, rfl⟩
    apply frontier_subset_closure
    apply harc
    exact ⟨t, rfl⟩
  have hb := (G).bordering_dart_of_openArc_subset_closure
    (uibhbot_faceOrbit_dartVertex_surjective W H) a
    K hopen
  rcases hb with hb | hb
  · exact ⟨_, hK', a.out, rfl, hb⟩
  · exact ⟨_, hK', wholePlaneDartFlip W a.out, rfl, hb⟩

/-- Helper toward Definition 3.2: a present assembly edge is not an
ExternalFrontierEdge. -/
theorem uibhbotDefinition32Presentation_presentEdge_not_externalFrontier
    (a : (G).GeometricEdge) (hpresent : wholePlaneEdgePresent W a.out.1) :
    ¬ ExternalFrontierEdge M a := by
  intro hfront
  obtain ⟨K, hK, d, hd, hborder⟩ :=
    uibhbotAssembly_externalFrontierEdge_has_borderingDart
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a hfront
  have hmissing := (uibhbot_assembly_unbounded_dartBorders_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K hK d).mp hborder
  exact hmissing.2 (hd ▸ hpresent)


/-- Helper toward Definition 3.2: every edge in the specified missing chain
lies on the frontier of an external assembly face. -/
theorem uibhbotDefinition32Presentation_missingChainEdge_externalFrontier
    (e : ℤ → WholePlaneEdge W) (_hinj : Function.Injective e)
    (_hwest : ∀ k, wholePlaneEdgeWest W (e k) =
      (uibhbotBusemannSource k W).id)
    (_heast : ∀ k, wholePlaneEdgeEast W (e k) =
      (uibhbotBusemannSource (k + 1) W).id)
    (hmissing : ∀ k, ¬ wholePlaneEdgePresent W (e k)) :
    ∀ k : ℤ, ExternalFrontierEdge M
      (Quotient.mk (G).edgeSetoid (e k, true)) := by
  intro k
  let a : (G).GeometricEdge := Quotient.mk (G).edgeSetoid (e k, true)
  have hmiss : (M).missing a := by
    rw [uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)]
    exact hmissing k
  obtain ⟨K, hK, hclosure⟩ := (M).toPlaneMapWithMissing.missing_on_external a hmiss
  apply (externalFrontierEdge_iff M a).mpr
  refine ⟨K, hK, ?_⟩
  exact (PlaneGraphDrawing.range_subset_closure_iff_frontier_of_face_complement
    (M).toPlaneGraphDrawing K a).mp hclosure


/-- Helper toward Definition 3.2: the external-frontier edges of the
assembly drawing are exactly its missing geometric edges. -/
theorem uibhbotAssembly_externalFrontierEdge_iff_missing
    (a : (G).GeometricEdge) : ExternalFrontierEdge M a ↔ (M).missing a := by
  constructor
  · intro hfront
    obtain ⟨K, hK, d, hd, hborder⟩ :=
      uibhbotAssembly_externalFrontierEdge_has_borderingDart
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a hfront
    have hmissing := (uibhbot_assembly_unbounded_dartBorders_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K hK d).mp hborder
    change ¬ wholePlaneEdgePresent W a.out.1
    rw [← hd]
    exact hmissing.2
  · intro hmissing
    obtain ⟨K, hK, hclosure⟩ :=
      (M).toPlaneMapWithMissing.missing_on_external a hmissing
    apply (externalFrontierEdge_iff M a).mpr
    exact ⟨K, hK,
      (PlaneGraphDrawing.range_subset_closure_iff_frontier_of_face_complement
        (M).toPlaneGraphDrawing K a).mp hclosure⟩











































end Assembly

end DirectedDistances.PaperProofs.Section5


end
