/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry4

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

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
local notation "Q" => uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
  hFim hFa hRpos

/-- Helper toward Definition 3.2: the external-frontier geometric edges are
exactly those selected by the indexed presentation darts, assuming the
source-certified boundary-order enumeration. -/
theorem uibhbotDefinition32Presentation_externalFrontierEdge_iff_dartEdgeEnumerated
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj))
    (a : (G).GeometricEdge) :
    ExternalFrontierEdge M a ↔
      ∃ i : InfiniteBoundaryDartIndex (Q e hinj),
        (InfiniteBoundaryDartIndex.dart (Q e hinj) i).1 = a := by
  exact ((IsBoundaryOrderOfInf_iff (Q e hinj)).mp hmap).1 a |>.symm

/-- Helper toward Definition 3.2: membership in the map's external dart set
is equivalent to the edge coordinate being enumerated by the presentation.
The set records both traversal bits for each external geometric edge. -/
theorem uibhbotDefinition32Presentation_externalBoundaryDartSet4_iff_dartEdgeEnumerated
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj))
    (d : (G).GeometricEdge × Bool) :
    d ∈ externalBoundaryDartSet4 M ↔
      ∃ i : InfiniteBoundaryDartIndex (Q e hinj),
        (InfiniteBoundaryDartIndex.dart (Q e hinj) i).1 = d.1 := by
  change ExternalFrontierEdge M d.1 ↔ _
  exact uibhbotDefinition32Presentation_externalFrontierEdge_iff_dartEdgeEnumerated
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap d.1

/-- Helper toward Definition 3.2: the external face of the transported
assembly drawing is bordered exactly by the representative-adjusted darts
selected by the integer-indexed lower-left presentation side. The reversal
matches that side's traversal marker convention. -/
theorem uibhbotAssemblyBoundaryPresentationExternalFace3_indexedDartCoverage
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj)) :
    ∃ G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
        (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      ∃ U : G'.Face,
        ∀ d, G'.dartBorders d U ↔
          ∃ k : ℤ,
            d = uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
              (e k, true) := by
  obtain ⟨G', U, _hunique, _hunbounded, hborder, _hsucc⟩ :=
    uibhbotAssemblyBoundaryPresentationExternalFace3
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  let qedge (k : ℤ) : (G).GeometricEdge :=
    Quotient.mk (G).edgeSetoid (e k, true)
  have hrange := uibhbotDefinition32Presentation_dartEdge_range
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  refine ⟨G', U, ?_⟩
  intro d
  rw [hborder]
  constructor
  · rintro ⟨hdirection, hmissing⟩
    have hsource : φ.symm d = ((φ.symm d).1, true) :=
      Prod.ext rfl hdirection
    have hd : d = φ ((φ.symm d).1, true) := by
      calc
        d = φ (φ.symm d) := (φ.apply_symm_apply d).symm
        _ = φ ((φ.symm d).1, true) := congrArg φ hsource
    have hquot : Quotient.mk (G).edgeSetoid (φ.symm d) = d.1 :=
      congrArg Prod.fst (φ.apply_symm_apply d)
    have hmissingMap : (M).toPlaneMapWithMissing.missing d.1 := by
      rw [← hquot, uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk]
      exact hmissing
    have hfrontier : ExternalFrontierEdge M d.1 :=
      (uibhbotAssembly_externalFrontierEdge_iff_missing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d.1).2 hmissingMap
    obtain ⟨i, hi⟩ :=
      (uibhbotDefinition32Presentation_externalFrontierEdge_iff_dartEdgeEnumerated
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap d.1).mp hfrontier
    obtain ⟨k, hk⟩ := hrange d.1 |>.mp ⟨i, hi⟩
    have hedge : (φ.symm d).1 = e k := by
      have hquotEq : Quotient.mk (G).edgeSetoid (φ.symm d) =
          Quotient.mk (G).edgeSetoid (e k, true) := hquot.trans hk
      rcases Quotient.exact hquotEq with h | h
      · exact congrArg Prod.fst h
      · exact congrArg Prod.fst h
    refine ⟨k, ?_⟩
    rw [hd]
    exact congrArg φ (Prod.ext hedge rfl)
  · rintro ⟨k, rfl⟩
    have hlisted := hrange (qedge k) |>.mpr ⟨k, rfl⟩
    have hfrontier : ExternalFrontierEdge M (qedge k) :=
      (uibhbotDefinition32Presentation_externalFrontierEdge_iff_dartEdgeEnumerated
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap
        (qedge k)).2 hlisted
    have hmissing := (uibhbotAssembly_externalFrontierEdge_iff_missing
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      (qedge k)).mp hfrontier
    have hmissingSource : ¬ wholePlaneEdgePresent W (e k) := by
      have hmissing' : (M).toPlaneMapWithMissing.missing
          (Quotient.mk (G).edgeSetoid (e k, true)) := by
        change (M).toPlaneMapWithMissing.missing (qedge k)
        exact hmissing
      have hiff : (M).toPlaneMapWithMissing.missing
          (Quotient.mk (G).edgeSetoid (e k, true)) ↔
            ¬ wholePlaneEdgePresent W (e k) := by
        simpa using uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)
      exact hiff.mp hmissing'
    let dsrc : WholePlaneDart W := (e k, true)
    change (φ.symm (φ dsrc)).2 = true ∧
      ¬ wholePlaneEdgePresent W (φ.symm (φ dsrc)).1
    rw [φ.symm_apply_apply]
    exact ⟨rfl, hmissingSource⟩

/-- Helper toward Definition 3.2: the indexed oriented darts of the UIBHBOT
presentation are injective, by injectivity of their edge coordinates. -/
theorem uibhbotDefinition32Presentation_dartIndex_injective
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    Function.Injective (InfiniteBoundaryDartIndex.dart (Q e hinj)) := by
  have hedge := uibhbotDefinition32Presentation_dartEdge_injective
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  intro i j hij
  exact hedge (congrArg Prod.fst hij)























































































end
end DirectedDistances.PaperProofs.Section5

end
