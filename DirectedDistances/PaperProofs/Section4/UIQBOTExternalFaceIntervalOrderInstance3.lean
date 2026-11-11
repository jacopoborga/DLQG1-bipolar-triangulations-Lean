/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance2
import all DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

/-! # Labeled UIQBOT external-face interval-order instance, continued

constructed quotient drawing without adding geometric or interval-order
premises. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: the external-face darts of the constructed
quotient drawing are exactly those enumerated by the labeled presentation. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_externalFaceCoverage
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∃ (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
        ℕ (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face),
      G.IsUnbounded U ∧
        (∀ d, G.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex P,
            InfiniteBoundaryDartIndex.dart P i = d) := by
  dsimp only
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, U, hUnbounded, hBorder, _hSucc⟩ :=
    uiqbotCanonicalQuotientDrawing_externalFace w hfin htrans hR hL0
  refine ⟨G, U, hUnbounded, ?_⟩
  intro d
  rw [hBorder d]
  simpa only [uiqbotCanonicalBoundaryDartEquiv, Equiv.symm_symm] using
    (uiqbotCanonicalBoundaryPresentationLabeledX_externalDartCoverage
      w hfin htrans hR hL0 d)



























































end DirectedDistances.PaperProofs.Section4

end
