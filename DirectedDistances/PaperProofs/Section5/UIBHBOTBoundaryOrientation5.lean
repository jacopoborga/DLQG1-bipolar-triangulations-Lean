/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation4

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

local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
local notation "Q" => uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
  P hp ha F hf hFim hFa hRpos
local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa

/-! Clause map for the corrected presentation (v3 is the infinite branch of v7).

| Predicate clause | Corrected-presentation source |
| --- | --- |
| `IsBoundaryOrderOfInf` | `ae_uibhbotDefinition32ReversedPresentation_isBoundaryOrderOfInf` in Orientation4, transferred from the source presentation. |
| Exact `dartBorders` coverage by indexed darts | `uibhbotAssemblyBoundaryPresentationExternalFace3_reversedIndexedCoverage` in Orientation, using Geometry5; it assumes the corrected `IsBoundaryOrderOfInf` and returns a drawing/face witness. |
| Unbounded face and geometric external successor | `ae_uibhbotDefinition32ReversedPresentation_lowerLeft_geometryClauses` in Orientation2; Geometry3 constructs the transported face and Geometry4 projects its geometric clauses. This event has its own existential source and face witnesses. |
| Within-side successor and vertex joins | Orientation2's `lowerLeft_geometryClauses`; the missing-edge and join fields are `LLOkInf`, while its within-side face-successor equation is proved from the source-chain labels. |
| Successor totality and converse side classification | Orientation3's `ae_uibhbotDefinition32ReversedPresentation_successorClassification`; totality also follows from the corrected lower-left `next k = k - 1`. |
| Four side predicates and endpoint labels | Orientation2 proves lower-left missingness and endpoint labels. The other three sides have empty indices in Orientation; their predicates and labels reduce by empty elimination. |
| Simplicity of upper-left and lower-right | Empty-index argument as in Geometry4's `uibhbotDefinition32Presentation_emptySides_simple`; its named wrapper is for the unreversed presentation. |
| `BoundaryPositionOrder3` | `uibhbotDefinition32ReversedPresentation_positionOrder3` in Orientation3. |
| `RequiredBoundaryJoinEndpointLabels` | Vacuous for the corrected presentation: its only nonempty side has a successor at every index. |
| v7 infinite branch | The theorem below proves the corrected-presentation reduction to v3 from boundary-order infinitude; `finiteJunctions? = none` is definitional. |

Three routes to the common-witness event were checked. First, intersecting the
existing almost-sure events with `Filter.Eventually.and` does not identify
their existentially chosen `H`, drawings, edge enumeration, or transported
face; the conclusions therefore cannot be combined at one `Q`, `G'`, and `U`.
Second, the Geometry4 v7-to-v3 reduction needs v3 for the same drawing and
face, while Geometry5's exact indexed-coverage theorem returns its own
existential drawing and face. Third, transferring the old boundary-order
witness through Orientation4 succeeds for `IsBoundaryOrderOfInf`, but does
not identify the Geometry3 transported external-face darts with those same
indexed darts. Resolving that identification requires a theorem with shared
`G'` and `U`; no such conclusion is inferred here. -/

/-- Helper toward Definition 3.2: for the corrected presentation, the infinite
v7 predicate is equivalent to its v3 clause once the source-certified
boundary-order property is known. -/
theorem uibhbotDefinition32ReversedPresentation_externalFaceIntervalOrder7_iff
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj))
    {rot : Equiv.Perm ((G).GeometricEdge × Bool)}
    (G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
      (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
    (U : G'.Face)
    (S : (G).GeometricEdge × Bool → (G).GeometricEdge × Bool) :
    let Q₀ := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj
    let B : BoundaryPresentationWithJunctions M := ⟨Q₀, none⟩
    IsExternalFaceIntervalOrder7 M B G' U S ↔
      IsExternalFaceIntervalOrder3 M Q₀ G' U S := by
  let Q₀ := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj
  let B : BoundaryPresentationWithJunctions M := ⟨Q₀, none⟩
  have hidx : Q₀.lowerLeft.Index = ℤ := by
    dsimp only [Q₀, uibhbotDefinition32ReversedPresentation]
  let ray : ℕ ↪ Q₀.lowerLeft.Index :=
    ⟨fun n => cast hidx.symm (n : ℤ), by
      intro n m h
      have h' := congrArg (cast hidx) h
      have h'' : (n : ℤ) = (m : ℤ) := by simpa using h'
      exact_mod_cast h''⟩
  have hinfinite : ¬ (externalBoundaryDartSet4 M).Finite :=
    externalBoundaryDartSet4_infinite_of_lowerLeft_ray hmap ray
  change IsExternalFaceIntervalOrder7 M B G' U S ↔
    IsExternalFaceIntervalOrder3 M Q₀ G' U S
  rw [IsExternalFaceIntervalOrder7.infinite_iff hinfinite]
  simp [B]














































end
end DirectedDistances.PaperProofs.Section5
