/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinitionV2
public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

section UIBHBOTPresentation

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





noncomputable def uibhbotDefinition32Presentation
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    InfiniteBoundaryPresentation M := by
  let side : InfiniteBoundarySide (WholePlaneVertex W) (G).GeometricEdge := {
    Index := ℤ
    darts := ⟨fun k =>
      let a : (G).GeometricEdge := Quotient.mk (G).edgeSetoid (e k, true)
      (a, !a.out.2), by
        intro k j h
        have hEdge :
            (Quotient.mk (G).edgeSetoid (e k, true) : (G).GeometricEdge) =
              Quotient.mk (G).edgeSetoid (e j, true) := congrArg Prod.fst h
        rcases Quotient.exact hEdge with h | h
        · exact hinj (congrArg Prod.fst h)
        · exact hinj (congrArg Prod.fst h)⟩
    next := fun k => some (k + 1)
    initialVertex? := none
    terminalVertex? := none }
  exact {
    upperLeft := {
      Index := Empty
      darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
      next := fun i => Empty.elim i
      initialVertex? := none
      terminalVertex? := none }
    upperRight := {
      Index := Empty
      darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
      next := fun i => Empty.elim i
      initialVertex? := none
      terminalVertex? := none }
    lowerRight := {
      Index := Empty
      darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
      next := fun i => Empty.elim i
      initialVertex? := none
      terminalVertex? := none }
    lowerLeft := side }

/-- The empty UL, UR and LR sides satisfy their predicates. Helper toward
Definition 3.2. -/
theorem uibhbotDefinition32Presentation_emptySides
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    ULOkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) ∧
    UROkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) ∧
    LROkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) := by
  let Q := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj
  have : IsEmpty Q.upperLeft.Index := by
    dsimp [Q, uibhbotDefinition32Presentation]
    infer_instance
  have : IsEmpty Q.upperRight.Index := by
    dsimp [Q, uibhbotDefinition32Presentation]
    infer_instance
  have : IsEmpty Q.lowerRight.Index := by
    dsimp [Q, uibhbotDefinition32Presentation]
    infer_instance
  exact ⟨ULOkInf_of_isEmpty Q, UROkInf_of_isEmpty Q,
    LROkInf_of_isEmpty Q⟩



































end UIBHBOTPresentation

end DirectedDistances.PaperProofs.Section5

end

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

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
  (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem uibhbotDefinition32Presentation_eq :
    uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos e hinj = by
        let side : InfiniteBoundarySide (WholePlaneVertex W) (G).GeometricEdge := {
          Index := ℤ
          darts := ⟨fun k =>
            let a : (G).GeometricEdge := Quotient.mk (G).edgeSetoid (e k, true)
            (a, !a.out.2), by
              intro k j h
              have hEdge :
                  (Quotient.mk (G).edgeSetoid (e k, true) : (G).GeometricEdge) =
                    Quotient.mk (G).edgeSetoid (e j, true) := congrArg Prod.fst h
              rcases Quotient.exact hEdge with h | h
              · exact hinj (congrArg Prod.fst h)
              · exact hinj (congrArg Prod.fst h)⟩
          next := fun k => some (k + 1)
          initialVertex? := none
          terminalVertex? := none }
        exact {
          upperLeft := {
            Index := Empty
            darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
            next := fun i => Empty.elim i
            initialVertex? := none
            terminalVertex? := none }
          upperRight := {
            Index := Empty
            darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
            next := fun i => Empty.elim i
            initialVertex? := none
            terminalVertex? := none }
          lowerRight := {
            Index := Empty
            darts := ⟨fun i => Empty.elim i, by intro i; exact Empty.elim i⟩
            next := fun i => Empty.elim i
            initialVertex? := none
            terminalVertex? := none }
          lowerLeft := side } := by
  exact uibhbotDefinition32Presentation.eq_def W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj

end DirectedDistances.PaperProofs.Section5
end
