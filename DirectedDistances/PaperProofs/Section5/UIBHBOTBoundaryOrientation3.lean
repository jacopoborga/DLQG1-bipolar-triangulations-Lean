/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation2

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

/-- Helper toward Definition 3.2: the corrected lower-left presentation has
integer position `-k`, so its successor in decreasing index order advances
one unit in boundary position and its full position map is gapless. -/
theorem uibhbotDefinition32ReversedPresentation_positionOrder3
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    BoundaryPositionOrder3
      (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
        hFim hFa hRpos e hinj) := by
  let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj
  let position : InfiniteBoundaryDartIndex Q → ℤ := fun i =>
    match i with
    | .upperLeft i => Empty.elim i
    | .upperRight i => Empty.elim i
    | .lowerRight i => Empty.elim i
    | .lowerLeft k => by
        change ℤ at k
        exact -k
  refine ⟨position, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at l
        change -k = -l at hij
        have hkl : k = l := by omega
        subst l
        rfl
  · intro i j htag
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at l
        change 3 = 3 at htag
        constructor
        · intro h
          have h' : (some (k - 1) : Option ℤ) = some l := by
            simpa [sideNext, uibhbotDefinition32ReversedPresentation] using h
          have hkl : l = k - 1 := (Option.some.inj h').symm
          change -l = -k + 1
          omega
        · intro h
          change -l = -k + 1 at h
          have hkl : l = k - 1 := by omega
          simpa [sideNext, uibhbotDefinition32ReversedPresentation] using
            congrArg (fun n : ℤ => some n) hkl.symm
  · intro i j z hiz hzj
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at l
        change -k ≤ z at hiz
        change z ≤ -l at hzj
        refine ⟨InfiniteBoundaryDartIndex.lowerLeft (-z), ?_⟩
        change -(-z) = z
        omega
  · intro i j k hij hjk htag
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft i =>
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft j =>
        cases k with
        | upperLeft k => cases k
        | upperRight k => cases k
        | lowerRight k => cases k
        | lowerLeft k => rfl
  · intro i j k hij hjk htag₁ htag₂ htag₃
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft i =>
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft j =>
        change ℤ at j
        cases k with
        | upperLeft k => cases k
        | upperRight k => cases k
        | lowerRight k => cases k
        | lowerLeft k =>
          change ℤ at k
          simp [sideTag, sideDistance]

/-- Helper toward Definition 3.2: almost surely the corrected external
successor has the converse side-index classification. Since the corrected
presentation has only a lower-left side and every lower-left index has a
successor, injectivity identifies the target index with that successor. -/
theorem ae_uibhbotDefinition32ReversedPresentation_successorClassification :
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
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        let S : (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
            × Bool → (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
              × Bool := fun d =>
          uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
            (wholePlaneFaceSucc W H
              ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d))
        ∀ i j : InfiniteBoundaryDartIndex Q,
          S (InfiniteBoundaryDartIndex.dart Q i) = InfiniteBoundaryDartIndex.dart Q j →
            sideNext Q i = some j ∨
              (sideNext Q i = none ∧ firstOnSide Q j ∧
                nextNonemptySide Q (sideTag Q i) (sideTag Q j) ∧
                boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
                  boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j)) := by
  filter_upwards [ae_uibhbotDefinition32ReversedPresentation_lowerLeft_geometryClauses]
    with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hLL, hlabels, G', U, hsucc, hwithin⟩
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos e hinj
  let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  let S : (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
      × Bool → (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge
        × Bool := fun d => φ (wholePlaneFaceSucc W H (φ.symm d))
  have hclass : ∀ i j : InfiniteBoundaryDartIndex Q,
      S (InfiniteBoundaryDartIndex.dart Q i) = InfiniteBoundaryDartIndex.dart Q j →
        sideNext Q i = some j ∨
          (sideNext Q i = none ∧ firstOnSide Q j ∧
            nextNonemptySide Q (sideTag Q i) (sideTag Q j) ∧
            boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
              boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j)) := by
    intro i j hS
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at l
        have hnext : sideNext Q (.lowerLeft k) = some (.lowerLeft (k - 1)) := by
          simp [sideNext, Q, uibhbotDefinition32ReversedPresentation]
        have hw := hwithin (.lowerLeft k) (.lowerLeft (k - 1)) hnext
        have hdart : InfiniteBoundaryDartIndex.dart Q (.lowerLeft (k - 1)) =
            InfiniteBoundaryDartIndex.dart Q (.lowerLeft l) := hw.symm.trans hS
        have hidx : k - 1 = l := by
          have hφ :
              uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                  (e (k - 1), true) =
                uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                  (e l, true) := by
            have hφ' := hdart
            have hlisted₁ : InfiniteBoundaryDartIndex.dart Q (.lowerLeft (k - 1)) =
                uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                  (e (k - 1), true) := by
              simp [Q, uibhbotDefinition32ReversedPresentation,
                InfiniteBoundaryDartIndex.dart_eq]
            have hlisted₂ : InfiniteBoundaryDartIndex.dart Q (.lowerLeft l) =
                uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
                  (e l, true) := by
              simp [Q, uibhbotDefinition32ReversedPresentation,
                InfiniteBoundaryDartIndex.dart_eq]
            exact hlisted₁.symm.trans (hφ'.trans hlisted₂)
          have hsrc := (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).injective hφ
          exact hinj (congrArg Prod.fst hsrc)
        left
        subst l
        simpa [sideNext, Q, uibhbotDefinition32ReversedPresentation]
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hinj,
    hclass⟩





























































end

end DirectedDistances.PaperProofs.Section5

end
