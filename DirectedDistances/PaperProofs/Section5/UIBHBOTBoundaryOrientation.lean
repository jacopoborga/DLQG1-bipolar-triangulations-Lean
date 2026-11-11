/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package2
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry5

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
local notation "φ" => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa

/-! Helper toward Definition 3.2.  `dartBorders d U` puts `U` on the left
of the oriented dart.  Package2 proves that every currently listed dart pulls
back with bit `false`; Geometry3 classifies the external face with bit `true`.
The corrected lower-left side therefore uses the reversed whole-plane dart,
and `next` runs in decreasing integer order. -/

/-- Helper toward Definition 3.2: reverse a presentation dart, retaining its
geometric edge identity. -/
@[expose] def uibhbotReverseBoundaryDart (d : (G).GeometricEdge × Bool) :
    (G).GeometricEdge × Bool := (d.1, !d.2)

/-- Helper toward Definition 3.2: reversing a dart twice restores it. -/
theorem uibhbotReverseBoundaryDart_involutive (d : (G).GeometricEdge × Bool) :
    uibhbotReverseBoundaryDart W H h0 hL hR hfin P hp ha F hf hFim hFa
      (uibhbotReverseBoundaryDart W H h0 hL hR hfin P hp ha F hf hFim hFa d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- Helper toward Definition 3.2: the corrected presentation reverses each
listed dart and its integer order, keeping all four source side labels and
the same edge sets.  The construction itself makes no claim about the
separate vertex-join predicate. -/
@[expose] def uibhbotDefinition32ReversedPresentation
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    InfiniteBoundaryPresentation M := by
  let lowerLeft : InfiniteBoundarySide (WholePlaneVertex W) (G).GeometricEdge := {
    Index := ℤ
    darts := ⟨fun k => φ (e k, true), by
        intro k j h
        have hsrc : (e k, true) = (e j, true) :=
          (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).injective h
        exact hinj (congrArg Prod.fst hsrc)⟩
    next := fun k => some (k - 1)
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
    lowerLeft := lowerLeft
  }

/-- Helper toward Definition 3.2: the reversed and reverse-indexed lower-left
dart is the representative-adjusted source dart with traversal bit `true`. -/
theorem uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) (k : ℤ) :
    (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos e hinj).lowerLeft.darts k = φ (e k, true) := by
  rfl

/-- Helper toward Definition 3.2: every reversed indexed UIBHBOT dart borders
the transported unbounded face, with that face on its left.  The old list's
false inverse bit is recorded by `uibhbotDefinition32Presentation_adjusted_inverse_bit`. -/
theorem uibhbotAssemblyBoundaryPresentationExternalFace3_reversedListedDartsBorder
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj)) :
    ∃ G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
        (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      ∃ U : G'.Face,
        ∀ k : ℤ, G'.dartBorders (φ (e k, true)) U := by
  obtain ⟨G', U, hcoverage⟩ :=
    uibhbotAssemblyBoundaryPresentationExternalFace3_indexedDartCoverage
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap
  refine ⟨G', U, ?_⟩
  intro k
  exact (hcoverage (φ (e k, true))).2 ⟨k, rfl⟩

/-- Helper toward Definition 3.2: reversing every listed dart gives exact
indexed coverage of the transported external face, with `U` on the left as
required by the v7 predicate. -/
theorem uibhbotAssemblyBoundaryPresentationExternalFace3_reversedIndexedCoverage
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf M (Q e hinj)) :
    ∃ G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
        (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      ∃ U : G'.Face,
        ∀ d, G'.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex
              (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj),
            InfiniteBoundaryDartIndex.dart
              (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj) i = d := by
  obtain ⟨G', U, hcoverage⟩ :=
    uibhbotAssemblyBoundaryPresentationExternalFace3_indexedDartCoverage
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap
  refine ⟨G', U, ?_⟩
  dsimp [uibhbotDefinition32ReversedPresentation]
  intro d
  rw [hcoverage d]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨InfiniteBoundaryDartIndex.lowerLeft k, ?_⟩
    have hk := uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj k
    dsimp [uibhbotDefinition32ReversedPresentation] at hk
    simp [InfiniteBoundaryDartIndex.dart_eq]
  · rintro ⟨i, hi⟩
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft j =>
      refine ⟨j, ?_⟩
      have hj := uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj j
      dsimp [uibhbotDefinition32ReversedPresentation] at hj
      have hlisted :
          InfiniteBoundaryDartIndex.dart
              (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj)
              (InfiniteBoundaryDartIndex.lowerLeft j) =
            φ (e j, true) := by
        simp [uibhbotDefinition32ReversedPresentation,
          InfiniteBoundaryDartIndex.dart_eq]
      exact hi.symm.trans hlisted



































end
end DirectedDistances.PaperProofs.Section5
