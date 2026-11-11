/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation3

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

local notation "Q" => uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
  hFim hFa hRpos
local notation "RQ" => uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
  P hp ha F hf hFim hFa hRpos
local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa

/-- Helper toward Definition 3.2: the representative-adjusted dart map
preserves the geometric-edge coordinate. -/
theorem uibhbotAssemblyBoundaryDartEquiv3_edge
    (d : WholePlaneDart W) :
    (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d).1 =
      Quotient.mk
        (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid d := by
  rcases d with ⟨e, b⟩
  simp only [uibhbotAssemblyBoundaryDartEquiv3,
    uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
  rfl

/-- Helper toward Definition 3.2: the corrected lower-left orientation and
successor convention preserve all three clauses of `IsBoundaryOrderOfInf`.
Each clause is transferred on its own lower-left index; the other three
families are empty in both presentations. -/
theorem uibhbotDefinition32ReversedPresentation_isBoundaryOrderOfInf_of_original
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (hmap : IsBoundaryOrderOfInf
      (uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos) (Q e hinj)) :
    IsBoundaryOrderOfInf
      (uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos) (RQ e hinj) := by
  rw [uibhbotDefinition32Presentation_eq
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj] at hmap
  dsimp [uibhbotDefinition32ReversedPresentation]
  rw [IsBoundaryOrderOfInf_iff] at hmap ⊢
  rcases hmap with ⟨hcover, hmultiplicity, hdouble⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | upperLeft i => cases i
      | upperRight i => cases i
      | lowerRight i => cases i
      | lowerLeft k =>
        rw [InfiniteBoundaryDartIndex.dart_eq] at hi
        apply (hcover a).mp
        refine ⟨InfiniteBoundaryDartIndex.lowerLeft k, ?_⟩
        rw [InfiniteBoundaryDartIndex.dart_eq]
        exact (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
          (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
          (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e k, true))).symm.trans hi
    · intro hfront
      obtain ⟨i, hi⟩ := (hcover a).mpr hfront
      cases i with
      | upperLeft i => cases i
      | upperRight i => cases i
      | lowerRight i => cases i
      | lowerLeft k =>
        rw [InfiniteBoundaryDartIndex.dart_eq] at hi
        refine ⟨InfiniteBoundaryDartIndex.lowerLeft k, ?_⟩
        rw [InfiniteBoundaryDartIndex.dart_eq]
        have hi' : Quotient.mk
            (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
            (e k, true) = a := by
          simpa [InfiniteBoundaryDartIndex.dart_eq] using hi
        exact (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
          (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
          (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e k, true))).trans hi'
  · intro a i j k hi hj hk
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
        | lowerLeft k =>
          rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj hk
          have hi' : Quotient.mk
              (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
              (e i, true) = a :=
            (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
              (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
              (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e i, true))).symm.trans hi
          have hj' : Quotient.mk
              (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
              (e j, true) = a :=
            (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
              (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
              (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e j, true))).symm.trans hj
          have hk' : Quotient.mk
              (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
              (e k, true) = a :=
            (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
              (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
              (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e k, true))).symm.trans hk
          rcases hmultiplicity a (.lowerLeft i) (.lowerLeft j) (.lowerLeft k)
              (by simpa [InfiniteBoundaryDartIndex.dart_eq] using hi')
              (by simpa [InfiniteBoundaryDartIndex.dart_eq] using hj')
              (by simpa [InfiniteBoundaryDartIndex.dart_eq] using hk') with hij | hik | hjk
          · apply Or.inl
            have hidx : i = j := by injection hij
            exact congrArg InfiniteBoundaryDartIndex.lowerLeft hidx
          · apply Or.inr (Or.inl _)
            have hidx : i = k := by injection hik
            exact congrArg InfiniteBoundaryDartIndex.lowerLeft hidx
          · apply Or.inr (Or.inr _)
            have hidx : j = k := by injection hjk
            exact congrArg InfiniteBoundaryDartIndex.lowerLeft hidx
  · intro a i j hij hi hj
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
        rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj
        have hi' : Quotient.mk
            (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
            (e i, true) = a :=
          (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
            (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
            (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e i, true))).symm.trans hi
        have hj' : Quotient.mk
            (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
            (e j, true) = a :=
          (uibhbotAssemblyBoundaryDartEquiv3_edge (W := W) (H := H) (h0 := h0)
            (hL := hL) (hR := hR) (hfin := hfin) (P := P) (hp := hp) (ha := ha)
            (F := F) (hf := hf) (hFim := hFim) (hFa := hFa) (d := (e j, true))).symm.trans hj
        refine hdouble a (.lowerLeft i) (.lowerLeft j) ?_
          (by simpa [InfiniteBoundaryDartIndex.dart_eq] using hi')
          (by simpa [InfiniteBoundaryDartIndex.dart_eq] using hj')
        intro heq
        injection heq with hidx
        exact hij (congrArg InfiniteBoundaryDartIndex.lowerLeft hidx)

/-- Helper toward Definition 3.2: almost surely the corrected presentation
inherits the source boundary-order clauses, while retaining the original
source-chain labels and full probability binders. -/
theorem ae_uibhbotDefinition32ReversedPresentation_isBoundaryOrderOfInf :
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
          h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e),
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        IsBoundaryOrderOfInf M
          (uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
            hFim hFa hRpos e hinj) := by
  filter_upwards [ae_uibhbotDefinition32Presentation_isBoundaryOrderOfInf]
    with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, hmap⟩
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hinj, hsource,
    uibhbotDefinition32ReversedPresentation_isBoundaryOrderOfInf_of_original
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap⟩





















































end

end DirectedDistances.PaperProofs.Section5

end
