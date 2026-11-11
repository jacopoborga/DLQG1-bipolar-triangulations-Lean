/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation6

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults
open scoped Classical

/-- Helper toward Definition 3.2: almost surely, with the assembly and
source-chain witnesses produced by the Definition 5.8 provider, every
geometric edge tagged missing by the assembly is represented by an indexed
source-chain edge. -/
theorem ae_uibhbotDefinition32Presentation_missingEdge_in_chain :
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
        (e : ℤ → WholePlaneEdge W),
        let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        Function.Injective e ∧
        ∀ a : G.GeometricEdge, M.missing a →
          ∃ k : ℤ, a = Quotient.mk G.edgeSetoid (e k, true) := by
  filter_upwards [def_uibhbot_provider] with W hW
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    _hexternal, _hacyclic, _huniqueFace, _hdartBorder, _hedgeBorder,
    _htriangles, hedge, hinj, _hroot, _hfaceSucc, hexhaust, _hleast,
    _hstrictAnti, _hzero, _hrootMissing, _hrootEndpoints, _hwalkZero,
    _hnegative, _hlawNat, _hlawInt⟩ := hW
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    ?_, hinj, ?_⟩
  · intro k
    exact ⟨(hedge k).1, (hedge k).2.1, (hedge k).2.2.1⟩
  · intro a hmiss
    change ¬ wholePlaneEdgePresent W a.out.1 at hmiss
    obtain ⟨k, hfk, _⟩ := (hexhaust a.out.1).mp hmiss
    refine ⟨k, ?_⟩
    calc
      a = Quotient.mk G.edgeSetoid a.out := (Quotient.out_eq a).symm
      _ = Quotient.mk G.edgeSetoid (e k, true) := by
        cases hb : a.out.2
        · have hd : a.out = (e k, false) := Prod.ext hfk hb
          rw [hd]
          exact G.geometricEdge_flip (e k, true)
        · have hd : a.out = (e k, true) := Prod.ext hfk hb
          rw [hd]

/-- Helper toward Definition 3.2: almost surely, the assembly's missing
geometric edges are exactly the edges indexed by the source chain. -/
theorem ae_uibhbotDefinition32Presentation_missingEdge_iff_chain :
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
        (e : ℤ → WholePlaneEdge W),
        let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        Function.Injective e ∧
        ∀ a : G.GeometricEdge, M.missing a ↔
          ∃ k : ℤ, a = Quotient.mk G.edgeSetoid (e k, true) := by
  filter_upwards [ae_uibhbotDefinition32Presentation_missingEdge_in_chain] with W hW
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hedge, hinj, hforward⟩ := hW
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hedge, hinj, ?_⟩
  intro a
  constructor
  · exact hforward a
  · rintro ⟨k, rfl⟩
    rw [uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)]
    exact (hedge k).2.2

/-- Helper toward Definition 3.2: the edge projection of the presentation's
disjoint-union index and dart maps has exactly the source-chain range. -/
theorem uibhbotDefinition32Presentation_dartEdge_range
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
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    ∀ a : (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge,
      (∃ i : InfiniteBoundaryDartIndex
        (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
          hRpos e hinj),
        (InfiniteBoundaryDartIndex.dart
          (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
            hRpos e hinj) i).1 = a) ↔
      ∃ k : ℤ, a = Quotient.mk
        (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
        (e k, true) := by
  intro a
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | upperLeft i => exact isEmptyElim i
    | upperRight i => exact isEmptyElim i
    | lowerRight i => exact isEmptyElim i
    | lowerLeft k =>
      rw [InfiniteBoundaryDartIndex.dart_eq] at hi
      refine ⟨k, ?_⟩
      change Quotient.mk _ (e k, true) = a at hi
      exact hi.symm
  · rintro ⟨k, ha⟩
    refine ⟨InfiniteBoundaryDartIndex.lowerLeft k, ?_⟩
    rw [InfiniteBoundaryDartIndex.dart_eq]
    change Quotient.mk _ (e k, true) = a
    exact ha.symm

/-- Helper toward Definition 3.2: distinct presentation indices select
distinct geometric edges, by injectivity of the source-chain edge map. -/
theorem uibhbotDefinition32Presentation_dartEdge_injective
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
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    Function.Injective (fun i : InfiniteBoundaryDartIndex
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj) =>
      (InfiniteBoundaryDartIndex.dart
        (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
          hRpos e hinj) i).1) := by
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj]
  intro i j hij
  cases i with
  | upperLeft i => exact isEmptyElim i
  | upperRight i => exact isEmptyElim i
  | lowerRight i => exact isEmptyElim i
  | lowerLeft k =>
    cases j with
    | upperLeft j => exact isEmptyElim j
    | upperRight j => exact isEmptyElim j
    | lowerRight j => exact isEmptyElim j
    | lowerLeft l =>
      change (InfiniteBoundaryDartIndex.dart _ (.lowerLeft k)).1 =
        (InfiniteBoundaryDartIndex.dart _ (.lowerLeft l)).1 at hij
      simp only [InfiniteBoundaryDartIndex.dart_eq] at hij
      change (Quotient.mk
          (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
          (e k, true) :
            (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge) =
        Quotient.mk
          (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid
          (e l, true) at hij
      have hkl : k = l := by
        apply hinj
        rcases Quotient.exact hij with h | h
        · exact congrArg Prod.fst h
        · exact congrArg Prod.fst h
      subst l
      rfl

/-- Helper toward Definition 3.2: almost surely, the indexed presentation
lists exactly the external frontier, with the required multiplicity clauses. -/
theorem ae_uibhbotDefinition32Presentation_isBoundaryOrderOfInf :
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
        let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        IsBoundaryOrderOfInf M
          (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
            hFim hFa hRpos e hinj) := by
  filter_upwards [ae_uibhbotDefinition32Presentation_missingEdge_iff_chain] with W hW
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hedge, hinj, hchain⟩ := hW
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hRange := uibhbotDefinition32Presentation_dartEdge_range
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  have hDartInj := uibhbotDefinition32Presentation_dartEdge_injective
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hinj, ?_, ?_⟩
  · exact hedge
  · rw [IsBoundaryOrderOfInf_iff]
    constructor
    · intro a
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨k, hEdge⟩ := (hRange a).mp ⟨i, hi⟩
        have hmissing : M.missing a := (hchain a).mpr ⟨k, hEdge⟩
        exact (uibhbotAssembly_externalFrontierEdge_iff_missing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a).mpr hmissing
      · intro hfront
        have hmissing := (uibhbotAssembly_externalFrontierEdge_iff_missing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a).mp hfront
        obtain ⟨k, hEdge⟩ := (hchain a).mp hmissing
        exact (hRange a).mpr ⟨k, hEdge⟩
    constructor
    · intro a i j k hi hj hk
      have hij : i = j := hDartInj (hi.trans hj.symm)
      exact Or.inl hij
    · intro a i j hne hi hj
      have hij : i = j := hDartInj (hi.trans hj.symm)
      exact False.elim (hne hij)

end DirectedDistances.PaperProofs.Section5

end
