/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation5

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
local notation "G₀" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "φ" => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "rot₀" => uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa

/-- Helper toward Definition 3.2: choose once the transported assembly drawing
whose external face has the source missing-dart classification. Existence is
proved in Geometry3 before this choice is made. -/
@[expose] def uibhbotFixedBoundaryDrawing :
    PLDrawing ((G₀).GeometricEdge × Bool) (WholePlaneVertex W)
      (fun d => (d.1, !d.2)) rot₀ (boundaryDartInitial M) :=
  Classical.choose (uibhbotAssemblyBoundaryPresentationExternalFace3
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)

local notation "G₁" => uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: choose the unbounded face in the already
fixed transported drawing, together with its proved classification. -/
@[expose] def uibhbotFixedBoundaryFace : (G₁).Face :=
  Classical.choose (Classical.choose_spec (uibhbotAssemblyBoundaryPresentationExternalFace3
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos))

local notation "U₁" => uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: the fixed drawing and face retain uniqueness,
unboundedness, the exact missing-dart classification and geometric successor
from the proved transport construction. -/
theorem uibhbotFixedBoundaryFace_spec :
    (∃! V : (G₁).Face, (G₁).IsUnbounded V) ∧
    (G₁).IsUnbounded U₁ ∧
    (∀ d, (G₁).dartBorders d U₁ ↔
      ((φ).symm d).2 = true ∧ ¬ wholePlaneEdgePresent W ((φ).symm d).1) ∧
    IsGeometricExternalFaceSucc G₁ U₁ (fun d => (φ) (wholePlaneFaceSucc W H ((φ).symm d))) := by
  exact Classical.choose_spec (Classical.choose_spec
    (uibhbotAssemblyBoundaryPresentationExternalFace3
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos))

/-- Helper toward Definition 3.2: any unbounded face of this fixed drawing
is the chosen face; no comparison between faces of different drawings is used. -/
theorem uibhbotFixedBoundaryFace_eq_of_isUnbounded
    (V : (G₁).Face) (hV : (G₁).IsUnbounded V) : V = U₁ := by
  have hs := uibhbotFixedBoundaryFace_spec
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  exact hs.1.unique hV hs.2.1

end

noncomputable section

/-- Helper toward Definition 3.2: almost surely the corrected presentation
satisfies every v3 clause for the drawing and unbounded face chosen once above.
All clauses are proved from one source event, retaining its joint witnesses. -/
theorem ae_uibhbotFixedBoundary_externalFaceIntervalOrder3 :
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
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        let G := uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let U := uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
        let S := fun d => φ (wholePlaneFaceSucc W H (φ.symm d))
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        IsExternalFaceIntervalOrder3 M Q G U S := by
  filter_upwards [ae_uibhbotDefinition32Presentation_isBoundaryOrderOfInf] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, hmap⟩
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos e hinj
  let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  let G' := uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let U := uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let S := fun d => φ (wholePlaneFaceSucc W H (φ.symm d))
  obtain ⟨hunique, hunbounded, hborder, hsucc⟩ := uibhbotFixedBoundaryFace_spec
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hmap' : IsBoundaryOrderOfInf M Q :=
    uibhbotDefinition32ReversedPresentation_isBoundaryOrderOfInf_of_original
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap
  have hwest (k : ℤ) := (hsource k).1
  have heast (k : ℤ) := (hsource k).2.1
  have hmissing (k : ℤ) := (hsource k).2.2
  have hcoverage : ∀ d, G'.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex Q, InfiniteBoundaryDartIndex.dart Q i = d := by
    intro d
    rw [hborder]
    constructor
    · rintro ⟨hdirection, hmissingD⟩
      have hd : d = φ ((φ.symm d).1, true) := by
        calc
          d = φ (φ.symm d) := (φ.apply_symm_apply d).symm
          _ = φ ((φ.symm d).1, true) := congrArg φ (Prod.ext rfl hdirection)
      have hquot : Quotient.mk G.edgeSetoid (φ.symm d) = d.1 :=
        congrArg Prod.fst (φ.apply_symm_apply d)
      have hm : M.toPlaneMapWithMissing.missing d.1 := by
        rw [← hquot, uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk]
        exact hmissingD
      have hfront : ExternalFrontierEdge M d.1 :=
        (uibhbotAssembly_externalFrontierEdge_iff_missing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d.1).2 hm
      obtain ⟨i, hi⟩ :=
        (uibhbotDefinition32Presentation_externalFrontierEdge_iff_dartEdgeEnumerated
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap d.1).mp hfront
      obtain ⟨k, hk⟩ := (uibhbotDefinition32Presentation_dartEdge_range
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj d.1).mp ⟨i, hi⟩
      have hedge : (φ.symm d).1 = e k := by
        have heq : Quotient.mk G.edgeSetoid (φ.symm d) =
            Quotient.mk G.edgeSetoid (e k, true) := hquot.trans hk
        rcases Quotient.exact heq with h | h
        · exact congrArg Prod.fst h
        · exact congrArg Prod.fst h
      refine ⟨.lowerLeft k, ?_⟩
      rw [InfiniteBoundaryDartIndex.dart_eq]
      change φ (e k, true) = d
      rw [hd]
      exact congrArg φ (Prod.ext hedge.symm rfl)
    · rintro ⟨i, rfl⟩
      cases i with
      | upperLeft i => cases i
      | upperRight i => cases i
      | lowerRight i => cases i
      | lowerLeft k =>
        change ℤ at k
        have hlisted : InfiniteBoundaryDartIndex.dart Q (.lowerLeft k) =
            φ (e k, true) := by
          simp [Q, φ, uibhbotDefinition32ReversedPresentation,
            InfiniteBoundaryDartIndex.dart_eq]
        rw [hlisted]
        let dsrc : WholePlaneDart W := (e k, true)
        change (φ.symm (φ dsrc)).2 = true ∧
          ¬ wholePlaneEdgePresent W (φ.symm (φ dsrc)).1
        rw [φ.symm_apply_apply]
        exact ⟨rfl, hmissing k⟩
  have hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N) := fun N =>
    boundaryHitWitnesses_of_le W (Nat.zero_le N) h0
  have hwithin : ∀ i j : InfiniteBoundaryDartIndex Q,
      sideNext Q i = some j →
        (fun d => φ (wholePlaneFaceSucc W H (φ.symm d)))
          (InfiniteBoundaryDartIndex.dart Q i) =
        InfiniteBoundaryDartIndex.dart Q j := by
    intro i j hnext
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      cases j with
      | upperLeft j => cases j
      | upperRight j => cases j
      | lowerRight j => cases j
      | lowerLeft l =>
        change ℤ at k
        change ℤ at l
        have hnext' : (some (k - 1) : Option ℤ) = some l := by
          simpa [sideNext, Q, uibhbotDefinition32ReversedPresentation] using hnext
        have hidx : l = k - 1 := (Option.some.inj hnext').symm
        subst l
        simp only [InfiniteBoundaryDartIndex.dart_eq]
        rw [uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj k,
          uibhbotDefinition32ReversedPresentation_lowerLeft_dart_eq
            W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj (k - 1)]
        let dk : WholePlaneDart W := (e k, true)
        let dnext : WholePlaneDart W := (e (k - 1), true)
        change φ (wholePlaneFaceSucc W H (φ.symm (φ dk))) = φ dnext
        rw [φ.symm_apply_apply]
        have hface := uibhbotSourceChainEastDart_faceSucc
          W H hhit e hwest heast hmissing k
        have hface' : wholePlaneFaceSucc W H dk = dnext := by
          simpa [dk, dnext] using hface
        rw [hface']
  have hjoin : ∀ i j : InfiniteBoundaryDartIndex Q, sideNext Q i = some j →
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j) := by
    intro i j hij
    let d := InfiniteBoundaryDartIndex.dart Q i
    have hb : G'.dartBorders d U := (hcoverage d).2 ⟨i, rfl⟩
    have hrot := (hsucc.2 d hb).1
    have hv := G'.vert_rotation
      ((uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm
        (d.1, !d.2))
    rw [Equiv.apply_symm_apply] at hv
    calc
      boundaryDartTerminal M d = boundaryDartInitial M (d.1, !d.2) := by
        rw [boundaryDartTerminal_eq, boundaryDartInitial_eq]
        cases d.2 <;> rfl
      _ = boundaryDartInitial M
          ((uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm
            (d.1, !d.2)) := hv
      _ = boundaryDartInitial M (S d) := congrArg (boundaryDartInitial M) hrot.symm
      _ = boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j) :=
        congrArg (boundaryDartInitial M) (hwithin i j hij)
  have hll : LLOkInf Q := by
    rw [LLOkInf_iff]
    constructor
    · intro k
      change ℤ at k
      change M.toPlaneMapWithMissing.missing (φ (e k, true)).1
      have hedge : (φ (e k, true)).1 = Quotient.mk G.edgeSetoid (e k, true) := rfl
      have hm := (uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos (e k, true)).2 (hmissing k)
      exact hedge.symm ▸ hm
    · intro i j hij
      have hj := hjoin (.lowerLeft i) (.lowerLeft j) (by
        simpa only [sideNext, Option.map] using congrArg
          (Option.map InfiniteBoundaryDartIndex.lowerLeft) hij)
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hj
  have htotal : ∀ i : InfiniteBoundaryDartIndex Q,
      ∃ j, S (InfiniteBoundaryDartIndex.dart Q i) = InfiniteBoundaryDartIndex.dart Q j := by
    intro i
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      exact ⟨.lowerLeft (k - 1), hwithin _ _ (by
        simp [sideNext, Q, uibhbotDefinition32ReversedPresentation])⟩
  have hinjQ : Function.Injective (InfiniteBoundaryDartIndex.dart Q) := by
    intro i j hij
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
        exact congrArg InfiniteBoundaryDartIndex.lowerLeft
          (Q.lowerLeft.darts.injective (by
            simpa only [InfiniteBoundaryDartIndex.dart_eq] using hij))
  have hclass : ∀ i j : InfiniteBoundaryDartIndex Q,
      S (InfiniteBoundaryDartIndex.dart Q i) = InfiniteBoundaryDartIndex.dart Q j →
        sideNext Q i = some j ∨
          (sideNext Q i = none ∧ firstOnSide Q j ∧
            nextNonemptySide Q (sideTag Q i) (sideTag Q j) ∧
            boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
              boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j)) := by
    intro i j hij
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k =>
      change ℤ at k
      have hn : sideNext Q (.lowerLeft k) = some (.lowerLeft (k - 1)) := by
        simp [sideNext, Q, uibhbotDefinition32ReversedPresentation]
      have heq := hinjQ ((hwithin _ _ hn).symm.trans hij)
      exact Or.inl (hn.trans (congrArg some heq))
  have hstop : ∀ i : InfiniteBoundaryDartIndex Q, sideNext Q i ≠ none := by
    intro i
    cases i with
    | upperLeft i => cases i
    | upperRight i => cases i
    | lowerRight i => cases i
    | lowerLeft k => exact Option.some_ne_none _
  have hUL : ULOkInf Q := by
    rw [ULOkInf_iff]
    exact ⟨fun i => Empty.elim i, fun i => Empty.elim i⟩
  have hUR : UROkInf Q := by
    rw [UROkInf_iff]
    exact ⟨fun i => Empty.elim i, fun i => Empty.elim i⟩
  have hLR : LROkInf Q := by
    rw [LROkInf_iff]
    exact ⟨fun i => Empty.elim i, fun i => Empty.elim i⟩
  let : IsEmpty Q.upperLeft.Index := by
    change IsEmpty Empty
    infer_instance
  let : IsEmpty Q.lowerRight.Index := by
    change IsEmpty Empty
    infer_instance
  have hsimpleUL : IsSimpleBoundarySide M Q.upperLeft :=
    isSimpleBoundarySide_of_isEmpty5 Q.upperLeft
  have hsimpleLR : IsSimpleBoundarySide M Q.lowerRight :=
    isSimpleBoundarySide_of_isEmpty5 Q.lowerRight
  have hlabelsUL : BoundarySideEndpointLabels M Q.upperLeft := by
    simp [BoundarySideEndpointLabels, Q, uibhbotDefinition32ReversedPresentation]
  have hlabelsUR : BoundarySideEndpointLabels M Q.upperRight := by
    simp [BoundarySideEndpointLabels, Q, uibhbotDefinition32ReversedPresentation]
  have hlabelsLR : BoundarySideEndpointLabels M Q.lowerRight := by
    simp [BoundarySideEndpointLabels, Q, uibhbotDefinition32ReversedPresentation]
  have hlabelsLL : BoundarySideEndpointLabels M Q.lowerLeft :=
    uibhbotDefinition32ReversedPresentation_lowerLeft_endpointLabels
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  have hjoinLabels : BoundaryJoinEndpointLabels Q S := by
    intro i j _ hnone
    exact (hstop i hnone).elim
  have hrequired : RequiredBoundaryJoinEndpointLabels Q S := by
    intro i j _ hnone
    exact (hstop i hnone).elim
  have hbase : IsExternalFaceIntervalOrder M Q G' U S :=
    ⟨hmap', hcoverage, hsucc, fun i j hij => ⟨hwithin i j hij, hjoin i j hij⟩,
      htotal, hclass⟩
  have hv2 : IsExternalFaceIntervalOrder2 M Q G' U S :=
    ⟨hbase, hUL, hUR, hLR, hll, hsimpleUL, hsimpleLR,
      hlabelsUL, hlabelsUR, hlabelsLR, hlabelsLL, hjoinLabels⟩
  have hv3 : IsExternalFaceIntervalOrder3 M Q G' U S :=
    ⟨hv2, uibhbotDefinition32ReversedPresentation_positionOrder3
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj, hrequired⟩
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hsource, hv3⟩

/-- Helper toward Definition 3.2: the fixed drawing and face satisfy the v7
predicate almost surely, by the proved infinite-boundary v7-to-v3 reduction. -/
theorem ae_uibhbotFixedBoundary_externalFaceIntervalOrder7 :
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
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        let G := uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let U := uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let φ := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
        let S := fun d => φ (wholePlaneFaceSucc W H (φ.symm d))
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        IsExternalFaceIntervalOrder7 M ⟨Q, none⟩ G U S := by
  filter_upwards [ae_uibhbotFixedBoundary_externalFaceIntervalOrder3] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, hv3⟩
  have hmap := hv3.1.1.1
  have hv7 := (uibhbotDefinition32ReversedPresentation_externalFaceIntervalOrder7_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj hmap
    (uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
    (uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
    (fun d => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
      (wholePlaneFaceSucc W H
        ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d)))).mpr hv3
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hsource, hv7⟩

/-- Helper toward Definition 3.2: almost surely the UIBHBOT assembly admits
a boundary presentation, rotation, drawing, unbounded face and successor with
`IsBoundEdges32`. The chosen presentation is exactly the reversed lower-left
integer chain, with no finite-junction marks. -/
theorem ae_exists_uibhbot_bound_edges32 :
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
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        let G₀ := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        ∃ (B : BoundaryPresentationWithJunctions M)
          (rot : Equiv.Perm (G₀.GeometricEdge × Bool))
          (G : PLDrawing (G₀.GeometricEdge × Bool) (WholePlaneVertex W)
            (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
          (U : G.Face) (S : G₀.GeometricEdge × Bool → G₀.GeometricEdge × Bool),
          B = ⟨Q, none⟩ ∧ B.finiteJunctions? = none ∧ IsBoundEdges32 M B G U S := by
  filter_upwards [ae_uibhbotFixedBoundary_externalFaceIntervalOrder7] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, hv7⟩
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hsource,
    ⟨uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj, none⟩,
    uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa,
    uibhbotFixedBoundaryDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    uibhbotFixedBoundaryFace W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    (fun d => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
      (wholePlaneFaceSucc W H
        ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d))),
    rfl, rfl, ?_⟩
  exact hv7
















end
end DirectedDistances.PaperProofs.Section5
