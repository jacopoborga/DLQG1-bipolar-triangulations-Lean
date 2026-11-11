/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness

/-! Cross-witness carrier transport and the unrestricted reader's mode obstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: every prescribed mode occurs among source
witnesses of an observed presentation, on a common probability-one event.
The presentation parameter `x` does not constrain the witness's mode. -/
theorem ae_lPlusSourceWitness_exists_with_longest
    (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ longest : Bool,
      ∃ s : LPlusSidePresentationSourceWitness x k
          (decodeLPlus x k (leftSideObsNonneg x k W)),
        s.W = W ∧ s.longest = longest := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hgeo
  intro longest
  obtain ⟨R, T, P, _, hleft, _, _⟩ := hpaths longest
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  refine ⟨⟨W, h, H, hLL, longest, hτ, hp, P k,
    hcoherent (if longest then XDP.ldp else XDP.sdp), T k, hfin,
    hleft k, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Helper toward Lemma 5.5: observed presentations almost surely have a
source witness whose selected mode differs from the presentation mode.
Consequently alignment cannot be deduced for every source witness. -/
theorem ae_lPlusSourceWitness_exists_not_mode_aligned
    (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : LPlusSidePresentationSourceWitness x k
          (decodeLPlus x k (leftSideObsNonneg x k W)),
        s.W = W ∧ (if s.longest then XDP.ldp else XDP.sdp) ≠ x := by
  filter_upwards [ae_lPlusSourceWitness_exists_with_longest x k] with W hW
  cases x with
  | ldp =>
    obtain ⟨s, hsW, hsl⟩ := hW false
    exact ⟨s, hsW, by rw [hsl]; decide⟩
  | sdp =>
    obtain ⟨s, hsW, hsl⟩ := hW true
    exact ⟨s, hsW, by rw [hsl]; decide⟩

/-- Helper toward Lemma 5.5: the corrected class of any source witness
is its own actual-side class, with no alignment restriction. -/
theorem LPlusSidePresentationSourceWitness.codeBlockSide4_class_eq_actual
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k) :
    geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
      geometricSideClass (m0GeodesicSide s.hp s.P .left) := by
  exact ((geometricSideClass_eq_iff _ _).mpr
    (boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4
      s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)).symm

/-- Helper toward Lemma 5.5: the quotient cell carrier is equivalent to
the corrected code side, retaining both vertex and dart branches. -/
@[expose] noncomputable def LPlusSidePresentationSourceWitness.codeBlockCellEquiv4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k) :
    Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
        (LPlusGluedDart s.longest s.hqMode s.hτ) ≃
      GeometricSideCell
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) :=
  (lPlusGluedCellEquiv s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).trans
    (lPlusActualCodeBlockCellEquiv4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)

/-- Helper toward Lemma 5.5: the corrected quotient-to-cell map preserves
the vertex tag exactly, including its false value on dart cells. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (u v : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
        (LPlusGluedDart s.longest s.hqMode s.hτ)) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .vertex (s.codeBlockCellEquiv4 x k r hk u)
          (s.codeBlockCellEquiv4 x k r hk v) ↔ u.isLeft = true := by
  cases u with
  | inl a =>
    change True ↔ true = true
    exact ⟨fun _ => rfl, fun _ => trivial⟩
  | inr d =>
    change False ↔ false = true
    exact ⟨False.elim, Bool.noConfusion⟩

/-- Helper toward Lemma 5.5: the root tag is precisely the quotient class
of primed vertex 1, for every source witness, including index zero. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (u v : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
        (LPlusGluedDart s.longest s.hqMode s.hτ)) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .root (s.codeBlockCellEquiv4 x k r hk u)
          (s.codeBlockCellEquiv4 x k r hk v) ↔
      u = .inl ⟦Sum.inr (Sum.inl 1)⟧ := by
  cases u with
  | inl a =>
    let V := lPlusGluedVertexEquiv s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let a₀ : LPlusGluedVertex s.longest s.hqMode s.hτ := ⟦Sum.inr (Sum.inl 1)⟧
    have hroot : (V a₀).val = boundaryVertex (shiftedStream s.W 0) s.h k :=
      lPlus_primed_root_starts_at_xk s.hτ
    change (V a).val = boundaryVertex (shiftedStream s.W 0) s.h k ↔
      Sum.inl a = (Sum.inl a₀ : Sum _ (LPlusGluedDart s.longest s.hqMode s.hτ))
    rw [← hroot]
    constructor
    · intro h
      exact congrArg Sum.inl (V.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun b => (V b).val) (Sum.inl.inj h)
  | inr d =>
    change False ↔ Sum.inr d =
      (Sum.inl ⟦Sum.inr (Sum.inl 1)⟧ : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ) _)
    exact ⟨False.elim, fun h => nomatch h⟩

/-- Helper toward Lemma 5.5: the simultaneous quotient transports induce
a cell equivalence preserving vertices and the marked root. All geometric
edges, including missing edges, remain in its dart carrier. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_vertex_root
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      (∀ u v, geometricSideRelation B .vertex u v ↔
        geometricSideRelation B' .vertex (F u) (F v)) ∧
      (∀ u v, geometricSideRelation B .root u v ↔
        geometricSideRelation B' .root (F u) (F v)) := by
  obtain ⟨phi, fV, fD, qV, qD, hqV, _, _, hTV, _, _, _, _⟩ :=
    lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  let E := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
  let E' := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
  let Q := Equiv.sumCongr qV qD
  let F := E.symm.trans (Q.trans E')
  have hF (a) : F (E a) = E' (Q a) := by
    change E' (Q (E.symm (E a))) = E' (Q a)
    rw [E.symm_apply_apply]
  have hroot : qV ⟦Sum.inr (Sum.inl 1)⟧ = ⟦Sum.inr (Sum.inl 1)⟧ := by
    rw [hqV, hTV]
  refine ⟨F, ?_, ?_⟩
  · intro u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff,
      s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff]
    cases a <;> rfl
  · intro u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff,
      s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff]
    have hQ : Q (.inl ⟦Sum.inr (Sum.inl 1)⟧) = .inl ⟦Sum.inr (Sum.inl 1)⟧ :=
      congrArg Sum.inl hroot
    rw [← hQ, Q.injective.eq_iff]


/-- Helper toward Lemma 5.5: reverse the endpoint bit inside its original
block, retaining the geometric edge even when it is missing. -/
@[expose] def lPlusSide4BlockOpposite
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {M : GeometricSideSubmap} :
    LPlusBlockDart W h k M → LPlusBlockDart W h k M
  | .inl d => .inl ⟨(d.val.1, !d.val.2), d.property⟩
  | .inr (.inl d) => .inr (.inl (d.1, !d.2))
  | .inr (.inr d) => .inr (.inr ⟨(d.val.1, !d.val.2), d.property⟩)

/-- Helper toward Lemma 5.5: reversing a local bit reverses the ambient
bit, including the primed block's side correction. -/
theorem lPlusSide4BlockOpposite_image
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {M : GeometricSideSubmap}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (a : LPlusBlockDart W h k M) :
    lPlusBlockDartImage hτ (lPlusSide4BlockOpposite a) =
      ((lPlusBlockDartImage hτ a).1, !(lPlusBlockDartImage hτ a).2) := by
  rcases a with a | (a | a)
  · rfl
  · change (_, (!a.2) ^^ primedLimitSideFlip _ hτ a.1) =
      (_, !(a.2 ^^ primedLimitSideFlip _ hτ a.1))
    cases a.2 <;> cases primedLimitSideFlip _ hτ a.1 <;> rfl
  · rfl

/-- Helper toward Lemma 5.5: the block reversal descends to the complete
gluing quotient, since its geometric image respects the gluing kernel. -/
@[expose] noncomputable def lPlusSide4GluedOpposite
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    {hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime}
    {hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)} :
    LPlusGluedDart longest hqMode hτ → LPlusGluedDart longest hqMode hτ :=
  Quotient.map lPlusSide4BlockOpposite (by
    intro a b hab
    change lPlusBlockDartImage hτ (lPlusSide4BlockOpposite a) =
      lPlusBlockDartImage hτ (lPlusSide4BlockOpposite b)
    rw [lPlusSide4BlockOpposite_image, lPlusSide4BlockOpposite_image]
    change lPlusBlockDartImage hτ a = lPlusBlockDartImage hτ b at hab
    rw [hab])

/-- Helper toward Lemma 5.5: the corrected side's opposite relation is
exactly reversal on its glued dart quotient. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .opposite (s.codeBlockCellEquiv4 x k r hk (.inr a))
          (s.codeBlockCellEquiv4 x k r hk (.inr b)) ↔
      lPlusSide4GluedOpposite a = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change ((lPlusBlockDartImage s.hτ a).1, !(lPlusBlockDartImage s.hτ a).2) =
        lPlusBlockDartImage s.hτ b ↔
        (⟦lPlusSide4BlockOpposite a⟧ : LPlusGluedDart s.longest s.hqMode s.hτ) = ⟦b⟧
      rw [← lPlusSide4BlockOpposite_image]
      constructor
      · intro h
        apply Quotient.sound
        exact h
      · intro h
        exact Quotient.exact h

/-- Helper toward Lemma 5.5: simultaneous quotient transports preserve
opposite darts, with the same block representative actions as the d340 map. -/
theorem lPlusSourceWitnessAligned_gluedQuotientEquiv_opposite
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    ∃ qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ,
      ∀ a, qD (lPlusSide4GluedOpposite a) = lPlusSide4GluedOpposite (qD a) := by
  obtain ⟨phi, fV, fD, qV, qD, _, hqD, _, _, _, hPD, hTD, hHD⟩ :=
    lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  have hblock (a) : fD (lPlusSide4BlockOpposite a) = lPlusSide4BlockOpposite (fD a) := by
    rcases a with a | (a | a)
    · obtain ⟨a', ha', hav⟩ := hPD a
      obtain ⟨b', hb', hbv⟩ := hPD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inl ⟨(a.val.1, !a.val.2), a.property⟩) = _
      rw [hb', ha']
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hbv.trans (congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hav.symm)
    · change fD (.inr (.inl (a.1, !a.2))) = _
      rw [hTD, hTD]
      rfl
    · obtain ⟨a', ha', hpa⟩ := hHD a
      obtain ⟨b', hb', hpb⟩ := hHD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inr (.inr ⟨(a.val.1, !a.val.2), a.property⟩)) = _
      rw [hb', ha']
      have hop := (phi.relation_iff .opposite (.inr a)
        (.inr ⟨(a.val.1, !a.val.2), a.property⟩)).mp
          (show geometricSideRelation _ .opposite _ _ from rfl)
      rw [hpa, hpb] at hop
      exact congrArg (fun d => Sum.inr (Sum.inr d)) (Subtype.ext hop.symm)
  refine ⟨qD, ?_⟩
  intro a
  induction a using Quotient.inductionOn with
  | h a =>
    change qD ⟦lPlusSide4BlockOpposite a⟧ = lPlusSide4GluedOpposite (qD ⟦a⟧)
    rw [hqD, hqD, hblock]
    rfl


/-- Helper toward Lemma 5.5: choose the incident vertex in the dart's own
block. The deleted prefix keeps its geometric endpoints and isolated root. -/
@[expose] noncomputable def LPlusSidePresentationSourceWitness.blockEndpoint4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) :
    LPlusBlockDart s.W s.h k
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode) →
      LPlusBlockVertex s.W s.h k
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)
  | .inl d => .inl ⟨kmswLimitDartVertex (shiftedStream s.W 0) d.val, by
      apply Or.inl
      refine ⟨d.val.1, d.property, ?_⟩
      cases hb : d.val.2
      · exact Or.inl (by simp only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte])
      · exact Or.inr (by simp only [kmswLimitDartVertex, hb, ↓reduceIte])⟩
  | .inr (.inl d) => .inr (.inl (kmswLimitDartVertex
      (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) d))
  | .inr (.inr d) => .inr (.inr ⟨if d.val.2 then
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).east d.val.1
      else (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).west d.val.1,
      by
        have he := geometricSideSubmap_endpoints
          (if s.longest then XDP.ldp else XDP.sdp)
          renewalTime renewalTime_positiveSuccessTime .left
          ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩ d.val.1 d.property
        cases d.val.2
        · exact he.1
        · exact he.2⟩)

/-- Helper toward Lemma 5.5: the local endpoint's vertex image is the
ambient endpoint of the corresponding geometric dart image. -/
theorem LPlusSidePresentationSourceWitness.blockEndpoint4_image
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusBlockVertexImage s.hτ (s.blockEndpoint4 x k r a) =
      kmswLimitDartVertex (shiftedStream s.W 0) (lPlusBlockDartImage s.hτ a) := by
  rcases a with a | (a | a)
  · rfl
  · exact (lMinusPrimedDartImage_endpoint s.hτ a).symm
  · change boundaryGluingHatVertexMap s.W s.h k s.hτ
      (kmswLimitDartVertex
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) a.val) = _
    rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
    have he := boundaryGluing_hat_edge_endpoints s.W s.h k s.hτ a.val.1
    cases hb : a.val.2
    · simpa only [lPlusBlockDartImage, kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using he.1.symm
    · simpa only [lPlusBlockDartImage, kmswLimitDartVertex, hb, ↓reduceIte] using he.2.symm

/-- Helper toward Lemma 5.5: incidence in the corrected side is equality
of a local endpoint class with the given glued vertex class. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode))
    (v : LPlusGluedVertex s.longest s.hqMode s.hτ) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .incident (s.codeBlockCellEquiv4 x k r hk (.inr ⟦a⟧))
          (s.codeBlockCellEquiv4 x k r hk (.inl v)) ↔
      (⟦s.blockEndpoint4 x k r a⟧ : LPlusGluedVertex s.longest s.hqMode s.hτ) = v := by
  let V := lPlusGluedVertexEquiv s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  change kmswLimitDartVertex (shiftedStream s.W 0) (lPlusBlockDartImage s.hτ a) =
    (V v).val ↔ _
  rw [← s.blockEndpoint4_image x k r a]
  change (V ⟦s.blockEndpoint4 x k r a⟧).val = (V v).val ↔ _
  exact ⟨fun h => V.injective (Subtype.ext h), fun h => congrArg (fun a => (V a).val) h⟩


/-- Helper toward Lemma 5.5: the d340 vertex and dart quotient maps
simultaneously transport every incident endpoint and the marked root. -/
theorem lPlusSourceWitnessAligned_endpointQuotient_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let N := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∃ (fD : LPlusBlockDart s.W s.h k M ≃ LPlusBlockDart s'.W s'.h k N)
      (qV : LPlusGluedVertex s.longest s.hqMode s.hτ ≃
        LPlusGluedVertex s'.longest s'.hqMode s'.hτ)
      (qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ a, qD ⟦a⟧ = ⟦fD a⟧) ∧
      qV ⟦Sum.inr (Sum.inl 1)⟧ = ⟦Sum.inr (Sum.inl 1)⟧ ∧
      (∀ a, qV ⟦s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r a⟧ =
        ⟦s'.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r' (fD a)⟧) ∧
      ∀ a, qD (lPlusSide4GluedOpposite a) = lPlusSide4GluedOpposite (qD a) := by
  obtain ⟨phi, fV, fD, qV, qD, hqV, hqD, hPV, hTV, hHV, hPD, hTD, hHD⟩ :=
    lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  let e := s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r
  let e' := s'.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r'
  have hendpoint (a) : fV (e a) = e' (fD a) := by
    rcases a with a | (a | a)
    · obtain ⟨a', ha, hav⟩ := hPD a
      obtain ⟨v', hv, hvv⟩ := hPV
        ⟨kmswLimitDartVertex (shiftedStream s.W 0) a.val,
          (show LPlusPrefixVertex s.W s.h k from
            (e (.inl a)).getLeft (by rfl)).property⟩
      change fV (.inl _) = _
      rw [hv, ha]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hvv.trans ((lPlusSourceWitnessAligned_prefixDartEndpoint_eq
        x k r r' s s' hk hr a).trans
          (congrArg (kmswLimitDartVertex (shiftedStream s'.W 0)) hav.symm))
    · change fV (.inr (.inl _)) = _
      rw [hTV, hTD]
      have hc := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
        x k r r' s s' hr
      change Sum.inr (Sum.inl (kmswLimitDartVertex _ a)) =
        Sum.inr (Sum.inl (kmswLimitDartVertex _ a))
      rw [hc]
    · obtain ⟨a', ha, hpa⟩ := hHD a
      let v := (e (.inr (.inr a))).getRight (by rfl) |>.getRight (by rfl)
      obtain ⟨v', hv, hpv⟩ := hHV v
      change fV (.inr (.inr v)) = _
      rw [hv, ha]
      have hi := (phi.relation_iff .incident (.inr a) (.inl v)).mp
        (show geometricSideRelation _ .incident (.inr a) (.inl v) from rfl)
      rw [hpa, hpv] at hi
      exact congrArg (fun v => Sum.inr (Sum.inr v)) (Subtype.ext hi.symm)
  have hblock (a) : fD (lPlusSide4BlockOpposite a) = lPlusSide4BlockOpposite (fD a) := by
    rcases a with a | (a | a)
    · obtain ⟨a', ha', hav⟩ := hPD a
      obtain ⟨b', hb', hbv⟩ := hPD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inl ⟨(a.val.1, !a.val.2), a.property⟩) = _
      rw [hb', ha']
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hbv.trans (congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hav.symm)
    · change fD (.inr (.inl (a.1, !a.2))) = _
      rw [hTD, hTD]
      rfl
    · obtain ⟨a', ha', hpa⟩ := hHD a
      obtain ⟨b', hb', hpb⟩ := hHD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inr (.inr ⟨(a.val.1, !a.val.2), a.property⟩)) = _
      rw [hb', ha']
      have hop := (phi.relation_iff .opposite (.inr a)
        (.inr ⟨(a.val.1, !a.val.2), a.property⟩)).mp
          (show geometricSideRelation _ .opposite _ _ from rfl)
      rw [hpa, hpb] at hop
      exact congrArg (fun d => Sum.inr (Sum.inr d)) (Subtype.ext hop.symm)
  refine ⟨fD, qV, qD, hqD, ?_, ?_, ?_⟩
  · rw [hqV, hTV]
  · intro a
    rw [hqV, hendpoint]
  · intro a
    induction a using Quotient.inductionOn with
    | h a =>
      change qD ⟦lPlusSide4BlockOpposite a⟧ = lPlusSide4GluedOpposite (qD ⟦a⟧)
      rw [hqD, hqD, hblock]
      rfl


/-- Helper toward Lemma 5.5: aligned equal-code witnesses have a cell
bijection preserving vertices, the root, incidence at either endpoint, and
opposite darts.
This does not assert the remaining marked relations. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_vertex_root_incident_opposite
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      ∀ t ∈ ({TruncationRelation.vertex, .root, .incident, .opposite} : Set TruncationRelation),
        ∀ u v, geometricSideRelation B t u v ↔
          geometricSideRelation B' t (F u) (F v) := by
  obtain ⟨fD, qV, qD, hqD, hroot, he, hop⟩ :=
    lPlusSourceWitnessAligned_endpointQuotient_transport x k r r' s s' hk hr
  let E := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
  let E' := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
  let Q := Equiv.sumCongr qV qD
  let F := E.symm.trans (Q.trans E')
  have hF (a) : F (E a) = E' (Q a) := by
    change E' (Q (E.symm (E a))) = E' (Q a)
    rw [E.symm_apply_apply]
  refine ⟨F, ?_⟩
  intro t ht u v
  obtain ⟨a, rfl⟩ := E.surjective u
  obtain ⟨b, rfl⟩ := E.surjective v
  rw [hF, hF]
  rcases ht with rfl | rfl | rfl | rfl
  · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff,
      s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff]
    cases a <;> rfl
  · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff,
      s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff]
    have hQ : Q (.inl ⟦Sum.inr (Sum.inl 1)⟧) = .inl ⟦Sum.inr (Sum.inl 1)⟧ :=
      congrArg Sum.inl hroot
    rw [← hQ, Q.injective.eq_iff]
  · cases a with
    | inl a => rfl
    | inr a =>
      cases b with
      | inr b => rfl
      | inl b =>
        induction a using Quotient.inductionOn with
        | h a =>
          change geometricSideRelation _ .incident (E (.inr ⟦a⟧)) (E (.inl b)) ↔
            geometricSideRelation _ .incident (E' (.inr (qD ⟦a⟧))) (E' (.inl (qV b)))
          rw [hqD,
            s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
            s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
            ← he, qV.injective.eq_iff]
  · cases a with
    | inl a => rfl
    | inr a =>
      cases b with
      | inl b => rfl
      | inr b =>
        change geometricSideRelation _ .opposite (E (.inr a)) (E (.inr b)) ↔
          geometricSideRelation _ .opposite (E' (.inr (qD a))) (E' (.inr (qD b)))
        rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
          ← hop, qD.injective.eq_iff]

/-- Helper toward Lemma 5.5: universal mode alignment is false for the
unrestricted witness type used by Reader4, even at a fixed nonnegative index. -/
theorem not_lPlusSourceWitness_universal_mode_alignment
    (x : XDP) (k : ℤ) :
    ¬ ∀ (r : LPlusSidePresentation x) (s : LPlusSidePresentationSourceWitness x k r),
      (if s.longest then XDP.ldp else XDP.sdp) = x := by
  intro hmode
  obtain ⟨W, s, _, hs⟩ := (ae_lPlusSourceWitness_exists_not_mode_aligned x k).exists
  exact hs (hmode _ s)


/-- Helper toward Lemma 5.5: at index zero, the nonpositive decoder
compares the complete aligned corrected-side classes, including all marks.
The isolated prefix root causes no loss of geometric information. -/
theorem lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq_zero
    (x : XDP) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x 0 r)
    (s' : LPlusSourceWitnessAligned x 0 r')
    (hr : r.code = r'.code) :
    geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft (le_refl 0)) =
      geometricSideClass
        (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft (le_refl 0)) := by
  let q : LMinusPreimage x :=
    ⟨s.W, s.h, s.H, s.hLL, s.longest, s.hmode.symm, 0, le_refl 0,
      s.hp, s.hτ, s.hqMode, s.hfin, s.P, s.Tpath, s.hleft⟩
  let q' : LMinusPreimage x :=
    ⟨s'.W, s'.h, s'.H, s'.hLL, s'.longest, s'.hmode.symm, 0, le_refl 0,
      s'.hp, s'.hτ, s'.hqMode, s'.hfin, s'.P, s'.Tpath, s'.hleft⟩
  have hcodes := lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x 0 r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr
  have hc : lMinusCodeOf q = lMinusCodeOf q' := by
    exact Prod.ext hcodes.2.2 hcodes.2.1
  have hd := (geometricSideClass_eq_iff _ _).mpr
    (lMinusDecodedSide4_markedIso_of_code_eq q q' hc)
  have hs := lMinusDecodedSide4_class_eq_actual
    s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft (le_refl 0)
  have hs' := lMinusDecodedSide4_class_eq_actual
    s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft (le_refl 0)
  exact (s.toLPlusSidePresentationSourceWitness.codeBlockSide4_class_eq_actual
    x 0 r (le_refl 0)).trans (hs.symm.trans (hd.trans (hs'.trans
      (s'.toLPlusSidePresentationSourceWitness.codeBlockSide4_class_eq_actual
        x 0 r' (le_refl 0)).symm)))

/-- Helper toward Lemma 5.5: equal-code aligned witnesses at index zero
have the full corrected-side marked isomorphism, with all relation tags. -/
theorem lPlusCodeBlockSide4_markedIso_of_presentation_codes_eq_zero
    (x : XDP) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x 0 r)
    (s' : LPlusSourceWitnessAligned x 0 r')
    (hr : r.code = r'.code) :
    Nonempty (GeometricSideMarkedIso
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft (le_refl 0))
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft (le_refl 0))) :=
  (geometricSideClass_eq_iff _ _).mp
    (lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq_zero x r r' s s' hr)

















































































end DirectedDistances.PaperProofs.Section5

/- Validation (2026-11-06): temporary in-file #print axioms probes checked
all 20 declarations above. Every result was exactly
[propext, Classical.choice, Quot.sound]. All probes were removed.
Development compile exits: 1,1,0,1,0,1,0,1,0,0,0,0,0,0.
Axiom-probe compile exit: 0. Final probe-free compile exit: 0.
was used for compilation. No separate kernel checker, cache retrieval,
remain with the sole coordinator. The general targets remain comments;
the full marked-isomorphism and class-equality results here cover index zero
only. No paper-completion claim is made. -/
