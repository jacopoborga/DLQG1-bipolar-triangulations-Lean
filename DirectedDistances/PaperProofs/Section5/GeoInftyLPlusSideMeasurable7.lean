/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable6

/-! # Glued block comparison for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Equality of carriers gives the canonical
equivalence between their subtype vertices or darts. -/
private def lPlusSetEqEquiv {α : Type*} {A B : Set α} (h : A = B) :
    {a // a ∈ A} ≃ {b // b ∈ B} where
  toFun a := ⟨a.1, h ▸ a.2⟩
  invFun b := ⟨b.1, h.symm ▸ b.2⟩
  left_inv := by intro a; apply Subtype.ext; rfl
  right_inv := by intro b; apply Subtype.ext; rfl

/-- Helper toward Lemma 5.5. A marked isomorphism restricts to an
equivalence of its vertex subtypes. -/
private theorem lPlusMarkedIsoVertexImage
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (v : M.vertices) : ∃ w : N.vertices, I.equiv (.inl v) = .inl w := by
  cases h : I.equiv (.inl v) with
  | inl w => exact ⟨w, rfl⟩
  | inr d =>
      have hrel := (I.relation_iff .vertex (.inl v) (.inl v)).mp trivial
      rw [h] at hrel
      simp [geometricSideRelation] at hrel

private theorem lPlusMarkedIsoVertexInverseImage
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (d : N.vertices) : ∃ v : M.vertices, I.equiv.symm (.inl d) = .inl v := by
  cases h : I.equiv.symm (.inl d) with
  | inl v => exact ⟨v, rfl⟩
  | inr e =>
      have hback : I.equiv (.inr e) = .inl d := by
        have hh := congrArg I.equiv h
        simpa using hh.symm
      have hsource := (I.relation_iff .vertex (.inr e) (.inr e)).mpr (by
        rw [hback]
        simp [geometricSideRelation])
      simp [geometricSideRelation] at hsource

private noncomputable def lPlusMarkedIsoVertexMap
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (v : M.vertices) : N.vertices := Classical.choose (lPlusMarkedIsoVertexImage I v)

private noncomputable def lPlusMarkedIsoVertexEquiv
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N) :
    M.vertices ≃ N.vertices := by
  let f : M.vertices → N.vertices := lPlusMarkedIsoVertexMap I
  have hf : Function.Injective f := by
    intro a b hab
    have hA := Classical.choose_spec (lPlusMarkedIsoVertexImage I a)
    have hB := Classical.choose_spec (lPlusMarkedIsoVertexImage I b)
    apply Subtype.ext
    have hh : I.equiv (.inl a) = I.equiv (.inl b) := by
      rw [hA, hB]
      exact congrArg (fun w : N.vertices => (Sum.inl w : GeometricSideCell N)) hab
    have hh' := I.equiv.injective hh
    exact congrArg Subtype.val (Sum.inl.inj hh')
  have hsurj : Function.Surjective f := by
    intro b
    refine ⟨Classical.choose (lPlusMarkedIsoVertexInverseImage I b), ?_⟩
    have hA := Classical.choose_spec (lPlusMarkedIsoVertexInverseImage I b)
    have hB := Classical.choose_spec (lPlusMarkedIsoVertexImage I
      (Classical.choose (lPlusMarkedIsoVertexInverseImage I b)))
    apply Subtype.ext
    have h1 : (Sum.inl b : GeometricSideCell N) =
        I.equiv (.inl (Classical.choose (lPlusMarkedIsoVertexInverseImage I b))) := by
      simpa only [Equiv.apply_symm_apply] using congrArg I.equiv hA
    have hh := h1.trans hB
    exact congrArg Subtype.val (Sum.inl.inj hh).symm
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

private theorem lPlusMarkedIsoVertexEquiv_spec
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (v : M.vertices) : I.equiv (.inl v) = .inl (lPlusMarkedIsoVertexEquiv I v) := by
  change I.equiv (.inl v) = .inl (lPlusMarkedIsoVertexMap I v)
  exact Classical.choose_spec (lPlusMarkedIsoVertexImage I v)

private theorem lPlusMarkedIsoDartImage
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
    ∃ e : {d : ℕ × Bool // d.1 ∈ N.edges}, I.equiv (.inr d) = .inr e := by
  cases h : I.equiv (.inr d) with
  | inl v =>
      have hsource := (I.relation_iff .vertex (.inr d) (.inr d)).mpr (by
        rw [h]
        simp [geometricSideRelation])
      simp [geometricSideRelation] at hsource
  | inr e => exact ⟨e, rfl⟩

private theorem lPlusMarkedIsoDartInverseImage
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (e : {d : ℕ × Bool // d.1 ∈ N.edges}) :
    ∃ d : {d : ℕ × Bool // d.1 ∈ M.edges}, I.equiv.symm (.inr e) = .inr d := by
  cases h : I.equiv.symm (.inr e) with
  | inl v =>
      have hback : I.equiv (.inl v) = .inr e := by
        have hh := congrArg I.equiv h
        simpa using hh.symm
      have hsource := (I.relation_iff .vertex (.inl v) (.inl v)).mp trivial
      rw [hback] at hsource
      simp [geometricSideRelation] at hsource
  | inr d => exact ⟨d, rfl⟩

private noncomputable def lPlusMarkedIsoDartMap
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
    {d : ℕ × Bool // d.1 ∈ N.edges} := Classical.choose (lPlusMarkedIsoDartImage I d)

private noncomputable def lPlusMarkedIsoDartEquiv
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N) :
    {d : ℕ × Bool // d.1 ∈ M.edges} ≃ {d : ℕ × Bool // d.1 ∈ N.edges} := by
  let f := lPlusMarkedIsoDartMap I
  have hf : Function.Injective f := by
    intro a b hab
    have hA := Classical.choose_spec (lPlusMarkedIsoDartImage I a)
    have hB := Classical.choose_spec (lPlusMarkedIsoDartImage I b)
    apply Subtype.ext
    have hh : I.equiv (.inr a) = I.equiv (.inr b) := by
      rw [hA, hB]
      exact congrArg (fun d : {d : ℕ × Bool // d.1 ∈ N.edges} =>
        (Sum.inr d : GeometricSideCell N)) hab
    have hh' := I.equiv.injective hh
    exact congrArg Subtype.val (Sum.inr.inj hh')
  have hsurj : Function.Surjective f := by
    intro b
    refine ⟨Classical.choose (lPlusMarkedIsoDartInverseImage I b), ?_⟩
    have hA := Classical.choose_spec (lPlusMarkedIsoDartInverseImage I b)
    have hB := Classical.choose_spec (lPlusMarkedIsoDartImage I
      (Classical.choose (lPlusMarkedIsoDartInverseImage I b)))
    apply Subtype.ext
    have h1 : (Sum.inr b : GeometricSideCell N) =
        I.equiv (.inr (Classical.choose (lPlusMarkedIsoDartInverseImage I b))) := by
      simpa only [Equiv.apply_symm_apply] using congrArg I.equiv hA
    have hh := h1.trans hB
    exact congrArg Subtype.val (Sum.inr.inj hh).symm
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

private theorem lPlusMarkedIsoDartEquiv_spec
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
    I.equiv (.inr d) = .inr (lPlusMarkedIsoDartEquiv I d) := by
  change I.equiv (.inr d) = .inr (lPlusMarkedIsoDartMap I d)
  exact Classical.choose_spec (lPlusMarkedIsoDartImage I d)

private theorem lPlusGeometricSideSubmap_congrDomain
    {x y : XDP} (side : ThinMapSide)
    (hxy : y = x)
    (q : selectedCutCoherentDomain y renewalTime renewalTime_positiveSuccessTime)
    (q' : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hq : hxy ▸ q = q') :
    geometricSideSubmap y renewalTime renewalTime_positiveSuccessTime side q =
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime side q' := by
  cases hxy
  cases hq
  rfl

private theorem lPlusSelectedCutDomainTransport_val
    {x y : XDP}
    (hxy : y = x)
    (q : selectedCutCoherentDomain y renewalTime renewalTime_positiveSuccessTime) :
    (hxy ▸ q).1 = q.1 := by
  cases hxy
  rfl

/-- Helper toward Lemma 5.5. Equal presentation codes determine bijections
between the three block representative families. The maps fix prefix and
primed representatives and use the aligned hatted marked isomorphism. -/
theorem lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M M')
      (fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      (∀ v : LPlusPrefixVertex s.W s.h k,
        ∃ v' : LPlusPrefixVertex s'.W s'.h k,
          fV (.inl v) = .inl v' ∧ v'.val = v.val) ∧
      (∀ v : LPlusPrimedVertex,
        fV (.inr (.inl v)) = .inr (.inl v)) ∧
      (∀ v : LPlusHattedVertex M,
        ∃ v' : LPlusHattedVertex M',
          fV (.inr (.inr v)) = .inr (.inr v') ∧
            phi.equiv (.inl v) = .inl v') ∧
      (∀ d : LPlusPrefixDart s.W s.h k,
        ∃ d' : LPlusPrefixDart s'.W s'.h k,
          fD (.inl d) = .inl d' ∧ d'.val = d.val) ∧
      (∀ d : LPlusPrimedDart,
        fD (.inr (.inl d)) = .inr (.inl d)) ∧
      (∀ d : LPlusHattedDart M,
        ∃ d' : LPlusHattedDart M',
          fD (.inr (.inr d)) = .inr (.inr d') ∧
            phi.equiv (.inr d) = .inr d') := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨phi0⟩ := lPlusSourceWitnessAligned_hatted_markedIso_of_presentation_codes_eq
    x k r r' s s' hr
  have hmodeS : (if s.longest = true then XDP.ldp else XDP.sdp) = x := by
    have hbool : (if s.longest = true then XDP.ldp else XDP.sdp) =
        (if s.longest then XDP.ldp else XDP.sdp) := by
      cases s.longest <;> rfl
    exact hbool.trans s.hmode
  have hmodeS' : (if s'.longest = true then XDP.ldp else XDP.sdp) = x := by
    have hbool : (if s'.longest = true then XDP.ldp else XDP.sdp) =
        (if s'.longest then XDP.ldp else XDP.sdp) := by
      cases s'.longest <;> rfl
    exact hbool.trans s'.hmode
  let qS : selectedCutCoherentDomain (if s.longest = true then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩
  let qX : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k s.W, s.hattedPath_mem⟩
  have hqTransport : hmodeS ▸ qS = qX := by
    apply Subtype.ext
    simpa [qS, qX] using lPlusSelectedCutDomainTransport_val hmodeS qS
  have hsideS : M = geometricSideSubmap x renewalTime
      renewalTime_positiveSuccessTime .left qX := by
    change geometricSideSubmap (if s.longest = true then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime .left qS = _
    exact lPlusGeometricSideSubmap_congrDomain .left hmodeS qS qX hqTransport
  let qS' : selectedCutCoherentDomain (if s'.longest = true then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k s'.W, s'.hqMode⟩
  let qX' : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k s'.W, s'.hattedPath_mem⟩
  have hqTransport' : hmodeS' ▸ qS' = qX' := by
    apply Subtype.ext
    simpa [qS', qX'] using lPlusSelectedCutDomainTransport_val hmodeS' qS'
  have hsideS' : M' = geometricSideSubmap x renewalTime
      renewalTime_positiveSuccessTime .left qX' := by
    change geometricSideSubmap (if s'.longest = true then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime .left qS' = _
    exact lPlusGeometricSideSubmap_congrDomain .left hmodeS' qS' qX' hqTransport'
  have phi : GeometricSideMarkedIso M M' := by
    simpa only [hsideS, hsideS'] using phi0
  let preV : LPlusPrefixVertex s.W s.h k ≃ LPlusPrefixVertex s'.W s'.h k :=
    lPlusSetEqEquiv (lPlusSourceWitnessAligned_prefixVertices_eq_of_presentation_codes_eq
      x k r r' s s' hk hr)
  have hpreE := lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
    x k r r' s s' hk hr
  have hpreD : {d : ℕ × Bool | d.1 ∈ boundaryGluingPrefixMinusEdges s.W s.h k} =
      {d : ℕ × Bool | d.1 ∈ boundaryGluingPrefixMinusEdges s'.W s'.h k} := by
    ext d
    simp only [Set.mem_ofPred_eq]
    rw [hpreE]
  let preD : LPlusPrefixDart s.W s.h k ≃ LPlusPrefixDart s'.W s'.h k :=
    lPlusSetEqEquiv hpreD
  let hatV := lPlusMarkedIsoVertexEquiv phi
  let hatD := lPlusMarkedIsoDartEquiv phi
  let fV : LPlusBlockVertex s.W s.h k M ≃ LPlusBlockVertex s'.W s'.h k M' :=
    Equiv.sumCongr preV (Equiv.sumCongr (Equiv.refl _) hatV)
  let fD : LPlusBlockDart s.W s.h k M ≃ LPlusBlockDart s'.W s'.h k M' :=
    Equiv.sumCongr preD (Equiv.sumCongr (Equiv.refl _) hatD)
  refine ⟨phi, fV, fD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨preV v, rfl, rfl⟩
  · intro v
    rfl
  · intro v
    exact ⟨hatV v, rfl, lPlusMarkedIsoVertexEquiv_spec phi v⟩
  · intro d
    exact ⟨preD d, rfl, rfl⟩
  · intro d
    rfl
  · intro d
    exact ⟨hatD d, rfl, lPlusMarkedIsoDartEquiv_spec phi d⟩


























































end DirectedDistances.PaperProofs.Section5
