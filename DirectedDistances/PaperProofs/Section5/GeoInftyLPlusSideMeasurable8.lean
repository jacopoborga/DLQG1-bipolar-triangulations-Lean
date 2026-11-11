/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable7

/-! # Kernel transport for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. A marked isomorphism carries each indexed
boundary dart to the dart with the same boundary index. -/
theorem lPlusMarkedIso_boundaryDart
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (i : ℕ) (hM : (M.boundary i).1 ∈ M.edges)
    (hN : (N.boundary i).1 ∈ N.edges) :
    phi.equiv (.inr ⟨M.boundary i, hM⟩) =
      .inr ⟨N.boundary i, hN⟩ := by
  let dM : {d : ℕ × Bool // d.1 ∈ M.edges} := ⟨M.boundary i, hM⟩
  let dN : {d : ℕ × Bool // d.1 ∈ N.edges} := ⟨N.boundary i, hN⟩
  have hrel : geometricSideRelation M (.boundary i) (.inr dM) (.inr dM) := by
    simp [geometricSideRelation, dM]
  have hrel' := (phi.relation_iff (.boundary i) (.inr dM) (.inr dM)).mp hrel
  cases h : phi.equiv (.inr dM) with
  | inl v => simp [geometricSideRelation, h] at hrel'
  | inr e =>
      rw [h] at hrel'
      simp [geometricSideRelation] at hrel'
      have he : e.val = N.boundary i := by
        exact hrel'.symm
      apply congrArg Sum.inr
      exact Subtype.ext he

/-- Helper toward Lemma 5.5. The isomorphism carries the opposite dart of an
indexed boundary edge to the opposite dart of the corresponding edge. -/
theorem lPlusMarkedIso_oppositeBoundaryDart
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (i : ℕ) (hM : (M.boundary i).1 ∈ M.edges)
    (hN : (N.boundary i).1 ∈ N.edges) :
    phi.equiv (.inr ⟨((M.boundary i).1, !(M.boundary i).2), hM⟩) =
      .inr ⟨((N.boundary i).1, !(N.boundary i).2), hN⟩ := by
  let dM : {d : ℕ × Bool // d.1 ∈ M.edges} := ⟨M.boundary i, hM⟩
  let dN : {d : ℕ × Bool // d.1 ∈ N.edges} := ⟨N.boundary i, hN⟩
  let dMopp : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((M.boundary i).1, !(M.boundary i).2), hM⟩
  let dNopp : {d : ℕ × Bool // d.1 ∈ N.edges} :=
    ⟨((N.boundary i).1, !(N.boundary i).2), hN⟩
  have hbase : phi.equiv (.inr dM) = .inr dN :=
    lPlusMarkedIso_boundaryDart phi i hM hN
  have hrel : geometricSideRelation M .opposite (.inr dM) (.inr dMopp) := by
    simp [geometricSideRelation, dM, dMopp]
  have hrel' := (phi.relation_iff .opposite (.inr dM) (.inr dMopp)).mp hrel
  rw [hbase] at hrel'
  cases h : phi.equiv (.inr dMopp) with
  | inl v => simp [geometricSideRelation, h] at hrel'
  | inr e =>
      rw [h] at hrel'
      simp [geometricSideRelation, dN] at hrel'
      have he : e.val = dNopp.val := hrel'.symm
      apply congrArg Sum.inr
      exact Subtype.ext he

/-- Helper toward Lemma 5.5. The indexed boundary dart of an aligned L+ hatted
side belongs to its geometric carrier. -/
theorem lPlusSourceWitnessAligned_hattedBoundary_mem
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (i : ℕ) :
    ((lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode).boundary i).1 ∈
    (lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode).edges := by
  let mode := if s.longest then XDP.ldp else XDP.sdp
  let q : selectedCutCoherentDomain mode renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩
  simpa [lPlusHattedSide, mode, q] using lMinus_hatted_boundary_mem mode q i

/-- Helper toward Lemma 5.5. The marked isomorphism selected from aligned
equal-code witnesses transports each indexed hatted boundary dart. -/
theorem lPlusSourceWitnessAligned_hattedBoundaryDart_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (i : ℕ) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M M'),
      phi.equiv (.inr ⟨M.boundary i,
        lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i⟩) =
      .inr ⟨M'.boundary i,
        lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i⟩ := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨phi, fV, fD, hprefixV, hprimedV, hhattedV,
      hprefixD, hprimedD, hhattedD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨phi, ?_⟩
  exact lPlusMarkedIso_boundaryDart phi i
    (lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i)
    (lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i)

/-- Helper toward Lemma 5.5. The representative equivalence preserves the
kernel relation when both representatives lie in the hatted vertex block.
The proof uses injectivity of each hatted embedding and injectivity of the
block equivalence; it does not assume compatibility between the two ambient
embeddings. -/
theorem lPlusSourceWitnessAligned_hattedVertexKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (_phi : GeometricSideMarkedIso M M')
      (fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (_fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      ∀ a b : LPlusHattedVertex M,
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr a)) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ
            (fV (.inr (.inr a))) =
          lPlusBlockVertexImage (M := M') s'.hτ
            (fV (.inr (.inr b))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨_phi, fV, _fD, hprefixV, hprimedV, hhattedV,
      hprefixD, hprimedD, hhattedD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨_phi, fV, _fD, ?_⟩
  intro a b
  obtain ⟨a', ha', _⟩ := hhattedV a
  obtain ⟨b', hb', _⟩ := hhattedV b
  have hrep : fV (.inr (.inr a)) = fV (.inr (.inr b)) ↔ a = b := by
    constructor
    · intro hab
      exact Sum.inr.inj (Sum.inr.inj (fV.injective hab))
    · intro hab
      subst b
      rfl
  rw [ha', hb'] at hrep
  simp only [Sum.inr.injEq] at hrep
  have hinj : Function.Injective (fun v : LPlusHattedVertex M =>
      lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr v))) :=
    lPlusHattedVertexImage_injective s.hτ s.hqMode
  have hinj' : Function.Injective (fun v : LPlusHattedVertex M' =>
      lPlusBlockVertexImage (M := M') s'.hτ (.inr (.inr v))) :=
    lPlusHattedVertexImage_injective s'.hτ s'.hqMode
  calc
    lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr a)) =
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔ a = b :=
      hinj.eq_iff
    _ ↔ a' = b' := hrep.symm
    _ ↔ lPlusBlockVertexImage (M := M') s'.hτ (.inr (.inr a')) =
        lPlusBlockVertexImage (M := M') s'.hτ (.inr (.inr b')) :=
      hinj'.eq_iff.symm
    _ ↔ lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr a))) =
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr b))) := by
      simp only [ha', hb']

/-- Helper toward Lemma 5.5. The same representative equivalence preserves
the kernel relation within the stopped-prefix and primed vertex components. -/
theorem lPlusSourceWitnessAligned_prefixPrimedVertexKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (_phi : GeometricSideMarkedIso M M')
      (fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (_fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      (∀ a b : LPlusPrefixVertex s.W s.h k,
        lPlusBlockVertexImage (M := M) s.hτ (.inl a) =
          lPlusBlockVertexImage (M := M) s.hτ (.inl b) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl b))) ∧
      (∀ a b : LPlusPrimedVertex,
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl a))) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl b)))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨_phi, fV, _fD, hprefixV, hprimedV, hhattedV,
      hprefixD, hprimedD, hhattedD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨_phi, fV, _fD, ?_, ?_⟩
  · intro a b
    obtain ⟨a', ha', hvalA⟩ := hprefixV a
    obtain ⟨b', hb', hvalB⟩ := hprefixV b
    change a.val = b.val ↔
      lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl b))
    rw [ha', hb']
    change a.val = b.val ↔ a'.val = b'.val
    constructor
    · intro hab
      calc
        a'.val = a.val := hvalA
        _ = b.val := hab
        _ = b'.val := hvalB.symm
    · intro hab
      calc
        a.val = a'.val := hvalA.symm
        _ = b'.val := hab
        _ = b.val := hvalB
  · intro a b
    have hinj : Function.Injective (fun v : LPlusPrimedVertex =>
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl v))) :=
      lPlusPrimedVertexImage_injective s.hτ s.hqMode
    have hinj' : Function.Injective (fun v : LPlusPrimedVertex =>
        lPlusBlockVertexImage (M := M') s'.hτ (.inr (.inl v))) :=
      lPlusPrimedVertexImage_injective s'.hτ s'.hqMode
    calc
      lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl b)) ↔ a = b :=
        hinj.eq_iff
      _ ↔ lPlusBlockVertexImage (M := M') s'.hτ
            (fV (.inr (.inl a))) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl b))) := by
        rw [hprimedV a, hprimedV b]
        exact hinj'.eq_iff.symm

/-- Helper toward Lemma 5.5. The representative equivalence preserves the
kernel relation within each of the three dart components. -/
theorem lPlusSourceWitnessAligned_componentDartKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (_phi : GeometricSideMarkedIso M M')
      (_fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      (∀ a b : LPlusPrefixDart s.W s.h k,
        lPlusBlockDartImage (M := M) s.hτ (.inl a) =
          lPlusBlockDartImage (M := M) s.hτ (.inl b) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inl b))) ∧
      (∀ a b : LPlusPrimedDart,
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl b)))) ∧
      (∀ a b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inr a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b)))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨_phi, _fV, fD, hprefixV, hprimedV, hhattedV,
      hprefixD, hprimedD, hhattedD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨_phi, _fV, fD, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨a', ha', hvalA⟩ := hprefixD a
    obtain ⟨b', hb', hvalB⟩ := hprefixD b
    change a.val = b.val ↔
      lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl b))
    rw [ha', hb']
    change a.val = b.val ↔ a'.val = b'.val
    constructor
    · intro hab
      calc
        a'.val = a.val := hvalA
        _ = b.val := hab
        _ = b'.val := hvalB.symm
    · intro hab
      calc
        a.val = a'.val := hvalA.symm
        _ = b'.val := hab
        _ = b.val := hvalB
  · intro a b
    have hinj : Function.Injective (fun d : LPlusPrimedDart =>
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inl d))) :=
      lPlusPrimedDartImage_injective s.hτ s.hqMode
    have hinj' : Function.Injective (fun d : LPlusPrimedDart =>
        lPlusBlockDartImage (M := M') s'.hτ (.inr (.inl d))) :=
      lPlusPrimedDartImage_injective s'.hτ s'.hqMode
    calc
      lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inl b)) ↔ a = b :=
        hinj.eq_iff
      _ ↔ lPlusBlockDartImage (M := M') s'.hτ
            (fD (.inr (.inl a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl b))) := by
        rw [hprimedD a, hprimedD b]
        exact hinj'.eq_iff.symm
  · intro a b
    obtain ⟨a', ha', _⟩ := hhattedD a
    obtain ⟨b', hb', _⟩ := hhattedD b
    have hrep : fD (.inr (.inr a)) = fD (.inr (.inr b)) ↔ a = b := by
      constructor
      · intro hab
        exact Sum.inr.inj (Sum.inr.inj (fD.injective hab))
      · intro hab
        subst b
        rfl
    rw [ha', hb'] at hrep
    simp only [Sum.inr.injEq] at hrep
    have hinj : Function.Injective (fun d : LPlusHattedDart M =>
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inr d))) :=
      lPlusHattedDartImage_injective s.hτ s.hqMode
    have hinj' : Function.Injective (fun d : LPlusHattedDart M' =>
        lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr d))) :=
      lPlusHattedDartImage_injective s'.hτ s'.hqMode
    calc
      lPlusBlockDartImage (M := M) s.hτ (.inr (.inr a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔ a = b :=
        hinj.eq_iff
      _ ↔ a' = b' := hrep.symm
      _ ↔ lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr a')) =
          lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr b')) :=
        hinj'.eq_iff.symm
      _ ↔ lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b))) := by
        simp only [ha', hb']

/-- Helper toward Lemma 5.5. Prefix and hatted darts never collapse under
either aligned witness, so this mixed component case needs no comparison of
their ambient embeddings. At index zero the prefix dart carrier is empty. -/
theorem lPlusSourceWitnessAligned_prefixHattedDartKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (_phi : GeometricSideMarkedIso M M')
      (_fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      ∀ a : LPlusPrefixDart s.W s.h k,
        ∀ b : LPlusHattedDart M,
          lPlusBlockDartImage (M := M) s.hτ (.inl a) =
              lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
            lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
              lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨_phi, _fV, fD, hprefixV, hprimedV, hhattedV,
      hprefixD, hprimedD, hhattedD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨_phi, _fV, fD, ?_⟩
  intro a b
  by_cases hkpos : 0 < k
  · obtain ⟨a', ha', _⟩ := hprefixD a
    obtain ⟨b', hb', _⟩ := hhattedD b
    have hsrc := lPlusPrefixHattedGluedDart_ne
      (hτ := s.hτ) (hqMode := s.hqMode) (hk := hkpos) a b
    have htgt := lPlusPrefixHattedGluedDart_ne
      (hτ := s'.hτ) (hqMode := s'.hqMode) (hk := hkpos) a' b'
    have hsrc' : ¬ lPlusBlockDartImage (M := M) s.hτ (.inl a) =
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) := by
      intro heq
      exact hsrc (Quotient.sound heq)
    have htgt' : ¬ lPlusBlockDartImage (M := M') s'.hτ (.inl a') =
        lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr b')) := by
      intro heq
      exact htgt (Quotient.sound heq)
    rw [ha', hb']
    exact ⟨hsrc'.elim, htgt'.elim⟩
  · have hkzero : k = 0 := by omega
    subst k
    rcases a with ⟨d, hd⟩
    have hd0 : d.1 ∈ boundaryGluingPrefixMinusEdges s.W s.h 0 := hd
    rw [boundaryGluingPrefixMinusEdges_zero] at hd0
    simp at hd0

















































































end DirectedDistances.PaperProofs.Section5
