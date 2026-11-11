/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable8

/-! # Cross-witness boundary compatibility for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),

The same-component vertex and dart kernel equivalences are available from
`GeoInftyLPlusSideMeasurable8`. The remaining cross-component cases reduce to
identifying the primed and hatted whole-plane embeddings on their shared
boundary for two distinct aligned witnesses. No such identification is
assumed here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The prefix-vertex kernel quotients agree when
restricted to their common stopped-prefix vertex carrier. -/
noncomputable def lPlusSourceWitnessAligned_prefixVertexQuotientEquiv_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    Quotient (Setoid.ker (fun v : LPlusPrefixVertex s.W s.h k =>
      lPlusBlockVertexImage (M := M) s.hτ (.inl v))) ≃
    Quotient (Setoid.ker (fun v : LPlusPrefixVertex s'.W s'.h k =>
      lPlusBlockVertexImage (M := M') s'.hτ (.inl v))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  let f : LPlusPrefixVertex s.W s.h k → ℕ := fun v =>
    lPlusBlockVertexImage (M := M) s.hτ (.inl v)
  let g : LPlusPrefixVertex s'.W s'.h k → ℕ := fun v =>
    lPlusBlockVertexImage (M := M') s'.hτ (.inl v)
  have hvertices :=
    lPlusSourceWitnessAligned_prefixVertices_eq_of_presentation_codes_eq
      x k r r' s s' hk hr
  have hrange : Set.range f = Set.range g := by
    ext n
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨v.val, ?_⟩, rfl⟩
      rw [← hvertices]
      exact v.property
    · rintro ⟨v, rfl⟩
      refine ⟨⟨v.val, ?_⟩, rfl⟩
      rw [hvertices]
      exact v.property
  exact (Setoid.quotientKerEquivRange f).trans
    ((Set.equivOfEq hrange).trans (Setoid.quotientKerEquivRange g).symm)

/-- Helper toward Lemma 5.5. The prefix-dart kernel quotients agree when
restricted to their common stopped-prefix dart carrier. -/
noncomputable def lPlusSourceWitnessAligned_prefixDartQuotientEquiv_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    Quotient (Setoid.ker (fun d : LPlusPrefixDart s.W s.h k =>
      lPlusBlockDartImage (M := M) s.hτ (.inl d))) ≃
    Quotient (Setoid.ker (fun d : LPlusPrefixDart s'.W s'.h k =>
      lPlusBlockDartImage (M := M') s'.hτ (.inl d))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  let f : LPlusPrefixDart s.W s.h k → ℕ × Bool := fun d =>
    lPlusBlockDartImage (M := M) s.hτ (.inl d)
  let g : LPlusPrefixDart s'.W s'.h k → ℕ × Bool := fun d =>
    lPlusBlockDartImage (M := M') s'.hτ (.inl d)
  have hedges :=
    lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
      x k r r' s s' hk hr
  have hrange : Set.range f = Set.range g := by
    ext d
    constructor
    · rintro ⟨e, rfl⟩
      refine ⟨⟨e.val, ?_⟩, rfl⟩
      rw [← hedges]
      exact e.property
    · rintro ⟨e, rfl⟩
      refine ⟨⟨e.val, ?_⟩, rfl⟩
      rw [hedges]
      exact e.property
  exact (Setoid.quotientKerEquivRange f).trans
    ((Set.equivOfEq hrange).trans (Setoid.quotientKerEquivRange g).symm)




/- theorem lPlusSourceWitnessAligned_crossComponentKernelCompatibility
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
      (∀ a : LPlusPrefixVertex s.W s.h k, ∀ b : LPlusPrimedVertex,
        lPlusBlockVertexImage (M := M) s.hτ (.inl a) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl b)))) ∧
      (∀ a : LPlusPrefixVertex s.W s.h k, ∀ b : LPlusHattedVertex M,
        lPlusBlockVertexImage (M := M) s.hτ (.inl a) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr b)))) ∧
      (∀ a : LPlusPrimedVertex, ∀ b : LPlusHattedVertex M,
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl a))) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr b)))) ∧
      (∀ a : LPlusPrefixDart s.W s.h k, ∀ b : LPlusPrimedDart,
        lPlusBlockDartImage (M := M) s.hτ (.inl a) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl b)))) ∧
      (∀ a : LPlusPrefixDart s.W s.h k, ∀ b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inl a) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b)))) ∧
      (∀ a : LPlusPrimedDart, ∀ b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b)))) -/























































































end DirectedDistances.PaperProofs.Section5
