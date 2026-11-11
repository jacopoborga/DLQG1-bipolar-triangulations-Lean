/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable9

/-! # Shared hatted boundary transport for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The witness-aligned marked isomorphism carries
both orientations of each indexed hatted boundary edge to the same indexed
edge for the second witness. -/
theorem lPlusSourceWitnessAligned_hattedBoundaryDarts_eq
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
            lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i⟩ ∧
      phi.equiv (.inr ⟨((M.boundary i).1, !(M.boundary i).2),
        lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i⟩) =
          .inr ⟨((M'.boundary i).1, !(M'.boundary i).2),
            lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i⟩ := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨phi, hboundary⟩ :=
    lPlusSourceWitnessAligned_hattedBoundaryDart_eq x k r r' s s' hk hr i
  refine ⟨phi, hboundary, ?_⟩
  exact lPlusMarkedIso_oppositeBoundaryDart phi i
    (lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i)
    (lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i)

/-- Helper toward Lemma 5.5. For nonnegative `k`, the stopped-prefix and
hatted dart images have no shared edge under either aligned witness. -/
theorem lPlusSourceWitnessAligned_prefixHattedDartImage_ne
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    (∀ a : LPlusPrefixDart s.W s.h k, ∀ b : LPlusHattedDart M,
      lPlusBlockDartImage (M := M) s.hτ (.inl a) ≠
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b))) ∧
    (∀ a : LPlusPrefixDart s'.W s'.h k, ∀ b : LPlusHattedDart M',
      lPlusBlockDartImage (M := M') s'.hτ (.inl a) ≠
        lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr b))) := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  refine ⟨?_, ?_⟩
  · intro a b heq
    by_cases hkpos : 0 < k
    · exact lPlusPrefixHattedGluedDart_ne
        (hτ := s.hτ) (hqMode := s.hqMode) (hk := hkpos) a b
        (Quotient.sound heq)
    · have hkzero : k = 0 := by omega
      subst k
      rcases a with ⟨d, hd⟩
      rw [boundaryGluingPrefixMinusEdges_zero] at hd
      simp at hd
  · intro a b heq
    by_cases hkpos : 0 < k
    · exact lPlusPrefixHattedGluedDart_ne
        (hτ := s'.hτ) (hqMode := s'.hqMode) (hk := hkpos) a b
        (Quotient.sound heq)
    · have hkzero : k = 0 := by omega
      subst k
      rcases a with ⟨d, hd⟩
      rw [boundaryGluingPrefixMinusEdges_zero] at hd
      simp at hd












end DirectedDistances.PaperProofs.Section5
