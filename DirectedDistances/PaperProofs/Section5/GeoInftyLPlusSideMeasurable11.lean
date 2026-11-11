/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable10

/-! # Boundary endpoint transport for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. A marked isomorphism carrying a dart also carries
its incident endpoint, with the endpoint selected by the dart orientation. -/
theorem lPlusMarkedIso_dartEndpoint
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    {dM : {d : ℕ × Bool // d.1 ∈ M.edges}}
    {dN : {d : ℕ × Bool // d.1 ∈ N.edges}}
    (hd : phi.equiv (.inr dM) = .inr dN)
    (hM : (if dM.val.2 then M.east dM.val.1 else M.west dM.val.1) ∈ M.vertices)
    (hN : (if dN.val.2 then N.east dN.val.1 else N.west dN.val.1) ∈ N.vertices) :
    phi.equiv (.inl ⟨if dM.val.2 then M.east dM.val.1 else M.west dM.val.1, hM⟩) =
      .inl ⟨if dN.val.2 then N.east dN.val.1 else N.west dN.val.1, hN⟩ := by
  let vM : {v : ℕ // v ∈ M.vertices} :=
    ⟨if dM.val.2 then M.east dM.val.1 else M.west dM.val.1, hM⟩
  let vN : {v : ℕ // v ∈ N.vertices} :=
    ⟨if dN.val.2 then N.east dN.val.1 else N.west dN.val.1, hN⟩
  have hincident : geometricSideRelation M .incident (.inr dM) (.inl vM) := by
    simp [geometricSideRelation, vM]
  have hincident' :=
    (phi.relation_iff .incident (.inr dM) (.inl vM)).mp hincident
  rw [hd] at hincident'
  cases h : phi.equiv (.inl vM) with
  | inl v =>
      rw [h] at hincident'
      have hvalue : v.val = vN.val := by
        change vN.val = v.val at hincident'
        exact hincident'.symm
      apply congrArg Sum.inl
      exact Subtype.ext hvalue
  | inr d =>
      rw [h] at hincident'
      simp only [geometricSideRelation] at hincident'

/-- Helper toward Lemma 5.5. The prefix and hatted dart kernel comparison is
vacuous: these two components have no shared geometric edge. -/
theorem lPlusSourceWitnessAligned_prefixHattedDartCrossKernel_iff
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
  exact lPlusSourceWitnessAligned_prefixHattedDartKernel_iff
    x k r r' s s' hk hr

/-- Helper toward Lemma 5.5. The indexed hatted boundary dart transports its
incident endpoint under the witness-aligned marked isomorphism. -/
theorem lPlusSourceWitnessAligned_hattedBoundaryEndpoint_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (i : ℕ)
    (hM : (if ((lPlusHattedSide (W := s.W) (h := s.h) (k := k)
        s.longest s.hqMode).boundary i).2 then
          (lPlusHattedSide (W := s.W) (h := s.h) (k := k)
            s.longest s.hqMode).east
              ((lPlusHattedSide (W := s.W) (h := s.h) (k := k)
                s.longest s.hqMode).boundary i).1
        else
          (lPlusHattedSide (W := s.W) (h := s.h) (k := k)
            s.longest s.hqMode).west
              ((lPlusHattedSide (W := s.W) (h := s.h) (k := k)
                s.longest s.hqMode).boundary i).1) ∈
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k)
          s.longest s.hqMode).vertices)
    (hM' : (if ((lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
        s'.longest s'.hqMode).boundary i).2 then
          (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
            s'.longest s'.hqMode).east
              ((lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
                s'.longest s'.hqMode).boundary i).1
        else
          (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
            s'.longest s'.hqMode).west
              ((lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
                s'.longest s'.hqMode).boundary i).1) ∈
        (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
          s'.longest s'.hqMode).vertices) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ phi : GeometricSideMarkedIso M M',
      phi.equiv (.inl ⟨if (M.boundary i).2 then M.east (M.boundary i).1
        else M.west (M.boundary i).1, hM⟩) =
        .inl ⟨if (M'.boundary i).2 then M'.east (M'.boundary i).1
          else M'.west (M'.boundary i).1, hM'⟩ := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
    s.longest s.hqMode
  let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
    s'.longest s'.hqMode
  obtain ⟨phi, hboundary, _hopposite⟩ :=
    lPlusSourceWitnessAligned_hattedBoundaryDarts_eq x k r r' s s' hk hr i
  refine ⟨phi, ?_⟩
  exact lPlusMarkedIso_dartEndpoint phi hboundary hM hM'






































































































































end DirectedDistances.PaperProofs.Section5
