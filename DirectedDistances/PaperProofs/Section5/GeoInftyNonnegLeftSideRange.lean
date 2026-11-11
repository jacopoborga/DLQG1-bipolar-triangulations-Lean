/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSidePrefix




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the three block dart images cover all darts of
the geometric nonnegative left side, retaining both endpoint bits of every
edge, including missing edges. -/
theorem lPlusBlockDartImage_range
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ}
    {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 < k) :
    Set.range (fun d : LPlusBlockDart W h k
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) =>
        lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ d) =
      {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P .left).edges} := by
  have hside := (boundaryGluing_nonneg_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft (by omega : 0 ≤ k)).2
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with a | a
    · rw [hside]
      exact Set.mem_union_left _ (Set.mem_union_left _ a.property)
    · rcases a with a | a
      · rw [hside]
        exact Set.mem_union_right _ ⟨a.1, rfl⟩
      · rw [hside]
        exact Set.mem_union_left _ (Set.mem_union_right _
          ⟨a.val.1, a.property, rfl⟩)
  · intro hd
    rw [hside] at hd
    rcases hd with ((hpref | hhat) | hprimed)
    · exact ⟨Sum.inl ⟨d, hpref⟩, rfl⟩
    · rcases hhat with ⟨e, he, hmap⟩
      refine ⟨Sum.inr (Sum.inr ⟨(e, d.2), he⟩), ?_⟩
      change (boundaryGluingHatEdgeMap W h k hτ e, d.2) = d
      exact Prod.ext hmap rfl
    · obtain ⟨e, hmap⟩ := hprimed
      refine ⟨Sum.inr (Sum.inl (e, d.2 ^^
        primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e)), ?_⟩
      change (boundaryGluingPrimedEdgeMap W h k hτ e,
        (d.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e) ^^
          primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e) = d
      apply Prod.ext hmap
      cases d.2 <;>
        cases primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e <;> rfl
















































end DirectedDistances.PaperProofs.Section5
