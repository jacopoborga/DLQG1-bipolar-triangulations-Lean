/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotation

/-! Helper toward Lemma 5.5: nonnegative left-side rotation transport. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "F" => lPlusBlockDartImage (M := MH) hτ
local notation "Q" => LPlusGluedDart longest hqMode hτ

include Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the block images cover every retained dart also
at zero, where the deleted prefix has no darts. -/
theorem lPlusBlockDartImage_range_nonneg :
    Set.range (F : LPlusBlockDart W h k MH → ℕ × Bool) =
      {d : ℕ × Bool | d.1 ∈ (S).edges} := by
  have hside := (boundaryGluing_nonneg_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).2
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

/-- Helper toward Lemma 5.5: the geometric dart equivalence on the complete
nonnegative domain. The earlier equivalence requires strictly positive k. -/
@[expose] noncomputable def lPlusGluedDartEquivNonneg :
    Q ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} :=
  (Setoid.quotientKerEquivRange F).trans
    (Set.equivOfEq (lPlusBlockDartImage_range_nonneg
      hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: the nonnegative equivalence preserves the
geometric image of each block representative, including its endpoint bit. -/
theorem lPlusGluedDartEquivNonneg_mk (d : LPlusBlockDart W h k MH) :
    (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk ⟦d⟧).val = F d :=
  rfl

/-- Helper toward Lemma 5.5: on positive indices the extended equivalence
agrees with the existing geometric equivalence on every quotient dart. -/
theorem lPlusGluedDartEquivNonneg_eq (hkpos : 0 < k) (d : Q) :
    lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d =
      lPlusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hkpos d := by
  induction d using Quotient.inductionOn with
  | h d => rfl

/-- Helper toward Lemma 5.5: the three block vertex images cover the
geometric nonnegative left side, including its attachment root at zero. -/
theorem lPlusBlockVertexImage_range :
    Set.range (lPlusBlockVertexImage (M := MH) hτ) = (S).vertices := by
  rw [boundaryGluing_nonneg_left_vertices hτ hp P hqMode Tpath hfin hleft hk]
  ext v
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact Or.inl (Or.inl ⟨a.val, a.property, rfl⟩)
    · rcases a with a | a
      · exact Or.inr ⟨a, Set.mem_univ _, rfl⟩
      · exact Or.inl (Or.inr ⟨a.val, a.property, rfl⟩)
  · rintro ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, _, rfl⟩)
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨a, ha⟩), rfl⟩
    · exact ⟨Sum.inr (Sum.inl a), rfl⟩

/-- Helper toward Lemma 5.5: the glued vertex quotient preserves the
actual vertex carrier for every nonnegative index. -/
@[expose] noncomputable def lPlusGluedVertexEquiv :
    LPlusGluedVertex longest hqMode hτ ≃ (S).vertices :=
  (Setoid.quotientKerEquivRange (lPlusBlockVertexImage (M := MH) hτ)).trans
    (Set.equivOfEq (lPlusBlockVertexImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: the cell equivalence includes every vertex
and dart branch for every nonnegative index. Rotation transport is separate. -/
@[expose] noncomputable def lPlusGluedCellEquiv :
    Sum (LPlusGluedVertex longest hqMode hτ) Q ≃ GeometricSideCell (S) :=
  Equiv.sumCongr (lPlusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk)






































































end DirectedDistances.PaperProofs.Section5
