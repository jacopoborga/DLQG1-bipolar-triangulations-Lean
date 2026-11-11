/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso8

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

The fixed-witness code-block side already carries corrected rotation 2.
Its exterior boundary, root, seam, and retained-face relation are the actual
side's fields. This file assembles the available relation comparisons; it
makes no numbered paper completion claim. -/

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
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "B" => lPlusCodeBlockSide hτ hp P hqMode Tpath hfin hleft hk
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "C" => lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
local notation "E" => lPlusActualCodeBlockCellEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "F" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
local notation "BV" => (Set.ofPred fun v : ℕ => ∃ e : ℕ,
  e ∈ boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingBetaEdges W h k hτ ∧
    (kmswLimitDartVertex (shiftedStream W 0) (e, false) = v ∨
      kmswLimitDartVertex (shiftedStream W 0) (e, true) = v))

/-- Helper toward Lemma 5.5: every tag except rotation is preserved by the
fixed-ID cell equivalence, including the exterior boundary and retained faces. -/
theorem lPlusActualCodeBlockCellEquiv_relation_iff_of_ne_rotation
    (t : TruncationRelation) (ht : t ≠ .rotation)
    (u v : GeometricSideCell S) :
    geometricSideRelation S t u v ↔ geometricSideRelation B t (E u) (E v) := by
  cases t <;> cases u <;> cases v <;>
    first | exact False.elim (ht rfl) | rfl

/-- Helper toward Lemma 5.5: on geometric images of glued darts, the
code-block rotation relation is exactly equality under corrected rotation 2. -/
theorem lPlusCodeBlockSide_rotation_glued_iff (d e : Q) :
    (B).rotation (D d).val (D e).val ↔ C d = e := by
  change (∃ a b : Q, (D a).val = (D d).val ∧ C a = b ∧
    (D b).val = (D e).val) ↔ C d = e
  constructor
  · rintro ⟨a, b, ha, hab, hb⟩
    have had : a = d := (D).injective (Subtype.ext ha)
    have hbe : b = e := (D).injective (Subtype.ext hb)
    exact had ▸ hbe ▸ hab
  · intro hde
    exact ⟨d, e, rfl, hde, rfl⟩

/-- Helper toward Lemma 5.5: the least positive code return transports the
actual-side rotation on every glued dart, without a block-rotation premise. -/
theorem lPlusGluedCodeReturn_rotation_iff (d e : Q) :
    lPlusGluedCodeReturn (H := H) hτ hqMode d = e ↔
      (S).rotation (D d).val (D e).val := by
  have hr : (S).rotation (D d).val
      (D (lPlusGluedCodeReturn (H := H) hτ hqMode d)).val := by
    obtain ⟨n, hn, hend, hgap⟩ :=
      lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d
    refine ⟨n, hn, hend, ?_⟩
    intro j hj hjn hs
    apply hgap j hj hjn
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  constructor
  · rintro rfl
    exact hr
  · intro he
    apply (D).injective
    apply Subtype.ext
    exact firstReturn_endpoint_unique
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
      {a : ℕ × Bool | a.1 ∈ (S).edges}
      (D (lPlusGluedCodeReturn (H := H) hτ hqMode d)).property (D e).property hr he

/-- Helper toward Lemma 5.5: the complete upper-left first-return theorem
also gives the rotation iff for every attachment dart and every output. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_rotation_iff
    (i : Fin (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length)
    (b : Bool) (e : Q) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
    C d = e ↔ (S).rotation (D d).val (D e).val := by
  dsimp only
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
  have hr : (S).rotation (D d).val (D (C d)).val := by
    obtain ⟨n, hn, hend, hgap⟩ :=
      lPlusGluedCorrectedRotation2_upperLeft_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk i b
    refine ⟨n, hn, hend, ?_⟩
    intro j hj hjn hs
    apply hgap j hj hjn
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  constructor
  · rintro rfl
    exact hr
  · intro he
    apply (D).injective
    apply Subtype.ext
    exact firstReturn_endpoint_unique
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
      {a : ℕ × Bool | a.1 ∈ (S).edges}
      (D (C d)).property (D e).property hr he

/-- Helper toward Lemma 5.5: rotation is preserved on the entire initial
root star by the fixed-ID cell equivalence. -/
theorem lPlusActualCodeBlockCellEquiv_rotation_iff_initial_vertex
    (d e : {d : ℕ × Bool // d.1 ∈ (S).edges})
    (hd : kmswLimitDartVertex (shiftedStream W 0) d.val =
      boundaryVertex (shiftedStream W 0) h k) :
    geometricSideRelation S .rotation (.inr d) (.inr e) ↔
      geometricSideRelation B .rotation (E (.inr d)) (E (.inr e)) := by
  change (S).rotation d.val e.val ↔ (B).rotation d.val e.val
  obtain ⟨a, rfl⟩ := (D).surjective d
  obtain ⟨b, rfl⟩ := (D).surjective e
  exact (lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk a hd b).symm.trans
      (lPlusCodeBlockSide_rotation_glued_iff
        hτ hp P hqMode Tpath hfin hleft hk a b).symm

/-- Helper toward Lemma 5.5: rotation is preserved off both gluing
boundary vertex sets by the fixed-ID cell equivalence. -/
theorem lPlusActualCodeBlockCellEquiv_rotation_iff_interior
    (d e : {d : ℕ × Bool // d.1 ∈ (S).edges})
    (hd : kmswLimitDartVertex (shiftedStream W 0) d.val ∉ BV) :
    geometricSideRelation S .rotation (.inr d) (.inr e) ↔
      geometricSideRelation B .rotation (E (.inr d)) (E (.inr e)) := by
  change (S).rotation d.val e.val ↔ (B).rotation d.val e.val
  obtain ⟨a, rfl⟩ := (D).surjective d
  obtain ⟨b, rfl⟩ := (D).surjective e
  exact (lPlusGluedCorrectedRotation2_interior
    hτ hp P hqMode Tpath hfin hleft hk a hd b).symm.trans
      (lPlusCodeBlockSide_rotation_glued_iff
        hτ hp P hqMode Tpath hfin hleft hk a b).symm

/-- Helper toward Lemma 5.5: corrected rotation equals the actual code
return at every initial-root input and every input off the gluing boundaries. -/
theorem lPlusGluedCorrectedRotation2_eq_codeReturn_initial_or_interior
    (d : Q)
    (hd : kmswLimitDartVertex (shiftedStream W 0) (D d).val =
        boundaryVertex (shiftedStream W 0) h k ∨
      kmswLimitDartVertex (shiftedStream W 0) (D d).val ∉ BV) :
    C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
  have hr := (lPlusGluedCodeReturn_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk d
      (lPlusGluedCodeReturn (H := H) hτ hqMode d)).mp rfl
  rcases hd with hd | hd
  · exact (lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d hd _).mpr hr
  · exact (lPlusGluedCorrectedRotation2_interior
      hτ hp P hqMode Tpath hfin hleft hk d hd _).mpr hr

/-- Helper toward Lemma 5.5: the corrected attachment rotation is the
least positive code return at both darts of every upper-left edge. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_eq_codeReturn
    (i : Fin (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length)
    (b : Bool) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
    C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
  dsimp only
  apply (lPlusGluedCorrectedRotation2_upperLeft_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk i b _).mpr
  exact (lPlusGluedCodeReturn_rotation_iff hτ hp P hqMode Tpath hfin hleft hk _ _).mp rfl

/-- Helper toward Lemma 5.5: the fixed-ID cell equivalence preserves
rotation at every upper-left attachment dart, including both endpoints. -/
theorem lPlusActualCodeBlockCellEquiv_rotation_iff_upperLeft
    (i : Fin (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length)
    (b : Bool) (e : Q) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
    geometricSideRelation S .rotation (.inr (D d)) (.inr (D e)) ↔
      geometricSideRelation B .rotation (E (.inr (D d))) (E (.inr (D e))) := by
  dsimp only
  change (S).rotation _ _ ↔ (B).rotation _ _
  exact (lPlusGluedCorrectedRotation2_upperLeft_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk i b e).symm.trans
      (lPlusCodeBlockSide_rotation_glued_iff
        hτ hp P hqMode Tpath hfin hleft hk _ e).symm












































































































/- Validation record: one initial development compile failed (notation precheck
and reduction of the cell equivalence); the repaired check and the next two
helper declarations reported exactly [propext, Classical.choice, Quot.sound].
The full target and residual propositions were also elaborated in that check.
checker, cache retrieval, dependency build, commit, or push was run. -/

end DirectedDistances.PaperProofs.Section5
