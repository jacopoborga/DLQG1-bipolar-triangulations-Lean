/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideVertices
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftReader
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSide
import DirectedDistances.KMSW.PrimedRotInducedOriented
import Mathlib.Order.Setoid.Basic

/-! The nonnegative left side is assembled from the deleted stopped prefix, the
hatted left block, and the primed block. The edge carriers below retain
geometric edge IDs, including missing edges, and darts retain their endpoint
bits. The identified edges are represented by the common whole-plane edge IDs
at the two source boundary attachments. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
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

section GeometricGluing

@[expose] noncomputable def lPlusHattedSide {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime) :
    GeometricSideSubmap :=
  geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime .left
    ⟨boundaryFutureHattedPath k W, hqMode⟩
/-- Helper toward Lemma 5.5: geometric darts of the stopped prefix after
deleting the active boundary edge. -/
abbrev LPlusPrefixDart (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :=
  {d : ℕ × Bool // d.1 ∈ boundaryGluingPrefixMinusEdges W h k}

/-- Helper toward Lemma 5.5: all geometric darts of the primed block,
including both darts of missing edges. -/
abbrev LPlusPrimedDart := ℕ × Bool

/-- Helper toward Lemma 5.5: geometric darts of the retained hatted left
block, including both darts of missing edges. -/
abbrev LPlusHattedDart (M : GeometricSideSubmap) :=
  {d : ℕ × Bool // d.1 ∈ M.edges}

/-- Helper toward Lemma 5.5: a dart in one of the three source blocks. -/
abbrev LPlusBlockDart (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (M : GeometricSideSubmap) := Sum (LPlusPrefixDart W h k)
  (Sum LPlusPrimedDart (LPlusHattedDart M))

/-- Helper toward Lemma 5.5: the block dart map keeps the shared edge ID and
transports the local endpoint bit into the orientation of the glued map. -/
@[expose] noncomputable def lPlusBlockDartImage {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {M : GeometricSideSubmap}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    LPlusBlockDart W h k M → ℕ × Bool
  | .inl d => d.val
  | .inr (.inl d) => (boundaryGluingPrimedEdgeMap W h k hτ d.1,
      d.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ d.1)
  | .inr (.inr d) => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)

/-- Helper toward Lemma 5.5: geometric prefix vertices after deletion. -/
abbrev LPlusPrefixVertex (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :=
  {v : ℕ // v ∈ boundaryGluingPrefixMinusVertices W h k}

/-- Helper toward Lemma 5.5: all geometric vertices of the primed block. -/
abbrev LPlusPrimedVertex := ℕ

/-- Helper toward Lemma 5.5: vertices of the hatted left block. -/
abbrev LPlusHattedVertex (M : GeometricSideSubmap) := {v : ℕ // v ∈ M.vertices}

/-- Helper toward Lemma 5.5: a vertex in one of the three source blocks. -/
abbrev LPlusBlockVertex (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (M : GeometricSideSubmap) := Sum (LPlusPrefixVertex W h k)
  (Sum LPlusPrimedVertex (LPlusHattedVertex M))

/-- Helper toward Lemma 5.5: the block vertex map into the geometric left
side, with the prefix inclusion and the two future embeddings. -/
@[expose] noncomputable def lPlusBlockVertexImage {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {M : GeometricSideSubmap}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    LPlusBlockVertex W h k M → ℕ
  | .inl v => v.val
  | .inr (.inl v) => boundaryGluingPrimedVertexMap W h k hτ v
  | .inr (.inr v) => boundaryGluingHatVertexMap W h k hτ v.val

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the block dart image lands in the geometric
left side. The deleted active edge is absent from the prefix block. -/
theorem lPlusBlockDartImage_mem (d : LPlusBlockDart W h k
    (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ d).1 ∈ (m0GeodesicSide hp P .left).edges := by
  have hside := (boundaryGluing_nonneg_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).2
  rcases d with d | d
  · rcases d with ⟨⟨e, b⟩, he⟩
    rw [hside]
    exact Set.mem_union_left _ (Set.mem_union_left _ he)
  · rcases d with d | d
    · rw [hside]
      exact Set.mem_union_right _ ⟨d.1, rfl⟩
    · rw [hside]
      exact Set.mem_union_left _ (Set.mem_union_right _ ⟨d.val.1, d.property, rfl⟩)

/-- Helper toward Lemma 5.5: the prefix dart embedding is injective. -/
theorem lPlusPrefixDartImage_injective :
    Function.Injective (fun d : LPlusPrefixDart W h k =>
      lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inl d : LPlusBlockDart W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  exact Subtype.ext (Prod.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- Helper toward Lemma 5.5: the primed dart embedding is injective. -/
theorem lPlusPrimedDartImage_injective :
    Function.Injective (fun d : LPlusPrimedDart =>
      lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inr (.inl d) : LPlusBlockDart W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  change (boundaryGluingPrimedEdgeMap W h k hτ a.1,
      a.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ a.1) =
    (boundaryGluingPrimedEdgeMap W h k hτ b.1,
      b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ b.1) at hab
  have he := boundaryGluingPrimedEdgeMap_injective W h k hτ (congrArg Prod.fst hab)
  have hb := congrArg (fun z : ℕ × Bool => z.2) hab
  rcases a with ⟨ae, ab⟩
  rcases b with ⟨be, bb⟩
  have he' : ae = be := by simpa using he
  subst be
  change (ab ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ ae) =
    (bb ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ ae) at hb
  exact Prod.ext rfl (Bool.xor_left_inj.mp hb)

/-- Helper toward Lemma 5.5: the hatted dart embedding is injective. -/
theorem lPlusHattedDartImage_injective :
    Function.Injective (fun d : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) =>
      lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inr (.inr d) : LPlusBlockDart W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  rcases a with ⟨⟨ae, ab⟩, ha⟩
  rcases b with ⟨⟨be, bb⟩, hb⟩
  change (boundaryGluingHatEdgeMap W h k hτ ae, ab) =
    (boundaryGluingHatEdgeMap W h k hτ be, bb) at hab
  simp only [Prod.mk.injEq] at hab
  rcases hab with ⟨habEdge, habBit⟩
  have he : ae = be := boundaryGluingHatEdgeMap_injective W h k hτ habEdge
  apply Subtype.ext
  exact Prod.ext he habBit

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the block vertex image lands in the geometric
left side. -/
theorem lPlusBlockVertexImage_mem
    (v : LPlusBlockVertex W h k
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ v ∈ (m0GeodesicSide hp P .left).vertices := by
  have hside := boundaryGluing_nonneg_left_vertices hτ hp P
    hqMode Tpath hfin hleft hk
  rcases v with v | v
  · rcases v with ⟨a, ha⟩
    rw [hside]
    exact Set.mem_union_left _ (Set.mem_union_left _ ⟨a, ha, rfl⟩)
  · rcases v with v | v
    · rw [hside]
      exact Set.mem_union_right _ ⟨v, Set.mem_univ _, rfl⟩
    · rw [hside]
      exact Set.mem_union_left _ (Set.mem_union_right _ ⟨v.val, v.property, rfl⟩)

/-- Helper toward Lemma 5.5: the prefix vertex embedding is injective. -/
theorem lPlusPrefixVertexImage_injective :
    Function.Injective (fun v : LPlusPrefixVertex W h k =>
      lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inl v : LPlusBlockVertex W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  exact Subtype.ext hab

/-- Helper toward Lemma 5.5: the hatted vertex embedding is injective. -/
theorem lPlusHattedVertexImage_injective :
    Function.Injective (fun v : LPlusHattedVertex
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) =>
      lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inr (.inr v) : LPlusBlockVertex W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  exact Subtype.ext (boundaryGluingHatVertexMap_injective W h k hτ hab)

/-- Helper toward Lemma 5.5: the primed vertex embedding is injective. -/
theorem lPlusPrimedVertexImage_injective :
    Function.Injective (fun v : LPlusPrimedVertex =>
      lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
        longest hqMode) hτ
        (.inr (.inl v) : LPlusBlockVertex W h k
          (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))) := by
  intro a b hab
  dsimp only [lPlusBlockVertexImage] at hab
  have hf : Function.Injective (boundaryGluingFutureVertexMap W h k) :=
    boundaryGluingFutureVertexMap_injective W h k
  have hp' : Function.Injective
      (primedLimitVertexMap (boundaryGluingFutureStream W h k) hτ) := by
    intro v z hvz
    exact (primedLimit_maps_injective_on_allocated
      (boundaryGluingFutureStream W h k) hτ).2
      ((primedLocalIds_eventually_allocated (boundaryGluingFutureStream W h k) hτ).2 v)
      ((primedLocalIds_eventually_allocated (boundaryGluingFutureStream W h k) hτ).2 z)
      hvz
  exact hp' (hf hab)

/-- Helper toward Lemma 5.5: code-glued darts identify representatives
precisely when their geometric edge ID and endpoint bit agree in the left side.
The quotient relation retains both endpoint darts, even for missing edges. -/
abbrev LPlusGluedDart {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :=
  Quotient (Setoid.ker (lPlusBlockDartImage
    (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ))

/-- Helper toward Lemma 5.5: code-glued vertices identify representatives
precisely when their geometric vertex ID agrees in the left side. -/
abbrev LPlusGluedVertex {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :=
  Quotient (Setoid.ker (lPlusBlockVertexImage
    (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ))

include hfin hqMode in
/-- Helper toward Lemma 5.5: the deleted prefix and primed block are
identified exactly along the source upper-left segment and the beta-zero part
of the upper-right segment, with the active edge removed. -/
theorem lPlus_prefix_primed_boundary_attachment :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ =
      (boundaryGluingUpperLeftEdges W h k ∪
        (boundaryGluingUpperRightEdges W h k ∩ boundaryGluingBetaEdges W h k hτ)) \
          {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  exact boundaryGluingPrefixMinusEdges_inter_primedEdges_eq_upperLeft_union_beta_sdiff
    (W := W) (h := h) (k := k) (hτ := hτ) (hfin := hfin)
    (x := ite (longest = true) XDP.ldp XDP.sdp) (hq := hqMode)

include hfin hqMode in
/-- Helper toward Lemma 5.5: the primed block and hatted left block are
identified exactly along their common right/left boundary. -/
theorem lPlus_primed_hatted_boundary_attachment :
    boundaryGluingPrimedEdges W h k hτ ∩
        boundaryGluingLeftHatEdges W h k hτ
          (ite (longest = true) XDP.ldp XDP.sdp) hqMode =
      boundaryGluingBetaEdges W h k hτ := by
  exact boundaryGluingPrimedEdges_inter_leftHatEdges
    (W := W) (h := h) (k := k) (hτ := hτ) (x := ite (longest = true) XDP.ldp XDP.sdp)
    (hq := hqMode) hfin

/-- Helper toward Lemma 5.5: the primed block's own rotation is its first
return inside the nonnegative geometric left-side embedding. -/
theorem lPlusPrimedDartImage_firstReturn (d : LPlusPrimedDart) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inr (.inl d))) =
        lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ
          (.inr (.inl (kmswInfRot (primedCode
            (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
              (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin) d))) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inr (.inl d))) ∉
            Set.range (fun e : LPlusPrimedDart =>
              lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
                longest hqMode) hτ (.inr (.inl e))) := by
  simpa [lPlusBlockDartImage, lMinusPrimedDartImage] using
    lMinusPrimedDartImage_firstReturn (H := H) hτ hfin d

/-- Helper toward Lemma 5.5: the hatted block's own rotation, defined as
first return of its KMSW rotation to the retained geometric left darts. -/
@[expose] noncomputable def lPlusHattedRotation (x : XDP)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    Equiv.Perm {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges} :=
  drawingFirstReturnPerm
    (monotoneFamilyDrawing (boltzmannKMSWStream (pathCode q.val))
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (monotone_family_all (boltzmannKMSWStream (pathCode q.val))))
    {d | d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges}

include hfin in
/-- Helper toward Lemma 5.5: the hatted left block's own rotation is its
first return inside the nonnegative geometric left-side embedding. -/
theorem lPlusHattedDartImage_firstReturn
    (d : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inr (.inr d))) =
        lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ (.inr (.inr (lPlusHattedRotation
            (ite (longest = true) XDP.ldp XDP.sdp)
            ⟨boundaryFutureHattedPath k W, hqMode⟩ d))) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inr (.inr d))) ∉
            Set.range (fun e : LPlusHattedDart
              (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) =>
              lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
                longest hqMode) hτ (.inr (.inr e))) := by
  simpa [lPlusBlockDartImage, lPlusHattedRotation, lPlusHattedSide,
    lMinusHattedRotation] using
    lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d

end GeometricGluing
















end DirectedDistances.PaperProofs.Section5
end
