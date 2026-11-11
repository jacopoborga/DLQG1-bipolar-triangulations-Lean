/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusDecodedReader4
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCorrectedDecoder

/-! This file records explicit raw block tokens and least-token IDs on the
existing prefix/primed/hatted gluing quotients. The present work does not yet
transport all ten marked relations to the canonical IDs. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The source type for the three glued vertex
blocks. The tag order is prefix, primed, hatted. -/
abbrev LPlusCanonicalVertexSource {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime) :=
  LPlusBlockVertex W h k (lPlusHattedSide (W := W) (h := h) (k := k)
    longest hqMode)

/-- Helper toward Lemma 5.5. The source type for the three glued dart
blocks, retaining both local endpoint bits. -/
abbrev LPlusCanonicalDartSource {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime) :=
  LPlusBlockDart W h k (lPlusHattedSide (W := W) (h := h) (k := k)
    longest hqMode)

/-- Helper toward Lemma 5.5. Explicit even/odd-style block tags preserve the
block identity and source vertex-stage label before gluing. -/
@[expose] def lPlusRawVertexToken {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (a : LPlusCanonicalVertexSource (W := W) (h := h) (k := k) longest hqMode) : ℕ :=
  match a with
  | .inl v => 3 * v.val
  | .inr (.inl v) => 3 * v + 1
  | .inr (.inr v) => 3 * v.val + 2

/-- Helper toward Lemma 5.5. A dart token records its block, source edge
stage label, and local endpoint bit. -/
@[expose] def lPlusRawDartToken {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (d : LPlusCanonicalDartSource (W := W) (h := h) (k := k) longest hqMode) : ℕ :=
  match d with
  | .inl e => 6 * e.val.1 + (if e.val.2 then 1 else 0)
  | .inr (.inl e) => 6 * e.1 + 2 + (if e.2 then 1 else 0)
  | .inr (.inr e) => 6 * e.val.1 + 4 + (if e.val.2 then 1 else 0)

/-- Helper toward Lemma 5.5. The vertex gluing relation on raw tokens is
the kernel of the existing block-to-whole-plane vertex map. -/
@[expose] def lPlusRawVertexTokenGluing {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (m n : ℕ) : Prop :=
  ∃ a b : LPlusCanonicalVertexSource (W := W) (h := h) (k := k) longest hqMode,
    lPlusRawVertexToken longest hqMode a = m ∧
    lPlusRawVertexToken longest hqMode b = n ∧
    lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ a =
    lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ b

/-- Helper toward Lemma 5.5. The dart gluing relation on raw tokens is the
kernel of the existing block-to-whole-plane dart map, so it retains edge
identity and the local endpoint bit. -/
@[expose] def lPlusRawDartTokenGluing {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (m n : ℕ) : Prop :=
  ∃ a b : LPlusCanonicalDartSource (W := W) (h := h) (k := k) longest hqMode,
    lPlusRawDartToken longest hqMode a = m ∧
    lPlusRawDartToken longest hqMode b = n ∧
    lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ a =
    lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ b

/-- Helper toward Lemma 5.5. Vertex equality in the code-glued quotient is
exactly equality under the old geometric vertex map. -/
theorem lPlusCanonicalVertex_quotient_iff {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (a b : LPlusCanonicalVertexSource (W := W) (h := h) (k := k) longest hqMode) :
    lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ a =
        lPlusBlockVertexImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ b ↔
      (⟦a⟧ : LPlusGluedVertex longest hqMode hτ) = ⟦b⟧ := by
  change (Setoid.ker (lPlusBlockVertexImage (M := lPlusHattedSide
    (W := W) (h := h) (k := k) longest hqMode) hτ) a b) ↔ _
  constructor
  · exact Quotient.sound
  · exact Quotient.exact

/-- Helper toward Lemma 5.5. Dart equality in the code-glued quotient is
exactly equality under the old geometric dart map. -/
theorem lPlusCanonicalDart_quotient_iff {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (a b : LPlusCanonicalDartSource (W := W) (h := h) (k := k) longest hqMode) :
    lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
      longest hqMode) hτ a =
        lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ b ↔
      (⟦a⟧ : LPlusGluedDart longest hqMode hτ) = ⟦b⟧ := by
  change (Setoid.ker (lPlusBlockDartImage (M := lPlusHattedSide
    (W := W) (h := h) (k := k) longest hqMode) hτ) a b) ↔ _
  constructor
  · exact Quotient.sound
  · exact Quotient.exact

/-- Helper toward Lemma 5.5. Every glued vertex has a raw-token candidate. -/
theorem lPlusCanonicalVertexCandidate_exists {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (v : LPlusGluedVertex longest hqMode hτ) :
    ∃ n, ∃ a : LPlusCanonicalVertexSource (W := W) (h := h) (k := k) longest hqMode,
      lPlusRawVertexToken longest hqMode a = n ∧
        (⟦a⟧ : LPlusGluedVertex longest hqMode hτ) = v := by
  refine Quotient.inductionOn v ?_
  intro a
  exact ⟨lPlusRawVertexToken longest hqMode a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Least raw-token ID of a glued vertex. -/
@[expose] noncomputable def lPlusCanonicalVertexId {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (v : LPlusGluedVertex longest hqMode hτ) : ℕ :=
  Nat.find (lPlusCanonicalVertexCandidate_exists longest hqMode hτ v)

/-- Helper toward Lemma 5.5. Every glued dart has a raw-token candidate. -/
theorem lPlusCanonicalDartCandidate_exists {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (v : LPlusGluedDart longest hqMode hτ) :
    ∃ n, ∃ a : LPlusCanonicalDartSource (W := W) (h := h) (k := k) longest hqMode,
      lPlusRawDartToken longest hqMode a = n ∧
        (⟦a⟧ : LPlusGluedDart longest hqMode hτ) = v := by
  refine Quotient.inductionOn v ?_
  intro a
  exact ⟨lPlusRawDartToken longest hqMode a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Least raw-token ID of a glued dart. -/
@[expose] noncomputable def lPlusCanonicalDartId {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (v : LPlusGluedDart longest hqMode hτ) : ℕ :=
  Nat.find (lPlusCanonicalDartCandidate_exists longest hqMode hτ v)







































































end DirectedDistances.PaperProofs.Section5
