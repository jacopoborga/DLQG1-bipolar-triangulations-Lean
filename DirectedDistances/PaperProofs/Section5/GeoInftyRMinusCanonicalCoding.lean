/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole11
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE

/-! Canonical raw-token coding toward Lemma 5.5
retain separate raw identities before the existing intrinsic gluing quotient. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Raw edge tokens distinguish the finite prefix
block from the hatted block and retain each block's local edge index. -/
@[expose] def rMinusRawEdgeToken (F : State) (M : GeometricSideSubmap) :
    Sum {e : ℕ // e < F.nextEdge} M.edges → ℕ
  | .inl e => 2 * e.val
  | .inr e => 2 * e.val + 1

/-- Helper toward Lemma 5.5. Raw edge tokens preserve block and local
identity. -/
theorem rMinusRawEdgeToken_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusRawEdgeToken F M) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change 2 * a.val = 2 * b.val at hab
      have h : a.val = b.val := by omega
      exact congrArg Sum.inl (Subtype.ext h)
    | inr b => change 2 * a.val = 2 * b.val + 1 at hab; omega
  | inr a =>
    cases b with
    | inl b => change 2 * a.val + 1 = 2 * b.val at hab; omega
    | inr b =>
      change 2 * a.val + 1 = 2 * b.val + 1 at hab
      have h : a.val = b.val := by omega
      exact congrArg Sum.inr (Subtype.ext h)

/-- Helper toward Lemma 5.5. Candidate raw tokens use the existing edge
quotient, with its boundary-pair gluing relation. -/
@[expose] def rMinusCanonicalEdgeCandidate (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) (n : ℕ) : Prop :=
  ∃ a : Sum {e : ℕ // e < F.nextEdge} M.edges,
    rMinusRawEdgeToken F M a = n ∧ (⟦a⟧ : RMinusCodeGluedEdge F M) = e

/-- Helper toward Lemma 5.5. Every glued edge has a raw-token candidate. -/
theorem rMinusCanonicalEdgeCandidate_exists (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) :
    ∃ n, rMinusCanonicalEdgeCandidate F M e n := by
  refine Quotient.inductionOn e ?_
  intro a
  exact ⟨rMinusRawEdgeToken F M a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. The canonical edge ID is the least raw token
in the intrinsic glued class; it uses no `Encodable` choice. -/
@[expose] noncomputable def rMinusCanonicalEdgeId (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) : ℕ :=
  Nat.find (rMinusCanonicalEdgeCandidate_exists F M e)

/-- Helper toward Lemma 5.5. Complete minimal-token characterization. -/
theorem rMinusCanonicalEdgeId_eq_iff (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) (n : ℕ) :
    rMinusCanonicalEdgeId F M e = n ↔
      rMinusCanonicalEdgeCandidate F M e n ∧
      ∀ m < n, ¬ rMinusCanonicalEdgeCandidate F M e m :=
  Nat.find_eq_iff (rMinusCanonicalEdgeCandidate_exists F M e)

/-- Helper toward Lemma 5.5. A canonical ID represents its glued edge. -/
theorem rMinusCanonicalEdgeId_spec (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) :
    rMinusCanonicalEdgeCandidate F M e (rMinusCanonicalEdgeId F M e) :=
  Nat.find_spec (rMinusCanonicalEdgeCandidate_exists F M e)

/-- Helper toward Lemma 5.5. Canonical edge IDs preserve edge identity. -/
theorem rMinusCanonicalEdgeId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCanonicalEdgeId F M) := by
  intro e f hef
  obtain ⟨a, ha, he⟩ := rMinusCanonicalEdgeId_spec F M e
  obtain ⟨b, hb, hf⟩ := rMinusCanonicalEdgeId_spec F M f
  have hab := rMinusRawEdgeToken_injective F M (ha.trans (hef.trans hb.symm))
  subst b
  exact he.symm.trans hf

/-- Helper toward Lemma 5.5. The least raw token is bounded by any known
prefix or hatted representative. -/
theorem rMinusCanonicalEdgeId_le_token (F : State) (M : GeometricSideSubmap)
    (a : Sum {e : ℕ // e < F.nextEdge} M.edges) :
    rMinusCanonicalEdgeId F M (⟦a⟧) ≤ rMinusRawEdgeToken F M a :=
  Nat.find_min' (rMinusCanonicalEdgeCandidate_exists F M (⟦a⟧))
    ⟨a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Raw vertex tokens distinguish the two blocks. -/
@[expose] def rMinusRawVertexToken : Sum ℕ ℕ → ℕ
  | .inl v => 2 * v
  | .inr v => 2 * v + 1

/-- Helper toward Lemma 5.5. Raw vertex tokens are injective. -/
theorem rMinusRawVertexToken_injective : Function.Injective rMinusRawVertexToken := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change 2 * a = 2 * b at hab
      have h : a = b := by omega
      exact congrArg Sum.inl h
    | inr b => change 2 * a = 2 * b + 1 at hab; omega
  | inr a =>
    cases b with
    | inl b => change 2 * a + 1 = 2 * b at hab; omega
    | inr b =>
      change 2 * a + 1 = 2 * b + 1 at hab
      have h : a = b := by omega
      exact congrArg Sum.inr h

/-- Helper toward Lemma 5.5. A raw vertex token represents a class in the
existing quotient generated by shared prefix/hatted edge endpoints. -/
@[expose] def rMinusCanonicalVertexCandidate (F : State) (M : GeometricSideSubmap)
    (v : RMinusCodeRawVertex F M) (n : ℕ) : Prop :=
  ∃ a : Sum ℕ ℕ, rMinusRawVertexToken a = n ∧
    (⟦a⟧ : RMinusCodeRawVertex F M) = v

/-- Helper toward Lemma 5.5. Every vertex quotient class has a candidate. -/
theorem rMinusCanonicalVertexCandidate_exists (F : State) (M : GeometricSideSubmap)
    (v : RMinusCodeRawVertex F M) :
    ∃ n, rMinusCanonicalVertexCandidate F M v n := by
  refine Quotient.inductionOn v ?_
  intro a
  exact ⟨rMinusRawVertexToken a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Canonical vertex IDs are least raw tokens. -/
@[expose] noncomputable def rMinusCanonicalVertexId (F : State) (M : GeometricSideSubmap)
    (v : RMinusCodeRawVertex F M) : ℕ :=
  Nat.find (rMinusCanonicalVertexCandidate_exists F M v)

/-- Helper toward Lemma 5.5. Canonical vertex IDs preserve quotient identity. -/
theorem rMinusCanonicalVertexId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCanonicalVertexId F M) := by
  intro v w hvw
  obtain ⟨a, ha, hv⟩ := Nat.find_spec (rMinusCanonicalVertexCandidate_exists F M v)
  obtain ⟨b, hb, hw⟩ := Nat.find_spec (rMinusCanonicalVertexCandidate_exists F M w)
  have hab := rMinusRawVertexToken_injective (ha.trans (hvw.trans hb.symm))
  subst b
  exact hv.symm.trans hw

/-- Helper toward Lemma 5.5. Canonical dart IDs retain the edge endpoint bit. -/
@[expose] noncomputable def rMinusCanonicalDartId (F : State) (M : GeometricSideSubmap)
    (d : RMinusCodeGluedDart F M) : ℕ × Bool :=
  (rMinusCanonicalEdgeId F M d.1, d.2)

/-- Helper toward Lemma 5.5. Canonical dart IDs preserve both geometric
edge identity and orientation bit. -/
theorem rMinusCanonicalDartId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCanonicalDartId F M) := by
  intro a b hab
  change (rMinusCanonicalEdgeId F M a.1, a.2) =
    (rMinusCanonicalEdgeId F M b.1, b.2) at hab
  apply Prod.ext
  · exact rMinusCanonicalEdgeId_injective F M (congrArg Prod.fst hab)
  · exact congrArg (fun p : ℕ × Bool => p.2) hab

/-- Helper toward Lemma 5.5. Canonical IDs are bounded by the explicit
prefix/hatted raw token of any representative. -/
theorem rMinusCanonicalEdgeId_prefix_le (F : State) (M : GeometricSideSubmap)
    (e : {e : ℕ // e < F.nextEdge}) :
    rMinusCanonicalEdgeId F M (⟦Sum.inl e⟧) ≤ 2 * e.val := by
  exact rMinusCanonicalEdgeId_le_token F M (Sum.inl e)

/-- Helper toward Lemma 5.5. The hatted block receives the odd raw token
for its local edge label. -/
theorem rMinusCanonicalEdgeId_hatted_le (F : State) (M : GeometricSideSubmap)
    (e : M.edges) :
    rMinusCanonicalEdgeId F M (⟦Sum.inr e⟧) ≤ 2 * e.val + 1 := by
  exact rMinusCanonicalEdgeId_le_token F M (Sum.inr e)

/-- Helper toward Lemma 5.5. A generating edge gluing written directly on
the explicit raw-token labels. -/
@[expose] def rMinusRawTokenGluing (F : State) (M : GeometricSideSubmap)
    (i j : ℕ) : Prop :=
  ∃ a b : Sum {e : ℕ // e < F.nextEdge} M.edges,
    rMinusRawEdgeToken F M a = i ∧ rMinusRawEdgeToken F M b = j ∧
      rMinusCodeEdgeGluing F M a b


















































end DirectedDistances.PaperProofs.Section5

