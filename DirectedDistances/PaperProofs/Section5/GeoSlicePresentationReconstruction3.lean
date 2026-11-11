/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction2

/-! Intrinsic least-coalescence data descend to the complete marked-side class.
This is boundary data for reconstruction, not an enclosed-slice extractor. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: indexed seam agreement of an internal ray,
including both zero offsets. This uses individual darts, not adjacency. -/
@[expose] def geometricSideRaySeamAgreement (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (a b : ℕ) : Prop :=
  ∀ n : ℕ, geometricSideRelation M (.seam (b + n)) (d (a + n)) (d (a + n))

/-- Helper toward Lemma 5.6: a marked isomorphism preserves all aligned
ray/seam tails, with the same two offsets. -/
theorem geometricSideRaySeamAgreement_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d : ℕ → GeometricSideCell M) (a b : ℕ) :
    geometricSideRaySeamAgreement M d a b ↔
      geometricSideRaySeamAgreement N (I.equiv ∘ d) a b := by
  exact forall_congr' (fun n => I.relation_iff _ _ _)

/-- Helper toward Lemma 5.6: each indexed seam mark denotes at most one
dart cell, even in a side with parallel geometric edges. -/
theorem geometricSideRelation_seam_self_unique (M : GeometricSideSubmap)
    (i : ℕ) {a b : GeometricSideCell M}
    (ha : geometricSideRelation M (.seam i) a a)
    (hb : geometricSideRelation M (.seam i) b b) : a = b := by
  cases a with
  | inl a => exact False.elim ha
  | inr a =>
    cases b with
    | inl b => exact False.elim hb
    | inr b => exact congrArg Sum.inr (Subtype.ext (ha.symm.trans hb))

/-- Helper toward Lemma 5.6: the two jointly least seam-agreement offsets
of an intrinsic adjacent ray. The pair is not split into separate choices. -/
@[expose] def geometricSideIntrinsicCoalescencePairs
    (M : GeometricSideSubmap) (longest : Bool) : Set (ℕ × ℕ) :=
  {p | ∃ v d : ℕ → GeometricSideCell M,
    IntrinsicallyLeftmostAdjacentRay M longest v d ∧
    geometricSideRaySeamAgreement M d p.1 p.2 ∧
    ∀ a b : ℕ, geometricSideRaySeamAgreement M d a b → p.1 ≤ a ∧ p.2 ≤ b}

/-- Helper toward Lemma 5.6: intrinsic joint coalescence data are invariant
under every complete marked-side isomorphism. -/
theorem geometricSideIntrinsicCoalescencePairs_eq {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool) :
    geometricSideIntrinsicCoalescencePairs M longest =
      geometricSideIntrinsicCoalescencePairs N longest := by
  have transport {A B : GeometricSideSubmap} (J : GeometricSideMarkedIso A B)
      {p : ℕ × ℕ} (hp : p ∈ geometricSideIntrinsicCoalescencePairs A longest) :
      p ∈ geometricSideIntrinsicCoalescencePairs B longest := by
    obtain ⟨v, d, hl, htail, hmin⟩ := hp
    exact ⟨J.equiv ∘ v, J.equiv ∘ d,
      intrinsicallyLeftmostAdjacentRay_map J longest hl,
      (geometricSideRaySeamAgreement_iff J d p.1 p.2).1 htail,
      fun a b hab => hmin a b ((geometricSideRaySeamAgreement_iff J d a b).2 hab)⟩
  exact Set.Subset.antisymm (fun _ => transport I)
    (fun _ => transport (GeometricSideMarkedIso.symm I))

/-- Helper toward Lemma 5.6: the intrinsic coalescence pairs as a function
of the complete side class. No geometric realization is an input. -/
@[expose] def geometricSideClassIntrinsicCoalescencePairs (longest : Bool) :
    GeometricSideClass → Set (ℕ × ℕ) :=
  Quotient.lift (fun M => geometricSideIntrinsicCoalescencePairs M longest)
    (fun _ _ h => h.elim fun I => geometricSideIntrinsicCoalescencePairs_eq I longest)

/-- Helper toward Lemma 5.6: the quotient function evaluates to the exact
intrinsic coalescence predicate on each representative. -/
theorem geometricSideClassIntrinsicCoalescencePairs_mk
    (M : GeometricSideSubmap) (longest : Bool) :
    geometricSideClassIntrinsicCoalescencePairs longest (geometricSideClass M) =
      geometricSideIntrinsicCoalescencePairs M longest := rfl

/-- Helper toward Lemma 5.6: select the joint coalescence pair precisely
when the intrinsic class predicate has a unique member. Other classes give
`none`; this function makes no assertion of slice reconstruction. -/
@[expose] noncomputable def geometricSideClassAdjacentCoalescence
    (longest : Bool) (C : GeometricSideClass) : Option (ℕ × ℕ) := by
  classical
  exact if h : ∃! p, p ∈ geometricSideClassIntrinsicCoalescencePairs longest C
    then some h.choose else none

/-- Helper toward Lemma 5.6: complete characterization of the optional
class reader; it returns a pair exactly for the corresponding singleton. -/
theorem geometricSideClassAdjacentCoalescence_eq_some_iff
    (longest : Bool) (C : GeometricSideClass) (p : ℕ × ℕ) :
    geometricSideClassAdjacentCoalescence longest C = some p ↔
      geometricSideClassIntrinsicCoalescencePairs longest C = {p} := by
  classical
  unfold geometricSideClassAdjacentCoalescence
  split
  next h =>
    simp only [Option.some.injEq]
    constructor
    · intro he
      ext q
      constructor
      · intro hq
        exact (h.choose_spec.2 q hq).trans he
      · intro hq
        have hqp : q = p := hq
        rw [hqp, ← he]
        exact h.choose_spec.1
    · intro hs
      simpa only [hs, Set.mem_singleton_iff] using h.choose_spec.1
  next h =>
    constructor
    · intro he
      cases he
    · intro hs
      exact False.elim (h ⟨p, by rw [hs]; exact Set.mem_singleton p,
        fun q hq => by rw [hs] at hq; exact hq⟩)

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: on a realized left side, the intrinsic class
predicate gives exactly the actual adjacent geodesics' least coalescence.
Containment is the established geometric carrier condition, discharged on
the simultaneous almost-sure event below. -/
theorem m0GeodesicSide_mem_intrinsicCoalescencePairs_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (a b : ℕ) :
    (a, b) ∈ geometricSideClassIntrinsicCoalescencePairs longest
      (geometricSideClass (m0GeodesicSide hp (P k) .left)) ↔
      M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b := by
  constructor
  · rintro ⟨v, d, hl, ht, hm⟩
    exact (m0GeodesicSide_leastCoalescence_iff_intrinsicSeam
      hp P T hleft k hcontain hl a b).2 ⟨ht, hm⟩
  · intro hab
    have hl := m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain
    obtain ⟨ht, hm⟩ := (m0GeodesicSide_leastCoalescence_iff_intrinsicSeam
      hp P T hleft k hcontain hl a b).1 hab
    exact ⟨_, _, hl, ht, hm⟩

/-- Helper toward Lemma 5.6: a realized left-side class determines its
joint least-coalescence pair uniquely, including either zero coordinate. -/
theorem m0GeodesicSide_intrinsicCoalescencePairs_eq_singleton
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {a b : ℕ} (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    geometricSideClassIntrinsicCoalescencePairs longest
      (geometricSideClass (m0GeodesicSide hp (P k) .left)) = {(a, b)} := by
  ext p
  rcases p with ⟨c, d⟩
  rw [m0GeodesicSide_mem_intrinsicCoalescencePairs_iff hp P T hleft k hcontain]
  constructor
  · intro hcd
    have h₁ := hab.2 c d hcd.1
    have h₂ := hcd.2 a b hab.1
    exact Prod.ext (Nat.le_antisymm h₂.1 h₁.1) (Nat.le_antisymm h₂.2 h₁.2)
  · intro he
    have he' : (c, d) = (a, b) := he
    cases he'
    exact hab

/-- Helper toward Lemma 5.6: one fixed function of the left-side class
recovers both least-coalescence offsets simultaneously for every cut and
both metrics, on one full-measure event. The actual paths and ambient
leftmostness remain in the conclusion; no reconstruction is assumed. -/
theorem m0GeodesicSide_ae_classAdjacentCoalescence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        ∀ k : ℤ, ∃ a b : ℕ,
          ∃ _hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
          geometricSideClassAdjacentCoalescence longest
            (geometricSideClass (m0GeodesicSide hp (P k) .left)) = some (a, b) := by
  filter_upwards [m0Cut_ae_realizedLeftSideSlice_eq] with W hW
  obtain ⟨H, h, hLL, hp, hmode⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, hc, hcontain, _⟩ := hmode longest
  refine ⟨P, T, hleft, fun k => ?_⟩
  obtain ⟨a, b, hab⟩ := hc k
  refine ⟨a, b, hab, ?_⟩
  apply (geometricSideClassAdjacentCoalescence_eq_some_iff _ _ _).2
  exact m0GeodesicSide_intrinsicCoalescencePairs_eq_singleton hp P T hleft k
    (hcontain (k - 1) k (by omega)) hab

section TwoRealizations

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))

include hleft hleft' in
/-- Helper toward Lemma 5.6: a marked isomorphism between two realized
left sides, even from different outcomes and different cut indices, maps
the actual preceding geodesics pointwise. Identification is proved by the
intrinsic selector, rather than imposed as a hypothesis on the isomorphism. -/
theorem m0GeodesicLeftSide_markedIso_map_previousRay :
    I.equiv ∘ m0GeodesicSideAdjacentVertices hp P k hcontain =
        m0GeodesicSideAdjacentVertices hp' P' l hcontain' ∧
      I.equiv ∘ m0GeodesicSideAdjacentDarts hp P k hcontain =
        m0GeodesicSideAdjacentDarts hp' P' l hcontain' := by
  exact m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique hp' (P' l) .left
    (intrinsicallyLeftmostAdjacentRay_map I longest
      (m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain))
    (m0GeodesicSide_realizedAdjacent_is_intrinsic hp' P' T' hleft' l hcontain')

/-- Helper toward Lemma 5.6: the same marked isomorphism transports every
indexed dart of the current geodesic, which is the stored seam. Together
with previous-ray transport this identifies both finite boundary segments
once their common least offsets are known. -/
theorem m0GeodesicLeftSide_markedIso_map_seamDart (n : ℕ) :
    I.equiv (m0GeodesicSideSeamDartCell hp (P k) .left n) =
      m0GeodesicSideSeamDartCell hp' (P' l) .left n := by
  apply geometricSideRelation_seam_self_unique _ n
  · exact (I.relation_iff _ _ _).1 (show geometricSideRelation
      (m0GeodesicSide hp (P k) .left) (.seam n)
      (m0GeodesicSideSeamDartCell hp (P k) .left n)
      (m0GeodesicSideSeamDartCell hp (P k) .left n) from rfl)
  · rfl

/-- Helper toward Lemma 5.6: the isomorphism also transports each current
geodesic vertex, by incidence with its identified indexed seam dart. -/
theorem m0GeodesicLeftSide_markedIso_map_seamVertex (n : ℕ) :
    I.equiv (m0GeodesicSideSeamVertexCell hp (P k) .left n) =
      m0GeodesicSideSeamVertexCell hp' (P' l) .left n := by
  apply geometricSideRelation_incident_right_unique _
    (a := m0GeodesicSideSeamDartCell hp' (P' l) .left n)
  · have hi := (I.relation_iff _ _ _).1
      ((m0GeodesicSide_seam_directedRay hp (P k) .left n).2.1)
    rw [m0GeodesicLeftSide_markedIso_map_seamDart hp hp' P P' k l I n] at hi
    exact hi
  · exact (m0GeodesicSide_seam_directedRay hp' (P' l) .left n).2.1

include hleft hleft' I hcontain hcontain' in
/-- Helper toward Lemma 5.6: all actual least-coalescence comparisons
agree across marked-isomorphic realized left sides. The two ambient edge
types are kept separate; only the natural-number offsets are compared. -/
theorem m0GeodesicLeftSide_markedIso_leastCoalescence_iff (a b : ℕ) :
    M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b ↔
      M0CutLeastEdgeCoalescence (P' (l - 1)) (P' l) a b := by
  rw [← m0GeodesicSide_mem_intrinsicCoalescencePairs_iff hp P T hleft k hcontain,
    ← m0GeodesicSide_mem_intrinsicCoalescencePairs_iff hp' P' T' hleft' l hcontain']
  have hclass := (geometricSideClass_eq_iff _ _).2 ⟨I⟩
  rw [hclass]

include hleft hleft' I hcontain hcontain' in
/-- Helper toward Lemma 5.6: the least offsets in any two realized left
sides in the same marked class are the same pair. This is only the boundary
data part of slice reconstruction, not equality of enclosed slice classes. -/
theorem m0GeodesicLeftSide_markedIso_leastCoalescence_eq
    {a b a' b' : ℕ}
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (hab' : M0CutLeastEdgeCoalescence (P' (l - 1)) (P' l) a' b') :
    a = a' ∧ b = b' := by
  have ht := (m0GeodesicLeftSide_markedIso_leastCoalescence_iff
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b).1 hab
  have h₁ := ht.2 a' b' hab'.1
  have h₂ := hab'.2 a b ht.1
  exact ⟨Nat.le_antisymm h₁.1 h₂.1, Nat.le_antisymm h₁.2 h₂.2⟩




















































end TwoRealizations

/- OPEN target (2): identify the next ambient geodesic P(k) intrinsically in
the right side of P(k-1), then prove the corresponding slice restriction.
Three routes were inspected: direct reuse of the left-side selector has
the wrong exterior-boundary incoming-corner convention; reflection reverses
the stored rotation (`MirrorMap.lean:22`) and needs a proved correspondence
of the leftmost predicates; and side-local metric selection needs a right-
side coherent ambient lift and global optimality bridge. The inspected
`GeoSliceCoherentAmbientLift` and `GeoSliceDetermination15:631` bridges are
for left sides. None of these right-side bridges is proved in this file.

OPEN target (3): construct the single slice-class readers F_L and F_R and
prove their identities simultaneously at every required cut. The optional
reader proved above returns offsets only. Choosing source preimages still
needs target (1); using the geometric formulas needs realization maps;
and `exists_measurable_ae_factorization` needs an already proved a.s.
determining function. None yields the missing slice reader. The exact
slice-valued target remains `GeoSlicePresentationReconstruction2:485` and
the hypotheses to consume are `GeoSliceLemma56Assembly2:228–243`.

OPEN target (4): construct the per-cut past/future sequence readers. Iterating
adjacent-ray recovery needs reconstruction of each preceding complete side;
direct extraction of every earlier slice still needs the enclosure
restriction and intrinsic internal-ray identification; and countable
intersection makes proved identities simultaneous but cannot construct
their determining functions. The existing all-index realized-carrier
equalities in `GeoSliceDetermination10:336–416` keep explicit realization
maps and internal rays. No sequence reader or measurability hypothesis is
introduced to bypass these obligations.

Only the preceding/current boundary-ray transport and class-valued offset
recovery have been proved here. No numbered paper result is closed. -/

end DirectedDistances.PaperProofs.Section5
