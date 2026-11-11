/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice5
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Reduction

/- Intrinsic reconstruction from a marked left side. Conditional geometric
identifications are kept separate from the intrinsic operations.
Numbered outputs are chosen representatives of the full intrinsic relational
restrictions, whose marked classes are proved unique before either choice.
The source realization domain is established conditional on the displayed
exhaustion hypothesis, rather than inserted into either reader as a premise.
with the sole coordinator. No numbered paper result is claimed here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: a complete marked realization of an intrinsic
restriction. The equivalence records every retained cell and every relation. -/
@[expose] def leftRestrictionRealizes (M : GeometricSideSubmap)
    (keep : Set (GeometricSideCell M))
    (R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop)
    (N : GeometricSideSubmap) : Prop :=
  ∃ e : GeometricSideCell N ≃ keep, ∀ t a b,
    geometricSideRelation N t a b ↔ R t (e a).val (e b).val

/-- Helper toward Lemma 5.6: a complete intrinsic restriction has at most
one marked isomorphism class, independently of its numbering. -/
theorem leftRestrictionRealizes_class_unique {M N N' : GeometricSideSubmap}
    {keep : Set (GeometricSideCell M)}
    {R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop}
    (h : leftRestrictionRealizes M keep R N)
    (h' : leftRestrictionRealizes M keep R N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  apply (geometricSideClass_eq_iff _ _).2
  refine ⟨⟨e.trans f.symm, ?_⟩⟩
  intro t a b
  change geometricSideRelation N t a b ↔
    geometricSideRelation N' t (f.symm (e a)) (f.symm (e b))
  rw [he, hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Helper toward Lemma 5.6: restriction realizations transport directly
through intrinsic retained-cell and relation identities. -/
theorem leftRestrictionRealizes_transport {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M')
    {keep : Set (GeometricSideCell M)} {keep' : Set (GeometricSideCell M')}
    {R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop}
    {R' : TruncationRelation → GeometricSideCell M' → GeometricSideCell M' → Prop}
    (hk : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (hr : ∀ t c e, R t c e ↔ R' t (I.equiv c) (I.equiv e))
    (h : leftRestrictionRealizes M keep R N) :
    leftRestrictionRealizes M' keep' R' N := by
  obtain ⟨e, he⟩ := h
  let f : keep ≃ keep' :=
    { toFun := fun c => ⟨I.equiv c.val, (hk c.val).1 c.property⟩
      invFun := fun c => ⟨I.equiv.symm c.val, (hk _).2 (by
        simpa only [Equiv.apply_symm_apply] using c.property)⟩
      left_inv := fun c => Subtype.ext (I.equiv.symm_apply_apply c.val)
      right_inv := fun c => Subtype.ext (I.equiv.apply_symm_apply c.val) }
  exact ⟨e.trans f, fun t a b => (he t a b).trans (hr t _ _)⟩

/-- Helper toward Lemma 5.6: unique intrinsic adjacent-ray data. No
existence or uniqueness on an arbitrary abstract side is postulated. -/
@[expose] def leftReconstructionRay (M : GeometricSideSubmap) (longest : Bool)
    (v d : ℕ → GeometricSideCell M) : Prop :=
  IntrinsicallyLeftmostAdjacentRay M longest v d ∧
    ∀ v' d', IntrinsicallyLeftmostAdjacentRay M longest v' d' → v' = v ∧ d' = d

/-- Helper toward Lemma 5.6: unique ray data transport without geometric
enclosure assumptions. -/
theorem leftReconstructionRay_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M} (h : leftReconstructionRay M longest v d) :
    leftReconstructionRay N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  refine ⟨intrinsicallyLeftmostAdjacentRay_map I longest h.1, ?_⟩
  intro v' d' hl
  obtain ⟨hv, hd⟩ := h.2 _ _
    (intrinsicallyLeftmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl)
  constructor
  · funext n
    exact (I.equiv.apply_symm_apply (v' n)).symm.trans (congrArg I.equiv (congrFun hv n))
  · funext n
    exact (I.equiv.apply_symm_apply (d' n)).symm.trans (congrArg I.equiv (congrFun hd n))

/-- Helper toward Lemma 5.6: intrinsic seam sequences, including their
initial vertices; the full indexed marks determine both sequences uniquely. -/
@[expose] def leftReconstructionSeam (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) : Prop :=
  ∀ n, geometricSideRelation M (.seam n) (d n) (d n) ∧
    geometricSideRelation M .incident (d n) (v n)

/-- Helper toward Lemma 5.6: the seam sequences transport intrinsically. -/
theorem leftReconstructionSeam_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {v d : ℕ → GeometricSideCell M}
    (h : leftReconstructionSeam M v d) :
    leftReconstructionSeam N (I.equiv ∘ v) (I.equiv ∘ d) :=
  fun n => ⟨(I.relation_iff _ _ _).1 (h n).1, (I.relation_iff _ _ _).1 (h n).2⟩

/-- Helper toward Lemma 5.6: uniqueness of both seam sequences. -/
theorem leftReconstructionSeam_unique {M : GeometricSideSubmap}
    {v d v' d' : ℕ → GeometricSideCell M}
    (h : leftReconstructionSeam M v d) (h' : leftReconstructionSeam M v' d') :
    v = v' ∧ d = d' := by
  have hd : d = d' := funext fun n =>
    geometricSideRelation_seam_self_unique M n (h n).1 (h' n).1
  subst d'
  exact ⟨funext fun n => geometricSideRelation_incident_right_unique M (h n).2 (h' n).2, rfl⟩

/-- Helper toward Lemma 5.6: the intrinsic previous-left carrier is the
complement of the open right candidate, retaining all ray cells. -/
@[expose] def leftPreviousKeep (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) : Set (GeometricSideCell M) :=
  {c | ¬ geometricSide_intrinsic_right M v d c ∨
    geometricSide_ray_vertex M v c ∨ geometricSide_ray_dart M d c}

/-- Helper toward Lemma 5.6: the intrinsic slice carrier deletes the
strict vertex tails and weak edge tails from the closed right candidate. -/
@[expose] def leftSliceKeep (M : GeometricSideSubmap)
    (v d vs ds : ℕ → GeometricSideCell M) (a b : ℕ) : Set (GeometricSideCell M) :=
  {c | geometricSide_intrinsic_right M v d c ∧
    c ∉ geometricSideRayDeletedTailCells M v d a ∪
      geometricSideRayDeletedTailCells M vs ds b}

/-- Helper toward Lemma 5.6: previous-left carrier transport is intrinsic. -/
theorem leftPreviousKeep_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    c ∈ leftPreviousKeep M v d ↔
      I.equiv c ∈ leftPreviousKeep N (I.equiv ∘ v) (I.equiv ∘ d) :=
  or_congr (not_congr (geometricSide_intrinsic_right_map_iff I v d c))
    (or_congr (geometricSide_ray_vertex_map_iff I v c) (geometricSide_ray_dart_map_iff I d c))

/-- Helper toward Lemma 5.6: slice carrier transport is intrinsic. -/
theorem leftSliceKeep_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d vs ds : ℕ → GeometricSideCell M)
    (a b : ℕ) (c : GeometricSideCell M) :
    c ∈ leftSliceKeep M v d vs ds a b ↔
      I.equiv c ∈ leftSliceKeep N (I.equiv ∘ v) (I.equiv ∘ d)
        (I.equiv ∘ vs) (I.equiv ∘ ds) a b :=
  and_congr (geometricSide_intrinsic_right_map_iff I v d c)
    (not_congr (or_congr (geometricSideRayDeletedTailCells_map_iff I v d a c)
      (geometricSideRayDeletedTailCells_map_iff I vs ds b c)))

/-- Helper toward Lemma 5.6: a submap realizes the previous-left intrinsic
restriction, with shifted boundary, internal seam, induced rotation and faces. -/
@[expose] def leftPreviousRealizes (longest : Bool) (M N : GeometricSideSubmap) : Prop :=
  ∃ v d, leftReconstructionRay M longest v d ∧
    leftRestrictionRealizes M (leftPreviousKeep M v d)
      (geometricSide_previous_left_relation M v d (leftPreviousKeep M v d)) N

/-- Helper toward Lemma 5.6: a submap realizes the intrinsic enclosed
slice at the jointly least seam-coalescence pair, with both tail deletions. -/
@[expose] def leftSliceRealizes (longest : Bool) (M N : GeometricSideSubmap) : Prop :=
  ∃ v d vs ds a b, leftReconstructionRay M longest v d ∧
    leftReconstructionSeam M vs ds ∧
    geometricSideRaySeamAgreement M d a b ∧
    (∀ a' b', geometricSideRaySeamAgreement M d a' b' → a ≤ a' ∧ b ≤ b') ∧
    leftRestrictionRealizes M (leftSliceKeep M v d vs ds a b)
      (geometricSide_enclosed_relation M v d (leftSliceKeep M v d vs ds a b)) N

/-- Helper toward Lemma 5.6: previous-left intrinsic realization transport
does not require Open A. -/
theorem leftPreviousRealizes_map {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M') (longest : Bool)
    (h : leftPreviousRealizes longest M N) : leftPreviousRealizes longest M' N := by
  obtain ⟨v, d, hr, hN⟩ := h
  exact ⟨I.equiv ∘ v, I.equiv ∘ d, leftReconstructionRay_map I longest hr,
    leftRestrictionRealizes_transport I (leftPreviousKeep_map_iff I v d)
      (geometricSide_previous_left_relation_map_iff I v d _ _
        (leftPreviousKeep_map_iff I v d)) hN⟩

/-- Helper toward Lemma 5.6: intrinsic slice realization transport
does not require Open A. -/
theorem leftSliceRealizes_map {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M') (longest : Bool)
    (h : leftSliceRealizes longest M N) : leftSliceRealizes longest M' N := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  refine ⟨I.equiv ∘ v, I.equiv ∘ d, I.equiv ∘ vs, I.equiv ∘ ds, a, b,
    leftReconstructionRay_map I longest hr, leftReconstructionSeam_map I hs,
    (geometricSideRaySeamAgreement_iff I d a b).1 ht,
    fun a' b' ht' => hm a' b' ((geometricSideRaySeamAgreement_iff I d a' b').2 ht'), ?_⟩
  exact leftRestrictionRealizes_transport I (leftSliceKeep_map_iff I v d vs ds a b)
    (geometricSide_enclosed_relation_map_iff I v d _ _
      (leftSliceKeep_map_iff I v d vs ds a b)) hN

/-- Helper toward Lemma 5.6: previous-left realizations have a unique class. -/
theorem leftPreviousRealizes_class_unique {longest : Bool} {M N N' : GeometricSideSubmap}
    (h : leftPreviousRealizes longest M N) (h' : leftPreviousRealizes longest M N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨v, d, hr, hN⟩ := h
  obtain ⟨v', d', hr', hN'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hr.2 v' d' hr'.1
  exact leftRestrictionRealizes_class_unique hN hN'

/-- Helper toward Lemma 5.6: intrinsic slice realizations have a unique
class; the two jointly least offsets are preserved together. -/
theorem leftSliceRealizes_class_unique {longest : Bool} {M N N' : GeometricSideSubmap}
    (h : leftSliceRealizes longest M N) (h' : leftSliceRealizes longest M N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  obtain ⟨v', d', vs', ds', a', b', hr', hs', ht', hm', hN'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hr.2 v' d' hr'.1
  obtain ⟨rfl, rfl⟩ := leftReconstructionSeam_unique hs' hs
  have ha : a' = a := Nat.le_antisymm (hm' a b ht).1 (hm a' b' ht').1
  have hb : b' = b := Nat.le_antisymm (hm' a b ht).2 (hm a' b' ht').2
  subst a'
  subst b'
  exact leftRestrictionRealizes_class_unique hN hN'

/-- Helper toward Lemma 5.6: the intrinsic optional slice reader. A
complete marked realization is chosen only after its class uniqueness has
been proved. Nonrealizable intrinsic restrictions give `none`. -/
@[expose] noncomputable def leftOneSlice (longest : Bool) (M : GeometricSideSubmap) :
    Option GeometricSideClass :=
  if h : ∃ N, leftSliceRealizes longest M N then some (geometricSideClass h.choose) else none

/-- Helper toward Lemma 5.6: choose a numbered representative of the
intrinsic previous-left restriction. Outside its realization domain the
operation is the identity; the characterization below records this branch. -/
@[expose] noncomputable def leftPrevSide (longest : Bool) (M : GeometricSideSubmap) :
    GeometricSideSubmap :=
  if h : ∃ N, leftPreviousRealizes longest M N then h.choose else M

/-- Helper toward Lemma 5.6: the optional reader returns the unique
marked class of any complete intrinsic slice realization. -/
theorem leftOneSlice_eq_of_realizes {longest : Bool} {M N : GeometricSideSubmap}
    (h : leftSliceRealizes longest M N) :
    leftOneSlice longest M = some (geometricSideClass N) := by
  have hex : ∃ N, leftSliceRealizes longest M N := ⟨N, h⟩
  rw [leftOneSlice, dite_eq_left hex]
  exact congrArg some (leftSliceRealizes_class_unique hex.choose_spec h)

/-- Helper toward Lemma 5.6: the chosen previous side realizes its full
intrinsic relation whenever a realization exists. -/
theorem leftPrevSide_realizes {longest : Bool} {M : GeometricSideSubmap}
    (h : ∃ N, leftPreviousRealizes longest M N) :
    leftPreviousRealizes longest M (leftPrevSide longest M) := by
  rw [leftPrevSide, dite_eq_left h]
  exact h.choose_spec

/-- Helper toward Lemma 5.6: the previous-side reader returns the unique
marked class of every complete intrinsic previous-left realization. -/
theorem leftPrevSide_class_eq_of_realizes {longest : Bool} {M N : GeometricSideSubmap}
    (h : leftPreviousRealizes longest M N) :
    geometricSideClass (leftPrevSide longest M) = geometricSideClass N :=
  leftPreviousRealizes_class_unique (leftPrevSide_realizes ⟨N, h⟩) h

/-- Helper toward Lemma 5.6: exact characterization of the reader's
undefined branch, with no geometric premise. -/
theorem leftOneSlice_eq_none_iff (longest : Bool) (M : GeometricSideSubmap) :
    leftOneSlice longest M = none ↔ ¬ ∃ N, leftSliceRealizes longest M N := by
  unfold leftOneSlice
  split <;> simp_all only [Option.some_ne_none, not_true_eq_false, not_false_eq_true]

/-- Helper toward Lemma 5.6: complete characterization of every successful
optional output as the unique class realizing the full intrinsic slice. -/
theorem leftOneSlice_eq_some_iff (longest : Bool) (M : GeometricSideSubmap)
    (C : GeometricSideClass) :
    leftOneSlice longest M = some C ↔
      ∃ N, leftSliceRealizes longest M N ∧ geometricSideClass N = C := by
  constructor
  · intro h
    by_cases hex : ∃ N, leftSliceRealizes longest M N
    · refine ⟨hex.choose, hex.choose_spec, ?_⟩
      exact Option.some.inj ((leftOneSlice_eq_of_realizes hex.choose_spec).symm.trans h)
    · rw [(leftOneSlice_eq_none_iff longest M).2 hex] at h
      cases h
  · rintro ⟨N, hN, rfl⟩
    exact leftOneSlice_eq_of_realizes hN

/-- Helper toward Lemma 5.6: exact characterization of the identity
extension outside the previous-side realization domain. -/
theorem leftPrevSide_eq_self_of_not_realizable (longest : Bool) (M : GeometricSideSubmap)
    (h : ¬ ∃ N, leftPreviousRealizes longest M N) : leftPrevSide longest M = M :=
  dite_eq_right h

/-- Helper toward Lemma 5.6: the optional slice reader is invariant
under every marked isomorphism, without any Open A premise. -/
theorem leftOneSlice_markedIso {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool) :
    leftOneSlice longest M = leftOneSlice longest N := by
  by_cases h : ∃ K, leftSliceRealizes longest M K
  · obtain ⟨K, hK⟩ := h
    exact (leftOneSlice_eq_of_realizes hK).trans
      (leftOneSlice_eq_of_realizes (leftSliceRealizes_map I longest hK)).symm
  · have hn : ¬ ∃ K, leftSliceRealizes longest N K := by
      rintro ⟨K, hK⟩
      exact h ⟨K, leftSliceRealizes_map (GeometricSideMarkedIso.symm I) longest hK⟩
    rw [(leftOneSlice_eq_none_iff longest M).2 h, (leftOneSlice_eq_none_iff longest N).2 hn]

/-- Helper toward Lemma 5.6: the previous-side class is invariant under
every marked isomorphism, including outside the realization domain. -/
theorem leftPrevSide_markedIso_class {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool) :
    geometricSideClass (leftPrevSide longest M) =
      geometricSideClass (leftPrevSide longest N) := by
  by_cases h : ∃ K, leftPreviousRealizes longest M K
  · obtain ⟨K, hK⟩ := h
    exact (leftPrevSide_class_eq_of_realizes hK).trans
      (leftPrevSide_class_eq_of_realizes (leftPreviousRealizes_map I longest hK)).symm
  · have hn : ¬ ∃ K, leftPreviousRealizes longest N K := by
      rintro ⟨K, hK⟩
      exact h ⟨K, leftPreviousRealizes_map (GeometricSideMarkedIso.symm I) longest hK⟩
    rw [leftPrevSide_eq_self_of_not_realizable longest M h,
      leftPrevSide_eq_self_of_not_realizable longest N hn]
    exact (geometricSideClass_eq_iff _ _).2 ⟨I⟩

/-- Helper toward Lemma 5.6: intrinsic one-slice extraction on marked
isomorphism classes, with no ambient realization as an input. -/
@[expose] noncomputable def oneL (longest : Bool) :
    GeometricSideClass → Option GeometricSideClass :=
  Quotient.lift (leftOneSlice longest)
    (fun _ _ h => h.elim fun I => leftOneSlice_markedIso I longest)

/-- Helper toward Lemma 5.6: intrinsic previous-side extraction on
marked isomorphism classes. -/
@[expose] noncomputable def prevL (longest : Bool) :
    GeometricSideClass → GeometricSideClass :=
  Quotient.lift (fun M => geometricSideClass (leftPrevSide longest M))
    (fun _ _ h => h.elim fun I => leftPrevSide_markedIso_class I longest)

/-- Helper toward Lemma 5.6: the class reader evaluates on each representative. -/
theorem oneL_geometricSideClass (longest : Bool) (M : GeometricSideSubmap) :
    oneL longest (geometricSideClass M) = leftOneSlice longest M := rfl

/-- Helper toward Lemma 5.6: the previous-side class reader evaluates on
each representative. -/
theorem prevL_geometricSideClass (longest : Bool) (M : GeometricSideSubmap) :
    prevL longest (geometricSideClass M) = geometricSideClass (leftPrevSide longest M) := rfl

/-- Helper toward Lemma 5.6: a fully characterized injective inclusion
constructs a complete intrinsic restriction realization. -/
theorem leftRestrictionRealizes_of_inclusion {M N : GeometricSideSubmap}
    (keep : Set (GeometricSideCell M))
    (R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop)
    (f : GeometricSideCell N → GeometricSideCell M) (hf : Function.Injective f)
    (hk : Set.range f = keep)
    (hr : ∀ t a b, geometricSideRelation N t a b ↔ R t (f a) (f b)) :
    leftRestrictionRealizes M keep R N := by
  classical
  let g : GeometricSideCell N → keep := fun a => ⟨f a, hk ▸ Set.mem_range_self a⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      exact hf (congrArg Subtype.val hab)
    · intro c
      obtain ⟨a, ha⟩ := (show c.val ∈ Set.range f from hk.symm ▸ c.property)
      exact ⟨a, Subtype.ext ha⟩
  exact ⟨Equiv.ofBijective g hg, hr⟩

section SourceReduction

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k : ℤ, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (k : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)

include T hleft in
/-- Helper toward Lemma 5.6: source leftmostness and containment prove
the unique intrinsic-ray characterization used by the readers. -/
theorem m0GeodesicLeftSide_leftReconstructionRay :
    leftReconstructionRay (m0GeodesicSide hp (P k) .left) longest
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) := by
  have hr := m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain
  exact ⟨hr, fun _ _ hr' =>
    m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique hp (P k) .left hr' hr⟩

/-- Helper toward Lemma 5.6: the indexed source seam satisfies its
complete intrinsic characterization. -/
theorem m0GeodesicLeftSide_leftReconstructionSeam :
    leftReconstructionSeam (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideSeamVertexCell hp (P k) .left)
      (m0GeodesicSideSeamDartCell hp (P k) .left) := by
  intro n
  exact ⟨rfl, (m0GeodesicSide_seam_directedRay hp (P k) .left n).2.1⟩

include T hleft in
/-- Helper toward Lemma 5.6: this named reduction is conditional on the
displayed Open A hypothesis. It identifies the entire intrinsic previous-left
realization, including its root, shifted boundary, seam, faces and rotation. -/
theorem m0GeodesicLeftSide_previousRealizes_of_openA
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right) :
    leftPreviousRealizes longest (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSide hp (P (k - 1)) .left) := by
  refine ⟨_, _, m0GeodesicLeftSide_leftReconstructionRay hp P T hleft k hcontain, ?_⟩
  have hk : Set.range (m0GeodesicPreviousLeftCell hp P k hcontain) =
      leftPreviousKeep _ (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) := by
    ext c
    exact (m0GeodesicPreviousLeftCell_mem_range_iff hp P k hcontain c).trans
      (m0GeodesicLeftSide_previousLeft_mem_iff_of_openA hp P k hcontain hA c)
  apply leftRestrictionRealizes_of_inclusion _ _
    (m0GeodesicPreviousLeftCell hp P k hcontain)
    (m0GeodesicPreviousLeftCell_injective hp P k hcontain) hk
  intro t c e
  rw [← hk]
  exact m0GeodesicPreviousLeft_relation_iff_of_openA hp P k hcontain hA t c e

include T hleft in
/-- Helper toward Lemma 5.6: this named reduction is conditional on the
displayed Open A hypothesis. It identifies the complete intrinsic slice
realization at the actual jointly least coalescence pair. -/
theorem m0GeodesicLeftSide_sliceRealizes_of_openA
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    leftSliceRealizes longest (m0GeodesicSide hp (P k) .left)
      (m0CutGeodesicSlice (hp := hp) P k a b hab) := by
  have hr := m0GeodesicLeftSide_leftReconstructionRay hp P T hleft k hcontain
  obtain ⟨ht, hm⟩ := (m0GeodesicSide_leastCoalescence_iff_intrinsicSeam
    hp P T hleft k hcontain hr.1 a b).1 hab
  refine ⟨_, _, _, _, a, b, hr, m0GeodesicLeftSide_leftReconstructionSeam hp P k,
    ht, hm, ?_⟩
  have hk : Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab) =
      leftSliceKeep _ (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)
        (m0GeodesicSideSeamVertexCell hp (P k) .left)
        (m0GeodesicSideSeamDartCell hp (P k) .left) a b := by
    ext c
    refine (m0CutGeodesicSliceLeftCell_mem_range_iff hp P k a b hab c).trans
      ((m0CutGeodesicSlice_mem_cell_iff_previousRight_and_not_deletedTail
        hp P k a b hab c).trans ?_)
    rw [m0GeodesicLeftSideDeletedTailCells_eq hp P k hcontain a b]
    exact and_congr (hA c).symm Iff.rfl
  apply leftRestrictionRealizes_of_inclusion _ _
    (m0CutGeodesicSliceLeftCell hp P k a b hab)
    (m0CutGeodesicSliceLeftCell_injective hp P k a b hab) hk
  intro t c e
  rw [← hk]
  exact m0CutGeodesicSlice_relation_iff_enclosed_of_openA hp P k hcontain hA a b hab t c e

end SourceReduction

/-- Helper toward Lemma 5.6: the source witness's proved adjacent
coalescences and planar leftmostness give containment of every preceding
ray in the current left side; containment is not a reader assumption. -/
theorem M0CutGeodesicSliceWitness.left_adjacent_containment
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    ∀ n : ℕ,
      (s.P (k - 1)).codePath.edge n ∈ (m0GeodesicSide s.hp (s.P k) .left).edges ∧
      ((s.P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide s.hp (s.P k) .left).vertices := by
  have hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (s.P m) (s.P (m + 1)) a b := by
    intro m
    refine ⟨s.thetaMinus (m + 1), s.theta (m + 1), ?_⟩
    have hab := s.least (m + 1)
    rw [show m + 1 - 1 = m by omega] at hab
    exact hab
  have hsub := m0CutGeodesicLeftSide_subset_of_adjacentCoalescence
    s.P s.T s.hleft hc (k - 1) k (by omega)
  intro n
  constructor
  · exact fun z hz => hsub ((m0GeodesicEdges_subset_both s.hp (s.P (k - 1))
      (m0GeodesicSeam_mem_edges (s.P (k - 1)) n)).1 hz)
  · have hv := m0Geodesic_initial_mem_vertices (s.P (k - 1)) n
    rw [← m0GeodesicSideVertices_inter s.hp (s.P (k - 1))] at hv
    exact hsub hv.1

/-- Helper toward Lemma 5.6: this reduction is conditional on the
displayed off-ray exhaustion hypothesis for all source cuts. On a single
event of full measure, both intrinsic left readers have the required
updates for the same slice witness and every integer index. -/
theorem m0Cut_ae_leftSideUpdates_of_exhaustion (x : XDP)
    (hexhaust : ∀ {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
      {h : BoundaryHitWitnesses (shiftedStream W 0)}
      {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
      (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
      (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
      (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k))
      (_hleft : ∀ k : ℤ, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
      (k : ℤ)
      (hcontain : ∀ n : ℕ,
        (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
        ((P (k - 1)).codePath.initial n).1.id ∈
          (m0GeodesicSide hp (P k) .left).vertices)
      (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)),
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right) →
      (match c with
       | .inl v => v.val ∉ m0GeodesicVertices (P (k - 1))
       | .inr d => d.val.1 ∉ m0GeodesicEdges (P (k - 1))) →
      ∃ a, geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
        Relation.ReflTransGen
          (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
            (m0GeodesicSideAdjacentVertices hp P k hcontain)
            (m0GeodesicSideAdjacentDarts hp P k hcontain)) a c) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneL (if x = XDP.ldp then true else false)
            (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          m0CutGeodesicSliceClassOption x j W ∧
        prevL (if x = XDP.ldp then true else false)
            (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j - 1)) .left) := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x] with W hW
  let s := Classical.choice hW
  refine ⟨s, fun j => ?_⟩
  let hc := s.left_adjacent_containment j
  have hA := m0GeodesicLeftSide_intrinsic_right_iff_previousRight_of_exhaustion
    s.hp s.P j hc (hexhaust s.hp s.P s.T s.hleft j hc)
  constructor
  · rw [oneL_geometricSideClass]
    have hs := leftOneSlice_eq_of_realizes
      (m0GeodesicLeftSide_sliceRealizes_of_openA s.hp s.P s.T s.hleft j hc hA
        (s.thetaMinus j) (s.theta j) (s.least j))
    simpa only [m0CutGeodesicSliceClassOption, dite_eq_left hW] using hs
  · rw [prevL_geometricSideClass]
    exact leftPrevSide_class_eq_of_realizes
      (m0GeodesicLeftSide_previousRealizes_of_openA s.hp s.P s.T s.hleft j hc hA)

end DirectedDistances.PaperProofs.Section5
