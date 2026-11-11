/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightEnclosedSlice

/-! Submap-level right updates use the unique intrinsic corner ray when it exists.
Their identification with the source slice and next closed side remains
conditional on the displayed source-side exhaustion hypotheses below. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the chosen metric mode for the cut parameter. -/
@[expose] def geoSliceRightLongest (x : XDP) : Bool :=
  if x = XDP.ldp then true else false

/-- Helper toward Lemma 5.6: a right corner ray consists of its vertex and
individual-dart streams in one marked side. -/
abbrev GeoSliceRightRay (M : GeometricSideSubmap) :=
  (ℕ → GeometricSideCell M) × (ℕ → GeometricSideCell M)

/-- Helper toward Lemma 5.6: existence and uniqueness of the intrinsic
right corner ray, stated on the full vertex/dart pair. -/
@[expose] def geoSliceRightRayUnique (x : XDP) (M : GeometricSideSubmap) : Prop :=
  ∃! r : GeoSliceRightRay M,
    intrinsicallyLeftmostAdjacentRightRay M (geoSliceRightLongest x) r.1 r.2

/-- Helper toward Lemma 5.6: select the unique intrinsic right corner ray,
returning `none` if no unique ray exists. -/
@[expose] noncomputable def geoSliceRightRayOption (x : XDP)
    (M : GeometricSideSubmap) : Option (GeoSliceRightRay M) :=
  if h : geoSliceRightRayUnique x M then some (Classical.choose h) else none

/-- Helper toward Lemma 5.6: edge identity of a dart cell, with a harmless
value on vertex cells. -/
@[expose] def geoSliceRightRayDartEdge {M : GeometricSideSubmap}
    (c : GeometricSideCell M) : ℕ :=
  match c with
  | .inl _ => 0
  | .inr d => d.val.1

/-- Helper toward Lemma 5.6: coordinatewise least aligned offsets between
the old seam and a selected intrinsic ray. -/
@[expose] def geoSliceRightRayOffsets (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (a b : ℕ) : Prop :=
  (∀ n, (M.seam (a + n)).1 = geoSliceRightRayDartEdge (d (b + n))) ∧
    ∀ a' b', (∀ n, (M.seam (a' + n)).1 = geoSliceRightRayDartEdge (d (b' + n))) →
      a ≤ a' ∧ b ≤ b'

/-- Helper toward Lemma 5.6: retained vertices of the intrinsic left
candidate after the strict vertex tails are removed. -/
@[expose] def geoSliceRightOneVertexKept (M : GeometricSideSubmap)
    (r : GeoSliceRightRay M) (a b v : ℕ) : Prop :=
  ∃ hv : v ∈ M.vertices,
    geometricSide_intrinsic_left M r.1 r.2 (.inl ⟨v, hv⟩) ∧
    (¬ ∃ n, a < n ∧ v = geometricSideDartInitial M (M.seam n)) ∧
    (¬ ∃ n, b < n ∧ v = match r.1 n with | .inl w => w.val | .inr _ => 0)

/-- Helper toward Lemma 5.6: retained geometric edges of the intrinsic left
candidate after both weak edge tails are removed. Both dart orientations are
required, so geometric edge identity is preserved. -/
@[expose] def geoSliceRightOneEdgeKept (M : GeometricSideSubmap)
    (r : GeoSliceRightRay M) (a b e : ℕ) : Prop :=
  ∃ he : e ∈ M.edges,
    geometricSide_intrinsic_left M r.1 r.2 (.inr ⟨(e, false), he⟩) ∧
    geometricSide_intrinsic_left M r.1 r.2 (.inr ⟨(e, true), he⟩) ∧
    (¬ ∃ n, a ≤ n ∧ e = (M.seam n).1) ∧
    (¬ ∃ n, b ≤ n ∧ e = geoSliceRightRayDartEdge (r.2 n))

/-- Helper toward Lemma 5.6: first return of the input rotation relation to a
retained geometric edge set, by a finite rotation chain. -/
@[expose] def geoSliceRightFirstReturn (M : GeometricSideSubmap)
    (E : Set ℕ) (d e : ℕ × Bool) : Prop :=
  d.1 ∈ E ∧ e.1 ∈ E ∧ ∃ n : ℕ, 0 < n ∧
    ∃ f : Fin (n + 1) → ℕ × Bool,
      f 0 = d ∧ f ⟨n, by omega⟩ = e ∧
      (∀ j : Fin n, M.rotation (f (Fin.castSucc j)) (f (Fin.succ j))) ∧
      ∀ j : Fin (n + 1), 0 < j.val → j.val < n → (f j).1 ∉ E

/-- Helper toward Lemma 5.6: the literal submap on the intrinsic left
candidate, with both marked tails removed. -/
@[expose] noncomputable def geoSliceRightOneSliceCore (M : GeometricSideSubmap)
    (r : GeoSliceRightRay M) (a b : ℕ) : GeometricSideSubmap where
  vertices := {v | geoSliceRightOneVertexKept M r a b v}
  edges := {e | geoSliceRightOneEdgeKept M r a b e}
  west := M.west
  east := M.east
  present := M.present
  rotation d e := geoSliceRightFirstReturn M
    {q | geoSliceRightOneEdgeKept M r a b q} d e
  faceNext d e := M.faceNext d e ∧
    d.1 ∈ {q | geoSliceRightOneEdgeKept M r a b q} ∧
    e.1 ∈ {q | geoSliceRightOneEdgeKept M r a b q} ∧
    (∃ hd : d.1 ∈ M.edges,
      geometricSide_intrinsic_left M r.1 r.2 (.inr ⟨d, hd⟩)) ∧
    (∃ he : e.1 ∈ M.edges,
      geometricSide_intrinsic_left M r.1 r.2 (.inr ⟨e, he⟩))
  root := M.root
  boundary := M.seam
  seam i := (geoSliceRightRayDartEdge (r.2 i), false)

/-- Helper toward Lemma 5.6: the right-side candidate determined by the
intrinsic right region, with its first-return rotation and shifted exterior
boundary mark. -/
@[expose] noncomputable def geoSliceRightNextSideCore (M : GeometricSideSubmap)
    (r : GeoSliceRightRay M) : GeometricSideSubmap where
  vertices := {v | ∃ hv : v ∈ M.vertices,
    geometricSide_intrinsic_right M r.1 r.2 (.inl ⟨v, hv⟩)}
  edges := {e | ∃ he : e ∈ M.edges,
    geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(e, false), he⟩) ∧
    geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(e, true), he⟩)}
  west := M.west
  east := M.east
  present := M.present
  rotation d e := geoSliceRightFirstReturn M
    {q | ∃ he : q ∈ M.edges,
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, false), he⟩) ∧
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, true), he⟩)} d e
  faceNext d e := M.faceNext d e ∧
    d.1 ∈ {q | ∃ he : q ∈ M.edges,
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, false), he⟩) ∧
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, true), he⟩)} ∧
    e.1 ∈ {q | ∃ he : q ∈ M.edges,
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, false), he⟩) ∧
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨(q, true), he⟩)} ∧
    (∃ hd : d.1 ∈ M.edges,
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨d, hd⟩)) ∧
    (∃ he : e.1 ∈ M.edges,
      geometricSide_intrinsic_right M r.1 r.2 (.inr ⟨e, he⟩))
  root := geometricSideDartInitial M ((M.boundary 0).1, !(M.boundary 0).2)
  boundary i := M.boundary (i + 1)
  seam i := (geoSliceRightRayDartEdge (r.2 i), false)

/-- Helper toward Lemma 5.6: the one-slice operation, returning `none` if
there is no unique intrinsic corner ray or no coordinatewise least aligned
tail pair. -/
@[expose] noncomputable def rightOneSlice (x : XDP) (M : GeometricSideSubmap) :
    Option GeometricSideClass := by
  classical
  exact if h : geoSliceRightRayUnique x M then
    let r := Classical.choose h
    if ho : ∃! q : ℕ × ℕ, geoSliceRightRayOffsets M r.2 q.1 q.2 then
      some (geometricSideClass (geoSliceRightOneSliceCore M r
        (Classical.choose ho).1 (Classical.choose ho).2))
    else none
  else none

/-- Helper toward Lemma 5.6: the next-side operation. A side with no unique
intrinsic corner ray is left unchanged; source realizations have the unique
ray supplied by the imported intrinsic source-identification theorem. -/
@[expose] noncomputable def rightNextSide (x : XDP) (M : GeometricSideSubmap) :
    GeometricSideSubmap := by
  classical
  exact if h : geoSliceRightRayUnique x M then
    geoSliceRightNextSideCore M (Classical.choose h)
  else M

/-- Helper toward Lemma 5.6: the unique intrinsic corner ray is preserved
by every complete marked-side isomorphism. -/
private theorem geoSliceRightRayUnique_markedIso_forward {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (x : XDP)
    (h : geoSliceRightRayUnique x M) : geoSliceRightRayUnique x N := by
  rcases h with ⟨r, hr, huniq⟩
  let r' : GeoSliceRightRay N := (I.equiv ∘ r.1, I.equiv ∘ r.2)
  have hr' := intrinsicallyLeftmostAdjacentRightRay_map I
    (geoSliceRightLongest x) hr
  refine ⟨r', hr', ?_⟩
  intro q hq
  have hqBack := intrinsicallyLeftmostAdjacentRightRay_map
    (GeometricSideMarkedIso.symm I) (geoSliceRightLongest x) hq
  have hback : (I.equiv.symm ∘ q.1, I.equiv.symm ∘ q.2) = r :=
    huniq _ hqBack
  apply Prod.ext
  · funext i
    have hi := congrFun (congrArg Prod.fst hback) i
    calc
      q.1 i = I.equiv (I.equiv.symm (q.1 i)) :=
        (I.equiv.apply_symm_apply _).symm
      _ = I.equiv (r.1 i) := congrArg I.equiv hi
  · funext i
    have hi := congrFun (congrArg Prod.snd hback) i
    calc
      q.2 i = I.equiv (I.equiv.symm (q.2 i)) :=
        (I.equiv.apply_symm_apply _).symm
      _ = I.equiv (r.2 i) := congrArg I.equiv hi

/-- Helper toward Lemma 5.6: unique intrinsic-ray existence is invariant
under complete marked-side isomorphisms. -/
theorem geoSliceRightRayUnique_markedIso_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (x : XDP) :
    geoSliceRightRayUnique x M ↔ geoSliceRightRayUnique x N := by
  constructor
  · exact geoSliceRightRayUnique_markedIso_forward I x
  · exact geoSliceRightRayUnique_markedIso_forward (GeometricSideMarkedIso.symm I) x







































































































end DirectedDistances.PaperProofs.Section5
