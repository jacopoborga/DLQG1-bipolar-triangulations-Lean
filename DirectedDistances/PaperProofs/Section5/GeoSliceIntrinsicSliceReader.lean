/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice2
public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReaders2

/-! The code-level slice candidate is extracted intrinsically from one marked
side. Its probabilistic identification with the source slice is separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: a vertex ID belongs to the intrinsic right
candidate when its corresponding side cell does. -/
@[expose] def geoSliceIntrinsicRightVertex
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) (longest : Bool)
    (hc : geoSliceSeamRayCandidate longest M p) (v : ℕ) (hv : v ∈ M.vertices) : Prop :=
  geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
    (geoSliceSeamRayDartCells hc) (.inl ⟨v, hv⟩)

/-- Helper toward Lemma 5.6: a geometric edge ID belongs to the intrinsic
right candidate only when both of its oriented darts do. This preserves the
whole-edge convention of `GeometricSideSubmap.edges`. -/
@[expose] def geoSliceIntrinsicRightEdge
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) (longest : Bool)
    (hc : geoSliceSeamRayCandidate longest M p) (e : ℕ) (he : e ∈ M.edges) : Prop :=
  geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
    (geoSliceSeamRayDartCells hc) (.inr ⟨(e, false), he⟩) ∧
  geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
    (geoSliceSeamRayDartCells hc) (.inr ⟨(e, true), he⟩)

/-- Helper toward Lemma 5.6: a raw vertex is retained by the intrinsic
candidate after removing the strict tails beyond both least offsets. -/
@[expose] def geoSliceIntrinsicVertexKept
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) (longest : Bool)
    (hc : geoSliceSeamRayCandidate longest M p) (a b v : ℕ) : Prop :=
  v ∈ M.vertices ∧ ∃ hv : v ∈ M.vertices,
    geoSliceIntrinsicRightVertex M p longest hc v hv ∧
    (¬ ∃ i, a < i ∧ v = M.west (geoSliceSeamRayEdge M p i)) ∧
    (¬ ∃ i, b < i ∧ v = geometricSideDartInitial M (M.seam i))

/-- Helper toward Lemma 5.6: a raw edge is retained by the intrinsic
candidate after deleting both edge tails starting at their offsets. -/
@[expose] def geoSliceIntrinsicEdgeKept
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) (longest : Bool)
    (hc : geoSliceSeamRayCandidate longest M p) (a b e : ℕ) : Prop :=
  e ∈ M.edges ∧ ∃ he : e ∈ M.edges,
    geoSliceIntrinsicRightEdge M p longest hc e he ∧
    (¬ ∃ i, a ≤ i ∧ e = geoSliceSeamRayEdge M p i) ∧
    (¬ ∃ i, b ≤ i ∧ e = (M.seam i).1)

/-- Helper toward Lemma 5.6: the intrinsic slice determined by one side,
a decoded adjacent ray, and its two least offsets. The vertex tails are
strict (`a < i`, `b < i`); edge tails start at the offsets (`a ≤ i`,
`b ≤ i`). A face-successor is kept precisely when it is a face-successor
in the input side and both oriented corner darts lie in the intrinsic
right candidate and in the retained geometric edge carrier. The rotation
is the first return of the input side's rotation relation to a retained
edge: the finite chain may visit deleted input-side edges, but no interior
dart may already be retained. -/
@[expose] def geoSliceIntrinsicSliceCore
    (longest : Bool) (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode)
    (hc : geoSliceSeamRayCandidate longest M p) (a b : ℕ) : GeometricSideSubmap where
  vertices := {v | geoSliceIntrinsicVertexKept M p longest hc a b v}
  edges := {e | geoSliceIntrinsicEdgeKept M p longest hc a b e}
  west := M.west
  east := M.east
  present := M.present
  rotation d e :=
    e.1 ∈ {q | geoSliceIntrinsicEdgeKept M p longest hc a b q} ∧
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin (n + 1) → ℕ × Bool,
      f 0 = d ∧ f ⟨n, Nat.lt_succ_self n⟩ = e ∧
      (∀ j : Fin n, M.rotation (f (Fin.castSucc j)) (f (Fin.succ j))) ∧
      ∀ j : Fin (n + 1), 0 < j.val → j.val < n →
        (f j).1 ∉ {q | geoSliceIntrinsicEdgeKept M p longest hc a b q}
  faceNext d e := ∃ hd : d.1 ∈ M.edges, ∃ he : e.1 ∈ M.edges,
    M.faceNext d e ∧
    d.1 ∈ {q | geoSliceIntrinsicEdgeKept M p longest hc a b q} ∧
    e.1 ∈ {q | geoSliceIntrinsicEdgeKept M p longest hc a b q} ∧
    geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
      (geoSliceSeamRayDartCells hc) (.inr ⟨d, hd⟩) ∧
    geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
      (geoSliceSeamRayDartCells hc) (.inr ⟨e, he⟩)
  root := M.west (geoSliceSeamRayEdge M p 0)
  boundary i := (geoSliceSeamRayEdge M p i, false)
  seam := M.seam

/-- Helper toward Lemma 5.6: read the side's own adjacent ray and least
offset pair, returning `none` if either fixed reader fails. -/
@[expose] noncomputable def intrinsicSliceOfSide (longest : Bool)
    (M : GeometricSideSubmap) : Option GeometricSideSubmap := do
  match hr : geoSliceOneSideRayCodeOption longest M with
  | none => none
  | some p =>
    match _hoff : geoSliceOneSideOffsetsOption longest M with
    | none => none
    | some ab =>
      some (geoSliceIntrinsicSliceCore longest M p
        ((geoSliceOneSideRayCodeOption_eq_some_iff longest M p).1 hr).1.1 ab.1 ab.2)


































































end DirectedDistances.PaperProofs.Section5
