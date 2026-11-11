/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction3

/-! Transport of the common-tail deletions in the enclosed-slice carrier.
The restriction to the region on the right of the preceding ray remains
separate from deletion of the tails; no enclosed-slice reader is asserted. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: the cells deleted after a ray's cut offset.
Vertices strictly after the offset are deleted. Both darts of every edge
at or after the offset are deleted, retaining geometric edge identity. -/
@[expose] def geometricSideRayDeletedTailCells (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (a : ℕ) : Set (GeometricSideCell M) :=
  {c | (∃ n, a < n ∧ c = v n) ∨
    ∃ n, a ≤ n ∧ (c = d n ∨ geometricSideRelation M .opposite (d n) c)}

/-- Helper toward Lemma 5.6: deleting a ray's strict vertex tail and
both darts of its edge tail commutes with every marked-side isomorphism. -/
theorem geometricSideRayDeletedTailCells_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (a : ℕ) (c : GeometricSideCell M) :
    c ∈ geometricSideRayDeletedTailCells M v d a ↔
      I.equiv c ∈ geometricSideRayDeletedTailCells N
        (I.equiv ∘ v) (I.equiv ∘ d) a := by
  constructor
  · rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc | hc⟩)
    · exact Or.inl ⟨n, hn, congrArg I.equiv hc⟩
    · exact Or.inr ⟨n, hn, Or.inl (congrArg I.equiv hc)⟩
    · exact Or.inr ⟨n, hn, Or.inr ((I.relation_iff _ _ _).1 hc)⟩
  · rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc | hc⟩)
    · exact Or.inl ⟨n, hn, I.equiv.injective hc⟩
    · exact Or.inr ⟨n, hn, Or.inl (I.equiv.injective hc)⟩
    · exact Or.inr ⟨n, hn, Or.inr ((I.relation_iff _ _ _).2 hc)⟩

/-- Helper toward Lemma 5.6: for concrete vertex and forward-dart
sequences, the intrinsic deletion set has the exact strict-vertex and
weak-edge endpoint conventions used by `m0CutGeodesicSlice`. -/
theorem geometricSideRayDeletedTailCells_mem_iff
    (M : GeometricSideSubmap) (v : ℕ → M.vertices)
    (q : ℕ → ℕ) (hq : ∀ n, q n ∈ M.edges) (a : ℕ)
    (c : GeometricSideCell M) :
    c ∈ geometricSideRayDeletedTailCells M (fun n => .inl (v n))
        (fun n => .inr ⟨(q n, false), hq n⟩) a ↔
      match c with
      | .inl u => ∃ n, a < n ∧ u.val = (v n).val
      | .inr e => e.val.1 ∈ Set.range (fun n => q (a + n)) := by
  cases c with
  | inl u =>
    change ((∃ n, a < n ∧ Sum.inl u = Sum.inl (v n)) ∨
      ∃ n, a ≤ n ∧ (Sum.inl u = Sum.inr _ ∨ False)) ↔ _
    simp only [Sum.inl.injEq, Sum.inl_ne_inr, or_self, and_false, exists_false,
      or_false, Subtype.ext_iff]
  | inr e =>
    change ((∃ n, a < n ∧ Sum.inr e = Sum.inl (v n)) ∨
      ∃ n, a ≤ n ∧ (Sum.inr e = Sum.inr _ ∨ (q n, true) = e.val)) ↔ _
    simp only [Sum.inr_ne_inl, and_false, exists_false, false_or,
      Sum.inr.injEq, Subtype.ext_iff]
    constructor
    · rintro ⟨n, hn, he | he⟩
      · exact ⟨n - a, by simpa only [Nat.add_sub_of_le hn] using
          (congrArg (fun z : ℕ × Bool => z.1) he).symm⟩
      · exact ⟨n - a, by simpa only [Nat.add_sub_of_le hn] using
          (congrArg (fun z : ℕ × Bool => z.1) he)⟩
    · rintro ⟨n, hn⟩
      refine ⟨a + n, Nat.le_add_right a n, ?_⟩
      cases hb : e.val.2 with
      | false => exact Or.inl (Prod.ext hn.symm hb)
      | true => exact Or.inr (Prod.ext hn hb.symm)

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the two deletion sets of the actual slice,
as a set of cells of the current closed-left side. This definition makes
no assertion about which side of the preceding ray a surviving cell lies. -/
@[expose] def m0GeodesicLeftSideDeletedTailCells
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) : Set (GeometricSideCell (m0GeodesicSide hp (P k) .left)) :=
  {c | match c with
    | .inl u =>
      (∃ n, a < n ∧ u.val = ((P (k - 1)).codePath.initial n).1.id) ∨
        ∃ n, b < n ∧ u.val = ((P k).codePath.initial n).1.id
    | .inr e =>
      e.val.1 ∈ Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n))}

/-- Helper toward Lemma 5.6: the actual common-tail deletion is the
union of the two intrinsic ray deletion sets, including zero offsets. -/
theorem m0GeodesicLeftSideDeletedTailCells_eq
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (a b : ℕ) :
    m0GeodesicLeftSideDeletedTailCells hp P k a b =
      geometricSideRayDeletedTailCells _
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∪
      geometricSideRayDeletedTailCells _
        (m0GeodesicSideSeamVertexCell hp (P k) .left)
        (m0GeodesicSideSeamDartCell hp (P k) .left) b := by
  ext c
  have hprev := geometricSideRayDeletedTailCells_mem_iff
    (m0GeodesicSide hp (P k) .left)
    (fun n => ⟨((P (k - 1)).codePath.initial n).1.id, (hcontain n).2⟩)
    (P (k - 1)).codePath.edge (fun n => (hcontain n).1) a c
  have hcurr := geometricSideRayDeletedTailCells_mem_iff
    (m0GeodesicSide hp (P k) .left)
    (fun n => ⟨((P k).codePath.initial n).1.id,
      by
        have hv := m0Geodesic_initial_mem_vertices (P k) n
        rw [← m0GeodesicSideVertices_inter hp (P k)] at hv
        exact hv.1⟩)
    (P k).codePath.edge (fun n =>
      (m0GeodesicEdges_subset_both hp (P k) (m0GeodesicSeam_mem_edges (P k) n)).1)
    b c
  change c ∈ geometricSideRayDeletedTailCells _
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain) a ↔ _ at hprev
  change c ∈ geometricSideRayDeletedTailCells _
    (m0GeodesicSideSeamVertexCell hp (P k) .left)
    (m0GeodesicSideSeamDartCell hp (P k) .left) b ↔ _ at hcurr
  change _ ↔ _ ∨ _
  rw [hprev, hcurr]
  cases c <;> rfl

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

include hleft hleft' hcontain hcontain' in
/-- Helper toward Lemma 5.6: a marked isomorphism between realized left
sides preserves exactly the two tail deletions used by their slice carriers.
The preceding ray is identified by the proved selector, not a new premise.
The offsets are arbitrary here, so in particular may be the common least pair. -/
theorem m0GeodesicLeftSide_markedIso_deletedTailCells_iff
    (a b : ℕ) (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    c ∈ m0GeodesicLeftSideDeletedTailCells hp P k a b ↔
      I.equiv c ∈ m0GeodesicLeftSideDeletedTailCells hp' P' l a b := by
  obtain ⟨hv, hd⟩ := m0GeodesicLeftSide_markedIso_map_previousRay
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I
  have hsv : I.equiv ∘ m0GeodesicSideSeamVertexCell hp (P k) .left =
      m0GeodesicSideSeamVertexCell hp' (P' l) .left := by
    funext n
    exact m0GeodesicLeftSide_markedIso_map_seamVertex hp hp' P P' k l I n
  have hsd : I.equiv ∘ m0GeodesicSideSeamDartCell hp (P k) .left =
      m0GeodesicSideSeamDartCell hp' (P' l) .left := by
    funext n
    exact m0GeodesicLeftSide_markedIso_map_seamDart hp hp' P P' k l I n
  rw [m0GeodesicLeftSideDeletedTailCells_eq hp P k hcontain,
    m0GeodesicLeftSideDeletedTailCells_eq hp' P' l hcontain']
  change (_ ∨ _) ↔ (_ ∨ _)
  have hprev := geometricSideRayDeletedTailCells_map_iff I
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain) a c
  have hcurr := geometricSideRayDeletedTailCells_map_iff I
    (m0GeodesicSideSeamVertexCell hp (P k) .left)
    (m0GeodesicSideSeamDartCell hp (P k) .left) b c
  rw [hv, hd] at hprev
  rw [hsv, hsd] at hcurr
  exact or_congr hprev hcurr

/-- Helper toward Lemma 5.6: the same isomorphism restricts to an
equivalence on the surviving cells after deleting both common tails.
These are surviving left-side cells, not yet the enclosed-slice cells. -/
@[expose] def m0GeodesicLeftSideMarkedIsoTailComplement (a b : ℕ) :
    {c : GeometricSideCell (m0GeodesicSide hp (P k) .left) //
      c ∉ m0GeodesicLeftSideDeletedTailCells hp P k a b} ≃
    {c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left) //
      c ∉ m0GeodesicLeftSideDeletedTailCells hp' P' l a b} where
  toFun c := ⟨I.equiv c.val, fun hc => c.property
    ((m0GeodesicLeftSide_markedIso_deletedTailCells_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b c.val).2 hc)⟩
  invFun c := ⟨I.equiv.symm c.val, fun hc => c.property (by
    have hm := (m0GeodesicLeftSide_markedIso_deletedTailCells_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b
      (I.equiv.symm c.val)).1 hc
    simpa only [Equiv.apply_symm_apply] using hm)⟩
  left_inv c := Subtype.ext (I.equiv.symm_apply_apply c.val)
  right_inv c := Subtype.ext (I.equiv.apply_symm_apply c.val)

/-- Helper toward Lemma 5.6: the tail-complement equivalence preserves
all inherited relations, including face succession, plane rotation and
each indexed mark, on its surviving cells. It does not identify which of
these cells lie in the enclosed region. -/
theorem m0GeodesicLeftSideMarkedIsoTailComplement_relation_iff
    (a b : ℕ) (t : TruncationRelation)
    (c d : {c : GeometricSideCell (m0GeodesicSide hp (P k) .left) //
      c ∉ m0GeodesicLeftSideDeletedTailCells hp P k a b}) :
    geometricSideRelation (m0GeodesicSide hp (P k) .left) t c.val d.val ↔
      geometricSideRelation (m0GeodesicSide hp' (P' l) .left) t
        (m0GeodesicLeftSideMarkedIsoTailComplement
          hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b c).val
        (m0GeodesicLeftSideMarkedIsoTailComplement
          hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b d).val :=
  I.relation_iff t c.val d.val

end TwoRealizations

/-- Helper toward Lemma 5.6: inside the current left side, actual slice
membership is exactly surviving tail deletion together with membership in
the preceding ray's right side. The latter geometric restriction remains
the enclosure-transport obligation. -/
theorem m0CutGeodesicSlice_mem_cell_iff_previousRight_and_not_deletedTail
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    (match c with
     | .inl v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
     | .inr d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) ↔
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right) ∧
        c ∉ m0GeodesicLeftSideDeletedTailCells hp P k a b := by
  cases c with
  | inl v =>
    change ((v.val ∈ _ ∧ v.val ∈ _) ∧ ¬ _) ↔ _
    exact ⟨fun hv => ⟨hv.1.1, hv.2⟩, fun hv => ⟨⟨hv.1, v.property⟩, hv.2⟩⟩
  | inr d =>
    change ((d.val.1 ∈ _ ∧ d.val.1 ∈ _) ∧ ¬ _) ↔ _
    exact ⟨fun hd => ⟨hd.1.1, hd.2⟩, fun hd => ⟨⟨hd.1, d.property⟩, hd.2⟩⟩
































































end DirectedDistances.PaperProofs.Section5
