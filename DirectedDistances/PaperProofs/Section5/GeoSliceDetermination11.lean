/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination10
public import DirectedDistances.PaperProofs.Section5.GeometricSideClass

/-! Intrinsic directed paths in a marked side and their isomorphism invariance.
These constructions require neither an embedding nor an ambient enclosure.
They do not select the leftmost ray or reconstruct the full slice. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: one present directed edge, retaining its dart
and its opposite. Missing geometric edges cannot witness this relation. -/
@[expose] def geometricSideDirectedStep (M : GeometricSideSubmap)
    (u v : GeometricSideCell M) : Prop :=
  ∃ d e : GeometricSideCell M,
    geometricSideRelation M .oriented d d ∧
    geometricSideRelation M .incident d u ∧
    geometricSideRelation M .opposite d e ∧
    geometricSideRelation M .incident e v

/-- Helper toward Lemma 5.6: marked isomorphisms transport present steps. -/
theorem geometricSideDirectedStep_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {u v : GeometricSideCell M}
    (h : geometricSideDirectedStep M u v) :
    geometricSideDirectedStep N (I.equiv u) (I.equiv v) := by
  obtain ⟨d, e, ho, hu, he, hv⟩ := h
  exact ⟨I.equiv d, I.equiv e, (I.relation_iff _ _ _).1 ho,
    (I.relation_iff _ _ _).1 hu, (I.relation_iff _ _ _).1 he,
    (I.relation_iff _ _ _).1 hv⟩

/-- Helper toward Lemma 5.6: the relational step is exactly the side's own
present-edge incidence, with the individual edge ID retained as a witness. -/
theorem geometricSideDirectedStep_vertices_iff (M : GeometricSideSubmap)
    (u v : M.vertices) :
    geometricSideDirectedStep M (.inl u) (.inl v) ↔
      ∃ f ∈ M.edges, f ∈ M.present ∧ M.west f = u.val ∧ M.east f = v.val := by
  constructor
  · rintro ⟨d, e, ho, hu, he, hv⟩
    cases d with
    | inl z => exact False.elim ho
    | inr d =>
      obtain ⟨hp, hb⟩ := ho
      cases e with
      | inl z => exact False.elim he
      | inr e =>
        have hi : (d.val.1, !d.val.2) = e.val := he
        have hu' : (if d.val.2 then M.east d.val.1 else M.west d.val.1) = u.val := hu
        have hv' : (if e.val.2 then M.east e.val.1 else M.west e.val.1) = v.val := hv
        rw [← hi, hb] at hv'
        rw [hb] at hu'
        exact ⟨d.val.1, d.property, hp, hu', hv'⟩
  · rintro ⟨f, hf, hp, hu, hv⟩
    exact ⟨.inr ⟨(f, false), hf⟩, .inr ⟨(f, true), hf⟩,
      ⟨hp, rfl⟩, hu, rfl, hv⟩



inductive GeometricSideDirectedWalk (M : GeometricSideSubmap) :
    ℕ → GeometricSideCell M → GeometricSideCell M → Prop
  | nil (u) : GeometricSideDirectedWalk M 0 u u
  | cons {n u v w} : geometricSideDirectedStep M u v →
      GeometricSideDirectedWalk M n v w → GeometricSideDirectedWalk M (n + 1) u w

/-- Helper toward Lemma 5.6: marked isomorphisms preserve every walk length. -/
theorem geometricSideDirectedWalk_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {n : ℕ} {u v : GeometricSideCell M}
    (h : GeometricSideDirectedWalk M n u v) :
    GeometricSideDirectedWalk N n (I.equiv u) (I.equiv v) := by
  induction h with
  | nil u => exact .nil _
  | cons hs _ ih => exact .cons (geometricSideDirectedStep_map I hs) ih

/-- Helper toward Lemma 5.6: preservation of walks is an equivalence. -/
theorem geometricSideDirectedWalk_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (n : ℕ) (u v : GeometricSideCell M) :
    GeometricSideDirectedWalk M n u v ↔
      GeometricSideDirectedWalk N n (I.equiv u) (I.equiv v) := by
  constructor
  · exact geometricSideDirectedWalk_map I
  · intro h
    simpa only [GeometricSideMarkedIso.symm, Equiv.symm_apply_apply] using
      geometricSideDirectedWalk_map (GeometricSideMarkedIso.symm I) h

/-- Helper toward Lemma 5.6: an attained optimal length, with a single mode
parameter for LDP (`true`) and SDP (`false`). Unbounded lengths yield no LDP
optimum; unreachable pairs yield no optimum in either mode. -/
@[expose] def geometricSideOptimalLength (M : GeometricSideSubmap)
    (longest : Bool) (n : ℕ) (u v : GeometricSideCell M) : Prop :=
  GeometricSideDirectedWalk M n u v ∧
    ∀ m, GeometricSideDirectedWalk M m u v → if longest then m ≤ n else n ≤ m

/-- Helper toward Lemma 5.6: both modes of attained optimal length are
intrinsic to marked-isomorphism classes; no finiteness premise is needed. -/
theorem geometricSideOptimalLength_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool) (n : ℕ)
    (u v : GeometricSideCell M) :
    geometricSideOptimalLength M longest n u v ↔
      geometricSideOptimalLength N longest n (I.equiv u) (I.equiv v) := by
  constructor
  · rintro ⟨hn, hopt⟩
    exact ⟨(geometricSideDirectedWalk_iff I n u v).1 hn,
      fun m hm => hopt m ((geometricSideDirectedWalk_iff I m u v).2 hm)⟩
  · rintro ⟨hn, hopt⟩
    exact ⟨(geometricSideDirectedWalk_iff I n u v).2 hn,
      fun m hm => hopt m ((geometricSideDirectedWalk_iff I m u v).1 hm)⟩

/-- Helper toward Lemma 5.6: a ray records vertices and individual directed
darts, so parallel edges are not identified. Only relations of the side occur. -/
@[expose] def geometricSideDirectedRay (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) : Prop :=
  ∀ i, geometricSideRelation M .oriented (d i) (d i) ∧
    geometricSideRelation M .incident (d i) (v i) ∧
    ∃ e, geometricSideRelation M .opposite (d i) e ∧
      geometricSideRelation M .incident e (v (i + 1))

/-- Helper toward Lemma 5.6: directed rays transport with their edge identity. -/
theorem geometricSideDirectedRay_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {v d : ℕ → GeometricSideCell M}
    (h : geometricSideDirectedRay M v d) :
    geometricSideDirectedRay N (I.equiv ∘ v) (I.equiv ∘ d) := by
  intro i
  obtain ⟨ho, hi, e, he, ht⟩ := h i
  exact ⟨(I.relation_iff _ _ _).1 ho, (I.relation_iff _ _ _).1 hi,
    I.equiv e, (I.relation_iff _ _ _).1 he, (I.relation_iff _ _ _).1 ht⟩

/-- Helper toward Lemma 5.6: every finite segment of an intrinsic ray is
a walk of the stated length, including length zero. -/
theorem geometricSideDirectedRay_walk {M : GeometricSideSubmap}
    {v d : ℕ → GeometricSideCell M} (h : geometricSideDirectedRay M v d)
    (i n : ℕ) : GeometricSideDirectedWalk M n (v i) (v (i + n)) := by
  induction n generalizing i with
  | zero => exact .nil _
  | succ n ih =>
    obtain ⟨ho, hi, e, he, ht⟩ := h i
    have hw := GeometricSideDirectedWalk.cons ⟨d i, e, ho, hi, he, ht⟩ (ih (i + 1))
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hw

/-- Helper toward Lemma 5.6: the metric part of an adjacent-ray candidate.
The initial vertex is the initial vertex of exterior-boundary dart 1; on a
realized left side at k this is x_(k-1). Every segment has the chosen optimal
length inside the side. Leftmostness is deliberately a separate open step. -/
@[expose] def geometricSideAdjacentGeodesicCandidate (M : GeometricSideSubmap)
    (longest : Bool) (v d : ℕ → GeometricSideCell M) : Prop :=
  geometricSideDirectedRay M v d ∧
    (∃ b, geometricSideRelation M (.boundary 1) b b ∧
      geometricSideRelation M .incident b (v 0)) ∧
    ∀ i n, geometricSideOptimalLength M longest n (v i) (v (i + n))

/-- Helper toward Lemma 5.6: every adjacent metric candidate transports
under a marked isomorphism, without choosing a representative of a quotient. -/
theorem geometricSideAdjacentGeodesicCandidate_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M}
    (h : geometricSideAdjacentGeodesicCandidate M longest v d) :
    geometricSideAdjacentGeodesicCandidate N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  obtain ⟨hr, ⟨b, hb, hi⟩, hg⟩ := h
  exact ⟨geometricSideDirectedRay_map I hr,
    ⟨I.equiv b, (I.relation_iff _ _ _).1 hb, (I.relation_iff _ _ _).1 hi⟩,
    fun i n => (geometricSideOptimalLength_iff I longest n _ _).1 (hg i n)⟩

/-- Helper toward Lemma 5.6: attained optimal lengths from an indexed
exterior-boundary vertex to an indexed seam vertex, entirely within the side. -/
@[expose] def geometricSideBoundarySeamLengths (M : GeometricSideSubmap)
    (longest : Bool) (i j : ℕ) : Set ℕ :=
  {n | ∃ b s u v : GeometricSideCell M,
    geometricSideRelation M (.boundary i) b b ∧
    geometricSideRelation M (.seam j) s s ∧
    geometricSideRelation M .incident b u ∧
    geometricSideRelation M .incident s v ∧
    geometricSideOptimalLength M longest n u v}

/-- Helper toward Lemma 5.6: the boundary-to-seam optimal-length observable
is invariant under marked isomorphism. -/
theorem geometricSideBoundarySeamLengths_eq {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool) (i j : ℕ) :
    geometricSideBoundarySeamLengths M longest i j =
      geometricSideBoundarySeamLengths N longest i j := by
  have transport {A B : GeometricSideSubmap} (J : GeometricSideMarkedIso A B)
      {n : ℕ} (h : n ∈ geometricSideBoundarySeamLengths A longest i j) :
      n ∈ geometricSideBoundarySeamLengths B longest i j := by
    obtain ⟨b, s, u, v, hb, hs, hu, hv, hn⟩ := h
    exact ⟨J.equiv b, J.equiv s, J.equiv u, J.equiv v,
      (J.relation_iff _ _ _).1 hb, (J.relation_iff _ _ _).1 hs,
      (J.relation_iff _ _ _).1 hu, (J.relation_iff _ _ _).1 hv,
      (geometricSideOptimalLength_iff J longest n u v).1 hn⟩
  exact Set.Subset.antisymm (fun _ => transport I)
    (fun _ => transport (GeometricSideMarkedIso.symm I))

/-- Helper toward Lemma 5.6: descent of the intrinsic length observable to
the actual marked-side quotient. This is a set-valued metric observable,
not a slice extractor or a measurability assertion. -/
@[expose] def geometricSideClassBoundarySeamLengths (longest : Bool) (i j : ℕ) :
    GeometricSideClass → Set ℕ :=
  Quotient.lift (fun M => geometricSideBoundarySeamLengths M longest i j)
    (fun _ _ h => h.elim fun I => geometricSideBoundarySeamLengths_eq I longest i j)

/-- Helper toward Lemma 5.6: the descended observable has exactly its
intrinsic value on every marked-side representative. -/
theorem geometricSideClassBoundarySeamLengths_mk (M : GeometricSideSubmap)
    (longest : Bool) (i j : ℕ) :
    geometricSideClassBoundarySeamLengths longest i j (geometricSideClass M) =
      geometricSideBoundarySeamLengths M longest i j := rfl

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the adjacent ray's starting vertex needs no
extra mark. It is already the initial vertex of exterior-boundary dart 1,
including when that geometric boundary edge is missing from the directed map. -/
theorem m0GeodesicLeftSide_adjacent_start
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    geometricSideDartInitial (m0GeodesicSide hp P .left)
      ((m0GeodesicSide hp P .left).boundary 1) =
        boundaryVertex (shiftedStream W 0) h (k - 1) := by
  change kmswLimitDartVertex (shiftedStream W 0)
    (m0GeodesicBoundaryDart (shiftedStream W 0) h k .left 1) = _
  exact m0GeodesicBoundaryDart_left_vertex (shiftedStream W 0) h k 1

/-- Helper toward Lemma 5.6: the seam's vertex cells in a realized side,
using the proved intersection characterization, without adding containment. -/
@[expose] noncomputable def m0GeodesicSideSeamVertexCell
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (n : ℕ) :
    GeometricSideCell (m0GeodesicSide hp P s) :=
  .inl ⟨(P.codePath.initial n).1.id, by
    have hv := m0Geodesic_initial_mem_vertices P n
    rw [← m0GeodesicSideVertices_inter hp P] at hv
    cases s with
    | left => exact hv.1
    | right => exact hv.2⟩

/-- Helper toward Lemma 5.6: the seam's forward dart cells in a realized
side, preserving the geometric edge IDs and their reversal bits. -/
@[expose] noncomputable def m0GeodesicSideSeamDartCell
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (n : ℕ) :
    GeometricSideCell (m0GeodesicSide hp P s) :=
  .inr ⟨(P.codePath.edge n, false), by
    have he := m0GeodesicEdges_subset_both hp P
      (m0GeodesicSeam_mem_edges P n)
    cases s with
    | left => exact he.1
    | right => exact he.2⟩

/-- Helper toward Lemma 5.6: the realized seam is a directed ray for the
intrinsic relational definition. This validates the incidence interpretation
on actual sides, without a geometric realization in that definition. -/
theorem m0GeodesicSide_seam_directedRay
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    geometricSideDirectedRay (m0GeodesicSide hp P s)
      (m0GeodesicSideSeamVertexCell hp P s) (m0GeodesicSideSeamDartCell hp P s) := by
  intro n
  have hout := P.codePath.edge_outgoing_at_initial (shiftedStream W 0) n
  have hin := P.codePath.edge_incoming_at_succ (shiftedStream W 0) n
  refine ⟨⟨hout.1, rfl⟩, hout.2, ?_⟩
  refine ⟨.inr ⟨(P.codePath.edge n, true), ?_⟩, rfl, hin.2⟩
  have he := m0GeodesicEdges_subset_both hp P (m0GeodesicSeam_mem_edges P n)
  cases s with
  | left => exact he.1
  | right => exact he.2

/-- Helper toward Lemma 5.6: intrinsic walks in a realized side lift to
actual present-edge paths of the same length. No ambient path can be created
by a missing geometric edge. -/
theorem m0GeodesicSide_walk_lifts
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (n : ℕ) (u v : (m0GeodesicSide hp P s).vertices)
    (hw : GeometricSideDirectedWalk (m0GeodesicSide hp P s) n (.inl u) (.inl v)) :
    ∃ p : Quiver.Path (⟨u.val⟩ : PresentVertex (shiftedStream W 0)) ⟨v.val⟩,
      p.length = n := by
  induction n generalizing u v with
  | zero =>
    cases hw
    exact ⟨.nil, rfl⟩
  | succ n ih =>
    cases hw with
    | @cons _ _ z _ hs ht =>
      cases z with
      | inl z =>
        obtain ⟨f, _, hf, hfu, hfz⟩ :=
          (geometricSideDirectedStep_vertices_iff _ u z).1 hs
        obtain ⟨p, hplen⟩ := ih z v ht
        let a : (⟨u.val⟩ : PresentVertex (shiftedStream W 0)) ⟶ ⟨z.val⟩ :=
          ⟨f, hf, hfu, hfz⟩
        refine ⟨a.toPath.comp p, ?_⟩
        simp only [Quiver.Path.length_comp, hplen]
        exact Nat.add_comm 1 n
      | inr z =>
        obtain ⟨d, e, _, _, _, he⟩ := hs
        cases e <;> exact False.elim he

/-- Helper toward Lemma 5.6: the realized seam has intrinsically optimal
segments for both LDP and SDP, including zero-length segments. This transfers
metric optimality through actual present-edge paths, rather than assuming a
side-local geodesic identification. -/
theorem m0GeodesicSide_seam_optimalLength
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (i n : ℕ) :
    geometricSideOptimalLength (m0GeodesicSide hp P s) longest n
      (m0GeodesicSideSeamVertexCell hp P s i)
      (m0GeodesicSideSeamVertexCell hp P s (i + n)) := by
  refine ⟨geometricSideDirectedRay_walk (m0GeodesicSide_seam_directedRay hp P s) i n,
    ?_⟩
  intro m hm
  obtain ⟨r, hr⟩ := m0GeodesicSide_walk_lifts hp P s m _ _ hm
  obtain ⟨p, q, hpq, _, hq, _⟩ := P.codePath.exists_shift_split i n
  cases longest with
  | false =>
    have hopt := P.codePath.initial_isShortest (shiftedStream W 0) P.segments (i + n)
    rw [hpq] at hopt
    have hle := hopt.of_comp_right r
    change n ≤ m
    simpa only [hq, hr] using hle
  | true =>
    have hopt := P.codePath.initial_isLongest (shiftedStream W 0) P.segments (i + n)
    rw [hpq] at hopt
    have hle := hopt.of_comp_right r
    change m ≤ n
    simpa only [hq, hr] using hle












































































































end DirectedDistances.PaperProofs.Section5
