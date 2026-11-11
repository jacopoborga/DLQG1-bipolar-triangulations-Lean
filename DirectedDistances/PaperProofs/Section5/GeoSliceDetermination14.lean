/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination13

/- Existence of the adjacent metric candidate in the stored left side, including
its simultaneous almost-sure version. A relation-only clockwise selector
predicate is invariant under marked isomorphism. Its agreement with the -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the indexed left exterior boundary is retained
as geometric edges, including edges missing from the directed map. -/
theorem m0GeodesicLeftSide_boundary_mem_edges
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    ((m0GeodesicSide hp P .left).boundary i).1 ∈
      (m0GeodesicSide hp P .left).edges := by
  change ∀ z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
    (wholePlaneDartι W 0
      (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), false))).image,
    z ∈ m0GeodesicSideRegion hp P .left
  intro z hz
  have ha := m0Geodesic_arc_subset_ambient hp
    (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ))) hz
  have hg := hz
  rw [m0CutBoundaryEdgeTrace_eq_graphOver hp] at hg
  refine ⟨m0CutGeodesic_mem_closure_leftOpen_of_re_le_root hp P ha ?_, ha⟩
  exact hg.2.1.trans ((seamX_strictMono (shiftedStream W 0) h (H.1 0)).monotone
    (by omega))

/-- Helper toward Lemma 5.6: the actual adjacent geodesic gives an intrinsic
metric candidate. `hcontain` is the standing almost-sure containment fact
supplied by `m0Cut_ae_realizedLeftSideSlice_eq`, not a selection hypothesis. -/
theorem m0GeodesicSide_adjacentCandidate
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSideAdjacentGeodesicCandidate
        (m0GeodesicSide hp (P k) .left) longest v d := by
  let M := m0GeodesicSide hp (P k) .left
  let v : ℕ → GeometricSideCell M := fun n =>
    .inl ⟨((P (k - 1)).codePath.initial n).1.id, (hcontain n).2⟩
  let d : ℕ → GeometricSideCell M := fun n =>
    .inr ⟨((P (k - 1)).codePath.edge n, false), (hcontain n).1⟩
  have hr : geometricSideDirectedRay M v d := by
    intro n
    have hout := (P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) n
    have hin := (P (k - 1)).codePath.edge_incoming_at_succ (shiftedStream W 0) n
    exact ⟨⟨hout.1, rfl⟩, hout.2,
      .inr ⟨((P (k - 1)).codePath.edge n, true), (hcontain n).1⟩, rfl, hin.2⟩
  refine ⟨v, d, hr, ?_, ?_⟩
  · refine ⟨.inr ⟨M.boundary 1,
      m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩, rfl, ?_⟩
    change geometricSideDartInitial M (M.boundary 1) =
      ((P (k - 1)).codePath.initial 0).1.id
    exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
      (m0Geodesic_initial_zero (P (k - 1))).symm
  · intro i n
    refine ⟨geometricSideDirectedRay_walk hr i n, ?_⟩
    intro m hm
    obtain ⟨r, hrlen⟩ := m0GeodesicSide_walk_lifts hp (P k) .left m _ _ hm
    obtain ⟨p, q, hpq, _, hq, _⟩ := (P (k - 1)).codePath.exists_shift_split i n
    cases longest with
    | false =>
      have hopt := (P (k - 1)).codePath.initial_isShortest
        (shiftedStream W 0) (P (k - 1)).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change n ≤ m
      simpa only [hq, hrlen] using hle
    | true =>
      have hopt := (P (k - 1)).codePath.initial_isLongest
        (shiftedStream W 0) (P (k - 1)).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change m ≤ n
      simpa only [hq, hrlen] using hle

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section1

/-- Helper toward Lemma 5.6: candidate existence holds simultaneously for
every boundary index and both modes on the existing full-measure event.
Containment is discharged by `m0Cut_ae_realizedLeftSideSlice_eq`. -/
theorem m0GeodesicSide_ae_adjacentCandidate :
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
      ∀ k : ℤ,
      ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
        geometricSideAdjacentGeodesicCandidate
          (m0GeodesicSide hp (P k) .left) longest v d := by
  filter_upwards [m0Cut_ae_realizedLeftSideSlice_eq] with W hW
  obtain ⟨H, h, hLL, hp, hmode⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, hc, hcontain, hslice⟩ := hmode longest
  exact ⟨P, fun k => m0GeodesicSide_adjacentCandidate hp P k
    (hcontain (k - 1) k (by omega))⟩

/-- Helper toward Lemma 5.6: a finite clockwise scan in the stored rotation
relation. The rotation itself is counterclockwise, hence the reversed
arguments. No finiteness or successor law is postulated for abstract sides. -/
@[expose] def geometricSideClockwiseScan (M : GeometricSideSubmap)
    (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ) : Prop :=
  f 0 = a ∧ ∀ j, j < n → geometricSideRelation M .rotation (f (j + 1)) (f j)

/-- Helper toward Lemma 5.6: marked isomorphisms transport finite clockwise
scans using only preservation of the rotation relation. -/
theorem geometricSideClockwiseScan_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {a : GeometricSideCell M}
    {f : ℕ → GeometricSideCell M} {n : ℕ}
    (hscan : geometricSideClockwiseScan M a f n) :
    geometricSideClockwiseScan N (I.equiv a) (I.equiv ∘ f) n := by
  exact ⟨congrArg I.equiv hscan.1,
    fun j hj => (I.relation_iff _ _ _).1 (hscan.2 j hj)⟩

/-- Helper toward Lemma 5.6: the incoming corner at step zero is the
indexed exterior-boundary dart 1; subsequently it is the opposite of the
previous directed dart. This uses no drawing or additional selected mark. -/
@[expose] def geometricSideRayIncomingCorner (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (i : ℕ) (a : GeometricSideCell M) : Prop :=
  match i with
  | 0 => geometricSideRelation M (.boundary 1) a a
  | j + 1 => geometricSideRelation M .opposite (d j) a

/-- Helper toward Lemma 5.6: incoming corners transport through the marked
boundary and opposite relations. -/
theorem geometricSideRayIncomingCorner_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d : ℕ → GeometricSideCell M)
    (i : ℕ) (a : GeometricSideCell M) :
    geometricSideRayIncomingCorner M d i a ↔
      geometricSideRayIncomingCorner N (I.equiv ∘ d) i (I.equiv a) := by
  cases i with
  | zero => exact I.relation_iff _ _ _
  | succ j => exact I.relation_iff _ _ _

/-- Helper toward Lemma 5.6: an intrinsic order-theoretic leftmost predicate.
At each step, scan clockwise from the incoming corner and take the first
dart admitting an adjacent metric candidate with the same dart prefix.
All comparisons use stored relations. This definition asserts neither
existence on arbitrary sides nor agreement with ambient planar leftmostness;
the latter is the separate bridge obligation below. -/
@[expose] def IntrinsicallyLeftmostAdjacentRay (M : GeometricSideSubmap)
    (longest : Bool) (v d : ℕ → GeometricSideCell M) : Prop :=
  geometricSideAdjacentGeodesicCandidate M longest v d ∧
    ∀ i, ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRayIncomingCorner M d i a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d i ∧
      ∀ (v' d' : ℕ → GeometricSideCell M),
        geometricSideAdjacentGeodesicCandidate M longest v' d' →
        (∀ j, j < i → d' j = d j) →
        ∀ j, j < n → f j ≠ d' i

/-- Helper toward Lemma 5.6: the intrinsic first-admissible-dart predicate
transports through marked isomorphisms, including its competing rays. -/
theorem intrinsicallyLeftmostAdjacentRay_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M}
    (hl : IntrinsicallyLeftmostAdjacentRay M longest v d) :
    IntrinsicallyLeftmostAdjacentRay N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  refine ⟨geometricSideAdjacentGeodesicCandidate_map I longest hl.1, ?_⟩
  intro i
  obtain ⟨a, f, n, ha, hf, hd, hfirst⟩ := hl.2 i
  refine ⟨I.equiv a, I.equiv ∘ f, n,
    (geometricSideRayIncomingCorner_iff I d i a).1 ha,
    geometricSideClockwiseScan_map I hf, congrArg I.equiv hd, ?_⟩
  intro v' d' hc hpref j hj heq
  have hc' := geometricSideAdjacentGeodesicCandidate_map
    (GeometricSideMarkedIso.symm I) longest hc
  have hpref' : ∀ t, t < i → (I.equiv.symm ∘ d') t = d t := by
    intro t ht
    change I.equiv.symm (d' t) = d t
    rw [hpref t ht]
    exact I.equiv.symm_apply_apply (d t)
  apply hfirst (I.equiv.symm ∘ v') (I.equiv.symm ∘ d') hc' hpref' j hj
  change f j = I.equiv.symm (d' i)
  exact (I.equiv.symm_apply_apply (f j)).symm.trans (congrArg I.equiv.symm heq)

/-- Helper toward Lemma 5.6: intrinsic leftmostness is invariant under
marked isomorphism in both directions. -/
theorem intrinsicallyLeftmostAdjacentRay_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    (v d : ℕ → GeometricSideCell M) :
    IntrinsicallyLeftmostAdjacentRay M longest v d ↔
      IntrinsicallyLeftmostAdjacentRay N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  constructor
  · exact intrinsicallyLeftmostAdjacentRay_map I longest
  · intro hl
    have hm := intrinsicallyLeftmostAdjacentRay_map
      (GeometricSideMarkedIso.symm I) longest hl
    have hv : I.equiv.symm ∘ (I.equiv ∘ v) = v := by
      funext i
      exact I.equiv.symm_apply_apply (v i)
    have hd : I.equiv.symm ∘ (I.equiv ∘ d) = d := by
      funext i
      exact I.equiv.symm_apply_apply (d i)
    change IntrinsicallyLeftmostAdjacentRay M longest
      (I.equiv.symm ∘ (I.equiv ∘ v)) (I.equiv.symm ∘ (I.equiv ∘ d)) at hm
    rw [hv, hd] at hm
    exact hm






















































































end DirectedDistances.PaperProofs.Section5
