/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SliceMeasurable
public import DirectedDistances.PaperProofs.Section5.GeoSliceIntrinsicSliceReader4

/-! Agreement of the single-side ray and offset readers with intrinsic data. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: on every source slice witness the selected
code decodes to the unique intrinsic adjacent ray, including its vertices
and individual darts. The least offsets belong to that same ray. -/
theorem M0CutGeodesicSliceWitness.oneSideReaders_eq
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    ∃ p : GeoSliceSeamRayCode,
      ∃ hc : geoSliceSeamRayCandidate (if x = XDP.ldp then true else false)
        (m0GeodesicSide s.hp (s.P k) .left) p,
      geoSliceOneSideRayCodeOption (if x = XDP.ldp then true else false)
          (m0GeodesicSide s.hp (s.P k) .left) = some p ∧
      geoSliceSeamRayVertexCells hc =
        m0GeodesicSideAdjacentVertices s.hp s.P k (s.left_adjacent_containment k) ∧
      geoSliceSeamRayDartCells hc =
        m0GeodesicSideAdjacentDarts s.hp s.P k (s.left_adjacent_containment k) ∧
      geoSliceOneSideOffsetsOption (if x = XDP.ldp then true else false)
          (m0GeodesicSide s.hp (s.P k) .left) =
        some (s.thetaMinus k, s.theta k) := by
  obtain ⟨p, hp, hfirst⟩ := geoSliceOneSideRayCodeOption_spec _ _
    ⟨_, geoSliceSeamRayFirst_source s.hp s.P s.T s.hleft k
      (s.thetaMinus k) (s.theta k) (s.least k).1 (s.left_adjacent_containment k)⟩
  refine ⟨p, hfirst.1, hp, ?_, ?_, ?_⟩
  · funext i
    apply congrArg Sum.inl
    apply Subtype.ext
    change (m0GeodesicSide s.hp (s.P k) .left).west
      (geoSliceSeamRayEdge _ p i) = _
    rw [geoSliceSeamRayFirst_source_edges s.hp s.P s.T s.hleft k
      (s.thetaMinus k) (s.theta k) (s.least k).1 (s.left_adjacent_containment k) hfirst i]
    exact ((s.P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2
  · funext i
    apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg (fun e : ℕ => (e, false))
      (geoSliceSeamRayFirst_source_edges s.hp s.P s.T s.hleft k
        (s.thetaMinus k) (s.theta k) (s.least k).1
        (s.left_adjacent_containment k) hfirst i)
  · exact geoSliceOneSideOffsetsOption_source s.hp s.P s.T s.hleft k
      (s.thetaMinus k) (s.theta k) (s.least k) (s.left_adjacent_containment k)

/-- Helper toward Lemma 5.6: conditional evaluation of the intrinsic
slice reader at explicitly successful ray and joint-offset reader outputs. -/
theorem intrinsicSliceOfSide_eq_some_core
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hr : geoSliceOneSideRayCodeOption longest M = some p)
    {a b : ℕ} (hoff : geoSliceOneSideOffsetsOption longest M = some (a, b)) :
    intrinsicSliceOfSide longest M =
      some (geoSliceIntrinsicSliceCore longest M p
        ((geoSliceOneSideRayCodeOption_eq_some_iff longest M p).1 hr).1.1 a b) := by
  unfold intrinsicSliceOfSide
  split
  · rename_i hnone
    rw [hr] at hnone
    cases hnone
  · rename_i q hq
    have hqp : q = p := Option.some.inj (hq.symm.trans hr)
    subst q
    split
    · rename_i hnone
      rw [hoff] at hnone
      cases hnone
    · rename_i ab hab
      have hab' : ab = (a, b) := Option.some.inj (hab.symm.trans hoff)
      subst ab
      rfl

/-- Helper toward Lemma 5.6: every source slice witness lies in the
successful domain of the full intrinsic candidate reader. This does not
identify that candidate's face relation with the source slice. -/
theorem M0CutGeodesicSliceWitness.intrinsicSliceOfSide_isSome
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    (intrinsicSliceOfSide (if x = XDP.ldp then true else false)
      (m0GeodesicSide s.hp (s.P k) .left)).isSome := by
  obtain ⟨p, _, hr, _, _, hoff⟩ := s.oneSideReaders_eq k
  rw [intrinsicSliceOfSide_eq_some_core hr hoff]
  rfl

/-- Helper toward Lemma 5.6: conditional on a retained geometric edge,
both of its darts belong to the intrinsic right candidate. -/
theorem geoSliceIntrinsicEdgeKept_right_dart
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) {a b : ℕ} {d : ℕ × Bool}
    (hd : geoSliceIntrinsicEdgeKept M p longest hc a b d.1) :
    ∃ hm : d.1 ∈ M.edges,
      geometricSide_intrinsic_right M (geoSliceSeamRayVertexCells hc)
        (geoSliceSeamRayDartCells hc) (.inr ⟨d, hm⟩) := by
  obtain ⟨_, hm, hr, _, _⟩ := hd
  refine ⟨hm, ?_⟩
  rcases d with ⟨e, bit⟩
  cases bit with
  | false => exact hr.1
  | true => exact hr.2

/-- Helper toward Lemma 5.6: conditional on both geometric edges being
retained, the intrinsic core keeps every input face-successor between them.
In particular its two intrinsic-right tests impose no further sector test. -/
theorem geoSliceIntrinsicSliceCore_faceNext_iff_of_kept
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) {a b : ℕ} {d e : ℕ × Bool}
    (hd : geoSliceIntrinsicEdgeKept M p longest hc a b d.1)
    (he : geoSliceIntrinsicEdgeKept M p longest hc a b e.1) :
    (geoSliceIntrinsicSliceCore longest M p hc a b).faceNext d e ↔
      M.faceNext d e := by
  constructor
  · rintro ⟨_, _, hface, _, _, _, _⟩
    exact hface
  · intro hface
    obtain ⟨hdm, hdr⟩ := geoSliceIntrinsicEdgeKept_right_dart hc hd
    obtain ⟨hem, her⟩ := geoSliceIntrinsicEdgeKept_right_dart hc he
    exact ⟨hdm, hem, hface, hd, he, hdr, her⟩

/-- Helper toward Lemma 5.6: the complete enclosed relation always excludes
a forward adjacent-ray departure from its face-successor relation. -/
theorem geometricSide_enclosed_relation_not_faceNext_ray
    {M : GeometricSideSubmap} (v d : ℕ → GeometricSideCell M)
    (keep : Set (GeometricSideCell M)) (i : ℕ) (e : GeometricSideCell M) :
    ¬ geometricSide_enclosed_relation M v d keep .faceNext (d i) e := by
  intro h
  exact h.2.2 i rfl

/-- Helper toward Lemma 5.6: conditional local obstruction to identifying
the intrinsic core with the complete enclosed relation by the canonical
cell inclusion. A retained forward-ray face corner survives in the core
and is excluded by the complete enclosed relation. -/
theorem geoSliceIntrinsicSliceCore_forward_face_obstruction
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) {a b : ℕ} (i : ℕ)
    (e : ℕ × Bool)
    (hd : geoSliceIntrinsicEdgeKept M p longest hc a b (geoSliceSeamRayEdge M p i))
    (he : geoSliceIntrinsicEdgeKept M p longest hc a b e.1)
    (hface : M.faceNext (geoSliceSeamRayEdge M p i, false) e)
    (keep : Set (GeometricSideCell M)) :
    (geoSliceIntrinsicSliceCore longest M p hc a b).faceNext
        (geoSliceSeamRayEdge M p i, false) e ∧
      ¬ geometricSide_enclosed_relation M (geoSliceSeamRayVertexCells hc)
        (geoSliceSeamRayDartCells hc) keep .faceNext
        (geoSliceSeamRayDartCells hc i) (.inr ⟨e, he.1⟩) := by
  exact ⟨(geoSliceIntrinsicSliceCore_faceNext_iff_of_kept hc hd he).2 hface,
    geometricSide_enclosed_relation_not_faceNext_ray _ _ keep i _⟩

/-- Helper toward Lemma 5.6: conditional on complete intrinsic slice
realization, no indexed boundary departure has a face successor. This is
an invariant of the marked class, independent of the cell numbering. -/
theorem leftSliceRealizes_not_boundary_faceNext
    {longest : Bool} {M N : GeometricSideSubmap}
    (hN : leftSliceRealizes longest M N) (i : ℕ)
    (c e : GeometricSideCell N)
    (hc : geometricSideRelation N (.boundary i) c c) :
    ¬ geometricSideRelation N .faceNext c e := by
  obtain ⟨v, d, vs, ds, a, b, _, _, _, _, E, hE⟩ := hN
  have hboundary : (E c).val = d i := (hE (.boundary i) c c).1 hc
  intro hface
  have hface' := (hE .faceNext c e).1 hface
  rw [hboundary] at hface'
  exact geometricSide_enclosed_relation_not_faceNext_ray v d _ i _ hface'

/-- Helper toward Lemma 5.6: conditional on a retained forward-ray face
corner, the core's marked class cannot be the optional class returned by
the complete intrinsic slice reader. Arbitrary renumbering cannot remove
the obstruction, since it preserves boundary marks and face successors. -/
theorem geoSliceIntrinsicSliceCore_class_ne_leftOneSlice_of_forward_face
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) {a b : ℕ} (i : ℕ)
    (e : ℕ × Bool)
    (hd : geoSliceIntrinsicEdgeKept M p longest hc a b (geoSliceSeamRayEdge M p i))
    (he : geoSliceIntrinsicEdgeKept M p longest hc a b e.1)
    (hface : M.faceNext (geoSliceSeamRayEdge M p i, false) e) :
    some (geometricSideClass (geoSliceIntrinsicSliceCore longest M p hc a b)) ≠
      leftOneSlice longest M := by
  intro hclass
  obtain ⟨N, hN, hNC⟩ :=
    (leftOneSlice_eq_some_iff longest M _).1 hclass.symm
  obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 hNC.symm
  let c : GeometricSideCell (geoSliceIntrinsicSliceCore longest M p hc a b) :=
    .inr ⟨(geoSliceSeamRayEdge M p i, false), hd⟩
  let f : GeometricSideCell (geoSliceIntrinsicSliceCore longest M p hc a b) :=
    .inr ⟨e, he⟩
  have hboundary : geometricSideRelation
      (geoSliceIntrinsicSliceCore longest M p hc a b) (.boundary i) c c := rfl
  have hcore : geometricSideRelation
      (geoSliceIntrinsicSliceCore longest M p hc a b) .faceNext c f :=
    (geoSliceIntrinsicSliceCore_faceNext_iff_of_kept hc hd he).2 hface
  exact leftSliceRealizes_not_boundary_faceNext hN i (I.equiv c) (I.equiv f)
    ((I.relation_iff (.boundary i) c c).1 hboundary)
    ((I.relation_iff .faceNext c f).1 hcore)

/-- Helper toward Lemma 5.6: a weak edge tail is exactly the range of
the edge sequence shifted by its offset, including offset zero. -/
theorem geoSlice_edge_tail_iff (q : ℕ → ℕ) (a e : ℕ) :
    (∃ i, a ≤ i ∧ e = q i) ↔ e ∈ Set.range (fun n => q (a + n)) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i - a, congrArg q (Nat.add_sub_of_le hi)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨a + n, Nat.le_add_right a n, rfl⟩

/-- Helper toward Lemma 5.6: the intrinsic reader on every source witness
returns a numbered candidate with exactly the source slice's vertex and
geometric-edge carriers. This asserts neither face nor rotation agreement. -/
theorem M0CutGeodesicSliceWitness.intrinsicSliceOfSide_carriers
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    ∃ N : GeometricSideSubmap,
      intrinsicSliceOfSide (if x = XDP.ldp then true else false)
          (m0GeodesicSide s.hp (s.P k) .left) = some N ∧
      N.vertices = (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k)).vertices ∧
      N.edges = (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k)).edges := by
  obtain ⟨p, hc, hr, hv, hd, hoff⟩ := s.oneSideReaders_eq k
  let M := m0GeodesicSide s.hp (s.P k) .left
  have hedge (i : ℕ) :
      geoSliceSeamRayEdge M p i = (s.P (k - 1)).codePath.edge i :=
    congrArg (fun c => (geoSliceCellDartValue c).1) (congrFun hd i)
  have hwest (i : ℕ) : M.west (geoSliceSeamRayEdge M p i) =
      ((s.P (k - 1)).codePath.initial i).1.id := by
    rw [hedge]
    exact ((s.P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2
  have hseam (i : ℕ) : geometricSideDartInitial M (M.seam i) =
      ((s.P k).codePath.initial i).1.id :=
    ((s.P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2
  have hseamEdge (i : ℕ) : (M.seam i).1 = (s.P k).codePath.edge i := rfl
  have hrightV (v : ℕ) (hm : v ∈ M.vertices) :
      geoSliceIntrinsicRightVertex M p _ hc v hm ↔
        v ∈ m0GeodesicSideVertices s.hp (s.P (k - 1)) .right := by
    unfold geoSliceIntrinsicRightVertex
    rw [hv, hd]
    exact s.left_intrinsic_right_iff_previousRight k (.inl ⟨v, hm⟩)
  have hrightE (e : ℕ) (hm : e ∈ M.edges) :
      geoSliceIntrinsicRightEdge M p _ hc e hm ↔
        e ∈ m0GeodesicSideEdges s.hp (s.P (k - 1)) .right := by
    unfold geoSliceIntrinsicRightEdge
    rw [hv, hd]
    have hf := s.left_intrinsic_right_iff_previousRight k (.inr ⟨(e, false), hm⟩)
    have ht := s.left_intrinsic_right_iff_previousRight k (.inr ⟨(e, true), hm⟩)
    exact ⟨fun h => hf.1 h.1, fun h => ⟨hf.2 h, ht.2 h⟩⟩
  refine ⟨geoSliceIntrinsicSliceCore _ M p hc (s.thetaMinus k) (s.theta k),
    intrinsicSliceOfSide_eq_some_core hr hoff, ?_, ?_⟩
  · ext v
    change geoSliceIntrinsicVertexKept M p _ hc (s.thetaMinus k) (s.theta k) v ↔ _
    rw [m0CutGeodesicSlice_mem_vertices_iff]
    simp only [geoSliceIntrinsicVertexKept, hrightV, hwest, hseam,
      Set.mem_union, Set.mem_ofPred_eq, not_or]
    constructor
    · rintro ⟨hL, _, hR, ha, hb⟩
      exact ⟨⟨hR, hL⟩, ha, hb⟩
    · rintro ⟨⟨hR, hL⟩, ha, hb⟩
      exact ⟨hL, hL, hR, ha, hb⟩
  · ext e
    change geoSliceIntrinsicEdgeKept M p _ hc (s.thetaMinus k) (s.theta k) e ↔ _
    rw [m0CutGeodesicSlice_mem_edges_iff]
    simp only [geoSliceIntrinsicEdgeKept, hrightE, hedge, hseamEdge,
      geoSlice_edge_tail_iff, Set.mem_union, not_or]
    constructor
    · rintro ⟨hL, _, hR, ha, hb⟩
      exact ⟨⟨hR, hL⟩, ha, hb⟩
    · rintro ⟨⟨hR, hL⟩, ha, hb⟩
      exact ⟨hL, hL, hR, ha, hb⟩
















































/- Temporary #print axioms probes of all eleven declarations compiled with
exit 0. Every transitive axiom set is contained in
{propext, Classical.choice, Quot.sound}; no sorryAx or custom axiom occurred.
The probes were removed before the final production compile. -/

end DirectedDistances.PaperProofs.Section5
