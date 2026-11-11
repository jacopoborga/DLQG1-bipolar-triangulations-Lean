/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceOneSideReader
public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction4

/-! Counterclockwise adjacent-ray scans and their measurable countable readers.
Identification with the source's leftmost next ray is a separate obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: reverse only the scan relation. This is an
algorithmic input to the existing reader, not a geometric reflected submap;
in particular its face succession is not asserted to be a reflection. -/
@[expose] def geoSliceReverseScanSide (M : GeometricSideSubmap) : GeometricSideSubmap :=
  { M with rotation := fun a b => M.rotation b a }

/-- Helper toward Lemma 5.6: reversing the scan relation twice restores
all ten stored fields. -/
theorem geoSliceReverseScanSide_involutive (M : GeometricSideSubmap) :
    geoSliceReverseScanSide (geoSliceReverseScanSide M) = M := by
  cases M
  rfl

/-- Helper toward Lemma 5.6: transposing the two countable rotation
coordinates is measurable in the complete side code. -/
theorem measurable_geoSliceReverseScanSide : Measurable geoSliceReverseScanSide := by
  apply measurable_comap_iff.mpr
  have hc : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hr : Measurable (fun M : GeometricSideSubmap =>
      fun a b : ℕ × Bool => decide (M.rotation b a)) :=
    measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
      (hc.snd.snd.snd.snd.snd.fst.eval (a := b)).eval (a := a)
  exact hc.fst.prodMk (hc.snd.fst.prodMk (hc.snd.snd.fst.prodMk
    (hc.snd.snd.snd.fst.prodMk (hc.snd.snd.snd.snd.fst.prodMk
    (hr.prodMk (hc.snd.snd.snd.snd.snd.snd.fst.prodMk
    (hc.snd.snd.snd.snd.snd.snd.snd.fst.prodMk
    (hc.snd.snd.snd.snd.snd.snd.snd.snd.fst.prodMk
      hc.snd.snd.snd.snd.snd.snd.snd.snd.snd))))))))

/-- Helper toward Lemma 5.6: a finite counterclockwise scan uses the
stored rotation in its forward order. -/
@[expose] def geometricSideCounterclockwiseScan (M : GeometricSideSubmap)
    (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ) : Prop :=
  f 0 = a ∧ ∀ j, j < n → geometricSideRelation M .rotation (f j) (f (j + 1))

/-- Helper toward Lemma 5.6: reversing the algorithmic scan relation
changes clockwise scanning into counterclockwise scanning. -/
theorem geometricSideCounterclockwiseScan_iff (M : GeometricSideSubmap)
    (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ) :
    geometricSideCounterclockwiseScan M a f n ↔
      geometricSideClockwiseScan (geoSliceReverseScanSide M) a f n := by
  have hr (u v : GeometricSideCell M) :
      geometricSideRelation (geoSliceReverseScanSide M) .rotation u v ↔
        geometricSideRelation M .rotation v u := by
    cases u <;> cases v <;> rfl
  simp only [geometricSideCounterclockwiseScan, geometricSideClockwiseScan, hr]
  rfl

/-- Helper toward Lemma 5.6: the mirror intrinsic selector, defined by
counterclockwise first-admissible scanning. Its candidates still retain
individual edge IDs, directed presence and attained segment optimality. -/
@[expose] def intrinsicallyRightmostAdjacentRay (M : GeometricSideSubmap)
    (longest : Bool) (v d : ℕ → GeometricSideCell M) : Prop :=
  IntrinsicallyLeftmostAdjacentRay (geoSliceReverseScanSide M) longest v d

/-- Helper toward Lemma 5.6: counterclockwise first-admissible scanning
is unique whenever the stored forward rotation is functional. -/
theorem intrinsicallyRightmostAdjacentRay_unique_of_rotation
    (M : GeometricSideSubmap) (longest : Bool)
    (hrot : ∀ a b c : GeometricSideCell M,
      geometricSideRelation M .rotation a b →
      geometricSideRelation M .rotation a c → b = c)
    {v d v' d' : ℕ → GeometricSideCell M}
    (hl : intrinsicallyRightmostAdjacentRay M longest v d)
    (hl' : intrinsicallyRightmostAdjacentRay M longest v' d') :
    v = v' ∧ d = d' := by
  apply intrinsicallyLeftmostAdjacentRay_unique_of_rotation
    (geoSliceReverseScanSide M) longest ?_ hl hl'
  intro a b c hb hc
  apply hrot a b c
  · cases a <;> cases b <;> exact hb
  · cases a <;> cases c <;> exact hc

/-- Helper toward Lemma 5.6: the countable rightmost ray-code reader
uses the same finite-prefix/seam-tail encoding with counterclockwise scans. -/
@[expose] noncomputable def geoSliceRightSideRayCodeOption (longest : Bool)
    (M : GeometricSideSubmap) : Option GeoSliceSeamRayCode :=
  geoSliceOneSideRayCodeOption longest (geoSliceReverseScanSide M)

local instance : MeasurableSpace GeoSliceSeamRayCode := ⊤
local instance : MeasurableSpace (Option GeoSliceSeamRayCode) := ⊤
local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: the counterclockwise code reader is measurable. -/
theorem measurable_geoSliceRightSideRayCodeOption (longest : Bool) :
    Measurable (geoSliceRightSideRayCodeOption longest) :=
  (measurable_geoSliceOneSideRayCodeOption longest).comp
    measurable_geoSliceReverseScanSide

/-- Helper toward Lemma 5.6: the complete graph of the rightmost code
reader chooses the least encoding satisfying the counterclockwise test. -/
theorem geoSliceRightSideRayCodeOption_eq_some_iff (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) :
    geoSliceRightSideRayCodeOption longest M = some p ↔
      geoSliceSeamRayFirst longest (geoSliceReverseScanSide M) p ∧
      ∀ q, geoSliceSeamRayFirst longest (geoSliceReverseScanSide M) q →
        Encodable.encode p ≤ Encodable.encode q :=
  geoSliceOneSideRayCodeOption_eq_some_iff longest (geoSliceReverseScanSide M) p

/-- Helper toward Lemma 5.6: rightmost selection fails exactly when
there is no first-admissible countably coded counterclockwise ray. -/
theorem geoSliceRightSideRayCodeOption_eq_none_iff (longest : Bool)
    (M : GeometricSideSubmap) :
    geoSliceRightSideRayCodeOption longest M = none ↔
      ¬∃ p, geoSliceSeamRayFirst longest (geoSliceReverseScanSide M) p :=
  geoSliceOneSideRayCodeOption_eq_none_iff longest (geoSliceReverseScanSide M)

/-- Helper toward Lemma 5.6: individual edges selected by the mirror
reader, with no invented edge when selection fails. -/
@[expose] noncomputable def geoSliceRightSideRayEdgeOption (longest : Bool)
    (i : ℕ) (M : GeometricSideSubmap) : Option ℕ :=
  geoSliceOneSideRayEdgeOption longest i (geoSliceReverseScanSide M)

/-- Helper toward Lemma 5.6: each edge returned by the mirror reader
is measurable in the original complete side code. -/
theorem measurable_geoSliceRightSideRayEdgeOption (longest : Bool) (i : ℕ) :
    Measurable (geoSliceRightSideRayEdgeOption longest i) :=
  (measurable_geoSliceOneSideRayEdgeOption longest i).comp
    measurable_geoSliceReverseScanSide

/-- Helper toward Lemma 5.6: right-side joint least offsets in source
order (old seam, selected next ray), reversing the existing reader's order. -/
@[expose] noncomputable def geoSliceRightSideOffsetsOption (longest : Bool)
    (M : GeometricSideSubmap) : Option (ℕ × ℕ) :=
  (geoSliceOneSideOffsetsOption longest (geoSliceReverseScanSide M)).map Prod.swap

/-- Helper toward Lemma 5.6: both mirror offsets are jointly measurable. -/
theorem measurable_geoSliceRightSideOffsetsOption (longest : Bool) :
    Measurable (geoSliceRightSideOffsetsOption longest) :=
  (measurable_of_countable (fun p : Option (ℕ × ℕ) => p.map Prod.swap)).comp
    ((measurable_geoSliceOneSideOffsetsOption longest).comp
      measurable_geoSliceReverseScanSide)

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: forward rotation on a realized side is
functional, as first return of the forward ambient rotation. -/
theorem m0GeodesicSide_counterclockwiseStep_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (a b c : GeometricSideCell (m0GeodesicSide hp P s))
    (hb : geometricSideRelation (m0GeodesicSide hp P s) .rotation a b)
    (hc : geometricSideRelation (m0GeodesicSide hp P s) .rotation a c) : b = c := by
  cases a with
  | inl a => cases b <;> exact False.elim hb
  | inr a =>
    cases b with
    | inl b => exact False.elim hb
    | inr b =>
      cases c with
      | inl c => exact False.elim hc
      | inr c =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact firstReturn_endpoint_unique
          (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)
          {d | d.1 ∈ (m0GeodesicSide hp P s).edges} b.property c.property hb hc

/-- Helper toward Lemma 5.6: two counterclockwise intrinsic selectors
on the same realized right side agree in vertices and individual darts. -/
theorem m0GeodesicRightSide_intrinsicallyRightmostAdjacentRay_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {v d v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp P .right)}
    (hl : intrinsicallyRightmostAdjacentRay (m0GeodesicSide hp P .right) longest v d)
    (hl' : intrinsicallyRightmostAdjacentRay (m0GeodesicSide hp P .right) longest v' d') :
    v = v' ∧ d = d' :=
  intrinsicallyRightmostAdjacentRay_unique_of_rotation _ longest
    (m0GeodesicSide_counterclockwiseStep_unique hp P .right) hl hl'

/-- Helper toward Lemma 5.6: the next source ray has a finite-prefix /
old-seam-tail encoding in the right side. The coalescence pair is kept in
source order `(a,b)`, so the new prefix has length `b` and old seam offset `a`. -/
theorem geoSliceRightSeamRayEdge_source_eq
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b) (i : ℕ) :
    geoSliceSeamRayEdge (m0GeodesicSide hp (P (k - 1)) .right)
      (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a) i =
        (P k).codePath.edge i := by
  by_cases hi : i < b
  · simp only [geoSliceSeamRayEdge, List.length_ofFn, hi, dite_eq_left,
      List.getElem_ofFn]
  · simp only [geoSliceSeamRayEdge, List.length_ofFn, hi]
    exact (wholePlaneEdgeι_injective W 0 (hab (i - b))).trans
      (congrArg (fun n => (P k).codePath.edge n)
        (Nat.add_sub_of_le (Nat.le_of_not_gt hi)))

/-- Helper toward Lemma 5.6: a fixed encoding of the next source ray
recovers its joint least coalescence offsets. This is an exact code test,
not an identification of the counterclockwise ray selector. -/
theorem geoSliceRightSeamRayOffsets_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    geoSliceSeamRayOffsets (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a)
      (m0GeodesicSide hp (P (k - 1)) .right) = some (b, a) := by
  apply (geoSliceSidePairOffsets_eq_some_iff _ b a).2
  have htail (i j : ℕ) :
      geoSliceSidePairTailsCoalesce
        ((geoSliceSeamRayMarkedSide
          (List.ofFn (fun t : Fin b => (P k).codePath.edge t), a)
          (m0GeodesicSide hp (P (k - 1)) .right),
          m0GeodesicSide hp (P (k - 1)) .right), id) i j ↔
        M0CutEdgeTailsCoalesce (P (k - 1)) (P k) j i := by
    simp only [geoSliceSidePairTailsCoalesce, geoSliceSeamRayMarkedSide,
      geoSliceRightSeamRayEdge_source_eq hp P k a b hab.1]
    constructor
    · intro hco n
      exact congrArg (wholePlaneEdgeι W 0) (hco n).symm
    · intro hco n
      exact (wholePlaneEdgeι_injective W 0 (hco n)).symm
  refine ⟨(htail b a).2 hab.1, ?_⟩
  intro i j hij
  obtain ⟨ha, hb⟩ := hab.2 j i ((htail i j).1 hij)
  exact ⟨hb, ha⟩

/-- Helper toward Lemma 5.6: all indexed right exterior-boundary edges
are geometric edges of the right side, whether or not they are directed-present. -/
theorem m0GeodesicRightSide_boundary_mem_edges
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    ((m0GeodesicSide hp P .right).boundary i).1 ∈
      (m0GeodesicSide hp P .right).edges := by
  change ∀ z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
    (wholePlaneDartι W 0
      (boundaryOuterEdge (shiftedStream W 0) h (k + (i : ℤ)), false))).image,
    z ∈ m0GeodesicSideRegion hp P .right
  intro z hz
  have ha := m0Geodesic_arc_subset_ambient hp
    (boundaryOuterEdge (shiftedStream W 0) h (k + (i : ℤ))) hz
  have hg := hz
  rw [m0CutBoundaryEdgeTrace_eq_graphOver hp] at hg
  refine ⟨ha, ?_⟩
  intro hleft
  obtain ⟨_, hwest | ⟨y, hy, hyre, hyim⟩⟩ :=
    (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp P z).1 hleft
  · have hroot := (seamX_strictMono (shiftedStream W 0) h (H.1 0)).monotone
      (show k ≤ k + (i : ℤ) by omega)
    exact (not_lt_of_ge (hroot.trans hg.1)) hwest
  · have hyabove := m0GeodesicTrace_subset_ambient hp P hy
    change seamFun (shiftedStream W 0) h (H.1 0) y.re ≤ y.im at hyabove
    rw [hyre, ← hg.2.2] at hyabove
    exact (not_lt_of_ge hyabove) hyim

/-- Helper toward Lemma 5.6: right exterior-boundary dart 1 starts at
the next cut vertex, preserving the unreversed right-boundary convention. -/
theorem m0GeodesicRightSide_adjacent_start
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    geometricSideDartInitial (m0GeodesicSide hp P .right)
      ((m0GeodesicSide hp P .right).boundary 1) =
        boundaryVertex (shiftedStream W 0) h (k + 1) := by
  exact boundaryOuterEdge_endpoints (shiftedStream W 0) h (k + 1) |>.1

/-- Helper toward Lemma 5.6: the next ray's whole edge and vertex streams
lie in the previous right side. The needed nesting is derived from ambient
leftmostness and the source's coalescence family. -/
theorem m0GeodesicRightSide_nextRay_contained
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (n : ℕ) :
    (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
    ((P k).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P (k - 1)) .right).vertices := by
  have hnest := m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
    P T hleft hc (k - 1) k (by omega)
  constructor
  · exact ((m0GeodesicEdges_subset_both hp (P k) ⟨n, rfl⟩).2).trans hnest
  · have ht := m0Geodesic_initial_pos_mem_trace hp (P k) n
    rw [← m0GeodesicSideRegion_inter hp (P k)] at ht
    exact hnest ht.2

/-- Helper toward Lemma 5.6: the explicit source encoding of the next
ray passes the intrinsic metric-candidate test in the preceding right side.
No extremal scan-order premise or identification premise is used. -/
theorem geoSliceRightSeamRayCandidate_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b) :
    geoSliceSeamRayCandidate longest (m0GeodesicSide hp (P (k - 1)) .right)
      (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a) := by
  simp only [geoSliceSeamRayCandidate, geoSliceRightSeamRayEdge_source_eq hp P k a b hab]
  let w := shiftedStream W 0
  have hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  have hout (i : ℕ) := (P k).codePath.edge_outgoing_at_initial w i
  refine ⟨?_, ⟨m0GeodesicRightSide_boundary_mem_edges hp (P (k - 1)) 1, ?_⟩, ?_⟩
  · intro i
    refine ⟨(hcontain i).1, (hout i).1, ?_, ?_⟩
    · change edgeWest w ((P k).codePath.edge i) ∈ _
      rw [(hout i).2]
      exact (hcontain i).2
    · change edgeEast w ((P k).codePath.edge i) =
        edgeWest w ((P k).codePath.edge (i + 1))
      exact ((P k).codePath.edge_incoming_at_succ w i).2.trans (hout (i + 1)).2.symm
  · have hs := m0GeodesicRightSide_adjacent_start hp (P (k - 1))
    rw [show k - 1 + 1 = k by omega] at hs
    exact hs.trans ((m0Geodesic_initial_zero (P k)).symm.trans (hout 0).2.symm)
  · intro i n m hm
    change geoSliceRawWalk _ m (edgeWest w ((P k).codePath.edge i))
      (edgeWest w ((P k).codePath.edge (i + n))) at hm
    rw [(hout i).2, (hout (i + n)).2] at hm
    obtain ⟨r, hrlen⟩ := m0GeodesicSide_walk_lifts hp (P (k - 1)) .right m
      ⟨_, (hcontain i).2⟩ ⟨_, (hcontain (i + n)).2⟩
      ((geoSliceRawWalk_iff _ m _ _).1 hm)
    obtain ⟨p, q, hpq, _, hq, _⟩ := (P k).codePath.exists_shift_split i n
    cases longest with
    | false =>
      change n ≤ m
      have hopt := (P k).codePath.initial_isShortest w (P k).segments (i + n)
      rw [hpq] at hopt
      simpa only [hq, hrlen] using hopt.of_comp_right r
    | true =>
      change m ≤ n
      have hopt := (P k).codePath.initial_isLongest w (P k).segments (i + n)
      rw [hpq] at hopt
      simpa only [hq, hrlen] using hopt.of_comp_right r

/-- Helper toward Lemma 5.6: counterclockwise turns from an incoming
west-pointing dart order outgoing arguments increasingly. This is the mirror
angle formula; the clockwise version orders them decreasingly. -/
theorem ccwTurn_west_east_lt_iff_arg_lt (a b c : ℂ)
    (ha : a.re < 0) (hb : 0 < b.re) (hc : 0 < c.re) :
    ccwTurn a b < ccwTurn a c ↔ Complex.arg b < Complex.arg c := by
  rw [west_east_turn_formula ha hb, west_east_turn_formula ha hc]
  constructor <;> intro h <;> linarith only [h]

/-- Helper toward Lemma 5.6: source leftmostness maximizes, rather than
minimizes, counterclockwise turn from an incoming reversed dart. This retains
the proved source inequality and does not identify the mirror selector. -/
theorem m0CutLeftmostXdp_raw_counterclockwiseTurn_le
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T)
    (e i j : ℕ) (hv : (P.codePath.initial i).1 = (Q.codePath.initial j).1) :
    ccwTurn
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (e, true)).initialDirection
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc
          (Q.codePath.edge j, false)).initialDirection ≤
    ccwTurn
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (e, true)).initialDirection
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc
          (P.codePath.edge i, false)).initialDirection := by
  have he := m0RawDrawing_incoming_initialDirection_re_neg H e
  have hP : 0 < ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc
        (P.codePath.edge i, false)).initialDirection.re :=
    outgoing_initialDirection_re_pos _ _ _ _
      (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).1
  have hQ : 0 < ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc
        (Q.codePath.edge j, false)).initialDirection.re :=
    outgoing_initialDirection_re_pos _ _ _ _
      (Q.codePath.edge_outgoing_at_initial (shiftedStream W 0) j).1
  rw [west_east_turn_formula he hQ, west_east_turn_formula he hP]
  have harg := m0CutLeftmostXdp_raw_departureArg_le hp P Q T hleft i j hv
  linarith only [harg]

/-- Helper toward Lemma 5.6: the past iteration skeleton applies a named
one-slice reader to successive outputs of a named side-update algorithm.
No geometric interpretation of the update algorithm is assumed here. -/
@[expose] def geoSlicePastReader
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (previousSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) :
    ∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass :=
  fun k => oneSlice (previousSide^[(j - k.val).toNat] M)

/-- Helper toward Lemma 5.6: the future iteration skeleton begins with
slice `j+1`, so its side-update depth is zero at that first future index. -/
@[expose] def geoSliceFutureReader
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (nextSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) :
    ∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass :=
  fun k => oneSlice (nextSide^[(k.val - (j + 1)).toNat] M)

/-- Helper toward Lemma 5.6: the past skeleton's current-cut entry
is the given one-slice reader without any side updates. -/
theorem geoSlicePastReader_at_cut
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (previousSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) :
    geoSlicePastReader oneSlice previousSide j M ⟨j, le_rfl⟩ = oneSlice M := by
  simp only [geoSlicePastReader, sub_self, Int.toNat_zero, Function.iterate_zero,
    id_eq]

/-- Helper toward Lemma 5.6: the future skeleton starts with the supplied
one-slice reader at cut `j`, which is to return slice `j+1`. -/
theorem geoSliceFutureReader_at_first
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (nextSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) :
    geoSliceFutureReader oneSlice nextSide j M ⟨j + 1, le_rfl⟩ = oneSlice M := by
  simp only [geoSliceFutureReader, sub_self, Int.toNat_zero, Function.iterate_zero,
    id_eq]

/-- Helper toward Lemma 5.6: past-family a.s. identity is equivalent to
its countably many coordinate identities. This is an identity reduction,
not a premise asserting source reconstruction or a theorem about `G`. -/
theorem geoSlicePastReader_ae_eq_iff
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (previousSide : GeometricSideSubmap → GeometricSideSubmap)
    (side : (ℤ → Fin 3) → GeometricSideSubmap) (j : ℤ) :
    ((fun W (k : {k : ℤ // k ≤ j}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlicePastReader oneSlice previousSide j (side W)) ↔
    ∀ k : {k : ℤ // k ≤ j}, G k.val =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => oneSlice (previousSide^[(j - k.val).toNat] (side W)) := by
  change (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    (fun k : {k : ℤ // k ≤ j} => G k.val W) =
      geoSlicePastReader oneSlice previousSide j (side W)) ↔ _
  simp only [funext_iff, geoSlicePastReader]
  exact ae_all_iff

/-- Helper toward Lemma 5.6: future-family a.s. identity is equivalent to
all future coordinate identities, with the source's strict cut convention. -/
theorem geoSliceFutureReader_ae_eq_iff
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (nextSide : GeometricSideSubmap → GeometricSideSubmap)
    (side : (ℤ → Fin 3) → GeometricSideSubmap) (j : ℤ) :
    ((fun W (k : {k : ℤ // j + 1 ≤ k}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSliceFutureReader oneSlice nextSide j (side W)) ↔
    ∀ k : {k : ℤ // j + 1 ≤ k}, G k.val =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => oneSlice (nextSide^[(k.val - (j + 1)).toNat] (side W)) := by
  change (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    (fun k : {k : ℤ // j + 1 ≤ k} => G k.val W) =
      geoSliceFutureReader oneSlice nextSide j (side W)) ↔ _
  simp only [funext_iff, geoSliceFutureReader]
  exact ae_all_iff

/-- Helper toward Lemma 5.6: on one event for both metric modes and every
integer cut, the next source ray has an intrinsic right-side metric-candidate
code, exact individual-edge decoding, and the correct joint least offsets.
This does not identify the counterclockwise selector with that code. -/
theorem m0Cut_ae_rightSide_nextRay_candidate_and_offsets :
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
        geoSliceSeamRayCandidate longest (m0GeodesicSide hp (P (k - 1)) .right)
          (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a) ∧
        geoSliceSeamRayOffsets (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a)
          (m0GeodesicSide hp (P (k - 1)) .right) = some (b, a) ∧
        ∀ i : ℕ, geoSliceSeamRayEdge (m0GeodesicSide hp (P (k - 1)) .right)
          (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a) i =
            (P k).codePath.edge i := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hmodes⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, _, hc, _⟩ := hmodes longest
  have hc' (m : ℤ) : ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b := by
    have hm := hc (m + 1)
    rw [show m + 1 - 1 = m by omega] at hm
    exact hm
  refine ⟨P, T, hleft, fun k => ?_⟩
  obtain ⟨a, b, hab⟩ := hc k
  exact ⟨a, b, hab, geoSliceRightSeamRayCandidate_source hp P T hleft hc' k a b hab.1,
    geoSliceRightSeamRayOffsets_source hp P k a b hab,
    geoSliceRightSeamRayEdge_source_eq hp P k a b hab.1⟩

/-- Helper toward Lemma 5.6: two countable counterclockwise first-admissible
codes on an actual right side have the same individual edge stream. -/
theorem geoSliceRightSeamRayFirst_edges_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {p q : GeoSliceSeamRayCode}
    (hpfirst : geoSliceSeamRayFirst longest
      (geoSliceReverseScanSide (m0GeodesicSide hp P .right)) p)
    (hqfirst : geoSliceSeamRayFirst longest
      (geoSliceReverseScanSide (m0GeodesicSide hp P .right)) q) :
    ∀ i, geoSliceSeamRayEdge (m0GeodesicSide hp P .right) p i =
      geoSliceSeamRayEdge (m0GeodesicSide hp P .right) q i := by
  have hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ (m0GeodesicSide hp P .right).edges →
      b.1 ∈ (m0GeodesicSide hp P .right).edges →
      c.1 ∈ (m0GeodesicSide hp P .right).edges →
      (m0GeodesicSide hp P .right).rotation a b →
      (m0GeodesicSide hp P .right).rotation a c → b = c := by
    intro a b c ha hb hc hab hac
    have he := m0GeodesicSide_counterclockwiseStep_unique hp P .right
      (.inr ⟨a, ha⟩) (.inr ⟨b, hb⟩) (.inr ⟨c, hc⟩) hab hac
    exact congrArg Subtype.val (Sum.inr.inj he)
  exact geoSliceSeamRayFirst_edges_unique longest
    (geoSliceReverseScanSide (m0GeodesicSide hp P .right)) hrot hpfirst hqfirst

/-- Helper toward Lemma 5.6: transposing scan relations transports every
complete marked-side isomorphism, without changing its cell equivalence. -/
@[expose] def geometricSideMarkedIsoReverseScanSide {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) :
    GeometricSideMarkedIso (geoSliceReverseScanSide M) (geoSliceReverseScanSide N) where
  equiv := I.equiv
  relation_iff t u v := by
    by_cases ht : t = .rotation
    · subst t
      have h (A : GeometricSideSubmap) (a b : GeometricSideCell A) :
          geometricSideRelation (geoSliceReverseScanSide A) .rotation a b ↔
            geometricSideRelation A .rotation b a := by
        cases a <;> cases b <;> rfl
      exact (h M u v).trans ((I.relation_iff .rotation v u).trans
        (h N (I.equiv u) (I.equiv v)).symm)
    · have h (A : GeometricSideSubmap) (a b : GeometricSideCell A) :
          geometricSideRelation (geoSliceReverseScanSide A) t a b ↔
            geometricSideRelation A t a b := by
        cases t <;> cases a <;> cases b <;> try rfl
        exact (ht rfl).elim
      exact (h M u v).trans ((I.relation_iff t u v).trans
        (h N (I.equiv u) (I.equiv v)).symm)

/-- Helper toward Lemma 5.6: counterclockwise first-admissible rays
transport through complete marked-side isomorphisms, including competitors. -/
theorem intrinsicallyRightmostAdjacentRay_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M}
    (hl : intrinsicallyRightmostAdjacentRay M longest v d) :
    intrinsicallyRightmostAdjacentRay N longest (I.equiv ∘ v) (I.equiv ∘ d) :=
  intrinsicallyLeftmostAdjacentRay_map (geometricSideMarkedIsoReverseScanSide I) longest hl

/-- Helper toward Lemma 5.6: mirror-selector uniqueness also holds on
every complete marked representative of a realized right side. -/
theorem m0GeodesicRightSide_intrinsicallyRightmostAdjacentRay_unique_of_markedIso
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide hp P .right) N)
    {v d v' d' : ℕ → GeometricSideCell N}
    (hl : intrinsicallyRightmostAdjacentRay N longest v d)
    (hl' : intrinsicallyRightmostAdjacentRay N longest v' d') :
    v = v' ∧ d = d' := by
  have h := m0GeodesicRightSide_intrinsicallyRightmostAdjacentRay_unique hp P
    (intrinsicallyRightmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl)
    (intrinsicallyRightmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl')
  constructor
  · funext i
    exact I.equiv.symm.injective (congrFun h.1 i)
  · funext i
    exact I.equiv.symm.injective (congrFun h.2 i)

/-- Helper toward Lemma 5.6: scan direction has no effect on the joint
least-offset test once the ray code has been specified. -/
theorem geoSliceSeamRayOffsets_reverseScanSide (p : GeoSliceSeamRayCode)
    (M : GeometricSideSubmap) :
    geoSliceSeamRayOffsets p (geoSliceReverseScanSide M) =
      geoSliceSeamRayOffsets p M := by
  rfl

/-- Helper toward Lemma 5.6: the past skeleton's depth `n` is exactly
the slice index `j-n`, including zero depth. -/
theorem geoSlicePastReader_at_depth
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (previousSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) (n : ℕ) :
    geoSlicePastReader oneSlice previousSide j M ⟨j - n, by omega⟩ =
      oneSlice (previousSide^[n] M) := by
  have hd : (j - (j - (n : ℤ))).toNat = n := by omega
  simp only [geoSlicePastReader, hd]

/-- Helper toward Lemma 5.6: future depth `n` is exactly index `j+1+n`,
so the strict future at cut `j` has the intended indexing. -/
theorem geoSliceFutureReader_at_depth
    (oneSlice : GeometricSideSubmap → Option GeometricSideClass)
    (nextSide : GeometricSideSubmap → GeometricSideSubmap)
    (j : ℤ) (M : GeometricSideSubmap) (n : ℕ) :
    geoSliceFutureReader oneSlice nextSide j M ⟨j + 1 + n, by omega⟩ =
      oneSlice (nextSide^[n] M) := by
  have hd : (j + 1 + (n : ℤ) - (j + 1)).toNat = n := by omega
  simp only [geoSliceFutureReader, hd]
















































































































end DirectedDistances.PaperProofs.Section5

/- successfully for all 39 declarations, including definitions. Their transitive
axiom sets are contained in {propext, Classical.choice, Quot.sound}; no custom
axiom or sorryAx occurred. The probes were removed before the final production
are not claimed. Only this owned source file was edited. -/
