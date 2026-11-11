/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReaders2

/-! The right-side selector starts from the reversal of boundary dart zero.
Positive steps retain the incoming-corner convention of the existing selector.
No numbered paper result is claimed. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4 Quiver
open scoped Classical

/-- Helper toward Lemma 5.6: the initial right-side corner reverses its
own boundary-zero mark; positive corners reverse the preceding ray dart. -/
@[expose] def geometricSideRightRayIncomingCorner (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (i : ℕ) (a : GeometricSideCell M) : Prop :=
  match i with
  | 0 => ∃ b, geometricSideRelation M (.boundary 0) b b ∧
      geometricSideRelation M .opposite b a
  | j + 1 => geometricSideRelation M .opposite (d j) a

/-- Helper toward Lemma 5.6: right-side incoming corners transport using
only the side's marked boundary and opposite relations. -/
theorem geometricSideRightRayIncomingCorner_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {d : ℕ → GeometricSideCell M}
    {i : ℕ} {a : GeometricSideCell M}
    (ha : geometricSideRightRayIncomingCorner M d i a) :
    geometricSideRightRayIncomingCorner N (I.equiv ∘ d) i (I.equiv a) := by
  cases i with
  | zero =>
    obtain ⟨b, hb, hba⟩ := ha
    exact ⟨I.equiv b, (I.relation_iff _ _ _).1 hb, (I.relation_iff _ _ _).1 hba⟩
  | succ j => exact (I.relation_iff _ _ _).1 ha

/-- Helper toward Lemma 5.6: the right-side intrinsic clockwise selector
uses the reversed boundary-zero corner at its first departure. -/
@[expose] def intrinsicallyLeftmostAdjacentRightRay (M : GeometricSideSubmap)
    (longest : Bool) (v d : ℕ → GeometricSideCell M) : Prop :=
  geometricSideAdjacentGeodesicCandidate M longest v d ∧
    ∀ i, ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRightRayIncomingCorner M d i a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d i ∧
      ∀ (v' d' : ℕ → GeometricSideCell M),
        geometricSideAdjacentGeodesicCandidate M longest v' d' →
        (∀ j, j < i → d' j = d j) →
        ∀ j, j < n → f j ≠ d' i

/-- Helper toward Lemma 5.6: the corrected right-side selector transports
through every complete marked side isomorphism, including competitors. -/
theorem intrinsicallyLeftmostAdjacentRightRay_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M}
    (hl : intrinsicallyLeftmostAdjacentRightRay M longest v d) :
    intrinsicallyLeftmostAdjacentRightRay N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  refine ⟨geometricSideAdjacentGeodesicCandidate_map I longest hl.1, ?_⟩
  intro i
  obtain ⟨a, f, n, ha, hf, hd, hfirst⟩ := hl.2 i
  refine ⟨I.equiv a, I.equiv ∘ f, n,
    geometricSideRightRayIncomingCorner_map I ha,
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

/-- Helper toward Lemma 5.6: equal prefixes determine the corrected corner
uniquely, including the reversal of the unique boundary-zero dart. -/
theorem geometricSideRightRayIncomingCorner_unique_of_prefix
    (M : GeometricSideSubmap) {d d' : ℕ → GeometricSideCell M} {i : ℕ}
    (hpref : ∀ j, j < i → d' j = d j) {a b : GeometricSideCell M}
    (ha : geometricSideRightRayIncomingCorner M d i a)
    (hb : geometricSideRightRayIncomingCorner M d' i b) : a = b := by
  cases i with
  | zero =>
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨e, he, heb⟩ := hb
    have hce := geometricSideRelation_boundary_self_unique M 0 hc he
    rw [← hce] at heb
    exact geometricSideRelation_opposite_right_unique M hca heb
  | succ j =>
    change geometricSideRelation M .opposite (d j) a at ha
    change geometricSideRelation M .opposite (d' j) b at hb
    rw [hpref j (Nat.lt_succ_self j)] at hb
    exact geometricSideRelation_opposite_right_unique M ha hb
/-- Helper toward Lemma 5.6: first-admissible scanning gives uniqueness
whenever the stored clockwise step is functional. This structural lemma's
rotation law is proved below for every realized side; no recognition or
identification is assumed. -/
theorem intrinsicallyLeftmostAdjacentRightRay_unique_of_rotation
    (M : GeometricSideSubmap) (longest : Bool)
    (hrot : ∀ a b c : GeometricSideCell M,
      geometricSideRelation M .rotation b a →
      geometricSideRelation M .rotation c a → b = c)
    {v d v' d' : ℕ → GeometricSideCell M}
    (hl : intrinsicallyLeftmostAdjacentRightRay M longest v d)
    (hl' : intrinsicallyLeftmostAdjacentRightRay M longest v' d') :
    v = v' ∧ d = d' := by
  have hd : ∀ i, d i = d' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hpref : ∀ j, j < i → d' j = d j := fun j hj => (ih j hj).symm
      obtain ⟨a, f, n, ha, hf, hend, hfirst⟩ := hl.2 i
      obtain ⟨b, g, m, hb, hg, hend', hfirst'⟩ := hl'.2 i
      have hab := geometricSideRightRayIncomingCorner_unique_of_prefix M hpref ha hb
      have hsync : ∀ t, t ≤ n → t ≤ m → f t = g t := by
        intro t
        induction t with
        | zero => intro _ _; exact hf.1.trans (hab.trans hg.1.symm)
        | succ t ht =>
          intro htn htm
          have he := ht (by omega) (by omega)
          apply hrot (f t) (f (t + 1)) (g (t + 1)) (hf.2 t (by omega))
          rw [he]
          exact hg.2 t (by omega)
      rcases lt_trichotomy n m with hnm | hnm | hmn
      · exact False.elim (hfirst' v d hl.1
          (fun j hj => ih j hj) n hnm ((hsync n le_rfl hnm.le).symm.trans hend))
      · exact hend.symm.trans ((hsync n le_rfl hnm.le).trans (hnm ▸ hend'))
      · exact False.elim (hfirst v' d' hl'.1 hpref m hmn
          ((hsync m hmn.le le_rfl).trans hend'))
  refine ⟨?_, funext hd⟩
  funext i
  have hi := (hl.1.1 i).2.1
  have hi' := (hl'.1.1 i).2.1
  rw [← hd i] at hi'
  exact geometricSideRelation_incident_right_unique M hi hi'

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: uniqueness on every realized right side follows
from its proved functional clockwise rotation. -/
theorem m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRightRay_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {v d v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp P .right)}
    (hl : intrinsicallyLeftmostAdjacentRightRay (m0GeodesicSide hp P .right) longest v d)
    (hl' : intrinsicallyLeftmostAdjacentRightRay (m0GeodesicSide hp P .right) longest v' d') :
    v = v' ∧ d = d' :=
  intrinsicallyLeftmostAdjacentRightRay_unique_of_rotation _ longest
    (m0GeodesicSide_clockwiseStep_unique hp P .right) hl hl'

section SourceFamily
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)

/-- Helper toward Lemma 5.6: at step zero the source departure is first
admissible clockwise from the reversed boundary-zero dart. -/
theorem m0GeodesicRightSide_nextRay_firstAdmissible_zero :
    let M := m0GeodesicSide hp (P (k - 1)) .right
    let d := m0GeodesicRightSideNextDarts hp P T hleft hc k
    ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRightRayIncomingCorner M d 0 a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d 0 ∧
      ∀ (v' d' : ℕ → GeometricSideCell M),
        geometricSideAdjacentGeodesicCandidate M longest v' d' →
        (∀ j, j < 0 → d' j = d j) →
        ∀ j, j < n → f j ≠ d' 0 := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let w := shiftedStream W 0
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  let e := (M.boundary 0).1
  let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨(e, true), m0GeodesicRightSide_boundary_mem_edges hp (P (k - 1)) 0⟩
  have hcorner : geometricSideRightRayIncomingCorner M
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) 0 (.inr a) :=
    ⟨.inr ⟨M.boundary 0, m0GeodesicRightSide_boundary_mem_edges hp (P (k - 1)) 0⟩,
      rfl, rfl⟩
  have hav : geometricSideDartInitial M a.val = ((P k).codePath.initial 0).1.id := by
    have hs := m0GeodesicRightSide_reverse_boundary_zero_initial hp (P (k - 1))
    rw [sub_add_cancel] at hs
    exact hs.trans (m0Geodesic_initial_zero (P k)).symm
  let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((P k).codePath.edge 0, false), (hcontain 0).1⟩
  have hv : wholePlaneDartVertex W (wholePlaneDartι W 0 b.val) =
      wholePlaneDartVertex W (wholePlaneDartι W 0 a.val) := by
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    apply congrArg (wholePlaneVertexι W 0)
    exact ((P k).codePath.edge_outgoing_at_initial w 0).2.trans hav.symm
  have hba : wholePlaneDartι W 0 b.val ≠ wholePlaneDartι W 0 a.val := by
    intro he
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) he
    change false = true at hbit
    cases hbit
  obtain ⟨r, _, _, hfirst, hindices⟩ :=
    m0WholePlane_clockwiseFirstReturn_indices (H := H) (wholePlaneDartι W 0 a.val)
  obtain ⟨n, _, hnr, hnb⟩ := hindices (wholePlaneDartι W 0 b.val) hv hba
  obtain ⟨f, m, hscan, hend, hearlier⟩ :=
    m0GeodesicSide_clockwiseScan_before_ambientEndpoint hp (P (k - 1)) .right a b n hnb
  refine ⟨.inr a, f, m, hcorner, hscan, hend, ?_⟩
  intro v' d' hcandidate hpref j hj heq
  have hlift := m0GeodesicRightSide_adjacentCandidate_coherentAmbientLift
    hp (P (k - 1)) hcandidate
  rw [sub_add_cancel] at hlift
  obtain ⟨Q, _, q, _, hdq, _, hQq⟩ := hlift
  have hturn := m0GeodesicRightSide_nextRay_candidate_counterclockwiseTurn_le
    hp P T hleft hc k hcandidate 0 e hpref
  rw [hdq 0] at hturn
  change ccwTurn _ (((monotoneFamilyDrawing _ _ _).arc
    ((q 0).val, false)).initialDirection) ≤ _ at hturn
  rw [← hQq 0] at hturn
  obtain ⟨c, t, hfc, htn, htc⟩ := hearlier j hj
  have hcq : c.val = ((q 0).val, false) := by
    exact congrArg Subtype.val (Sum.inr.inj (hfc.symm.trans (heq.trans (hdq 0))))
  have hfalse : c.val.2 = false := by
    have hout := (hcandidate.1 0).1
    rw [← heq, hfc] at hout
    exact hout.2
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have htc0 : (wholePlaneDartι W 0 a.val : WholePlaneDart W) =
        wholePlaneDartι W 0 c.val := by
      subst t
      exact htc
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) htc0
    change true = c.val.2 at hbit
    rw [hfalse] at hbit
    cases hbit
  have hang := m0WholePlane_clockwiseIterate_departureAngle_lt
    (W := W) (H := H) (h := h) (hp := hp) (wholePlaneDartι W 0 a.val) r
    hfirst htpos htn hnr
  have ha : a.val = (e, true) := rfl
  rw [htc, hnb, ha, hcq, ← hQq 0] at hang
  have hraw := (m0WholePlane_incomingCorner_ccwTurn_lt_iff_rawArg_lt
    (W := W) (H := H) (h := h) (hp := hp) e (Q.codePath.edge 0)
    ((P k).codePath.edge 0)
    (Q.codePath.edge_outgoing_at_initial w 0).1
    ((P k).codePath.edge_outgoing_at_initial w 0).1).1 hang
  have hstrict := (ccwTurn_west_east_lt_iff_arg_lt _ _ _
    (m0RawDrawing_incoming_initialDirection_re_neg H e)
    (outgoing_initialDirection_re_pos _ _ _ _
      ((P k).codePath.edge_outgoing_at_initial w 0).1)
    (outgoing_initialDirection_re_pos _ _ _ _
      (Q.codePath.edge_outgoing_at_initial w 0).1)).2 hraw
  exact (not_lt_of_ge hturn) hstrict

/-- Helper toward Lemma 5.6: the actual next source ray satisfies the
corrected intrinsic selector in the right side of the preceding ray. -/
theorem m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight :
    intrinsicallyLeftmostAdjacentRightRay
      (m0GeodesicSide hp (P (k - 1)) .right) longest
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) := by
  refine ⟨m0GeodesicRightSide_nextRay_candidate hp P T hleft hc k, ?_⟩
  intro i
  cases i with
  | zero => exact m0GeodesicRightSide_nextRay_firstAdmissible_zero hp P T hleft hc k
  | succ i => exact m0GeodesicRightSide_nextRay_firstAdmissible_succ hp P T hleft hc k i

end SourceFamily
/-- Helper toward Lemma 5.6: the incoming dart for a forward coded ray,
starting with reversed exterior-boundary dart 0 and then reversing its previous edge. -/
@[expose] def geoSliceRightCornerSeamRayIncoming (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) : ℕ → ℕ × Bool
  | 0 => ((M.boundary 0).1, !(M.boundary 0).2)
  | i + 1 => (geoSliceSeamRayEdge M p i, true)

/-- Helper toward Lemma 5.6: every coded incoming-corner coordinate is measurable. -/
theorem measurable_geoSliceRightCornerSeamRayIncoming (p : GeoSliceSeamRayCode) (i : ℕ) :
    Measurable (fun M => geoSliceRightCornerSeamRayIncoming M p i) := by
  cases i with
  | zero =>
    exact (measurable_of_countable (fun d : ℕ × Bool => (d.1, !d.2))).comp
      ((comap_measurable geometricSideCode).snd.snd.snd.snd.snd.snd.snd.snd.fst.eval
        (a := 0))
  | succ i => exact (measurable_geoSliceSeamRayEdge p i).prodMk measurable_const

/-- Helper toward Lemma 5.6: first-admissible scanning among the countable
family of eventually-seam candidates. A scan is finite data, and the test
does not quantify over arbitrary infinite competitor sequences. -/
@[expose] def geoSliceRightCornerSeamRayFirst (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) : Prop :=
  geoSliceSeamRayCandidate longest M p ∧
  ∀ i : ℕ, ∃ n : ℕ, ∃ f : Fin (n + 1) → ℕ × Bool,
    f 0 = geoSliceRightCornerSeamRayIncoming M p i ∧
    (∀ j, (f j).1 ∈ M.edges) ∧
    (∀ j : Fin n, M.rotation (f ⟨j + 1, by omega⟩) (f ⟨j, by omega⟩)) ∧
    f ⟨n, by omega⟩ = (geoSliceSeamRayEdge M p i, false) ∧
    ∀ p' : GeoSliceSeamRayCode, geoSliceSeamRayCandidate longest M p' →
      (∀ j : ℕ, j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j) →
      ∀ j : Fin (n + 1), j.val < n → f j ≠ (geoSliceSeamRayEdge M p' i, false)

/-- Helper toward Lemma 5.6: the first-admissible finite-scan test is
measurable in the side code, including its countable competitor search. -/
theorem measurableSet_geoSliceRightCornerSeamRayFirst (longest : Bool) (p : GeoSliceSeamRayCode) :
    MeasurableSet {M | geoSliceRightCornerSeamRayFirst longest M p} := by
  have hc : Measurable geometricSideCode := comap_measurable geometricSideCode
  simp only [geoSliceRightCornerSeamRayFirst, Set.ofPred_and]
  apply (measurableSet_geoSliceSeamRayCandidate longest p).inter
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro f
  have hstart : MeasurableSet {M : GeometricSideSubmap |
      f 0 = geoSliceRightCornerSeamRayIncoming M p i} :=
    (measurable_const.eq (measurable_geoSliceRightCornerSeamRayIncoming p i)).setOf
  have hedges : MeasurableSet {M : GeometricSideSubmap | ∀ j, (f j).1 ∈ M.edges} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((hc.snd.fst.eval (a := (f j).1)).eq_const true).setOf
  have hrot : MeasurableSet {M : GeometricSideSubmap | ∀ j : Fin n,
      M.rotation (f ⟨j + 1, by omega⟩) (f ⟨j, by omega⟩)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        (((hc.snd.snd.snd.snd.snd.fst.eval (a := f ⟨j + 1, by omega⟩)).eval
          (a := f ⟨j, by omega⟩)).eq_const true).setOf
  have hend : MeasurableSet {M : GeometricSideSubmap |
      f ⟨n, by omega⟩ = (geoSliceSeamRayEdge M p i, false)} :=
    (measurable_const.eq ((measurable_geoSliceSeamRayEdge p i).prodMk measurable_const)).setOf
  have hfirst : MeasurableSet {M : GeometricSideSubmap |
      ∀ p' : GeoSliceSeamRayCode, geoSliceSeamRayCandidate longest M p' →
      (∀ j : ℕ, j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j) →
      ∀ j : Fin (n + 1), j.val < n → f j ≠ (geoSliceSeamRayEdge M p' i, false)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro p'
    apply (measurableSet_geoSliceSeamRayCandidate longest p').imp
    have hprefix : MeasurableSet {M : GeometricSideSubmap | ∀ j : ℕ,
        j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        ((measurable_geoSliceSeamRayEdge p' j).eq (measurable_geoSliceSeamRayEdge p j)).setOf
    apply hprefix.imp
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_const.eq
        ((measurable_geoSliceSeamRayEdge p' i).prodMk measurable_const)).setOf.compl)
  exact hstart.inter (hedges.inter (hrot.inter (hend.inter hfirst)))

/-- Helper toward Lemma 5.6: finite first-admissible scans determine
the edge sequence uniquely when clockwise succession is functional on
retained darts. Different finite encodings of the same ray are permitted. -/
theorem geoSliceRightCornerSeamRayFirst_edges_unique (longest : Bool) (M : GeometricSideSubmap)
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    {p q : GeoSliceSeamRayCode}
    (hp : geoSliceRightCornerSeamRayFirst longest M p)
    (hq : geoSliceRightCornerSeamRayFirst longest M q) :
    ∀ i, geoSliceSeamRayEdge M p i = geoSliceSeamRayEdge M q i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    obtain ⟨n, f, hf0, hfe, hfr, hfn, hfirst⟩ := hp.2 i
    obtain ⟨m, g, hg0, hge, hgr, hgm, hfirst'⟩ := hq.2 i
    have hcorner : geoSliceRightCornerSeamRayIncoming M p i = geoSliceRightCornerSeamRayIncoming M q i := by
      cases i with
      | zero => rfl
      | succ i => exact congrArg (fun e => (e, true)) (ih i (Nat.lt_succ_self i))
    have hsync : ∀ t (htn : t ≤ n) (htm : t ≤ m),
        f ⟨t, by omega⟩ = g ⟨t, by omega⟩ := by
      intro t
      induction t with
      | zero => intro _ _; exact hf0.trans (hcorner.trans hg0.symm)
      | succ t ht =>
        intro htn htm
        have he := ht (by omega) (by omega)
        apply hrot (f ⟨t, by omega⟩) _ _ (hfe _) (hfe _) (hge _)
          (hfr ⟨t, by omega⟩)
        rw [he]
        exact hgr ⟨t, by omega⟩
    have hend : f ⟨n, by omega⟩ = g ⟨m, by omega⟩ := by
      rcases lt_trichotomy n m with hnm | hnm | hmn
      · exact False.elim (hfirst' p hp.1 (fun j hj => ih j hj) ⟨n, by omega⟩ hnm
          ((hsync n le_rfl hnm.le).symm.trans hfn))
      · subst m
        exact hsync n le_rfl le_rfl
      · exact False.elim (hfirst q hq.1 (fun j hj => (ih j hj).symm)
          ⟨m, by omega⟩ hmn ((hsync m hmn.le le_rfl).trans hgm))
    exact congrArg Prod.fst (hfn.symm.trans (hend.trans hgm))

/-- Helper toward Lemma 5.6: first-admissible codes at a prescribed
natural encoding index. This is a countable search predicate. -/
@[expose] def geoSliceRightCornerSeamRayIndexValid (longest : Bool)
    (M : GeometricSideSubmap) (n : ℕ) : Prop :=
  ∃ p : GeoSliceSeamRayCode, Encodable.encode p = n ∧ geoSliceRightCornerSeamRayFirst longest M p

/-- Helper toward Lemma 5.6: every index-validity event is measurable. -/
theorem measurableSet_geoSliceRightCornerSeamRayIndexValid (longest : Bool) (n : ℕ) :
    MeasurableSet {M | geoSliceRightCornerSeamRayIndexValid longest M n} := by
  simp only [geoSliceRightCornerSeamRayIndexValid, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun p => (MeasurableSet.const _).inter
    (measurableSet_geoSliceRightCornerSeamRayFirst longest p)

/-- Helper toward Lemma 5.6: choose the least valid natural encoding
index, with `none` precisely when no first-admissible coded ray exists. -/
@[expose] noncomputable def geoSliceRightCornerRayIndexOption (longest : Bool)
    (M : GeometricSideSubmap) : Option ℕ :=
  if h : ∃ n, geoSliceRightCornerSeamRayIndexValid longest M n then some (Nat.find h) else none

local instance : MeasurableSpace (Option ℕ) := ⊤

/-- Helper toward Lemma 5.6: the exact graph of the least valid index. -/
theorem geoSliceRightCornerRayIndexOption_eq_some_iff (longest : Bool)
    (M : GeometricSideSubmap) (n : ℕ) :
    geoSliceRightCornerRayIndexOption longest M = some n ↔
      geoSliceRightCornerSeamRayIndexValid longest M n ∧
        ∀ j, j < n → ¬geoSliceRightCornerSeamRayIndexValid longest M j := by
  by_cases h : ∃ n, geoSliceRightCornerSeamRayIndexValid longest M n
  · simp only [geoSliceRightCornerRayIndexOption, dite_eq_left h, Option.some.injEq]
    exact Nat.find_eq_iff h
  · simp only [geoSliceRightCornerRayIndexOption, dite_eq_right h]
    constructor
    · intro he
      cases he
    · rintro ⟨hn, _⟩
      exact (h ⟨n, hn⟩).elim

/-- Helper toward Lemma 5.6: least valid index selection is measurable;
its singletons are countable Boolean combinations of validity events. -/
theorem measurable_geoSliceRightCornerRayIndexOption (longest : Bool) :
    Measurable (geoSliceRightCornerRayIndexOption longest) := by
  apply measurable_to_countable'
  intro n
  cases n with
  | none =>
    have he : (geoSliceRightCornerRayIndexOption longest) ⁻¹' {none} =
        (⋃ n : ℕ, {M | geoSliceRightCornerSeamRayIndexValid longest M n})ᶜ := by
      ext M
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        geoSliceRightCornerRayIndexOption, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      split <;> simp_all only [Option.some_ne_none, not_true_eq_false,
        not_false_eq_true]
    rw [he]
    exact (MeasurableSet.iUnion fun n =>
      measurableSet_geoSliceRightCornerSeamRayIndexValid longest n).compl
  | some n =>
    have he : (geoSliceRightCornerRayIndexOption longest) ⁻¹' {some n} =
        {M | geoSliceRightCornerSeamRayIndexValid longest M n ∧
          ∀ j, j < n → ¬geoSliceRightCornerSeamRayIndexValid longest M j} := by
      ext M
      exact geoSliceRightCornerRayIndexOption_eq_some_iff longest M n
    rw [he]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_geoSliceRightCornerSeamRayIndexValid longest n).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (measurableSet_geoSliceRightCornerSeamRayIndexValid longest j).compl)

local instance : MeasurableSpace GeoSliceSeamRayCode := ⊤
local instance : MeasurableSpace (Option GeoSliceSeamRayCode) := ⊤

/-- Helper toward Lemma 5.6: a fixed optional countable ray decoder
on a single side. It returns a first-admissible eventually-seam code. -/
@[expose] noncomputable def geoSliceRightCornerRayCodeOption (longest : Bool)
    (M : GeometricSideSubmap) : Option GeoSliceSeamRayCode :=
  (geoSliceRightCornerRayIndexOption longest M).bind (Encodable.decode (α := GeoSliceSeamRayCode))

/-- Helper toward Lemma 5.6: the one-side countable ray-code selector
is measurable on the full side-code space. -/
theorem measurable_geoSliceRightCornerRayCodeOption (longest : Bool) :
    Measurable (geoSliceRightCornerRayCodeOption longest) :=
  (measurable_of_countable (fun n : Option ℕ =>
    n.bind (Encodable.decode (α := GeoSliceSeamRayCode)))).comp
      (measurable_geoSliceRightCornerRayIndexOption longest)

/-- Helper toward Lemma 5.6: whenever a first-admissible coded ray exists,
the fixed decoder returns such a code, rather than a default ray. -/
theorem geoSliceRightCornerRayCodeOption_spec (longest : Bool) (M : GeometricSideSubmap)
    (hex : ∃ p, geoSliceRightCornerSeamRayFirst longest M p) :
    ∃ p, geoSliceRightCornerRayCodeOption longest M = some p ∧
      geoSliceRightCornerSeamRayFirst longest M p := by
  have hex' : ∃ n, geoSliceRightCornerSeamRayIndexValid longest M n := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨Encodable.encode p, p, rfl, hp⟩
  obtain ⟨p, hp, hfirst⟩ := Nat.find_spec hex'
  refine ⟨p, ?_, hfirst⟩
  simp only [geoSliceRightCornerRayCodeOption, geoSliceRightCornerRayIndexOption,
    dite_eq_left hex', Option.bind_some, ← hp, Encodable.encodek]

/-- Helper toward Lemma 5.6: the complete graph of the optional code
reader is the least encoding among first-admissible seam-tail candidates. -/
theorem geoSliceRightCornerRayCodeOption_eq_some_iff (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) :
    geoSliceRightCornerRayCodeOption longest M = some p ↔
      geoSliceRightCornerSeamRayFirst longest M p ∧
      ∀ q, geoSliceRightCornerSeamRayFirst longest M q → Encodable.encode p ≤ Encodable.encode q := by
  constructor
  · intro hread
    unfold geoSliceRightCornerRayCodeOption geoSliceRightCornerRayIndexOption at hread
    split at hread
    · rename_i h
      simp only [Option.bind_some] at hread
      obtain ⟨q, hq, hqfirst⟩ := Nat.find_spec h
      have hdec : Encodable.decode (Nat.find h) = some q := by
        rw [← hq]
        exact Encodable.encodek q
      have hqp : q = p := Option.some.inj (hdec.symm.trans hread)
      subst q
      refine ⟨hqfirst, fun q hqfirst' => ?_⟩
      rw [hq]
      exact Nat.find_min' h ⟨q, rfl, hqfirst'⟩
    · cases hread
  · rintro ⟨hfirst, hmin⟩
    have hindex : geoSliceRightCornerRayIndexOption longest M = some (Encodable.encode p) := by
      apply (geoSliceRightCornerRayIndexOption_eq_some_iff longest M _).2
      refine ⟨⟨p, rfl, hfirst⟩, ?_⟩
      intro j hj hjvalid
      obtain ⟨q, hq, hqfirst⟩ := hjvalid
      exact (not_le_of_gt hj) (hq ▸ hmin q hqfirst)
    simp only [geoSliceRightCornerRayCodeOption, hindex, Option.bind_some, Encodable.encodek]

/-- Helper toward Lemma 5.6: failure of the optional ray reader is
exactly absence of any first-admissible eventually-seam candidate. -/
theorem geoSliceRightCornerRayCodeOption_eq_none_iff (longest : Bool)
    (M : GeometricSideSubmap) :
    geoSliceRightCornerRayCodeOption longest M = none ↔
      ¬∃ p, geoSliceRightCornerSeamRayFirst longest M p := by
  constructor
  · intro hnone hex
    obtain ⟨p, hp, _⟩ := geoSliceRightCornerRayCodeOption_spec longest M hex
    rw [hnone] at hp
    cases hp
  · intro hnone
    cases he : geoSliceRightCornerRayCodeOption longest M with
    | none => rfl
    | some p =>
      exact (hnone ⟨p, ((geoSliceRightCornerRayCodeOption_eq_some_iff longest M p).1 he).1⟩).elim

/-- Helper toward Lemma 5.6: the selected ray's individual edge coordinate,
with `none` when the side has no first-admissible eventually-seam candidate. -/
@[expose] noncomputable def geoSliceRightCornerRayEdgeOption (longest : Bool)
    (i : ℕ) (M : GeometricSideSubmap) : Option ℕ :=
  (geoSliceRightCornerRayCodeOption longest M).map (fun p => geoSliceSeamRayEdge M p i)

/-- Helper toward Lemma 5.6: every selected edge coordinate is a
measurable function of the single side code. -/
theorem measurable_geoSliceRightCornerRayEdgeOption (longest : Bool) (i : ℕ) :
    Measurable (geoSliceRightCornerRayEdgeOption longest i) := by
  let f (z : GeometricSideSubmap × Option GeoSliceSeamRayCode) : Option ℕ :=
    z.2.map (fun p => geoSliceSeamRayEdge z.1 p i)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro p
    cases p with
    | none => exact measurable_const
    | some p =>
      exact (measurable_of_countable (some : ℕ → Option ℕ)).comp
        (measurable_geoSliceSeamRayEdge p i)
  exact hf.comp (measurable_id.prodMk (measurable_geoSliceRightCornerRayCodeOption longest))

local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: the corrected fixed right-side reader returns
joint least offsets in source order, old seam followed by next ray. -/
@[expose] noncomputable def geoSliceRightCornerOffsetsOption (longest : Bool)
    (M : GeometricSideSubmap) : Option (ℕ × ℕ) :=
  ((geoSliceRightCornerRayCodeOption longest M).bind
    (fun p => geoSliceSeamRayOffsets p M)).map Prod.swap

/-- Helper toward Lemma 5.6: the corrected right-side least-offset reader
is measurable on the complete side-code space. -/
theorem measurable_geoSliceRightCornerOffsetsOption (longest : Bool) :
    Measurable (geoSliceRightCornerOffsetsOption longest) := by
  let f (z : GeometricSideSubmap × Option GeoSliceSeamRayCode) : Option (ℕ × ℕ) :=
    z.2.bind (fun p => geoSliceSeamRayOffsets p z.1)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro p
    cases p with
    | none => exact measurable_const
    | some p => exact measurable_geoSliceSeamRayOffsets p
  exact (measurable_of_countable (fun p : Option (ℕ × ℕ) => p.map Prod.swap)).comp
    (hf.comp (measurable_id.prodMk (measurable_geoSliceRightCornerRayCodeOption longest)))

section SourceReaders
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hco : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)

include T hleft hco

/-- Helper toward Lemma 5.6: the next source ray passes the corrected
countable test, with no containment or selector-identification premise. -/
theorem geoSliceRightCornerSeamRayFirst_source (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b) :
    geoSliceRightCornerSeamRayFirst longest (m0GeodesicSide hp (P (k - 1)) .right)
      (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a) := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let p : GeoSliceSeamRayCode :=
    (List.ofFn (fun j : Fin b => (P k).codePath.edge j), a)
  have heq (i : ℕ) : geoSliceSeamRayEdge M p i = (P k).codePath.edge i :=
    geoSliceRightSeamRayEdge_source_eq hp P k a b hab i
  refine ⟨geoSliceRightSeamRayCandidate_source hp P T hleft hco k a b hab, ?_⟩
  intro i
  obtain ⟨c, f, n, hcorner, hf, hend, hfirst⟩ :=
    (m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight hp P T hleft hco k).2 i
  have hc : ∃ d, c = .inr d := by
    cases i with
    | zero => cases c with
      | inl v =>
        obtain ⟨z, _, hz⟩ := hcorner
        cases z <;> exact False.elim hz
      | inr d => exact ⟨d, rfl⟩
    | succ i => cases c with
      | inl v => exact False.elim hcorner
      | inr d => exact ⟨d, rfl⟩
  obtain ⟨c, rfl⟩ := hc
  let g (j : Fin (n + 1)) := geoSliceCellDartValue (f j)
  have hfg (j : Fin (n + 1)) : ∃ d,
      f j = .inr d ∧ g j = d.val := by
    obtain ⟨d, hd⟩ := geometricSideClockwiseScan_isDart hf j (by omega)
    exact ⟨d, hd, by simp only [g, hd, geoSliceCellDartValue]⟩
  refine ⟨n, g, ?_, ?_, ?_, ?_, ?_⟩
  · change geoSliceCellDartValue (f 0) = geoSliceRightCornerSeamRayIncoming M p i
    rw [hf.1]
    change c.val = geoSliceRightCornerSeamRayIncoming M p i
    cases i with
    | zero =>
      obtain ⟨z, hz, hzc⟩ := hcorner
      cases z with
      | inl z => exact False.elim hz
      | inr z =>
        exact hzc.symm.trans (congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hz.symm)
    | succ i =>
      change ((P k).codePath.edge i, true) = c.val at hcorner
      simpa only [geoSliceRightCornerSeamRayIncoming, heq] using hcorner.symm
  · intro j
    obtain ⟨d, _, hd⟩ := hfg j
    rw [hd]
    exact d.property
  · intro j
    obtain ⟨d, hd, hgd⟩ := hfg ⟨j + 1, by omega⟩
    obtain ⟨e, he, hge⟩ := hfg ⟨j, by omega⟩
    rw [hgd, hge]
    have hr := hf.2 j j.isLt
    rw [hd, he] at hr
    exact hr
  · change geoSliceCellDartValue (f n) = (geoSliceSeamRayEdge M p i, false)
    rw [hend, heq]
    rfl
  · intro q hq hpref j hj hgj
    have hprefix : ∀ t, t < i → geoSliceSeamRayDartCells hq t =
        m0GeodesicRightSideNextDarts hp P T hleft hco k t := by
      intro t ht
      apply congrArg Sum.inr
      apply Subtype.ext
      change (geoSliceSeamRayEdge M q t, false) = ((P k).codePath.edge t, false)
      rw [hpref t ht, heq]
    apply hfirst (geoSliceSeamRayVertexCells hq) (geoSliceSeamRayDartCells hq)
      (geoSliceSeamRayCandidate_intrinsic hq) hprefix j hj
    obtain ⟨d, hd, hgd⟩ := hfg j
    rw [hd]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact hgd.symm.trans hgj

/-- Helper toward Lemma 5.6: every accepted corrected countable code has
the actual next source ray's complete individual-edge stream. -/
theorem geoSliceRightCornerSeamRayFirst_source_edges (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b)
    {p : GeoSliceSeamRayCode}
    (hpfirst : geoSliceRightCornerSeamRayFirst longest
      (m0GeodesicSide hp (P (k - 1)) .right) p) :
    ∀ i, geoSliceSeamRayEdge (m0GeodesicSide hp (P (k - 1)) .right) p i =
      (P k).codePath.edge i := by
  have hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges →
      b.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges →
      c.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges →
      (m0GeodesicSide hp (P (k - 1)) .right).rotation b a →
      (m0GeodesicSide hp (P (k - 1)) .right).rotation c a → b = c := by
    intro a b c ha hb hc hba hca
    have he := m0GeodesicSide_clockwiseStep_unique hp (P (k - 1)) .right
      (.inr ⟨a, ha⟩) (.inr ⟨b, hb⟩) (.inr ⟨c, hc⟩) hba hca
    exact congrArg Subtype.val (Sum.inr.inj he)
  intro i
  exact (geoSliceRightCornerSeamRayFirst_edges_unique longest _ hrot hpfirst
    (geoSliceRightCornerSeamRayFirst_source hp P T hleft hco k a b hab) i).trans
      (geoSliceRightSeamRayEdge_source_eq hp P k a b hab i)

/-- Helper toward Lemma 5.6: the fixed corrected right-side edge reader
returns the next source geodesic's edge at every natural index. -/
theorem geoSliceRightCornerRayEdgeOption_source (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b) (i : ℕ) :
    geoSliceRightCornerRayEdgeOption longest i (m0GeodesicSide hp (P (k - 1)) .right) =
      some ((P k).codePath.edge i) := by
  obtain ⟨p, hread, hfirst⟩ := geoSliceRightCornerRayCodeOption_spec longest _
    ⟨_, geoSliceRightCornerSeamRayFirst_source hp P T hleft hco k a b hab⟩
  simp only [geoSliceRightCornerRayEdgeOption, hread, Option.map_some,
    geoSliceRightCornerSeamRayFirst_source_edges hp P T hleft hco k a b hab hfirst]

/-- Helper toward Lemma 5.6: the corrected fixed right-side offset reader
returns the source's joint least pair in the order old seam, next ray. -/
theorem geoSliceRightCornerOffsetsOption_source (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    geoSliceRightCornerOffsetsOption longest (m0GeodesicSide hp (P (k - 1)) .right) =
      some (a, b) := by
  obtain ⟨p, hread, hfirst⟩ := geoSliceRightCornerRayCodeOption_spec longest _
    ⟨_, geoSliceRightCornerSeamRayFirst_source hp P T hleft hco k a b hab.1⟩
  have hoff : geoSliceSeamRayOffsets p (m0GeodesicSide hp (P (k - 1)) .right) =
      some (b, a) := by
    apply (geoSliceSidePairOffsets_eq_some_iff _ b a).2
    have htail (i j : ℕ) :
        geoSliceSidePairTailsCoalesce
          ((geoSliceSeamRayMarkedSide p (m0GeodesicSide hp (P (k - 1)) .right),
            m0GeodesicSide hp (P (k - 1)) .right), id) i j ↔
          M0CutEdgeTailsCoalesce (P (k - 1)) (P k) j i := by
      simp only [geoSliceSidePairTailsCoalesce, geoSliceSeamRayMarkedSide,
        geoSliceRightCornerSeamRayFirst_source_edges hp P T hleft hco k a b hab.1 hfirst]
      constructor
      · intro hco n
        exact congrArg (wholePlaneEdgeι W 0) (hco n).symm
      · intro hco n
        exact (wholePlaneEdgeι_injective W 0 (hco n)).symm
    refine ⟨(htail b a).2 hab.1, ?_⟩
    intro i j hij
    obtain ⟨ha, hb⟩ := hab.2 j i ((htail i j).1 hij)
    exact ⟨hb, ha⟩
  simp only [geoSliceRightCornerOffsetsOption, hread, Option.bind_some, hoff,
    Option.map_some, Prod.swap_prod_mk]

end SourceReaders

/-- Helper toward Lemma 5.6: on one full-measure event, both metrics and
every cut have the corrected intrinsic selector and fixed right-side readers
recovering the next ray and the joint least offsets in source order. -/
theorem m0Cut_ae_rightCornerRay_and_offsets :
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
      ∃ hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k),
      ∃ hc : ∀ m : ℤ, ∃ a b : ℕ,
        M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b,
      ∀ k : ℤ,
        intrinsicallyLeftmostAdjacentRightRay
          (m0GeodesicSide hp (P (k - 1)) .right) longest
          (m0GeodesicRightSideNextVertices hp P T hleft hc k)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k) ∧
        ∃ a b : ℕ, M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b ∧
          geoSliceRightCornerOffsetsOption longest
            (m0GeodesicSide hp (P (k - 1)) .right) = some (a, b) ∧
          ∀ i : ℕ, geoSliceRightCornerRayEdgeOption longest i
            (m0GeodesicSide hp (P (k - 1)) .right) = some ((P k).codePath.edge i) := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hmodes⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, _, hc, _⟩ := hmodes longest
  have hc' (m : ℤ) : ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b := by
    have hm := hc (m + 1)
    rw [show m + 1 - 1 = m by omega] at hm
    exact hm
  refine ⟨P, T, hleft, hc', fun k => ?_⟩
  obtain ⟨a, b, hab⟩ := hc k
  exact ⟨m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight hp P T hleft hc' k,
    a, b, hab, geoSliceRightCornerOffsetsOption_source hp P T hleft hc' k a b hab,
    geoSliceRightCornerRayEdgeOption_source hp P T hleft hc' k a b hab.1⟩

/-- Helper toward Lemma 5.6: corrected intrinsic selection is invariant
under complete marked side isomorphism in both directions. -/
theorem intrinsicallyLeftmostAdjacentRightRay_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    (v d : ℕ → GeometricSideCell M) :
    intrinsicallyLeftmostAdjacentRightRay M longest v d ↔
      intrinsicallyLeftmostAdjacentRightRay N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  constructor
  · exact intrinsicallyLeftmostAdjacentRightRay_map I longest
  · intro hl
    have hm := intrinsicallyLeftmostAdjacentRightRay_map
      (GeometricSideMarkedIso.symm I) longest hl
    have hv : I.equiv.symm ∘ (I.equiv ∘ v) = v := by
      funext i
      exact I.equiv.symm_apply_apply (v i)
    have hd : I.equiv.symm ∘ (I.equiv ∘ d) = d := by
      funext i
      exact I.equiv.symm_apply_apply (d i)
    change intrinsicallyLeftmostAdjacentRightRay M longest
      (I.equiv.symm ∘ (I.equiv ∘ v)) (I.equiv.symm ∘ (I.equiv ∘ d)) at hm
    rw [hv, hd] at hm
    exact hm

/-- Helper toward Lemma 5.6: corrected intrinsic uniqueness persists on
every complete marked representative of a realized right side. -/
theorem m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRightRay_unique_of_markedIso
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide hp P .right) N)
    {v d v' d' : ℕ → GeometricSideCell N}
    (hl : intrinsicallyLeftmostAdjacentRightRay N longest v d)
    (hl' : intrinsicallyLeftmostAdjacentRightRay N longest v' d') :
    v = v' ∧ d = d' := by
  have he := m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRightRay_unique hp P
    (intrinsicallyLeftmostAdjacentRightRay_map (GeometricSideMarkedIso.symm I) longest hl)
    (intrinsicallyLeftmostAdjacentRightRay_map (GeometricSideMarkedIso.symm I) longest hl')
  exact ⟨funext fun i => I.equiv.symm.injective (congrFun he.1 i),
    funext fun i => I.equiv.symm.injective (congrFun he.2 i)⟩

/-- Helper toward Lemma 5.6: any corrected intrinsic selector in the source
right side is exactly the next ray, in both vertices and individual darts. -/
theorem m0GeodesicRightSide_intrinsicRightRay_eq_realizedNext
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (hl : intrinsicallyLeftmostAdjacentRightRay
      (m0GeodesicSide hp (P (k - 1)) .right) longest v d) :
    v = m0GeodesicRightSideNextVertices hp P T hleft hc k ∧
      d = m0GeodesicRightSideNextDarts hp P T hleft hc k :=
  m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRightRay_unique hp (P (k - 1)) hl
    (m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight hp P T hleft hc k)

end DirectedDistances.PaperProofs.Section5

/- OPEN (5): source identification of the future-skeleton side update.
Full binders (not an admitted declaration):

  ∀ x : XDP,
    ∃ oneSliceR : GeometricSideSubmap → Option GeometricSideClass,
    ∃ nextSide : GeometricSideSubmap → GeometricSideSubmap,
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x,
      ∀ j : ℤ,
        geoSliceFutureReader oneSliceR nextSide j
          (m0GeodesicSide s.hp (s.P j) .right) =
            (fun k : {k : ℤ // j + 1 ≤ k} => m0CutGeodesicSliceClassOption x k.val W)

Three approaches were checked against the allowed imported APIs:
1. Re-mark the selected ray as seam using geoSliceSeamRayMarkedSide.
   Its seam is now source-identified by the edge-reader theorem, but its
   vertices, edges, faces, rotation and boundary remain those of the old
   right side. Identifying it with the next closed right side would require
2. Reuse geometricSideRayDeletedTailCells and the tail-complement transport.
   These remove the common tails to describe a finite slice, whereas the
   next closed right side must retain its entire new infinite seam.
   m0CutGeodesicSlice_mem_cell_iff_previousRight_and_not_deletedTail still
   has a separate geometric side-membership conjunct. Tail deletion alone
   supplies neither the next-side region nor retained face/rotation data.
3. Choose an ambient realization of a given right-side code and read its
   next side, or iterate the source-recognized edge reader. Well-definedness
   of the former requires equality of complete next sides for all such
   realizations; the latter requires a complete next-side update at the
   first iteration. The proved intrinsic ray uniqueness determines vertex
   and dart streams, not the complementary component, faces, or induced
   rotation. Countable a.s. intersection cannot discharge those identities.

No incomplete side-update definition, geometric-identification premise,
sole coordinator. -/

/- declarations (including definitions) compiled with exit 0. Every transitive
axiom set was contained in {propext, Classical.choice, Quot.sound}; no custom
axiom or sorryAx occurred. The probes were removed before the final production
sole coordinator. Only GeoSliceRightReaders3.lean was edited. -/
