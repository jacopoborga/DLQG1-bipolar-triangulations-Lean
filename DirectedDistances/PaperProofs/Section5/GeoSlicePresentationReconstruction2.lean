/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction
public import DirectedDistances.PaperProofs.Section5.GeoSliceRotationAngleBridge








public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: intrinsic adjacent-ray existence on one event
for both metrics and every cut, retaining ambient leftmostness, least
coalescence, and transport to every representative of the marked side class.
The recognition obligation is discharged by the rotation-angle theorem. -/
theorem m0GeodesicSide_ae_intrinsicRay_exists :
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
        (∀ j : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) ∧
        (∀ k : ℤ, ∀ N : GeometricSideSubmap,
          geometricSideClass (m0GeodesicSide hp (P k) .left) =
            geometricSideClass N →
          ∃ v d : ℕ → GeometricSideCell N,
            IntrinsicallyLeftmostAdjacentRay N longest v d) := by
  apply m0GeodesicSide_ae_intrinsicRay_exists_of_recognition
  intro W H h hLL hp longest P T hleft k hcontain
  exact m0GeodesicSide_adjacentIntrinsicSelector_angleComparison hp P T hleft k hcontain

/-- Helper toward Lemma 5.6: incidence determines the vertex cell, while
retaining the entire dart and hence the identity of parallel edges. -/
theorem geometricSideRelation_incident_right_unique (M : GeometricSideSubmap)
    {a u v : GeometricSideCell M}
    (hu : geometricSideRelation M .incident a u)
    (hv : geometricSideRelation M .incident a v) : u = v := by
  cases a with
  | inl a => exact False.elim hu
  | inr a =>
    cases u with
    | inr u => exact False.elim hu
    | inl u =>
      cases v with
      | inr v => exact False.elim hv
      | inl v => exact congrArg Sum.inl (Subtype.ext (hu.symm.trans hv))

/-- Helper toward Lemma 5.6: an opposite dart is unique on any side. -/
theorem geometricSideRelation_opposite_right_unique (M : GeometricSideSubmap)
    {a u v : GeometricSideCell M}
    (hu : geometricSideRelation M .opposite a u)
    (hv : geometricSideRelation M .opposite a v) : u = v := by
  cases a with
  | inl a => exact False.elim hu
  | inr a =>
    cases u with
    | inl u => exact False.elim hu
    | inr u =>
      cases v with
      | inl v => exact False.elim hv
      | inr v => exact congrArg Sum.inr (Subtype.ext (hu.symm.trans hv))

/-- Helper toward Lemma 5.6: an indexed boundary mark denotes one dart. -/
theorem geometricSideRelation_boundary_self_unique (M : GeometricSideSubmap)
    (i : ℕ) {a b : GeometricSideCell M}
    (ha : geometricSideRelation M (.boundary i) a a)
    (hb : geometricSideRelation M (.boundary i) b b) : a = b := by
  cases a with
  | inl a => exact False.elim ha
  | inr a =>
    cases b with
    | inl b => exact False.elim hb
    | inr b => exact congrArg Sum.inr (Subtype.ext (ha.symm.trans hb))

/-- Helper toward Lemma 5.6: equal dart prefixes give the same incoming
corner, including the exterior-boundary corner at step zero. -/
theorem geometricSideRayIncomingCorner_unique_of_prefix
    (M : GeometricSideSubmap) {d d' : ℕ → GeometricSideCell M} {i : ℕ}
    (hpref : ∀ j, j < i → d' j = d j) {a b : GeometricSideCell M}
    (ha : geometricSideRayIncomingCorner M d i a)
    (hb : geometricSideRayIncomingCorner M d' i b) : a = b := by
  cases i with
  | zero => exact geometricSideRelation_boundary_self_unique M 1 ha hb
  | succ j =>
    change geometricSideRelation M .opposite (d j) a at ha
    change geometricSideRelation M .opposite (d' j) b at hb
    rw [hpref j (Nat.lt_succ_self j)] at hb
    exact geometricSideRelation_opposite_right_unique M ha hb

/-- Helper toward Lemma 5.6: first-admissible scanning gives uniqueness
whenever the stored clockwise step is functional. This structural lemma's
rotation law is proved below for every realized side; no recognition or
identification is assumed. -/
theorem intrinsicallyLeftmostAdjacentRay_unique_of_rotation
    (M : GeometricSideSubmap) (longest : Bool)
    (hrot : ∀ a b c : GeometricSideCell M,
      geometricSideRelation M .rotation b a →
      geometricSideRelation M .rotation c a → b = c)
    {v d v' d' : ℕ → GeometricSideCell M}
    (hl : IntrinsicallyLeftmostAdjacentRay M longest v d)
    (hl' : IntrinsicallyLeftmostAdjacentRay M longest v' d') :
    v = v' ∧ d = d' := by
  have hd : ∀ i, d i = d' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hpref : ∀ j, j < i → d' j = d j := fun j hj => (ih j hj).symm
      obtain ⟨a, f, n, ha, hf, hend, hfirst⟩ := hl.2 i
      obtain ⟨b, g, m, hb, hg, hend', hfirst'⟩ := hl'.2 i
      have hab := geometricSideRayIncomingCorner_unique_of_prefix M hpref ha hb
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

/-- Helper toward Lemma 5.6: the clockwise step on a realized side is
functional, since it is first return of the ambient inverse rotation. -/
theorem m0GeodesicSide_clockwiseStep_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (a b c : GeometricSideCell (m0GeodesicSide hp P s))
    (hb : geometricSideRelation (m0GeodesicSide hp P s) .rotation b a)
    (hc : geometricSideRelation (m0GeodesicSide hp P s) .rotation c a) : b = c := by
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
          ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm : _ → _)
          {d | d.1 ∈ (m0GeodesicSide hp P s).edges} b.property c.property
          ((m0GeodesicSide_clockwiseStep_iff hp P s a b).1 hb)
          ((m0GeodesicSide_clockwiseStep_iff hp P s a c).1 hc)

/-- Helper toward Lemma 5.6: two intrinsically leftmost adjacent rays on
any realized side coincide in both vertices and individual directed darts. -/
theorem m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    {v d v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp P s)}
    (hl : IntrinsicallyLeftmostAdjacentRay (m0GeodesicSide hp P s) longest v d)
    (hl' : IntrinsicallyLeftmostAdjacentRay (m0GeodesicSide hp P s) longest v' d') :
    v = v' ∧ d = d' := by
  exact intrinsicallyLeftmostAdjacentRay_unique_of_rotation _ longest
    (m0GeodesicSide_clockwiseStep_unique hp P s) hl hl'

/-- Helper toward Lemma 5.6: the side-coded previous ambient geodesic
itself satisfies the intrinsic selector. This retains the actual witnesses
used in the rotation-angle bridge, rather than merely their existence. -/
theorem m0GeodesicSide_realizedAdjacent_is_intrinsic
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) := by
  classical
  let M := m0GeodesicSide hp (P k) .left
  let w := shiftedStream W 0
  let d := m0GeodesicSideAdjacentDarts hp P k hcontain
  refine ⟨m0GeodesicSide_realized_adjacentCandidate hp P k hcontain, ?_⟩
  intro i
  have hcorner : ∃ (a : {d : ℕ × Bool // d.1 ∈ M.edges}) (e : ℕ),
      a.val = (e, true) ∧ geometricSideRayIncomingCorner M d i (.inr a) ∧
      geometricSideDartInitial M a.val = ((P (k - 1)).codePath.initial i).1.id := by
    cases i with
    | zero =>
      let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
        ⟨M.boundary 1, m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩
      refine ⟨a, (M.boundary 1).1, rfl, rfl, ?_⟩
      exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
        (m0Geodesic_initial_zero (P (k - 1))).symm
    | succ j =>
      refine ⟨⟨((P (k - 1)).codePath.edge j, true), (hcontain j).1⟩,
        (P (k - 1)).codePath.edge j, rfl, rfl, ?_⟩
      exact ((P (k - 1)).codePath.edge_incoming_at_succ w j).2
  obtain ⟨a, e, ha, hcorner, hav⟩ := hcorner
  let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((P (k - 1)).codePath.edge i, false), (hcontain i).1⟩
  have hv : wholePlaneDartVertex W (wholePlaneDartι W 0 b.val) =
      wholePlaneDartVertex W (wholePlaneDartι W 0 a.val) := by
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    apply congrArg (wholePlaneVertexι W 0)
    exact ((P (k - 1)).codePath.edge_outgoing_at_initial w i).2.trans hav.symm
  have hba : wholePlaneDartι W 0 b.val ≠ wholePlaneDartι W 0 a.val := by
    intro he
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) he
    change false = a.val.2 at hbit
    rw [ha] at hbit
    cases hbit
  obtain ⟨r, _, _, hfirst, hindices⟩ :=
    m0WholePlane_clockwiseFirstReturn_indices (H := H) (wholePlaneDartι W 0 a.val)
  obtain ⟨n, _, hnr, hnb⟩ := hindices (wholePlaneDartι W 0 b.val) hv hba
  obtain ⟨f, m, hscan, hend, hearlier⟩ :=
    m0GeodesicSide_clockwiseScan_before_ambientEndpoint hp (P k) .left a b n hnb
  refine ⟨.inr a, f, m, hcorner, hscan, hend, ?_⟩
  intro v' d' hcandidate hpref j hj heq
  obtain ⟨Q, _, q, _, hdq, _, hQq⟩ :=
    m0GeodesicLeftSide_adjacentCandidate_coherentAmbientLift hp (P k) hcandidate
  have hprefEdge (t : ℕ) (ht : t < i) :
      Q.codePath.edge t = (P (k - 1)).codePath.edge t := by
    have he := (hdq t).symm.trans ((hpref t ht).trans rfl)
    have he' := congrArg Subtype.val (Sum.inr.inj he)
    exact (hQq t).trans (congrArg Prod.fst he')
  have hvertex : ((P (k - 1)).codePath.initial i).1 = (Q.codePath.initial i).1 := by
    apply InfinitePresentPath.initial_vertex_eq_of_prefix_eq
    apply congrArg List.ofFn
    funext t
    exact (hprefEdge t.val t.isLt).symm
  have harg := m0CutLeftmostXdp_raw_departureArg_le hp (P (k - 1)) Q
    (T (k - 1)) (hleft (k - 1)) i i hvertex
  obtain ⟨c, t, hfc, htn, htc⟩ := hearlier j hj
  have hcq : c.val = ((q i).val, false) := by
    exact congrArg Subtype.val (Sum.inr.inj (hfc.symm.trans (heq.trans (hdq i))))
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have htc0 : (wholePlaneDartι W 0 a.val : WholePlaneDart W) =
        wholePlaneDartι W 0 c.val := by
      subst t
      exact htc
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) htc0
    change a.val.2 = c.val.2 at hbit
    rw [ha, hcq] at hbit
    cases hbit
  have hang := m0WholePlane_clockwiseIterate_departureAngle_lt
    (W := W) (H := H) (h := h) (hp := hp) (wholePlaneDartι W 0 a.val) r
    hfirst htpos htn hnr
  rw [htc, hnb, ha, hcq, ← hQq i] at hang
  have hraw := (m0WholePlane_incomingCorner_ccwTurn_lt_iff_rawArg_lt
    (W := W) (H := H) (h := h) (hp := hp) e (Q.codePath.edge i)
    ((P (k - 1)).codePath.edge i)
    (Q.codePath.edge_outgoing_at_initial w i).1
    ((P (k - 1)).codePath.edge_outgoing_at_initial w i).1).1 hang
  exact (not_lt_of_ge harg) hraw

/-- Helper toward Lemma 5.6: every intrinsic selector in the left side at
cut `k` is exactly the side-coded `P (k - 1)`, in vertices and darts. -/
theorem m0GeodesicSide_intrinsicRay_eq_realizedAdjacent
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hl : IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest v d) :
    v = m0GeodesicSideAdjacentVertices hp P k hcontain ∧
      d = m0GeodesicSideAdjacentDarts hp P k hcontain := by
  exact m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique hp (P k) .left hl
    (m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain)

/-- Helper toward Lemma 5.6: intrinsic-ray uniqueness holds on every
marked representative of a realized side, without a rotation-law premise
on that representative. -/
theorem m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique_of_markedIso
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    {N : GeometricSideSubmap} (I : GeometricSideMarkedIso (m0GeodesicSide hp P s) N)
    {v d v' d' : ℕ → GeometricSideCell N}
    (hl : IntrinsicallyLeftmostAdjacentRay N longest v d)
    (hl' : IntrinsicallyLeftmostAdjacentRay N longest v' d') :
    v = v' ∧ d = d' := by
  apply intrinsicallyLeftmostAdjacentRay_unique_of_rotation N longest _ hl hl'
  intro a b c hb hc
  apply I.equiv.symm.injective
  apply m0GeodesicSide_clockwiseStep_unique hp P s (I.equiv.symm a)
  · apply (I.relation_iff _ _ _).2
    simpa only [Equiv.apply_symm_apply] using hb
  · apply (I.relation_iff _ _ _).2
    simpa only [Equiv.apply_symm_apply] using hc

/-- Helper toward Lemma 5.6: the intrinsic ray in any marked
representative is the transported side-coded preceding ambient geodesic.
This identifies darts pointwise, preserving multiedge identity. -/
theorem m0GeodesicSide_intrinsicRay_eq_map_realizedAdjacent
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left) N)
    {v d : ℕ → GeometricSideCell N}
    (hl : IntrinsicallyLeftmostAdjacentRay N longest v d) :
    v = I.equiv ∘ m0GeodesicSideAdjacentVertices hp P k hcontain ∧
      d = I.equiv ∘ m0GeodesicSideAdjacentDarts hp P k hcontain := by
  exact m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique_of_markedIso
    hp (P k) .left I hl
    (intrinsicallyLeftmostAdjacentRay_map I longest
      (m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain))

/-- Helper toward Lemma 5.6: on one simultaneous full-measure event, both
metrics and every cut have a unique intrinsic ray on every representative
of the left-side class. Ambient leftmostness and least coalescence are
retained on the same event. -/
theorem m0GeodesicSide_ae_intrinsicRay_exists_unique :
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
        (∀ j : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) ∧
        (∀ k : ℤ, ∀ N : GeometricSideSubmap,
          geometricSideClass (m0GeodesicSide hp (P k) .left) =
            geometricSideClass N →
          ∃ v d : ℕ → GeometricSideCell N,
            IntrinsicallyLeftmostAdjacentRay N longest v d ∧
            ∀ v' d' : ℕ → GeometricSideCell N,
              IntrinsicallyLeftmostAdjacentRay N longest v' d' →
              v' = v ∧ d' = d) := by
  filter_upwards [m0GeodesicSide_ae_intrinsicRay_exists] with W hW
  obtain ⟨H, h, hLL, hp, hmode⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, hc, hex⟩ := hmode longest
  refine ⟨P, T, hleft, hc, ?_⟩
  intro k N hN
  obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 hN
  obtain ⟨v, d, hl⟩ := hex k N hN
  exact ⟨v, d, hl, fun v' d' hl' =>
    m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique_of_markedIso
      hp (P k) .left I hl' hl⟩

/-- Helper toward Lemma 5.6: the seam-incidence test for an intrinsic ray
is exactly equality of the corresponding ambient geometric edges. Thus its
coalescence comparisons are visible in the complete marked side. -/
theorem m0GeodesicSide_intrinsicRay_seam_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hl : IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest v d) (a b : ℕ) :
    geometricSideRelation (m0GeodesicSide hp (P k) .left) (.seam b) (d a) (d a) ↔
      wholePlaneEdgeι W 0 ((P (k - 1)).codePath.edge a) =
        wholePlaneEdgeι W 0 ((P k).codePath.edge b) := by
  have hd := (m0GeodesicSide_intrinsicRay_eq_realizedAdjacent
    hp P T hleft k hcontain hl).2
  rw [hd]
  change ((P k).codePath.edge b, false) =
    ((P (k - 1)).codePath.edge a, false) ↔ _
  constructor
  · intro he
    exact congrArg (wholePlaneEdgeι W 0) (congrArg Prod.fst he).symm
  · intro he
    exact Prod.ext (wholePlaneEdgeι_injective W 0 he).symm rfl

/-- Helper toward Lemma 5.6: the least coalescence offsets are
characterized entirely by the intrinsic ray and indexed seam relation of
the side. Both coordinates are minimized jointly over aligned tails. -/
theorem m0GeodesicSide_leastCoalescence_iff_intrinsicSeam
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hl : IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest v d) (a b : ℕ) :
    M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b ↔
      (∀ n : ℕ, geometricSideRelation (m0GeodesicSide hp (P k) .left)
        (.seam (b + n)) (d (a + n)) (d (a + n))) ∧
      ∀ a' b' : ℕ,
        (∀ n : ℕ, geometricSideRelation (m0GeodesicSide hp (P k) .left)
          (.seam (b' + n)) (d (a' + n)) (d (a' + n))) →
        a ≤ a' ∧ b ≤ b' := by
  have htail (a' b' : ℕ) :
      M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a' b' ↔
        ∀ n : ℕ, geometricSideRelation (m0GeodesicSide hp (P k) .left)
          (.seam (b' + n)) (d (a' + n)) (d (a' + n)) := by
    exact forall_congr' (fun n =>
      (m0GeodesicSide_intrinsicRay_seam_iff hp P T hleft k hcontain hl
        (a' + n) (b' + n)).symm)
  constructor
  · rintro ⟨hc, hmin⟩
    exact ⟨(htail a b).1 hc, fun a' b' hco => hmin a' b' ((htail a' b').2 hco)⟩
  · rintro ⟨hc, hmin⟩
    exact ⟨(htail a b).2 hc, fun a' b' hco => hmin a' b' ((htail a' b').1 hco)⟩





























































end DirectedDistances.PaperProofs.Section5
