/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceOneSliceReaderFixed

/- Intrinsic characterization of countably coded ray selection. Independent -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: an intrinsically leftmost coded ray passes
 the countable first-admissible scan on any numbered side. -/
theorem geoSliceSeamRayFirst_of_intrinsic
    {longest : Bool} {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p)
    (hl : IntrinsicallyLeftmostAdjacentRay M longest
      (geoSliceSeamRayVertexCells hc) (geoSliceSeamRayDartCells hc)) :
    geoSliceSeamRayFirst longest M p := by
  refine ⟨hc, ?_⟩
  intro i
  obtain ⟨c, f, n, hcorner, hf, hend, hfirst⟩ := hl.2 i
  have hcd : ∃ d, c = .inr d := by
    cases i with
    | zero => cases c with
      | inl v => exact False.elim hcorner
      | inr d => exact ⟨d, rfl⟩
    | succ i => cases c with
      | inl v => exact False.elim hcorner
      | inr d => exact ⟨d, rfl⟩
  obtain ⟨c, rfl⟩ := hcd
  let g (j : Fin (n + 1)) := geoSliceCellDartValue (f j)
  have hfg (j : Fin (n + 1)) : ∃ d,
      f j = .inr d ∧ g j = d.val := by
    obtain ⟨d, hd⟩ := geometricSideClockwiseScan_isDart hf j (by omega)
    exact ⟨d, hd, by simp only [g, hd, geoSliceCellDartValue]⟩
  refine ⟨n, g, ?_, ?_, ?_, ?_, ?_⟩
  · change geoSliceCellDartValue (f 0) = geoSliceSeamRayIncoming M p i
    rw [hf.1]
    change c.val = geoSliceSeamRayIncoming M p i
    cases i with
    | zero => exact hcorner.symm
    | succ i => exact hcorner.symm
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
    rw [hend]
    rfl
  · intro q hq hpref j hj hgj
    have hprefix : ∀ t, t < i → geoSliceSeamRayDartCells hq t =
        geoSliceSeamRayDartCells hc t := by
      intro t ht
      apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun e : ℕ => (e, false)) (hpref t ht)
    apply hfirst (geoSliceSeamRayVertexCells hq) (geoSliceSeamRayDartCells hq)
      (geoSliceSeamRayCandidate_intrinsic hq) hprefix j hj
    obtain ⟨d, hd, hgd⟩ := hfg j
    rw [hd]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact hgd.symm.trans hgj

/-- Helper toward Lemma 5.6: with unique rotation predecessors, the
selected code reads the edges of every intrinsically leftmost coded ray. -/
theorem geoSliceOneSideRayCodeOption_edges_of_intrinsic
    {longest : Bool} {M : GeometricSideSubmap}
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    {p : GeoSliceSeamRayCode} (hc : geoSliceSeamRayCandidate longest M p)
    (hl : IntrinsicallyLeftmostAdjacentRay M longest
      (geoSliceSeamRayVertexCells hc) (geoSliceSeamRayDartCells hc)) :
    ∃ q, geoSliceOneSideRayCodeOption longest M = some q ∧
      geoSliceSeamRayFirst longest M q ∧
      ∀ i, geoSliceSeamRayEdge M q i = geoSliceSeamRayEdge M p i := by
  have hp := geoSliceSeamRayFirst_of_intrinsic hc hl
  obtain ⟨q, hq, hqfirst⟩ := geoSliceOneSideRayCodeOption_spec longest M ⟨p, hp⟩
  exact ⟨q, hq, hqfirst, geoSliceSeamRayFirst_edges_unique longest M hrot hqfirst hp⟩


/-- Helper toward Lemma 5.6: equality of decoded edge sequences gives
 equality of the complete intrinsic vertex and dart sequences. -/
theorem geoSliceSeamRayCells_eq_of_edges_eq
    {longest : Bool} {M : GeometricSideSubmap} {p q : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayCandidate longest M p)
    (hq : geoSliceSeamRayCandidate longest M q)
    (he : ∀ i, geoSliceSeamRayEdge M p i = geoSliceSeamRayEdge M q i) :
    geoSliceSeamRayVertexCells hp = geoSliceSeamRayVertexCells hq ∧
      geoSliceSeamRayDartCells hp = geoSliceSeamRayDartCells hq := by
  constructor
  · funext i
    apply congrArg Sum.inl
    apply Subtype.ext
    exact congrArg M.west (he i)
  · funext i
    apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg (fun e : ℕ => (e, false)) (he i)

/-- Helper toward Lemma 5.6: under functional clockwise rotation, the
reader recovers the complete intrinsically leftmost coded ray. -/
theorem geoSliceOneSideReaders_intrinsic_ray
    {longest : Bool} {M : GeometricSideSubmap}
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    {p : GeoSliceSeamRayCode} (hc : geoSliceSeamRayCandidate longest M p)
    (hl : IntrinsicallyLeftmostAdjacentRay M longest
      (geoSliceSeamRayVertexCells hc) (geoSliceSeamRayDartCells hc)) :
    ∃ q, ∃ hq : geoSliceSeamRayCandidate longest M q,
      geoSliceOneSideRayCodeOption longest M = some q ∧
      geoSliceSeamRayVertexCells hq = geoSliceSeamRayVertexCells hc ∧
      geoSliceSeamRayDartCells hq = geoSliceSeamRayDartCells hc ∧
      IntrinsicallyLeftmostAdjacentRay M longest
        (geoSliceSeamRayVertexCells hq) (geoSliceSeamRayDartCells hq) := by
  obtain ⟨q, hr, hfirst, he⟩ :=
    geoSliceOneSideRayCodeOption_edges_of_intrinsic hrot hc hl
  obtain ⟨hv, hd⟩ := geoSliceSeamRayCells_eq_of_edges_eq hfirst.1 hc he
  refine ⟨q, hfirst.1, hr, hv, hd, ?_⟩
  rw [hv, hd]
  exact hl

/-- Helper toward Lemma 5.6: every directed intrinsic ray has unique raw
forward dart and vertex coordinates; no geometric edge is identified with
another edge having the same endpoints. -/
theorem geometricSideDirectedRay_raw_coordinates
    {M : GeometricSideSubmap} {v d : ℕ → GeometricSideCell M}
    (hr : geometricSideDirectedRay M v d) :
    ∀ i, ∃ e : ℕ, ∃ he : e ∈ M.edges,
      e ∈ M.present ∧ ∃ hv : M.west e ∈ M.vertices,
        d i = .inr ⟨(e, false), he⟩ ∧ v i = .inl ⟨M.west e, hv⟩ := by
  intro i
  obtain ⟨ho, hi, _⟩ := hr i
  cases hdi : d i with
  | inl w => rw [hdi] at ho; exact False.elim ho
  | inr e =>
    rw [hdi] at ho hi
    have hbit : e.val.2 = false := ho.2
    cases hvi : v i with
    | inr f => rw [hvi] at hi; exact False.elim hi
    | inl w =>
      rw [hvi] at hi
      change (if e.val.2 then M.east e.val.1 else M.west e.val.1) = w.val at hi
      rw [hbit] at hi
      change M.west e.val.1 = w.val at hi
      have hv : M.west e.val.1 ∈ M.vertices := hi ▸ w.property
      refine ⟨e.val.1, e.property, ho.1, hv, ?_, ?_⟩
      · apply congrArg Sum.inr
        exact Subtype.ext (Prod.ext rfl hbit)
      · exact congrArg Sum.inl (Subtype.ext hi.symm)


/-- Helper toward Lemma 5.6: a seam-coalescing intrinsic adjacent metric
ray has a finite-prefix code with exactly its original vertices and darts. -/
theorem geometricSideAdjacentGeodesicCandidate_exists_code
    {M : GeometricSideSubmap} {longest : Bool}
    {v d : ℕ → GeometricSideCell M}
    (hc : geometricSideAdjacentGeodesicCandidate M longest v d)
    {a b : ℕ} (hab : geometricSideRaySeamAgreement M d a b) :
    ∃ p, ∃ hp : geoSliceSeamRayCandidate longest M p,
      geoSliceSeamRayVertexCells hp = v ∧ geoSliceSeamRayDartCells hp = d := by
  choose e he hp hv hd hvi using geometricSideDirectedRay_raw_coordinates hc.1
  let p : GeoSliceSeamRayCode := (List.ofFn (fun j : Fin a => e j), b)
  have htail (n : ℕ) : (M.seam (b + n)).1 = e (a + n) := by
    have ht := hab n
    rw [hd (a + n)] at ht
    exact congrArg Prod.fst ht
  have hdecode (i : ℕ) : geoSliceSeamRayEdge M p i = e i := by
    by_cases hi : i < a
    · simp only [geoSliceSeamRayEdge, p, List.length_ofFn, hi, dite_eq_left,
        List.getElem_ofFn]
    · simp only [geoSliceSeamRayEdge, p, List.length_ofFn]
      rw [dite_eq_right hi]
      rw [htail, Nat.add_sub_of_le (Nat.le_of_not_gt hi)]
  have hcan : geoSliceSeamRayCandidate longest M p := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [hdecode]
      refine ⟨he i, hp i, hv i, ?_⟩
      obtain ⟨_, _, c, hopp, hinc⟩ := hc.1 i
      rw [hd i] at hopp
      have hce : c = .inr ⟨(e i, true), he i⟩ :=
        geometricSideRelation_opposite_right_unique M hopp rfl
      rw [hce, hvi (i + 1)] at hinc
      exact hinc
    · obtain ⟨c, hboundary, hinc⟩ := hc.2.1
      cases c with
      | inl c => exact False.elim hboundary
      | inr c =>
        change M.boundary 1 = c.val at hboundary
        refine ⟨hboundary.symm ▸ c.property, ?_⟩
        rw [hdecode, hboundary]
        rw [hvi 0] at hinc
        exact hinc
    · intro i n m hm
      simp only [hdecode] at hm
      apply (hc.2.2 i n).2 m
      rw [hvi i, hvi (i + n)]
      exact (geoSliceRawWalk_iff M m ⟨e i |> M.west, hv i⟩
        ⟨e (i + n) |> M.west, hv (i + n)⟩).1 hm
  refine ⟨p, hcan, ?_, ?_⟩
  · funext i
    rw [hvi i]
    apply congrArg Sum.inl
    apply Subtype.ext
    exact congrArg M.west (hdecode i)
  · funext i
    rw [hd i]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg (fun e : ℕ => (e, false)) (hdecode i)


/-- Helper toward Lemma 5.6: on any side with functional clockwise
rotation, every seam-coalescing intrinsic ray is exactly the ray read by
the fixed single-side selector, including its vertex and dart coordinates. -/
theorem geoSliceOneSideReaders_eq_intrinsic_of_coalescence
    {M : GeometricSideSubmap} {longest : Bool}
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    {v d : ℕ → GeometricSideCell M}
    (hl : IntrinsicallyLeftmostAdjacentRay M longest v d)
    {a b : ℕ} (hab : geometricSideRaySeamAgreement M d a b) :
    ∃ q, ∃ hq : geoSliceSeamRayCandidate longest M q,
      geoSliceOneSideRayCodeOption longest M = some q ∧
      geoSliceSeamRayVertexCells hq = v ∧ geoSliceSeamRayDartCells hq = d := by
  obtain ⟨p, hp, hv, hd⟩ :=
    geometricSideAdjacentGeodesicCandidate_exists_code hl.1 hab
  have hlp : IntrinsicallyLeftmostAdjacentRay M longest
      (geoSliceSeamRayVertexCells hp) (geoSliceSeamRayDartCells hp) := by
    rw [hv, hd]
    exact hl
  obtain ⟨q, hq, hr, hvq, hdq, _⟩ := geoSliceOneSideReaders_intrinsic_ray hrot hp hlp
  exact ⟨q, hq, hr, hvq.trans hv, hdq.trans hd⟩

/-- Helper toward Lemma 5.6: for a forward indexed seam, the raw edge
tail test is precisely the intrinsic full-dart seam-agreement predicate. -/
theorem geoSliceSeamRay_raw_tail_iff_intrinsic
    {M : GeometricSideSubmap} {longest : Bool}
    (hseam : ∀ i, (M.seam i).2 = false)
    {p : GeoSliceSeamRayCode} (hp : geoSliceSeamRayCandidate longest M p)
    (a b : ℕ) :
    geoSliceSidePairTailsCoalesce ((geoSliceSeamRayMarkedSide p M, M), id) a b ↔
      geometricSideRaySeamAgreement M (geoSliceSeamRayDartCells hp) a b := by
  constructor
  · intro ht n
    exact Prod.ext (ht n).symm (hseam (b + n))
  · intro ht n
    exact (congrArg Prod.fst (ht n)).symm

/-- Helper toward Lemma 5.6: the optional offset reader on a forward
seam returns exactly the jointly least intrinsic seam-coalescence pair. -/
theorem geoSliceSeamRayOffsets_eq_some_iff_intrinsic
    {M : GeometricSideSubmap} {longest : Bool}
    (hseam : ∀ i, (M.seam i).2 = false)
    {p : GeoSliceSeamRayCode} (hp : geoSliceSeamRayCandidate longest M p)
    (a b : ℕ) :
    geoSliceSeamRayOffsets p M = some (a, b) ↔
      geometricSideRaySeamAgreement M (geoSliceSeamRayDartCells hp) a b ∧
      ∀ a' b', geometricSideRaySeamAgreement M
        (geoSliceSeamRayDartCells hp) a' b' → a ≤ a' ∧ b ≤ b' := by
  rw [geoSliceSeamRayOffsets, geoSliceSidePairOffsets_eq_some_iff]
  constructor
  · rintro ⟨ht, hleast⟩
    exact ⟨(geoSliceSeamRay_raw_tail_iff_intrinsic hseam hp a b).1 ht,
      fun i j hij => hleast i j
        ((geoSliceSeamRay_raw_tail_iff_intrinsic hseam hp i j).2 hij)⟩
  · rintro ⟨ht, hleast⟩
    exact ⟨(geoSliceSeamRay_raw_tail_iff_intrinsic hseam hp a b).2 ht,
      fun i j hij => hleast i j
        ((geoSliceSeamRay_raw_tail_iff_intrinsic hseam hp i j).1 hij)⟩

/-- Helper toward Lemma 5.6: the single-side readers recover both a
seam-coalescing intrinsic ray and its same jointly least offsets. -/
theorem geoSliceOneSideReaders_eq_intrinsic_least
    {M : GeometricSideSubmap} {longest : Bool}
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    (hseam : ∀ i, (M.seam i).2 = false)
    {v d : ℕ → GeometricSideCell M}
    (hl : IntrinsicallyLeftmostAdjacentRay M longest v d)
    {a b : ℕ} (hab : geometricSideRaySeamAgreement M d a b)
    (hmin : ∀ a' b', geometricSideRaySeamAgreement M d a' b' → a ≤ a' ∧ b ≤ b') :
    ∃ q, ∃ hq : geoSliceSeamRayCandidate longest M q,
      geoSliceOneSideRayCodeOption longest M = some q ∧
      geoSliceSeamRayVertexCells hq = v ∧ geoSliceSeamRayDartCells hq = d ∧
      geoSliceOneSideOffsetsOption longest M = some (a, b) := by
  obtain ⟨q, hq, hr, hv, hd⟩ :=
    geoSliceOneSideReaders_eq_intrinsic_of_coalescence hrot hl hab
  refine ⟨q, hq, hr, hv, hd, ?_⟩
  simp only [geoSliceOneSideOffsetsOption, hr, Option.bind_some]
  apply (geoSliceSeamRayOffsets_eq_some_iff_intrinsic hseam hq a b).2
  rw [hd]
  exact ⟨hab, hmin⟩


/-- Helper toward Lemma 5.6: unique clockwise rotation transports to
any numbered representative of an actual geodesic side. -/
theorem m0GeodesicSide_rawRotation_unique_of_markedIso
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (side : ThinMapSide)
    {N : GeometricSideSubmap} (I : GeometricSideMarkedIso (m0GeodesicSide hp P side) N) :
    ∀ a b c : ℕ × Bool,
      a.1 ∈ N.edges → b.1 ∈ N.edges → c.1 ∈ N.edges →
      N.rotation b a → N.rotation c a → b = c := by
  intro a b c ha hb hc hba hca
  have he : (Sum.inr ⟨b, hb⟩ : GeometricSideCell N) = .inr ⟨c, hc⟩ := by
    apply I.equiv.symm.injective
    apply m0GeodesicSide_clockwiseStep_unique hp P side (I.equiv.symm (.inr ⟨a, ha⟩))
    · apply (I.relation_iff .rotation _ _).2
      simpa only [Equiv.apply_symm_apply, geometricSideRelation] using hba
    · apply (I.relation_iff .rotation _ _).2
      simpa only [Equiv.apply_symm_apply, geometricSideRelation] using hca
  exact congrArg Subtype.val (Sum.inr.inj he)

/-- Helper toward Lemma 5.6: every indexed seam on a numbered
representative of an actual side retains its forward orientation. -/
theorem m0GeodesicSide_seam_forward_of_markedIso
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (side : ThinMapSide)
    {N : GeometricSideSubmap} (I : GeometricSideMarkedIso (m0GeodesicSide hp P side) N) :
    ∀ i, (N.seam i).2 = false := by
  intro i
  let c := m0GeodesicSideSeamDartCell hp P side i
  have hm : geometricSideRelation N (.seam i) (I.equiv c) (I.equiv c) :=
    (I.relation_iff (.seam i) c c).1 rfl
  have ho : geometricSideRelation N .oriented (I.equiv c) (I.equiv c) :=
    (I.relation_iff .oriented c c).1 (m0GeodesicSide_seam_directedRay hp P side i).1
  cases he : I.equiv c with
  | inl v => rw [he] at hm; exact False.elim hm
  | inr d =>
    rw [he] at hm ho
    exact (congrArg Prod.snd hm).trans ho.2

/-- Helper toward Lemma 5.6: on every marked representative of an actual
left side, the fixed readers recover the transported intrinsic ray and
the original jointly least offsets, without a reader-agreement premise. -/
theorem M0CutGeodesicSliceWitness.oneSideReaders_eq_of_markedIso
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide s.hp (s.P k) .left) N) :
    ∃ q, ∃ hq : geoSliceSeamRayCandidate (if x = XDP.ldp then true else false) N q,
      geoSliceOneSideRayCodeOption (if x = XDP.ldp then true else false) N = some q ∧
      geoSliceSeamRayVertexCells hq = I.equiv ∘
        m0GeodesicSideAdjacentVertices s.hp s.P k (s.left_adjacent_containment k) ∧
      geoSliceSeamRayDartCells hq = I.equiv ∘
        m0GeodesicSideAdjacentDarts s.hp s.P k (s.left_adjacent_containment k) ∧
      geoSliceOneSideOffsetsOption (if x = XDP.ldp then true else false) N =
        some (s.thetaMinus k, s.theta k) := by
  have hl := m0GeodesicSide_realizedAdjacent_is_intrinsic
    s.hp s.P s.T s.hleft k (s.left_adjacent_containment k)
  obtain ⟨ht, hmin⟩ := (m0GeodesicSide_leastCoalescence_iff_intrinsicSeam
    s.hp s.P s.T s.hleft k (s.left_adjacent_containment k) hl
    (s.thetaMinus k) (s.theta k)).1 (s.least k)
  apply geoSliceOneSideReaders_eq_intrinsic_least
    (m0GeodesicSide_rawRotation_unique_of_markedIso s.hp (s.P k) .left I)
    (m0GeodesicSide_seam_forward_of_markedIso s.hp (s.P k) .left I)
    (intrinsicallyLeftmostAdjacentRay_map I _ hl)
    ((geometricSideRaySeamAgreement_iff I _ _ _).1 ht)
  intro a b hab
  exact hmin a b ((geometricSideRaySeamAgreement_iff I _ _ _).2 hab)


/-- Helper toward Lemma 5.6: the intrinsic indexed seam has precisely
its raw forward darts and initial vertices whenever its marks are forward. -/
theorem leftReconstructionSeam_forward_coordinates
    {M : GeometricSideSubmap} {vs ds : ℕ → GeometricSideCell M}
    (hs : leftReconstructionSeam M vs ds)
    (hforward : ∀ i, (M.seam i).2 = false) :
    ∀ i, ∃ he : (M.seam i).1 ∈ M.edges,
      ∃ hv : M.west (M.seam i).1 ∈ M.vertices,
        ds i = .inr ⟨((M.seam i).1, false), he⟩ ∧
        vs i = .inl ⟨M.west (M.seam i).1, hv⟩ := by
  intro i
  obtain ⟨hm, hi⟩ := hs i
  cases hd : ds i with
  | inl w => rw [hd] at hm; exact False.elim hm
  | inr d =>
    rw [hd] at hm hi
    change M.seam i = d.val at hm
    have hbit : d.val.2 = false := (congrArg Prod.snd hm).symm.trans (hforward i)
    cases hv : vs i with
    | inr c => rw [hv] at hi; exact False.elim hi
    | inl v =>
      rw [hv] at hi
      change (if d.val.2 then M.east d.val.1 else M.west d.val.1) = v.val at hi
      rw [hbit] at hi
      change M.west d.val.1 = v.val at hi
      have hed : (M.seam i).1 = d.val.1 := congrArg Prod.fst hm
      have hmem : (M.seam i).1 ∈ M.edges := hed.symm ▸ d.property
      have hvmem : M.west (M.seam i).1 ∈ M.vertices := by
        rw [hed, hi]
        exact v.property
      refine ⟨hmem, hvmem, ?_, ?_⟩
      · apply congrArg Sum.inr
        exact Subtype.ext (Prod.ext hed.symm hbit)
      · apply congrArg Sum.inl
        exact Subtype.ext (hi.symm.trans (congrArg M.west hed.symm))

/-- Helper toward Lemma 5.6: any realizable enclosed intrinsic
restriction is closed under reversing an individual retained dart. -/
theorem leftRestrictionRealizes_enclosed_opposite_closed
    {M G : GeometricSideSubmap} (v d : ℕ → GeometricSideCell M)
    (S : Set (GeometricSideCell M))
    (hr : leftRestrictionRealizes M S (geometricSide_enclosed_relation M v d S) G)
    (c : {d : ℕ × Bool // d.1 ∈ M.edges}) (hc : Sum.inr c ∈ S) :
    (Sum.inr ⟨(c.val.1, !c.val.2), c.property⟩ : GeometricSideCell M) ∈ S := by
  obtain ⟨E, hE⟩ := hr
  let a := E.symm ⟨.inr c, hc⟩
  have ha : (E a).val = .inr c := congrArg Subtype.val (E.apply_symm_apply _)
  cases he : a with
  | inl u =>
    have hfalse := (hE .vertex a a).1 (by rw [he]; trivial)
    change geometricSideRelation M .vertex (E a).val (E a).val at hfalse
    rw [ha] at hfalse
    exact False.elim hfalse
  | inr q =>
    let b : GeometricSideCell G := .inr ⟨(q.val.1, !q.val.2), q.property⟩
    have hop : geometricSideRelation G .opposite a b := by rw [he]; rfl
    have hop' := (hE .opposite a b).1 hop
    change geometricSideRelation M .opposite (E a).val (E b).val at hop'
    rw [ha] at hop'
    have hb : (E b).val = .inr ⟨(c.val.1, !c.val.2), c.property⟩ :=
      geometricSideRelation_opposite_right_unique M hop' rfl
    exact hb ▸ (E b).property


/-- Helper toward Lemma 5.6: intrinsic slice membership on a forward
indexed seam has the exact raw strict-vertex and weak-edge tail tests. -/
theorem geoSliceFixed_intrinsic_keep_iff
    {M : GeometricSideSubmap} {longest : Bool} {p : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayCandidate longest M p)
    {vs ds : ℕ → GeometricSideCell M} (hs : leftReconstructionSeam M vs ds)
    (hforward : ∀ i, (M.seam i).2 = false) (a b : ℕ) (c : GeometricSideCell M) :
    c ∈ leftSliceKeep M (geoSliceSeamRayVertexCells hp)
      (geoSliceSeamRayDartCells hp) vs ds a b ↔
      match c with
      | .inl v => geoSliceFixedVertexKept M p a b v.val
      | .inr d => geoSliceIntrinsicRightRaw M p (.inr d.val) ∧
          (¬ ∃ i, a ≤ i ∧ d.val.1 = geoSliceSeamRayEdge M p i) ∧
          (¬ ∃ i, b ≤ i ∧ d.val.1 = (M.seam i).1) := by
  choose he hv hds hvs using leftReconstructionSeam_forward_coordinates hs hforward
  have hdse : ds = fun i => .inr ⟨((M.seam i).1, false), he i⟩ := funext hds
  have hvse : vs = fun i => .inl ⟨M.west (M.seam i).1, hv i⟩ := funext hvs
  have hray := geometricSideRayDeletedTailCells_mem_iff M
    (fun i => ⟨M.west (geoSliceSeamRayEdge M p i), (hp.1 i).2.2.1⟩)
    (geoSliceSeamRayEdge M p) (fun i => (hp.1 i).1) a c
  change c ∈ geometricSideRayDeletedTailCells M (geoSliceSeamRayVertexCells hp)
    (geoSliceSeamRayDartCells hp) a ↔ _ at hray
  have hseam := geometricSideRayDeletedTailCells_mem_iff M
    (fun i => ⟨M.west (M.seam i).1, hv i⟩) (fun i => (M.seam i).1) he b c
  change (geometricSide_intrinsic_right M _ _ c ∧ ¬ (_ ∨ _)) ↔ _
  rw [hvse, hdse, hray, hseam, not_or]
  cases c with
  | inl v =>
    dsimp only
    have hi (i : ℕ) : geometricSideDartInitial M (M.seam i) = M.west (M.seam i).1 := by
      change (if (M.seam i).2 then M.east (M.seam i).1 else M.west (M.seam i).1) = _
      rw [hforward i]
      rfl
    simp only [geoSliceFixedVertexKept, hi]
    have hright := geoSliceFixed_rawRight_iff hp (.inl v.val) v.property
    change (_ ∧ _ ∧ _) ↔ (v.val ∈ M.vertices ∧ _ ∧ _ ∧ _)
    exact ⟨fun h => ⟨v.property, hright.mpr h.1, h.2⟩,
      fun h => ⟨hright.mp h.2.1, h.2.2⟩⟩
  | inr d =>
    dsimp only
    have hright := geoSliceFixed_rawRight_iff hp (.inr d.val) d.property
    have htail (q : ℕ → ℕ) (a : ℕ) :
        d.val.1 ∈ Set.range (fun n => q (a + n)) ↔
          ∃ i, a ≤ i ∧ d.val.1 = q i := by
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨a + n, Nat.le_add_right a n, hn.symm⟩
      · rintro ⟨i, hi, heq⟩
        exact ⟨i - a, by change q (a + (i - a)) = d.val.1; rw [Nat.add_sub_of_le hi]; exact heq.symm⟩
    rw [htail (geoSliceSeamRayEdge M p) a, htail (fun i => (M.seam i).1) b]
    exact and_congr hright.symm Iff.rfl

/-- Helper toward Lemma 5.6: when the full intrinsic restriction is
realizable, its retained darts are exactly the fixed reader's geometric
edge carrier, for either orientation of each edge. -/
theorem geoSliceFixedEdgeKept_iff_intrinsic_keep
    {M G : GeometricSideSubmap} {longest : Bool} {p : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayCandidate longest M p)
    {vs ds : ℕ → GeometricSideCell M} (hs : leftReconstructionSeam M vs ds)
    (hforward : ∀ i, (M.seam i).2 = false) (a b : ℕ)
    (hr : leftRestrictionRealizes M
      (leftSliceKeep M (geoSliceSeamRayVertexCells hp) (geoSliceSeamRayDartCells hp) vs ds a b)
      (geometricSide_enclosed_relation M (geoSliceSeamRayVertexCells hp)
        (geoSliceSeamRayDartCells hp)
        (leftSliceKeep M (geoSliceSeamRayVertexCells hp)
          (geoSliceSeamRayDartCells hp) vs ds a b)) G)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
    geoSliceFixedEdgeKept M p a b d.val.1 ↔
      Sum.inr d ∈ leftSliceKeep M (geoSliceSeamRayVertexCells hp)
        (geoSliceSeamRayDartCells hp) vs ds a b := by
  constructor
  · rintro ⟨_, hf, ht, ha, hb⟩
    apply (geoSliceFixed_intrinsic_keep_iff hp hs hforward a b (.inr d)).2
    refine ⟨?_, ha, hb⟩
    change geoSliceIntrinsicRightRaw M p (.inr (d.val.1, d.val.2))
    cases hbit : d.val.2 with
    | false => exact hf
    | true => exact ht
  · intro hd
    have ho := leftRestrictionRealizes_enclosed_opposite_closed _ _ _ hr d hd
    have hD := (geoSliceFixed_intrinsic_keep_iff hp hs hforward a b (.inr d)).1 hd
    have hO := (geoSliceFixed_intrinsic_keep_iff hp hs hforward a b
      (.inr ⟨(d.val.1, !d.val.2), d.property⟩)).1 ho
    have hdright : geoSliceIntrinsicRightRaw M p (.inr (d.val.1, d.val.2)) := hD.1
    refine ⟨d.property, ?_, ?_, hD.2⟩
    · cases hbit : d.val.2 with
      | false => simpa only [hbit] using hdright
      | true => simpa only [hbit, Bool.not_true] using hO.1
    · cases hbit : d.val.2 with
      | false => simpa only [hbit, Bool.not_false] using hO.1
      | true => simpa only [hbit] using hdright


/-- Helper toward Lemma 5.6: whenever an enclosed intrinsic restriction
has a complete realization, the corrected raw core realizes that same
restriction, including induced rotation and oriented face succession. -/
theorem geoSliceFixedCore_realizes_of_realizable
    {M G : GeometricSideSubmap} {longest : Bool} {p : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayCandidate longest M p)
    {vs ds : ℕ → GeometricSideCell M} (hs : leftReconstructionSeam M vs ds)
    (hforward : ∀ i, (M.seam i).2 = false) (a b : ℕ)
    (hr : leftRestrictionRealizes M
      (leftSliceKeep M (geoSliceSeamRayVertexCells hp) (geoSliceSeamRayDartCells hp) vs ds a b)
      (geometricSide_enclosed_relation M (geoSliceSeamRayVertexCells hp)
        (geoSliceSeamRayDartCells hp)
        (leftSliceKeep M (geoSliceSeamRayVertexCells hp)
          (geoSliceSeamRayDartCells hp) vs ds a b)) G) :
    leftRestrictionRealizes M
      (leftSliceKeep M (geoSliceSeamRayVertexCells hp) (geoSliceSeamRayDartCells hp) vs ds a b)
      (geometricSide_enclosed_relation M (geoSliceSeamRayVertexCells hp)
        (geoSliceSeamRayDartCells hp)
        (leftSliceKeep M (geoSliceSeamRayVertexCells hp)
          (geoSliceSeamRayDartCells hp) vs ds a b)) (geoSliceFixedCore M p a b) := by
  let N := geoSliceFixedCore M p a b
  let S := leftSliceKeep M (geoSliceSeamRayVertexCells hp)
    (geoSliceSeamRayDartCells hp) vs ds a b
  let f : GeometricSideCell N → GeometricSideCell M
    | .inl v => .inl ⟨v.val, v.property.1⟩
    | .inr d => .inr ⟨d.val, d.property.1⟩
  have hS (c : GeometricSideCell M) :
      c ∈ S ↔ geoSliceCellToRawCell c ∈ geoSliceFixedRawKept M p a b := by
    cases c with
    | inl v => exact geoSliceFixed_intrinsic_keep_iff hp hs hforward a b (.inl v)
    | inr d => exact (geoSliceFixedEdgeKept_iff_intrinsic_keep hp hs hforward a b hr d).symm
  apply leftRestrictionRealizes_of_inclusion _ _ f
  · intro c e hce
    cases c <;> cases e <;> simp_all only [f, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Subtype.ext_iff]
  · ext c
    constructor
    · rintro ⟨e, rfl⟩
      apply (hS (f e)).2
      cases e with
      | inl v => exact v.property
      | inr d => exact d.property
    · intro hc
      have hk := (hS c).1 hc
      cases c with
      | inl v => exact ⟨.inl ⟨v.val, hk⟩, rfl⟩
      | inr d => exact ⟨.inr ⟨d.val, hk⟩, rfl⟩
  · intro t c e
    cases t with
    | rotation =>
      cases c with
      | inl c =>
        cases e <;> refine ⟨False.elim, ?_⟩ <;> intro hh <;>
          obtain ⟨z, hz⟩ := enclosedSliceRotationChain_first hh <;> cases z <;> exact hz.elim
      | inr c => cases e with
        | inl e =>
          refine ⟨False.elim, ?_⟩
          intro hh
          obtain ⟨z, hz⟩ := enclosedSliceRotationChain_last hh
          cases z <;> exact hz.elim
        | inr e =>
          have hcM : c.val.1 ∈ M.edges := c.property.1
          have heM : e.val.1 ∈ M.edges := e.property.1
          have hchain := geoSliceFixed_rotation_chain_iff M p a b S hS
            ⟨c.val, hcM⟩ ⟨e.val, heM⟩
          change (_ ∧ _) ↔ EnclosedSliceRotationChain _ S _ _
          exact ⟨fun h => hchain.mpr h.2, fun h => ⟨e.property, hchain.mp h⟩⟩
    | faceNext =>
      cases c with
      | inl c => cases e <;> exact ⟨False.elim, fun h => h.1.elim⟩
      | inr c => cases e with
        | inl e => exact ⟨False.elim, fun h => h.1.elim⟩
        | inr e =>
          have hright := geoSliceFixed_rawRight_iff hp (.inr c.val) c.property.1
          change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
          constructor
          · rintro ⟨hf, _, _, hR, hn⟩
            refine ⟨hf, hright.mp hR, ?_⟩
            intro i hi
            exact hn i (congrArg Subtype.val (Sum.inr.inj hi))
          · rintro ⟨hf, hR, hn⟩
            refine ⟨hf, c.property, e.property, hright.mpr hR, ?_⟩
            intro i hi
            exact hn i (congrArg Sum.inr (Subtype.ext hi))
    | root =>
      cases c with
      | inl c => cases e <;> change (c.val = M.west (geoSliceSeamRayEdge M p 0)) ↔
          ((Sum.inl ⟨c.val, c.property.1⟩ : GeometricSideCell M) = geoSliceSeamRayVertexCells hp 0) <;>
          simp only [geoSliceSeamRayVertexCells, Sum.inl.injEq, Subtype.ext_iff]
      | inr c => cases e <;> exact ⟨False.elim, fun h => (Sum.inr_ne_inl h).elim⟩
    | boundary i =>
      cases c with
      | inl c => cases e <;> exact ⟨False.elim, fun h => (Sum.inl_ne_inr h).elim⟩
      | inr c => cases e <;> change ((geoSliceSeamRayEdge M p i, false) = c.val) ↔
          ((Sum.inr ⟨c.val, c.property.1⟩ : GeometricSideCell M) = geoSliceSeamRayDartCells hp i) <;>
          simp only [geoSliceSeamRayDartCells, Sum.inr.injEq, Subtype.ext_iff, eq_comm]
    | vertex => cases c <;> cases e <;> rfl
    | incident => cases c <;> cases e <;> rfl
    | opposite => cases c <;> cases e <;> rfl
    | oriented => cases c <;> cases e <;> rfl
    | target => cases c <;> cases e <;> rfl
    | seam i => cases c <;> cases e <;> rfl

/-- Helper toward Lemma 5.6: the complete corrected core has the same
marked class as every realization of its intrinsic enclosed restriction. -/
theorem geoSliceFixedCore_class_eq_of_realizable
    {M G : GeometricSideSubmap} {longest : Bool} {p : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayCandidate longest M p)
    {vs ds : ℕ → GeometricSideCell M} (hs : leftReconstructionSeam M vs ds)
    (hforward : ∀ i, (M.seam i).2 = false) (a b : ℕ)
    (hr : leftRestrictionRealizes M
      (leftSliceKeep M (geoSliceSeamRayVertexCells hp) (geoSliceSeamRayDartCells hp) vs ds a b)
      (geometricSide_enclosed_relation M (geoSliceSeamRayVertexCells hp)
        (geoSliceSeamRayDartCells hp)
        (leftSliceKeep M (geoSliceSeamRayVertexCells hp)
          (geoSliceSeamRayDartCells hp) vs ds a b)) G) :
    geometricSideClass (geoSliceFixedCore M p a b) = geometricSideClass G := by
  exact leftRestrictionRealizes_class_unique
    (geoSliceFixedCore_realizes_of_realizable hp hs hforward a b hr) hr


/-- Helper toward Lemma 5.6: on the realizable intrinsic slice domain,
functional rotation and forward seam marks suffice for general agreement
of the fixed measurable reader with the intrinsic class reader. -/
theorem oneSliceReaderFixed_class_eq_of_leftSliceRealizes
    {longest : Bool} {M G : GeometricSideSubmap}
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    (hforward : ∀ i, (M.seam i).2 = false)
    (hreal : leftSliceRealizes longest M G) :
    (oneSliceReaderFixed longest M).map geometricSideClass = leftOneSlice longest M := by
  have hclass := leftOneSlice_eq_of_realizes hreal
  obtain ⟨v, d, vs, ds, a, b, hl, hs, ht, hmin, hr⟩ := hreal
  obtain ⟨q, hq, hread, hv, hd, hoff⟩ :=
    geoSliceOneSideReaders_eq_intrinsic_least hrot hforward hl.1 ht hmin
  rw [← hv, ← hd] at hr
  rw [oneSliceReaderFixed_eq_some_core hread hoff, Option.map_some, hclass]
  exact congrArg some (geoSliceFixedCore_class_eq_of_realizable hq hs hforward a b hr)

/-- Helper toward Lemma 5.6: the fixed measurable reader agrees with
the intrinsic reader on every marked representative of an actual left side. -/
theorem M0CutGeodesicSliceWitness.oneSliceReaderFixed_class_eq_of_markedIso
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide s.hp (s.P k) .left) N) :
    (oneSliceReaderFixed (if x = XDP.ldp then true else false) N).map geometricSideClass =
      leftOneSlice (if x = XDP.ldp then true else false) N := by
  exact oneSliceReaderFixed_class_eq_of_leftSliceRealizes
    (m0GeodesicSide_rawRotation_unique_of_markedIso s.hp (s.P k) .left I)
    (m0GeodesicSide_seam_forward_of_markedIso s.hp (s.P k) .left I)
    (leftSliceRealizes_map I _ (s.left_sliceRealizes k))

/-- Helper toward Lemma 5.6: the fixed reader's class is invariant under
renumbering an actual left side, without any selected-ray preservation premise. -/
theorem M0CutGeodesicSliceWitness.oneSliceReaderFixed_class_markedIso
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide s.hp (s.P k) .left) N) :
    (oneSliceReaderFixed (if x = XDP.ldp then true else false)
      (m0GeodesicSide s.hp (s.P k) .left)).map geometricSideClass =
    (oneSliceReaderFixed (if x = XDP.ldp then true else false) N).map geometricSideClass := by
  rw [s.oneSliceReaderFixed_class_eq k,
    s.oneSliceReaderFixed_class_eq_of_markedIso k I]
  exact leftOneSlice_markedIso I _


/-- Helper toward Lemma 5.6: composing the measurable fixed reader with
the certified positive-side canonical representative proves slice-class
measurability at every nonnegative boundary index. -/
theorem aemeasurable_m0CutGeodesicSliceClassOption_nonneg
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    AEMeasurable (m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure := by
  let longest := if x = XDP.ldp then true else false
  let f (z : LPlusCodingPair x) : Option GeometricSideClass :=
    if hz : z ∈ lPlusCertifiedCodingPairDomain x then
      (oneSliceReaderFixed longest (lPlusCanonicalSideOnCertifiedPair x k ⟨z, hz⟩)).map
        geometricSideClass
    else none
  have hf : Measurable f :=
    ((measurable_oneSliceReaderFixed_class longest).comp
      (measurable_lPlusCanonicalSideOnCertifiedPair x k)).dite measurable_const
        (measurableSet_lPlusCertifiedCodingPairDomain x)
  apply (hf.comp_aemeasurable (aemeasurable_lPlusCodingPairObservation x k)).congr
  filter_upwards [m0Cut_ae_leftSideUpdates x,
    lemma55LeftSideClassOption_ae_eq_lPlusRawPairCanonicalClassOption x k hk]
    with W hW hraw
  obtain ⟨s, hs⟩ := hW
  have hsome := hraw.symm.trans (lemma55LeftSideClassOption_eq_of_sliceWitness s k)
  dsimp only [Function.comp_apply] at hsome
  by_cases hz : lPlusCodingPairObservation x k W ∈ lPlusCertifiedCodingPairDomain x
  · rw [lPlusRawPairCanonicalClassOption, dite_eq_left hz] at hsome
    have hclass := Option.some.inj hsome
    obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 hclass.symm
    change f (lPlusCodingPairObservation x k W) = _
    dsimp only [f]
    rw [dite_eq_left hz, s.oneSliceReaderFixed_class_eq_of_markedIso k I]
    rw [← oneL_geometricSideClass, hclass]
    exact (hs k).1
  · rw [lPlusRawPairCanonicalClassOption, dite_eq_right hz] at hsome
    cases hsome


/-- Helper toward Lemma 5.6: the raw coherent-pair canonical class
agrees almost surely with the nonpositive left-side presentation reader. -/
theorem geoSlice_lMinusRawCanonicalClassOption_ae_eq (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    (fun W => lMinusRawCanonicalClassOption x
      (decodeLMinus x k (leftSideObsNonpos x k W), boundaryFutureHattedPath k W))
      =ᵐ[wholePlaneIIDCodeMeasure]
    (fun W => (decodeLMinus x k (leftSideObsNonpos x k W)).classOption4) := by
  filter_upwards [ae_boundaryGluing_nonpos_left_class_eq_lMinusDecodedSide4] with W hW
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hW
  cases x with
  | ldp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths true
    obtain ⟨hτ, hfin, hq, he, hr⟩ := hclass k hk
    have hf := lMinus_primed_observation_finiteIncidence (longest := true) hτ hfin
    change KMSWFiniteIncidence (decodeLMinus XDP.ldp k
      (leftSideObsNonpos XDP.ldp k W)).code.1 at hf
    change boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime at hq
    dsimp only [lMinusRawCanonicalClassOption, Prod.fst, Prod.snd]
    rw [dite_eq_left ⟨hf, hq⟩]
    exact (congrArg some (lMinusCanonicalSide_class_eq_decodedSide4
      (longest := true) hτ hq hfin)).trans
      ((congrArg some he).symm.trans hr.symm)
  | sdp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths false
    obtain ⟨hτ, hfin, hq, he, hr⟩ := hclass k hk
    have hf := lMinus_primed_observation_finiteIncidence (longest := false) hτ hfin
    change KMSWFiniteIncidence (decodeLMinus XDP.sdp k
      (leftSideObsNonpos XDP.sdp k W)).code.1 at hf
    change boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime at hq
    dsimp only [lMinusRawCanonicalClassOption, Prod.fst, Prod.snd]
    rw [dite_eq_left ⟨hf, hq⟩]
    exact (congrArg some (lMinusCanonicalSide_class_eq_decodedSide4
      (longest := false) hτ hq hfin)).trans
      ((congrArg some he).symm.trans hr.symm)


/-- Helper toward Lemma 5.6: composing the measurable fixed reader with
the coherent negative-side canonical representative proves slice-class
measurability at every nonpositive boundary index. -/
theorem aemeasurable_m0CutGeodesicSliceClassOption_nonpos
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure := by
  let longest := if x = XDP.ldp then true else false
  let D : Set (LMinusSidePresentation x × (ℕ → ℤ × ℤ)) :=
    {z | KMSWFiniteIncidence z.1.code.1 ∧
      z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime}
  have hD : MeasurableSet D :=
    (measurableSet_finiteIncidence.preimage
      ((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst)).inter
    ((selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1.preimage measurable_snd)
  let g (z : D) : LMinusCanonicalCodingDomain x :=
    ⟨(z.val.1, ⟨z.val.2, z.property.2⟩), z.property.1⟩
  have hg : Measurable g :=
    ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).subtype_mk
  let f (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) : Option GeometricSideClass :=
    if hz : z ∈ D then
      (oneSliceReaderFixed longest (lMinusCanonicalSideOnCoherent x (g ⟨z, hz⟩))).map
        geometricSideClass
    else none
  have hf : Measurable f :=
    (((measurable_oneSliceReaderFixed_class longest).comp
      (measurable_lMinusCanonicalSideOnCoherent x)).comp hg).dite measurable_const hD
  have hobs := (aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
    (aemeasurable_boundaryFutureHattedPath k)
  apply (hf.comp_aemeasurable hobs).congr
  filter_upwards [m0Cut_ae_leftSideUpdates x,
    geoSlice_lMinusRawCanonicalClassOption_ae_eq x k hk,
    lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x k hk]
    with W hW hraw hleft
  obtain ⟨s, hs⟩ := hW
  have hsome := hraw.trans (hleft.symm.trans
    (lemma55LeftSideClassOption_eq_of_sliceWitness s k))
  let z := (decodeLMinus x k (leftSideObsNonpos x k W), boundaryFutureHattedPath k W)
  by_cases hz : z ∈ D
  · have hz' : KMSWFiniteIncidence z.1.code.1 ∧
        z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := hz
    change lMinusRawCanonicalClassOption x z = _ at hsome
    rw [lMinusRawCanonicalClassOption, dite_eq_left hz'] at hsome
    have hclass := Option.some.inj hsome
    obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 hclass.symm
    change f z = _
    dsimp only [f]
    rw [dite_eq_left hz]
    change (oneSliceReaderFixed longest
      (lMinusCanonicalSide x z.1 ⟨z.2, hz'.2⟩ hz'.1)).map geometricSideClass = _
    rw [s.oneSliceReaderFixed_class_eq_of_markedIso k I]
    rw [← oneL_geometricSideClass, hclass]
    exact (hs k).1
  · have hz' : ¬ (KMSWFiniteIncidence z.1.code.1 ∧
        z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) := hz
    change lMinusRawCanonicalClassOption x z = _ at hsome
    rw [lMinusRawCanonicalClassOption, dite_eq_right hz'] at hsome
    cases hsome

/-- Helper toward Lemma 5.6: the optional actual geodesic slice class is
almost-everywhere measurable for both metrics and every integer cut. -/
theorem aemeasurable_m0CutGeodesicSliceClassOption (x : XDP) (k : ℤ) :
    AEMeasurable (m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure := by
  by_cases hk : 0 ≤ k
  · exact aemeasurable_m0CutGeodesicSliceClassOption_nonneg x k hk
  · exact aemeasurable_m0CutGeodesicSliceClassOption_nonpos x k (le_of_not_ge hk)









































end DirectedDistances.PaperProofs.Section5

/- compile exited 0. Their transitive axiom union is exactly
{propext, Classical.choice, Quot.sound}, with no placeholder or custom axiom.
an external kernel-checker run are not claimed. -/
