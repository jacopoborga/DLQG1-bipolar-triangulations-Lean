/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction4

/-! Intrinsic slit-cell connectivity and its transport by marked isomorphisms.
Identification with the geometrically defined preceding right side is separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: membership in the vertex sequence of the ray. -/
@[expose] def geometricSide_ray_vertex (M : GeometricSideSubmap)
    (v : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  ∃ n, c = v n

/-- Helper toward Lemma 5.6: both darts of every geometric ray edge,
without identifying parallel edges or discarding missing geometric edges. -/
@[expose] def geometricSide_ray_dart (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  ∃ n, c = d n ∨ geometricSideRelation M .opposite (d n) c

/-- Helper toward Lemma 5.6: ray vertices transport under a cell equivalence. -/
theorem geometricSide_ray_vertex_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_ray_vertex M v c ↔
      geometricSide_ray_vertex N (I.equiv ∘ v) (I.equiv c) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg I.equiv hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, I.equiv.injective hn⟩

/-- Helper toward Lemma 5.6: both orientations of ray edges transport. -/
theorem geometricSide_ray_dart_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_ray_dart M d c ↔
      geometricSide_ray_dart N (I.equiv ∘ d) (I.equiv c) := by
  constructor
  · rintro ⟨n, hn | hn⟩
    · exact ⟨n, Or.inl (congrArg I.equiv hn)⟩
    · exact ⟨n, Or.inr ((I.relation_iff _ _ _).1 hn)⟩
  · rintro ⟨n, hn | hn⟩
    · exact ⟨n, Or.inl (I.equiv.injective hn)⟩
    · exact ⟨n, Or.inr ((I.relation_iff _ _ _).2 hn)⟩

/-- Helper toward Lemma 5.6: slit-cell adjacency uses retained face
succession, crosses only edges off the ray, and passes through only vertices
through a ray vertex. All data belong to the side itself. -/
@[expose] def geometricSide_slit_step (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (c e : GeometricSideCell M) : Prop :=
  geometricSideRelation M .faceNext c e ∨
  geometricSideRelation M .faceNext e c ∨
  (geometricSideRelation M .opposite c e ∧ ¬ geometricSide_ray_dart M d c) ∨
  (geometricSideRelation M .incident c e ∧ ¬ geometricSide_ray_vertex M v e) ∨
  (geometricSideRelation M .incident e c ∧ ¬ geometricSide_ray_vertex M v c)

/-- Helper toward Lemma 5.6: slit adjacency is intrinsic under marked
isomorphisms mapping the two ray sequences. -/
theorem geometricSide_slit_step_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (c e : GeometricSideCell M) :
    geometricSide_slit_step M v d c e ↔
      geometricSide_slit_step N (I.equiv ∘ v) (I.equiv ∘ d)
        (I.equiv c) (I.equiv e) := by
  simp only [geometricSide_slit_step, ← I.relation_iff,
    ← geometricSide_ray_dart_map_iff I, ← geometricSide_ray_vertex_map_iff I]

/-- Helper toward Lemma 5.6: every finite slit-cell chain transports in
both directions; no ambient face chain or geometric map is supplied. -/
theorem geometricSide_slit_reaches_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (c e : GeometricSideCell M) :
    Relation.ReflTransGen (geometricSide_slit_step M v d) c e ↔
      Relation.ReflTransGen
        (geometricSide_slit_step N (I.equiv ∘ v) (I.equiv ∘ d))
        (I.equiv c) (I.equiv e) := by
  constructor
  · intro hce
    exact Relation.ReflTransGen.lift I.equiv
      (fun a b hab => (geometricSide_slit_step_map_iff I v d a b).1 hab) c e hce
  · intro hce
    have hback := Relation.ReflTransGen.lift I.equiv.symm
      (fun a b hab => (geometricSide_slit_step_map_iff I v d
        (I.equiv.symm a) (I.equiv.symm b)).2 (by
          simpa only [Equiv.apply_symm_apply] using hab)) _ _ hce
    change Relation.ReflTransGen (geometricSide_slit_step M v d)
      (I.equiv.symm (I.equiv c)) (I.equiv.symm (I.equiv e)) at hback
    simpa only [Equiv.symm_apply_apply] using hback

/-- Helper toward Lemma 5.6: a retained face on the right of an oriented
ray edge is seeded at its reverse dart. `faceNext` records the face on the
left of its argument. The existence of a successor excludes exterior corners
whose faces are absent from this side. -/
@[expose] def geometricSide_right_face_seed (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  ∃ n, geometricSideRelation M .opposite (d n) c ∧
    ∃ e, geometricSideRelation M .faceNext c e

/-- Helper toward Lemma 5.6: right-face seeds transport using only the
opposite and retained-face relations. -/
theorem geometricSide_right_face_seed_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_right_face_seed M d c ↔
      geometricSide_right_face_seed N (I.equiv ∘ d) (I.equiv c) := by
  constructor
  · rintro ⟨n, hn, e, he⟩
    exact ⟨n, (I.relation_iff _ _ _).1 hn,
      I.equiv e, (I.relation_iff _ _ _).1 he⟩
  · rintro ⟨n, hn, e, he⟩
    refine ⟨n, (I.relation_iff _ _ _).2 hn, I.equiv.symm e, ?_⟩
    apply (I.relation_iff _ _ _).2
    simpa only [Equiv.apply_symm_apply] using he

/-- Helper toward Lemma 5.6: an intrinsic candidate for the closed right
side of a ray inside a side. It contains the ray and cells reached from
retained right-face seeds without crossing the slit. This definition does
not assert agreement with the connected-component definition of actual sides. -/
@[expose] def geometricSide_intrinsic_right (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  geometricSide_ray_vertex M v c ∨ geometricSide_ray_dart M d c ∨
    ∃ a, geometricSide_right_face_seed M d a ∧
      Relation.ReflTransGen (geometricSide_slit_step M v d) a c

/-- Helper toward Lemma 5.6: the intrinsic candidate right-side predicate
is invariant under every marked isomorphism mapping ray to ray. -/
theorem geometricSide_intrinsic_right_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_intrinsic_right M v d c ↔
      geometricSide_intrinsic_right N (I.equiv ∘ v) (I.equiv ∘ d) (I.equiv c) := by
  rw [geometricSide_intrinsic_right, geometricSide_intrinsic_right,
    ← geometricSide_ray_vertex_map_iff I, ← geometricSide_ray_dart_map_iff I]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨a, ha, hac⟩
    exact ⟨I.equiv a, (geometricSide_right_face_seed_map_iff I d a).1 ha,
      (geometricSide_slit_reaches_map_iff I v d a c).1 hac⟩
  · rintro ⟨a, ha, hac⟩
    refine ⟨I.equiv.symm a, ?_, ?_⟩
    · apply (geometricSide_right_face_seed_map_iff I d _).2
      simpa only [Equiv.apply_symm_apply] using ha
    · apply (geometricSide_slit_reaches_map_iff I v d _ c).2
      simpa only [Equiv.apply_symm_apply] using hac

/-- Helper toward Lemma 5.6: a point of an arc's first segment belongs to
the arc image, with both segment endpoints allowed. -/
private theorem enclosedSlice_initialSegment_mem (p : Polyline)
    (hlen : 2 ≤ p.points.length) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  refine Or.inr ⟨0, by omega, ?_⟩
  change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
  rw [Polyline.point_zero_eq_start]
  have heq : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: a retained face bordering the reverse dart
of a geodesic edge lies in its actual open right side. The proof uses the
westward left wedge below the arc's final segment, with no separation or
side-characterization premise. -/
theorem m0Geodesic_reverse_seam_face_right
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (P.codePath.edge i, true)) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P .right := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let q := G.arc (wholePlaneDartι W 0 (P.codePath.edge i, true))
  have hd : q.initialDirection.re < 0 := by
    dsimp only [q, G]
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hp H
      (P.codePath.edge i, true)]
    exact m0RawDrawing_incoming_initialDirection_re_neg H (P.codePath.edge i)
  let η := -q.initialDirection.re
  let upper : ℝ → ℝ := fun x => q.start.im +
    q.initialDirection.im / q.initialDirection.re * (x - q.start.re)
  let lower : ℝ → ℝ := fun x => q.start.im +
    (q.initialDirection.im / q.initialDirection.re + 1) * (x - q.start.re)
  obtain ⟨δ, hδ, hw⟩ := wedgeIn_graphRegion_west_upper_slope
    (a := q.start.re - η) (b := q.start.re) (f := lower) (g := upper)
    q.start q.initialDirection η (q.initialDirection.im / q.initialDirection.re + 1)
    hd le_rfl (neg_pos.mpr hd) le_rfl (fun _ _ => rfl) (lt_add_one _)
    (fun _ _ => le_rfl)
  obtain ⟨δF, hδF, hwF⟩ := hb
  let t := min δ δF / 2
  have ht : 0 < t := half_pos (lt_min hδ hδF)
  have htδ : t < δ := (half_lt_self (lt_min hδ hδF)).trans_le (min_le_left _ _)
  have htF : t < δF := (half_lt_self (lt_min hδ hδF)).trans_le (min_le_right _ _)
  let z := PlanarMap.wedgePoint q.start q.initialDirection t t
  have hzF : z ∈ F.val := hwF t t ht htF ht htF
  have hz := hw t t ht htδ ht htδ
  change q.start.re - η < z.re ∧ z.re < q.start.re ∧
    lower z.re < z.im ∧ z.im < upper z.re at hz
  let u := (z.re - q.start.re) / q.initialDirection.re
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr hz.2.1.le) hd.le
    · apply (div_le_one_of_neg hd).mpr
      dsimp only [η] at hz
      linarith only [hz.1]
  let y := q.start + u • q.initialDirection
  have hyq : y ∈ q.image := enclosedSlice_initialSegment_mem q (G.arc_length _) hu
  have hyP : y ∈ m0GeodesicTrace hp P := by
    apply m0Geodesic_arc_subset_trace hp P i
    have hflip := G.arc_flip (wholePlaneDartι W 0 (m0GeodesicSeam P i))
    change q = (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).reverse at hflip
    rw [hflip, Polyline.image_reverse_transfer] at hyq
    exact hyq
  have hyre : y.re = z.re := by
    simp only [y, u, Complex.add_re, Complex.smul_re, smul_eq_mul,
      div_mul_cancel₀ _ hd.ne]
    ring
  have hyim : y.im = upper z.re := by
    simp only [y, u, upper, Complex.add_im, Complex.smul_im, smul_eq_mul]
    ring
  have hzbelow : z.im < y.im := by
    rw [hyim]
    exact hz.2.2.2
  have hznot := boundaryGluing_below_trace_not_mem_leftOpen W h k longest hp P
    hyP hyre hzbelow
  obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp P F hFR
  cases s with
  | right => exact hs
  | left => exact False.elim (hznot (hs hzF))

/-- Helper toward Lemma 5.6: an intrinsic right-face seed in the current
left side borders a face in the actual right/left open-side overlap. Thus
seed soundness is proved using the carrier's geometric definition. -/
theorem m0GeodesicLeftSide_right_face_seed_has_common_side_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (c : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (hc : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inr c)) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 c.val) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
  obtain ⟨i, hi, e, he⟩ := hc
  change ((P (k - 1)).codePath.edge i, true) = c.val at hi
  cases e with
  | inl e => exact False.elim he
  | inr e =>
    obtain ⟨⟨F, hb, hF⟩, _⟩ := he
    refine ⟨F, hb, ?_, hF⟩
    apply m0Geodesic_reverse_seam_face_right hp (P (k - 1)) i F
      (fun z hz => (m0GeodesicLeftOpen_subset hp (P k) (hF hz)).1)
    rw [hi]
    exact hb

/-- Helper toward Lemma 5.6: each intrinsic right-face seed supplies a
face represented by the actual slice, for every valid pair of cut offsets.
This proves seed soundness, not exhaustion of all represented faces. -/
theorem m0GeodesicLeftSide_right_face_seed_represents_slice_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (hc : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inr c)) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 c.val) F ∧
      m0CutGeodesicSliceRepresentsFace hp P k a b hab F := by
  obtain ⟨F, hb, hr, hl⟩ :=
    m0GeodesicLeftSide_right_face_seed_has_common_side_face hp P k hcontain c hc
  exact ⟨F, hb,
    (m0CutGeodesicSliceRepresentsFace_iff_common_side_face hp P k a b hab F).2
      ⟨⟨c.val, hb⟩, hr, hl⟩⟩

/-- Helper toward Lemma 5.6: the canonical inclusion of actual slice
cells into the current left side retains vertex IDs and individual darts.
It asserts no isomorphism or enclosure characterization. -/
@[expose] def m0CutGeodesicSliceLeftCell
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab) →
      GeometricSideCell (m0GeodesicSide hp (P k) .left)
  | .inl v => .inl ⟨v.val, v.property.1.2⟩
  | .inr d => .inr ⟨d.val, d.property.1.2⟩

/-- Helper toward Lemma 5.6: including slice cells loses no vertex or
dart identity, including for multiedges. -/
theorem m0CutGeodesicSliceLeftCell_injective
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    Function.Injective (m0CutGeodesicSliceLeftCell hp P k a b hab) := by
  intro c e hce
  cases c <;> cases e
  · dsimp only [m0CutGeodesicSliceLeftCell] at hce
    have hv := congrArg Subtype.val (Sum.inl.inj hce)
    exact congrArg Sum.inl (Subtype.ext hv)
  · exact False.elim (Sum.inl_ne_inr hce)
  · exact False.elim (Sum.inr_ne_inl hce)
  · dsimp only [m0CutGeodesicSliceLeftCell] at hce
    have hd := congrArg Subtype.val (Sum.inr.inj hce)
    exact congrArg Sum.inr (Subtype.ext hd)

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

include hleft hleft' in
/-- Helper toward Lemma 5.6: the candidate enclosure predicate for the
intrinsically selected preceding ray transports between realized left sides.
Ray identification is proved by the imported selector, rather than assumed. -/
theorem m0GeodesicLeftSide_markedIso_intrinsic_right_iff
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
    geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') (I.equiv c) := by
  obtain ⟨hv, hd⟩ := m0GeodesicLeftSide_markedIso_map_previousRay
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I
  have hm := geometricSide_intrinsic_right_map_iff I
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain) c
  rw [hv, hd] at hm
  exact hm

include hleft hleft' in
/-- Helper toward Lemma 5.6: the intrinsic candidate restricted by the
exact surviving-tail test is invariant, including both zero cut offsets.
This is not asserted to be the actual enclosed-slice carrier. -/
theorem m0GeodesicLeftSide_markedIso_intrinsic_survivor_iff
    (a b : ℕ) (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    (geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ∧
      c ∉ m0GeodesicLeftSideDeletedTailCells hp P k a b) ↔
    (geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') (I.equiv c) ∧
      I.equiv c ∉ m0GeodesicLeftSideDeletedTailCells hp' P' l a b) :=
  and_congr (m0GeodesicLeftSide_markedIso_intrinsic_right_iff
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I c)
    (not_congr (m0GeodesicLeftSide_markedIso_deletedTailCells_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b c))

end TwoRealizations




















































































































end DirectedDistances.PaperProofs.Section5
