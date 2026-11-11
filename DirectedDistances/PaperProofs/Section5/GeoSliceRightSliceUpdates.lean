/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceFaceChainClopen2
public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReconstruction
public import DirectedDistances.PaperProofs.Section5.GeoSliceCarrierFidelity

/-! Helper toward Lemma 5.6: corrected right-side slice reconstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Set Metric
open scoped Classical Topology

/-- Helper toward Lemma 5.6: the preceding seam segment includes its
coalescence vertex and both orientations of edges strictly before the offset. -/
@[expose] def rightSlicePrecedingSegment (M : GeometricSideSubmap)
    (vs ds : ℕ → GeometricSideCell M) (a : ℕ) : Set (GeometricSideCell M) :=
  {c | (∃ n, n ≤ a ∧ c = vs n) ∨
    ∃ n, n < a ∧ (c = ds n ∨ geometricSideRelation M .opposite (ds n) c)}

/-- Helper toward Lemma 5.6: the corrected slice carrier adjoins the old
boundary segment to the intrinsic left candidate before deleting both tails. -/
@[expose] def rightSliceKeep2 (M : GeometricSideSubmap)
    (v d vs ds : ℕ → GeometricSideCell M) (a b : ℕ) :
    Set (GeometricSideCell M) :=
  {c | (geometricSide_intrinsic_left M v d c ∨
      c ∈ rightSlicePrecedingSegment M vs ds a) ∧
    c ∉ geometricSideRayDeletedTailCells M vs ds a ∪
      geometricSideRayDeletedTailCells M v d b}

/-- Helper toward Lemma 5.6: the preceding segment transports using
indexed seam cells and opposite darts, without any source hypothesis. -/
theorem rightSlicePrecedingSegment_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (vs ds : ℕ → GeometricSideCell M)
    (a : ℕ) (c : GeometricSideCell M) :
    c ∈ rightSlicePrecedingSegment M vs ds a ↔
      I.equiv c ∈ rightSlicePrecedingSegment N (I.equiv ∘ vs) (I.equiv ∘ ds) a := by
  constructor
  · rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc | hc⟩)
    · exact Or.inl ⟨n, hn, congrArg I.equiv hc⟩
    · exact Or.inr ⟨n, hn, Or.inl (congrArg I.equiv hc)⟩
    · exact Or.inr ⟨n, hn, Or.inr ((I.relation_iff _ _ _).1 hc)⟩
  · rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc | hc⟩)
    · exact Or.inl ⟨n, hn, I.equiv.injective hc⟩
    · exact Or.inr ⟨n, hn, Or.inl (I.equiv.injective hc)⟩
    · exact Or.inr ⟨n, hn, Or.inr ((I.relation_iff _ _ _).2 hc)⟩

/-- Helper toward Lemma 5.6: corrected carrier transport is unconditional
and preserves the jointly specified two offsets. -/
theorem rightSliceKeep2_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d vs ds : ℕ → GeometricSideCell M)
    (a b : ℕ) (c : GeometricSideCell M) :
    c ∈ rightSliceKeep2 M v d vs ds a b ↔
      I.equiv c ∈ rightSliceKeep2 N (I.equiv ∘ v) (I.equiv ∘ d)
        (I.equiv ∘ vs) (I.equiv ∘ ds) a b :=
  and_congr (or_congr (geometricSide_intrinsic_left_map_iff I v d c)
      (rightSlicePrecedingSegment_map_iff I vs ds a c))
    (not_congr (or_congr (geometricSideRayDeletedTailCells_map_iff I vs ds a c)
      (geometricSideRayDeletedTailCells_map_iff I v d b c)))

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: OPEN R supplies the complete next-right
carrier characterization without adding an exhaustion premise. -/
theorem m0GeodesicRightSide_intrinsic_right_iff_nextRight
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    geometricSide_intrinsic_right _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right := by
  exact m0GeodesicRightSide_intrinsic_right_reduction_of_exhaustion hp P k
    (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k)
    (fun c hm hv hd => m0GeodesicRightSide_source_right_exhaustion
      hp P T hleft hc k c hm hv hd) c

/-- Helper toward Lemma 5.6: on a source right side, the intrinsic old
segment is exactly the literal preceding-ray vertex/edge prefix. -/
theorem rightSlicePrecedingSegment_source_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a : ℕ)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    c ∈ rightSlicePrecedingSegment _
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a ↔
      match c with
      | .inl v => ∃ n, n ≤ a ∧ v.val = ((P (k - 1)).codePath.initial n).1.id
      | .inr d => ∃ n, n < a ∧ d.val.1 = (P (k - 1)).codePath.edge n := by
  cases c with
  | inl v =>
    change ((∃ n, n ≤ a ∧ Sum.inl v = Sum.inl _) ∨
      ∃ n, n < a ∧ (Sum.inl v = Sum.inr _ ∨ False)) ↔ _
    simp only [Sum.inl.injEq, Subtype.ext_iff, Sum.inl_ne_inr,
      or_self, and_false, exists_false, or_false]
  | inr d =>
    change ((∃ n, n ≤ a ∧ Sum.inr d = Sum.inl _) ∨
      ∃ n, n < a ∧ (Sum.inr d = Sum.inr _ ∨
        ((P (k - 1)).codePath.edge n, true) = d.val)) ↔ _
    simp only [Sum.inr_ne_inl, and_false, exists_false, false_or,
      Sum.inr.injEq, Subtype.ext_iff]
    constructor
    · rintro ⟨n, hn, hd | hd⟩
      · exact ⟨n, hn, congrArg Prod.fst hd⟩
      · exact ⟨n, hn, (congrArg Prod.fst hd).symm⟩
    · rintro ⟨n, hn, hd⟩
      refine ⟨n, hn, ?_⟩
      cases hb : d.val.2 with
      | false => exact Or.inl (Prod.ext hd hb)
      | true => exact Or.inr (Prod.ext hd.symm hb.symm)

/-- Helper toward Lemma 5.6: survival outside the old boundary segment
excludes the entire preceding ray, including its coalescence vertex. -/
theorem m0GeodesicRightSide_survivor_off_precedingRay
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (htail : c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b)
    (hsegment : c ∉ rightSlicePrecedingSegment _
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a) :
    (match c with
    | .inl v => v.val ∉ m0GeodesicVertices (P (k - 1))
    | .inr d => d.val.1 ∉ m0GeodesicEdges (P (k - 1))) := by
  have hs := rightSlicePrecedingSegment_source_iff hp P k a c
  cases c with
  | inl v =>
    rintro ⟨n, hn⟩
    by_cases hna : n ≤ a
    · exact hsegment (hs.mpr ⟨n, hna, hn.symm⟩)
    · exact htail (Or.inl ⟨n, Nat.lt_of_not_ge hna, hn.symm⟩)
  | inr d =>
    rintro ⟨n, hn⟩
    by_cases hna : n < a
    · exact hsegment (hs.mpr ⟨n, hna, hn.symm⟩)
    · exact htail (Or.inl ⟨n - a, by
        simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hna)] using hn⟩)

/-- Helper toward Lemma 5.6: the adjoined preceding segment belongs to
the literal source slice, with strict edge and weak vertex endpoints. -/
theorem rightSlicePrecedingSegment_source_mem_slice
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hsegment : c ∈ rightSlicePrecedingSegment _
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a) :
    Sum.elim (fun v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices)
      (fun d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) c := by
  have hs := (rightSlicePrecedingSegment_source_iff hp P k a c).mp hsegment
  have hb := m0CutGeodesicSlice_boundary_segments_mem (hp := hp) P T hleft k a b hab
  cases c with
  | inl v =>
    obtain ⟨n, hn, he⟩ := hs
    change v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
    rw [he]
    exact hb.1 n hn
  | inr d =>
    obtain ⟨n, hn, he⟩ := hs
    change d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges
    rw [he]
    exact hb.2.1 n hn

/-- Helper toward Lemma 5.6: every cell of the corrected intrinsic
carrier belongs to the source slice. No exhaustion is used for soundness. -/
theorem rightSliceKeep2_source_sound
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hkeep : c ∈ rightSliceKeep2 _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k)
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b) :
    Sum.elim (fun v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices)
      (fun d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) c := by
  rcases hkeep with ⟨hleftCell | hsegment, htail⟩
  · have hm : Sum.elim
        (fun v => v.val ∈ m0GeodesicSideVertices hp (P k) .left)
        (fun d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) c ∧
          c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b := by
      refine ⟨?_, ?_⟩
      · cases c <;> exact m0GeodesicRightSide_intrinsic_left_sound hp P k
          (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) _ hleftCell
      · rwa [m0GeodesicRightSideDeletedTailCells_eq hp P k
          (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) a b]
    cases c with
    | inl v => exact (m0CutGeodesicSlice_mem_cell_iff_nextLeft_and_not_deletedTail
        hp P k a b hab (.inl v)).mpr ⟨hm.1, hm.2⟩
    | inr d => exact (m0CutGeodesicSlice_mem_cell_iff_nextLeft_and_not_deletedTail
        hp P k a b hab (.inr d)).mpr ⟨hm.1, hm.2⟩
  · exact rightSlicePrecedingSegment_source_mem_slice hp P T hleft k a b hab c hsegment

/-- Helper toward Lemma 5.6: every cell in the modified OPEN L domain
has an actual overlap face and a slit chain from a bordering dart to the
cell. The global chain from a next-left seed remains a separate obligation. -/
theorem m0GeodesicRightSide_survivor_has_overlap_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hmem : match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left)
    (htail : c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b)
    (hsegment : c ∉ rightSlicePrecedingSegment _
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a)
    (hoffV : ¬ geometricSide_ray_vertex _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k) c)
    (hoffD : ¬ geometricSide_ray_dart _
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c) :
    ∃ (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges}),
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 d.val) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      Relation.ReflTransGen
        (geometricSide_slit_step _
          (m0GeodesicRightSideNextVertices hp P T hleft hc k)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k)) (.inr d) c := by
  have hpOff := m0GeodesicRightSide_survivor_off_precedingRay hp P k a b c htail hsegment
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  cases c with
  | inl v =>
    have hvOff : v.val ∉ m0GeodesicVertices (P k) := fun hv =>
      hoffV ((m0GeodesicRightSide_ray_vertex_iff hp P k hcontain v).mpr hv)
    obtain ⟨e, _, hev⟩ := uibot_allocated_vertex_outgoing
      (shiftedStream W 0) h.R_unbounded_below v.val
      (kmsw_vertex_allocated_of_finite_incidence (shiftedStream W 0) (H.1 0) v.val)
    have heL := (m0Geodesic_incident_off_ray_side_iff hp (P k) .left
      (e, false) v.val hev hvOff).2.mpr hmem
    obtain ⟨heOff, heRiff⟩ := m0Geodesic_incident_off_ray_side_iff hp (P (k - 1))
      .right (e, false) v.val hev hpOff
    have heR := heRiff.mpr v.property
    obtain ⟨F, hb, hFL, hFR⟩ := m0GeodesicLeftSide_off_ray_edge_has_overlap_face
      hp P k e heL heR heOff
    refine ⟨F, ⟨(e, false), heR⟩, hb, hFL, hFR, .single ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hev, hoffV⟩)))
  | inr d =>
    obtain ⟨F, hb, hFL, hFR⟩ := m0GeodesicLeftSide_off_ray_edge_has_overlap_face
      hp P k d.val.1 hmem d.property hpOff
    let e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨(d.val.1, false), d.property⟩
    refine ⟨F, e, hb, hFL, hFR, ?_⟩
    cases hd : d.val.2 with
    | false =>
      have he : e = d := Subtype.ext (Prod.ext rfl hd.symm)
      rw [he]
    | true =>
      refine .single (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
      · change (d.val.1, true) = d.val
        exact Prod.ext rfl hd.symm
      · intro he
        apply hoffD
        apply (m0GeodesicRightSide_ray_dart_iff hp P k hcontain d).mpr
        exact (m0GeodesicRightSide_ray_dart_iff hp P k hcontain e).mp he

/-- Helper toward Lemma 5.6: positive rotation chains skip every internal
cell of the retained slice carrier. -/
inductive RightSliceRotationChain2 {α : Type*} (R : α → α → Prop)
    (keep : Set α) : α → α → Prop
  | single {a b} (h : R a b) : RightSliceRotationChain2 R keep a b
  | cons {a b c} (h : R a b) (hb : b ∉ keep)
      (tail : RightSliceRotationChain2 R keep b c) : RightSliceRotationChain2 R keep a c

/-- Helper toward Lemma 5.6: restricted rotation chains transport through
any map preserving their steps and omitted cells. -/
theorem rightSliceRotationChain2_map {α β : Type*}
    {R : α → α → Prop} {S : β → β → Prop} {A : Set α} {B : Set β}
    (f : α → β) (hr : ∀ a b, R a b → S (f a) (f b))
    (hk : ∀ a, a ∉ A → f a ∉ B) {a b : α}
    (h : RightSliceRotationChain2 R A a b) :
    RightSliceRotationChain2 S B (f a) (f b) := by
  induction h with
  | single h => exact .single (hr _ _ h)
  | cons h hb _ ih => exact .cons (hr _ _ h) (hk _ hb) ih

/-- Helper toward Lemma 5.6: first-return rotation is invariant under a
bijection preserving retained cells and the full ambient rotation. -/
theorem rightSliceRotationChain2_map_iff {α β : Type*}
    {R : α → α → Prop} {S : β → β → Prop} {A : Set α} {B : Set β}
    (I : α ≃ β) (hr : ∀ a b, R a b ↔ S (I a) (I b))
    (hk : ∀ a, a ∈ A ↔ I a ∈ B) (a b : α) :
    RightSliceRotationChain2 R A a b ↔ RightSliceRotationChain2 S B (I a) (I b) := by
  constructor
  · exact rightSliceRotationChain2_map I (fun a b => (hr a b).1)
      (fun a => (not_congr (hk a)).1)
  · intro h
    have hh := rightSliceRotationChain2_map I.symm
      (fun a b hab => (hr (I.symm a) (I.symm b)).2
        (by simpa only [Equiv.apply_symm_apply] using hab))
      (fun a ha => (not_congr (hk (I.symm a))).2
        (by simpa only [Equiv.apply_symm_apply] using ha)) h
    simpa only [Equiv.symm_apply_apply] using hh

/-- Helper toward Lemma 5.6: the corrected slice relation keeps the old
root, marks the old seam as boundary and the next ray as seam, induces
rotation by first return, and retains precisely the next-left face sector.
The sector test uses the complete intrinsic right candidate and forward darts. -/
@[expose] def rightSliceRelation2 (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (keep : Set (GeometricSideCell M))
    (t : TruncationRelation) (c e : GeometricSideCell M) : Prop :=
  match t with
  | .boundary i => geometricSideRelation M (.seam i) c e
  | .seam i => c = d i
  | .rotation => RightSliceRotationChain2 (geometricSideRelation M .rotation) keep c e
  | .faceNext => geometricSideRelation M .faceNext c e ∧
      (¬ geometricSide_intrinsic_right M v d c ∨ ∃ n, c = d n)
  | _ => geometricSideRelation M t c e

/-- Helper toward Lemma 5.6: the complete corrected slice relation,
including every mark and face sector, transports intrinsically. -/
theorem rightSliceRelation2_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (keep : Set (GeometricSideCell M)) (keep' : Set (GeometricSideCell N))
    (hk : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (t : TruncationRelation) (c e : GeometricSideCell M) :
    rightSliceRelation2 M v d keep t c e ↔
      rightSliceRelation2 N (I.equiv ∘ v) (I.equiv ∘ d) keep' t
        (I.equiv c) (I.equiv e) := by
  cases t with
  | boundary i => exact I.relation_iff (.seam i) c e
  | seam i => exact ⟨congrArg I.equiv, fun h => I.equiv.injective h⟩
  | rotation => exact rightSliceRotationChain2_map_iff I.equiv (I.relation_iff .rotation) hk c e
  | faceNext =>
    exact and_congr (I.relation_iff .faceNext c e)
      (or_congr (not_congr (geometricSide_intrinsic_right_map_iff I v d c))
        (exists_congr fun n => ⟨congrArg I.equiv, fun h => I.equiv.injective h⟩))
  | vertex => exact I.relation_iff .vertex c e
  | root => exact I.relation_iff .root c e
  | incident => exact I.relation_iff .incident c e
  | opposite => exact I.relation_iff .opposite c e
  | oriented => exact I.relation_iff .oriented c e
  | target => exact I.relation_iff .target c e

/-- Helper toward Lemma 5.6: a numbered marked submap realizes every
cell and every relation of a specified intrinsic restriction. -/
@[expose] def rightRestrictionRealizes2 (M : GeometricSideSubmap)
    (keep : Set (GeometricSideCell M))
    (R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop)
    (N : GeometricSideSubmap) : Prop :=
  ∃ e : GeometricSideCell N ≃ keep, ∀ t a b,
    geometricSideRelation N t a b ↔ R t (e a).val (e b).val

/-- Helper toward Lemma 5.6: full restriction realizations have one
marked class, independently of the chosen natural numbering. -/
theorem rightRestrictionRealizes2_class_unique {M N N' : GeometricSideSubmap}
    {keep : Set (GeometricSideCell M)}
    {R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop}
    (h : rightRestrictionRealizes2 M keep R N)
    (h' : rightRestrictionRealizes2 M keep R N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  apply (geometricSideClass_eq_iff _ _).2
  refine ⟨⟨e.trans f.symm, ?_⟩⟩
  intro t a b
  change geometricSideRelation N t a b ↔
    geometricSideRelation N' t (f.symm (e a)) (f.symm (e b))
  rw [he, hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Helper toward Lemma 5.6: realization transport retains the entire
restriction, without geometric characterization assumptions. -/
theorem rightRestrictionRealizes2_transport {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M')
    {keep : Set (GeometricSideCell M)} {keep' : Set (GeometricSideCell M')}
    {R : TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop}
    {R' : TruncationRelation → GeometricSideCell M' → GeometricSideCell M' → Prop}
    (hk : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (hr : ∀ t c e, R t c e ↔ R' t (I.equiv c) (I.equiv e))
    (h : rightRestrictionRealizes2 M keep R N) :
    rightRestrictionRealizes2 M' keep' R' N := by
  obtain ⟨e, he⟩ := h
  let f : keep ≃ keep' :=
    { toFun := fun c => ⟨I.equiv c.val, (hk c.val).1 c.property⟩
      invFun := fun c => ⟨I.equiv.symm c.val, (hk _).2 (by
        simpa only [Equiv.apply_symm_apply] using c.property)⟩
      left_inv := fun c => Subtype.ext (I.equiv.symm_apply_apply c.val)
      right_inv := fun c => Subtype.ext (I.equiv.apply_symm_apply c.val) }
  exact ⟨e.trans f, fun t a b => (he t a b).trans (hr t _ _)⟩

/-- Helper toward Lemma 5.6: unique intrinsic corner-ray data for the
corrected reader, with no asserted existence on arbitrary abstract sides. -/
@[expose] def rightReconstructionRay2 (longest : Bool) (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) : Prop :=
  intrinsicallyLeftmostAdjacentRightRay M longest v d ∧
    ∀ v' d', intrinsicallyLeftmostAdjacentRightRay M longest v' d' → v' = v ∧ d' = d

/-- Helper toward Lemma 5.6: uniqueness of the corner ray transports
through every complete marked-side isomorphism. -/
theorem rightReconstructionRay2_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (longest : Bool)
    {v d : ℕ → GeometricSideCell M} (h : rightReconstructionRay2 longest M v d) :
    rightReconstructionRay2 longest N (I.equiv ∘ v) (I.equiv ∘ d) := by
  refine ⟨intrinsicallyLeftmostAdjacentRightRay_map I longest h.1, ?_⟩
  intro v' d' hl
  obtain ⟨hv, hd⟩ := h.2 _ _
    (intrinsicallyLeftmostAdjacentRightRay_map (GeometricSideMarkedIso.symm I) longest hl)
  constructor
  · funext n
    exact (I.equiv.apply_symm_apply (v' n)).symm.trans (congrArg I.equiv (congrFun hv n))
  · funext n
    exact (I.equiv.apply_symm_apply (d' n)).symm.trans (congrArg I.equiv (congrFun hd n))

/-- Helper toward Lemma 5.6: the indexed old seam and its initial
vertices are specified intrinsically by all seam and incidence marks. -/
@[expose] def rightReconstructionSeam2 (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) : Prop :=
  ∀ n, geometricSideRelation M (.seam n) (d n) (d n) ∧
    geometricSideRelation M .incident (d n) (v n)

/-- Helper toward Lemma 5.6: the old seam data transport intrinsically. -/
theorem rightReconstructionSeam2_map {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) {v d : ℕ → GeometricSideCell M}
    (h : rightReconstructionSeam2 M v d) :
    rightReconstructionSeam2 N (I.equiv ∘ v) (I.equiv ∘ d) :=
  fun n => ⟨(I.relation_iff _ _ _).1 (h n).1, (I.relation_iff _ _ _).1 (h n).2⟩

/-- Helper toward Lemma 5.6: indexed marks determine both old-seam
streams uniquely, including their geometric vertex cells. -/
theorem rightReconstructionSeam2_unique {M : GeometricSideSubmap}
    {v d v' d' : ℕ → GeometricSideCell M}
    (h : rightReconstructionSeam2 M v d) (h' : rightReconstructionSeam2 M v' d') :
    v = v' ∧ d = d' := by
  have hd : d = d' := funext fun n =>
    geometricSideRelation_seam_self_unique M n (h n).1 (h' n).1
  subst d'
  exact ⟨funext fun n => geometricSideRelation_incident_right_unique M (h n).2 (h' n).2, rfl⟩

/-- Helper toward Lemma 5.6: realization of the corrected restriction at
its jointly least aligned old-seam and next-ray offsets. The old offset is
a and the next offset is b, reversing the intrinsic agreement API's order. -/
@[expose] def rightSliceRealizes2 (x : XDP) (M N : GeometricSideSubmap) : Prop :=
  ∃ v d vs ds a b, rightReconstructionRay2 (geoSliceRightLongest x) M v d ∧
    rightReconstructionSeam2 M vs ds ∧ geometricSideRaySeamAgreement M d b a ∧
    (∀ a' b', geometricSideRaySeamAgreement M d b' a' → a ≤ a' ∧ b ≤ b') ∧
    rightRestrictionRealizes2 M (rightSliceKeep2 M v d vs ds a b)
      (rightSliceRelation2 M v d (rightSliceKeep2 M v d vs ds a b)) N

/-- Helper toward Lemma 5.6: corrected slice realization transports with
no exhaustion or source-realization premise. -/
theorem rightSliceRealizes2_map {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M') (x : XDP)
    (h : rightSliceRealizes2 x M N) : rightSliceRealizes2 x M' N := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  refine ⟨I.equiv ∘ v, I.equiv ∘ d, I.equiv ∘ vs, I.equiv ∘ ds, a, b,
    rightReconstructionRay2_map I _ hr, rightReconstructionSeam2_map I hs,
    (geometricSideRaySeamAgreement_iff I d b a).1 ht,
    fun a' b' ht' => hm a' b' ((geometricSideRaySeamAgreement_iff I d b' a').2 ht'), ?_⟩
  exact rightRestrictionRealizes2_transport I (rightSliceKeep2_map_iff I v d vs ds a b)
    (rightSliceRelation2_map_iff I v d _ _ (rightSliceKeep2_map_iff I v d vs ds a b)) hN

/-- Helper toward Lemma 5.6: corrected realizations have a unique marked
class; uniqueness precedes the choice in the optional reader. -/
theorem rightSliceRealizes2_class_unique {x : XDP} {M N N' : GeometricSideSubmap}
    (h : rightSliceRealizes2 x M N) (h' : rightSliceRealizes2 x M N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  obtain ⟨v', d', vs', ds', a', b', hr', hs', ht', hm', hN'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hr.2 v' d' hr'.1
  obtain ⟨rfl, rfl⟩ := rightReconstructionSeam2_unique hs' hs
  have ha : a' = a := Nat.le_antisymm (hm' a b ht).1 (hm a' b' ht').1
  have hb : b' = b := Nat.le_antisymm (hm' a b ht).2 (hm a' b' ht').2
  subst a'
  subst b'
  exact rightRestrictionRealizes2_class_unique hN hN'

/-- Helper toward Lemma 5.6: the corrected optional reader chooses the
unique marked class of the complete intrinsic restriction. Nonrealizable
restrictions return none; source realizability is not asserted here. -/
@[expose] noncomputable def rightOneSlice2 (x : XDP) (M : GeometricSideSubmap) :
    Option GeometricSideClass :=
  if h : ∃ N, rightSliceRealizes2 x M N then some (geometricSideClass h.choose) else none

/-- Helper toward Lemma 5.6: the corrected reader returns the class of
every complete realization of its intrinsic restriction. -/
theorem rightOneSlice2_eq_of_realizes {x : XDP} {M N : GeometricSideSubmap}
    (h : rightSliceRealizes2 x M N) :
    rightOneSlice2 x M = some (geometricSideClass N) := by
  have hex : ∃ N, rightSliceRealizes2 x M N := ⟨N, h⟩
  rw [rightOneSlice2, dite_eq_left hex]
  exact congrArg some (rightSliceRealizes2_class_unique hex.choose_spec h)

/-- Helper toward Lemma 5.6: the corrected reader is absent precisely
when its complete intrinsic restriction has no numbered realization. -/
theorem rightOneSlice2_eq_none_iff (x : XDP) (M : GeometricSideSubmap) :
    rightOneSlice2 x M = none ↔ ¬ ∃ N, rightSliceRealizes2 x M N := by
  unfold rightOneSlice2
  split_ifs with h <;> simp only [not_true_eq_false,
    not_false_eq_true, h]

/-- Helper toward Lemma 5.6: the corrected optional reader is invariant
under every marked-side isomorphism, including outside its realization domain. -/
theorem rightOneSlice2_markedIso {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (x : XDP) :
    rightOneSlice2 x M = rightOneSlice2 x N := by
  by_cases h : ∃ K, rightSliceRealizes2 x M K
  · obtain ⟨K, hK⟩ := h
    exact (rightOneSlice2_eq_of_realizes hK).trans
      (rightOneSlice2_eq_of_realizes (rightSliceRealizes2_map I x hK)).symm
  · have hn : ¬ ∃ K, rightSliceRealizes2 x N K := by
      rintro ⟨K, hK⟩
      exact h ⟨K, rightSliceRealizes2_map (GeometricSideMarkedIso.symm I) x hK⟩
    rw [(rightOneSlice2_eq_none_iff x M).2 h, (rightOneSlice2_eq_none_iff x N).2 hn]

/-- Helper toward Lemma 5.6: the corrected slice reader descends to
marked-isomorphism classes without an exhaustion assumption. -/
@[expose] noncomputable def oneR (x : XDP) :
    GeometricSideClass → Option GeometricSideClass :=
  Quotient.lift (rightOneSlice2 x)
    (fun _ _ h => h.elim fun I => rightOneSlice2_markedIso I x)

/-- Helper toward Lemma 5.6: the quotient reader evaluates on every
representative by the corrected intrinsic one-slice operation. -/
theorem oneR_geometricSideClass (x : XDP) (M : GeometricSideSubmap) :
    oneR x (geometricSideClass M) = rightOneSlice2 x M := rfl

/-- Helper toward Lemma 5.6: the full graph of the corrected reader
characterizes its value by a realization of the specified intrinsic restriction. -/
theorem rightOneSlice2_eq_some_iff (x : XDP) (M : GeometricSideSubmap)
    (C : GeometricSideClass) :
    rightOneSlice2 x M = some C ↔
      ∃ N, rightSliceRealizes2 x M N ∧ geometricSideClass N = C := by
  constructor
  · intro h
    by_cases hex : ∃ N, rightSliceRealizes2 x M N
    · refine ⟨hex.choose, hex.choose_spec, ?_⟩
      rw [rightOneSlice2, dite_eq_left hex] at h
      exact Option.some.inj h
    · rw [(rightOneSlice2_eq_none_iff x M).2 hex] at h
      cases h
  · rintro ⟨N, hN, rfl⟩
    exact rightOneSlice2_eq_of_realizes hN

/-- Helper toward Lemma 5.6: actual source right sides supply the unique
corner-ray data used by the corrected reader, without assuming exhaustion. -/
theorem m0GeodesicRightSide_rightReconstructionRay2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) :
    rightReconstructionRay2 longest (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) := by
  have hr := m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight hp P T hleft hc k
  exact ⟨hr, fun _ _ hr' =>
    m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRightRay_unique
      hp (P (k - 1)) hr' hr⟩

/-- Helper toward Lemma 5.6: the source's old seam satisfies all indexed
mark and incidence conditions of the corrected reader. -/
theorem m0GeodesicRightSide_rightReconstructionSeam2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    rightReconstructionSeam2 (m0GeodesicSide hp P .right)
      (m0GeodesicSideSeamVertexCell hp P .right)
      (m0GeodesicSideSeamDartCell hp P .right) := by
  intro n
  exact ⟨rfl, (m0GeodesicSide_seam_directedRay hp P .right n).2.1⟩

/-- Helper toward Lemma 5.6: aligned intrinsic old-seam and next-ray
marks are exactly the source edge-tail agreement, preserving edge identity. -/
theorem m0GeodesicRightSide_seamAgreement_iff_coalescence2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ) :
    geometricSideRaySeamAgreement _
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) b a ↔
      M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b := by
  change (∀ n, ((P (k - 1)).codePath.edge (a + n), false) =
    ((P k).codePath.edge (b + n), false)) ↔
    ∀ n, wholePlaneEdgeι W 0 ((P (k - 1)).codePath.edge (a + n)) =
      wholePlaneEdgeι W 0 ((P k).codePath.edge (b + n))
  constructor
  · intro h n
    exact congrArg (wholePlaneEdgeι W 0) (congrArg Prod.fst (h n))
  · intro h n
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (h n)) rfl

/-- Helper toward Lemma 5.6: the corrected reader's jointly least
intrinsic offsets are exactly the source's two least-coalescence offsets. -/
theorem m0GeodesicRightSide_leastCoalescence_iff_intrinsicSeam2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ) :
    M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b ↔
      geometricSideRaySeamAgreement _
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) b a ∧
      ∀ a' b', geometricSideRaySeamAgreement _
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) b' a' →
        a ≤ a' ∧ b ≤ b' := by
  constructor
  · rintro ⟨ht, hm⟩
    exact ⟨(m0GeodesicRightSide_seamAgreement_iff_coalescence2 hp P T hleft hc k a b).2 ht,
      fun a' b' ht' => hm a' b'
        ((m0GeodesicRightSide_seamAgreement_iff_coalescence2 hp P T hleft hc k a' b').1 ht')⟩
  · rintro ⟨ht, hm⟩
    exact ⟨(m0GeodesicRightSide_seamAgreement_iff_coalescence2 hp P T hleft hc k a b).1 ht,
      fun a' b' ht' => hm a' b'
        ((m0GeodesicRightSide_seamAgreement_iff_coalescence2 hp P T hleft hc k a' b').2 ht')⟩

/-- Helper toward Lemma 5.6: on a retained preceding-right face, the
corrected intrinsic sector test is exactly retention in the next left side.
This uses OPEN R, and requires no left-exhaustion premise. -/
theorem m0GeodesicRightSide_nextLeft_faceNext_iff_sector2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges})
    (hde : (m0GeodesicSide hp (P (k - 1)) .right).faceNext d.val e.val) :
    (m0GeodesicSide hp (P k) .left).faceNext d.val e.val ↔
      (¬ geometricSide_intrinsic_right _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) (.inr d) ∨
      ∃ n, (.inr d : GeometricSideCell _) =
        m0GeodesicRightSideNextDarts hp P T hleft hc k n) := by
  obtain ⟨⟨F, hb, hFR⟩, hsucc⟩ := hde
  have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h := fun z hz => (hFR hz).1
  have hface : (m0GeodesicSide hp (P k) .left).faceNext d.val e.val ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
    constructor
    · rintro ⟨⟨G, hbG, hG⟩, _⟩
      have heq := (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders_face_unique
        (wholePlaneDartι W 0 d.val) G F hbG hb
      exact heq ▸ hG
    · intro hF
      exact ⟨⟨F, hb, hF⟩, hsucc⟩
  rw [hface]
  have hright := m0GeodesicRightSide_intrinsic_right_iff_nextRight hp P T hleft hc k (.inr d)
  change geometricSide_intrinsic_right _ _ _ (.inr d) ↔
    d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right at hright
  constructor
  · intro hFL
    by_cases hR : d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right
    · have hray : d.val.1 ∈ m0GeodesicEdges (P k) := by
        by_contra hoff
        have hFR' := (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp
          (P k) hoff d.val.2 F hFA hb .right).mp hR
        obtain ⟨z, hz, hval⟩ := F.property
        have hzF : z ∈ F.val := hval ▸ mem_connectedComponentIn hz
        exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P k))
          (hFL hzF) (hFR' hzF)
      obtain ⟨n, hn⟩ := hray
      have hi := m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1))
        .left d F hb hFL
      have hbit : d.val.2 = false := by
        cases hd : d.val.2 with
        | false => rfl
        | true => exact False.elim (hi.2 n (Prod.ext hn.symm hd))
      apply Or.inr
      refine ⟨n, congrArg Sum.inr (Subtype.ext ?_)⟩
      exact Prod.ext hn.symm hbit
    · exact Or.inl (fun hr => hR (hright.mp hr))
  · rintro (hnot | ⟨n, hn⟩)
    · obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp (P k) F hFA
      cases s with
      | left => exact hs
      | right =>
        exact False.elim (hnot (hright.mpr
          (m0Geodesic_side_edge_of_bordering_face hp (P k) .right d.val F hs hb)))
    · have hd : d.val = ((P k).codePath.edge n, false) := by
        exact congrArg Subtype.val (Sum.inr.inj hn)
      apply boundaryGluing_forward_seam_face_left W h k longest hp (P k) n F hFA
      simpa only [hd, m0GeodesicSeam] using hb




theorem m0CutGeodesicSlice_faceNext_iff_rightSliceRelation2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges}) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext d.val e.val ↔
      rightSliceRelation2 _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (rightSliceKeep2 _
          (m0GeodesicRightSideNextVertices hp P T hleft hc k)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k)
          (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
          (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b)
        .faceNext (.inr d) (.inr e) := by
  constructor
  · rintro ⟨hpF, hnF⟩
    exact ⟨hpF, (m0GeodesicRightSide_nextLeft_faceNext_iff_sector2
      hp P T hleft hc k d e hpF).mp hnF⟩
  · rintro ⟨hpF, hsector⟩
    exact ⟨hpF, (m0GeodesicRightSide_nextLeft_faceNext_iff_sector2
      hp P T hleft hc k d e hpF).mpr hsector⟩

end DirectedDistances.PaperProofs.Section5























































































































