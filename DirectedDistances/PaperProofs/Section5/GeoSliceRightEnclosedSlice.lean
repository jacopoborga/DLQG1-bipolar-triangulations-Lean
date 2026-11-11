/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReaders3
public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice2

/-! Intrinsic candidates inside the preceding right side. Soundness and the
remaining exhaustion obligations are kept separate from slice reconstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: a retained face on the left of a forward
ray dart is seeded at that dart itself. The successor requirement excludes
corners whose left face is absent from the ambient side. -/
@[expose] def geometricSide_left_face_seed (M : GeometricSideSubmap)
    (d : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  ∃ n, c = d n ∧ ∃ e, geometricSideRelation M .faceNext c e

/-- Helper toward Lemma 5.6: left-face seeds transport by marked isomorphisms. -/
theorem geometricSide_left_face_seed_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_left_face_seed M d c ↔
      geometricSide_left_face_seed N (I.equiv ∘ d) (I.equiv c) := by
  constructor
  · rintro ⟨n, hn, e, he⟩
    exact ⟨n, congrArg I.equiv hn, I.equiv e, (I.relation_iff _ _ _).1 he⟩
  · rintro ⟨n, hn, e, he⟩
    refine ⟨n, I.equiv.injective hn, I.equiv.symm e, ?_⟩
    apply (I.relation_iff _ _ _).2
    simpa only [Equiv.apply_symm_apply] using he

/-- Helper toward Lemma 5.6: the intrinsic closed left candidate consists
of ray vertices, both darts of ray edges, and finite slit chains from retained
left-face seeds. This is a candidate, with exhaustion a separate obligation. -/
@[expose] def geometricSide_intrinsic_left (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (c : GeometricSideCell M) : Prop :=
  geometricSide_ray_vertex M v c ∨ geometricSide_ray_dart M d c ∨
    ∃ a, geometricSide_left_face_seed M d a ∧
      Relation.ReflTransGen (geometricSide_slit_step M v d) a c

/-- Helper toward Lemma 5.6: the complete intrinsic left candidate is
invariant under marked isomorphisms mapping the two ray streams. -/
theorem geometricSide_intrinsic_left_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (c : GeometricSideCell M) :
    geometricSide_intrinsic_left M v d c ↔
      geometricSide_intrinsic_left N (I.equiv ∘ v) (I.equiv ∘ d) (I.equiv c) := by
  rw [geometricSide_intrinsic_left, geometricSide_intrinsic_left,
    ← geometricSide_ray_vertex_map_iff I, ← geometricSide_ray_dart_map_iff I]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨a, ha, hac⟩
    exact ⟨I.equiv a, (geometricSide_left_face_seed_map_iff I d a).1 ha,
      (geometricSide_slit_reaches_map_iff I v d a c).1 hac⟩
  · rintro ⟨a, ha, hac⟩
    refine ⟨I.equiv.symm a, ?_, ?_⟩
    · apply (geometricSide_left_face_seed_map_iff I d _).2
      simpa only [Equiv.apply_symm_apply] using ha
    · apply (geometricSide_slit_reaches_map_iff I v d _ c).2
      simpa only [Equiv.apply_symm_apply] using hac


variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the oriented invariant inside an actual
right side. A left chain excludes reverse ray darts; a right chain excludes
forward ray darts. Ray cells themselves are included separately. -/
@[expose] def m0GeodesicRightSlitInvariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (P : M0CutInfiniteGeodesic W H h hLL j longest) (s : ThinMapSide)
    (c : GeometricSideCell (m0GeodesicSide hp P .right)) : Prop :=
  match c with
  | .inl v => v.val ∈ m0GeodesicSideVertices hp Q s
  | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp Q s ∧
      ∀ n : ℕ, d.val ≠ (Q.codePath.edge n, match s with | .left => true | .right => false)

/-- Helper toward Lemma 5.6: each dart bordering a retained face of
either actual side has the corresponding oriented slit invariant. -/
theorem m0GeodesicRightSide_face_dart_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (P : M0CutInfiniteGeodesic W H h hLL j longest) (s : ThinMapSide)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .right).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (hs : F.val ⊆ m0GeodesicSideOpenRegion hp Q s) :
    m0GeodesicRightSlitInvariant hp Q P s (.inr d) := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
    cases s with
    | left => exact fun _ hz => (m0GeodesicLeftOpen_subset hp Q (hs hz)).1
    | right => exact fun _ hz => (hs hz).1
  constructor
  · by_cases he : d.val.1 ∈ m0GeodesicEdges Q
    · have hboth := m0GeodesicEdges_subset_both hp Q he
      cases s with
      | left => exact hboth.1
      | right => exact hboth.2
    · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
        he d.val.2 F hFR hb s).mpr hs
  · intro n hn
    obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    cases s with
    | left =>
      have hr := m0Geodesic_reverse_seam_face_right hp Q n F hFR
        (by simpa only [hn] using hb)
      exact Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        (hs hzF) (hr hzF)
    | right =>
      have hl := boundaryGluing_forward_seam_face_left W h k longest hp Q n F hFR
        (by simpa only [hn, m0GeodesicSeam] using hb)
      exact Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        (hl hzF) (hs hzF)

/-- Helper toward Lemma 5.6: the oriented invariant determines the side
of every retained face bordering that orientation of a dart. -/
theorem m0GeodesicRightSide_invariant_dart_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (P : M0CutInfiniteGeodesic W H h hLL j longest) (s : ThinMapSide)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .right).edges})
    (hd : m0GeodesicRightSlitInvariant hp Q P s (.inr d))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp Q s := by
  by_cases he : d.val.1 ∈ m0GeodesicEdges Q
  · obtain ⟨n, hn⟩ := he
    cases s with
    | left =>
      have hbool : d.val.2 = false := by
        cases hbit : d.val.2 with
        | false => rfl
        | true => exact False.elim (hd.2 n (Prod.ext hn.symm hbit))
      apply boundaryGluing_forward_seam_face_left W h k longest hp Q n F hFR
      have hv : d.val = (Q.codePath.edge n, false) := Prod.ext hn.symm hbool
      simpa only [hv, m0GeodesicSeam] using hb
    | right =>
      have hbool : d.val.2 = true := by
        cases hbit : d.val.2 with
        | false => exact False.elim (hd.2 n (Prod.ext hn.symm hbit))
        | true => rfl
      apply m0Geodesic_reverse_seam_face_right hp Q n F hFR
      have hv : d.val = (Q.codePath.edge n, true) := Prod.ext hn.symm hbool
      simpa only [hv] using hb
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
      he d.val.2 F hFR hb s).mp hd.1

/-- Helper toward Lemma 5.6: retained face succession inside a right
side preserves either oriented side invariant in both directions. -/
theorem m0GeodesicRightSide_faceNext_invariant_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (P : M0CutInfiniteGeodesic W H h hLL j longest) (s : ThinMapSide)
    {c e : GeometricSideCell (m0GeodesicSide hp P .right)}
    (hce : geometricSideRelation (m0GeodesicSide hp P .right) .faceNext c e) :
    m0GeodesicRightSlitInvariant hp Q P s c ↔
      m0GeodesicRightSlitInvariant hp Q P s e := by
  cases c with
  | inl c => exact False.elim hce
  | inr c =>
    cases e with
    | inl e => exact False.elim hce
    | inr e =>
      obtain ⟨⟨F, hb, hr⟩, hsucc⟩ := hce
      have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := fun _ hz => (hr hz).1
      have hb' := m0Geodesic_retained_face_succ_borders hp F hFR c.val hb
      rw [hsucc] at hb'
      constructor
      · intro hc
        exact m0GeodesicRightSide_face_dart_invariant hp Q P s e F hb'
          (m0GeodesicRightSide_invariant_dart_face hp Q P s c hc F hFR hb)
      · intro he
        exact m0GeodesicRightSide_face_dart_invariant hp Q P s c F hb
          (m0GeodesicRightSide_invariant_dart_face hp Q P s e he F hFR hb')

/-- Helper toward Lemma 5.6: off a ray, the edge's actual side label
agrees with that of either incident vertex, for both sides. -/
theorem m0Geodesic_incident_off_ray_side_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (d : ℕ × Bool) (v : ℕ)
    (hinc : kmswLimitDartVertex (shiftedStream W 0) d = v)
    (hv : v ∉ m0GeodesicVertices Q) :
    d.1 ∉ m0GeodesicEdges Q ∧
      (d.1 ∈ m0GeodesicSideEdges hp Q s ↔ v ∈ m0GeodesicSideVertices hp Q s) := by
  obtain ⟨he, hi⟩ := m0Geodesic_incident_off_ray_right_iff hp Q d v hinc hv
  refine ⟨he, ?_⟩
  cases s with
  | right => exact hi
  | left =>
    have heLR : d.1 ∈ m0GeodesicSideEdges hp Q .left ↔
        d.1 ∉ m0GeodesicSideEdges hp Q .right := by
      constructor
      · intro hl hr
        apply he
        rw [← boundaryGluing_m0SideEdges_inter W h k longest hp Q]
        exact ⟨hl, hr⟩
      · intro hr
        exact (m0GeodesicSideEdges_cover hp Q d.1).resolve_right hr
    have hvLR : v ∈ m0GeodesicSideVertices hp Q .left ↔
        v ∉ m0GeodesicSideVertices hp Q .right := by
      constructor
      · intro hl hr
        apply hv
        rw [← m0GeodesicSideVertices_inter hp Q]
        exact ⟨hl, hr⟩
      · intro hr
        exact (m0GeodesicSideVertices_cover hp Q v).resolve_right hr
    exact heLR.trans ((not_congr hi).trans hvLR.symm)


section AdjacentRay
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
  (hcontain : ∀ n : ℕ,
    (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
    ((P k).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P (k - 1)) .right).vertices)

/-- Helper toward Lemma 5.6: intrinsic ray vertices inside the preceding
right side are exactly the geometric vertices of the next ray. -/
theorem m0GeodesicRightSide_ray_vertex_iff
    (v : (m0GeodesicSide hp (P (k - 1)) .right).vertices) :
    geometricSide_ray_vertex (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain) (.inl v) ↔
      v.val ∈ m0GeodesicVertices (P k) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg Subtype.val (Sum.inl.inj hn)).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg Sum.inl (Subtype.ext hn.symm)⟩

/-- Helper toward Lemma 5.6: both orientations of exactly the next
ray's geometric edges are slit darts inside the preceding right side. -/
theorem m0GeodesicRightSide_ray_dart_iff
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges}) :
    geometricSide_ray_dart (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) (.inr d) ↔
      d.val.1 ∈ m0GeodesicEdges (P k) := by
  constructor
  · rintro ⟨n, hn | hn⟩
    · exact ⟨n, (congrArg (fun c => c.1) (congrArg Subtype.val
        (Sum.inr.inj hn))).symm⟩
    · exact ⟨n, congrArg Prod.fst hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    cases hb : d.val.2 with
    | false => exact Or.inl (congrArg Sum.inr (Subtype.ext (Prod.ext hn.symm hb)))
    | true => exact Or.inr (Prod.ext hn hb.symm)

/-- Helper toward Lemma 5.6: a slit step inside the preceding right side
preserves the actual side label and excluded ray orientation. -/
theorem m0GeodesicRightSide_slit_step_invariant (s : ThinMapSide)
    {c e : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (hstep : geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c e)
    (hc : m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) s c) :
    m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) s e := by
  rcases hstep with hce | hec | ⟨hopp, hoff⟩ | ⟨hinc, hoff⟩ | ⟨hinc, hoff⟩
  · exact (m0GeodesicRightSide_faceNext_invariant_iff hp (P k) (P (k - 1)) s hce).mp hc
  · exact (m0GeodesicRightSide_faceNext_invariant_iff hp (P k) (P (k - 1)) s hec).mpr hc
  · cases c with
    | inl c => exact False.elim hopp
    | inr c =>
      cases e with
      | inl e => exact False.elim hopp
      | inr e =>
        change (c.val.1, !c.val.2) = e.val at hopp
        have heq := congrArg (fun z : ℕ × Bool => z.1) hopp
        change c.val.1 = e.val.1 at heq
        have hcoff : c.val.1 ∉ m0GeodesicEdges (P k) :=
          fun he => hoff ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain c).mpr he)
        constructor
        · exact heq ▸ hc.1
        · intro n hn
          exact hcoff ⟨n, (congrArg Prod.fst hn).symm.trans heq.symm⟩
  · cases c with
    | inl c => exact False.elim hinc
    | inr c =>
      cases e with
      | inr e => exact False.elim hinc
      | inl e =>
        have heoff : e.val ∉ m0GeodesicVertices (P k) :=
          fun he => hoff ((m0GeodesicRightSide_ray_vertex_iff hp P k hcontain e).mpr he)
        change kmswLimitDartVertex (shiftedStream W 0) c.val = e.val at hinc
        exact (m0Geodesic_incident_off_ray_side_iff hp (P k) s
          c.val e.val hinc heoff).2.mp hc.1
  · cases c with
    | inr c => cases e <;> exact False.elim hinc
    | inl c =>
      cases e with
      | inl e => exact False.elim hinc
      | inr e =>
        have hcoff : c.val ∉ m0GeodesicVertices (P k) :=
          fun hv => hoff ((m0GeodesicRightSide_ray_vertex_iff hp P k hcontain c).mpr hv)
        change kmswLimitDartVertex (shiftedStream W 0) e.val = c.val at hinc
        obtain ⟨heoff, hi⟩ := m0Geodesic_incident_off_ray_side_iff hp (P k) s
          e.val c.val hinc hcoff
        refine ⟨hi.mpr hc, ?_⟩
        intro n hn
        exact heoff ⟨n, (congrArg Prod.fst hn).symm⟩

/-- Helper toward Lemma 5.6: retained left seeds satisfy the left invariant. -/
theorem m0GeodesicRightSide_left_face_seed_invariant
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hc : geometricSide_left_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c) :
    m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) .left c := by
  obtain ⟨n, rfl, e, he⟩ := hc
  cases e with
  | inl e => exact False.elim he
  | inr e =>
    obtain ⟨⟨F, hb, hr⟩, _⟩ := he
    have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := fun _ hz => (hr hz).1
    apply m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .left _ F hb
    exact boundaryGluing_forward_seam_face_left W h k longest hp (P k) n F hFR hb

/-- Helper toward Lemma 5.6: retained right seeds satisfy the right invariant. -/
theorem m0GeodesicRightSide_right_face_seed_invariant
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hc : geometricSide_right_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c) :
    m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) .right c := by
  cases c with
  | inl c => obtain ⟨n, hn, _⟩ := hc; exact False.elim hn
  | inr c =>
    obtain ⟨n, hn, e, he⟩ := hc
    cases e with
    | inl e => exact False.elim he
    | inr e =>
      obtain ⟨⟨F, hb, hr⟩, _⟩ := he
      have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := fun _ hz => (hr hz).1
      apply m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .right c F hb
      apply m0Geodesic_reverse_seam_face_right hp (P k) n F hFR
      change ((P k).codePath.edge n, true) = c.val at hn
      simpa only [← hn] using hb

/-- Helper toward Lemma 5.6: finite slit chains propagate either oriented
invariant from their starting cell, without a connectivity premise. -/
theorem m0GeodesicRightSide_slit_reaches_invariant (s : ThinMapSide)
    {a c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (ha : m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) s a)
    (hac : Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain)) a c) :
    m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) s c := by
  induction hac with
  | refl => exact ha
  | tail _ hstep ih =>
    exact m0GeodesicRightSide_slit_step_invariant hp P k hcontain s hstep ih

/-- Helper toward Lemma 5.6: the intrinsic left candidate is sound for
the actual left side of the next ray, inside the preceding right side. -/
theorem m0GeodesicRightSide_intrinsic_left_sound
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hc : geometricSide_intrinsic_left (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c) :
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left := by
  rcases hc with hv | hd | ⟨a, ha, hac⟩
  · obtain ⟨n, rfl⟩ := hv
    exact (show ((P k).codePath.initial n).1.id ∈
      m0GeodesicSideVertices hp (P k) .left ∩
        m0GeodesicSideVertices hp (P k) .right from
          (m0GeodesicSideVertices_inter hp (P k)).symm ▸
            m0Geodesic_initial_mem_vertices (P k) n).1
  · cases c with
    | inl c =>
      obtain ⟨n, hn | hn⟩ := hd
      · exact False.elim (Sum.inl_ne_inr hn)
      · exact False.elim hn
    | inr c =>
      exact (m0GeodesicEdges_subset_both hp (P k)
        ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain c).mp hd)).1
  · have hi := m0GeodesicRightSide_slit_reaches_invariant hp P k hcontain .left
      (m0GeodesicRightSide_left_face_seed_invariant hp P k hcontain a ha) hac
    cases c with
    | inl c => exact hi
    | inr c => exact hi.1

/-- Helper toward Lemma 5.6: the existing intrinsic right candidate is
sound for the actual right side of the next ray, inside the preceding right side. -/
theorem m0GeodesicRightSide_intrinsic_right_sound
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hc : geometricSide_intrinsic_right (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c) :
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right := by
  rcases hc with hv | hd | ⟨a, ha, hac⟩
  · obtain ⟨n, rfl⟩ := hv
    exact m0GeodesicVertices_subset_right hp (P k) (m0Geodesic_initial_mem_vertices (P k) n)
  · cases c with
    | inl c =>
      obtain ⟨n, hn | hn⟩ := hd
      · exact False.elim (Sum.inl_ne_inr hn)
      · exact False.elim hn
    | inr c =>
      exact m0GeodesicEdges_subset_right hp (P k)
        ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain c).mp hd)
  · have hi := m0GeodesicRightSide_slit_reaches_invariant hp P k hcontain .right
      (m0GeodesicRightSide_right_face_seed_invariant hp P k hcontain a ha) hac
    cases c with
    | inl c => exact hi
    | inr c => exact hi.1

end AdjacentRay

/-- Helper toward Lemma 5.6: the source's strict vertex and weak edge
tail deletions, now on cells of the preceding right side. -/
@[expose] def m0GeodesicRightSideDeletedTailCells
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    Set (GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :=
  {c | match c with
    | .inl u =>
      (∃ n, a < n ∧ u.val = ((P (k - 1)).codePath.initial n).1.id) ∨
        ∃ n, b < n ∧ u.val = ((P k).codePath.initial n).1.id
    | .inr e =>
      e.val.1 ∈ Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n))}

/-- Helper toward Lemma 5.6: tail deletion inside the preceding right
side is the union of the old seam's and next ray's intrinsic deletion sets. -/
theorem m0GeodesicRightSideDeletedTailCells_eq
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
      ((P k).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P (k - 1)) .right).vertices)
    (a b : ℕ) :
    m0GeodesicRightSideDeletedTailCells hp P k a b =
      geometricSideRayDeletedTailCells _
        (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
        (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a ∪
      geometricSideRayDeletedTailCells _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) b := by
  ext c
  have hprev := geometricSideRayDeletedTailCells_mem_iff
    (m0GeodesicSide hp (P (k - 1)) .right)
    (fun n => ⟨((P (k - 1)).codePath.initial n).1.id,
      m0GeodesicVertices_subset_right hp (P (k - 1))
        (m0Geodesic_initial_mem_vertices (P (k - 1)) n)⟩)
    (P (k - 1)).codePath.edge (fun n =>
      m0GeodesicEdges_subset_right hp (P (k - 1)) (m0GeodesicSeam_mem_edges (P (k - 1)) n))
    a c
  have hcurr := geometricSideRayDeletedTailCells_mem_iff
    (m0GeodesicSide hp (P (k - 1)) .right)
    (fun n => ⟨((P k).codePath.initial n).1.id, (hcontain n).2⟩)
    (P k).codePath.edge (fun n => (hcontain n).1) b c
  change c ∈ geometricSideRayDeletedTailCells _
    (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
    (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a ↔ _ at hprev
  change c ∈ geometricSideRayDeletedTailCells _
    (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
    (m0GeodesicRightSideAdjacentDarts hp P k hcontain) b ↔ _ at hcurr
  change _ ↔ _ ∨ _
  rw [hprev, hcurr]
  cases c <;> rfl

/-- Helper toward Lemma 5.6: actual slice membership inside the preceding
right side is next-left membership and survival of the two source tails. -/
theorem m0CutGeodesicSlice_mem_cell_iff_nextLeft_and_not_deletedTail
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    (match c with
     | .inl v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
     | .inr d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) ↔
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) ∧
        c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b := by
  cases c with
  | inl v =>
    change ((v.val ∈ _ ∧ v.val ∈ _) ∧ ¬ _) ↔ _
    exact ⟨fun hv => ⟨hv.1.2, hv.2⟩, fun hv => ⟨⟨v.property, hv.1⟩, hv.2⟩⟩
  | inr d =>
    change ((d.val.1 ∈ _ ∧ d.val.1 ∈ _) ∧ ¬ _) ↔ _
    exact ⟨fun hd => ⟨hd.1.2, hd.2⟩, fun hd => ⟨⟨d.property, hd.1⟩, hd.2⟩⟩

section ExhaustionReductions
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
  (hcontain : ∀ n : ℕ,
    (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
    ((P k).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P (k - 1)) .right).vertices)

/-- Helper toward Lemma 5.6: reduction of the next-right characterization
to the explicitly displayed off-ray exhaustion. This lemma does not prove
exhaustion and is not an unconditional source characterization. -/
theorem m0GeodesicRightSide_intrinsic_right_reduction_of_exhaustion
    (hExhaust : ∀ c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right) →
      ¬ geometricSide_ray_vertex _ (m0GeodesicRightSideAdjacentVertices hp P k hcontain) c →
      ¬ geometricSide_ray_dart _ (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c →
      ∃ a, geometricSide_right_face_seed _
          (m0GeodesicRightSideAdjacentDarts hp P k hcontain) a ∧
        Relation.ReflTransGen
          (geometricSide_slit_step _
            (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
            (m0GeodesicRightSideAdjacentDarts hp P k hcontain)) a c)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    geometricSide_intrinsic_right _
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right := by
  constructor
  · intro hc
    cases c <;> exact m0GeodesicRightSide_intrinsic_right_sound hp P k hcontain _ hc
  · intro hc
    by_cases hv : geometricSide_ray_vertex _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain) c
    · exact Or.inl hv
    by_cases hd : geometricSide_ray_dart _
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c
    · exact Or.inr (Or.inl hd)
    exact Or.inr (Or.inr (hExhaust c hc hv hd))

/-- Helper toward Lemma 5.6: reduction of slice membership to exhaustion
only for surviving off-ray next-left cells. The tails retain their exact
strict-vertex and weak-edge conventions, including zero offsets. -/
theorem m0GeodesicRightSide_slice_reduction_of_exhaustion
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (hExhaust : ∀ c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) →
      c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b →
      ¬ geometricSide_ray_vertex _ (m0GeodesicRightSideAdjacentVertices hp P k hcontain) c →
      ¬ geometricSide_ray_dart _ (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c →
      ∃ q, geometricSide_left_face_seed _
          (m0GeodesicRightSideAdjacentDarts hp P k hcontain) q ∧
        Relation.ReflTransGen
          (geometricSide_slit_step _
            (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
            (m0GeodesicRightSideAdjacentDarts hp P k hcontain)) q c)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    (match c with
     | .inl v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
     | .inr d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) ↔
      geometricSide_intrinsic_left _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c ∧
      c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b := by
  rw [m0CutGeodesicSlice_mem_cell_iff_nextLeft_and_not_deletedTail hp P k a b hab c]
  constructor
  · rintro ⟨hc, htail⟩
    refine ⟨?_, htail⟩
    by_cases hv : geometricSide_ray_vertex _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain) c
    · exact Or.inl hv
    by_cases hd : geometricSide_ray_dart _
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c
    · exact Or.inr (Or.inl hd)
    exact Or.inr (Or.inr (hExhaust c hc htail hv hd))
  · rintro ⟨hc, htail⟩
    refine ⟨?_, htail⟩
    cases c <;> exact m0GeodesicRightSide_intrinsic_left_sound hp P k hcontain _ hc

end ExhaustionReductions

section Separation
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
  (hcontain : ∀ n : ℕ,
    (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
    ((P k).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P (k - 1)) .right).vertices)

/-- Helper toward Lemma 5.6: the two sound candidates intersect exactly
on the ray's vertex and geometric dart cells, even before exhaustion. -/
theorem m0GeodesicRightSide_intrinsic_left_and_right_iff_ray
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    (geometricSide_intrinsic_left _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c ∧
      geometricSide_intrinsic_right _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c) ↔
      geometricSide_ray_vertex _ (m0GeodesicRightSideAdjacentVertices hp P k hcontain) c ∨
      geometricSide_ray_dart _ (m0GeodesicRightSideAdjacentDarts hp P k hcontain) c := by
  constructor
  · rintro ⟨hl, hr⟩
    have hleft := m0GeodesicRightSide_intrinsic_left_sound hp P k hcontain c hl
    have hright := m0GeodesicRightSide_intrinsic_right_sound hp P k hcontain c hr
    cases c with
    | inl v =>
      apply Or.inl
      apply (m0GeodesicRightSide_ray_vertex_iff hp P k hcontain v).mpr
      rw [← m0GeodesicSideVertices_inter hp (P k)]
      exact ⟨hleft, hright⟩
    | inr d =>
      apply Or.inr
      apply (m0GeodesicRightSide_ray_dart_iff hp P k hcontain d).mpr
      rw [← boundaryGluing_m0SideEdges_inter W h k longest hp (P k)]
      exact ⟨hleft, hright⟩
  · rintro (hv | hd)
    · exact ⟨Or.inl hv, Or.inl hv⟩
    · exact ⟨Or.inr (Or.inl hd), Or.inr (Or.inl hd)⟩

/-- Helper toward Lemma 5.6: no chain from a retained left-face seed
reaches a reverse ray dart; these cells enter the closed candidate separately. -/
theorem m0GeodesicRightSide_left_seed_not_reaches_reverse_ray_dart
    {a : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (ha : geometricSide_left_face_seed _
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) a) (n : ℕ) :
    ¬ Relation.ReflTransGen
      (geometricSide_slit_step _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain)) a
      (.inr ⟨((P k).codePath.edge n, true), (hcontain n).1⟩) := by
  intro hac
  have hi := m0GeodesicRightSide_slit_reaches_invariant hp P k hcontain .left
    (m0GeodesicRightSide_left_face_seed_invariant hp P k hcontain a ha) hac
  exact hi.2 n rfl

/-- Helper toward Lemma 5.6: no chain from a retained right-face seed
reaches a forward ray dart; these cells enter the closed candidate separately. -/
theorem m0GeodesicRightSide_right_seed_not_reaches_forward_ray_dart
    {a : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (ha : geometricSide_right_face_seed _
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) a) (n : ℕ) :
    ¬ Relation.ReflTransGen
      (geometricSide_slit_step _
        (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
        (m0GeodesicRightSideAdjacentDarts hp P k hcontain)) a
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain n) := by
  intro hac
  have hi := m0GeodesicRightSide_slit_reaches_invariant hp P k hcontain .right
    (m0GeodesicRightSide_right_face_seed_invariant hp P k hcontain a ha) hac
  exact hi.2 n rfl

end Separation

section TwoSourceRealizations
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
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k, Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ, M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (hc' : ∀ m : ℤ, ∃ a b : ℕ, M0CutLeastEdgeCoalescence (P' m) (P' (m + 1)) a b)
  (k l : ℤ)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P (k - 1)) .right)
    (m0GeodesicSide hp' (P' (l - 1)) .right))

/-- Helper toward Lemma 5.6: a marked isomorphism between source right
sides transports the entire next ray, by the corrected intrinsic selector's
proved source identification and uniqueness. No ray-mapping premise is added. -/
theorem m0GeodesicRightSide_markedIso_map_nextRay :
    I.equiv ∘ m0GeodesicRightSideNextVertices hp P T hleft hc k =
      m0GeodesicRightSideNextVertices hp' P' T' hleft' hc' l ∧
    I.equiv ∘ m0GeodesicRightSideNextDarts hp P T hleft hc k =
      m0GeodesicRightSideNextDarts hp' P' T' hleft' hc' l := by
  exact m0GeodesicRightSide_intrinsicRightRay_eq_realizedNext hp' P' T' hleft' hc' l
    (intrinsicallyLeftmostAdjacentRightRay_map I longest
      (m0GeodesicRightSide_nextRay_is_intrinsicallyLeftmostRight hp P T hleft hc k))

/-- Helper toward Lemma 5.6: the intrinsic left candidate for the actual
next source ray transports under a marked isomorphism of preceding right sides. -/
theorem m0GeodesicRightSide_markedIso_intrinsic_left_iff
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    geometricSide_intrinsic_left _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ↔
    geometricSide_intrinsic_left _
      (m0GeodesicRightSideNextVertices hp' P' T' hleft' hc' l)
      (m0GeodesicRightSideNextDarts hp' P' T' hleft' hc' l) (I.equiv c) := by
  obtain ⟨hv, hd⟩ := m0GeodesicRightSide_markedIso_map_nextRay
    hp hp' P P' T T' hleft hleft' hc hc' k l I
  have hm := geometricSide_intrinsic_left_map_iff I
    (m0GeodesicRightSideNextVertices hp P T hleft hc k)
    (m0GeodesicRightSideNextDarts hp P T hleft hc k) c
  rw [hv, hd] at hm
  exact hm

/-- Helper toward Lemma 5.6: the reused intrinsic right candidate for
the next source ray also transports, without a geometric exhaustion premise. -/
theorem m0GeodesicRightSide_markedIso_intrinsic_right_iff
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    geometricSide_intrinsic_right _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ↔
    geometricSide_intrinsic_right _
      (m0GeodesicRightSideNextVertices hp' P' T' hleft' hc' l)
      (m0GeodesicRightSideNextDarts hp' P' T' hleft' hc' l) (I.equiv c) := by
  obtain ⟨hv, hd⟩ := m0GeodesicRightSide_markedIso_map_nextRay
    hp hp' P P' T T' hleft hleft' hc hc' k l I
  have hm := geometricSide_intrinsic_right_map_iff I
    (m0GeodesicRightSideNextVertices hp P T hleft hc k)
    (m0GeodesicRightSideNextDarts hp P T hleft hc k) c
  rw [hv, hd] at hm
  exact hm


/-- Helper toward Lemma 5.6: every indexed old seam dart transports
under the right-side marked isomorphism. -/
theorem m0GeodesicRightSide_markedIso_map_seamDart (n : ℕ) :
    I.equiv (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right n) =
      m0GeodesicSideSeamDartCell hp' (P' (l - 1)) .right n := by
  apply geometricSideRelation_seam_self_unique _ n
  · exact (I.relation_iff _ _ _).1 (show geometricSideRelation
      (m0GeodesicSide hp (P (k - 1)) .right) (.seam n)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right n)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right n) from rfl)
  · rfl

/-- Helper toward Lemma 5.6: every indexed old seam vertex transports
by incidence with its transported forward seam dart. -/
theorem m0GeodesicRightSide_markedIso_map_seamVertex (n : ℕ) :
    I.equiv (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right n) =
      m0GeodesicSideSeamVertexCell hp' (P' (l - 1)) .right n := by
  apply geometricSideRelation_incident_right_unique _
    (a := m0GeodesicSideSeamDartCell hp' (P' (l - 1)) .right n)
  · have hi := (I.relation_iff _ _ _).1
      ((m0GeodesicSide_seam_directedRay hp (P (k - 1)) .right n).2.1)
    rw [m0GeodesicRightSide_markedIso_map_seamDart hp hp' P P' k l I n] at hi
    exact hi
  · exact (m0GeodesicSide_seam_directedRay hp' (P' (l - 1)) .right n).2.1

include T T' hleft hleft' hc hc' in
/-- Helper toward Lemma 5.6: both common-tail deletion tests transport
between source right sides, with the same arbitrary pair of offsets. -/
theorem m0GeodesicRightSide_markedIso_deletedTailCells_iff
    (a b : ℕ) (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    c ∈ m0GeodesicRightSideDeletedTailCells hp P k a b ↔
      I.equiv c ∈ m0GeodesicRightSideDeletedTailCells hp' P' l a b := by
  obtain ⟨hv, hd⟩ := m0GeodesicRightSide_markedIso_map_nextRay
    hp hp' P P' T T' hleft hleft' hc hc' k l I
  have hsv : I.equiv ∘ m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right =
      m0GeodesicSideSeamVertexCell hp' (P' (l - 1)) .right := by
    funext n
    exact m0GeodesicRightSide_markedIso_map_seamVertex hp hp' P P' k l I n
  have hsd : I.equiv ∘ m0GeodesicSideSeamDartCell hp (P (k - 1)) .right =
      m0GeodesicSideSeamDartCell hp' (P' (l - 1)) .right := by
    funext n
    exact m0GeodesicRightSide_markedIso_map_seamDart hp hp' P P' k l I n
  rw [m0GeodesicRightSideDeletedTailCells_eq hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k),
    m0GeodesicRightSideDeletedTailCells_eq hp' P' l
      (m0GeodesicRightSide_nextRay_contained hp' P' T' hleft' hc' l)]
  change (_ ∨ _) ↔ (_ ∨ _)
  have hprev := geometricSideRayDeletedTailCells_map_iff I
    (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
    (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a c
  have hcurr := geometricSideRayDeletedTailCells_map_iff I
    (m0GeodesicRightSideNextVertices hp P T hleft hc k)
    (m0GeodesicRightSideNextDarts hp P T hleft hc k) b c
  rw [hsv, hsd] at hprev
  rw [hv, hd] at hcurr
  exact or_congr hprev hcurr

/-- Helper toward Lemma 5.6: the intrinsic slice candidate, comprising
next-left cells surviving both tails, transports between source right sides.
Agreement with the actual slice remains the displayed exhaustion reduction. -/
theorem m0GeodesicRightSide_markedIso_intrinsic_survivor_iff
    (a b : ℕ) (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    (geometricSide_intrinsic_left _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ∧
      c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b) ↔
    (geometricSide_intrinsic_left _
        (m0GeodesicRightSideNextVertices hp' P' T' hleft' hc' l)
        (m0GeodesicRightSideNextDarts hp' P' T' hleft' hc' l) (I.equiv c) ∧
      I.equiv c ∉ m0GeodesicRightSideDeletedTailCells hp' P' l a b) :=
  and_congr (m0GeodesicRightSide_markedIso_intrinsic_left_iff
    hp hp' P P' T T' hleft hleft' hc hc' k l I c)
    (not_congr (m0GeodesicRightSide_markedIso_deletedTailCells_iff
      hp hp' P P' T T' hleft hleft' hc hc' k l I a b c))

end TwoSourceRealizations

/-- Helper toward Lemma 5.6: both soundness assertions for the actual
source next ray, with containment discharged by the proved nesting theorem. -/
theorem m0GeodesicRightSide_source_intrinsic_candidates_sound
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ, M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    (geometricSide_intrinsic_left _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c →
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) ∧
    (geometricSide_intrinsic_right _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c →
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right) := by
  constructor
  · intro hleftCell
    cases c <;> exact m0GeodesicRightSide_intrinsic_left_sound hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) _ hleftCell
  · intro hrightCell
    cases c <;> exact m0GeodesicRightSide_intrinsic_right_sound hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) _ hrightCell

end DirectedDistances.PaperProofs.Section5














































































































/- local declarations, including all four definitions, compiled with exit 0.
Every transitive axiom set was contained in {propext, Classical.choice,
Quot.sound}; no placeholder or custom axiom occurred. The probes were removed
kernel validation remain with the sole coordinator. -/
