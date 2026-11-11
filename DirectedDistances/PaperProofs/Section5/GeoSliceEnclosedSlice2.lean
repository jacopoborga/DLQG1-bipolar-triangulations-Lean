/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice

/-! Soundness of intrinsic slit chains in the geometric preceding right side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: a glued face retained in the future region
is a bounded run-zero face, rather than a transferred past face. -/
theorem m0Geodesic_retained_face_runZero
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    ∃ F0 : (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).Face,
      ¬ (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).IsUnbounded F0 ∧
      F.val = F0.val := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h hp H F with
    hf | ⟨Fp, hFp, hval⟩
  · exact hf
  · obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    have hbelow := PastFacesLower.image_boundedFace_subset_lower W h hp H Fp hFp
      (hval ▸ hzF)
    have habove := hFR hzF
    change z.im < seamFun (shiftedStream W 0) h (H.1 0) z.re at hbelow
    change seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im at habove
    exact False.elim (not_lt_of_ge habove hbelow)

/-- Helper toward Lemma 5.6: retained run-zero face succession preserves
the actual bordering face, including at geometric boundary edges. -/
theorem m0Geodesic_retained_face_succ_borders
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h) (d : ℕ × Bool)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d) F) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) F := by
  obtain ⟨F0, hF0, hval⟩ := m0Geodesic_retained_face_runZero hp F hFR
  have hb0 := (PLDrawing.dartBorders_congr _ _ F0 F
    (WholePlanePastGlueM0Restriction.restrict_arc W h hp H d) hval).mp hb
  obtain ⟨j, hj⟩ := (boundedFace_iff_creation_orbit (shiftedStream W 0)
    (H.1 0) h F0).mp hF0
  have hd : d ∈ stageTriangleDartList (shiftedStream W 0) j :=
    (cap_border_iff (shiftedStream W 0) (H.1 0) j d).mp (hj ▸ hb0)
  have hb' := WholePlaneGlueFaceCorrespondenceFull.faceSucc_dartBorders
    W h hp H (wholePlaneDartι W 0 d) F hb
  rw [wholePlaneFaceSucc_run_of_triangle W H 0 d ⟨j, hd⟩] at hb'
  exact hb'

/-- Helper toward Lemma 5.6: the induction invariant retains the
geometric right-side label and excludes the forward ray dart. Excluding
that orientation prevents a face step from entering the left face at a slit. -/
@[expose] def m0GeodesicSlitRightInvariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (c : GeometricSideCell (m0GeodesicSide hp P .left)) : Prop :=
  match c with
  | .inl v => v.val ∈ m0GeodesicSideVertices hp Q .right
  | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp Q .right ∧
      ∀ n : ℕ, d.val ≠ (Q.codePath.edge n, false)

/-- Helper toward Lemma 5.6: every dart bordering a retained right face
has the right-side edge label and cannot be a forward dart of the slit ray. -/
theorem m0Geodesic_right_face_dart_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (hr : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    m0GeodesicSlitRightInvariant hp Q P (.inr d) := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := fun _ hz => (hr hz).1
  constructor
  · by_cases he : d.val.1 ∈ m0GeodesicEdges Q
    · exact m0GeodesicEdges_subset_right hp Q he
    · exact (boundaryGluing_sideEdges_iff_borderingFace W h j longest hp Q
        he d.val.2 F hFR hb .right).mpr hr
  · intro n hn
    have hl := boundaryGluing_forward_seam_face_left W h j longest hp Q n F hFR
      (by simpa only [hn, m0GeodesicSeam] using hb)
    obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    exact Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
      (hl hzF) (hr hzF)

/-- Helper toward Lemma 5.6: the dart invariant gives the right label
to every retained face bordering that orientation of the dart. -/
theorem m0Geodesic_invariant_dart_face_right
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges})
    (hd : m0GeodesicSlitRightInvariant hp Q P (.inr d))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp Q .right := by
  by_cases he : d.val.1 ∈ m0GeodesicEdges Q
  · obtain ⟨n, hn⟩ := he
    have hbool : d.val.2 = true := by
      cases hb : d.val.2 with
      | false => exact False.elim (hd.2 n (Prod.ext hn.symm hb))
      | true => rfl
    apply m0Geodesic_reverse_seam_face_right hp Q n F hFR
    have hdval : d.val = (Q.codePath.edge n, true) := Prod.ext hn.symm hbool
    simpa only [hdval] using hb
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h j longest hp Q
      he d.val.2 F hFR hb .right).mp hd.1

/-- Helper toward Lemma 5.6: a retained face step preserves the stronger
oriented invariant in both directions, even when its edge lies on the slit. -/
theorem m0Geodesic_faceNext_right_invariant_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {c e : GeometricSideCell (m0GeodesicSide hp P .left)}
    (hce : geometricSideRelation (m0GeodesicSide hp P .left) .faceNext c e) :
    m0GeodesicSlitRightInvariant hp Q P c ↔
      m0GeodesicSlitRightInvariant hp Q P e := by
  cases c with
  | inl c => exact False.elim hce
  | inr c =>
    cases e with
    | inl e => exact False.elim hce
    | inr e =>
      obtain ⟨⟨F, hb, hl⟩, hsucc⟩ := hce
      have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h :=
        fun _ hz => (m0GeodesicLeftOpen_subset hp P (hl hz)).1
      have hb' := m0Geodesic_retained_face_succ_borders hp F hFR c.val hb
      rw [hsucc] at hb'
      constructor
      · intro hc
        exact m0Geodesic_right_face_dart_invariant hp Q P e F hb'
          (m0Geodesic_invariant_dart_face_right hp Q P c hc F hFR hb)
      · intro he
        exact m0Geodesic_right_face_dart_invariant hp Q P c F hb
          (m0Geodesic_invariant_dart_face_right hp Q P e he F hFR hb')

/-- Helper toward Lemma 5.6: the intrinsic ray-vertex test has exactly
the original geometric ray vertex IDs. -/
theorem m0GeodesicLeftSide_ray_vertex_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (v : (m0GeodesicSide hp (P k) .left).vertices) :
    geometricSide_ray_vertex (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain) (.inl v) ↔
      v.val ∈ m0GeodesicVertices (P (k - 1)) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg Subtype.val (Sum.inl.inj hn)).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg Sum.inl (Subtype.ext hn.symm)⟩

/-- Helper toward Lemma 5.6: the slit removes both darts of exactly the
geometric ray edges, preserving individual edge identities. -/
theorem m0GeodesicLeftSide_ray_dart_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) :
    geometricSide_ray_dart (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inr d) ↔
      d.val.1 ∈ m0GeodesicEdges (P (k - 1)) := by
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

/-- Helper toward Lemma 5.6: the endpoint selected by either orientation
of a geometric dart belongs to its forward geometric arc. -/
theorem m0Geodesic_dart_vertex_mem_arc
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (d : ℕ × Bool) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) d)) ∈
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (d.1, false))).image := by
  rcases d with ⟨e, b⟩
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hs : (G.arc (wholePlaneDartι W 0 (e, b))).start =
      G.pos (wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) (e, b))) :=
    (G.arc_start _).trans (congrArg G.pos (wholePlaneDartVertex_ι W 0 (e, b)))
  have hm : (G.arc (wholePlaneDartι W 0 (e, b))).start ∈
      (G.arc (wholePlaneDartι W 0 (e, b))).image := Or.inl rfl
  rw [hs] at hm
  cases b with
  | false => exact hm
  | true =>
    have hf := G.arc_flip (wholePlaneDartι W 0 (e, false))
    change G.arc (wholePlaneDartι W 0 (e, true)) = _ at hf
    rw [hf, Polyline.image_reverse_transfer] at hm
    exact hm

/-- Helper toward Lemma 5.6: at a vertex outside the ray, the incident
edge has the right-side label exactly when that vertex does. -/
theorem m0Geodesic_incident_off_ray_right_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (d : ℕ × Bool) (v : ℕ)
    (hinc : kmswLimitDartVertex (shiftedStream W 0) d = v)
    (hv : v ∉ m0GeodesicVertices Q) :
    d.1 ∉ m0GeodesicEdges Q ∧
      (d.1 ∈ m0GeodesicSideEdges hp Q .right ↔
        v ∈ m0GeodesicSideVertices hp Q .right) := by
  let q := (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    (wholePlaneVertexι W 0 v)
  have hq : q ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (d.1, false))).image := by
    simpa only [hinc] using m0Geodesic_dart_vertex_mem_arc hp d
  have hqP : q ∉ m0GeodesicTrace hp Q :=
    fun hqP => hv ((m0Geodesic_pos_mem_trace_iff hp Q v).mp hqP)
  have he : d.1 ∉ m0GeodesicEdges Q := by
    rintro ⟨n, hn⟩
    apply hqP
    apply m0Geodesic_arc_subset_trace hp Q n
    simpa only [hn, m0GeodesicSeam] using hq
  refine ⟨he, ?_⟩
  have hi := (boundaryGluing_sideEdges_iff_off_trace_point W h j longest hp Q
    he hq hqP).2
  constructor
  · intro heR
    exact ⟨m0Geodesic_pos_mem_ambient hp v, hi.mp heR⟩
  · intro hvR
    exact hi.mpr hvR.2

/-- Helper toward Lemma 5.6: one intrinsic slit step preserves the
oriented geometric right-side invariant. The incidence cases use the
actual component at an off-ray vertex, not an assumed slice connectivity. -/
theorem m0GeodesicLeftSide_slit_step_right_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {c e : GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hstep : geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c e)
    (hc : m0GeodesicSlitRightInvariant hp (P (k - 1)) (P k) c) :
    m0GeodesicSlitRightInvariant hp (P (k - 1)) (P k) e := by
  rcases hstep with hce | hec | ⟨hopp, hoff⟩ | ⟨hinc, hoff⟩ | ⟨hinc, hoff⟩
  · exact (m0Geodesic_faceNext_right_invariant_iff hp (P (k - 1)) (P k) hce).mp hc
  · exact (m0Geodesic_faceNext_right_invariant_iff hp (P (k - 1)) (P k) hec).mpr hc
  · cases c with
    | inl c => exact False.elim hopp
    | inr c =>
      cases e with
      | inl e => exact False.elim hopp
      | inr e =>
        change (c.val.1, !c.val.2) = e.val at hopp
        have heq := congrArg (fun z : ℕ × Bool => z.1) hopp
        change c.val.1 = e.val.1 at heq
        have hcoff : c.val.1 ∉ m0GeodesicEdges (P (k - 1)) :=
          fun he => hoff ((m0GeodesicLeftSide_ray_dart_iff hp P k hcontain c).mpr he)
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
        have heoff : e.val ∉ m0GeodesicVertices (P (k - 1)) :=
          fun he => hoff ((m0GeodesicLeftSide_ray_vertex_iff hp P k hcontain e).mpr he)
        change kmswLimitDartVertex (shiftedStream W 0) c.val = e.val at hinc
        exact (m0Geodesic_incident_off_ray_right_iff hp (P (k - 1))
          c.val e.val hinc heoff).2.mp hc.1
  · cases c with
    | inr c =>
      cases e <;> exact False.elim hinc
    | inl c =>
      cases e with
      | inl e => exact False.elim hinc
      | inr e =>
        have hcoff : c.val ∉ m0GeodesicVertices (P (k - 1)) :=
          fun hv => hoff ((m0GeodesicLeftSide_ray_vertex_iff hp P k hcontain c).mpr hv)
        change kmswLimitDartVertex (shiftedStream W 0) e.val = c.val at hinc
        obtain ⟨heoff, hi⟩ := m0Geodesic_incident_off_ray_right_iff hp (P (k - 1))
          e.val c.val hinc hcoff
        refine ⟨hi.mpr hc, ?_⟩
        intro n hn
        exact heoff ⟨n, (congrArg Prod.fst hn).symm⟩

/-- Helper toward Lemma 5.6: every intrinsic right-face seed satisfies
the oriented geometric invariant needed for slit-chain induction. -/
theorem m0GeodesicLeftSide_right_face_seed_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (hc : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c) :
    m0GeodesicSlitRightInvariant hp (P (k - 1)) (P k) c := by
  cases c with
  | inl c =>
    obtain ⟨n, hn, _⟩ := hc
    exact False.elim hn
  | inr c =>
    obtain ⟨F, hb, hr, _⟩ :=
      m0GeodesicLeftSide_right_face_seed_has_common_side_face hp P k hcontain c hc
    exact m0Geodesic_right_face_dart_invariant hp (P (k - 1)) (P k) c F hb hr

/-- Helper toward Lemma 5.6: every cell reached from a retained right
seed by an intrinsic finite slit chain satisfies the oriented invariant. -/
theorem m0GeodesicLeftSide_slit_reaches_right_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {a c : GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (ha : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) a)
    (hac : Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)) a c) :
    m0GeodesicSlitRightInvariant hp (P (k - 1)) (P k) c := by
  induction hac with
  | refl => exact m0GeodesicLeftSide_right_face_seed_invariant hp P k hcontain a ha
  | tail _ hstep ih =>
    exact m0GeodesicLeftSide_slit_step_right_invariant hp P k hcontain hstep ih

/-- Helper toward Lemma 5.6: soundness, every cell reached by an
intrinsic slit chain from a seed lies in the actual preceding right side. -/
theorem m0GeodesicLeftSide_slit_reaches_previousRight
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {a c : GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (ha : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) a)
    (hac : Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)) a c) :
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right := by
  have hc := m0GeodesicLeftSide_slit_reaches_right_invariant hp P k hcontain ha hac
  cases c with
  | inl c => exact hc
  | inr c => exact hc.1

/-- Helper toward Lemma 5.6: the whole intrinsic candidate, including
both orientations of every ray edge, is sound in the geometric right side. -/
theorem m0GeodesicLeftSide_intrinsic_right_sound
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (hc : geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c) :
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right := by
  rcases hc with hv | hd | ⟨a, ha, hac⟩
  · obtain ⟨n, rfl⟩ := hv
    exact m0GeodesicVertices_subset_right hp (P (k - 1))
      (m0Geodesic_initial_mem_vertices (P (k - 1)) n)
  · cases c with
    | inl c =>
      obtain ⟨n, hn | hn⟩ := hd
      · exact False.elim (Sum.inl_ne_inr hn)
      · exact False.elim hn
    | inr c =>
      exact m0GeodesicEdges_subset_right hp (P (k - 1))
        ((m0GeodesicLeftSide_ray_dart_iff hp P k hcontain c).mp hd)
  · cases c <;>
      exact m0GeodesicLeftSide_slit_reaches_previousRight hp P k hcontain ha hac

/-- Helper toward Lemma 5.6: forward slit darts cannot be reached from
right-face seeds. They are included separately in the intrinsic candidate.
Thus exhaustion by chains alone cannot include all closed-side cells. -/
theorem m0GeodesicLeftSide_slit_not_reaches_forward_ray_dart
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {a : GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (ha : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) a) (n : ℕ) :
    ¬ Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)) a
      (m0GeodesicSideAdjacentDarts hp P k hcontain n) := by
  intro hac
  have hc := m0GeodesicLeftSide_slit_reaches_right_invariant hp P k hcontain ha hac
  exact hc.2 n rfl

/-- Helper toward Lemma 5.6: each forward previous-ray dart belongs to
the preceding closed right side, while no right-face seed reaches it by a
slit chain inside the current left side. This is the literal all-cell
chain-exhaustion obstruction, with no new geometric premise. -/
theorem m0GeodesicLeftSide_forward_ray_dart_exhaustion_obstruction
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (n : ℕ) :
    (P (k - 1)).codePath.edge n ∈ m0GeodesicSideEdges hp (P (k - 1)) .right ∧
      ¬ ∃ a : GeometricSideCell (m0GeodesicSide hp (P k) .left),
        geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
        Relation.ReflTransGen
          (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
            (m0GeodesicSideAdjacentVertices hp P k hcontain)
            (m0GeodesicSideAdjacentDarts hp P k hcontain)) a
          (m0GeodesicSideAdjacentDarts hp P k hcontain n) := by
  refine ⟨m0GeodesicEdges_subset_right hp (P (k - 1)) ⟨n, rfl⟩, ?_⟩
  rintro ⟨a, ha, hac⟩
  exact m0GeodesicLeftSide_slit_not_reaches_forward_ray_dart hp P k hcontain ha n hac

































































































































































end DirectedDistances.PaperProofs.Section5
