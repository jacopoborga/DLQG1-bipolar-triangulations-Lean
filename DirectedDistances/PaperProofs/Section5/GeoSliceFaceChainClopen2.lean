/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceFaceChainClopen
public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice4

/-! Transfer of retained geometric face chains to intrinsic slit-cell chains. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Set Metric
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: reversing a slit step is again a slit step. -/
theorem geometricSide_slit_step_reverse (M : GeometricSideSubmap)
    (v q : ℕ → GeometricSideCell M) {c e : GeometricSideCell M}
    (hce : geometricSide_slit_step M v q c e) :
    geometricSide_slit_step M v q e c := by
  have hop {a b : GeometricSideCell M}
      (hab : geometricSideRelation M .opposite a b) :
      geometricSideRelation M .opposite b a := by
    cases a with
    | inl a => exact False.elim hab
    | inr a =>
      cases b with
      | inl b => exact False.elim hab
      | inr b =>
        change (a.val.1, !a.val.2) = b.val at hab
        change (b.val.1, !b.val.2) = a.val
        rw [← hab]
        exact Prod.ext rfl (Bool.not_not _)
  rcases hce with hce | hec | ⟨hopp, hoff⟩ | hinc | hinc
  · exact Or.inr (Or.inl hce)
  · exact Or.inl hec
  · refine Or.inr (Or.inr (Or.inl ⟨hop hopp, ?_⟩))
    rintro ⟨n, hn | hn⟩
    · exact hoff ⟨n, Or.inr (hn ▸ hop hopp)⟩
    · exact hoff ⟨n, Or.inl
        (geometricSideRelation_opposite_right_unique M (hop hopp) (hop hn))⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr hinc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hinc)))

/-- Helper toward Lemma 5.6: finite intrinsic slit chains are reversible. -/
theorem geometricSide_slit_reaches_reverse (M : GeometricSideSubmap)
    (v q : ℕ → GeometricSideCell M) {c e : GeometricSideCell M}
    (hce : Relation.ReflTransGen (geometricSide_slit_step M v q) c e) :
    Relation.ReflTransGen (geometricSide_slit_step M v q) e c := by
  induction hce with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head (geometricSide_slit_step_reverse M v q hstep)

/-- Helper toward Lemma 5.6: any two darts bordering one retained face
of either side are joined by retained face succession, without crossing a slit. -/
theorem m0GeodesicSide_common_face_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (v q : ℕ → GeometricSideCell (m0GeodesicSide hp P s))
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) F) :
    Relation.ReflTransGen (geometricSide_slit_step (m0GeodesicSide hp P s) v q)
      (.inr d) (.inr e) := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
    cases s with
    | left => exact fun z hz => (m0GeodesicLeftOpen_subset hp P (hF hz)).1
    | right => exact fun z hz => (hF hz).1
  obtain ⟨F0, hF0, hval⟩ := m0Geodesic_retained_face_runZero hp F hFR
  obtain ⟨j, hj⟩ := (boundedFace_iff_creation_orbit (shiftedStream W 0)
    (H.1 0) h F0).mp hF0
  have hmem (a : ℕ × Bool)
      (ha : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 a) F) :
      a ∈ stageTriangleDartList (shiftedStream W 0) j := by
    have ha0 := (PLDrawing.dartBorders_congr _ _ F0 F
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H a) hval).mp ha
    exact (cap_border_iff (shiftedStream W 0) (H.1 0) j a).mp (hj ▸ ha0)
  have htriangle (x y : ℕ × Bool)
      (hx : x ∈ stageTriangleDartList (shiftedStream W 0) j)
      (hy : y ∈ stageTriangleDartList (shiftedStream W 0) j) :
      x = y ∨ kmswInfFaceSucc (shiftedStream W 0) (H.1 0) x = y ∨
        kmswInfFaceSucc (shiftedStream W 0) (H.1 0) y = x := by
    let t := stageTriangleDartTriple (shiftedStream W 0) j
    obtain ⟨h1, h2, h3, _⟩ :=
      capFace_triangle_darts_sameCycle (shiftedStream W 0) (H.1 0) j
    change x ∈ [t.1, t.2.1, t.2.2] at hx
    change y ∈ [t.1, t.2.1, t.2.2] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h2)
    · exact Or.inl rfl
  rcases htriangle d.val e.val (hmem d.val hd) (hmem e.val he) with hde | hde | hed
  · have hde' : d = e := Subtype.ext hde
    rw [hde']
  · exact .single (Or.inl ⟨⟨F, hd, hF⟩, hde⟩)
  · exact .single (Or.inr (Or.inl ⟨⟨F, he, hF⟩, hed⟩))

/-- Helper toward Lemma 5.6: a retained face dart has an intrinsic face
successor in either side, including at geometric boundary edges. -/
theorem m0GeodesicSide_bordering_face_has_successor
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    ∃ e : GeometricSideCell (m0GeodesicSide hp P s),
      geometricSideRelation (m0GeodesicSide hp P s) .faceNext (.inr d) e := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
    cases s with
    | left => exact fun z hz => (m0GeodesicLeftOpen_subset hp P (hF hz)).1
    | right => exact fun z hz => (hF hz).1
  have hb' := m0Geodesic_retained_face_succ_borders hp F hFR d.val hb
  have he := m0Geodesic_side_edge_of_bordering_face hp P s _ F hF hb'
  exact ⟨.inr ⟨kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d.val, he⟩,
    ⟨⟨F, hb, hF⟩, rfl⟩⟩

/-- Helper toward Lemma 5.6: crossing one shared off-ray edge transfers
geometric adjacency into a slit chain between arbitrary bordering darts. -/
theorem m0GeodesicSide_adjacent_faces_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (v q : ℕ → GeometricSideCell (m0GeodesicSide hp P s))
    (d e a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hG : G.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) G)
    (ha : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 a.val) F)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (a.val.1, !a.val.2)) G)
    (hoff : ¬ geometricSide_ray_dart (m0GeodesicSide hp P s) q (.inr a)) :
    Relation.ReflTransGen (geometricSide_slit_step (m0GeodesicSide hp P s) v q)
      (.inr d) (.inr e) := by
  let b : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges} :=
    ⟨(a.val.1, !a.val.2), a.property⟩
  have hda := m0GeodesicSide_common_face_slit_reaches hp P s v q d a F hF hd ha
  have hbe := m0GeodesicSide_common_face_slit_reaches hp P s v q b e G hG hb he
  have hab : geometricSide_slit_step (m0GeodesicSide hp P s) v q (.inr a) (.inr b) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, hoff⟩))
  exact hda.trans ((Relation.ReflTransGen.single hab).trans hbe)

/-- Helper toward Lemma 5.6: a finite geometric chain of retained faces
crossing off-ray edge interiors transfers to the intrinsic slit relation.
The chain is the input to this transfer lemma, not an exhaustion premise. -/
theorem m0GeodesicSide_face_chain_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (v q : ℕ → GeometricSideCell (m0GeodesicSide hp P s))
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hchain : Relation.ReflTransGen
      (fun A B => ∃ a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges},
        ¬ geometricSide_ray_dart (m0GeodesicSide hp P s) q (.inr a) ∧
        A.val ⊆ m0GeodesicSideOpenRegion hp P s ∧
        B.val ⊆ m0GeodesicSideOpenRegion hp P s ∧
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 a.val) A ∧
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (a.val.1, !a.val.2)) B) F G)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) G) :
    Relation.ReflTransGen (geometricSide_slit_step (m0GeodesicSide hp P s) v q)
      (.inr d) (.inr e) := by
  induction hchain generalizing e with
  | refl => exact m0GeodesicSide_common_face_slit_reaches hp P s v q d e F hF hd he
  | @tail G J _ hGJ ih =>
    obtain ⟨a, hoff, hG, hJ, ha, hb⟩ := hGJ
    exact (ih a ha).trans
      (m0GeodesicSide_adjacent_faces_slit_reaches hp P s v q a e a G J hG hJ
        ha he ha hb hoff)

/-- Helper toward Lemma 5.6: nesting of closed right sides retains each
later right face in the earlier open right side. -/
theorem m0Geodesic_right_face_subset_of_rightSide_subset
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hsub : m0GeodesicSideRegion hp Q .right ⊆ m0GeodesicSideRegion hp P .right)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P .right := by
  have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h := fun z hz => (hF hz).1
  obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp P F hFA
  cases s with
  | right => exact hs
  | left =>
    obtain ⟨z, hz, hval⟩ := F.property
    have hzF : z ∈ F.val := hval ▸ mem_connectedComponentIn hz
    have hzR := hsub ⟨(hF hzF).1, fun hl => (hF hzF).2 (subset_closure hl)⟩
    exact False.elim (hzR.2 (hs hzF))

section SourceFamily
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)

/-- Helper toward Lemma 5.6: every dart of a retained next-right face
is reached from an actual reverse-ray seed inside the preceding right side. -/
theorem m0GeodesicRightSide_right_face_slit_reached
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .right)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges})
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    ∃ q, geometricSide_right_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) q ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
          (m0GeodesicRightSideNextVertices hp P T hleft hc k)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k)) q (.inr d) := by
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  have hnest := m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
    P T hleft hc (k - 1) k (by omega)
  have hprev (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (hA : A.val ⊆ m0GeodesicSideOpenRegion hp (P k) .right) :=
    m0Geodesic_right_face_subset_of_rightSide_subset hp (P k) (P (k - 1)) hnest A hA
  obtain ⟨n, A, hb, hA, hchain⟩ :=
    m0GeodesicFaceChain_right_face_reaches_ray_off_ray hp (P k) F hF
  let a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
    ⟨((P k).codePath.edge n, true), (hcontain n).1⟩
  have hseed : geometricSide_right_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) (.inr a) := by
    refine ⟨n, rfl, ?_⟩
    exact m0GeodesicSide_bordering_face_has_successor hp (P (k - 1)) .right a A
      (hprev A hA) hb
  have htransfer : Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)) (.inr d) (.inr a) := by
    apply m0GeodesicSide_face_chain_slit_reaches hp (P (k - 1)) .right _ _ F A
      (hprev F hF) ?_ d a hd hb
    apply Relation.ReflTransGen.mono ?_ F A hchain
    intro X Y hXY
    obtain ⟨e, hoff, hX, hY, heX, heY⟩ := hXY
    let b : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨e, m0Geodesic_side_edge_of_bordering_face hp (P (k - 1)) .right e X
        (hprev X hX) heX⟩
    refine ⟨b, ?_, hprev X hX, hprev Y hY, heX, heY⟩
    intro hray
    exact hoff ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain b).mp hray)
  refine ⟨.inr a, hseed, ?_⟩
  exact geometricSide_slit_reaches_reverse _ _ _ htransfer

/-- Helper toward Lemma 5.6: every off-ray next-right cell, including
both orientations of every edge and every vertex, is reached from a retained
right-face seed within the preceding right side. -/
theorem m0GeodesicRightSide_source_right_exhaustion
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hmem : match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right)
    (hoffV : ¬ geometricSide_ray_vertex (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideNextVertices hp P T hleft hc k) c)
    (hoffD : ¬ geometricSide_ray_dart (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c) :
    ∃ q : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
      geometricSide_right_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) q ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
          (m0GeodesicRightSideNextVertices hp P T hleft hc k)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k)) q c := by
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  have hnest := m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
    P T hleft hc (k - 1) k (by omega)
  have hface (e : ℕ) (he : e ∈ m0GeodesicSideEdges hp (P k) .right)
      (hoff : e ∉ m0GeodesicEdges (P k)) :
      ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (e, false)) F ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .right := by
    obtain ⟨F, hFA, hb⟩ := boundaryGluing_retained_borderingFace_exists W h hp e
    exact ⟨F, hb, (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp
      (P k) hoff false F hFA hb .right).mp he⟩
  cases c with
  | inl v =>
    have hvoff : v.val ∉ m0GeodesicVertices (P k) :=
      fun hv => hoffV ((m0GeodesicRightSide_ray_vertex_iff hp P k hcontain v).mpr hv)
    obtain ⟨e, _, hev⟩ := uibot_allocated_vertex_outgoing
      (shiftedStream W 0) h.R_unbounded_below v.val
      (kmsw_vertex_allocated_of_finite_incidence (shiftedStream W 0) (H.1 0) v.val)
    obtain ⟨heoff, heiff⟩ := m0Geodesic_incident_off_ray_side_iff hp (P k) .right
      (e, false) v.val hev hvoff
    have heR := heiff.mpr hmem
    obtain ⟨F, hb, hF⟩ := hface e heR heoff
    let a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨(e, false), heR.trans hnest⟩
    obtain ⟨q, hq, hqa⟩ :=
      m0GeodesicRightSide_right_face_slit_reached hp P T hleft hc k F hF a hb
    exact ⟨q, hq, hqa.tail (Or.inr (Or.inr (Or.inr (Or.inl ⟨hev, hoffV⟩))))⟩
  | inr d =>
    have heoff : d.val.1 ∉ m0GeodesicEdges (P k) :=
      fun he => hoffD ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain d).mpr he)
    obtain ⟨F, hb, hF⟩ := hface d.val.1 hmem heoff
    let a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨(d.val.1, false), d.property⟩
    obtain ⟨q, hq, hqa⟩ :=
      m0GeodesicRightSide_right_face_slit_reached hp P T hleft hc k F hF a hb
    refine ⟨q, hq, ?_⟩
    cases hd : d.val.2 with
    | false =>
      have had : a = d := Subtype.ext (Prod.ext rfl hd.symm)
      exact had ▸ hqa
    | true =>
      apply hqa.tail
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨?_, ?_⟩
      · change (d.val.1, true) = d.val
        exact Prod.ext rfl hd.symm
      · intro ha
        exact heoff ((m0GeodesicRightSide_ray_dart_iff hp P k hcontain a).mp ha)

end SourceFamily
/-- Helper toward Lemma 5.6: the interior of the future-map epigraph is
exactly the strict region above its continuous seam. -/
theorem m0Geodesic_interior_ambient_eq_strict :
    interior (m0GeodesicAmbientRegion W H h) =
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} := by
  let U : Set ℂ := {z | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im}
  have hU : IsOpen U := (m0Geodesic_strict_ambient_isOpen_isPreconnected
    (H := H) (h := h)).1
  apply Subset.antisymm
  · intro z hz
    have hzA := interior_subset hz
    change seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im at hzA
    by_contra hnot
    have hzle : z.im ≤ seamFun (shiftedStream W 0) h (H.1 0) z.re := le_of_not_gt hnot
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let y : ℂ := z - ((r / 2 : ℝ) : ℂ) * Complex.I
    have hy : y ∈ ball z r := by
      rw [mem_ball]
      have hd : dist y z = r / 2 := by
        simp only [y, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
          abs_of_pos (half_pos hr)]
      rw [hd]
      exact half_lt_self hr
    have hyA := interior_subset (hball hy)
    change seamFun (shiftedStream W 0) h (H.1 0) y.re ≤ y.im at hyA
    have hyre : y.re = z.re := by simp only [y, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, sub_zero]
    have hyim : y.im = z.im - r / 2 := by simp [y]
    rw [hyre, hyim] at hyA
    linarith only [hyA, hzle, hr]
  · apply hU.subset_interior_iff.mpr
    intro z hz
    change seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im
    exact hz.le

/-- Helper toward Lemma 5.6: crossing inside an open region of one side
retains both bordering faces in that side. -/
theorem m0GeodesicFaceChainStep_faces_subset_side_of_open_region
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (C : Set ℂ) (hCo : IsOpen C) (hC : C ⊆ m0GeodesicSideOpenRegion hp P s)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp C F G) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P s ∧
      G.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  let D := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨d, hd, he, q, hqd, hqC⟩ := hFG
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hCo.mem_nhds hqC)
  have hside (A : D.Face) (hqA : q ∈ closure A.val) :
      A.val ⊆ m0GeodesicSideOpenRegion hp P s := by
    obtain ⟨y, hyA, hyq⟩ := Metric.mem_closure_iff.mp hqA r hr
    have hyC := hC (hball (by rwa [mem_ball, dist_comm]))
    have hyM : y ∈ m0GeodesicAmbientRegion W H h := by
      cases s with
      | left => exact (m0GeodesicLeftOpen_subset hp P hyC).1
      | right => exact hyC.1
    exact (m0CutFace_subset_sideOpenRegion_iff_mem hp P A s hyA
      ((m0CutFace_subset_ambient_iff_mem hp A hyA).mpr hyM)).mpr hyC
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  refine ⟨hside F (D.dartBorders_arc_subset_closure hv d F hd hqd.1), ?_⟩
  apply hside G
  apply D.dartBorders_arc_subset_closure hv (wholePlaneDartFlip W d) G he
  rw [D.arc_flip, Polyline.image_reverse_transfer]
  exact hqd.1

/-- Helper toward Lemma 5.6: a retained overlap face reaches a reverse
preceding-ray face by off-ray dual steps entirely within the overlap.
The first crossing is taken in the open strict part of the current left side. -/
theorem m0GeodesicLeftSide_overlap_face_chain_to_ray
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right) :
    ∃ (G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) (n : ℕ),
      G.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
      G.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 ((P (k - 1)).codePath.edge n, true)) G ∧
      Relation.ReflTransGen
        (fun A B : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face =>
          A.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
          A.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
          B.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
          B.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
          ∃ e : ℕ, e ∉ m0GeodesicEdges (P (k - 1)) ∧ ∃ b c : Bool,
            (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
              (wholePlaneDartι W 0 (e, b)) A ∧
            (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
              (wholePlaneDartι W 0 (e, c)) B) F G := by
  let U := m0GeodesicLeftOpen hp (P k) ∩ interior (m0GeodesicAmbientRegion W H h)
  have hUo : IsOpen U := m0GeodesicLeftOpen_inter_interior_ambient_isOpen hp (P k)
  have hUc : IsPreconnected U :=
    (m0GeodesicLeftOpen_inter_interior_ambient_isPathConnected hp (P k)).isConnected.isPreconnected
  obtain ⟨B, hBA, hbB⟩ := boundaryGluing_retained_borderingFace_exists W h hp
    ((P (k - 1)).codePath.edge 0)
  have hBL := boundaryGluing_forward_seam_face_left W h (k - 1) longest hp
    (P (k - 1)) 0 B hBA (by simpa only [m0GeodesicSeam] using hbB)
  have hBk : B.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
    by_cases he : (P (k - 1)).codePath.edge 0 ∈ m0GeodesicEdges (P k)
    · obtain ⟨n, hn⟩ := he
      apply boundaryGluing_forward_seam_face_left W h k longest hp (P k) n B hBA
      simpa only [m0GeodesicSeam, hn] using hbB
    · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp (P k)
        he false B hBA hbB .left).mp (hcontain 0).1
  have hmeet (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (hA : A.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left) : (U ∩ A.val).Nonempty := by
    obtain ⟨z, hz, hval⟩ := A.property
    have hzA : z ∈ A.val := hval ▸ mem_connectedComponentIn hz
    exact ⟨z, ⟨hA hzA, m0Geodesic_retained_face_subset_interior_ambient hp A
      (fun y hy => (m0GeodesicLeftOpen_subset hp (P k) (hA hy)).1) hzA⟩, hzA⟩
  have hchain := m0GeodesicFaceChain_reaches_of_isOpen_isPreconnected hp U hUo hUc
    F B (hmeet F hFL) (hmeet B hBk)
  revert hFL hFR
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ hBR
    obtain ⟨z, hz, hval⟩ := B.property
    have hzB : z ∈ B.val := hval ▸ mem_connectedComponentIn hz
    exact False.elim (disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P (k - 1)))
      (hBL hzB) (hBR hzB))
  | @head A D hAD _ ih =>
    intro hAL hAR
    have hside := m0GeodesicFaceChainStep_faces_subset_side_of_open_region hp (P k)
      .left U hUo (fun _ hz => hz.1) hAD
    have hAD' : m0GeodesicFaceChainStep hp
        {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} A D := by
      obtain ⟨d, hd, he, q, hq, hqU⟩ := hAD
      refine ⟨d, hd, he, q, hq, ?_⟩
      exact (m0Geodesic_interior_ambient_eq_strict (H := H) (h := h)) ▸ hqU.2
    have hDA : D.val ⊆ m0GeodesicAmbientRegion W H h :=
      fun z hz => (m0GeodesicLeftOpen_subset hp (P k) (hside.2 hz)).1
    obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp (P (k - 1)) D hDA
    cases s with
    | left =>
      obtain ⟨n, hn⟩ := m0GeodesicFaceChain_right_left_crossing hp (P (k - 1)) hAD' hAR hs
      exact ⟨A, n, hAL, hAR, hn, .refl⟩
    | right =>
      obtain ⟨G, n, hGL, hGR, hbG, hDG⟩ := ih hside.2 hs
      obtain ⟨e, he, heA, heD⟩ := m0GeodesicFaceChainStep_right_off_ray hp
        (P (k - 1)) hAD' hAR hs
      exact ⟨G, n, hGL, hGR, hbG,
        hDG.head ⟨hAL, hAR, hside.2, hs, e.1, he, e.2, !e.2, heA, heD⟩⟩

section LeftOverlap
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k : ℤ, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (k : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈ (m0GeodesicSide hp (P k) .left).vertices)

include T hleft

/-- Helper toward Lemma 5.6: every dart of a retained overlap face is
reached from a preceding-ray right-face seed in the current left side. -/
theorem m0GeodesicLeftSide_overlap_face_slit_reached
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    ∃ a, geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain)
          (m0GeodesicSideAdjacentDarts hp P k hcontain)) a (.inr d) := by
  obtain ⟨G, n, hGL, hGR, hbG, hchain⟩ :=
    m0GeodesicLeftSide_overlap_face_chain_to_ray hp P T hleft k hcontain F hFL hFR
  revert d hd
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro d hd
    exact m0GeodesicLeftSide_ray_incident_overlap_face_reached hp P k hcontain
      d G hGL hGR hd n true hbG
  | @head A B hAB _ ih =>
    intro d hd
    obtain ⟨hAL, _, hBL, hBR, e, heoff, b, c, hb, hc⟩ := hAB
    let db : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges} :=
      ⟨(e, c), m0Geodesic_side_edge_of_bordering_face hp (P k) .left (e, c) B hBL hc⟩
    obtain ⟨q, hq, hqdb⟩ := ih hBL hBR db hc
    have hddb := m0GeodesicLeftSide_adjacent_faces_slit_reaches hp P k hcontain
      d db A B hAL hBL hd hc e b c heoff hb hc
    exact ⟨q, hq, hqdb.trans (geometricSide_slit_reaches_reverse _ _ _ hddb)⟩

/-- Helper toward Lemma 5.6: every off-ray overlap cell in the current
left side is reached from a preceding-ray right-face seed. Both cell sorts
are reduced to actual retained overlap faces. -/
theorem m0GeodesicLeftSide_off_ray_previousRight_reached
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (hc : match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (hoff : match c with
      | .inl v => v.val ∉ m0GeodesicVertices (P (k - 1))
      | .inr d => d.val.1 ∉ m0GeodesicEdges (P (k - 1))) :
    ∃ a, geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain)
          (m0GeodesicSideAdjacentDarts hp P k hcontain)) a c := by
  obtain ⟨F, d, hd, hFL, hFR, hdc⟩ :=
    m0GeodesicLeftSide_off_ray_cell_has_overlap_face_slit_reaches hp P k hcontain c hc hoff
  obtain ⟨a, ha, had⟩ :=
    m0GeodesicLeftSide_overlap_face_slit_reached hp P T hleft k hcontain F hFL hFR d hd
  exact ⟨a, ha, had.trans hdc⟩

end LeftOverlap

/-- Helper toward Lemma 5.6: if the next ray starts on the common tail,
there are no retained next-left face seeds in the preceding right side.
This detects the zero-length next-prefix endpoint of the proposed OPEN L. -/
theorem m0GeodesicRightSide_no_left_seed_of_zero_next_coalescence
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    ¬ geometricSide_left_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c := by
  rintro ⟨n, rfl, e, he⟩
  cases e with
  | inl e => exact False.elim he
  | inr e =>
    obtain ⟨⟨F, hb, hFR⟩, _⟩ := he
    have hsame := wholePlaneEdgeι_injective W 0 (hab.1 n)
    simp only [Nat.zero_add] at hsame
    have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h := fun z hz => (hFR hz).1
    have hFL := boundaryGluing_forward_seam_face_left W h (k - 1) longest hp
      (P (k - 1)) (a + n) F hFA (by simpa only [m0GeodesicSeam, hsame] using hb)
    obtain ⟨z, hz, hval⟩ := F.property
    have hzF : z ∈ F.val := hval ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P (k - 1)))
      (hFL hzF) (hFR hzF)

/-- Helper toward Lemma 5.6: a positive preceding prefix and zero next
prefix supply a surviving off-ray cell satisfying every cell hypothesis of
OPEN L but admitting no next-left face seed. This is an endpoint obstruction
to that proposed characterization, not a correction to the paper. -/
theorem m0GeodesicRightSide_zero_next_coalescence_obstruction
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a : ℕ) (ha : 0 < a)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0) :
    ∃ c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) ∧
      c ∉ m0GeodesicRightSideDeletedTailCells hp P k a 0 ∧
      ¬ geometricSide_ray_vertex (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextVertices hp P T hleft hc k) c ∧
      ¬ geometricSide_ray_dart (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ∧
      ¬ ∃ q : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
        geometricSide_left_face_seed (m0GeodesicSide hp (P (k - 1)) .right)
          (m0GeodesicRightSideNextDarts hp P T hleft hc k) q ∧
        Relation.ReflTransGen
          (geometricSide_slit_step (m0GeodesicSide hp (P (k - 1)) .right)
            (m0GeodesicRightSideNextVertices hp P T hleft hc k)
            (m0GeodesicRightSideNextDarts hp P T hleft hc k)) q c := by
  let d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
    ⟨((P (k - 1)).codePath.edge 0, false),
      m0GeodesicEdges_subset_right hp (P (k - 1)) ⟨0, rfl⟩⟩
  have hoff : (P (k - 1)).codePath.edge 0 ∉ m0GeodesicEdges (P k) := by
    rintro ⟨n, hn⟩
    have hco := hab.1 n
    simp only [Nat.zero_add] at hco
    have hidx := m0Cut_geodesic_edge_injective (P (k - 1))
      (hco.trans (congrArg (wholePlaneEdgeι W 0) hn))
    omega
  refine ⟨.inr d, (m0CutAdjacentGeodesics_ordered_before_coalescence
    P T hleft k a 0 hab).1 0 ha, ?_, ?_, ?_, ?_⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · have hidx := m0Cut_geodesic_edge_injective (P (k - 1))
        (congrArg (wholePlaneEdgeι W 0) hn)
      omega
    · apply hoff
      exact ⟨n, by simpa only [Nat.zero_add] using hn⟩
  · rintro ⟨n, hn⟩
    exact Sum.inr_ne_inl hn
  · intro hd
    exact hoff ((m0GeodesicRightSide_ray_dart_iff hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) d).mp hd)
  · rintro ⟨q, hq, _⟩
    exact m0GeodesicRightSide_no_left_seed_of_zero_next_coalescence
      hp P T hleft hc k a hab q hq

end DirectedDistances.PaperProofs.Section5

























































