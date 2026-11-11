module

public import DirectedDistances.KMSW.HatDeletedGeometryConnectivity
public import DirectedDistances.KMSW.HatRealizedFacesResidual

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

Paths avoiding the reachable drawing stay in one complementary component.
Consequently the deleted-geometry path obligation implies root-face connectivity
and exclusion of deleted geometry from every bounded face. Conditional reductions
in this file do not discharge their explicitly named geometric antecedent. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A path in a drawing complement stays in the face containing its terminal point. -/
private theorem path_source_mem_face {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (Q : PLDrawing D V flip rot vert)
    (U : Q.Face) {z q : ℂ} (hq : q ∈ U.val)
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ)
    (h0 : γ 0 = z) (h1 : γ 1 = q) (havoid : ∀ t, γ t ∉ Q.image) :
    z ∈ U.val := by
  obtain ⟨a, _, hU⟩ := U.property
  have hqa : q ∈ connectedComponentIn Q.imageᶜ a := hU ▸ hq
  have hUq : U.val = connectedComponentIn Q.imageᶜ q :=
    hU.trans (connectedComponentIn_eq hqa)
  rw [hUq]
  apply (isPreconnected_range hγ).subset_connectedComponentIn
    (show q ∈ range γ from ⟨1, h1⟩)
    (by rintro _ ⟨t, rfl⟩; exact havoid t)
  exact ⟨0, h0⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Deleted-point paths to the ambient exterior imply the exact root-face goal.
The path obligation remains an explicit antecedent, not a source assumption. -/
theorem hatDeletedGeometryPathToAmbientExteriorGoal_implies_rootFaceConnectivity
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryPathToAmbientExteriorGoal w hfin →
      hatDeletedGeometryRootFaceConnectivityGoal w h hfin := by
  intro hpath E U hE hEU _ _ z hzP hzQ
  obtain ⟨q, hq, γ, hγ, h0, h1, havoid⟩ := hpath E hE z hzP hzQ
  exact path_source_mem_face (hatRealizedDrawing w hfin) U (hEU hq)
    γ hγ h0 h1 havoid

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A bounded drawing face cannot also satisfy the quantified unboundedness predicate. -/
private theorem bounded_face_not_unbounded {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (Q : PLDrawing D V flip rot vert)
    (G : PlaneFaces Q) : ¬ Q.IsUnbounded G.val := by
  obtain ⟨R, hR⟩ := G.property.subset_closedBall (0 : ℂ)
  intro hG
  obtain ⟨z, hz, hnorm⟩ := hG R
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact (not_lt_of_ge hzR) hnorm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Root-face connectivity excludes deleted ambient geometry from bounded faces.
The connectivity obligation remains an explicit antecedent. -/
theorem hatDeletedGeometryRootFaceConnectivityGoal_implies_deletedGeometryExclusion
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryRootFaceConnectivityGoal w h hfin →
      hatBoundedFaceDeletedGeometryExclusionGoal w hfin := by
  intro hconn G
  obtain ⟨E, U, hE, hEU, hU, hroot⟩ := hatRealizedFaces_unbounded_root_face w h hfin
  apply disjoint_left.mpr
  intro z hzG hzP
  have hzQ := (hatRealizedDrawing w hfin).face_subset_compl G.val hzG
  have hzU := hconn E U hE hEU hU hroot z hzP hzQ
  have heq := (hatRealizedDrawing w hfin).faces_eq_of_mem hzG hzU
  exact bounded_face_not_unbounded (hatRealizedDrawing w hfin) G (heq.symm ▸ hU)




theorem hatDeletedGeometryPathToAmbientExteriorGoal_implies_boundedFaceFiniteBorder
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryPathToAmbientExteriorGoal w hfin →
      hatBoundedFaceFiniteBorderGoal w h hfin := by
  intro hpath
  apply (hatBoundedFaceFiniteBorderGoal_iff_deletedGeometryExclusion w h hfin).mpr
  exact hatDeletedGeometryRootFaceConnectivityGoal_implies_deletedGeometryExclusion w h hfin
    (hatDeletedGeometryPathToAmbientExteriorGoal_implies_rootFaceConnectivity w h hfin hpath)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The sole remaining geometric obligation, restricted to deleted vertices: join
each such vertex to the ambient exterior without crossing the reachable image.
It is open. No separation theorem for beta_0 is asserted by this definition. -/
@[expose] def hatDeletedVertexPathToAmbientExteriorGoal (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  ∀ E : P.Face, P.IsUnbounded E → ∀ v, P.pos v ∉ Q.image →
    ∃ q ∈ E.val, JoinedIn Q.imageᶜ (P.pos v) q

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The full path obligation implies its vertex restriction. -/
theorem hatDeletedGeometryPathToAmbientExteriorGoal_implies_deletedVertexPath
    (w : ℕ → Fin 3) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryPathToAmbientExteriorGoal w hfin →
      hatDeletedVertexPathToAmbientExteriorGoal w hfin := by
  intro hpath E hE v hv
  obtain ⟨q, hq, γ, hγ, h0, h1, havoid⟩ :=
    hpath E hE _ (Or.inl ⟨v, rfl⟩) hv
  exact ⟨q, hq, ⟨⟨⟨γ, hγ⟩, h0, h1⟩, havoid⟩⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every monotone layout arc is the graph of a continuous height function. -/
private theorem layoutArc_continuous_graph (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (layoutArc w n e).image =
      graphOver (layoutArc w n e).start.re (layoutArc w n e).finish.re f := by
  induction n with
  | zero =>
    have hab : (layoutPos w 0 0).re < (layoutPos w 0 1).re := by
      norm_num [layoutPos, kmswStageRank]
    refine ⟨segmentHeight (layoutPos w 0 0) (layoutPos w 0 1), ?_, ?_⟩
    · unfold segmentHeight
      fun_prop
    · simpa only [layoutArc, segmentArc_start, segmentArc_finish, graphOver]
        using segmentArc_image hab
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · rw [layoutArc_old w n e ho]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [(layoutArc_endpoints w (n + 1) e he).1,
        (layoutArc_endpoints w (n + 1) e he).2]
      let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
      let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
      by_cases hm : isFreshLeftMissing w n e
      · refine ⟨segmentHeight a b, ?_, ?_⟩
        · unfold segmentHeight
          fun_prop
        · simpa only [hm, ↓reduceIte, graphOver] using layoutArc_image_fresh w n e hf
      · refine ⟨roofHeight a b (n + 1) (rampSlope w n), continuous_roofHeight _ _ _ _, ?_⟩
        simpa only [hm, ↓reduceIte, graphOver] using layoutArc_image_fresh w n e hf

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The last point of a polyline belongs to its image. -/
private theorem finish_mem_polyline_image (p : Polyline) : p.finish ∈ p.image := by
  rw [← p.point_last_eq_finish]
  by_cases hlen : 2 ≤ p.points.length
  · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
    rw [Polyline.segmentAt,
      show p.points.length - 2 + 1 = p.points.length - 1 by omega]
    exact right_mem_segment ℝ _ _
  · have hlen1 : p.points.length = 1 := by
      have := List.length_pos_iff.mpr p.nonempty
      omega
    simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
    exact Or.inl rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Reversing a polyline preserves its geometric image. -/
private theorem reverse_polyline_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ finish_mem_polyline_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A removed arc's interior avoids every retained vertex and retained arc. -/
private theorem deleted_arc_interior_avoids (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (e : ℕ) (he : ¬ MhatGeometricEdge w e) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).interior ⊆
      (hatRealizedDrawing w hfin).imageᶜ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  intro z hz hzQ
  rw [restrictDrawing_image_eq] at hzQ
  rcases hzQ with ⟨v, hv⟩ | ⟨d, hd⟩
  · have hv' : P.pos v.val = z := hv
    exact P.interior_avoids_vertices (e, false) v.val (hv'.symm ▸ hz)
  · have hne : d.val ≠ (e, false) := by
      intro hde
      have hprop : MhatGeometricEdge w d.val.1 := d.property
      have hfirst : d.val.1 = e := congrArg Prod.fst hde
      exact he (hfirst ▸ hprop)
    have hflip : d.val ≠ (e, true) := by
      intro hde
      have hprop : MhatGeometricEdge w d.val.1 := d.property
      have hfirst : d.val.1 = e := congrArg Prod.fst hde
      exact he (hfirst ▸ hprop)
    have hdi : z ∈ (P.arc d.val).interior := by
      refine ⟨hd, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro hs
        exact P.interior_avoids_vertices (e, false) _ (P.arc_start d.val ▸ hs ▸ hz)
      · intro hs
        exact P.interior_avoids_vertices (e, false) _ (P.arc_finish d.val ▸ hs ▸ hz)
    exact (disjoint_left.mp (P.interior_disjoint (e, false) d.val hne hflip)) hz hdi

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A vertex position retained by the drawing has a reachable vertex ID. -/
private theorem retained_position_reachable (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (v : ℕ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v ∈
      (hatRealizedDrawing w hfin).image) : MhatVertex w v := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  rw [restrictDrawing_image_eq] at hv
  rcases hv with ⟨a, ha⟩ | ⟨d, hd⟩
  · have hva : a.val = v := P.pos_injective ha
    obtain ⟨d, hd, had⟩ := a.property
    rw [← hva, ← had]
    cases hb : d.2
    · simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using hd.1
    · simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using hd.2
  · have hend : P.pos v = (P.arc d.val).start ∨
        P.pos v = (P.arc d.val).finish := by
      by_contra hn
      apply P.interior_avoids_vertices d.val v
      exact ⟨hd, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    rcases hend with hs | hs
    · rw [P.arc_start] at hs
      have he := P.pos_injective hs
      rw [he]
      cases hb : d.val.2
      · simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte]
          using d.property.1
      · simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using d.property.2
    · rw [P.arc_finish] at hs
      have he := P.pos_injective hs
      rw [he]
      cases hb : d.val.2
      · exact d.property.2
      · exact d.property.1

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A point on a continuous graph arc joins either endpoint that is deleted, using
the closed subarc between them. Only the opposite endpoint can meet the retained
set, and it enters this subarc only when it is the original deleted point. -/
private theorem graph_arc_joins_deleted_endpoint (p : Polyline) (K : Set ℂ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hgraph : p.image = graphOver p.start.re p.finish.re f)
    (hint : p.interior ⊆ Kᶜ) {z : ℂ} (hz : z ∈ p.image) (hzK : z ∉ K)
    (hends : p.start ∉ K ∨ p.finish ∉ K) :
    ∃ a, (a = p.start ∨ a = p.finish) ∧ a ∉ K ∧ JoinedIn Kᶜ z a := by
  have hzg : z ∈ graphOver p.start.re p.finish.re f := hgraph ▸ hz
  have hag : p.start ∈ graphOver p.start.re p.finish.re f := hgraph ▸ Or.inl rfl
  have hbg : p.finish ∈ graphOver p.start.re p.finish.re f :=
    hgraph ▸ finish_mem_polyline_image p
  rcases hends with ha | hb
  · have hsub : graphOver p.start.re z.re f ⊆ Kᶜ := by
      intro y hy
      have hyarc : y ∈ p.image := by
        rw [hgraph]
        exact ⟨hy.1, hy.2.1.trans hzg.2.1, hy.2.2⟩
      by_cases hya : y = p.start
      · exact hya ▸ ha
      by_cases hyb : y = p.finish
      · have hzre : z.re = p.finish.re :=
          le_antisymm hzg.2.1 (by simpa only [hyb] using hy.2.1)
        have hzb : z = p.finish := Complex.ext hzre
          (hzg.2.2.trans ((congrArg f hzre).trans hbg.2.2.symm))
        intro hyK
        exact hzK (hzb.symm ▸ hyb ▸ hyK)
      exact hint ⟨hyarc, by
        simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hya hyb⟩
    refine ⟨p.start, Or.inl rfl, ha, ?_⟩
    exact ((isPathConnected_graphOver hzg.1 hf.continuousOn).joinedIn z
      ⟨hzg.1, le_rfl, hzg.2.2⟩ p.start ⟨le_rfl, hzg.1, hag.2.2⟩).mono hsub
  · have hsub : graphOver z.re p.finish.re f ⊆ Kᶜ := by
      intro y hy
      have hyarc : y ∈ p.image := by
        rw [hgraph]
        exact ⟨hzg.1.trans hy.1, hy.2.1, hy.2.2⟩
      by_cases hyb : y = p.finish
      · exact hyb ▸ hb
      by_cases hya : y = p.start
      · have hzre : z.re = p.start.re :=
          le_antisymm (by simpa only [hya] using hy.1) hzg.1
        have hza : z = p.start := Complex.ext hzre
          (hzg.2.2.trans ((congrArg f hzre).trans hag.2.2.symm))
        intro hyK
        exact hzK (hza.symm ▸ hya ▸ hyK)
      exact hint ⟨hyarc, by
        simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hya hyb⟩
    refine ⟨p.finish, Or.inr rfl, hb, ?_⟩
    exact ((isPathConnected_graphOver hzg.2.1 hf.continuousOn).joinedIn z
      ⟨le_rfl, hzg.2.1, hzg.2.2⟩ p.finish ⟨hzg.2.1, le_rfl, hbg.2.2⟩).mono hsub

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every deleted ambient point joins a deleted vertex along a subarc of its own
edge, avoiding the reachable image. This includes removed vertices and both
orientations of every geometric edge, without identifying parallel edges. -/
theorem hatDeletedGeometryPoint_joins_deletedVertex (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := hatRealizedDrawing w hfin
    ∀ z, z ∈ P.image → z ∉ Q.image →
      ∃ v, P.pos v ∉ Q.image ∧ JoinedIn Q.imageᶜ z (P.pos v) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  change ∀ z, z ∈ P.image → z ∉ Q.image →
    ∃ v, P.pos v ∉ Q.image ∧ JoinedIn Q.imageᶜ z (P.pos v)
  rintro z (⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩) hzQ
  · exact ⟨v, hzQ, JoinedIn.refl hzQ⟩
  · have hzarc : z ∈ (P.arc (e, false)).image := by
      cases b with
      | false => exact hz
      | true =>
        have hflip : P.arc (e, true) = (P.arc (e, false)).reverse := P.arc_flip (e, false)
        rw [hflip] at hz
        exact reverse_polyline_image_subset _ hz
    have he : ¬ MhatGeometricEdge w e := by
      intro he
      apply hzQ
      rw [restrictDrawing_image_eq]
      exact Or.inr ⟨⟨(e, false), he⟩, hzarc⟩
    have hstart : (P.arc (e, false)).start = P.pos (edgeWest w e) := P.arc_start _
    have hfinish : (P.arc (e, false)).finish = P.pos (edgeEast w e) := P.arc_finish _
    have hends : (P.arc (e, false)).start ∉ Q.image ∨
        (P.arc (e, false)).finish ∉ Q.image := by
      by_cases hs : (P.arc (e, false)).start ∈ Q.image
      · right
        intro ht
        exact he ⟨retained_position_reachable w hfin _ (hstart ▸ hs),
          retained_position_reachable w hfin _ (hfinish ▸ ht)⟩
      · exact Or.inl hs
    have harc : P.arc (e, false) = layoutArc w e e := by
      rw [familyDrawing_arc w hfin (monotone_family_all w) e
        (⟨e, kmsw_edge_allocated_by_self w e⟩, false)]
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        (familyG w (monotone_family_all w) e).arc_layout
          (⟨e, kmsw_edge_allocated_by_self w e⟩, false)
    obtain ⟨f, hf, hgraph⟩ :=
      layoutArc_continuous_graph w e e (kmsw_edge_allocated_by_self w e)
    have hgraphP : (P.arc (e, false)).image =
        graphOver (P.arc (e, false)).start.re (P.arc (e, false)).finish.re f := by
      rw [harc]
      exact hgraph
    obtain ⟨a, ha, haQ, hjoin⟩ := graph_arc_joins_deleted_endpoint (P.arc (e, false))
      Q.image f hf hgraphP (deleted_arc_interior_avoids w hfin e he) hzarc hzQ hends
    rcases ha with ha | ha
    · rw [ha, hstart] at haQ hjoin
      exact ⟨edgeWest w e, haQ, hjoin⟩
    · rw [ha, hfinish] at haQ hjoin
      exact ⟨edgeEast w e, haQ, hjoin⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The vertex-only geometric obligation implies the full deleted-point path goal.
All arc-interior cases are discharged by the monotone drawing construction. -/
theorem hatDeletedVertexPathToAmbientExteriorGoal_implies_deletedGeometryPath
    (w : ℕ → Fin 3) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedVertexPathToAmbientExteriorGoal w hfin →
      hatDeletedGeometryPathToAmbientExteriorGoal w hfin := by
  intro hvertex E hE z hzP hzQ
  obtain ⟨v, hv, hzv⟩ := hatDeletedGeometryPoint_joins_deletedVertex w hfin z hzP hzQ
  obtain ⟨q, hq, hvq⟩ := hvertex E hE v hv
  obtain ⟨γ, hγ⟩ := hzv.trans hvq
  exact ⟨q, hq, γ, γ.continuous, γ.source, γ.target, hγ⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The full deleted-point path goal is equivalent to its vertex-only restriction.
Neither equivalent proposition is proved here. -/
theorem hatDeletedGeometryPathToAmbientExteriorGoal_iff_deletedVertexPath
    (w : ℕ → Fin 3) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryPathToAmbientExteriorGoal w hfin ↔
      hatDeletedVertexPathToAmbientExteriorGoal w hfin :=
  ⟨hatDeletedGeometryPathToAmbientExteriorGoal_implies_deletedVertexPath w hfin,
    hatDeletedVertexPathToAmbientExteriorGoal_implies_deletedGeometryPath w hfin⟩




theorem hatDeletedVertexPathToAmbientExteriorGoal_implies_rootFaceConnectivity
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedVertexPathToAmbientExteriorGoal w hfin →
      hatDeletedGeometryRootFaceConnectivityGoal w h hfin := by
  intro hvertex
  exact hatDeletedGeometryPathToAmbientExteriorGoal_implies_rootFaceConnectivity w h hfin
    (hatDeletedVertexPathToAmbientExteriorGoal_implies_deletedGeometryPath w hfin hvertex)




theorem hatDeletedVertexPathToAmbientExteriorGoal_implies_boundedFaceFiniteBorder
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedVertexPathToAmbientExteriorGoal w hfin →
      hatBoundedFaceFiniteBorderGoal w h hfin := by
  intro hvertex
  exact hatDeletedGeometryPathToAmbientExteriorGoal_implies_boundedFaceFiniteBorder w h hfin
    (hatDeletedVertexPathToAmbientExteriorGoal_implies_deletedGeometryPath w hfin hvertex)

end DirectedDistances.KMSW
