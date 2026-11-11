module

public import DirectedDistances.KMSW.HatDeletedGeometryPathConnect
public import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.PlanarMap.FiniteDrawingExterior
import Mathlib.Topology.LocallyFinite

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

Deleted vertices escape backwards along finite present paths to the lower-left
outer boundary. Missing edges remain geometric edges and are never used as arrows. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set Quiver
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Reachability propagates across a present stage edge. -/
private theorem reachable_across_stage_edge (w : ℕ → Fin 3) (n e u : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true)
    (hr : Reachable (⟨u⟩ : PresentVertex w) ⟨(kmswStage w n).west e⟩) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨(kmswStage w n).east e⟩ := by
  obtain ⟨p⟩ := hr
  have hends := edge_endpoints_eq w he
  exact ⟨p.cons ⟨e, ⟨n, he, hp⟩, hends.1.symm, hends.2.symm⟩⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every allocated vertex is reached from a nonpositive-index outer-boundary vertex.
The path uses only present edges, including when its source borders missing edges. -/
private theorem hatEscape_stageVertex_reachable_from_leftBoundary (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ k : ℤ, k ≤ 0 ∧ Reachable (⟨boundaryVertex w hb k⟩ : PresentVertex w) ⟨v⟩ := by
  induction n generalizing v with
  | zero =>
    have hv' : v < 2 := hv
    refine ⟨0, le_rfl, ?_⟩
    rw [boundaryVertex_zero]
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact Reachable.refl _
    · exact reachable_across_stage_edge w 0 0 0 (by change 0 < 1; omega) rfl
        (Reachable.refl _)
  | succ n ih =>
    have hend := kmswStage_endpoints_lt_nextVertex w n (act w n)
      (act_lt_nextEdge w le_rfl)
    by_cases hold : v < (kmswStage w n).nextVertex
    · exact ih v hold
    by_cases h0 : w n = 0
    · cases hs : (kmswStage w n).UL.dropLast.reverse with
      | cons e es =>
        simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
          kmswStepOfStep, hs, State.addEdge] at hv
        exact (hold hv).elim
      | nil =>
        have hvnew : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hs, State.addEdge] at hv
          omega
        have hmem : (kmswStage w n).nextEdge + 1 ∈ (kmswStage w (n + 1)).LL := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hs]
        have hw : (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) = v := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hs, State.addEdge, hvnew]
        obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary w hb v
          ⟨n + 1, _, Or.inl hmem, Or.inl hw⟩
        by_cases hkpos : 1 ≤ k
        · refine ⟨0, le_rfl, ?_⟩
          rw [← hk]
          exact boundaryVertex_nonneg_reachable w hb le_rfl (by omega)
        · exact ⟨k, by omega, hk ▸ Reachable.refl _⟩
    · by_cases h1 : w n = 1
      · have hvnew : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
            State.addEdge] at hv
          omega
        subst v
        have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        obtain ⟨k, hk, hr⟩ := ih _ hend.1
        have hreach := reachable_across_stage_edge w (n + 1)
          (kmswStage w n).nextEdge (boundaryVertex w hb k) he hp
        have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
            (kmswStage w n).west (act w n) := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge, act]
        have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
            (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        rw [hw, ht] at hreach
        exact ⟨k, hk, hreach hr⟩
      · cases hs : (kmswStage w n).UR with
        | cons e es =>
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
            kmswStepOfStep, hs] at hv
          exact (hold hv).elim
        | nil =>
          have hvnew : v = (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge] at hv
            omega
          subst v
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          obtain ⟨k, hk, hr⟩ := ih _ hend.2
          have hreach := reachable_across_stage_edge w (n + 1)
            (kmswStage w n).nextEdge (boundaryVertex w hb k) he hp
          have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
              (kmswStage w n).east (act w n) := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge, act]
          have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
              (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          rw [hw, ht] at hreach
          exact ⟨k, hk, hreach hr⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A finite polyline joins its endpoints within its full geometric image. -/
private theorem polyline_endpoints_joined (p : Polyline) :
    JoinedIn p.image p.start p.finish := by
  have hpoint : ∀ i, i < p.points.length → JoinedIn p.image p.start (p.point i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Polyline.point_zero_eq_start]
      exact JoinedIn.refl (Or.inl rfl)
    | succ i ih =>
      intro hi
      apply (ih (by omega)).trans
      apply JoinedIn.of_segment_subset
      intro z hz
      exact Or.inr ⟨i, hi, hz⟩
  rw [← p.point_last_eq_finish]
  exact hpoint _ (by have := List.length_pos_iff.mpr p.nonempty; omega)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A retained vertex position has a reachable vertex ID. -/
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
A reachable vertex position is retained, using a present outgoing edge. -/
private theorem reachable_position_retained (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (v : ℕ) (hv : MhatVertex w v) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v ∈
      (hatRealizedDrawing w hfin).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨e, he, hev⟩ := uibot_allocated_vertex_outgoing w hb.R_unbounded_below v
    (kmsw_vertex_allocated_of_finite_incidence w hfin v)
  have hwest : MhatVertex w (edgeWest w e) := hev ▸ hv
  have heast := hwest.trans (Hom.reachable
    (⟨e, he, rfl, rfl⟩ :
      (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeEast w e⟩))
  rw [restrictDrawing_image_eq]
  refine Or.inr ⟨⟨(e, false), hwest, heast⟩, ?_⟩
  have hs : (P.arc (e, false)).start = P.pos v := by
    simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, hev]
      using P.arc_start (e, false)
  exact Or.inl hs.symm




private theorem unreachable_arc_avoids (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (e : ℕ)
    (hw : ¬ MhatVertex w (edgeWest w e))
    (he : ¬ MhatVertex w (edgeEast w e)) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).image ⊆
      (hatRealizedDrawing w hfin).imageᶜ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  intro z hz hzQ
  by_cases hs : z = (P.arc (e, false)).start
  · apply hw
    apply retained_position_reachable w hfin
    have hs' : (P.arc (e, false)).start = P.pos (edgeWest w e) := P.arc_start _
    exact hs' ▸ hs ▸ hzQ
  by_cases ht : z = (P.arc (e, false)).finish
  · apply he
    apply retained_position_reachable w hfin
    have ht' : (P.arc (e, false)).finish = P.pos (edgeEast w e) := P.arc_finish _
    exact ht' ▸ ht ▸ hzQ
  have hzi : z ∈ (P.arc (e, false)).interior := by
    exact ⟨hz, by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using ⟨hs, ht⟩⟩
  rw [restrictDrawing_image_eq] at hzQ
  rcases hzQ with ⟨v, hv⟩ | ⟨d, hd⟩
  · have hv' : P.pos v.val = z := hv
    exact P.interior_avoids_vertices (e, false) v.val (hv'.symm ▸ hzi)
  · have hne : d.val ≠ (e, false) := by
      intro hde
      have hfirst : d.val.1 = e := congrArg Prod.fst hde
      exact hw (hfirst ▸ d.property.1)
    have hflip : d.val ≠ (e, true) := by
      intro hde
      have hfirst : d.val.1 = e := congrArg Prod.fst hde
      exact hw (hfirst ▸ d.property.1)
    have hdi : z ∈ (P.arc d.val).interior := by
      refine ⟨hd, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro hstart
        exact P.interior_avoids_vertices (e, false) _
          (P.arc_start d.val ▸ hstart ▸ hzi)
      · intro hfinish
        exact P.interior_avoids_vertices (e, false) _
          (P.arc_finish d.val ▸ hfinish ▸ hzi)
    exact (disjoint_left.mp (P.interior_disjoint (e, false) d.val hne hflip)) hzi hdi

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A present directed path ending at an unreachable vertex lies in the hatted complement. -/
private theorem hatEscape_presentPath_joined (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) {u v : PresentVertex w}
    (p : Path u v) (hv : ¬ MhatVertex w v.id) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    JoinedIn (hatRealizedDrawing w hfin).imageᶜ (P.pos u.id) (P.pos v.id) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  induction p with
  | nil =>
    exact JoinedIn.refl (fun h => hv (retained_position_reachable w hfin _ h))
  | @cons a b p e ih =>
    have ha : ¬ MhatVertex w a.id := fun h => hv (h.trans e.reachable)
    have hw : ¬ MhatVertex w (edgeWest w e.val) := by rw [e.property.2.1]; exact ha
    have he : ¬ MhatVertex w (edgeEast w e.val) := by rw [e.property.2.2]; exact hv
    have hjoin := (polyline_endpoints_joined (P.arc (e.val, false))).mono
      (unreachable_arc_avoids w hfin e.val hw he)
    have hs : (P.arc (e.val, false)).start = P.pos a.id := by
      simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, e.property.2.1]
        using P.arc_start (e.val, false)
    have ht : (P.arc (e.val, false)).finish = P.pos b.id := by
      simpa only [kmswLimitDartVertex, Bool.false_eq_true, Bool.not_false,
        ↓reduceIte, e.property.2.2] using P.arc_finish (e.val, false)
    rw [hs, ht] at hjoin
    exact (ih ha).trans hjoin

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The hatted image is closed by local finiteness of its compact edge arcs. -/
private theorem hat_image_closed (w : ℕ → Fin 3) (hfin : hatLimitFiniteIncidence w) :
    IsClosed (hatRealizedDrawing w hfin).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  have heq : Q.image = ⋃ d, (Q.arc d).image := by
    ext z
    constructor
    · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
      · obtain ⟨d, hd, hv⟩ := v.property
        refine mem_iUnion.mpr ⟨⟨d, hd⟩, ?_⟩
        change P.pos v.val ∈ (P.arc d).image
        rw [← hv, ← P.arc_start]
        exact Or.inl rfl
      · exact mem_iUnion.mpr ⟨d, hd⟩
    · intro hz
      obtain ⟨d, hd⟩ := mem_iUnion.mp hz
      exact Or.inr ⟨d, hd⟩
  have hlocal : LocallyFinite (fun d => (Q.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z (by norm_num), ?_⟩
    apply (Q.locally_finite (Metric.ball z 1) Metric.isBounded_ball).subset
    rintro d ⟨a, ha, hb⟩
    exact ⟨a, hb, ha⟩
  rw [heq]
  exact hlocal.isClosed_iUnion (fun d => (Q.arc d).isCompact_image.isClosed)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The starting vertex of a bordering dart lies in the closure of its face. -/
private theorem border_start_mem_closure {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F : P.Face) (d : D) (hd : P.dartBorders d F) :
    (P.arc d).start ∈ closure F.val := by
  obtain ⟨δ, hδ, hw⟩ := hd
  let g : ℝ → ℂ := fun t => (P.arc d).start + (t : ℂ) *
    ((P.arc d).initialDirection + (t : ℂ) * Complex.I *
      (P.arc d).initialDirection)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 δ) := by
    rw [closure_Ioo (ne_of_lt hδ)]
    exact ⟨le_rfl, hδ.le⟩
  have hsub : g '' Ioo 0 δ ⊆ F.val := by
    rintro z ⟨t, ht, rfl⟩
    exact hw t t ht.1 ht.2 ht.1 ht.2
  have hz := closure_mono hsub (mem_closure_image hg.continuousAt hzero)
  simpa only [g, Complex.ofReal_zero, zero_mul, add_zero] using hz

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A point outside a closed barrier joins a nearby point of any set whose closure contains it. -/
private theorem closure_point_joins_set (K S : Set ℂ) (hK : IsClosed K)
    {z : ℂ} (hz : z ∉ K) (hcl : z ∈ closure S) :
    ∃ q ∈ S, JoinedIn Kᶜ z q := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z hz
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  have hqball : q ∈ Metric.ball z ε := by
    simpa only [Metric.mem_ball, dist_comm] using hdist
  have hzball : z ∈ Metric.ball z ε := Metric.mem_ball_self hε
  exact ⟨q, hq, (((convex_ball z ε).isPathConnected ⟨z, hzball⟩).joinedIn
    z hzball q hqball).mono hball⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every deleted outer-boundary vertex joins any ambient unbounded face while avoiding
the hatted image. The ambient boundary classification supplies the bordering dart. -/
private theorem hatEscape_boundaryVertex_joins_unboundedFace (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (E : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hE : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded E)
    (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (hatRealizedDrawing w hfin).image) :
    ∃ q ∈ E.val, JoinedIn (hatRealizedDrawing w hfin).imageᶜ
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
        (boundaryVertex w hb k)) q := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, _, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  have hEU : E = U := huniq E hE
  have hd : P.dartBorders (futureMapBoundaryDart w hb (k - 1)) E := by
    rw [hEU]
    exact (hborder _).mpr (futureMapBoundaryDart_external w hb (k - 1))
  have hcl := border_start_mem_closure P E _ hd
  rw [P.arc_start, futureMap_outerVertex_eq_boundaryVertex] at hcl
  exact closure_point_joins_set _ _ (hat_image_closed w hfin) hv hcl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Under the existing boundary-hit hypotheses, every deleted vertex escapes to the
ambient exterior. All intermediate path and boundary-adjacency obligations are proved. -/
private theorem hatDeletedVertexPathToAmbientExteriorGoal_of_boundaryHits (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    hatDeletedVertexPathToAmbientExteriorGoal w hfin := by
  intro E hE v hv
  have hnot : ¬ MhatVertex w v := fun hr =>
    hv (reachable_position_retained w hfin hb v hr)
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
  obtain ⟨k, _, ⟨p⟩⟩ := hatEscape_stageVertex_reachable_from_leftBoundary w hb n v hn
  have hknot : ¬ MhatVertex w (boundaryVertex w hb k) := fun hr =>
    hnot (hr.trans p.reachable)
  have hkdel : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (hatRealizedDrawing w hfin).image := fun hr =>
    hknot (retained_position_reachable w hfin _ hr)
  obtain ⟨q, hq, hjoin⟩ :=
    hatEscape_boundaryVertex_joins_unboundedFace w hfin hb E hE k hkdel
  exact ⟨q, hq, (hatEscape_presentPath_joined w hfin p hnot).symm.trans hjoin⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The standing flow-line-hit hypothesis supplies the boundary hits used for vertex escape. -/
theorem hatDeletedVertexPathToAmbientExteriorGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedVertexPathToAmbientExteriorGoal w hfin :=
  hatDeletedVertexPathToAmbientExteriorGoal_of_boundaryHits w hfin (hatBoundaryHitWitnesses w h)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Vertex escape discharges the deleted-geometry root-face connectivity obligation. -/
theorem hatDeletedGeometryRootFaceConnectivityGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryRootFaceConnectivityGoal w h hfin :=
  hatDeletedVertexPathToAmbientExteriorGoal_implies_rootFaceConnectivity w h hfin
    (hatDeletedVertexPathToAmbientExteriorGoal_holds w h hfin)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Vertex escape discharges the hatted bounded-face finite-border obligation. -/
theorem hatBoundedFaceFiniteBorderGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatBoundedFaceFiniteBorderGoal w h hfin :=
  hatDeletedVertexPathToAmbientExteriorGoal_implies_boundedFaceFiniteBorder w h hfin
    (hatDeletedVertexPathToAmbientExteriorGoal_holds w h hfin)

end DirectedDistances.KMSW
