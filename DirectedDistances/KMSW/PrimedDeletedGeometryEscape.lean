module

public import DirectedDistances.KMSW.PrimedRealizedFacesClose
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.PlanarMap.FiniteDrawingExterior
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Connected.LocallyConnected

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

The geometric primed carrier retains beta-zero and the C18 missing root.
Deleted geometry is therefore not the whole reachable submap. All deleted-point
and bounded-face conclusions below are conditional on the explicitly open
one-point-per-deleted-arc escape obligation. No escape obligation is assumed by
an unconditional theorem, and this file does not claim the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Precisely the reachable non-beta edges are deleted from the primed geometry. -/
theorem primedDeletedEdge_iff (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (e : ℕ) :
    ¬ primeGeomEdge w hfin hb e ↔
      MhatGeometricEdge w e ∧ ¬ primeBetaEdge w hfin hb e := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  classical
  simp only [primeGeomEdge, not_or, not_not]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The full geometric arc of each beta-zero edge is retained despite its missing tag. -/
theorem primedBeta0_arc_subset (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : primeBetaEdge w hfin hb e) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).image ⊆
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  intro z hz
  rw [mhatPrimeDrawing, restrictDrawing_image_eq]
  exact Or.inr ⟨⟨(e, false), Or.inr he⟩, hz⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The C18 root arc is retained in the geometric drawing as a missing edge. -/
theorem primedC18Root_arc_subset (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (primedLimitEdgeMap w h 0, false)).image ⊆
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  intro z hz
  rw [mhatPrimeDrawing, restrictDrawing_image_eq]
  exact Or.inr ⟨⟨(_, false), (primedLimitRoot_primeMissingEdge w h hfin hb).1⟩, hz⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A deleted arc interior avoids every retained vertex and both retained orientations. -/
theorem primedDeletedArc_interior_avoids (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).interior ⊆
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  intro z hz hzQ
  rw [mhatPrimeDrawing, restrictDrawing_image_eq] at hzQ
  rcases hzQ with ⟨v, hv⟩ | ⟨d, hd⟩
  · have hv' : P.pos v.val = z := hv
    rw [← hv'] at hz
    exact P.interior_avoids_vertices (e, false) v.val hz
  · have hne : d.val ≠ (e, false) := by
      intro hd'
      have hp : primeGeomEdge w hfin hb d.val.1 := d.property
      have hfirst : d.val.1 = e := congrArg Prod.fst hd'
      rw [hfirst] at hp
      exact he hp
    have hflip : d.val ≠ (e, true) := by
      intro hd'
      have hp : primeGeomEdge w hfin hb d.val.1 := d.property
      have hfirst : d.val.1 = e := congrArg Prod.fst hd'
      rw [hfirst] at hp
      exact he hp
    have hdi : z ∈ (P.arc d.val).interior := by
      refine ⟨hd, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro hs
        exact P.interior_avoids_vertices (e, false) _ (P.arc_start d.val ▸ hs ▸ hz)
      · intro ht
        exact P.interior_avoids_vertices (e, false) _ (P.arc_finish d.val ▸ ht ▸ hz)
    exact (disjoint_left.mp (P.interior_disjoint (e, false) d.val hne hflip)) hz hdi

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The primed image is closed by local finiteness of its compact retained arcs. -/
private theorem primedEscape_image_closed (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    IsClosed (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
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
A deleted closure point joins a nearby member of the indicated set. -/
private theorem primedEscape_closure_point_joins_set (K S : Set ℂ) (hK : IsClosed K)
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
Each allocated layout arc is a continuous graph. -/
private theorem primedEscape_layoutArc_continuous_graph (w : ℕ → Fin 3) (n e : ℕ)
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
Endpoint and orientation facts for the complete geometric arc. -/
private theorem primedEscape_finish_mem_polyline_image (p : Polyline) : p.finish ∈ p.image := by
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
Endpoint and orientation facts for the complete geometric arc. -/
private theorem primedEscape_reverse_polyline_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ primedEscape_finish_mem_polyline_image p
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
A nondegenerate continuous graph has a path-connected interior with both
endpoints in its closure. -/
private theorem primedEscape_graph_interior (p : Polyline) (f : ℝ → ℝ)
    (hf : Continuous f) (hab : p.start.re < p.finish.re)
    (hgraph : p.image = graphOver p.start.re p.finish.re f) :
    IsPathConnected p.interior ∧ p.image ⊆ closure p.interior := by
  let g := graphParam f
  have hg : Continuous g := by
    change Continuous (fun x : ℝ => (x : ℂ) + (f x : ℂ) * Complex.I)
    fun_prop
  have ha : p.start.im = f p.start.re :=
    (show p.start ∈ graphOver p.start.re p.finish.re f from hgraph ▸ Or.inl rfl).2.2
  have hb : p.finish.im = f p.finish.re :=
    (show p.finish ∈ graphOver p.start.re p.finish.re f from
      hgraph ▸ primedEscape_finish_mem_polyline_image p).2.2
  have hga : g p.start.re = p.start := by
    apply Complex.ext <;> simp [g, graphParam, ha]
  have hgb : g p.finish.re = p.finish := by
    apply Complex.ext <;> simp [g, graphParam, hb]
  have heq : p.interior = g '' Ioo p.start.re p.finish.re := by
    ext z
    constructor
    · rintro ⟨hz, hne⟩
      have hz' : z ∈ graphOver p.start.re p.finish.re f := hgraph ▸ hz
      have hza : p.start.re < z.re := by
        apply lt_of_le_of_ne hz'.1
        intro hx
        apply hne
        left
        exact Complex.ext hx.symm (hz'.2.2.trans ((congrArg f hx.symm).trans ha.symm))
      have hzb : z.re < p.finish.re := by
        apply lt_of_le_of_ne hz'.2.1
        intro hx
        apply hne
        right
        exact Complex.ext hx (hz'.2.2.trans ((congrArg f hx).trans hb.symm))
      refine ⟨z.re, ⟨hza, hzb⟩, ?_⟩
      apply Complex.ext <;> simp [g, graphParam, hz'.2.2]
    · rintro ⟨x, hx, rfl⟩
      constructor
      · rw [hgraph]
        simpa [g, graphParam, graphOver] using And.intro hx.1.le hx.2.le
      · simp only [mem_insert_iff, mem_singleton_iff, not_or]
        constructor
        · intro h
          have hh := congrArg Complex.re h
          have hh' : x = p.start.re := by simpa [g, graphParam] using hh
          exact (ne_of_gt hx.1) hh'
        · intro h
          have hh := congrArg Complex.re h
          have hh' : x = p.finish.re := by simpa [g, graphParam] using hh
          exact (ne_of_lt hx.2) hh'
  constructor
  · rw [heq]
    exact ((convex_Ioo p.start.re p.finish.re).isPathConnected
      (nonempty_Ioo.mpr hab)).image hg
  · intro z hz
    by_cases hi : z ∈ p.interior
    · exact subset_closure hi
    have hend : z = p.start ∨ z = p.finish := by
      by_contra hn
      exact hi ⟨hz, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    have hcl : closure (Ioo p.start.re p.finish.re) =
        Icc p.start.re p.finish.re := closure_Ioo (ne_of_lt hab)
    rw [heq]
    rcases hend with rfl | rfl
    · have hc : p.start.re ∈ closure (Ioo p.start.re p.finish.re) := by
        rw [hcl]
        exact ⟨le_rfl, hab.le⟩
      have hc' := mem_closure_image hg.continuousAt hc
      rw [hga] at hc'
      exact hc'
    · have hc : p.finish.re ∈ closure (Ioo p.start.re p.finish.re) := by
        rw [hcl]
        exact ⟨hab.le, le_rfl⟩
      have hc' := mem_closure_image hg.continuousAt hc
      rw [hgb] at hc'
      exact hc'

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The ambient arc interiors are path-connected and dense in their full arcs. -/
private theorem primedEscape_arc_interior_geometry (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (e : ℕ) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    IsPathConnected (P.arc (e, false)).interior ∧
      (P.arc (e, false)).image ⊆ closure (P.arc (e, false)).interior := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have he := kmsw_edge_allocated_by_self w e
  have harc : P.arc (e, false) = layoutArc w e e := by
    rw [familyDrawing_arc w hfin (monotone_family_all w) e (⟨e, he⟩, false)]
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (familyG w (monotone_family_all w) e).arc_layout (⟨e, he⟩, false)
  obtain ⟨f, hf, hgraph⟩ := primedEscape_layoutArc_continuous_graph w e e he
  have hab : (layoutArc w e e).start.re < (layoutArc w e e).finish.re := by
    rw [(layoutArc_endpoints w e e he).1, (layoutArc_endpoints w e e he).2]
    change (kmswStageRank w e ((kmswStage w e).west e) : ℝ) <
      (kmswStageRank w e ((kmswStage w e).east e) : ℝ)
    exact_mod_cast kmswStageRank_strict w e e he
  change IsPathConnected (P.arc (e, false)).interior ∧
    (P.arc (e, false)).image ⊆ closure (P.arc (e, false)).interior
  rw [harc]
  exact primedEscape_graph_interior _ f hf hab hgraph

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every deleted point, including a deleted vertex or an arc with retained endpoints,
joins the interior of a deleted edge without meeting retained primed geometry. -/
theorem primedDeletedGeometryPoint_joins_deletedArcInterior (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ z, z ∈ P.image → z ∉ Q.image →
      ∃ e, ¬ primeGeomEdge w hfin hb e ∧
        ∃ a ∈ (P.arc (e, false)).interior, JoinedIn Q.imageᶜ z a := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  change ∀ z, z ∈ P.image → z ∉ Q.image →
    ∃ e, ¬ primeGeomEdge w hfin hb e ∧
      ∃ a ∈ (P.arc (e, false)).interior, JoinedIn Q.imageᶜ z a
  intro z hz hzQ
  have hedge : ∃ e, z ∈ (P.arc (e, false)).image := by
    rcases hz with ⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩
    · obtain ⟨e, _, hev⟩ := uibot_allocated_vertex_outgoing w hb.R_unbounded_below v
        (kmsw_vertex_allocated_of_finite_incidence w hfin v)
      refine ⟨e, ?_⟩
      have hs : (P.arc (e, false)).start = P.pos v := by
        simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, hev]
          using P.arc_start (e, false)
      exact Or.inl hs.symm
    · refine ⟨e, ?_⟩
      cases b with
      | false => exact hz
      | true =>
        have hflip : P.arc (e, true) = (P.arc (e, false)).reverse :=
          P.arc_flip (e, false)
        rw [hflip] at hz
        exact primedEscape_reverse_polyline_image_subset _ hz
  obtain ⟨e, hze⟩ := hedge
  have he : ¬ primeGeomEdge w hfin hb e := by
    intro he
    apply hzQ
    change z ∈ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image
    rw [mhatPrimeDrawing, restrictDrawing_image_eq]
    exact Or.inr ⟨⟨(e, false), he⟩, hze⟩
  obtain ⟨a, ha, hza⟩ := primedEscape_closure_point_joins_set Q.image
    (P.arc (e, false)).interior (primedEscape_image_closed w hfin hb) hzQ
    ((primedEscape_arc_interior_geometry w hfin e).2 hze)
  exact ⟨e, he, a, ha, hza⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A bordering dart starts in the closure of its ambient face. -/
private theorem primedEscape_border_start_mem_closure {D V : Type*} {flip : D → D}
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





theorem primedDeletedBoundaryVertex_joins_ambientExterior (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (E : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hE : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded E)
    (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image) :
    ∃ q ∈ E.val, JoinedIn (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
        (boundaryVertex w hb k)) q := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, _, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  have hEU : E = U := huniq E hE
  have hd : P.dartBorders (futureMapBoundaryDart w hb (k - 1)) E := by
    rw [hEU]
    exact (hborder _).mpr (futureMapBoundaryDart_external w hb (k - 1))
  have hcl := primedEscape_border_start_mem_closure P E _ hd
  rw [P.arc_start, futureMap_outerVertex_eq_boundaryVertex] at hcl
  exact primedEscape_closure_point_joins_set _ _
    (primedEscape_image_closed w hfin hb) hv hcl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Open residual: one interior point of each deleted reachable non-beta edge must
escape to each ambient unbounded face. Retained beta endpoints need not escape.
This proposition is not proved or assumed by any unconditional result here. -/
@[expose] def primedDeletedArcInteriorEscapeGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
    ∀ E : P.Face, P.IsUnbounded E →
      ∃ a ∈ (P.arc (e, false)).interior, ∃ q ∈ E.val, JoinedIn Q.imageᶜ a q




@[expose] def primedDeletedGeometryPathToAmbientExteriorGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ E : P.Face, P.IsUnbounded E → ∀ z, z ∈ P.image → z ∉ Q.image →
    ∃ q ∈ E.val, JoinedIn Q.imageᶜ z q

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
One escaping point per deleted arc suffices for every deleted ambient point.
This is a conditional reduction of the explicitly open geometric obligation. -/
theorem primedDeletedArcInteriorEscapeGoal_implies_deletedGeometryPath (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedDeletedArcInteriorEscapeGoal w hfin hb →
      primedDeletedGeometryPathToAmbientExteriorGoal w hfin hb := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  intro harc E hE z hzP hzQ
  obtain ⟨e, he, a, ha, hza⟩ :=
    primedDeletedGeometryPoint_joins_deletedArcInterior w hfin hb z hzP hzQ
  obtain ⟨hmhat, hbeta⟩ := (primedDeletedEdge_iff w hfin hb e).mp he
  obtain ⟨b, hb', q, hq, hbq⟩ := harc e hmhat hbeta E hE
  have hab := ((primedEscape_arc_interior_geometry w hfin e).1.joinedIn a ha b hb').mono
    (primedDeletedArc_interior_avoids w hfin hb e he)
  exact ⟨q, hq, (hza.trans hab).trans hbq⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The smaller one-point arc residual is equivalent to full deleted-point escape.
Neither equivalent proposition is asserted unconditionally. -/
theorem primedDeletedGeometryPath_iff_arcInteriorEscape (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedDeletedGeometryPathToAmbientExteriorGoal w hfin hb ↔
      primedDeletedArcInteriorEscapeGoal w hfin hb := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  constructor
  · intro hpath e hmhat hbeta E hE
    have he := (primedDeletedEdge_iff w hfin hb e).mpr ⟨hmhat, hbeta⟩
    obtain ⟨a, ha⟩ := (primedEscape_arc_interior_geometry w hfin e).1.nonempty
    obtain ⟨q, hq, haq⟩ := hpath E hE a (Or.inr ⟨(e, false), ha.1⟩)
      (primedDeletedArc_interior_avoids w hfin hb e he ha)
    exact ⟨a, ha, q, hq, haq⟩
  · exact primedDeletedArcInteriorEscapeGoal_implies_deletedGeometryPath w hfin hb

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A complementary path keeps its endpoints in the same face. -/
private theorem primedEscape_joined_target_mem_face {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (Q : PLDrawing D V flip rot vert)
    (F : Q.Face) {z q : ℂ} (hz : z ∈ F.val) (hjoin : JoinedIn Q.imageᶜ z q) :
    q ∈ F.val := by
  obtain ⟨x, _, hF⟩ := F.property
  have hFz : F.val = connectedComponentIn Q.imageᶜ z :=
    hF.trans (connectedComponentIn_eq (hF ▸ hz))
  rw [hFz]
  obtain ⟨γ, hγ⟩ := hjoin
  exact (isPreconnected_range γ.continuous).subset_connectedComponentIn
    (show z ∈ range γ from ⟨0, γ.source⟩)
    (by rintro a ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Escape to the ambient exterior excludes deleted geometry from bounded primed faces.
The escape proposition remains an explicit open antecedent. -/
theorem primedDeletedGeometryPath_implies_deletedGeometryExclusion (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedDeletedGeometryPathToAmbientExteriorGoal w hfin hb →
      primedBoundedFace_deletedGeometryExclusionGoal w hfin hb := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  intro hpath F
  obtain ⟨E, hE, _, _⟩ := monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  apply disjoint_left.mpr
  intro z hzF hzP
  have hzQ := Q.face_subset_compl F.val hzF
  obtain ⟨q, hq, hzq⟩ := hpath E hE z hzP hzQ
  have hqF := primedEscape_joined_target_mem_face Q F.val hzF hzq
  have hEF : E.val ⊆ F.val.val := by
    obtain ⟨a, _, hF⟩ := F.val.property
    have hFq : F.val.val = connectedComponentIn Q.imageᶜ q :=
      hF.trans (connectedComponentIn_eq (hF ▸ hqF))
    rw [hFq]
    have hc : IsPreconnected E.val := by
      obtain ⟨a, _, ha⟩ := E.property
      rw [ha]
      exact isPreconnected_connectedComponentIn
    exact hc.subset_connectedComponentIn hq (fun a ha haQ =>
      P.face_subset_compl E ha
        (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w) haQ))
  obtain ⟨R, hR⟩ := F.property.subset_closedBall (0 : ℂ)
  obtain ⟨a, ha, hnorm⟩ := hE R
  have haR : ‖a‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR (hEF ha)
  exact (not_lt_of_ge haR) hnorm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The single open arc-escape residual suffices for the original ambient-face goal.
This implication does not prove or assume that residual in any unconditional result. -/
theorem primedDeletedArcInteriorEscapeGoal_implies_ambientFaceGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedDeletedArcInteriorEscapeGoal w hfin hb →
      primedBoundedFace_ambientFaceGoal w hfin hb := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  intro harc
  apply (primedBoundedFace_ambientFaceGoal_iff_deletedGeometryExclusion w hfin hb).mpr
  exact primedDeletedGeometryPath_implies_deletedGeometryExclusion w hfin hb
    (primedDeletedArcInteriorEscapeGoal_implies_deletedGeometryPath w hfin hb harc)

end DirectedDistances.KMSW
