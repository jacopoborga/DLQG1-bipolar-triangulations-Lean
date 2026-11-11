module

public import DirectedDistances.KMSW.HatRealizedFaces
import DirectedDistances.PlanarMap.FiniteDrawingExterior
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Connected.LocallyConnected

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

Local finiteness makes the set of darts bordering a bounded component finite.
The ambient exterior supplies an unbounded component of the restriction, with
the root's east dart on its border. Finite compressed orbits cannot border any
unbounded component. The remaining deleted-geometry exclusion and exterior
identification obligations are stated explicitly below; neither is assumed. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

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

private theorem face_eq_of_common_border {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F G : P.Face) (d : D) (hF : P.dartBorders d F) (hG : P.dartBorders d G) :
    F = G := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hG⟩ := hG
  let t := min a b / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := by
    have := min_le_left a b
    dsimp [t]
    linarith
  have htb : t < b := by
    have := min_le_right a b
    dsimp [t]
    linarith
  exact P.faces_eq_of_mem (hF t t ht hta ht hta) (hG t t ht htb ht htb)

private theorem bounded_not_unbounded {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F : PlaneFaces P) : ¬ P.IsUnbounded F.val := by
  obtain ⟨R, hR⟩ := F.property.subset_closedBall (0 : ℂ)
  intro h
  obtain ⟨z, hz, hnorm⟩ := h R
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact (not_lt_of_ge hzR) hnorm

private theorem restricted_image_closed {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (S : Set D) (hS : ∀ d, d ∈ S ↔ flip d ∈ S) :
    IsClosed (restrictDrawing P S hS).image := by
  let Q := restrictDrawing P S hS
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

private theorem face_frontier_subset_image {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (hclosed : IsClosed P.image) (F : P.Face) : frontier F.val ⊆ P.image := by
  obtain ⟨x, hx, hF⟩ := F.property
  have hopen : IsOpen F.val := by rw [hF]; exact hclosed.isOpen_compl.connectedComponentIn
  intro z hz
  by_contra hzP
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzP
  obtain ⟨y, hyball, hyF⟩ := (mem_closure_iff.mp hz.1)
    (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  have hcomp : connectedComponentIn P.imageᶜ y = F.val := by
    rw [hF] at hyF ⊢
    exact (connectedComponentIn_eq hyF).symm
  have hzF : z ∈ F.val := by
    rw [← hcomp]
    exact (convex_ball z ε).isPreconnected.subset_connectedComponentIn hyball hball
      (Metric.mem_ball_self hε)
  exact hz.2 (hopen.interior_eq.symm ▸ hzF)

private theorem retained_pos_reachable (w : ℕ → Fin 3)
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
  · have hnot := P.interior_avoids_vertices d.val v
    have hend : P.pos v = (P.arc d.val).start ∨
        P.pos v = (P.arc d.val).finish := by
      by_contra hn
      apply hnot
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

private theorem first_creation_dart_mem (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    ((stageTriangleRecord w j).1, false) ∈ stageTriangleDartList w j := by
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0, hp]
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0]

private theorem reachable_cap_finite_border (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (j : TriangleCreationTime w)
    (hr : HatTriangleReachable w (stageTriangleRecord w j)) :
    ∃ (i : Fin (kmswStage w (j.val + 1)).triangles.length)
      (G : PlaneFaces (hatRealizedDrawing w hfin)),
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      G.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
      ∃ d : ℕ × Bool,
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) G.val ∧
        {e | (kmswInfFaceSucc (hatCodes w h)
          (hatCodes_finiteIncidence w h hfin)).SameCycle d e}.Finite := by
  obtain ⟨i, F, G, hi, hF, hG, hb⟩ := hatReachableCreationCap_survives w hfin j hr
  let s : GlobalHatTri w := ⟨stageTriangleRecord w j, j.val + 1,
    hi ▸ List.get_mem _ i, hr⟩
  let t := (hatLimitFaceEquiv w h).symm s
  have hmap : (hatLimitFaceEquiv w h t).val = stageTriangleRecord w j :=
    congrArg Subtype.val ((hatLimitFaceEquiv w h).apply_symm_apply s)
  change (hatLimitEdgeMap w h t.val.1, hatLimitEdgeMap w h t.val.2.1,
    hatLimitEdgeMap w h t.val.2.2) = stageTriangleRecord w j at hmap
  let d : ℕ × Bool := (t.val.1, false)
  have hHd : (hatLimitDartEquiv w h d).val = ((stageTriangleRecord w j).1, false) := by
    rw [hatLimitDartEquiv_apply]
    change (hatLimitEdgeMap w h t.val.1, false) = ((stageTriangleRecord w j).1, false)
    apply Prod.ext
    · exact congrArg (fun q : ℕ × ℕ × ℕ => q.1) hmap
    · rfl
  have hdG := hb (hatLimitDartEquiv w h d)
    (by rw [hHd]; exact first_creation_dart_mem w j)
  have hnot : ¬ limitExternalDart (hatCodes w h) d := by
    obtain ⟨n, hn⟩ := t.property
    rw [← stageTriangleTimes_records] at hn
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hn
    apply stageTriangleDart_not_limitExternal (hatCodes w h) k d
    change (t.val.1, false) ∈ _
    rw [← hk]
    exact first_creation_dart_mem _ k
  exact ⟨i, G, hi, hG.trans hF, d, hdG,
    (finiteFaceOrbit_iff_not_external (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin) d).mpr hnot⟩

private theorem bounded_ambient_face_creation_cap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w))) :
    ∃ (j : TriangleCreationTime w)
      (i : Fin (kmswStage w (j.val + 1)).triangles.length),
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  let E := monotoneLimitExterior Q G
  have himage : P.image = ⋃ n, (Q n).image :=
    monotoneFamilyDrawing_image w hfin (monotone_family_all w)
  obtain ⟨z, hz, hF⟩ := F.val.property
  have hzF : z ∈ F.val.val := hF ▸ mem_connectedComponentIn hz
  have hzE : z ∉ E := by
    intro hzE
    have hconn := (monotoneLimitExterior_isPathConnected_twoSided w hfin
      (hatBoundaryHitWitnesses w h) Q G).isConnected
    have havoid : E ⊆ P.imageᶜ := by
      intro a ha hPa
      rw [himage] at hPa
      obtain ⟨n, hn⟩ := mem_iUnion.mp hPa
      exact (disjoint_left.mp (monotoneLimitExterior_disjoint_stageImage Q G n)) ha hn
    have hEF : E ⊆ F.val.val := by
      rw [hF]
      exact hconn.isPreconnected.subset_connectedComponentIn hzE havoid
    apply bounded_not_unbounded P F
    intro R
    obtain ⟨a, ha, hRa⟩ := monotoneLimitExterior_unbounded_twoSided Q G R
    exact ⟨a, hEF ha, hRa⟩
  have hzUnion : z ∈ monotoneStageRegionUnion Q G := not_not.mp hzE
  have hzTrace : z ∉ monotoneLayoutTraceUnion Q := by
    intro hzT
    apply hz
    exact himage.symm ▸ hzT
  obtain ⟨n, i, hzcap⟩ := monotoneStageRegionUnion_mem_cap_of_not_trace Q G hzUnion hzTrace
  obtain ⟨F', hF'⟩ := monotoneFamily_cap_planeFace w hfin n i
  have heq : F.val = F'.val := P.faces_eq_of_mem hzF (hF'.symm ▸ hzcap)
  let tri := (kmswStage w n).triangles.get i
  have ht : tri ∈ (kmswStage w n).triangles := List.get_mem _ i
  rw [← stageTriangleTimes_records] at ht
  obtain ⟨j, _, hj⟩ := List.mem_map.mp ht
  obtain ⟨k, hk⟩ := stageTriangleRecord_fin_index w j
  have hcap : ((G n).cap i).region = ((G (j.val + 1)).cap k).region := by
    apply monotone_cap_region_eq w (G n) (G (j.val + 1)) i k (hj.symm.trans hk.symm)
    intro e he
    have hb := triBound_stage w n _ (List.get_mem _ i)
    have hb' := triBound_stage w (j.val + 1) _ (List.get_mem _ k)
    have he' : e ∈ [((kmswStage w (j.val + 1)).triangles.get k).1,
        ((kmswStage w (j.val + 1)).triangles.get k).2.1,
        ((kmswStage w (j.val + 1)).triangles.get k).2.2] := by
      rwa [hk, hj]
    have hbound : e < (kmswStage w n).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2
    have hbound' : e < (kmswStage w (j.val + 1)).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · exact hb'.1
      · exact hb'.2.1
      · exact hb'.2.2
    simp only [stageEdgeTrace, dite_eq_left hbound, dite_eq_left hbound']
    rw [← familyDrawing_arc w hfin (monotone_family_all w) n (⟨e, hbound⟩, false),
      ← familyDrawing_arc w hfin (monotone_family_all w) (j.val + 1)
        (⟨e, hbound'⟩, false)]
  exact ⟨j, k, hk, (congrArg Subtype.val heq).trans (hF'.trans hcap)⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every bounded restricted face has only finitely many bordering compressed darts.
This does not assert that any dart borders it, or that bordering is preserved by -/
theorem hatRealizedFaces_borderingDarts_finite (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (G : PlaneFaces (hatRealizedDrawing w hfin)) :
    {d : ℕ × Bool | (hatRealizedDrawing w hfin).dartBorders
      (hatLimitDartEquiv w h d) G.val}.Finite := by
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  have hfinite := Q.locally_finite (closure G.val.val) G.property.closure
  apply (hfinite.preimage H.injective.injOn).subset
  intro d hd
  refine ⟨(Q.arc (H d)).start, border_start_mem_closure Q G.val (H d) hd, ?_⟩
  exact Or.inl rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every dart bordering any unbounded restricted face is persistently external in -/
theorem hatRealizedFaces_unbounded_border_external (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (U : (hatRealizedDrawing w hfin).Face)
    (hU : (hatRealizedDrawing w hfin).IsUnbounded U) (d : ℕ × Bool)
    (hd : (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) U) :
    limitExternalDart (hatCodes w h) d := by
  classical
  by_contra hext
  have hf := (finiteFaceOrbit_iff_not_external (hatCodes w h)
    (hatCodes_finiteIncidence w h hfin) d).mpr hext
  obtain ⟨_, _, _, _, G, _, _, _, _, _, _, _, hb⟩ :=
    hatFiniteFaceOrbit_realized w h hfin d hf
  have heq := face_eq_of_common_border (hatRealizedDrawing w hfin)
    U G.val (hatLimitDartEquiv w h d) hd (hb d (Equiv.Perm.SameCycle.refl _ _))
  exact bounded_not_unbounded (hatRealizedDrawing w hfin) G (heq ▸ hU)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The restricted drawing has an unbounded face containing the ambient exterior;
its border includes the root's east dart. No uniqueness is asserted here. -/
theorem hatRealizedFaces_unbounded_root_face (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := hatRealizedDrawing w hfin
    ∃ (E : P.Face) (U : Q.Face), P.IsUnbounded E ∧ E.val ⊆ U.val ∧
      Q.IsUnbounded U ∧ Q.dartBorders (hatLimitDartEquiv w h futureMapOuterDart) U := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  have hsub : Q.image ⊆ P.image := restrictDrawing_image_subset P
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)
  obtain ⟨E, hE, _, hborder⟩ := monotoneFamilyDrawing_faceClassification_twoSided
    w hfin (hatBoundaryHitWitnesses w h)
  obtain ⟨z, hz, hEset⟩ := E.property
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let U : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hEU : E.val ⊆ U.val := by
    rw [hEset]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
  have hU : Q.IsUnbounded U := by
    intro R
    obtain ⟨x, hx, hxR⟩ := hE R
    exact ⟨x, hEU hx, hxR⟩
  have hext : limitExternalDart w futureMapOuterDart :=
    (futureMap_limitExternalDart_iff_sameCycle w hfin
      (hatBoundaryHitWitnesses w h) futureMapOuterDart).mpr
      (Equiv.Perm.SameCycle.refl _ _)
  have hd := (hborder futureMapOuterDart).mpr hext
  obtain ⟨δ, hδ, hd⟩ := hd
  refine ⟨E, U, hE, hEU, hU, δ, hδ, ?_⟩
  intro t ε ht htδ hε hεδ
  have harc : Q.arc (hatLimitDartEquiv w h futureMapOuterDart) =
      P.arc futureMapOuterDart := by
    rw [restrictDrawing_arc]
    rw [hatLimitDartEquiv_apply]
    change P.arc (hatLimitEdgeMap w h 0, true) = P.arc (0, true)
    rw [hatLimitEdgeMap_zero]
  rw [harc]
  exact hEU (hd t ε ht htδ hε hεδ)

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
restriction contains deleted ambient geometry. The quantifier includes removed
vertices and points on removed arcs, retaining edge identities. -/
@[expose] def hatBoundedFaceDeletedGeometryExclusionGoal (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) : Prop :=
  ∀ G : PlaneFaces (hatRealizedDrawing w hfin),
    Disjoint G.val.val (monotoneFamilyDrawing w hfin (monotone_family_all w)).image






theorem hatBoundedFaceFiniteBorderGoal_iff_deletedGeometryExclusion (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatBoundedFaceFiniteBorderGoal w h hfin ↔
      hatBoundedFaceDeletedGeometryExclusionGoal w hfin := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  have hsub : Q.image ⊆ P.image := restrictDrawing_image_subset P
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)
  constructor
  · intro hgoal G
    obtain ⟨d, hd, hf⟩ := hgoal G
    obtain ⟨_, _, _, F, G', _, _, _, _, _, _, hG', hb⟩ :=
      hatFiniteFaceOrbit_realized w h hfin d hf
    have heq := face_eq_of_common_border Q G'.val G.val (hatLimitDartEquiv w h d)
      (hb d (Equiv.Perm.SameCycle.refl _ _)) hd
    apply disjoint_left.mpr
    intro z hzG hzP
    have hzF : z ∈ F.val.val := by
      rw [← hG']
      exact (congrArg Subtype.val heq).symm ▸ hzG
    exact P.face_subset_compl F.val hzF hzP
  · intro hgoal G
    obtain ⟨z, hzQ, hG⟩ := G.val.property
    have hzG : z ∈ G.val.val := hG ▸ mem_connectedComponentIn hzQ
    have hGavoid : G.val.val ⊆ P.imageᶜ := fun a ha =>
      fun hPa => (disjoint_left.mp (hgoal G)) ha hPa
    have hzP : z ∉ P.image := hGavoid hzG
    let F : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
    have hFG : F.val ⊆ G.val.val := by
      rw [hG]
      exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
    have hGF : G.val.val ⊆ F.val := by
      have hconn : IsPreconnected G.val.val := by
        rw [hG]
        exact isPreconnected_connectedComponentIn
      exact hconn.subset_connectedComponentIn hzG hGavoid
    have hFGset : F.val = G.val.val := Subset.antisymm hFG hGF
    let Fb : PlaneFaces P := ⟨F, G.property.subset hFG⟩
    obtain ⟨j, i, hi, hFcap⟩ := bounded_ambient_face_creation_cap w h hfin Fb
    have hGcap : G.val.val =
        ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region :=
      hFGset.symm.trans hFcap
    have hfront : frontier
        ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ⊆ Q.image := by
      rw [← hGcap]
      exact face_frontier_subset_image Q
        (restricted_image_closed P {d : ℕ × Bool | MhatGeometricEdge w d.1}
          (fun _ => Iff.rfl)) G.val
    have hr : HatTriangleReachable w (stageTriangleRecord w j) := by
      intro e he
      have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
      have hbound : e < (kmswStage w (j.val + 1)).nextEdge := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact hb.1
        · exact hb.2.1
        · exact hb.2.2
      have harc : (P.arc (e, false)).image ⊆ Q.image := by
        intro a ha
        apply hfront
        rw [creationCap_frontier_eq_traces w j i hi]
        have htrace : a ∈ stageEdgeTrace
            (familyQ w (monotone_family_all w) (j.val + 1)) e := by
          rw [stageEdgeTrace, dite_eq_left hbound,
            ← familyDrawing_arc w hfin (monotone_family_all w) (j.val + 1)
              (⟨e, hbound⟩, false)]
          exact ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact Or.inl (Or.inl htrace)
        · exact Or.inl (Or.inr htrace)
        · exact Or.inr htrace
      have hwest : P.pos (edgeWest w e) ∈ Q.image := by
        have hs : P.pos (edgeWest w e) = (P.arc (e, false)).start :=
          (P.arc_start (e, false)).symm
        rw [hs]
        exact harc (Or.inl rfl)
      have heast : P.pos (edgeEast w e) ∈ Q.image := by
        have hs : P.pos (edgeEast w e) = (P.arc (e, false)).finish :=
          (P.arc_finish (e, false)).symm
        rw [hs]
        apply harc
        let p := P.arc (e, false)
        have hlen := P.arc_length (e, false)
        refine Or.inr ⟨p.points.length - 2, by dsimp [p]; omega, ?_⟩
        rw [Polyline.segmentAt,
          show p.points.length - 2 + 1 = p.points.length - 1 by dsimp [p]; omega,
          Polyline.point_last_eq_finish]
        exact right_mem_segment ℝ _ _
      exact ⟨retained_pos_reachable w hfin _ hwest,
        retained_pos_reachable w hfin _ heast⟩
    obtain ⟨k, G', hk, hG', d, hd, hf⟩ := reachable_cap_finite_border w h hfin j hr
    have hcaps := monotone_cap_region_eq w
      (familyG w (monotone_family_all w) (j.val + 1))
      (familyG w (monotone_family_all w) (j.val + 1)) i k
      (hi.trans hk.symm) (fun _ _ => rfl)
    have heq : G'.val = G.val :=
      Subtype.ext (hG'.trans (hcaps.symm.trans hGcap.symm))
    exact ⟨d, heq ▸ hd, hf⟩

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
root's east dart, prove uniqueness, external-dart coverage and connectivity of
the persistent external orbit. The reverse dart implication and existence have -/
@[expose] def hatUnboundedFaceResidualGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) : Prop :=
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  let u := hatCodes w h
  let f := kmswInfFaceSucc u (hatCodes_finiteIncidence w h hfin)
  ∀ U : Q.Face, Q.IsUnbounded U → Q.dartBorders (H futureMapOuterDart) U →
    (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
    (∀ d, limitExternalDart u d → Q.dartBorders (H d) U) ∧
    (∀ d, limitExternalDart u d ↔ f.SameCycle futureMapOuterDart d)




theorem hatUnboundedFaceIdentificationGoal_iff_residual (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatUnboundedFaceIdentificationGoal w h hfin ↔ hatUnboundedFaceResidualGoal w h hfin := by
  obtain ⟨_, V, _, _, hV, hrootV⟩ := hatRealizedFaces_unbounded_root_face w h hfin
  have hrootext := hatRealizedFaces_unbounded_border_external w h hfin V hV
    futureMapOuterDart hrootV
  constructor
  · rintro ⟨U, hU, huniq, hd, horbit⟩ F hF hrootF
    have hrootU := (hd futureMapOuterDart).mpr hrootext
    have heq := face_eq_of_common_border (hatRealizedDrawing w hfin)
      U F (hatLimitDartEquiv w h futureMapOuterDart) hrootU hrootF
    subst F
    exact ⟨huniq, fun d hde => (hd d).mpr hde, horbit⟩
  · intro hres
    obtain ⟨huniq, hd, horbit⟩ := hres V hV hrootV
    exact ⟨V, hV, huniq, fun d =>
      ⟨hatRealizedFaces_unbounded_border_external w h hfin V hV d, hd d⟩, horbit⟩

end DirectedDistances.KMSW
