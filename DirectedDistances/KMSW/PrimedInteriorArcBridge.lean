/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedInteriorArcEscape

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Creation triangles incident to interior deleted arcs

Supporting results for Lemma 5.13 (`lem-quad-kmsw`), source -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set Quiver
open scoped Topology



private theorem bridge_predecessor_east (w : ℕ → Fin 3) (n f : ℕ) (fs : List ℕ)
    (hp : (kmswStage w n).UL.dropLast.reverse = f :: fs) :
    (kmswStage w n).east f = (kmswStage w n).west (act w n) := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hr : xs.reverse = f :: fs := by simpa [hxs] using hp
  have hxs' : xs = fs.reverse ++ [f] := by
    have hh := congrArg List.reverse hr
    simpa using hh
  have hc := (kmswStage_boundary_chain_invariant w n).1.left_of_append
  have hc' : List.IsChain
      (fun a b => (kmswStage w n).east a = (kmswStage w n).west b)
      (fs.reverse ++ [f, act w n]) := by
    simpa [hxs, hxs', List.append_assoc, act] using hc
  exact (List.isChain_append_cons_cons.mp hc').2.1



private theorem bridge_triangle_reachable_of_active_tails (w : ℕ → Fin 3)
    (j : TriangleCreationTime w)
    (hOld : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w j.val).west (act w j.val)⟩)
    (hNew : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (j.val + 1)).west (act w (j.val + 1))⟩) :
    HatTriangleReachable w (stageTriangleRecord w j) := by
  have hOldEast := kmswStage_activeEast_reachable w j.val hOld
  have hNewEast := kmswStage_activeEast_reachable w (j.val + 1) hNew
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have ha0 := ne_of_lt ha
  have ha1 : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by omega
  have hends := edge_endpoints_eq w hb.1
  have hends2 := edge_endpoints_eq w hb.2.1
  have hends3 := edge_endpoints_eq w hb.2.2
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  all_goals
    simp only [← hends.1, ← hends.2, ← hends2.1, ← hends2.2,
      ← hends3.1, ← hends3.2]
  all_goals
    rcases j.property with h0 | h1
    · cases hp : (kmswStage w j.val).UL.dropLast.reverse with
      | nil =>
          simp [act, stageTriangleRecord, kmswStage, kmswStep, kmswCodeStep,
            h0, kmswStepOfStep, hp, State.addEdge, ha0, ha1] at hNew hNewEast ⊢
          all_goals first | exact ⟨hOld, hOldEast⟩ | exact ⟨hNew, hNewEast⟩ | exact ⟨hNew, hOld⟩
      | cons f fs =>
          have hfUL : f ∈ (kmswStage w j.val).UL :=
            List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hp]; simp))
          have hf := (kmswStage_boundary_ids_lt_nextEdge w j.val).2 f
            (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hfUL)))
          have hf0 := ne_of_lt hf
          simp [act, stageTriangleRecord, kmswStage, kmswStep, kmswCodeStep,
            h0, kmswStepOfStep, hp, State.addEdge, ha0, hf0,
            bridge_predecessor_east w j.val f fs hp] at hNew hNewEast ⊢
          all_goals first | exact ⟨hOld, hOldEast⟩ | exact ⟨hNew, hNewEast⟩ | exact ⟨hNew, hOld⟩
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simp [act, stageTriangleRecord, kmswStage, kmswStep, kmswCodeStep,
        h1, kmswStepOfStep, State.addEdge, ha0, ha1] at hNew hNewEast ⊢
      all_goals first | exact ⟨hOld, hOldEast⟩ | exact ⟨hNew, hNewEast⟩ | exact ⟨hNewEast, hOldEast⟩




theorem primedStageTriangle_reachable_of_eastDart (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (j : TriangleCreationTime w) (e : ℕ)
    (hd : (e, true) ∈ stageTriangleDartList w j)
    (hm : MhatGeometricEdge w e) :
    HatTriangleReachable w (stageTriangleRecord w j) := by
  have he := stageTriangleDartList_lt w (j.val + 1) j (Nat.lt_succ_self _) (e, true) hd
  have hw := (edge_endpoints_eq w he).1
  have hr : Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (j.val + 1)).west e⟩ :=
    hw.symm ▸ hm.1
  rcases j.property with h0 | h1
  · have heq : e = (kmswStage w j.val).nextEdge := by
      cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
        simpa [stageTriangleDartList, stageTriangleDartTriple, h0, hp] using hd
    subst e
    have hNew : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (j.val + 1)).west (act w (j.val + 1))⟩ := by
      cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
        simpa [act, kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
          hp, State.addEdge] using hr
    apply bridge_triangle_reachable_of_active_tails w j _ hNew
    cases hp : (kmswStage w j.val).UL.dropLast.reverse with
    | nil =>
        have hmem := (stageReachableVertices_left_activeWest_iff w j.val h0).mp
          ((mem_stageReachableVertices_iff w (j.val + 1) _).mpr
            ((actReachableBefore_activeWest_iff w (j.val + 1)).mpr hNew))
        simp only [hp] at hmem
    | cons f fs =>
        have hfUL : f ∈ (kmswStage w j.val).UL :=
          List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hp]; simp))
        have hf := (kmswStage_boundary_ids_lt_nextEdge w j.val).2 f
          (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hfUL)))
        have hr' : Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w j.val).west f⟩ := by
          simpa [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hp, State.addEdge] using hr
        obtain ⟨p⟩ := hr'
        exact ⟨p.cons ⟨f, EdgePresent.of_stage_present hf
          ((kmswStage_status w j.val).2.1 f hfUL),
          (edge_endpoints_eq w hf).1.symm,
          (edge_endpoints_eq w hf).2.symm.trans (bridge_predecessor_east w j.val f fs hp)⟩⟩
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    have heq : e = (kmswStage w j.val).nextEdge + 1 ∨
        e = (kmswStage w j.val).nextEdge := by
      simpa [stageTriangleDartList, stageTriangleDartTriple, h0] using hd
    have hOld : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w j.val).west (act w j.val)⟩ := by
      rcases heq with rfl | rfl
      · have hFresh : Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w j.val).nextVertex⟩ := by
          simpa [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
            State.addEdge] using hr
        obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h j.val
        · exact flowLine_phase_reachable w h k j.val hk.1 hk.2
        · have hlt : j.val + 1 < walkNR w h (k + 1) := by
            by_contra hnot
            have heq : walkNR w h (k + 1) - 1 = j.val := by omega
            have hc := walkNR_succ_previous_code w h k
            rw [heq, h1] at hc
            contradiction
          exact (lPhase_up_fresh_vertex_unreachable w h k j.val hk.1 hlt h1 hFresh).elim
      · simpa [act, kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
          State.addEdge] using hr
    exact bridge_triangle_reachable_of_active_tails w j hOld
      (kmswStage_up_activeWest_reachable w j.val h1 hOld)



private theorem bridge_west_triangle_of_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (e : ℕ)
    (he : (e, false) ∈ stageTriangleDartList w j) :
    ∃ n t, t ∈ (kmswStage w n).triangles ∧
      ∃ he : e < (kmswStage w n).nextEdge,
        kmswWestSideFaceIsTriangle w n ⟨e, he⟩ t ∧ t = stageTriangleRecord w j := by
  let n := j.val + 1
  have hj : j.val < n := Nat.lt_succ_self _
  have hbound := stageTriangleDartList_lt w n j hj (e, false) he
  have hbase :
      ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₁ w n j hj ∨
        ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₂ w n j hj ∨
        ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₃ w n j hj := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h
    · exact Or.inl (Prod.ext (Fin.ext (congrArg Prod.fst h))
        (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h))
    · exact Or.inr (Or.inl
        (Prod.ext (Fin.ext (congrArg Prod.fst h))
          (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h)))
    · exact Or.inr (Or.inr
        (Prod.ext (Fin.ext (congrArg Prod.fst h))
          (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h)))
  refine ⟨n, stageTriangleRecord w j, ?_, hbound, ?_, rfl⟩
  · rw [← stageTriangleTimes_records]
    exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes w n j).mpr hj, rfl⟩
  · exact ⟨j, hj, rfl, hbase,
      kmswWestSideFaceOrbit_eq_triangleDarts w n j hj ⟨e, hbound⟩ hbase⟩




theorem primedStageTriangle_reachable_of_deletedDart (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) (hm : MhatGeometricEdge w d.1)
    (hbeta : ¬ primeBetaEdge w hfin hb d.1) :
    HatTriangleReachable w (stageTriangleRecord w j) := by
  cases d with
  | mk e b =>
    cases b
    · by_contra hnot
      apply hbeta
      apply (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb e).mpr
      obtain ⟨n, t, ht, he, hface, hrec⟩ := bridge_west_triangle_of_mem w j e hd
      exact ⟨mhatGeometricEdge_edgePresent w hb e hm, hm.1, hm.2,
        n, t, ht, he, hface, hrec ▸ hnot⟩
    · exact primedStageTriangle_reachable_of_eastDart w h j e hd hm




theorem primedDeletedDart_boundedHatCreationTriangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hm : MhatGeometricEdge w d.1) (hbeta : ¬ primeBetaEdge w hfin hb d.1)
    (hext : ¬ limitExternalDart w d) :
    ∃ (j : TriangleCreationTime w), d ∈ stageTriangleDartList w j ∧
      HatTriangleReachable w (stageTriangleRecord w j) ∧
      ∃ G : PlaneFaces (hatRealizedDrawing w hfin),
        ∀ q : {q : ℕ × Bool // MhatGeometricEdge w q.1},
          q.val ∈ stageTriangleDartList w j →
            (hatRealizedDrawing w hfin).dartBorders q G.val := by
  obtain ⟨j, hd⟩ := finiteFaceOrbit_mem_triangle w hfin d
    ((finiteFaceOrbit_iff_not_external w hfin d).mpr hext)
  have hr := primedStageTriangle_reachable_of_deletedDart w h hfin hb j d hd hm hbeta
  obtain ⟨i, F, G, hi, hF, hG, hborder⟩ := hatReachableCreationCap_survives w hfin j hr
  exact ⟨j, hd, hr, G, hborder⟩



private theorem bridge_dart_record_iff (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (e : ℕ) :
    e ∈ [(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
      (stageTriangleRecord w j).2.2] ↔
      ∃ d ∈ stageTriangleDartList w j, d.1 = e := by
  rcases j.property with h0 | h1
  · cases hl : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0, hl]
      <;> tauto
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0]
    tauto



private theorem bridge_arc_interior_nonempty {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) : (P.arc d).interior.Nonempty := by
  let p := P.arc d
  let a := midpoint ℝ p.start (p.point 1)
  let b := midpoint ℝ p.start a
  have hne : p.start ≠ p.point 1 := by
    intro he
    exact P.initial_nonzero d (sub_eq_zero.mpr he.symm)
  have ha : a ≠ p.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ p.start := by
    intro he
    exact ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := by
    intro he
    exact ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ p.start (p.point 1) := midpoint_mem_segment _ _
  have hbm : b ∈ segment ℝ p.start (p.point 1) :=
    (convex_segment p.start (p.point 1)).segment_subset
      (left_mem_segment ℝ p.start (p.point 1)) ham (midpoint_mem_segment p.start a)
  have himage {z : ℂ} (hz : z ∈ segment ℝ p.start (p.point 1)) : z ∈ p.image := by
    refine Or.inr ⟨0, ?_, ?_⟩
    · have hl := P.arc_length d
      change 2 ≤ p.points.length at hl
      omega
    · change z ∈ segment ℝ (p.point 0) (p.point 1)
      rw [Polyline.point_zero_eq_start]
      exact hz
  by_cases haf : a = p.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩




theorem primedReachableTriangle_boundedHatFace_contacts (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (j : TriangleCreationTime w)
    (hr : HatTriangleReachable w (stageTriangleRecord w j)) :
    ∃ G : PlaneFaces (hatRealizedDrawing w hfin),
      ∀ d ∈ stageTriangleDartList w j, MhatGeometricEdge w d.1 ∧
        ((((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
          (d.1, false)).interior) ∩ closure G.val.val).Nonempty := by
  obtain ⟨i, F, G, hi, hF, hG, _⟩ := hatReachableCreationCap_survives w hfin j hr
  obtain ⟨a, b, c, ha, hb, hc, hfront⟩ :=
    hatReachableCreationCap_frontier_eq_arcs w hfin j hr i hi
  simp only [restrictDrawing_arc, ha, hb, hc] at hfront
  refine ⟨G, ?_⟩
  intro d hd
  have hde := (bridge_dart_record_iff w j d.1).mpr ⟨d, hd, rfl⟩
  refine ⟨hr d.1 hde, ?_⟩
  obtain ⟨z, hz⟩ := bridge_arc_interior_nonempty
    (monotoneFamilyDrawing w hfin (monotone_family_all w)) (d.1, false)
  refine ⟨z, hz, ?_⟩
  rw [hG, hF]
  apply frontier_subset_closure
  rw [hfront]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hde
  rcases hde with he | he | he
  · exact Or.inl (Or.inl (he ▸ hz.1))
  · exact Or.inl (Or.inr (he ▸ hz.1))
  · exact Or.inr (he ▸ hz.1)



theorem primedStageTriangle_eq_of_common_dart (w : ℕ → Fin 3)
    (j k : TriangleCreationTime w) (d : ℕ × Bool)
    (hj : d ∈ stageTriangleDartList w j) (hk : d ∈ stageTriangleDartList w k) :
    j = k := by
  by_contra hne
  have hd := stageTriangleDartLists_disjoint w (max j.val k.val + 1) j k
    (by omega) (by omega) hne
  exact List.disjoint_left.mp hd hj hk




theorem primedStageTriangles_incident_finite (w : ℕ → Fin 3)
    (C : Set ℕ) (hC : C.Finite) :
    {j : TriangleCreationTime w | ∃ d ∈ stageTriangleDartList w j, d.1 ∈ C}.Finite := by
  have hsingle (d : ℕ × Bool) : {j | d ∈ stageTriangleDartList w j}.Subsingleton := by
    intro j hj k hk
    exact primedStageTriangle_eq_of_common_dart w j k d hj hk
  have hfinite := (hC.prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).biUnion
    (fun d _ => (hsingle d).finite)
  apply hfinite.subset
  rintro j ⟨d, hd, hdc⟩
  exact mem_biUnion ⟨hdc, mem_univ _⟩ hd




theorem primedDeletedArc_faceReach_infinite_or_externalDart (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) :
    {f | Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f}.Infinite ∨
      ∃ f, Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f ∧
        (limitExternalDart w (f, false) ∨ limitExternalDart w (f, true)) := by
  classical
  let C : Set ℕ := {f | Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f}
  have hdeleted (f : ℕ) (hf : f ∈ C) : ¬ primeGeomEdge w hfin hb f := by
    rcases hf.cases_tail with hfe | ⟨g, _, hgf⟩
    · exact hfe ▸ he
    · exact hgf.2.1
  by_cases hterminal : ∃ f ∈ C,
      limitExternalDart w (f, false) ∨ limitExternalDart w (f, true)
  · exact Or.inr hterminal
  left
  change C.Infinite
  by_contra hC
  have hno (f : ℕ) (hf : f ∈ C) :
      ¬ limitExternalDart w (f, false) ∧ ¬ limitExternalDart w (f, true) :=
    not_or.mp (fun hh => hterminal ⟨f, hf, hh⟩)
  let J : Set (TriangleCreationTime w) :=
    {j | HatTriangleReachable w (stageTriangleRecord w j) ∧
      ∃ d ∈ stageTriangleDartList w j, d.1 ∈ C}
  have hJ : J.Finite := (primedStageTriangles_incident_finite w C (not_not.mp hC)).subset
    (fun _ hj => hj.2)
  have hclosed : ∀ j ∈ J, ∀ d ∈ stageTriangleDartList w j,
      ¬ primeBetaEdge w hfin hb d.1 →
        ∃ k ∈ J, futureMapEdgeInv d ∈ stageTriangleDartList w k := by
    intro j hj d hd hbeta
    obtain ⟨G, hG⟩ := primedReachableTriangle_boundedHatFace_contacts w hfin j hj.1
    have hm : MhatGeometricEdge w d.1 := (hG d hd).1
    have hdDel := (primedDeletedEdge_iff w hfin hb d.1).mpr ⟨hm, hbeta⟩
    obtain ⟨q, hq, hqC⟩ := hj.2
    have hdC : d.1 ∈ C := Relation.ReflTransGen.tail hqC
      ⟨hdeleted q.1 hqC, hdDel, G, (hG q hq).2, (hG d hd).2⟩
    have hflipExt : ¬ limitExternalDart w (futureMapEdgeInv d) := by
      cases hbit : d.2
      · simpa only [futureMapEdgeInv, Equiv.coe_fn_mk, hbit, Bool.not_false]
          using (hno d.1 hdC).2
      · simpa only [futureMapEdgeInv, Equiv.coe_fn_mk, hbit, Bool.not_true]
          using (hno d.1 hdC).1
    obtain ⟨k, hk, hrk, _⟩ := primedDeletedDart_boundedHatCreationTriangle
      w h hfin hb (futureMapEdgeInv d) hm hbeta hflipExt
    exact ⟨k, ⟨hrk, futureMapEdgeInv d, hk, hdC⟩, hk⟩
  have hempty := primedFiniteTriangleClosure_eq_empty w hfin hb J hJ hclosed
  have heC : e ∈ C := Relation.ReflTransGen.refl
  obtain ⟨hm, hbeta⟩ := (primedDeletedEdge_iff w hfin hb e).mp he
  obtain ⟨j, hj, hrj, _⟩ := primedDeletedDart_boundedHatCreationTriangle
    w h hfin hb (e, false) hm hbeta (hno e heC).1
  have hjJ : j ∈ J := ⟨hrj, (e, false), hj, heC⟩
  rw [hempty] at hjJ
  exact hjJ





theorem primedDeletedArc_component_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  rcases primedDeletedArc_faceReach_infinite_or_externalDart w h hfin hb e he with
    hinf | ⟨f, hf, hext⟩
  · exact primedDeletedArc_component_unbounded_of_infinite_faceReach w h hfin hb e he hinf
  · have hfdel : ¬ primeGeomEdge w hfin hb f := by
      rcases hf.cases_tail with hfe | ⟨g, _, hgf⟩
      · exact hfe ▸ he
      · exact hgf.2.1
    exact primedDeletedArc_component_unbounded_of_faceReach_externalDart
      w h hfin hb e f he hfdel hf hext




theorem primedInteriorArc_component_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
      (¬ limitExternalDart w (e, false) ∧ ¬ limitExternalDart w (e, true)) →
      (∀ k : ℤ, (edgeWest w e = boundaryVertex w hb k ∨
        edgeEast w e = boundaryVertex w hb k) → P.pos (boundaryVertex w hb k) ∈ Q.image) →
      ∀ a ∈ (P.arc (e, false)).interior,
        ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  dsimp only
  intro e hm hbeta _ _
  exact primedDeletedArc_component_unbounded w h hfin hb e
    ((primedDeletedEdge_iff w hfin hb e).mpr ⟨hm, hbeta⟩)



theorem primedBoundedFace_deletedGeometryExclusionGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_deletedGeometryExclusionGoal w hfin hb :=
  (primedDeletedGeometryExclusion_iff_interiorArcComponents_unbounded w hfin hb).mpr
    (primedInteriorArc_component_unbounded w h hfin hb)



theorem primedBoundedFace_ambientFaceGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_ambientFaceGoal w hfin hb :=
  (primedBoundedFace_ambientFaceGoal_iff_deletedGeometryExclusion w hfin hb).mpr
    (primedBoundedFace_deletedGeometryExclusionGoal_holds w h hfin hb)




theorem iidCodes_ae_primedInteriorArc_component_unbounded :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (_h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
        ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
          (¬ limitExternalDart w (e, false) ∧ ¬ limitExternalDart w (e, true)) →
          (∀ k : ℤ, (edgeWest w e = boundaryVertex w hb k ∨
            edgeEast w e = boundaryVertex w hb k) →
              P.pos (boundaryVertex w hb k) ∈ Q.image) →
          ∀ a ∈ (P.arc (e, false)).interior,
            ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, primedInteriorArc_component_unbounded _ h hfin hb⟩




theorem iidCodes_ae_primedBoundedFace_deletedGeometryExclusionGoal :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (_h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        primedBoundedFace_deletedGeometryExclusionGoal w hfin hb ∧
          primedBoundedFace_ambientFaceGoal w hfin hb := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, primedBoundedFace_deletedGeometryExclusionGoal_holds _ h hfin hb,
    primedBoundedFace_ambientFaceGoal_holds _ h hfin hb⟩

end DirectedDistances.KMSW
