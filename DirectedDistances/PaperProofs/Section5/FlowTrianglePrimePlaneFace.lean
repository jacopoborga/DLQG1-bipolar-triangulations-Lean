module
public import DirectedDistances.KMSW.MhatPrimeDrawing
public import DirectedDistances.PlanarMap.PlaneFaceSurvival
public import DirectedDistances.KMSW.CreationCapExactFrontier
public import DirectedDistances.KMSW.MhatPrimeAmbientFace
public import DirectedDistances.KMSW.FlowTriangleRetainedEdges
public section
namespace DirectedDistances.PaperProofs.Section5
open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open scoped Topology
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Reversing a geometric arc preserves its trace. -/
private theorem primeFace_reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · have hz' : z = p.finish := by
      simpa only [Polyline.start_reverse, Set.mem_singleton_iff] using hz
    rw [hz', ← p.point_last_eq_finish]
    by_cases hlen : 2 ≤ p.points.length
    · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
      have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
      rw [Polyline.segmentAt, hidx]
      exact right_mem_segment ℝ _ _
    · have hlen1 : p.points.length = 1 := by
        have := List.length_pos_iff.mpr p.nonempty
        omega
      simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
      exact Or.inl rfl
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
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The two dart orientations have the same trace. -/
private theorem primeFace_reverse_image (p : Polyline) : p.reverse.image = p.image := by
  apply Set.Subset.antisymm (primeFace_reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using primeFace_reverse_image_subset p.reverse
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The later third edge has an unreachable initial vertex, since it precedes the next -/
theorem flowTriangleLaterThirdEdgePrimeGeom : flowTriangleLaterThirdEdgePrimeGeomGoal := by
  intro w hfin hb h k hk
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hspec := (walkNR_succ_spec w h (k - 2)).1
  have hnot := lPhase_activeWest_unreachable w h (k - 2)
    (walkNR w h (k - 1) - 1) (by rw [hindex] at hspec; omega)
    (by rw [hindex]; rw [hindex] at hspec; omega)
  apply Or.inl
  intro hgeom
  have hwest := hgeom.1
  change Quiver.Reachable (⟨0⟩ : PresentVertex w)
    ⟨edgeWest w (act w (sourceFlowNR w h (k - 1) - 1))⟩ at hwest
  rw [← (edge_endpoints_eq w (act_lt_nextEdge w
    (le_rfl : sourceFlowNR w h (k - 1) - 1 ≤ _))).1] at hwest
  rw [sourceFlowNR_eq_walkNR] at hwest
  exact hnot hwest
variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
All three source edge identities, including initial triangle convention's initial missing edge, survive in -/
theorem flowTriangle_three_retained (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let e := if k = 1 then (kmswStage w (t - 1)).nextEdge + 1 else act w (r - 1)
    primeGeomEdge w hfin hb (act w (t - 1)) ∧
      primeGeomEdge w hfin hb (act w t) ∧ primeGeomEdge w hfin hb e := by
  refine ⟨(flowLineTimes_oldActive_primeMissingEdge w hfin hb h k hk).1,
    Or.inl (flowLineTimes_newActive_primePresentEdge w hfin hb h k hk).2, ?_⟩
  by_cases hk1 : k = 1
  · subst k
    simpa only [Nat.sub_zero, ite_true] using
      (flowLineTimes_initialThird_primeMissingEdge w hfin hb h).1
  · simp only [hk1, ite_false]
    exact flowTriangleLaterThirdEdgePrimeGeom w hfin hb h k (by omega)
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every source flow triangle is a bounded face of the restricted primed drawing,
with its exact creation cap, oriented borders, and edge multiset. -/
theorem flowTriangle_prime_plane_face (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let e := if k = 1 then (kmswStage w (t - 1)).nextEdge + 1 else act w (r - 1)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ j : TriangleCreationTime w,
      j.val = t - 1 ∧ j.val + 1 = t ∧
      stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
      ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
        (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
        ∃ G : MhatPrimeFaces w hfin hb (monotone_family_all w),
          G.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
          ∃ ds : List (RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb)),
            ds.length = 3 ∧
            (↑(ds.map (fun d =>
              (restrictedDartEquivPrimeDart w hfin hb d).1.val)) : Multiset ℕ) =
                {act w (t - 1), act w t, e} ∧
            frontier G.val.val = ⋃ d ∈ ds, (Q.arc d).image ∧
            ∀ d ∈ ds, Q.dartBorders d G.val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨j, hj, hjtime, hrecord, i, hi⟩ :=
    flowLineTimes_triangle_creation_record w h k hk
  obtain ⟨hold, hnew, hthird⟩ := flowTriangle_three_retained w hfin hb h k hk
  have hret : ∀ e, e ∈ ({(stageTriangleRecord w j).1,
      (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2} : Multiset ℕ) →
      primeGeomEdge w hfin hb e := by
    intro e he
    rw [hrecord] at he
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hold
    · exact hnew
    · exact hthird
  have htrace (e : ℕ) (he : primeGeomEdge w hfin hb e) :
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) e ⊆ Q.image := by
    intro z hz
    unfold stageEdgeTrace at hz
    split_ifs at hz with halloc
    · let d : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb) := ⟨(e, false), he⟩
      change z ∈ Set.range Q.pos ∪ {z | ∃ d, z ∈ (Q.arc d).image}
      refine Or.inr ⟨d, ?_⟩
      rw [mhatPrimeDrawing_arc, familyDrawing_arc w hfin (monotone_family_all w)
        (j.val + 1) (⟨e, halloc⟩, false)]
      exact hz
    · exact hz.elim
  obtain ⟨F, hF, hborders, _, _⟩ := mhatPrimeTriangleFace_ambient_face w hfin j i hi
  have hopen : IsOpen F.val.val := by
    rw [hF]
    exact isOpen_graphRegion
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).low_continuous
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).high_continuous
  have hfront : frontier F.val.val ⊆ Q.image := by
    rw [hF, creationCap_frontier_eq_traces w j i hi]
    apply Set.union_subset
    · apply Set.union_subset
      · exact htrace _ (hret _ (by simp))
      · exact htrace _ (hret _ (by simp))
    · exact htrace _ (hret _ (by simp))
  obtain ⟨G, hG⟩ := planeFace_survives P Q F hopen
    (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)) hfront
  have hdret : ∀ d ∈ stageTriangleDartList w j, primeGeomEdge w hfin hb d.1 := by
    intro d hd
    apply hret
    rw [← stageTriangleDartTriple_edges_eq_record w j]
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp
  let ds := (stageTriangleDartList w j).attach.map fun d =>
    (⟨d.val, hdret d.val d.property⟩ : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb))
  have hmap : ds.map (fun d => d.val.1) =
      (stageTriangleDartList w j).map Prod.fst := by
    simp only [ds, List.map_map]
    change (stageTriangleDartList w j).attach.map (fun d => d.val.1) = _
    exact List.attach_map_val
  have hids : (↑(ds.map (fun d => d.val.1)) : Multiset ℕ) =
      {(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
        (stageTriangleRecord w j).2.2} := by
    rw [hmap]
    exact stageTriangleDartTriple_edges_eq_record w j
  have harcimage (d : ℕ × Bool) : (P.arc d).image = (P.arc (d.1, false)).image := by
    rcases d with ⟨e, b⟩
    cases b
    · rfl
    · have heq : P.arc (e, true) = (P.arc (e, false)).reverse := P.arc_flip (e, false)
      rw [heq, primeFace_reverse_image]
  have hdsTrace : ∀ d ∈ ds, (Q.arc d).image =
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) d.val.1 := by
    intro d hd
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hd
    have halloc := stageTriangleDartList_lt w (j.val + 1) j
      (Nat.lt_succ_self _) a.val a.property
    rw [mhatPrimeDrawing_arc, harcimage]
    unfold stageEdgeTrace
    rw [dite_eq_left halloc, ← familyDrawing_arc w hfin (monotone_family_all w)
      (j.val + 1) (⟨a.val.1, halloc⟩, false)]
  refine ⟨j, hj, hjtime, hrecord, i, hi, G, hG.trans hF, ds, ?_, ?_, ?_, ?_⟩
  · simp [ds, stageTriangleDartList]
  · change (↑(ds.map (fun d => d.val.1)) : Multiset ℕ) = _
    rw [hids, hrecord]
  · rw [hG, hF, creationCap_frontier_eq_traces w j i hi]
    ext z
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · intro hz
      have hex : ∃ e ∈ ({(stageTriangleRecord w j).1,
          (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2} : Multiset ℕ),
          z ∈ stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) e := by
        rcases hz with (hz | hz) | hz
        · exact ⟨_, by simp, hz⟩
        · exact ⟨_, by simp, hz⟩
        · exact ⟨_, by simp, hz⟩
      obtain ⟨e, he, hz⟩ := hex
      rw [← hids] at he
      change e ∈ ds.map (fun d => d.val.1) at he
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact ⟨d, hd, (hdsTrace d hd).symm ▸ hz⟩
    · rintro ⟨d, hd, hz⟩
      rw [hdsTrace d hd] at hz
      have he : d.val.1 ∈ ({(stageTriangleRecord w j).1,
          (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2} : Multiset ℕ) := by
        rw [← hids]
        exact List.mem_map.mpr ⟨d, hd, rfl⟩
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
      rcases he with he | he | he
      · exact Or.inl (Or.inl (he ▸ hz))
      · exact Or.inl (Or.inr (he ▸ hz))
      · exact Or.inr (he ▸ hz)
  · intro d hd
    obtain ⟨a, ha, had⟩ := List.mem_map.mp hd
    subst d
    exact dartBorders_transport P Q F.val G.val a.val _ hG
      (mhatPrimeDrawing_arc w hfin hb (monotone_family_all w) _) (hborders _ a.property)
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The three geometric PrimeDarts border the surviving face through the drawing's -/
theorem flowTriangle_prime_darts_border_face (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let e := if k = 1 then (kmswStage w (t - 1)).nextEdge + 1 else act w (r - 1)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    let f := restrictedDartEquivPrimeDart w hfin hb
    ∃ G : MhatPrimeFaces w hfin hb (monotone_family_all w),
      ∃ ds : List (PrimeDart w hfin hb),
        ds.length = 3 ∧
        (↑(ds.map (fun d => d.1.val)) : Multiset ℕ) =
          {act w (t - 1), act w t, e} ∧
        frontier G.val.val = ⋃ d ∈ ds, (Q.arc (f.symm d)).image ∧
        ∀ d ∈ ds, Q.dartBorders (f.symm d) G.val := by
  obtain ⟨_, _, _, _, _, _, G, _, ds, hlen, hids, hfront, hborders⟩ :=
    flowTriangle_prime_plane_face w hfin hb h k hk
  let f := restrictedDartEquivPrimeDart w hfin hb
  refine ⟨G, ds.map f, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hlen
  · simpa only [List.map_map, Function.comp_def] using hids
  · rw [hfront]
    ext z
    simp only [Set.mem_iUnion, List.mem_map]
    constructor
    · rintro ⟨d, hd, hz⟩
      exact ⟨f d, ⟨d, hd, rfl⟩, by simpa only [f, Equiv.symm_apply_apply] using hz⟩
    · rintro ⟨p, ⟨d, hd, rfl⟩, hz⟩
      exact ⟨d, hd, by simpa only [f, Equiv.symm_apply_apply] using hz⟩
  · intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    simpa only [f, Equiv.symm_apply_apply] using hborders d hd
/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
On the provider's single almost-sure event all source indices simultaneously have -/
theorem flowTriangle_ae_prime_plane_faces :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hb : BoundaryHitWitnesses w,
      ∃ h : HasFlowLineHits w,
        FlowLineTimesJointMinima w h ∧ FlowLineTimesItemI w h ∧
        FlowLineTimesItemII w hfin hb h ∧
        ∀ k, 1 ≤ k →
          let r := sourceFlowNR w h (k - 1)
          let t := sourceFlowNL w h (k - 1)
          let e := if k = 1 then (kmswStage w (t - 1)).nextEdge + 1 else act w (r - 1)
          let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
          ∃ j : TriangleCreationTime w,
            j.val = t - 1 ∧ j.val + 1 = t ∧
            stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
            ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
              (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
              ∃ G : MhatPrimeFaces w hfin hb (monotone_family_all w),
                G.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
                ∃ ds : List (RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb)),
                  ds.length = 3 ∧
                  (↑(ds.map (fun d =>
                    (restrictedDartEquivPrimeDart w hfin hb d).1.val)) : Multiset ℕ) =
                      {act w (t - 1), act w t, e} ∧
                  frontier G.val.val = ⋃ d ∈ ds, (Q.arc d).image ∧
                  ∀ d ∈ ds, Q.dartBorders d G.val := by
  filter_upwards [lemma_5_12_provider] with ω hprovider
  obtain ⟨hfin, hb, h, hmin, hitemI, hitemII, _⟩ := hprovider
  exact ⟨hfin, hb, h, hmin, hitemI, hitemII,
    flowTriangle_prime_plane_face (fun i => ω (i + 1)) hfin hb h⟩
end DirectedDistances.PaperProofs.Section5
