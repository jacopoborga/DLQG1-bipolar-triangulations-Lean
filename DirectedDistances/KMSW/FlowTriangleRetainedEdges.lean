module

public import DirectedDistances.KMSW.MhatPrimeGeometricCarrier
public import DirectedDistances.KMSW.MhatPrimeAmbientFace
public import DirectedDistances.KMSW.MhatPrimeFaceSource
public import DirectedDistances.PaperProofs.Section5.FlowLineTimesLemma

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section5
open Quiver

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The creation-time darts project in their stored cyclic order to exactly the -/
theorem flowLineTimes_triangle_dart_projection (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
    (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
    ∃ j : TriangleCreationTime w,
      j.val = t - 1 ∧ j.val + 1 = t ∧
      stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
      (stageTriangleDartList w j).length = 3 ∧
      (stageTriangleDartList w j).map Prod.fst =
        [(stageTriangleDartTriple w j).1.1,
          (stageTriangleDartTriple w j).2.1.1,
          (stageTriangleDartTriple w j).2.2.1] ∧
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
          {act w (t - 1), act w t, e} := by
  let r := sourceFlowNR w h (k - 1)
  let t := sourceFlowNL w h (k - 1)
  let s := kmswStage w (t - 1)
  let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
  obtain ⟨j, hj, hjtime, hrecord, _, _⟩ :=
    flowLineTimes_triangle_creation_record w h k hk
  refine ⟨j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [r, t] using hj
  · simpa only [r, t] using hjtime
  · simpa only [r, t, s, e] using hrecord
  · simp [stageTriangleDartList]
  · simp only [stageTriangleDartList, List.map_cons, List.map_nil]
  · have hEdges := stageTriangleDartTriple_edges_eq_record w j
    rw [hrecord] at hEdges
    simpa only [r, t, s, e] using hEdges

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The old active edge is retained as a missing β₀ edge -/
theorem flowLineTimes_oldActive_primeMissingEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
    (k : ℕ) (hk : 1 ≤ k) :
    primeMissingEdge w hfin hb
      (act w (sourceFlowNL w h (k - 1) - 1) : ℕ) := by
  obtain ⟨_, _, _, _, _, _, _, _, hstream⟩ :=
    flow_line_times_lemma_item_ii w hfin hb h k hk
  obtain ⟨n, hn⟩ := hstream
  have hbeta : primeBetaEdge w hfin hb
      (act w (sourceFlowNL w h (k - 1) - 1)) := ⟨n, hn⟩
  exact primeBetaEdge_primeMissingEdge w hfin hb _ hbeta

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The new active edge is present and leaves the reachable submap -/
theorem flowLineTimes_newActive_primePresentEdge (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
    (k : ℕ) (hk : 1 ≤ k) :
    let t := sourceFlowNL w h (k - 1)
    primePresentEdge w (act w t) := by
  let t := sourceFlowNL w h (k - 1)
  rcases flow_line_times_source_item_ii_geometry w h k hk with
    ⟨_, e, _, _, hpresent, hnot, _, _⟩
  have halloc : act w t < (kmswStage w t).nextEdge := by
    dsimp [t]
    exact act_lt_nextEdge w le_rfl
  have hnotWest : ¬ MhatVertex w (edgeWest w (act w t)) := by
    intro hreach
    change Reachable (⟨0⟩ : PresentVertex w)
      ⟨edgeWest w (act w t)⟩ at hreach
    change ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w t).west (act w t)⟩ at hnot
    have hend := (edge_endpoints_eq w halloc).1
    exact hnot (by simpa only [hend] using hreach)
  have hnotGeom : ¬ MhatGeometricEdge w (act w t) := by
    intro hgeom
    exact hnotWest hgeom.1
  exact ⟨EdgePresent.of_stage_present halloc hpresent, hnotGeom⟩



theorem flowLineTimes_initialThird_primeMissingEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    let t := sourceFlowNL w h 0
    let s := kmswStage w (t - 1)
    primeMissingEdge w hfin hb (s.nextEdge + 1) := by
  let t := sourceFlowNL w h 0
  let s := kmswStage w (t - 1)
  rcases flow_line_times_source_item_ii_first_geometry w h with
    ⟨_, _, _, _, _, _, healloc, _, hends, hnot, _⟩
  have hends' :
      ({(kmswStage w t).west (s.nextEdge + 1),
        (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) =
        {(kmswStage w t).west (act w t), s.west (act w (t - 1))} := by
    simpa only [t, s] using hends
  have hside : (kmswStage w t).west (act w t) =
      (kmswStage w t).west (s.nextEdge + 1) ∨
      (kmswStage w t).west (act w t) =
        (kmswStage w t).east (s.nextEdge + 1) := by
    have hmem : (kmswStage w t).west (act w t) ∈
        ({(kmswStage w t).west (s.nextEdge + 1),
          (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) := by
      rw [hends']
      simp
    simpa using hmem
  have hnotGeom : ¬ MhatGeometricEdge w (s.nextEdge + 1) := by
    intro hgeom
    have hreach : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ := by
      rcases hside with hwest | heast
      · have heq : edgeWest w (s.nextEdge + 1) =
          (kmswStage w t).west (act w t) := by
          exact (edge_endpoints_eq w healloc).1.symm.trans hwest.symm
        have hgeomWest : MhatVertex w (edgeWest w (s.nextEdge + 1)) := hgeom.1
        change Reachable (⟨0⟩ : PresentVertex w)
          ⟨edgeWest w (s.nextEdge + 1)⟩ at hgeomWest
        simpa only [heq] using hgeomWest
      · have heq : edgeEast w (s.nextEdge + 1) =
          (kmswStage w t).west (act w t) := by
          exact (edge_endpoints_eq w healloc).2.symm.trans heast.symm
        have hgeomEast : MhatVertex w (edgeEast w (s.nextEdge + 1)) := hgeom.2
        change Reachable (⟨0⟩ : PresentVertex w)
          ⟨edgeEast w (s.nextEdge + 1)⟩ at hgeomEast
        simpa only [heq] using hgeomEast
    exact hnot hreach
  have hnotPresent : ¬ EdgePresent w (s.nextEdge + 1) := by
    rcases flow_line_times_source_first_missing_persistent w h with
      ⟨_, _, _, hnotPresent⟩
    exact hnotPresent
  refine ⟨Or.inl hnotGeom, ?_⟩
  intro hpresent
  exact hnotPresent hpresent.1

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
For initial triangle convention's initial triangle, every oriented source dart has its corresponding -/
theorem flowLineTimes_initial_triangle_primeDarts (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    let t := sourceFlowNL w h 0
    let s := kmswStage w (t - 1)
    ∃ j : TriangleCreationTime w,
      j.val = t - 1 ∧ j.val + 1 = t ∧
      stageTriangleRecord w j = (act w (t - 1), act w t, s.nextEdge + 1) ∧
      (stageTriangleDartList w j).length = 3 ∧
      (stageTriangleDartList w j).map Prod.fst =
        [(stageTriangleDartTriple w j).1.1,
          (stageTriangleDartTriple w j).2.1.1,
          (stageTriangleDartTriple w j).2.2.1] ∧
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
          {act w (t - 1), act w t, s.nextEdge + 1} ∧
      ∀ d ∈ stageTriangleDartList w j,
        ∃ p : PrimeDart w hfin hb,
          p.1.1 = d.1 ∧ p.2 = d.2 := by
  let t := sourceFlowNL w h 0
  let s := kmswStage w (t - 1)
  obtain ⟨j, hj, hjtime, hrecordRaw, hlength, hmap, hidsRaw⟩ :=
    flowLineTimes_triangle_dart_projection w hfin hb h 1 (by omega)
  have hrecord : stageTriangleRecord w j =
      (act w (t - 1), act w t, s.nextEdge + 1) := by
    simpa only [Nat.sub_zero, ite_true, t, s] using hrecordRaw
  have hids :
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
          {act w (t - 1), act w t, s.nextEdge + 1} := by
    simpa only [Nat.sub_zero, ite_true, t, s] using hidsRaw
  have hold : primeMissingEdge w hfin hb (act w (t - 1)) := by
    simpa [t] using flowLineTimes_oldActive_primeMissingEdge w hfin hb h 1
      (by omega)
  have hnew : primePresentEdge w (act w t) := by
    simpa [t] using flowLineTimes_newActive_primePresentEdge w hfin hb h 1
      (by omega)
  have hthird : primeMissingEdge w hfin hb (s.nextEdge + 1) :=
    flowLineTimes_initialThird_primeMissingEdge w hfin hb h
  have hdartGeom : ∀ d ∈ stageTriangleDartList w j,
      primeGeomEdge w hfin hb d.1 := by
    intro d hd
    have hdid : d.1 = (stageTriangleDartTriple w j).1.1 ∨
        d.1 = (stageTriangleDartTriple w j).2.1.1 ∨
        d.1 = (stageTriangleDartTriple w j).2.2.1 := by
      have hd' : d ∈ [(stageTriangleDartTriple w j).1,
          (stageTriangleDartTriple w j).2.1, (stageTriangleDartTriple w j).2.2] := by
        simpa only [stageTriangleDartList] using hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with h₁ | h₂ | h₃
      · exact Or.inl (congrArg Prod.fst h₁)
      · exact Or.inr (Or.inl (congrArg Prod.fst h₂))
      · exact Or.inr (Or.inr (congrArg Prod.fst h₃))
    have hmember : d.1 ∈ ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) := by
      rcases hdid with h₁ | h₂ | h₃
      · rw [h₁]
        simp
      · rw [h₂]
        simp
      · rw [h₃]
        simp
    rw [hids] at hmember
    simp at hmember
    rcases hmember with h₁ | h₂ | h₃
    · rw [h₁]
      exact hold.1
    · rw [h₂]
      exact Or.inl hnew.2
    · rw [h₃]
      exact hthird.1
  refine ⟨j, hj, hjtime, hrecord, hlength, hmap, hids, ?_⟩
  intro d hd
  exact ⟨(⟨⟨d.1, hdartGeom d hd⟩, d.2⟩ : PrimeDart w hfin hb), rfl, rfl⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The later third edge is present in the original directed map -/
theorem flowLineTimes_laterThird_edgePresent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    EdgePresent w (act w (sourceFlowNR w h (k - 1) - 1)) := by
  apply EdgePresent.of_stage_present
  · exact act_lt_nextEdge w le_rfl
  · exact kmswStage_active_present w _

/- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The remaining later third edge is the smallest retained-carrier obligation -/
@[expose] def flowTriangleLaterThirdEdgePrimeGeomGoal : Prop :=
  ∀ (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
    (k : ℕ),
    2 ≤ k →
    primeGeomEdge w hfin hb (act w (sourceFlowNR w h (k - 1) - 1))

end DirectedDistances.KMSW
