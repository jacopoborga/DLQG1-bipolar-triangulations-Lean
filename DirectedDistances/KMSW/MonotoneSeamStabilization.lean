module

public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneXminGrowth
public import DirectedDistances.KMSW.MonotoneStepAll

/-! Helper toward Theorem 1.4 (UIBOT plane realization for the M_{0,∞} identification, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Theorem 1.4 (UIBOT plane realization for the M_{0,∞} identification,
Lower-chain edges persist through every later KMSW stage. -/
theorem monotoneSeam_lower_edge_mem_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) :
    e ∈ (kmswStage w m).LL ++ (kmswStage w m).LR := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m _ ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL ++
      (kmswStep (kmswStage w m) (w m)).LR
    unfold kmswStep
    cases kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR with
      | nil =>
        simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
          List.mem_singleton] at *
        tauto
      | cons a as => simpa only [kmswStepOfStep, hs] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
          List.mem_cons] at *
        tauto

/-- Helper toward Theorem 1.4 (UIBOT plane realization for the M_{0,∞} identification,
The stage interval expands monotonically for any certified family. -/
theorem monotoneSeam_interval_mono (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {n m : ℕ} (hnm : n ≤ m) :
    (G m).xmin ≤ (G n).xmin ∧ (G n).xmax ≤ (G m).xmax := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ m hnm ih =>
    exact ⟨(monotoneStage_xmin_succ_anti w Q G m).trans ih.1,
      ih.2.trans (monotoneStage_xmax_succ_mono w Q G m)⟩

/-- Helper toward Theorem 1.4 (UIBOT plane realization for the M_{0,∞} identification,
A fixed point of the lower boundary stays in its domain and keeps its height. -/
theorem monotoneSeam_lower_stable (w : ℕ → Fin 3) (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (familyG w (monotone_family_all w) n).xmin
      (familyG w (monotone_family_all w) n).xmax) :
    ∀ m, n ≤ m →
      x ∈ Icc (familyG w (monotone_family_all w) m).xmin
        (familyG w (monotone_family_all w) m).xmax ∧
      (familyG w (monotone_family_all w) m).lower x =
        (familyG w (monotone_family_all w) n).lower x := by
  let hfam := monotone_family_all w
  let Q := familyQ w hfam
  let G := familyG w hfam
  change ∀ m, n ≤ m →
    x ∈ Icc (G m).xmin (G m).xmax ∧ (G m).lower x = (G n).lower x
  intro m hnm
  have hinterval := monotoneSeam_interval_mono w Q G hnm
  have hxm : x ∈ Icc (G m).xmin (G m).xmax :=
    ⟨hinterval.1.trans hx.1, hx.2.trans hinterval.2⟩
  let z : ℂ := ⟨x, (G n).lower x⟩
  have hz : z ∈ graphOver (G n).xmin (G n).xmax (G n).lower := by
    exact ⟨hx.1, hx.2, rfl⟩
  rw [(G n).lower_trace] at hz
  obtain ⟨e, hz⟩ := mem_iUnion.mp hz
  obtain ⟨heLower, hzTrace⟩ := mem_iUnion.mp hz
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heLower ⊢
      tauto)
  have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
    simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
  have hzArcQ : z ∈ ((Q n).arc
      (⟨⟨e, he⟩, false⟩ : StageDart (kmswStage w n).nextEdge)).image := by
    simpa only [stageEdgeTrace, dite_eq_left he] using hzTrace
  have hzArc : z ∈ (layoutArc w n e).image := by
    rw [hd] at hzArcQ
    exact hzArcQ
  have hstable (k : ℕ) (hnk : n ≤ k) : layoutArc w k e = layoutArc w n e := by
    induction k, hnk using Nat.le_induction with
    | base => rfl
    | succ k hnk ih =>
      rw [layoutArc_old w k e
        (he.trans_le (kmswStage_nextEdge_mono w hnk)), ih]
  have hzLater : z ∈ (layoutArc w m e).image := by
    rw [hstable m hnm]
    exact hzArc
  have hheight := (G m).lower_eq_arc_height
    (monotoneSeam_lower_edge_mem_mono w hnm heLower) hzLater
  refine ⟨hxm, ?_⟩
  simpa [z] using hheight

/-- Helper toward Theorem 1.4 (UIBOT plane realization for the M_{0,∞} identification,
An edge outside the lower chain has no interior point on the lower graph. -/
theorem monotoneSeam_nonlower_interior_not_lower_graph (w : ℕ → Fin 3)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    {n e : ℕ} (he : e < (kmswStage w n).nextEdge)
    (hne : e ∉ (kmswStage w n).LL ++ (kmswStage w n).LR) :
    ∀ z, z ∈ ((familyQ w hfam n).arc
      (⟨⟨e, he⟩, false⟩ : StageDart (kmswStage w n).nextEdge)).interior →
      z ∉ graphOver (familyG w hfam n).xmin (familyG w hfam n).xmax
        (familyG w hfam n).lower := by
  intro z hzInterior hzGraph
  let Q := familyQ w hfam
  let G := familyG w hfam
  change z ∈ ((Q n).arc (⟨⟨e, he⟩, false⟩ :
    StageDart (kmswStage w n).nextEdge)).interior at hzInterior
  change z ∈ graphOver (G n).xmin (G n).xmax (G n).lower at hzGraph
  let d : StageDart (kmswStage w n).nextEdge := (⟨e, he⟩, false)
  have hgood : LayoutGood w n := layoutGood_of_invariant (G n)
  rw [(G n).lower_trace] at hzGraph
  obtain ⟨f, hzTrace⟩ := mem_iUnion.mp hzGraph
  obtain ⟨hfLower, hzTrace⟩ := mem_iUnion.mp hzTrace
  have hf : f < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by
      simp only [List.mem_append] at hfLower ⊢
      tauto)
  let fd : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, false)
  have hzF : z ∈ ((Q n).arc fd).image := by
    simpa only [stageEdgeTrace, dite_eq_left hf] using hzTrace
  have hfd : fd ≠ d := by
    intro h
    have hv : f = e := by
      simpa only [fd, d] using
        congrArg (fun a : StageDart (kmswStage w n).nextEdge => a.1.val) h
    exact hne (hv ▸ hfLower)
  have hflip : fd ≠ edgeFlip _ d := by
    intro h
    have hb := congrArg Prod.snd h
    change false = true at hb
    cases hb
  have hdj := hgood.interior_disjoint d fd hfd hflip
  rw [(G n).arc_layout d] at hzInterior
  have hzLayoutInterior := hzInterior
  by_cases hzFInterior : z ∈ ((Q n).arc fd).interior
  · rw [(G n).arc_layout fd] at hzFInterior
    exact (Set.disjoint_left.mp hdj) hzLayoutInterior hzFInterior
  · have hEnds : z = ((Q n).arc fd).start ∨ z = ((Q n).arc fd).finish := by
      by_contra h
      apply hzFInterior
      simp only [Polyline.interior, Set.mem_sdiff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact ⟨hzF, fun hp => h (by simpa using hp)⟩
    rcases hEnds with hStart | hFinish
    · let v := stageVertex w n fd
      have hpos : layoutPos w n v.val = z := by
        calc
          layoutPos w n v.val = (Q n).pos v := (G n).pos_layout v |>.symm
          _ = ((Q n).arc fd).start := ((Q n).arc_start fd).symm
          _ = z := hStart.symm
      have hzVertex := hzLayoutInterior
      rw [← hpos] at hzVertex
      exact hgood.interior_avoids_vertices d v hzVertex
    · let v := stageVertex w n (edgeFlip _ fd)
      have hpos : layoutPos w n v.val = z := by
        calc
          layoutPos w n v.val = (Q n).pos v := (G n).pos_layout v |>.symm
          _ = ((Q n).arc fd).finish := ((Q n).arc_finish fd).symm
          _ = z := hFinish.symm
      have hzVertex := hzLayoutInterior
      rw [← hpos] at hzVertex
      exact hgood.interior_avoids_vertices d v hzVertex

end DirectedDistances.KMSW
