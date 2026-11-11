module

public import DirectedDistances.KMSW.KMSWStageDrawing
public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.StageBoundaryMap

/-! # Finite-stage KMSW exterior geometry

Finite-stage geometry toward Lemma 3.10 (`lem-uibot-bdy`, probability-one scope), using the
all-code monotone layout and the ordered finite-stage boundary word. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- Helper toward Lemma 3.10 (probability-one scope ruling); not a paper result.
Every code sequence has a compatible family of finite-stage drawings carrying -/
theorem kmswStageGeometry_monotone_family_all (w : ℕ → Fin 3) :
    ∃ Q : ∀ n, StageDrawing w n,
      Q 0 = kmswStage0Drawing w ∧
      (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
      ∀ n, Nonempty (MonotoneStageInvariant w n (Q n)) := by
  classical
  let hfam := monotone_family_all w
  let Q : ∀ n, StageDrawing w n := fun n =>
    monotoneLayoutDrawing w n (hfam n).choose
  refine ⟨Q, ?_, ?_, ?_⟩
  · have hh : (hfam 0).choose =
        layoutGood_of_invariant (kmswStage0MonotoneInvariant w) :=
      Subsingleton.elim _ _
    have hstage := eq_monotoneLayoutDrawing (kmswStage0Drawing w)
      (kmswStage0MonotoneInvariant w).pos_layout
      (by simpa [layoutDart] using (kmswStage0MonotoneInvariant w).arc_layout)
    change monotoneLayoutDrawing w 0 (hfam 0).choose = kmswStage0Drawing w
    rw [hh]
    exact hstage.symm
  · intro n
    exact stageExtends_monotoneLayout w n (hfam n).choose (hfam (n + 1)).choose
  · intro n
    exact ⟨Classical.choice (hfam n).choose_spec⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, probability-one scope); not a paper result.
For every code sequence, the finite-stage drawings extend one another and
have a unique unbounded face bordered exactly by the UL/UR false darts and
LL/LR true darts. Each LL edge is allocated geometrically but missing from
the directed map, and the outer-face word has the ordered four-run form -/
theorem kmswStageGeometry_induction_all (w : ℕ → Fin 3) :
    ∃ Q : ∀ n, StageDrawing w n,
      Q 0 = kmswStage0Drawing w ∧
      (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
      (∀ n, ∃ U : (Q n).Face,
        (Q n).IsUnbounded U ∧
        (∀ F : (Q n).Face, (Q n).IsUnbounded F → F = U) ∧
        ∀ d, (Q n).dartBorders d U ↔
          (d.2 = false ∧ d.1.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) ∨
          (d.2 = true ∧ d.1.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)) ∧
      (∀ n e, e ∈ (kmswStage w n).LL →
        ∃ he : e < (kmswStage w n).nextEdge,
          (stageEdgeTrace (Q n) e).Nonempty ∧
          (kmswStageDirectedMap w n).missing ((⟨e, he⟩, true))) ∧
      ∀ n, stageOuterWordVal w n =
        ((kmswStage w n).UL.map fun e => (e, false)) ++
        ((kmswStage w n).UR.map fun e => (e, false)) ++
        ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
        ((kmswStage w n).LL.reverse.map fun e => (e, true)) := by
  classical
  let hfam := monotone_family_all w
  let Q : ∀ n, StageDrawing w n := fun n =>
    monotoneLayoutDrawing w n (hfam n).choose
  let G : ∀ n, MonotoneStageInvariant w n (Q n) := fun n =>
    Classical.choice (hfam n).choose_spec
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : (hfam 0).choose =
        layoutGood_of_invariant (kmswStage0MonotoneInvariant w) :=
      Subsingleton.elim _ _
    have hdraw : Q 0 = monotoneLayoutDrawing w 0
        (layoutGood_of_invariant (kmswStage0MonotoneInvariant w)) := by
      change monotoneLayoutDrawing w 0 (hfam 0).choose = _
      rw [hh]
    have hstage := eq_monotoneLayoutDrawing (kmswStage0Drawing w)
      (kmswStage0MonotoneInvariant w).pos_layout
      (by simpa [layoutDart] using (kmswStage0MonotoneInvariant w).arc_layout)
    exact hdraw.trans hstage.symm
  · intro n
    exact stageExtends_monotoneLayout w n (hfam n).choose (hfam (n + 1)).choose
  · intro n
    obtain ⟨_, U, hU, hbound, huniq, hdart⟩ := G n |>.face_partition
    refine ⟨U, hbound, huniq, ?_⟩
    intro d
    rw [hdart, kmswStage_isOuter_iff_boundary]
  · intro n e he
    have hbound := stageRun_edge_bound w n e (Or.inl (Or.inr he))
    refine ⟨hbound, ?_, ?_⟩
    · refine ⟨((Q n).arc ((⟨e, hbound⟩, false))).start, ?_⟩
      simp only [stageEdgeTrace, dite_eq_left hbound]
      simp [Polyline.image]
    · exact ((kmswStageDirectedMap_LL_east w n ⟨e, hbound⟩).mpr he).1
  · intro n
    exact stageOuterWordVal_eq_runs w n

private theorem stageEdgeTrace_subset_image {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (e : ℕ) : stageEdgeTrace P e ⊆ P.image := by
  unfold stageEdgeTrace
  split
  · intro z hz
    exact Or.inr ⟨_, hz⟩
  · simp

private theorem monotoneCap_frontier_subset_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    frontier (G.cap i).region ⊆ P.image := by
  change frontier (graphRegion _ _ _ _) ⊆ P.image
  rw [frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
    (G.cap i).left_join (G.cap i).right_join]
  rw [(G.cap_lower_trace i), (G.cap_upper_trace i)]
  rintro z (hz | hz)
  · obtain ⟨e, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := Set.mem_iUnion.mp hz
    exact stageEdgeTrace_subset_image P e hz
  · obtain ⟨e, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := Set.mem_iUnion.mp hz
    exact stageEdgeTrace_subset_image P e hz

private theorem monotoneCap_subset_closedGraphRegion {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    (G.cap i).region ⊆
      closedGraphRegion G.xmin G.xmax G.lower G.upper := by
  rw [← G.cover]
  intro z hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, subset_closure hz⟩)

/-- Helper toward Lemma 3.10 (probability-one scope ruling); not a paper result.
The monotone invariant supplies open cap cells, their edge frontiers, and
the stage's unbounded exterior face (`def-kmsw`, -/
theorem MonotoneStageInvariant.stageGeom_cap_data {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ E : Set ℂ, ∃ cells : Fin (kmswStage w n).triangles.length → Set ℂ,
      E = (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ ∧
      (∀ i, cells i = (G.cap i).region) ∧
      (∀ i, IsOpen (cells i) ∧ Bornology.IsBounded (cells i) ∧
        Disjoint (cells i) E ∧ Disjoint (cells i) P.image ∧
        frontier (cells i) =
          stageEdgeTrace P ((kmswStage w n).triangles.get i).1 ∪
          stageEdgeTrace P ((kmswStage w n).triangles.get i).2.1 ∪
          stageEdgeTrace P ((kmswStage w n).triangles.get i).2.2) ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      IsOpen E ∧ IsConnected E ∧
      (∀ R : ℝ, ∃ z ∈ E, R < ‖z‖) ∧
      P.imageᶜ = E ∪ ⋃ i, cells i ∧
      ∃ U : P.Face, U.val = E ∧ P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d := by
  classical
  let C := G.toMonotoneStageCertificate
  let E : Set ℂ := (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ
  let cells : Fin (kmswStage w n).triangles.length → Set ℂ := fun i =>
    (G.cap i).region
  have hface := G.face_partition.2
  obtain ⟨U, hUeq, hUunbounded, hUunique, hUborder⟩ := hface
  refine ⟨E, cells, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change IsOpen ((G.cap i).region)
      exact isOpen_graphRegion (G.cap i).low_continuous (G.cap i).high_continuous
    · change Bornology.IsBounded ((G.cap i).region)
      exact isBounded_graphRegion (G.cap i).low_continuous
        (G.cap i).high_continuous (by
          intro x hx
          rcases lt_or_eq_of_le hx.1 with hxa | hxa
          · rcases lt_or_eq_of_le hx.2 with hxb | hxb
            · exact ((G.cap i).separated x ⟨hxa, hxb⟩).le
            · rw [hxb, (G.cap i).right_join]
          · rw [← hxa, (G.cap i).left_join])
    · change Disjoint ((G.cap i).region) E
      apply Set.disjoint_left.mpr
      intro z hzCap hzE
      exact hzE (monotoneCap_subset_closedGraphRegion G i hzCap)
    · change Disjoint ((G.cap i).region) P.image
      exact (C.cap_avoid i)
    · change frontier ((G.cap i).region) = _
      calc
        frontier (G.cap i).region =
            graphOver (G.cap i).a (G.cap i).b (G.cap i).low ∪
              graphOver (G.cap i).a (G.cap i).b (G.cap i).high :=
          frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
            (G.cap i).high_continuous (G.cap i).separated
            (G.cap i).left_join (G.cap i).right_join
        _ = (⋃ e ∈ C.capLower i, stageEdgeTrace P e) ∪
              ⋃ e ∈ C.capUpper i, stageEdgeTrace P e := by
          rw [C.cap_lower_trace i, C.cap_upper_trace i]
        _ = (⋃ e ∈ C.capLower i ++ C.capUpper i, stageEdgeTrace P e) := by
          apply Set.ext
          intro z
          simp only [Set.mem_union, Set.mem_iUnion]
          constructor
          · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
            · exact ⟨e, List.mem_append.mpr (Or.inl he), hz⟩
            · exact ⟨e, List.mem_append.mpr (Or.inr he), hz⟩
          · rintro ⟨e, he, hz⟩
            rcases List.mem_append.mp he with he | he
            · exact Or.inl ⟨e, he, hz⟩
            · exact Or.inr ⟨e, he, hz⟩
        _ = stageEdgeTrace P ((kmswStage w n).triangles.get i).1 ∪
              stageEdgeTrace P ((kmswStage w n).triangles.get i).2.1 ∪
              stageEdgeTrace P ((kmswStage w n).triangles.get i).2.2 := by
          apply Set.ext
          intro z
          simp only [Set.mem_union, Set.mem_iUnion]
          constructor
          · rintro ⟨e, he, hz⟩
            rcases (C.cap_edges i e).mp he with h | h | h
            · exact Or.inl (Or.inl (h ▸ hz))
            · exact Or.inl (Or.inr (h ▸ hz))
            · exact Or.inr (h ▸ hz)
          · intro h
            rcases h with h12 | h3
            · rcases h12 with h1 | h2
              · exact ⟨_, (C.cap_edges i _).mpr (Or.inl rfl), h1⟩
              · exact ⟨_, (C.cap_edges i _).mpr (Or.inr (Or.inl rfl)), h2⟩
            · exact ⟨_, (C.cap_edges i _).mpr (Or.inr (Or.inr rfl)), h3⟩
  · intro i j hij
    change Disjoint ((G.cap i).region) ((G.cap j).region)
    exact C.cap_disjoint i j hij
  · exact (isClosed_closedGraphRegion G.lower_continuous G.upper_continuous).isOpen_compl
  · exact (isPathConnected_compl_closedGraphRegion G.hx G.lower_continuous
      G.upper_continuous G.lower_le_upper).isConnected
  · intro R
    exact exists_norm_gt_compl_closedGraphRegion G.lower_continuous
      G.upper_continuous G.lower_le_upper R
  · change P.imageᶜ = E ∪ ⋃ i, (G.cap i).region
    have himage_closed : P.image ⊆
        closedGraphRegion G.xmin G.xmax G.lower G.upper := by
      rw [← G.cover]
      exact Set.subset_union_left
    ext z
    constructor
    · intro hz
      by_cases he : z ∈ E
      · exact Or.inl he
      · right
        have hclosed : z ∈ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
          by_contra hnot
          exact he (by simpa [E] using hnot)
        rw [← G.cover] at hclosed
        rcases hclosed with himage | hcaps
        · exact False.elim (hz himage)
        · obtain ⟨i, hci⟩ := Set.mem_iUnion.mp hcaps
          have hci' : z ∈ closure (G.cap i).region := by
            change z ∈ closure (C.cap i).region at hci
            exact hci
          rw [closure_eq_self_union_frontier] at hci'
          rcases hci' with hcell | hfront
          · exact Set.mem_iUnion.mpr ⟨i, hcell⟩
          · exact False.elim (hz (monotoneCap_frontier_subset_image G i hfront))
    · rintro (hE | hcell)
      · intro himage
        exact hE (himage_closed himage)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcell
        exact (Set.disjoint_left.mp (G.cap_avoid i)) hi
  · refine ⟨U, ?_, hUunbounded, ?_, ?_⟩
    · exact hUeq
    · exact hUunique
    · intro d
      exact hUborder d


end DirectedDistances.KMSW
