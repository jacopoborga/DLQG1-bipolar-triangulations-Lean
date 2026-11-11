module

public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.StageTriangleDarts
public import DirectedDistances.PlanarMap.PlaneRealization

/-! # Bounded faces containing the creation triangles

Helpers toward Lemma 5.12 (`lem-flow-line-times`); not a paper result.
The realized drawing is `monotoneFamilyDrawing`
(`MonotoneStageFamily.lean:92-100`), used in
`KMSWConstructedRealizationProof.lean:34-37` and as the base of the Section
7.9 whole-plane drawing (`WholePlaneDrawingExtend.lean:101-104`). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Bounded components of the complement of a realized plane drawing.
Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def PlaneFaces {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) :=
  {F : P.Face // Bornology.IsBounded F.val}

/-- Every cap at a finite stage gives a bounded complementary component of the
all-stage realization. Helper toward Lemma 5.12 (lem-flow-line-times); not a
paper result. The drawing is the `monotoneFamilyDrawing` used by
`KMSWConstructedRealizationProof.lean:34-37` and the Section 7.9 base drawing
(`WholePlaneDrawingExtend.lean:101-104`); its definition is at
`MonotoneStageFamily.lean:92-100`. -/
theorem monotoneFamily_cap_planeFace (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (i : Fin (kmswStage w n).triangles.length) :
    ∃ F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)),
      F.val.val = ((familyG w (monotone_family_all w) n).cap i).region := by
  let hfam := monotone_family_all w
  let Q := familyQ w hfam
  let G := familyG w hfam
  let P := monotoneFamilyDrawing w hfin hfam
  have hfaces := monotoneLimit_cap_faces w hfin Q G P
    (familyDrawing_pos w hfin hfam) (familyDrawing_arc w hfin hfam)
    (family_cap_persistence w hfam)
  obtain ⟨F, hF, hb⟩ := hfaces n i
  exact ⟨⟨F, hb⟩, hF⟩

/-- A triangle creation time indexes one of the stored triangles at the next
stage. Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
`DirectedDistances/KMSW/StageTriangleDarts.lean`. -/
theorem stageTriangleRecord_fin_index (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j := by
  have hmem : stageTriangleRecord w j ∈
      (kmswStage w (j.val + 1)).triangles := by
    rw [← stageTriangleTimes_records]
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    rw [mem_stageTriangleTimes]
    omega
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
  exact ⟨⟨i, hi⟩, by simpa using heq⟩

/-- The oriented creation triple has the edge-ID multiset stored at its
creation time. Helper toward Lemma 5.12 (lem-flow-line-times); not a paper -/
theorem stageTriangleDartTriple_edges_eq_record (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    ({(stageTriangleDartTriple w j).1.1,
      (stageTriangleDartTriple w j).2.1.1,
      (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
      {(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
        (stageTriangleRecord w j).2.2} := by
  rcases j.property with h0 | h1
  · by_cases hl : (kmswStage w j.val).UL.dropLast.reverse = []
    · simp [stageTriangleDartTriple, stageTriangleRecord, h0, hl]
    · cases hl' : (kmswStage w j.val).UL.dropLast.reverse with
      | nil => exact (hl hl').elim
      | cons e es =>
        simp only [stageTriangleDartTriple, stageTriangleRecord, h0, hl', ↓reduceIte]
        simp only [Multiset.insert_eq_cons]
        rw [Multiset.cons_swap e (kmswStage w j.val).active
          {(kmswStage w j.val).nextEdge}]
        congr 1
        exact Multiset.pair_comm _ _
  · simp [stageTriangleDartTriple, stageTriangleRecord, h1]
    exact Multiset.pair_comm _ _

/-- Every creation-time triangle's stored cap has a bounded limit component.
Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. This
uses the all-stage `monotoneFamilyDrawing` realization and the stage cap
certificate (`MonotoneStageCertificate.lean:85-109`), then
`monotoneLimit_cap_faces` (`MonotoneLimitFaces.lean:459-484`). -/
theorem monotoneFamily_creation_cap_planeFace (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
      ∃ F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)),
        F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
        (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
        (∀ e, e ∈ (familyG w (monotone_family_all w) (j.val + 1)).capLower i ++
            (familyG w (monotone_family_all w) (j.val + 1)).capUpper i ↔
          e = (stageTriangleRecord w j).1 ∨
            e = (stageTriangleRecord w j).2.1 ∨
            e = (stageTriangleRecord w j).2.2) ∧
        ({(stageTriangleDartTriple w j).1.1,
          (stageTriangleDartTriple w j).2.1.1,
          (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
          {(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
            (stageTriangleRecord w j).2.2} := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  obtain ⟨F, hF⟩ := monotoneFamily_cap_planeFace w hfin (j.val + 1) i
  have hEdges := (familyG w (monotone_family_all w) (j.val + 1)).cap_edges i
  rw [hi] at hEdges
  exact ⟨i, F, hF, hi, hEdges, stageTriangleDartTriple_edges_eq_record w j⟩

/-- Every edge of the creation-time dart triple occurs in the associated cap's
combined lower/upper edge list. Helper toward Lemma 5.12 (lem-flow-line-times);
not a paper result. -/
theorem stageTriangleDarts_mem_creation_cap_edge_union (w : ℕ → Fin 3)
    (j : TriangleCreationTime w)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    ∀ d ∈ stageTriangleDartList w j,
      d.1 ∈ (familyG w (monotone_family_all w) (j.val + 1)).capLower i ++
        (familyG w (monotone_family_all w) (j.val + 1)).capUpper i := by
  intro d hd
  have hmem : d.1 ∈
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd
    · subst d
      simp
    · subst d
      simp
    · subst d
      simp
  rw [stageTriangleDartTriple_edges_eq_record w j] at hmem
  have hmem' : d.1 = (stageTriangleRecord w j).1 ∨
      d.1 = (stageTriangleRecord w j).2.1 ∨
      d.1 = (stageTriangleRecord w j).2.2 := by
    simpa only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] using hmem
  exact ((familyG w (monotone_family_all w) (j.val + 1)).cap_edges i d.1).2
    (by rw [hi]; exact hmem')

end DirectedDistances.KMSW
