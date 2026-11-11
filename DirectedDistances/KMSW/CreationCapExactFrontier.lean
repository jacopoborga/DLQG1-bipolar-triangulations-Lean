module

public import DirectedDistances.KMSW.KMSWStageDrawing
public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.StageTriangleDarts
public import DirectedDistances.PlanarMap.GraphRegionClosure

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The cap frontier is exactly the traces of its three stored creation edges. -/
theorem creationCap_frontier_eq_traces (w : ℕ → Fin 3)
    (j : TriangleCreationTime w)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    frontier ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region =
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).1 ∪
        stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).2.1 ∪
        stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).2.2 := by
  let G := familyG w (monotone_family_all w) (j.val + 1)
  let P := familyQ w (monotone_family_all w) (j.val + 1)
  let C := G.cap i
  have hboundary :
      graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high =
        stageEdgeTrace P (stageTriangleRecord w j).1 ∪
          stageEdgeTrace P (stageTriangleRecord w j).2.1 ∪
          stageEdgeTrace P (stageTriangleRecord w j).2.2 := by
    have hedge (e : ℕ) :
        e ∈ G.capLower i ++ G.capUpper i ↔
          e = (stageTriangleRecord w j).1 ∨
            e = (stageTriangleRecord w j).2.1 ∨
            e = (stageTriangleRecord w j).2.2 := by
      rw [G.cap_edges i e, hi]
    ext z
    rw [G.cap_lower_trace i, G.cap_upper_trace i]
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
      · have ht := (hedge e).mp (List.mem_append.mpr (Or.inl he))
        rcases ht with h | h | h
        · subst e
          exact Or.inl (Or.inl hz)
        · subst e
          exact Or.inl (Or.inr hz)
        · subst e
          exact Or.inr hz
      · have ht := (hedge e).mp (List.mem_append.mpr (Or.inr he))
        rcases ht with h | h | h
        · subst e
          exact Or.inl (Or.inl hz)
        · subst e
          exact Or.inl (Or.inr hz)
        · subst e
          exact Or.inr hz
    · rintro ((hz | hz) | hz)
      · have he := (hedge (stageTriangleRecord w j).1).mpr (Or.inl rfl)
        rcases List.mem_append.mp he with he | he
        · exact Or.inl ⟨_, he, hz⟩
        · exact Or.inr ⟨_, he, hz⟩
      · have he := (hedge (stageTriangleRecord w j).2.1).mpr
          (Or.inr (Or.inl rfl))
        rcases List.mem_append.mp he with he | he
        · exact Or.inl ⟨_, he, hz⟩
        · exact Or.inr ⟨_, he, hz⟩
      · have he := (hedge (stageTriangleRecord w j).2.2).mpr
          (Or.inr (Or.inr rfl))
        rcases List.mem_append.mp he with he | he
        · exact Or.inl ⟨_, he, hz⟩
        · exact Or.inr ⟨_, he, hz⟩
  calc
    frontier C.region = graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high := by
      exact frontier_graphRegion_eq C.ab C.low_continuous C.high_continuous
        C.separated C.left_join C.right_join
    _ = stageEdgeTrace P (stageTriangleRecord w j).1 ∪
          stageEdgeTrace P (stageTriangleRecord w j).2.1 ∪
          stageEdgeTrace P (stageTriangleRecord w j).2.2 := hboundary

end DirectedDistances.KMSW
