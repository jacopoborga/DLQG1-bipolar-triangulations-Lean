module

public import DirectedDistances.KMSW.HatFaceVertices
public import DirectedDistances.KMSW.StageOuterCycle

/-! # Oriented inner faces of the hatted KMSW map

Hatted-half helpers for `lem-quad-kmsw` -/

public section
namespace DirectedDistances.KMSW

/-- The hatted stage embedding on geometric darts preserves their west/east side -/
@[expose] noncomputable def hatDartMap (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    StageDart (kmswStage w (quadrantRStageTime w h m)).nextEdge :=
  (⟨hatAllEdgeMap w h m d.1.val,
    (hatAll_sim w h m).incidenceSim.edge_bound _ d.1.isLt⟩, d.2)

/-- No geometric darts are identified by the hatted embedding -/
theorem hatDartMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    Function.Injective (hatDartMap w h m) := by
  intro d e heq
  apply Prod.ext
  · apply Fin.ext
    exact (hatAll_sim w h m).incidenceSim.edge_injective _ _ d.1.isLt e.1.isLt
      (congrArg (fun x => x.1.val) heq)
  · exact congrArg (fun x : StageDart (kmswStage w (quadrantRStageTime w h m)).nextEdge => x.2) heq

/-- Edge reversal commutes with the hatted dart embedding -/
theorem hatDartMap_edgeInv (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    (kmswMap w (quadrantRStageTime w h m)).edgeInv (hatDartMap w h m d) =
      hatDartMap w h m ((kmswMap (hatCodes w h) m).edgeInv d) := rfl

private theorem record_east_eq_iff (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  have hjmem : stageTriangleRecord w j ∈ (kmswStage w (j.val + 1)).triangles := by
    rw [← stageTriangleTimes_records]
    exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes w _ j).mpr (Nat.lt_succ_self _), rfl⟩
  have hb := triBound_stage w (j.val + 1) _ hjmem
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
      State.addEdge, hne, hne', ne_of_lt hv]

/-- The oriented boundary of a stored triangle, starting at its old active west
 dart. The endpoint test distinguishes left creation from up creation -/
@[expose] def triangleOrientedDarts (w : ℕ → Fin 3) (t : ℕ × ℕ × ℕ) :
    List (ℕ × Bool) :=
  if edgeEast w t.1 = edgeEast w t.2.1 then
    [(t.1, false), (t.2.1, true), (t.2.2, false)]
  else [(t.1, false), (t.2.2, true), (t.2.1, true)]

/-- The canonical oriented triangle darts, typed at a stage containing the face -/
@[expose] def triangleDartCycle (w : ℕ → Fin 3) (n : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w n).triangles) :
    StageDart (kmswStage w n).nextEdge ×
      StageDart (kmswStage w n).nextEdge × StageDart (kmswStage w n).nextEdge :=
  let hb := triBound_stage w n t ht
  if edgeEast w t.1 = edgeEast w t.2.1 then
    ((⟨t.1, hb.1⟩, false), (⟨t.2.1, hb.2.1⟩, true), (⟨t.2.2, hb.2.2⟩, false))
  else
    ((⟨t.1, hb.1⟩, false), (⟨t.2.2, hb.2.2⟩, true), (⟨t.2.1, hb.2.1⟩, true))

/-- The value word of the typed canonical cycle is its oriented boundary word -/
theorem triangleDartCycle_values (w : ℕ → Fin 3) (n : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w n).triangles) :
    let c := triangleDartCycle w n t ht
    [(c.1.1.val, c.1.2), (c.2.1.1.val, c.2.1.2), (c.2.2.1.val, c.2.2.2)] =
      triangleOrientedDarts w t := by
  unfold triangleDartCycle triangleOrientedDarts
  split <;> rfl

/-- The canonical cycle follows the actual finite-stage face successor
(hatted-half helper for `lem-quad-kmsw`, -/
theorem triangleDartCycle_isFace (w : ℕ → Fin 3) (n : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w n).triangles) :
    FaceSucc3Cycle (kmswMap w n).faceSucc
      (triangleDartCycle w n t ht).1 (triangleDartCycle w n t ht).2.1
      (triangleDartCycle w n t ht).2.2 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ((stageTriangleTimes_records w n).symm ▸ ht)
  have hjn := (mem_stageTriangleTimes w n j).mp hj
  have cyc := stageTriangle_isFace w j n hjn
  have heq := record_east_eq_iff w j
  rcases j.property with h0 | h1
  · have he := heq.mpr h0
    cases hp : (kmswStage w j.val).UL.dropLast.reverse with
    | nil =>
      dsimp only [triangleDartCycle]
      rw [ite_eq_left he]
      simpa only [stageTriangleRecord, h0, ↓reduceIte,
        hp, stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
        stageTriangleDartAt, stageTriangleDartTriple] using cyc
    | cons e es =>
      have cy : FaceSucc3Cycle (kmswMap w n).faceSucc
          (triangleDartCycle w n (stageTriangleRecord w j) ht).2.2
          (triangleDartCycle w n (stageTriangleRecord w j) ht).1
          (triangleDartCycle w n (stageTriangleRecord w j) ht).2.1 := by
        dsimp only [triangleDartCycle]
        rw [ite_eq_left he]
        simpa only [stageTriangleRecord, h0, ↓reduceIte,
          hp, stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
          stageTriangleDartAt, stageTriangleDartTriple] using cyc
      exact ⟨cy.2.1, cy.2.2.1, cy.1, cy.2.2.2.2.1, cy.2.2.2.2.2, cy.2.2.2.1⟩
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    have he : edgeEast w (stageTriangleRecord w j).1 ≠
        edgeEast w (stageTriangleRecord w j).2.1 := fun hh => h0 (heq.mp hh)
    dsimp only [triangleDartCycle]
    rw [ite_eq_right he]
    simpa only [stageTriangleRecord, h0, ↓reduceIte,
      stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
      stageTriangleDartAt, stageTriangleDartTriple] using cyc

private theorem hat_east_eq_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m a b : ℕ) (ha : a < (kmswStage (hatCodes w h) m).nextEdge)
    (hb : b < (kmswStage (hatCodes w h) m).nextEdge) :
    edgeEast w (hatAllEdgeMap w h m a) = edgeEast w (hatAllEdgeMap w h m b) ↔
      edgeEast (hatCodes w h) a = edgeEast (hatCodes w h) b := by
  have hs := (hatAll_sim w h m).incidenceSim
  rw [← (edge_endpoints_eq w (hs.edge_bound a ha)).2,
    ← (edge_endpoints_eq w (hs.edge_bound b hb)).2,
    (hs.incidence a ha).2, (hs.incidence b hb).2,
    ← (edge_endpoints_eq (hatCodes w h) ha).2,
    ← (edge_endpoints_eq (hatCodes w h) hb).2]
  exact ⟨hs.vertex_injective _ _
    (kmswStage_endpoints_lt_nextVertex _ m a ha).2
    (kmswStage_endpoints_lt_nextVertex _ m b hb).2, congrArg _⟩

/-- The hatted embedding carries the entire ordered triangle cycle to the
canonical global cycle, with its side bits unchanged (`lem-quad-kmsw`, -/
theorem hatDartMap_triangleDartCycle (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage (hatCodes w h) m).triangles) :
    let c := triangleDartCycle (hatCodes w h) m t ht
    (hatDartMap w h m c.1, hatDartMap w h m c.2.1, hatDartMap w h m c.2.2) =
      triangleDartCycle w (quadrantRStageTime w h m)
        (hatAllEdgeMap w h m t.1, hatAllEdgeMap w h m t.2.1,
          hatAllEdgeMap w h m t.2.2) (hatAll_triSim w h m t ht) := by
  have hb := triBound_stage (hatCodes w h) m t ht
  have he := hat_east_eq_iff w h m t.1 t.2.1 hb.1 hb.2.1
  dsimp only
  unfold triangleDartCycle
  by_cases hl : edgeEast (hatCodes w h) t.1 = edgeEast (hatCodes w h) t.2.1
  · rw [ite_eq_left hl, ite_eq_left (he.mpr hl)]
    rfl
  · rw [ite_eq_right hl, ite_eq_right (fun hh => hl (he.mp hh))]
    rfl

/-- On every dart of every stored local triangle, the hatted embedding commutes
with the actual face successor. This is inner-face rotation compatibility
for the hatted half of `lem-quad-kmsw` -/
theorem hatDartMap_faceSucc (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage (hatCodes w h) m).triangles)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : d ∈ [(triangleDartCycle (hatCodes w h) m t ht).1,
      (triangleDartCycle (hatCodes w h) m t ht).2.1,
      (triangleDartCycle (hatCodes w h) m t ht).2.2]) :
    (kmswMap w (quadrantRStageTime w h m)).faceSucc (hatDartMap w h m d) =
      hatDartMap w h m ((kmswMap (hatCodes w h) m).faceSucc d) := by
  have lc := triangleDartCycle_isFace (hatCodes w h) m t ht
  have gc := triangleDartCycle_isFace w (quadrantRStageTime w h m)
    _ (hatAll_triSim w h m t ht)
  have hc := hatDartMap_triangleDartCycle w h m t ht
  dsimp only at hc
  rw [← hc] at gc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · rw [lc.1]
    exact gc.1
  · rw [lc.2.1]
    exact gc.2.1
  · rw [lc.2.2.1]
    exact gc.2.2.1

/-- Ordered edge-and-side boundary words agree at aligned finite stages -/
theorem hatAll_triangleOrientedDarts (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage (hatCodes w h) m).triangles) :
    (triangleOrientedDarts (hatCodes w h) t).map
      (fun d => (hatAllEdgeMap w h m d.1, d.2)) =
      triangleOrientedDarts w (hatAllEdgeMap w h m t.1,
        hatAllEdgeMap w h m t.2.1, hatAllEdgeMap w h m t.2.2) := by
  have hb := triBound_stage (hatCodes w h) m t ht
  have he := hat_east_eq_iff w h m t.1 t.2.1 hb.1 hb.2.1
  unfold triangleOrientedDarts
  by_cases hl : edgeEast (hatCodes w h) t.1 = edgeEast (hatCodes w h) t.2.1
  · rw [ite_eq_left hl, ite_eq_left (he.mpr hl)]
    rfl
  · rw [ite_eq_right hl, ite_eq_right (fun hh => hl (he.mp hh))]
    rfl

/-- The source face equivalence preserves the oriented face boundary word,
using the very same limit edge map as the graph equivalence -/
theorem hatSourceFaceEquiv_orientedDarts (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    (triangleOrientedDarts (hatCodes w h) t.val).map
      (fun d => (hatLimitEdgeMap w h d.1, d.2)) =
      triangleOrientedDarts w (hatSourceFaceEquiv w h t).val := by
  obtain ⟨m, ht⟩ := t.property
  have hb := triBound_stage (hatCodes w h) m t.val ht
  have hface := hatSourceFaceEquiv_compatible w h t
  simp only [hatExplicitEdgeEquiv_apply] at hface
  rw [hface, hatLimitEdgeMap_eq_stage w h m _ hb.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.2]
  rw [← hatAll_triangleOrientedDarts w h m t.val ht]
  unfold triangleOrientedDarts
  split <;> simp only [List.map_cons, List.map_nil]
  all_goals rw [hatLimitEdgeMap_eq_stage w h m _ hb.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.2]

private theorem record_oriented_mem (w : ℕ → Fin 3) (j : TriangleCreationTime w)
    (p : ℕ × Bool) :
    p ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      p ∈ stageTriangleDartList w j := by
  unfold triangleOrientedDarts
  rcases j.property with h0 | h1
  · rw [ite_eq_left ((record_east_eq_iff w j).mpr h0)]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
        h0, hp, or_comm, or_left_comm, or_assoc]
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right (fun he => h0 ((record_east_eq_iff w j).mp he))]
    simp only [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
      h0, ↓reduceIte]

/-- Every inner dart, as characterized by the proved finite face partition,
commutes with face successor under the hatted embedding (`lem-quad-kmsw`, -/
theorem hatDartMap_faceSucc_of_not_outer (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : d ∉ stageOuterWord (hatCodes w h) m) :
    (kmswMap w (quadrantRStageTime w h m)).faceSucc (hatDartMap w h m d) =
      hatDartMap w h m ((kmswMap (hatCodes w h) m).faceSucc d) := by
  obtain ho | ⟨j, ⟨hj, hdj⟩, _⟩ := stage_dart_partition (hatCodes w h) m d
  · exact (hd ho).elim
  have ht : stageTriangleRecord (hatCodes w h) j ∈
      (kmswStage (hatCodes w h) m).triangles := by
    rw [← stageTriangleTimes_records]
    exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes _ m j).mpr hj, rfl⟩
  apply hatDartMap_faceSucc w h m _ ht d
  have hv := (record_oriented_mem (hatCodes w h) j (d.1.val, d.2)).mpr hdj
  rw [← triangleDartCycle_values (hatCodes w h) m _ ht] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hv ⊢
  rcases hv with h1 | h2 | h3
  · exact Or.inl (Prod.ext (Fin.ext h1.1) h1.2)
  · exact Or.inr (Or.inl (Prod.ext (Fin.ext h2.1) h2.2))
  · exact Or.inr (Or.inr (Prod.ext (Fin.ext h3.1) h3.2))

/-- Active west darts correspond at every aligned stage. This is exploration
root data, rather than an outer-face identification (`lem-quad-kmsw`, -/
theorem hatDartMap_active (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    hatDartMap w h m
      (⟨(kmswStage (hatCodes w h) m).active,
        (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).1⟩, false) =
      (⟨(kmswStage w (quadrantRStageTime w h m)).active,
        (kmswStage_boundary_ids_lt_nextEdge w (quadrantRStageTime w h m)).1⟩,
        false) := by
  apply Prod.ext
  · exact Fin.ext (hatAll_sim w h m).incidenceSim.active
  · rfl

/-- The vertex root and the original edge `lambda_0` are fixed by the coherent
maps, including at the limit (`lem-quad-kmsw`, -/
theorem hat_root_correspondence (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (∀ m, hatAllVertexMap w h m 0 = 0) ∧
      (∀ m, hatAllEdgeMap w h m 0 = 0) ∧
      hatLimitVertexMap w h 0 = 0 ∧ hatLimitEdgeMap w h 0 = 0 := by
  have hb : 0 < (kmswStage (hatCodes w h) 0).nextEdge := by change 0 < 1; decide
  have hv : 0 < (kmswStage (hatCodes w h) 0).nextVertex := by change 0 < 2; decide
  have he : ∀ m, hatAllEdgeMap w h m 0 = 0 := by
    intro m
    exact hatAllEdgeMap_eq_of_le w h 0 m 0 (Nat.zero_le m) hb
  refine ⟨hatAllVertexMap_root w h, he, ?_, ?_⟩
  · rw [hatLimitVertexMap_eq_stage w h 0 0 hv]
    rfl
  · rw [hatLimitEdgeMap_eq_stage w h 0 0 hb]
    rfl

/-- A short-word boundary obstruction: after a fresh-left excursion and a
pendant down step, the original edge's west dart lies on an excluded triangle.
The local down stage sees it on the outer face. Thus side-preserving incidence
embeddings cannot in general preserve the ambient outer-face successor
inner-dart statement is `hatDartMap_faceSucc_of_not_outer`. -/
theorem outer_faceSucc_counterexample :
    let u : ℕ → Fin 3 := fun n => if n = 0 then 0 else 2
    let a : StageDart (kmswStage (fun _ => 2) 1).nextEdge := (⟨0, by decide⟩, false)
    let b : StageDart (kmswStage u 2).nextEdge := (⟨0, by decide⟩, false)
    a ∈ stageOuterWord (fun _ => 2) 1 ∧ b ∉ stageOuterWord u 2 ∧
      ((kmswMap (fun _ => 2) 1).faceSucc a).2 = false ∧
      ((kmswMap u 2).faceSucc b).2 = true := by
  decide

end DirectedDistances.KMSW
