module

public import DirectedDistances.KMSW.StageTrianglePersistence
public import DirectedDistances.KMSW.FaceCountEuler
public import DirectedDistances.KMSW.StageEdgesConnected
public import DirectedDistances.KMSW.StageOuterWordSucc
public import DirectedDistances.PlanarMap.CombinatorialMap

/-! # Planarity of the finite KMSW maps

into planarity in the sense of `defn:planar-map-with-missing-edges`,
The outer-word face cycle property enters as the hypothesis `hcycle`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The typed dart triple of the triangle created at time `j`, at a stage `n` -/
@[expose] def stageTriangleTriple (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) :
    StageDart (kmswStage w n).nextEdge × StageDart (kmswStage w n).nextEdge ×
      StageDart (kmswStage w n).nextEdge :=
  (stageTriangleDart₁ w n j hj, stageTriangleDart₂ w n j hj, stageTriangleDart₃ w n j hj)

/-- The typed triple of the `i`-th recorded triangle, indexed through the -/
@[expose] def stageTriangleTyped (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (kmswStage w n).triangles.length) :
    StageDart (kmswStage w n).nextEdge × StageDart (kmswStage w n).nextEdge ×
      StageDart (kmswStage w n).nextEdge :=
  stageTriangleTriple w n ((stageTriangleTimes w n)[i.val]'
      (by rw [stageTriangleTimes_length]; exact i.2))
    ((mem_stageTriangleTimes w n _).mp (List.getElem_mem _))

private theorem mem_stageTriangleTriple (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ [(stageTriangleTriple w n j hj).1, (stageTriangleTriple w n j hj).2.1,
        (stageTriangleTriple w n j hj).2.2] ↔
      (d.1.val, d.2) ∈ stageTriangleDartList w j := by
  rcases d with ⟨⟨e, he⟩, b⟩
  simp [stageTriangleTriple, stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
    stageTriangleDartAt, stageTriangleDartList, Prod.ext_iff]

private theorem mem_faceWords_some (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (List.ofFn (stageTriangleTyped w n)).length)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ faceWords (stageOuterWord w n) (List.ofFn (stageTriangleTyped w n)) (some i) ↔
      ∃ hi : i.val < (stageTriangleTimes w n).length,
        (d.1.val, d.2) ∈ stageTriangleDartList w ((stageTriangleTimes w n)[i.val]'hi) := by
  have hi' : i.val < (kmswStage w n).triangles.length := by simpa using i.2
  have hi'' : i.val < (stageTriangleTimes w n).length := by
    rw [stageTriangleTimes_length]; exact hi'
  have e : (List.ofFn (stageTriangleTyped w n))[i.val] =
      stageTriangleTyped w n ⟨i.val, hi'⟩ := by simp
  simp only [faceWords, Fin.getElem_fin, e]
  exact (mem_stageTriangleTriple w n _ _ d).trans ⟨fun h => ⟨hi'', h⟩, fun ⟨_, h⟩ => h⟩

private theorem isPlanar_of_triangle_cycles (w : ℕ → Fin 3) (n : ℕ)
    (hB : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (hT : ∀ i, FaceSucc3Cycle (kmswMap w n).faceSucc
      (stageTriangleTyped w n i).1 (stageTriangleTyped w n i).2.1
      (stageTriangleTyped w n i).2.2) :
    (kmswMap w n).IsPlanar := by
  refine ⟨kmswMap_isConnected w n, ?_⟩
  refine kmswMap_eulerChar_of_face_partition w n (stageTriangleTyped w n) hB hT ?_ ?_
  · intro i j hij
    rw [List.disjoint_left]
    intro d hdi hdj
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        obtain ⟨hj, hdj'⟩ := (mem_faceWords_some w n j d).mp hdj
        exact stageTriangleDart_not_outer w n _
          ((mem_stageTriangleTimes w n _).mp (List.getElem_mem hj)) d hdj' hdi
    | some i =>
      cases j with
      | none =>
        obtain ⟨hi, hdi'⟩ := (mem_faceWords_some w n i d).mp hdi
        exact stageTriangleDart_not_outer w n _
          ((mem_stageTriangleTimes w n _).mp (List.getElem_mem hi)) d hdi' hdj
      | some j =>
        obtain ⟨hi, hdi'⟩ := (mem_faceWords_some w n i d).mp hdi
        obtain ⟨hj, hdj'⟩ := (mem_faceWords_some w n j d).mp hdj
        have hne : (stageTriangleTimes w n)[i.val] ≠ (stageTriangleTimes w n)[j.val] := by
          intro h
          apply hij
          have := (List.Nodup.getElem_inj_iff (stageTriangleTimes_nodup w n)).mp h
          exact congrArg some (Fin.ext this)
        exact List.disjoint_left.mp (stageTriangleDartLists_disjoint w n _ _
          ((mem_stageTriangleTimes w n _).mp (List.getElem_mem hi))
          ((mem_stageTriangleTimes w n _).mp (List.getElem_mem hj)) hne) hdi' hdj'
  · intro d
    rcases stage_dart_partition w n d with ho | ⟨j, ⟨hjn, hdj⟩, _⟩
    · exact ⟨none, ho⟩
    · obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.mp
        ((mem_stageTriangleTimes w n j).mpr hjn)
      have hk' : k < (List.ofFn (stageTriangleTyped w n)).length := by
        simpa [← stageTriangleTimes_length] using hk
      refine ⟨some ⟨k, hk'⟩, (mem_faceWords_some w n ⟨k, hk'⟩ d).mpr ⟨hk, ?_⟩⟩
      simpa [hkj] using hdj

/-- Planarity of the stage-`n` KMSW map (`def-kmsw`,
is a face cycle. -/
theorem kmswMap_isPlanar_of_cycle (w : ℕ → Fin 3)
    (hcycle : ∀ n, ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) (n : ℕ) :
    (kmswMap w n).IsPlanar :=
  isPlanar_of_triangle_cycles w n (hcycle n)
    (fun i => stageTriangle_faceSucc3Cycle w hcycle
      ((stageTriangleTimes w n)[i.val]'(by rw [stageTriangleTimes_length]; exact i.2)) n
      ((mem_stageTriangleTimes w n _).mp (List.getElem_mem _)))

/-- Planarity of the stage-`0` KMSW map, unconditionally (`def-kmsw`, -/
theorem kmswMap_isPlanar_zero (w : ℕ → Fin 3) : (kmswMap w 0).IsPlanar :=
  isPlanar_of_triangle_cycles w 0 (stageOuterWord_faceSucc_zero w)
    (fun i => absurd i.2 (Nat.not_lt_zero _))

end DirectedDistances.KMSW
