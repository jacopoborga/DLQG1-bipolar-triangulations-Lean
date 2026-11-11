module

public import DirectedDistances.KMSW.StageOuterWord

/-! # Dart-count bookkeeping for finite KMSW stages

The boundary and triangle counts in `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

/-- The outer-word length is the sum of the four boundary lengths -/
theorem stageOuterWord_length (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWord w n).length =
      (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        (kmswStage w n).LR.length + (kmswStage w n).LL.length := by
  simp [stageOuterWord, stageDarts, Nat.add_assoc]

private theorem stage_boundary_triangle_count (w : ℕ → Fin 3) (n : ℕ) :
    2 * (kmswStage w n).nextEdge =
      (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        (kmswStage w n).LR.length + (kmswStage w n).LL.length +
          3 * (kmswStage w n).triangles.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 0 < (kmswStage w n).UL.length := by
      obtain ⟨es, hes⟩ := kmswStage_UL_last w n
      rw [hes]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    change 2 * (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).nextEdge =
      (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).UL.length +
        (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).UR.length +
        (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.length +
        (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LL.length +
        3 * (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).triangles.length
    cases kmswCodeStep (w n) with
    | down =>
      cases hr : (kmswStage w n).UR with
      | nil =>
        simp only [kmswStepOfStep, hr, State.addEdge, List.length_append,
          List.length_cons, List.length_nil]
        simp only [hr, List.length_nil] at ih
        omega
      | cons e es =>
        simp only [kmswStepOfStep, hr, List.length_append,
          List.length_cons, List.length_nil]
        simp only [hr, List.length_cons] at ih
        omega
    | left =>
      cases hl : (kmswStage w n).UL.dropLast.reverse with
      | nil =>
        have hlen := congrArg List.length hl
        simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hlen
        simp only [kmswStepOfStep, hl, State.addEdge, List.length_append,
          List.length_cons, List.length_nil]
        omega
      | cons e es =>
        have hlen := congrArg List.length hl
        simp only [List.length_reverse, List.length_dropLast, List.length_cons] at hlen
        simp only [kmswStepOfStep, hl, State.addEdge, List.length_append,
          List.length_reverse, List.length_cons, List.length_nil]
        omega
    | up =>
      simp only [kmswStepOfStep, State.addEdge, List.length_append,
        List.length_dropLast, List.length_cons, List.length_nil]
      omega

/-- Every allocated edge contributes two darts, accounted for numerically
by the outer boundary and three darts per recorded triangle (`def-kmsw`,
disjoint face partition. -/
theorem kmswStage_dart_count (w : ℕ → Fin 3) (n : ℕ) :
    2 * (kmswStage w n).nextEdge =
      (stageOuterWord w n).length + 3 * (kmswStage w n).triangles.length := by
  rw [stageOuterWord_length]
  exact stage_boundary_triangle_count w n

/-- Edge-ID triangle records do not distinguish fresh-left and up creation:
both first steps record `(0, 1, 2)` (`def-kmsw`,
are therefore not recoverable from the recorded three IDs alone. -/
theorem first_left_up_triangle_records :
    (kmswStage (fun _ => 0) 1).triangles = [(0, 1, 2)] ∧
      (kmswStage (fun _ => 1) 1).triangles = [(0, 1, 2)] := by
  constructor <;> rfl

/-- No function of a triangle's three edge IDs alone can give both required
creation triples. The fresh-left and up formulas in `def-kmsw` -/
theorem no_id_only_triangle_darts :
    ¬ ∃ T : (ℕ × ℕ × ℕ) → (ℕ × Bool) × (ℕ × Bool) × (ℕ × Bool),
      T (0, 1, 2) = ((0, false), (1, true), (2, false)) ∧
      T (0, 1, 2) = ((0, false), (2, true), (1, true)) := by
  rintro ⟨T, hl, hu⟩
  have he : (1 : ℕ) = 2 := congrArg (fun t => t.2.1.1) (hl.symm.trans hu)
  omega

end DirectedDistances.KMSW
