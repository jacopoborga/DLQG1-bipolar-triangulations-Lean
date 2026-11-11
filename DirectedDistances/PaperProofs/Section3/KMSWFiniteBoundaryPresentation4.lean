/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation3
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation4






public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite four-run presentation has the
same ordered dart word as the stage exterior face. -/
private theorem kmswStageFiniteBoundaryPresentation4_runSplit
    (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n =
      kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
  simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
    kmswStageLRDartRun, kmswStageLLDartRun]

/-- Helper toward Definition 3.2: the stage face successor sends each
nonterminal upper-left run dart to the next dart in that run. -/
theorem kmswStageFiniteBoundaryPresentation4_upperLeft_faceSucc
    (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (kmswStageULDartRun w n).length)
    (hi : i.val + 1 < (kmswStageULDartRun w n).length) :
    (kmswMap w n).faceSucc
        ((kmswStageULDartRun w n)[i.val]'i.isLt) =
      (kmswStageULDartRun w n)[i.val + 1]'hi := by
  let W := stageOuterWord w n
  let R := kmswStageULDartRun w n
  have hsplit := kmswStageFiniteBoundaryPresentation4_runSplit w n
  change W = R ++ kmswStageURDartRun w n ++
    kmswStageLRDartRun w n ++ kmswStageLLDartRun w n at hsplit
  have hlen := congrArg List.length hsplit
  have hiW : i.val < W.length := by
    rw [hlen]
    calc
      i.val < R.length := i.isLt
      _ ≤ (R ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n).length := by simp
  have hiW' : i.val + 1 < W.length := by
    rw [hlen]
    calc
      i.val + 1 < R.length := hi
      _ ≤ (R ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n).length := by simp
  have hget : W[i.val]'hiW = R[i.val]'i.isLt := by
    simp [W, R, hsplit]
  have hget' : W[i.val + 1]'hiW' = R[i.val + 1]'hi := by
    simp [W, R, hsplit, hi]
  have hface := stageOuterWord_faceSucc w n (W[i.val]'hiW)
    (List.getElem_mem hiW)
  have hform := List.formPerm_apply_getElem W (stageOuterWord_nodup w n)
    i.val hiW
  rw [hget] at hface
  calc
    (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
        W.formPerm (W[i.val]'hiW) := by
      calc
        (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
            (stageOuterWord w n).formPerm (R[i.val]'i.isLt) := hface
        _ = W.formPerm (W[i.val]'hiW) := by
          simpa [W] using congrArg (fun d =>
            (stageOuterWord w n).formPerm d) hget.symm
    _ = W[((i.val + 1) % W.length)]'(Nat.mod_lt _ (by omega)) := by
      exact hform
    _ = R[i.val + 1]'hi := by
      simpa only [Nat.mod_eq_of_lt hiW'] using hget'

/-- Helper toward Definition 3.2: the stage face successor sends each
nonterminal upper-right run dart to the next dart in that run. -/
theorem kmswStageFiniteBoundaryPresentation4_upperRight_faceSucc
    (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (kmswStageURDartRun w n).length)
    (hi : i.val + 1 < (kmswStageURDartRun w n).length) :
    (kmswMap w n).faceSucc
        ((kmswStageURDartRun w n)[i.val]'i.isLt) =
      (kmswStageURDartRun w n)[i.val + 1]'hi := by
  let W := stageOuterWord w n
  let R := kmswStageURDartRun w n
  let offset := (kmswStageULDartRun w n).length
  let k := offset + i.val
  have hsplit := kmswStageFiniteBoundaryPresentation4_runSplit w n
  change W = kmswStageULDartRun w n ++ R ++
    kmswStageLRDartRun w n ++ kmswStageLLDartRun w n at hsplit
  have hlen := congrArg List.length hsplit
  have hiW : k < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length + i.val <
          (kmswStageULDartRun w n).length + R.length :=
        Nat.add_lt_add_left i.isLt _
      _ ≤ (kmswStageULDartRun w n ++ R ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n).length := by simp
  have hiW' : k + 1 < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length + (i.val + 1) <
          (kmswStageULDartRun w n).length + R.length :=
        Nat.add_lt_add_left hi _
      _ ≤ (kmswStageULDartRun w n ++ R ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n).length := by simp
  have hget : W[k]'hiW = R[i.val]'i.isLt := by
    simp [W, R, k, offset, hsplit]
  have hget' : W[k + 1]'hiW' = R[i.val + 1]'hi := by
    simp [W, R, k, offset, hsplit, Nat.add_assoc, hi]
  have hface := stageOuterWord_faceSucc w n (W[k]'hiW)
    (List.getElem_mem hiW)
  have hform := List.formPerm_apply_getElem W (stageOuterWord_nodup w n)
    k hiW
  rw [hget] at hface
  calc
    (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
        W.formPerm (W[k]'hiW) := by
      calc
        (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
            (stageOuterWord w n).formPerm (R[i.val]'i.isLt) := hface
        _ = W.formPerm (W[k]'hiW) := by
          simpa [W] using congrArg (fun d =>
            (stageOuterWord w n).formPerm d) hget.symm
    _ = W[(k + 1) % W.length]'(Nat.mod_lt _ (by omega)) := hform
    _ = R[i.val + 1]'hi := by
      simpa only [Nat.mod_eq_of_lt hiW'] using hget'

/-- Helper toward Definition 3.2: the stage face successor sends each
nonterminal lower-right run dart to the next dart in its reversed run. -/
theorem kmswStageFiniteBoundaryPresentation4_lowerRight_faceSucc
    (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (kmswStageLRDartRun w n).length)
    (hi : i.val + 1 < (kmswStageLRDartRun w n).length) :
    (kmswMap w n).faceSucc
        ((kmswStageLRDartRun w n)[i.val]'i.isLt) =
      (kmswStageLRDartRun w n)[i.val + 1]'hi := by
  let W := stageOuterWord w n
  let R := kmswStageLRDartRun w n
  let offset := (kmswStageULDartRun w n).length +
    (kmswStageURDartRun w n).length
  let k := offset + i.val
  have hsplit := kmswStageFiniteBoundaryPresentation4_runSplit w n
  change W = kmswStageULDartRun w n ++ kmswStageURDartRun w n ++ R ++
    kmswStageLLDartRun w n at hsplit
  have hlen := congrArg List.length hsplit
  have hiW : k < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length + i.val <
        (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length + R.length := by
            exact Nat.add_lt_add_left i.isLt _
      _ ≤ (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++ R ++
        kmswStageLLDartRun w n).length := by
          simp only [List.length_append]
          omega
  have hiW' : k + 1 < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length + (i.val + 1) <
        (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length + R.length := by
            exact Nat.add_lt_add_left hi _
      _ ≤ (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++ R ++
        kmswStageLLDartRun w n).length := by
          simp only [List.length_append]
          omega
  have hget : W[k]'hiW = R[i.val]'i.isLt := by
    simp [W, R, k, offset, hsplit, Nat.add_assoc]
  have hget' : W[k + 1]'hiW' = R[i.val + 1]'hi := by
    simp [W, R, k, offset, hsplit, Nat.add_assoc, hi]
  have hface := stageOuterWord_faceSucc w n (W[k]'hiW)
    (List.getElem_mem hiW)
  have hform := List.formPerm_apply_getElem W (stageOuterWord_nodup w n)
    k hiW
  rw [hget] at hface
  calc
    (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
        W.formPerm (W[k]'hiW) := by
      calc
        (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
            (stageOuterWord w n).formPerm (R[i.val]'i.isLt) := hface
        _ = W.formPerm (W[k]'hiW) := by
          simpa [W] using congrArg (fun d =>
            (stageOuterWord w n).formPerm d) hget.symm
    _ = W[(k + 1) % W.length]'(Nat.mod_lt _ (by omega)) := hform
    _ = R[i.val + 1]'hi := by
      simpa only [Nat.mod_eq_of_lt hiW'] using hget'

/-- Helper toward Definition 3.2: the stage face successor sends each
nonterminal lower-left run dart to the next dart in its reversed run. -/
theorem kmswStageFiniteBoundaryPresentation4_lowerLeft_faceSucc
    (w : ℕ → Fin 3) (n : ℕ)
    (i : Fin (kmswStageLLDartRun w n).length)
    (hi : i.val + 1 < (kmswStageLLDartRun w n).length) :
    (kmswMap w n).faceSucc
        ((kmswStageLLDartRun w n)[i.val]'i.isLt) =
      (kmswStageLLDartRun w n)[i.val + 1]'hi := by
  let W := stageOuterWord w n
  let R := kmswStageLLDartRun w n
  let offset := (kmswStageULDartRun w n).length +
    (kmswStageURDartRun w n).length +
    (kmswStageLRDartRun w n).length
  let k := offset + i.val
  have hsplit := kmswStageFiniteBoundaryPresentation4_runSplit w n
  change W = kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
    kmswStageLRDartRun w n ++ R at hsplit
  have hlen := congrArg List.length hsplit
  have hiW : k < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length +
          (kmswStageLRDartRun w n).length + i.val <
        (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length +
          (kmswStageLRDartRun w n).length + R.length := by
            exact Nat.add_lt_add_left i.isLt _
      _ ≤ (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ R).length := by
          simp only [List.length_append]
          omega
  have hiW' : k + 1 < W.length := by
    rw [hlen]
    dsimp [k, offset]
    calc
      (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length +
          (kmswStageLRDartRun w n).length + (i.val + 1) <
        (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length +
          (kmswStageLRDartRun w n).length + R.length := by
            exact Nat.add_lt_add_left hi _
      _ ≤ (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ R).length := by
          simp only [List.length_append]
          omega
  have hget : W[k]'hiW = R[i.val]'i.isLt := by
    simp [W, R, k, offset, hsplit, Nat.add_assoc]
  have hget' : W[k + 1]'hiW' = R[i.val + 1]'hi := by
    simp [W, R, k, offset, hsplit, Nat.add_assoc]
  have hface := stageOuterWord_faceSucc w n (W[k]'hiW)
    (List.getElem_mem hiW)
  have hform := List.formPerm_apply_getElem W (stageOuterWord_nodup w n)
    k hiW
  rw [hget] at hface
  calc
    (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
        W.formPerm (W[k]'hiW) := by
      calc
        (kmswMap w n).faceSucc (R[i.val]'i.isLt) =
            (stageOuterWord w n).formPerm (R[i.val]'i.isLt) := hface
        _ = W.formPerm (W[k]'hiW) := by
          simpa [W] using congrArg (fun d =>
            (stageOuterWord w n).formPerm d) hget.symm
    _ = W[(k + 1) % W.length]'(Nat.mod_lt _ (by omega)) := hform
    _ = R[i.val + 1]'hi := by
      simpa only [Nat.mod_eq_of_lt hiW'] using hget'

/-- Helper toward Definition 3.2: the drawing and unique unbounded face from
the stage geometry representation have the prescribed geometric successor
on every nonterminal dart of all four runs. -/
theorem kmswStageFiniteBoundaryPresentation4_geometric_run_successors
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (G : StageDrawing w n) (U : G.Face),
      G.IsUnbounded U ∧
      (∀ F : G.Face, G.IsUnbounded F → F = U) ∧
      (∀ d, G.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d) ∧
      (∀ (i : Fin (kmswStageULDartRun w n).length)
        (hi : i.val + 1 < (kmswStageULDartRun w n).length),
        G.dartBorders ((kmswStageULDartRun w n)[i.val]'i.isLt) U ∧
        (stageRot w n).symm ((edgeFlip (kmswStage w n).nextEdge)
          ((kmswStageULDartRun w n)[i.val]'i.isLt)) =
          (kmswStageULDartRun w n)[i.val + 1]'hi ∧
        G.dartBorders ((kmswStageULDartRun w n)[i.val + 1]'hi) U) ∧
      (∀ (i : Fin (kmswStageURDartRun w n).length)
        (hi : i.val + 1 < (kmswStageURDartRun w n).length),
        G.dartBorders ((kmswStageURDartRun w n)[i.val]'i.isLt) U ∧
        (stageRot w n).symm ((edgeFlip (kmswStage w n).nextEdge)
          ((kmswStageURDartRun w n)[i.val]'i.isLt)) =
          (kmswStageURDartRun w n)[i.val + 1]'hi ∧
        G.dartBorders ((kmswStageURDartRun w n)[i.val + 1]'hi) U) ∧
      (∀ (i : Fin (kmswStageLRDartRun w n).length)
        (hi : i.val + 1 < (kmswStageLRDartRun w n).length),
        G.dartBorders ((kmswStageLRDartRun w n)[i.val]'i.isLt) U ∧
        (stageRot w n).symm ((edgeFlip (kmswStage w n).nextEdge)
          ((kmswStageLRDartRun w n)[i.val]'i.isLt)) =
          (kmswStageLRDartRun w n)[i.val + 1]'hi ∧
        G.dartBorders ((kmswStageLRDartRun w n)[i.val + 1]'hi) U) ∧
      (∀ (i : Fin (kmswStageLLDartRun w n).length)
        (hi : i.val + 1 < (kmswStageLLDartRun w n).length),
        G.dartBorders ((kmswStageLLDartRun w n)[i.val]'i.isLt) U ∧
        (stageRot w n).symm ((edgeFlip (kmswStage w n).nextEdge)
          ((kmswStageLLDartRun w n)[i.val]'i.isLt)) =
          (kmswStageLLDartRun w n)[i.val + 1]'hi ∧
        G.dartBorders ((kmswStageLLDartRun w n)[i.val + 1]'hi) U) := by
  obtain ⟨G, U, hU, hunique, hborder⟩ :=
    DirectedDistances.PaperProofs.Section5.kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
      w n
  have hsplit := kmswStageFiniteBoundaryPresentation4_runSplit w n
  have hmemUL : ∀ i : Fin (kmswStageULDartRun w n).length,
      (kmswStageULDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    rw [hsplit]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (List.getElem_mem i.isLt)))
  have hmemUR : ∀ i : Fin (kmswStageURDartRun w n).length,
      (kmswStageURDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    rw [hsplit]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.getElem_mem i.isLt)))
  have hmemLR : ∀ i : Fin (kmswStageLRDartRun w n).length,
      (kmswStageLRDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    rw [hsplit]
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.getElem_mem i.isLt))
  have hmemLL : ∀ i : Fin (kmswStageLLDartRun w n).length,
      (kmswStageLLDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    rw [hsplit]
    simp only [List.mem_append]
    exact Or.inr (List.getElem_mem i.isLt)
  refine ⟨G, U, hU, hunique, hborder, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hbefore := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2 (hmemUL i))
    have hnext := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2
      (hmemUL ⟨i.val + 1, hi⟩))
    refine ⟨hbefore, ?_, hnext⟩
    change (kmswMap w n).faceSucc _ = _
    exact kmswStageFiniteBoundaryPresentation4_upperLeft_faceSucc w n i hi
  · intro i hi
    have hbefore := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2 (hmemUR i))
    have hnext := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2
      (hmemUR ⟨i.val + 1, hi⟩))
    refine ⟨hbefore, ?_, hnext⟩
    change (kmswMap w n).faceSucc _ = _
    exact kmswStageFiniteBoundaryPresentation4_upperRight_faceSucc w n i hi
  · intro i hi
    have hbefore := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2 (hmemLR i))
    have hnext := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2
      (hmemLR ⟨i.val + 1, hi⟩))
    refine ⟨hbefore, ?_, hnext⟩
    change (kmswMap w n).faceSucc _ = _
    exact kmswStageFiniteBoundaryPresentation4_lowerRight_faceSucc w n i hi
  · intro i hi
    have hbefore := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2 (hmemLL i))
    have hnext := (hborder _).2 ((kmsw_stage_outer_face_exact w n _).2
      (hmemLL ⟨i.val + 1, hi⟩))
    refine ⟨hbefore, ?_, hnext⟩
    change (kmswMap w n).faceSucc _ = _
    exact kmswStageFiniteBoundaryPresentation4_lowerLeft_faceSucc w n i hi

/-! Open endpoint-label statements, with full binders. For
`(w : ℕ → Fin 3) (n : ℕ)`,
`(M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
  (Fin (kmswStage w n).nextEdge))`,
`(J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))`, and
`P := kmswStageFiniteBoundaryPresentation w n M J`, the open conclusions are
`BoundarySideEndpointLabels M P.upperLeft`,
`BoundarySideEndpointLabels M P.upperRight`,
`BoundarySideEndpointLabels M P.lowerRight`, and
`BoundarySideEndpointLabels M P.lowerLeft`.

Three routes were checked: projecting the retained junction-label theorem
only identifies the optional labels with `J`; translating the four stage
endpoint-incidence chains requires `M`'s source and target maps to be the
stage endpoints; and the empty-side endpoint helper requires the side's two
labels to denote the same actual vertex. The first route lacks endpoint
incidence, and the latter two lack a hypothesis-free map identification.
Such an identification cannot be added to these binders: `M` and `J` are
arbitrary in the exact target.

The open finite-join statement, with full binders, is: for the same `w`, `n`,
`M`, and `J`, and
`(S : StageDart (kmswStage w n).nextEdge →
  StageDart (kmswStage w n).nextEdge)`, prove
`RequiredFiniteBoundaryJoinEndpointLabels7 P S`.
Three routes were checked: close each run in the cyclic outer word and use
the source endpoint chains; reduce to the v4 closing-junction predicate;
or split into the two-present-path and missing-present-path branches of v7.
All require actual endpoint equalities in `M` and a successor map whose
geometric action is identified with the stage word; those data are not in
these binders. No label equation, interval order, position order, or
geometric-correspondence premise is supplied. -/

end DirectedDistances.PaperProofs.Section3
