/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: index the two nonempty boundary paths in
their outer-face traversal order, with UL before LR. -/
@[expose] def boundaryChanneledPresentation_position {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation → ℤ := by
  intro i
  cases i with
  | upperLeft i => exact (i.val : ℤ)
  | upperRight i => exact Empty.elim i
  | lowerRight i => exact (ℓ + i.val : ℤ)
  | lowerLeft i => exact Empty.elim i

/-- Helper toward Definition 3.2: the finite path positions are injective. -/
theorem boundaryChanneledPresentation_position_injective {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    Function.Injective (boundaryChanneledPresentation_position R G) := by
  intro i j h
  cases i <;> cases j <;> rename_i a b
  all_goals try { first
    | (change Empty at a; cases a)
    | (change Empty at b; cases b) }
  case upperLeft.upperLeft =>
    dsimp [boundaryChanneledPresentation_position] at h
    have hv : a.val = b.val := by exact_mod_cast h
    exact congrArg InfiniteBoundaryDartIndex.upperLeft (Fin.ext hv)
  case upperLeft.lowerRight =>
    dsimp [boundaryChanneledPresentation_position] at h
    have hval : a.val = ℓ + b.val := by exact_mod_cast h
    omega
  case lowerRight.upperLeft =>
    dsimp [boundaryChanneledPresentation_position] at h
    have hval : ℓ + a.val = b.val := by exact_mod_cast h
    omega
  case lowerRight.lowerRight =>
    dsimp [boundaryChanneledPresentation_position] at h
    have hval : ℓ + a.val = ℓ + b.val := by exact_mod_cast h
    have hv : a.val = b.val := by omega
    exact congrArg InfiniteBoundaryDartIndex.lowerRight (Fin.ext hv)

/-- Helper toward Definition 3.2: each UL successor in the finite presentation
joins the corresponding directed path darts at their common vertex. -/
theorem boundaryChanneledPresentation_upperLeft_join {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (i j : Fin ℓ)
    (hnext : (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next i =
      some j) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        (boundaryChanneledLeftDart R G i) =
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
        (boundaryChanneledLeftDart R G j) := by
  have hnext' : (if h : i.val + 1 < ℓ then
      some (⟨i.val + 1, h⟩ : Fin ℓ) else none) = some j := by
    simpa [boundaryChanneledPresentationWithJunctions] using hnext
  by_cases hi : i.val + 1 < ℓ
  · rw [dif_pos hi] at hnext'
    have hij : (⟨i.val + 1, hi⟩ : Fin ℓ) = j := Option.some.inj hnext'
    have hval : i.val + 1 = j.val := congrArg Fin.val hij
    have hiStep := R.B.leftPath.edge_step
      ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩
    have hjStep := R.B.leftPath.edge_step
      ⟨j.val, by rw [R.B.leftPath.darts_length]; omega⟩
    calc
      boundaryDartTerminal (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G i) =
          dartHeadVertex R.B.map (boundaryPathDart R.B.leftPath i) :=
        boundaryChanneledLeftDart_terminal R G i
      _ = R.B.leftPath.vertices.get ⟨i.val + 1, by
            rw [R.B.leftPath.vertices_length]
            omega⟩ := hiStep.2.2.2.symm
      _ = R.B.leftPath.vertices.get ⟨j.val, by
            rw [R.B.leftPath.vertices_length]
            omega⟩ := by congr 1; apply Fin.ext; omega
      _ = dartTailVertex R.B.map (boundaryPathDart R.B.leftPath j) := hjStep.2.2.1
      _ = boundaryDartInitial (boundaryChanneledPlaneMap R G)
            (boundaryChanneledLeftDart R G j) :=
        (boundaryChanneledLeftDart_initial R G j).symm
  · rw [dif_neg hi] at hnext'
    cases hnext'



















































end DirectedDistances.PaperProofs.Section3

end
end
