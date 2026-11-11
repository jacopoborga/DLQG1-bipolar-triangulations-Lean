/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry15
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry14

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the constructed presentation indexes
exactly its upper-left and lower-right dart families; its other two families
are empty. -/
theorem boundaryChanneledPresentation_indexRange_iff_leftRight16
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : G.GeometricEdge × Bool) :
    (∃ i : InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation,
      InfiniteBoundaryDartIndex.dart
        (boundaryChanneledPresentationWithJunctions R G).presentation i = d) ↔
    (∃ i : Fin ℓ, boundaryChanneledLeftDart R G i = d) ∨
      (∃ i : Fin r, boundaryChanneledRightDart R G i = d) := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hleft (i : Fin ℓ) : P.upperLeft.darts i = boundaryChanneledLeftDart R G i := by
    rfl
  have hright (i : Fin r) : P.lowerRight.darts i = boundaryChanneledRightDart R G i := by
    rfl
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | upperLeft i =>
        have hi' : P.upperLeft.darts i = d := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
        exact Or.inl ⟨i, (hleft i).symm.trans hi'⟩
    | upperRight i =>
        change Empty at i
        exact i.elim
    | lowerRight i =>
        have hi' : P.lowerRight.darts i = d := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
        exact Or.inr ⟨i, (hright i).symm.trans hi'⟩
    | lowerLeft i =>
        change Empty at i
        exact i.elim
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨InfiniteBoundaryDartIndex.upperLeft i, ?_⟩
      have hi' : P.upperLeft.darts i = d := (hleft i).trans hi
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi'
    · refine ⟨InfiniteBoundaryDartIndex.lowerRight i, ?_⟩
      have hi' : P.lowerRight.darts i = d := (hright i).trans hi
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi'






































end DirectedDistances.PaperProofs.Section3

end
