/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation

/-! # UIQBOT infinite boundary presentation joins -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: consecutive UL and LR darts in the
constructed UIQBOT presentation join in traversal order -/
theorem uiqbotDefinition32Presentation_joins
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E)
    (hcompat : ∀ e, M.tail (iota e) = edgeWest w e ∧
      M.head (iota e) = edgeEast w e) :
    (∀ i : ℕ,
      boundaryDartTerminal (uiqbotMapWithNoMissing M)
          (iota (kmswLeftBoundaryEdge w i),
            (uiqbotMapWithNoMissing M).forward
              ⟨iota (kmswLeftBoundaryEdge w i), by
                simp [uiqbotMapWithNoMissing]⟩) =
        boundaryDartInitial (uiqbotMapWithNoMissing M)
          (iota (kmswLeftBoundaryEdge w (i + 1)),
            (uiqbotMapWithNoMissing M).forward
              ⟨iota (kmswLeftBoundaryEdge w (i + 1)), by
                simp [uiqbotMapWithNoMissing]⟩)) ∧
    (∀ i : ℕ,
      boundaryDartTerminal (uiqbotMapWithNoMissing M)
          (iota (kmswRightBoundaryEdge w (i + 1)),
            !(uiqbotMapWithNoMissing M).forward
              ⟨iota (kmswRightBoundaryEdge w (i + 1)), by
                simp [uiqbotMapWithNoMissing]⟩) =
        boundaryDartInitial (uiqbotMapWithNoMissing M)
          (iota (kmswRightBoundaryEdge w i),
            !(uiqbotMapWithNoMissing M).forward
              ⟨iota (kmswRightBoundaryEdge w i), by
                simp [uiqbotMapWithNoMissing]⟩)) := by
  have hmiss (e : ℕ) : ¬ (uiqbotMapWithNoMissing M).toPlaneMapWithMissing.missing (iota e) := by
    simp [uiqbotMapWithNoMissing]
  have hULterm (e : ℕ) :
      boundaryDartTerminal (uiqbotMapWithNoMissing M)
          (iota e, (uiqbotMapWithNoMissing M).forward ⟨iota e, hmiss e⟩) =
        edgeEast w e := by
    by_cases hf : M.forward (iota e)
    · simpa [boundaryDartTerminal_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
    · simpa [boundaryDartTerminal_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
  have hULinitial (e : ℕ) :
      boundaryDartInitial (uiqbotMapWithNoMissing M)
          (iota e, (uiqbotMapWithNoMissing M).forward ⟨iota e, hmiss e⟩) =
        edgeWest w e := by
    by_cases hf : M.forward (iota e)
    · simpa [boundaryDartInitial_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
    · simpa [boundaryDartInitial_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
  have hLRterm (e : ℕ) :
      boundaryDartTerminal (uiqbotMapWithNoMissing M)
          (iota e, !(uiqbotMapWithNoMissing M).forward ⟨iota e, hmiss e⟩) =
        edgeWest w e := by
    by_cases hf : M.forward (iota e)
    · simpa [boundaryDartTerminal_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
    · simpa [boundaryDartTerminal_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
  have hLRinitial (e : ℕ) :
      boundaryDartInitial (uiqbotMapWithNoMissing M)
          (iota e, !(uiqbotMapWithNoMissing M).forward ⟨iota e, hmiss e⟩) =
        edgeEast w e := by
    by_cases hf : M.forward (iota e)
    · simpa [boundaryDartInitial_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
    · simpa [boundaryDartInitial_eq, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
  constructor
  · intro i
    rw [hULterm, hULinitial]
    exact (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).2.1 i
  · intro i
    rw [hLRterm, hLRinitial]
    exact (kmswRightBoundary_infinite_present_path w hL0 hR).2.1 i |>.symm

/-- Helper toward Definition 3.2: the consecutive-dart join clauses of
`ULOkInf` and `LROkInf` hold for the constructed UIQBOT presentation. -/
theorem uiqbotDefinition32Presentation_joinClauses
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E)
    (hcompat : ∀ e, M.tail (iota e) = edgeWest w e ∧
      M.head (iota e) = edgeEast w e) :
    (∀ i j : ℕ,
      (uiqbotDefinition32Presentation w htrans hR hL0 M iota).upperLeft.next i = some j →
        boundaryDartTerminal (uiqbotMapWithNoMissing M)
            ((uiqbotDefinition32Presentation w htrans hR hL0 M iota).upperLeft.darts i) =
          boundaryDartInitial (uiqbotMapWithNoMissing M)
            ((uiqbotDefinition32Presentation w htrans hR hL0 M iota).upperLeft.darts j)) ∧
    (∀ i j : ℕ,
      (uiqbotDefinition32Presentation w htrans hR hL0 M iota).lowerRight.next i = some j →
        boundaryDartTerminal (uiqbotMapWithNoMissing M)
            ((uiqbotDefinition32Presentation w htrans hR hL0 M iota).lowerRight.darts i) =
          boundaryDartInitial (uiqbotMapWithNoMissing M)
            ((uiqbotDefinition32Presentation w htrans hR hL0 M iota).lowerRight.darts j)) := by
  let P := uiqbotDefinition32Presentation w htrans hR hL0 M iota
  have hnextUL (i : ℕ) : P.upperLeft.next i = some (i + 1) := by
    rfl
  have hnextLR (i : ℕ) :
      P.lowerRight.next i = if i = 0 then none else some (i - 1) := by
    rfl
  have hdataUL (i : ℕ) :
      P.upperLeft.darts i =
        (iota (kmswLeftBoundaryEdge w i),
          (uiqbotMapWithNoMissing M).forward
            ⟨iota (kmswLeftBoundaryEdge w i), by simp [uiqbotMapWithNoMissing]⟩) := by
    rfl
  have hdataLR (i : ℕ) :
      P.lowerRight.darts i =
        (iota (kmswRightBoundaryEdge w i),
          !(uiqbotMapWithNoMissing M).forward
            ⟨iota (kmswRightBoundaryEdge w i), by simp [uiqbotMapWithNoMissing]⟩) := by
    rfl
  have hjoins := uiqbotDefinition32Presentation_joins w htrans hR hL0 M iota hcompat
  constructor
  · intro i j hj
    have hij : i + 1 = j := Option.some.inj ((hnextUL i).symm.trans hj)
    subst j
    rw [hdataUL i, hdataUL (i + 1)]
    exact hjoins.1 i
  · intro i j hj
    change P.lowerRight.next i = some j at hj
    have hi : i ≠ 0 := by
      intro hi
      subst i
      simp [hnextLR] at hj
    have hij : i - 1 = j := by
      have hnext := hnextLR i
      rw [ite_eq_right hi] at hnext
      exact Option.some.inj (hnext.symm.trans hj)
    have hsucc : j + 1 = i := by omega
    subst i
    rw [hdataLR (j + 1), hdataLR j]
    exact hjoins.2 j































end DirectedDistances.PaperProofs.Section4

end
