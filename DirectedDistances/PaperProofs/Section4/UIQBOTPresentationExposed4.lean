/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed3

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

variable {V : Type*} {E : Type*} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: the generic presentation update which changes
only the two lower-left endpoint labels. -/
abbrev uiqbotEndpointUpdatePresentation
    (P : InfiniteBoundaryPresentation M) (a b : Option V) :
    InfiniteBoundaryPresentation M :=
  {P with lowerLeft := {P.lowerLeft with
    initialVertex? := a, terminalVertex? := b}}

/-- Helper toward Definition 3.2: changing only the endpoint labels of the
lower-left side induces the constructor-wise equivalence of dart indices. -/
@[expose] def uiqbotEndpointUpdateIndexEquiv (P : InfiniteBoundaryPresentation M)
    (a b : Option V) :
    let Q := uiqbotEndpointUpdatePresentation P a b
    InfiniteBoundaryDartIndex Q ≃ InfiniteBoundaryDartIndex P := by
  intro Q
  exact {
    toFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    invFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    left_inv := by intro i; cases i <;> rfl
    right_inv := by intro i; cases i <;> rfl }

/-- Helper toward Definition 3.2: the endpoint update preserves the within-side
successor after transporting its index. -/
theorem uiqbotEndpointUpdateIndexEquiv_sideNext
    (P : InfiniteBoundaryPresentation M) (a b : Option V) :
    let Q := uiqbotEndpointUpdatePresentation P a b
    ∀ i : InfiniteBoundaryDartIndex Q,
      Option.map (uiqbotEndpointUpdateIndexEquiv P a b) (sideNext Q i) =
        sideNext P (uiqbotEndpointUpdateIndexEquiv P a b i) := by
  dsimp only
  intro i
  cases i with
  | upperLeft i =>
      change Option.map (uiqbotEndpointUpdateIndexEquiv P a b)
          (Option.map InfiniteBoundaryDartIndex.upperLeft (P.upperLeft.next i)) = _
      rw [Option.map_map]
      congr 1
  | upperRight i =>
      change Option.map (uiqbotEndpointUpdateIndexEquiv P a b)
          (Option.map InfiniteBoundaryDartIndex.upperRight (P.upperRight.next i)) = _
      rw [Option.map_map]
      congr 1
  | lowerRight i =>
      change Option.map (uiqbotEndpointUpdateIndexEquiv P a b)
          (Option.map InfiniteBoundaryDartIndex.lowerRight (P.lowerRight.next i)) = _
      rw [Option.map_map]
      congr 1
  | lowerLeft i =>
      change Option.map (uiqbotEndpointUpdateIndexEquiv P a b)
          (Option.map InfiniteBoundaryDartIndex.lowerLeft (P.lowerLeft.next i)) = _
      rw [Option.map_map]
      congr 1

/-- Helper toward Definition 3.2: the endpoint update preserves side labels. -/
theorem uiqbotEndpointUpdateIndexEquiv_sideTag
    (P : InfiniteBoundaryPresentation M) (a b : Option V) :
    let Q := uiqbotEndpointUpdatePresentation P a b
    ∀ i : InfiniteBoundaryDartIndex Q,
      sideTag P (uiqbotEndpointUpdateIndexEquiv P a b i) = sideTag Q i := by
  dsimp only
  intro i
  cases i <;> simp [sideTag, uiqbotEndpointUpdateIndexEquiv]

/-- Helper toward Definition 3.2: the endpoint update preserves the oriented
dart selected by each transported index. -/
theorem uiqbotEndpointUpdateIndexEquiv_dart
    (P : InfiniteBoundaryPresentation M) (a b : Option V) :
    let Q := uiqbotEndpointUpdatePresentation P a b
    ∀ i : InfiniteBoundaryDartIndex Q,
      InfiniteBoundaryDartIndex.dart P
        (uiqbotEndpointUpdateIndexEquiv P a b i) =
          InfiniteBoundaryDartIndex.dart Q i := by
  dsimp only
  intro i
  cases i with
  | upperLeft i => rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]; rfl
  | upperRight i => rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]; rfl
  | lowerRight i => rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]; rfl
  | lowerLeft i => rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]; rfl

/-- Helper toward Definition 3.2: the endpoint update preserves the next
nonempty-side relation because it leaves all side index types unchanged. -/
theorem uiqbotEndpointUpdate_nextNonemptySide
    (P : InfiniteBoundaryPresentation M) (a b : Option V) (s t : Fin 4) :
    let Q := uiqbotEndpointUpdatePresentation P a b
    (nextNonemptySide Q s t ↔ nextNonemptySide P s t) := by
  rfl















































































end DirectedDistances.PaperProofs.Section4

end
