/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: transport boundary dart indices from the
labeled exposed presentation to the presentation before its endpoint update. -/
def uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    InfiniteBoundaryDartIndex Q ≃ InfiniteBoundaryDartIndex P := by
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
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

/-- Helper toward Definition 3.2: transported boundary indices preserve the
within-side successor, with `Option.map` handling the endpoint. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideNext
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q,
      Option.map (uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
        w hfin htrans hR hL0) (sideNext Q i) =
        sideNext P ((uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
          w hfin htrans hR hL0) i) := by
  dsimp only
  intro i
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  cases i with
  | upperLeft i =>
      change ℕ at i
      change Option.map (uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
        w hfin htrans hR hL0)
        (Option.map InfiniteBoundaryDartIndex.upperLeft (Q.upperLeft.next i)) =
        Option.map InfiniteBoundaryDartIndex.upperLeft (P.upperLeft.next i)
      have hn : Q.upperLeft.next i = P.upperLeft.next i := rfl
      rw [hn]
      cases h : P.upperLeft.next i with
      | none => rfl
      | some j =>
          change ℕ at j
          simp only [Option.map]
          congr 1
  | upperRight i => cases i
  | lowerRight i =>
      change ℕ at i
      change Option.map (uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
        w hfin htrans hR hL0)
        (Option.map InfiniteBoundaryDartIndex.lowerRight (Q.lowerRight.next i)) =
        Option.map InfiniteBoundaryDartIndex.lowerRight (P.lowerRight.next i)
      have hn : Q.lowerRight.next i = P.lowerRight.next i := rfl
      rw [hn]
      cases h : P.lowerRight.next i with
      | none => rfl
      | some j =>
          change ℕ at j
          simp only [Option.map]
          congr 1
  | lowerLeft i => cases i

/-- Helper toward Definition 3.2: transported boundary indices preserve side
labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideTag
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q,
      sideTag P ((uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
        w hfin htrans hR hL0) i) = sideTag Q i := by
  dsimp only
  intro i
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  cases i with
  | upperLeft i => change ℕ at i; simp [sideTag, uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv]
  | upperRight i => cases i
  | lowerRight i => change ℕ at i; simp [sideTag, uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv]
  | lowerLeft i => cases i

/-- Helper toward Definition 3.2: transported boundary indices select the same
oriented dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_dart
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q,
      InfiniteBoundaryDartIndex.dart P
        ((uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
          w hfin htrans hR hL0) i) = InfiniteBoundaryDartIndex.dart Q i := by
  dsimp only
  intro i
  cases i with
  | upperLeft i =>
      change ℕ at i
      rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
      simp only [uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv]
      rfl
  | upperRight i => cases i
  | lowerRight i =>
      change ℕ at i
      rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
      simp only [uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv]
      rfl
  | lowerLeft i => cases i

/-- Helper toward Definition 3.2: the unlabeled exposed presentation stops
within a side exactly at the terminal dart LR(0). -/
theorem uiqbotCanonicalBoundaryPresentationX_sideNext_none_iff
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex P,
      sideNext P i = none ↔
        i = .lowerRight ((uiqbotCanonicalLowerRightIndexEquivX
          w hfin htrans hR hL0).symm 0) := by
  dsimp only
  intro i
  cases i with
  | upperLeft i =>
      change ℕ at i
      simp [sideNext, uiqbotCanonicalBoundaryPresentationX,
        uiqbotDefinition32Presentation, uiqbotCanonicalUpperLeftIndexEquivX]
  | upperRight i => cases i
  | lowerRight i =>
      change ℕ at i
      cases i with
      | zero =>
          simp [sideNext, uiqbotCanonicalBoundaryPresentationX,
            uiqbotDefinition32Presentation, uiqbotCanonicalLowerRightIndexEquivX]
          change (0 : ℕ) = 0
          rfl
      | succ i =>
          simp [sideNext, uiqbotCanonicalBoundaryPresentationX,
            uiqbotDefinition32Presentation, uiqbotCanonicalLowerRightIndexEquivX]
          change i + 1 ≠ 0
          exact Nat.succ_ne_zero _
  | lowerLeft i => cases i

/-- Helper toward Definition 3.2: the next nonempty side after LR in the
unlabeled exposed presentation is UL. -/
theorem uiqbotCanonicalBoundaryPresentationX_nextNonemptySide
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    ∀ t : Fin 4,
      nextNonemptySide P 2 t ↔ t = 0 := by
  intro P
  intro t
  have hUL : Nonempty P.upperLeft.Index :=
    ⟨(uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0⟩
  have hLR : Nonempty P.lowerRight.Index :=
    ⟨(uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0⟩
  have hUR : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    infer_instance
  have hLL : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    infer_instance
  fin_cases t
  · constructor
    · intro _
      rfl
    · intro _
      refine ⟨hUL, by norm_num [sideDistance], ?_⟩
      intro c hc₁ hc₂
      fin_cases c <;> simp_all [sideDistance, sideNonempty]
  · simp [nextNonemptySide, sideDistance, sideNonempty, hUL, hUR, hLR, hLL]
  · simp [nextNonemptySide, sideDistance, sideNonempty, hUL, hUR, hLR, hLL]
  · simp [nextNonemptySide, sideDistance, sideNonempty, hUL, hUR, hLR, hLL]




































































end DirectedDistances.PaperProofs.Section4

end
