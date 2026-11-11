/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation27
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation23

/-! Finite-stage skipped-side marks and the remaining finite boundary package. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

private theorem kmswStageFiniteBoundaryPresentation28_skipped_side_cases
    {V E : Type*} {M : DirectedPlaneMapWithMissing V E}
    (Q : InfiniteBoundaryPresentation M)
    (hUL : sideNonempty Q 0) (hLR : sideNonempty Q 2)
    (a b k : Fin 4) (hnext : nextNonemptySide Q a b)
    (hk₁ : 0 < sideDistance a k)
    (hk₂ : sideDistance a k < sideDistance a b) :
    (a = 0 ∧ b = 2 ∧ k = 1) ∨ (a = 2 ∧ b = 0 ∧ k = 3) := by
  have hdist := hnext.2.1
  have hskipUL : ¬ (0 < sideDistance a 0 ∧
      sideDistance a 0 < sideDistance a b) := by
    rintro ⟨h₁, h₂⟩
    exact hnext.2.2 0 h₁ h₂ hUL
  have hskipLR : ¬ (0 < sideDistance a 2 ∧
      sideDistance a 2 < sideDistance a b) := by
    rintro ⟨h₁, h₂⟩
    exact hnext.2.2 2 h₁ h₂ hLR
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    norm_num [sideDistance] at *

/-- Helper toward Definition 3.2: every side strictly between a terminal
side and its geometric successor is empty, and both of its retained marks
equal the actual shared corner. Only UR or LL can be skipped, since UL and
LR are nonempty. -/
theorem kmswStageFiniteBoundaryPresentation28_intervening_side_endpoints
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft)
    (hUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight)
    (hLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight)
    (hLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft) :
    ∀ i j : InfiniteBoundaryDartIndex
        (kmswStageFiniteBoundaryPresentation w n M J),
      (fun d => (stageRot w n).symm (d.1, !d.2))
          (InfiniteBoundaryDartIndex.dart _ i) = InfiniteBoundaryDartIndex.dart _ j →
      sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = none →
      let Q := kmswStageFiniteBoundaryPresentation w n M J
      let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)
      ∀ k : Fin 4,
        0 < sideDistance (sideTag Q i) k →
        sideDistance (sideTag Q i) k <
          (if sideTag Q i = sideTag Q j then 4
            else sideDistance (sideTag Q i) (sideTag Q j)) →
        ¬ sideNonempty Q k ∧
          sideInitialVertex? Q k = some v ∧ sideTerminalVertex? Q k = some v := by
  intro i j hsucc hlast
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hsucc' : (stageRot w n).symm
      (edgeFlip _ (InfiniteBoundaryDartIndex.dart Q i)) =
      InfiniteBoundaryDartIndex.dart Q j := hsucc
  obtain hstep | ⟨_, hfirst, hnext⟩ :=
    kmswStageFiniteBoundaryPresentation27_successor_classification
      w n P M J hreal i j hsucc'
  · rw [hlast] at hstep
    cases hstep
  have hne : sideTag Q i ≠ sideTag Q j := by
    intro heq
    have hd := hnext.2.1
    rw [heq] at hd
    unfold sideDistance at hd
    have he : (sideTag Q j).val + 4 - (sideTag Q j).val = 4 := by omega
    rw [he, Nat.mod_self] at hd
    omega
  have hmarks := kmswStageFiniteBoundaryPresentation22_join_marks_of_first
    w n P M J hreal hUL hUR hLR hLL i j hsucc hlast hfirst
  change sideTerminalVertex? Q (sideTag Q i) =
      some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) ∧
    sideInitialVertex? Q (sideTag Q j) =
      some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) at hmarks
  have hpresent := kmswStageFiniteBoundaryPresentation13_present_sides_nonempty w n M J
  have hnonUL : sideNonempty Q 0 := hpresent.1
  have hnonLR : sideNonempty Q 2 := hpresent.2
  dsimp only
  intro k hk₁ hk₂
  rw [ite_eq_right hne] at hk₂
  have hempty := hnext.2.2 k hk₁ hk₂
  refine ⟨hempty, ?_⟩
  obtain ⟨ha, hb, hk⟩ | ⟨ha, hb, hk⟩ :=
    kmswStageFiniteBoundaryPresentation28_skipped_side_cases
      Q hnonUL hnonLR (sideTag Q i) (sideTag Q j) k hnext hk₁ hk₂
  · rw [ha] at hmarks
    rw [hb] at hmarks
    subst k
    exact ⟨hmarks.1, hmarks.2⟩
  · rw [ha] at hmarks
    rw [hb] at hmarks
    subst k
    exact ⟨hmarks.1, hmarks.2⟩

/-- Helper toward Definition 3.2: the finite-stage presentation has all
required join endpoint labels, including both possible skipped missing sides. -/
theorem kmswStageFiniteBoundaryPresentation28_required_join_labels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft)
    (hUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight)
    (hLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight)
    (hLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft) :
    RequiredFiniteBoundaryJoinEndpointLabels7
      (kmswStageFiniteBoundaryPresentation w n M J)
      (fun d => (stageRot w n).symm (d.1, !d.2)) := by
  apply (kmswStageFiniteBoundaryPresentation22_join_labels_iff_core w n M J).mpr
  intro i j hsucc hlast
  have hsucc' : (stageRot w n).symm
      (edgeFlip _ (InfiniteBoundaryDartIndex.dart
        (kmswStageFiniteBoundaryPresentation w n M J) i)) =
      InfiniteBoundaryDartIndex.dart
        (kmswStageFiniteBoundaryPresentation w n M J) j := hsucc
  obtain hstep | ⟨_, hfirst, _⟩ :=
    kmswStageFiniteBoundaryPresentation27_successor_classification
      w n P M J hreal i j hsucc'
  · rw [hlast] at hstep
    cases hstep
  have hmarks := kmswStageFiniteBoundaryPresentation22_join_marks_of_first
    w n P M J hreal hUL hUR hLR hLL i j hsucc hlast hfirst
  have hintervening :=
    kmswStageFiniteBoundaryPresentation28_intervening_side_endpoints
      w n P M J hreal hUL hUR hLR hLL i j hsucc hlast
  exact ⟨hmarks.1, hmarks.2, fun k hk₁ hk₂ => (hintervening k hk₁ hk₂).2⟩

/-- Helper toward Definition 3.2: every finite stage admits the constructed
map, retained four-side presentation, and geometric finite-boundary package.
No open-clause hypothesis is required. -/
theorem exists_kmswStage_bound_edges32 (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  obtain ⟨P, U, hU, hborder, hpackage⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses23 w n
  exact ⟨P, U, hU, hborder, hpackage
    (kmswStageFiniteBoundaryPresentation28_required_join_labels w n P)⟩

end DirectedDistances.PaperProofs.Section3

end
