/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIQBOTPlaneRealization
public import DirectedDistances.KMSW.PathSpaceTransferCarrier
public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData

/-! # UIQBOT boundary presentation -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: regard a directed plane map as a map with
no missing edges, preserving its drawing and its edge orientation. -/
@[expose] def uiqbotMapWithNoMissing {V E : Type*} (M : DirectedPlaneMap V E) :
    DirectedPlaneMapWithMissing V E :=
  { toPlaneMapWithMissing :=
      { toPlaneGraphDrawing := M.toPlaneGraphDrawing
        missing := fun _ => False
        missing_on_external := by
          intro e he
          exact False.elim he }
    forward := fun e => M.forward e.1 }

/-- Helper toward Definition 3.2: the two present UIQBOT boundary chains,
with the lower-right chain indexed in external-face traversal order. -/
@[expose] def uiqbotDefinition32Presentation
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    InfiniteBoundaryPresentation (uiqbotMapWithNoMissing M) := by
  let M0 := uiqbotMapWithNoMissing M
  have hleft : Function.Injective (kmswLeftBoundaryEdge w) :=
    (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).1
  have hright : Function.Injective (kmswRightBoundaryEdge w) :=
    (kmswRightBoundary_infinite_present_path w hL0 hR).1
  refine ⟨⟨ℕ, ?_, (fun i => some (i + 1)), some 0, none⟩,
    ⟨Empty, ⟨(fun i => nomatch i), by intro i; nomatch i⟩,
      (fun i => nomatch i), none, none⟩,
    ⟨ℕ, ?_, (fun i => if i = 0 then none else some (i - 1)), none, some 0⟩,
    ⟨Empty, ⟨(fun i => nomatch i), by intro i; nomatch i⟩,
      (fun i => nomatch i), none, none⟩⟩
  · refine ⟨fun i =>
      (iota (kmswLeftBoundaryEdge w i),
        M0.forward ⟨iota (kmswLeftBoundaryEdge w i), by
          simp [M0, uiqbotMapWithNoMissing]⟩), ?_⟩
    intro i j hij
    apply hleft
    exact iota.injective (congrArg Prod.fst hij)
  · refine ⟨fun i =>
      (iota (kmswRightBoundaryEdge w i),
        !(M0.forward ⟨iota (kmswRightBoundaryEdge w i), by
          simp [M0, uiqbotMapWithNoMissing]⟩)), ?_⟩
    intro i j hij
    apply hright
    exact iota.injective (congrArg Prod.fst hij)

/-- Helper toward Definition 3.2: the constructed presentation has empty
upper-right and lower-left sides, as required for the UIQBOT with no missing -/
theorem uiqbotDefinition32Presentation_emptySides
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    UROkInf (uiqbotDefinition32Presentation w htrans hR hL0 M iota) ∧
      LLOkInf (uiqbotDefinition32Presentation w htrans hR hL0 M iota) := by
  let P := uiqbotDefinition32Presentation w htrans hR hL0 M iota
  letI : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    exact inferInstance
  letI : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    exact inferInstance
  exact ⟨UROkInf_of_isEmpty P, LLOkInf_of_isEmpty P⟩





































end DirectedDistances.PaperProofs.Section4

end

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem uiqbotDefinition32Presentation_eq
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    uiqbotDefinition32Presentation w htrans hR hL0 M iota = by
      let M0 := uiqbotMapWithNoMissing M
      have hleft : Function.Injective (kmswLeftBoundaryEdge w) :=
        (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).1
      have hright : Function.Injective (kmswRightBoundaryEdge w) :=
        (kmswRightBoundary_infinite_present_path w hL0 hR).1
      refine ⟨⟨ℕ, ?_, (fun i => some (i + 1)), some 0, none⟩,
        ⟨Empty, ⟨(fun i => nomatch i), by intro i; nomatch i⟩,
          (fun i => nomatch i), none, none⟩,
        ⟨ℕ, ?_, (fun i => if i = 0 then none else some (i - 1)), none, some 0⟩,
        ⟨Empty, ⟨(fun i => nomatch i), by intro i; nomatch i⟩,
          (fun i => nomatch i), none, none⟩⟩
      · refine ⟨fun i =>
          (iota (kmswLeftBoundaryEdge w i),
            M0.forward ⟨iota (kmswLeftBoundaryEdge w i), by
              simp [M0, uiqbotMapWithNoMissing]⟩), ?_⟩
        intro i j hij
        apply hleft
        exact iota.injective (congrArg Prod.fst hij)
      · refine ⟨fun i =>
          (iota (kmswRightBoundaryEdge w i),
            !(M0.forward ⟨iota (kmswRightBoundaryEdge w i), by
              simp [M0, uiqbotMapWithNoMissing]⟩)), ?_⟩
        intro i j hij
        apply hright
        exact iota.injective (congrArg Prod.fst hij) := by
  exact uiqbotDefinition32Presentation.eq_def w htrans hR hL0 M iota

end DirectedDistances.PaperProofs.Section4
end
end

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem uiqbotMapWithNoMissing_drawing_eq {V E : Type*}
    (M : DirectedPlaneMap V E) :
    (uiqbotMapWithNoMissing M).toPlaneMapWithMissing.toPlaneGraphDrawing =
      M.toPlaneGraphDrawing := rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem uiqbotMapWithNoMissing_missing_eq {V E : Type*}
    (M : DirectedPlaneMap V E) (e : E) :
    (uiqbotMapWithNoMissing M).toPlaneMapWithMissing.missing e = False := rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem uiqbotMapWithNoMissing_forward_eq {V E : Type*}
    (M : DirectedPlaneMap V E) (e : E) :
    (uiqbotMapWithNoMissing M).forward
      ⟨e, by simp [uiqbotMapWithNoMissing]⟩ = M.forward e := rfl

end DirectedDistances.PaperProofs.Section4
end
