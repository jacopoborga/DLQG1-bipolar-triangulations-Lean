module

public import DirectedDistances.KMSW.QuadKMSWHatAllStages
public import DirectedDistances.KMSW.CoherentLimitMaps

/-! # Limit input from the all-stage M-hat simulation

This module assembles the stagewise M-hat incidence simulation into the input
for the limit argument toward `lem-quad-kmsw`
hypothesis is a separate structural property, to be proved in
`QuadKMSWHatStructure`. These helpers make no face or rotation claim and do
not prove the full `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Every all-stage vertex map fixes the root, by coherence with the identity
map at stage zero. This is root data for `lem-quad-kmsw` -/
theorem hatAllVertexMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, hatAllVertexMap w h m 0 = 0 := by
  intro m
  have hzero : 0 < (kmswStage (hatCodes w h) 0).nextVertex := by
    change 0 < 2
    omega
  calc
    hatAllVertexMap w h m 0 = hatAllVertexMap w h 0 0 :=
      hatAllVertexMap_eq_of_le w h 0 m 0 (Nat.zero_le m) hzero
    _ = 0 := rfl

/-- The canonical R-stage times are unbounded: distinct extracted indices
have distinct counters, so monotonicity makes each time at least its index.
This supplies time data for `lem-quad-kmsw` -/
theorem quadrantRStageTime_unbounded (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ n, ∃ m, n ≤ quadrantRStageTime w h m := by
  have hbound : ∀ m, m ≤ quadrantRStageTime w h m := by
    intro m
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
        have hmono : quadrantRStageTime w h m ≤ quadrantRStageTime w h (m + 1) :=
          quadrantRStageTime_mono w h (Nat.le_succ m)
        have hne : quadrantRStageTime w h m ≠ quadrantRStageTime w h (m + 1) := by
          intro heq
          have hcount := (quadrantRStageTime_spec w h m).2.1
          rw [heq, (quadrantRStageTime_spec w h (m + 1)).2.1] at hcount
          omega
        omega
  intro n
  exact ⟨n, hbound n⟩

/-- The all-stage reachable-edge identity in the set-image form required by
the coherent limit construction for `lem-quad-kmsw` -/
theorem hatAllEdgeMap_set_image_eq_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    hatAllEdgeMap w h m '' {e | e < (kmswStage (hatCodes w h) m).nextEdge ∧
      (kmswStage (hatCodes w h) m).present e = true} =
      stageReachablePresentEdges w (quadrantRStageTime w h m) := by
  rw [← hatAllEdgeMap_image_eq_reachable w h m]
  ext e
  constructor
  · rintro ⟨f, ⟨hf, hp⟩, he⟩
    exact ⟨f, hf, hp, he⟩
  · rintro ⟨f, hf, hp, he⟩
    exact ⟨f, ⟨hf, hp⟩, he⟩

/-- Assemble the stagewise M-hat simulation into limit input using the
canonical first-allocation edge and vertex maps, toward `lem-quad-kmsw`
separate allocated non-root incidence property to be proved in
`QuadKMSWHatStructure`; it is retained explicitly here. This is not the full
paper lemma and asserts no face or rotation correspondence. -/
theorem hatImageLimitInput_exists_of_incident (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hinc : ∀ a : PresentVertex (hatCodes w h),
      (∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex) → a.id ≠ 0 →
        ∃ e, EdgePresent (hatCodes w h) e ∧
          (edgeWest (hatCodes w h) e = a.id ∨ edgeEast (hatCodes w h) e = a.id) ∧
          Reachable (⟨0⟩ : PresentVertex (hatCodes w h))
            ⟨edgeWest (hatCodes w h) e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex (hatCodes w h))
            ⟨edgeEast (hatCodes w h) e⟩) :
    ∃ eφ vφ : ℕ → ℕ,
      HatImageLimitInput (hatCodes w h) w (quadrantRStageTime w h) eφ vφ := by
  refine ⟨limitEdgeMap (hatAllEdgeMap w h) (hatCodes w h),
    limitVertexMap (hatAllVertexMap w h) (hatCodes w h), ?_⟩
  exact hatImageLimitInput_of_coherent_stage_maps
    (quadrantRStageTime w h) (hatAllEdgeMap w h) (hatAllVertexMap w h)
    (fun _ _ hmn => quadrantRStageTime_mono w h hmn)
    (quadrantRStageTime_unbounded w h)
    (hatAllEdgeMap_extend w h) (hatAllVertexMap_extend w h)
    (fun m => (hatAll_sim w h m).incidenceSim)
    (hatAllEdgeMap_set_image_eq_reachable w h)
    (hatAllVertexMap_root w h) hinc

end DirectedDistances.KMSW
