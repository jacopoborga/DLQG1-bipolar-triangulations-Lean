module

public import DirectedDistances.KMSW.HatInducedBoundary
public import DirectedDistances.KMSW.HatInducedLeft
public import DirectedDistances.KMSW.HatInducedPendant
public import DirectedDistances.KMSW.HatInducedExit
public import DirectedDistances.KMSW.HatInducedEmbedding

/-! # Conditional assembly of the hatted induced embedding

These are conditional helpers toward Lemma 5.13 (`lem-quad-kmsw`,
resulting rooted embedding are conditional on the named pendant-exit step;
neither declaration is the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The stagewise induced-rotation invariant used by the hatted step theorems.
This is a conditional helper toward Lemma 5.13 (`lem-quad-kmsw`, -/
@[expose] def HatRotInducedAt (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) : Prop :=
  ∀ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
    ∃ k : ℕ, 0 < k ∧
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
        (hatDartMap w h m d) =
          hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
          (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)

/-- All stages satisfy the induced-rotation invariant, conditional on the
named pendant-exit step. This is a helper toward Lemma 5.13
result. -/
theorem hatRotInduced_all_of_exitPendant (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hexitPendant : ∀ k,
      (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = [] →
        HatRotInducedAt w h (hatExitIndex w h k) →
          HatRotInducedAt w h (hatExitIndex w h k + 1)) :
    ∀ m, HatRotInducedAt w h m := by
  intro m
  induction m with
  | zero =>
      intro d
      exact hatDartMap_rot_induced_zero w h d
  | succ m ih =>
      by_cases hex : ∃ k, hatExitIndex w h k = m
      · obtain ⟨k, hk⟩ := hex
        subst m
        by_cases hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = []
        · exact hexitPendant k hur ih
        · exact hatDartMap_rot_induced_exit_activation w h k hur ih
      · have hcodes :
            hatCodes w h m = 0 ∨ hatCodes w h m = 1 ∨ hatCodes w h m = 2 := by
          have hval : (hatCodes w h m).val < 3 := (hatCodes w h m).isLt
          have hc : (hatCodes w h m).val = 0 ∨
              (hatCodes w h m).val = 1 ∨ (hatCodes w h m).val = 2 := by omega
          rcases hc with hc | hc | hc
          · exact Or.inl (Fin.ext hc)
          · exact Or.inr (Or.inl (Fin.ext hc))
          · exact Or.inr (Or.inr (Fin.ext hc))
        rcases hcodes with hc | hc | hc
        · exact hatDartMap_rot_induced_step_left w h m hex hc ih
        · exact hatDartMap_rot_induced_step_up w h m hex hc ih
        · by_cases hur : (kmswStage (hatCodes w h) m).UR = []
          · exact hatDartMap_rot_induced_step_pendant w h m hex hc hur ih
          · exact hatDartMap_rot_induced_step_activation w h m hex hc hur ih

/-- The stagewise dart map forms a rooted induced embedding at every stage,
conditional on the named pendant-exit step. This helper supports Lemma 5.13
result. -/
noncomputable def hatInducedEmbedding_of_exitPendant (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hexitPendant : ∀ k,
      (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = [] →
        HatRotInducedAt w h (hatExitIndex w h k) →
          HatRotInducedAt w h (hatExitIndex w h k + 1))
    (m : ℕ) :
    RootedInducedEmbedding
      (kmswRootedStage (hatCodes w h) m)
      (kmswRootedStage w (quadrantRStageTime w h m)) := by
  refine
    { dartMap := hatDartMap w h m
      injective := hatDartMap_injective w h m
      flip_comm := ?_
      present := ?_
      tail_comm := ?_
      rot_induced := ?_
      root_comm := hatDartMap_root w h m }
  · intro d
    exact (hatDartMap_edgeInv w h m d).symm
  · intro d hd
    exact hatDartMap_present w h m d hd
  · intro d hd
    exact hatDartMap_tail w h m d hd
  · exact hatRotInduced_all_of_exitPendant w h hexitPendant m

end DirectedDistances.KMSW
