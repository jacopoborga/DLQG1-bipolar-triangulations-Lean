module

public import DirectedDistances.KMSW.MonotoneStageFamily
public import DirectedDistances.KMSW.MonotoneStepGoodACT
public import DirectedDistances.KMSW.MonotoneStepInvACT
public import DirectedDistances.KMSW.MonotoneStepGoodPEN
public import DirectedDistances.KMSW.MonotoneStepInvPEN
public import DirectedDistances.KMSW.MonotoneStepGoodUP
public import DirectedDistances.KMSW.MonotoneStepInvUP
public import DirectedDistances.KMSW.MonotoneStepGoodLEX
public import DirectedDistances.KMSW.MonotoneStepInvLEX
public import DirectedDistances.KMSW.MonotoneStepGoodLFR
public import DirectedDistances.KMSW.MonotoneStepInvLFR

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

/-- Every KMSW step preserves the monotone stage invariant (`def-kmsw`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStepFrom_all (w : ℕ → Fin 3) (n : ℕ) : MonotoneStepFrom w n := by
  apply monotoneStepFrom_of_cases w n
  · intro hc e es hUR P G
    exact ⟨layoutGood_succ_act w n hc e es hUR G,
      ⟨invariant_succ_act w n hc e es hUR G _⟩⟩
  · intro hc hUR P G
    exact ⟨layoutGood_succ_pen w n hc hUR G, ⟨invariant_succ_pen w n hc hUR G _⟩⟩
  · intro hc P G
    exact ⟨layoutGood_succ_up w n hc G, ⟨invariant_succ_up w n hc G _⟩⟩
  · intro hc e es hUL P G
    exact ⟨layoutGood_succ_lex w n hc e es hUL G,
      ⟨invariant_succ_lex w n hc e es hUL G _⟩⟩
  · intro hc hUL P G
    exact ⟨layoutGood_succ_lfr w n hc hUL G, ⟨invariant_succ_lfr w n hc hUL G _⟩⟩

/-- The x-monotone layout drawings carry a stage invariant at every stage, for every
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_family_all (w : ℕ → Fin 3) :
    ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)) :=
  monotone_family w (monotoneStepFrom_all w)

end DirectedDistances.KMSW
