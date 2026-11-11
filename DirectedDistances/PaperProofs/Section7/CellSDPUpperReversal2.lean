module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperReversal

/-! The two- and three-step cases of the open finite-cell reversal obligation at
defined without assuming it. This file does not close Lemma 7.8. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver
open DirectedDistances.KMSW

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
@[simp] private theorem reversal_swap_two : Equiv.swap (0 : Fin 3) 1 2 = 2 := by
  decide

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private def lowerVertex (w : ℕ → Fin 3) (n y : ℕ) : Prop :=
  ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
    (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private def upperVertex (w : ℕ → Fin 3) (n y : ℕ) : Prop :=
  ∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
    (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
with the same endpoint and path witness order as the existing open obligation. -/
@[expose] def cellSdpUpper_reversalInteriorPathTransportAt (n : ℕ) : Prop :=
  ∀ ω : ℕ → Fin 3,
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal n ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      (¬ ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
            (kmswStage wr n).west e = xr ∨ (kmswStage wr n).east e = xr) →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩,
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩,
                q.length ≤ p.length

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
the selected reversed lower vertex is outside the reversed upper boundary. -/
private theorem one_edge_transport (w wr : ℕ → Fin 3) (n y yr x : ℕ)
    (hnot : ¬ upperVertex wr n yr)
    (hx : lowerVertex w n x) (e : (⟨x⟩ : StagePresentVertex w n) ⟶ ⟨y⟩) :
    ∀ xr : ℕ, upperVertex wr n xr →
      ∀ p : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩,
        ∃ x : ℕ, lowerVertex w n x ∧
          ∃ q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩,
            q.length ≤ p.length := by
  intro xr hxr p
  have hpos : 0 < p.length := by
    by_contra hn
    have heq := congrArg StagePresentVertex.id (p.eq_of_length_zero (by omega))
    change yr = xr at heq
    exact hnot (heq.symm ▸ hxr)
  exact ⟨x, hx, Path.nil.cons e, by simpa only [Path.length_cons, Path.length_nil]⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
All nine two-letter codes satisfy the exact interior path transport obligation. -/
theorem cellSdpUpper_reversalInteriorPathTransport_two :
    cellSdpUpper_reversalInteriorPathTransportAt 2 := by
  intro ω
  dsimp only
  intro y hy hyl
  generalize hc₁ : ω 1 = c₁
  generalize hc₂ : ω 2 = c₂
  have hr₁ : codeReversal 2 ω 1 = Equiv.swap (0 : Fin 3) 1 c₂ := by
    simp [codeReversal, hc₂]
  have hr₂ : codeReversal 2 ω 2 = Equiv.swap (0 : Fin 3) 1 c₁ := by
    simp [codeReversal, hc₁]
  fin_cases c₁ <;> fin_cases c₂
  all_goals
    simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge, hc₁, hc₂] at hy hyl
  all_goals try omega
  · have hy3 : y = 3 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 2 3 0 2 ?_ ?_ ⟨3, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]
  · have hy2 : y = 2 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 2 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]
  · have hy23 : y = 2 ∨ y = 3 := by omega
    rcases hy23 with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 2 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]
    · refine ⟨0, ?_, one_edge_transport _ _ 2 3 0 0 ?_ ?_ ⟨3, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]
  · have hy2 : y = 2 := by omega
    subst y
    refine ⟨1, ?_, one_edge_transport _ _ 2 2 1 0 ?_ ?_ ⟨1, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]
  · have hy3 : y = 3 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 2 3 0 1 ?_ ?_ ⟨2, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hr₁, hr₂]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
no zero- or one-edge reversed path reaches the upper boundary. -/
private theorem two_edge_transport (w wr : ℕ → Fin 3) (n y yr x : ℕ)
    (hnot : ¬ upperVertex wr n yr)
    (hnoarrow : ∀ xr, upperVertex wr n xr →
      ((⟨yr⟩ : StagePresentVertex wr n) ⟶ ⟨xr⟩) → False)
    (hx : lowerVertex w n x) (q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩)
    (hq : q.length = 2) :
    ∀ xr : ℕ, upperVertex wr n xr →
      ∀ p : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩,
        ∃ x : ℕ, lowerVertex w n x ∧
          ∃ q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩,
            q.length ≤ p.length := by
  intro xr hxr p
  refine ⟨x, hx, q, ?_⟩
  rw [hq]
  cases p with
  | nil => exact (hnot hxr).elim
  | cons p e =>
    cases p with
    | nil => exact (hnoarrow _ hxr e).elim
    | cons p f => simp only [Path.length_cons]; omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
Three-step transport for codes beginning with letter 0. -/
private theorem reversal_three_zero (ω : ℕ → Fin 3) (hc₁ : ω 1 = 0) :
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal 3 ω (i + 1)
    ∀ y, upperVertex w 3 y → ¬ lowerVertex w 3 y →
      ∃ yr, lowerVertex wr 3 yr ∧
        ∀ xr, upperVertex wr 3 xr →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr 3) ⟨xr⟩,
            ∃ x, lowerVertex w 3 x ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w 3) ⟨y⟩,
                q.length ≤ p.length := by
  dsimp only
  intro y hy hyl
  generalize hc₂ : ω 2 = c₂
  generalize hc₃ : ω 3 = c₃
  have hr₁ : codeReversal 3 ω 1 = Equiv.swap (0 : Fin 3) 1 c₃ := by
    simp [codeReversal, hc₃]
  have hr₂ : codeReversal 3 ω 2 = Equiv.swap (0 : Fin 3) 1 c₂ := by
    simp [codeReversal, hc₂]
  have hr₃ : codeReversal 3 ω 3 = Equiv.swap (0 : Fin 3) 1 0 := by
    simp [codeReversal, hc₁]
  fin_cases c₂ <;> fin_cases c₃
  all_goals
    simp [upperVertex, lowerVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃] at hy hyl
  all_goals try omega
  · have hyv : y = 4 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 3 ?_ ?_ ⟨5, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 2 ?_ ?_ ⟨3, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 ∨ y = 4 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 2 ?_ ?_ ⟨3, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 2 ?_ ?_ ⟨5, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 := by omega
    subst y
    refine ⟨1, ?_, one_edge_transport _ _ 3 3 1 2 ?_ ?_ ⟨3, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 4 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 1 ?_ ?_ ⟨4, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
Three-step transport for codes beginning with letter 1. -/
private theorem reversal_three_one (ω : ℕ → Fin 3) (hc₁ : ω 1 = 1) :
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal 3 ω (i + 1)
    ∀ y, upperVertex w 3 y → ¬ lowerVertex w 3 y →
      ∃ yr, lowerVertex wr 3 yr ∧
        ∀ xr, upperVertex wr 3 xr →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr 3) ⟨xr⟩,
            ∃ x, lowerVertex w 3 x ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w 3) ⟨y⟩,
                q.length ≤ p.length := by
  dsimp only
  intro y hy hyl
  generalize hc₂ : ω 2 = c₂
  generalize hc₃ : ω 3 = c₃
  have hr₁ : codeReversal 3 ω 1 = Equiv.swap (0 : Fin 3) 1 c₃ := by
    simp [codeReversal, hc₃]
  have hr₂ : codeReversal 3 ω 2 = Equiv.swap (0 : Fin 3) 1 c₂ := by
    simp [codeReversal, hc₂]
  have hr₃ : codeReversal 3 ω 3 = Equiv.swap (0 : Fin 3) 1 1 := by
    simp [codeReversal, hc₁]
  fin_cases c₂ <;> fin_cases c₃
  all_goals
    simp [upperVertex, lowerVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃] at hy hyl
  all_goals try omega
  · have hyv : y = 2 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 ∨ y = 4 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 3 ?_ ?_ ⟨5, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 := by omega
    subst y
    refine ⟨1, ?_, one_edge_transport _ _ 3 2 1 0 ?_ ?_ ⟨1, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 ∨ y = 3 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 0 ?_ ?_ ⟨3, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 ∨ y = 3 ∨ y = 4 := by omega
    rcases hyv with rfl | rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 0 ?_ ?_ ⟨3, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 0 ?_ ?_ ⟨5, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 ∨ y = 3 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 0 ?_ ?_ ⟨3, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 2 ∨ y = 3 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 2 0 0 ?_ ?_ ⟨1, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · let e₁ : (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) 3) ⟶ ⟨2⟩ :=
        ⟨1, by simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hc₁, hc₂, hc₃]⟩
      let e₂ : (⟨2⟩ : StagePresentVertex (fun i => ω (i + 1)) 3) ⟶ ⟨3⟩ :=
        ⟨3, by simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hc₁, hc₂, hc₃]⟩
      refine ⟨0, ?_, two_edge_transport _ _ 3 3 0 0 ?_ ?_ ?_
        ((Path.nil.cons e₁).cons e₂) rfl⟩
      · simp [lowerVertex, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hr₁, hr₂, hr₃]
      · simp [upperVertex, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hr₁, hr₂, hr₃]
      · intro xr hxr e
        have he := e.property
        change e.val < (kmswStage (fun i => codeReversal 3 ω (i + 1)) 3).nextEdge ∧
          (kmswStage (fun i => codeReversal 3 ω (i + 1)) 3).present e.val = true ∧
          (kmswStage (fun i => codeReversal 3 ω (i + 1)) 3).west e.val = 0 ∧
          (kmswStage (fun i => codeReversal 3 ω (i + 1)) 3).east e.val = xr at he
        simp [upperVertex, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hr₁, hr₂, hr₃] at hxr
        simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hr₁, hr₂, hr₃] at he
        obtain ⟨hb, _, hw, heast⟩ := he
        have hcases : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨
            e.val = 3 ∨ e.val = 4 := by omega
        rcases hcases with heq | heq | heq | heq | heq
        all_goals simp [heq] at hw heast
        all_goals omega
      · simp [lowerVertex, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
          kmswInit, State.addEdge, hc₁, hc₂, hc₃]
  · have hyv : y = 2 := by omega
    subst y
    refine ⟨2, ?_, one_edge_transport _ _ 3 2 2 0 ?_ ?_ ⟨1, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
Three-step transport for codes beginning with letter 2. -/
private theorem reversal_three_two (ω : ℕ → Fin 3) (hc₁ : ω 1 = 2) :
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal 3 ω (i + 1)
    ∀ y, upperVertex w 3 y → ¬ lowerVertex w 3 y →
      ∃ yr, lowerVertex wr 3 yr ∧
        ∀ xr, upperVertex wr 3 xr →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr 3) ⟨xr⟩,
            ∃ x, lowerVertex w 3 x ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w 3) ⟨y⟩,
                q.length ≤ p.length := by
  dsimp only
  intro y hy hyl
  generalize hc₂ : ω 2 = c₂
  generalize hc₃ : ω 3 = c₃
  have hr₁ : codeReversal 3 ω 1 = Equiv.swap (0 : Fin 3) 1 c₃ := by
    simp [codeReversal, hc₃]
  have hr₂ : codeReversal 3 ω 2 = Equiv.swap (0 : Fin 3) 1 c₂ := by
    simp [codeReversal, hc₂]
  have hr₃ : codeReversal 3 ω 3 = Equiv.swap (0 : Fin 3) 1 2 := by
    simp [codeReversal, hc₁]
  fin_cases c₂ <;> fin_cases c₃
  all_goals
    simp [upperVertex, lowerVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃] at hy hyl
  all_goals try omega
  · have hyv : y = 3 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 0 ?_ ?_ ⟨3, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 0 ?_ ?_ ⟨4, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 ∨ y = 4 := by omega
    rcases hyv with rfl | rfl
    · refine ⟨0, ?_, one_edge_transport _ _ 3 3 0 1 ?_ ?_ ⟨2, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
    · refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 1 ?_ ?_ ⟨4, ?_⟩⟩
      all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 3 := by omega
    subst y
    refine ⟨1, ?_, one_edge_transport _ _ 3 3 1 1 ?_ ?_ ⟨2, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]
  · have hyv : y = 4 := by omega
    subst y
    refine ⟨0, ?_, one_edge_transport _ _ 3 4 0 2 ?_ ?_ ⟨3, ?_⟩⟩
    all_goals simp [lowerVertex, upperVertex, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hc₁, hc₂, hc₃, hr₁, hr₂, hr₃]


/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
All twenty-seven three-letter codes satisfy the exact path transport obligation. -/
theorem cellSdpUpper_reversalInteriorPathTransport_three :
    cellSdpUpper_reversalInteriorPathTransportAt 3 := by
  intro ω
  have hc : ω 1 = 0 ∨ ω 1 = 1 ∨ ω 1 = 2 := by
    have hb := (ω 1).isLt
    omega
  rcases hc with hc | hc | hc
  · exact reversal_three_zero ω hc
  · exact reversal_three_one ω hc
  · exact reversal_three_two ω hc

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
an attained minimum over all upper-boundary endpoints, including its own endpoint. -/
private theorem shortest_upper_exit (w : ℕ → Fin 3) (n yr xr : ℕ)
    (hxr : upperVertex w n xr) (p : Path (⟨yr⟩ : StagePresentVertex w n) ⟨xr⟩) :
    ∃ zr, upperVertex w n zr ∧
      ∃ r : Path (⟨yr⟩ : StagePresentVertex w n) ⟨zr⟩,
        r.length ≤ p.length ∧
          ∀ z, upperVertex w n z →
            ∀ q : Path (⟨yr⟩ : StagePresentVertex w n) ⟨z⟩,
              r.length ≤ q.length := by
  classical
  let P (k : ℕ) : Prop := ∃ z, upperVertex w n z ∧
    ∃ q : Path (⟨yr⟩ : StagePresentVertex w n) ⟨z⟩, q.length = k
  have hP : ∃ k, P k := ⟨p.length, xr, hxr, p, rfl⟩
  obtain ⟨zr, hzr, r, hr⟩ := Nat.find_spec hP
  refine ⟨zr, hzr, r, ?_, ?_⟩
  · rw [hr]
    exact Nat.find_min' hP ⟨xr, hxr, p, rfl⟩
  · intro z hz q
    rw [hr]
    exact Nat.find_min' hP ⟨z, hz, q, rfl⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
Only paths minimizing exit length over the entire reversed upper boundary need
transport. The original lower endpoint and its path may depend on this minimizing
path. This proposition is defined, never assumed or asserted unconditionally. -/
@[expose] def cellSdpUpper_reversalShortestExitTransport : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ ω : ℕ → Fin 3,
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal n ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      (¬ ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
            (kmswStage wr n).west e = xr ∨ (kmswStage wr n).east e = xr) →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩,
            (∀ zr : ℕ,
              (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
                (kmswStage wr n).west e = zr ∨ (kmswStage wr n).east e = zr) →
              ∀ r : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨zr⟩,
                p.length ≤ r.length) →
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩,
                q.length ≤ p.length

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
at stages at least four. The two- and three-step cases are proved, and arbitrary
reversed paths are replaced by an attained shortest exit without exchanging the
selected reversed lower vertex with a path-dependent witness. -/
theorem cellSdpUpper_reversalInteriorPathTransport_iff_shortestExitTransport :
    cellSdpUpper_reversalInteriorPathTransport ↔
      cellSdpUpper_reversalShortestExitTransport := by
  constructor
  · intro h n hn ω
    dsimp only
    intro y hy hyl
    obtain ⟨yr, hyr, ht⟩ := h n (by omega) ω y hy hyl
    exact ⟨yr, hyr, fun xr hxr p _ => ht xr hxr p⟩
  · intro h n hn
    by_cases hn4 : 4 ≤ n
    · intro ω
      dsimp only
      intro y hy hyl
      obtain ⟨yr, hyr, ht⟩ := h n hn4 ω y hy hyl
      refine ⟨yr, hyr, fun xr hxr p => ?_⟩
      obtain ⟨zr, hzr, r, hr, hmin⟩ := shortest_upper_exit _ n yr xr hxr p
      obtain ⟨x, hx, q, hq⟩ := ht zr hzr r hmin
      exact ⟨x, hx, q, hq.trans hr⟩
    · have hn23 : n = 2 ∨ n = 3 := by omega
      rcases hn23 with rfl | rfl
      · exact cellSdpUpper_reversalInteriorPathTransport_two
      · exact cellSdpUpper_reversalInteriorPathTransport_three

end DirectedDistances.PaperProofs.Section7
