/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimes
public import DirectedDistances.KMSW.QuadrantSourceWalks
public import DirectedDistances.RandomWalk.QuadrantWalkUncond

/-! Supporting lemmas for paper labels `lem-flow-line-times`, `lem-quadrant-walk` (see CORRESPONDENCE.md). -/

/- # Source-indexed quadrant walk law

Candidate provider for corrected Lemma 5.14, `lem-quadrant-walk` -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open Quiver
open scoped Classical BigOperators

/-- Endpoint (vertex-induced) encoding of edge membership `lambda_n ∈ Mhat`
by `sourceFlowMhat_endpoints_iff`. -/
@[expose] def sourceLambdaInMhat (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).east (act w n)⟩







@[expose] def sourceLambdaInMhatPrime (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  ¬ sourceLambdaInMhat w n

/-- For positive source indices, `lambda_n ∈ Mhat` exactly when the active
west endpoint is reachable (`lem-flow-line-times`,
the present west-to-east active arrow. -/
theorem sourceLambdaInMhat_iff_quadrantHatTime (w : ℕ → Fin 3) (n : ℕ)
    (hn : 1 ≤ n) :
    sourceLambdaInMhat w n ↔ quadrantHatTime w n := by
  constructor
  · rintro ⟨hw, _⟩
    exact ⟨hn, hw⟩
  · rintro ⟨_, hw⟩
    exact (sourceFlowMhat_endpoints_iff w n).mp hw

/-- For positive source indices, `lambda_n ∈ Mhat'` exactly when its active
west endpoint is unreachable (`lem-flow-line-times`, -/
theorem sourceLambdaInMhatPrime_iff_quadrantPrimedTime
    (w : ℕ → Fin 3) (n : ℕ) (hn : 1 ≤ n) :
    sourceLambdaInMhatPrime w n ↔ quadrantPrimedTime w n := by
  constructor
  · intro hnot
    refine ⟨hn, ?_⟩
    intro hw
    apply hnot
    exact ⟨hw, kmswStage_activeEast_reachable w n hw⟩
  · rintro ⟨_, hnot⟩ hmem
    exact hnot hmem.1

/-- Literal positive-time count predicate for `S_m`, using `lambda_n ∈ Mhat` -/
@[expose] def sourceQuadrantHatTime (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  1 ≤ n ∧ sourceLambdaInMhat w n

/-- Literal positive-time count predicate for `S'_m`, using `lambda_n ∈ Mhat'` -/
@[expose] def sourceQuadrantPrimedTime (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  1 ≤ n ∧ sourceLambdaInMhatPrime w n

private theorem sourceQuadrantHatTime_eq (w : ℕ → Fin 3) :
    sourceQuadrantHatTime w = quadrantHatTime w := by
  funext n
  apply propext
  change (1 ≤ n ∧ _ ∧ _) ↔ (1 ≤ n ∧ _)
  constructor
  · rintro ⟨hn, hw, _⟩
    exact ⟨hn, hw⟩
  · rintro ⟨hn, hw⟩
    exact ⟨hn, hw, (sourceFlowMhat_endpoints_iff w n).mp hw |>.2⟩

private theorem sourceQuadrantPrimedTime_eq (w : ℕ → Fin 3) :
    sourceQuadrantPrimedTime w = quadrantPrimedTime w := by
  funext n
  apply propext
  change (1 ≤ n ∧ ¬ (_ ∧ _)) ↔ (1 ≤ n ∧ ¬ _)
  constructor
  · rintro ⟨hn, hnot⟩
    refine ⟨hn, ?_⟩
    intro hw
    apply hnot
    exact ⟨hw, kmswStage_activeEast_reachable w n hw⟩
  · rintro ⟨hn, hnot⟩
    exact ⟨hn, fun hm => hnot hm.1⟩

/-- Literal source `S_m`, with `S_0 = 0` and positive-time counting as in the
is stated in `sourceQuadrantS_isLeast_count`. -/
@[expose] noncomputable def sourceQuadrantS (w : ℕ → Fin 3)
    (_h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  if m = 0 then 0 else natSelect (sourceQuadrantHatTime w) (m - 1)

/-- Literal source `S'_m`, with `S'_0 = 0` and positive-time counting as in
characterization is stated in `sourceQuadrantS'_isLeast_count`. -/
@[expose] noncomputable def sourceQuadrantS' (w : ℕ → Fin 3)
    (_h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  if m = 0 then 0 else natSelect (sourceQuadrantPrimedTime w) (m - 1)



@[expose] noncomputable def sourceQuadrantHatWalk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.range m,
    (integrateCodes w (sourceQuadrantS w h (j + 1)) -
      integrateCodes w (sourceQuadrantS w h (j + 1) - 1))



@[expose] noncomputable def sourceQuadrantPrimedWalk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.range m,
    (if ∃ k, sourceQuadrantS' w h (j + 1) = walkNL w h k then (0, 1) else
      integrateCodes w (sourceQuadrantS' w h (j + 1)) -
        integrateCodes w (sourceQuadrantS' w h (j + 1) - 1))

private theorem sourceQuadrantS_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : sourceQuadrantS w h = quadrantS w h := by
  funext m
  by_cases hm : m = 0
  · simp [sourceQuadrantS, quadrantS, hm]
  · simp [sourceQuadrantS, quadrantS, hm, sourceQuadrantHatTime_eq]

private theorem sourceQuadrantS'_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : sourceQuadrantS' w h = quadrantS' w h := by
  funext m
  by_cases hm : m = 0
  · simp [sourceQuadrantS', quadrantS', hm]
  · simp [sourceQuadrantS', quadrantS', hm, sourceQuadrantPrimedTime_eq]

/-- For every positive index `m`, `sourceQuadrantS w h m` is the least `n`
whose inclusive positive-time count of `lambda_j ∈ Mhat` for `1 ≤ j ≤ n` is
`Nat.count` on the positive-time source predicate. -/
theorem sourceQuadrantS_isLeast_count (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : 1 ≤ m) :
    IsLeast {n : ℕ | Nat.count
      (sourceQuadrantHatTime w) (n + 1) = m}
      (sourceQuadrantS w h m) := by
  have hchar := quadrantS_characterization w h hm
  constructor
  · change Nat.count (sourceQuadrantHatTime w)
      (sourceQuadrantS w h m + 1) = m
    rw [sourceQuadrantS_eq w h, sourceQuadrantHatTime_eq]
    exact hchar.2.1
  · intro n hn
    change Nat.count (sourceQuadrantHatTime w) (n + 1) = m at hn
    have hn' : Nat.count (quadrantHatTime w) (n + 1) = m := by
      rw [← sourceQuadrantHatTime_eq w]
      exact hn
    rw [sourceQuadrantS_eq w h]
    exact hchar.2.2 n hn'

/-- For every positive index `m`, `sourceQuadrantS' w h m` is the least `n`
whose inclusive positive-time count of `lambda_j ∈ Mhat'` for `1 ≤ j ≤ n`
operative present-edge complement predicate; cut-completed map membership
remains the separate Lemma 5.13 P2 gate. -/
theorem sourceQuadrantS'_isLeast_count (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : 1 ≤ m) :
    IsLeast {n : ℕ | Nat.count
      (sourceQuadrantPrimedTime w) (n + 1) = m}
      (sourceQuadrantS' w h m) := by
  have hchar := quadrantS'_characterization w h hm
  constructor
  · change Nat.count (sourceQuadrantPrimedTime w)
      (sourceQuadrantS' w h m + 1) = m
    rw [sourceQuadrantS'_eq w h, sourceQuadrantPrimedTime_eq]
    exact hchar.2.1
  · intro n hn
    change Nat.count (sourceQuadrantPrimedTime w) (n + 1) = m at hn
    have hn' : Nat.count (quadrantPrimedTime w) (n + 1) = m := by
      rw [← sourceQuadrantPrimedTime_eq w]
      exact hn
    rw [sourceQuadrantS'_eq w h]
    exact hchar.2.2 n hn'

/-- The zero-time source indices of both literal selection sequences are zero -/
theorem sourceQuadrantS_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    sourceQuadrantS w h 0 = 0 := by
  simp [sourceQuadrantS]

 
theorem sourceQuadrantS'_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    sourceQuadrantS' w h 0 = 0 := by
  simp [sourceQuadrantS']

/-- The literal `Mhat`-indexed walk agrees with the selected-time provider
`quadrantHatSourceWalk` by the active-edge membership equivalence -/
theorem sourceQuadrantHatWalk_eq_quadrantHatSourceWalk
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    sourceQuadrantHatWalk w h = quadrantHatSourceWalk w h := by
  funext m
  simp only [sourceQuadrantHatWalk, quadrantHatSourceWalk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceQuadrantS_eq]

/-- The literal `Mhat'`-indexed walk agrees with the selected-time provider
`quadrantPrimedSourceWalk`, preserving the C13 replacement at left exit -/
theorem sourceQuadrantPrimedWalk_eq_quadrantPrimedSourceWalk
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    sourceQuadrantPrimedWalk w h = quadrantPrimedSourceWalk w h := by
  funext m
  simp only [sourceQuadrantPrimedWalk, quadrantPrimedSourceWalk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceQuadrantS'_eq]

/-- Totalized path-valued representative of the literal `Mhat`-indexed walk.
It uses a `HasFlowLineHits` proof when one exists and is the zero path
otherwise; the zero branch is only an internal representative on the null -/
@[expose] noncomputable def sourceQuadrantHatPath (ω : ℕ → Fin 3) :
    ℕ → ℤ × ℤ := by
  classical
  exact if h : HasFlowLineHits (fun i => ω (i + 1)) then
    sourceQuadrantHatWalk (fun i => ω (i + 1)) h else fun _ => 0

/-- The hatted source path starts at `(0,0)` for every code stream -/
theorem sourceQuadrantHatPath_zero (ω : ℕ → Fin 3) :
    sourceQuadrantHatPath ω 0 = (0, 0) := by
  by_cases h : HasFlowLineHits (fun i => ω (i + 1))
  · simp [sourceQuadrantHatPath, h, sourceQuadrantHatWalk]
    rfl
  · simp [sourceQuadrantHatPath, h]
    rfl

/-- Totalized path-valued representative of the literal `Mhat'`-indexed
zero branch is only an internal representative on the null exceptional set; -/
@[expose] noncomputable def sourceQuadrantPrimedPath (ω : ℕ → Fin 3) :
    ℕ → ℤ × ℤ := by
  classical
  exact if h : HasFlowLineHits (fun i => ω (i + 1)) then
    sourceQuadrantPrimedWalk (fun i => ω (i + 1)) h else fun _ => 0



theorem iidCodeMeasure_ae_sourceQuadrantHatPath_eq_quadrantHatWalk :
    sourceQuadrantHatPath =ᵐ[iidCodeMeasure] quadrantHatWalk := by
  filter_upwards [iidCodeMeasure_ae_quadrantSourceWalks_eq_totalWalks]
    with ω hsource
  rcases hsource with ⟨h, hhat, _⟩
  have hdef : sourceQuadrantHatPath ω =
      sourceQuadrantHatWalk (fun i => ω (i + 1)) h := by
    simp [sourceQuadrantHatPath, h]
  exact hdef.trans
    ((sourceQuadrantHatWalk_eq_quadrantHatSourceWalk _ h).trans hhat)

/-- Almost surely, the totalized literal source primed path equals the -/
theorem iidCodeMeasure_ae_sourceQuadrantPrimedPath_eq_quadrantPrimedWalk :
    sourceQuadrantPrimedPath =ᵐ[iidCodeMeasure] quadrantPrimedWalk := by
  filter_upwards [iidCodeMeasure_ae_quadrantSourceWalks_eq_totalWalks]
    with ω hsource
  rcases hsource with ⟨h, _, hprime⟩
  have hdef : sourceQuadrantPrimedPath ω =
      sourceQuadrantPrimedWalk (fun i => ω (i + 1)) h := by
    simp [sourceQuadrantPrimedPath, h]
  exact hdef.trans
    ((sourceQuadrantPrimedWalk_eq_quadrantPrimedSourceWalk _ h).trans hprime)







theorem quadrant_walk_corrected :
    sourceQuadrantHatPath ⟂ᵢ[iidCodeMeasure] sourceQuadrantPrimedPath ∧
    (∀ n, iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) => sourceQuadrantHatPath ω j.val) =
      ((Measure.uniformOfFinset
        (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0)) ∧
    (∀ᵐ ω ∂iidCodeMeasure,
      sourceQuadrantPrimedPath ω 0 = (0, 0) ∧
        sourceQuadrantPrimedPath ω 1 = (0, 1)) ∧
    (∀ n, iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      sourceQuadrantPrimedPath ω (j.val + 1) -
        sourceQuadrantPrimedPath ω 1) =
        ((Measure.uniformOfFinset
          (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0)) ∧
    (AEMeasurable sourceQuadrantHatPath iidCodeMeasure ∧
      AEMeasurable sourceQuadrantPrimedPath iidCodeMeasure) := by
  have hhat := iidCodeMeasure_ae_sourceQuadrantHatPath_eq_quadrantHatWalk
  have hprime := iidCodeMeasure_ae_sourceQuadrantPrimedPath_eq_quadrantPrimedWalk
  rcases DirectedDistances.RandomWalk.quadrant_walk_law_total with
    ⟨hind, hhatLaw, hinitial, hprimeLaw, hmeas⟩
  refine ⟨hind.congr hhat.symm hprime.symm, ?_, ?_, ?_, ?_⟩
  · intro n
    calc
      iidCodeMeasure.map (fun ω =>
          fun j : Fin (n + 1) => sourceQuadrantHatPath ω j.val) =
          iidCodeMeasure.map (fun ω =>
            fun j : Fin (n + 1) => quadrantHatWalk ω j.val) := by
              apply Measure.map_congr
              filter_upwards [hhat] with ω hω
              funext j
              exact congrFun hω j.val
      _ = _ := hhatLaw n
  · filter_upwards [hprime, hinitial] with ω hω hi
    rw [hω]
    exact hi
  · intro n
    calc
      iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
          sourceQuadrantPrimedPath ω (j.val + 1) -
            sourceQuadrantPrimedPath ω 1) =
          iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
            quadrantPrimedWalk ω (j.val + 1) - quadrantPrimedWalk ω 1) := by
              apply Measure.map_congr
              filter_upwards [hprime] with ω hω
              funext j
              rw [hω]
      _ = _ := hprimeLaw n
  · exact ⟨hmeas.1.congr hhat.symm, hmeas.2.congr hprime.symm⟩

end DirectedDistances.PaperProofs.Section5
