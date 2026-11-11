/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantWalkLaw
public import DirectedDistances.RandomWalk.QuadrantWalkTotal
public import DirectedDistances.KMSW.FlowLineTimesIff
public import DirectedDistances.KMSW.PrimedQuadrantIntervals
public import DirectedDistances.KMSW.InfiniteBoundary
import DirectedDistances.RandomWalk.QuadrantWalkUncond








public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open Quiver
open scoped Classical BigOperators

/-- Positive times whose active west vertex is reachable from the root; this -/
@[expose] def quadrantHatTime (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  1 ≤ n ∧ Reachable (⟨0⟩ : PresentVertex w)
    ⟨(kmswStage w n).west (act w n)⟩

/-- Positive times whose active west vertex is not reachable from the root; -/
@[expose] def quadrantPrimedTime (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  1 ≤ n ∧ ¬ Reachable (⟨0⟩ : PresentVertex w)
    ⟨(kmswStage w n).west (act w n)⟩

private theorem walkNR_strictMono_local (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : StrictMono (walkNR w h) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hL := (walkNL_spec w h k).1
  have hR := (walkNR_succ_spec w h k).1
  omega

private theorem walkNL_strictMono_local (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : StrictMono (walkNL w h) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hR := (walkNR_succ_spec w h k).1
  have hL := (walkNL_spec w h (k + 1)).1
  omega

private theorem walkNR_succ_injective (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Function.Injective (fun k => walkNR w h (k + 1)) := by
  intro k l heq
  have hkl := (walkNR_strictMono_local w h).injective heq
  omega

/-- Both source time sets are infinite under `HasFlowLineHits`. Reachable
times contain every `walkNR (k+1)`; nonreachable times contain every
`walkNL k`. These are the two interval families in `eqn-quad-pre` -/
theorem quadrantTimeSets_infinite (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (Set.ofPred (quadrantHatTime w)).Infinite ∧
      (Set.ofPred (quadrantPrimedTime w)).Infinite := by
  constructor
  · apply Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (walkNR_succ_injective w h))
    rintro n ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · have hk := (walkNR_succ_spec w h k).1
      exact Nat.le_trans (by omega) hk
    · apply (flowLineTimes_iff w h (walkNR w h (k + 1))).2
      refine ⟨k + 1, le_rfl, ?_⟩
      have hL := (walkNL_spec w h (k + 1)).1
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hL
  · apply Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (walkNL_strictMono_local w h).injective)
    rintro n ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · have hk := (walkNL_spec w h k).1
      omega
    · intro hr
      obtain ⟨q, hq₀, hq₁⟩ := (flowLineTimes_iff w h (walkNL w h k)).1 hr
      by_cases hq : q ≤ k
      · have hmono := (walkNL_strictMono_local w h).monotone hq
        omega
      · have hlt : k < q := Nat.lt_of_not_ge hq
        have hmono := (walkNR_strictMono_local w h).monotone (Nat.succ_le_of_lt hlt)
        have hspec := (walkNR_succ_spec w h k).1
        have hgap : walkNL w h k < walkNR w h (k + 1) := by omega
        have hmono' : walkNR w h (k + 1) ≤ walkNR w h q := by simpa using hmono
        omega

/-- The `m`th positive source time, with source indexing `S_0 = 0` and
`S_m` the `(m-1)`st zero-indexed element selected by the project's count-based
`natSelect` (the cache does not build `Mathlib.Data.Nat.Nth`). This follows the -/
@[expose] noncomputable def quadrantS (w : ℕ → Fin 3)
    (_h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  if m = 0 then 0 else natSelect (quadrantHatTime w) (m - 1)

/-- The `m`th positive complementary source time, with `S'_0 = 0`; positive-time counting convention is -/
@[expose] noncomputable def quadrantS' (w : ℕ → Fin 3)
    (_h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  if m = 0 then 0 else natSelect (quadrantPrimedTime w) (m - 1)

/-- Exact least-time characterization of `S_m`: the count over `1 ≤ j ≤ n` -/
theorem quadrantS_characterization (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : 1 ≤ m) :
    quadrantHatTime w (quadrantS w h m) ∧
      Nat.count (quadrantHatTime w) (quadrantS w h m + 1) = m ∧
      ∀ n, Nat.count (quadrantHatTime w) (n + 1) = m →
        quadrantS w h m ≤ n := by
  have hinf := (quadrantTimeSets_infinite w h).1
  have hspec := natSelect_spec hinf (m - 1)
  have hmzero : m ≠ 0 := by omega
  constructor
  · simpa [quadrantS, hmzero]
      using hspec.1
  constructor
  · have hc : Nat.count (quadrantHatTime w)
        (natSelect (quadrantHatTime w) (m - 1) + 1) = m := by
      rw [Nat.count_succ, hspec.2]
      simp [hspec.1]
      omega
    simpa [quadrantS, hmzero] using hc
  · intro n hn
    have hlt : m - 1 < Nat.count (quadrantHatTime w) (n + 1) := by
      rw [hn]
      omega
    have hsel : natSelect (quadrantHatTime w) (m - 1) ≤ n := by
      unfold natSelect
      rw [dif_pos (⟨n, hlt⟩ : ∃ k, m - 1 <
        Nat.count (quadrantHatTime w) (k + 1))]
      exact Nat.find_min' _ hlt
    simpa [quadrantS, hmzero] using hsel

/-- Exact least-time characterization of `S'_m`, with counts restricted to -/
theorem quadrantS'_characterization (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : 1 ≤ m) :
    quadrantPrimedTime w (quadrantS' w h m) ∧
      Nat.count (quadrantPrimedTime w) (quadrantS' w h m + 1) = m ∧
      ∀ n, Nat.count (quadrantPrimedTime w) (n + 1) = m →
        quadrantS' w h m ≤ n := by
  have hinf := (quadrantTimeSets_infinite w h).2
  have hspec := natSelect_spec hinf (m - 1)
  have hmzero : m ≠ 0 := by omega
  constructor
  · simpa [quadrantS', hmzero]
      using hspec.1
  constructor
  · have hc : Nat.count (quadrantPrimedTime w)
        (natSelect (quadrantPrimedTime w) (m - 1) + 1) = m := by
      rw [Nat.count_succ, hspec.2]
      simp [hspec.1]
      omega
    simpa [quadrantS', hmzero] using hc
  · intro n hn
    have hlt : m - 1 < Nat.count (quadrantPrimedTime w) (n + 1) := by
      rw [hn]
      omega
    have hsel : natSelect (quadrantPrimedTime w) (m - 1) ≤ n := by
      unfold natSelect
      rw [dif_pos (⟨n, hlt⟩ : ∃ k, m - 1 <
        Nat.count (quadrantPrimedTime w) (k + 1))]
      exact Nat.find_min' _ hlt
    simpa [quadrantS', hmzero] using hsel

/-- The hatted source walk formed by summing the increments at the selected
positive reachable times (`eqn-walk-quadrant`, -/
@[expose] noncomputable def quadrantHatSourceWalk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.range m,
    (integrateCodes w (quadrantS w h (j + 1)) -
      integrateCodes w (quadrantS w h (j + 1) - 1))




@[expose] noncomputable def quadrantPrimedSourceWalk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.range m,
    (if ∃ k, quadrantS' w h (j + 1) = walkNL w h k then (0, 1) else
      integrateCodes w (quadrantS' w h (j + 1)) -
        integrateCodes w (quadrantS' w h (j + 1) - 1))

private theorem quadrantHatTime_iff_rPhase (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    quadrantHatTime w n ↔ 1 ≤ n ∧
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  constructor
  · rintro ⟨hn, hr⟩
    have htimes := (flowLineTimes_iff w h n).1 hr
    refine ⟨hn, ?_⟩
    exact (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w)
      hω n).2 (by simpa [quadrantTrajectoryOfStageCodes] using htimes)
  · rintro ⟨hn, hp⟩
    refine ⟨hn, ?_⟩
    apply (flowLineTimes_iff w h n).2
    exact (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w)
      hω n).1 hp

private theorem quadrantPrimedTime_iff_lPhase (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    quadrantPrimedTime w n ↔ 1 ≤ n ∧
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .l := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  constructor
  · rintro ⟨hn, hnr⟩
    have hphase : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase ≠ .r := by
      intro hp
      apply hnr
      apply (flowLineTimes_iff w h n).2
      exact (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w)
        hω n).1 hp
    cases hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase with
    | r => exact (hphase hp).elim
    | l => exact ⟨hn, rfl⟩
  · rintro ⟨hn, hp⟩
    refine ⟨hn, ?_⟩
    intro hr
    have hphase := (quadrantSplitState_rPhase_iff
      (quadrantTrajectoryOfStageCodes w) hω n).2
      ((flowLineTimes_iff w h n).1 hr)
    rw [hp] at hphase
    cases hphase

private theorem quadrantHatCount_rCount (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    Nat.count (quadrantHatTime w) (n + 1) + 1 =
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount +
        (if (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r
          then 1 else 0) := by
  induction n with
  | zero =>
      simp [Nat.count_succ, quadrantHatTime, quadrantSplitState, quadrantSplitStart]
  | succ n ih =>
      have hupdate :
          (quadrantSplitState (quadrantTrajectoryOfStageCodes w) (n + 1)).rCount =
            (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount +
              (if (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r
                then 1 else 0) := by
        rw [quadrantSplitState, quadrantSplitAdvance_rCount]
        by_cases hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r
        · simp [hp]
        · simp [hp]
      rw [Nat.count_succ, hupdate]
      by_cases hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (n + 1)).phase = .r
      · have htime : quadrantHatTime w (n + 1) := by
          exact (quadrantHatTime_iff_rPhase w h (n + 1)).2 ⟨by omega, hp⟩
        simp [htime, hp]
        omega
      · have htime : ¬ quadrantHatTime w (n + 1) := by
          intro ht
          exact hp ((quadrantHatTime_iff_rPhase w h (n + 1)).1 ht).2
        simp [htime, hp]
        omega

private theorem quadrantPrimedCount_lCount (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    Nat.count (quadrantPrimedTime w) (n + 1) =
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).lCount +
        (if (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .l
          then 1 else 0) := by
  induction n with
  | zero =>
      simp [Nat.count_succ, quadrantPrimedTime, quadrantSplitState,
        quadrantSplitStart]
  | succ n ih =>
      have hupdate :
          (quadrantSplitState (quadrantTrajectoryOfStageCodes w) (n + 1)).lCount =
            (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).lCount +
              (if (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .l
                then 1 else 0) := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        by_cases hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .l
        · simp [hp]
        · simp [hp]
      rw [Nat.count_succ, hupdate]
      by_cases hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (n + 1)).phase = .l
      · have htime : quadrantPrimedTime w (n + 1) := by
          exact (quadrantPrimedTime_iff_lPhase w h (n + 1)).2 ⟨by omega, hp⟩
        simp [htime, hp]
        omega
      · have htime : ¬ quadrantPrimedTime w (n + 1) := by
          intro ht
          exact hp ((quadrantPrimedTime_iff_lPhase w h (n + 1)).1 ht).2
        simp [htime, hp]
        omega

/-- The positive reachable-time enumeration is the splitter's canonical
R-phase enumeration: `S_m` is `quadrantRStageTime m` for `m ≥ 1`. The index
shift in the source walk is then exactly `S_m - 1 = hatCodeTime (m-1)` -/
theorem quadrantS_eq_quadrantRStageTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : 1 ≤ m) :
    quadrantS w h m = quadrantRStageTime w h m := by
  have hchar := quadrantS_characterization w h hm
  have hphaseS := (quadrantHatTime_iff_rPhase w h _).1 hchar.1 |>.2
  have hcounterS :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (quadrantS w h m)).rCount = m := by
    have hc := quadrantHatCount_rCount w h (quadrantS w h m)
    rw [hchar.2.1] at hc
    simp [hphaseS] at hc
    omega
  have hs := quadrantRStageTime_spec w h m
  exact quadrantRStageCodes_RPhaseTime_unique w m
    (quadrantS w h m) (quadrantRStageTime w h m)
    hphaseS hcounterS hs.1 hs.2.1

private theorem lPhaseTime_unique_local (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n m : ℕ)
    (hp : (quadrantSplitState ω n).phase = .l)
    (hc : (quadrantSplitState ω n).lCount = m) :
    n = lPhaseTime ω h m := by
  let t := lPhaseTime ω h m
  have htphase : (quadrantSplitState ω t).phase = .l := lPhaseTime_phase ω h m
  have htcount : (quadrantSplitState ω t).lCount = m := lPhaseTime_lCount ω h m
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnt | htn
  · have hstep : (quadrantSplitState ω (n + 1)).lCount = m + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_lCount]
      simp [hp, hc]
    have hmono := quadrantSplitState_lCount_mono ω (n + 1) t (by omega)
    rw [hstep, htcount] at hmono
    omega
  · have hstep : (quadrantSplitState ω (t + 1)).lCount = m + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_lCount]
      simp [htphase, htcount]
    have hmono := quadrantSplitState_lCount_mono ω (t + 1) n (by omega)
    rw [hstep, hc] at hmono
    omega

/-- The positive complementary-time enumeration is the splitter's canonical
L-phase enumeration: `S'_m` is the state time with L counter `m-1` for -/
theorem quadrantS'_eq_lPhaseTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : 1 ≤ m) :
    quadrantS' w h m =
      lPhaseTime (quadrantTrajectoryOfStageCodes w)
        (by simpa [quadrantTrajectoryOfStageCodes] using h) (m - 1) := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  have hchar := quadrantS'_characterization w h hm
  have hphaseS := (quadrantPrimedTime_iff_lPhase w h _).1 hchar.1 |>.2
  have hcounterS :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (quadrantS' w h m)).lCount = m - 1 := by
    have hc := quadrantPrimedCount_lCount w h (quadrantS' w h m)
    rw [hchar.2.1] at hc
    simp [hphaseS] at hc
    omega
  exact lPhaseTime_unique_local (quadrantTrajectoryOfStageCodes w) hω
    (quadrantS' w h m) (m - 1) hphaseS hcounterS

private theorem integrateCodes_increment (w : ℕ → Fin 3) {n : ℕ}
    (hn : 1 ≤ n) :
    integrateCodes w n - integrateCodes w (n - 1) =
      lazyTwoDimensionalStep (w (n - 1)) := by
  have hidx : n - 1 + 1 = n := by omega
  have hsum : integrateCodes w (n - 1 + 1) =
      integrateCodes w (n - 1) + lazyTwoDimensionalStep (w (n - 1)) := by
    simp [integrateCodes, Finset.sum_range_succ]
  rw [← hidx, hsum]
  have hidx' : n - 1 + 1 - 1 = n - 1 := by omega
  rw [hidx']
  abel

/-- For the code stream `w i = ω (i+1)`, the source-defined hatted walk is
the existing `hatCodes` interval walk. The proof uses `S_m-1 = hatCodeTime` -/
theorem quadrantHatSourceWalk_eq_quadrantHatIntervalWalk (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantHatSourceWalk (fun i => ω (i + 1)) h =
      quadrantHatIntervalWalk ω h := by
  funext m
  change (∑ j ∈ Finset.range m,
      (integrateCodes (fun i => ω (i + 1))
          (quadrantS (fun i => ω (i + 1)) h (j + 1)) -
        integrateCodes (fun i => ω (i + 1))
          (quadrantS (fun i => ω (i + 1)) h (j + 1) - 1))) =
    ∑ j ∈ Finset.range m,
      lazyTwoDimensionalStep
        (hatCodes (fun i => ω (i + 1)) h j)
  apply Finset.sum_congr rfl
  intro j hj
  have htime := quadrantS_eq_quadrantRStageTime (fun i => ω (i + 1)) h
    (m := j + 1) (by omega)
  have htc := hatCodeTime_succ (fun i => ω (i + 1)) h j
  have hpos : 1 ≤ quadrantS (fun i => ω (i + 1)) h (j + 1) := by
    exact (quadrantS_characterization (fun i => ω (i + 1)) h (by omega)).1.1
  have hcodeTime :
      quadrantS (fun i => ω (i + 1)) h (j + 1) - 1 =
        hatCodeTime (fun i => ω (i + 1)) h j := by
    rw [htime]
    omega
  rw [integrateCodes_increment _ hpos, hcodeTime, hatCodes]

private theorem lCount_constant_on_rightInterval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNR (fun i => ω (i + 1)) h k + d ≤
      walkNL (fun i => ω (i + 1)) h k) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).lCount := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNR (fun i => ω (i + 1)) h k + d ≤
          walkNL (fun i => ω (i + 1)) h k := by omega
      have hp : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d)).phase = .r := by
        apply (quadrantSplitState_rPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNR (fun i => ω (i + 1)) h k + d)).lCount := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNR (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNR (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']

private theorem lCount_add_on_leftInterval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNL (fun i => ω (i + 1)) h k + d ≤
      walkNR (fun i => ω (i + 1)) h (k + 1)) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lCount + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNL (fun i => ω (i + 1)) h k + d ≤
          walkNR (fun i => ω (i + 1)) h (k + 1) := by omega
      have hp : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNL (fun i => ω (i + 1)) h k + d)).lCount + 1 := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNL (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNL (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']
      omega

private theorem lCount_at_primedIntervalLeft (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (primedIntervalLeft ω h k)).lCount =
      primedIntervalBase ω h k := by
  induction k with
  | zero =>
      have hzero : walkNR (fun i => ω (i + 1)) h 0 = 0 := walkNR_zero _ _
      have hconst := lCount_constant_on_rightInterval ω h 0
        (walkNL (fun i => ω (i + 1)) h 0) (by rw [hzero]; omega)
      simpa [primedIntervalLeft, primedIntervalBase, hzero,
        quadrantSplitState, quadrantSplitStart] using hconst
  | succ k ih =>
      let tL := walkNL (fun i => ω (i + 1)) h k
      let tR := walkNR (fun i => ω (i + 1)) h (k + 1)
      let tNext := walkNL (fun i => ω (i + 1)) h (k + 1)
      have hL := lCount_add_on_leftInterval ω h k (tR - tL) (by
        have hs := walkNR_succ_spec (fun i => ω (i + 1)) h k
        dsimp [tL, tR]
        omega)
      have hR := lCount_constant_on_rightInterval ω h (k + 1) (tNext - tR) (by
        have hs := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
        dsimp [tNext, tR]
        omega)
      have hidxR : tL + (tR - tL) = tR := by
        have hs := (walkNR_succ_spec (fun i => ω (i + 1)) h k).1
        dsimp [tL, tR]
        omega
      have hidxN : tR + (tNext - tR) = tNext := by
        have hs := (walkNL_spec (fun i => ω (i + 1)) h (k + 1)).1
        dsimp [tNext, tR]
        omega
      have hcount :
          (quadrantSplitState ω tNext).lCount =
            (quadrantSplitState ω tL).lCount + (tR - tL) := by
        calc
          (quadrantSplitState ω tNext).lCount =
              (quadrantSplitState ω (tR + (tNext - tR))).lCount := by rw [hidxN]
          _ = (quadrantSplitState ω tR).lCount := hR
          _ = (quadrantSplitState ω (tL + (tR - tL))).lCount := by rw [hidxR]
          _ = (quadrantSplitState ω tL).lCount + (tR - tL) := hL
      change (quadrantSplitState ω tNext).lCount = primedIntervalBase ω h (k + 1)
      rw [primedIntervalBase_succ, ← ih]
      change (quadrantSplitState ω tNext).lCount =
        (quadrantSplitState ω tL).lCount + (tR - tL)
      exact hcount

private theorem lPhaseTime_eq_primedIntervalTime_local (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : j < primedIntervalWidth ω h k) :
    lPhaseTime ω h (primedIntervalBase ω h k + j) =
      primedIntervalLeft ω h k + j := by
  let t := primedIntervalLeft ω h k + j
  have hright : t < primedIntervalRight ω h k := by
    dsimp [t, primedIntervalRight, primedIntervalWidth,
      primedIntervalLeft] at hj ⊢
    omega
  have hleft : primedIntervalLeft ω h k ≤ t := by
    dsimp [t]
    omega
  have hphase : (quadrantSplitState ω t).phase = .l := by
    apply (quadrantSplitState_lPhase_iff ω h t).2
    exact ⟨k, hleft, by simpa [primedIntervalRight] using hright⟩
  have hbound : primedIntervalLeft ω h k + j ≤ primedIntervalRight ω h k := by
    dsimp [t] at hright
    omega
  have hcountStep := lCount_add_on_leftInterval ω h k j (by
    simpa [primedIntervalLeft, primedIntervalRight] using hbound)
  have hcount : (quadrantSplitState ω t).lCount =
      primedIntervalBase ω h k + j := by
    calc
      (quadrantSplitState ω t).lCount =
          (quadrantSplitState ω (primedIntervalLeft ω h k)).lCount + j := by
            simpa [t, primedIntervalLeft] using hcountStep
      _ = primedIntervalBase ω h k + j := by
            rw [lCount_at_primedIntervalLeft]
  exact (lPhaseTime_unique_local ω h t
    (primedIntervalBase ω h k + j) hphase hcount).symm

private theorem primedIntervalIndex_offset_bound (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    primedIntervalBase ω h (primedIntervalIndex ω h m) ≤ m ∧
      m - primedIntervalBase ω h (primedIntervalIndex ω h m) <
        primedIntervalWidth ω h (primedIntervalIndex ω h m) := by
  let k := primedIntervalIndex ω h m
  have hspec := primedIntervalIndex_spec ω h m
  have hbase : primedIntervalBase ω h k ≤ m := by
    by_cases hk : k = 0
    · simp [k, hk, primedIntervalBase_zero]
    · have hkpos : 1 ≤ k := by omega
      have hmin : ¬ m < primedIntervalBase ω h k := by
        have hfindPos : 1 ≤ Nat.find (primedIntervalIndex_exists ω h m) := by
          change 1 ≤ k
          exact hkpos
        have hfind := Nat.find_min (primedIntervalIndex_exists ω h m)
          (show Nat.find (primedIntervalIndex_exists ω h m) - 1 <
              Nat.find (primedIntervalIndex_exists ω h m) by omega)
        have hfind' : ¬ m < primedIntervalBase ω h
            (Nat.find (primedIntervalIndex_exists ω h m)) := by
          simpa only [Nat.sub_add_cancel hfindPos] using hfind
        simpa [k, primedIntervalIndex] using hfind'
      omega
  have hupper : m < primedIntervalBase ω h (k + 1) := by
    simpa [k, primedIntervalIndex] using hspec
  constructor
  · exact hbase
  · have hbase' : primedIntervalBase ω h (primedIntervalIndex ω h m) ≤ m := by
      simpa [k] using hbase
    have hupper' := primedIntervalIndex_spec ω h m
    rw [primedIntervalBase_succ] at hupper'
    omega

private theorem quadrantPrimedSourceStep_eq_codeStep (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    (if ∃ k, quadrantS' (fun i => ω (i + 1)) h (m + 1) =
        walkNL (fun i => ω (i + 1)) h k then (0, 1) else
      integrateCodes (fun i => ω (i + 1))
          (quadrantS' (fun i => ω (i + 1)) h (m + 1)) -
        integrateCodes (fun i => ω (i + 1))
          (quadrantS' (fun i => ω (i + 1)) h (m + 1) - 1)) =
      lazyTwoDimensionalStep (primedCode ω h m) := by
  classical
  let w := fun i => ω (i + 1)
  let τ := quadrantTrajectoryOfStageCodes w
  have hτ : HasFlowLineHits (fun i => τ (i + 1)) := by
    simpa [τ, quadrantTrajectoryOfStageCodes, w] using h
  let k := primedIntervalIndex ω h m
  let d := m - primedIntervalBase ω h k
  have hoff := primedIntervalIndex_offset_bound ω h m
  have hbase : primedIntervalBase ω h k ≤ m := hoff.1
  have hdwidth : d < primedIntervalWidth ω h k := by
    simpa [d, k] using hoff.2
  have hdecomp : primedIntervalBase ω h k + d = m := by
    dsimp [d]
    exact Nat.add_sub_of_le hbase
  have htimeIndex := quadrantS'_eq_lPhaseTime w h (m := m + 1) (by omega)
  have hselected : quadrantS' w h (m + 1) =
      primedIntervalLeft ω h k + d := by
    have hphaseTime : quadrantS' w h (m + 1) = lPhaseTime τ hτ m := by
      simpa [w, τ] using htimeIndex
    have hinterval := lPhaseTime_eq_primedIntervalTime_local τ hτ k d hdwidth
    have hbaseτ : primedIntervalBase τ hτ k = primedIntervalBase ω h k := by
      rfl
    have hindex : primedIntervalBase τ hτ k + d = m := by
      rw [hbaseτ]
      exact hdecomp
    rw [hindex] at hinterval
    have hinterval' : lPhaseTime τ hτ m = primedIntervalLeft ω h k + d := by
      simpa [w, τ, primedIntervalLeft, quadrantTrajectoryOfStageCodes] using
        hinterval
    exact hphaseTime.trans hinterval'
  have hreplacement :
      (∃ q, quadrantS' w h (m + 1) = walkNL w h q) ↔ d = 0 := by
    constructor
    · rintro ⟨q, hq⟩
      by_contra hd0
      have hdp : 0 < d := Nat.pos_of_ne_zero hd0
      have hqt : walkNL w h q = walkNL w h k + d := by
        simpa [primedIntervalLeft, w] using hq.symm.trans hselected
      by_cases hqk : q ≤ k
      · have hmono := (walkNL_strictMono_local w h).monotone hqk
        rw [hqt] at hmono
        omega
      · have hkq' : k + 1 ≤ q := by omega
        have hmono := (walkNL_strictMono_local w h).monotone hkq'
        have hright := (walkNR_succ_spec w h k).1
        have hwidth : d < walkNR w h (k + 1) - walkNL w h k := by
          simpa [primedIntervalWidth, primedIntervalRight,
            primedIntervalLeft, w] using hdwidth
        have hltR : walkNL w h k + d < walkNR w h (k + 1) := by omega
        have hnext := (walkNL_spec w h (k + 1)).1
        have hltNext : walkNL w h k + d < walkNL w h (k + 1) := by omega
        rw [hqt] at hmono
        omega
    · intro hd0
      refine ⟨k, ?_⟩
      rw [hselected]
      simpa [primedIntervalLeft, w, hd0]
  have hpositive : 1 ≤ quadrantS' w h (m + 1) :=
    (quadrantS'_characterization w h (m := m + 1) (by omega)).1.1
  change (if ∃ q, quadrantS' w h (m + 1) = walkNL w h q then (0, 1) else
      integrateCodes w (quadrantS' w h (m + 1)) -
        integrateCodes w (quadrantS' w h (m + 1) - 1)) =
    lazyTwoDimensionalStep (primedCode ω h m)
  by_cases hd0 : d = 0
  · have hrep := hreplacement.mpr hd0
    rw [if_pos hrep, ← hdecomp, primedCode_block ω h k d hdwidth]
    simp [hd0]
  · have hnot : ¬ ∃ q, quadrantS' w h (m + 1) = walkNL w h q := by
      intro hrep
      exact hd0 (hreplacement.mp hrep)
    rw [if_neg hnot, integrateCodes_increment w hpositive, hselected,
      ← hdecomp, primedCode_block ω h k d hdwidth]
    simp [w, hd0]



theorem quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk
    (ω : ℕ → Fin 3) (h : HasFlowLineHits (fun i => ω (i + 1))) :
    quadrantPrimedSourceWalk (fun i => ω (i + 1)) h =
      quadrantPrimedIntervalWalk ω h := by
  funext m
  change (∑ j ∈ Finset.range m,
      (if ∃ k, quadrantS' (fun i => ω (i + 1)) h (j + 1) =
          walkNL (fun i => ω (i + 1)) h k then (0, 1) else
        integrateCodes (fun i => ω (i + 1))
            (quadrantS' (fun i => ω (i + 1)) h (j + 1)) -
          integrateCodes (fun i => ω (i + 1))
            (quadrantS' (fun i => ω (i + 1)) h (j + 1) - 1))) =
    ∑ j ∈ Finset.range m, lazyTwoDimensionalStep (primedCode ω h j)
  apply Finset.sum_congr rfl
  intro j hj
  exact quadrantPrimedSourceStep_eq_codeStep ω h j

/-- Almost surely, for a flow-line-hit witness, the source primed path under -/
theorem iidCodeMeasure_ae_quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        quadrantPrimedSourceWalk (fun i => ω (i + 1)) h =
          quadrantPrimedIntervalWalk ω h := by
  filter_upwards [DirectedDistances.RandomWalk.iidCodeMeasure_ae_hasFlowLineHits]
    with ω h
  exact ⟨h, quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk ω h⟩

/-- Almost surely both positive-time counting convention source walks equal the totalized interval walks
used by the unconditional law provider; the source count reading remains -/
theorem iidCodeMeasure_ae_quadrantSourceWalks_eq_totalWalks :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        quadrantHatSourceWalk (fun i => ω (i + 1)) h =
            DirectedDistances.RandomWalk.quadrantHatWalk ω ∧
          quadrantPrimedSourceWalk (fun i => ω (i + 1)) h =
            DirectedDistances.RandomWalk.quadrantPrimedWalk ω := by
  filter_upwards [DirectedDistances.RandomWalk.iidCodeMeasure_ae_hasFlowLineHits]
    with ω h
  refine ⟨h, ?_, ?_⟩
  · exact (quadrantHatSourceWalk_eq_quadrantHatIntervalWalk ω h).trans
      (DirectedDistances.RandomWalk.quadrantHatWalk_eq_interval ω h).symm
  · exact (quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk ω h).trans
      (DirectedDistances.RandomWalk.quadrantPrimedWalk_eq_interval ω h).symm

end DirectedDistances.KMSW
