module

public import DirectedDistances.KMSW.QuadrantSourceWalks
public import DirectedDistances.KMSW.PrimedQuadrantIntervals
public import DirectedDistances.KMSW.PrimedSimActive
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange
public import DirectedDistances.RandomWalk.QuadrantWalkUncond
import DirectedDistances.KMSW.PrimedLPhaseRecode

/-! # Source-walk increments and quadrant code streams

Walk-level input identification for `lem-quad-kmsw`
`primedCode` stream; for P2, its input is `primedSimInput w`, whose time-zero
letter is `0` and whose letter at time `i+1` is `w i`. positive-time counting convention's positive-time
not a proof of Lemma 5.13. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open MeasureTheory

private theorem integrateCodes_succ_sub (c : ℕ → Fin 3) (m : ℕ) :
    integrateCodes c (m + 1) - integrateCodes c m =
      lazyTwoDimensionalStep (c m) := by
  have hs : integrateCodes c (m + 1) =
      integrateCodes c m + lazyTwoDimensionalStep (c m) := by
    simp [integrateCodes, Finset.sum_range_succ]
  rw [hs]
  abel

private theorem quadrantSplitState_eq_of_succ_eq (ω ω' : ℕ → Fin 3)
    (hω : ∀ i, ω (i + 1) = ω' (i + 1)) (n : ℕ) :
    quadrantSplitState ω n = quadrantSplitState ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1)) =
        quadrantSplitAdvance (quadrantSplitState ω' n) (ω' (n + 1))
      rw [ih, hω n]

private theorem quadrantLCode_eq_of_succ_eq (ω ω' : ℕ → Fin 3)
    (hω : ∀ i, ω (i + 1) = ω' (i + 1)) (k : ℕ) :
    quadrantLCode ω k = quadrantLCode ω' k := by
  classical
  have hP :
      (∃ n, (quadrantSplitState ω n).lCount = k + 1) ↔
        ∃ n, (quadrantSplitState ω' n).lCount = k + 1 := by
    constructor
    · rintro ⟨n, hn⟩
      have hs := quadrantSplitState_eq_of_succ_eq ω ω' hω n
      exact ⟨n, by rw [← hs]; exact hn⟩
    · rintro ⟨n, hn⟩
      have hs := quadrantSplitState_eq_of_succ_eq ω ω' hω n
      exact ⟨n, by rw [hs]; exact hn⟩
  unfold quadrantLCode
  by_cases hl : ∃ n, (quadrantSplitState ω n).lCount = k + 1
  · have hr := hP.mp hl
    simp only [dite_eq_left hl, dite_eq_left hr]
    have hspecL := Nat.find_spec hl
    have hspecR := Nat.find_spec hr
    have hRasL : (quadrantSplitState ω (Nat.find hr)).lCount = k + 1 := by
      have hs := quadrantSplitState_eq_of_succ_eq ω ω' hω (Nat.find hr)
      rw [← hs] at hspecR
      exact hspecR
    have hLasR : (quadrantSplitState ω' (Nat.find hl)).lCount = k + 1 := by
      have hs := quadrantSplitState_eq_of_succ_eq ω ω' hω (Nat.find hl)
      rw [hs] at hspecL
      exact hspecL
    have hLleR : Nat.find hl ≤ Nat.find hr := Nat.find_min' hl hRasL
    have hRleL : Nat.find hr ≤ Nat.find hl := Nat.find_min' hr hLasR
    have hindex : Nat.find hl = Nat.find hr := by omega
    have hpos : 0 < Nat.find hl := by
      by_contra hzero
      have hz : Nat.find hl = 0 := by omega
      rw [hz] at hspecL
      simp [quadrantSplitState, quadrantSplitStart] at hspecL
    calc
      ω (Nat.find hl) = ω (Nat.find hl - 1 + 1) := by congr 1; omega
      _ = ω' (Nat.find hl - 1 + 1) := hω (Nat.find hl - 1)
      _ = ω' (Nat.find hr) := by rw [hindex]; congr 1; omega
  · have hr : ¬ ∃ n, (quadrantSplitState ω' n).lCount = k + 1 :=
      fun hr => hl (hP.mpr hr)
    simp only [dite_eq_right hl, dite_eq_right hr]

private theorem lCode_eq_of_succ_eq (ω ω' : ℕ → Fin 3)
    (hω : ∀ i, ω (i + 1) = ω' (i + 1)) : lCode ω = lCode ω' := by
  funext m
  change quadrantLCode ω m = quadrantLCode ω' m
  exact quadrantLCode_eq_of_succ_eq ω ω' hω m

/-- `primedCode` depends only on the positive-index tail of its input: if
`omega (i+1) = omega' (i+1)` for every `i`, then both the code and the
`HasFlowLineHits` witnesses for those tails determine the same value -/
theorem primedCode_eq_of_succ_eq (ω ω' : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1)))
    (h' : HasFlowLineHits (fun i => ω' (i + 1)))
    (hω : ∀ i, ω (i + 1) = ω' (i + 1)) (m : ℕ) :
    primedCode ω h m = primedCode ω' h' m := by
  rw [primedCode_eq_lExcursionShift ω h m,
    primedCode_eq_lExcursionShift ω' h' m]
  rw [lCode_eq_of_succ_eq ω ω' hω]

/-- The source-indexed hatted path is the integral of its raw `hatCodes`
stream, for arbitrary source codes `w` (the harmless time-zero letter is
inserted by `primedSimInput`). This identifies the walk increments in
count reading is used by `quadrantS` and `quadrantS'` in
`DirectedDistances/KMSW/QuadrantSourceWalks.lean`. -/
theorem quadrantHatSourceWalk_eq_integrateCodes_hatCodes
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    quadrantHatSourceWalk w h = integrateCodes (hatCodes w h) := by
  have hh : HasFlowLineHits (fun i => primedSimInput w (i + 1)) := by
    simpa [primedSimInput] using h
  simpa [primedSimInput, quadrantHatIntervalWalk] using
    (quadrantHatSourceWalk_eq_quadrantHatIntervalWalk (primedSimInput w) hh)

/-- At each index `m`, the hatted source-walk increment is exactly the
`m`th `hatCodes` step. Thus `hatCodes w h` is the raw `Mhat` increment stream
in the walk-level input of `lem-quad-kmsw` -/
theorem quadrantHatSourceWalk_increment
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    quadrantHatSourceWalk w h (m + 1) - quadrantHatSourceWalk w h m =
      lazyTwoDimensionalStep (hatCodes w h m) := by
  have hp := congrFun (quadrantHatSourceWalk_eq_integrateCodes_hatCodes w h) (m + 1)
  have hq := congrFun (quadrantHatSourceWalk_eq_integrateCodes_hatCodes w h) m
  rw [hp, hq]
  exact integrateCodes_succ_sub (hatCodes w h) m

/-- Each hatted source-walk increment determines a unique code in `Fin 3`; -/
theorem quadrantHatSourceWalk_increment_unique
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    ∃! c : Fin 3,
      quadrantHatSourceWalk w h (m + 1) - quadrantHatSourceWalk w h m =
        lazyTwoDimensionalStep c := by
  refine ⟨hatCodes w h m, quadrantHatSourceWalk_increment w h m, ?_⟩
  intro c hc
  apply lazyTwoDimensionalStep_injective
  exact hc.symm.trans (quadrantHatSourceWalk_increment w h m)

/-- In the manuscript indexing, the primed source walk's `m`th increment is
the step of `primedCode ω h m`, where the source code at time `i` is
`ω (i+1)`. This uses the C13 replacement at the first time of every L-phase -/
theorem quadrantPrimedSourceWalk_increment
    (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    quadrantPrimedSourceWalk (fun i => ω (i + 1)) h (m + 1) -
        quadrantPrimedSourceWalk (fun i => ω (i + 1)) h m =
      lazyTwoDimensionalStep (primedCode ω h m) := by
  have hp := congrFun (quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk ω h) (m + 1)
  have hq := congrFun (quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk ω h) m
  rw [hp, hq]
  exact integrateCodes_succ_sub (primedCode ω h) m

/-- The P2 primed simulation uses `primedCode (primedSimInput w) h m` at
zero-based code index `m`: `primedSimInput w 0 = 0` and
`primedSimInput w (i+1) = w i`. Its steps are exactly the increments of the -/
theorem quadrantPrimedSourceWalk_increment_simInput
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    quadrantPrimedSourceWalk w h (m + 1) - quadrantPrimedSourceWalk w h m =
      lazyTwoDimensionalStep (primedCode (primedSimInput w) h m) := by
  have hh : HasFlowLineHits (fun i => primedSimInput w (i + 1)) := by
    simpa [primedSimInput] using h
  simpa [primedSimInput] using
    quadrantPrimedSourceWalk_increment (primedSimInput w) hh m

/-- The P2 primed code begins with code `1`, hence with the C13 step -/
theorem primedSimInput_code_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedCode (primedSimInput w) h 0 = 1 := by
  have hh : HasFlowLineHits (fun i => primedSimInput w (i + 1)) := by
    simpa [primedSimInput] using h
  exact primedCode_zero (primedSimInput w) hh

/-- The first primed source-walk increment is the C13 replacement step -/
theorem quadrantPrimedSourceWalk_first_increment
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    quadrantPrimedSourceWalk w h 1 - quadrantPrimedSourceWalk w h 0 = (0, 1) := by
  rw [quadrantPrimedSourceWalk_increment_simInput w h 0, primedSimInput_code_zero w h]
  rfl

/-- Almost surely, a flow-line-hit witness makes both source walks' increments
the steps of the precise interval-code streams: `hatCodes` on the shifted
input and `primedCode ω h` on the primed input. The source count convention -/
theorem iidCodeMeasure_ae_quadrantSourceWalk_increments :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        (∀ m, quadrantHatSourceWalk (fun i => ω (i + 1)) h (m + 1) -
            quadrantHatSourceWalk (fun i => ω (i + 1)) h m =
          lazyTwoDimensionalStep (hatCodes (fun i => ω (i + 1)) h m)) ∧
        (∀ m, quadrantPrimedSourceWalk (fun i => ω (i + 1)) h (m + 1) -
            quadrantPrimedSourceWalk (fun i => ω (i + 1)) h m =
          lazyTwoDimensionalStep (primedCode ω h m)) := by
  filter_upwards [DirectedDistances.RandomWalk.iidCodeMeasure_ae_hasFlowLineHits]
    with ω h
  exact ⟨h, fun m => quadrantHatSourceWalk_increment _ h m,
    fun m => quadrantPrimedSourceWalk_increment ω h m⟩

/-- Almost surely, the primed source-walk increments also have the canonical
P2 input form `primedCode (primedSimInput (fun i => ω (i+1)))`. This follows
from the position-zero independence of `primedCode`; it identifies the
indexing used by the P2 simulation without asserting Lemma 5.13 -/
theorem iidCodeMeasure_ae_quadrantSourceWalk_primedSimInput_increments :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        ∀ m, quadrantPrimedSourceWalk (fun i => ω (i + 1)) h (m + 1) -
            quadrantPrimedSourceWalk (fun i => ω (i + 1)) h m =
          lazyTwoDimensionalStep
            (primedCode (primedSimInput (fun i => ω (i + 1))) h m) := by
  filter_upwards [iidCodeMeasure_ae_quadrantSourceWalk_increments]
    with ω hsource
  rcases hsource with ⟨h, _, hprime⟩
  refine ⟨h, ?_⟩
  intro m
  rw [← primedCode_eq_of_succ_eq ω
    (primedSimInput (fun i => ω (i + 1))) h h
    (by intro i; simp [primedSimInput]) m]
  exact hprime m

end DirectedDistances.KMSW
