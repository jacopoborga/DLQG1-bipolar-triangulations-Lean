/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageStackInvariantUR
public import DirectedDistances.KMSW.StoppedLeftBoundaryMarkAE
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLaw
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperHatGeometry
public import DirectedDistances.PaperProofs.Section7.StoppedRightBoundarySDPTransfer























































public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped geometry); not a paper result.
Before a first hit, a code walk with downward steps at least `-1` stays above
the hit level. -/
private theorem codeWalk_strictly_above_before_first_hit
    (p : ℕ → ℤ) (r : ℕ) (hr : 1 ≤ r) (hp0 : p 0 = 0)
    (hstep : ∀ n, -1 ≤ p (n + 1) - p n) {t : ℕ}
    (hhit : p t = -(r : ℤ)) (hfirst : ∀ s < t, p s ≠ -(r : ℤ)) :
    ∀ s < t, -(r : ℤ) < p s := by
  intro s hs
  induction s with
  | zero => rw [hp0]; omega
  | succ s ih =>
    have hprev := ih (by omega)
    have hstep' := hstep s
    by_contra hbad
    have heq : p (s + 1) = -(r : ℤ) := by omega
    exact hfirst (s + 1) hs heq

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped geometry); not a paper result.
A lower bound on every visited height is a lower bound on its running minimum. -/
private theorem lower_bound_runningMin (f : ℕ → ℤ) (a : ℤ) :
    ∀ n, (∀ j ≤ n, a ≤ f j) → a ≤ runningMin f n := by
  intro n
  induction n with
  | zero => intro h; simpa [runningMin] using h 0 le_rfl
  | succ n ih =>
    intro h
    rw [runningMin]
    apply le_min
    · apply ih
      intro j hj
      exact h j (by omega)
    · exact h (n + 1) le_rfl

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped geometry); not a paper result.
At the first hit of `-r` by the KMSW vertical walk, the previous value is
`-r+1`, and every earlier value is at least `-r+1`. -/
theorem hat_first_hit_prev_running_min (w : ℕ → Fin 3) (r : ℕ)
    (hr : 1 ≤ r) {t : ℕ} (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ)) :
    R w (t - 1) = -(r : ℤ) + 1 ∧
      ∀ s < t, -(r : ℤ) + 1 ≤ R w s := by
  have hzero : R w 0 = 0 := by simp [R]
  have hstep (n : ℕ) : -1 ≤ R w (n + 1) - R w n := by
    have hs : R w (n + 1) = R w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
      Finset.sum_range_succ _ _
    rw [hs, add_sub_cancel_left]
    have hc : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
      have := (w n).isLt
      omega
    rcases hc with hc | hc | hc <;> rw [hc] <;>
      norm_num [RandomWalk.lazyTwoDimensionalStep]
  have hstrict := codeWalk_strictly_above_before_first_hit (R w) r hr hzero
    hstep hhit hfirst
  have htpos : 0 < t := by
    by_contra h
    have ht : t = 0 := by omega
    subst t
    rw [hzero] at hhit
    omega
  have hprevStrict : -(r : ℤ) < R w (t - 1) := hstrict (t - 1) (by omega)
  have hidx : t - 1 + 1 = t := by omega
  have hstepPrev := hstep (t - 1)
  rw [hidx, hhit] at hstepPrev
  constructor
  · omega
  · intro s hs
    have h := hstrict s hs
    omega

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped geometry); not a paper result.
The KMSW stage immediately before its first vertical hit of `-r` has empty
upper-right boundary. -/
theorem stopped_UR_nil (w : ℕ → Fin 3) (r : ℕ) (hr : 1 ≤ r)
    {t : ℕ} (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ)) :
    (kmswStage w (t - 1)).UR = [] := by
  obtain ⟨hprev, hbefore⟩ := hat_first_hit_prev_running_min w r hr hhit hfirst
  have htpos : 0 < t := by
    by_contra h
    have ht : t = 0 := by omega
    subst t
    have hzero : R w 0 = 0 := by simp [R]
    rw [hzero] at hhit
    omega
  let n := t - 1
  have hlow : ∀ j ≤ n, -(r : ℤ) + 1 ≤ R w j := by
    intro j hj
    exact hbefore j (by dsimp [n] at hj ⊢; omega)
  have hminLower : -(r : ℤ) + 1 ≤ runningMin (R w) n :=
    lower_bound_runningMin (R w) (-(r : ℤ) + 1) n hlow
  have hminUpper : runningMin (R w) n ≤ R w n :=
    runningMin_le (R w) n n le_rfl
  have hnval : R w n = -(r : ℤ) + 1 := by
    simpa [n] using hprev
  have hmin : runningMin (R w) n = -(r : ℤ) + 1 := by omega
  have hlen := kmswStage_UR_length w n
  change ((kmswStage w n).UR.length : ℤ) =
    R w n - runningMin (R w) n at hlen
  rw [hnval, hmin] at hlen
  have hlen0 : ((kmswStage w n).UR.length : ℤ) = 0 := by omega
  have hnat : (kmswStage w n).UR.length = 0 := by exact_mod_cast hlen0
  have hnil : (kmswStage w n).UR = [] := List.length_eq_zero_iff.mp hnat
  simpa [n] using hnil

end DirectedDistances.PaperProofs.Section7
