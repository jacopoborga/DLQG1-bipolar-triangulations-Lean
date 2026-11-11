/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.CanonicalBusemann
public import DirectedDistances.KMSW.DirectedContainLaw1

/-! # Measurable boundary hitting times for the canonical Busemann construction

This helper supports the code-space realization of `thm-busemann`
measurability of the totalized first coordinate-hit time used to define the
boundary labels, and identifies it with `boundaryHitTime` wherever the hit
witnesses exist. It does not prove measurability of the canonical Busemann
function itself.

Open in this file (not proved here): `Measurable (fun ω => canonicalBusemannLDP ω k)`. Remaining gap here: the canonical selector chooses finiteness and hit witnesses and a common reachable sequence by choice; measurable finite-prefix approximants of the selected distances are not constructed in this file. A measurable a.e.-equal version is constructed separately in `Recursive/BusemannMeasurable.lean` (`busemannLDPMeasurableVersion`, `measurable_busemannLDPMeasurableVersion`, `iidCodes_ae_busemannLDPMeasurableVersion_eq`). -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory

private theorem measurable_codeFstFirstHit (a : ℤ) :
    Measurable (fun ω : ℕ → Fin 3 => RandomWalk.codeFstFirstHit a ω) := by
  rw [ENat.measurable_iff]
  intro n
  exact RandomWalk.codePast_le n _
    (RandomWalk.measurableSet_codePast_codeFstFirstHit_eq a n)

private theorem measurable_codeSndFirstHit (a : ℤ) :
    Measurable (fun ω : ℕ → Fin 3 => RandomWalk.codeSndFirstHit a ω) := by
  rw [ENat.measurable_iff]
  intro n
  exact RandomWalk.codePast_le n _
    (RandomWalk.measurableSet_codePast_codeSndFirstHit_eq a n)

/-- The totalized first coordinate-hit time associated with the boundary
index `k`, with value zero at `k = 0`. For positive `k` it is the first hit
of `R = -k`; for negative `k` it is the first hit of `L = k`. It is a helper -/
@[expose] noncomputable def boundaryHitTimeTotal (ω : ℕ → Fin 3) (k : ℤ) : ℕ∞ := by
  classical
  exact if hk0 : k = 0 then 0 else
    if hkpos : 0 < k then RandomWalk.codeSndFirstHit (-k) ω
    else RandomWalk.codeFstFirstHit k ω

/-- The totalized boundary coordinate-hit time is measurable on code space.
210–238`). -/
theorem measurable_boundaryHitTimeTotal (k : ℤ) :
    Measurable (fun ω : ℕ → Fin 3 => boundaryHitTimeTotal ω k) := by
  classical
  by_cases hk0 : k = 0
  · simp [boundaryHitTimeTotal, hk0]
  · by_cases hkpos : 0 < k
    · simpa [boundaryHitTimeTotal, hk0, hkpos] using measurable_codeSndFirstHit (-k)
    · simpa [boundaryHitTimeTotal, hk0, hkpos] using measurable_codeFstFirstHit k

/-- On codes with boundary-hit witnesses, `boundaryHitTimeTotal` agrees with
the witness-indexed `boundaryHitTime` (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryHitTimeTotal_eq_boundaryHitTime (ω : ℕ → Fin 3)
    (h : KMSW.BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) :
    boundaryHitTimeTotal ω k =
      (KMSW.boundaryHitTime (fun i => ω (i + 1)) h k : ℕ∞) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryHitTimeTotal, KMSW.boundaryHitTime_zero]
  · by_cases hkpos : 0 < k
    · have hk : 1 ≤ k := by omega
      simp only [boundaryHitTimeTotal,
        dite_eq_right (by omega : k ≠ 0),
        dite_eq_left (by omega : 0 < k)]
      exact KMSW.codeSndFirstHit_eq_boundaryHitTime ω h hk
    · have hkneg : k ≤ -1 := by omega
      simp only [boundaryHitTimeTotal,
        dite_eq_right (by omega : k ≠ 0),
        dite_eq_right (by omega : ¬ 0 < k)]
      exact KMSW.codeFstFirstHit_eq_boundaryHitTime ω h hkneg

end DirectedDistances.Recursive
