 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.PitmanProcessLaw

/-!
# Lemma 5.15 (`lem-lazy-walk-flip`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/







public section
namespace DirectedDistances.Paper.Section5
open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped ENNReal



theorem pitman_transform_conditioned_prefix_law :
∀ {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : Ω → ℕ → ℤ}
    (hL : Measurable L) (hzero : ∀ᵐ ω ∂μ, L ω 0 = 0)
    (hind : iIndepFun (fun i ω => L ω (i + 1) - L ω i) μ)
    (hlaw : ∀ i, μ.map (fun ω => L ω (i + 1) - L ω i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)),
    ∀ n : ℕ,
      μ.map (fun ω => fun j : Fin (n + 1) => globalLazyPhi (L ω) j.val) =
        (μ.map (fun ω => fun j : Fin (n + 1) => L ω j.val)).withDensity
          (fun p : Fin (n + 1) → ℤ => if ∀ j, 0 ≤ p j then
            (((p (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) else 0) :=
 
by exact DirectedDistances.RandomWalk.pitman_process_prefix_law
 
 

end DirectedDistances.Paper.Section5
 
