module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteInvariance
public import Mathlib.Data.Nat.Sqrt

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory TopologicalSpace





theorem uibhbotRootedPlanarMapLaw_map_mirror_invariant_of_admissible_sequence
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).map
        mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw := by
  exact uibhbotRootedPlanarMapLaw_map_eq_unconditionally A hA ell hadm hlo hhi

/-- Helper toward Proposition 5.9. A positive boundary length congruent to `k + 1`
and comparable to its square root. -/
def prop59AdmissibleBoundaryLength (k : ℕ) : ℕ :=
  Nat.sqrt (k + 1) + ((k + 1 - Nat.sqrt (k + 1)) % 3)

/-- Helper toward Proposition 5.9. The explicit square-root boundary lengths meet the
admissibility and uniform two-sided bounds needed by the local-limit corollary. -/
theorem prop59AdmissibleBoundaryLength_spec (k : ℕ) :
    0 < prop59AdmissibleBoundaryLength k ∧
      prop59AdmissibleBoundaryLength k ≤ k + 1 ∧
      (∃ q : ℤ, ((k + 1 : ℕ) : ℤ) =
        (prop59AdmissibleBoundaryLength k : ℤ) + 3 * q) ∧
      (3 : ℝ)⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        (prop59AdmissibleBoundaryLength k : ℝ) ∧
      (prop59AdmissibleBoundaryLength k : ℝ) ≤
        3 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
  let m := k + 1
  let s := Nat.sqrt m
  let r := (m - s) % 3
  have hm : 0 < m := by simp [m]
  have hs : 0 < s := (Nat.sqrt_pos).2 hm
  have hsm : s ≤ m := Nat.sqrt_le_self m
  have hr : r < 3 := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hrle : r ≤ m - s := Nat.mod_le _ _
  have hlow : s ≤ prop59AdmissibleBoundaryLength k := by
    change s ≤ s + r
    omega
  have hhigh : prop59AdmissibleBoundaryLength k ≤ 3 * s := by
    have hsone : 1 ≤ s := by omega
    change s + r ≤ 3 * s
    omega
  have hmod := Nat.mod_add_div (m - s) 3
  have hrootlower : (s : ℝ) ≤ Real.sqrt (m : ℝ) := by
    change (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ)
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (Nat.sqrt_le' m)
  have hrootupper : Real.sqrt (m : ℝ) < (s : ℝ) + 1 := by
    apply (Real.sqrt_lt' (by positivity)).2
    have hnat : m < (Nat.succ s) ^ 2 := by
      simpa [s, pow_two] using (Nat.lt_succ_sqrt m)
    have hnatR : (m : ℝ) < ((Nat.succ s : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hnat
    simpa [Nat.succ_eq_add_one] using hnatR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 0 < s + r
    omega
  · change s + r ≤ m
    omega
  · refine ⟨((m - s) / 3 : ℕ), ?_⟩
    have hmodZ : (((m - s) % 3 : ℕ) : ℤ) +
        3 * (((m - s) / 3 : ℕ) : ℤ) = ((m - s : ℕ) : ℤ) := by
      exact_mod_cast hmod
    have hsubZ : ((m : ℕ) : ℤ) - ((s : ℕ) : ℤ) = ((m - s : ℕ) : ℤ) := by
      rw [Nat.cast_sub hsm]
    change (m : ℤ) = (s : ℤ) + ((m - s) % 3 : ℕ) +
      3 * (((m - s) / 3 : ℕ) : ℤ)
    omega
  · have hbound : Real.sqrt (m : ℝ) ≤ 2 *
        (prop59AdmissibleBoundaryLength k : ℝ) := by
      have hspos : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      have hlowR : (s : ℝ) ≤ (prop59AdmissibleBoundaryLength k : ℝ) := by
        exact_mod_cast hlow
      linarith [le_of_lt hrootupper]
    have hdiv : Real.sqrt (m : ℝ) / 3 ≤
        (prop59AdmissibleBoundaryLength k : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith
    calc
      (3 : ℝ)⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) =
          Real.sqrt (m : ℝ) / 3 := by simp [m, div_eq_mul_inv, mul_comm]
      _ ≤ (prop59AdmissibleBoundaryLength k : ℝ) := by simpa [m] using hdiv
  · have hhighR : (prop59AdmissibleBoundaryLength k : ℝ) ≤ 3 * (s : ℝ) := by
      exact_mod_cast hhigh
    calc
      (prop59AdmissibleBoundaryLength k : ℝ) ≤ 3 * (s : ℝ) := hhighR
      _ ≤ 3 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
        simpa [m] using (mul_le_mul_of_nonneg_left hrootlower (by norm_num : (0:ℝ) ≤ 3))






theorem prop_uihbot_sym :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw := by
  exact uibhbotRootedPlanarMapLaw_map_mirror_invariant_of_admissible_sequence
    3 (by norm_num) prop59AdmissibleBoundaryLength
    (fun k => ⟨(prop59AdmissibleBoundaryLength_spec k).1,
      ⟨(prop59AdmissibleBoundaryLength_spec k).2.1,
        (prop59AdmissibleBoundaryLength_spec k).2.2.1⟩⟩)
    (fun k => (prop59AdmissibleBoundaryLength_spec k).2.2.2.1)
    (fun k => (prop59AdmissibleBoundaryLength_spec k).2.2.2.2)

/-! No exact statement anchor was found under `DirectedDistances/Paper/Section5/` for
`prop-uihbot-sym` or `5.9`. The law here is the code push-forward `uibhbotRootedPlanarMapLaw`.
On a conull event, `uibhbotRootedPlanarMapOfCode_on_event` identifies the code-selected map
with the canonical rooted locally finite map `uibhbotRootedLocallyFinitePlanarMap`;
`Prop516Def58Law` matches its root edge with the root edge enumerated by the installed
Definition 5.8 provider, and `Prop59ProviderLaw` relates the provider to the code law only at
the local topology planar-class level. The provider's assembly carrier is not identified with
`RootedLocallyFinitePlanarMap`, and no source-plane (orientation-reversing homeomorphism) or
local topology mirror transfer is established. This theorem therefore does not assert Proposition 5.9,
faithfulness of local topology to orientation-preserving planar-map equivalence, or whole-paper
completion. -/

end DirectedDistances.PaperProofs.Section5
end


