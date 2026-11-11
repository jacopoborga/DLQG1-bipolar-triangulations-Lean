/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison
public import DirectedDistances.PaperProofs.Section5.Prop59ProviderRootedMapIso

/-! Reversed-root lifting preserves the exact local topology cylinder topology and transports
the proved finite-sample cylinder limit to exterior-marked codes. The lift is
identified with geometric exterior only for drawings with the corresponding
proved source certificate. No geometric convergence is claimed here. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal
open Prop516RootExteriorEncoding

/-- Helper toward Proposition 5.16: a lifted cylinder is precisely its
unmarked cylinder whenever the target is the reversed-root lift of its
projection. -/
theorem rootLift_cylinder_eq_of_mem_range {X : Type*} (b : X → D39BallClass)
    (c : ExteriorMarkedBallClass) (hc : rootLift c.forget = c) :
    (fun x => rootLift (b x)) ⁻¹' {c} = b ⁻¹' {c.forget} := by
  ext x
  change rootLift (b x) = c ↔ b x = c.forget
  conv_lhs => rw [← hc]
  exact rootLift_injective.eq_iff

/-- Helper toward Proposition 5.16: classes outside the reversed-root
image have empty cylinders, including in every finite-sample law. -/
theorem rootLift_cylinder_eq_empty {X : Type*} (b : X → D39BallClass)
    (c : ExteriorMarkedBallClass) (hc : rootLift c.forget ≠ c) :
    (fun x => rootLift (b x)) ⁻¹' {c} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  change rootLift (b x) = c at hx
  apply hc
  rw [← hx, rootLift_forget]

/-- Helper toward Proposition 5.16: reversed-root marking preserves the
cylinder topology exactly, without changing the underlying map carrier. -/
theorem rootLift_localClassTopology {X : Type*} (b : ℕ → X → D39BallClass) :
    localClassTopology (fun r x => rootLift (b r x)) = localClassTopology b := by
  apply le_antisymm
  · let : TopologicalSpace X := localClassTopology (fun r x => rootLift (b r x))
    apply le_generateFrom
    rintro s ⟨r, c, rfl⟩
    have heq : (fun x => rootLift (b r x)) ⁻¹' {rootLift c} = b r ⁻¹' {c} := by
      ext x
      exact rootLift_injective.eq_iff
    rw [← heq]
    exact isOpen_localCylinder (fun r x => rootLift (b r x)) r (rootLift c)
  · let : TopologicalSpace X := localClassTopology b
    apply le_generateFrom
    rintro s ⟨r, c, rfl⟩
    by_cases hc : rootLift c.forget = c
    · rw [rootLift_cylinder_eq_of_mem_range (b r) c hc]
      exact isOpen_localCylinder b r c.forget
    · rw [rootLift_cylinder_eq_empty (b r) c hc]
      exact isOpen_empty

/-- Helper toward Proposition 5.16: the marked local topology observation topology is
literally the existing Definition 3.8 combinatorial topology. -/
theorem rootLift_d39_topology :
    localClassTopology (fun r (M : D39RootedMap) =>
      rootLift (d39RootedBallSystem.ballClass r M)) =
        bsLocalDistanceTopologyGeneric d39RootedBallSystem := by
  exact (rootLift_localClassTopology
    (fun r (M : D39RootedMap) => d39RootedBallSystem.ballClass r M)).trans
      (bsLocalDistanceTopology_eq_localClassTopologyGeneric d39RootedBallSystem).symm

/-- Helper toward Proposition 5.16: restriction of faced balls commutes
with reversed-root marked equality at consecutive positive radii. -/
theorem rootLift_d39_restriction (M N : D39RootedMap) (r : ℕ)
    (h : rootLift (d39RootedBallSystem.ballClass (r + 1) M) =
      rootLift (d39RootedBallSystem.ballClass (r + 1) N)) :
    rootLift (d39RootedBallSystem.ballClass r M) =
      rootLift (d39RootedBallSystem.ballClass r N) := by
  apply congrArg rootLift
  exact d39BallClass_restriction_compatible M N (r + 1) (Nat.succ_pos r)
    (rootLift_injective h)

/-- Helper toward Proposition 5.16: the canonical drawing's actual exterior
code agrees with the lift of the code-selected rooted map used in the limit
law, for every provider witness and every positive radius. -/
theorem canonicalExteriorMarkedClass_eq_code_rootLift
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    (r : ℕ) (hr : 0 < r) :
    Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr) =
      rootLift (d39BallClass
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr) := by
  rw [prop516_canonicalExteriorMarkedBallClass_eq_rootLift W D hhit C₀ hrootAbsent r hr]
  obtain ⟨⟨I⟩, _⟩ := uibhbotRootedPlanarMapOfCode_d39_iso_for_provider_rotation
    W hW D.rotation hhit C₀ (fun _ => uibhbotRootEdge W) rfl
  exact congrArg rootLift (Quotient.sound ⟨I.ballIso r hr⟩)

/-- Helper toward Proposition 5.16: the canonical geometric/code cylinder
identification holds simultaneously for all radii and provider witnesses
on one conull event. -/
theorem canonicalExteriorMarkedClass_eq_code_rootLift_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0) (r : ℕ) (hr : 0 < r),
        Quotient.mk exteriorMarkedBallSetoid
          (d39FacedBallPLWithExternal
            (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
            (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr) =
          rootLift (d39BallClass
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr) := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1,
    prop59_uibhbotRootEdge_absent_ae_for_mirror_compat] with W hW hroot
  intro D hhit C₀ r hr
  exact canonicalExteriorMarkedClass_eq_code_rootLift W hW D hhit C₀ hroot r hr

/-- Helper toward Proposition 5.16: convergence of every unmarked cylinder
mass transports to every reversed-root marked cylinder mass; no measurability
of a quotient choice or summation over unmarked classes is needed. -/
theorem rootLift_cylinder_tendsto
    {X ι : Type*} [MeasurableSpace X] {L : Filter ι}
    (b : X → D39BallClass) (μs : ι → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X)
    (h : ∀ c, Tendsto (fun i => μs i (b ⁻¹' {c})) L (𝓝 (μ (b ⁻¹' {c}))))
    (c : ExteriorMarkedBallClass) :
    Tendsto (fun i => μs i ((fun x => rootLift (b x)) ⁻¹' {c})) L
      (𝓝 (μ ((fun x => rootLift (b x)) ⁻¹' {c}))) := by
  by_cases hc : rootLift c.forget = c
  · rw [rootLift_cylinder_eq_of_mem_range b c hc]
    exact h c.forget
  · rw [rootLift_cylinder_eq_empty b c hc]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : NNReal)) L (𝓝 0))

/-- Helper toward Proposition 5.16: the actual finite disk laws converge
on all reversed-root marked local topology cylinders to the canonical UIBHBOT law,
using exactly the existing admissibility and shared square-root bounds. -/
theorem diskRootedPlanarMapLaw_rootLift_cylinder_tendsto_uibhbot
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    ∀ r c, Tendsto (fun k =>
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
          (fun M : RootedLocallyFinitePlanarMap =>
            M.toRootedLocallyFiniteMap.toD39RootedMap))
        ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c}))
      atTop (𝓝 ((uibhbotRootedPlanarMapLaw.map
        (fun M : RootedLocallyFinitePlanarMap =>
          M.toRootedLocallyFiniteMap.toD39RootedMap))
        ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c}))) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace D39RootedMap := borel D39RootedMap
  let : BorelSpace D39RootedMap := ⟨rfl⟩
  intro r c
  exact rootLift_cylinder_tendsto
    (fun M : D39RootedMap => d39RootedBallSystem.ballClass r M) _ _
    (diskRootedPlanarMapLaw_d39_cylinder_tendsto_uibhbot A hA ell hadm hlo hhi r) c

/- The marked cylinder limit above is unconditional apart from the displayed
source size/admissibility bounds. It is not geometric weak convergence.
The source metric target with all binders is recorded in
Prop516ExteriorMarkedComparison.lean. Until it is proved, no marked variant
of the geometric assembly is supplied, and no reverse comparison is taken
as a hypothesis. The measurable geometric class maps, their cylinder
identifications on the common carrier, and the Definition 5.8 law
identification remain the explicit downstream assembly obligations. -/

end DirectedDistances.PaperProofs.Section5

end
