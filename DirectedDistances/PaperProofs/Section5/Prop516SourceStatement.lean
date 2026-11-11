/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516D39ClassTransport

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology





theorem diskRootedPlanarMapLaw_positiveIndex_toMeasure
    (n : {n : ℕ // 0 < n}) (ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n.1)
    (hmod : ∃ q : ℤ, (n.1 : ℤ) = (ell : ℤ) + 3 * q) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n.1 (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n.1 + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n.1) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (diskRootedPlanarMapLaw n.1 ell hell hle hmod).toMeasure =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (diskRootedPlanarMapOfSample n.1 ell hell) := by
  exact diskRootedPlanarMapLaw_toMeasure n.1 ell hell hle hmod




theorem diskRootedPlanarMapLaw_sourceIndex_tendsto_uibhbot
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < ell n)
    (hadm : ∀ n : ℕ, 0 < n →
      ell n ≤ n ∧ ∃ q : ℤ, (n : ℤ) = (ell n : ℤ) + 3 * q)
    (hlo : ∀ n : ℕ, 0 < n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell n : ℝ))
    (hhi : ∀ n : ℕ, 0 < n →
      (ell n : ℝ) ≤ A * Real.sqrt (n : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    Tendsto
      (fun n : {n : ℕ // 0 < n} =>
        diskRootedPlanarMapLaw n.1 (ell n.1)
          (hpos n.1 n.2) (hadm n.1 n.2).1 (hadm n.1 n.2).2)
      atTop (𝓝 uibhbotRootedPlanarMapLaw) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let sourcePreimage : {n : ℕ // 0 < n} → ℕ := fun n => n.1 - 1
  have hsourcePreimage : Tendsto sourcePreimage atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop
      (⟨k + 1, Nat.succ_pos k⟩ : {n : ℕ // 0 < n})] with n hn
    change k + 1 ≤ n.1 at hn
    change k ≤ n.1 - 1
    omega
  let sourceSeq : {n : ℕ // 0 < n} → ProbabilityMeasure RootedLocallyFinitePlanarMap :=
    fun n => diskRootedPlanarMapLaw n.1 (ell n.1)
      (hpos n.1 n.2) (hadm n.1 n.2).1 (hadm n.1 n.2).2
  let shiftedSeq : ℕ → ProbabilityMeasure RootedLocallyFinitePlanarMap :=
    fun k => diskRootedPlanarMapLaw (k + 1) (ell (k + 1))
      (hpos (k + 1) (Nat.succ_pos k))
      (hadm (k + 1) (Nat.succ_pos k)).1
      (hadm (k + 1) (Nat.succ_pos k)).2
  have hconv := diskRootedPlanarMapLaw_tendsto_uibhbot
    A hA (fun k => ell (k + 1))
    (fun k =>
      ⟨hpos (k + 1) (Nat.succ_pos k),
        (hadm (k + 1) (Nat.succ_pos k)).1,
        (hadm (k + 1) (Nat.succ_pos k)).2⟩)
    (fun k => hlo (k + 1) (Nat.succ_pos k))
    (fun k => hhi (k + 1) (Nat.succ_pos k))
  have hseq : sourceSeq = shiftedSeq ∘ sourcePreimage := by
    funext n
    dsimp [sourceSeq, shiftedSeq, sourcePreimage]
    have hn : n.1 - 1 + 1 = n.1 := by omega
    simp only [hn]
  change Tendsto sourceSeq atTop (𝓝 uibhbotRootedPlanarMapLaw)
  rw [hseq]
  exact hconv.comp hsourcePreimage




































































end DirectedDistances.PaperProofs.Section5
