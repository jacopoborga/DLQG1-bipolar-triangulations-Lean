/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DiskCodeMarkUniform
public import DirectedDistances.KMSW.KMSWDiskFiniteSample







public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk
  DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped ENNReal





private theorem uniformCountingMeasure_prod_singleton_mass
    (Q : Type*) (ell : ℕ) [Fintype Q]
    [MeasurableSpace Q] [MeasurableSpace (Fin ell)]
    [MeasurableSingletonClass Q] [MeasurableSingletonClass (Fin ell)]
    (q : Q) (k : Fin ell) :
    ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell)))
      {p | p = (q, k)} =
        (Fintype.card Q : ℝ≥0∞)⁻¹ * (ell : ℝ≥0∞)⁻¹ := by
  rw [show {p : Q × Fin ell | p = (q, k)} = ({q} ×ˢ {k}) by
    ext p
    simp]
  rw [Measure.prod_prod]
  simp [uniformCountingMeasure, Fintype.card_fin]





theorem bridgeLevelLaw_diskClassMark_singleton
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    let F : KMSWLeftWalkClass (ell + 1) n ≃
        {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
      kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    ∀ q : Q, ∀ k : Fin ell,
      bridgeLevelLaw n ell
        {p | (∀ i : Fin n, p.1 (i.val + 1) = (F.symm q).val i) ∧
          p.2 = k.val + 1} =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell)))
        {p | p = (q, k)} := by
  classical
  dsimp only
  let F : KMSWLeftWalkClass (ell + 1) n ≃
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
    kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  intro q k
  let c : KMSWLeftWalkClass (ell + 1) n := F.symm q
  have hfiber := bridgeLevelLaw_code_mark_fiber ell n hell hle hmod c k
  have hleft :
      {p : (ℕ → Fin 3) × ℕ |
        (∀ i : Fin n, p.1 (i.val + 1) = (F.symm q).val i) ∧ p.2 = k.val + 1} =
        {p | (∀ i : Fin n, p.1 (i.val + 1) = c.val i) ∧ p.2 = k.val + 1} := by
    rfl
  rw [hleft, hfiber]
  let instQ : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  have hcard : @Fintype.card Q instQ = Fintype.card (KMSWLeftWalkClass (ell + 1) n) := by
    exact @Fintype.card_congr Q (KMSWLeftWalkClass (ell + 1) n)
      instQ inferInstance F.symm
  have hmass := @uniformCountingMeasure_prod_singleton_mass Q ell instQ
    (⊤ : MeasurableSpace Q) (⊤ : MeasurableSpace (Fin ell))
    (inferInstance : @MeasurableSingletonClass Q ⊤)
    (inferInstance : @MeasurableSingletonClass (Fin ell) ⊤) q k
  rw [← hcard, hmass]

end DirectedDistances.PaperProofs.Section5
