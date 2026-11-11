/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWLeftZeroStep

/-! # Isolated proof provider for Lemma 3.19 (lem-kmsw-left), S7-singleton-corrected

This single-declaration leaf assembles the checked theorems
`lem_kmsw_left_procedureReading_uniform` (positive `ℓ, n`) and
`kmsw_left_zeroStep_procedureReading` (the separate `m₀` / zero-step-walk clause), which
the S7-singleton correction (exclude only `m₀` from the positive-length target, keep `n - 1`
non-boundary edges and `N = n + ℓ`, and separately record `m₀`'s correspondence with the
separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Isolated source-domain proof provider for Lemma 3.19 (lem-kmsw-left), procedure reading,
with the separate `m₀` / zero-step-walk clause. -/
theorem kmsw_left :
    (∀ (ℓ n : ℕ), 1 ≤ ℓ → 1 ≤ n →
      ∃ F : KMSWLeftWalkClass ℓ n ≃
          {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
        (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
        (∀ c (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}),
          Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
            (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) →
              q = F c) ∧
        (∀ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
          KMSWMapIsoClass.nonBoundaryEdgeCount q.val = n - 1)) ∧
    (∃ F : KMSWLeftWalkClass 1 0 ≃ {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled},
      (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0))) ∧
      (∀ c (q : {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0)) → q = F c) ∧
      (∀ q : {q : KMSWMapIsoClass 1 1 1 // q.IsChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = 0)) :=
by exact ⟨fun ℓ n hℓ hn =>
    DirectedDistances.KMSW.lem_kmsw_left_procedureReading_uniform ℓ n hℓ hn,
  DirectedDistances.KMSW.kmsw_left_zeroStep_procedureReading⟩

end DirectedDistances.PaperProofs.SourceResults
