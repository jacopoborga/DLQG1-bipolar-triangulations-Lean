 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.KMSWLeft

/-!
# Lemma 3.19 (`lem-kmsw-left`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/







































public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap



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
 
by exact DirectedDistances.PaperProofs.SourceResults.kmsw_left
 
 

end DirectedDistances.Paper.Section3
 
