/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHatPhases
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.CutEquivalence

/-! # Reachable present edges as an increasing union

P2 helper toward `lem-quad-kmsw`
of the KMSW stages are exactly the induced edges of M̂; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- P2 helper toward `lem-quad-kmsw`
of the KMSW stages are exactly the induced edges of M̂; not the paper result. -/
theorem stageReachablePresentEdges_iUnion_iff
    (w : ℕ → Fin 3) (e : ℕ) :
    (∃ n, e ∈ stageReachablePresentEdges w n) ↔
      EdgePresent w e ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩ := by
  constructor
  · rintro ⟨n, he⟩
    change e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).east e⟩ at he
    have hends := edge_endpoints_eq w he.1
    refine ⟨⟨n, he.1, he.2.1⟩, ?_, ?_⟩
    · exact hends.1 ▸ he.2.2.1
    · exact hends.2 ▸ he.2.2.2
  · rintro ⟨⟨n, hbound, hpresent⟩, hwest, heast⟩
    refine ⟨n, ?_⟩
    change e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).east e⟩
    have hends := edge_endpoints_eq w hbound
    exact ⟨hbound, hpresent, hends.1.symm ▸ hwest,
      hends.2.symm ▸ heast⟩

end DirectedDistances.KMSW
