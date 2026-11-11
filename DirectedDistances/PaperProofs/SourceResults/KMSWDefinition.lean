/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWDefinitionFullProvider

/- # Isolated proof provider for Definition 3.3 (`def-kmsw`)

provider; installation, sealing and counting are separate gates. No conclusion
or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3

/-- Definition 3.3 isolated provider (`def-kmsw`, -/
theorem def_kmsw (w : ℕ → Fin 3) (n : ℕ) :
    (((kmswStage w 0).nextVertex = 2 ∧
        (kmswStage w 0).nextEdge = 1 ∧
        (kmswStage w 0).active = 0 ∧
        (kmswStage w 0).west 0 = 0 ∧
        (kmswStage w 0).east 0 = 1 ∧
        (kmswStage w 0).present 0 = true ∧
        (kmswStage w 0).triangles = [] ∧
        (kmswStage w 0).UL = [0] ∧
        (kmswStage w 0).LR = [0] ∧
        (kmswStage w 0).UR = [] ∧
        (kmswStage w 0).LL = []) ∧
        (let s := kmswStage w n
         let t := kmswStage w (n + 1)
         ((w n = 2 → ∀ e es, s.UR = e :: es
        → s.present e = false ∧
        t.nextEdge = s.nextEdge ∧
        t.nextVertex = s.nextVertex ∧
        t.west = s.west ∧
        t.east = s.east ∧
        t.active = e ∧
        t.present e = true ∧
        t.triangles = s.triangles ∧
        t.UL = s.UL ++ [e] ∧
        t.UR = es ∧
        t.LR = s.LR ∧
        t.LL = s.LL) ∧
        (w n = 2 → s.UR = [] → t.nextEdge = s.nextEdge + 1 ∧
        t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.east s.active ∧
        t.east s.nextEdge = s.nextVertex ∧
        t.active = s.nextEdge ∧
        t.present s.nextEdge = true ∧
        t.triangles = s.triangles ∧
        (∀ tri ∈ t.triangles, tri.1 ≠ s.nextEdge ∧
        tri.2.1 ≠ s.nextEdge ∧
        tri.2.2 ≠ s.nextEdge) ∧
        t.UL = s.UL ++ [s.nextEdge] ∧
        t.UR = [] ∧
        t.LR = s.LR ++ [s.nextEdge] ∧
        t.LL = s.LL) ∧
        (∀ (hc : w n = 0), ∀ e es, s.UL.dropLast.reverse = e :: es → s.present e = true ∧
        t.nextEdge = s.nextEdge + 1 ∧
        t.nextVertex = s.nextVertex ∧
        t.west s.nextEdge = s.west e ∧
        t.east s.nextEdge = s.east s.active ∧
        t.west e = t.west s.nextEdge ∧
        t.east s.active = t.east s.nextEdge ∧
        t.active = s.nextEdge ∧
        t.present s.nextEdge = true ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, e)] ∧
        t.UL = es.reverse ++ [s.nextEdge] ∧
        t.UR = s.UR ∧
        t.LR = s.LR ∧
        t.LL = s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inl hc⟩ = ((e, false), (s.active, false), (s.nextEdge,
        true)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc (stageTriangleDart₁ w (n + 1) ⟨n, Or.inl hc⟩
        (Nat.lt_succ_self n)) (stageTriangleDart₂ w (n + 1) ⟨n, Or.inl hc⟩ (Nat.lt_succ_self n))
        (stageTriangleDart₃ w (n + 1) ⟨n, Or.inl hc⟩ (Nat.lt_succ_self n))) ∧
        (∀ (hc : w n = 0), s.UL.dropLast.reverse = [] → t.nextEdge = s.nextEdge + 2 ∧
        t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.nextVertex ∧
        t.east s.nextEdge = s.east s.active ∧
        t.west (s.nextEdge + 1) = s.nextVertex ∧
        t.east (s.nextEdge + 1) = s.west s.active ∧
        t.east s.active = t.east s.nextEdge ∧
        t.west (s.nextEdge + 1) = t.west s.nextEdge ∧
        t.active = s.nextEdge ∧
        t.present s.nextEdge = true ∧
        t.present (s.nextEdge + 1) = false ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] ∧
        t.UL = [s.nextEdge] ∧
        t.UR = s.UR ∧
        t.LR = s.LR ∧
        t.LL = (s.nextEdge + 1) :: s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inl hc⟩ = ((s.active, false), (s.nextEdge, true),
        (s.nextEdge + 1, false)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc (stageTriangleDart₁ w (n + 1) ⟨n, Or.inl hc⟩
        (Nat.lt_succ_self n)) (stageTriangleDart₂ w (n + 1) ⟨n, Or.inl hc⟩ (Nat.lt_succ_self n))
        (stageTriangleDart₃ w (n + 1) ⟨n, Or.inl hc⟩ (Nat.lt_succ_self n))) ∧
        (∀ (hc : w n = 1), t.nextEdge = s.nextEdge + 2 ∧
        t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.west s.active ∧
        t.east s.nextEdge = s.nextVertex ∧
        t.west (s.nextEdge + 1) = s.nextVertex ∧
        t.east (s.nextEdge + 1) = s.east s.active ∧
        t.west s.active = t.west s.nextEdge ∧
        t.west (s.nextEdge + 1) = t.east s.nextEdge ∧
        t.active = s.nextEdge ∧
        t.present s.nextEdge = true ∧
        t.present (s.nextEdge + 1) = false ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] ∧
        t.UL = s.UL.dropLast ++ [s.nextEdge] ∧
        t.UR = (s.nextEdge + 1) :: s.UR ∧
        t.LR = s.LR ∧
        t.LL = s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inr hc⟩ = ((s.active, false), (s.nextEdge + 1, true),
        (s.nextEdge, true)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc (stageTriangleDart₁ w (n + 1) ⟨n, Or.inr hc⟩
        (Nat.lt_succ_self n)) (stageTriangleDart₂ w (n + 1) ⟨n, Or.inr hc⟩ (Nat.lt_succ_self n))
        (stageTriangleDart₃ w (n + 1) ⟨n, Or.inr hc⟩ (Nat.lt_succ_self n)))))) ∧
        ∀ j ≤ n + 1, (kmswMap w j).IsPlanar ∧
        (kmswStageDirectedMap w j).IsAcyclic ∧
        (∀ d ∈ stageOuterWord w j, (kmswMap w j).faceSucc d = (stageOuterWord w j).formPerm d) ∧
        (∀ d : StageDart (kmswStage w j).nextEdge, d ∈ stageOuterWord w j ∨
        (d ∉ stageOuterWord w j ∧ ∃! τ : TriangleCreationTime w, τ.val < j ∧
        (d.1.val, d.2) ∈ stageTriangleDartList w τ)) ∧
        (∀ τ : TriangleCreationTime w, ∀ hτ : τ.val < j, FaceSucc3Cycle (kmswMap w j).faceSucc
        (stageTriangleDart₁ w j τ hτ) (stageTriangleDart₂ w j τ hτ) (stageTriangleDart₃ w j τ
        hτ)) ∧
        (∀ d : StageDart (kmswStage w j).nextEdge, (d ∈ kmswStageULDartsFinset w j ↔ d ∈
        (kmswStageDirectedMap w j).ulDarts) ∧
        (d ∈ kmswStageLRDartsFinset w j ↔ d ∈ (kmswStageDirectedMap w j).lrDarts) ∧
        (d ∈ kmswStageLLDartsFinset w j ↔ (kmswStageDirectedMap w j).missing d ∧
        (kmswStageDirectedMap w j).IsOuter d ∧
        d.2 = true) ∧
        (d ∈ kmswStageURDartsFinset w j ↔ (kmswStageDirectedMap w j).missing d ∧
        (kmswStageDirectedMap w j).IsOuter d ∧
        d.2 = false))
:= by
  exact DirectedDistances.PaperProofs.Section3.def_3_3_kmsw_full_provider w n

end DirectedDistances.PaperProofs.SourceResults
