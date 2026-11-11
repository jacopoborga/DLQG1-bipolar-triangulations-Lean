module

public import DirectedDistances.KMSW.StageOuterWordSucc
public import DirectedDistances.KMSW.StageOuterWordSuccAlloc
public import DirectedDistances.KMSW.StagePlanar
public import DirectedDistances.KMSW.StageDirectedMap
public import DirectedDistances.KMSW.StageTrianglePersistence

/-! # The outer-word cycle property of every finite KMSW stage

The branch lemmas of `StageOuterWordSucc` (zero, down-activation, both left cases, and the
induction `stageOuterWord_faceSucc_of_branches`) and of `StageOuterWordSuccAlloc` (up and
pendant) give, for every code sequence and every stage, that the face permutation acts on
cyclic successor. Consequently every finite stage is a genus-zero combinatorial map
directed-map-with-missing-edges structure with acyclic orientation and the UL/LR boundary
bridges, and every recorded triangle is a face. Helper statements; no numbered source result
is admitted here. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The outer-word cycle property holds at every stage of every code sequence -/
theorem stageOuterWord_faceSucc (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d :=
  stageOuterWord_faceSucc_of_branches stageOuterWord_faceSucc_up
    stageOuterWord_faceSucc_pendant w n

/-- Every finite KMSW stage is a genus-zero combinatorial map: connected with Euler -/
theorem kmswMap_isPlanar (w : ℕ → Fin 3) (n : ℕ) : (kmswMap w n).IsPlanar :=
  kmswMap_isPlanar_of_cycle w (fun m => stageOuterWord_faceSucc w m) n

/-- The directed map with missing edges of a finite KMSW stage -/
@[expose] def kmswStageDirectedMap (w : ℕ → Fin 3) (n : ℕ) :
    DirectedMapWithMissing (StageDart (kmswStage w n).nextEdge) :=
  kmswDirectedMap w n (stageOuterWord_faceSucc w n)

/-- The orientation of every finite KMSW stage is acyclic -/
theorem kmswStageDirectedMap_isAcyclic (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageDirectedMap w n).IsAcyclic :=
  kmswDirectedMap_isAcyclic w n (stageOuterWord_faceSucc w n)

/-- Upper-left bookkeeping edges are exactly the edges whose tail dart is an upper-left -/
theorem kmswStageDirectedMap_UL_bridge (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    e.val ∈ (kmswStage w n).UL ↔ (e, false) ∈ (kmswStageDirectedMap w n).ulDarts :=
  kmswDirectedMap_UL_bridge w n (stageOuterWord_faceSucc w n) e

/-- Lower-right bookkeeping edges are exactly the edges whose head dart is a lower-right -/
theorem kmswStageDirectedMap_LR_bridge (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    e.val ∈ (kmswStage w n).LR ↔ (e, true) ∈ (kmswStageDirectedMap w n).lrDarts :=
  kmswDirectedMap_LR_bridge w n (stageOuterWord_faceSucc w n) e

/-- Every recorded triangle is a face (a three-cycle of the face permutation) at every -/
theorem stageTriangle_isFace (w : ℕ → Fin 3) (j : TriangleCreationTime w) (n : ℕ)
    (hj : j.val < n) :
    FaceSucc3Cycle (kmswMap w n).faceSucc
      (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
      (stageTriangleDart₃ w n j hj) :=
  stageTriangle_faceSucc3Cycle w (fun m => stageOuterWord_faceSucc w m) j n hj

end DirectedDistances.KMSW
