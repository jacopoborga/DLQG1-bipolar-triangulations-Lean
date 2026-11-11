module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.KMSW.StageTriangleDarts

import DirectedDistances.KMSW.KMSWInverseStepLink
import DirectedDistances.KMSW.HatTriangleSim
import DirectedDistances.KMSW.StageBoundaryMap
import DirectedDistances.KMSW.StageIncidence

/-! # Candidate provider for Definition 3.3 (`def-kmsw`)


Clause dictionary for `def_3_3_kmsw_provider`:

* The first conjunct records the single directed edge and coincident UL/LR
  boundaries from source line 71.
* In the transition conjunction, `w n = 2` is increment `(1,-1)` (lines 77–81):
  the first subclause activates the first missing UR edge, and the second adds
  a present pendant active edge when UR is empty.
* `w n = 0` is increment `(-1,0)` (lines 85–89): the two subclauses add a
  triangle using the nearest existing UL edge, or a fresh missing third edge.
* `w n = 1` is increment `(0,1)` (line 91): the final subclause adds a
  triangle and a fresh missing third edge.
* `State.triangles` stores `(old active, new active, third edge)` records;
  the paired `stageTriangleDartTriple` and `FaceSucc3Cycle` conjuncts certify
  the cyclic face order, including when a side is missing.

In `State`, a present edge is directed from `west` to `east`; missing edges
retain geometric endpoints and have `present = false`. -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Candidate provider toward Definition 3.3 (`def-kmsw`); not yet a counted
paper result. This records the initial state and every exact code-step branch -/
theorem def_3_3_kmsw_provider (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w 0).nextVertex = 2 ∧
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
     ((w n = 2 → ∀ e es, s.UR = e :: es →
        s.present e = false ∧
        t.nextEdge = s.nextEdge ∧ t.nextVertex = s.nextVertex ∧
        t.west = s.west ∧ t.east = s.east ∧
        t.active = e ∧ t.present e = true ∧
        t.triangles = s.triangles ∧
        t.UL = s.UL ++ [e] ∧ t.UR = es ∧
        t.LR = s.LR ∧ t.LL = s.LL) ∧
      (w n = 2 → s.UR = [] →
        t.nextEdge = s.nextEdge + 1 ∧ t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.east s.active ∧
        t.east s.nextEdge = s.nextVertex ∧
        t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
        t.triangles = s.triangles ∧
        (∀ tri ∈ t.triangles,
          tri.1 ≠ s.nextEdge ∧ tri.2.1 ≠ s.nextEdge ∧
            tri.2.2 ≠ s.nextEdge) ∧
        t.UL = s.UL ++ [s.nextEdge] ∧ t.UR = [] ∧
        t.LR = s.LR ++ [s.nextEdge] ∧ t.LL = s.LL) ∧
      (∀ (hc : w n = 0), ∀ e es, s.UL.dropLast.reverse = e :: es →
        s.present e = true ∧
        t.nextEdge = s.nextEdge + 1 ∧ t.nextVertex = s.nextVertex ∧
        t.west s.nextEdge = s.west e ∧
        t.east s.nextEdge = s.east s.active ∧
        t.west e = t.west s.nextEdge ∧
        t.east s.active = t.east s.nextEdge ∧
        t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, e)] ∧
        t.UL = es.reverse ++ [s.nextEdge] ∧
        t.UR = s.UR ∧ t.LR = s.LR ∧ t.LL = s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inl hc⟩ =
          ((e, false), (s.active, false), (s.nextEdge, true)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc
          (stageTriangleDart₁ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₂ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₃ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))) ∧
      (∀ (hc : w n = 0), s.UL.dropLast.reverse = [] →
        t.nextEdge = s.nextEdge + 2 ∧ t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.nextVertex ∧
        t.east s.nextEdge = s.east s.active ∧
        t.west (s.nextEdge + 1) = s.nextVertex ∧
        t.east (s.nextEdge + 1) = s.west s.active ∧
        t.east s.active = t.east s.nextEdge ∧
        t.west (s.nextEdge + 1) = t.west s.nextEdge ∧
        t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
        t.present (s.nextEdge + 1) = false ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] ∧
        t.UL = [s.nextEdge] ∧ t.UR = s.UR ∧
        t.LR = s.LR ∧ t.LL = (s.nextEdge + 1) :: s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inl hc⟩ =
          ((s.active, false), (s.nextEdge, true),
            (s.nextEdge + 1, false)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc
          (stageTriangleDart₁ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₂ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₃ w (n + 1) ⟨n, Or.inl hc⟩
            (Nat.lt_succ_self n))) ∧
      (∀ (hc : w n = 1),
        t.nextEdge = s.nextEdge + 2 ∧ t.nextVertex = s.nextVertex + 1 ∧
        t.west s.nextEdge = s.west s.active ∧
        t.east s.nextEdge = s.nextVertex ∧
        t.west (s.nextEdge + 1) = s.nextVertex ∧
        t.east (s.nextEdge + 1) = s.east s.active ∧
        t.west s.active = t.west s.nextEdge ∧
        t.west (s.nextEdge + 1) = t.east s.nextEdge ∧
        t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
        t.present (s.nextEdge + 1) = false ∧
        t.triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] ∧
        t.UL = s.UL.dropLast ++ [s.nextEdge] ∧
        t.UR = (s.nextEdge + 1) :: s.UR ∧
        t.LR = s.LR ∧ t.LL = s.LL ∧
        stageTriangleDartTriple w ⟨n, Or.inr hc⟩ =
          ((s.active, false), (s.nextEdge + 1, true),
            (s.nextEdge, true)) ∧
        FaceSucc3Cycle (kmswMap w (n + 1)).faceSucc
          (stageTriangleDart₁ w (n + 1) ⟨n, Or.inr hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₂ w (n + 1) ⟨n, Or.inr hc⟩
            (Nat.lt_succ_self n))
          (stageTriangleDart₃ w (n + 1) ⟨n, Or.inr hc⟩
            (Nat.lt_succ_self n))))) := by
  constructor
  · simp [kmswStage, kmswInit]
  · dsimp only
    constructor
    · intro hc e es hur
      have he : e < (kmswStage w n).nextEdge := by
        apply stageRun_edge_bound w n e
        exact Or.inl (Or.inl (Or.inr (by simp [hur])))
      have hmissing := ((kmswStage_status w n).1 e he).2
        (Or.inl (by simp [hur]))
      have h := kmswStage_step_activation_facts w n e es hc hur
      rcases h with ⟨hEdge, hVertex, hWest, hEast, hActive, hPresent,
        _, hUL, hLR, hUR, hLL⟩
      have htri : (kmswStage w (n + 1)).triangles =
          (kmswStage w n).triangles := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hur]
      exact ⟨hmissing, hEdge, hVertex, hWest, hEast, hActive,
        hPresent, htri, hUL, hUR, hLR, hLL⟩
    constructor
    · intro hc hur
      have h := kmswStage_step_pendant_facts w n hc hur
      rcases h with ⟨hEdge, hVertex, hWest, hEast, hActive, hPresent,
        hUL, hLR, hUR, hLL⟩
      have htri : (kmswStage w (n + 1)).triangles =
          (kmswStage w n).triangles := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hur, State.addEdge]
      have hnoTri : ∀ tri ∈ (kmswStage w (n + 1)).triangles,
          tri.1 ≠ (kmswStage w n).nextEdge ∧
            tri.2.1 ≠ (kmswStage w n).nextEdge ∧
              tri.2.2 ≠ (kmswStage w n).nextEdge := by
        intro tri hmem
        rw [htri] at hmem
        obtain ⟨h₁, h₂, h₃⟩ := (triBound_stage w n) tri hmem
        exact ⟨by omega, by omega, by omega⟩
      exact ⟨hEdge, hVertex, hWest, hEast, hActive, hPresent,
        htri, hnoTri, hUL, hUR, hLR, hLL⟩
    constructor
    · intro hc e es hUL
      have heUL : e ∈ (kmswStage w n).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [hUL]; simp))
      have hpresent := (kmswStage_status w n).2.1 e heUL
      have h := kmswStage_step_leftExisting_facts w n e es hc hUL
      rcases h with ⟨hEdge, hVertex, hWest, hEast, hActive, hNewPresent,
        hUL', hLR, hUR, hLL⟩
      have htri : (kmswStage w (n + 1)).triangles =
          (kmswStage w n).triangles ++
            [((kmswStage w n).active, (kmswStage w n).nextEdge, e)] := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hUL, State.addEdge]
      have he : e < (kmswStage w n).nextEdge :=
        stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl heUL)))
      have hstableE := kmswStage_endpoints_stable w
        (m := n) (n := n + 1) (by omega) he
      have hactiveBound := act_lt_nextEdge w (le_refl n)
      have hstableActive := kmswStage_endpoints_stable w
        (m := n) (n := n + 1) (by omega) hactiveBound
      have hface := stageTriangle_isFace w ⟨n, Or.inl hc⟩
        (n + 1) (Nat.lt_succ_self n)
      have htriple := stageTriangleDartTriple_left_existing w
        ⟨n, Or.inl hc⟩ hc e es hUL
      exact ⟨hpresent, hEdge, hVertex, hWest, hEast,
        hstableE.1.trans hWest.symm,
        hstableActive.2.trans hEast.symm,
        hActive, hNewPresent, htri, hUL', hUR, hLR, hLL,
        htriple, hface⟩
    constructor
    · intro hc hUL
      have h := kmswStage_step_leftFresh_facts w n hc hUL
      rcases h with ⟨hEdge, hVertex, hWest, hEast, hMissingWest,
        hMissingEast, hActive, hPresent, hMissing, hUL', hLR, hUR, hLL⟩
      have hactiveBound := act_lt_nextEdge w (le_refl n)
      have hstableActive := kmswStage_endpoints_stable w
        (m := n) (n := n + 1) (by omega) hactiveBound
      have hterminal := hstableActive.2.trans hEast.symm
      have hwest : (kmswStage w (n + 1)).west
          ((kmswStage w n).nextEdge + 1) =
            (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge) :=
        hMissingWest.trans hWest.symm
      have htri : (kmswStage w (n + 1)).triangles =
          (kmswStage w n).triangles ++
            [((kmswStage w n).active, (kmswStage w n).nextEdge,
              (kmswStage w n).nextEdge + 1)] := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hUL, State.addEdge]
      have hface := stageTriangle_isFace w ⟨n, Or.inl hc⟩
        (n + 1) (Nat.lt_succ_self n)
      have htriple := stageTriangleDartTriple_left_fresh w
        ⟨n, Or.inl hc⟩ hc hUL
      exact ⟨hEdge, hVertex, hWest, hEast, hMissingWest, hMissingEast,
        hterminal, hwest, hActive, hPresent, hMissing, htri, hUL', hUR,
        hLR, hLL, htriple, hface⟩
    · intro hc
      have h := kmswStage_step_up_facts w n hc
      rcases h with ⟨hEdge, hVertex, hWest, hEast, hMissingWest,
        hMissingEast, hActive, hPresent, hMissing, hUL, hLR, hUR, hLL⟩
      have hactiveBound := act_lt_nextEdge w (le_refl n)
      have hstableActive := kmswStage_endpoints_stable w
        (m := n) (n := n + 1) (by omega) hactiveBound
      have hinitial := hstableActive.1.trans hWest.symm
      have hterminal : (kmswStage w (n + 1)).west
          ((kmswStage w n).nextEdge + 1) =
            (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge) :=
        hMissingWest.trans hEast.symm
      have htri : (kmswStage w (n + 1)).triangles =
          (kmswStage w n).triangles ++
            [((kmswStage w n).active, (kmswStage w n).nextEdge,
              (kmswStage w n).nextEdge + 1)] := by
        simp [kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, State.addEdge]
      have hface := stageTriangle_isFace w ⟨n, Or.inr hc⟩
        (n + 1) (Nat.lt_succ_self n)
      have htriple := stageTriangleDartTriple_up w ⟨n, Or.inr hc⟩ hc
      exact ⟨hEdge, hVertex, hWest, hEast, hMissingWest, hMissingEast,
        hinitial, hterminal, hActive, hPresent, hMissing, htri, hUL,
        hUR, hLR, hLL, htriple, hface⟩

end DirectedDistances.PaperProofs.Section3
