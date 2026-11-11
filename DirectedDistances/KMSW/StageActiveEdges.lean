module

public import DirectedDistances.KMSW.BoundaryDynamics
import DirectedDistances.KMSW.BoundaryRecordsUL
import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.FlowLineReachability
import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.CutEquivalenceConverse
import DirectedDistances.KMSW.StageIncidenceChains

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW




theorem kmswStage_active_lt (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).active < (kmswStage w t).nextEdge :=
  act_lt_nextEdge w le_rfl




theorem kmswStage_active_present_mono (w : ℕ → Fin 3) {t m : ℕ}
    (htm : t ≤ m) :
    (kmswStage w m).present (kmswStage w t).active = true := by
  exact (present_mono w (kmswStage_active_lt w t)
    (kmswStage_active_present w t) m htm).2




theorem kmswStage_active_injOn (w : ℕ → Fin 3) (n t t' : ℕ)
    (_ht : t ≤ n) (_ht' : t' ≤ n)
    (h : (kmswStage w t).active = (kmswStage w t').active) :
    t = t' :=
  CutConverse.act_injective w h




theorem kmswStage_present_eq_active (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true) :
    ∃ t ≤ n, (kmswStage w t).active = e := by
  obtain ⟨t, htn, hte⟩ := stagePresent_exists_active w n e he hp
  exact ⟨t, htn, by simpa only [act] using hte.symm⟩




theorem kmswStage_up_active_endpoints (w : ℕ → Fin 3) (t : ℕ)
    (hc : w t = 1) :
    (kmswStage w (t + 1)).west (kmswStage w (t + 1)).active =
        (kmswStage w t).west (kmswStage w t).active ∧
      (kmswStage w (t + 1)).east (kmswStage w (t + 1)).active =
        (kmswStage w t).nextVertex := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge]





theorem kmswStage_down_UR_cons_endpoints (w : ℕ → Fin 3) (t e : ℕ)
    (es : List ℕ) (hc : w t = 2)
    (hUR : (kmswStage w t).UR = e :: es) :
    (kmswStage w (t + 1)).active = e ∧
      (kmswStage w (t + 1)).west (kmswStage w (t + 1)).active =
        (kmswStage w t).east (kmswStage w t).active := by
  have hhead : (kmswStage w t).west e =
      (kmswStage w t).east (kmswStage w t).active :=
    (kmswStage_boundary_chain_invariant w t).2.2.2.2.2.1 e es hUR
  constructor
  · simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR]
  · simpa [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR]
      using hhead




theorem kmswStage_down_UR_nil_endpoints (w : ℕ → Fin 3) (t : ℕ)
    (hc : w t = 2) (hUR : (kmswStage w t).UR = []) :
    (kmswStage w (t + 1)).west (kmswStage w (t + 1)).active =
        (kmswStage w t).east (kmswStage w t).active ∧
      (kmswStage w (t + 1)).east (kmswStage w (t + 1)).active =
        (kmswStage w t).nextVertex := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR,
    State.addEdge]




theorem kmswStage_left_UL_cons_endpoints (w : ℕ → Fin 3) (t e : ℕ)
    (es : List ℕ) (hc : w t = 0)
    (hUL : (kmswStage w t).UL.dropLast.reverse = e :: es) :
    (kmswStage w (t + 1)).west (kmswStage w (t + 1)).active =
        (kmswStage w t).west e ∧
      (kmswStage w (t + 1)).east (kmswStage w (t + 1)).active =
        (kmswStage w t).east (kmswStage w t).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]




theorem kmswStage_left_UL_nil_endpoints (w : ℕ → Fin 3) (t : ℕ)
    (hc : w t = 0)
    (hUL : (kmswStage w t).UL.dropLast.reverse = []) :
    (kmswStage w (t + 1)).west (kmswStage w (t + 1)).active =
        (kmswStage w t).nextVertex ∧
      (kmswStage w (t + 1)).east (kmswStage w (t + 1)).active =
        (kmswStage w t).east (kmswStage w t).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

end DirectedDistances.KMSW
