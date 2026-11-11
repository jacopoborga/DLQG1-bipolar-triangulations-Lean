module

public import DirectedDistances.KMSW.PrimedComplementCoverageBase
import DirectedDistances.KMSW.PrimedInducedEmbedding
import DirectedDistances.KMSW.FlowLineEntryFrontier
import DirectedDistances.KMSW.OutgoingInterval

/-! # Primed complement coverage across compressed crossings

The skipped right-phase active edges are root-reachable. Thus a present edge
outside every root-reachable present-edge set was already present before the
crossing or is the exit active edge. Coherence transports the former preimage;
the existing crossing simulation supplies the latter through active alignment.
This closes the edge-only G2 helper for the implemented interval blocks. -/

public section
namespace DirectedDistances.KMSW

private theorem crossing_active_preimage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    ∃ e, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ∧
      (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e = true ∧
      primedAllEdgeMap w h m e = act w (primedStageTime w h m) := by
  obtain ⟨k, hs, _⟩ := primedAll_sim w h m hm
  let u := primedCode (primedSimInput w) h
  have hagree := kmswMissingRootStage_agree u m
  refine ⟨(kmswMissingRootStage u m).active, ?_, primed_active_present w h m hm,
    hs.active_alignment⟩
  rw [hagree.2.2.2.2.2.2.1, hagree.2.1]
  exact act_lt_nextEdge u le_rfl

private theorem crossing_local_present_step (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m e : ℕ)
    (he : e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hp : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e = true) :
    e < (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge ∧
      (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).present e = true := by
  constructor
  · rw [(kmswMissingRootStage_agree _ (m + 1)).2.1]
    have hb : e < (kmswStage (primedCode (primedSimInput w) h) m).nextEdge := by
      rw [← (kmswMissingRootStage_agree _ m).2.1]
      exact he
    exact hb.trans_le (kmswStage_nextEdge_mono _ (Nat.le_succ m))
  · change (kmswStep _ _).present e = true
    rw [kmswStep_present_existing _ _ he]
    split
    · rfl
    · exact hp

/-- gate G2 (complement edge coverage); primedStageTime follows the implemented
interval blocks, not a ruling on positive-time counting convention; C18 root convention; Q1–Q3 not used;
not the paper result.
Coverage survives a compressed crossing: an edge activated strictly inside
the skipped right phase is root-reachable. Every remaining present edge has
an old preimage or is the exit active edge, covered by the active simulation. -/
theorem primedComplementCoverageAt_step_crossing (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (hc : PrimedComplementCoverageAt w h
      (primedIntervalBase (primedSimInput w) h (k + 1))) :
    PrimedComplementCoverageAt w h
      (primedIntervalBase (primedSimInput w) h (k + 1) + 1) := by
  let m := primedIntervalBase (primedSimInput w) h (k + 1)
  have ht0 : primedStageTime w h m = walkNR w h (k + 1) - 1 :=
    primedStageTime_at_crossing w h k
  have ht1 : primedStageTime w h (m + 1) = walkNL w h (k + 1) :=
    primedStageTime_after_crossing w h (k + 1)
  intro e he hp hnever
  rw [ht1] at he hp
  obtain ⟨j, hj, heq⟩ := stagePresent_exists_active w (walkNL w h (k + 1)) e he hp
  by_cases hjold : j ≤ primedStageTime w h m
  · have hold := present_mono w (act_lt_nextEdge w (le_rfl : j ≤ j))
      (kmswStage_active_present w j) (primedStageTime w h m) hjold
    rw [← heq] at hold
    obtain ⟨f, hf, hpf, hmap⟩ := hc e hold.1 hold.2 hnever
    obtain ⟨hfnext, hpfnext⟩ := crossing_local_present_step w h m f hf hpf
    exact ⟨f, hfnext, hpfnext, ((primedAll_maps_extend w h m).1 f hf).trans hmap⟩
  · have hjexit : j = walkNL w h (k + 1) := by
      by_contra hne
      have hr : walkNR w h (k + 1) ≤ j := by rw [ht0] at hjold; omega
      have hl : j < walkNL w h (k + 1) := by omega
      have hw := flowLine_phase_reachable w h (k + 1) j hr hl
      apply hnever j
      rw [heq]
      exact ⟨act_lt_nextEdge w le_rfl, kmswStage_active_present w j, hw,
        kmswStage_activeEast_reachable w j hw⟩
    obtain ⟨f, hf, hpf, hmap⟩ := crossing_active_preimage w h (m + 1) (by omega)
    refine ⟨f, hf, hpf, ?_⟩
    rw [hmap, ht1, heq, hjexit]

private theorem crossing_block_bounds (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    let k := primedIntervalIndex (primedSimInput w) h (m - 1)
    primedIntervalBase (primedSimInput w) h k < m ∧
      m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
  dsimp only
  have hr := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
  constructor
  · cases hk : primedIntervalIndex (primedSimInput w) h (m - 1) with
    | zero => rw [primedIntervalBase_zero]; omega
    | succ k =>
      have hn := Nat.find_min (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show k < Nat.find (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change k < primedIntervalIndex (primedSimInput w) h (m - 1)
          omega)
      omega
  · omega

private theorem crossing_step_cases (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    primedStageTime w h (m + 1) = primedStageTime w h m + 1 ∨
      ∃ k, m = primedIntervalBase (primedSimInput w) h (k + 1) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  obtain ⟨hl, hr⟩ := crossing_block_bounds w h m hm
  change primedIntervalBase (primedSimInput w) h k < m at hl
  change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
  by_cases ho : m < primedIntervalBase (primedSimInput w) h (k + 1)
  · left
    rw [primedStageTime_block w h k m hl hr,
      primedStageTime_block w h k (m + 1) (by omega) (by omega)]
    omega
  · exact Or.inr ⟨k, by omega⟩

/-- gate G2 (complement edge coverage); primedStageTime follows the implemented
interval blocks, not a ruling on positive-time counting convention; C18 root convention; Q1–Q3 not used;
not the paper result.
Coverage holds at every positive local stage, by the stage-one base and the
exhaustive ordinary-step or compressed-crossing split. -/
theorem primedComplementCoverageAt_all (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, 1 ≤ m → PrimedComplementCoverageAt w h m := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
      intro _
      by_cases hm : m = 0
      · subst m
        exact primedComplementCoverageAt_one w h
      · have hmpos : 1 ≤ m := by omega
        rcases crossing_step_cases w h m hmpos with ht | ⟨k, rfl⟩
        · exact primedComplementCoverageAt_step_ordinary w h m ht (ih hmpos)
        · exact primedComplementCoverageAt_step_crossing w h k (ih hmpos)

/-- gate G2 (complement edge coverage); primedStageTime follows the implemented
interval blocks, not a ruling on positive-time counting convention; C18 root convention; Q1–Q3 not used;
not the paper result.
Every globally present edge outside all root-reachable present-edge sets has
a present primed preimage under the coherent limit edge map. -/
theorem primedLimitEdgeComplement (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ e', EdgePresent w e' →
      (∀ n, e' ∉ stageReachablePresentEdges w n) →
      ∃ e, PrimedEdgePresent w h e ∧ primedLimitEdgeMap w h e = e' :=
  primedLimitEdgeComplement_of_positive_coverage w h (primedComplementCoverageAt_all w h)

end DirectedDistances.KMSW
