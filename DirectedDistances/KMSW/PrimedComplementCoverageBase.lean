module

public import DirectedDistances.KMSW.PrimedImageLimit
import DirectedDistances.KMSW.PrimedInducedEmbedding
import DirectedDistances.KMSW.OutgoingInterval


















public section
namespace DirectedDistances.KMSW

/-- gate G2 (complement edge coverage); primedStageTime follows the implemented
interval blocks, not a ruling on positive-time counting convention; Q1–Q3 not used; not the paper result.
Every allocated global edge present at this stage and absent from every
root-reachable present-edge set has an allocated present local preimage. -/
@[expose] def PrimedComplementCoverageAt (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : Prop :=
  ∀ e', e' < (kmswStage w (primedStageTime w h m)).nextEdge →
    (kmswStage w (primedStageTime w h m)).present e' = true →
    (∀ n, e' ∉ stageReachablePresentEdges w n) →
    ∃ e, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ∧
      (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e = true ∧
      primedAllEdgeMap w h m e = e'





theorem primedComplementCoverageAt_zero_impossible (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ¬ PrimedComplementCoverageAt w h 0 := by
  intro hcoverage
  let N := walkNL w h 0
  have he : act w N < (kmswStage w N).nextEdge := act_lt_nextEdge w le_rfl
  have hp : (kmswStage w N).present (act w N) = true :=
    kmswStage_active_present w N
  have hnever : ∀ n, act w N ∉ stageReachablePresentEdges w n := by
    intro n hreach
    have hwest : (kmswStage w n).west (act w N) =
        (kmswStage w N).west (act w N) :=
      (edge_endpoints_eq w hreach.1).1.trans (edge_endpoints_eq w he).1.symm
    have hw := hreach.2.2.1
    rw [hwest] at hw
    exact quadrantFirstR_exit_activeWest_unreachable w h hw
  obtain ⟨e, helocal, hplocal, _⟩ := hcoverage (act w N)
    (by simpa only [primedStageTime_zero] using he)
    (by simpa only [primedStageTime_zero] using hp) hnever
  have hezero : e = 0 := by
    change e < 1 at helocal
    omega
  subst e
  rw [kmswMissingRootStage_present_zero] at hplocal
  cases hplocal


private theorem primed_positive_active_preimage (w : ℕ → Fin 3)
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









theorem primedComplementCoverageAt_one (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : PrimedComplementCoverageAt w h 1 := by
  have ht : primedStageTime w h 1 = walkNL w h 0 := by
    simpa only [primedIntervalBase_zero, zero_add] using
      primedStageTime_after_crossing w h 0
  intro e he hp hnever
  rw [ht] at he hp
  obtain ⟨j, hj, heq⟩ := stagePresent_exists_active w (walkNL w h 0) e he hp
  have hjexit : j = walkNL w h 0 := by
    by_contra hne
    have hjlt : j < walkNL w h 0 := by omega
    have hb : e < (kmswStage w j).nextEdge := by
      rw [heq]
      exact act_lt_nextEdge w le_rfl
    have hpres : (kmswStage w j).present e = true := by
      rw [heq]
      exact kmswStage_active_present w j
    exact hnever j ⟨hb, hpres, quadrantFirstRStage_edges_reachable w h hjlt e hb⟩
  obtain ⟨f, hf, hpf, hmap⟩ := primed_positive_active_preimage w h 1 (by omega)
  refine ⟨f, hf, hpf, ?_⟩
  rw [hmap, ht, heq, hjexit]

private theorem primed_local_present_step (w : ℕ → Fin 3)
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








theorem primedComplementCoverageAt_step_ordinary (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (ht : primedStageTime w h (m + 1) = primedStageTime w h m + 1)
    (hc : PrimedComplementCoverageAt w h m) :
    PrimedComplementCoverageAt w h (m + 1) := by
  intro e he hp hnever
  rw [ht] at he hp
  obtain ⟨j, hj, heq⟩ :=
    stagePresent_exists_active w (primedStageTime w h m + 1) e he hp
  by_cases hjold : j ≤ primedStageTime w h m
  · have hold := present_mono w (act_lt_nextEdge w (le_rfl : j ≤ j))
      (kmswStage_active_present w j) (primedStageTime w h m) hjold
    rw [← heq] at hold
    obtain ⟨f, hf, hpf, hmap⟩ := hc e hold.1 hold.2 hnever
    obtain ⟨hfnext, hpfnext⟩ := primed_local_present_step w h m f hf hpf
    exact ⟨f, hfnext, hpfnext, ((primedAll_maps_extend w h m).1 f hf).trans hmap⟩
  · have hjnew : j = primedStageTime w h m + 1 := by omega
    obtain ⟨f, hf, hpf, hmap⟩ :=
      primed_positive_active_preimage w h (m + 1) (by omega)
    refine ⟨f, hf, hpf, ?_⟩
    rw [hmap, ht, heq, hjnew]


private theorem primed_coverage_walkNR_ge_index (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : k ≤ walkNR w h k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hL := (walkNL_spec w h k).1
    have hR := (walkNR_succ_spec w h k).1
    omega

private theorem primed_coverage_positive_time_cofinal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (N : ℕ) :
    ∃ m, 1 ≤ m ∧ N ≤ primedStageTime w h m := by
  refine ⟨primedIntervalBase (primedSimInput w) h (N + 1), ?_, ?_⟩
  · have hb := primedIntervalBase_ge (primedSimInput w) h (N + 1)
    omega
  · rw [primedStageTime_at_crossing]
    have hR := primed_coverage_walkNR_ge_index w h (N + 1)
    omega









theorem primedLimitEdgeComplement_of_positive_coverage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hcoverage : ∀ m, 1 ≤ m → PrimedComplementCoverageAt w h m) :
    ∀ e', EdgePresent w e' →
      (∀ n, e' ∉ stageReachablePresentEdges w n) →
      ∃ e, PrimedEdgePresent w h e ∧ primedLimitEdgeMap w h e = e' := by
  intro e' hp hnever
  obtain ⟨N, hN⟩ := hp.eventually_present
  obtain ⟨m, hm, htime⟩ := primed_coverage_positive_time_cofinal w h N
  have hstage := hN (primedStageTime w h m) htime
  obtain ⟨e, he, hpe, hmap⟩ := hcoverage m hm e' hstage.1 hstage.2 hnever
  exact ⟨e, ⟨m, he, hpe⟩, ((primedLimit_maps_eq_of_allocated w h m).1 e he).trans hmap⟩

end DirectedDistances.KMSW
