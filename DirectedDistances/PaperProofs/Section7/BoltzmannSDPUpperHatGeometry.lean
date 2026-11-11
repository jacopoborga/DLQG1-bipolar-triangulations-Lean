module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperProps2

/-! # Hat-walk geometry helpers for Lemma 7.13

The source hat-time convention is positive-time (`QuadrantSourceWalks`). The
zero-time tail belongs to the rooted future map, so the out-closure statement
has a necessary zero-time exception. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.RandomWalk

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: hat-walk geometry); not a paper result.
canonical hat-to-raw stage-time map is strictly increasing. -/
theorem quadrantRStageTime_strictMono (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : StrictMono (quadrantRStageTime w h) := by
  intro a b hab
  have hle := quadrantRStageTime_mono w h (Nat.le_of_lt hab)
  have hne : quadrantRStageTime w h a ≠ quadrantRStageTime w h b := by
    intro heq
    have hc := congrArg
      (fun n => (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount)
      heq
    rw [(quadrantRStageTime_spec w h a).2.1,
      (quadrantRStageTime_spec w h b).2.1] at hc
    omega
  exact lt_of_le_of_ne hle hne

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: hat-walk geometry); not a paper result.
root-reachable tail at a positive raw time is a hat time, by the definition
of the hatted future-time predicate. -/
theorem quadrantHatFuture_tail_isHatTime_of_pos (w : ℕ → Fin 3) (m : ℕ)
    (hm : 1 ≤ m)
    (hv : MhatVertex w ((kmswStage w m).west (act w m))) :
    quadrantHatTime w m := by
  exact ⟨hm, hv⟩

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: hat-walk geometry); not a paper result.
time zero the active tail is the root, which is future-reachable, while zero
is excluded from the positive-time hat-time predicate. -/
theorem quadrantHatTime_zero_tail_counterexample (w : ℕ → Fin 3) :
    MhatVertex w ((kmswStage w 0).west (act w 0)) ∧
      ¬ quadrantHatTime w 0 := by
  have htail : (kmswStage w 0).west (act w 0) = 0 := by
    rw [← CutConverse.activeInitial_eq]
    simp [activeInitial, edgeWest, act, kmswStage, kmswInit]
  constructor
  · simp [MhatVertex, htail]
  · simp [quadrantHatTime]

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: hat-walk geometry); not a paper result.
has a zero-time exception because `quadrantHatTime` only includes positive
raw times; every positive root-reachable active tail is a hat time. -/
theorem quadrantHatFuture_tail_isHatTime_or_zero (w : ℕ → Fin 3) (m : ℕ)
    (hv : MhatVertex w ((kmswStage w m).west (act w m))) :
    m = 0 ∨ quadrantHatTime w m := by
  by_cases hm : m = 0
  · exact Or.inl hm
  · exact Or.inr (quadrantHatFuture_tail_isHatTime_of_pos w m (by omega) hv)

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: hat-walk geometry); not a paper result.
ordered left boundary starts at the source and ends at the sink, so the
suffix selected by the mark is the upper marked arc orientation. -/
theorem boltzmannSdpUpper_leftVertex_source_sink {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) :
    boltzmannSdpUpper_leftVertex q 0 = q.1.2.2.out.B.source ∧
      boltzmannSdpUpper_leftVertex q (Fin.last q.1.1) =
        q.1.2.2.out.B.sink := by
  let B := q.1.2.2.out.B
  constructor
  · change B.leftPath.vertices.get
      ⟨0, by rw [B.leftPath.vertices_length]; simp⟩ = B.source
    exact B.leftPath.start_vertex
  · change B.leftPath.vertices.get
      ⟨q.1.1, by rw [B.leftPath.vertices_length]; omega⟩ = B.sink
    simpa [B.leftPath.vertices_length] using B.leftPath.end_vertex

end DirectedDistances.PaperProofs.Section7
