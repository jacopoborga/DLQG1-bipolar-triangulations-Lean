module

public import DirectedDistances.KMSW.WholePlaneLLRecordEdges
public import DirectedDistances.KMSW.WalkRecordCounts

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: the beta_0^L edges are present in the two-sided map); not a paper result.
Fixed-time backward record escape makes each hit-indexed lower-left edge present. -/
theorem m0Cut_llPresence_of_backwardRecordEscape (W : ℤ → Fin 3)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) (hk : k ≤ 0) :
    wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))) := by
  let w := shiftedStream W 0
  let q := k - 1
  let m := boundaryHitTime w h q
  have hq : q ≤ -1 := by dsimp [q]; omega
  have hmval : L w m = q := by
    exact boundaryHitTime_left_spec w h hq
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := by omega
    rw [hmzero] at hmval
    simp [L] at hmval
    omega
  have hzero : L w 0 = 0 := by simp [L]
  have hstep : ∀ i, |L w (i + 1) - L w i| ≤ 1 := by
    intro i
    have hsum : L w (i + 1) = L w i +
        (RandomWalk.lazyTwoDimensionalStep (w i)).1 := Finset.sum_range_succ _ _
    rw [hsum]
    have hbound : |(RandomWalk.lazyTwoDimensionalStep (w i)).1| ≤ 1 := by
      have hi : w i = 0 ∨ w i = 1 ∨ w i = 2 := by
        have hi' := (w i).isLt
        omega
      rcases hi with hi | hi | hi
      · rw [hi]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [hi]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [hi]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
    simpa only [add_sub_cancel_left] using hbound
  have hfind : m = Nat.find (h.leftHit q hq) := by
    dsimp [m, q, boundaryHitTime]
    simp only [dite_eq_right (by omega : k - 1 ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k - 1)]
  have hchar := (strict_running_minimum_iff_first_hit (L w) hzero hstep
    m m q (by dsimp [q]; omega) (h.leftHit q hq)).2
      ⟨le_rfl, hmval, hfind⟩
  have hrecord : ∀ j < m, L w m < L w j := by
    intro j hj
    exact (Finset.mem_filter.mp hchar.1).2 j hj
  exact wholePlaneLLCreatedEdge_present_of_record_escape W hB 0 m hmpos hrecord

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: the beta_0^L edges are present in the two-sided map); not a paper result.
Almost surely, every valid boundary-hit witness gives the lower-left presence premise. -/
theorem m0Cut_llPresence_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (h : BoundaryHitWitnesses (shiftedStream W 0)),
        ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))) := by
  filter_upwards [wholePlaneIID_ae_fixed_time_nonrecord] with W hB h k hk
  exact m0Cut_llPresence_of_backwardRecordEscape W hB h k hk

end DirectedDistances.KMSW
