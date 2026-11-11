module

public import DirectedDistances.KMSW.BoundaryAEExistence
public import DirectedDistances.PaperProofs.Section5.FlowLineTimesLemma

/-! # Almost-sure local content toward Lemma 5.12

This file exposes the deterministic flow-line-hit consequence of the boundary
witnesses and packages the local clauses of Lemma 5.12 almost surely. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Filter MeasureTheory
open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

-- This first-hit argument is copied from the private helper in
-- `DirectedDistances/KMSW/Beta0BoundarySuccessor.lean:228`.
private theorem boundary_future_hit_for_flow (f : ℕ → ℤ)
    (hs : ∀ n, f n - 1 ≤ f (n + 1))
    (hu : ∀ a : ℤ, ∃ n, f n ≤ a) (n : ℕ) :
    ∃ m, n + 1 ≤ m ∧ f m = f n - 1 := by
  classical
  obtain ⟨m, hm⟩ := hu (runningMin f n - 1)
  have hmn : n < m := by
    by_contra h
    have := runningMin_le f n m (by omega)
    omega
  have hmin := runningMin_le f n n le_rfl
  have hex : ∃ m, n + 1 ≤ m ∧ f m ≤ f n - 1 :=
    ⟨m, by omega, by omega⟩
  let t := Nat.find hex
  have ht : n + 1 ≤ t ∧ f t ≤ f n - 1 := Nat.find_spec hex
  have hp : f n - 1 < f (t - 1) := by
    by_cases he : t - 1 = n
    · rw [he]
      omega
    · have hnot := Nat.find_min hex (show t - 1 < t by omega)
      by_contra h
      exact hnot ⟨by omega, by omega⟩
  have hstep := hs (t - 1)
  rw [show t - 1 + 1 = t by omega] at hstep
  exact ⟨t, ht.1, by omega⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Re-proves the private boundary implication from
`DirectedDistances/KMSW/Beta0BoundarySuccessor.lean:252` -/
theorem hasFlowLineHits_of_boundaryHitWitnesses (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) : HasFlowLineHits w := by
  constructor
  · apply boundary_future_hit_for_flow (L w)
    · intro n
      have hs : L w (n + 1) = L w n +
          (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
      have hl : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
        change (-1 : ℤ) ≤ (w n : ℤ) - 1
        omega
      omega
    · intro a
      obtain ⟨n, hn⟩ := hb.leftHit (min a (-1)) (min_le_right _ _)
      exact ⟨n, hn ▸ min_le_left _ _⟩
  · apply boundary_future_hit_for_flow (R w)
    · intro n
      have hs : R w (n + 1) = R w n +
          (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
      have hl : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
        change (-1 : ℤ) ≤ if w n = 0 then 0 else if w n = 1 then 1 else -1
        split
        · omega
        · split <;> omega
      omega
    · exact hb.R_unbounded_below

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Almost surely supplies finite incidence and boundary-hit witnesses for the -/
theorem iidCodes_ae_flowLineEvent :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ _hfin : ∀ v : ℕ,
        {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨
            (kmswStage w n).east e = v)}.Finite,
      ∃ _hb : BoundaryHitWitnesses w, True := by
  filter_upwards [DirectedDistances.KMSW.iidCodes_ae_boundaryProperties]
    with ω hprops
  change ∃ _hfin : ∀ v : ℕ,
      {e : ℕ | ∃ n, e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
          (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
    ∃ _hb : BoundaryHitWitnesses (fun i => ω (i + 1)), True
  obtain ⟨hfin, hb, _⟩ := hprops
  exact ⟨hfin, hb, trivial⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Almost surely provides the joint minima and items (i) and (ii), excluding -/
theorem lemma_5_12_local_part :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ hfin : ∀ v : ℕ,
        {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨
            (kmswStage w n).east e = v)}.Finite,
      ∃ hb : BoundaryHitWitnesses w,
      ∃ h : HasFlowLineHits w,
        FlowLineTimesJointMinima w h ∧
        FlowLineTimesItemI w h ∧
        FlowLineTimesItemII w hfin hb h := by
  filter_upwards [iidCodes_ae_boundaryProperties] with ω hprops
  change ∃ hfin : ∀ v : ℕ,
      {e : ℕ | ∃ n, e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
          (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
    ∃ hb : BoundaryHitWitnesses (fun i => ω (i + 1)),
    ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      FlowLineTimesJointMinima (fun i => ω (i + 1)) h ∧
      FlowLineTimesItemI (fun i => ω (i + 1)) h ∧
      FlowLineTimesItemII (fun i => ω (i + 1)) hfin hb h
  obtain ⟨hfin, hb, _⟩ := hprops
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let h := hasFlowLineHits_of_boundaryHitWitnesses w hb
  obtain ⟨hmin, hitems⟩ := flow_line_times_lemma_local w hfin hb h
  exact ⟨hfin, hb, h, hmin, hitems.1, hitems.2.1⟩

end DirectedDistances.PaperProofs.Section5
