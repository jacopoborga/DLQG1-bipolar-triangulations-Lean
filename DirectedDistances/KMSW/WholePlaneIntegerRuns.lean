module

public import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
public import DirectedDistances.KMSW.WholePlaneLLRecordEdges
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure

/-! Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

private theorem measurable_integerShift (n : ℤ) :
    Measurable (fun W : ℤ → Fin 3 => fun i : ℤ => W (i + n)) := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_pi_apply (i + n)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Translation of a two-sided iid word preserves its law, so
any almost-sure property holds for every translated word, simultaneously. -/
theorem wholePlaneIID_ae_shift_all
    (P : (ℤ → Fin 3) → Prop)
    (hP : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, P W) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ, P (fun i => W (i + n)) := by
  apply ae_all_iff.2
  intro n
  have h := hP
  rw [← wholePlaneIIDCodeMeasure_map_shift n] at h
  exact ae_of_ae_map (measurable_integerShift n).aemeasurable h

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Cutting the translated word at stage zero gives the run
whose absolute start is `n`. -/
theorem integerRun_eq_shiftedStream_zero (W : ℤ → Fin 3) (n : ℤ) :
    (fun i : ℕ => W ((i : ℤ) + n)) =
      shiftedStream (fun k : ℤ => W (k + n)) 0 := by
  funext i
  simp [shiftedStream]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. A run starting at `-N` is the existing `shiftedStream W N`. -/
theorem integerRun_neg_nat_eq_shiftedStream (W : ℤ → Fin 3) (N : ℕ) :
    (fun i : ℕ => W ((i : ℤ) + (-(N : ℤ)))) = shiftedStream W N := by
  funext i
  apply congrArg W
  omega

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Almost surely, every integer-start run has the one-sided
degree classification from `wholePlaneIID_ae_runBoundaryDegree`. -/
theorem wholePlaneIID_ae_runBoundaryDegree_integer_starts :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      ∃ h : BoundaryHitWitnesses (fun i : ℕ => W ((i : ℤ) + n)), ∀ v,
        (∃ m, v < (kmswStage (fun i : ℕ => W ((i : ℤ) + n)) m).nextVertex) →
          (∃ e, EdgePresent (fun i : ℕ => W ((i : ℤ) + n)) e ∧
            edgeWest (fun i : ℕ => W ((i : ℤ) + n)) e = v) ∧
          ((¬ ∃ e, EdgePresent (fun i : ℕ => W ((i : ℤ) + n)) e ∧
              edgeEast (fun i : ℕ => W ((i : ℤ) + n)) e = v) ↔
            ∃ k : ℤ, k ≤ 0 ∧
              v = boundaryVertex (fun i : ℕ => W ((i : ℤ) + n)) h k) := by
  have hzero : ∀ᵐ V ∂wholePlaneIIDCodeMeasure,
      ∃ h : BoundaryHitWitnesses (shiftedStream V 0), ∀ v,
        (∃ m, v < (kmswStage (shiftedStream V 0) m).nextVertex) →
          (∃ e, EdgePresent (shiftedStream V 0) e ∧
            edgeWest (shiftedStream V 0) e = v) ∧
          ((¬ ∃ e, EdgePresent (shiftedStream V 0) e ∧
              edgeEast (shiftedStream V 0) e = v) ↔
            ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex (shiftedStream V 0) h k) := by
    filter_upwards [wholePlaneIID_ae_runBoundaryDegree] with V h
    exact h 0
  have hall := wholePlaneIID_ae_shift_all _ hzero
  filter_upwards [hall] with W h n
  simpa only [integerRun_eq_shiftedStream_zero] using h n

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Almost surely, every integer-start run's strict lower-left
record edge is missing from that run. The presence clause is stated in the
separately constructed colimit of the translated word: its stage `N` is the run
`i ↦ W ((i : ℤ) - N + n)`. No equivalence with `WholePlaneEdge W` is proved. -/
theorem wholePlaneIID_ae_LL_record_edges_integer_starts :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ, ∀ m : ℕ, 0 < m →
      (∀ j < m, L (fun i : ℕ => W ((i : ℤ) + n)) m <
        L (fun i : ℕ => W ((i : ℤ) + n)) j) →
      wholePlaneEdgePresent (fun k : ℤ => W (k + n))
        (wholePlaneEdgeι (fun k : ℤ => W (k + n)) 0
          (kmswLLCreatedEdge (fun i : ℕ => W ((i : ℤ) + n)) m)) ∧
        ¬ EdgePresent (fun i : ℕ => W ((i : ℤ) + n))
          (kmswLLCreatedEdge (fun i : ℕ => W ((i : ℤ) + n)) m) := by
  have hzero : ∀ᵐ V ∂wholePlaneIIDCodeMeasure, ∀ m : ℕ, 0 < m →
      (∀ j < m, L (shiftedStream V 0) m < L (shiftedStream V 0) j) →
      wholePlaneEdgePresent V
        (wholePlaneEdgeι V 0 (kmswLLCreatedEdge (shiftedStream V 0) m)) ∧
        ¬ EdgePresent (shiftedStream V 0) (kmswLLCreatedEdge (shiftedStream V 0) m) := by
    filter_upwards [wholePlaneIID_ae_LL_record_edges] with V h
    intro m hm hr
    exact h 0 m hm hr
  have hall := wholePlaneIID_ae_shift_all _ hzero
  filter_upwards [hall] with W h n m hm hr
  have hr' : ∀ j < m,
      L (shiftedStream (fun k : ℤ => W (k + n)) 0) m <
        L (shiftedStream (fun k : ℤ => W (k + n)) 0) j := by
    simpa only [integerRun_eq_shiftedStream_zero] using hr
  have hc := h n m hm hr'
  simpa only [integerRun_eq_shiftedStream_zero] using hc

end DirectedDistances.KMSW
