module

public import DirectedDistances.PaperProofs.Section4.SelectedCutCodeDistanceLaw
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
public import DirectedDistances.PlanarMap.ZeroEdgeMarkedPast
public import DirectedDistances.PaperProofs.Section4.SelectedCutPastKernel

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The positive branches reuse `PositiveCutOutput`, created by
`firstHitPastAllCuts` through `lrRepresentativeCutPair`. In the planar cut model,
`pathCutLeftHalfDarts` and `pathCutRightHalfDarts` are each defined as the union
of the respective off-seam darts with `pathCutSeamDarts`
(`PlanarPathCutHalves.lean`); `lrRepresentativeCutPair` supplies the positive
side classes. This carrier does not identify the selected output with the paper's
submaps. Source: -/
abbrev Lemma414PositiveSide := Option (Σ n : ℕ, AllBoltzmannSpace n)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The positive side carrier is countable. Source: -/
noncomputable instance lemma414PositiveSide_countable :
    Countable (Σ n : ℕ, AllBoltzmannSpace n) := by
  unfold AllBoltzmannSpace
  infer_instance

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
One side is either the zero-edge point or an existing positive cut class. -/
abbrev Lemma414SideOutput := ZeroEdgeMarkedPast ⊕ Lemma414PositiveSide

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The zero-or-positive side carrier is countable. Source: -/
noncomputable instance lemma414SideOutput_countable :
    Countable Lemma414SideOutput := by
  dsimp [Lemma414SideOutput, PositiveCutOutput]
  infer_instance

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
Give the countable side carrier its discrete measurable space. Source: -/
noncomputable instance lemma414SideOutput_measurableSpace :
    MeasurableSpace Lemma414SideOutput := ⊤

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
On a zero selected cut return the distinct one-vertex, zero-edge point on each
side; otherwise embed the existing positive left and right cut classes. -/
@[expose] noncomputable def selectedCutPastSides
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (_hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) (p : ℕ → ℤ × ℤ) : Lemma414SideOutput × Lemma414SideOutput :=
  if selectedCutTime T k p = 0 then
    (Sum.inl zeroEdgeMarkedPast, Sum.inl zeroEdgeMarkedPast)
  else
    (Sum.inr (selectedCutPastCuts x T k p).1,
      Sum.inr (selectedCutPastCuts x T k p).2)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
Both outputs are measurable for a positive-success-time selector. -/
theorem measurable_selectedCutPastSides
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) :
    Measurable (selectedCutPastSides x T hT k) := by
  let S := {p | selectedCutTime T k p = 0}
  have hS : MeasurableSet S :=
    measurable_selectedCutTime T k hT (measurableSet_singleton 0)
  have hCuts : Measurable (selectedCutPastCuts x T k) :=
    measurable_selectedCutPastCuts x T k hT
  let embed : Lemma414PositiveSide × Lemma414PositiveSide →
      Lemma414SideOutput × Lemma414SideOutput :=
    fun c => ((Sum.inr c.1 : Lemma414SideOutput),
      (Sum.inr c.2 : Lemma414SideOutput))
  have hEmbed : Measurable embed := measurable_of_countable _
  have hPos : Measurable (fun p => embed (selectedCutPastCuts x T k p)) :=
    hEmbed.comp hCuts
  have hZero : Measurable (fun _ : ℕ → ℤ × ℤ =>
      ((Sum.inl zeroEdgeMarkedPast : Lemma414SideOutput),
        (Sum.inl zeroEdgeMarkedPast : Lemma414SideOutput))) := measurable_const
  have hIte : Measurable (fun p =>
      if selectedCutTime T k p = 0 then
        (Sum.inl zeroEdgeMarkedPast, Sum.inl zeroEdgeMarkedPast)
      else embed (selectedCutPastCuts x T k p)) :=
    @Measurable.ite _ _ _ _ _ _ _
      (fun p => LinearOrder.toDecidableEq (selectedCutTime T k p) 0)
      hS hZero hPos
  unfold selectedCutPastSides
  simpa [embed] using hIte

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The first side component is measurable. -/
theorem measurable_selectedCutPastSides_fst
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) :
    Measurable (fun p => (selectedCutPastSides x T hT k p).1) :=
  (measurable_selectedCutPastSides x T hT k).fst

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
The second side component is measurable. -/
theorem measurable_selectedCutPastSides_snd
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) :
    Measurable (fun p => (selectedCutPastSides x T hT k p).2) :=
  (measurable_selectedCutPastSides x T hT k).snd

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
At selected time zero both sides are the distinct point branch. -/
theorem selectedCutPastSides_zero
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) (p : ℕ → ℤ × ℤ)
    (hzero : selectedCutTime T k p = 0) :
    selectedCutPastSides x T hT k p =
      (Sum.inl zeroEdgeMarkedPast, Sum.inl zeroEdgeMarkedPast) := by
  simp [selectedCutPastSides, hzero]

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
At positive selected time the two components are the existing positive cut classes. -/
theorem selectedCutPastSides_pos
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (k : ℕ) (p : ℕ → ℤ × ℤ)
    (hpos : 0 < selectedCutTime T k p) :
    selectedCutPastSides x T hT k p =
      (Sum.inr (selectedCutPastCuts x T k p).1,
        Sum.inr (selectedCutPastCuts x T k p).2) := by
  simp [selectedCutPastSides, ne_of_gt hpos]

end DirectedDistances.PaperProofs.Section4
