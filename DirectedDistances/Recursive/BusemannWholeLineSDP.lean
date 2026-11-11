module

public import DirectedDistances.Recursive.BusemannPositiveHalfLawSDP
public import DirectedDistances.Probability.WholeLineGlueLaw
import all DirectedDistances.Probability.SkorokhodJ1WholeLineGlue
import DirectedDistances.Probability.SkorokhodFloorStep













public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result.
The actual SDP whole-line floor path on the existing iid code space, at scale -/
@[expose] noncomputable def sdpBusemannWholeLinePath (n : ℕ)
    (ω : ℕ → Fin 3) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (busemannSDPMeasurableVersion ω j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩

/-- Helper toward Theorem 1.6; not a paper result.
Exact scaled whole-line evaluation, including negative indices. -/
theorem sdpBusemannWholeLinePath_apply (n : ℕ) (ω : ℕ → Fin 3) (t : ℝ) :
    (sdpBusemannWholeLinePath n ω).1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ) := rfl

/-- Helper toward Theorem 1.6; not a paper result.
The existing positive half-path has value zero at zero for every code. -/
theorem sdpBusemannPositiveHalfPath_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (sdpBusemannPositiveHalfPath n ω).1 ⟨0, le_rfl⟩ = 0 := by
  rw [sdpBusemannPositiveHalfPath_apply]
  simp [busemannSDPMeasurableVersion_zero]

/-- Helper toward Theorem 1.6; not a paper result.
The actual positive half, with its proved zero initial condition retained in the -/
@[expose] noncomputable def sdpBusemannPositiveHalfPathZero (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ⟨sdpBusemannPositiveHalfPath n ω, sdpBusemannPositiveHalfPath_zero n ω⟩

/-- Helper toward Theorem 1.6; not a paper result.
The literal whole-line path restricts to the previously constructed positive -/
theorem sdpBusemannWholeLinePath_nonnegative (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    (sdpBusemannWholeLinePath n ω).1 t =
      (sdpBusemannPositiveHalfPathZero n ω).val.1 t := by
  exact (sdpBusemannPositiveHalfPath_apply n ω t).symm

/-- Helper toward Theorem 1.6; not a paper result.
Every zero-glued path has left limit zero at the origin. -/
theorem wholeLineGlueZero_leftLim_zero (p : CadlagLocalZero × CadlagLocalZero) :
    (wholeLineGlueZero p).1.leftLim 0 = 0 := by
  exact leftLim_eq_of_tendsto
    (wholeLineGlue_tendsto_left_zero p.1.val p.2.val p.1.property p.2.property)

/-- Helper toward Theorem 1.6; not a paper result.
The actual floor path has the scaled value at index `-1` as its left limit at -/
theorem sdpBusemannWholeLinePath_leftLim_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (sdpBusemannWholeLinePath n ω).1.leftLim 0 =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (busemannSDPMeasurableVersion ω (-1) : ℝ) := by
  apply leftLim_eq_of_tendsto
  simpa [sdpBusemannWholeLinePath] using floorStep_left_limit
    (fun j => (busemannSDPMeasurableVersion ω j : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity) 0

/-- Helper toward Theorem 1.6; not a paper result.
Exact zero-gluing of the actual floor path would force its index `-1` value to
vanish. This is a necessary condition, not an assumption supplied to a -/
theorem sdpBusemannWholeLinePath_eq_glueZero_implies (n : ℕ) (ω : ℕ → Fin 3)
    (p : CadlagLocalZero × CadlagLocalZero)
    (h : sdpBusemannWholeLinePath n ω = wholeLineGlueZero p) :
    busemannSDPMeasurableVersion ω (-1) = 0 := by
  have heq := congrArg (fun x : WholeLineCadlag => x.1.leftLim 0) h
  rw [sdpBusemannWholeLinePath_leftLim_zero, wholeLineGlueZero_leftLim_zero] at heq
  have ha : ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hz := (mul_eq_zero.mp heq).resolve_left ha
  exact_mod_cast hz

/-- Helper toward Theorem 1.6; not a paper result.
A nonzero value at index `-1` prevents exact identification with any zero-glued -/
theorem sdpBusemannWholeLinePath_ne_glueZero (n : ℕ) (ω : ℕ → Fin 3)
    (h : busemannSDPMeasurableVersion ω (-1) ≠ 0)
    (p : CadlagLocalZero × CadlagLocalZero) :
    sdpBusemannWholeLinePath n ω ≠ wholeLineGlueZero p := by
  intro heq
  exact h (sdpBusemannWholeLinePath_eq_glueZero_implies n ω p heq)

end DirectedDistances.Recursive
