module

public import DirectedDistances.Recursive.BusemannPositiveHalfLaw
public import DirectedDistances.Probability.WholeLineGlueLaw
import all DirectedDistances.Probability.SkorokhodJ1WholeLineGlue
import DirectedDistances.Probability.SkorokhodFloorStep












public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result.
The actual LDP whole-line floor path on the existing iid code space, at scale `n + 1`. -/
@[expose] noncomputable def ldpBusemannWholeLinePath (n : ℕ)
    (ω : ℕ → Fin 3) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    (busemannLDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (busemannLDPMeasurableVersion ω j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩

/-- Helper toward Theorem 1.6; not a paper result.
Exact scaled whole-line evaluation, including negative indices. -/
theorem ldpBusemannWholeLinePath_apply (n : ℕ) (ω : ℕ → Fin 3) (t : ℝ) :
    (ldpBusemannWholeLinePath n ω).1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (busemannLDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ) := rfl

/-- Helper toward Theorem 1.6; not a paper result.
The existing positive half-path has value zero at zero for every code. -/
theorem ldpBusemannPositiveHalfPath_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (ldpBusemannPositiveHalfPath n ω).1 ⟨0, le_rfl⟩ = 0 := by
  rw [ldpBusemannPositiveHalfPath_apply]
  simp [busemannLDPMeasurableVersion_zero]

/-- Helper toward Theorem 1.6; not a paper result.
The actual positive half, with its proved zero initial condition retained in the carrier. -/
@[expose] noncomputable def ldpBusemannPositiveHalfPathZero (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ⟨ldpBusemannPositiveHalfPath n ω, ldpBusemannPositiveHalfPath_zero n ω⟩

/-- Helper toward Theorem 1.6; not a paper result.
The literal whole-line path restricts to the previously constructed positive half. -/
theorem ldpBusemannWholeLinePath_nonnegative (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    (ldpBusemannWholeLinePath n ω).1 t =
      (ldpBusemannPositiveHalfPathZero n ω).val.1 t := by
  exact (ldpBusemannPositiveHalfPath_apply n ω t).symm

/-- Helper toward Theorem 1.6; not a paper result.
Every zero-glued path has left limit zero at the origin. -/
theorem wholeLineGlueZero_leftLim_zero (p : CadlagLocalZero × CadlagLocalZero) :
    (wholeLineGlueZero p).1.leftLim 0 = 0 := by
  exact leftLim_eq_of_tendsto
    (wholeLineGlue_tendsto_left_zero p.1.val p.2.val p.1.property p.2.property)

/-- Helper toward Theorem 1.6; not a paper result.
The actual floor path has the scaled value at index `-1` as its left limit at zero. -/
theorem ldpBusemannWholeLinePath_leftLim_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (ldpBusemannWholeLinePath n ω).1.leftLim 0 =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (busemannLDPMeasurableVersion ω (-1) : ℝ) := by
  apply leftLim_eq_of_tendsto
  simpa [ldpBusemannWholeLinePath] using floorStep_left_limit
    (fun j => (busemannLDPMeasurableVersion ω j : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity) 0

/-- Helper toward Theorem 1.6; not a paper result.
Exact zero-gluing of the actual floor path would force its index `-1` value to vanish.
This is a necessary condition, not an assumption supplied to a convergence theorem. -/
theorem ldpBusemannWholeLinePath_eq_glueZero_implies (n : ℕ) (ω : ℕ → Fin 3)
    (p : CadlagLocalZero × CadlagLocalZero)
    (h : ldpBusemannWholeLinePath n ω = wholeLineGlueZero p) :
    busemannLDPMeasurableVersion ω (-1) = 0 := by
  have heq := congrArg (fun x : WholeLineCadlag => x.1.leftLim 0) h
  rw [ldpBusemannWholeLinePath_leftLim_zero, wholeLineGlueZero_leftLim_zero] at heq
  have ha : ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hz := (mul_eq_zero.mp heq).resolve_left ha
  exact_mod_cast hz

/-- Helper toward Theorem 1.6; not a paper result.
A nonzero value at index `-1` prevents exact identification with any zero-glued path. -/
theorem ldpBusemannWholeLinePath_ne_glueZero (n : ℕ) (ω : ℕ → Fin 3)
    (h : busemannLDPMeasurableVersion ω (-1) ≠ 0)
    (p : CadlagLocalZero × CadlagLocalZero) :
    ldpBusemannWholeLinePath n ω ≠ wholeLineGlueZero p := by
  intro heq
  exact h (ldpBusemannWholeLinePath_eq_glueZero_implies n ω p heq)

end DirectedDistances.Recursive
