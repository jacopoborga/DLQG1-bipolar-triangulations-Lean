module

public import DirectedDistances.Paper.Section4.RenewalTime
public import DirectedDistances.PaperProofs.Section4.ThinIndependenceFinal
public import DirectedDistances.PaperProofs.Section4.ThinSideCodeFidelity
public import DirectedDistances.PaperProofs.Section4.ThinSideSuccessorRestriction
import DirectedDistances.PaperProofs.Section4.RenewalTimeCharacterization

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.Paper.Section4 DirectedDistances.RandomWalk
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical renewal time satisfies the literal positive success-time property. -/
theorem renewalTime_positiveSuccessTime :
    ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (renewalTime m p) := by
  intro p m
  exact (renewalTime_characterization m p).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical left and right codes are independent under the conditioned path law. -/
theorem thin_side_codes_indep_renewal (x : XDP) :
    IndepFun
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left)
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)
      (conditionedVectorPathLaw 0 0) := by
  exact thin_side_codes_indep_conditioned
    x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Realization and finite isomorphism assembly give whole-code geometric fidelity. -/
theorem thinSideCodeGeometricFidelity_renewal_of_realization
    (x : XDP)
    (hreal : SourceAncestorCutRealization x renewalTime
      renewalTime_positiveSuccessTime) :
    ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime := by
  exact
    (thinSideCodeGeometricFidelity_iff_assembly
      (x := x) (T := renewalTime)
      (hT := renewalTime_positiveSuccessTime) hreal).2
      (geometricAncestorIsoAssembly_proved
        (x := x) (T := renewalTime)
        (hT := renewalTime_positiveSuccessTime))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The code package includes independence, fidelity, measurability, and invariant
factorization for every inhabited codomain. Source: -/
theorem thin_ind_renewal_package_of_realization
    (x : XDP)
    (hreal : SourceAncestorCutRealization x renewalTime
      renewalTime_positiveSuccessTime) :
    IndepFun
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left)
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)
        (conditionedVectorPathLaw 0 0) ∧
      ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime ∧
      Measurable (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left) ∧
      Measurable (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right) ∧
      (∀ {β : Type*} [Nonempty β] (a : ThinMapSide)
        (f : selectedCutCoherentDomain x renewalTime
          renewalTime_positiveSuccessTime → β),
        IsGeometricRestrictionInvariant x renewalTime
          renewalTime_positiveSuccessTime a f →
        ∃ F : (ℕ → Option FiniteThinMap) → β,
          ∀ q, f q = F
            (thinSideCode x renewalTime renewalTime_positiveSuccessTime a q.1)) := by
  refine ⟨thin_side_codes_indep_renewal x,
    thinSideCodeGeometricFidelity_renewal_of_realization x hreal,
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left,
    measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right,
    ?_⟩
  intro β hβ a f hf
  exact geometricRestrictionInvariant_factorsThrough_code
    (x := x) (T := renewalTime)
    (hT := renewalTime_positiveSuccessTime) hreal a f hf

end DirectedDistances.PaperProofs.Section4
