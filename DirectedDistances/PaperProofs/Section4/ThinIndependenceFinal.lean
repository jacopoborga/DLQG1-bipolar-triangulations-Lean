module

public import DirectedDistances.PaperProofs.Section4.ThinCutCommonPrefixFamily
public import DirectedDistances.PaperProofs.Section4.ThinDecoderAssembly

/-! # Independence of the whole thin truncation codes

Helpers toward Proposition 4.7 (`prop-thin-ind`),
marked thin-map classes. Identification with the geometric infinite side submaps is
a separate obligation: `ThinMapExhaustion.lean:13-64` records the missing interior
exhaustion, geometric representability and one-cut identification. No independence
of geometric side submaps is claimed by the code independence theorems below. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap MeasureTheory ProbabilityTheory
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "ThinCode" => (ℕ → Option FiniteThinMap)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The entire left and right truncation sequences are independent on the conull coherent
premise beyond the proved `halfTruncateCutEqLeastGood_holds`. -/
theorem thin_side_codes_indep
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    IndepFun (fun q s => thinTruncationAt x T hT .left s q)
      (fun q s => thinTruncationAt x T hT .right s q)
      ((conditionedVectorPathLaw 0 0).comap
        (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) := by
  apply thinIndependence_of_cumulativeThinCodes x T hT
    (halfTruncateCutEqLeastGood_holds x T hT)
  · exact measurable_iSup_wholeCode none
      (fun s => measurable_thinTruncationAt x T hT .left s)
  · exact measurable_iSup_wholeCode none
      (fun s => measurable_thinTruncationAt x T hT .right s)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The whole side code, extended by the constantly absent code off the conull coherent -/
@[expose] noncomputable def thinSideCode
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (p : Ω) : ThinCode :=
  if hp : p ∈ selectedCutCoherentDomain x T hT then
    fun s => thinTruncationAt x T hT a s ⟨p, hp⟩
  else fun _ => none

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The extension agrees pointwise with the original code on its domain. -/
theorem thinSideCode_coe
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) :
    thinSideCode x T hT a q.1 = fun s => thinTruncationAt x T hT a s q := by
  simp only [thinSideCode, dite_eq_left q.2]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The extended whole side code is measurable for the product sigma-algebra. -/
theorem measurable_thinSideCode
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) : Measurable (thinSideCode x T hT a) := by
  exact (measurable_pi_iff.mpr
    (fun s => measurable_thinTruncationAt x T hT a s)).dite measurable_const
    (selectedCutCoherentDomain_measurable_conull x T hT).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The extended whole left and right codes are independent under the full conditioned
path law. The extension changes nothing on the conull coherent domain. -/
theorem thin_side_codes_indep_conditioned
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    IndepFun (thinSideCode x T hT .left) (thinSideCode x T hT .right)
      (conditionedVectorPathLaw 0 0) := by
  let μ := conditionedVectorPathLaw 0 0
  let ν := μ.comap (Subtype.val : selectedCutCoherentDomain x T hT → Ω)
  have hD := selectedCutCoherentDomain_measurable_conull x T hT
  have hmap : ν.map Subtype.val = μ := by
    rw [map_comap_subtype_coe hD.1]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hD.2)
  have hemb := MeasurableEmbedding.subtype_coe hD.1
  change IndepFun (thinSideCode x T hT .left) (thinSideCode x T hT .right) μ
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  rw [← hmap, hemb.map_apply, hemb.map_apply, hemb.map_apply]
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def,
    thinSideCode_coe] using
    (thin_side_codes_indep x T hT).measure_inter_preimage_eq_mul s t hs ht

end DirectedDistances.PaperProofs.Section4
