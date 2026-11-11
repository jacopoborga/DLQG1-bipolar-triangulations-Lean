module

public import DirectedDistances.PaperProofs.Section7.CellLDPLowerIndSym
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerAssembly
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperAssembly
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperGoodEvent
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerIncrementTail
public import DirectedDistances.PaperProofs.Section7.CellLDPReduction
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerGeodesic
public import DirectedDistances.PaperProofs.Section7.BoltzmannLDPUpperConditional
import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementReflectLdp
import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose4
import DirectedDistances.Recursive.HLRLdpFinal

/-! Supporting lemmas for paper labels `lem-boltzmann-ldp-upper`, `lem-cell-ldp-lower`, `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/

/- # Section 7 LDP helpers with proved code-law inputs

These are code-level helpers toward Lemmas 7.2, 7.4 and 7.10, not paper results.
The scope is every public theorem with an independence or symmetry premise in the
Section 7 LDP modules. Deterministic helpers without those premises are reused unchanged.
Symmetry uses faced-shell transport composed with `hsym_ldp_of_facedShellTransport`.
Independence uses `ldpIncrements_iIndep_proved`. No measurable-intrinsic-data
premise is used. Generic measures and profiles are specialized to `iidCodeMeasure`
and `busemannLDPMeasurableVersion`.

OPEN for `ldp_nonpos_index_positive_tail_ldpRest` and
`ldp_lower_product_step_ldpRest`: `hc`, `hx₀`, and `habs` at the prescribed
parameters `c`, `x₀`. These are explicit parameter-dependent premises, not claims
by `ldp_habs_of_ind_sym_ldpCode`. No fixed constants are silently selected for the
statements whose conclusions mention `c` or `x₀`.

For the four cell lower-bound assemblies, the constants and geodesic inputs do not
occur in the conclusion; their proved existential forms discharge them completely.
Ordinary range conditions on `ε` remain explicit parameters.
from compilation of these helpers. Existing source issue dispositions remain in force. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap

/-- Helper (code level, LDP) toward Lemma 7.2; not a paper result.
The index-zero symmetry input follows by composition of proved faced-shell transport. -/
private theorem section7_ldp_code_symmetry :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) :=
  hsym_ldp_of_facedShellTransport incrementClose4_facedShellTransport

/-- Helper (code level, LDP) toward Lemma 7.2; not a paper result.
Measurability of each integer-valued increment of the measurable representative. -/
private theorem section7_ldp_increment_measurable (k : ℤ) :
    Measurable (fun ω => ldpIncrement busemannLDPMeasurableVersion k ω) :=
  (measurable_busemannLDPMeasurableVersion k).sub
    (measurable_busemannLDPMeasurableVersion (k - 1))

/-- Helper (code level, LDP) toward Lemma 7.2; not a paper result.
Source helper documentation (the original conditional status is historical):
Only Theorem 1.7(i) (`hind`) and 1.7(iv) at index 0 (`hsym`) remain; the
absolute-tail asymptotic is converted using a strictly smaller constant.
The source-identification gates F1/F4 apply to the measurable Busemann
representative. This is not the paper result. -/
theorem ldp_habs_of_ind_sym_ldpCode :
    ∃ c x₀ : ℝ, 0 < c ∧ 0 < x₀ ∧ ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤ iidCodeMeasure.real
        {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|} := by
  exact ldp_habs_of_ind_sym ldpIncrements_iIndep_proved section7_ldp_code_symmetry






theorem cell_ldp_lower_of_ind_sym_ldpCode
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
        1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
          c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
          iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
            (fun i => ω (i + 1)) n, ∃ q : Path a b,
              A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  exact cell_ldp_lower_of_ind_sym ldpIncrements_iIndep_proved
    section7_ldp_code_symmetry ε hε





theorem cell_ldp_lower_conditional_ldpCode
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  exact cell_ldp_lower_of_ind_sym_ldpCode ε hε







theorem cell_ldp_upper_conditional_ldpCode :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  exact cell_ldp_upper_conditional ldpIncrements_iIndep_proved
    busemannLDPMeasurableVersion_left_stationary section7_ldp_code_symmetry






theorem cell_ldp_upper_good_event_ldpCode :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω : ℕ → Fin 3 |
            (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
              ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
                A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
            ∀ l : ℤ,
              |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
              |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
                  A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
              |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
                  A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} := by
  exact cell_ldp_upper_good_event ldpIncrements_iIndep_proved
    busemannLDPMeasurableVersion_left_stationary section7_ldp_code_symmetry







theorem ldp_nonpos_index_positive_tail_ldpRest
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|}) :
    ∀ k : ℤ, k ≤ 0 → ∀ x ≥ x₀,
      c * x ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x ≤ (ldpIncrement busemannLDPMeasurableVersion k ω : ℝ)} := by
  exact ldp_nonpos_index_positive_tail (μ := iidCodeMeasure) (Y := busemannLDPMeasurableVersion)
    section7_ldp_increment_measurable
    busemannLDPMeasurableVersion_left_stationary section7_ldp_code_symmetry
    hc hx₀ habs







theorem ldp_lower_product_step_ldpRest
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|})
    (ε : ℝ) :
    ∃ c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      x₀ ≤ A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) →
      1 - c₂ * Real.exp (-(c₃ * A ^ ε)) ≤
        iidCodeMeasure.real {ω | ∃ j ∈ Finset.range
          ⌊A ^ (-2 / 3 + ε : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤
            (ldpIncrement busemannLDPMeasurableVersion (-((j : ℤ) + 1)) ω : ℝ)} := by
  exact ldp_lower_product_step (μ := iidCodeMeasure) (Y := busemannLDPMeasurableVersion)
    section7_ldp_increment_measurable
    (fun j => (measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      (section7_ldp_increment_measurable (-((j : ℤ) + 1))))
    (cell_ldp_negative_subfamily_independent ldpIncrements_iIndep_proved)
    busemannLDPMeasurableVersion_left_stationary section7_ldp_code_symmetry
    hc hx₀ habs ε






theorem cell_ldp_upper_of_items_ldpCode :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex
            (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤
              ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  exact cell_ldp_upper_of_items ldpIncrements_iIndep_proved section7_ldp_code_symmetry

/-- Helper (code level, LDP) toward Lemma 7.2; not a paper result.
Source helper documentation (the original conditional status is historical):
The negative-side subfamily inherits independence from the full integer
family by injective precomposition and measurable casting to `ℝ`. -/
theorem cell_ldp_negative_subfamily_independent_ldpCode :
    iIndepFun
      (fun (j : ℕ) ω =>
        (ldpIncrement busemannLDPMeasurableVersion (-((j : ℤ) + 1)) ω : ℝ))
      iidCodeMeasure := by
  exact cell_ldp_negative_subfamily_independent ldpIncrements_iIndep_proved















theorem cell_ldp_lower_of_items_ldpCode
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  exact cell_ldp_lower_of_ind_sym_ldpCode ε hε







theorem cell_ldp_lower_of_items_geodesic_ldpCode
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  exact cell_ldp_lower_of_ind_sym_ldpCode ε hε

/-- Helper (code level, LDP) toward Lemma 7.10; not a paper result.
Source helper documentation (the original conditional status is historical):
Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The cell and right-hit estimates hold jointly -/
theorem cellAndHit_intersection_probability_conditional_ldpCode :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        ∀ r : ℕ, 1 ≤ r →
          1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
            4 * (r : ℝ) / Real.sqrt n) ≤
            iidCodeMeasure.real
              ({ω : ℕ → Fin 3 |
                (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
                ∀ l : ℤ,
                  |l| ≤
                    ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
                  |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
                      A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
                  |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
                      A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} ∩
                {ω | ∃ k ≤ n,
                  R (fun i => ω (i + 1)) k = -(r : ℤ)}) := by
  exact cellAndHit_intersection_probability_conditional ldpIncrements_iIndep_proved
    section7_ldp_code_symmetry

/-- Helper (code level, LDP) toward Lemma 7.10; not a paper result.
Source helper documentation (the original conditional status is historical):
Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The cell event and a right hit control the marked stopped -/
theorem boltzmann_ldp_upper_conditional_ldpCode :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
        1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
          {q : RightVertexMarkedBoltzmannSpace r |
            (ldpLengthBase q.1.2.2.out.B : ℝ) ≤
              A * (r : ℝ) ^ (3 / 2 : ℝ)} := by
  exact boltzmann_ldp_upper_conditional ldpIncrements_iIndep_proved
    section7_ldp_code_symmetry

end DirectedDistances.PaperProofs.Section7
