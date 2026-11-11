module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
public import DirectedDistances.Recursive.BusemannSdpUnconditional
public import DirectedDistances.Recursive.LDPDiscriminantBridge
public import DirectedDistances.Recursive.SDPSideSelection
public import DirectedDistances.PaperProofs.Section6.Tauberian

public section
namespace DirectedDistances.PaperProofs.Section6

open MeasureTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7
open scoped Topology

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. Transfer an arbitrary pair of LDP evaluations. -/
theorem incrementLawsIdentified_ldp_probability (i j k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedLDPBusemann W i - identifiedLDPBusemann W j = k} =
      iidCodeMeasure.real
        {w | busemannLDPMeasurableVersion w i - busemannLDPMeasurableVersion w j = k} := by
  have hevent : MeasurableSet
      {w | busemannLDPMeasurableVersion w i - busemannLDPMeasurableVersion w j = k} :=
    measurableSet_eq_fun
      ((measurable_busemannLDPMeasurableVersion i).sub
        (measurable_busemannLDPMeasurableVersion j)) measurable_const
  calc
    _ = wholePlaneIIDCodeMeasure.real
        {W | busemannLDPMeasurableVersion (shiftedCodePath W 0) i -
          busemannLDPMeasurableVersion (shiftedCodePath W 0) j = k} := by
      apply measureReal_congr
      filter_upwards [identifiedLDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. Transfer an arbitrary pair of SDP evaluations. -/
theorem incrementLawsIdentified_sdp_probability (i j k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedSDPBusemann W i - identifiedSDPBusemann W j = k} =
      iidCodeMeasure.real
        {w | busemannSDPMeasurableVersion w i - busemannSDPMeasurableVersion w j = k} := by
  have hevent : MeasurableSet
      {w | busemannSDPMeasurableVersion w i - busemannSDPMeasurableVersion w j = k} :=
    measurableSet_eq_fun
      ((measurable_busemannSDPMeasurableVersion i).sub
        (measurable_busemannSDPMeasurableVersion j)) measurable_const
  calc
    _ = wholePlaneIIDCodeMeasure.real
        {W | busemannSDPMeasurableVersion (shiftedCodePath W 0) i -
          busemannSDPMeasurableVersion (shiftedCodePath W 0) j = k} := by
      apply measureReal_congr
      filter_upwards [identifiedSDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The left LDP atom probabilities on the whole-plane law. -/
@[expose] noncomputable def incrementLawsIdentified_ldpF : ℤ → ℝ :=
  ldpF wholePlaneIIDCodeMeasure identifiedLDPBusemann

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The right LDP atom probabilities on the whole-plane law. -/
@[expose] noncomputable def incrementLawsIdentified_ldpG : ℤ → ℝ :=
  ldpG wholePlaneIIDCodeMeasure identifiedLDPBusemann

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The left SDP atom probabilities on the whole-plane law. -/
@[expose] noncomputable def incrementLawsIdentified_sdpF : ℤ → ℝ :=
  SDPMasterFromLaw.sdpF wholePlaneIIDCodeMeasure identifiedSDPBusemann

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The right SDP atom probabilities on the whole-plane law. -/
@[expose] noncomputable def incrementLawsIdentified_sdpG : ℤ → ℝ :=
  SDPMasterFromLaw.sdpG wholePlaneIIDCodeMeasure identifiedSDPBusemann

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The entire left LDP law equals the code-level f. -/
theorem incrementLawsIdentified_ldpF_eq :
    incrementLawsIdentified_ldpF = ldpF iidCodeMeasure busemannLDPMeasurableVersion := by
  funext k
  simpa only [incrementLawsIdentified_ldpF, ldpF, ldpIncrement, zero_sub] using
    incrementLawsIdentified_ldp_probability 0 (-1) k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The entire right LDP law equals the code-level g. -/
theorem incrementLawsIdentified_ldpG_eq :
    incrementLawsIdentified_ldpG = ldpG iidCodeMeasure busemannLDPMeasurableVersion := by
  funext k
  simpa only [incrementLawsIdentified_ldpG, ldpG, ldpIncrement, sub_self] using
    incrementLawsIdentified_ldp_probability 1 0 k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The entire left SDP law equals the code-level f. -/
theorem incrementLawsIdentified_sdpF_eq :
    incrementLawsIdentified_sdpF =
      SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion := by
  funext k
  simpa only [incrementLawsIdentified_sdpF, SDPMasterFromLaw.sdpF,
    SDPMasterFromLaw.increment, zero_sub] using
    incrementLawsIdentified_sdp_probability 0 (-1) k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The entire right SDP law equals the code-level g. -/
theorem incrementLawsIdentified_sdpG_eq :
    incrementLawsIdentified_sdpG =
      SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion := by
  funext k
  simpa only [incrementLawsIdentified_sdpG, SDPMasterFromLaw.sdpG,
    SDPMasterFromLaw.increment, sub_self] using
    incrementLawsIdentified_sdp_probability 1 0 k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The left LDP increment has the code-level atom law. -/
theorem incrementLawsIdentified_ldp_left_atom (k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedLDPBusemann W 0 - identifiedLDPBusemann W (-1) = k} =
      ldpF iidCodeMeasure busemannLDPMeasurableVersion k := by
  simpa only [ldpF, ldpIncrement, zero_sub] using
    incrementLawsIdentified_ldp_probability 0 (-1) k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The right LDP increment has the code-level atom law. -/
theorem incrementLawsIdentified_ldp_right_atom (k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedLDPBusemann W 1 - identifiedLDPBusemann W 0 = k} =
      ldpG iidCodeMeasure busemannLDPMeasurableVersion k := by
  simpa only [ldpG, ldpIncrement, sub_self] using
    incrementLawsIdentified_ldp_probability 1 0 k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The left SDP increment has the code-level atom law. -/
theorem incrementLawsIdentified_sdp_left_atom (k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedSDPBusemann W 0 - identifiedSDPBusemann W (-1) = k} =
      SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion k := by
  simpa only [SDPMasterFromLaw.sdpF, SDPMasterFromLaw.increment, zero_sub] using
    incrementLawsIdentified_sdp_probability 0 (-1) k

/-- Helper toward Section 6 (recursive.tex, eq:den-dist-f-g) on the identified Busemann
increments; not a paper result. The right SDP increment has the code-level atom law. -/
theorem incrementLawsIdentified_sdp_right_atom (k : ℤ) :
    wholePlaneIIDCodeMeasure.real
        {W | identifiedSDPBusemann W 1 - identifiedSDPBusemann W 0 = k} =
      SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion k := by
  simpa only [SDPMasterFromLaw.sdpG, SDPMasterFromLaw.increment, sub_self] using
    incrementLawsIdentified_sdp_probability 1 0 k

section LDP

local notation "f" => incrementLawsIdentified_ldpF
local notation "g" => incrementLawsIdentified_ldpG

/-- Helper toward Section 6 (recursive.tex, prop:LDP-recursive-equation) on the identified
Busemann increments; not a paper result. Transfer the unconditional master recursion. -/
theorem incrementLawsIdentified_ldp_recursive_equation :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) := by
  rw [incrementLawsIdentified_ldpF_eq, incrementLawsIdentified_ldpG_eq]
  exact ldp_master_equation_ldpCode

/-- Helper toward Section 6 (recursive.tex, lem:Y-not-const) on the identified Busemann
increments; not a paper result. No atom has mass one, and zero has positive mass. -/
theorem incrementLawsIdentified_ldp_nondegenerate :
    (∀ c : ℤ, f c < 1) ∧ 0 < f 0 := by
  rw [incrementLawsIdentified_ldpF_eq]
  exact ldp_pmf_nondegenerate_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsymLdp_ldpCode) busemann_ldpG_zero_of_nonneg
    ldp_master_equation_ldpCode

/-- Helper toward Section 6 (recursive.tex, lem:nonreal2) on the identified Busemann
increments; not a paper result. The discriminant is negative and the actual shifted
transform is nonreal on one positive interval. This transfers these two clauses only. -/
theorem incrementLawsIdentified_ldp_nonreal :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      (3 * (integerCF f t).re - 1) ^ 2 - 4 * (integerCF f t).re ^ 3 < 0 ∧
      (ldpHat f t).im ≠ 0 := by
  rw [incrementLawsIdentified_ldpF_eq]
  exact ldp_discriminant_and_actual_transform_nonreal_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsymLdp_ldpCode) busemann_ldpG_zero_of_nonneg
    ldp_master_equation_ldpCode

/-- Helper toward Section 6 (recursive.tex, prop:asympt-exp2) on the identified Busemann
increments; not a paper result. All three right-hand characteristic expansions share
one kappa and one coefficient, with the source signs and exponents. -/
theorem incrementLawsIdentified_ldp_expansions :
    let kappa : ℝ := 3 + f 0
    let a : ℝ := (kappa / 2) ^ (1 / 3 : ℝ)
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    0 < kappa ∧
      ((fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ))) ∧
      ((fun t : ℝ => negativeCF g t - 1 -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ))) := by
  rw [incrementLawsIdentified_ldpF_eq, incrementLawsIdentified_ldpG_eq]
  have hF := ldp_real_transform_expansion_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsymLdp_ldpCode) busemann_ldpG_zero_of_nonneg
    ldp_master_equation_ldpCode
  have hside := ldp_side_expansions_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsymLdp_ldpCode) busemann_ldpG_zero_of_nonneg
    ldp_master_equation_ldpCode
  exact ⟨hF.1, hF.2, hside.1, hside.2⟩

end LDP

section SDP

open DirectedDistances.Recursive.SDPExpansion

local notation "f" => incrementLawsIdentified_sdpF
local notation "g" => incrementLawsIdentified_sdpG

/-- Helper toward Section 6 (recursive.tex, prop:SDP-recursive-equation) on the identified
Busemann increments; not a paper result. Transfer the unconditional master recursion. -/
theorem incrementLawsIdentified_sdp_recursive_equation :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  exact sdp_master_equation_sdpCode

/-- Helper toward Section 6 (recursive.tex, lem:Y-not-const2) on the identified Busemann
increments; not a paper result. No left atom has mass one; f(0) and g(-1) are positive. -/
theorem incrementLawsIdentified_sdp_nondegenerate :
    (∀ c : ℤ, f c < 1) ∧ 0 < f 0 ∧ 0 < g (-1) := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  exact sdp_pmf_nondegenerate_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsymSdp_sdpCode) busemann_sdpG_zero_below
    sdp_master_equation_sdpCode

/-- Helper toward Section 6 (recursive.tex, prop:asympt-exp) on the identified Busemann
increments; not a paper result. Kappa vanishes, g(-1) is positive, and all three
right-hand characteristic expansions have the source coefficients. -/
theorem incrementLawsIdentified_sdp_expansions :
    let kappa : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    let b : ℝ := g (-1) ^ (2 / 3 : ℝ)
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    kappa = 0 ∧ 0 < g (-1) ∧
      ((fun t : ℝ => SDPExpansion.integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => SDPExpansion.negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) +
        (((2 * g (-1) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
        (dPlus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))) ∧
      ((fun t : ℝ => sdpCF g t - 1 -
        (dMinus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))) := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  have hkappa := sdp_tail_asymptotics_explicit_sdpCode.1
  have hF := sdp_real_transform_dichotomy_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsymSdp_sdpCode) busemann_sdpG_zero_below
    sdp_master_equation_sdpCode
  have hside := sdp_kappa_zero_side_expansions_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsymSdp_sdpCode) busemann_sdpG_zero_below
    sdp_master_equation_sdpCode
    hkappa
  rcases hF.2 with hzero | hpos
  · exact ⟨hkappa, hF.1, hzero.2, hside.1, hside.2⟩
  · exact False.elim ((ne_of_gt hpos.1) hkappa)

end SDP
end DirectedDistances.PaperProofs.Section6
