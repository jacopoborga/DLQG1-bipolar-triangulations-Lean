module

public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov




















public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

private theorem busemannVersion_congr_positive {ω η : ℕ → Fin 3}
    (h : ∀ i, ω (i + 1) = η (i + 1)) :
    busemannLDPMeasurableVersion ω = busemannLDPMeasurableVersion η := by
  classical
  have htail : (fun i => ω (i + 1)) = (fun i => η (i + 1)) := funext h
  have hw : codeWalk ω = codeWalk η := by
    funext n
    simp only [codeWalk, h]
  have hfst (a : ℤ) : codeFstFirstHit a ω = codeFstFirstHit a η := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).1 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hsnd (a : ℤ) : codeSndFirstHit a ω = codeSndFirstHit a η := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).2 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hh : boundaryHitTimeTotal ω = boundaryHitTimeTotal η := by
    funext k
    simp only [boundaryHitTimeTotal, hfst, hsnd]
  have hid : busemannBoundaryIdTotal ω = busemannBoundaryIdTotal η := by
    funext k
    simp only [busemannBoundaryIdTotal, htail, hh]
  have hstage (n a b : ℕ) :
      busemannStageLdpCode ω n a b = busemannStageLdpCode η n a b := by
    exact congrArg (fun w : ℕ → Fin 3 => Int.ofNat
      ((DirectedDistances.KMSW.ldpSup
        (⟨a⟩ : DirectedDistances.KMSW.StagePresentVertex w n) ⟨b⟩).unbotD 0)) htail
  funext k
  simp only [busemannLDPMeasurableVersion, boundaryLdpDifference, hid, hstage]

private theorem measurable_busemannVersion_process :
    Measurable busemannLDPMeasurableVersion :=
  measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion

/-- The one-step shift resetting the dummy coordinate zero preserves the iid
code measure. Probabilistic helper for `prop:LDP-recursive-equation`
raw shift, which fails to preserve the deterministic coordinate zero. -/
theorem measurePreserving_codeShift_one :
    MeasurePreserving (codeShift 1) iidCodeMeasure iidCodeMeasure :=
  ⟨measurable_codeShift 1, map_codeShift 1⟩

/-- Resetting the dummy coordinate has no effect on the shifted Busemann
representative, pointwise on all codes. Helper for `prop:LDP-recursive-equation` -/
theorem busemannLDPMeasurableVersion_shift_eq (ω : ℕ → Fin 3) :
    busemannLDPMeasurableVersion (fun i => ω (i + 1)) =
      busemannLDPMeasurableVersion (codeShift 1 ω) := by
  apply busemannVersion_congr_positive
  intro i
  simp only [codeShift, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ite_false, Nat.add_comm 1]

/-- Full process equality in law on `ℤ → ℤ` with its product sigma-algebra:
`X¹` and `X` have the same law. Probabilistic input to
using the second-map indexing of `lem:LDP-relating-X1-X` -/
theorem iidCodeMeasure_map_busemannLDPMeasurableVersion_shift :
    iidCodeMeasure.map (fun ω => busemannLDPMeasurableVersion (fun i => ω (i + 1))) =
      iidCodeMeasure.map busemannLDPMeasurableVersion := by
  simp_rw [busemannLDPMeasurableVersion_shift_eq]
  change iidCodeMeasure.map (busemannLDPMeasurableVersion ∘ codeShift 1) = _
  rw [← Measure.map_map measurable_busemannVersion_process (measurable_codeShift 1),
    map_codeShift]

/-- Any pair of coordinates of `X¹` has the same joint law as the corresponding
pair of `X`. Helper for `prop:LDP-recursive-equation` -/
theorem iidCodeMeasure_map_busemannLDPMeasurableVersion_shift_pair (k k' : ℤ) :
    iidCodeMeasure.map (fun ω =>
      (busemannLDPMeasurableVersion (fun i => ω (i + 1)) k,
        busemannLDPMeasurableVersion (fun i => ω (i + 1)) k')) =
    iidCodeMeasure.map (fun ω =>
      (busemannLDPMeasurableVersion ω k, busemannLDPMeasurableVersion ω k')) := by
  have hp : Measurable (fun X : ℤ → ℤ => (X k, X k')) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply k')
  have hs : Measurable (fun ω : ℕ → Fin 3 =>
      busemannLDPMeasurableVersion (fun i => ω (i + 1))) :=
    measurable_busemannVersion_process.comp
      (measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1))
  have he := congrArg (fun μ : Measure (ℤ → ℤ) =>
    μ.map (fun X => (X k, X k')))
    iidCodeMeasure_map_busemannLDPMeasurableVersion_shift
  simpa only [Measure.map_map hp hs,
    Measure.map_map hp measurable_busemannVersion_process, Function.comp_def] using he

private theorem indepFun_firstCode_codeShift_one :
    (fun ω : ℕ → Fin 3 => ω 1) ⟂ᵢ[iidCodeMeasure] codeShift 1 := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hA : MeasurableSet[codePast 1] ((fun ω : ℕ → Fin 3 => ω 1) ⁻¹' s) := by
    exact ⟨(fun q : Fin 1 → Fin 3 => q 0) ⁻¹' s,
      (measurable_pi_apply 0) hs, rfl⟩
  rw [iidCodeMeasure_inter_codeShift_preimage 1 hA ht]
  rw [← Measure.map_apply (measurable_codeShift 1) ht, map_codeShift]

/-- The first source step `ω 1` is independent of the entire shifted Busemann
process `X¹`. This is independence from the first step, not independence of
the Busemann increments. Probabilistic input for `prop:LDP-recursive-equation` -/
theorem indepFun_firstCode_busemannLDPMeasurableVersion_shift :
    (fun ω : ℕ → Fin 3 => ω 1) ⟂ᵢ[iidCodeMeasure]
      (fun ω => busemannLDPMeasurableVersion (fun i => ω (i + 1))) := by
  simp_rw [busemannLDPMeasurableVersion_shift_eq]
  exact indepFun_firstCode_codeShift_one.comp measurable_id
    measurable_busemannVersion_process

end DirectedDistances.Recursive
