module

public import DirectedDistances.KMSW.UIBOTBoundaryShift
public import DirectedDistances.Recursive.BusemannShiftLaw
public import DirectedDistances.Recursive.BusemannMeasurable

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/

/-! # Shifted boundary Busemann input for the cell LDP upper bound

These helpers transfer the measurable boundary LDP Busemann characterization
to each shifted code sequence and record equality in law of the resulting
integer-valued processes. They are not the paper result.

`BoundaryHitWitnesses` is a proposition. Each almost-sure statement supplies
a witness for its own code sequence; proof irrelevance lets a later assembly
reuse any witness for that same sequence. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive MeasureTheory




theorem codeShift_succ_eq_shiftedTail (n : ℕ) (ω : ℕ → Fin 3) :
    (fun i => codeShift n ω (i + 1)) = (fun i => ω (n + i + 1)) := by
  funext i
  simp [codeShift, Nat.add_assoc]




theorem shiftedTail_eq_baseTail (n : ℕ) (ω : ℕ → Fin 3) :
    (fun i => ω (n + i + 1)) =
      (fun i => (fun j => ω (j + 1)) (n + i)) := rfl





theorem iidCodes_ae_boundaryBusemannLDPMeasurableVersion :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ m,
          e < (kmswStage (fun i => ω (i + 1)) m).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) m).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) m).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin _ hfin)
          (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_existsUnique_eq_canonicalBusemannLDP,
    iidCodes_ae_busemannLDPMeasurableVersion_eq] with ω hω heq
  obtain ⟨hfin, h, X, hX, -, hcanon⟩ := hω
  refine ⟨hfin, h, ?_⟩
  have hversion : busemannLDPMeasurableVersion ω = X := heq.trans hcanon.symm
  rw [hversion]
  exact hX




theorem iidCodes_ae_boundaryBusemannLDPMeasurableVersion_shift (n : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ m,
          e < (kmswStage (fun i => ω (n + i + 1)) m).nextEdge ∧
          ((kmswStage (fun i => ω (n + i + 1)) m).west e = v ∨
            (kmswStage (fun i => ω (n + i + 1)) m).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (n + i + 1)),
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin _ hfin)
          (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion (codeShift n ω)) := by
  have hmap : ∀ᵐ η ∂iidCodeMeasure.map (codeShift n),
      ∃ hfin : ∀ v, {e : ℕ | ∃ m,
          e < (kmswStage (fun i => η (i + 1)) m).nextEdge ∧
          ((kmswStage (fun i => η (i + 1)) m).west e = v ∨
            (kmswStage (fun i => η (i + 1)) m).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin _ hfin)
          (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion η) := by
    simpa only [map_codeShift n] using
      iidCodes_ae_boundaryBusemannLDPMeasurableVersion
  have hae := (Measure.tendsto_ae_map
    (measurable_codeShift n).aemeasurable).eventually hmap
  filter_upwards [hae] with ω hω
  rw [codeShift_succ_eq_shiftedTail n ω] at hω
  exact hω

private theorem measurable_busemannVersion_process :
    Measurable busemannLDPMeasurableVersion :=
  measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion




theorem iidCodeMeasure_map_busemannLDPMeasurableVersion_codeShift (n : ℕ) :
    iidCodeMeasure.map (fun ω => busemannLDPMeasurableVersion (codeShift n ω)) =
      iidCodeMeasure.map busemannLDPMeasurableVersion := by
  change iidCodeMeasure.map (busemannLDPMeasurableVersion ∘ codeShift n) = _
  rw [← Measure.map_map measurable_busemannVersion_process
    (measurable_codeShift n), map_codeShift]





theorem iidCodeMeasure_busemannCodeShift_preimage (n : ℕ)
    {S : Set (ℤ → ℤ)} (hS : MeasurableSet S) :
    iidCodeMeasure {ω | busemannLDPMeasurableVersion (codeShift n ω) ∈ S} =
      iidCodeMeasure {ω | busemannLDPMeasurableVersion ω ∈ S} := by
  change iidCodeMeasure
      ((busemannLDPMeasurableVersion ∘ codeShift n) ⁻¹' S) =
    iidCodeMeasure (busemannLDPMeasurableVersion ⁻¹' S)
  rw [← Measure.map_apply
      (measurable_busemannVersion_process.comp (measurable_codeShift n)) hS,
    ← Measure.map_apply measurable_busemannVersion_process hS]
  exact congrArg (fun μ : Measure (ℤ → ℤ) => μ S)
    (iidCodeMeasure_map_busemannLDPMeasurableVersion_codeShift n)

end DirectedDistances.PaperProofs.Section7
