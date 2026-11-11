module

public import DirectedDistances.KMSW.FutureMapHatLawShift
public import DirectedDistances.KMSW.PrimedFaceOrbitEquiv

/-! # Primed future-map law transport

Helpers toward Proposition 5.1 and the primed half of Lemma 5.13 -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk

/-- The padded shifted path's raw tail is the zero-start translated stream. -/
theorem futureMapShiftedCodePath_rawStream_eq_shiftedStream
    (n : ℤ) (W : ℤ → Fin 3) :
    (fun i => futureMapShiftedCodePath n W (i + 1)) =
      shiftedStream (fun k => W (k + n)) 0 := by
  rw [futureMapShiftedCodePath_tail]
  rfl

/-- Transfer any almost-sure property of the one-sided raw iid stream to all
integer-shifted future raw streams, recording their exact translated-stream -/
theorem wholePlane_ae_futureMapShift_rawStream_of_iid_ae
    {P : (ℕ → Fin 3) → Prop}
    (hP : ∀ᵐ ω ∂iidCodeMeasure, P (fun i => ω (i + 1))) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      P (fun i => futureMapShiftedCodePath n W (i + 1)) ∧
        (fun i => futureMapShiftedCodePath n W (i + 1)) =
          shiftedStream (fun k => W (k + n)) 0 := by
  apply ae_all_iff.mpr
  intro n
  have hmap : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n),
      P (fun i => ω (i + 1)) := by
    rw [futureMapShiftedCodePath_law n]
    exact hP
  have hpull := (Measure.tendsto_ae_map
    (measurable_futureMapShiftedCodePath n).aemeasurable).eventually hmap
  filter_upwards [hpull] with W hW
  exact ⟨hW, futureMapShiftedCodePath_rawStream_eq_shiftedStream n W⟩

/-- On the flow-line-hit event, the primed code observation is exactly the
corrected primed code of the raw future stream. Source: -/
theorem futureMapShift_hatLawPrimedCodes_eq_primedCode
    (n : ℤ) (W : ℤ → Fin 3)
    (h : HasFlowLineHits
      (fun i => futureMapShiftedCodePath n W (i + 1))) :
    hatLawPrimedCodes (futureMapShiftedCodePath n W) =
      primedCode
        (primedSimInput (fun i => futureMapShiftedCodePath n W (i + 1))) h := by
  simp only [hatLawPrimedCodes, dite_eq_left h]

/-- At every integer shift, the iid primed finite-face event supplies the
shared flow-hit, finite-incidence and boundary-hit witnesses, and the primed
code observation agrees with the corrected primed code built from that raw
stream. The face-orbit clauses are precisely those of the x113 event; no
exterior identification is asserted. Source: -/
theorem wholePlane_ae_futureMapShift_primedFiniteFaceOrbit_identification :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      ∃ (h : HasFlowLineHits u) (hfin : primedLimitFiniteIncidence u)
        (hb : BoundaryHitWitnesses u),
        primedCreationTriangle_orientedImageGoal u h hfin hb ∧
        primedCreationTriangle_orientedBordersGoal u h hfin hb ∧
        (∀ d : ℕ × Bool,
          {e | (kmswInfFaceSucc (primedCode (primedSimInput u) h)
            (primedCode_finiteIncidence u h hfin)).SameCycle d e}.Finite →
          ∃ F : PlaneFaces (mhatPrimeDrawing u hfin hb (monotone_family_all u)),
            ∀ e,
              (mhatPrimeDrawing u hfin hb (monotone_family_all u)).dartBorders
                (primedGeometricDartEquiv u h hfin hb e) F.val ↔
              (kmswInfFaceSucc (primedCode (primedSimInput u) h)
                (primedCode_finiteIncidence u h hfin)).SameCycle d e) ∧
        hatLawPrimedCodes (futureMapShiftedCodePath n W) =
          primedCode (primedSimInput u) h := by
  let P : (ℕ → Fin 3) → Prop := fun u =>
    ∃ (h : HasFlowLineHits u) (hfin : primedLimitFiniteIncidence u)
      (hb : BoundaryHitWitnesses u),
      primedCreationTriangle_orientedImageGoal u h hfin hb ∧
      primedCreationTriangle_orientedBordersGoal u h hfin hb ∧
      (∀ d : ℕ × Bool,
        {e | (kmswInfFaceSucc (primedCode (primedSimInput u) h)
          (primedCode_finiteIncidence u h hfin)).SameCycle d e}.Finite →
        ∃ F : PlaneFaces (mhatPrimeDrawing u hfin hb (monotone_family_all u)),
          ∀ e,
            (mhatPrimeDrawing u hfin hb (monotone_family_all u)).dartBorders
              (primedGeometricDartEquiv u h hfin hb e) F.val ↔
            (kmswInfFaceSucc (primedCode (primedSimInput u) h)
              (primedCode_finiteIncidence u h hfin)).SameCycle d e)
  have hP : ∀ᵐ ω ∂iidCodeMeasure, P (fun i => ω (i + 1)) := by
    simpa only [P] using iidCodes_ae_primedFiniteFaceOrbit_identification
  have htransfer := wholePlane_ae_futureMapShift_rawStream_of_iid_ae hP
  filter_upwards [htransfer] with W hW
  intro n
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  obtain ⟨hP_n, _hraw⟩ := hW n
  obtain ⟨h, hfin, hb, himage, hborders, horbits⟩ := hP_n
  exact ⟨h, hfin, hb, himage, hborders, horbits,
    futureMapShift_hatLawPrimedCodes_eq_primedCode n W h⟩

end DirectedDistances.PaperProofs.Section5
