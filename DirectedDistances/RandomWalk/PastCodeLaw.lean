module

public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure
public import DirectedDistances.KMSW.DirectedContain
import Mathlib.Probability.Independence.InfinitePi

/-! # The reversed past-code law

Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
@[expose] def pastCode (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  fun i => Equiv.swap (0 : Fin 3) 1 (W (-1 - (i : ℤ)))

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
theorem measurable_pastCode : Measurable (fun W : ℤ → Fin 3 => pastCode W) := by
  apply measurable_pi_iff.2
  intro i
  exact (measurable_of_countable _).comp (measurable_pi_apply (-1 - (i : ℤ)))

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private def pastCodeTail (ω : ℕ → Fin 3) : ℕ → Fin 3 := fun i => ω (i + 1)

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private theorem measurable_pastCodeTail : Measurable pastCodeTail := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_pi_apply (i + 1)

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private theorem measurable_pastCodeInsertDummy : Measurable insertDummy := by
  apply measurable_pi_iff.2
  intro i
  by_cases hi : i = 0
  · simp [insertDummy, hi]
  · simpa [insertDummy, hi] using measurable_pi_apply (i - 1)

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private theorem uniformCodeMeasure_map_swap :
    uniformCodeMeasure.map (Equiv.swap (0 : Fin 3) 1) = uniformCodeMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hpre : (Equiv.swap (0 : Fin 3) 1) ⁻¹' ({x} : Set (Fin 3)) =
      {Equiv.swap (0 : Fin 3) 1 x} := by
    ext y
    fin_cases x <;> fin_cases y <;> simp [Equiv.swap_apply_def]
  rw [hpre]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
theorem wholePlaneIIDCodeMeasure_map_pastCode :
    wholePlaneIIDCodeMeasure.map pastCode =
      Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
  let raw : (ℤ → Fin 3) → (ℕ → Fin 3) := fun W i => W (-1 - (i : ℤ))
  let swap : (ℕ → Fin 3) → (ℕ → Fin 3) :=
    fun x i => Equiv.swap (0 : Fin 3) 1 (x i)
  have hinj : Function.Injective (fun i : ℕ => -1 - (i : ℤ)) := by
    intro i j hij
    have hcast : (-1 : ℤ) - (i : ℤ) = -1 - (j : ℤ) := by exact_mod_cast hij
    omega
  have hraw : wholePlaneIIDCodeMeasure.map raw =
      Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
    simpa [raw, wholePlaneIIDCodeMeasure] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℤ => uniformCodeMeasure) hinj)
  have hswap :
      (Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure)).map swap =
        Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
    rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniformCodeMeasure)
      (f := fun _ => Equiv.swap (0 : Fin 3) 1) (fun _ => measurable_of_countable _)]
    congr 1
    funext i
    exact uniformCodeMeasure_map_swap
  have hfun : pastCode = swap ∘ raw := by
    funext W i
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hraw]
  exact hswap

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private theorem iidCodeMeasure_eq_product_map_insertDummy :
    iidCodeMeasure =
      (Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure)).map insertDummy := by
  have hraw := wholePlaneIIDCodeMeasure_map_shiftedStream 0
  have hstream : Measurable (fun W : ℤ → Fin 3 => KMSW.shiftedStream W 0) := by
    apply measurable_pi_iff.2
    intro i
    simpa [KMSW.shiftedStream] using measurable_pi_apply (i : ℤ)
  have hfun : (fun W : ℤ → Fin 3 => shiftedCodePath W 0) =
      insertDummy ∘ (fun W => KMSW.shiftedStream W 0) := by
    funext W i
    cases i with
    | zero => simp [shiftedCodePath, insertDummy]
    | succ i => simp [shiftedCodePath, insertDummy, KMSW.shiftedStream]
  have hcomp : wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0) =
      (wholePlaneIIDCodeMeasure.map
        (fun W => KMSW.shiftedStream W 0)).map insertDummy := by
    rw [hfun]
    exact (Measure.map_map measurable_pastCodeInsertDummy hstream).symm
  calc
    iidCodeMeasure = wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0) :=
      (wholePlaneIIDCodeMeasure_map_shiftedPath 0).symm
    _ = (wholePlaneIIDCodeMeasure.map
        (fun W => KMSW.shiftedStream W 0)).map insertDummy := hcomp
    _ = _ := by
      have hraw' :
          wholePlaneIIDCodeMeasure.map
              (fun W : ℤ → Fin 3 => fun i : ℕ => KMSW.shiftedStream W 0 i) =
            Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
        simpa [KMSW.shiftedStream] using hraw
      rw [hraw']

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
private theorem pastCodeTail_insertDummy (x : ℕ → Fin 3) :
    pastCodeTail (insertDummy x) = x := by
  funext i
  simp [pastCodeTail, insertDummy]

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
theorem wholePlaneIID_ae_pastCode_finiteIncidence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, KMSW.KMSWFiniteIncidence (pastCode W) := by
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      KMSW.KMSWFiniteIncidence (pastCodeTail ω) := by
    have h := KMSW.iidCodes_ae_finite_incident_edges
    convert h using 1
    funext ω
    rfl
  have htarget : ∀ᵐ x ∂Measure.infinitePi
      (fun _ : ℕ => uniformCodeMeasure), KMSW.KMSWFiniteIncidence x := by
    have htargetDummy : ∀ᵐ x ∂(Measure.infinitePi
        (fun _ : ℕ => uniformCodeMeasure)).map insertDummy,
        KMSW.KMSWFiniteIncidence (pastCodeTail x) := by
      rw [← iidCodeMeasure_eq_product_map_insertDummy]
      exact hsource
    have hpull := MeasureTheory.ae_of_ae_map
      measurable_pastCodeInsertDummy.aemeasurable
      htargetDummy
    simpa only [pastCodeTail_insertDummy] using hpull
  have hmap : ∀ᵐ x ∂wholePlaneIIDCodeMeasure.map pastCode,
      KMSW.KMSWFiniteIncidence x := by
    rw [wholePlaneIIDCodeMeasure_map_pastCode]
    exact htarget
  exact MeasureTheory.ae_of_ae_map measurable_pastCode.aemeasurable hmap

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
theorem wholePlaneIID_ae_pastCode_boundaryHitWitnesses :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      KMSW.BoundaryHitWitnesses (pastCode W) := by
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      KMSW.BoundaryHitWitnesses (pastCodeTail ω) := by
    change ∀ᵐ ω ∂iidCodeMeasure,
      KMSW.BoundaryHitWitnesses (fun i => ω (i + 1))
    exact KMSW.iidCodes_ae_boundaryHitWitnesses
  have htarget : ∀ᵐ x ∂Measure.infinitePi
      (fun _ : ℕ => uniformCodeMeasure), KMSW.BoundaryHitWitnesses x := by
    have htargetDummy : ∀ᵐ x ∂(Measure.infinitePi
        (fun _ : ℕ => uniformCodeMeasure)).map insertDummy,
        KMSW.BoundaryHitWitnesses (pastCodeTail x) := by
      rw [← iidCodeMeasure_eq_product_map_insertDummy]
      exact hsource
    have hpull := MeasureTheory.ae_of_ae_map
      measurable_pastCodeInsertDummy.aemeasurable
      htargetDummy
    simpa only [pastCodeTail_insertDummy] using hpull
  have hmap : ∀ᵐ x ∂wholePlaneIIDCodeMeasure.map pastCode,
      KMSW.BoundaryHitWitnesses x := by
    rw [wholePlaneIIDCodeMeasure_map_pastCode]
    exact htarget
  exact MeasureTheory.ae_of_ae_map measurable_pastCode.aemeasurable hmap

/-- Helper toward Theorem 1.4 (UIBOT plane realization: law of the reversed past code); -/
theorem wholePlaneIID_ae_pastCode_joint :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      KMSW.KMSWFiniteIncidence (pastCode W) ∧
      KMSW.BoundaryHitWitnesses (pastCode W) ∧
      ∀ N, KMSW.KMSWFiniteIncidence (KMSW.shiftedStream W N) := by
  filter_upwards [wholePlaneIID_ae_pastCode_finiteIncidence,
    wholePlaneIID_ae_pastCode_boundaryHitWitnesses,
    wholePlaneIID_ae_finite_incidence] with W hfin hhit hshift
  exact ⟨hfin, hhit, hshift⟩

end DirectedDistances.RandomWalk
