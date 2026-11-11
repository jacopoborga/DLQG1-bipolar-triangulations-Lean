module

public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.KMSWWholePlaneRotationTransport
public import DirectedDistances.KMSW.LocalFinitenessIID
public import DirectedDistances.RandomWalk.IIDVectorWalk
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! # Two-sided iid KMSW code law

Helper toward F4c / the whole-plane KMSW carrier
uniform code law and almost-sure finite incidence of every one-sided run
(first conjunct of `WholePlaneRotationHypothesis`); cofinal freshness, the
whole-plane carrier identification and Q-F4c are not treated; not the paper
result. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

/-- The two-sided iid uniform source-code law toward F4c -/
@[expose] noncomputable def wholePlaneIIDCodeMeasure : Measure (ℤ → Fin 3) :=
  Measure.infinitePi (fun _ : ℤ => uniformCodeMeasure)

instance : IsProbabilityMeasure wholePlaneIIDCodeMeasure := by
  unfold wholePlaneIIDCodeMeasure
  infer_instance

private def wholePlaneIndexShiftEquiv (t : ℤ) : ℤ ≃ ℤ where
  toFun := fun k => k + t
  invFun := fun k => k - t
  left_inv := by intro k; change k + t - t = k; omega
  right_inv := by intro k; change k - t + t = k; omega

/-- Reindexing the two-sided iid law by an integer translation preserves its law. -/
theorem wholePlaneIIDCodeMeasure_map_shift (t : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W k => W (k + t)) =
      wholePlaneIIDCodeMeasure := by
  have hfun : (fun W : ℤ → Fin 3 => fun k => W (k + t)) =
      (MeasurableEquiv.piCongrLeft (fun _ : ℤ => Fin 3)
        (wholePlaneIndexShiftEquiv t).symm) := by
    funext W k
    change W ((wholePlaneIndexShiftEquiv t) k) =
      ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => Fin 3)
        (wholePlaneIndexShiftEquiv t).symm) W) k
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℤ => Fin 3) (wholePlaneIndexShiftEquiv t).symm W
      ((wholePlaneIndexShiftEquiv t) k)).symm
  rw [wholePlaneIIDCodeMeasure, hfun]
  simpa using (Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : ℤ => uniformCodeMeasure) (wholePlaneIndexShiftEquiv t).symm)

/-- The raw one-sided stream cut from any integer start has the iid product law. -/
theorem wholePlaneIIDCodeMeasure_map_shiftedStream (N : ℕ) :
    wholePlaneIIDCodeMeasure.map
        (fun W : ℤ → Fin 3 => fun i : ℕ => W ((i : ℤ) - N)) =
      Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) - N) := by
    intro i j hij
    have hsub : (i : ℤ) - (N : ℤ) = (j : ℤ) - (N : ℤ) := by
      exact_mod_cast hij
    have hcast : (i : ℤ) = (j : ℤ) := by omega
    exact_mod_cast hcast
  change (Measure.infinitePi (fun _ : ℤ => uniformCodeMeasure)).map
      (fun W : ℤ → Fin 3 => fun i : ℕ => W ((i : ℤ) - (N : ℤ))) =
    Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℤ => uniformCodeMeasure) hinj

private def codeTail (ω : ℕ → Fin 3) : ℕ → Fin 3 := fun i => ω (i + 1)

/-- Insert the deterministic time-zero code into a shifted run toward F4c -/
@[expose] def insertDummy (x : ℕ → Fin 3) : ℕ → Fin 3 := fun i =>
  if i = 0 then 0 else x (i - 1)

private theorem measurable_codeTail : Measurable codeTail := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_pi_apply (i + 1)

private theorem measurable_insertDummy : Measurable insertDummy := by
  apply measurable_pi_iff.2
  intro i
  by_cases hi : i = 0
  · simp [insertDummy, hi]
  · simpa [insertDummy, hi] using measurable_pi_apply (i - 1)

private theorem measurable_shiftedStream (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => fun i : ℕ => KMSW.shiftedStream W N i) := by
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun W : ℤ → Fin 3 => W ((i : ℤ) - N))
  exact measurable_pi_apply ((i : ℤ) - N)

private noncomputable def codeMarginalLaw (i : ℕ) : Measure (Fin 3) :=
  if i = 0 then Measure.dirac 0 else uniformCodeMeasure

private instance (i : ℕ) : IsProbabilityMeasure (codeMarginalLaw i) := by
  unfold codeMarginalLaw
  split <;> infer_instance

private theorem map_code_coordinate (i : ℕ) :
    iidCodeMeasure.map (fun ω => ω (i + 1)) = uniformCodeMeasure := by
  let j : Fin (i + 1 + 1) := ⟨i + 1, by omega⟩
  have h := congrArg (fun μ : Measure (Fin (i + 1 + 1) → Fin 3) =>
    μ.map (Function.eval j)) (iidCodeMeasure_map_prefix (i + 1))
  have hprefix : Measurable
      (fun ω : ℕ → Fin 3 => fun k : Fin (i + 1 + 1) => ω k.val) := by
    apply measurable_pi_iff.2
    intro k
    exact measurable_pi_apply k.val
  rw [Measure.map_map (measurable_pi_apply j) hprefix] at h
  have hp : (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginalLaw j.val)).map
      (Function.eval j) = codeMarginalLaw j.val := (measurePreserving_eval _ j).map_eq
  change _ = (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginalLaw j.val)).map
    (Function.eval j) at h
  rw [hp] at h
  simpa [codeMarginalLaw, j, Function.comp_def, Function.eval] using h

private theorem iIndepFun_codeTail :
    iIndepFun (fun i (ω : ℕ → Fin 3) => ω (i + 1)) iidCodeMeasure := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  let n := s.sup id + 1
  let e (i : s) : Fin (n + 1) := ⟨i.val + 1, by
    have hi := Finset.le_sup (f := id) i.property
    change i.val ≤ s.sup id at hi
    dsimp [n]
    omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    have := congrArg Fin.val h
    dsimp [e] at this
    omega
  let μ := Measure.pi (fun j : Fin (n + 1) =>
    codeMarginalLaw j.val)
  have hind : iIndepFun (fun i : s => fun q : Fin (n + 1) → Fin 3 => q (e i)) μ :=
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).precomp he
  have hm : iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => ω j.val) = μ :=
    iidCodeMeasure_map_prefix n
  have hmass (t : Set (Fin (n + 1) → Fin 3)) :
      μ t = iidCodeMeasure ((fun ω => fun j : Fin (n + 1) => ω j.val) ⁻¹' t) := by
    rw [← hm, Measure.map_apply (by fun_prop) ((Set.to_countable t).measurableSet)]
  have h := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : s => sets i.val) (fun _ _ => (Set.to_countable _).measurableSet)
  simp only [hmass] at h
  rw [← Finset.prod_coe_sort]
  convert h using 1
  · congr 1
    ext ω
    simp [e]
  · apply Finset.prod_congr rfl
    intro i _
    congr 1

private theorem iidCodeMeasure_map_codeTail :
    iidCodeMeasure.map codeTail =
      Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
  have h := iIndepFun_codeTail.map_fun_eq_infinitePi_map (by fun_prop)
  calc
    iidCodeMeasure.map codeTail =
        Measure.infinitePi (fun i => iidCodeMeasure.map (fun ω => ω (i + 1))) := by
      change iidCodeMeasure.map (fun ω i => ω (i + 1)) = _
      exact h
    _ = Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
      congr 1
      funext i
      exact map_code_coordinate i

private theorem iidCodeMeasure_eq_insertDummy_map_codeTail :
    iidCodeMeasure = (iidCodeMeasure.map codeTail).map insertDummy := by
  have hstart : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 := by
    rw [iidCodeMeasure]
    exact DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) 0
  have hfun : insertDummy ∘ codeTail =ᵐ[iidCodeMeasure] id := by
    filter_upwards [hstart] with ω hω
    funext i
    cases i with
    | zero => simpa [insertDummy, codeTail] using hω.symm
    | succ i => simp [insertDummy, codeTail]
  calc
    iidCodeMeasure = iidCodeMeasure.map id := by rw [Measure.map_id]
    _ = iidCodeMeasure.map (insertDummy ∘ codeTail) := Measure.map_congr hfun.symm
    _ = (iidCodeMeasure.map codeTail).map insertDummy :=
      (Measure.map_map measurable_insertDummy measurable_codeTail).symm

@[expose] def shiftedCodePath (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else KMSW.shiftedStream W N (i - 1)

theorem measurable_shiftedCodePath (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => shiftedCodePath W N) := by
  change Measurable (fun W : ℤ → Fin 3 => insertDummy (KMSW.shiftedStream W N))
  exact measurable_insertDummy.comp (measurable_shiftedStream N)

/-- The one-sided run with its deterministic dummy coordinate has exactly
the existing one-sided iid code law. -/
theorem wholePlaneIIDCodeMeasure_map_shiftedPath (N : ℕ) :
    wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W N) =
        iidCodeMeasure := by
  have hraw := wholePlaneIIDCodeMeasure_map_shiftedStream N
  have hfun : (fun W => shiftedCodePath W N) =
      insertDummy ∘ (fun W i => KMSW.shiftedStream W N i) := by
    funext W i
    cases i with
    | zero => simp [shiftedCodePath, insertDummy]
    | succ i => simp [shiftedCodePath, insertDummy, KMSW.shiftedStream]
  calc
    wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W N) =
        (wholePlaneIIDCodeMeasure.map (fun W i => KMSW.shiftedStream W N i)).map
          insertDummy := by
            rw [hfun]
            exact (Measure.map_map measurable_insertDummy
              (measurable_shiftedStream N)).symm
    _ = (iidCodeMeasure.map codeTail).map insertDummy := by
      have hraw' :
          wholePlaneIIDCodeMeasure.map
              (fun W : ℤ → Fin 3 => fun i : ℕ => KMSW.shiftedStream W N i) =
            iidCodeMeasure.map codeTail := by
        calc
          _ = Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
            simpa [KMSW.shiftedStream] using hraw
          _ = iidCodeMeasure.map codeTail := iidCodeMeasure_map_codeTail.symm
      rw [hraw']
    _ = iidCodeMeasure := iidCodeMeasure_eq_insertDummy_map_codeTail.symm

/-- Almost surely, every shifted one-sided run has finite geometric incidence,
including the missing boundary edges, toward F4c; not the paper result. -/
theorem wholePlaneIID_ae_finite_incidence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      KMSW.KMSWFiniteIncidence (KMSW.shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      KMSW.KMSWFiniteIncidence (fun i => ω (i + 1)) :=
    KMSW.iidCodes_ae_finite_incident_edges
  have htarget : ∀ᵐ x ∂wholePlaneIIDCodeMeasure.map
      (fun W => shiftedCodePath W N),
      KMSW.KMSWFiniteIncidence (fun i => x (i + 1)) := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath N]
    simpa [codeTail] using hsource
  have hpull := MeasureTheory.ae_of_ae_map
    (measurable_shiftedCodePath N).aemeasurable htarget
  simpa [shiftedCodePath, insertDummy] using hpull

end DirectedDistances.RandomWalk
