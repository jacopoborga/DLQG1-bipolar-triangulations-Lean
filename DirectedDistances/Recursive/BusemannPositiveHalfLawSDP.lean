module

public import DirectedDistances.Recursive.BusemannPositiveHalfLaw

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

private theorem cadlag_restrict_positive {f : ℝ → ℝ} (hf : IsCadlag f) :
    IsCadlag (fun t : Set.Ici (0 : ℝ) => f t) := by
  constructor
  · intro t
    apply (hf.isRightContinuous (t : ℝ)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (fun _ h => h)⟩
  · intro t
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (t : ℝ)
    refine ⟨l, hl.comp ?_⟩
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (fun _ h => h)⟩

/-- Helper toward Theorem 1.6; not a paper result.
The actual SDP positive half-path at scale `n + 1`. -/
@[expose] noncomputable def sdpBusemannPositiveHalfPath (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocal :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ : ℝ),
    by
      exact cadlag_restrict_positive (floorStep_isCadlag
        (fun j => (busemannSDPMeasurableVersion ω j : ℝ))
        (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity))⟩

/-- Helper toward Theorem 1.6; not a paper result.
Exact floor-sample identification, including time zero. -/
theorem sdpBusemannPositiveHalfPath_apply (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    (sdpBusemannPositiveHalfPath n ω).1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ : ℝ) := rfl

/-- Helper toward Theorem 1.6; not a paper result.
The actual uncut path agrees with every existing scaled SDP window. -/
theorem sdpBusemannPositiveHalfPath_window (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) :
    (sdpBusemannPositiveHalfPath n ω).1 (localWindowTime t) =
      (sdpBusemannWindow n hT ω).path.1 t := by
  rw [sdpBusemannPositiveHalfPath_apply, sdpBusemannWindow_apply]
  rfl

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff vector is the scaled window vector multiplied by the local cutoff. -/
theorem finiteCutoffWindows_sdpBusemannPositiveHalfPath (n N : ℕ)
    (ω : ℕ → Fin 3) (i : Fin (N + 1)) (t : J1Window ((i.val : ℝ) + 1)) :
    (finiteCutoffWindows N (sdpBusemannPositiveHalfPath n ω) i).path.1 t =
      (sdpBusemannWindow n (by positivity : 0 < (i.val : ℝ) + 1) ω).path.1 t *
        localCutoff i.val (localWindowTime t) := by
  change (sdpBusemannPositiveHalfPath n ω).1 (localWindowTime t) * _ = _
  rw [sdpBusemannPositiveHalfPath_window n (by positivity)]

/-- Helper toward Theorem 1.6; not a paper result.
Pathwise identification of the entire finite cutoff vector through one actual raw window. -/
theorem positiveHalfCutoffFactor_sdpBusemannWindow (n N : ℕ) (ω : ℕ → Fin 3) :
    positiveHalfCutoffFactor N (sdpBusemannWindow n (by positivity) ω) =
      finiteCutoffWindows N (sdpBusemannPositiveHalfPath n ω) := by
  funext i
  apply congrArg (fun p => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  change (sdpBusemannWindow n (by positivity) ω).path.1 _ * _ =
    (sdpBusemannPositiveHalfPath n ω).1 (localWindowTime t) * _
  rw [sdpBusemannWindow_apply, sdpBusemannPositiveHalfPath_apply]
  rfl

/-- Helper toward Theorem 1.6; not a paper result.
The actual scaled SDP path is Borel measurable in the local J1 topology. -/
theorem measurable_sdpBusemannPositiveHalfPath (n : ℕ) :
    Measurable (sdpBusemannPositiveHalfPath n) := by
  apply measurable_of_measurable_finiteCutoffWindows
  intro N
  have hw : Measurable
      (sdpBusemannWindow n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) := by
    apply measurable_scaledPartialSumWindow
    intro j
    exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((measurable_busemannSDPMeasurableVersion _).sub
        (measurable_busemannSDPMeasurableVersion _))
  have heq : (fun ω => finiteCutoffWindows N (sdpBusemannPositiveHalfPath n ω)) =
      positiveHalfCutoffFactor N ∘ sdpBusemannWindow n (by positivity) := by
    funext ω
    exact (positiveHalfCutoffFactor_sdpBusemannWindow n N ω).symm
  rw [heq]
  exact (measurable_positiveHalfCutoffFactor N).comp hw

/-- Helper toward Theorem 1.6; not a paper result.
The probability law of the actual scaled SDP positive half-path. -/
@[expose] noncomputable def sdpBusemannPositiveHalfLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocal :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (sdpBusemannPositiveHalfPath n)

/-- Helper toward Theorem 1.6; not a paper result.
The local path law is the pushforward of the code measure by the actual scaled path. -/
theorem sdpBusemannPositiveHalfLaw_toMeasure (n : ℕ) :
    (sdpBusemannPositiveHalfLaw n : Measure CadlagLocal) =
      iidCodeMeasure.map (sdpBusemannPositiveHalfPath n) := rfl

/-- Helper toward Theorem 1.6; not a paper result.
The consistent selected SDP limits have a genuine probability law on raw trajectories. -/
theorem exists_sdpBusemannProjectiveWindowLaw
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∃ P : ProbabilityMeasure PositiveHalfWindowTrajectory,
      ∀ m, (P : Measure PositiveHalfWindowTrajectory).map (fun x => x.1 m) =
        (sdpBusemannIntegerWindowLimit hind_sdp hsym_sdp m :
          Measure (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))) := by
  apply projectiveProbabilityOnInverseLimit
    (X := fun m => J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))
    (fun m => restrictJ1Window (by positivity) (by norm_cast; omega))
    (fun m => measurable_restrictJ1Window (by positivity) (by norm_cast; omega))
    (sdpBusemannIntegerWindowLimit hind_sdp hsym_sdp)
  intro m
  exact congrArg ProbabilityMeasure.toMeasure
    (sdpBusemannIntegerWindowLimit_projective hind_sdp hsym_sdp m)

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem sdpBusemannPositiveHalfLaw_finiteCutoffWindows (n N : ℕ) :
    (sdpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N) =
      (sdpBusemannWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))).map
        (positiveHalfCutoffFactor N) := by
  have hw : Measurable (sdpBusemannWindow n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) := by
    apply measurable_scaledPartialSumWindow
    intro j
    exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((measurable_busemannSDPMeasurableVersion _).sub
        (measurable_busemannSDPMeasurableVersion _))
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (sdpBusemannPositiveHalfPath n)).map
      (finiteCutoffWindows N) =
    (iidCodeMeasure.map (sdpBusemannWindow n (by positivity))).map
      (positiveHalfCutoffFactor N)
  rw [Measure.map_map (finiteCutoffWindows_measurable N)
    (measurable_sdpBusemannPositiveHalfPath n),
    Measure.map_map (measurable_positiveHalfCutoffFactor N) hw]
  congr 1
  funext ω
  exact (positiveHalfCutoffFactor_sdpBusemannWindow n N ω).symm

/-- Helper toward Theorem 1.6; not a paper result.
The selected finite cutoff-vector limit, retaining the exact selected raw window law. -/
@[expose] noncomputable def sdpBusemannPositiveCutoffLimit
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (N : ℕ) : ProbabilityMeasure (LocalCutoffTuple N) :=
  (Classical.choose (sdp_busemann_window_tendsto hind_sdp hsym_sdp
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).map (positiveHalfCutoffFactor N)

/-- Helper toward Theorem 1.6; not a paper result.
Every finite cutoff-vector law of the actual scaled path converges. -/
theorem sdpBusemannPositiveHalfLaw_finite_tendsto
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (N : ℕ) :
    Tendsto (fun n => (sdpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N))
      atTop (𝓝 (sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp N)) := by
  let ν := Classical.choose (sdp_busemann_window_tendsto hind_sdp hsym_sdp
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))
  have hν := (Classical.choose_spec (sdp_busemann_window_tendsto hind_sdp hsym_sdp
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).1
  have hcont : ∀ᵐ x ∂(ν : Measure (J1WindowD (((N + 2 : ℕ) : ℝ)) (by positivity))),
      ContinuousAt (positiveHalfCutoffFactor N) x := by
    have hc : ∀ i : Fin (N + 1), ∀ᵐ x
        ∂(ν : Measure (J1WindowD (((N + 2 : ℕ) : ℝ)) (by positivity))),
        ContinuousAt x.path.1
          (⟨(i.val : ℝ) + 1, by positivity, by
            have hi : (i.val : ℝ) ≤ N := by
              exact_mod_cast (Nat.le_of_lt_succ i.isLt)
            push_cast
            linarith⟩ : J1Window (((N + 2 : ℕ) : ℝ))) := by
      intro i
      apply sdpBusemannWindowLimit_continuousAt hind_sdp hsym_sdp (by positivity)
      have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      push_cast
      linarith
    filter_upwards [ae_all_iff.2 hc] with x hx
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_cutoffJ1Window i.val (by positivity)).continuousAt.comp
      (continuousAt_restrictJ1Window_of_path_continuousAt (by positivity) (by
        have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        push_cast
        linarith) x (hx i))
  have h := tendsto_map_of_ae_continuousAt
    (fun n => sdpBusemannWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) ν hν
    (positiveHalfCutoffFactor N) (measurable_positiveHalfCutoffFactor N) hcont
  simpa only [sdpBusemannPositiveHalfLaw_finiteCutoffWindows,
    sdpBusemannPositiveCutoffLimit, ν] using h

/-- Helper toward Theorem 1.6; not a paper result.
The selected finite cutoff-vector limits form a projective family. -/
theorem sdpBusemannPositiveCutoffLimit_projective
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (N : ℕ) :
    (sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp (N + 1)).map
      (positiveCutoffTupleRestrict N) = sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp N := by
  have hc : Continuous (positiveCutoffTupleRestrict N) :=
    continuous_pi fun i => continuous_apply
      (⟨i.val, by omega⟩ : Fin ((N + 1) + 1))
  have ht := tendsto_map_of_ae_continuousAt
    (fun n => (sdpBusemannPositiveHalfLaw n).map (finiteCutoffWindows (N + 1)))
    (sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp (N + 1))
    (sdpBusemannPositiveHalfLaw_finite_tendsto hind_sdp hsym_sdp (N + 1))
    (positiveCutoffTupleRestrict N) hc.measurable
    (Filter.Eventually.of_forall fun _ => hc.continuousAt)
  have heq (n : ℕ) :
      ((sdpBusemannPositiveHalfLaw n).map (finiteCutoffWindows (N + 1))).map
        (positiveCutoffTupleRestrict N) =
      (sdpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map hc.measurable (finiteCutoffWindows_measurable (N + 1))
  exact tendsto_nhds_unique (ht.congr' (Filter.Eventually.of_forall heq))
    (sdpBusemannPositiveHalfLaw_finite_tendsto hind_sdp hsym_sdp N)

/-- Helper toward Theorem 1.6; not a paper result.
The selected cutoff-vector marginals are realized by one law on half-line càdlàg paths.
This predicate is proved below by measurable projective gluing. -/
@[expose] def SdpPositiveHalfLimitRealization
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) : Prop :=
  ∃ ν : ProbabilityMeasure CadlagLocal,
    ∀ N, ν.map (finiteCutoffWindows N) = sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp N

/-- Helper toward Theorem 1.6; not a paper result.
The projective raw-window law glues to a genuine positive-half path law with the
selected finite cutoff marginals. -/
theorem sdpBusemannPositiveHalfLimitRealization
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    SdpPositiveHalfLimitRealization hind_sdp hsym_sdp := by
  obtain ⟨P, hP⟩ := exists_sdpBusemannProjectiveWindowLaw hind_sdp hsym_sdp
  refine ⟨P.map positiveHalfWindowGlue, ?_⟩
  intro N
  apply ProbabilityMeasure.toMeasure_injective
  change ((P : Measure PositiveHalfWindowTrajectory).map positiveHalfWindowGlue).map
      (finiteCutoffWindows N) = _
  rw [Measure.map_map (finiteCutoffWindows_measurable N) measurable_positiveHalfWindowGlue]
  have heq : (finiteCutoffWindows N ∘ positiveHalfWindowGlue) =
      positiveHalfCutoffFactor N ∘
        (fun x : PositiveHalfWindowTrajectory => x.1 (N + 1)) :=
    funext (finiteCutoffWindows_positiveHalfWindowGlue N)
  rw [heq, ← Measure.map_map (measurable_positiveHalfCutoffFactor N)
    ((measurable_pi_apply (N + 1)).comp measurable_subtype_coe), hP (N + 1)]
  rfl

/-- Helper toward Theorem 1.6; not a paper result.
A local J1 convergence wrapper for any realization of the selected cutoff marginals. -/
theorem sdpBusemannPositiveHalfLaw_tendsto_of_realization
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (hreal : SdpPositiveHalfLimitRealization hind_sdp hsym_sdp) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto sdpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp N := by
  obtain ⟨ν, hν⟩ := hreal
  refine ⟨ν, tendsto_of_tendsto_finiteCutoffWindows sdpBusemannPositiveHalfLaw ν ?_, hν⟩
  intro N
  rw [hν N]
  exact sdpBusemannPositiveHalfLaw_finite_tendsto hind_sdp hsym_sdp N

/-- Helper toward Theorem 1.6; not a paper result.
The actual scaled SDP positive-half path laws converge in local J1, retaining all
selected finite cutoff marginals. Independence and index-zero symmetry remain explicit. -/
theorem sdpBusemannPositiveHalfLaw_tendsto
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto sdpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = sdpBusemannPositiveCutoffLimit hind_sdp hsym_sdp N :=
  sdpBusemannPositiveHalfLaw_tendsto_of_realization hind_sdp hsym_sdp
    (sdpBusemannPositiveHalfLimitRealization hind_sdp hsym_sdp)

end DirectedDistances.Recursive
