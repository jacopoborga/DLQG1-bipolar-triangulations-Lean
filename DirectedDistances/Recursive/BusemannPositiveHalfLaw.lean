module

public import DirectedDistances.Recursive.BusemannWindowLimitSelectedConsistency
public import DirectedDistances.Probability.SkorokhodJ1LocalLawCriterionFinal
public import DirectedDistances.Probability.SkorokhodJ1LocalProjectiveLimit
import DirectedDistances.Probability.SkorokhodFloorStep
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

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
Rescale a nonnegative integer sequence into a positive half-line path. -/
@[expose] noncomputable def scaledIntegerPositiveHalfPath (n : ℕ) (z : ℕ → ℤ) : CadlagLocal :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ), by
    have h := cadlag_restrict_positive (floorStep_isCadlag
      (fun j : ℤ => (z j.toNat : ℝ)) (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))
      ((n + 1 : ℕ) : ℝ) (by positivity))
    convert h using 1
    funext t
    rw [← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property)]
    simp only [Int.toNat_natCast]⟩

/-- Helper toward Theorem 1.6; not a paper result.
The actual LDP positive half-path at scale `n + 1`. -/
@[expose] noncomputable def ldpBusemannPositiveHalfPath (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocal :=
  scaledIntegerPositiveHalfPath n (fun j => busemannLDPMeasurableVersion ω (j : ℤ))

/-- Helper toward Theorem 1.6; not a paper result.
Exact floor-sample identification, including time zero. -/
theorem ldpBusemannPositiveHalfPath_apply (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    (ldpBusemannPositiveHalfPath n ω).1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (busemannLDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ : ℝ) := by
  change _ * (busemannLDPMeasurableVersion ω
    (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℤ) : ℝ) = _
  rw [Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property)]

/-- Helper toward Theorem 1.6; not a paper result.
The actual uncut path agrees with every existing scaled LDP window. -/
theorem ldpBusemannPositiveHalfPath_window (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) :
    (ldpBusemannPositiveHalfPath n ω).1 (localWindowTime t) =
      (ldpBusemannWindow n hT ω).path.1 t := by
  rw [ldpBusemannPositiveHalfPath_apply, ldpBusemannWindow_apply]
  rfl

/-- Helper toward Theorem 1.6; not a paper result.
The finite cutoff vector is the scaled window vector multiplied by the local cutoff. -/
theorem finiteCutoffWindows_ldpBusemannPositiveHalfPath (n N : ℕ)
    (ω : ℕ → Fin 3) (i : Fin (N + 1)) (t : J1Window ((i.val : ℝ) + 1)) :
    (finiteCutoffWindows N (ldpBusemannPositiveHalfPath n ω) i).path.1 t =
      (ldpBusemannWindow n (by positivity : 0 < (i.val : ℝ) + 1) ω).path.1 t *
        localCutoff i.val (localWindowTime t) := by
  change (ldpBusemannPositiveHalfPath n ω).1 (localWindowTime t) * _ = _
  rw [ldpBusemannPositiveHalfPath_window n (by positivity)]

private theorem truncatedHalfPath_tendsto (n : ℕ) (z : ℕ → ℤ) :
    Tendsto (fun M => scaledIntegerPositiveHalfPath n (fun j => z (min j M)))
      atTop (𝓝 (scaledIntegerPositiveHalfPath n z)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_order.1 tendsto_localJ1TailBound).2 ε hε)
  refine ⟨(n + 1) * (N + 1), ?_⟩
  intro M hM
  have heq : finiteCutoffWindows N
      (scaledIntegerPositiveHalfPath n (fun j => z (min j M))) =
      finiteCutoffWindows N (scaledIntegerPositiveHalfPath n z) := by
    funext i
    apply congrArg (fun p => J1WindowD.mk p)
    apply Subtype.ext
    funext t
    change (_ * (z (min ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ M) : ℝ)) * _ =
      (_ * (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)) * _
    have hi : (i.val : ℝ) + 1 ≤ ((N + 1 : ℕ) : ℝ) := by
      norm_cast
      omega
    have ht : (t : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := t.property.2.trans hi
    have hj : ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ ≤ (n + 1) * (N + 1) := by
      apply Nat.floor_le_of_le
      exact_mod_cast mul_le_mul_of_nonneg_left ht (by positivity :
        0 ≤ ((n + 1 : ℕ) : ℝ))
    rw [min_eq_left (hj.trans hM)]
  have hb := dist_le_finiteCutoffWindowTruncDist_add_bound N
    (scaledIntegerPositiveHalfPath n (fun j => z (min j M)))
    (scaledIntegerPositiveHalfPath n z)
  rw [heq, finiteCutoffWindowTruncDist_self, zero_add] at hb
  exact hb.trans_lt (hN N le_rfl)

/-- Helper toward Theorem 1.6; not a paper result.
The actual scaled LDP path is Borel measurable in the local J1 topology. -/
theorem measurable_ldpBusemannPositiveHalfPath (n : ℕ) :
    Measurable (ldpBusemannPositiveHalfPath n) := by
  let f : ℕ → (ℕ → Fin 3) → CadlagLocal := fun M ω =>
    scaledIntegerPositiveHalfPath n
      (fun j => busemannLDPMeasurableVersion ω ((min j M : ℕ) : ℤ))
  have hf (M : ℕ) : Measurable (f M) := by
    let v : (ℕ → Fin 3) → (Fin (M + 1) → ℤ) := fun ω i =>
      busemannLDPMeasurableVersion ω (i.val : ℤ)
    have hv : Measurable v := Measurable.of_eval fun i =>
      measurable_busemannLDPMeasurableVersion _
    let g : (Fin (M + 1) → ℤ) → CadlagLocal := fun v =>
      scaledIntegerPositiveHalfPath n (fun j => v ⟨min j M, by omega⟩)
    exact (measurable_of_countable g).comp hv
  apply measurable_of_tendsto_metrizable hf
  apply tendsto_pi_nhds.mpr
  intro ω
  exact truncatedHalfPath_tendsto n
    (fun j => busemannLDPMeasurableVersion ω (j : ℤ))

/-- Helper toward Theorem 1.6; not a paper result.
The probability law of the actual scaled LDP positive half-path. -/
@[expose] noncomputable def ldpBusemannPositiveHalfLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocal :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (ldpBusemannPositiveHalfPath n)

/-- Helper toward Theorem 1.6; not a paper result.
The local path law is the pushforward of the code measure by the actual scaled path. -/
theorem ldpBusemannPositiveHalfLaw_toMeasure (n : ℕ) :
    (ldpBusemannPositiveHalfLaw n : Measure CadlagLocal) =
      iidCodeMeasure.map (ldpBusemannPositiveHalfPath n) := rfl

/-- Helper toward Theorem 1.6; not a paper result.
Compatible raw integer windows, before multiplication by the local cutoffs. -/
abbrev PositiveHalfWindowTrajectory :=
  {x : (m : ℕ) → J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity) //
    ∀ m, restrictJ1Window (by positivity) (by norm_cast; omega) (x (m + 1)) = x m}

/-- Helper toward Theorem 1.6; not a paper result.
The consistent selected LDP limits have a genuine probability law on raw trajectories. -/
theorem exists_ldpBusemannProjectiveWindowLaw
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ P : ProbabilityMeasure PositiveHalfWindowTrajectory,
      ∀ m, (P : Measure PositiveHalfWindowTrajectory).map (fun x => x.1 m) =
        (ldpBusemannIntegerWindowLimit hind hsym m :
          Measure (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))) := by
  apply projectiveProbabilityOnInverseLimit
    (X := fun m => J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))
    (fun m => restrictJ1Window (by positivity) (by norm_cast; omega))
    (fun m => measurable_restrictJ1Window (by positivity) (by norm_cast; omega))
    (ldpBusemannIntegerWindowLimit hind hsym)
  intro m
  exact congrArg ProbabilityMeasure.toMeasure
    (ldpBusemannIntegerWindowLimit_projective hind hsym m)

private theorem localCutoff_abs_le_one (n : ℕ) (t : Set.Ici (0 : ℝ)) :
    |localCutoff n t| ≤ 1 := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_left _ _)

private theorem localCutoff_abs_sub_le (n : ℕ) (s t : Set.Ici (0 : ℝ)) :
    |localCutoff n s - localCutoff n t| ≤ |(s : ℝ) - (t : ℝ)| := by
  have h₁ := abs_max_sub_max_le_max (0 : ℝ)
    (min 1 ((n : ℝ) + 1 - s)) 0 (min 1 ((n : ℝ) + 1 - t))
  have h₂ := abs_min_sub_min_le_max (1 : ℝ) ((n : ℝ) + 1 - s)
    1 ((n : ℝ) + 1 - t)
  simp only [sub_self, abs_zero] at h₁ h₂
  rw [show (n : ℝ) + 1 - s - ((n : ℝ) + 1 - t) = -((s : ℝ) - t) by ring,
    abs_neg] at h₂
  exact h₁.trans (max_le (abs_nonneg _)
    (h₂.trans (max_le (abs_nonneg _) le_rfl)))

/-- Helper toward Theorem 1.6; not a paper result.
Multiply a raw finite-window path by Billingsley's integer cutoff. -/
@[expose] noncomputable def cutoffJ1Window (n : ℕ) {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) : J1WindowD T hT :=
  ⟨⟨fun t => x.path.1 t * localCutoff n (localWindowTime t),
    x.path.2.mul ((localCutoff_continuous n).comp
      localWindowTime_continuous).isCadlag⟩⟩

/-- Helper toward Theorem 1.6; not a paper result.
Multiplication by the fixed continuous cutoff is continuous in finite-window J1. -/
theorem continuous_cutoffJ1Window (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Continuous (cutoffJ1Window n hT) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let : CompactSpace (J1Window T) := compactSpace_Icc 0 T
  let : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  obtain ⟨B, hB, hbound⟩ :=
    (isBounded_image_of_isCadlag_of_isCompact x.path.2 isCompact_univ).exists_pos_norm_le
  have hBx (t : J1Window T) : |x.path.1 t| ≤ B := by
    exact hbound _ ⟨t, Set.mem_univ _, rfl⟩
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let δ := ε / (2 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy' : (⨅ φ : J1TimeChange T,
      max (⨆ t : J1Window T, |(φ t : ℝ) - t|)
        (⨆ t : J1Window T, |y.path.1 (φ t) - x.path.1 t|)) < δ := hy
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hy'
  have htime (t : J1Window T) : |(φ t : ℝ) - t| ≤ δ :=
    (le_ciSup (j1WindowTimeChangeDistortion_bddAbove φ) t).trans
      (max_lt_iff.mp hφ).1.le
  have hvalue (t : J1Window T) : |y.path.1 (φ t) - x.path.1 t| ≤ δ :=
    (le_ciSup (j1WindowValueError_bddAbove y.path x.path φ) t).trans
      (max_lt_iff.mp hφ).2.le
  have hpoint (t : J1Window T) :
      |(cutoffJ1Window n hT y).path.1 (φ t) -
        (cutoffJ1Window n hT x).path.1 t| ≤ (B + 1) * δ := by
    let a := localCutoff n (localWindowTime (φ t))
    let b := localCutoff n (localWindowTime t)
    change |y.path.1 (φ t) * a - x.path.1 t * b| ≤ _
    calc
      _ = |(y.path.1 (φ t) - x.path.1 t) * a + x.path.1 t * (a - b)| := by
        congr 1
        ring
      _ ≤ |y.path.1 (φ t) - x.path.1 t| * |a| + |x.path.1 t| * |a - b| := by
        simpa only [abs_mul] using abs_add_le
          ((y.path.1 (φ t) - x.path.1 t) * a) (x.path.1 t * (a - b))
      _ ≤ δ * 1 + B * δ := by
        apply add_le_add
        · exact mul_le_mul (hvalue t) (localCutoff_abs_le_one n _)
            (abs_nonneg _) hδ.le
        · exact mul_le_mul (hBx t)
            ((localCutoff_abs_sub_le n _ _).trans (htime t))
            (abs_nonneg _) hB.le
      _ = (B + 1) * δ := by ring
  have hcost : max (⨆ t : J1Window T, |(φ t : ℝ) - t|)
      (⨆ t : J1Window T, |(cutoffJ1Window n hT y).path.1 (φ t) -
        (cutoffJ1Window n hT x).path.1 t|) ≤ (B + 1) * δ := by
    apply max_le
    · exact ((max_lt_iff.mp hφ).1.le).trans (by nlinarith [hδ.le])
    · exact ciSup_le hpoint
  have hbelow : BddBelow (Set.range fun ψ : J1TimeChange T =>
      max (⨆ t : J1Window T, |(ψ t : ℝ) - t|)
        (⨆ t : J1Window T, |(cutoffJ1Window n hT y).path.1 (ψ t) -
          (cutoffJ1Window n hT x).path.1 t|)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove ψ)
      ⟨0, le_rfl, hT.le⟩ (abs_nonneg _)).trans (le_max_left _ _)
  have hdist : dist (cutoffJ1Window n hT y) (cutoffJ1Window n hT x) ≤
      (B + 1) * δ := (ciInf_le hbelow φ).trans hcost
  apply hdist.trans_lt
  calc
    (B + 1) * δ = ε / 2 := by dsimp [δ]; field_simp
    _ < ε := by linarith

/-- Helper toward Theorem 1.6; not a paper result.
Obtain the first `N + 1` cutoff windows from one raw window of length `N + 2`. -/
@[expose] noncomputable def positiveHalfCutoffFactor (N : ℕ)
    (x : J1WindowD (((N + 2 : ℕ) : ℝ)) (by positivity)) : LocalCutoffTuple N :=
  fun i => cutoffJ1Window i.val (by positivity)
    (restrictJ1Window (by positivity) (by
      have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      push_cast
      linarith) x)

/-- Helper toward Theorem 1.6; not a paper result.
The raw-window-to-cutoff-vector map is Borel measurable. -/
theorem measurable_positiveHalfCutoffFactor (N : ℕ) :
    Measurable (positiveHalfCutoffFactor N) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (continuous_cutoffJ1Window i.val (by positivity)).measurable.comp
    (measurable_restrictJ1Window (by positivity) (by
      have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      push_cast
      linarith))

/-- Helper toward Theorem 1.6; not a paper result.
Pathwise identification of the entire finite cutoff vector through one actual raw window. -/
theorem positiveHalfCutoffFactor_ldpBusemannWindow (n N : ℕ) (ω : ℕ → Fin 3) :
    positiveHalfCutoffFactor N (ldpBusemannWindow n (by positivity) ω) =
      finiteCutoffWindows N (ldpBusemannPositiveHalfPath n ω) := by
  funext i
  apply congrArg (fun p => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  change (ldpBusemannWindow n (by positivity) ω).path.1 _ * _ =
    (ldpBusemannPositiveHalfPath n ω).1 (localWindowTime t) * _
  rw [ldpBusemannWindow_apply, ldpBusemannPositiveHalfPath_apply]
  rfl

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem ldpBusemannPositiveHalfLaw_finiteCutoffWindows (n N : ℕ) :
    (ldpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N) =
      (ldpBusemannWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))).map
        (positiveHalfCutoffFactor N) := by
  have hw : Measurable (ldpBusemannWindow n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) := by
    apply measurable_scaledPartialSumWindow
    intro j
    exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((measurable_busemannLDPMeasurableVersion _).sub
        (measurable_busemannLDPMeasurableVersion _))
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (ldpBusemannPositiveHalfPath n)).map
      (finiteCutoffWindows N) =
    (iidCodeMeasure.map (ldpBusemannWindow n (by positivity))).map
      (positiveHalfCutoffFactor N)
  rw [Measure.map_map (finiteCutoffWindows_measurable N)
    (measurable_ldpBusemannPositiveHalfPath n),
    Measure.map_map (measurable_positiveHalfCutoffFactor N) hw]
  congr 1
  funext ω
  exact (positiveHalfCutoffFactor_ldpBusemannWindow n N ω).symm

/-- Helper toward Theorem 1.6; not a paper result.
The selected finite cutoff-vector limit, retaining the exact selected raw window law. -/
@[expose] noncomputable def ldpBusemannPositiveCutoffLimit
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (N : ℕ) : ProbabilityMeasure (LocalCutoffTuple N) :=
  (Classical.choose (ldp_busemann_window_tendsto hind hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).map (positiveHalfCutoffFactor N)

/-- Helper toward Theorem 1.6; not a paper result.
Every finite cutoff-vector law of the actual scaled path converges. -/
theorem ldpBusemannPositiveHalfLaw_finite_tendsto
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (N : ℕ) :
    Tendsto (fun n => (ldpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N))
      atTop (𝓝 (ldpBusemannPositiveCutoffLimit hind hsym N)) := by
  let ν := Classical.choose (ldp_busemann_window_tendsto hind hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))
  have hν := (Classical.choose_spec (ldp_busemann_window_tendsto hind hsym
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
      apply ldpBusemannWindowLimit_continuousAt hind hsym (by positivity)
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
    (fun n => ldpBusemannWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) ν hν
    (positiveHalfCutoffFactor N) (measurable_positiveHalfCutoffFactor N) hcont
  simpa only [ldpBusemannPositiveHalfLaw_finiteCutoffWindows,
    ldpBusemannPositiveCutoffLimit, ν] using h

/-- Helper toward Theorem 1.6; not a paper result.
Discard the last coordinate of a finite cutoff tuple. -/
@[expose] def positiveCutoffTupleRestrict (N : ℕ)
    (x : LocalCutoffTuple (N + 1)) : LocalCutoffTuple N :=
  fun i => x ⟨i.val, by omega⟩

/-- Helper toward Theorem 1.6; not a paper result.
The selected finite cutoff-vector limits form a projective family. -/
theorem ldpBusemannPositiveCutoffLimit_projective
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (N : ℕ) :
    (ldpBusemannPositiveCutoffLimit hind hsym (N + 1)).map
      (positiveCutoffTupleRestrict N) = ldpBusemannPositiveCutoffLimit hind hsym N := by
  have hc : Continuous (positiveCutoffTupleRestrict N) :=
    continuous_pi fun i => continuous_apply
      (⟨i.val, by omega⟩ : Fin ((N + 1) + 1))
  have ht := tendsto_map_of_ae_continuousAt
    (fun n => (ldpBusemannPositiveHalfLaw n).map (finiteCutoffWindows (N + 1)))
    (ldpBusemannPositiveCutoffLimit hind hsym (N + 1))
    (ldpBusemannPositiveHalfLaw_finite_tendsto hind hsym (N + 1))
    (positiveCutoffTupleRestrict N) hc.measurable
    (Filter.Eventually.of_forall fun _ => hc.continuousAt)
  have heq (n : ℕ) :
      ((ldpBusemannPositiveHalfLaw n).map (finiteCutoffWindows (N + 1))).map
        (positiveCutoffTupleRestrict N) =
      (ldpBusemannPositiveHalfLaw n).map (finiteCutoffWindows N) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map hc.measurable (finiteCutoffWindows_measurable (N + 1))
  exact tendsto_nhds_unique (ht.congr' (Filter.Eventually.of_forall heq))
    (ldpBusemannPositiveHalfLaw_finite_tendsto hind hsym N)

/-- Helper toward Theorem 1.6; not a paper result.
Measurability into local J1 can be checked on every finite cutoff vector. -/
theorem measurable_of_measurable_finiteCutoffWindows {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → CadlagLocal)
    (hf : ∀ N, Measurable (fun ω => finiteCutoffWindows N (f ω))) : Measurable f := by
  apply measurable_of_isClosed'
  intro F hF hFne _
  let q : CadlagLocal → ℝ := fun x => min (Metric.infDist x F) 1
  have hqB (x : CadlagLocal) : |q x| ≤ 1 := by
    rw [abs_of_nonneg (le_min Metric.infDist_nonneg zero_le_one)]
    exact min_le_right _ _
  have hqL : LipschitzWith 1 q := (Metric.lipschitz_infDist_pt F).min_const 1
  choose g hgL hgB hgA using fun N =>
    exists_bounded_lipschitz_finiteCutoffWindows_approximation q 1 1 hqB hqL N
  have hq : Measurable (fun ω => q (f ω)) := by
    apply measurable_of_tendsto_metrizable
      (fun N => (hgL N).continuous.measurable.comp (hf N))
    apply tendsto_pi_nhds.mpr
    intro ω
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_localJ1TailBound
    intro N
    simpa only [Real.dist_eq, abs_sub_comm, NNReal.coe_one, one_mul, Function.comp_def]
      using hgA N (f ω)
  have heq : f ⁻¹' F = (fun ω => q (f ω)) ⁻¹' {0} := by
    ext ω
    change f ω ∈ F ↔ q (f ω) = 0
    rw [hF.mem_iff_infDist_zero hFne]
    constructor
    · intro h
      simp only [q, h, min_eq_left zero_le_one]
    · intro h
      by_contra hn
      have hp : 0 < Metric.infDist (f ω) F :=
        lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hn)
      have hpos : 0 < q (f ω) := lt_min hp zero_lt_one
      rw [h] at hpos
      exact (lt_irrefl 0) hpos
  rw [heq]
  exact hq (measurableSet_singleton 0)

private theorem trajectory_eval_eq (x : PositiveHalfWindowTrajectory)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht0 : 0 ≤ t)
    (htm : t ≤ ((m + 1 : ℕ) : ℝ)) :
    (x.1 n).path.1 ⟨t, ht0, htm.trans (by exact_mod_cast Nat.succ_le_succ hmn)⟩ =
      (x.1 m).path.1 ⟨t, ht0, htm⟩ := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h := congrArg (fun p : J1WindowD ((n + 1 : ℕ) : ℝ) (by positivity) =>
      p.path.1 ⟨t, ht0, htm.trans (by exact_mod_cast Nat.succ_le_succ hn)⟩) (x.2 n)
    exact h.trans ih

/-- Helper toward Theorem 1.6; not a paper result.
The pointwise gluing of a compatible family of raw integer windows. -/
@[expose] noncomputable def positiveHalfWindowGlueFun (x : PositiveHalfWindowTrajectory)
    (t : Set.Ici (0 : ℝ)) : ℝ :=
  (x.1 (⌊(t : ℝ)⌋₊ + 1)).path.1 ⟨t, t.property, by
    have h := Nat.lt_floor_add_one (t : ℝ)
    push_cast
    linarith⟩

private theorem positiveHalfWindowGlueFun_eq (x : PositiveHalfWindowTrajectory)
    (m : ℕ) (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) ≤ ((m + 1 : ℕ) : ℝ)) :
    positiveHalfWindowGlueFun x t = (x.1 m).path.1 ⟨t, t.property, ht⟩ := by
  rcases le_total m (⌊(t : ℝ)⌋₊ + 1) with h | h
  · exact trajectory_eval_eq x m _ h t t.property ht
  · exact (trajectory_eval_eq x _ m h t t.property (by
      have hfloor := Nat.lt_floor_add_one (t : ℝ)
      push_cast
      linarith)).symm

private noncomputable def rawWindowClamp (m : ℕ) (t : Set.Ici (0 : ℝ)) :
    J1Window ((m + 1 : ℕ) : ℝ) :=
  ⟨min (t : ℝ) ((m + 1 : ℕ) : ℝ),
    le_min t.property (by positivity), min_le_right _ _⟩

private theorem rawWindowClamp_continuous (m : ℕ) : Continuous (rawWindowClamp m) := by
  apply continuous_induced_rng.mpr
  exact continuous_subtype_val.min continuous_const

/-- Helper toward Theorem 1.6; not a paper result.
Compatible raw integer windows glue to a càdlàg function on the whole positive half-line. -/
theorem positiveHalfWindowGlueFun_isCadlag (x : PositiveHalfWindowTrajectory) :
    IsCadlag (positiveHalfWindowGlueFun x) := by
  have hnear (a : Set.Ici (0 : ℝ)) :
      ∃ m : ℕ, (a : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    refine ⟨⌊(a : ℝ)⌋₊ + 1, ?_⟩
    have h := Nat.lt_floor_add_one (a : ℝ)
    push_cast
    linarith
  constructor
  · intro a
    obtain ⟨m, ha⟩ := hnear a
    let aw : J1Window ((m + 1 : ℕ) : ℝ) := ⟨a, a.property, ha.le⟩
    have heq : rawWindowClamp m a = aw := Subtype.ext (min_eq_left ha.le)
    have hev : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a,
        (s : ℝ) < ((m + 1 : ℕ) : ℝ) :=
      (continuous_subtype_val.continuousAt.tendsto).eventually (Iio_mem_nhds ha)
    have hmap : Tendsto (rawWindowClamp m) (𝓝[Set.Ioi a] a) (𝓝[Set.Ioi aw] aw) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨heq ▸ (rawWindowClamp_continuous m).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds]
        with s hs hsm
      change (a : ℝ) < min (s : ℝ) ((m + 1 : ℕ) : ℝ)
      rw [min_eq_left hsm.le]
      exact hs
    have hp := ((x.1 m).path.2.isRightContinuous aw).tendsto.comp hmap
    change Tendsto (positiveHalfWindowGlueFun x) _ _
    rw [positiveHalfWindowGlueFun_eq x m a ha.le]
    apply hp.congr'
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
    rw [positiveHalfWindowGlueFun_eq x m s hs.le]
    exact congrArg (x.1 m).path.1 (Subtype.ext (min_eq_left hs.le))
  · intro a
    obtain ⟨m, ha⟩ := hnear a
    let aw : J1Window ((m + 1 : ℕ) : ℝ) := ⟨a, a.property, ha.le⟩
    have heq : rawWindowClamp m a = aw := Subtype.ext (min_eq_left ha.le)
    have hev : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a,
        (s : ℝ) < ((m + 1 : ℕ) : ℝ) :=
      (continuous_subtype_val.continuousAt.tendsto).eventually (Iio_mem_nhds ha)
    have hmap : Tendsto (rawWindowClamp m) (𝓝[Set.Iio a] a) (𝓝[Set.Iio aw] aw) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨heq ▸ (rawWindowClamp_continuous m).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds]
        with s hs hsm
      change min (s : ℝ) ((m + 1 : ℕ) : ℝ) < (a : ℝ)
      rw [min_eq_left hsm.le]
      exact hs
    obtain ⟨l, hl⟩ := (x.1 m).path.2.tendsto_nhdsLT aw
    refine ⟨l, (hl.comp hmap).congr' ?_⟩
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
    rw [positiveHalfWindowGlueFun_eq x m s hs.le]
    exact congrArg (x.1 m).path.1 (Subtype.ext (min_eq_left hs.le))

/-- Helper toward Theorem 1.6; not a paper result.
The actual càdlàg gluing of compatible raw integer windows. -/
@[expose] noncomputable def positiveHalfWindowGlue (x : PositiveHalfWindowTrajectory) :
    CadlagLocal :=
  ⟨positiveHalfWindowGlueFun x, positiveHalfWindowGlueFun_isCadlag x⟩

/-- Helper toward Theorem 1.6; not a paper result.
The glued path recovers every raw window, including its endpoints. -/
theorem positiveHalfWindowGlue_window (x : PositiveHalfWindowTrajectory)
    (m : ℕ) (t : J1Window ((m + 1 : ℕ) : ℝ)) :
    (positiveHalfWindowGlue x).1 (localWindowTime t) = (x.1 m).path.1 t :=
  positiveHalfWindowGlueFun_eq x m (localWindowTime t) t.property.2

/-- Helper toward Theorem 1.6; not a paper result.
The glued path's finite cutoff vector factors through one raw trajectory coordinate. -/
theorem finiteCutoffWindows_positiveHalfWindowGlue (N : ℕ)
    (x : PositiveHalfWindowTrajectory) :
    finiteCutoffWindows N (positiveHalfWindowGlue x) =
      positiveHalfCutoffFactor N (x.1 (N + 1)) := by
  funext i
  apply congrArg (fun p => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  change positiveHalfWindowGlueFun x (localWindowTime t) * _ =
    (x.1 (N + 1)).path.1 _ * _
  rw [positiveHalfWindowGlueFun_eq x (N + 1) _ (by
    have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have ht := t.property.2
    change (t : ℝ) ≤ (((N + 1) + 1 : ℕ) : ℝ)
    push_cast
    linarith)]
  rfl

/-- Helper toward Theorem 1.6; not a paper result.
Gluing raw compatible windows is Borel measurable for the local J1 sigma algebra. -/
theorem measurable_positiveHalfWindowGlue : Measurable positiveHalfWindowGlue := by
  apply measurable_of_measurable_finiteCutoffWindows
  intro N
  have heq : (fun x => finiteCutoffWindows N (positiveHalfWindowGlue x)) =
      positiveHalfCutoffFactor N ∘
        (fun x : PositiveHalfWindowTrajectory => x.1 (N + 1)) :=
    funext (finiteCutoffWindows_positiveHalfWindowGlue N)
  rw [heq]
  exact (measurable_positiveHalfCutoffFactor N).comp
    ((measurable_pi_apply (N + 1)).comp measurable_subtype_coe)

/-- Helper toward Theorem 1.6; not a paper result.
The selected cutoff-vector marginals are realized by one law on half-line càdlàg paths.
This predicate is proved below by measurable projective gluing. -/
@[expose] def LdpPositiveHalfLimitRealization
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) : Prop :=
  ∃ ν : ProbabilityMeasure CadlagLocal,
    ∀ N, ν.map (finiteCutoffWindows N) = ldpBusemannPositiveCutoffLimit hind hsym N

/-- Helper toward Theorem 1.6; not a paper result.
The projective raw-window law glues to a genuine positive-half path law with the
selected finite cutoff marginals. -/
theorem ldpBusemannPositiveHalfLimitRealization
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    LdpPositiveHalfLimitRealization hind hsym := by
  obtain ⟨P, hP⟩ := exists_ldpBusemannProjectiveWindowLaw hind hsym
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
theorem ldpBusemannPositiveHalfLaw_tendsto_of_realization
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (hreal : LdpPositiveHalfLimitRealization hind hsym) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto ldpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = ldpBusemannPositiveCutoffLimit hind hsym N := by
  obtain ⟨ν, hν⟩ := hreal
  refine ⟨ν, tendsto_of_tendsto_finiteCutoffWindows ldpBusemannPositiveHalfLaw ν ?_, hν⟩
  intro N
  rw [hν N]
  exact ldpBusemannPositiveHalfLaw_finite_tendsto hind hsym N

/-- Helper toward Theorem 1.6; not a paper result.
The actual scaled LDP positive-half path laws converge in local J1, retaining all
selected finite cutoff marginals. Independence and index-zero symmetry remain explicit. -/
theorem ldpBusemannPositiveHalfLaw_tendsto
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto ldpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = ldpBusemannPositiveCutoffLimit hind hsym N :=
  ldpBusemannPositiveHalfLaw_tendsto_of_realization hind hsym
    (ldpBusemannPositiveHalfLimitRealization hind hsym)

end DirectedDistances.Recursive
