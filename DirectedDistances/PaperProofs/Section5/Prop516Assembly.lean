module

public import DirectedDistances.PaperProofs.Section5.DiskBSBallLaw
public import DirectedDistances.PaperProofs.Section5.UIBHBOTWindowClassCompare
public import DirectedDistances.PaperProofs.Section5.DiskWindowDecodeTV
public import DirectedDistances.PaperProofs.Section5.DiskBallIdentification
import DirectedDistances.PaperProofs.Section5.Prop516BallLawClose
import DirectedDistances.PaperProofs.Section5.DiskStageBallStability
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Conditional assembly toward Proposition 5.16 (`prop-disk-bs-conv`), not a paper result.

Both actual laws take values in `FramedBallClass`; no change of class carrier or
coercion is used. The topology below is the discrete topology on that countable
carrier. Only positive radii are used.

The open geometric premise is `DiskWindowClassComparison.class_eq_on_capture`.
`KMSWDiskBallCapture.lean` supplies induced edges at the window endpoint;
`DiskWindowFramedCapture.lean` supplies endpoint dart and structure comparisons;
`DiskBallIdentification.lean` supplies later-stage vertex equality;
`Prop516BallLawClose.lean` supplies high-probability vertex identification;
`DiskStageBallStability.lean` supplies later-stage dart equivalence preserving
edge identities and sides. These do not yet supply the complete framed-class
equality below: rotation, faces/outer face, missing/present tags, orientation and
the ordered root must all agree between the disk stage and decoded window.
The probability field is proved here independently. Its quantifiers permit
arbitrarily large fixed windows, followed by sufficiently large disk sizes;
they do not incorrectly assert zero failure in a fixed finite window. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal symmDiff

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premises `hA`, `hadm`, `hlo`, `hhi` give the S3 sequence. Capture failure
can be made arbitrarily small along that sequence, with the window chosen -/
theorem diskWindowCapture_probability
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ K0 N : ℕ, N₀ ≤ N ∧ ∀ᶠ k in atTop,
      1 - ε ≤ (bridgeLevelLaw (k + 1) (ell k)).real
        {p | ∃ x, bridgeOptionWindow (k + 1) N p = some x ∧
          kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧
          ¬ DiskDip N K0 p} := by
  obtain ⟨K0, M, hE⟩ := uibhbot_prob_windowEventK_ge r (ε / 3) (by positivity)
  obtain ⟨N, hN, n₀, hgood⟩ := diskWindow_prob_good_ge A hA r K0
    (max N₀ M) (ε / 3) (by positivity)
    (fun N hN => hE N ((le_max_right _ _).trans hN))
  refine ⟨K0, N, (le_max_left _ _).trans hN, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with k hk
  have h := hgood (k + 1) (by omega) (ell k) (hlo k) (hhi k)
    (hadm k).2.1 (hadm k).2.2
  linarith only [h]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Explicit named disk-side premise: complete class equality on capture, together
with arbitrarily small capture failure along every S3 sequence. The latter
field is already proved by `diskWindowCapture_probability`; the former remains -/
structure DiskWindowClassComparison : Prop where
  /-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
  Named premises are the admissible disk domain and the window capture/no-dip
  inputs. This is the remaining complete framed-class identification. -/
  class_eq_on_capture : ∀ (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r),
    ∀ᵐ p ∂bridgeLevelLaw n ell, ∀ x,
      bridgeOptionWindow n N p = some x →
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
      ¬ DiskDip N K0 p →
      diskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
        uibhbotDecodedWindowBallClass N r x
  /-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
  Named premises `hA`, `hadm`, `hlo`, `hhi` specify the S3 sequence.
  This probability obligation is already proved, independently of class equality. -/
  capture_probability : ∀ (A : ℝ) (_hA : 1 < A) (ell : ℕ → ℕ)
    (_hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (_hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (_hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (r : ℕ) (ε : ℝ) (_hε : 0 < ε) (N₀ : ℕ),
    ∃ K0 N : ℕ, N₀ ≤ N ∧ ∀ᶠ k in atTop,
      1 - ε ≤ (bridgeLevelLaw (k + 1) (ell k)).real
        {p | ∃ x, bridgeOptionWindow (k + 1) N p = some x ∧
          kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧
          ¬ DiskDip N K0 p}

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premise `hclass` is exactly the remaining geometric field. The probability -/
theorem diskWindowClassComparison_of_class_eq
    (hclass : ∀ (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
      (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
      (N K0 r : ℕ) (hr : 0 < r),
      ∀ᵐ p ∂bridgeLevelLaw n ell, ∀ x,
        bridgeOptionWindow n N p = some x →
        kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
        ¬ DiskDip N K0 p →
        diskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
          uibhbotDecodedWindowBallClass N r x) : DiskWindowClassComparison :=
  ⟨hclass, diskWindowCapture_probability⟩

private theorem bridge_probability (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    IsProbabilityMeasure (bridgeLevelLaw n ell) := by
  have hc := cond_isProbabilityMeasure
    (iidCodeMeasure_coneEvent_pos_of_domain ell n hell hle hmod).ne'
  let := hc
  have hu : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.Icc 1 ell)) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    have hcard : (Finset.Icc 1 ell).card = ell := by simp
    rw [hcard]
    exact ENNReal.div_self (by exact_mod_cast Nat.ne_of_gt hell) (by finiteness)
  let := hu
  unfold bridgeLevelLaw
  infer_instance

private theorem measurable_bridgeBall (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) (hr : 0 < r) :
    Measurable (diskBSBallClass n ell hell r hr ∘
      diskBridgeDecoder ell n hell hle hmod) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  exact (measurable_diskBSBallClass n ell hell r hr).comp
    (measurable_diskBridgeDecoder ell n hell hle hmod)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premise `hcompare` supplies equality on capture. The subset-law discrepancy -/
theorem diskBSBallLaw_sub_decodedWindow_le
    (hcompare : DiskWindowClassComparison)
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) (C : Set FramedBallClass) :
    |(diskBSBallLaw n ell hell hle hmod r hr : Measure FramedBallClass).real C -
      (bridgeLevelLaw n ell).real
        ((fun p => (bridgeOptionWindow n N p).map
          (uibhbotDecodedWindowBallClass N r)) ⁻¹' (some '' C))| ≤
    1 - (bridgeLevelLaw n ell).real
      {p | ∃ x, bridgeOptionWindow n N p = some x ∧
        kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧
        ¬ DiskDip N K0 p} := by
  classical
  let μ := bridgeLevelLaw n ell
  let : IsProbabilityMeasure μ := bridge_probability n ell hell hle hmod
  let f := diskBSBallClass n ell hell r hr ∘ diskBridgeDecoder ell n hell hle hmod
  let B := (fun p => (bridgeOptionWindow n N p).map
    (uibhbotDecodedWindowBallClass N r)) ⁻¹' (some '' C)
  let G : Set ((ℕ → Fin 3) × ℕ) :=
    {p | ∃ x, bridgeOptionWindow n N p = some x ∧
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧ ¬ DiskDip N K0 p}
  have hf : Measurable f := measurable_bridgeBall n ell hell hle hmod r hr
  have hB : MeasurableSet B := measurableSet_bridgeOptionWindow_preimage n N
    ((Option.map (uibhbotDecodedWindowBallClass N r)) ⁻¹' (some '' C))
  have hC : MeasurableSet C := MeasurableSpace.measurableSet_top
  let D := (f ⁻¹' C) ∆ B
  have hD : MeasurableSet D := (hf hC).symmDiff hB
  have hbound : μ.real G ≤ μ.real Dᶜ := by
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [hcompare.class_eq_on_capture n ell hell hle hmod N K0 r hr]
      with p hp
    rintro ⟨x, hx, hev, hnd⟩
    have he := hp x hx hev hnd
    have hb : p ∈ B ↔ f p ∈ C := by
      simp only [B, Set.mem_preimage, hx, Option.map_some]
      simpa only [Set.mem_image, Option.some.injEq, exists_eq_right] using
        (show uibhbotDecodedWindowBallClass N r x ∈ C ↔ f p ∈ C from he ▸ Iff.rfl)
    change ¬ ((f p ∈ C ∧ p ∉ B) ∨ (p ∈ B ∧ f p ∉ C))
    exact fun h => h.elim (fun h => h.2 (hb.mpr h.1))
      (fun h => h.2 (hb.mp h.1))
  have hfailure : μ.real D ≤ 1 - μ.real G := by
    rw [probReal_compl_eq_one_sub hD] at hbound
    linarith only [hbound]
  rw [← bridgeLevelLaw_map_diskBSBallClass n ell hell hle hmod r hr,
    map_measureReal_apply hf hC]
  exact (abs_measureReal_sub_le_measureReal_symmDiff
    (hf hC).nullMeasurableSet hB.nullMeasurableSet).trans hfailure

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premises `hA` and `hε` give the decoded class-law TV estimate, uniformly -/
theorem diskDecodedWindow_sub_uibhbotWindow_le
    (A : ℝ) (hA : 1 < A) (N r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ C : Set FramedBallClass,
        |(bridgeLevelLaw n ell).real
            ((fun p => (bridgeOptionWindow n N p).map
              (uibhbotDecodedWindowBallClass N r)) ⁻¹' (some '' C)) -
          (uibhbotWindowClassLaw N r).real C| ≤ ε := by
  obtain ⟨n₀, htv⟩ := diskWindow_decode_tv A hA N ε hε
    (uibhbotDecodedWindowBallClass N r) (measurable_uibhbotDecodedWindowBallClass N r)
  refine ⟨n₀, ?_⟩
  intro n hn ell hlo hhi hle hmod C
  have h := htv n hn ell hlo hhi hle hmod (some '' C)
  change |(bridgeLevelLaw n ell).real _ -
    (uibhbotEncodingWindowLaw N).real _| ≤ ε at h
  rw [uibhbotWindowClassLaw_eq_map, map_measureReal_apply
    (measurable_uibhbotDecodedWindowBallClass N r) MeasurableSpace.measurableSet_top]
  have hpre : (fun x => some (uibhbotDecodedWindowBallClass N r x)) ⁻¹' (some '' C) =
      (uibhbotDecodedWindowBallClass N r) ⁻¹' C := by
    ext x
    simp
  rw [hpre] at h
  exact h

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premise `hcompare` supplies the disk class comparison; `hA`, `hadm`,
`hlo`, `hhi` give exactly the S3 domain. Every subset mass converges. -/
theorem prop516_setwise_of_diskWindowClassComparison
    (hcompare : DiskWindowClassComparison)
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (r : ℕ) (hr : 0 < r) (C : Set FramedBallClass) :
    Tendsto (fun k =>
      (diskBSBallLaw (k + 1) (ell k) (hadm k).1 (hadm k).2.1
        (hadm k).2.2 r hr : Measure FramedBallClass).real C)
      atTop (𝓝 ((uibhbotBSBallLaw r hr : Measure FramedBallClass).real C)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
    (tendsto_uibhbotWindow_noCertifiedCapture r) (ε / 4) (by positivity)
  obtain ⟨K0, N, hMN, hgood⟩ :=
    hcompare.capture_probability A hA ell hadm hlo hhi r (ε / 4) (by positivity) M
  obtain ⟨n₀, htv⟩ := diskDecodedWindow_sub_uibhbotWindow_le A hA N r
    (ε / 4) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hgood
  refine ⟨max n₀ k₀, ?_⟩
  intro k hk
  let d := (diskBSBallLaw (k + 1) (ell k) (hadm k).1 (hadm k).2.1
    (hadm k).2.2 r hr : Measure FramedBallClass).real C
  let b := (bridgeLevelLaw (k + 1) (ell k)).real
    ((fun p => (bridgeOptionWindow (k + 1) N p).map
      (uibhbotDecodedWindowBallClass N r)) ⁻¹' (some '' C))
  let w := (uibhbotWindowClassLaw N r).real C
  let u := (uibhbotBSBallLaw r hr : Measure FramedBallClass).real C
  have hdb : |d - b| ≤ ε / 4 := by
    have hb := diskBSBallLaw_sub_decodedWindow_le hcompare (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2 N K0 r hr C
    have hg := hk₀ k ((le_max_right _ _).trans hk)
    dsimp only [d, b]
    linarith only [hb, hg]
  have hbw : |b - w| ≤ ε / 4 :=
    htv (k + 1) (by omega) (ell k) (hlo k) (hhi k)
      (hadm k).2.1 (hadm k).2.2 C
  have hwu : |w - u| < ε / 4 := by
    have hbound := uibhbotBSBallLaw_sub_windowClassLaw_le_noCapture N r hr C
    have hsmall := hM N hMN
    rw [Real.dist_eq, sub_zero] at hsmall
    rw [abs_sub_comm] at hbound
    dsimp only [w, u]
    exact hbound.trans_lt ((le_abs_self _).trans_lt hsmall)
  change dist d u < ε
  rw [Real.dist_eq]
  have htri₁ := abs_sub_le d b u
  have htri₂ := abs_sub_le b w u
  linarith only [hdb, hbw, hwu, htri₁, htri₂, hε]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Named premise `hmass` is convergence of each singleton mass. The countable
discrete class space then gives weak convergence by Mathlib's pi-system -/
theorem framedBallLaw_tendsto_of_singleton
    (μ : ℕ → ProbabilityMeasure FramedBallClass) (ν : ProbabilityMeasure FramedBallClass)
    (hmass : ∀ c : FramedBallClass,
      Tendsto (fun k => (μ k : Measure FramedBallClass).real {c}) atTop
        (𝓝 ((ν : Measure FramedBallClass).real {c}))) :
    letI : TopologicalSpace FramedBallClass := ⊥
    letI : OpensMeasurableSpace FramedBallClass := ⟨le_top⟩
    Tendsto μ atTop (𝓝 ν) := by
  classical
  let : TopologicalSpace FramedBallClass := ⊥
  let : DiscreteTopology FramedBallClass := ⟨rfl⟩
  let : OpensMeasurableSpace FramedBallClass := ⟨le_top⟩
  let S : Set (Set FramedBallClass) := {s | ∃ c, s = {c}}
  have hcount : S.Countable := by
    have he : S = Set.range (fun c : FramedBallClass => ({c} : Set FramedBallClass)) := by
      ext s
      simp only [S, Set.mem_ofPred_eq, Set.mem_range]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    rw [he]
    exact Set.countable_range _
  let : SecondCountableTopology FramedBallClass :=
    (isTopologicalBasis_singletons FramedBallClass).secondCountableTopology
      hcount
  have hpi : IsPiSystem S := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ ⟨x, hx, hy⟩
    have hab : a = b := (Set.mem_singleton_iff.mp hx).symm.trans
      (Set.mem_singleton_iff.mp hy)
    exact ⟨a, by rw [← hab, Set.inter_self]⟩
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun _ _ => MeasurableSpace.measurableSet_top)
  · intro U _ x hx
    exact ⟨{x}, ⟨x, rfl⟩, (isOpen_discrete _).mem_nhds (Set.mem_singleton x),
      Set.singleton_subset_iff.mpr hx⟩
  · rintro _ ⟨c, rfl⟩
    rw [← NNReal.tendsto_coe]
    simpa using hmass c

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
CONDITIONAL helper, not counted. Named premise `hcompare` is the explicit disk
comparison obligation. `hA`, `hadm`, `hlo`, `hhi` are exactly the S3 sequence
domain. The actual disk and UIBHBOT laws share `FramedBallClass`, so the carrier
map is the identity, with no quotient coercion. local topology uses every positive radius. -/
theorem prop516_of_diskWindowClassComparison
    (hcompare : DiskWindowClassComparison)
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace FramedBallClass := ⊥
    letI : OpensMeasurableSpace FramedBallClass := ⟨le_top⟩
    ∀ r : ℕ, ∀ hr : 0 < r,
      Tendsto (fun k => diskBSBallLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2 r hr)
        atTop (𝓝 (uibhbotBSBallLaw r hr)) := by
  let : TopologicalSpace FramedBallClass := ⊥
  let : OpensMeasurableSpace FramedBallClass := ⟨le_top⟩
  intro r hr
  apply framedBallLaw_tendsto_of_singleton
  intro c
  exact prop516_setwise_of_diskWindowClassComparison hcompare A hA ell hadm hlo hhi r hr {c}

end DirectedDistances.PaperProofs.Section5
