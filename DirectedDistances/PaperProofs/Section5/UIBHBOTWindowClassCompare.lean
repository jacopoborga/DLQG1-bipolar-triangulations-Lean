module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.KMSW.UIBHBOTWindowProb
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.

Leaf 4, UIBHBOT comparison chain:
(a) On rotation and certified relaxed capture of the root in the stage of length
`2 * N`, the canonical class equals the complete framed class of that stage,
rooted at the west incidence of the record edge created at time `N`. Decoding
`[-N,N]` gives the same stage class, including rotation, faces, tags and frame.
(b) For every subset of framed classes, the absolute difference between the
canonical ball law and the decoded-window class law is at most the probability
that this certified capture fails. Almost surely the capture holds for every
sufficiently large `N`; continuity from above on the decreasing unions of future
failure events makes these failure probabilities tend to zero. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory Filter
open scoped Topology ENNReal symmDiff

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Finite-stage class rooted at the record edge at time `N`, using the existing
specified off-capture value on invalid data. -/
@[expose] noncomputable def uibhbotWindowStageBallClass (N r : ℕ)
    (u : ℕ → Fin 3) : FramedBallClass :=
  uibhbotStageDataBallClassRel
    ⟨kmswStage u (2 * N), kmswStageDirectedMap u (2 * N)⟩
    r (kmswLLCreatedEdge u N) true

private theorem stageDataClass_eq_prefix (u v : ℕ → Fin 3) (m r e : ℕ)
    (b : Bool) (h : ∀ i < m, u i = v i) :
    uibhbotStageDataBallClassRel ⟨kmswStage u m, kmswStageDirectedMap u m⟩ r e b =
      uibhbotStageDataBallClassRel ⟨kmswStage v m, kmswStageDirectedMap v m⟩ r e b := by
  have hu : shiftedStream (fun t => u t.toNat) 0 = u := by
    funext i
    simp only [shiftedStream, Nat.cast_zero, sub_zero, Int.toNat_natCast]
  have hv : shiftedStream (fun t => v t.toNat) 0 = v := by
    funext i
    simp only [shiftedStream, Nat.cast_zero, sub_zero, Int.toNat_natCast]
  have hc := uibhbotStageDataBallClassRel_eq_of_window (fun t => u t.toNat)
      (fun t => v t.toNat) 0 m r e b (by
        intro i hi
        simpa only [Nat.cast_zero, sub_zero, Int.toNat_natCast] using h i hi)
  rw [hu, hv] at hc
  exact hc

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The entire framed class depends only on the `2 * N` letters of the window. -/
theorem uibhbotWindowStageBallClass_eq_prefix (N r : ℕ) (u v : ℕ → Fin 3)
    (h : ∀ i < 2 * N, u i = v i) :
    uibhbotWindowStageBallClass N r u = uibhbotWindowStageBallClass N r v := by
  have he : kmswLLCreatedEdge u N = kmswLLCreatedEdge v N := by
    unfold kmswLLCreatedEdge
    rw [kmswStage_congr (fun i hi => h i (by omega))]
  unfold uibhbotWindowStageBallClass
  rw [he]
  exact stageDataClass_eq_prefix u v (2 * N) r _ true h

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The stage-ball class map is measurable on code streams. -/
theorem measurable_uibhbotWindowStageBallClass (N r : ℕ) :
    Measurable (uibhbotWindowStageBallClass N r) :=
  measurable_of_factors_prefix (2 * N) _ (uibhbotWindowStageBallClass_eq_prefix N r)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The complete class computed from the decoded centered window. -/
@[expose] noncomputable def uibhbotDecodedWindowBallClass (N r : ℕ)
    (x : Fin (2 * N + 1) → ℤ × ℤ) : FramedBallClass :=
  uibhbotWindowStageBallClass N r (windowCodeDecode N x)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Measurability of the decoded-window stage-ball class map. -/
theorem measurable_uibhbotDecodedWindowBallClass (N r : ℕ) :
    Measurable (uibhbotDecodedWindowBallClass N r) :=
  (measurable_uibhbotWindowStageBallClass N r).comp (measurable_windowCodeDecode N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Pushforward of the decoded UIBHBOT window law under its complete stage-ball class map. -/
@[expose] noncomputable def uibhbotWindowClassLaw (N r : ℕ) : Measure FramedBallClass :=
  ((uibhbotEncodingWindowLaw N).map (windowCodeDecode N)).map
    (uibhbotWindowStageBallClass N r)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The window law is the direct pushforward by the decoded class map. -/
theorem uibhbotWindowClassLaw_eq_map (N r : ℕ) :
    uibhbotWindowClassLaw N r =
      (uibhbotEncodingWindowLaw N).map (uibhbotDecodedWindowBallClass N r) := by
  exact Measure.map_map (measurable_uibhbotWindowStageBallClass N r)
    (measurable_windowCodeDecode N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On a certified root capture at window size `N`, the selector equals the complete
finite stage class, with the same ordered missing root incidence. -/
theorem uibhbotBallClassRel_eq_windowStageClass (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N r : ℕ) (hr : 0 < r)
    (hcap : ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W N) N) true) :
    uibhbotBallClassRel W r hr =
      uibhbotWindowStageBallClass N r (shiftedStream W N) := by
  obtain ⟨c, hc⟩ := hcap
  obtain ⟨C, hN, hm, _, he, hb⟩ :=
    (uibhbotFixedCaptureRel_iff W r N (2 * N) c _ true).mp hc
  rw [uibhbotBallClassRel_eq_capture W H r hr C, C.class_eq_stageData hr]
  rw [he, hb]
  unfold uibhbotWindowStageBallClass
  have hs : shiftedStream W C.N = shiftedStream W N := congrArg _ hN
  rw [hs, hm]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Decoding an actual UIBHBOT window computes the same complete stage class. -/
theorem uibhbotDecodedWindowBallClass_concat (N r : ℕ) (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    uibhbotDecodedWindowBallClass N r
      (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)) =
      uibhbotWindowStageBallClass N r
        (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) :=
  uibhbotWindowStageBallClass_eq_prefix N r _ _
    (windowCodeDecode_uibhbotConcatWalk N w hw)

private theorem measurable_windowShift (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => shiftedStream W N) :=
  Measurable.of_eval (fun i => measurable_pi_apply ((i : ℤ) - N))

private theorem measurable_windowRootEdge (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => kmswLLCreatedEdge (shiftedStream W N) N) := by
  have hm : Measurable (fun u : ℕ → Fin 3 => kmswLLCreatedEdge u N) := by
    apply measurable_of_factors_prefix N
    intro u v h
    unfold kmswLLCreatedEdge
    rw [kmswStage_congr h]
  exact hm.comp (measurable_windowShift N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The rotation-and-certified-window-capture event is measurable, including its
whole-plane root and all seam certificates. -/
theorem measurableSet_uibhbotWindowCertifiedCapture (N r : ℕ) :
    MeasurableSet {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W ∧
      ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
        (kmswLLCreatedEdge (shiftedStream W N) N) true} := by
  have heq : {W : ℤ → Fin 3 | ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
        (kmswLLCreatedEdge (shiftedStream W N) N) true} =
      {W : ℤ → Fin 3 | ∃ c e, kmswLLCreatedEdge (shiftedStream W N) N = e ∧
        uibhbotFixedCaptureRel W r N (2 * N) c e true} := by
    ext W
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, _, rfl, hc⟩
    · rintro ⟨c, e, he, hc⟩
      exact ⟨c, he.symm ▸ hc⟩
  change MeasurableSet ({W : ℤ → Fin 3 | WholePlaneRotationHypothesis W} ∩
    {W : ℤ → Fin 3 | ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W N) N) true})
  apply measurableSet_uibhbotRotationHypothesisRel.inter
  rw [heq]
  exact (Measurable.exists (fun c => Measurable.exists (fun e =>
    ((measurable_windowRootEdge N).eq measurable_const).and
      (measurableSet_setOfPred.mp
        (measurableSet_uibhbotFixedCaptureRel r N (2 * N) c e true))))).setOf

private theorem aemeasurable_windowFromWords (N : ℕ) :
    AEMeasurable (fun w (j : Fin (2 * N + 1)) =>
      uibhbotConcatWalk w ((j : ℤ) - N)) uibhbotWordFamilyLaw := by
  let coords : (ℤ → List (Fin 3)) → Fin (2 * N) → List (Fin 3) := fun w i =>
    if i.val < N then w (i.val : ℤ) else w (-((i.val - N : ℕ) : ℤ) - 1)
  have hc : Measurable coords := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp only [coords]
    split_ifs <;> exact measurable_pi_apply _
  apply ((measurable_uibhbotWindowFromWords N).comp hc).aemeasurable.congr
  filter_upwards [uibhbotWordFamilyLaw_ae_hP2] with w hw
  obtain ⟨hw, _⟩ := hw
  funext j
  exact (uibhbotConcatWalk_eq_uibhbotWindowFromWords N w
    (fun k _ _ => (hw k).1) j).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The decoded-window class law is also the pushforward of the canonical code law. -/
theorem uibhbotWindowClassLaw_eq_code_map (N r : ℕ) :
    uibhbotWindowClassLaw N r =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => uibhbotWindowStageBallClass N r (shiftedStream W N)) := by
  rw [uibhbotWindowClassLaw_eq_map, uibhbotEncodingWindowLaw,
    AEMeasurable.map_map_of_aemeasurable
      (measurable_uibhbotDecodedWindowBallClass N r).aemeasurable
      (aemeasurable_windowFromWords N)]
  change _ = (uibhbotWordFamilyLaw.map uibhbotCodeWordRel).map _
  have hg : Measurable (fun W : ℤ → Fin 3 =>
      uibhbotWindowStageBallClass N r (shiftedStream W N)) :=
    (measurable_uibhbotWindowStageBallClass N r).comp (measurable_windowShift N)
  rw [Measure.map_map hg measurable_uibhbotCodeWordRel]
  apply Measure.map_congr
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w hw
  obtain ⟨hw, _, _⟩ := hw
  change uibhbotDecodedWindowBallClass N r _ =
    uibhbotWindowStageBallClass N r (shiftedStream (uibhbotCodeWordRel w) N)
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact uibhbotDecodedWindowBallClass_concat N r w hw

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every subset of complete framed classes satisfies the capture-failure error bound. -/
theorem uibhbotBSBallLaw_sub_windowClassLaw_le (N r : ℕ) (hr : 0 < r)
    (A : Set FramedBallClass) :
    |(uibhbotBSBallLaw r hr : Measure FramedBallClass).real A -
        (uibhbotWindowClassLaw N r).real A| ≤
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).real
        {W | ¬ (WholePlaneRotationHypothesis W ∧
          ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
            (kmswLLCreatedEdge (shiftedStream W N) N) true)} := by
  have hA : MeasurableSet A := MeasurableSpace.measurableSet_top
  have hf := measurable_uibhbotBallClassRel r hr
  have hg : Measurable (fun W =>
      uibhbotWindowStageBallClass N r (shiftedStream W N)) :=
    (measurable_uibhbotWindowStageBallClass N r).comp (measurable_windowShift N)
  rw [uibhbotWindowClassLaw_eq_code_map]
  change |((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    (fun W => uibhbotBallClassRel W r hr)).real A - _| ≤ _
  rw [map_measureReal_apply hf hA, map_measureReal_apply hg hA]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hf hA).nullMeasurableSet (hg hA).nullMeasurableSet).trans
  refine measureReal_mono ?_ (by finiteness)
  intro W hW hcap
  have he := uibhbotBallClassRel_eq_windowStageClass W hcap.1 N r hr hcap.2
  change (uibhbotBallClassRel W r hr ∈ A ∧
      uibhbotWindowStageBallClass N r (shiftedStream W N) ∉ A) ∨
    (uibhbotWindowStageBallClass N r (shiftedStream W N) ∈ A ∧
      uibhbotBallClassRel W r hr ∉ A) at hW
  rw [he] at hW
  exact hW.elim (fun h => h.2 h.1) (fun h => h.2 h.1)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Certified relaxed captures with the canonical window root hold eventually,
including rotation, all global seam certificates and prefix floors. -/
theorem uibhbotWordFamilyLaw_ae_eventualWindowCertifiedCapture (r : ℕ) :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ N₀, ∀ N ≥ N₀, WholePlaneRotationHypothesis W ∧
          ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
            (kmswLLCreatedEdge (shiftedStream W N) N) true := by
  filter_upwards [uibhbotWordFamilyLaw_ae_eventualWholePlaneBall,
    uibhbotWordFamilyLaw_ae_hP2, ae_uibhbotConcatWalk_snd_unbounded_below]
    with w hball hP2 hP1
  obtain ⟨hw, hball⟩ := hball
  obtain ⟨hw', hP2⟩ := hP2
  have hproof : hw' = hw := Subsingleton.elim _ _
  subst hw'
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨A, hA⟩ := hball (r + 1)
  obtain ⟨B, hB⟩ := uibhbotCodeWord_eventualLeftSeamBarrier w hw hP1 hP2 (r + 1)
  refine ⟨hw, max (max A B) 1, ?_⟩
  intro N hN
  have hAN : A ≤ N := (Nat.le_max_left A B).trans
    ((Nat.le_max_left (max A B) 1).trans hN)
  have hBN : B ≤ N := (Nat.le_max_right A B).trans
    ((Nat.le_max_left (max A B) 1).trans hN)
  have h1N : 1 ≤ N := (Nat.le_max_right (max A B) 1).trans hN
  have hev := hA N hAN
  obtain ⟨hc, d, hd, he, hm⟩ :=
    uibhbotRelaxedCapture_rootDart_exists w hw N (2 * N) h1N (by omega)
  have hs : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) (r + 1)
        (activeInitial (shiftedStream W N) N),
      minL (shiftedStream W M) (M - N + k) = L (shiftedStream W M) (M - N + k) ∧
      ∀ j ≤ M - N,
        L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j := by
    intro M hNM k hk
    have hg := uibhbotCodeWord_minL_eq_of_leftSeamBarrier w hw N k
      (hev.2.1 k hk) (hB N hBN k hk) M hNM
    refine ⟨hg, ?_⟩
    intro j hj
    have hle := runningMin_le (L (shiftedStream W M)) (M - N + k) j (by omega)
    change minL (shiftedStream W M) (M - N + k) ≤ _ at hle
    rw [hg] at hle
    exact hle
  let C : UIBHBOTCertifiedRootCapture W r :=
    ⟨N, 2 * N, activeInitial (shiftedStream W N) N, hev.1, hs, hc, d, hd, he, hm⟩
  refine ⟨uibhbotCodeWord_rotationHypothesis w hw hP1 hP2,
    activeInitial (shiftedStream W N) N, ?_⟩
  apply (uibhbotFixedCaptureRel_iff W r N (2 * N) _ _ true).mpr
  refine ⟨C, rfl, rfl, rfl, ?_, ?_⟩
  · exact wholePlaneEdgeι_injective W N
      (he.trans (uibhbotRootEdge_eq_window_of_stopped w hw N h1N))
  · exact uibhbotRelaxedCapture_rootDart_side W N (2 * N) _ hc d hd he

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The decoded-window class law has total mass one. -/
theorem uibhbotWindowClassLaw_probability (N r : ℕ) :
    IsProbabilityMeasure (uibhbotWindowClassLaw N r) := by
  rw [uibhbotWindowClassLaw_eq_code_map]
  infer_instance

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The comparison chain ends at the class of the decoded window itself. -/
theorem uibhbotBallClassRel_eq_decodedWindowClass (N r : ℕ) (hr : 0 < r)
    (w : ℤ → List (Fin 3)) (hw : ∀ k, IsStoppedExcursionWord (w k))
    (H : WholePlaneRotationHypothesis (uibhbotCodeWord w (fun k => (hw k).1)))
    (hcap : ∃ c, uibhbotFixedCaptureRel (uibhbotCodeWord w (fun k => (hw k).1))
      r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) N)
      true) :
    uibhbotBallClassRel (uibhbotCodeWord w (fun k => (hw k).1)) r hr =
      uibhbotDecodedWindowBallClass N r
        (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)) :=
  (uibhbotBallClassRel_eq_windowStageClass _ H N r hr hcap).trans
    (uibhbotDecodedWindowBallClass_concat N r w hw).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The canonical code law almost surely has certified captures at every sufficiently
large symmetric window, with its specified missing-root dart. -/
theorem uibhbotCodeLawRel_ae_eventualWindowCertifiedCapture (r : ℕ) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ N₀, ∀ N ≥ N₀, WholePlaneRotationHypothesis W ∧
        ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
          (kmswLLCreatedEdge (shiftedStream W N) N) true := by
  have hm : MeasurableSet {W : ℤ → Fin 3 | ∃ n, ∀ N ≥ n,
      WholePlaneRotationHypothesis W ∧
        ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
          (kmswLLCreatedEdge (shiftedStream W N) N) true} := by
    exact (Measurable.exists (fun n => Measurable.forall (fun N =>
      Measurable.forall (fun (_ : n ≤ N) => measurableSet_setOfPred.mp
        (measurableSet_uibhbotWindowCertifiedCapture N r))))).setOf
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hm).mpr
  filter_upwards [uibhbotWordFamilyLaw_ae_eventualWindowCertifiedCapture r] with w hw
  obtain ⟨hw, hcap⟩ := hw
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact hcap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The probability that the specified symmetric window lacks a certified capture
tends to zero. The proof uses continuity from above on future-failure unions;
individual capture events need not be monotone. -/
theorem tendsto_uibhbotWindow_noCertifiedCapture (r : ℕ) :
    Tendsto (fun N => (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).real
      {W | ¬ ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
        (kmswLLCreatedEdge (shiftedStream W N) N) true}) atTop (𝓝 0) := by
  let μ := (uibhbotCodeLawRel : Measure (ℤ → Fin 3))
  let B : ℕ → Set (ℤ → Fin 3) := fun n => {W | ∃ N, n ≤ N ∧
    ¬ (WholePlaneRotationHypothesis W ∧
      ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
        (kmswLLCreatedEdge (shiftedStream W N) N) true)}
  have hB (n : ℕ) : MeasurableSet (B n) := by
    exact (Measurable.exists (fun N => measurable_const.and
      (measurableSet_setOfPred.mp
        (measurableSet_uibhbotWindowCertifiedCapture N r)).not)).setOf
  have hmono : Antitone B := by
    intro n m hnm W hW
    obtain ⟨N, hN, hbad⟩ := hW
    exact ⟨N, hnm.trans hN, hbad⟩
  have hzero : μ (⋂ n, B n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [uibhbotCodeLawRel_ae_eventualWindowCertifiedCapture r] with W hW
    obtain ⟨n, hn⟩ := hW
    intro hmem
    obtain ⟨N, hN, hbad⟩ := Set.mem_iInter.mp hmem n
    exact hbad (hn N hN)
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hB n).nullMeasurableSet) hmono ⟨0, by finiteness⟩
  rw [hzero] at hlim
  have hreal : Tendsto (fun n => μ.real (B n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hreal
  intro N
  refine measureReal_mono ?_ (by finiteness)
  intro W hW
  exact ⟨N, le_rfl, fun h => hW h.2⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
For every subset, the error is bounded by failure of capture alone; rotation
failure contributes zero probability under the canonical code law. -/
theorem uibhbotBSBallLaw_sub_windowClassLaw_le_noCapture (N r : ℕ) (hr : 0 < r)
    (A : Set FramedBallClass) :
    |(uibhbotBSBallLaw r hr : Measure FramedBallClass).real A -
        (uibhbotWindowClassLaw N r).real A| ≤
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).real
        {W | ¬ ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
          (kmswLLCreatedEdge (shiftedStream W N) N) true} := by
  refine (uibhbotBSBallLaw_sub_windowClassLaw_le N r hr A).trans_eq ?_
  apply measureReal_congr
  filter_upwards [uibhbotCodeLawRel_ae_ballClassRel_event r] with W hW
  exact propext (by simp only [hW.1, true_and])

end DirectedDistances.PaperProofs.Section5
