module

public import DirectedDistances.Recursive.BusemannWindowLimitContinuity

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk
open DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv); unconditional pathwise identity
for 0 < S < T; not a paper result.
from [0,T] to [0,S] gives the same scaled partial-sum path. -/
theorem ldpBusemannWindow_restrict {n : ℕ} {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (ω : ℕ → Fin 3) :
    restrictJ1Window hS hST (ldpBusemannWindow n (lt_trans hS hST) ω) =
      ldpBusemannWindow n hS ω := by
  change J1WindowD.mk (restrictJ1Window hS hST
    (ldpBusemannWindow n (lt_trans hS hST) ω)).path =
      J1WindowD.mk (ldpBusemannWindow n hS ω).path
  apply congrArg (fun p : CadlagWindow S => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  simp only [restrictJ1Window_apply, ldpBusemannWindow_apply,
    restrictWindowTime]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); unconditional pathwise identity
for 0 < S < T; not a paper result.
from [0,T] to [0,S] gives the same scaled partial-sum path. -/
theorem sdpBusemannWindow_restrict {n : ℕ} {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (ω : ℕ → Fin 3) :
    restrictJ1Window hS hST (sdpBusemannWindow n (lt_trans hS hST) ω) =
      sdpBusemannWindow n hS ω := by
  change J1WindowD.mk (restrictJ1Window hS hST
    (sdpBusemannWindow n (lt_trans hS hST) ω)).path =
      J1WindowD.mk (sdpBusemannWindow n hS ω).path
  apply congrArg (fun p : CadlagWindow S => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  simp only [restrictJ1Window_apply, sdpBusemannWindow_apply,
    restrictWindowTime]

private theorem measurableLdpBusemannWindow {n : ℕ} {T : ℝ} (hT : 0 < T) :
    Measurable (ldpBusemannWindow n hT) := by
  apply measurable_scaledPartialSumWindow
  intro j
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _))

private theorem measurableSdpBusemannWindow {n : ℕ} {T : ℝ} (hT : 0 < T) :
    Measurable (sdpBusemannWindow n hT) := by
  apply measurable_scaledPartialSumWindow
  intro j
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _))

private theorem ldpBusemannWindowLaw_restrict {n : ℕ} {S T : ℝ}
    (hS : 0 < S) (hST : S < T) :
    (ldpBusemannWindowLaw n (lt_trans hS hST)).map
      (restrictJ1Window hS hST) = ldpBusemannWindowLaw n hS := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (ldpBusemannWindow n (lt_trans hS hST))).map
      (restrictJ1Window hS hST) =
    iidCodeMeasure.map (ldpBusemannWindow n hS)
  rw [Measure.map_map (measurable_restrictJ1Window hS hST)
    (measurableLdpBusemannWindow (lt_trans hS hST))]
  congr 1

private theorem sdpBusemannWindowLaw_restrict {n : ℕ} {S T : ℝ}
    (hS : 0 < S) (hST : S < T) :
    (sdpBusemannWindowLaw n (lt_trans hS hST)).map
      (restrictJ1Window hS hST) = sdpBusemannWindowLaw n hS := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (sdpBusemannWindow n (lt_trans hS hST))).map
      (restrictJ1Window hS hST) =
    iidCodeMeasure.map (sdpBusemannWindow n hS)
  rw [Measure.map_map (measurable_restrictJ1Window hS hST)
    (measurableSdpBusemannWindow (lt_trans hS hST))]
  congr 1

/-- Helper toward Theorem 1.6 (thm-busemann-conv); the conditions are hind, hsym, and
ν_T-almost-everywhere continuity at S (hcont) for the selected limit ν_T;
not a paper result.
are consistent under restriction, assuming almost-everywhere continuity at S. -/
theorem ldp_busemann_window_limit_restrict
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T)
    (hcont : ∀ᵐ x ∂((Classical.choose
      (ldp_busemann_window_tendsto hind hsym (lt_trans hS hST)) :
        ProbabilityMeasure (J1WindowD T (lt_trans hS hST))) :
        Measure (J1WindowD T (lt_trans hS hST))),
      ContinuousAt x.path.1 (⟨S, hS.le, hST.le⟩ : J1Window T)) :
    (Classical.choose
      (ldp_busemann_window_tendsto hind hsym (lt_trans hS hST))).map
        (restrictJ1Window hS hST) =
      Classical.choose (ldp_busemann_window_tendsto hind hsym hS) := by
  let νT : ProbabilityMeasure (J1WindowD T (lt_trans hS hST)) :=
    Classical.choose (ldp_busemann_window_tendsto hind hsym (lt_trans hS hST))
  let νS : ProbabilityMeasure (J1WindowD S hS) :=
    Classical.choose (ldp_busemann_window_tendsto hind hsym hS)
  have hTlim := (Classical.choose_spec
    (ldp_busemann_window_tendsto hind hsym (lt_trans hS hST))).1
  have hSlim := (Classical.choose_spec
    (ldp_busemann_window_tendsto hind hsym hS)).1
  have hmap := tendsto_map_of_ae_continuousAt
    (fun n => ldpBusemannWindowLaw n (lt_trans hS hST)) νT hTlim
    (restrictJ1Window hS hST) (measurable_restrictJ1Window hS hST) ?_
  · have hrestrict : Tendsto
        (fun n => ldpBusemannWindowLaw n hS) atTop (𝓝 (νT.map
          (restrictJ1Window hS hST))) := by
      apply hmap.congr'
      filter_upwards [] with n
      exact (ldpBusemannWindowLaw_restrict (n := n) hS hST)
    have hlimS : Tendsto (fun n => ldpBusemannWindowLaw n hS) atTop (𝓝 νS) :=
      hSlim
    exact tendsto_nhds_unique hrestrict hlimS
  · filter_upwards [hcont] with x hx
    exact continuousAt_restrictJ1Window_of_path_continuousAt hS hST x hx

/-- Helper toward Theorem 1.6 (thm-busemann-conv); the conditions are hind, hsym, and
ν_T-almost-everywhere continuity at S (hcont) for the selected limit ν_T;
not a paper result.
are consistent under restriction, assuming almost-everywhere continuity at S. -/
theorem sdp_busemann_window_limit_restrict
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T)
    (hcont : ∀ᵐ x ∂((Classical.choose
      (sdp_busemann_window_tendsto hind hsym (lt_trans hS hST)) :
        ProbabilityMeasure (J1WindowD T (lt_trans hS hST))) :
        Measure (J1WindowD T (lt_trans hS hST))),
      ContinuousAt x.path.1 (⟨S, hS.le, hST.le⟩ : J1Window T)) :
    (Classical.choose
      (sdp_busemann_window_tendsto hind hsym (lt_trans hS hST))).map
        (restrictJ1Window hS hST) =
      Classical.choose (sdp_busemann_window_tendsto hind hsym hS) := by
  let νT : ProbabilityMeasure (J1WindowD T (lt_trans hS hST)) :=
    Classical.choose (sdp_busemann_window_tendsto hind hsym (lt_trans hS hST))
  let νS : ProbabilityMeasure (J1WindowD S hS) :=
    Classical.choose (sdp_busemann_window_tendsto hind hsym hS)
  have hTlim := (Classical.choose_spec
    (sdp_busemann_window_tendsto hind hsym (lt_trans hS hST))).1
  have hSlim := (Classical.choose_spec
    (sdp_busemann_window_tendsto hind hsym hS)).1
  have hmap := tendsto_map_of_ae_continuousAt
    (fun n => sdpBusemannWindowLaw n (lt_trans hS hST)) νT hTlim
    (restrictJ1Window hS hST) (measurable_restrictJ1Window hS hST) ?_
  · have hrestrict : Tendsto
        (fun n => sdpBusemannWindowLaw n hS) atTop (𝓝 (νT.map
          (restrictJ1Window hS hST))) := by
      apply hmap.congr'
      filter_upwards [] with n
      exact (sdpBusemannWindowLaw_restrict (n := n) hS hST)
    have hlimS : Tendsto (fun n => sdpBusemannWindowLaw n hS) atTop (𝓝 νS) :=
      hSlim
    exact tendsto_nhds_unique hrestrict hlimS
  · filter_upwards [hcont] with x hx
    exact continuousAt_restrictJ1Window_of_path_continuousAt hS hST x hx

end DirectedDistances.Recursive
