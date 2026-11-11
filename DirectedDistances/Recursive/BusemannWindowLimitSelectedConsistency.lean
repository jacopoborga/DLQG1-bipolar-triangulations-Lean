module

public import DirectedDistances.Recursive.BusemannWindowLimitConsistency
public import DirectedDistances.Recursive.BusemannWindowLimitNoFixedJumps

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
limits are consistent under restriction for every 0 < S < T. -/
theorem ldp_busemann_window_limit_consistent
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    (Classical.choose
      (ldp_busemann_window_tendsto hind hsym (lt_trans hS hST))).map
        (restrictJ1Window hS hST) =
      Classical.choose (ldp_busemann_window_tendsto hind hsym hS) := by
  apply ldp_busemann_window_limit_restrict hind hsym hS hST
  simpa only using
    (ldp_busemann_window_fixed_time_continuous hind hsym
      (T := T) (hT := lt_trans hS hST)
      (⟨S, hS.le, hST.le⟩ : J1Window T) hST)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
limits are consistent under restriction for every 0 < S < T. -/
theorem sdp_busemann_window_limit_consistent
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    (Classical.choose
      (sdp_busemann_window_tendsto hind hsym (lt_trans hS hST))).map
        (restrictJ1Window hS hST) =
      Classical.choose (sdp_busemann_window_tendsto hind hsym hS) := by
  apply sdp_busemann_window_limit_restrict hind hsym hS hST
  simpa only using
    (sdp_busemann_window_fixed_time_continuous hind hsym
      (T := T) (hT := lt_trans hS hST)
      (⟨S, hS.le, hST.le⟩ : J1Window T) hST)



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
positive real LDP window, the selected limit is almost surely continuous. -/
theorem ldpBusemannWindowLimit_continuousAt
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) (t : J1Window T) (htT : (t : ℝ) < T) :
    ∀ᵐ x : J1WindowD T hT
      ∂(((Classical.choose (ldp_busemann_window_tendsto hind hsym hT) :
        ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT))),
      ContinuousAt x.path.1 t := by
  exact ldp_busemann_window_fixed_time_continuous hind hsym hT t htT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
positive real SDP window, the selected limit is almost surely continuous. -/
theorem sdpBusemannWindowLimit_continuousAt
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) (t : J1Window T) (htT : (t : ℝ) < T) :
    ∀ᵐ x : J1WindowD T hT
      ∂(((Classical.choose (sdp_busemann_window_tendsto hind hsym hT) :
        ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT))),
      ContinuousAt x.path.1 t := by
  exact sdp_busemann_window_fixed_time_continuous hind hsym hT t htT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
integer window [0,m+1]. -/
@[expose] noncomputable def ldpBusemannIntegerWindowLimit
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (m : ℕ) :
    ProbabilityMeasure
      (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)) :=
  Classical.choose (ldp_busemann_window_tendsto hind hsym (by positivity))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
integer window [0,m+1]. -/
@[expose] noncomputable def sdpBusemannIntegerWindowLimit
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (m : ℕ) :
    ProbabilityMeasure
      (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)) :=
  Classical.choose (sdp_busemann_window_tendsto hind hsym (by positivity))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
projective under restriction from [0,m+2] to [0,m+1]. -/
theorem ldpBusemannIntegerWindowLimit_projective
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (m : ℕ) :
    (ldpBusemannIntegerWindowLimit hind hsym (m + 1)).map
      (restrictJ1Window (by positivity) (by norm_cast; omega)) =
        ldpBusemannIntegerWindowLimit hind hsym m := by
  have h := ldp_busemann_window_limit_consistent hind hsym
    (S := ((m + 1 : ℕ) : ℝ)) (T := (((m + 1) + 1 : ℕ) : ℝ))
    (by positivity) (by norm_cast; omega)
  simpa [ldpBusemannIntegerWindowLimit] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
projective under restriction from [0,m+2] to [0,m+1]. -/
theorem sdpBusemannIntegerWindowLimit_projective
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (m : ℕ) :
    (sdpBusemannIntegerWindowLimit hind hsym (m + 1)).map
      (restrictJ1Window (by positivity) (by norm_cast; omega)) =
        sdpBusemannIntegerWindowLimit hind hsym m := by
  have h := sdp_busemann_window_limit_consistent hind hsym
    (S := ((m + 1 : ℕ) : ℝ)) (T := (((m + 1) + 1 : ℕ) : ℝ))
    (by positivity) (by norm_cast; omega)
  simpa [sdpBusemannIntegerWindowLimit] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
surely continuous at every integer time strictly before its window endpoint. -/
theorem ldpBusemannIntegerWindowLimit_continuousAt
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (m k : ℕ) (hkm : k ≤ m) :
    ∀ᵐ x : J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)
      ∂(ldpBusemannIntegerWindowLimit hind hsym m :
        Measure (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))),
      ContinuousAt x.path.1
        (⟨(k : ℝ), by positivity,
          (show (k : ℝ) < ((m + 1 : ℕ) : ℝ) by norm_cast; omega).le⟩ :
            J1Window ((m + 1 : ℕ) : ℝ)) := by
  have hkT : (k : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  have h := ldp_busemann_window_fixed_time_continuous hind hsym
    (T := ((m + 1 : ℕ) : ℝ)) (hT := by positivity)
    (⟨(k : ℝ), by positivity, hkT.le⟩ : J1Window ((m + 1 : ℕ) : ℝ)) hkT
  simpa [ldpBusemannIntegerWindowLimit] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
surely continuous at every integer time strictly before its window endpoint. -/
theorem sdpBusemannIntegerWindowLimit_continuousAt
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (m k : ℕ) (hkm : k ≤ m) :
    ∀ᵐ x : J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)
      ∂(sdpBusemannIntegerWindowLimit hind hsym m :
        Measure (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))),
      ContinuousAt x.path.1
        (⟨(k : ℝ), by positivity,
          (show (k : ℝ) < ((m + 1 : ℕ) : ℝ) by norm_cast; omega).le⟩ :
            J1Window ((m + 1 : ℕ) : ℝ)) := by
  have hkT : (k : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  have h := sdp_busemann_window_fixed_time_continuous hind hsym
    (T := ((m + 1 : ℕ) : ℝ)) (hT := by positivity)
    (⟨(k : ℝ), by positivity, hkT.le⟩ : J1Window ((m + 1 : ℕ) : ℝ)) hkT
  simpa [sdpBusemannIntegerWindowLimit] using h

end DirectedDistances.Recursive
