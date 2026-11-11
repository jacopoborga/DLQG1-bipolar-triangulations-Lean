module

public import DirectedDistances.PaperProofs.Section4.FinitePastIndependenceFirstHitKernel
public import DirectedDistances.PaperProofs.Section4.FirstHitXDPIdentification

/-! conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. The finite natural number is
decoded from the extended distance: non-finite values (LDP ⊥ or SDP ⊤) decode to 0;
this convention is used only on a μ-null set, since the distance is proved a.s. equal
to the finite past-map length. -/
@[expose] noncomputable def firstHitCodeXdpDistance (x : XDP) (r : ℕ)
    (p : ℕ → ℤ × ℤ) : ℕ :=
  let t := (conditionedSecondCoordinateFirstHit r p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  match x with
  | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
      (presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t))
  | .sdp => (sdp (⟨0⟩ : PresentVertex w) (recordVertex w t)).toNat

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. This declaration identifies
the decoded (natural-valued) code-graph distance with the stopped-past length almost
surely; the
decoder's convention that non-finite values (LDP ⊥ or SDP ⊤) decode to 0 is therefore
used only on a μ-null set. -/
theorem firstHitCodeXdpDistance_ae_eq_pastLength (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      firstHitCodeXdpDistance x r p =
        firstHitPastXdpLength x r (stoppedMap r hr (pathCode p)) := by
  cases x with
  | ldp =>
    filter_upwards [firstHitPastXdpLength_ae_eq_shifted_limit r hr] with p hp
    let t := (conditionedSecondCoordinateFirstHit r p).toNat
    let w := boltzmannKMSWStream (pathCode p)
    change WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
      (presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t)) = _
    have h := congrArg (fun d : WithBot ℕ∞ =>
      WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun n : ℕ∞ => n.toNat) d) hp.1
    calc
      _ = WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun n : ℕ∞ => n.toNat)
          (((firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) : ℕ∞) :
            WithBot ℕ∞)) := h.symm
      _ = _ := by simp only [WithBot.recBotCoe_coe, ENat.toNat_natCast]
  | sdp =>
    filter_upwards [firstHitPastXdpLength_ae_eq_shifted_limit r hr] with p hp
    let t := (conditionedSecondCoordinateFirstHit r p).toNat
    let w := boltzmannKMSWStream (pathCode p)
    change (sdp (⟨0⟩ : PresentVertex w) (recordVertex w t)).toNat = _
    have h := congrArg ENat.toNat hp.2
    calc
      _ = (firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) :
        ℕ∞).toNat := h.symm
      _ = _ := by simp

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. This is its conditioning
variable. -/
@[expose] noncomputable def firstHitCodeDistanceConditioning (x : XDP) (r : ℕ)
    (_hr : 1 ≤ r) (p : ℕ → ℤ × ℤ) : (ℕ → ℤ × ℤ) × ℕ :=
  (conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p,
    firstHitCodeXdpDistance x r p)

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. The conditioning variables
agree almost surely with the measurable stopped-past version. -/
theorem firstHitCodeDistanceConditioning_ae_eq_pastConditioning (x : XDP)
    (r : ℕ) (hr : 1 ≤ r) :
    firstHitCodeDistanceConditioning x r hr =ᵐ[conditionedVectorPathLaw 0 0]
      fun p =>
        (conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p,
          firstHitPastXdpLength x r (stoppedMap r hr (pathCode p))) := by
  filter_upwards [firstHitCodeXdpDistance_ae_eq_pastLength x r hr] with p hp
  simp only [firstHitCodeDistanceConditioning, hp]

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. The conditioning variable
is almost surely measurable. -/
theorem aemeasurable_firstHitCodeDistanceConditioning (x : XDP) (r : ℕ)
    (hr : 1 ≤ r) :
    AEMeasurable (firstHitCodeDistanceConditioning x r hr)
      (conditionedVectorPathLaw 0 0) := by
  have hEq := firstHitCodeDistanceConditioning_ae_eq_pastConditioning x r hr
  have hPast : Measurable (fun p : ℕ → ℤ × ℤ =>
      (conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p,
        firstHitPastXdpLength x r (stoppedMap r hr (pathCode p)))) :=
    (measurable_conditionedFirstHit_future r).prodMk
    ((measurable_firstHitPastXdpLength x r).comp
      ((measurable_stoppedMap r hr).comp measurable_pathCode))
  exact hPast.aemeasurable.congr hEq.symm

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. This is the conditional-law
statement. -/
theorem firstHitCodeDistance_condDistrib (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let M := fun p => stoppedMap r hr (pathCode p)
    let C := firstHitPastAllCuts x r ∘ M
    condDistrib C (firstHitCodeDistanceConditioning x r hr) μ =ᵐ[
      μ.map (firstHitCodeDistanceConditioning x r hr)] firstHitPastCutsKernel x r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let M := fun p : ℕ → ℤ × ℤ => stoppedMap r hr (pathCode p)
  let Y := fun p : ℕ → ℤ × ℤ =>
    conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let Bcode := firstHitCodeDistanceConditioning x r hr
  let C := firstHitPastAllCuts x r ∘ M
  have hEq := firstHitCodeDistanceConditioning_ae_eq_pastConditioning x r hr
  have hMap : μ.map Bcode = μ.map B := Measure.map_congr hEq
  have hOld := firstHitPastAllCuts_condDistrib x r hr
  change condDistrib C B μ =ᵐ[μ.map B] firstHitPastCutsKernel x r hr at hOld
  rw [← hMap] at hOld
  have hCond : condDistrib C B μ = condDistrib C Bcode μ :=
    condDistrib_congr_right (Y := C) hEq.symm
  rw [hCond] at hOld
  exact hOld

/-- conditional independence of the past cut outputs given the uncentered future and
the code-graph XDP distance from the source to the cut vertex at τ_r; the
renewal-time selection T_{m_k}, the T_0 branch and the infinite source-map (F4c)
identification are not treated; not the paper result. This is the conditional-
independence statement. -/
theorem firstHitCodeDistance_conditionalIndependence (x : XDP) (r : ℕ)
    (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let M := fun p => stoppedMap r hr (pathCode p)
    let C := firstHitPastAllCuts x r ∘ M
    condDistrib C (firstHitCodeDistanceConditioning x r hr) μ =ᵐ[
      μ.map (firstHitCodeDistanceConditioning x r hr)] fun b =>
        (condDistrib (fun p => (C p).1) (firstHitCodeDistanceConditioning x r hr) μ b).prod
          (condDistrib (fun p => (C p).2)
            (firstHitCodeDistanceConditioning x r hr) μ b) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let M := fun p : ℕ → ℤ × ℤ => stoppedMap r hr (pathCode p)
  let Y := fun p : ℕ → ℤ × ℤ =>
    conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let Bcode := firstHitCodeDistanceConditioning x r hr
  let C := firstHitPastAllCuts x r ∘ M
  have hEq := firstHitCodeDistanceConditioning_ae_eq_pastConditioning x r hr
  have hMap : μ.map Bcode = μ.map B := Measure.map_congr hEq
  have hOld := firstHitPastAllCuts_conditionalIndependence x r hr
  change condDistrib C B μ =ᵐ[μ.map B] fun b =>
    (condDistrib (fun p => (C p).1) B μ b).prod
      (condDistrib (fun p => (C p).2) B μ b) at hOld
  rw [← hMap] at hOld
  have hCond : condDistrib C B μ = condDistrib C Bcode μ :=
    condDistrib_congr_right (Y := C) hEq.symm
  have hLeft : condDistrib (fun p => (C p).1) B μ =
      condDistrib (fun p => (C p).1) Bcode μ :=
    condDistrib_congr_right (Y := fun p => (C p).1) hEq.symm
  have hRight : condDistrib (fun p => (C p).2) B μ =
      condDistrib (fun p => (C p).2) Bcode μ :=
    condDistrib_congr_right (Y := fun p => (C p).2) hEq.symm
  filter_upwards [hOld] with b hb
  change condDistrib C Bcode μ b =
    ((condDistrib (fun p => (C p).1) Bcode μ b).prod
      (condDistrib (fun p => (C p).2) Bcode μ b))
  rw [← hCond, ← hLeft, ← hRight]
  exact hb

end DirectedDistances.PaperProofs.Section4
