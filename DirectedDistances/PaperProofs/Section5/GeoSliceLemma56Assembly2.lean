/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceMeasurableReduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusMeasurableDescent

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6. Normalize left cut presentations to the
nonnegative thin carrier. In the nonpositive layout, the absent prefix is
filled by a fixed code and the primed and hatted blocks retain their order. -/
noncomputable def lMinusThinIntoLPlus (c : LMinusThinPresentation) :
    LPlusThinPresentation := (fun _ => 0, c.2, c.1)

/-- Helper toward Lemma 5.6. Normalize the nonnegative right code to the
nonpositive thin carrier by adjoining a fixed unused prefix. -/
noncomputable def rPlusThinIntoRMinus (c : RightThinCode) :
    RMinusThinPresentation := (fun _ => 0, c)

theorem measurable_lMinusThinIntoLPlus : Measurable lMinusThinIntoLPlus := by
  exact measurable_const.prodMk (measurable_snd.prodMk measurable_fst)

theorem measurable_rPlusThinIntoRMinus : Measurable rPlusThinIntoRMinus := by
  exact measurable_const.prodMk measurable_id

/-- Helper toward Lemma 5.6. The left cut observation is represented in one
standard Borel thin carrier. For `j > 0` it is the L-plus presentation; for
`j ≤ 0` it is the equivalent normalized L-minus presentation. -/
noncomputable def geoSlice56LeftCutObservation (x : XDP) (j : ℤ)
    (W : ℤ → Fin 3) : LPlusThinPresentation :=
  if 0 < j then
    lPlusThinPresentationRetract x (decodeLPlus x j (leftSideObsNonneg x j W))
  else
    lMinusThinIntoLPlus
      (lMinusThinPresentationRetract x (decodeLMinus x j (leftSideObsNonpos x j W)))

/-- Helper toward Lemma 5.6. The right cut observation is represented in one
standard Borel thin carrier. For `j ≥ 0` it is the R-plus hatted code with a
fixed unused prefix; for `j < 0` it is the R-minus presentation. -/
noncomputable def geoSlice56RightCutObservation (x : XDP) (j : ℤ)
    (W : ℤ → Fin 3) : RMinusThinPresentation :=
  if 0 ≤ j then
    rPlusThinIntoRMinus (rightThinCodeRetract (rightSideObsNonneg x j W))
  else
    rMinusThinPresentationRetract x
      (decodeRMinus x j (rightSideObsNonpos x j W))

theorem aemeasurable_geoSlice56LeftCutObservation (x : XDP) (j : ℤ) :
    AEMeasurable (geoSlice56LeftCutObservation x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 < j
  · unfold geoSlice56LeftCutObservation
    simp only [if_pos hj]
    exact (measurable_lPlusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeLPlus_leftSideObsNonneg x j)
  · unfold geoSlice56LeftCutObservation
    simp only [if_neg hj]
    exact ((measurable_lMinusThinIntoLPlus.comp
      (measurable_lMinusThinPresentationRetract x)).comp_aemeasurable
      (aemeasurable_decodeLMinus_leftSideObsNonpos x j))

theorem aemeasurable_geoSlice56RightCutObservation (x : XDP) (j : ℤ) :
    AEMeasurable (geoSlice56RightCutObservation x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 ≤ j
  · unfold geoSlice56RightCutObservation
    simp only [if_pos hj]
    exact (measurable_rPlusThinIntoRMinus.comp measurable_rightThinCodeRetract).comp_aemeasurable
      (aemeasurable_boundaryFourObservations x j 2)
  · unfold geoSlice56RightCutObservation
    simp only [if_neg hj]
    exact (measurable_rMinusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeRMinus_rightSideObsNonpos x j)

/-- Helper toward Lemma 5.6. The two normalized cut presentations remain
independent by the proved nonnegative and nonpositive presentation results. -/
theorem geoSlice56LeftRightCutIndependent (x : XDP) (j : ℤ) :
    IndepFun (geoSlice56LeftCutObservation x j)
      (geoSlice56RightCutObservation x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 < j
  · unfold geoSlice56LeftCutObservation geoSlice56RightCutObservation
    have hj' : 0 ≤ j := by omega
    simp only [if_pos hj, if_pos hj']
    have hright : Measurable
        (fun r : RPlusSidePresentation x =>
          rPlusThinIntoRMinus (rightThinCodeRetract r.code)) := by
      exact (measurable_rPlusThinIntoRMinus.comp
        (measurable_rightThinCodeRetract.comp
          (measurable_rPlusSidePresentation_code (x := x))))
    simpa [Function.comp_def, rPlusThinIntoRMinus, decodeRPlus] using
      (lemma55_nonneg_presentation_indepFun x j).comp
        (φ := lPlusThinPresentationRetract x)
        (ψ := fun r : RPlusSidePresentation x =>
          rPlusThinIntoRMinus (rightThinCodeRetract r.code))
        (measurable_lPlusThinPresentationRetract x)
        hright
  · by_cases hzero : j = 0
    · subst j
      unfold geoSlice56LeftCutObservation geoSlice56RightCutObservation
      simp only [lt_irrefl, if_false, le_refl, if_true]
      have hright : Measurable
          (fun r : RMinusSidePresentation x =>
            (fun _ : ℕ => (0 : Fin 3),
              (rMinusThinPresentationRetract x r).2)) := by
        exact (measurable_const.prodMk measurable_snd).comp
          (measurable_rMinusThinPresentationRetract x)
      simpa [Function.comp_def, rPlusThinIntoRMinus, decodeRMinus,
        rightSideObsNonpos, rightSideObsNonneg, rMinusThinPresentationRetract] using
        (lemma55_nonpos_presentation_indepFun x 0).comp
          (φ := fun r => lMinusThinIntoLPlus (lMinusThinPresentationRetract x r))
          (ψ := fun r : RMinusSidePresentation x =>
            (fun _ : ℕ => (0 : Fin 3),
              (rMinusThinPresentationRetract x r).2))
          (measurable_lMinusThinIntoLPlus.comp
            (measurable_lMinusThinPresentationRetract x)) hright
    · have hjneg : j < 0 := by omega
      unfold geoSlice56LeftCutObservation geoSlice56RightCutObservation
      simp only [if_neg (by omega : ¬ 0 < j), if_neg (by omega : ¬ 0 ≤ j)]
      simpa [Function.comp_def] using (lemma55_nonpos_presentation_indepFun x j).comp
          (φ := fun r => lMinusThinIntoLPlus (lMinusThinPresentationRetract x r))
          (ψ := rMinusThinPresentationRetract x)
          (measurable_lMinusThinIntoLPlus.comp (measurable_lMinusThinPresentationRetract x))
          (measurable_rMinusThinPresentationRetract x)

/-- Helper toward Lemma 5.6. The normalized left cut presentations have one
law throughout the nonpositive range, including the L-minus layout at zero. -/
theorem geoSlice56LeftCutObservation_law_eq_zero (x : XDP) (j : ℤ)
    (hj : j ≤ 0) :
    wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation x j) =
      wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation x 0) := by
  let Φ : LMinusSidePresentation x → LPlusThinPresentation :=
    fun r => lMinusThinIntoLPlus (lMinusThinPresentationRetract x r)
  have hΦ : Measurable Φ :=
    measurable_lMinusThinIntoLPlus.comp (measurable_lMinusThinPresentationRetract x)
  have hdec (k : ℤ) :
      AEMeasurable (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
        wholePlaneIIDCodeMeasure :=
    aemeasurable_decodeLMinus_leftSideObsNonpos x k
  have hj' : ¬ 0 < j := by omega
  unfold geoSlice56LeftCutObservation
  simp only [if_neg hj', if_neg (by decide : ¬ (0 : ℤ) < 0)]
  change wholePlaneIIDCodeMeasure.map
      (Φ ∘ fun W => decodeLMinus x j (leftSideObsNonpos x j W)) =
    wholePlaneIIDCodeMeasure.map
      (Φ ∘ fun W => decodeLMinus x 0 (leftSideObsNonpos x 0 W))
  rw [← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (hdec j),
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (hdec 0),
    decodeLMinus_leftSideObsNonpos_law_eq_zero x j hj]

/-- Helper toward Lemma 5.6. The normalized right cut presentations have one
law throughout the nonnegative range used for the positive-slice clause. -/
theorem geoSlice56RightCutObservation_law_eq_zero (x : XDP) (j : ℤ)
    (hj : 0 ≤ j) :
    wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation x j) =
      wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation x 0) := by
  let Ψ : RightThinCode → RMinusThinPresentation := rPlusThinIntoRMinus
  have hΨ : Measurable Ψ := measurable_rPlusThinIntoRMinus
  have hcode (k : ℤ) : AEMeasurable (rightSideObsNonneg x k)
      wholePlaneIIDCodeMeasure := by
    change AEMeasurable (boundaryFourObservations x k 2) wholePlaneIIDCodeMeasure
    exact aemeasurable_boundaryFourObservations x k 2
  unfold geoSlice56RightCutObservation
  simp only [if_pos hj, if_pos (show 0 ≤ (0 : ℤ) by omega)]
  change wholePlaneIIDCodeMeasure.map
      ((Ψ ∘ rightThinCodeRetract) ∘ rightSideObsNonneg x j) =
    wholePlaneIIDCodeMeasure.map
      ((Ψ ∘ rightThinCodeRetract) ∘ rightSideObsNonneg x 0)
  rw [← AEMeasurable.map_map_of_aemeasurable
      (hΨ.comp measurable_rightThinCodeRetract).aemeasurable (hcode j),
    ← AEMeasurable.map_map_of_aemeasurable
      (hΨ.comp measurable_rightThinCodeRetract).aemeasurable (hcode 0),
    rightSideObsNonneg_law_eq_zero x j hj]

/-- Helper toward Lemma 5.6. Almost-everywhere measurable slices whose past
and future restrictions factor through the independent thin presentations are
mutually independent. The determining functions in the hypotheses need not
be measurable; standard Borel factorization supplies measurable versions. -/
theorem lemma56_independent_of_presentationDetermination
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation x j W)) :
    iIndepFun G wholePlaneIIDCodeMeasure := by
  apply DirectedDistances.Probability.iIndepFun_of_indepFun_int_splits'
  intro j
  obtain ⟨f, hf⟩ := hPast j
  obtain ⟨g, hg⟩ := hFuture j
  have hPastAE : AEMeasurable
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) wholePlaneIIDCodeMeasure :=
    aemeasurable_pi_iff.mpr (fun k => hG k)
  have hFutureAE : AEMeasurable
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) wholePlaneIIDCodeMeasure :=
    aemeasurable_pi_iff.mpr (fun k => hG k)
  obtain ⟨F, hF, hdetL⟩ := exists_measurable_ae_factorization
    wholePlaneIIDCodeMeasure (aemeasurable_geoSlice56LeftCutObservation x j)
    hPastAE (by simpa [Function.comp_def] using hf)
  obtain ⟨H, hH, hdetR⟩ := exists_measurable_ae_factorization
    wholePlaneIIDCodeMeasure (aemeasurable_geoSlice56RightCutObservation x j)
    hFutureAE (by simpa [Function.comp_def] using hg)
  have hcomp : IndepFun
      (F ∘ geoSlice56LeftCutObservation x j)
      (H ∘ geoSlice56RightCutObservation x j) wholePlaneIIDCodeMeasure :=
    (geoSlice56LeftRightCutIndependent x j).comp
      (φ := F) (ψ := H) hF hH
  exact hcomp.congr hdetL.symm hdetR.symm

/-- Helper toward Lemma 5.6. The slice family is mutually independent and
has the two half-index laws when each range factors through one fixed function
of its thin side presentation. Positive slices use the right presentation at
cut `k - 1`, matching the source's future-at-the-cut index. -/
theorem lemma56_of_presentationDetermination
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation x j W))
    (F_L : LPlusThinPresentation → Option GeometricSideClass)
    (hFL : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_L (geoSlice56LeftCutObservation x k W))
    (F_R : RMinusThinPresentation → Option GeometricSideClass)
    (hFR : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_R (geoSlice56RightCutObservation x (k - 1) W)) :
    iIndepFun G wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 0)) := by
  have hind := lemma56_independent_of_presentationDetermination x G hG hPast hFuture
  have hleftComp : AEMeasurable (fun W => F_L (geoSlice56LeftCutObservation x 0 W))
      wholePlaneIIDCodeMeasure := (hG 0).congr (hFL 0 (by omega))
  have hleftMap := aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure
    (aemeasurable_geoSlice56LeftCutObservation x 0) hleftComp
  let FL : LPlusThinPresentation → Option GeometricSideClass := hleftMap.mk F_L
  have hFLmeas : Measurable FL := hleftMap.measurable_mk
  have hFLae : F_L =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation x 0)] FL :=
    hleftMap.ae_eq_mk
  have hleftDet : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => FL (geoSlice56LeftCutObservation x k W) := by
    intro k hk
    have hpush : F_L =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation x k)] FL := by
      have h := hFLae
      rw [← geoSlice56LeftCutObservation_law_eq_zero x k hk] at h
      exact h
    exact (hFL k hk).trans
      (ae_eq_comp (aemeasurable_geoSlice56LeftCutObservation x k) hpush)
  have hnonpos := DirectedDistances.Probability.map_eq_of_ae_determined_left_range
    FL hFLmeas (fun k => aemeasurable_geoSlice56LeftCutObservation x k)
    (fun k hk => geoSlice56LeftCutObservation_law_eq_zero x k hk) hleftDet
  have hrightComp : AEMeasurable (fun W => F_R (geoSlice56RightCutObservation x 0 W))
      wholePlaneIIDCodeMeasure := (hG 1).congr (hFR 1 (by omega))
  have hrightMap := aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure
    (aemeasurable_geoSlice56RightCutObservation x 0) hrightComp
  let FR : RMinusThinPresentation → Option GeometricSideClass := hrightMap.mk F_R
  have hFRmeas : Measurable FR := hrightMap.measurable_mk
  have hFRae : F_R =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation x 0)] FR :=
    hrightMap.ae_eq_mk
  have hrightDet : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => FR (geoSlice56RightCutObservation x (k - 1) W) := by
    intro k hk
    have hpush : F_R =ᵐ[wholePlaneIIDCodeMeasure.map
        (geoSlice56RightCutObservation x (k - 1))] FR := by
      have h := hFRae
      rw [← geoSlice56RightCutObservation_law_eq_zero x (k - 1) (by omega)] at h
      exact h
    exact (hFR k hk).trans
      (ae_eq_comp (aemeasurable_geoSlice56RightCutObservation x (k - 1)) hpush)
  have hpositive := DirectedDistances.Probability.map_eq_of_ae_determined_right_range
    FR hFRmeas (fun k => aemeasurable_geoSlice56RightCutObservation x k)
    (fun k hk => geoSlice56RightCutObservation_law_eq_zero x k hk) hrightDet
  exact ⟨hind, hpositive, hnonpos⟩

end DirectedDistances.PaperProofs.Section5
