/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceMeasurableReduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Reduction
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment3

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Final
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly12
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusReader5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableDescent

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
@[expose]
noncomputable def lMinusThinIntoLPlus4 (c : LMinusThinPresentation) :
    LPlusThinPresentation := (fun _ => 0, c.2, c.1)

/-- Helper toward Lemma 5.6. Normalize the nonnegative right code to the
nonpositive thin carrier by adjoining a fixed unused prefix. -/
@[expose]
noncomputable def rPlusThinIntoRMinus4 (c : RightThinCode) :
    RMinusThinPresentation := (fun _ => 0, c)

/-- Helper toward Lemma 5.6. The left normalization map is measurable. -/
theorem measurable_lMinusThinIntoLPlus4 : Measurable lMinusThinIntoLPlus4 := by
  exact measurable_const.prodMk (measurable_snd.prodMk measurable_fst)

/-- Helper toward Lemma 5.6. The right normalization map is measurable. -/
theorem measurable_rPlusThinIntoRMinus4 : Measurable rPlusThinIntoRMinus4 := by
  exact measurable_const.prodMk measurable_id

/-- Helper toward Lemma 5.6. The left cut observation is represented in one
standard Borel thin carrier. For `j > 0` it is the L-plus presentation; for
`j ≤ 0` it is the equivalent normalized L-minus presentation. -/
@[expose]
noncomputable def geoSlice56LeftCutObservation4 (x : XDP) (j : ℤ)
    (W : ℤ → Fin 3) : LPlusThinPresentation :=
  if 0 < j then
    lPlusThinPresentationRetract x (decodeLPlus x j (leftSideObsNonneg x j W))
  else
    lMinusThinIntoLPlus4
      (lMinusThinPresentationRetract x (decodeLMinus x j (leftSideObsNonpos x j W)))

/-- Helper toward Lemma 5.6. The right cut observation is represented in one
standard Borel thin carrier. For `j ≥ 0` it is the R-plus hatted code with a
fixed unused prefix; for `j < 0` it is the R-minus presentation. -/
@[expose]
noncomputable def geoSlice56RightCutObservation4 (x : XDP) (j : ℤ)
    (W : ℤ → Fin 3) : RMinusThinPresentation :=
  if 0 ≤ j then
    rPlusThinIntoRMinus4 (rightThinCodeRetract (rightSideObsNonneg x j W))
  else
    rMinusThinPresentationRetract x
      (decodeRMinus x j (rightSideObsNonpos x j W))

/-- Helper toward Lemma 5.6. The exposed left observation is almost-everywhere measurable. -/
theorem aemeasurable_geoSlice56LeftCutObservation4 (x : XDP) (j : ℤ) :
    AEMeasurable (geoSlice56LeftCutObservation4 x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 < j
  · unfold geoSlice56LeftCutObservation4
    simp only [if_pos hj]
    exact (measurable_lPlusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeLPlus_leftSideObsNonneg x j)
  · unfold geoSlice56LeftCutObservation4
    simp only [if_neg hj]
    exact ((measurable_lMinusThinIntoLPlus4.comp
      (measurable_lMinusThinPresentationRetract x)).comp_aemeasurable
      (aemeasurable_decodeLMinus_leftSideObsNonpos x j))

/-- Helper toward Lemma 5.6. The exposed right observation is almost-everywhere measurable. -/
theorem aemeasurable_geoSlice56RightCutObservation4 (x : XDP) (j : ℤ) :
    AEMeasurable (geoSlice56RightCutObservation4 x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 ≤ j
  · unfold geoSlice56RightCutObservation4
    simp only [if_pos hj]
    exact (measurable_rPlusThinIntoRMinus4.comp measurable_rightThinCodeRetract).comp_aemeasurable
      (aemeasurable_boundaryFourObservations x j 2)
  · unfold geoSlice56RightCutObservation4
    simp only [if_neg hj]
    exact (measurable_rMinusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeRMinus_rightSideObsNonpos x j)

/-- Helper toward Lemma 5.6. The two normalized cut presentations remain
independent by the proved nonnegative and nonpositive presentation results. -/
theorem geoSlice56LeftRightCutIndependent4 (x : XDP) (j : ℤ) :
    IndepFun (geoSlice56LeftCutObservation4 x j)
      (geoSlice56RightCutObservation4 x j) wholePlaneIIDCodeMeasure := by
  by_cases hj : 0 < j
  · unfold geoSlice56LeftCutObservation4 geoSlice56RightCutObservation4
    have hj' : 0 ≤ j := by omega
    simp only [if_pos hj, if_pos hj']
    have hright : Measurable
        (fun r : RPlusSidePresentation x =>
          rPlusThinIntoRMinus4 (rightThinCodeRetract r.code)) := by
      exact (measurable_rPlusThinIntoRMinus4.comp
        (measurable_rightThinCodeRetract.comp
          (measurable_rPlusSidePresentation_code (x := x))))
    simpa [Function.comp_def, rPlusThinIntoRMinus4, decodeRPlus] using
      (lemma55_nonneg_presentation_indepFun x j).comp
        (φ := lPlusThinPresentationRetract x)
        (ψ := fun r : RPlusSidePresentation x =>
          rPlusThinIntoRMinus4 (rightThinCodeRetract r.code))
        (measurable_lPlusThinPresentationRetract x)
        hright
  · by_cases hzero : j = 0
    · subst j
      unfold geoSlice56LeftCutObservation4 geoSlice56RightCutObservation4
      simp only [lt_irrefl, if_false, le_refl, if_true]
      have hright : Measurable
          (fun r : RMinusSidePresentation x =>
            (fun _ : ℕ => (0 : Fin 3),
              (rMinusThinPresentationRetract x r).2)) := by
        exact (measurable_const.prodMk measurable_snd).comp
          (measurable_rMinusThinPresentationRetract x)
      simpa [Function.comp_def, rPlusThinIntoRMinus4, decodeRMinus,
        rightSideObsNonpos, rightSideObsNonneg, rMinusThinPresentationRetract] using
        (lemma55_nonpos_presentation_indepFun x 0).comp
          (φ := fun r => lMinusThinIntoLPlus4 (lMinusThinPresentationRetract x r))
          (ψ := fun r : RMinusSidePresentation x =>
            (fun _ : ℕ => (0 : Fin 3),
              (rMinusThinPresentationRetract x r).2))
          (measurable_lMinusThinIntoLPlus4.comp
            (measurable_lMinusThinPresentationRetract x)) hright
    · have hjneg : j < 0 := by omega
      unfold geoSlice56LeftCutObservation4 geoSlice56RightCutObservation4
      simp only [if_neg (by omega : ¬ 0 < j), if_neg (by omega : ¬ 0 ≤ j)]
      simpa [Function.comp_def] using (lemma55_nonpos_presentation_indepFun x j).comp
          (φ := fun r => lMinusThinIntoLPlus4 (lMinusThinPresentationRetract x r))
          (ψ := rMinusThinPresentationRetract x)
          (measurable_lMinusThinIntoLPlus4.comp (measurable_lMinusThinPresentationRetract x))
          (measurable_rMinusThinPresentationRetract x)

/-- Helper toward Lemma 5.6. The normalized left cut presentations have one
law throughout the nonpositive range, including the L-minus layout at zero. -/
theorem geoSlice56LeftCutObservation4_law_eq_zero (x : XDP) (j : ℤ)
    (hj : j ≤ 0) :
    wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation4 x j) =
      wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation4 x 0) := by
  let Φ : LMinusSidePresentation x → LPlusThinPresentation :=
    fun r => lMinusThinIntoLPlus4 (lMinusThinPresentationRetract x r)
  have hΦ : Measurable Φ :=
    measurable_lMinusThinIntoLPlus4.comp (measurable_lMinusThinPresentationRetract x)
  have hdec (k : ℤ) :
      AEMeasurable (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
        wholePlaneIIDCodeMeasure :=
    aemeasurable_decodeLMinus_leftSideObsNonpos x k
  have hj' : ¬ 0 < j := by omega
  unfold geoSlice56LeftCutObservation4
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
theorem geoSlice56RightCutObservation4_law_eq_zero (x : XDP) (j : ℤ)
    (hj : 0 ≤ j) :
    wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation4 x j) =
      wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation4 x 0) := by
  let Ψ : RightThinCode → RMinusThinPresentation := rPlusThinIntoRMinus4
  have hΨ : Measurable Ψ := measurable_rPlusThinIntoRMinus4
  have hcode (k : ℤ) : AEMeasurable (rightSideObsNonneg x k)
      wholePlaneIIDCodeMeasure := by
    change AEMeasurable (boundaryFourObservations x k 2) wholePlaneIIDCodeMeasure
    exact aemeasurable_boundaryFourObservations x k 2
  unfold geoSlice56RightCutObservation4
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

/-- Helper toward Lemma 5.6. Conditional on the displayed measurability and
presentation-determination hypotheses, the slice family is mutually
independent. The determining functions need not be measurable; standard
Borel factorization supplies measurable versions. -/
theorem lemma56_independent_of_presentationDetermination4
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation4 x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation4 x j W)) :
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
    wholePlaneIIDCodeMeasure (aemeasurable_geoSlice56LeftCutObservation4 x j)
    hPastAE (by simpa [Function.comp_def] using hf)
  obtain ⟨H, hH, hdetR⟩ := exists_measurable_ae_factorization
    wholePlaneIIDCodeMeasure (aemeasurable_geoSlice56RightCutObservation4 x j)
    hFutureAE (by simpa [Function.comp_def] using hg)
  have hcomp : IndepFun
      (F ∘ geoSlice56LeftCutObservation4 x j)
      (H ∘ geoSlice56RightCutObservation4 x j) wholePlaneIIDCodeMeasure :=
    (geoSlice56LeftRightCutIndependent4 x j).comp
      (φ := F) (ψ := H) hF hH
  exact hcomp.congr hdetL.symm hdetR.symm

/-- Helper toward Lemma 5.6. Conditional on the displayed presentation
determination and shared-reader hypotheses, the slice family is mutually
independent and has the two half-index laws. Positive slices use the right
presentation at cut `k - 1`, matching the source's future-at-the-cut index. -/
theorem lemma56_of_presentationDetermination4
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation4 x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation4 x j W))
    (F_L : LPlusThinPresentation → Option GeometricSideClass)
    (hFL : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_L (geoSlice56LeftCutObservation4 x k W))
    (F_R : RMinusThinPresentation → Option GeometricSideClass)
    (hFR : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_R (geoSlice56RightCutObservation4 x (k - 1) W)) :
    iIndepFun G wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 0)) := by
  have hind := lemma56_independent_of_presentationDetermination4 x G hG hPast hFuture
  have hleftComp : AEMeasurable (fun W => F_L (geoSlice56LeftCutObservation4 x 0 W))
      wholePlaneIIDCodeMeasure := (hG 0).congr (hFL 0 (by omega))
  have hleftMap := aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure
    (aemeasurable_geoSlice56LeftCutObservation4 x 0) hleftComp
  let FL : LPlusThinPresentation → Option GeometricSideClass := hleftMap.mk F_L
  have hFLmeas : Measurable FL := hleftMap.measurable_mk
  have hFLae : F_L =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation4 x 0)] FL :=
    hleftMap.ae_eq_mk
  have hleftDet : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => FL (geoSlice56LeftCutObservation4 x k W) := by
    intro k hk
    have hpush : F_L =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56LeftCutObservation4 x k)] FL := by
      have h := hFLae
      rw [← geoSlice56LeftCutObservation4_law_eq_zero x k hk] at h
      exact h
    exact (hFL k hk).trans
      (ae_eq_comp (aemeasurable_geoSlice56LeftCutObservation4 x k) hpush)
  have hnonpos := DirectedDistances.Probability.map_eq_of_ae_determined_left_range
    FL hFLmeas (fun k => aemeasurable_geoSlice56LeftCutObservation4 x k)
    (fun k hk => geoSlice56LeftCutObservation4_law_eq_zero x k hk) hleftDet
  have hrightComp : AEMeasurable (fun W => F_R (geoSlice56RightCutObservation4 x 0 W))
      wholePlaneIIDCodeMeasure := (hG 1).congr (hFR 1 (by omega))
  have hrightMap := aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure
    (aemeasurable_geoSlice56RightCutObservation4 x 0) hrightComp
  let FR : RMinusThinPresentation → Option GeometricSideClass := hrightMap.mk F_R
  have hFRmeas : Measurable FR := hrightMap.measurable_mk
  have hFRae : F_R =ᵐ[wholePlaneIIDCodeMeasure.map (geoSlice56RightCutObservation4 x 0)] FR :=
    hrightMap.ae_eq_mk
  have hrightDet : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => FR (geoSlice56RightCutObservation4 x (k - 1) W) := by
    intro k hk
    have hpush : F_R =ᵐ[wholePlaneIIDCodeMeasure.map
        (geoSlice56RightCutObservation4 x (k - 1))] FR := by
      have h := hFRae
      rw [← geoSlice56RightCutObservation4_law_eq_zero x (k - 1) (by omega)] at h
      exact h
    exact (hFR k hk).trans
      (ae_eq_comp (aemeasurable_geoSlice56RightCutObservation4 x (k - 1)) hpush)
  have hpositive := DirectedDistances.Probability.map_eq_of_ae_determined_right_range
    FR hFRmeas (fun k => aemeasurable_geoSlice56RightCutObservation4 x k)
    (fun k hk => geoSlice56RightCutObservation4_law_eq_zero x k hk) hrightDet
  exact ⟨hind, hpositive, hnonpos⟩

/-- Helper toward Lemma 5.6. Conditional on the displayed presentation
determination and shared-reader hypotheses, the slice family is mutually
independent and has the two half-index laws after forgetting the internal
marks. -/
theorem lemma56_unmarked_of_presentationDetermination4
    (default : GeometricSideClass)
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation4 x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation4 x j W))
    (F_L : LPlusThinPresentation → Option GeometricSideClass)
    (hFL : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_L (geoSlice56LeftCutObservation4 x k W))
    (F_R : RMinusThinPresentation → Option GeometricSideClass)
    (hFR : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_R (geoSlice56RightCutObservation4 x (k - 1) W)) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 0)) := by
  have hmarked := lemma56_of_presentationDetermination4 x G hG hPast hFuture
    F_L hFL F_R hFR
  rcases hmarked with ⟨hind, hpositive, hnonpositive⟩
  refine ⟨iIndepFun_forgetMarksOptionClassValue default hind, ?_, ?_⟩
  · intro k hk
    exact map_forgetMarksOptionClassValue_eq default (hG k) (hG 1)
      (hpositive k hk)
  · intro k hk
    exact map_forgetMarksOptionClassValue_eq default (hG k) (hG 0)
      (hnonpositive k hk)

/-- Helper toward Lemma 5.6. This conditional reduction uses index-dependent
readers for past and future determination, and one shared reader on each
half-index range for the two law conclusions. -/
theorem lemma56_unmarked_of_sideReaders4
    (default : GeometricSideClass) (x : XDP)
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (oneL : GeometricSideClass → Option GeometricSideClass)
    (prevL : GeometricSideClass → GeometricSideClass)
    (hL : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneL (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) = G j W ∧
        prevL (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j - 1)) .left))
    (oneR : GeometricSideClass → Option GeometricSideClass)
    (nextR : GeometricSideClass → GeometricSideClass)
    (hR : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneR (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          G (j + 1) W ∧
        nextR (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j + 1)) .right))
    (readL : ∀ j : ℤ, LPlusThinPresentation → GeometricSideClass)
    (hReadL : ∀ j : ℤ, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readL j (geoSlice56LeftCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .left))
    (readR : ∀ j : ℤ, RMinusThinPresentation → GeometricSideClass)
    (hReadR : ∀ j : ℤ, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readR j (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right))
    (readLminus : LPlusThinPresentation → GeometricSideClass)
    (hReadLminus : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, k ≤ 0 →
      ∀ s : M0CutGeodesicSliceWitness W x,
        readLminus (geoSlice56LeftCutObservation4 x k W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P k) .left))
    (readRplus : RMinusThinPresentation → GeometricSideClass)
    (hReadRplus : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ, 0 ≤ j →
      ∀ s : M0CutGeodesicSliceWitness W x,
        readRplus (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 0)) := by
  let F_L : LPlusThinPresentation → Option GeometricSideClass :=
    fun c => oneL (readLminus c)
  let F_R : RMinusThinPresentation → Option GeometricSideClass :=
    fun c => oneR (readRplus c)
  have hPast : ∀ j, ∃ f : LPlusThinPresentation →
      (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation4 x j W) := by
    intro j
    let f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass) := fun c k =>
      oneL (prevL^[(j - k.val).toNat] (readL j c))
    refine ⟨f, ?_⟩
    filter_upwards [hL, hReadL j] with W hL hObs
    obtain ⟨s, hs⟩ := hL
    funext k
    change G k.val W = oneL
      (prevL^[(j - k.val).toNat]
        (readL j (geoSlice56LeftCutObservation4 x j W)))
    have hrec : ∀ n, prevL
        (geometricSideClass (m0GeodesicSide s.hp (s.P n) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (n - 1)) .left) :=
      fun n => (hs n).2
    have hn : ((j - k.val).toNat : ℤ) = j - k.val :=
      Int.toNat_of_nonneg (sub_nonneg.mpr k.property)
    have hidx : j - ((j - k.val).toNat : ℤ) = k.val := by rw [hn]; omega
    rw [← (hs k.val).1, hObs s, geoSlicePreviousSide_iterate prevL
      (fun n => geometricSideClass (m0GeodesicSide s.hp (s.P n) .left))
      hrec (j - k.val).toNat j]
    rw [hidx]
  have hFuture : ∀ j, ∃ f : RMinusThinPresentation →
      (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation4 x j W) := by
    intro j
    let f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass) := fun c k =>
      oneR (nextR^[(k.val - (j + 1)).toNat] (readR j c))
    refine ⟨f, ?_⟩
    filter_upwards [hR, hReadR j] with W hR hObs
    obtain ⟨s, hs⟩ := hR
    funext k
    change G k.val W = oneR
      (nextR^[(k.val - (j + 1)).toNat]
        (readR j (geoSlice56RightCutObservation4 x j W)))
    have hrec : ∀ n, nextR
        (geometricSideClass (m0GeodesicSide s.hp (s.P n) .right)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (n + 1)) .right) :=
      fun n => (hs n).2
    have hn : ((k.val - (j + 1)).toNat : ℤ) = k.val - (j + 1) :=
      Int.toNat_of_nonneg (sub_nonneg.mpr k.property)
    have hidx : j + ((k.val - (j + 1)).toNat : ℤ) = k.val - 1 := by
      rw [hn]
      omega
    have hone : oneR
        (geometricSideClass (m0GeodesicSide s.hp (s.P (k.val - 1)) .right)) =
          G k.val W := by
      simpa only [sub_add_cancel] using (hs (k.val - 1)).1
    rw [← hone, hObs s, geoSliceNextSide_iterate nextR
      (fun n => geometricSideClass (m0GeodesicSide s.hp (s.P n) .right))
      hrec (k.val - (j + 1)).toNat j]
    rw [hidx]
  have hFL : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_L (geoSlice56LeftCutObservation4 x k W) := by
    intro k hk
    filter_upwards [hL, hReadLminus] with W hL hObs
    obtain ⟨s, hs⟩ := hL
    change G k W = oneL (readLminus (geoSlice56LeftCutObservation4 x k W))
    rw [← (hs k).1, ← hObs k hk s]
  have hFR : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_R (geoSlice56RightCutObservation4 x (k - 1) W) := by
    intro k hk
    filter_upwards [hR, hReadRplus] with W hR hObs
    obtain ⟨s, hs⟩ := hR
    change G k W = oneR (readRplus (geoSlice56RightCutObservation4 x (k - 1) W))
    have hone : oneR
        (geometricSideClass (m0GeodesicSide s.hp (s.P (k - 1)) .right)) = G k W := by
      simpa only [sub_add_cancel] using (hs (k - 1)).1
    rw [← hone, ← hObs (k - 1) (by omega) s]
  exact lemma56_unmarked_of_presentationDetermination4 default x G hG hPast hFuture
    F_L hFL F_R hFR

/-- Helper toward Lemma 5.6. The L-minus embedding recovers every
presentation whose hatted coordinates are certified. -/
theorem lMinusThinPresentationVal_retract4 (x : XDP)
    (r : LMinusSidePresentation x) (hr : r ∈ lMinusCertifiedPresentationDomain x) :
    lMinusThinPresentationVal x (lMinusThinPresentationRetract x r) = r := by
  obtain ⟨c, rfl⟩ := (range_lMinusThinPresentationVal x).symm ▸ hr
  rw [lMinusThinPresentationRetract_val]

/-- Helper toward Lemma 5.6. Read the nonpositive left class from the
normalized thin carrier, undoing the exchange of primed and hatted blocks.
This function has no boundary-index argument. -/
@[expose] noncomputable def geoSlice56LeftMinusClassOption4 (x : XDP)
    (c : LPlusThinPresentation) : Option GeometricSideClass :=
  (lMinusThinPresentationVal x (c.2.2, c.2.1)).classOption4

/-- Helper toward Lemma 5.6. Read the positive left class from the complete
certified presentation using the proved aligned reader. -/
@[expose] noncomputable def geoSlice56LeftPlusClassOption4 (x : XDP) (k : ℤ)
    (c : LPlusThinPresentation) : Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt5 x k (lPlusThinPresentationVal x c)

/-- Helper toward Lemma 5.6. Use the appropriate left class reader at
each boundary index. -/
@[expose] noncomputable def geoSlice56LeftClassOption4 (x : XDP) (k : ℤ)
    (c : LPlusThinPresentation) : Option GeometricSideClass :=
  if 0 < k then geoSlice56LeftPlusClassOption4 x k c
  else geoSlice56LeftMinusClassOption4 x c

/-- Helper toward Lemma 5.6. At every nonpositive index the actual left
observable factors through one index-free function of the normalized cut. -/
theorem lemma55LeftSideClassOption_ae_eq_leftMinusCut4
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56LeftMinusClassOption4 x
        (geoSlice56LeftCutObservation4 x k W) := by
  filter_upwards
    [lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x k hk,
      ae_decodeLMinus_leftSideObsNonpos_hatted_mem_range x k hk] with W hactual hrange
  have hr : decodeLMinus x k (leftSideObsNonpos x k W) ∈
      lMinusCertifiedPresentationDomain x := hrange
  have he := lMinusThinPresentationVal_retract4 x _ hr
  simpa only [geoSlice56LeftCutObservation4, ite_eq_right (by omega : ¬ 0 < k),
    geoSlice56LeftMinusClassOption4, lMinusThinIntoLPlus4, he,
    Function.comp_apply] using hactual

/-- Helper toward Lemma 5.6. At every positive index the actual left
observable factors through the explicit aligned reader of the normalized cut. -/
theorem lemma55LeftSideClassOption_ae_eq_leftPlusCut4
    (x : XDP) (k : ℤ) (hk : 0 < k) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56LeftPlusClassOption4 x k
        (geoSlice56LeftCutObservation4 x k W) := by
  filter_upwards
    [lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
      lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq x k (le_of_lt hk),
      ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range x k] with W hactual hrange
  have he := lPlusThinPresentationVal_retract x
    (decodeLPlus x k (leftSideObsNonneg x k W)) hrange
  simpa only [geoSlice56LeftCutObservation4, ite_eq_left hk,
    geoSlice56LeftPlusClassOption4, he, Function.comp_apply] using hactual

/-- Helper toward Lemma 5.6. At every index the actual left observable
factors through its explicit normalized-cut reader. -/
theorem lemma55LeftSideClassOption_ae_eq_leftCut4 (x : XDP) (k : ℤ) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56LeftClassOption4 x k
        (geoSlice56LeftCutObservation4 x k W) := by
  by_cases hk : 0 < k
  · simpa only [geoSlice56LeftClassOption4, ite_eq_left hk] using
      lemma55LeftSideClassOption_ae_eq_leftPlusCut4 x k hk
  · simpa only [geoSlice56LeftClassOption4, ite_eq_right hk] using
      lemma55LeftSideClassOption_ae_eq_leftMinusCut4 x k (by omega)

/-- Helper toward Lemma 5.6. Every slice witness left class has the
explicit per-index factorization through the normalized cut, almost surely. -/
theorem ae_sliceLeftSideClass_eq_leftCut4 (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ s : M0CutGeodesicSliceWitness W x,
      some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .left)) =
        geoSlice56LeftClassOption4 x k (geoSlice56LeftCutObservation4 x k W) := by
  filter_upwards [ae_lemma55LeftSideClassOption_eq_sliceSideClass x k,
    lemma55LeftSideClassOption_ae_eq_leftCut4 x k] with W hslice hcut
  intro s
  exact (hslice s).symm.trans hcut

/-- Helper toward Lemma 5.6. Every nonpositive slice witness left class
has a factorization through the same index-free function, on one event. -/
theorem ae_all_sliceLeftSideClass_eq_leftMinusCut4 (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, k ≤ 0 →
      ∀ s : M0CutGeodesicSliceWitness W x,
        some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .left)) =
          geoSlice56LeftMinusClassOption4 x (geoSlice56LeftCutObservation4 x k W) := by
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k ≤ 0
  · filter_upwards [ae_lemma55LeftSideClassOption_eq_sliceSideClass x k,
      lemma55LeftSideClassOption_ae_eq_leftMinusCut4 x k hk] with W hslice hcut
    intro _ s
    exact (hslice s).symm.trans hcut
  · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)

/-- Helper toward Lemma 5.6. Default the explicit per-index left reader
outside its almost-sure source-valid domain. -/
@[expose] noncomputable def readL4 (default : GeometricSideClass) (x : XDP)
    (k : ℤ) (c : LPlusThinPresentation) : GeometricSideClass :=
  (geoSlice56LeftClassOption4 x k c).getD default

/-- Helper toward Lemma 5.6. Default the shared nonpositive left reader
outside its almost-sure source-valid domain. -/
@[expose] noncomputable def readLminus4 (default : GeometricSideClass) (x : XDP)
    (c : LPlusThinPresentation) : GeometricSideClass :=
  (geoSlice56LeftMinusClassOption4 x c).getD default

/-- Helper toward Lemma 5.6. The explicit per-index reader satisfies
exactly the left-reader hypothesis of the conditional side-reader reduction. -/
theorem hReadL4 (default : GeometricSideClass) (x : XDP) :
    ∀ j : ℤ, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readL4 default x j (geoSlice56LeftCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .left) := by
  intro j
  filter_upwards [ae_sliceLeftSideClass_eq_leftCut4 x j] with W hW
  intro s
  exact (congrArg (fun o : Option GeometricSideClass => o.getD default) (hW s)).symm

/-- Helper toward Lemma 5.6. The explicit shared reader satisfies exactly
the nonpositive left-reader hypothesis, with all indices on one event. -/
theorem hReadLminus4 (default : GeometricSideClass) (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, k ≤ 0 →
      ∀ s : M0CutGeodesicSliceWitness W x,
        readLminus4 default x (geoSlice56LeftCutObservation4 x k W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P k) .left) := by
  filter_upwards [ae_all_sliceLeftSideClass_eq_leftMinusCut4 x] with W hW
  intro k hk s
  exact (congrArg (fun o : Option GeometricSideClass => o.getD default) (hW k hk s)).symm

end DirectedDistances.PaperProofs.Section5
