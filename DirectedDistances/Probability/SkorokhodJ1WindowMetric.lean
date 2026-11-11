module

public import DirectedDistances.Probability.SkorokhodJ1Window

/-! # Metric structure for the Skorokhod J1 window distance -/

@[expose] public section
namespace DirectedDistances.Probability

/-- A small J1 cost gives uniform pointwise bounds on displacement and value error. -/
private theorem j1WindowDist_small_cost {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (ε : ℝ) (hε : 0 < ε)
    (hzero : j1WindowDist hT f g = 0) :
    ∃ φ : J1TimeChange T,
      (∀ t, |(φ t : ℝ) - (t : ℝ)| < ε) ∧
      (∀ t, |f.1 (φ t) - g.1 t| < ε) := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  have hsmall : j1WindowDist hT f g < ε := by rw [hzero]; exact hε
  change (⨅ φ : J1TimeChange T,
    max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) < ε at hsmall
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hsmall
  refine ⟨φ, ?_, ?_⟩
  · intro t
    have hle : |(φ t : ℝ) - (t : ℝ)| ≤
        max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) := by
      exact (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) t le_rfl)
        |>.trans (le_max_left _ _)
    exact hle.trans_lt hφ
  · intro t
    have hle : |f.1 (φ t) - g.1 t| ≤
        max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) := by
      exact (le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) t le_rfl)
        |>.trans (le_max_right _ _)
    exact hle.trans_lt hφ

/-- An order-isomorphism of the window fixes its greatest endpoint. -/
private theorem j1WindowTimeChange_fixes_endpoint {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T) :
    φ ⟨T, ⟨hT.le, le_rfl⟩⟩ = ⟨T, ⟨hT.le, le_rfl⟩⟩ := by
  apply Subtype.ext
  apply le_antisymm
  · exact (φ ⟨T, ⟨hT.le, le_rfl⟩⟩).property.2
  · obtain ⟨x, hx⟩ := φ.surjective ⟨T, ⟨hT.le, le_rfl⟩⟩
    have hxe : x ≤ (⟨T, ⟨hT.le, le_rfl⟩⟩ : J1Window T) := x.property.2
    have hmono := φ.monotone hxe
    rw [hx] at hmono
    exact hmono

/-- The J1 window distance separates càdlàg paths. -/
theorem j1WindowDist_eq_zero_iff {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    j1WindowDist hT f g = 0 ↔ f = g := by
  constructor
  · intro hzero
    apply Subtype.ext
    funext t
    by_cases htT : (t : ℝ) = T
    · have ht : t = ⟨T, ⟨hT.le, le_rfl⟩⟩ := Subtype.ext htT
      subst t
      by_contra hne
      have hpos : 0 < |f.1 ⟨T, ⟨hT.le, le_rfl⟩⟩ -
          g.1 ⟨T, ⟨hT.le, le_rfl⟩⟩| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨φ, -, hvalue⟩ :=
        j1WindowDist_small_cost hT f g _ hpos hzero
      have hfix := j1WindowTimeChange_fixes_endpoint hT φ
      have hlt := hvalue ⟨T, ⟨hT.le, le_rfl⟩⟩
      rw [hfix] at hlt
      exact (lt_irrefl _ hlt)
    · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htT
      by_contra hne
      let η := |f.1 t - g.1 t| / 4
      have hη : 0 < η := by
        dsimp [η]
        exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
      have hfr :=
        (Metric.continuousWithinAt_iff).mp (f.2.isRightContinuous t)
      obtain ⟨rF, hrF, hF⟩ := hfr η hη
      have hgr :=
        (Metric.continuousWithinAt_iff).mp (g.2.isRightContinuous t)
      obtain ⟨rG, hrG, hG⟩ := hgr η hη
      let ε := min (T - (t : ℝ)) (min rF (min rG η)) / 4
      have hε : 0 < ε := by
        dsimp [ε]
        positivity
      have hεT : ε * 4 ≤ T - (t : ℝ) := by
        dsimp [ε]
        nlinarith [min_le_left (T - (t : ℝ)) (min rF (min rG η))]
      have hεF : ε * 4 ≤ rF := by
        dsimp [ε]
        nlinarith [min_le_right (T - (t : ℝ)) (min rF (min rG η)),
          min_le_left rF (min rG η)]
      have hεG : ε * 4 ≤ rG := by
        dsimp [ε]
        nlinarith [min_le_right (T - (t : ℝ)) (min rF (min rG η)),
          min_le_right rF (min rG η), min_le_left rG η]
      have hεη : ε * 4 ≤ η := by
        dsimp [ε]
        nlinarith [min_le_right (T - (t : ℝ)) (min rF (min rG η)),
          min_le_right rF (min rG η), min_le_right rG η]
      obtain ⟨φ, hdisp, hvalue⟩ :=
        j1WindowDist_small_cost hT f g ε hε hzero
      let s : J1Window T := ⟨(t : ℝ) + 2 * ε,
        ⟨by linarith [t.property.1], by nlinarith [hεT]⟩⟩
      have hts : (t : ℝ) < (s : ℝ) := by
        dsimp [s]
        linarith
      have hφts : (t : ℝ) < (φ s : ℝ) := by
        have hd := abs_lt.mp (hdisp s)
        dsimp [s]
        linarith
      have hsrad : dist s t < rG := by
        rw [Subtype.dist_eq, Real.dist_eq]
        dsimp [s]
        rw [show (t : ℝ) + 2 * ε - (t : ℝ) = 2 * ε by ring]
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
        nlinarith [hεG]
      have hφrad : dist (φ s) t < rF := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have hd := hdisp s
        have hstval : |(s : ℝ) - (t : ℝ)| = 2 * ε := by
          dsimp [s]
          rw [show (t : ℝ) + 2 * ε - (t : ℝ) = 2 * ε by ring]
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
        calc
          |(φ s : ℝ) - (t : ℝ)| ≤
              |(φ s : ℝ) - (s : ℝ)| + |(s : ℝ) - (t : ℝ)| := abs_sub_le _ _ _
          _ < ε + 2 * ε := by rw [hstval]; exact add_lt_add_of_lt_of_le hd le_rfl
          _ < rF := by nlinarith [hεF, hε]
      have hFval : |f.1 (φ s) - f.1 t| < η := by
        simpa only [Real.dist_eq] using hF hφts hφrad
      have hGval : |g.1 s - g.1 t| < η := by
        simpa only [Real.dist_eq] using hG hts hsrad
      have hvalue' := hvalue s
      have htriangle : |f.1 t - g.1 t| ≤
          |f.1 t - f.1 (φ s)| + |f.1 (φ s) - g.1 s| +
            |g.1 s - g.1 t| := by
        calc
          |f.1 t - g.1 t| ≤
              |f.1 t - f.1 (φ s)| + |f.1 (φ s) - g.1 t| := abs_sub_le _ _ _
          _ ≤ |f.1 t - f.1 (φ s)| +
              (|f.1 (φ s) - g.1 s| + |g.1 s - g.1 t|) :=
            add_le_add (le_rfl)
              (abs_sub_le (f.1 (φ s)) (g.1 s) (g.1 t))
          _ = |f.1 t - f.1 (φ s)| + |f.1 (φ s) - g.1 s| +
              |g.1 s - g.1 t| := by ring
      have hFval' : |f.1 t - f.1 (φ s)| < η := by
        simpa [abs_sub_comm] using hFval
      have hlt : |f.1 t - g.1 t| < 4 * η := by
        calc
          |f.1 t - g.1 t| ≤
              |f.1 t - f.1 (φ s)| + |f.1 (φ s) - g.1 s| +
                |g.1 s - g.1 t| := htriangle
          _ < η + ε + η := by linarith [hFval', hvalue', hGval]
          _ < 4 * η := by nlinarith [hεη, hη]
      have : 4 * η = |f.1 t - g.1 t| := by
        dsimp [η]
        ring
      exact (lt_irrefl _ (this ▸ hlt))
  · rintro rfl
    exact j1WindowDist_self hT f

/-- Helper toward E-STABLE / thm-busemann-conv
Skorokhod J1 distance on càdlàg paths over [0,T] separates points and is a
metric (Billingsley, Convergence of Probability Measures, 2nd ed., §12); no
completeness, separability, Borel structure, tightness or functional
convergence is claimed; not the paper result. -/
@[instance_reducible] noncomputable def j1WindowMetricSpace {T : ℝ} (hT : 0 < T) :
    MetricSpace (CadlagWindow T) where
  dist := j1WindowDist hT
  dist_self := j1WindowDist_self hT
  dist_comm := j1WindowDist_symm hT
  dist_triangle := j1WindowDist_triangle hT
  eq_of_dist_eq_zero := fun h => (j1WindowDist_eq_zero_iff hT _ _).mp h

/-- The J1 distance is bounded by the uniform distance, so the identity has
Lipschitz constant one from uniform distance to J1 distance. -/
theorem j1WindowDist_lipschitz_sup {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    j1WindowDist hT f g ≤ ⨆ t : J1Window T, |f.1 t - g.1 t| :=
  j1WindowDist_le_sup_dist hT f g

end DirectedDistances.Probability
