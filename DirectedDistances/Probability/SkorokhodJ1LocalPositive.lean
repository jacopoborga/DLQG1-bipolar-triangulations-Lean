module

public import DirectedDistances.Probability.SkorokhodJ1WindowMetric
public import DirectedDistances.Probability.SkorokhodJ1WindowEvaluation

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Cardinality
import DirectedDistances.Probability.SkorokhodJ1WindowContinuityTimes

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

/-! # The local Skorokhod J1 space on the positive half-line

The intended metric is Billingsley's §16 metric, using the cutoffs and
finite-window J1 distances from this module.  See Billingsley 1999, §§16.1–16.3. -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped Topology




abbrev CadlagLocal := {x : Set.Ici (0 : ℝ) → ℝ // IsCadlag x}




noncomputable def localCutoff (n : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  max 0 (min 1 ((n : ℝ) + 1 - (t : ℝ)))




theorem localCutoff_continuous (n : ℕ) : Continuous (localCutoff n) := by
  unfold localCutoff
  have hc : Continuous (fun _ : Set.Ici (0 : ℝ) => (n : ℝ) + 1) := continuous_const
  have hv : Continuous (fun t : Set.Ici (0 : ℝ) => (t : ℝ)) :=
    continuous_subtype_val
  change Continuous (fun t : Set.Ici (0 : ℝ) =>
    max 0 (min 1 ((n : ℝ) + 1 - (t : ℝ))))
  exact (continuous_const.max ((continuous_const.min (hc.sub hv))))




theorem localCutoff_mul_isCadlag (n : ℕ) (x : CadlagLocal) :
    IsCadlag (fun t => x.1 t * localCutoff n t) := by
  exact x.2.mul (localCutoff_continuous n).isCadlag




def localWindowTime {T : ℝ} (t : J1Window T) : Set.Ici (0 : ℝ) :=
  ⟨t.1, t.2.1⟩




theorem localWindowTime_continuous {T : ℝ} :
    Continuous (localWindowTime (T := T)) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val




theorem localWindowRestriction_isCadlag {T : ℝ} {f : Set.Ici (0 : ℝ) → ℝ}
    (hf : IsCadlag f) :
    IsCadlag (fun t : J1Window T => f (localWindowTime t)) := by
  constructor
  · intro a
    have hi : Tendsto (localWindowTime (T := T)) (𝓝[Set.Ioi a] a)
        (𝓝[Set.Ioi (localWindowTime a)] (localWindowTime a)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(localWindowTime_continuous.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds, ?_⟩
      apply eventually_nhdsWithin_of_forall
      intro u hu
      change (a : ℝ) < (u : ℝ) at hu
      exact Set.mem_Ioi.mpr hu
    exact (hf.isRightContinuous (localWindowTime a)).tendsto.comp hi
  · intro a
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (localWindowTime a)
    have hi : Tendsto (localWindowTime (T := T)) (𝓝[Set.Iio a] a)
        (𝓝[Set.Iio (localWindowTime a)] (localWindowTime a)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(localWindowTime_continuous.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds, ?_⟩
      apply eventually_nhdsWithin_of_forall
      intro u hu
      change (u : ℝ) < (a : ℝ) at hu
      exact Set.mem_Iio.mpr hu
    exact ⟨l, hl.comp hi⟩




noncomputable def cutoffWindow (n : ℕ) (x : CadlagLocal) :
    CadlagWindow ((n : ℝ) + 1) :=
  ⟨fun t => x.1 (localWindowTime t) * localCutoff n (localWindowTime t),
    localWindowRestriction_isCadlag
      (x.2.mul (localCutoff_continuous n).isCadlag)⟩




@[simp] theorem cutoffWindow_endpoint (n : ℕ) (x : CadlagLocal) :
    (cutoffWindow n x).1 ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩ = 0 := by
  simp [cutoffWindow, localCutoff, localWindowTime]




theorem cutoffWindow_endpoint_tendsto (n : ℕ) (x : CadlagLocal) :
    Tendsto (fun t : J1Window ((n : ℝ) + 1) => (cutoffWindow n x).1 t)
      (𝓝[Set.Iio ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩]
        ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩) (𝓝 0) := by
  let endpoint : Set.Ici (0 : ℝ) :=
    ⟨(n : ℝ) + 1, by change (0 : ℝ) ≤ (n : ℝ) + 1; positivity⟩
  obtain ⟨l, hl⟩ := x.2.tendsto_nhdsLT endpoint
  have hcut : Tendsto (localCutoff n) (𝓝[Set.Iio endpoint] endpoint) (𝓝 0) := by
    have hcont : Tendsto (localCutoff n) (𝓝[Set.Iio endpoint] endpoint)
        (𝓝 (localCutoff n endpoint)) :=
      (localCutoff_continuous n).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [localCutoff, endpoint] using hcont
  have hprod : Tendsto (fun t => x.1 t * localCutoff n t)
      (𝓝[Set.Iio endpoint] endpoint) (𝓝 0) := by
    simpa using hl.mul hcut
  have hmap : Tendsto (localWindowTime (T := (n : ℝ) + 1))
      (𝓝[Set.Iio ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩]
        ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩)
      (𝓝[Set.Iio endpoint] endpoint) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(localWindowTime_continuous.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro t ht
    change (t : ℝ) < (n : ℝ) + 1 at ht
    exact Set.mem_Iio.mpr ht
  have hcomp := hprod.comp hmap
  change Tendsto (fun t : J1Window ((n : ℝ) + 1) =>
    x.1 (localWindowTime t) * localCutoff n (localWindowTime t))
      (𝓝[Set.Iio ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩]
        ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩) (𝓝 0) at hcomp
  simpa [cutoffWindow] using hcomp




theorem cutoffWindow_endpoint_continuousAt (n : ℕ) (x : CadlagLocal) :
    ContinuousAt (fun t : J1Window ((n : ℝ) + 1) => (cutoffWindow n x).1 t)
      ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩ := by
  let e : J1Window ((n : ℝ) + 1) :=
    ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩
  rw [ContinuousAt]
  change Tendsto (fun t : J1Window ((n : ℝ) + 1) =>
    (cutoffWindow n x).1 t) (𝓝 e) (𝓝 ((cutoffWindow n x).1 e))
  rw [cutoffWindow_endpoint]
  rw [← nhdsLT_sup_nhdsGE e]
  apply Tendsto.sup
  · simpa only [e] using cutoffWindow_endpoint_tendsto n x
  · have hright : Tendsto
        (fun t : J1Window ((n : ℝ) + 1) => (cutoffWindow n x).1 t)
        (𝓝[Set.Ici e] e) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hte : t = e := by
        apply Subtype.ext
        exact le_antisymm t.property.2 ht
      simp [hte, e]
    simpa only [nhdsWithin, Set.Ici] using hright




noncomputable def localJ1Term (n : ℕ) (x y : CadlagLocal) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1) *
    min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y))

private theorem localJ1Term_nonneg (n : ℕ) (x y : CadlagLocal) :
    0 ≤ localJ1Term n x y := by
  apply mul_nonneg (by positivity)
  exact le_min (by norm_num) (j1WindowDist_nonneg _ _ _)

private theorem localJ1Term_le_geometric (n : ℕ) (x y : CadlagLocal) :
    localJ1Term n x y ≤ (1 / 2 : ℝ) ^ n := by
  unfold localJ1Term
  have hw : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  calc
    (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) ≤
      (1 / 2 : ℝ) ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hw
    _ ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      norm_num




theorem localJ1Term_summable (x y : CadlagLocal) :
    Summable (fun n => localJ1Term n x y) := by
  exact Summable.of_nonneg_of_le
    (fun n => localJ1Term_nonneg n x y)
    (fun n => localJ1Term_le_geometric n x y) summable_geometric_two




noncomputable def j1LocalDist (x y : CadlagLocal) : ℝ :=
  ∑' n : ℕ, localJ1Term n x y




noncomputable def localWindowCoordinates (x : CadlagLocal) :
    (n : ℕ) → CadlagWindow ((n : ℝ) + 1) :=
  fun n => cutoffWindow n x




noncomputable def weightedJ1ProductDist
    (u v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1)) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
    min 1 (j1WindowDist (by positivity) (u n) (v n))

private theorem weightedJ1ProductTerm_nonneg (n : ℕ)
    (u v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1)) :
    0 ≤ (1 / 2 : ℝ) ^ (n + 1) *
      min 1 (j1WindowDist (by positivity) (u n) (v n)) := by
  apply mul_nonneg (by positivity)
  exact le_min (by norm_num) (j1WindowDist_nonneg _ _ _)

private theorem weightedJ1ProductTerm_le_geometric (n : ℕ)
    (u v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1)) :
    (1 / 2 : ℝ) ^ (n + 1) *
      min 1 (j1WindowDist (by positivity) (u n) (v n)) ≤ (1 / 2 : ℝ) ^ n := by
  have hw : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hw
    _ ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      norm_num

private theorem weightedJ1ProductDist_summable
    (u v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1)) :
    Summable (fun n => (1 / 2 : ℝ) ^ (n + 1) *
      min 1 (j1WindowDist (by positivity) (u n) (v n))) :=
  Summable.of_nonneg_of_le
    (fun n => weightedJ1ProductTerm_nonneg n u v)
    (fun n => weightedJ1ProductTerm_le_geometric n u v) summable_geometric_two

private theorem weighted_min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases h1 : 1 ≤ a
  · rw [min_eq_left h1]
    calc
      min 1 (a + b) ≤ 1 := min_le_left _ _
      _ ≤ 1 + min 1 b := le_add_of_nonneg_right (le_min (by norm_num) hb)
  · by_cases h2 : 1 ≤ b
    · rw [min_eq_left h2]
      calc
        min 1 (a + b) ≤ 1 := min_le_left _ _
        _ ≤ min 1 a + 1 := le_add_of_nonneg_left (le_min (by norm_num) ha)
    · have ha' : a ≤ 1 := le_of_not_ge h1
      have hb' : b ≤ 1 := le_of_not_ge h2
      rw [min_eq_right ha', min_eq_right hb']
      exact min_le_right _ _

private theorem weightedJ1ProductTerm_triangle (n : ℕ)
    (u v w : (n : ℕ) → CadlagWindow ((n : ℝ) + 1)) :
    (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (u n) (w n)) ≤
      (1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (u n) (v n)) +
        (1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (v n) (w n)) := by
  have huv := j1WindowDist_nonneg (by positivity) (u n) (v n)
  have hvw := j1WindowDist_nonneg (by positivity) (v n) (w n)
  have htri := j1WindowDist_triangle (by positivity) (u n) (v n) (w n)
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (u n) (v n) +
          j1WindowDist (by positivity) (v n) (w n)) :=
      mul_le_mul_of_nonneg_left (min_le_min_left 1 htri) (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) *
        (min 1 (j1WindowDist (by positivity) (u n) (v n)) +
          min 1 (j1WindowDist (by positivity) (v n) (w n))) :=
      mul_le_mul_of_nonneg_left (weighted_min_one_add_le _ _ huv hvw) (by positivity)
    _ = _ := by ring




theorem j1LocalDist_coordinates (x y : CadlagLocal) :
    j1LocalDist x y = weightedJ1ProductDist
      (localWindowCoordinates x) (localWindowCoordinates y) := rfl




theorem j1LocalDist_nonneg (x y : CadlagLocal) : 0 ≤ j1LocalDist x y := by
  exact tsum_nonneg (fun n => localJ1Term_nonneg n x y)




theorem j1LocalDist_symm (x y : CadlagLocal) :
    j1LocalDist x y = j1LocalDist y x := by
  simp [j1LocalDist, localJ1Term, j1WindowDist_symm]

private theorem min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases h1 : 1 ≤ a
  · rw [min_eq_left h1]
    calc
      min 1 (a + b) ≤ 1 := min_le_left _ _
      _ ≤ 1 + min 1 b := by
        exact le_add_of_nonneg_right (le_min (by norm_num) hb)
  · by_cases h2 : 1 ≤ b
    · rw [min_eq_left h2]
      calc
        min 1 (a + b) ≤ 1 := min_le_left _ _
        _ ≤ min 1 a + 1 := by
          exact le_add_of_nonneg_left (le_min (by norm_num) ha)
    · have ha' : a ≤ 1 := le_of_not_ge h1
      have hb' : b ≤ 1 := le_of_not_ge h2
      rw [min_eq_right ha', min_eq_right hb']
      exact min_le_right _ _

private theorem localJ1Term_triangle (n : ℕ) (x y z : CadlagLocal) :
    localJ1Term n x z ≤ localJ1Term n x y + localJ1Term n y z := by
  unfold localJ1Term
  have hdxy := j1WindowDist_nonneg (by positivity)
    (cutoffWindow n x) (cutoffWindow n y)
  have hdyz := j1WindowDist_nonneg (by positivity)
    (cutoffWindow n y) (cutoffWindow n z)
  have htri := j1WindowDist_triangle (by positivity)
    (cutoffWindow n x) (cutoffWindow n y) (cutoffWindow n z)
  have hmin := min_one_add_le _ _ hdxy hdyz
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y) +
          j1WindowDist (by positivity) (cutoffWindow n y) (cutoffWindow n z)) :=
      mul_le_mul_of_nonneg_left (min_le_min_left 1 htri) (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) *
        (min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) +
          min 1 (j1WindowDist (by positivity) (cutoffWindow n y) (cutoffWindow n z))) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = _ := by ring




theorem localCutoff_eq_one (n : ℕ) (t : Set.Ici (0 : ℝ))
    (ht : (t : ℝ) ≤ (n : ℝ)) : localCutoff n t = 1 := by
  unfold localCutoff
  have hm : 1 ≤ (n : ℝ) + 1 - (t : ℝ) := by linarith
  rw [min_eq_left hm]
  norm_num

private theorem cutoffWindow_point_eq (n : ℕ) (x : CadlagLocal)
    (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) ≤ (n : ℝ)) :
    (cutoffWindow n x).1
      ⟨(t : ℝ), ⟨t.property, by linarith⟩⟩ = x.1 t := by
  simp [cutoffWindow, localWindowTime, localCutoff_eq_one n t ht]

private theorem cutoffWindow_eq_of_j1LocalDist_eq_zero (n : ℕ)
    (x y : CadlagLocal) (hxy : j1LocalDist x y = 0) :
    cutoffWindow n x = cutoffWindow n y := by
  have hterm : localJ1Term n x y ≤ j1LocalDist x y :=
    (localJ1Term_summable x y).le_tsum n
      (fun i _ => localJ1Term_nonneg i x y)
  have hterm0 : localJ1Term n x y = 0 := by
    rw [hxy] at hterm
    exact le_antisymm hterm (localJ1Term_nonneg n x y)
  have hmin :
      min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) = 0 := by
    unfold localJ1Term at hterm0
    have hw : (1 / 2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hterm0).resolve_left hw
  have hd : j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y) = 0 := by
    by_contra hdne
    have hdpos : 0 < j1WindowDist (by positivity)
        (cutoffWindow n x) (cutoffWindow n y) :=
      lt_of_le_of_ne (j1WindowDist_nonneg _ _ _) (Ne.symm hdne)
    have : 0 < min 1
        (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) :=
      lt_min (by norm_num) hdpos
    rw [hmin] at this
    exact (lt_irrefl 0 this)
  exact (j1WindowDist_eq_zero_iff (by positivity) _ _).mp hd




theorem j1LocalDist_triangle (x y z : CadlagLocal) :
    j1LocalDist x z ≤ j1LocalDist x y + j1LocalDist y z := by
  unfold j1LocalDist
  calc
    ∑' n, localJ1Term n x z ≤ ∑' n, (localJ1Term n x y + localJ1Term n y z) :=
      (localJ1Term_summable x z).tsum_le_tsum
        (fun n => localJ1Term_triangle n x y z)
        ((localJ1Term_summable x y).add (localJ1Term_summable y z))
    _ = _ := Summable.tsum_add (localJ1Term_summable x y)
      (localJ1Term_summable y z)




theorem j1LocalDist_eq_zero_iff (x y : CadlagLocal) :
    j1LocalDist x y = 0 ↔ x = y := by
  constructor
  · intro hxy
    apply Subtype.ext
    funext t
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    have hnle : (t : ℝ) ≤ (n : ℝ) := le_of_lt hn
    have hwindow := cutoffWindow_eq_of_j1LocalDist_eq_zero n x y hxy
    have hpoint := congrArg
      (fun w : CadlagWindow ((n : ℝ) + 1) =>
        w.1 ⟨(t : ℝ), ⟨t.property, by linarith⟩⟩) hwindow
    rw [cutoffWindow_point_eq n x t hnle,
      cutoffWindow_point_eq n y t hnle] at hpoint
    exact hpoint
  · rintro rfl
    simp [j1LocalDist, localJ1Term, j1WindowDist_self]




@[instance_reducible] noncomputable instance j1LocalMetricSpace :
    MetricSpace CadlagLocal where
  dist := j1LocalDist
  dist_self x := by
    simp [j1LocalDist, localJ1Term, j1WindowDist_self]
  dist_comm := j1LocalDist_symm
  dist_triangle := j1LocalDist_triangle
  eq_of_dist_eq_zero := fun h => (j1LocalDist_eq_zero_iff _ _).mp h




@[instance_reducible] noncomputable instance weightedJ1ProductMetricSpace :
    MetricSpace ((n : ℕ) → CadlagWindow ((n : ℝ) + 1)) where
  dist := weightedJ1ProductDist
  dist_self u := by
    simp [weightedJ1ProductDist, j1WindowDist_self]
  dist_comm u v := by
    simp [weightedJ1ProductDist, j1WindowDist_symm]
  dist_triangle u v w := by
    unfold weightedJ1ProductDist
    calc
      ∑' n, (1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (u n) (w n)) ≤
        ∑' n, ((1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (u n) (v n)) +
          (1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (v n) (w n))) :=
        (weightedJ1ProductDist_summable u w).tsum_le_tsum
          (fun n => weightedJ1ProductTerm_triangle n u v w)
          ((weightedJ1ProductDist_summable u v).add
            (weightedJ1ProductDist_summable v w))
      _ = _ := Summable.tsum_add
        (weightedJ1ProductDist_summable u v)
        (weightedJ1ProductDist_summable v w)
  eq_of_dist_eq_zero := by
    intro u v huv
    apply funext
    intro n
    have hterm :
        (1 / 2 : ℝ) ^ (n + 1) *
          min 1 (j1WindowDist (by positivity) (u n) (v n)) ≤
        weightedJ1ProductDist u v :=
      (weightedJ1ProductDist_summable u v).le_tsum n
        (fun i _ => weightedJ1ProductTerm_nonneg i u v)
    rw [huv] at hterm
    have hterm0 : (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (u n) (v n)) = 0 :=
      le_antisymm hterm (weightedJ1ProductTerm_nonneg n u v)
    have hmin : min 1 (j1WindowDist (by positivity) (u n) (v n)) = 0 := by
      have hw : (1 / 2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hterm0).resolve_left hw
    have hd : j1WindowDist (by positivity) (u n) (v n) = 0 := by
      by_contra hdne
      have hdpos : 0 < j1WindowDist (by positivity) (u n) (v n) :=
        lt_of_le_of_ne (j1WindowDist_nonneg _ _ _) (Ne.symm hdne)
      have hpos : 0 < min 1 (j1WindowDist (by positivity) (u n) (v n)) :=
        lt_min (by norm_num) hdpos
      rw [hmin] at hpos
      exact (lt_irrefl 0 hpos)
    exact (j1WindowDist_eq_zero_iff (by positivity) (u n) (v n)).mp hd




theorem weightedJ1ProductDist_tendsto_coordinate
    (u : ℕ → (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto (fun k => weightedJ1ProductDist (u k) v)
      atTop (𝓝 0)) (i : ℕ) :
    Tendsto (fun k => j1WindowDist (by positivity) (u k i) (v i))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let w : ℝ := (1 / 2 : ℝ) ^ (i + 1)
  have hw : 0 < w := by positivity
  have hε' : 0 < min ε 1 := lt_min hε (by norm_num)
  have hδ : 0 < w * min ε 1 := mul_pos hw hε'
  filter_upwards [(tendsto_order.1 hu).2 (w * min ε 1) hδ] with k hk
  have hterm : w * min 1
      (j1WindowDist (by positivity) (u k i) (v i)) ≤
        weightedJ1ProductDist (u k) v := by
    unfold weightedJ1ProductDist
    change w * min 1 (j1WindowDist (by positivity) (u k i) (v i)) ≤
      ∑' n, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (j1WindowDist (by positivity) (u k n) (v n))
    simpa [w] using
      (weightedJ1ProductDist_summable (u k) v).le_tsum i
        (fun n _ => weightedJ1ProductTerm_nonneg n (u k) v)
  have hstrict : w * min 1
      (j1WindowDist (by positivity) (u k i) (v i)) < w * min ε 1 :=
    hterm.trans_lt hk
  have hmin : min 1
      (j1WindowDist (by positivity) (u k i) (v i)) < min ε 1 :=
    by
    by_contra h
    have hle : min ε 1 ≤ min 1
        (j1WindowDist (by positivity) (u k i) (v i)) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle hw.le
    exact (not_lt_of_ge hmul) hstrict
  have hdist : j1WindowDist (by positivity) (u k i) (v i) < ε := by
    have hltone : j1WindowDist (by positivity) (u k i) (v i) < 1 := by
      by_contra h
      have heq : min 1 (j1WindowDist (by positivity) (u k i) (v i)) = 1 :=
        min_eq_left (le_of_not_gt h)
      rw [heq] at hmin
      exact (not_lt_of_ge (min_le_right ε 1)) hmin
    rw [min_eq_right hltone.le] at hmin
    exact hmin.trans_le (min_le_left ε 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (j1WindowDist_nonneg (by positivity) (u k i) (v i))]
  exact hdist




theorem localWindowCoordinates_isometry : Isometry localWindowCoordinates := by
  apply Isometry.of_dist_eq
  intro x y
  change j1LocalDist x y = weightedJ1ProductDist
    (localWindowCoordinates x) (localWindowCoordinates y)
  exact j1LocalDist_coordinates x y




theorem localWindowCoordinates_tendsto_coordinate
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (i : ℕ) :
    Tendsto (fun k => localWindowCoordinates (x k) i) atTop
      (@nhds (CadlagWindow ((i : ℝ) + 1))
        (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace (v i)) := by
  let hT : 0 < (i : ℝ) + 1 := by positivity
  apply (@Metric.tendsto_nhds _ ℕ
    (j1WindowMetricSpace hT).toPseudoMetricSpace).mpr
  intro ε hε
  have hd := weightedJ1ProductDist_tendsto_coordinate
    (fun k => localWindowCoordinates (x k)) v hu i
  filter_upwards [(Metric.tendsto_nhds.mp hd ε hε)] with k hk
  have hdist : j1WindowDist hT (localWindowCoordinates (x k) i) (v i) < ε := by
    have hnonneg := j1WindowDist_nonneg hT (localWindowCoordinates (x k) i) (v i)
    simpa only [Real.dist_eq, abs_of_nonneg hnonneg, sub_zero] using hk
  exact hdist




theorem localWindowCoordinates_limit_endpoint_zero
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) :
    (v n).1 ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩ = 0 := by
  let hT : 0 < (n : ℝ) + 1 := by positivity
  have hcoord : Tendsto (fun k => localWindowCoordinates (x k) n) atTop
      (@nhds (CadlagWindow ((n : ℝ) + 1))
        (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace (v n)) :=
    localWindowCoordinates_tendsto_coordinate x v hu n
  let e : J1Window ((n : ℝ) + 1) := ⟨(n : ℝ) + 1, ⟨hT.le, le_rfl⟩⟩
  have heval : Tendsto (fun k => (localWindowCoordinates (x k) n).1 e)
      atTop (𝓝 ((v n).1 e)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hdist := (@Metric.tendsto_nhds _ ℕ
      (j1WindowMetricSpace hT).toPseudoMetricSpace).mp hcoord
    filter_upwards [hdist ε hε] with k hk
    have hdist : j1WindowDist hT (localWindowCoordinates (x k) n) (v n) < ε := by
      change j1WindowDist hT (localWindowCoordinates (x k) n) (v n) < ε at hk
      exact hk
    have hbound := j1WindowDist_eval_endpoint_le hT (localWindowCoordinates (x k) n)
      (v n)
    rw [Real.dist_eq]
    change |(localWindowCoordinates (x k) n).1 e - (v n).1 e| < ε
    have hbound' : |(localWindowCoordinates (x k) n).1 e - (v n).1 e| ≤
        j1WindowDist hT (localWindowCoordinates (x k) n) (v n) := by
      simpa [e] using hbound
    exact hbound'.trans_lt hdist
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 ((v n).1 e)) := by
    have hzero (k : ℕ) : (localWindowCoordinates (x k) n).1 e = 0 := by
      change (cutoffWindow n (x k)).1 e = 0
      exact cutoffWindow_endpoint n (x k)
    have h' := heval.congr' (Filter.Eventually.of_forall hzero)
    simpa using h'
  have heq := tendsto_nhds_unique tendsto_const_nhds hconst
  simpa [e] using heq.symm




theorem localWindowCoordinates_limits_satisfy_cutoff_at_continuity
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ (n : ℝ) + 1)
    (hvn : ContinuousAt (v n).1 ⟨t, ⟨ht0, ht⟩⟩)
    (hvnext : ContinuousAt (v (n + 1)).1
      ⟨t, ⟨ht0, by have := ht; push_cast at *; linarith⟩⟩) :
    (v n).1 ⟨t, ⟨ht0, ht⟩⟩ =
      localCutoff n ⟨t, ht0⟩ *
        (v (n + 1)).1 ⟨t, ⟨ht0, by have := ht; push_cast at *; linarith⟩⟩ := by
  let a : J1Window ((n : ℝ) + 1) := ⟨t, ⟨ht0, ht⟩⟩
  let b : J1Window (((n + 1 : ℕ) : ℝ) + 1) :=
    ⟨t, ⟨ht0, by have := ht; push_cast at *; linarith⟩⟩
  have hna := localWindowCoordinates_tendsto_coordinate x v hu n
  have hnb := localWindowCoordinates_tendsto_coordinate x v hu (n + 1)
  have hEvalnC := j1Window_eval_continuousAt (T := (n : ℝ) + 1)
    (by positivity) (v n) a hvn
  change Tendsto (fun f : CadlagWindow ((n : ℝ) + 1) => f.1 a)
    (@nhds (CadlagWindow ((n : ℝ) + 1))
      (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace (v n))
    (𝓝 ((v n).1 a)) at hEvalnC
  have hEvaln := hEvalnC.comp hna
  have hEvalnextC := j1Window_eval_continuousAt
    (T := ((n + 1 : ℕ) : ℝ) + 1) (by positivity) (v (n + 1)) b hvnext
  change Tendsto (fun f : CadlagWindow (((n + 1 : ℕ) : ℝ) + 1) => f.1 b)
    (@nhds (CadlagWindow (((n + 1 : ℕ) : ℝ) + 1))
      (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace
        (v (n + 1))) (𝓝 ((v (n + 1)).1 b)) at hEvalnextC
  have hEvalnext := hEvalnextC.comp hnb
  have hscaled : Tendsto (fun k : ℕ => localCutoff n ⟨t, ht0⟩ *
      (localWindowCoordinates (x k) (n + 1)).1 b) atTop
      (𝓝 (localCutoff n ⟨t, ht0⟩ * (v (n + 1)).1 b)) := by
    exact (tendsto_const_nhds.mul hEvalnext)
  have hpoint (k : ℕ) :
      (localWindowCoordinates (x k) n).1 a =
        localCutoff n ⟨t, ht0⟩ *
          (localWindowCoordinates (x k) (n + 1)).1 b := by
    change (cutoffWindow n (x k)).1 a =
      localCutoff n ⟨t, ht0⟩ * (cutoffWindow (n + 1) (x k)).1 b
    simp only [cutoffWindow, localWindowTime]
    have ht' : (t : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact ht
    have htI : (⟨t, ht0⟩ : Set.Ici (0 : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) := ht'
    rw [localCutoff_eq_one (n + 1) ⟨t, ht0⟩ htI]
    ring
  have hEvalnext' : Tendsto
      (fun k : ℕ => (localWindowCoordinates (x k) n).1 a) atTop
      (𝓝 (localCutoff n ⟨t, ht0⟩ * (v (n + 1)).1 b)) := hscaled.congr'
    (Filter.Eventually.of_forall fun k => by
      simpa [a, b] using (hpoint k).symm)
  have hEvaln' : Tendsto (fun k : ℕ => (localWindowCoordinates (x k) n).1 a)
      atTop (𝓝 ((v n).1 a)) := by
    exact hEvaln
  exact tendsto_nhds_unique hEvaln' hEvalnext'




theorem localWindowCoordinates_limits_agree_at_continuity
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ (n : ℝ))
    (hvn : ContinuousAt (v n).1
      ⟨t, ⟨ht0, by linarith⟩⟩)
    (hvnext : ContinuousAt (v (n + 1)).1
      ⟨t, ⟨ht0, by have := htn; norm_num at *; linarith⟩⟩) :
    (v n).1 ⟨t, ⟨ht0, by linarith⟩⟩ =
      (v (n + 1)).1
        ⟨t, ⟨ht0, by have := htn; norm_num at *; linarith⟩⟩ := by
  let a : J1Window ((n : ℝ) + 1) := ⟨t, ⟨ht0, by linarith⟩⟩
  let b : J1Window ((↑(n + 1) : ℝ) + 1) :=
    ⟨t, ⟨ht0, by have := htn; norm_num at *; linarith⟩⟩
  have hna : Tendsto (fun k => localWindowCoordinates (x k) n) atTop
      (@nhds (CadlagWindow ((n : ℝ) + 1))
        (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace (v n)) :=
    localWindowCoordinates_tendsto_coordinate x v hu n
  have hnb : Tendsto (fun k => localWindowCoordinates (x k) (n + 1)) atTop
      (@nhds (CadlagWindow ((↑(n + 1) : ℝ) + 1))
        (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace
        (v (n + 1))) :=
    localWindowCoordinates_tendsto_coordinate x v hu (n + 1)
  have hEvalnC := j1Window_eval_continuousAt (T := (n : ℝ) + 1)
    (by positivity) (v n) a hvn
  change Tendsto (fun f : CadlagWindow ((n : ℝ) + 1) => f.1 a)
    (@nhds (CadlagWindow ((n : ℝ) + 1))
      (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace (v n))
    (𝓝 ((v n).1 a)) at hEvalnC
  have hEvaln := hEvalnC
  have hEvalnextC := j1Window_eval_continuousAt
    (T := (↑(n + 1) : ℝ) + 1) (by positivity) (v (n + 1)) b hvnext
  change Tendsto (fun f : CadlagWindow ((↑(n + 1) : ℝ) + 1) => f.1 b)
    (@nhds (CadlagWindow ((↑(n + 1) : ℝ) + 1))
      (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace
      (v (n + 1))) (𝓝 ((v (n + 1)).1 b)) at hEvalnextC
  have hEvalnext := hEvalnextC
  have hevn := hEvaln.comp hna
  have hevnext := hEvalnext.comp hnb
  have hpoint (k : ℕ) :
      (localWindowCoordinates (x k) n).1 a =
        (localWindowCoordinates (x k) (n + 1)).1 b := by
    change (cutoffWindow n (x k)).1 a =
      (cutoffWindow (n + 1) (x k)).1 b
    have hleft := cutoffWindow_point_eq n (x k) ⟨t, ht0⟩ htn
    have hright := cutoffWindow_point_eq (n + 1) (x k) ⟨t, ht0⟩ (by
      have := htn
      norm_num at *
      linarith)
    change (cutoffWindow n (x k)).1 a = (x k).1 ⟨t, ht0⟩ at hleft
    change (cutoffWindow (n + 1) (x k)).1 b = (x k).1 ⟨t, ht0⟩ at hright
    exact hleft.trans hright.symm
  exact tendsto_nhds_unique hevn
    (hevnext.congr' (Filter.Eventually.of_forall fun k => (hpoint k).symm))




theorem cadlagWindow_countable_discontinuities {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) :
    {t : J1Window T | ¬ ContinuousAt f.1 t}.Countable := by
  let x : J1WindowD T hT := ⟨f⟩
  let μ : MeasureTheory.Measure (J1WindowD T hT) := MeasureTheory.Measure.dirac x
  have hmeas (t : J1Window T) :
      MeasurableSet {y : J1WindowD T hT | ContinuousAt y.path.1 t} := by
    by_cases ht : (t : ℝ) = 0
    · have hall (y : J1WindowD T hT) : ContinuousAt y.path.1 t := by
        rw [cadlag_continuousAt_iff_j1WindowJump_eq_zero]
        simp [j1WindowJump, ht]
      have heq : {y : J1WindowD T hT | ContinuousAt y.path.1 t} = Set.univ := by
        ext y
        simp [hall y]
      rw [heq]
      exact MeasurableSet.univ
    · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have heq : {y : J1WindowD T hT | ContinuousAt y.path.1 t} =
          {y | j1WindowJump y t = 0} := by
        ext y
        exact cadlag_continuousAt_iff_j1WindowJump_eq_zero y t
      rw [heq]
      have hzero : {y : J1WindowD T hT | j1WindowJump y t = 0} =
          {y | ¬ 0 < j1WindowJump y t} := by
        ext y
        constructor
        · intro hy
          change j1WindowJump y t = 0 at hy
          change ¬ 0 < j1WindowJump y t
          rw [hy]
          norm_num
        · intro hy
          change ¬ 0 < j1WindowJump y t at hy
          apply le_antisymm (not_lt.mp hy)
          unfold j1WindowJump
          split_ifs
          positivity
      rw [hzero]
      exact (measurableSet_j1WindowJump_gt hT t 0).compl
  have hbad : {t : J1Window T | ¬ ContinuousAt f.1 t} ⊆
      (continuityTimes μ)ᶜ := by
    intro t ht
    change t ∉ continuityTimes μ
    intro hct
    have hct' : ∀ᵐ y ∂μ, ContinuousAt y.path.1 t := hct
    have hx : ContinuousAt x.path.1 t :=
      (MeasureTheory.ae_dirac_iff (hmeas t)).mp hct'
    exact ht hx
  exact (countable_compl_continuityTimes μ).mono hbad




theorem dense_common_continuityTimes_on_Icc {N T U : ℝ} (hN : 0 < N)
    (hNT : N < T) (hNU : N < U) (f : CadlagWindow T) (g : CadlagWindow U) :
    Dense {t : Set.Icc (0 : ℝ) N |
      ContinuousAt f.1 ⟨t, ⟨t.property.1, le_trans t.property.2 hNT.le⟩⟩ ∧
      ContinuousAt g.1 ⟨t, ⟨t.property.1, le_trans t.property.2 hNU.le⟩⟩} := by
  let Df : Set ℝ := Subtype.val ''
    {s : J1Window T | ¬ ContinuousAt f.1 s}
  let Dg : Set ℝ := Subtype.val ''
    {s : J1Window U | ¬ ContinuousAt g.1 s}
  let D : Set ℝ := Df ∪ Dg
  have hDf : Df.Countable :=
    (cadlagWindow_countable_discontinuities (hT := hN.trans hNT) f).image
      Subtype.val
  have hDg : Dg.Countable :=
    (cadlagWindow_countable_discontinuities (hT := hN.trans hNU) g).image
      Subtype.val
  have hD : D.Countable := hDf.union hDg
  apply Metric.dense_iff.mpr
  intro t ε hε
  let a : ℝ := max 0 ((t : ℝ) - ε / 2)
  let b : ℝ := min N ((t : ℝ) + ε / 2)
  have hab : a < b := by
    apply max_lt_iff.mpr
    constructor
    · apply lt_min
      · exact hN
      · have ht : 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ N := Set.mem_Icc.mp t.property
        have ht0 := ht.1
        linarith
    · apply lt_min
      · have ht : 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ N := Set.mem_Icc.mp t.property
        have htN := ht.2
        linarith
      · linarith
  have hex : ∃ r ∈ Set.Ioo a b, r ∉ D := by
    by_contra hn
    have hsub : Set.Ioo a b ⊆ D := by
      intro r hr
      by_contra hrd
      exact hn ⟨r, hr, hrd⟩
    have hcnt : (Set.Ioo a b).Countable := hD.mono hsub
    have hba : b ≤ a := by
      exact (Cardinal.Real.Ioo_countable_iff).mp hcnt
    exact (not_le_of_gt hab) hba
  obtain ⟨r, hr, hrD⟩ := hex
  have hra : a < r := hr.1
  have hrb : r < b := hr.2
  have hr0 : 0 ≤ r := by
    have : 0 ≤ a := le_max_left _ _
    linarith
  have hrN : r ≤ N := by
    have : b ≤ N := min_le_left _ _
    linarith
  have hrf : ContinuousAt f.1
      ⟨r, ⟨hr0, hrN.trans hNT.le⟩⟩ := by
    by_contra hbad
    have hrDf : r ∈ Df := ⟨⟨r, ⟨hr0, hrN.trans hNT.le⟩⟩, hbad, rfl⟩
    exact hrD (Or.inl hrDf)
  have hrg : ContinuousAt g.1
      ⟨r, ⟨hr0, hrN.trans hNU.le⟩⟩ := by
    by_contra hbad
    have hrDg : r ∈ Dg := ⟨⟨r, ⟨hr0, hrN.trans hNU.le⟩⟩, hbad, rfl⟩
    exact hrD (Or.inr hrDg)
  have ha : (t : ℝ) - ε / 2 ≤ a := le_max_right _ _
  have hb : b ≤ (t : ℝ) + ε / 2 := min_le_right _ _
  let s : Set.Icc (0 : ℝ) N := ⟨r, Set.mem_Icc.mpr ⟨hr0, hrN⟩⟩
  refine ⟨s, ?_, ⟨hrf, hrg⟩⟩
  change dist (r : ℝ) (t : ℝ) < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith




theorem localWindowCoordinates_limits_agree_before
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htn : t < (n : ℝ)) :
    (v n).1 ⟨t, ⟨ht0, le_of_lt (by linarith : t < (n : ℝ) + 1)⟩⟩ =
      (v (n + 1)).1 ⟨t, ⟨ht0, le_of_lt (by
        have hn : (n : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        linarith)⟩⟩ := by
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by dsimp [N]; linarith
  have hleft : N < (n : ℝ) + 1 := by dsimp [N]; norm_num
  have hright : N < ((n + 1 : ℕ) : ℝ) + 1 := by
    dsimp [N]
    push_cast
    linarith
  let S : Set (Set.Icc (0 : ℝ) N) := {s |
    ContinuousAt (v n).1 ⟨s, ⟨s.property.1, le_trans s.property.2 hleft.le⟩⟩ ∧
    ContinuousAt (v (n + 1)).1
      ⟨s, ⟨s.property.1, le_trans s.property.2 hright.le⟩⟩}
  have hS : Dense S := by
    simpa [S, N] using dense_common_continuityTimes_on_Icc
      (N := (n : ℝ)) (T := (n : ℝ) + 1)
      (U := ((n + 1 : ℕ) : ℝ) + 1) hN hleft hright (v n) (v (n + 1))
  let p : Set.Icc (0 : ℝ) N := ⟨t, ⟨ht0, htn.le⟩⟩
  let ρ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let δ (k : ℕ) : ℝ := min ((N - t) / 2) (ρ k)
  have hρ (k : ℕ) : 0 < ρ k := by
    dsimp [ρ]
    positivity
  have hδ (k : ℕ) : 0 < δ k := by
    dsimp [δ]
    exact lt_min (by linarith) (hρ k)
  have hδN (k : ℕ) : δ k ≤ (N - t) / 2 := min_le_left _ _
  have hδρ (k : ℕ) : δ k ≤ ρ k := min_le_right _ _
  let c (k : ℕ) : Set.Icc (0 : ℝ) N :=
    ⟨t + δ k, ⟨by linarith [hδ k], by linarith [hδN k]⟩⟩
  have hex (k : ℕ) : ∃ s ∈ S, dist (c k) s < δ k / 2 :=
    hS.exists_dist_lt (c k) (by positivity)
  choose q hqS hqdist using hex
  have hqbounds (k : ℕ) : t < (q k : ℝ) ∧ (q k : ℝ) < t + 2 * ρ k := by
    have hd : |(c k : ℝ) - (q k : ℝ)| < δ k / 2 := by
      have hd0 : dist (c k : ℝ) (q k : ℝ) < δ k / 2 := by
        simpa only [Subtype.dist_eq] using hqdist k
      simpa only [Real.dist_eq] using hd0
    rw [abs_lt] at hd
    constructor
    · dsimp [c] at hd ⊢
      linarith [hδ k]
    · dsimp [c] at hd ⊢
      linarith [hδ k, hδρ k]
  have hqreal : Tendsto (fun k => (q k : ℝ)) atTop (𝓝 t) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hev : ∀ᶠ k : ℕ in atTop, ρ k < ε / 2 := by
      have hzero := tendsto_one_div_add_atTop_nhds_zero_nat
        (𝕜 := ℝ)
      exact hzero.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hev] with k hk
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hqbounds k]
    · linarith [hqbounds k]
  have hqsub : Tendsto q atTop (𝓝 p) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hqreal ε hε)] with k hk
    simpa only [Subtype.dist_eq] using hk
  let leftWin (s : Set.Icc (0 : ℝ) N) : J1Window ((n : ℝ) + 1) :=
    ⟨s, ⟨s.property.1, le_trans s.property.2 hleft.le⟩⟩
  let rightWin (s : Set.Icc (0 : ℝ) N) :
      J1Window (((n + 1 : ℕ) : ℝ) + 1) :=
    ⟨s, ⟨s.property.1, le_trans s.property.2 hright.le⟩⟩
  have hleftCont : Continuous leftWin := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val
  have hrightCont : Continuous rightWin := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val
  let a : J1Window ((n : ℝ) + 1) :=
    ⟨t, ⟨ht0, le_of_lt (by linarith)⟩⟩
  let b : J1Window (((n + 1 : ℕ) : ℝ) + 1) :=
    ⟨t, ⟨ht0, le_of_lt (by linarith)⟩⟩
  have hleftAt : leftWin p = a := by
    apply Subtype.ext
    rfl
  have hrightAt : rightWin p = b := by
    apply Subtype.ext
    rfl
  have hleftNhds : Tendsto (fun k => leftWin (q k)) atTop (𝓝 a) := by
    rw [← hleftAt]
    exact hleftCont.continuousAt.tendsto.comp hqsub
  have hrightNhds : Tendsto (fun k => rightWin (q k)) atTop (𝓝 b) := by
    rw [← hrightAt]
    exact hrightCont.continuousAt.tendsto.comp hqsub
  have hleftWithin : Tendsto (fun k => leftWin (q k)) atTop (𝓝[Set.Ioi a] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hleftNhds, ?_⟩
    filter_upwards [] with k
    change (t : ℝ) < (q k : ℝ)
    exact (hqbounds k).1
  have hrightWithin : Tendsto (fun k => rightWin (q k)) atTop
      (𝓝[Set.Ioi b] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hrightNhds, ?_⟩
    filter_upwards [] with k
    change (t : ℝ) < (q k : ℝ)
    exact (hqbounds k).1
  have hleftLimit : Tendsto (fun k => (v n).1 (leftWin (q k))) atTop
      (𝓝 ((v n).1 a)) :=
    ((v n).2.isRightContinuous a).tendsto.comp hleftWithin
  have hrightLimit : Tendsto (fun k => (v (n + 1)).1 (rightWin (q k))) atTop
      (𝓝 ((v (n + 1)).1 b)) :=
    ((v (n + 1)).2.isRightContinuous b).tendsto.comp hrightWithin
  have heq (k : ℕ) : (v n).1 (leftWin (q k)) =
      (v (n + 1)).1 (rightWin (q k)) := by
    have hmem := hqS k
    change ContinuousAt (v n).1
        ⟨q k, ⟨(q k).property.1, le_trans (q k).property.2 hleft.le⟩⟩ ∧
      ContinuousAt (v (n + 1)).1
        ⟨q k, ⟨(q k).property.1, le_trans (q k).property.2 hright.le⟩⟩ at hmem
    exact localWindowCoordinates_limits_agree_at_continuity x v hu n
      (q k : ℝ) (q k).property.1 (q k).property.2 hmem.1 hmem.2
  exact tendsto_nhds_unique hleftLimit
    (hrightLimit.congr' (Filter.Eventually.of_forall fun k => (heq k).symm))




theorem localWindowCoordinates_limits_satisfy_cutoff
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ (n : ℝ) + 1) :
    (v n).1 ⟨t, ⟨ht0, ht⟩⟩ = localCutoff n ⟨t, ht0⟩ *
      (v (n + 1)).1 ⟨t, ⟨ht0, by
        have hn : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        exact ht.trans hn⟩⟩ := by
  by_cases hend : t = (n : ℝ) + 1
  · subst t
    rw [localWindowCoordinates_limit_endpoint_zero x v hu n]
    simp [localCutoff]
  · have htlt : t < (n : ℝ) + 1 := lt_of_le_of_ne ht hend
    let N : ℝ := (t + ((n : ℝ) + 1)) / 2
    have htN : t < N := by
      dsimp [N]
      linarith
    have hNend : N < (n : ℝ) + 1 := by
      dsimp [N]
      linarith
    have hNpos : 0 < N := by linarith
    have hNnext : N < ((n + 1 : ℕ) : ℝ) + 1 := by
      have : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        linarith
      exact hNend.trans_le this
    let S : Set (Set.Icc (0 : ℝ) N) := {s |
      ContinuousAt (v n).1 ⟨s, ⟨s.property.1, le_trans s.property.2 hNend.le⟩⟩ ∧
      ContinuousAt (v (n + 1)).1
        ⟨s, ⟨s.property.1, le_trans s.property.2 hNnext.le⟩⟩}
    have hS : Dense S := by
      simpa [S] using dense_common_continuityTimes_on_Icc
        (N := N) (T := (n : ℝ) + 1)
        (U := ((n + 1 : ℕ) : ℝ) + 1) hNpos hNend hNnext
        (v n) (v (n + 1))
    let p : Set.Icc (0 : ℝ) N := ⟨t, ⟨ht0, htN.le⟩⟩
    let ρ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
    let δ (k : ℕ) : ℝ := min ((N - t) / 2) (ρ k)
    have hρ (k : ℕ) : 0 < ρ k := by
      dsimp [ρ]
      positivity
    have hδ (k : ℕ) : 0 < δ k := by
      dsimp [δ]
      exact lt_min (by linarith) (hρ k)
    have hδN (k : ℕ) : δ k ≤ (N - t) / 2 := min_le_left _ _
    have hδρ (k : ℕ) : δ k ≤ ρ k := min_le_right _ _
    let c (k : ℕ) : Set.Icc (0 : ℝ) N :=
      ⟨t + δ k, ⟨by linarith [hδ k], by linarith [hδN k]⟩⟩
    have hex (k : ℕ) : ∃ s ∈ S, dist (c k) s < δ k / 2 :=
      hS.exists_dist_lt (c k) (by positivity)
    choose q hqS hqdist using hex
    have hqbounds (k : ℕ) : t < (q k : ℝ) ∧ (q k : ℝ) < t + 2 * ρ k := by
      have hd : |(c k : ℝ) - (q k : ℝ)| < δ k / 2 := by
        have hd0 : dist (c k : ℝ) (q k : ℝ) < δ k / 2 := by
          simpa only [Subtype.dist_eq] using hqdist k
        simpa only [Real.dist_eq] using hd0
      rw [abs_lt] at hd
      constructor
      · dsimp [c] at hd ⊢
        linarith [hδ k]
      · dsimp [c] at hd ⊢
        linarith [hδ k, hδρ k]
    have hqreal : Tendsto (fun k => (q k : ℝ)) atTop (𝓝 t) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hev : ∀ᶠ k : ℕ in atTop, ρ k < ε / 2 := by
        have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        exact hzero.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [hev] with k hk
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hqbounds k]
    have hqsub : Tendsto q atTop (𝓝 p) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [(Metric.tendsto_nhds.mp hqreal ε hε)] with k hk
      simpa only [Subtype.dist_eq] using hk
    let leftWin (s : Set.Icc (0 : ℝ) N) : J1Window ((n : ℝ) + 1) :=
      ⟨s, ⟨s.property.1, le_trans s.property.2 hNend.le⟩⟩
    let rightWin (s : Set.Icc (0 : ℝ) N) :
        J1Window (((n + 1 : ℕ) : ℝ) + 1) :=
      ⟨s, ⟨s.property.1, le_trans s.property.2 hNnext.le⟩⟩
    have hleftCont : Continuous leftWin := by
      apply continuous_induced_rng.2
      exact continuous_subtype_val
    have hrightCont : Continuous rightWin := by
      apply continuous_induced_rng.2
      exact continuous_subtype_val
    let a : J1Window ((n : ℝ) + 1) := ⟨t, ⟨ht0, ht⟩⟩
    let b : J1Window (((n + 1 : ℕ) : ℝ) + 1) :=
      ⟨t, ⟨ht0, by
        have hn : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        exact ht.trans hn⟩⟩
    have hleftAt : leftWin p = a := by
      apply Subtype.ext
      rfl
    have hrightAt : rightWin p = b := by
      apply Subtype.ext
      rfl
    have hleftNhds : Tendsto (fun k => leftWin (q k)) atTop (𝓝 a) := by
      rw [← hleftAt]
      exact hleftCont.continuousAt.tendsto.comp hqsub
    have hrightNhds : Tendsto (fun k => rightWin (q k)) atTop (𝓝 b) := by
      rw [← hrightAt]
      exact hrightCont.continuousAt.tendsto.comp hqsub
    have hleftWithin : Tendsto (fun k => leftWin (q k)) atTop (𝓝[Set.Ioi a] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hleftNhds, ?_⟩
      filter_upwards [] with k
      change (t : ℝ) < (q k : ℝ)
      exact (hqbounds k).1
    have hrightWithin : Tendsto (fun k => rightWin (q k)) atTop
        (𝓝[Set.Ioi b] b) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hrightNhds, ?_⟩
      filter_upwards [] with k
      change (t : ℝ) < (q k : ℝ)
      exact (hqbounds k).1
    have hleftLimit : Tendsto (fun k => (v n).1 (leftWin (q k))) atTop
        (𝓝 ((v n).1 a)) := ((v n).2.isRightContinuous a).tendsto.comp hleftWithin
    have hrightLimit : Tendsto (fun k => (v (n + 1)).1 (rightWin (q k))) atTop
        (𝓝 ((v (n + 1)).1 b)) :=
      ((v (n + 1)).2.isRightContinuous b).tendsto.comp hrightWithin
    let cutoffAt (s : Set.Icc (0 : ℝ) N) : ℝ := localCutoff n ⟨s, s.property.1⟩
    have hcutCont : Continuous cutoffAt := by
      exact (localCutoff_continuous n).comp
        (continuous_subtype_val.subtype_mk fun s => s.property.1)
    have hcutLimit : Tendsto (fun k => cutoffAt (q k)) atTop (𝓝 (cutoffAt p)) :=
      hcutCont.continuousAt.tendsto.comp hqsub
    have hscaled : Tendsto
        (fun k => cutoffAt (q k) * (v (n + 1)).1 (rightWin (q k))) atTop
        (𝓝 (cutoffAt p * (v (n + 1)).1 b)) :=
      hcutLimit.mul hrightLimit
    have heq (k : ℕ) : (v n).1 (leftWin (q k)) =
        cutoffAt (q k) * (v (n + 1)).1 (rightWin (q k)) := by
      have hmem := hqS k
      change ContinuousAt (v n).1
          ⟨q k, ⟨(q k).property.1, le_trans (q k).property.2 hNend.le⟩⟩ ∧
        ContinuousAt (v (n + 1)).1
          ⟨q k, ⟨(q k).property.1, le_trans (q k).property.2 hNnext.le⟩⟩ at hmem
      have hpoint := localWindowCoordinates_limits_satisfy_cutoff_at_continuity
        x v hu n (q k : ℝ) (q k).property.1
        (le_trans (q k).property.2 hNend.le)
        hmem.1 hmem.2
      simpa [cutoffAt, leftWin, rightWin] using hpoint
    have hleftLimit' : Tendsto (fun k => (v n).1 (leftWin (q k))) atTop
        (𝓝 (cutoffAt p * (v (n + 1)).1 b)) :=
      hscaled.congr' (Filter.Eventually.of_forall fun k => (heq k).symm)
    have hresult := tendsto_nhds_unique hleftLimit hleftLimit'
    simpa [cutoffAt, p, a, b] using hresult




theorem localWindowCoordinates_limits_agree_at_or_before
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (htn : t ≤ (n : ℝ)) :
    (v n).1 ⟨t, ⟨ht0, by linarith⟩⟩ =
      (v (n + 1)).1 ⟨t, ⟨ht0, by
        have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        exact htn.trans hn⟩⟩ := by
  have h := localWindowCoordinates_limits_satisfy_cutoff
    x v hu n t ht0 (by linarith)
  rw [localCutoff_eq_one n ⟨t, ht0⟩ htn] at h
  simpa using h




def localWindowCoordinateAt
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (n : ℕ) (t : Set.Ici (0 : ℝ))
    (ht : (t : ℝ) ≤ (n : ℝ) + 1) : ℝ :=
  (v n).1 ⟨(t : ℝ), ⟨t.2, ht⟩⟩

private theorem localWindowCoordinateAt_step
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (n : ℕ) (t : Set.Ici (0 : ℝ))
    (htn : (t : ℝ) ≤ (n : ℝ)) :
    localWindowCoordinateAt v n t (by linarith) =
      localWindowCoordinateAt v (n + 1) t (by
        have hn : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        linarith) := by
  exact localWindowCoordinates_limits_agree_at_or_before
    x v hu n (t : ℝ) t.2 htn

private theorem localWindowCoordinateAt_chain
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (q m : ℕ) (t : Set.Ici (0 : ℝ))
    (htq : (t : ℝ) < (q : ℝ)) (hqm : q ≤ m) :
    localWindowCoordinateAt v q t (by linarith) =
      localWindowCoordinateAt v m t (by
        have hqmR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
        linarith) := by
  have hchain : ∀ d : ℕ,
        localWindowCoordinateAt v q t (by linarith) =
        localWindowCoordinateAt v (q + d) t (by
          have hqd : q ≤ q + d := Nat.le_add_right q d
          have hqdR : (q : ℝ) ≤ (q + d : ℕ) := by exact_mod_cast hqd
          have htqd : (t : ℝ) ≤ (q + d : ℕ) := (le_of_lt htq).trans hqdR
          linarith) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hqd : q ≤ q + d := Nat.le_add_right q d
      have hstep := localWindowCoordinateAt_step x v hu (q + d) t
        (le_trans (le_of_lt htq) (by exact_mod_cast hqd))
      exact ih.trans hstep
  have hlast := hchain (m - q)
  have hqm' : q + (m - q) = m := Nat.add_sub_of_le hqm
  simpa [hqm'] using hlast




noncomputable def localWindowGlueFun
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (t : Set.Ici (0 : ℝ)) : ℝ :=
  localWindowCoordinateAt v (⌊(t : ℝ)⌋₊ + 1) t (by
    have hfloor := Nat.lt_floor_add_one (t : ℝ)
    push_cast at hfloor ⊢
    linarith)

private theorem localWindowGlueFun_eq_coordinate
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) (m : ℕ) (t : Set.Ici (0 : ℝ))
    (htm : (t : ℝ) < (m : ℝ)) :
    localWindowGlueFun v t =
      localWindowCoordinateAt v m t (by linarith) := by
  let q : ℕ := ⌊(t : ℝ)⌋₊ + 1
  have htq : (t : ℝ) < (q : ℝ) := by
    dsimp [q]
    push_cast
    exact Nat.lt_floor_add_one (t : ℝ)
  have hqfloor : (⌊(t : ℝ)⌋₊ : ℝ) < (m : ℝ) :=
    (Nat.floor_le t.2).trans_lt htm
  have hqm : q ≤ m := by
    have hqfloorN : ⌊(t : ℝ)⌋₊ < m := by exact_mod_cast hqfloor
    dsimp [q]
    exact Nat.succ_le_of_lt hqfloorN
  exact localWindowCoordinateAt_chain x v hu q m t htq hqm




noncomputable def localWindowClamp (m : ℕ)
    (t : Set.Ici (0 : ℝ)) : J1Window ((m : ℝ) + 1) :=
  ⟨min (t : ℝ) ((m : ℝ) + 1),
    ⟨le_min t.2 (by positivity), min_le_right _ _⟩⟩

private theorem localWindowClamp_continuous (m : ℕ) :
    Continuous (localWindowClamp m) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val.min continuous_const

private theorem localWindowClamp_eq_self (m : ℕ)
    (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) < (m : ℝ) + 1) :
    localWindowClamp m t = ⟨(t : ℝ), ⟨t.2, le_of_lt ht⟩⟩ := by
  apply Subtype.ext
  exact min_eq_left ht.le




theorem localWindowGlueFun_isCadlag
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) :
    IsCadlag (localWindowGlueFun v) := by
  constructor
  · intro a
    let m : ℕ := ⌊(a : ℝ)⌋₊ + 2
    have haM : (a : ℝ) < (m : ℝ) := by
      dsimp [m]
      have hfloor := Nat.lt_floor_add_one (a : ℝ)
      push_cast at hfloor ⊢
      linarith
    let aw : J1Window ((m : ℝ) + 1) :=
      ⟨(a : ℝ), ⟨a.2, le_of_lt (by linarith)⟩⟩
    let mIci : Set.Ici (0 : ℝ) := ⟨(m : ℝ), Nat.cast_nonneg m⟩
    let endIci : Set.Ici (0 : ℝ) := ⟨(m : ℝ) + 1,
      add_nonneg (Nat.cast_nonneg m) (by norm_num)⟩
    have haM' : a < mIci := by change (a : ℝ) < (m : ℝ); exact haM
    have haEnd' : a < endIci := by change (a : ℝ) < (m : ℝ) + 1; linarith
    have haw : localWindowClamp m a = aw := by
      apply Subtype.ext
      exact min_eq_left (by linarith : (a : ℝ) ≤ (m : ℝ) + 1)
    let g : Set.Ici (0 : ℝ) → ℝ := fun s => (v m).1 (localWindowClamp m s)
    have hbaseR : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a,
        (s : ℝ) < (m : ℝ) + 1 := by
      filter_upwards [Iio_mem_nhds haEnd'] with s hs
      change (s : ℝ) < (m : ℝ) + 1 at hs
      exact hs
    have hnearR : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝[Set.Ioi a] a,
        (s : ℝ) < (m : ℝ) + 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hbaseR
    have hmapR : Tendsto (localWindowClamp m)
        (𝓝[Set.Ioi a] a) (𝓝[Set.Ioi aw] aw) := by
      rw [← haw]
      apply tendsto_nhdsWithin_iff.mpr
      have hcont : Tendsto (localWindowClamp m) (𝓝 a)
          (𝓝 (localWindowClamp m a)) :=
        (localWindowClamp_continuous m).continuousAt.tendsto
      have hcont' := hcont.mono_left
        (show 𝓝[Set.Ioi a] a ≤ 𝓝 a from nhdsWithin_le_nhds)
      refine ⟨hcont', ?_⟩
      filter_upwards [self_mem_nhdsWithin, hnearR] with s hsIoi hs
      change (a : ℝ) < (s : ℝ) at hsIoi
      rw [localWindowClamp_eq_self m a (by linarith),
        localWindowClamp_eq_self m s hs]
      exact hsIoi
    have hpathR : Tendsto g (𝓝[Set.Ioi a] a) (𝓝 (g a)) := by
      change Tendsto (fun s => (v m).1 (localWindowClamp m s)) _ _
      rw [show g a = (v m).1 aw by simp [g, haw]]
      exact ((v m).2.isRightContinuous aw).tendsto.comp hmapR
    have hnear : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝[Set.Ioi a] a,
        (s : ℝ) < (m : ℝ) := by
      have hbase : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a, (s : ℝ) < (m : ℝ) := by
        filter_upwards [Iio_mem_nhds haM'] with s hs
        change (s : ℝ) < (m : ℝ) at hs
        exact hs
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hbase
    have heq : ∀ᶠ s in 𝓝[Set.Ioi a] a,
        localWindowGlueFun v s = g s := by
      filter_upwards [hnear] with s hs
      rw [localWindowGlueFun_eq_coordinate x v hu m s hs]
      simp [localWindowCoordinateAt, g, localWindowClamp_eq_self m s (by linarith)]
    change Tendsto (localWindowGlueFun v) (𝓝[Set.Ioi a] a) (𝓝 (localWindowGlueFun v a))
    have haeq : g a = localWindowGlueFun v a := by
      symm
      rw [localWindowGlueFun_eq_coordinate x v hu m a haM]
      simp [localWindowCoordinateAt, g, localWindowClamp_eq_self m a (by linarith)]
    rw [← haeq]
    have heq' : ∀ᶠ s in 𝓝[Set.Ioi a] a, g s = localWindowGlueFun v s :=
      heq.mono fun s hs => hs.symm
    exact hpathR.congr' heq'
  · intro a
    let m : ℕ := ⌊(a : ℝ)⌋₊ + 2
    have haM : (a : ℝ) < (m : ℝ) := by
      dsimp [m]
      have hfloor := Nat.lt_floor_add_one (a : ℝ)
      push_cast at hfloor ⊢
      linarith
    let aw : J1Window ((m : ℝ) + 1) :=
      ⟨(a : ℝ), ⟨a.2, le_of_lt (by linarith)⟩⟩
    let mIci : Set.Ici (0 : ℝ) := ⟨(m : ℝ), Nat.cast_nonneg m⟩
    let endIci : Set.Ici (0 : ℝ) := ⟨(m : ℝ) + 1,
      add_nonneg (Nat.cast_nonneg m) (by norm_num)⟩
    have haM' : a < mIci := by change (a : ℝ) < (m : ℝ); exact haM
    have haEnd' : a < endIci := by change (a : ℝ) < (m : ℝ) + 1; linarith
    have haw : localWindowClamp m a = aw := by
      apply Subtype.ext
      exact min_eq_left (by linarith : (a : ℝ) ≤ (m : ℝ) + 1)
    let g : Set.Ici (0 : ℝ) → ℝ := fun s => (v m).1 (localWindowClamp m s)
    have hbaseL : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a,
        (s : ℝ) < (m : ℝ) + 1 := by
      filter_upwards [Iio_mem_nhds haEnd'] with s hs
      change (s : ℝ) < (m : ℝ) + 1 at hs
      exact hs
    have hnearL : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝[Set.Iio a] a,
        (s : ℝ) < (m : ℝ) + 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hbaseL
    have hmapL : Tendsto (localWindowClamp m)
        (𝓝[Set.Iio a] a) (𝓝[Set.Iio aw] aw) := by
      rw [← haw]
      apply tendsto_nhdsWithin_iff.mpr
      have hcont : Tendsto (localWindowClamp m) (𝓝 a)
          (𝓝 (localWindowClamp m a)) :=
        (localWindowClamp_continuous m).continuousAt.tendsto
      have hcont' := hcont.mono_left
        (show 𝓝[Set.Iio a] a ≤ 𝓝 a from nhdsWithin_le_nhds)
      refine ⟨hcont', ?_⟩
      filter_upwards [self_mem_nhdsWithin, hnearL] with s hsIio hs
      rw [localWindowClamp_eq_self m a (by linarith),
        localWindowClamp_eq_self m s hs]
      change (s : ℝ) < (a : ℝ) at hsIio
      exact Set.mem_Iio.mpr hsIio
    obtain ⟨l, hl⟩ := (v m).2.tendsto_nhdsLT aw
    have hpathL : Tendsto g (𝓝[Set.Iio a] a) (𝓝 l) := by
      change Tendsto (fun s => (v m).1 (localWindowClamp m s)) _ _
      exact hl.comp hmapL
    have hnear : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝[Set.Iio a] a,
        (s : ℝ) < (m : ℝ) := by
      have hbase : ∀ᶠ s : Set.Ici (0 : ℝ) in 𝓝 a, (s : ℝ) < (m : ℝ) := by
        filter_upwards [Iio_mem_nhds haM'] with s hs
        change (s : ℝ) < (m : ℝ) at hs
        exact hs
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hbase
    have heq : ∀ᶠ s in 𝓝[Set.Iio a] a,
        localWindowGlueFun v s = g s := by
      filter_upwards [hnear] with s hs
      rw [localWindowGlueFun_eq_coordinate x v hu m s hs]
      simp [localWindowCoordinateAt, g, localWindowClamp_eq_self m s (by linarith)]
    have heq' : ∀ᶠ s in 𝓝[Set.Iio a] a, g s = localWindowGlueFun v s :=
      heq.mono fun s hs => hs.symm
    exact ⟨l, hpathL.congr' heq'⟩




noncomputable def localWindowGlue
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) : CadlagLocal :=
  ⟨localWindowGlueFun v, localWindowGlueFun_isCadlag x v hu⟩




theorem localWindowGlue_coordinates
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) :
    localWindowCoordinates (localWindowGlue x v hu) = v := by
  funext n
  apply Subtype.ext
  funext t
  let ti : Set.Ici (0 : ℝ) := ⟨(t : ℝ), t.property.1⟩
  by_cases hend : (t : ℝ) = (n : ℝ) + 1
  · have htEq : t = ⟨(n : ℝ) + 1, ⟨by positivity, le_rfl⟩⟩ := by
      apply Subtype.ext
      exact hend
    rw [htEq]
    change (cutoffWindow n (localWindowGlue x v hu)).1 _ = _
    rw [cutoffWindow_endpoint]
    exact (localWindowCoordinates_limit_endpoint_zero x v hu n).symm
  · have htlt : (t : ℝ) < (n : ℝ) + 1 :=
      lt_of_le_of_ne t.property.2 hend
    have hglue := localWindowGlueFun_eq_coordinate x v hu (n + 1) ti (by
      push_cast
      exact htlt)
    have hlimit := localWindowCoordinates_limits_satisfy_cutoff
      x v hu n (t : ℝ) t.property.1 t.property.2
    change localWindowGlueFun v ti * localCutoff n ti = (v n).1 t
    rw [hglue]
    have hlimit' : (v n).1 t = localCutoff n ti *
        localWindowCoordinateAt v (n + 1) ti (by push_cast; linarith) := by
      simpa [localWindowCoordinateAt, ti] using hlimit
    simpa [mul_comm] using hlimit'.symm




theorem localWindowCoordinates_limits_realized
    (x : ℕ → CadlagLocal)
    (v : (n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    (hu : Tendsto
      (fun k => weightedJ1ProductDist (localWindowCoordinates (x k)) v)
      atTop (𝓝 0)) :
    ∃ y : CadlagLocal, localWindowCoordinates y = v :=
  ⟨localWindowGlue x v hu, localWindowGlue_coordinates x v hu⟩




theorem localWindowCoordinates_range_isClosed :
    @IsClosed ((n : ℕ) → CadlagWindow ((n : ℝ) + 1))
      weightedJ1ProductMetricSpace.toUniformSpace.toTopologicalSpace
      (Set.range localWindowCoordinates) := by
  rw [← @closure_subset_iff_isClosed
    ((n : ℕ) → CadlagWindow ((n : ℝ) + 1))
    weightedJ1ProductMetricSpace.toUniformSpace.toTopologicalSpace
    (Set.range localWindowCoordinates)]
  intro p hp
  classical
  have happrox (k : ℕ) : ∃ u ∈ Set.range localWindowCoordinates,
      dist p u < 1 / ((k : ℝ) + 1) := by
    apply (@Metric.mem_closure_iff _
      weightedJ1ProductMetricSpace.toPseudoMetricSpace).mp hp
    positivity
  choose u hu hudist using happrox
  have hlim : Tendsto u atTop
      (@nhds ((n : ℕ) → CadlagWindow ((n : ℝ) + 1))
        weightedJ1ProductMetricSpace.toUniformSpace.toTopologicalSpace p) := by
    apply (@Metric.tendsto_nhds _ ℕ
      weightedJ1ProductMetricSpace.toPseudoMetricSpace).mpr
    intro ε hε
    have hev : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε := by
      have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact hzero.eventually (Iio_mem_nhds hε)
    filter_upwards [hev] with k hk
    rw [dist_comm]
    exact lt_trans (hudist k) hk
  let x : ℕ → CadlagLocal := fun k => Classical.choose (hu k)
  have hx (k : ℕ) : localWindowCoordinates (x k) = u k :=
    Classical.choose_spec (hu k)
  have hdist : Tendsto (fun k =>
      weightedJ1ProductDist (localWindowCoordinates (x k)) p)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(@Metric.tendsto_nhds _ ℕ
      weightedJ1ProductMetricSpace.toPseudoMetricSpace).mp hlim ε hε] with k hk
    change weightedJ1ProductDist (u k) p < ε at hk
    have hdk : weightedJ1ProductDist (localWindowCoordinates (x k)) p < ε := by
      simpa only [hx] using hk
    have hnonneg : 0 ≤ weightedJ1ProductDist (localWindowCoordinates (x k)) p :=
      tsum_nonneg (fun i => weightedJ1ProductTerm_nonneg i
        (localWindowCoordinates (x k)) p)
    simpa only [Real.dist_eq, abs_of_nonneg hnonneg, sub_zero] using hdk
  obtain ⟨y, hy⟩ := localWindowCoordinates_limits_realized x p hdist
  exact ⟨y, hy⟩

end DirectedDistances.Probability
