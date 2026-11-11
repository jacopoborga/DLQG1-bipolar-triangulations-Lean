module

public import DirectedDistances.Probability.GeometricCenteredMoments
public import Mathlib.Probability.ProductMeasure

import DirectedDistances.Probability.CenteredSumMoments
import DirectedDistances.Probability.SignAntiConcentration
import Mathlib.Probability.Independence.InfinitePi





public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal




theorem exists_uniform_gap_sum_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, 1 ≤ M →
      c ≤ ((Measure.pi (fun _ : Fin M => geomTwoThirds))
        {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)}).toReal := by
  let μinf : Measure (ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ => geomTwoThirds)
  let Y : ℕ → (ℕ → ℕ) → ℝ := fun i ω => (ω i : ℝ) - 1 / 2
  have hind : iIndepFun Y μinf := by
    exact ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => geomTwoThirds)
      (X := fun _ (n : ℕ) => (n : ℝ) - 1 / 2) (by fun_prop)
  have hmeas : ∀ i, Measurable (Y i) := by
    intro i
    fun_prop
  have hcoord (i : ℕ) :
      IdentDistrib (fun ω : ℕ → ℕ => ω i) (fun ω => ω 0) μinf μinf := by
    refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      ?_⟩
    simp only [μinf, Measure.infinitePi_map_eval]
  have hid : ∀ i, IdentDistrib (Y i) (Y 0) μinf μinf := by
    intro i
    simpa [Y, Function.comp_def] using
      (hcoord i).comp (by fun_prop : Measurable (fun n : ℕ => (n : ℝ) - 1 / 2))
  have hzeroLaw :
      IdentDistrib (fun ω : ℕ → ℕ => ω 0) (fun n : ℕ => n) μinf geomTwoThirds := by
    refine ⟨(measurable_pi_apply 0).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa [μinf] using
      (Measure.infinitePi_map_eval (fun _ : ℕ => geomTwoThirds) 0)
  have hbase :
      IdentDistrib (Y 0) (fun n : ℕ => (n : ℝ) - 1 / 2) μinf geomTwoThirds := by
    simpa [Y, Function.comp_def] using
      hzeroLaw.comp (by fun_prop : Measurable (fun n : ℕ => (n : ℝ) - 1 / 2))
  have hY4 : MemLp (Y 0) 4 μinf :=
    hbase.memLp_iff.mpr memLp_geomTwoThirds_centered_four
  have hYmean : ∫ ω, Y 0 ω ∂μinf = 0 := by
    rw [hbase.integral_eq, integral_geomTwoThirds_centered]
  have hY2 : ∫ ω, (Y 0 ω) ^ 2 ∂μinf = 3 / 4 := by
    have h := (hbase.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))).integral_eq
    simpa [Y, Function.comp_def] using h.trans integral_geomTwoThirds_centered_sq
  have hYfour : ∫ ω, (Y 0 ω) ^ 4 ∂μinf =
      ∫ n, ((n : ℝ) - 1 / 2) ^ 4 ∂geomTwoThirds := by
    have h := (hbase.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 4))).integral_eq
    simpa [Y, Function.comp_def] using h
  let D : ℝ :=
    (∫ n, ((n : ℝ) - 1 / 2) ^ 4 ∂geomTwoThirds) + 3 * (3 / 4 : ℝ) ^ 2
  let c : ℝ := (3 / 4 : ℝ) ^ 2 / (128 * D)
  have hDpos : 0 < D := by
    dsimp [D]
    have hm := integral_geomTwoThirds_centered_four_pos
    positivity
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hcpos, ?_⟩
  intro M hM
  let X := centeredPartialSum Y M
  have hXmem : MemLp X 4 μinf := centeredPartialSum_memLp_four hid hY4 M
  have hXmean : ∫ ω, X ω ∂μinf = 0 :=
    centeredPartialSum_integral_eq_zero hid hY4 hYmean M
  have hsecond := centeredPartialSum_second_moment hind hmeas hid hY4 hYmean M
  have hsecond' : ∫ ω, X ω ^ 2 ∂μinf = (M : ℝ) * (3 / 4 : ℝ) := by
    simpa [X, hY2] using hsecond
  have hfour := centeredPartialSum_fourth_moment hind hmeas hid hY4 hYmean M
  have hfour' : ∫ ω, X ω ^ 4 ∂μinf =
      (M : ℝ) * (∫ n, ((n : ℝ) - 1 / 2) ^ 4 ∂geomTwoThirds) +
        3 * (M : ℝ) * ((M : ℝ) - 1) * (3 / 4 : ℝ) ^ 2 := by
    simpa [X, hY2, hYfour] using hfour
  have hfourPos : 0 < ∫ ω, X ω ^ 4 ∂μinf := by
    rw [hfour']
    have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
    have hbasepos :
        0 < (M : ℝ) * ∫ n, ((n : ℝ) - 1 / 2) ^ 4 ∂geomTwoThirds :=
      mul_pos hMr integral_geomTwoThirds_centered_four_pos
    have hcross :
        0 ≤ 3 * (M : ℝ) * ((M : ℝ) - 1) * (3 / 4 : ℝ) ^ 2 := by
      positivity
    exact add_pos_of_pos_of_nonneg hbasepos hcross
  have hfourLe := centeredPartialSum_fourth_moment_le hind hmeas hid hY4 hYmean hM
  have hfourLe' : ∫ ω, X ω ^ 4 ∂μinf ≤ (M : ℝ) ^ 2 * D := by
    simpa [X, D, hY2, hYfour] using hfourLe
  have hanti := prob_pos_ge_of_fourth_moment hXmem hXmean hfourPos
  have hden : 0 < 128 * ∫ ω, X ω ^ 4 ∂μinf := by positivity
  have hdenBound :
      128 * ∫ ω, X ω ^ 4 ∂μinf ≤ 128 * (M : ℝ) ^ 2 * D := by
    nlinarith [hfourLe']
  have hnumNonneg : 0 ≤ ((M : ℝ) * (3 / 4 : ℝ)) ^ 2 := sq_nonneg _
  have hratio : c ≤
      (∫ ω, X ω ^ 2 ∂μinf) ^ 2 / (128 * ∫ ω, X ω ^ 4 ∂μinf) := by
    rw [hsecond']
    calc
      c = ((M : ℝ) * (3 / 4 : ℝ)) ^ 2 /
          (128 * (M : ℝ) ^ 2 * D) := by
        dsimp [c, D]
        have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        field_simp [ne_of_gt hMpos, ne_of_gt hDpos]
        ring_nf
      _ ≤ ((M : ℝ) * (3 / 4 : ℝ)) ^ 2 /
          (128 * ∫ ω, X ω ^ 4 ∂μinf) :=
        div_le_div_of_nonneg_left hnumNonneg hden hdenBound
  have hprob : c ≤ (μinf {ω | 0 < X ω}).toReal := hratio.trans hanti
  have hlaw :
      μinf.map (fun ω (i : Fin M) => ω i.val) =
        Measure.pi (fun _ : Fin M => geomTwoThirds) := by
    let I : Finset ℕ := Finset.range M
    let e : Fin M ≃ {i : ℕ // i ∈ Finset.range M} :=
      { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
        invFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
        left_inv := fun i => by ext; rfl
        right_inv := fun i => by ext; rfl }
    calc
      μinf.map (fun ω (i : Fin M) => ω i.val) =
          (μinf.map (fun ω => I.restrict ω)).map (fun g i => g (e i)) := by
              rw [Measure.map_map]
              · rfl
              · fun_prop
              · fun_prop
      _ = (Measure.pi (fun _ : {i : ℕ // i ∈ Finset.range M} => geomTwoThirds)).map
            (fun g i => g (e i)) := by
              rw [Measure.infinitePi_map_restrict (μ := fun _ : ℕ => geomTwoThirds)
                (I := I)]
      _ = Measure.pi (fun _ : Fin M => geomTwoThirds) := by
        change (Measure.pi (fun _ : {i : ℕ // i ∈ Finset.range M} => geomTwoThirds)).map
          (MeasurableEquiv.piCongrLeft (fun _ : Fin M => ℕ) e.symm) = _
        exact Measure.pi_map_piCongrLeft e.symm (fun _ : Fin M => geomTwoThirds)
  have hset :
      {ω : ℕ → ℕ | 0 < X ω} =
        (fun ω (i : Fin M) => ω i.val) ⁻¹'
          {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)} := by
    ext ω
    change (0 < X ω) ↔ 0 < ∑ i : Fin M, ((ω i.val : ℝ) - 1 / 2)
    have hsum : X ω = ∑ i : Fin M, ((ω i.val : ℝ) - 1 / 2) := by
      have hsumRange : ∀ n (f : ℕ → ℝ),
          (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, f i.val := by
        intro n
        induction n with
        | zero => intro f; simp
        | succ n ih =>
            intro f
            rw [Finset.sum_range_succ, Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            rw [ih]
      dsimp [X, centeredPartialSum, Y]
      simp only [Finset.sum_apply]
      exact hsumRange M (fun i => (ω i : ℝ) - 1 / 2)
    rw [hsum]
  have hsetMeas : MeasurableSet {g : Fin M → ℕ |
      0 < ∑ i, ((g i : ℝ) - 1 / 2)} := by
    change MeasurableSet ((fun g : Fin M → ℕ =>
      ∑ i : Fin M, ((g i : ℝ) - 1 / 2)) ⁻¹' Set.Ioi 0)
    exact measurableSet_Ioi.preimage (by fun_prop)
  have hprobEq : μinf {ω : ℕ → ℕ | 0 < X ω} =
      (Measure.pi (fun _ : Fin M => geomTwoThirds))
        {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)} := by
    rw [hset, ← Measure.map_apply (by fun_prop) hsetMeas, hlaw]
  change c ≤ ((Measure.pi (fun _ : Fin M => geomTwoThirds))
    {g | 0 < ∑ i, ((g i : ℝ) - 1 / 2)}).toReal
  rw [← hprobEq]
  exact hprob

end DirectedDistances.Probability
