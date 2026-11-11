/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding2
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Signed-angle winding helpers for closed polygons

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology

/-- Helper toward Proposition 5.16: the principal argument of the quotient
from the ray to a point to the ray to the next point, viewed from `z`. -/
@[expose] def edgeAngle (p : Polyline) (z : ℂ) (i : ℕ) : ℝ :=
  Complex.arg ((p.point (i + 1) - z) / (p.point i - z))

/-- Helper toward Proposition 5.16: the sum of principal edge arguments,
normalized by one full turn. -/
@[expose] def angleSum (p : Polyline) (z : ℂ) : ℝ :=
  (∑ i ∈ Finset.range (p.points.length - 1), p.edgeAngle z i) /
    (2 * Real.pi)

/-- Helper toward Proposition 5.16: every in-range edge quotient has its
principal argument strictly between `-pi` and `pi` when `z` avoids the
polyline. -/
theorem edgeAngle_mem_Ioo (p : Polyline) (z : ℂ) (i : ℕ)
    (hi : i + 1 < p.points.length) (hz : z ∉ p.image) :
    p.edgeAngle z i ∈ Set.Ioo (-Real.pi) Real.pi := by
  exact edgeArgument_mem_Ioo p z i hi hz

private theorem prod_range_div_eq (v : ℕ → ℂ) : ∀ n : ℕ,
    v 0 ≠ 0 → (∀ i < n, v i ≠ 0) →
      Finset.prod (Finset.range n) (fun i => v (i + 1) / v i) = v n / v 0 := by
  intro n
  induction n with
  | zero =>
      intro h0 _
      simp [h0]
  | succ n ih =>
      intro h0 hne
      have hne' : ∀ i < n, v i ≠ 0 := fun i hi => hne i (by omega)
      rw [Finset.prod_range_succ, ih h0 hne']
      have hn : v n ≠ 0 := hne n (by omega)
      field_simp [hn, h0]

private theorem exp_sum_range (p : Polyline) (z : ℂ) : ∀ n : ℕ,
    Complex.exp ((∑ i ∈ Finset.range n, p.edgeAngle z i) * Complex.I) =
      ∏ i ∈ Finset.range n, Complex.exp (p.edgeAngle z i * Complex.I) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      simp only [Complex.ofReal_add, add_mul, Complex.exp_add, ih]

/-- Helper toward Proposition 5.16: for a closed polyline, the normalized
principal-angle sum is an integer away from the polyline. -/
theorem angleSum_isInt (p : Polyline) (hclosed : p.start = p.finish)
    (z : ℂ) (hz : z ∉ p.image) : ∃ n : ℤ, p.angleSum z = (n : ℝ) := by
  let N := p.points.length - 1
  let v : ℕ → ℂ := fun i => p.point i - z
  have hpoint_mem (i : ℕ) (hi : i < p.points.length) : p.point i ∈ p.image := by
    by_cases hi0 : i = 0
    · subst i
      have hstart : p.point 0 = p.start := by
        cases hp : p.points with
        | nil => exact (p.nonempty hp).elim
        | cons a l => simp [point, start, hp]
      rw [hstart]
      change p.start ∈ {p.start} ∪ {w : ℂ | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
      exact Or.inl rfl
    · have hi' : i - 1 + 1 = i := by omega
      have hs : i - 1 + 1 < p.points.length := by omega
      change p.point i ∈ {p.start} ∪ {w | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
      right
      refine ⟨i - 1, hs, ?_⟩
      rw [← hi']
      exact right_mem_segment ℝ _ _
  have hv_ne (i : ℕ) (hi : i < p.points.length) : v i ≠ 0 := by
    dsimp [v]
    apply sub_ne_zero.mpr
    intro h
    exact hz (h ▸ hpoint_mem i hi)
  have hNlt : N < p.points.length := by
    have hlen : 0 < p.points.length := List.length_pos_iff_ne_nil.mpr p.nonempty
    dsimp [N]
    omega
  have hstart : p.point 0 = p.start := by
    cases hp : p.points with
    | nil => exact (p.nonempty hp).elim
    | cons a l => simp [point, start, hp]
  have hfinish : p.point N = p.finish := by
    have hget? : p.points[N]? = some (p.points.get ⟨N, hNlt⟩) :=
      List.getElem?_eq_getElem hNlt
    change p.points[N]?.getD p.start = p.points.getLast p.nonempty
    rw [hget?]
    simp only [Option.getD_some]
    have hlast := List.get_length_sub_one (l := p.points) hNlt
    simpa [N] using hlast
  have hv_end : v N = v 0 := by
    dsimp [v]
    rw [hfinish, hstart, hclosed]
  have hqprod :
      Finset.prod (Finset.range N)
        (fun i => (p.point (i + 1) - z) / (p.point i - z)) = 1 := by
    have h0 : v 0 ≠ 0 := hv_ne 0 (by omega)
    have htel := prod_range_div_eq v N h0 (fun i hi => hv_ne i (by omega))
    change Finset.prod (Finset.range N) (fun i => v (i + 1) / v i) = v N / v 0 at htel
    have hratio : v N / v 0 = 1 := by rw [hv_end]; field_simp [h0]
    rw [hratio] at htel
    simpa only [v] using htel
  have hsumexp := exp_sum_range p z N
  have hnormprod :
      (∏ i ∈ Finset.range N,
        ‖(p.point (i + 1) - z) / (p.point i - z)‖) = 1 := by
    rw [← Complex.norm_prod]
    simp [hqprod]
  have hexp_one :
      Complex.exp ((∑ i ∈ Finset.range N, p.edgeAngle z i) * Complex.I) = 1 := by
    rw [hsumexp]
    calc
      (∏ i ∈ Finset.range N, Complex.exp (p.edgeAngle z i * Complex.I)) =
          Finset.prod (Finset.range N) (fun i =>
            ((p.point (i + 1) - z) / (p.point i - z)) /
              ‖(p.point (i + 1) - z) / (p.point i - z)‖) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i + 1 < p.points.length := by
          dsimp [N] at hi
          simp only [Finset.mem_range] at hi
          omega
        let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
        have hq : q ≠ 0 := by
          dsimp [q]
          apply div_ne_zero
          · exact sub_ne_zero.mpr (fun h => hz (h ▸ hpoint_mem (i + 1) (by omega)))
          · exact sub_ne_zero.mpr (fun h => hz (h ▸ hpoint_mem i (by omega)))
        have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
        have ha := Complex.norm_mul_exp_arg_mul_I q
        change Complex.exp (Complex.arg q * Complex.I) = q / ‖q‖
        calc
          Complex.exp (Complex.arg q * Complex.I) =
              (‖q‖ * Complex.exp (Complex.arg q * Complex.I)) / ‖q‖ := by
                field_simp [hn]
          _ = q / ‖q‖ := by rw [ha]
      _ = 1 := by
        rw [Finset.prod_div_distrib, hqprod]
        have hnormcoe :
            Finset.prod (Finset.range N) (fun i =>
              ((‖(p.point (i + 1) - z) / (p.point i - z)‖ : ℝ) : ℂ)) = 1 := by
          norm_cast
        rw [hnormcoe]
        simp
  obtain ⟨m, hm⟩ := (Complex.exp_eq_one_iff).mp hexp_one
  have him := congrArg Complex.im hm
  have hsum : (∑ i ∈ Finset.range N, p.edgeAngle z i) =
      (m : ℝ) * (2 * Real.pi) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using him
  refine ⟨m, ?_⟩
  dsimp [angleSum, N]
  rw [hsum]
  field_simp [Real.pi_ne_zero]

/-- Helper toward Proposition 5.16: the raw edge angle is continuous at every
point outside the polyline. -/
theorem continuousAt_edgeAngle (p : Polyline) (z : ℂ) (i : ℕ)
    (hi : i + 1 < p.points.length) (hz : z ∉ p.image) :
    ContinuousAt (fun w : ℂ => p.edgeAngle w i) z := by
  let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
  have hq : q ≠ 0 := by
    dsimp [q]
    apply div_ne_zero
    · apply sub_ne_zero.mpr
      intro h
      have hp : p.point (i + 1) ∈ p.image := by
        change p.point (i + 1) ∈ {p.start} ∪
          {w : ℂ | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
        exact Or.inr ⟨i, hi, right_mem_segment ℝ _ _⟩
      exact hz (h ▸ hp)
    · apply sub_ne_zero.mpr
      intro h
      have hp : p.point i ∈ p.image := by
        change p.point i ∈ {p.start} ∪
          {w : ℂ | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
        exact Or.inr ⟨i, hi, left_mem_segment ℝ _ _⟩
      exact hz (h ▸ hp)
  have harg := edgeAngle_mem_Ioo p z i hi hz
  have hslit : q ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr ⟨ne_of_lt harg.2, hq⟩
  have hnum : ContinuousAt (fun w : ℂ => p.point (i + 1) - w) z :=
    continuousAt_const.sub continuousAt_id
  have hden : ContinuousAt (fun w : ℂ => p.point i - w) z :=
    continuousAt_const.sub continuousAt_id
  have hden0 : p.point i - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hp : p.point i ∈ p.image := by
      change p.point i ∈ {p.start} ∪
        {w : ℂ | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
      exact Or.inr ⟨i, hi, left_mem_segment ℝ _ _⟩
    exact hz (h ▸ hp)
  have hquot : ContinuousAt
      (fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w)) z :=
    hnum.div hden hden0
  have hcont : ContinuousAt
      (Complex.arg ∘ fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w)) z :=
    ContinuousAt.comp (f := fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w))
      (x := z) (g := Complex.arg) (Complex.continuousAt_arg hslit) hquot
  change ContinuousAt (fun w : ℂ =>
    Complex.arg ((p.point (i + 1) - w) / (p.point i - w))) z
  convert hcont using 1
  ext w
  rfl

/-- Helper toward Proposition 5.16: the normalized angle sum is continuous
at every point outside the polyline. -/
theorem continuousAt_angleSum (p : Polyline) (z : ℂ)
    (hz : z ∉ p.image) : ContinuousAt (fun w : ℂ => p.angleSum w) z := by
  have hsum : ∀ s : Finset ℕ, (∀ i ∈ s, i + 1 < p.points.length) →
      ContinuousAt (fun w : ℂ => ∑ i ∈ s, p.edgeAngle w i) z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa using (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z)
    | @insert i s his ih =>
        intro hbound
        have hi : i + 1 < p.points.length := hbound i (Finset.mem_insert_self i s)
        have hs : ∀ j ∈ s, j + 1 < p.points.length :=
          fun j hj => hbound j (Finset.mem_insert_of_mem hj)
        convert (continuousAt_edgeAngle p z i hi hz).add (ih hs) using 1
        ext w
        simp only [Pi.add_apply, Finset.sum_insert his]
  have htotal : ContinuousAt
      (fun w : ℂ => ∑ i ∈ Finset.range (p.points.length - 1), p.edgeAngle w i) z :=
    hsum _ (by
      intro i hi
      simp only [Finset.mem_range] at hi
      omega)
  simpa [angleSum] using htotal.div_const (2 * Real.pi)

/-- Helper toward Proposition 5.16: the angle sum is locally constant on the
complement of a closed polyline. -/
theorem angleSum_locallyConstant (p : Polyline) (hclosed : p.start = p.finish)
    (z : ℂ) (hz : z ∉ p.image) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ∉ p.image → dist w z < ε →
      p.angleSum w = p.angleSum z := by
  have hc := continuousAt_angleSum p z hz
  have hev : ∀ᶠ w : ℂ in 𝓝 z, dist (p.angleSum w) (p.angleSum z) < 1 := by
    have hball : Metric.ball (p.angleSum z) 1 ∈ 𝓝 (p.angleSum z) :=
      Metric.ball_mem_nhds _ (by norm_num : 0 < (1 : ℝ))
    simpa [Metric.mem_ball] using hc.eventually hball
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro w hw hwd
  obtain ⟨m, hm⟩ := angleSum_isInt p hclosed w hw
  obtain ⟨n, hn⟩ := angleSum_isInt p hclosed z hz
  have hdist : dist (m : ℝ) (n : ℝ) < 1 := by
    simpa [hm, hn] using hnear hwd
  have hdist' : |(m : ℝ) - (n : ℝ)| < 1 := by
    simpa [Real.dist_eq] using hdist
  have hmn : m = n := by
    apply le_antisymm
    · by_contra hnot
      have hlt : n < m := lt_of_not_ge hnot
      have hgapInt : n + 1 ≤ m := by omega
      have hgap : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgapInt
      have hnonneg : 0 ≤ (m : ℝ) - (n : ℝ) := by linarith
      rw [abs_of_nonneg hnonneg] at hdist'
      linarith
    · by_contra hnot
      have hlt : m < n := lt_of_not_ge hnot
      have hgapInt : m + 1 ≤ n := by omega
      have hgap : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgapInt
      have hnonneg : 0 ≤ (n : ℝ) - (m : ℝ) := by linarith
      rw [abs_of_neg (by linarith : (m : ℝ) - (n : ℝ) < 0)] at hdist'
      linarith
  calc
    p.angleSum w = (m : ℝ) := hm
    _ = (n : ℝ) := congrArg Int.cast hmn
    _ = p.angleSum z := hn.symm










































end Polyline
end DirectedDistances.PlanarMap

end
