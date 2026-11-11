module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Helpers toward Lemma 4.11: deterministic dyadic chaining and moment bounds.
The moment hypotheses here are inputs for the code-walk estimates, not premises
added to the manuscript lemma. -/

@[expose] public section

namespace DirectedDistances.Probability

open Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- Helper toward Lemma 4.11: the `k`-th time on the mesh of width `2⁻ʳ`. -/
noncomputable def dyadicTime (r k : ℕ) : ℝ≥0 := ⟨(k : ℝ) / 2 ^ r, by positivity⟩

/-- Helper toward Lemma 4.11: index of the left dyadic approximation. -/
noncomputable def dyadicIndex (r : ℕ) (t : ℝ≥0) : ℕ := ⌊(t : ℝ) * 2 ^ r⌋₊

/-- Helper toward Lemma 4.11: left dyadic approximations converge to their time. -/
theorem tendsto_dyadicTime_index (t : ℝ≥0) :
    Tendsto (fun r => dyadicTime r (dyadicIndex r t)) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  exact (tendsto_nat_floor_mul_div_atTop t.property).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Helper toward Lemma 4.11: successive dyadic indices have the same parent. -/
theorem dyadicIndex_succ_div (r : ℕ) (t : ℝ≥0) :
    dyadicIndex (r + 1) t / 2 = dyadicIndex r t := by
  unfold dyadicIndex
  rw [pow_succ]
  rw [← mul_assoc]
  exact Nat.mul_cast_floor_div_cancel (by decide : 2 ≠ 0) _

/-- Helper toward Lemma 4.11: a dyadic parent is the even-indexed child. -/
theorem dyadicTime_succ_double (r k : ℕ) :
    dyadicTime (r + 1) (2 * k) = dyadicTime r k := by
  apply Subtype.ext
  simp only [dyadicTime, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

/-- Helper toward Lemma 4.11: rounding a time in a bounded window stays
within the corresponding finite dyadic grid. -/
theorem dyadicIndex_le {t : ℝ≥0} (N r : ℕ) (ht : (t : ℝ) ≤ N) :
    dyadicIndex r t ≤ N * 2 ^ r := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_mul_of_nonneg_right ht (by positivity)

/-- Helper toward Lemma 4.11: rounding on consecutive meshes changes the
path by at most one adjacent increment on the finer mesh. -/
theorem dist_dyadic_approx_succ_le {E : Type*} [PseudoMetricSpace E]
    (f : ℝ≥0 → E) (N : ℕ) (b : ℕ → ℝ) (hb : ∀ r, 0 ≤ b r)
    (hgrid : ∀ r k, k < N * 2 ^ r →
      dist (f (dyadicTime r k)) (f (dyadicTime r (k + 1))) ≤ b r)
    (r : ℕ) (t : ℝ≥0) (ht : (t : ℝ) ≤ N) :
    dist (f (dyadicTime r (dyadicIndex r t)))
      (f (dyadicTime (r + 1) (dyadicIndex (r + 1) t))) ≤ b (r + 1) := by
  have hp := dyadicIndex_succ_div r t
  have hm := Nat.mod_add_div (dyadicIndex (r + 1) t) 2
  have hlt := Nat.mod_lt (dyadicIndex (r + 1) t) (by decide : 0 < 2)
  have hcases : dyadicIndex (r + 1) t = 2 * dyadicIndex r t ∨
      dyadicIndex (r + 1) t = 2 * dyadicIndex r t + 1 := by omega
  rcases hcases with h | h
  · rw [h, dyadicTime_succ_double, dist_self]
    exact hb _
  · rw [h, ← dyadicTime_succ_double r (dyadicIndex r t)]
    apply hgrid
    have hle := dyadicIndex_le N (r + 1) ht
    omega

/-- Helper toward Lemma 4.11: the error after rounding down at mesh `r`
is bounded by the sum of adjacent-increment bounds on all finer meshes. -/
theorem dist_dyadic_approx_le_tsum {E : Type*} [PseudoMetricSpace E]
    (f : C(ℝ≥0, E)) (N : ℕ) (b : ℕ → ℝ) (hb : ∀ r, 0 ≤ b r) (hsum : Summable b)
    (hgrid : ∀ r k, k < N * 2 ^ r →
      dist (f (dyadicTime r k)) (f (dyadicTime r (k + 1))) ≤ b r)
    (r : ℕ) (t : ℝ≥0) (ht : (t : ℝ) ≤ N) :
    dist (f (dyadicTime r (dyadicIndex r t))) (f t) ≤ ∑' j, b (r + j + 1) := by
  have hshift : Summable (fun r => b (r + 1)) := hsum.comp_injective
    (fun _ _ h => Nat.add_right_cancel h)
  exact dist_le_tsum_of_dist_le_of_tendsto (fun r => b (r + 1))
    (fun r => dist_dyadic_approx_succ_le f N b hb hgrid r t ht) hshift
    (f.continuous.continuousAt.tendsto.comp (tendsto_dyadicTime_index t)) r

/-- Helper toward Lemma 4.11: times at distance at most one mesh width
have dyadic indices differing by at most one. -/
theorem dyadicIndex_le_add_one (r : ℕ) {s t : ℝ≥0}
    (hst : (t : ℝ) - (s : ℝ) ≤ 1 / 2 ^ r) :
    dyadicIndex r t ≤ dyadicIndex r s + 1 := by
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt (by positivity : 0 ≤ (t : ℝ) * 2 ^ r)).mpr
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  have hh := (le_div_iff₀ hp).mp hst
  have hf := Nat.lt_floor_add_one ((s : ℝ) * 2 ^ r)
  dsimp [dyadicIndex]
  push_cast
  nlinarith only [hh, hf]

/-- Helper toward Lemma 4.11: dyadic chaining controls every increment
inside a bounded window by one coarse increment and two summable fine tails. -/
theorem dist_le_dyadic_chaining {E : Type*} [PseudoMetricSpace E]
    (f : C(ℝ≥0, E)) (N : ℕ) (b : ℕ → ℝ) (hb : ∀ r, 0 ≤ b r) (hsum : Summable b)
    (hgrid : ∀ r k, k < N * 2 ^ r →
      dist (f (dyadicTime r k)) (f (dyadicTime r (k + 1))) ≤ b r)
    (r : ℕ) (s t : ℝ≥0) (hs : (s : ℝ) ≤ N) (ht : (t : ℝ) ≤ N)
    (hst : dist s t ≤ 1 / 2 ^ r) :
    dist (f s) (f t) ≤ b r + 2 * ∑' j, b (r + j + 1) := by
  have ordered (s t : ℝ≥0) (hs : (s : ℝ) ≤ N) (ht : (t : ℝ) ≤ N)
      (hle : s ≤ t) (hst : dist s t ≤ 1 / 2 ^ r) :
      dist (f s) (f t) ≤ b r + 2 * ∑' j, b (r + j + 1) := by
    have hi : dyadicIndex r s ≤ dyadicIndex r t :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right hle (by positivity))
    have hd : (t : ℝ) - (s : ℝ) ≤ 1 / 2 ^ r := by
      simpa only [NNReal.dist_eq, abs_of_nonpos
        (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hle)), neg_sub] using hst
    have hj := dyadicIndex_le_add_one r hd
    have hcoarse : dist (f (dyadicTime r (dyadicIndex r s)))
        (f (dyadicTime r (dyadicIndex r t))) ≤ b r := by
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · rw [heq, dist_self]
        exact hb r
      · have heq : dyadicIndex r t = dyadicIndex r s + 1 := by omega
        rw [heq]
        apply hgrid
        have htop := dyadicIndex_le N r ht
        omega
    have hleft := dist_dyadic_approx_le_tsum f N b hb hsum hgrid r s hs
    have hright := dist_dyadic_approx_le_tsum f N b hb hsum hgrid r t ht
    have htri := dist_triangle4 (f s) (f (dyadicTime r (dyadicIndex r s)))
      (f (dyadicTime r (dyadicIndex r t))) (f t)
    rw [dist_comm] at hleft
    linarith only [htri, hleft, hright, hcoarse]
  rcases le_total s t with h | h
  · exact ordered s t hs ht h hst
  · rw [dist_comm]
    exact ordered t s ht hs h (by rwa [dist_comm])

/-- Helper toward Lemma 4.11: the distance between adjacent mesh times. -/
theorem dist_dyadicTime_succ (r k : ℕ) :
    dist (dyadicTime r k) (dyadicTime r (k + 1)) = 1 / 2 ^ r := by
  rw [NNReal.dist_eq]
  have h : (dyadicTime r k : ℝ) - (dyadicTime r (k + 1) : ℝ) = -(1 / 2 ^ r) := by
    change (k : ℝ) / 2 ^ r - ((k + 1 : ℕ) : ℝ) / 2 ^ r = _
    push_cast
    ring
  rw [h, abs_neg, abs_of_nonneg (by positivity)]

/-- Helper toward Lemma 4.11: fourth-moment Markov inequality, with an
integrability input and the outer measure of the norm-tail event. -/
theorem measure_dist_ge_le_fourth_moment {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y Z : Ω → E) {a M : ℝ} (ha : 0 < a)
    (hint : Integrable (fun ω => dist (Y ω) (Z ω) ^ 4) μ)
    (hmom : (∫ ω, dist (Y ω) (Z ω) ^ 4 ∂μ) ≤ M) :
    μ {ω | a ≤ dist (Y ω) (Z ω)} ≤ ENNReal.ofReal (M / a ^ 4) := by
  have hsub : {ω | a ≤ dist (Y ω) (Z ω)} ⊆
      {ω | a ^ 4 ≤ dist (Y ω) (Z ω) ^ 4} := by
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω 4
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity) hint (a ^ 4)
  have hreal : μ.real {ω | a ≤ dist (Y ω) (Z ω)} ≤ M / a ^ 4 := by
    apply (le_div_iff₀ (pow_pos ha 4)).mpr
    calc
      _ ≤ μ.real {ω | a ^ 4 ≤ dist (Y ω) (Z ω) ^ 4} * a ^ 4 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) (by positivity)
      _ ≤ (∫ ω, dist (Y ω) (Z ω) ^ 4 ∂μ) := by simpa only [mul_comm] using hm
      _ ≤ M := hmom
  rw [← ofReal_measureReal (μ := μ) (s := {ω | a ≤ dist (Y ω) (Z ω)})]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Helper toward Lemma 4.11: the bad event that some dyadic increment
exceeds a prescribed, scale-dependent threshold on the window `[0,N]`. -/
def dyadicBadEvent {Ω E : Type*} [PseudoMetricSpace E]
    (X : Ω → C(ℝ≥0, E)) (N : ℕ) (b : ℕ → ℝ) : Set Ω :=
  ⋃ r : ℕ, ⋃ k ∈ Finset.range (N * 2 ^ r),
    {ω | b r ≤ dist (X ω (dyadicTime r k)) (X ω (dyadicTime r (k + 1)))}

/-- Helper toward Lemma 4.11: fourth moments control the probability of
any exceptional dyadic increment, uniformly over all scales. -/
theorem measure_dyadicBadEvent_le {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → C(ℝ≥0, E)) (N : ℕ) (b : ℕ → ℝ) (hb : ∀ r, 0 < b r)
    (C : ℝ)
    (hint : ∀ s t, Integrable (fun ω => dist (X ω s) (X ω t) ^ 4) μ)
    (hmom : ∀ s t, (∫ ω, dist (X ω s) (X ω t) ^ 4 ∂μ) ≤ C * dist s t ^ 2) :
    μ (dyadicBadEvent X N b) ≤
      ∑' r : ℕ, (N * 2 ^ r : ℕ) * ENNReal.ofReal (C * (1 / 2 ^ r) ^ 2 / b r ^ 4) := by
  apply (measure_iUnion_le _).trans
  apply tsum_le_tsum
  intro r
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (N * 2 ^ r),
        ENNReal.ofReal (C * (1 / 2 ^ r) ^ 2 / b r ^ 4) := by
      apply Finset.sum_le_sum
      intro k hk
      apply measure_dist_ge_le_fourth_moment μ _ _ (hb r) (hint _ _)
      simpa only [dist_dyadicTime_succ] using hmom (dyadicTime r k) (dyadicTime r (k + 1))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Helper toward Lemma 4.11: outside the exceptional dyadic event,
the full continuous path has the modulus furnished by dyadic chaining. -/
theorem measure_modulus_ge_le_dyadicBadEvent {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) (X : Ω → C(ℝ≥0, E))
    (N : ℕ) (b : ℕ → ℝ) (hb : ∀ r, 0 ≤ b r) (hsum : Summable b)
    (r : ℕ) (ε : ℝ) (hε : b r + 2 * ∑' j, b (r + j + 1) < ε) :
    μ {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ N ∧ (t : ℝ) ≤ N ∧
      dist s t ≤ 1 / 2 ^ r ∧ ε ≤ dist (X ω s) (X ω t)} ≤ μ (dyadicBadEvent X N b) := by
  apply measure_mono
  rintro ω ⟨s, t, hs, ht, hst, hlarge⟩
  by_contra hbad
  have hgrid : ∀ r k, k < N * 2 ^ r →
      dist (X ω (dyadicTime r k)) (X ω (dyadicTime r (k + 1))) ≤ b r := by
    intro r k hk
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hbad (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨k,
      Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, h⟩⟩⟩)
  exact (not_le_of_gt ((dist_le_dyadic_chaining (X ω) N b hb hsum hgrid r s t hs ht hst).trans_lt hε)) hlarge

/-- Helper toward Lemma 4.11: geometric adjacent-increment bounds yield
an explicit modulus on each dyadic scale. -/
theorem dyadic_chaining_geometric (A : ℝ) (r : ℕ) :
    A * (7 / 8 : ℝ) ^ r + 2 * (∑' j : ℕ, A * (7 / 8 : ℝ) ^ (r + j + 1)) =
      15 * A * (7 / 8 : ℝ) ^ r := by
  have hsum : (∑' j : ℕ, A * (7 / 8 : ℝ) ^ (r + j + 1)) =
      (A * (7 / 8 : ℝ) ^ r * (7 / 8)) * (∑' j : ℕ, (7 / 8 : ℝ) ^ j) := by
    rw [← tsum_mul_left]
    congr 1
    funext j
    rw [pow_add, pow_add, pow_one]
    ring
  rw [hsum, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
    (by norm_num : (7 / 8 : ℝ) < 1)]
  norm_num
  ring

private theorem geometric_grid_algebra (N r : ℕ) (C A : ℝ) (hA : 0 < A) :
    (N * 2 ^ r : ℕ) *
        ENNReal.ofReal (C * (1 / 2 ^ r) ^ 2 / (A * (7 / 8 : ℝ) ^ r) ^ 4) =
      ENNReal.ofReal ((N : ℝ) * C / A ^ 4 * (2048 / 2401 : ℝ) ^ r) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  have heq : (2048 / 2401 : ℝ) = 1 / (2 * (7 / 8 : ℝ) ^ 4) := by norm_num
  have hcomm : ((7 / 8 : ℝ) ^ 4) ^ r = ((7 / 8 : ℝ) ^ r) ^ 4 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hh : (1 / (2 * (7 / 8 : ℝ) ^ 4)) ^ r =
      1 / ((2 : ℝ) ^ r * ((7 / 8 : ℝ) ^ r) ^ 4) := by
    rw [div_pow, one_pow, mul_pow, hcomm]
  rw [heq, hh]
  field_simp

/-- Helper toward Lemma 4.11: summing fourth-moment Markov bounds over
all dyadic scales gives a probability bound decaying as the fourth power
of the reciprocal Hölder constant. -/
theorem measure_dyadicBadEvent_geometric_le {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → C(ℝ≥0, E)) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ s t, Integrable (fun ω => dist (X ω s) (X ω t) ^ 4) μ)
    (hmom : ∀ s t, (∫ ω, dist (X ω s) (X ω t) ^ 4 ∂μ) ≤ C * dist s t ^ 2)
    (A : ℝ) (hA : 0 < A) :
    μ (dyadicBadEvent X N (fun r => A * (7 / 8 : ℝ) ^ r)) ≤
      ENNReal.ofReal ((N : ℝ) * C / A ^ 4 * (1 - (2048 / 2401 : ℝ))⁻¹) := by
  apply (measure_dyadicBadEvent_le μ X N _ (fun r => by positivity) C hint hmom).trans
  simp_rw [geometric_grid_algebra N _ C A hA]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2048 / 2401)
      (by norm_num : (2048 / 2401 : ℝ) < 1)).mul_left ((N : ℝ) * C / A ^ 4))]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2048 / 2401)
    (by norm_num : (2048 / 2401 : ℝ) < 1)]

/-- Helper toward Lemma 4.11: an explicit modulus tail bound derived only
from a uniform fourth increment moment bound and continuous paths. -/
theorem measure_modulus_ge_le_of_fourth_moment {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → C(ℝ≥0, E)) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ s t, Integrable (fun ω => dist (X ω s) (X ω t) ^ 4) μ)
    (hmom : ∀ s t, (∫ ω, dist (X ω s) (X ω t) ^ 4 ∂μ) ≤ C * dist s t ^ 2)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ N ∧ (t : ℝ) ≤ N ∧
      dist s t ≤ 1 / 2 ^ r ∧ ε ≤ dist (X ω s) (X ω t)} ≤
      ENNReal.ofReal ((N : ℝ) * C / (ε / (30 * (7 / 8 : ℝ) ^ r)) ^ 4 *
        (1 - (2048 / 2401 : ℝ))⁻¹) := by
  let A : ℝ := ε / (30 * (7 / 8 : ℝ) ^ r)
  have hA : 0 < A := by positivity
  apply (measure_modulus_ge_le_dyadicBadEvent μ X N (fun j => A * (7 / 8 : ℝ) ^ j)
    (fun j => by positivity)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
      (by norm_num : (7 / 8 : ℝ) < 1)).mul_left A) r ε ?_).trans
  · exact measure_dyadicBadEvent_geometric_le μ X N C hC hint hmom A hA
  · rw [dyadic_chaining_geometric]
    dsimp [A]
    have hq : (7 / 8 : ℝ) ^ r ≠ 0 := by positivity
    field_simp
    linarith only [hε]

private theorem modulus_bound_algebra (N r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    (N : ℝ) * C / (ε / (30 * (7 / 8 : ℝ) ^ r)) ^ 4 *
        (1 - (2048 / 2401 : ℝ))⁻¹ =
      ((N : ℝ) * C * 30 ^ 4 / ε ^ 4 * (1 - (2048 / 2401 : ℝ))⁻¹) *
        ((7 / 8 : ℝ) ^ 4) ^ r := by
  rw [show ((7 / 8 : ℝ) ^ 4) ^ r = ((7 / 8 : ℝ) ^ r) ^ 4 by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  field_simp

/-- Helper toward Lemma 4.11: the explicit fourth-moment modulus bound
tends to zero as the dyadic mesh tends to zero, for each positive tolerance. -/
theorem tendsto_fourth_moment_modulus_bound (N : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun r : ℕ =>
      ENNReal.ofReal ((N : ℝ) * C / (ε / (30 * (7 / 8 : ℝ) ^ r)) ^ 4 *
        (1 - (2048 / 2401 : ℝ))⁻¹)) atTop (𝓝 0) := by
  simp_rw [modulus_bound_algebra N _ C ε hε]
  have hpow : Tendsto (fun r : ℕ => ((7 / 8 : ℝ) ^ 4) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hreal := hpow.const_mul
    ((N : ℝ) * C * 30 ^ 4 / ε ^ 4 * (1 - (2048 / 2401 : ℝ))⁻¹)
  simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- Helper toward Lemma 4.11: a family with one common fourth-moment
constant has uniformly small modulus tails on every bounded time window. -/
theorem uniform_modulus_of_fourth_moment {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → C(ℝ≥0, E)) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n s t, Integrable (fun ω => dist (X n ω s) (X n ω t) ^ 4) μ)
    (hmom : ∀ n s t, (∫ ω, dist (X n ω s) (X n ω t) ^ 4 ∂μ) ≤ C * dist s t ^ 2)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
      μ {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ N ∧ (t : ℝ) ≤ N ∧
        dist s t ≤ δ ∧ ε ≤ dist (X n ω s) (X n ω t)} ≤ η := by
  have hevent := (tendsto_fourth_moment_modulus_bound N C ε hε).eventually
    (gt_mem_nhds hη)
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨1 / 2 ^ r, by positivity, fun n => ?_⟩
  exact (measure_modulus_ge_le_of_fourth_moment μ (X n) N C hC
    (hint n) (hmom n) r ε hε).trans (hr r le_rfl).le

/-- Helper toward Lemma 4.11: the ordered, norm-valued fourth-moment
hypothesis supplies the symmetric metric version used in the modulus proof. -/
theorem dist_fourth_moment_le_of_norm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (X : Ω → C(ℝ≥0, E)) (C : ℝ)
    (hmom : ∀ s t : ℝ≥0, s ≤ t →
      (∫ ω, ‖X ω t - X ω s‖ ^ 4 ∂μ) ≤ C * ((t : ℝ) - (s : ℝ)) ^ 2)
    (s t : ℝ≥0) :
    (∫ ω, dist (X ω s) (X ω t) ^ 4 ∂μ) ≤ C * dist s t ^ 2 := by
  rcases le_total s t with h | h
  · have hm := hmom s t h
    simpa only [dist_eq_norm', NNReal.dist_eq, sq_abs, sub_sq_comm] using hm
  · have hm := hmom t s h
    simpa only [dist_eq_norm, NNReal.dist_eq, sq_abs] using hm

/-- Helper toward Lemma 4.11: the usual fourth norm-moment hypothesis,
with one constant for the whole family and only ordered time pairs, yields
uniform smallness of continuous-path modulus tails. -/
theorem uniform_modulus_of_norm_fourth_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → C(ℝ≥0, E)) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n (s t : ℝ≥0), Integrable (fun ω => ‖X n ω t - X n ω s‖ ^ 4) μ)
    (hmom : ∀ n (s t : ℝ≥0), s ≤ t →
      (∫ ω, ‖X n ω t - X n ω s‖ ^ 4 ∂μ) ≤ C * ((t : ℝ) - (s : ℝ)) ^ 2)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
      μ {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ N ∧ (t : ℝ) ≤ N ∧
        dist s t ≤ δ ∧ ε ≤ ‖X n ω t - X n ω s‖} ≤ η := by
  have hi : ∀ n s t, Integrable (fun ω => dist (X n ω s) (X n ω t) ^ 4) μ := by
    intro n s t
    simpa only [dist_eq_norm'] using hint n s t
  simpa only [dist_eq_norm'] using uniform_modulus_of_fourth_moment μ X N C hC hi
    (fun n => dist_fourth_moment_le_of_norm μ (X n) C (hmom n)) ε hε η hη

/- Remaining target C (not a declaration, premise, or completion claim):

For every type Ω with a measurable space, every real normed additive group E
with a real normed-space structure and FiniteDimensional ℝ E, every probability
measure μ on Ω, every X : ℕ → Ω → C(ℝ≥0, E), every C : ℝ with 0 ≤ C, and
every T : ℝ≥0, put K := Set.Icc (0 : ℝ≥0) T and
R n ω := (X n ω).comp ⟨Subtype.val, continuous_subtype_val⟩ : C(K, E).
Equip C(K, E) with its Borel measurable space. Assume
  (1) ∀ n, Measurable (R n),
  (2) ∀ n ω, X n ω 0 = 0,
  (3) ∀ n (s t : ℝ≥0),
        Integrable (fun ω => ‖X n ω t - X n ω s‖ ^ 4) μ,
  (4) ∀ n (s t : ℝ≥0), s ≤ t →
        (∫ ω, ‖X n ω t - X n ω s‖ ^ 4 ∂μ) ≤ C * ((t : ℝ) - (s : ℝ)) ^ 2.
Prove IsTightMeasureSet (Set.range (fun n => Measure.map (R n) μ)).

Inspected routes: IsKolmogorovProcess only packages moment assumptions; it
does not export Kolmogorov-Chentsov. The direct chaining/Markov route above
closes A and B. For C, inspected BoundedContinuousFunction.arzela_ascoli and
ArzelaAscoli.isCompact_closure_of_isClosedEmbedding, followed by
isTightMeasureSet_iff_exists_isCompact_measure_compl_le. Both relevant Ascoli
compiled imports are absent:
  Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.olean
  Mathlib/Topology/UniformSpace/Ascoli.olean
No dependency compilation or retrieval was attempted. Compact containment
in C(K,E), using zero start and finite-dimensional compact value balls, remains -/

end DirectedDistances.Probability
