module

public import DirectedDistances.PlanarMap.PlaneRealization
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith






public section
namespace DirectedDistances.PlanarMap

noncomputable section





theorem open_graphs_disjoint_of_ne {φ ψ : ℝ → ℝ} {a b c d : ℝ}
    (_hab : a < b) (_hcd : c < d)
    (hne : ∀ x, max a c < x → x < min b d → φ x ≠ ψ x) :
    Disjoint {z : ℂ | a < z.re ∧ z.re < b ∧ z.im = φ z.re}
      {z : ℂ | c < z.re ∧ z.re < d ∧ z.im = ψ z.re} := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hxlo : max a c < z.re := max_lt_iff.mpr ⟨hz₁.1, hz₂.1⟩
  have hxhi : z.re < min b d := lt_min_iff.mpr ⟨hz₁.2.1, hz₂.2.1⟩
  exact hne z.re hxlo hxhi (hz₁.2.2.symm.trans hz₂.2.2)





theorem closed_graphs_disjoint_of_ne {φ ψ : ℝ → ℝ} {a b c d : ℝ}
    (_hcommon : max a c < min b d)
    (hne : ∀ x, max a c < x → x < min b d → φ x ≠ ψ x) :
    Disjoint
      {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ z.im = φ z.re ∧
        z.re ≠ max a c ∧ z.re ≠ min b d}
      {z : ℂ | c ≤ z.re ∧ z.re ≤ d ∧ z.im = ψ z.re ∧
        z.re ≠ max a c ∧ z.re ≠ min b d} := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hxlo : max a c < z.re := lt_of_le_of_ne
    (max_le_iff.mpr ⟨hz₁.1, hz₂.1⟩) (Ne.symm hz₁.2.2.2.1)
  have hxhi : z.re < min b d := lt_of_le_of_ne
    (le_min_iff.mpr ⟨hz₁.2.1, hz₂.2.1⟩) hz₁.2.2.2.2
  exact hne z.re hxlo hxhi (hz₁.2.2.1.symm.trans hz₂.2.2.1)

namespace Polyline



@[expose] def XMonotone (p : Polyline) : Prop :=
  List.Pairwise (fun z w => z.re < w.re) p.points



@[expose] def heightFn (p : Polyline) (x : ℝ) : ℝ :=
  p.start.im + ∑ i ∈ Finset.range (p.points.length - 1),
    (((p.point (i + 1)).im - (p.point i).im) /
      (if (p.point (i + 1)).re = (p.point i).re then 1
        else (p.point (i + 1)).re - (p.point i).re)) *
      max 0 (min ((p.point (i + 1)).re - (p.point i).re)
        (x - (p.point i).re))



theorem continuous_heightFn (p : Polyline) : Continuous p.heightFn := by
  unfold Polyline.heightFn
  refine continuous_const.add (continuous_finsetSum _ ?_)
  intro i hi
  exact continuous_const.mul (continuous_const.max
    (continuous_const.min
      (continuous_id.sub continuous_const)))




theorem point_re_lt {p : Polyline} (hp : p.XMonotone) {i j : ℕ}
    (hij : i < j) (hj : j < p.points.length) :
    (p.point i).re < (p.point j).re := by
  have hi : i < p.points.length := Nat.lt_trans hij hj
  have h := List.Pairwise.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hp (Fin.mk_lt_mk.mpr hij)
  change (p.points.getD i p.start).re < (p.points.getD j p.start).re
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]
  exact h



theorem point_re_le_of_le {p : Polyline} (hp : p.XMonotone) {i j : ℕ}
    (hij : i ≤ j) (hj : j < p.points.length) :
    (p.point i).re ≤ (p.point j).re := by
  rcases eq_or_lt_of_le hij with h | h
  · subst j
    exact le_rfl
  · exact (point_re_lt (p := p) hp h hj).le



theorem heightFn_point {p : Polyline} (hp : p.XMonotone) {k : ℕ}
    (hk : k < p.points.length) :
    p.heightFn (p.point k).re = (p.point k).im := by
  let n := p.points.length - 1
  let x : ℕ → ℝ := fun j => (p.point j).re
  let y : ℕ → ℝ := fun j => (p.point j).im
  let F : ℕ → ℝ := fun j =>
    if j ≤ k then y j else y k
  have hkn : k ≤ n := by dsimp [n]; omega
  have hFn : F n = y k := by
    change (if n ≤ k then y n else y k) = y k
    by_cases h : n ≤ k
    · have heq : n = k := Nat.le_antisymm h hkn
      simp [heq]
    · simp [h]
  have hp0 : p.point 0 = p.start := by
    cases h : p.points with
    | nil => exact (p.nonempty h).elim
    | cons a l => simp [Polyline.point, Polyline.start, h]
  have hF0 : F 0 = p.start.im := by
    simp [F, y, hp0]
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
      ((y (i + 1) - y i) / (if x (i + 1) = x i then 1 else x (i + 1) - x i)) *
        max 0 (min (x (i + 1) - x i) (x k - x i)) = F (i + 1) - F i := by
    have hin : i < n := Finset.mem_range.mp hi
    have hi₁ : i + 1 < p.points.length := by dsimp [n] at hin; omega
    have hi_lt : i < p.points.length := Nat.lt_trans (Nat.lt_succ_self i) hi₁
    have hdx : x i < x (i + 1) := by
      change (p.point i).re < (p.point (i + 1)).re
      exact point_re_lt (p := p) hp (Nat.lt_succ_self i) hi₁
    have hdelta : 0 < x (i + 1) - x i := sub_pos.mpr hdx
    by_cases hik : i < k
    · have hik₁ : i + 1 ≤ k := by omega
      have hxn : x (i + 1) ≤ x k := by
        apply point_re_le_of_le (p := p) hp hik₁ hk
      have hclamp : max 0 (min (x (i + 1) - x i) (x k - x i)) =
          x (i + 1) - x i := by
        rw [min_eq_left (by linarith)]
        exact max_eq_right hdelta.le
      have hneq : x (i + 1) ≠ x i := ne_of_gt hdx
      rw [ite_eq_right hneq, hclamp]
      rw [div_mul_cancel₀ _ hdelta.ne']
      simp [F, le_of_lt hik, hik₁]
    · have hki : k ≤ i := Nat.le_of_not_gt hik
      have hxk : x k ≤ x i := by
        apply point_re_le_of_le (p := p) hp hki hi_lt
      have hclamp : max 0 (min (x (i + 1) - x i) (x k - x i)) = 0 := by
        rw [max_eq_left (le_trans (min_le_right _ _) (by linarith))]
      rw [hclamp]
      by_cases heq : i = k
      · subst i
        simp [F]
      · have hki' : k < i := lt_of_le_of_ne hki (Ne.symm heq)
        have hki1' : k < i + 1 := by omega
        simp [F, not_le_of_gt hki', not_le_of_gt hki1']
  unfold Polyline.heightFn
  change p.start.im + ∑ i ∈ Finset.range n,
      ((y (i + 1) - y i) / (if x (i + 1) = x i then 1 else x (i + 1) - x i)) *
        max 0 (min (x (i + 1) - x i) (x k - x i)) = y k
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub, hFn, hF0]
  rw [← hp0]
  ring



theorem point_zero_eq_start (p : Polyline) : p.point 0 = p.start := by
  cases h : p.points with
  | nil => exact (p.nonempty h).elim
  | cons a l => simp [Polyline.point, Polyline.start, h]



theorem initialDirection_re_pos {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : 0 < p.initialDirection.re := by
  have h := point_re_lt (p := p) hp (i := 0) (j := 1) (by decide)
    (lt_of_lt_of_le (by decide : 1 < 2) hlen)
  rw [Polyline.initialDirection, ← p.point_zero_eq_start, Complex.sub_re]
  exact sub_pos.mpr h




theorem point_last_eq_finish (p : Polyline) :
    p.point (p.points.length - 1) = p.finish := by
  cases h : p.points with
  | nil => exact (p.nonempty h).elim
  | cons a l => simp [Polyline.point, Polyline.finish, List.getLast_eq_getElem, h]



theorem reverse_point_one (p : Polyline) (hlen : 2 ≤ p.points.length) :
    p.reverse.point 1 = p.point (p.points.length - 2) := by
  have hidx : p.points.length - 1 - 1 = p.points.length - 2 := by
    omega
  have hi : p.points.length - 2 < p.points.length := by
    omega
  change p.points.reverse.getD 1 p.reverse.start = p.points.getD (p.points.length - 2) p.start
  rw [Polyline.start_reverse]
  rw [List.getD_reverse (l := p.points) 1 (lt_of_lt_of_le (by decide : 1 < 2) hlen), hidx]
  rw [List.getD_eq_getElem (l := p.points) (d := p.finish) hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hi]



theorem reverse_initialDirection_re_neg {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :  p.reverse.initialDirection.re < 0 := by
  have h := point_re_lt (p := p) hp (i := p.points.length - 2)
    (j := p.points.length - 1) (by omega) (by omega)
  rw [Polyline.initialDirection, Polyline.start_reverse, p.reverse_point_one hlen,
    ← p.point_last_eq_finish, Complex.sub_re]
  exact sub_neg.mpr h



theorem initialDirection_ne_zero {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.initialDirection ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  rw [Complex.zero_re] at hRe
  exact (not_lt_of_ge (le_of_eq hRe)) (initialDirection_re_pos hp hlen)




theorem segment_re_bounds {a b z : ℂ} (hab : a.re ≤ b.re)
    (hz : z ∈ segment ℝ a b) : a.re ≤ z.re ∧ z.re ≤ b.re := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hre : (((1 - t) • a + t • b : ℂ).re) = (1 - t) * a.re + t * b.re := by
    simp [Complex.real_smul]
  constructor <;> rw [hre] <;> nlinarith [ht.1, ht.2]



theorem mem_segment_eq_right {a b z : ℂ} (hab : a.re < b.re)
    (hz : z ∈ segment ℝ a b) (hx : z.re = b.re) : z = b := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hre : (((1 - t) • a + t • b : ℂ).re) = (1 - t) * a.re + t * b.re := by
    simp [Complex.real_smul]
  have ht1 : t = 1 := by
    rw [hre] at hx
    nlinarith [ht.1, ht.2, hab]
  subst t
  simp



theorem mem_segment_eq_left {a b z : ℂ} (hab : a.re < b.re)
    (hz : z ∈ segment ℝ a b) (hx : z.re = a.re) : z = a := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hre : (((1 - t) • a + t • b : ℂ).re) = (1 - t) * a.re + t * b.re := by
    simp [Complex.real_smul]
  have ht0 : t = 0 := by
    rw [hre] at hx
    nlinarith [ht.1, ht.2, hab]
  subst t
  simp



theorem segmentAt_re_bounds {p : Polyline} (hp : p.XMonotone) {i : ℕ}
    (hi : i + 1 < p.points.length) {z : ℂ} (hz : z ∈ p.segmentAt i) :
    (p.point i).re ≤ z.re ∧ z.re ≤ (p.point (i + 1)).re := by
  have hab : (p.point i).re < (p.point (i + 1)).re :=
    point_re_lt (p := p) hp (Nat.lt_succ_self i) hi
  exact segment_re_bounds hab.le (by simpa [Polyline.segmentAt] using hz)



theorem isSimple_of_XMonotone {p : Polyline} (hp : p.XMonotone)
    (_hlen : 2 ≤ p.points.length) : p.IsSimple := by
  constructor
  · intro i hi heq
    have hxy : (p.point i).re < (p.point (i + 1)).re :=
      point_re_lt (p := p) hp (Nat.lt_succ_self i) hi
    exact (ne_of_lt hxy) (congrArg Complex.re heq)
  constructor
  · intro i hi
    have hi₁ : i + 1 < p.points.length := by omega
    have hi₂ : i + 2 < p.points.length := hi
    have h₁ : (p.point i).re < (p.point (i + 1)).re :=
      point_re_lt (p := p) hp (Nat.lt_succ_self i) hi₁
    have h₂ : (p.point (i + 1)).re < (p.point (i + 2)).re :=
      point_re_lt (p := p) hp (Nat.lt_succ_self (i + 1)) hi₂
    apply Set.ext
    intro z
    constructor
    · rintro ⟨hz₁, hz₂⟩
      have hb₁ := segmentAt_re_bounds (p := p) hp hi₁ hz₁
      have hb₂ := segmentAt_re_bounds (p := p) hp hi₂ hz₂
      have hx : z.re = (p.point (i + 1)).re := le_antisymm hb₁.2 hb₂.1
      exact mem_segment_eq_right h₁ (by simpa [Polyline.segmentAt] using hz₁) hx
    · intro hz
      subst z
      constructor
      · change p.point (i + 1) ∈ segment ℝ (p.point i) (p.point (i + 1))
        exact right_mem_segment ℝ _ _
      · change p.point (i + 1) ∈ segment ℝ (p.point (i + 1)) (p.point (i + 2))
        exact left_mem_segment ℝ _ _
  · intro i j hi hj hij
    apply Set.disjoint_left.mpr
    intro z hzᵢ hzⱼ
    have hi₁ : i + 1 < p.points.length := by omega
    have hj₁ : j + 1 < p.points.length := hj
    have hsep : (p.point (i + 1)).re < (p.point j).re :=
      point_re_lt (p := p) hp hij (by omega)
    have hbᵢ := segmentAt_re_bounds (p := p) hp hi₁ hzᵢ
    have hbⱼ := segmentAt_re_bounds (p := p) hp hj₁ hzⱼ
    exact (not_le_of_gt hsep) (le_trans hbⱼ.1 hbᵢ.2)




theorem heightFn_linear_on_segment {p : Polyline} (hp : p.XMonotone)
    {i : ℕ} (hi : i + 1 < p.points.length) {xval : ℝ}
    (hleft : (p.point i).re ≤ xval)
    (hright : xval ≤ (p.point (i + 1)).re) :
    p.heightFn xval = (p.point i).im +
      (((p.point (i + 1)).im - (p.point i).im) /
        ((p.point (i + 1)).re - (p.point i).re)) *
        (xval - (p.point i).re) := by
  let n := p.points.length - 1
  let x : ℕ → ℝ := fun j => (p.point j).re
  let y : ℕ → ℝ := fun j => (p.point j).im
  let F : ℕ → ℝ := fun j => if j ≤ i then y j else y i
  let q := ((y (i + 1) - y i) / (x (i + 1) - x i)) * (xval - x i)
  have hin : i < n := by dsimp [n]; omega
  have hkn : i ≤ n := hin.le
  have hp0 : p.point 0 = p.start := p.point_zero_eq_start
  have hFn : F n = y i := by
    dsimp [F]
    by_cases h : n ≤ i
    · have heq : n = i := Nat.le_antisymm h hkn
      simp [heq]
    · simp [h]
  have hF0 : F 0 = p.start.im := by simp [F, y, hp0]
  have hdx : x i < x (i + 1) := by
    change (p.point i).re < (p.point (i + 1)).re
    exact point_re_lt (p := p) hp (Nat.lt_succ_self i) hi
  have hdelta : 0 < x (i + 1) - x i := sub_pos.mpr hdx
  have hidx : i ∈ Finset.range n := Finset.mem_range.mpr hin
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ((y (j + 1) - y j) /
        (if x (j + 1) = x j then 1 else x (j + 1) - x j)) *
        max 0 (min (x (j + 1) - x j) (xval - x j)) =
      F (j + 1) - F j + (if j = i then q else 0) := by
    have hjn : j < n := Finset.mem_range.mp hj
    have hj₁ : j + 1 < p.points.length := by dsimp [n] at hjn; omega
    have hjx : x j < x (j + 1) := by
      change (p.point j).re < (p.point (j + 1)).re
      exact point_re_lt (p := p) hp (Nat.lt_succ_self j) hj₁
    have hjdelta : 0 < x (j + 1) - x j := sub_pos.mpr hjx
    by_cases hji : j < i
    · have hji₁ : j + 1 ≤ i := by omega
      have hxnext : x (j + 1) ≤ x i := by
        apply point_re_le_of_le (p := p) hp hji₁
        exact lt_trans (Nat.lt_succ_self i) hi
      have hclamp : max 0 (min (x (j + 1) - x j) (xval - x j)) =
          x (j + 1) - x j := by
        rw [min_eq_left (by linarith)]
        exact max_eq_right hjdelta.le
      have hneq : x (j + 1) ≠ x j := ne_of_gt hjx
      rw [ite_eq_right hneq, hclamp, div_mul_cancel₀ _ hjdelta.ne']
      have hji' : j ≤ i := hji.le
      have hji1' : j + 1 ≤ i := hji₁
      have hne : j ≠ i := by omega
      simp [F, hji', hji1', hne]
    · by_cases heq : j = i
      · subst j
        have hclamp : max 0 (min (x (i + 1) - x i) (xval - x i)) =
            xval - x i := by
          rw [min_eq_right (by linarith :
            xval - x i ≤ x (i + 1) - x i)]
          exact max_eq_right (by linarith : 0 ≤ xval - x i)
        have hneq : x (i + 1) ≠ x i := ne_of_gt hdx
        rw [ite_eq_right hneq, hclamp]
        simp [F, q]
      · have hneij : i ≠ j := by
          intro h
          exact heq h.symm
        have hij : i < j := lt_of_le_of_ne (Nat.le_of_not_gt hji) hneij
        have hj_lt : j < p.points.length := by dsimp [n] at hjn; omega
        have hix : x (i + 1) ≤ x j := by
          apply point_re_le_of_le (p := p) hp (by omega)
          exact hj_lt
        have hclamp : max 0 (min (x (j + 1) - x j) (xval - x j)) = 0 := by
          rw [max_eq_left (le_trans (min_le_right _ _) (by linarith))]
        rw [hclamp]
        have hji' : ¬ j ≤ i := not_le_of_gt hij
        have hji1' : ¬ j + 1 ≤ i := by omega
        have hne : j ≠ i := heq
        simp [F, hji', hji1', hne]
  unfold Polyline.heightFn
  change p.start.im + ∑ j ∈ Finset.range n,
      ((y (j + 1) - y j) /
        (if x (j + 1) = x j then 1 else x (j + 1) - x j)) *
        max 0 (min (x (j + 1) - x j) (xval - x j)) = y i + q
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_range_sub]
  simp only [Finset.sum_ite_eq', hidx, hFn, hF0]
  rw [← hp0]
  dsimp [q, x, y]
  ring

end Polyline

end
end DirectedDistances.PlanarMap
