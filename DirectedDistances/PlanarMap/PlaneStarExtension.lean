/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Data.Fin.Tuple.Basic
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Angular interpolation for plane stars

Helper toward Definition 3.8 (geometric bridge).
identified modulo orientation-preserving homeomorphisms of the plane. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

/-- Helper toward Definition 3.8 (geometric bridge): the affine angular lift
of a rotation sending angle `a` to angle `b`. -/
@[expose] def starRotationLift (a b : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.addRight (b - a)

/-- Helper toward Definition 3.8 (geometric bridge): the rotation lift is
strictly increasing. -/
theorem strictMono_starRotationLift (a b : ℝ) :
    StrictMono (starRotationLift a b) := by
  intro x y hxy
  change x + (b - a) < y + (b - a)
  simpa only [add_comm] using add_lt_add_right hxy (b - a)

/-- Helper toward Definition 3.8 (geometric bridge): the rotation lift has
degree one with angular period `2 * π`. -/
theorem starRotationLift_add_two_pi (a b t : ℝ) :
    starRotationLift a b (t + 2 * Real.pi) =
      starRotationLift a b t + 2 * Real.pi := by
  change (t + 2 * Real.pi) + (b - a) = (t + (b - a)) + 2 * Real.pi
  ring

/-- Helper toward Definition 3.8 (geometric bridge): rotation on the unit circle. -/
@[expose] def starCircleRotation (a b : ℝ) : Circle ≃ₜ Circle :=
  Homeomorph.mulLeft (Circle.exp (b - a))

/-- Helper toward Definition 3.8 (geometric bridge): the circle rotation is
induced by its strictly increasing affine lift. -/
theorem starCircleRotation_exp (a b t : ℝ) :
    starCircleRotation a b (Circle.exp t) =
      Circle.exp (starRotationLift a b t) := by
  change Circle.exp (b - a) * Circle.exp t = Circle.exp (t + (b - a))
  rw [Circle.exp_add, mul_comm]

/-- Helper toward Definition 3.8 (geometric bridge): a one-ray cyclic star
admits a circle homeomorphism with a strictly increasing affine degree-one lift. -/
theorem exists_circle_homeomorph_single_angle (a b : ℝ) :
    ∃ (φ : ℝ ≃ₜ ℝ) (h : Circle ≃ₜ Circle),
      StrictMono φ ∧
      (∀ t : ℝ, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) ∧
      (∀ t : ℝ, h (Circle.exp t) = Circle.exp (φ t)) ∧
      φ a = b ∧ h (Circle.exp a) = Circle.exp b ∧
      (∀ t : ℝ, φ t = t + (b - a)) := by
  refine ⟨starRotationLift a b, starCircleRotation a b,
    strictMono_starRotationLift a b, starRotationLift_add_two_pi a b,
    starCircleRotation_exp a b, ?_, ?_, fun _ => rfl⟩
  · change a + (b - a) = b
    ring
  · rw [starCircleRotation_exp]
    congr 1
    change a + (b - a) = b
    ring

/-- Helper toward Definition 3.8 (geometric bridge): the two affine pieces
which fix `l` and `u` and send the interior knot `a` to `b`. -/
@[expose] def starIntervalBend (l a b u t : ℝ) : ℝ :=
  if t ≤ a then b + (t - a) * ((b - l) / (a - l))
  else b + (t - a) * ((u - b) / (u - a))

/-- Helper toward Definition 3.8 (geometric bridge): the two pieces agree at
their common knot. -/
theorem starIntervalBend_knot (l a b u : ℝ) :
    starIntervalBend l a b u a = b := by
  simp only [starIntervalBend, le_refl, ite_true, sub_self, zero_mul, add_zero]

/-- Helper toward Definition 3.8 (geometric bridge): the two-piece angular
interpolant is continuous, including at its knot. -/
theorem continuous_starIntervalBend (l a b u : ℝ) :
    Continuous (starIntervalBend l a b u) := by
  apply Continuous.if_le
  · fun_prop
  · fun_prop
  · exact continuous_id
  · exact continuous_const
  · intro t ht
    simp only [ht, sub_self, zero_mul, add_zero]

/-- Helper toward Definition 3.8 (geometric bridge): both affine slopes are
positive for interior source and target knots. -/
theorem strictMono_starIntervalBend {l a b u : ℝ}
    (hla : l < a) (hau : a < u) (hlb : l < b) (hbu : b < u) :
    StrictMono (starIntervalBend l a b u) := by
  have hc : 0 < (b - l) / (a - l) := div_pos (sub_pos.mpr hlb) (sub_pos.mpr hla)
  have hd : 0 < (u - b) / (u - a) := div_pos (sub_pos.mpr hbu) (sub_pos.mpr hau)
  intro x y hxy
  unfold starIntervalBend
  split_ifs with hx hy hy
  · nlinarith only [mul_pos (sub_pos.mpr hxy) hc]
  · have hx' : (x - a) * ((b - l) / (a - l)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hc.le
    have hy' : 0 < (y - a) * ((u - b) / (u - a)) :=
      mul_pos (sub_pos.mpr (lt_of_not_ge hy)) hd
    linarith only [hx', hy']
  · exact (not_le_of_gt ((lt_of_not_ge hx).trans hxy) hy).elim
  · nlinarith only [mul_pos (sub_pos.mpr hxy) hd]

/-- Helper toward Definition 3.8 (geometric bridge): the source knot and
target knot divide the interpolant into corresponding half-lines. -/
theorem starIntervalBend_le_knot_iff {l a b u : ℝ}
    (hla : l < a) (hau : a < u) (hlb : l < b) (hbu : b < u) (t : ℝ) :
    starIntervalBend l a b u t ≤ b ↔ t ≤ a := by
  calc
    starIntervalBend l a b u t ≤ b ↔
        starIntervalBend l a b u t ≤ starIntervalBend l a b u a := by
      rw [starIntervalBend_knot]
    _ ↔ t ≤ a := (strictMono_starIntervalBend hla hau hlb hbu).le_iff_le

/-- Helper toward Definition 3.8 (geometric bridge): interchanging the
interior knots gives the inverse, with no homeomorphism premise. -/
theorem starIntervalBend_inverse {l a b u : ℝ}
    (hla : l < a) (hau : a < u) (hlb : l < b) (hbu : b < u) (t : ℝ) :
    starIntervalBend l b a u (starIntervalBend l a b u t) = t := by
  have ha : a - l ≠ 0 := ne_of_gt (sub_pos.mpr hla)
  have hb : b - l ≠ 0 := ne_of_gt (sub_pos.mpr hlb)
  have ha' : u - a ≠ 0 := ne_of_gt (sub_pos.mpr hau)
  have hb' : u - b ≠ 0 := ne_of_gt (sub_pos.mpr hbu)
  by_cases ht : t ≤ a
  · have ht' := (starIntervalBend_le_knot_iff hla hau hlb hbu t).2 ht
    rw [starIntervalBend, ite_eq_left ht', starIntervalBend, ite_eq_left ht]
    field_simp [ha, hb]
    ring
  · have ht' : ¬ starIntervalBend l a b u t ≤ b := by
      rw [starIntervalBend_le_knot_iff hla hau hlb hbu]
      exact ht
    rw [starIntervalBend, ite_eq_right ht', starIntervalBend, ite_eq_right ht]
    field_simp [ha', hb']
    ring

/-- Helper toward Definition 3.8 (geometric bridge): a homeomorphism of the
line obtained by two affine pieces with positive slopes. -/
@[expose] def starIntervalBendHomeomorph {l a b u : ℝ}
    (hla : l < a) (hau : a < u) (hlb : l < b) (hbu : b < u) : ℝ ≃ₜ ℝ where
  toFun := starIntervalBend l a b u
  invFun := starIntervalBend l b a u
  left_inv := starIntervalBend_inverse hla hau hlb hbu
  right_inv := starIntervalBend_inverse hlb hbu hla hau
  continuous_toFun := continuous_starIntervalBend l a b u
  continuous_invFun := continuous_starIntervalBend l b a u

/-- Helper toward Definition 3.8 (geometric bridge): the left endpoint of
the two-piece interpolation is fixed. -/
theorem starIntervalBend_left {l a b u : ℝ} (hla : l < a) :
    starIntervalBend l a b u l = l := by
  rw [starIntervalBend, ite_eq_left hla.le]
  field_simp [ne_of_gt (sub_pos.mpr hla)]
  ring

/-- Helper toward Definition 3.8 (geometric bridge): the right endpoint of
the two-piece interpolation is fixed. -/
theorem starIntervalBend_right {l a b u : ℝ} (hau : a < u) :
    starIntervalBend l a b u u = u := by
  rw [starIntervalBend, ite_eq_right (not_le_of_gt hau)]
  field_simp [ne_of_gt (sub_pos.mpr hau)]
  ring

/-- Helper toward Definition 3.8 (geometric bridge): recursive affine
interpolation through a finite ordered list, with affine tails on the line. -/
@[expose] def starFiniteInterpolate :
    (n : ℕ) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℝ → ℝ
  | 0, a, b, t => b 0 + (t - a 0)
  | n + 1, a, b, t =>
      if t ≤ a (Fin.last n).castSucc then
        starFiniteInterpolate n (fun i => a i.castSucc) (fun i => b i.castSucc) t
      else b (Fin.last n).castSucc + (t - a (Fin.last n).castSucc) *
        ((b (Fin.last (n + 1)) - b (Fin.last n).castSucc) /
          (a (Fin.last (n + 1)) - a (Fin.last n).castSucc))

/-- Helper toward Definition 3.8 (geometric bridge): finite affine
interpolation attains every prescribed knot. -/
theorem starFiniteInterpolate_knot (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (i : Fin (n + 1)) :
    starFiniteInterpolate n a b (a i) = b i := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simp only [starFiniteInterpolate, sub_self, add_zero]
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hlt : a (Fin.last n).castSucc < a (Fin.last (n + 1)) :=
          ha (Fin.castSucc_lt_last _)
        rw [starFiniteInterpolate, ite_eq_right (not_le_of_gt hlt)]
        field_simp [ne_of_gt (sub_pos.mpr hlt)]
        ring
      · have hj : a j.castSucc ≤ a (Fin.last n).castSucc :=
          ha.monotone (show j.castSucc ≤ (Fin.last n).castSucc from Fin.le_last j)
        rw [starFiniteInterpolate, ite_eq_left hj]
        exact ih (fun k => a k.castSucc) (fun k => b k.castSucc)
          (ha.comp (fun _ _ h => h)) j

/-- Helper toward Definition 3.8 (geometric bridge): interpolation of two
strictly increasing finite lists is strictly increasing on the whole line. -/
theorem strictMono_starFiniteInterpolate (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) :
    StrictMono (starFiniteInterpolate n a b) := by
  induction n with
  | zero =>
      intro x y hxy
      dsimp only [starFiniteInterpolate]
      linarith only [hxy]
  | succ n ih =>
      have hap : StrictMono (fun i : Fin (n + 1) => a i.castSucc) :=
        ha.comp (fun _ _ h => h)
      have hbp : StrictMono (fun i : Fin (n + 1) => b i.castSucc) :=
        hb.comp (fun _ _ h => h)
      have hp := ih _ _ hap hbp
      have hk := starFiniteInterpolate_knot n
        (fun i => a i.castSucc) (fun i => b i.castSucc) hap (Fin.last n)
      have hc : 0 < (b (Fin.last (n + 1)) - b (Fin.last n).castSucc) /
          (a (Fin.last (n + 1)) - a (Fin.last n).castSucc) :=
        div_pos (sub_pos.mpr (hb (Fin.castSucc_lt_last _)))
          (sub_pos.mpr (ha (Fin.castSucc_lt_last _)))
      intro x y hxy
      rw [starFiniteInterpolate, starFiniteInterpolate]
      split_ifs with hx hy hy
      · exact hp hxy
      · have hx' := hp.monotone hx
        rw [hk] at hx'
        have hy' := mul_pos (sub_pos.mpr (lt_of_not_ge hy)) hc
        linarith only [hx', hy']
      · exact (not_le_of_gt ((lt_of_not_ge hx).trans hxy) hy).elim
      · nlinarith only [mul_pos (sub_pos.mpr hxy) hc]

/-- Helper toward Definition 3.8 (geometric bridge): swapping the finite
angle lists gives the inverse interpolation. -/
theorem starFiniteInterpolate_inverse (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) (t : ℝ) :
    starFiniteInterpolate n b a (starFiniteInterpolate n a b t) = t := by
  induction n with
  | zero =>
      dsimp only [starFiniteInterpolate]
      ring
  | succ n ih =>
      have hap : StrictMono (fun i : Fin (n + 1) => a i.castSucc) :=
        ha.comp (fun _ _ h => h)
      have hbp : StrictMono (fun i : Fin (n + 1) => b i.castSucc) :=
        hb.comp (fun _ _ h => h)
      have hp := strictMono_starFiniteInterpolate n _ _ hap hbp
      have hk := starFiniteInterpolate_knot n
        (fun i => a i.castSucc) (fun i => b i.castSucc) hap (Fin.last n)
      have ha' := sub_pos.mpr (ha (Fin.castSucc_lt_last (Fin.last n)))
      have hb' := sub_pos.mpr (hb (Fin.castSucc_lt_last (Fin.last n)))
      by_cases ht : t ≤ a (Fin.last n).castSucc
      · have hft : starFiniteInterpolate (n + 1) a b t ≤ b (Fin.last n).castSucc := by
          rw [starFiniteInterpolate, ite_eq_left ht]
          calc
            _ ≤ starFiniteInterpolate n (fun i => a i.castSucc)
                (fun i => b i.castSucc) (a (Fin.last n).castSucc) := hp.monotone ht
            _ = _ := hk
        rw [starFiniteInterpolate, ite_eq_left hft, starFiniteInterpolate, ite_eq_left ht]
        exact ih _ _ hap hbp
      · have hft : ¬ starFiniteInterpolate (n + 1) a b t ≤ b (Fin.last n).castSucc := by
          rw [starFiniteInterpolate, ite_eq_right ht]
          have hc := mul_pos (sub_pos.mpr (lt_of_not_ge ht)) (div_pos hb' ha')
          linarith only [hc]
        rw [starFiniteInterpolate, ite_eq_right hft, starFiniteInterpolate, ite_eq_right ht]
        field_simp [ne_of_gt ha', ne_of_gt hb']
        ring

/-- Helper toward Definition 3.8 (geometric bridge): finite affine
interpolation is continuous across all its knots. -/
theorem continuous_starFiniteInterpolate (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) : Continuous (starFiniteInterpolate n a b) := by
  induction n with
  | zero =>
      dsimp only [starFiniteInterpolate]
      fun_prop
  | succ n ih =>
      have hap : StrictMono (fun i : Fin (n + 1) => a i.castSucc) :=
        ha.comp (fun _ _ h => h)
      change Continuous (fun t => if t ≤ a (Fin.last n).castSucc then _ else _)
      apply Continuous.if_le
      · exact ih _ _ hap
      · fun_prop
      · exact continuous_id
      · exact continuous_const
      · intro t ht
        rw [ht, starFiniteInterpolate_knot n _ _ hap (Fin.last n)]
        simp only [sub_self, zero_mul, add_zero]

/-- Helper toward Definition 3.8 (geometric bridge): an explicit
homeomorphism interpolating two finite increasing lists of real angles. This
is a line homeomorphism; periodic extension is a separate obligation. -/
@[expose] def starFiniteInterpolationHomeomorph (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b) : ℝ ≃ₜ ℝ where
  toFun := starFiniteInterpolate n a b
  invFun := starFiniteInterpolate n b a
  left_inv := starFiniteInterpolate_inverse n a b ha hb
  right_inv := starFiniteInterpolate_inverse n b a hb ha
  continuous_toFun := continuous_starFiniteInterpolate n a b ha
  continuous_invFun := continuous_starFiniteInterpolate n b a hb

/-- Helper toward Definition 3.8 (geometric bridge): repeat the finite
interpolation with period `P`, using the first source knot as the cut. -/
@[expose] def starPeriodicInterpolate (P : ℝ) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  let k : ℤ := ⌊(t - a 0) / P⌋
  starFiniteInterpolate n a b (t - (k : ℝ) * P) + (k : ℝ) * P

/-- Helper toward Definition 3.8 (geometric bridge): the residual angle
belongs to the half-open fundamental interval. -/
theorem star_period_remainder_mem {P : ℝ} (hP : 0 < P) (c t : ℝ) :
    c ≤ t - (⌊(t - c) / P⌋ : ℤ) * P ∧
      t - (⌊(t - c) / P⌋ : ℤ) * P < c + P := by
  have hl := (le_div_iff₀ hP).mp (Int.floor_le ((t - c) / P))
  have hu := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one ((t - c) / P))
  constructor <;> nlinarith only [hl, hu]

/-- Helper toward Definition 3.8 (geometric bridge): a periodic
interpolant maps each fundamental interval to the corresponding target interval. -/
theorem starFiniteInterpolate_mem_period {P : ℝ} (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P)
    {t : ℝ} (ht : a 0 ≤ t ∧ t < a 0 + P) :
    b 0 ≤ starFiniteInterpolate n a b t ∧
      starFiniteInterpolate n a b t < b 0 + P := by
  have hm := strictMono_starFiniteInterpolate n a b ha hb
  constructor
  · calc
      b 0 = starFiniteInterpolate n a b (a 0) :=
        (starFiniteInterpolate_knot n a b ha 0).symm
      _ ≤ _ := hm.monotone ht.1
  · calc
      _ < starFiniteInterpolate n a b (a (Fin.last n)) := hm (by rw [haP]; exact ht.2)
      _ = b (Fin.last n) := starFiniteInterpolate_knot n a b ha (Fin.last n)
      _ = b 0 + P := hbP

/-- Helper toward Definition 3.8 (geometric bridge): source and image
angles have the same period index. -/
theorem starPeriodicInterpolate_index {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P) (t : ℝ) :
    ⌊(starPeriodicInterpolate P n a b t - b 0) / P⌋ = ⌊(t - a 0) / P⌋ := by
  have hr := star_period_remainder_mem hP (a 0) t
  have hf := starFiniteInterpolate_mem_period n a b ha hb haP hbP hr
  apply Int.floor_eq_iff.mpr
  dsimp only [starPeriodicInterpolate]
  constructor
  · apply (le_div_iff₀ hP).mpr
    linarith only [hf.1]
  · apply (div_lt_iff₀ hP).mpr
    nlinarith only [hf.2]

/-- Helper toward Definition 3.8 (geometric bridge): interchanging the
lists inverts their periodic interpolation. -/
theorem starPeriodicInterpolate_inverse {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P) (t : ℝ) :
    starPeriodicInterpolate P n b a (starPeriodicInterpolate P n a b t) = t := by
  rw [starPeriodicInterpolate]
  rw [starPeriodicInterpolate_index hP n a b ha hb haP hbP t]
  rw [starPeriodicInterpolate]
  rw [add_sub_cancel_right, starFiniteInterpolate_inverse n a b ha hb]
  ring

/-- Helper toward Definition 3.8 (geometric bridge): periodic
interpolation commutes with addition of one full period. -/
theorem starPeriodicInterpolate_add_period {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (t : ℝ) :
    starPeriodicInterpolate P n a b (t + P) =
      starPeriodicInterpolate P n a b t + P := by
  have he : (t + P - a 0) / P = (t - a 0) / P + 1 := by
    field_simp [ne_of_gt hP]
    ring
  unfold starPeriodicInterpolate
  rw [he, Int.floor_add_one]
  push_cast
  have hr : t + P - ((⌊(t - a 0) / P⌋ : ℤ) + 1 : ℝ) * P =
      t - (⌊(t - a 0) / P⌋ : ℤ) * P := by ring
  rw [hr]
  ring

/-- Helper toward Definition 3.8 (geometric bridge): repeating finite
interpolation is strictly increasing even across the chosen angular cut. -/
theorem strictMono_starPeriodicInterpolate {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P) :
    StrictMono (starPeriodicInterpolate P n a b) := by
  intro x y hxy
  let kx : ℤ := ⌊(x - a 0) / P⌋
  let ky : ℤ := ⌊(y - a 0) / P⌋
  have hkxy : kx ≤ ky := Int.floor_mono
    ((div_le_div_iff_of_pos_right hP).mpr (sub_le_sub_right hxy.le _))
  have hx := starFiniteInterpolate_mem_period n a b ha hb haP hbP
    (star_period_remainder_mem hP (a 0) x)
  have hy := starFiniteInterpolate_mem_period n a b ha hb haP hbP
    (star_period_remainder_mem hP (a 0) y)
  change starFiniteInterpolate n a b (x - (kx : ℝ) * P) + (kx : ℝ) * P <
    starFiniteInterpolate n a b (y - (ky : ℝ) * P) + (ky : ℝ) * P
  by_cases hk : kx = ky
  · rw [hk]
    have hm := strictMono_starFiniteInterpolate n a b ha hb
      (show x - (ky : ℝ) * P < y - (ky : ℝ) * P by linarith only [hxy])
    linarith only [hm]
  · have hki : (kx : ℝ) + 1 ≤ (ky : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr (lt_of_le_of_ne hkxy hk)
    have hmul := mul_le_mul_of_nonneg_right hki hP.le
    change b 0 ≤ starFiniteInterpolate n a b (y - (ky : ℝ) * P) ∧ _ at hy
    change _ ∧ starFiniteInterpolate n a b (x - (kx : ℝ) * P) < b 0 + P at hx
    nlinarith only [hx.2, hy.1, hmul]

/-- Helper toward Definition 3.8 (geometric bridge): a degree-one
homeomorphism of the line from finite interpolation on a fundamental interval. -/
@[expose] def starPeriodicInterpolationHomeomorph {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P) : ℝ ≃ₜ ℝ :=
  (show ℝ ≃o ℝ from
    { toFun := starPeriodicInterpolate P n a b
      invFun := starPeriodicInterpolate P n b a
      left_inv := starPeriodicInterpolate_inverse hP n a b ha hb haP hbP
      right_inv := starPeriodicInterpolate_inverse hP n b a hb ha hbP haP
      map_rel_iff' := (strictMono_starPeriodicInterpolate hP n a b ha hb haP hbP).le_iff_le
    }).toHomeomorph

/-- Helper toward Definition 3.8 (geometric bridge): the periodic
interpolant commutes with every integral angular translation. -/
theorem starPeriodicInterpolate_add_int_mul {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (t : ℝ) (k : ℤ) :
    starPeriodicInterpolate P n a b (t + (k : ℝ) * P) =
      starPeriodicInterpolate P n a b t + (k : ℝ) * P := by
  have he : (t + (k : ℝ) * P - a 0) / P = (t - a 0) / P + k := by
    field_simp [ne_of_gt hP]
    ring
  unfold starPeriodicInterpolate
  rw [he, Int.floor_add_intCast]
  push_cast
  have hr : t + (k : ℝ) * P - ((⌊(t - a 0) / P⌋ : ℤ) + k : ℝ) * P =
      t - (⌊(t - a 0) / P⌋ : ℤ) * P := by ring
  rw [hr]
  ring

/-- Helper toward Definition 3.8 (geometric bridge): equal circle angles
have equal images under periodic interpolation. -/
theorem starPeriodicInterpolate_exp_congr (n : ℕ) (a b : Fin (n + 1) → ℝ)
    {s t : ℝ} (hst : Circle.exp s = Circle.exp t) :
    Circle.exp (starPeriodicInterpolate (2 * Real.pi) n a b s) =
      Circle.exp (starPeriodicInterpolate (2 * Real.pi) n a b t) := by
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hst
  rw [hk, starPeriodicInterpolate_add_int_mul (by positivity)]
  exact Circle.exp_eq_exp.mpr ⟨k, rfl⟩

/-- Helper toward Definition 3.8 (geometric bridge): the circle map induced
by the explicit periodic interpolation. -/
@[expose] def starPeriodicCircleMap (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (z : Circle) : Circle :=
  Circle.exp (starPeriodicInterpolate (2 * Real.pi) n a b (Complex.arg z))

/-- Helper toward Definition 3.8 (geometric bridge): the induced circle
map agrees with the periodic lift at every real angle. -/
theorem starPeriodicCircleMap_exp (n : ℕ) (a b : Fin (n + 1) → ℝ) (t : ℝ) :
    starPeriodicCircleMap n a b (Circle.exp t) =
      Circle.exp (starPeriodicInterpolate (2 * Real.pi) n a b t) := by
  exact starPeriodicInterpolate_exp_congr n a b (Circle.exp_arg (Circle.exp t))

/-- Helper toward Definition 3.8 (geometric bridge): continuity on the
circle follows from the quotient topology, including at the angular cut. -/
theorem continuous_starPeriodicCircleMap (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + 2 * Real.pi)
    (hbP : b (Fin.last n) = b 0 + 2 * Real.pi) :
    Continuous (starPeriodicCircleMap n a b) := by
  apply (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff.mpr
  have he : starPeriodicCircleMap n a b ∘ Circle.exp =
      Circle.exp ∘ starPeriodicInterpolate (2 * Real.pi) n a b := by
    funext t
    exact starPeriodicCircleMap_exp n a b t
  rw [he]
  exact Circle.exp.continuous.comp
    (starPeriodicInterpolationHomeomorph (by positivity) n a b ha hb haP hbP).continuous

/-- Helper toward Definition 3.8 (geometric bridge): the circle
homeomorphism obtained by periodic finite interpolation. Its lift is strictly
increasing, so this realizes the positive orientation on the circle. -/
@[expose] def starPeriodicCircleHomeomorph (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (haP : a (Fin.last n) = a 0 + 2 * Real.pi)
    (hbP : b (Fin.last n) = b 0 + 2 * Real.pi) : Circle ≃ₜ Circle where
  toFun := starPeriodicCircleMap n a b
  invFun := starPeriodicCircleMap n b a
  left_inv := by
    intro z
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    rw [starPeriodicCircleMap_exp, starPeriodicCircleMap_exp,
      starPeriodicInterpolate_inverse (by positivity) n a b ha hb haP hbP]
  right_inv := by
    intro z
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    rw [starPeriodicCircleMap_exp, starPeriodicCircleMap_exp,
      starPeriodicInterpolate_inverse (by positivity) n b a hb ha hbP haP]
  continuous_toFun := continuous_starPeriodicCircleMap n a b ha hb haP hbP
  continuous_invFun := continuous_starPeriodicCircleMap n b a hb ha hbP haP

/-- Helper toward Definition 3.8 (geometric bridge): interpolation is
affine on each interval between successive prescribed knots. -/
theorem starFiniteInterpolate_affine (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (i : Fin n) (t : ℝ)
    (htl : a i.castSucc ≤ t) (htu : t ≤ a i.succ) :
    starFiniteInterpolate n a b t = b i.castSucc + (t - a i.castSucc) *
      ((b i.succ - b i.castSucc) / (a i.succ - a i.castSucc)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      have hap : StrictMono (fun j : Fin (n + 1) => a j.castSucc) :=
        ha.comp (fun _ _ h => h)
      revert htl htu
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro htl htu
        by_cases ht : t ≤ a (Fin.last n).castSucc
        · have he : t = a (Fin.last n).castSucc := le_antisymm ht htl
          rw [he, starFiniteInterpolate_knot _ _ _ ha]
          simp only [sub_self, zero_mul, add_zero]
        · rw [starFiniteInterpolate, ite_eq_right ht]
          rfl
      · intro htl htu
        have ht : t ≤ a (Fin.last n).castSucc := htu.trans
          (ha.monotone (show (j.castSucc).succ ≤ (Fin.last n).castSucc from
            Fin.le_last j.succ))
        rw [starFiniteInterpolate, ite_eq_left ht]
        exact ih _ _ hap j htl htu

/-- Helper toward Definition 3.8 (geometric bridge): on a half-open
fundamental interval the periodic extension equals the finite interpolation. -/
theorem starPeriodicInterpolate_eq_of_mem_Ico {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) {t : ℝ} (ht : a 0 ≤ t ∧ t < a 0 + P) :
    starPeriodicInterpolate P n a b t = starFiniteInterpolate n a b t := by
  have hk : ⌊(t - a 0) / P⌋ = (0 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_zero, zero_add]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hP.le
    · apply (div_lt_iff₀ hP).mpr
      linarith only [ht.2]
  simp only [starPeriodicInterpolate, hk, Int.cast_zero, zero_mul, sub_zero, add_zero]

/-- Helper toward Definition 3.8 (geometric bridge): the finite and
periodic interpolations agree on the closed fundamental interval, including
the wraparound endpoint. -/
theorem starPeriodicInterpolate_eq_of_mem_Icc {P : ℝ} (hP : 0 < P) (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (haP : a (Fin.last n) = a 0 + P) (hbP : b (Fin.last n) = b 0 + P)
    {t : ℝ} (ht : a 0 ≤ t ∧ t ≤ a 0 + P) :
    starPeriodicInterpolate P n a b t = starFiniteInterpolate n a b t := by
  by_cases hlt : t < a 0 + P
  · exact starPeriodicInterpolate_eq_of_mem_Ico hP n a b ⟨ht.1, hlt⟩
  · have he : t = a 0 + P := le_antisymm ht.2 (le_of_not_gt hlt)
    rw [he, starPeriodicInterpolate_add_period hP,
      starPeriodicInterpolate_eq_of_mem_Ico hP n a b ⟨le_rfl, by linarith only [hP]⟩,
      starFiniteInterpolate_knot n a b ha 0, ← haP,
      starFiniteInterpolate_knot n a b ha (Fin.last n), hbP]

/-- Helper toward Definition 3.8 (geometric bridge): adjoining an upper
endpoint to a strictly increasing finite list preserves strict increase. -/
theorem strictMono_star_snoc {n : ℕ} (a : Fin n → ℝ) (u : ℝ)
    (ha : StrictMono a) (hu : ∀ i, a i < u) : StrictMono (Fin.snoc a u) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij
    have hi : i.val < n := hij
    have he : i = (⟨i.val, hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he, Fin.snoc_castSucc, Fin.snoc_last]
    exact hu _
  · intro hij
    have hi : i.val < n := lt_trans hij j.isLt
    have he : i = (⟨i.val, hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact ha hij

/-- Helper toward Definition 3.8 (geometric bridge): two nonempty strictly
increasing angle lists in `[0, 2π)` are matched by a circle homeomorphism
whose lift is strictly increasing, commutes with `+2π`, and is affine on
each interval of an explicit finite partition of a fundamental interval.
The final knot records the wraparound interval; every knot is matched by
the same lift and the same circle homeomorphism. -/
theorem exists_circle_homeomorph_finite_angles (n : ℕ) (hn : 1 ≤ n)
    (a b : Fin n → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ j, 0 ≤ a j) (ha2 : ∀ j, a j < 2 * Real.pi)
    (hb0 : ∀ j, 0 ≤ b j) (hb2 : ∀ j, b j < 2 * Real.pi) :
    ∃ (φ : ℝ ≃ₜ ℝ) (h : Circle ≃ₜ Circle) (c d : Fin (n + 1) → ℝ),
      StrictMono φ ∧
      (∀ t : ℝ, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi) ∧
      (∀ t : ℝ, h (Circle.exp t) = Circle.exp (φ t)) ∧
      (∀ j : Fin n, φ (a j) = b j ∧ h (Circle.exp (a j)) = Circle.exp (b j)) ∧
      StrictMono c ∧ StrictMono d ∧
      (∀ j : Fin n, c j.castSucc = a j ∧ d j.castSucc = b j) ∧
      c (Fin.last n) = c 0 + 2 * Real.pi ∧
      d (Fin.last n) = d 0 + 2 * Real.pi ∧
      (∀ (i : Fin n) (t : ℝ), c i.castSucc ≤ t → t ≤ c i.succ →
        φ t = d i.castSucc + (t - c i.castSucc) *
          ((d i.succ - d i.castSucc) / (c i.succ - c i.castSucc))) := by
  cases n with
  | zero => omega
  | succ n =>
      let c : Fin (n + 1 + 1) → ℝ := Fin.snoc a (a 0 + 2 * Real.pi)
      let d : Fin (n + 1 + 1) → ℝ := Fin.snoc b (b 0 + 2 * Real.pi)
      have hc : StrictMono c := strictMono_star_snoc a _ ha (by
        intro j
        linarith only [ha2 j, ha0 0])
      have hd : StrictMono d := strictMono_star_snoc b _ hb (by
        intro j
        linarith only [hb2 j, hb0 0])
      have hc0 : c 0 = a 0 := Fin.snoc_apply_zero _ _
      have hd0 : d 0 = b 0 := Fin.snoc_apply_zero _ _
      have hcP : c (Fin.last (n + 1)) = c 0 + 2 * Real.pi := by
        rw [hc0]
        exact Fin.snoc_last _ _
      have hdP : d (Fin.last (n + 1)) = d 0 + 2 * Real.pi := by
        rw [hd0]
        exact Fin.snoc_last _ _
      let φ := starPeriodicInterpolationHomeomorph (by positivity) (n + 1) c d hc hd hcP hdP
      let h := starPeriodicCircleHomeomorph (n + 1) c d hc hd hcP hdP
      have hφ (t : ℝ) : φ t = starPeriodicInterpolate (2 * Real.pi) (n + 1) c d t := rfl
      have hh (t : ℝ) : h (Circle.exp t) = Circle.exp (φ t) :=
        starPeriodicCircleMap_exp (n + 1) c d t
      have hj (j : Fin (n + 1)) : φ (a j) = b j := by
        rw [hφ, starPeriodicInterpolate_eq_of_mem_Ico (by positivity)]
        · have he : a j = c j.castSucc := by
            change a j = (Fin.snoc a (a 0 + 2 * Real.pi) : Fin (n + 1 + 1) → ℝ) j.castSucc
            rw [Fin.snoc_castSucc]
          rw [he, starFiniteInterpolate_knot (n + 1) c d hc]
          exact Fin.snoc_castSucc _ _ _
        · rw [hc0]
          exact ⟨ha.monotone (show (0 : Fin (n + 1)) ≤ j from Nat.zero_le _),
            by linarith only [ha2 j, ha0 0]⟩
      refine ⟨φ, h, c, d,
        strictMono_starPeriodicInterpolate (by positivity) (n + 1) c d hc hd hcP hdP,
        starPeriodicInterpolate_add_period (by positivity) (n + 1) c d, hh,
        (fun j => ⟨hj j, by rw [hh, hj]⟩), hc, hd,
        (fun j => ⟨Fin.snoc_castSucc _ _ _, Fin.snoc_castSucc _ _ _⟩), hcP, hdP, ?_⟩
      intro i t htl htu
      rw [hφ, starPeriodicInterpolate_eq_of_mem_Icc (by positivity) (n + 1) c d hc hcP hdP]
      · exact starFiniteInterpolate_affine (n + 1) c d hc i t htl htu
      · constructor
        · exact (hc.monotone (show (0 : Fin (n + 1 + 1)) ≤ i.castSucc from
            Nat.zero_le _)).trans htl
        · rw [← hcP]
          exact htu.trans (hc.monotone (Fin.le_last i.succ))

































end DirectedDistances.PlanarMap
