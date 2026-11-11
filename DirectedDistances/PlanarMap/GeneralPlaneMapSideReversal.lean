/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree

/-! # Reversal of winding sides -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

variable {V E : Type*}




theorem hasWinding_congr_fun {x y : ℂ} (L : Path x x) (L' : Path y y)
    (w : ℂ) (n : ℤ) (h : ∀ t, L t = L' t) :
    HasWinding L w n ↔ HasWinding L' w n := by
  constructor
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    rw [← h t]
    exact hφ t
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    rw [h t]
    exact hφ t

/-- Helper toward Definition 1.1: cyclically moving the starting point of a
concatenated loop preserves its winding number. -/
theorem hasWinding_trans_swap_forward {x y : ℂ} (α : Path x y)
    (β : Path y x) (w : ℂ) (n : ℤ)
    (h : HasWinding (α.trans β) w n) :
    HasWinding (β.trans α) w n := by
  obtain ⟨φ, hφ, hinc⟩ := h
  let δ : ℂ := 2 * Real.pi * Complex.I * n
  have hδ : Complex.exp δ = 1 := by
    have hperiod : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
      have htwo : (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
          (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by ring
      rw [htwo, Complex.exp_add, Complex.exp_pi_mul_I]
      norm_num
    have hcast : δ = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [δ]
      push_cast
      ring
    rw [hcast, Complex.exp_int_mul, hperiod]
    simp
  let u : I → I := fun t =>
    ⟨min ((t : ℝ) + 1 / 2) 1,
      le_min (by have := t.property.1; linarith) (by norm_num), min_le_right _ _⟩
  let v : I → I := fun t =>
    ⟨max ((t : ℝ) - 1 / 2) 0,
      le_max_right _ _, max_le (by have := t.property.2; linarith) (by norm_num)⟩
  have hu : Continuous u := by
    apply Continuous.subtype_mk
    fun_prop
  have hv : Continuous v := by
    apply Continuous.subtype_mk
    fun_prop
  let half : I := ⟨(1 / 2 : ℝ), by norm_num⟩
  let ψfun : I → ℂ := fun t =>
    if (t : ℝ) ≤ 1 / 2 then φ (u t) else φ (v t) + δ
  have hψfun : Continuous ψfun := by
    apply Continuous.if_le
    · exact φ.continuous.comp hu
    · exact (φ.continuous.comp hv).add continuous_const
    · exact continuous_subtype_val
    · exact continuous_const
    · intro t ht
      have ht' : (t : ℝ) = 1 / 2 := ht
      have hu' : u t = 1 := by
        apply Subtype.ext
        simp [u, ht']
        norm_num
      have hv' : v t = 0 := by
        apply Subtype.ext
        simp [v, ht']
      rw [hu', hv']
      change φ 1 = φ 0 + δ
      calc
        φ 1 = (φ 1 - φ 0) + φ 0 := by ring
        _ = δ + φ 0 := by rw [hinc]
        _ = φ 0 + δ := by ring
  let ψ : C(I, ℂ) := ⟨ψfun, hψfun⟩
  refine ⟨ψ, ?_, ?_⟩
  · intro t
    change Complex.exp (ψfun t) = (β.trans α) t - w
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [ψfun, if_pos ht]
      have huval : (u t : ℝ) = (t : ℝ) + 1 / 2 := by
        change min ((t : ℝ) + 1 / 2) 1 = _
        rw [min_eq_left (by have := t.property.2; nlinarith)]
      by_cases hzero : (t : ℝ) = 0
      · have hφt := hφ (u t)
        have htzero : t = 0 := Subtype.ext hzero
        have huone : u t = half := by
          apply Subtype.ext
          rw [huval, hzero]
          change 0 + (1 / 2 : ℝ) = (1 / 2 : ℝ)
          ring
        have hloop : (α.trans β) half = β 0 := by
          simp [Path.trans_apply, half]
        have hnew : (β.trans α) t = β 0 := by
          simp [Path.trans_apply, htzero]
        rw [huone, hloop] at hφt
        rw [huone, hnew]
        exact hφt
      · have hu_gt : (1 / 2 : ℝ) < (u t : ℝ) := by
          have htpos : 0 < (t : ℝ) := by
            by_contra hnot
            have hzero' : (t : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) t.property.1
            exact hzero hzero'
          rw [huval]
          linarith
        have hφt := hφ (u t)
        have hnew : (β.trans α) t = (α.trans β) (u t) := by
          rw [Path.trans_apply, Path.trans_apply]
          simp only [show ¬ ((u t : I) : ℝ) ≤ 1 / 2 by exact not_le.mpr hu_gt,
            dite_false, show (t : ℝ) ≤ 1 / 2 by exact ht, dite_true]
          apply congrArg β
          apply Subtype.ext
          change 2 * (t : ℝ) = 2 * (u t : ℝ) - 1
          rw [huval]
          ring
        rw [hnew]
        exact hφt
    · simp only [ψfun, if_neg ht]
      have hvval : (v t : ℝ) = (t : ℝ) - 1 / 2 := by
        change max ((t : ℝ) - 1 / 2) 0 = _
        rw [max_eq_left (by have := t.property.1; linarith)]
      have hφt := hφ (v t)
      have hvle : (v t : ℝ) ≤ 1 / 2 := by rw [hvval]; have := t.property.2; linarith
      have hnew : (β.trans α) t = (α.trans β) (v t) := by
        rw [Path.trans_apply, Path.trans_apply]
        simp only [show ¬ (t : ℝ) ≤ 1 / 2 by exact ht, dite_false,
          hvle, dite_true]
        apply congrArg α
        apply Subtype.ext
        change 2 * (t : ℝ) - 1 = 2 * (v t : ℝ)
        rw [hvval]
        ring
      change Complex.exp (φ (v t) + δ) = (β.trans α) t - w
      rw [Complex.exp_add, hδ]
      simp only [mul_one]
      rw [hnew]
      simpa using hφt
  · have hu0 : u 0 = half := by
      apply Subtype.ext
      norm_num [u, half]
    have hv1 : v 1 = half := by
      apply Subtype.ext
      norm_num [v, half]
    have hψ0 : ψ 0 = φ half := by
      change ψfun 0 = φ half
      change (if ((0 : I) : ℝ) ≤ (1 / 2 : ℝ) then φ (u 0) else φ (v 0) + δ) = _
      rw [if_pos (by norm_num), hu0]
    have hψ1 : ψ 1 = φ half + δ := by
      change ψfun 1 = φ half + δ
      change (if ((1 : I) : ℝ) ≤ (1 / 2 : ℝ) then φ (u 1) else φ (v 1) + δ) = _
      rw [if_neg (by norm_num), hv1]
    rw [hψ1, hψ0]
    dsimp [δ]
    ring

/-- Helper toward Definition 1.1: reversing both paths in a chord-closed
loop negates its winding number, after accounting for the moved basepoint. -/
theorem hasWinding_trans_symm_swap_iff {x y : ℂ} (α : Path x y)
    (β : Path y x) (w : ℂ) (n : ℤ) :
    HasWinding (α.trans β) w (-n) ↔
      HasWinding (α.symm.trans β.symm) w n := by
  constructor
  · intro h
    have hrev := hasWinding_symm (α.trans β) w (-n) h
    have hrev' : HasWinding (β.symm.trans α.symm) w n := by
      simpa only [Path.trans_symm, neg_neg] using hrev
    exact hasWinding_trans_swap_forward β.symm α.symm w n hrev'
  · intro h
    have hcy := hasWinding_trans_swap_forward α.symm β.symm w n h
    have hrev : HasWinding (α.trans β).symm w n := by
      simpa only [Path.trans_symm] using hcy
    have hback := hasWinding_symm (α.trans β).symm w n hrev
    simpa using hback

/-- Helper toward Definition 1.1: the edge segment traversed on a reversed
parameterized arc is the reverse of the original segment. -/
theorem edgeSubarc_symm {x y : ℂ} (γ : Path x y) (a b : I)
    (hab : a ≤ b) :
    (edgeSubarc γ a b hab).symm =
      (edgeSubarc γ.symm (σ b) (σ a) ((unitInterval.symm_le_symm).2 hab)).cast
        (by simp [Path.symm]) (by simp [Path.symm]) := by
  apply Path.ext
  funext t
  change γ.extend (min (max (1 - (t : ℝ)) (a : ℝ)) (b : ℝ)) =
    (γ.symm).extend
      (min (max (t : ℝ) (1 - (b : ℝ))) (1 - (a : ℝ)))
  rw [Path.extend_symm_apply]
  apply congrArg γ.extend
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  by_cases h₀ : 1 - (t : ℝ) ≤ (a : ℝ)
  · have htA : 1 - (a : ℝ) ≤ t := by linarith
    have htB : 1 - (b : ℝ) ≤ t := by linarith
    rw [max_eq_right h₀, min_eq_left habR, max_eq_left htB, min_eq_right htA]
    linarith
  · by_cases h₁ : (b : ℝ) ≤ 1 - (t : ℝ)
    · have htB : (t : ℝ) ≤ 1 - (b : ℝ) := by linarith
      have htA : (a : ℝ) ≤ 1 - (t : ℝ) := by linarith [habR]
      have hAB : 1 - (b : ℝ) ≤ 1 - (a : ℝ) := by linarith [habR]
      rw [max_eq_left htA, min_eq_right h₁, max_eq_right htB, min_eq_left hAB]
      linarith
    · have hleft : (a : ℝ) < 1 - (t : ℝ) := lt_of_not_ge h₀
      have hright : 1 - (t : ℝ) < (b : ℝ) := lt_of_not_ge h₁
      have htB : 1 - (b : ℝ) < t := by linarith
      have htA : (t : ℝ) < 1 - (a : ℝ) := by linarith
      rw [max_eq_left (le_of_lt hleft), min_eq_left (le_of_lt hright),
        max_eq_left (le_of_lt htB), min_eq_left (le_of_lt htA)]



/-- The unit-interval involution preserves the open parameter interval. -/
theorem symm_mem_openParams_iff {t : I} :
    σ t ∈ openParams ↔ t ∈ openParams := by
  simp only [openParams, Set.mem_setOf_eq, unitInterval.coe_symm_eq]
  constructor <;> intro h <;> constructor <;>
    linarith [t.property.1, t.property.2]

/-- Helper toward Definition 1.1: reversing the parameterized edge and its
chord changes the sign of the winding test for the corresponding subarc. -/
theorem edgeSubarc_winding_reverse_iff {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a ≤ b) (q : Path (γ b) (γ a)) (w : ℂ) :
    HasWinding
      ((edgeSubarc γ.symm (σ b) (σ a) (unitInterval.symm_le_symm.2 hab)).trans
        (q.symm.cast (by simp [Path.symm]) (by simp [Path.symm]))) w 1 ↔
    HasWinding ((edgeSubarc γ a b hab).trans q) w (-1) := by
  let δ := edgeSubarc γ a b hab
  let δr := edgeSubarc γ.symm (σ b) (σ a)
    (unitInterval.symm_le_symm.2 hab)
  let qr : Path (γ.symm (σ a)) (γ.symm (σ b)) :=
    q.symm.cast (by simp [Path.symm]) (by simp [Path.symm])
  let Lr : Path (γ b) (γ b) := δ.symm.trans q.symm
  let Ls : Path (γ.symm (σ b)) (γ.symm (σ b)) := δr.trans qr
  have hδ : δ.symm = δr.cast (by simp [δr, Path.symm])
      (by simp [δr, Path.symm]) := by
    dsimp [δ, δr]
    simpa only [Path.symm_symm] using (edgeSubarc_symm γ a b hab)
  have hfun : ∀ t, Ls t = Lr t := by
    intro t
    dsimp [Ls, Lr]
    rw [Path.trans_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dif_pos ht]
      let r : I := ⟨2 * (t : ℝ), by
        constructor
        · exact mul_nonneg (by norm_num) t.property.1
        · nlinarith [ht, t.property.1]⟩
      have heq := congrArg (fun p : Path _ _ => p r) hδ
      simpa only [Path.cast_coe] using heq.symm
    · simp only [dif_neg ht]
      change qr ⟨2 * (t : ℝ) - 1, _⟩ = q.symm ⟨2 * (t : ℝ) - 1, _⟩
      simp only [qr, Path.cast_coe]
  have hwind : HasWinding Ls w 1 ↔ HasWinding Lr w 1 :=
    hasWinding_congr_fun Ls Lr w 1 hfun
  have hcycle := hasWinding_trans_symm_swap_iff δ q w 1
  constructor
  · intro h
    exact hcycle.symm.mp (hwind.mp h)
  · intro h
    exact hwind.mpr (hcycle.mp h)

/-- Helper toward Definition 1.1: the value of an edge subarc depends only on
its two parameter endpoints, not on proofs of their ordering. -/
theorem edgeSubarc_apply_param_congr {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) {a a' b b' : I} (ha : a = a')
    (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') (t : I) :
    edgeSubarc γ a b hab t = edgeSubarc γ a' b' hab' t := by
  subst a'
  subst b'
  rfl

/-- Helper toward Definition 1.1: a left-side witness on the reversed arc
produces the corresponding right-side witness on the original arc. -/
theorem leftAtOn_symm_to_rightAtOn {x y : ℂ} (F : Set ℂ)
    (γ : Path x y) (s s' : {t : I // t ∈ openParams})
    (hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1)
    (hside : LeftAtOn F γ.symm s') : RightAtOn F γ s := by
  rcases hside with ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩
  have hcomp' : (s'.1 : ℝ) = 1 - (s.1 : ℝ) := by linarith
  have hs' : s'.1 = σ s.1 := by
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq]
    exact hcomp'
  have haR : (a : ℝ) > 0 := by exact_mod_cast ha
  have hasR : (a : ℝ) < (s'.1 : ℝ) := by exact_mod_cast has
  have hsbR : (s'.1 : ℝ) < (b : ℝ) := by exact_mod_cast hsb
  have hbR : (b : ℝ) < 1 := by exact_mod_cast hb
  let a' : I := σ b
  let b' : I := σ a
  have ha' : 0 < a' := by
    change (0 : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith
  have has' : a' < s.1 := by
    change (a' : ℝ) < (s.1 : ℝ)
    dsimp [a']
    linarith
  have hsb' : s.1 < b' := by
    change (s.1 : ℝ) < (b' : ℝ)
    dsimp [b']
    linarith
  have hb' : b' < 1 := by
    change (b' : ℝ) < 1
    dsimp [b']
    linarith
  have hab : a ≤ b := le_of_lt (lt_trans has hsb)
  let q' : Path (γ b') (γ a') :=
    q.symm.cast (by simp [b', Path.symm]) (by simp [a', Path.symm])
  have hab' : a' ≤ b' := le_of_lt (lt_trans has' hsb')
  let qrev : Path (γ.symm (σ a')) (γ.symm (σ b')) :=
    q'.symm.cast (by simp [a', Path.symm]) (by simp [b', Path.symm])
  have hσa' : σ a' = b := by dsimp [a']; simp
  have hσb' : σ b' = a := by dsimp [b']; simp
  have hsrcFun : ∀ t,
      ((edgeSubarc γ.symm a b hab).trans q) t =
        ((edgeSubarc γ.symm (σ b') (σ a')
          (unitInterval.symm_le_symm.2 hab')).trans qrev) t := by
    intro t
    rw [Path.trans_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dif_pos ht]
      exact edgeSubarc_apply_param_congr γ.symm hσb'.symm hσa'.symm
        hab (unitInterval.symm_le_symm.2 hab') _
    · simp only [dif_neg ht]
      change q ⟨2 * (t : ℝ) - 1, _⟩ =
        q (σ (σ ⟨2 * (t : ℝ) - 1, _⟩))
      simp
  have hpoint : γ.symm s'.1 = γ s.1 := by
    rw [hs']
    simp [Path.symm]
  let targetLoop := (edgeSubarc γ a' b' hab').trans q'
  have hclosure : γ s.1 ∈ closure
      {w : ℂ | w ∈ F ∧ HasWinding targetLoop w (-1)} := by
    rw [← hpoint]
    have hsubset :
        {w : ℂ | w ∈ F ∧ HasWinding
          ((edgeSubarc γ.symm a b hab).trans q) w 1} ⊆
        {w : ℂ | w ∈ F ∧ HasWinding targetLoop w (-1)} := by
      intro w hw
      refine ⟨hw.1, ?_⟩
      have hsource : HasWinding
          ((edgeSubarc γ.symm (σ b') (σ a')
            (unitInterval.symm_le_symm.2 hab')).trans qrev) w 1 := by
        exact (hasWinding_congr_fun _ _ w 1 hsrcFun).mp hw.2
      exact (edgeSubarc_winding_reverse_iff γ a' b' hab' q' w).mp hsource
    exact closure_mono hsubset hcl
  have hq' : Function.Injective q' := by
    intro u v huv
    have hσ : σ u = σ v := hq (by
      simpa [q', Path.cast_coe, Path.symm] using huv)
    exact unitInterval.symm_bijective.injective hσ
  have hq'F : ∀ t : I, t ∈ openParams → q' t ∈ F := by
    intro t ht
    have hσt : σ t ∈ openParams := (symm_mem_openParams_iff).2 ht
    simpa [q', Path.cast_coe, Path.symm] using hqF (σ t) hσt
  exact ⟨a', b', ha', has', hsb', hb', q', hq', hq'F, hclosure⟩

/-- Helper toward Definition 1.1: a right-side witness on the original arc
produces the corresponding left-side witness on the reversed arc. -/
theorem rightAtOn_to_leftAtOn_symm {x y : ℂ} (F : Set ℂ)
    (γ : Path x y) (s s' : {t : I // t ∈ openParams})
    (hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1)
    (hside : RightAtOn F γ s) : LeftAtOn F γ.symm s' := by
  rcases hside with ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩
  have hcomp' : (s'.1 : ℝ) = 1 - (s.1 : ℝ) := by linarith
  have hs' : s'.1 = σ s.1 := by
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq]
    exact hcomp'
  have haR : (a : ℝ) > 0 := by exact_mod_cast ha
  have hasR : (a : ℝ) < (s.1 : ℝ) := by exact_mod_cast has
  have hsbR : (s.1 : ℝ) < (b : ℝ) := by exact_mod_cast hsb
  have hbR : (b : ℝ) < 1 := by exact_mod_cast hb
  let a' : I := σ b
  let b' : I := σ a
  have ha' : 0 < a' := by
    change (0 : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith
  have has' : a' < s'.1 := by
    change (a' : ℝ) < (s'.1 : ℝ)
    dsimp [a']
    linarith
  have hsb' : s'.1 < b' := by
    change (s'.1 : ℝ) < (b' : ℝ)
    dsimp [b']
    linarith
  have hb' : b' < 1 := by
    change (b' : ℝ) < 1
    dsimp [b']
    linarith
  have hab : a ≤ b := le_of_lt (lt_trans has hsb)
  let q' : Path (γ.symm b') (γ.symm a') :=
    q.symm.cast (by simp [b', Path.symm]) (by simp [a', Path.symm])
  have hab' : a' ≤ b' := le_of_lt (lt_trans has' hsb')
  let targetLoop := (edgeSubarc γ.symm a' b' hab').trans q'
  let helperLoop :=
    (edgeSubarc γ.symm (σ b) (σ a)
      (unitInterval.symm_le_symm.2 hab)).trans
      (q.symm.cast
        (by change γ (σ (σ a)) = γ a
            exact congrArg γ (unitInterval.symm_symm a))
        (by change γ (σ (σ b)) = γ b
            exact congrArg γ (unitInterval.symm_symm b)))
  have hloopfun : ∀ t, targetLoop t = helperLoop t := by
    intro t
    change ((edgeSubarc γ.symm a' b' hab').trans q') t =
      ((edgeSubarc γ.symm a' b'
        (unitInterval.symm_le_symm.2 hab)).trans
        (q.symm.cast _ _)) t
    rw [Path.trans_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dif_pos ht]
    · simp only [dif_neg ht]
      change q (σ ⟨2 * (t : ℝ) - 1, _⟩) =
        q (σ ⟨2 * (t : ℝ) - 1, _⟩)
      rfl
  have hpoint : γ s.1 = γ.symm s'.1 := by
    rw [hs']
    simp [Path.symm]
  let sourceLoop := (edgeSubarc γ a b hab).trans q
  have hsubset :
      {w : ℂ | w ∈ F ∧ HasWinding sourceLoop w (-1)} ⊆
        {w : ℂ | w ∈ F ∧ HasWinding targetLoop w 1} := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    have hhelper : HasWinding helperLoop w 1 := by
      exact (edgeSubarc_winding_reverse_iff γ a b hab q w).mpr hw.2
    exact (hasWinding_congr_fun targetLoop helperLoop w 1 hloopfun).mpr hhelper
  have hclosure : γ.symm s'.1 ∈ closure
      {w : ℂ | w ∈ F ∧ HasWinding targetLoop w 1} := by
    rw [← hpoint]
    exact closure_mono hsubset hcl
  have hq' : Function.Injective q' := by
    intro u v huv
    change q.symm u = q.symm v at huv
    change q (σ u) = q (σ v) at huv
    have hσ : σ u = σ v := hq huv
    exact unitInterval.symm_bijective.injective hσ
  have hq'F : ∀ t : I, t ∈ openParams → q' t ∈ F := by
    intro t ht
    have hσt : σ t ∈ openParams := (symm_mem_openParams_iff).2 ht
    change q.symm t ∈ F
    change q (σ t) ∈ F
    exact hqF (σ t) hσt
  exact ⟨a', b', ha', has', hsb', hb', q', hq', hq'F, hclosure⟩

/-- Helper toward Definition 1.1: reversing the stored edge parameterization
interchanges its left and right side predicates. -/
theorem leftAtOn_edge_reversal_iff {V E : Type*}
    (D : PlaneGraphDrawing V E) (F : D.Face) (e : E)
    (s s' : {t : I // t ∈ openParams})
    (hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1) :
    LeftAtOn F.val (D.arc e).symm s' ↔ RightAtOn F.val (D.arc e) s := by
  constructor
  · exact leftAtOn_symm_to_rightAtOn F (D.arc e) s s' hcomp
  · exact rightAtOn_to_leftAtOn_symm F (D.arc e) s s' hcomp

/-- Helper toward Definition 1.1: the right-to-left formulation of edge
reversal is the symmetric orientation of `leftAtOn_edge_reversal_iff`. -/
theorem rightAtOn_edge_reversal_iff {V E : Type*}
    (D : PlaneGraphDrawing V E) (F : D.Face) (e : E)
    (s s' : {t : I // t ∈ openParams})
    (hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1) :
    RightAtOn F.val (D.arc e) s ↔ LeftAtOn F.val (D.arc e).symm s' := by
  exact (leftAtOn_edge_reversal_iff D F e s s' hcomp).symm

end DirectedDistances.PlanarMap

end

