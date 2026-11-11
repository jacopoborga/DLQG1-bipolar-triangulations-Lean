/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder17

/-! Helper toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: an orientation-preserving homeomorphism
preserves the strict comparison of turns determined by three radial germs. -/
theorem orientationPreserving_ccwTurn_lt_iff_of_radial_segments
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (u v w u' v' w' : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg)
    (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'})
    (hsegmentsW : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * w} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * w'}) :
    ccwTurn u w < ccwTurn u v ↔ ccwTurn u' w' < ccwTurn u' v' := by
  rcases hsegmentsU with ⟨rU, sU, hrU, hsU, himageU⟩
  rcases hsegmentsV with ⟨rV, sV, hrV, hsV, himageV⟩
  rcases hsegmentsW with ⟨rW, sW, hrW, hsW, himageW⟩

  have argsNeOfSegments (a b a' b' : ℂ) (ra sa rb sb : ℝ)
      (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
      (hab : a.arg ≠ b.arg) (hsa : 0 < sa) (hsb : 0 < sb)
      (himageA : K '' {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ ra ∧
          z = (q : ℂ) * a} =
        {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ sa ∧ z = (q : ℂ) * a'})
      (himageB : K '' {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ rb ∧
          z = (q : ℂ) * b} =
        {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ sb ∧ z = (q : ℂ) * b'}) :
      a'.arg ≠ b'.arg := by
    intro hargs
    have hratio := (Complex.arg_eq_arg_iff ha' hb').mp hargs
    let c : ℝ := ‖b'‖ / ‖a'‖
    have hcpos : 0 < c := by
      dsimp [c]
      exact div_pos (norm_pos_iff.mpr hb') (norm_pos_iff.mpr ha')
    have hratio' : (c : ℂ) * a' = b' := by
      simpa [c] using hratio
    let lam : ℝ := min sa (c * sb) / 2
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    have hlamA : lam ≤ sa := by
      dsimp [lam]
      have hmin := min_le_left sa (c * sb)
      have hmin0 : 0 ≤ min sa (c * sb) := le_min (le_of_lt hsa)
        (le_of_lt (mul_pos hcpos hsb))
      nlinarith
    have hlamB : lam ≤ c * sb := by
      dsimp [lam]
      have hmin := min_le_right sa (c * sb)
      have hmin0 : 0 ≤ min sa (c * sb) := le_min (le_of_lt hsa)
        (le_of_lt (mul_pos hcpos hsb))
      nlinarith
    let mu : ℝ := lam / c
    have hmu : 0 < mu := div_pos hlam hcpos
    have hmuB : mu ≤ sb := by
      apply (div_le_iff₀ hcpos).2
      nlinarith [hlamB]
    have hmul : mu * c = lam := by
      dsimp [mu]
      field_simp [ne_of_gt hcpos]
    have hmulC : (mu : ℂ) * (c : ℂ) = (lam : ℂ) := by
      exact_mod_cast hmul
    let z : ℂ := (lam : ℂ) * a'
    have hzNe : z ≠ 0 := by
      dsimp [z]
      exact mul_ne_zero (by exact_mod_cast hlam.ne') ha'
    have hzA : z ∈ {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ sa ∧
        z = (q : ℂ) * a'} := by
      exact ⟨lam, hlam.le, hlamA, rfl⟩
    have hzB : z ∈ {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ sb ∧
        z = (q : ℂ) * b'} := by
      refine ⟨mu, hmu.le, hmuB, ?_⟩
      dsimp [z]
      calc
        (lam : ℂ) * a' = ((mu : ℂ) * (c : ℂ)) * a' := by rw [hmulC]
        _ = (mu : ℂ) * ((c : ℂ) * a') := by ring
        _ = (mu : ℂ) * b' := by rw [hratio']
    rw [← himageA] at hzA
    rw [← himageB] at hzB
    rcases hzA with ⟨x, hx, hxK⟩
    rcases hzB with ⟨y, hy, hyK⟩
    rcases hx with ⟨qa, hqa, hqar, hxq⟩
    rcases hy with ⟨qb, hqb, hqbr, hyq⟩
    have hxy : x = y := K.injective (hxK.trans hyK.symm)
    have hsource : (qa : ℂ) * a = (qb : ℂ) * b := by
      calc
        (qa : ℂ) * a = x := hxq.symm
        _ = y := hxy
        _ = (qb : ℂ) * b := hyq
    have hqaPos : 0 < qa := by
      by_contra hnot
      have hzero : qa = 0 := le_antisymm (le_of_not_gt hnot) hqa
      have hx0 : x = 0 := by rw [hxq, hzero]; simp
      apply hzNe
      calc
        z = K x := hxK.symm
        _ = K 0 := by rw [hx0]
        _ = 0 := hK0
    have hqbPos : 0 < qb := by
      by_contra hnot
      have hzero : qb = 0 := le_antisymm (le_of_not_gt hnot) hqb
      have hy0 : y = 0 := by rw [hyq, hzero]; simp
      apply hzNe
      calc
        z = K y := hyK.symm
        _ = K 0 := by rw [hy0]
        _ = 0 := hK0
    have harg := congrArg Complex.arg hsource
    rw [Complex.arg_real_mul a hqaPos, Complex.arg_real_mul b hqbPos] at harg
    exact hab harg

  have huv' : u'.arg ≠ v'.arg :=
    argsNeOfSegments u v u' v' rU sU rV sV hu hv hu' hv' huv hsU hsV
      himageU himageV
  have huw' : u'.arg ≠ w'.arg :=
    argsNeOfSegments u w u' w' rU sU rW sW hu hw hu' hw' huw hsU hsW
      himageU himageW
  have hvw' : v'.arg ≠ w'.arg :=
    argsNeOfSegments v w v' w' rV sV rW sW hv hw hv' hw' hvw hsV hsW
      himageV himageW

  obtain ⟨ρ, hρ, hρU, hρV, hρW, hKball⟩ :=
    d39_small_radius_for_three_image_germs K hK0 u v w u' v' w'
      rU rV rW sU sV sW hu hv hw hu' hv' hw' hrU hrV hrW hsU hsV hsW
  have hKballU : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < sU * ‖u'‖ := by
    intro z hz
    exact lt_of_lt_of_le (hKball z hz) (min_le_left _ _)
  have hKballV : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < sV * ‖v'‖ := by
    intro z hz
    exact lt_of_lt_of_le (hKball z hz)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hKballW : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < sW * ‖w'‖ := by
    intro z hz
    exact lt_of_lt_of_le (hKball z hz)
      (le_trans (min_le_right _ _) (min_le_right _ _))

  obtain ⟨α, hmissU, hmissV, hmissW, hHitU, hHitV, hHitW⟩ :=
    d39_exists_base_angle_with_three_interior_ray_hits u v w hu hv hw huv huw hvw
  obtain ⟨φ, hφ, hinc⟩ :=
    d39_oriented_image_rotatedCirclePath_has_lift_increment hK hρ
  let L : C(unitInterval, ℝ) :=
    ⟨fun t => (φ t).im, Complex.continuous_im.comp φ.continuous⟩
  let period : ℝ := 2 * Real.pi
  let L0 : ℝ := L 0
  have hperiod : 0 < period := by dsimp [period]; positivity
  have hperiodEq : period = 2 * Real.pi := rfl
  have hend : L 1 = L 0 + period := by
    dsimp [L, period]
    linarith [hinc]

  have hAvoidEndpointU := d39_imageRotatedCirclePath_endpoints_avoid_image_germ
    K u u' rU sU ρ α hu hρ himageU hmissU
  have hAvoidEndpointV := d39_imageRotatedCirclePath_endpoints_avoid_image_germ
    K v v' rV sV ρ α hv hρ himageV hmissV
  have hAvoidEndpointW := d39_imageRotatedCirclePath_endpoints_avoid_image_germ
    K w w' rW sW ρ α hw hρ himageW hmissW
  have hUniqueU0 := d39_image_lift_ray_argument_has_unique_time_all
    K hK0 u u' rU sU ρ α hu hu' hρ hρU hKballU himageU hmissU φ hφ
      hAvoidEndpointU hHitU
  have hUniqueV0 := d39_image_lift_ray_argument_has_unique_time_all
    K hK0 v v' rV sV ρ α hv hv' hρ hρV hKballV himageV hmissV φ hφ
      hAvoidEndpointV hHitV
  have hUniqueW0 := d39_image_lift_ray_argument_has_unique_time_all
    K hK0 w w' rW sW ρ α hw hw' hρ hρW hKballW himageW hmissW φ hφ
      hAvoidEndpointW hHitW
  have hUniqueU : ∀ t : unitInterval,
      (∃ k : ℤ, L t = u'.arg + period * (k : ℝ)) ↔
        (t : ℝ) = d39RotatedCircleRayHitTime α u := by
    intro t
    simpa [L, period] using hUniqueU0 t
  have hUniqueV : ∀ t : unitInterval,
      (∃ k : ℤ, L t = v'.arg + period * (k : ℝ)) ↔
        (t : ℝ) = d39RotatedCircleRayHitTime α v := by
    intro t
    simpa [L, period] using hUniqueV0 t
  have hUniqueW : ∀ t : unitInterval,
      (∃ k : ℤ, L t = w'.arg + period * (k : ℝ)) ↔
        (t : ℝ) = d39RotatedCircleRayHitTime α w := by
    intro t
    simpa [L, period] using hUniqueW0 t

  have havoidU : ∀ k : ℤ, L 0 ≠ u'.arg + period * (k : ℝ) := by
    intro k hk
    have htime := (hUniqueU (0 : unitInterval)).1 ⟨k, hk⟩
    have hzero : (0 : ℝ) = d39RotatedCircleRayHitTime α u := by simpa using htime
    exact (ne_of_gt hHitU.1) hzero.symm
  have havoidV : ∀ k : ℤ, L 0 ≠ v'.arg + period * (k : ℝ) := by
    intro k hk
    have htime := (hUniqueV (0 : unitInterval)).1 ⟨k, hk⟩
    have hzero : (0 : ℝ) = d39RotatedCircleRayHitTime α v := by simpa using htime
    exact (ne_of_gt hHitV.1) hzero.symm
  have havoidW : ∀ k : ℤ, L 0 ≠ w'.arg + period * (k : ℝ) := by
    intro k hk
    have htime := (hUniqueW (0 : unitInterval)).1 ⟨k, hk⟩
    have hzero : (0 : ℝ) = d39RotatedCircleRayHitTime α w := by simpa using htime
    exact (ne_of_gt hHitW.1) hzero.symm

  obtain ⟨repU, hrepU, hUlo, hUhi⟩ :=
    d39_exists_lattice_representative_in_open_period u'.arg L0 period hperiod havoidU
  obtain ⟨repV, hrepV, hVlo, hVhi⟩ :=
    d39_exists_lattice_representative_in_open_period v'.arg L0 period hperiod havoidV
  obtain ⟨repW, hrepW, hWlo, hWhi⟩ :=
    d39_exists_lattice_representative_in_open_period w'.arg L0 period hperiod havoidW
  have hwindowU : L 0 < repU ∧ repU < L 0 + period := by simpa [L0] using And.intro hUlo hUhi
  have hwindowV : L 0 < repV ∧ repV < L 0 + period := by simpa [L0] using And.intro hVlo hVhi
  have hwindowW : L 0 < repW ∧ repW < L 0 + period := by simpa [L0] using And.intro hWlo hWhi

  let tu : unitInterval := ⟨d39RotatedCircleRayHitTime α u,
    ⟨hHitU.1.le, hHitU.2.le⟩⟩
  let tv : unitInterval := ⟨d39RotatedCircleRayHitTime α v,
    ⟨hHitV.1.le, hHitV.2.le⟩⟩
  let tw : unitInterval := ⟨d39RotatedCircleRayHitTime α w,
    ⟨hHitW.1.le, hHitW.2.le⟩⟩

  have adaptUnique (a : ℂ) (hit : ℝ) (tHit : unitInterval)
      (hval : (tHit : ℝ) = hit)
      (hreal : ∀ t : unitInterval,
        (∃ k : ℤ, L t = a.arg + period * (k : ℝ)) ↔ (t : ℝ) = hit) :
      ∀ t : unitInterval,
        (∃ k : ℤ, L t = a.arg + period * (k : ℝ)) ↔ t = tHit := by
    intro t
    constructor
    · intro h
      apply Subtype.ext
      exact (hreal t).1 h |>.trans hval.symm
    · intro h
      apply (hreal t).2
      calc
        (t : ℝ) = (tHit : ℝ) := congrArg (fun x : unitInterval => (x : ℝ)) h
        _ = hit := hval
  have hUniqueUHit := adaptUnique u' _ tu rfl hUniqueU
  have hUniqueVHit := adaptUnique v' _ tv rfl hUniqueV
  have hUniqueWHit := adaptUnique w' _ tw rfl hUniqueW

  have horderUW := d39_image_lift_lattice_hit_times_order_iff
    L u'.arg w'.arg repU repW period tu tw hperiod hrepU hrepW
    ⟨hwindowU.1, hwindowU.2, hwindowW.1, hwindowW.2⟩ hend hUniqueUHit hUniqueWHit
  have horderUV := d39_image_lift_lattice_hit_times_order_iff
    L u'.arg v'.arg repU repV period tu tv hperiod hrepU hrepV
    ⟨hwindowU.1, hwindowU.2, hwindowV.1, hwindowV.2⟩ hend hUniqueUHit hUniqueVHit
  have horderWU := d39_image_lift_lattice_hit_times_order_iff
    L w'.arg u'.arg repW repU period tw tu hperiod hrepW hrepU
    ⟨hwindowW.1, hwindowW.2, hwindowU.1, hwindowU.2⟩ hend hUniqueWHit hUniqueUHit
  have horderWV := d39_image_lift_lattice_hit_times_order_iff
    L w'.arg v'.arg repW repV period tw tv hperiod hrepW hrepV
    ⟨hwindowW.1, hwindowW.2, hwindowV.1, hwindowV.2⟩ hend hUniqueWHit hUniqueVHit
  have horderVU := d39_image_lift_lattice_hit_times_order_iff
    L v'.arg u'.arg repV repU period tv tu hperiod hrepV hrepU
    ⟨hwindowV.1, hwindowV.2, hwindowU.1, hwindowU.2⟩ hend hUniqueVHit hUniqueUHit
  have horderVW := d39_image_lift_lattice_hit_times_order_iff
    L v'.arg w'.arg repV repW period tv tw hperiod hrepV hrepW
    ⟨hwindowV.1, hwindowV.2, hwindowW.1, hwindowW.2⟩ hend hUniqueVHit hUniqueWHit

  let xU : ℝ := (repU - L0) / period
  let xV : ℝ := (repV - L0) / period
  let xW : ℝ := (repW - L0) / period
  have repOrderCoord (a b : ℝ) : a < b ↔ (a - L0) / period < (b - L0) / period := by
    constructor
    · intro hab
      apply div_lt_div_of_pos_right
      · linarith
      · exact hperiod
    · intro hab
      have hmul := mul_lt_mul_of_pos_right hab hperiod
      field_simp [ne_of_gt hperiod] at hmul
      linarith
  have htuW : (tu : ℝ) < (tw : ℝ) ↔ xU < xW := by
    simpa [xU, xW] using horderUW.trans (repOrderCoord repU repW)
  have htuV : (tu : ℝ) < (tv : ℝ) ↔ xU < xV := by
    simpa [xU, xV] using horderUV.trans (repOrderCoord repU repV)
  have htwU : (tw : ℝ) < (tu : ℝ) ↔ xW < xU := by
    simpa [xW, xU] using horderWU.trans (repOrderCoord repW repU)
  have htwV : (tw : ℝ) < (tv : ℝ) ↔ xW < xV := by
    simpa [xW, xV] using horderWV.trans (repOrderCoord repW repV)
  have htvU : (tv : ℝ) < (tu : ℝ) ↔ xV < xU := by
    simpa [xV, xU] using horderVU.trans (repOrderCoord repV repU)
  have htvW : (tv : ℝ) < (tw : ℝ) ↔ xV < xW := by
    simpa [xV, xW] using horderVW.trans (repOrderCoord repV repW)

  have hcyclic : d39CyclicOrder (tu : ℝ) (tw : ℝ) (tv : ℝ) ↔
      d39CyclicOrder xU xW xV :=
    d39CyclicOrder_iff_of_pairwise_lt_iff _ _ _ _ _ _ htuW htuV htwU htwV htvU htvW
  have hsource := d39_source_ccwTurn_lt_iff_cyclicOrder α u v w
    hu hv hw huv huw hvw hmissU hmissV hmissW
  have himage := d39_image_ccwTurn_lt_iff_cyclicOrder
    u' v' w' L hu' hv' hw' repU repV repW tu tv tw period L0
    hperiod hperiodEq hend huv' huw' hvw' hrepU hrepV hrepW
    ⟨hwindowU.1, hwindowU.2, hwindowV.1, hwindowV.2, hwindowW.1, hwindowW.2⟩
    hUniqueUHit hUniqueVHit hUniqueWHit
  have hcyclic' : d39CyclicOrder (d39RotatedCircleRayHitTime α u)
      (d39RotatedCircleRayHitTime α w) (d39RotatedCircleRayHitTime α v) ↔
        d39CyclicOrder xU xW xV := by
    simpa [tu, tw, tv] using hcyclic
  exact hsource.trans (hcyclic'.trans himage.symm)

end DirectedDistances.PlanarMap

end
