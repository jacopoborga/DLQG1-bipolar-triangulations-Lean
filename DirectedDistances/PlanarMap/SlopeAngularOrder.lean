module

public import DirectedDistances.PlanarMap.PlaneRealization






public section
namespace DirectedDistances.PlanarMap

open Real Set




@[expose] def CcwBetween (a b c : ℂ) : Prop :=
  ccwTurn a b < ccwTurn a c



theorem ccwTurn_pos (a b : ℂ) : 0 < ccwTurn a b := by
  unfold ccwTurn
  split_ifs with h
  · exact sub_pos.mpr h
  · have ha := Complex.arg_mem_Ioc a
    have hb := Complex.arg_mem_Ioc b
    change -Real.pi < Complex.arg a ∧ Complex.arg a ≤ Real.pi at ha
    change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
    linarith [Real.pi_pos]



theorem ccwTurn_le_two_pi (a b : ℂ) : ccwTurn a b ≤ 2 * Real.pi := by
  unfold ccwTurn
  split_ifs with h
  · have ha := Complex.arg_mem_Ioc a
    have hb := Complex.arg_mem_Ioc b
    change -Real.pi < Complex.arg a ∧ Complex.arg a ≤ Real.pi at ha
    change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
    linarith [Real.pi_pos]
  · have hba : Complex.arg b ≤ Complex.arg a := le_of_not_gt h
    linarith



theorem ccwTurn_eq_two_pi_iff (a b : ℂ) :
    ccwTurn a b = 2 * Real.pi ↔ Complex.arg a = Complex.arg b := by
  by_cases hab : Complex.arg a < Complex.arg b
  · rw [show ccwTurn a b = Complex.arg b - Complex.arg a from by
      simp [ccwTurn, hab]]
    have ha := Complex.arg_mem_Ioc a
    have hb := Complex.arg_mem_Ioc b
    change -Real.pi < Complex.arg a ∧ Complex.arg a ≤ Real.pi at ha
    change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
    constructor
    · intro he
      linarith
    · intro he
      exfalso
      linarith
  · rw [show ccwTurn a b = Complex.arg b - Complex.arg a + 2 * Real.pi from by
      simp [ccwTurn, hab]]
    constructor
    · intro he
      linarith
    · intro he
      simp [he]



theorem ccwTurn_add_reverse (a b : ℂ) (h : Complex.arg a ≠ Complex.arg b) :
    ccwTurn a b + ccwTurn b a = 2 * Real.pi := by
  by_cases hab : Complex.arg a < Complex.arg b
  · have hba : ¬ Complex.arg b < Complex.arg a := not_lt_of_ge hab.le
    simp [ccwTurn, hab, hba]
    ring
  · have hba : Complex.arg b < Complex.arg a := lt_of_le_of_ne
      (le_of_not_gt hab) (Ne.symm h)
    have hnot : ¬ Complex.arg a < Complex.arg b := hab
    simp [ccwTurn, hba, hnot]
    ring



theorem ccwTurn_eq_turn_of_arg_lt {a b : ℂ} (h : Complex.arg a < Complex.arg b) :
    ccwTurn a b = Complex.arg b - Complex.arg a := by
  simp [ccwTurn, h]



theorem ccwBetween_iff (a b c : ℂ) :
    ccwTurn a b < ccwTurn a c ↔ CcwBetween a b c := Iff.rfl



theorem east_arg_eq_arctan {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hlow : -(Real.pi / 2) < Complex.arg z := abs_lt.mp harg |>.1
  have hup : Complex.arg z < Real.pi / 2 := abs_lt.mp harg |>.2
  rw [← Real.arctan_tan hlow hup, Complex.tan_arg]



theorem east_arg_lt_iff_slope_lt {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.arg u < Complex.arg v ↔ u.im / u.re < v.im / v.re := by
  rw [east_arg_eq_arctan hu, east_arg_eq_arctan hv]
  exact Real.arctan_lt_arctan_iff



theorem west_slope_order {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0) :
    Complex.arg (-u) < Complex.arg (-v) ↔ u.im / u.re < v.im / v.re := by
  simpa only [Complex.neg_re, Complex.neg_im, neg_div_neg_eq] using
    (east_arg_lt_iff_slope_lt (u := -u) (v := -v)
      (neg_pos.mpr hu) (neg_pos.mpr hv))



theorem west_arg_eq_arctan {z : ℂ} (hz : z.re < 0) :
    Complex.arg (-z) = Real.arctan (z.im / z.re) := by
  simpa only [Complex.neg_re, Complex.neg_im, neg_div_neg_eq] using
    (east_arg_eq_arctan (z := -z) (neg_pos.mpr hz))



theorem west_theta_pos {z : ℂ} (hz : z.re < 0) (him : z.im < 0) :
    0 < Complex.arg (-z) := by
  rw [west_arg_eq_arctan hz]
  exact Real.arctan_pos.mpr (div_pos_of_neg_of_neg him hz)



theorem west_theta_nonpos {z : ℂ} (hz : z.re < 0) (him : 0 ≤ z.im) :
    Complex.arg (-z) ≤ 0 := by
  rw [west_arg_eq_arctan hz]
  exact Real.arctan_le_zero.mpr (div_nonpos_of_nonneg_of_nonpos him hz.le)



theorem west_arg_normalized {z : ℂ} (hz : z.re < 0) :
    Complex.arg z = if z.im < 0 then Complex.arg (-z) - Real.pi
      else Real.pi + Complex.arg (-z) := by
  by_cases him : z.im < 0
  · have hneg : 0 < (-z).im := by simpa using neg_pos.mpr him
    have harg : Complex.arg z = Complex.arg (-z) - Real.pi := by
      simpa only [neg_neg] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hneg
    simp [him, harg]
  · have himnonneg : 0 ≤ z.im := le_of_not_gt him
    by_cases hzero : z.im = 0
    · have harg : Complex.arg z = Real.pi :=
        Complex.arg_eq_pi_iff.mpr ⟨hz, hzero⟩
      have hargneg : Complex.arg (-z) = 0 := by
        apply Complex.arg_eq_zero_iff.mpr
        constructor
        · exact (neg_pos.mpr hz).le
        · simpa using hzero
      simp [him, harg, hargneg]
    · have himpos : 0 < z.im := lt_of_le_of_ne himnonneg (Ne.symm hzero)
      have hneg : (-z).im < 0 := by simpa using neg_neg_of_pos himpos
      have harg : Complex.arg z = Complex.arg (-z) + Real.pi := by
        simpa [add_comm] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hneg
      simp [him, harg]
      ring



theorem west_west_turn_formula {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0)
    (hs : u.im / u.re < v.im / v.re) :
    ccwTurn u v = Complex.arg (-v) - Complex.arg (-u) := by
  have htheta := (west_slope_order hu hv).2 hs
  have huarg := Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < (-u).re by simpa using neg_pos.mpr hu))
  have hvarg := Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < (-v).re by simpa using neg_pos.mpr hv))
  by_cases himu : u.im < 0
  · by_cases himv : v.im < 0
    · have hraw : Complex.arg u < Complex.arg v := by
        rw [west_arg_normalized hu, west_arg_normalized hv]
        simp [himu, himv]
        exact htheta
      rw [ccwTurn_eq_turn_of_arg_lt hraw, west_arg_normalized hu,
        west_arg_normalized hv]
      rw [ite_eq_left himu, ite_eq_left himv]
      ring
    · have hposu := west_theta_pos hu himu
      have hnonposv := west_theta_nonpos hv (le_of_not_gt himv)
      linarith
  · by_cases himv : v.im < 0
    · have hunonpos := west_theta_nonpos hu (le_of_not_gt himu)
      have hvpos := west_theta_pos hv himv
      have hargu := west_arg_normalized hu
      have hargv := west_arg_normalized hv
      have hraw : Complex.arg v < Complex.arg u := by
        rw [hargu, hargv]
        simp [himu, himv]
        have huupper := (abs_lt.mp huarg).2
        have hulower := (abs_lt.mp huarg).1
        have hvupper := (abs_lt.mp hvarg).2
        linarith [hulower, huupper, hvupper]
      have hturn : ccwTurn u v = Complex.arg v - Complex.arg u + 2 * Real.pi := by
        simp [ccwTurn, not_lt.mpr hraw.le]
      rw [hturn, hargu, hargv]
      rw [ite_eq_right himu, ite_eq_left himv]
      ring
    · have htheta' := htheta
      have hargu := west_arg_normalized hu
      have hargv := west_arg_normalized hv
      have hraw : Complex.arg u < Complex.arg v := by
        rw [hargu, hargv]
        simp [himu, himv]
        exact htheta
      rw [ccwTurn_eq_turn_of_arg_lt hraw, hargu, hargv]
      rw [ite_eq_right himu, ite_eq_right himv]
      ring



theorem west_east_turn_formula {u v : ℂ} (hu : u.re < 0) (hv : 0 < v.re) :
    ccwTurn u v = Real.pi + Complex.arg v - Complex.arg (-u) := by
  have huarg := Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < (-u).re by simpa using neg_pos.mpr hu))
  have hvarg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  by_cases him : u.im < 0
  · have huθ := west_theta_pos hu him
    have harg : Complex.arg u < Complex.arg v := by
      rw [west_arg_normalized hu]
      simp [him]
      linarith [(abs_lt.mp huarg).2, (abs_lt.mp hvarg).1]
    rw [ccwTurn_eq_turn_of_arg_lt harg]
    rw [west_arg_normalized hu]
    rw [ite_eq_left him]
    ring
  · have huθ := west_theta_nonpos hu (le_of_not_gt him)
    have harg : Complex.arg v < Complex.arg u := by
      rw [west_arg_normalized hu]
      simp [him]
      linarith [(abs_lt.mp huarg).1, (abs_lt.mp hvarg).2]
    have hturn : ccwTurn u v = Complex.arg v - Complex.arg u + 2 * Real.pi := by
      simp [ccwTurn, not_lt.mpr harg.le]
    rw [hturn, west_arg_normalized hu]
    rw [ite_eq_right him]
    ring





theorem west_insert_topmost_predecessor {D : Type*} (star : Set D)
    (dir : D → ℂ) (d x : D) (hfin : star.Finite)
    (hnonvertical : ∀ f ∈ star, (dir f).re ≠ 0)
    (hd : d ∈ star) (hfresh : x ∉ star)
    (hdWest : (dir d).re < 0) (hxWest : (dir x).re < 0)
    (hdmin : ∀ f ∈ star, (dir f).re < 0 →
      f = d ∨ (dir d).im / (dir d).re < (dir f).im / (dir f).re)
    (hnew : (dir x).im / (dir x).re < (dir d).im / (dir d).re) :
    CcwSuccessor (insert x star) dir x d := by
  classical
  have hxmem : x ∈ insert x star := by simp
  have hne : d ≠ x := by intro h; subst x; exact hfresh hd
  refine ⟨hfin.insert x, hxmem, Set.mem_insert_of_mem _ hd,
    Or.inr ⟨hne, ?_⟩⟩
  intro f hf hfx
  rcases Set.mem_insert_iff.mp hf with hfxeq | hfstar
  · exact (hfx hfxeq).elim
  · by_cases hfd : f = d
    · subst f
      exact le_rfl
    · by_cases hpos : 0 < (dir f).re
      · rw [west_west_turn_formula hxWest hdWest hnew,
          west_east_turn_formula hxWest hpos]
        have htheta := Complex.abs_arg_lt_pi_div_two_iff.mpr
          (Or.inl (show 0 < (-dir d).re by simpa using neg_pos.mpr hdWest))
        have hfarg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
        linarith [Real.pi_pos, (abs_lt.mp htheta).2, (abs_lt.mp hfarg).1]
      · have hneg : (dir f).re < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpos) (hnonvertical f hfstar)
        have hslopeOr := hdmin f hfstar hneg
        have hslope : (dir d).im / (dir d).re < (dir f).im / (dir f).re := by
          rcases hslopeOr with rfl | hs
          · exact (hfd rfl).elim
          · exact hs
        have hxf := west_west_turn_formula hxWest hneg (lt_trans hnew hslope)
        have hxd := west_west_turn_formula hxWest hdWest hnew
        rw [hxd, hxf]
        exact sub_le_sub_right ((west_slope_order hdWest hneg).2 hslope).le
          (Complex.arg (-dir x))


theorem west_arg_lt_lower {z : ℂ} (hz : z.re < 0) (him : z.im < 0) :
    Complex.arg z < -(Real.pi / 2) := by
  have hnot : ¬ (-(Real.pi / 2) ≤ Complex.arg z) := by
    rw [Complex.neg_pi_div_two_le_arg_iff]
    simp [hz, him]
  exact lt_of_not_ge hnot



theorem west_arg_gt_upper {z : ℂ} (hz : z.re < 0) (him : 0 ≤ z.im) :
    Real.pi / 2 < Complex.arg z := by
  have hnot : ¬ Complex.arg z ≤ Real.pi / 2 := by
    rw [Complex.arg_le_pi_div_two_iff]
    simp [hz, him]
  exact lt_of_not_ge hnot



theorem east_west_turn_formula {u w : ℂ} (hu : 0 < u.re) (hw : w.re < 0) :
    ccwTurn u w = Real.pi + Complex.arg (-w) - Complex.arg u := by
  have huarg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hzre : 0 < (-w).re := by simpa using neg_pos.mpr hw
  have hzarg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  by_cases him : (-w).im < 0
  · have hn : Complex.arg w = Complex.arg (-w) + Real.pi := by
      simpa using Complex.arg_neg_eq_arg_add_pi_of_im_neg him
    have hlt : Complex.arg u < Complex.arg w := by
      rw [hn]
      linarith [(abs_lt.mp huarg).2, (abs_lt.mp hzarg).1, Real.pi_pos]
    rw [ccwTurn_eq_turn_of_arg_lt hlt, hn]
    ring
  · by_cases hzero : (-w).im = 0
    · have hzarg0 : Complex.arg (-w) = 0 :=
        Complex.arg_eq_zero_iff.mpr ⟨hzre.le, hzero⟩
      have hn : Complex.arg w = Real.pi := by
        apply Complex.arg_eq_pi_iff.mpr
        refine ⟨hw, ?_⟩
        have himw : w.im = 0 := by simpa using hzero
        exact himw
      have hlt : Complex.arg u < Complex.arg w := by
        rw [hn]
        linarith [(abs_lt.mp huarg).2, Real.pi_pos]
      rw [ccwTurn_eq_turn_of_arg_lt hlt, hn, hzarg0]
      ring
    · have himpos : 0 < (-w).im := lt_of_le_of_ne (le_of_not_gt him) (Ne.symm hzero)
      have hn : Complex.arg w = Complex.arg (-w) - Real.pi :=
        by simpa only [neg_neg] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos himpos
      have hlt : Complex.arg w < Complex.arg u := by
        rw [hn]
        linarith [(abs_lt.mp hzarg).2, (abs_lt.mp huarg).1, Real.pi_pos]
      have hwrap : ccwTurn u w = Complex.arg w - Complex.arg u + 2 * Real.pi := by
        simp [ccwTurn, not_lt.mpr (le_of_lt hlt)]
      rw [hwrap, hn]
      ring



theorem east_west_turn_lt_iff_slope_lt {u v w : ℂ} (hu : 0 < u.re)
    (hv : v.re < 0) (hw : w.re < 0) :
    ccwTurn u v < ccwTurn u w ↔ v.im / v.re < w.im / w.re := by
  rw [east_west_turn_formula hu hv, east_west_turn_formula hu hw]
  have hs := west_slope_order hv hw
  constructor
  · intro h
    exact hs.mp (by
      have : Complex.arg (-v) < Complex.arg (-w) := by linarith
      exact this)
  · intro h
    have h' := hs.mpr h
    linarith



theorem east_west_arg_gap {u v : ℂ} (hu : 0 < u.re) (hv : v.re < 0) :
    Complex.arg u < Complex.arg v ∨ Complex.arg v < Complex.arg u := by
  have hu' := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  by_cases him : v.im < 0
  · have hv' := west_arg_lt_lower hv him
    exact Or.inr (lt_trans hv' (abs_lt.mp hu').1)
  · have hv' := west_arg_gt_upper hv (le_of_not_gt him)
    exact Or.inl ((abs_lt.mp hu').2.trans hv')



theorem east_to_west_ccwTurn_lt_two_pi {u v : ℂ} (hu : 0 < u.re)
    (hv : v.re < 0) : 0 < ccwTurn u v ∧ ccwTurn u v < 2 * Real.pi := by
  refine ⟨ccwTurn_pos u v, ?_⟩
  rcases lt_or_eq_of_le (ccwTurn_le_two_pi u v) with hlt | heq
  · exact hlt
  · have heqarg := (ccwTurn_eq_two_pi_iff u v).mp heq
    rcases east_west_arg_gap hu hv with h | h
    · exact False.elim ((ne_of_lt h) heqarg)
    · exact False.elim ((ne_of_gt h) heqarg)



theorem east_pair_turn_before_west {u v w : ℂ} (hu : 0 < u.re)
    (hv : 0 < v.re) (hw : w.re < 0)
    (hs : u.im / u.re < v.im / v.re) :
    ccwTurn u v < ccwTurn u w := by
  have hau := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hav := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hau1 := (abs_lt.mp hau).1
  have hau2 := (abs_lt.mp hau).2
  have hav1 := (abs_lt.mp hav).1
  have hav2 := (abs_lt.mp hav).2
  have huv : Complex.arg u < Complex.arg v :=
    east_arg_lt_iff_slope_lt hu hv |>.2 hs
  by_cases him : w.im < 0
  · have hwl := west_arg_lt_lower hw him
    have hturnuv : ccwTurn u v = Complex.arg v - Complex.arg u :=
      ccwTurn_eq_turn_of_arg_lt huv
    have hturnuw : ccwTurn u w = Complex.arg w - Complex.arg u + 2 * Real.pi := by
      have hwu : Complex.arg w < Complex.arg u := hwl.trans hau1
      simp [ccwTurn, not_lt.mpr hwu.le]
    rw [hturnuv, hturnuw]
    have hwpi := (Complex.arg_mem_Ioc w).1
    have hvpi := (Complex.arg_mem_Ioc v).2
    linarith [Real.pi_pos]
  · have hwg := west_arg_gt_upper hw (le_of_not_gt him)
    have huvW : Complex.arg v < Complex.arg w := hav2.trans hwg
    rw [ccwTurn_eq_turn_of_arg_lt huv, ccwTurn_eq_turn_of_arg_lt (huv.trans huvW)]
    linarith



theorem ccwTurn_left_injective {a b c : ℂ}
    (h : ccwTurn a b = ccwTurn a c) : Complex.arg b = Complex.arg c := by
  by_cases hab : Complex.arg a < Complex.arg b <;>
    by_cases hac : Complex.arg a < Complex.arg c
  · unfold ccwTurn at h
    simp [hab, hac] at h
    linarith
  · have hb := Complex.arg_mem_Ioc b
    have hc := Complex.arg_mem_Ioc c
    change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
    change -Real.pi < Complex.arg c ∧ Complex.arg c ≤ Real.pi at hc
    unfold ccwTurn at h
    simp [hab, hac] at h
    exfalso
    linarith
  · have hb := Complex.arg_mem_Ioc b
    have hc := Complex.arg_mem_Ioc c
    change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
    change -Real.pi < Complex.arg c ∧ Complex.arg c ≤ Real.pi at hc
    unfold ccwTurn at h
    simp [hab, hac] at h
    exfalso
    linarith
  · unfold ccwTurn at h
    simp [hab, hac] at h
    linarith



theorem ccwTurn_comp_add {a b c : ℂ}
    (h : ccwTurn a b < ccwTurn a c) :
    ccwTurn a b + ccwTurn b c = ccwTurn a c := by
  have ha := Complex.arg_mem_Ioc a
  have hb := Complex.arg_mem_Ioc b
  have hc := Complex.arg_mem_Ioc c
  change -Real.pi < Complex.arg a ∧ Complex.arg a ≤ Real.pi at ha
  change -Real.pi < Complex.arg b ∧ Complex.arg b ≤ Real.pi at hb
  change -Real.pi < Complex.arg c ∧ Complex.arg c ≤ Real.pi at hc
  by_cases hab : Complex.arg a < Complex.arg b <;>
    by_cases hac : Complex.arg a < Complex.arg c <;>
    by_cases hbc : Complex.arg b < Complex.arg c <;>
    simp [ccwTurn, hab, hac, hbc] at h ⊢ <;>
    linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, Real.pi_pos]



theorem ccwSuccessor_iff_no_between {D : Type*} (star : Set D)
    (dir : D → ℂ) (d e : D) (hfin : star.Finite) (hd : d ∈ star)
    : CcwSuccessor star dir d e ↔
      (e = d ∧ star = {d}) ∨
        (e ≠ d ∧ e ∈ star ∧ ∀ f ∈ star, f ≠ d → f ≠ e →
          ¬ CcwBetween (dir d) (dir f) (dir e)) := by
  unfold CcwSuccessor CcwBetween
  constructor
  · rintro ⟨_, _, he, hmin⟩
    rcases hmin with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · refine Or.inr ⟨hne, he, ?_⟩
      intro f hf hfd hfe hbetween
      exact (not_lt_of_ge (hmin f hf hfd)) hbetween
  · rintro (⟨rfl, hs⟩ | ⟨hne, he, hno⟩)
    · exact ⟨hfin, hd, by simp [hs], Or.inl ⟨rfl, hs⟩⟩
    · refine ⟨hfin, hd, he, Or.inr ⟨hne, ?_⟩⟩
      intro f hf hfd
      by_contra hgt
      have hlt : ccwTurn (dir d) (dir f) < ccwTurn (dir d) (dir e) := not_le.mp hgt
      by_cases hfe : f = e
      · subst f
        exact (lt_irrefl _ hlt)
      · exact hno f hf hfd hfe hlt




theorem ccwSuccessor_insert_preserve {D : Type*} (star : Set D)
    (dir : D → ℂ) (f g x : D) (hfin : star.Finite)
    (hargs : ∀ a ∈ insert x star, ∀ b ∈ insert x star, a ≠ b →
      Complex.arg (dir a) ≠ Complex.arg (dir b))
    (hold : CcwSuccessor star dir f g) (hfresh : x ∉ star)
    (houtside : ¬ CcwBetween (dir f) (dir x) (dir g)) :
    CcwSuccessor (insert x star) dir f g := by
  have hf : f ∈ star := by rcases hold with ⟨_, hf, _, _⟩; exact hf
  have hg : g ∈ star := by rcases hold with ⟨_, _, hg, _⟩; exact hg
  have hchar := (ccwSuccessor_iff_no_between star dir f g hfin hf).mp hold
  rcases hold with ⟨_, _, _, hcase⟩
  rcases hcase with hsingle | ⟨hfg, _⟩
  · have hfx : f ≠ x := by
      intro h
      exact hfresh (h ▸ hf)
    have harg := hargs f (Set.mem_insert_of_mem x hf) x (by simp) hfx
    have hfull : ccwTurn (dir f) (dir f) = 2 * Real.pi :=
      (ccwTurn_eq_two_pi_iff _ _).2 rfl
    have hxle := ccwTurn_le_two_pi (dir f) (dir x)
    have hxge : 2 * Real.pi ≤ ccwTurn (dir f) (dir x) := by
      have hout := houtside
      rw [CcwBetween, hsingle.1, hfull] at hout
      exact le_of_not_gt hout
    have hxfull : ccwTurn (dir f) (dir x) = 2 * Real.pi := le_antisymm hxle hxge
    exact False.elim (harg ((ccwTurn_eq_two_pi_iff _ _).mp hxfull))
  · have hno : ∀ z ∈ star, z ≠ f → z ≠ g →
        ¬ CcwBetween (dir f) (dir z) (dir g) := by
      rcases hchar with hsingle | ⟨_, _, hno⟩
      · exact False.elim (hfg hsingle.1)
      · exact hno
    apply (ccwSuccessor_iff_no_between (insert x star) dir f g
      (hfin.insert x) (Set.mem_insert_of_mem x hf)).2
    refine Or.inr ⟨hfg, Set.mem_insert_of_mem x hg, ?_⟩
    intro z hz hzf hzg
    rcases Set.mem_insert_iff.mp hz with hzx | hzold
    · subst z
      exact houtside
    · exact hno z hzold hzf hzg

private theorem ccwBetween_of_not_reverse {a b c : ℂ}
    (hab : Complex.arg a ≠ Complex.arg b) (hbc : Complex.arg b ≠ Complex.arg c)
    (hno : ¬ CcwBetween b a c) : CcwBetween a b c := by
  have hturnne : ccwTurn a b ≠ ccwTurn a c := by
    intro h
    exact hbc (ccwTurn_left_injective h)
  rcases lt_or_gt_of_ne hturnne with hlt | hgt
  · exact hlt
  · have hcomp := ccwTurn_comp_add (a := a) (b := c) (c := b) hgt
    have habrev := ccwTurn_add_reverse a b hab
    have hbcRev := ccwTurn_add_reverse b c hbc
    have hpos := ccwTurn_pos a c
    have hbetween : CcwBetween b a c := by
      change ccwTurn b a < ccwTurn b c
      linarith
    exact False.elim (hno hbetween)






theorem west_insert_topmost_splice {D : Type*} (star : Set D)
    (dir : D → ℂ) (p d x : D) (hfin : star.Finite)
    (hnonvertical : ∀ f ∈ star, (dir f).re ≠ 0)
    (hargs : ∀ a ∈ insert x star, ∀ b ∈ insert x star, a ≠ b →
      Complex.arg (dir a) ≠ Complex.arg (dir b))
    (hfresh : x ∉ star)
    (hdWest : (dir d).re < 0) (hxWest : (dir x).re < 0)
    (hdmin : ∀ f ∈ star, (dir f).re < 0 →
      f = d ∨ (dir d).im / (dir d).re < (dir f).im / (dir f).re)
    (hnew : (dir x).im / (dir x).re < (dir d).im / (dir d).re)
    (hold : CcwSuccessor star dir p d) :
    CcwBetween (dir p) (dir x) (dir d) ∧
      CcwSuccessor (insert x star) dir p x ∧
      CcwSuccessor (insert x star) dir x d := by
  have hp : p ∈ star := hold.2.1
  have hd : d ∈ star := hold.2.2.1
  have hxmem : x ∈ insert x star := by simp
  have hpx : p ≠ x := by intro h; exact hfresh (h ▸ hp)
  have hdx : d ≠ x := by intro h; exact hfresh (h ▸ hd)
  have hxd := west_insert_topmost_predecessor star dir d x hfin
    hnonvertical hd hfresh hdWest hxWest hdmin hnew
  have holdCase := hold
  have hslot : CcwBetween (dir p) (dir x) (dir d) := by
    rcases holdCase with ⟨_, _, _, hcase⟩
    rcases hcase with hsingle | ⟨hpd, _⟩
    · have hpd' : p = d := hsingle.1.symm
      have harg := hargs p (Set.mem_insert_of_mem x hp) x (by simp) hpx
      have hnotfull : ccwTurn (dir p) (dir x) ≠ 2 * Real.pi := by
        intro hfull
        exact harg ((ccwTurn_eq_two_pi_iff _ _).mp hfull)
      have hle := ccwTurn_le_two_pi (dir p) (dir x)
      have hlt : ccwTurn (dir p) (dir x) < 2 * Real.pi :=
        lt_of_le_of_ne hle hnotfull
      change ccwTurn (dir p) (dir x) < ccwTurn (dir p) (dir d)
      rw [← hpd', (ccwTurn_eq_two_pi_iff _ _).2 rfl]
      exact hlt
    · have hno :=
        (ccwSuccessor_iff_no_between (insert x star) dir x d
          (hfin.insert x) hxmem).mp hxd
      rcases hno with hsingle | ⟨_, _, hno⟩
      · exact False.elim (hdx hsingle.1)
      · have hargPX := hargs p (Set.mem_insert_of_mem x hp) x (by simp) hpx
        have hargXD := hargs x (by simp) d (Set.mem_insert_of_mem x hd) hdx.symm
        exact ccwBetween_of_not_reverse hargPX hargXD (hno p
          (Set.mem_insert_of_mem x hp) (by
            intro h
            exact hpx h) hpd.symm)
  have hnoOld : ∀ z ∈ star, z ≠ p → z ≠ d →
      ¬ CcwBetween (dir p) (dir z) (dir d) := by
    intro z hz hzp hzd hbetween
    have hchar := (ccwSuccessor_iff_no_between star dir p d hfin hp).mp hold
    rcases hchar with hsingle | ⟨_, _, hno⟩
    · have hzP : z = p := by simpa [hsingle.2] using hz
      exact hzp hzP
    · exact hno z hz hzp hzd hbetween
  have hnoSlot : ∀ z ∈ star, z ≠ p → z ≠ x →
      ¬ CcwBetween (dir p) (dir z) (dir x) := by
    intro z hz hzp hzx hbetween
    by_cases hzd : z = d
    · subst z
      exact (not_lt_of_ge hslot.le) hbetween
    · have hbetween' : CcwBetween (dir p) (dir z) (dir d) := by
        change ccwTurn (dir p) (dir z) < ccwTurn (dir p) (dir d)
        exact lt_trans hbetween hslot
      exact hnoOld z hz hzp hzd hbetween'
  have hfirst : CcwSuccessor (insert x star) dir p x := by
    apply (ccwSuccessor_iff_no_between (insert x star) dir p x
      (hfin.insert x) (Set.mem_insert_of_mem x hp)).2
    refine Or.inr ⟨hpx.symm, hxmem, ?_⟩
    intro z hz hzp hzx
    rcases Set.mem_insert_iff.mp hz with hzx' | hzold
    · exact False.elim (hzx hzx')
    · exact hnoSlot z hzold hzp hzx
  exact ⟨hslot, hfirst, hxd⟩





theorem ccwSuccessor_insert_next {D : Type*} (star : Set D) (dir : D → ℂ)
    (d e x : D) (hfin : star.Finite)
    (hargs : ∀ p ∈ insert x star, ∀ q ∈ insert x star, p ≠ q →
      Complex.arg (dir p) ≠ Complex.arg (dir q))
    (hold : CcwSuccessor star dir d e) (hfresh : x ∉ star)
    (hslot : CcwBetween (dir d) (dir x) (dir e)) :
    CcwSuccessor (insert x star) dir x e := by
  classical
  have hxmem : x ∈ insert x star := by simp
  have heold : e ∈ star := by
    rcases hold with ⟨_, _, he, _⟩
    exact he
  have hemem : e ∈ insert x star := Set.mem_insert_of_mem _ heold
  have hxe : x ≠ e := by
    intro h
    subst e
    exact hfresh heold
  have hxd : x ≠ d := by
    intro h
    subst d
    exact hfresh (by rcases hold with ⟨_, hd, _, _⟩; exact hd)
  have holdle : ∀ f ∈ star, ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d) (dir f) := by
    intro f hf
    rcases hold with ⟨_, hd, he, hcase⟩
    rcases hcase with hsing | ⟨hne, hmin⟩
    · rw [hsing.1]
      have hfd : f = d := by simpa [hsing.2] using hf
      subst f
      exact le_rfl
    · by_cases hfd : f = d
      · subst f
        have hfull : ccwTurn (dir d) (dir d) = 2 * Real.pi :=
          (ccwTurn_eq_two_pi_iff _ _).2 rfl
        rw [hfull]
        exact ccwTurn_le_two_pi (dir d) (dir e)
      · exact hmin f hf hfd
  have holdlt : ∀ f ∈ star, f ≠ e →
      ccwTurn (dir d) (dir e) < ccwTurn (dir d) (dir f) := by
    intro f hf hfe
    have hle := holdle f hf
    have hargne := hargs e hemem f (Set.mem_insert_of_mem _ hf) (Ne.symm hfe)
    have hturnne : ccwTurn (dir d) (dir e) ≠ ccwTurn (dir d) (dir f) := by
      intro heq
      exact hargne (ccwTurn_left_injective heq)
    exact lt_of_le_of_ne hle hturnne
  refine ⟨hfin.insert x, hxmem, hemem, Or.inr ⟨hxe.symm, ?_⟩⟩
  intro f hf hfx
  rcases Set.mem_insert_iff.mp hf with hfxeq | hfstar
  · exact (hfx hfxeq).elim
  · by_cases hfe : f = e
    · subst f
      exact le_rfl
    · have hde' := holdlt f hfstar hfe
      have hslot' : ccwTurn (dir d) (dir x) < ccwTurn (dir d) (dir f) :=
        lt_trans hslot hde'
      have hxecomp := ccwTurn_comp_add hslot
      have hxfcomp := ccwTurn_comp_add hslot'
      linarith





theorem east_max_ccwSuccessor {D : Type*} (star : Set D) (dir : D → ℂ)
    (d e : D) (hfin : star.Finite) (hd : d ∈ star) (he : e ∈ star)
    (hnonvertical : ∀ f ∈ star, (dir f).re ≠ 0)
    (hdEast : 0 < (dir d).re) (heWest : (dir e).re < 0)
    (hdmax : ∀ f ∈ star, 0 < (dir f).re →
      f = d ∨ (dir f).im / (dir f).re < (dir d).im / (dir d).re)
    (hemin : ∀ f ∈ star, (dir f).re < 0 →
      f = e ∨ (dir e).im / (dir e).re < (dir f).im / (dir f).re) :
    CcwSuccessor star dir d e := by
  have hne : e ≠ d := by
    intro h
    subst d
    linarith [hdEast, heWest]
  refine ⟨hfin, hd, he, Or.inr ⟨hne, ?_⟩⟩
  intro f hf hfd
  by_cases hfe : f = e
  · subst f
    exact le_rfl
  · by_cases hpos : 0 < (dir f).re
    · have hslopeOr := hdmax f hf hpos
      have hslope : (dir f).im / (dir f).re < (dir d).im / (dir d).re := by
        rcases hslopeOr with rfl | hs
        · exact (hfd rfl).elim
        · exact hs
      have harg : Complex.arg (dir f) < Complex.arg (dir d) :=
        (east_arg_lt_iff_slope_lt hpos hdEast).2 hslope
      have hturnf : ccwTurn (dir d) (dir f) =
          Complex.arg (dir f) - Complex.arg (dir d) + 2 * Real.pi := by
        simp [ccwTurn, not_lt.mpr harg.le]
      rw [hturnf, east_west_turn_formula hdEast heWest]
      have hfb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
      have heb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl
        (show 0 < (-dir e).re by simpa using neg_pos.mpr heWest))
      have hff := (abs_lt.mp hfb).1
      have hee := (abs_lt.mp heb).2
      linarith [Real.pi_pos]
    · have hneg : (dir f).re < 0 := lt_of_le_of_ne (le_of_not_gt hpos)
        (hnonvertical f hf)
      have hslopeOr := hemin f hf hneg
      have hslope : (dir e).im / (dir e).re < (dir f).im / (dir f).re := by
        rcases hslopeOr with rfl | hs
        · exact (hfe rfl).elim
        · exact hs
      exact le_of_lt ((east_west_turn_lt_iff_slope_lt hdEast heWest hneg).2 hslope)





theorem east_insert_topmost_successors {D : Type*} (star : Set D) (dir : D → ℂ)
    (d e x : D) (hfin : star.Finite)
    (hargs : ∀ p ∈ insert x star, ∀ q ∈ insert x star, p ≠ q →
      Complex.arg (dir p) ≠ Complex.arg (dir q))
    (hnonvertical : ∀ f ∈ star, (dir f).re ≠ 0)
    (hd : d ∈ star) (hfresh : x ∉ star)
    (hdEast : 0 < (dir d).re) (hxEast : 0 < (dir x).re)
    (hdmax : ∀ f ∈ star, 0 < (dir f).re →
      f = d ∨ (dir f).im / (dir f).re < (dir d).im / (dir d).re)
    (hnew : (dir d).im / (dir d).re < (dir x).im / (dir x).re)
    (hold : CcwSuccessor star dir d e) :
    CcwSuccessor (insert x star) dir d x ∧ CcwSuccessor (insert x star) dir x e := by
  classical
  have hxmem : x ∈ insert x star := by simp
  have hne : x ≠ d := by intro h; subst d; exact hfresh hd
  have hfirst : CcwSuccessor (insert x star) dir d x := by
    refine ⟨hfin.insert x, Set.mem_insert_of_mem _ hd, hxmem, Or.inr ⟨hne, ?_⟩⟩
    intro f hf hfd
    rcases Set.mem_insert_iff.mp hf with rfl | hfstar
    · exact le_rfl
    · by_cases hfd' : f = d
      · exact (hfd hfd').elim
      · by_cases hpos : 0 < (dir f).re
        · have hslopeOr := hdmax f hfstar hpos
          have hslope : (dir f).im / (dir f).re < (dir d).im / (dir d).re := by
            rcases hslopeOr with rfl | hs
            · exact (hfd rfl).elim
            · exact hs
          have hfarg : Complex.arg (dir f) < Complex.arg (dir d) :=
            (east_arg_lt_iff_slope_lt hpos hdEast).2 hslope
          have hdarg : Complex.arg (dir d) < Complex.arg (dir x) :=
            (east_arg_lt_iff_slope_lt hdEast hxEast).2 hnew
          have htf : ccwTurn (dir d) (dir f) =
              Complex.arg (dir f) - Complex.arg (dir d) + 2 * Real.pi := by
            simp [ccwTurn, not_lt.mpr hfarg.le]
          rw [htf, ccwTurn_eq_turn_of_arg_lt hdarg]
          have hfb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
          have hxb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxEast)
          linarith [(abs_lt.mp hfb).1, (abs_lt.mp hxb).2, Real.pi_pos]
        · have hneg : (dir f).re < 0 := lt_of_le_of_ne (le_of_not_gt hpos)
            (hnonvertical f hfstar)
          exact le_of_lt ((east_pair_turn_before_west hdEast hxEast hneg hnew))
  have heold : e ∈ star := by rcases hold with ⟨_, _, he, _⟩; exact he
  have hemem : e ∈ insert x star := Set.mem_insert_of_mem _ heold
  have hlede : ccwTurn (dir d) (dir x) ≤ ccwTurn (dir d) (dir e) := by
      by_cases hed : e = d
      · subst e
        have hfull : ccwTurn (dir d) (dir d) = 2 * Real.pi :=
          (ccwTurn_eq_two_pi_iff _ _).2 rfl
        rw [hfull]
        exact ccwTurn_le_two_pi _ _
      · rcases hfirst with ⟨_, _, _, hcase⟩
        rcases hcase with ⟨hself, _⟩ | ⟨_, hmin⟩
        · exact False.elim (hne hself)
        · exact hmin e hemem hed
  have hde : ccwTurn (dir d) (dir x) < ccwTurn (dir d) (dir e) := by
    rcases lt_or_eq_of_le hlede with hlt | heq
    · exact hlt
    · have hargne := hargs x hxmem e hemem (by
        intro h
        exact hfresh (h.symm ▸ heold))
      exact False.elim (hargne (ccwTurn_left_injective heq))
  have hnext := ccwSuccessor_insert_next star dir d e x hfin hargs hold hfresh hde
  exact ⟨hfirst, hnext⟩


end DirectedDistances.PlanarMap
