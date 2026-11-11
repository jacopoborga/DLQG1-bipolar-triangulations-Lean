/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion3

/-! Helpers toward Proposition 5.16: angular slots for the straight closing frame side. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

private theorem frame_turn_coe_angle (u v : ℂ) :
    (ccwTurn u v : Real.Angle) = (v.arg : Real.Angle) - u.arg := by
  unfold ccwTurn
  split_ifs
  · exact Real.Angle.coe_sub _ _
  · rw [Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.coe_two_pi, add_zero]

/-- Helper toward Proposition 5.16: multiplying two nonzero directions by
the same nonzero complex number preserves their positive counterclockwise turn. -/
theorem frame_ccwTurn_mul_left (s u v : ℂ) (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    ccwTurn (s * u) (s * v) = ccwTurn u v := by
  let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    (p := 2 * Real.pi) (a := 0)
    (show ccwTurn (s * u) (s * v) ∈ Ioc 0 (0 + 2 * Real.pi) from
      ⟨ccwTurn_pos _ _, by simpa only [zero_add] using ccwTurn_le_two_pi (s * u) (s * v)⟩)
    (show ccwTurn u v ∈ Ioc 0 (0 + 2 * Real.pi) from
      ⟨ccwTurn_pos _ _, by simpa only [zero_add] using ccwTurn_le_two_pi u v⟩)).mp
  change (ccwTurn (s * u) (s * v) : Real.Angle) = (ccwTurn u v : Real.Angle)
  rw [frame_turn_coe_angle, frame_turn_coe_angle,
    Complex.arg_mul_coe_angle hs hv, Complex.arg_mul_coe_angle hs hu]
  abel

/-- Helper toward Proposition 5.16: from a nonzero direction in the closed
left half-plane, two right-half-plane rays have the same order as their arguments. -/
theorem frame_ccwTurn_lt_of_left_right {u v w : ℂ}
    (hu : u ≠ 0) (hure : u.re ≤ 0) (hv : 0 < v.re) (hw : 0 < w.re)
    (hvw : v.arg < w.arg) : ccwTurn u v < ccwTurn u w := by
  have hwide : Real.pi / 2 ≤ |u.arg| := by
    by_contra h
    rcases Complex.abs_arg_lt_pi_div_two_iff.mp (lt_of_not_ge h) with hpos | hzero
    · exact (not_lt_of_ge hure) hpos
    · exact hu hzero
  have hvarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have hwarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  by_cases hsign : 0 ≤ u.arg
  · rw [abs_of_nonneg hsign] at hwide
    have huv : ¬ u.arg < v.arg := by linarith only [hwide, hvarg.2]
    have huw : ¬ u.arg < w.arg := by linarith only [hwide, hwarg.2]
    simp only [ccwTurn, ite_eq_right huv, ite_eq_right huw]
    linarith only [hvw]
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hwide
    have huv : u.arg < v.arg := by linarith only [hwide, hvarg.1]
    have huw : u.arg < w.arg := by linarith only [hwide, hwarg.1]
    simp only [ccwTurn, ite_eq_left huv, ite_eq_left huw]
    linarith only [hvw]

/-- Helper toward Proposition 5.16: at right-square contact, the straight
closing ray occurs before the first frame ray when viewed from any nonzero
incoming access direction contained in the closed left half-plane. -/
theorem rightCornerFrame_contact_turn (R : ℝ) (hR : 0 < R) (u : ℂ)
    (hu : u ≠ 0) (hure : u.re ≤ 0) :
    ccwTurn u (⟨4 * R, -4 * R⟩ : ℂ) < ccwTurn u (⟨4 * R, 4 * R⟩ : ℂ) := by
  apply frame_ccwTurn_lt_of_left_right hu hure (by dsimp; positivity) (by dsimp; positivity)
  apply (east_arg_lt_iff_slope_lt (by dsimp; positivity) (by dsimp; positivity)).mpr
  dsimp
  have hp : 0 < 4 * R := by positivity
  exact lt_trans (div_neg_of_neg_of_pos (by linarith only [hR]) hp) (div_pos hp hp)

namespace Polyline

/-- Helper toward Proposition 5.16: an access polyline contained in the
closed square has its initial direction on the inner side of a contact
point, after undoing any square symmetry. -/
theorem contact_initialDirection_re_nonpos (p : Polyline) (R t : ℝ)
    (hR : 0 < R) (s : ℂ) (hs : s ≠ 0)
    (hsym : ∀ z : ℂ, max |(s * z).re| |(s * z).im| = max |z.re| |z.im|)
    (hlen : 2 ≤ p.points.length) (hp : p.image ⊆ closure (enclosingSquare R).inside)
    (hstart : p.start = s * (⟨R, t⟩ : ℂ)) :
    (s⁻¹ * p.initialDirection).re ≤ 0 := by
  have hpt := hp (p.point_mem_image (i := 1) (by omega))
  rw [enclosingSquare_closure_inside R hR] at hpt
  have hsympt := hsym (s⁻¹ * p.point 1)
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul] at hsympt
  have hmax : max |(s⁻¹ * p.point 1).re| |(s⁻¹ * p.point 1).im| ≤ R := by
    rw [← hsympt]
    exact max_le hpt.1 hpt.2
  have hbound : (s⁻¹ * p.point 1).re ≤ R :=
    (le_abs_self _).trans ((le_max_left _ _).trans hmax)
  rw [initialDirection, mul_sub, hstart, ← mul_assoc, inv_mul_cancel₀ hs, one_mul,
    Complex.sub_re]
  exact sub_nonpos.mpr hbound

/-- Helper toward Proposition 5.16: the two frame rays at any square
contact have the required strict order from the actual access direction.
The square symmetry preserves orientation, and no slot is assumed. -/
theorem cornerFrame_contact_turn (p : Polyline) (R t : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ≠ 0)
    (hsym : ∀ z : ℂ, max |(s * z).re| |(s * z).im| = max |z.re| |z.im|)
    (hlen : 2 ≤ p.points.length) (hdir : p.initialDirection ≠ 0)
    (hp : p.image ⊆ closure (enclosingSquare R).inside)
    (hstart : p.start = s * (⟨R, t⟩ : ℂ)) :
    ccwTurn p.initialDirection (s * (⟨4 * R, -4 * R⟩ : ℂ)) <
      ccwTurn p.initialDirection (s * (⟨4 * R, 4 * R⟩ : ℂ)) := by
  have hu := p.contact_initialDirection_re_nonpos R t hR s hs hsym hlen hp hstart
  have hn : s⁻¹ * p.initialDirection ≠ 0 := mul_ne_zero (inv_ne_zero hs) hdir
  have hlow : (⟨4 * R, -4 * R⟩ : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    dsimp at hh
    linarith only [hR, hh]
  have hupp : (⟨4 * R, 4 * R⟩ : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    dsimp at hh
    linarith only [hR, hh]
  have ht := rightCornerFrame_contact_turn R hR (s⁻¹ * p.initialDirection) hn hu
  rw [← frame_ccwTurn_mul_left s _ _ hs hn hlow,
    ← frame_ccwTurn_mul_left s _ _ hs hn hupp,
    ← mul_assoc, mul_inv_cancel₀ hs, one_mul] at ht
  exact ht

/-- Helper toward Proposition 5.16: at the last frame vertex, the closing
side lies strictly in the full-turn leaf slot, by simplicity of the frame. -/
theorem closing_side_leaf_turn (c A B C : ℂ)
    (hF : (ofHead c [A, B, C, c]).IsCyclicSimple) :
    ccwTurn (cornerSegment B C).reverse.initialDirection (cornerSegment C c).initialDirection <
      ccwTurn (cornerSegment B C).reverse.initialDirection
        (cornerSegment B C).reverse.initialDirection := by
  rw [(ccwTurn_eq_two_pi_iff _ _).mpr rfl]
  apply d39_ccwTurn_lt_two_pi
  change (cornerSegment C B).initialDirection.arg ≠ (cornerSegment C c).initialDirection.arg
  apply initialDirection_arg_ne_of_inter_eq_start (cornerSegment C B) (cornerSegment C c)
    (isSimple_cornerSegment (Ne.symm (hF.2.2.1 2 (by change 3 < 5; omega))))
    (isSimple_cornerSegment (hF.2.2.1 3 (by change 4 < 5; omega)))
    (by change 2 ≤ 2; omega) (by change 2 ≤ 2; omega) rfl
  rw [image_cornerSegment, image_cornerSegment, segment_symm ℝ C B]
  exact hF.2.2.2.1 2 (by change 4 < 5; omega)

end Polyline

namespace Polyline

/-- Helper toward Proposition 5.16: the open horizontal ray from the
right contact runs through the outside of the reflex corner frame. -/
theorem rightCornerFrame_right_ray_outside (R t : ℝ) (hR : 0 < R)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (⟨R + ρ, t⟩ : ℂ) ∈ (rightCornerFrame R t).outside := by
  let p := rightCornerFrame R t
  let f : ℝ → ℂ := fun r => ⟨R + r, t⟩
  let U := f '' Ioi 0
  have havoid : U ⊆ p.imageᶜ := by
    rintro z ⟨r, hr, rfl⟩ hz
    have hr' : 0 < r := hr
    rcases hz with hz | ⟨j, hj, hz⟩
    · have hh := congrArg Complex.re hz
      change R + r = R at hh
      linarith only [hr', hh]
    · change j + 1 < 5 at hj
      have hh := rightCornerFrame_segment_constraints R t hR (f r)
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
      · have hc := hh.1 hz
        dsimp [f] at hc
        linarith only [hc.2.2, hr']
      · have hc := hh.2.1 hz
        dsimp [f] at hc
        linarith only [hc.2.2, hr', hR]
      · have hc := hh.2.2.1 hz
        dsimp [f] at hc
        linarith only [hc.2.2, hr', hR]
      · have hc := hh.2.2.2 hz
        dsimp [f] at hc
        linarith only [hc.2.2, hr']
  have hf : Continuous f := by
    have heq : f = fun r : ℝ => ((R + r : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      funext r
      apply Complex.ext <;> simp [f]
    rw [heq]
    fun_prop
  have hpre : IsPreconnected U := isPreconnected_Ioi.image f hf.continuousOn
  obtain ⟨S, hS⟩ := p.exists_radius_exterior_subset_outside (by rfl)
  let r := |S| + |R| + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hfar : f r ∈ p.outside := by
    apply hS
    have hnorm : (f r).re ≤ ‖f r‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    dsimp [f, r] at hnorm
    linarith only [hnorm, le_abs_self S, neg_abs_le R]
  have hzU : f ρ ∈ U := ⟨ρ, hρ, rfl⟩
  refine ⟨havoid hzU, ?_⟩
  change p.angleSum (f ρ) = 0
  rw [p.angleSum_eq_of_isPreconnected (by rfl) U hpre havoid (f ρ) (f r)
    hzU ⟨r, hr, rfl⟩]
  exact hfar.2

/-- Helper toward Proposition 5.16: complex rotation carries the escaping
contact ray to the outside of the rotated corner frame. -/
theorem cornerFrame_right_ray_outside (R t : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    s * (⟨R + ρ, t⟩ : ℂ) ∈
      (mapPoints (fun z => s * z) (rightCornerFrame R t)).outside := by
  have hz := rightCornerFrame_right_ray_outside R t hR ρ hρ
  constructor
  · rw [image_mapPoints _ _ (affineOnSegments_mul _ s)]
    rintro ⟨w, hw, heq⟩
    exact hz.1 ((mul_right_injective₀ hs heq) ▸ hw)
  · exact (angleSum_mapPoints_mul _ s hs _).trans hz.2

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the escaping ray in the notch belongs
to the closing dart's actual face, which is precisely the frame outside.
Only the installed arcs and geometric containment are inputs. -/
theorem plDartFace_eq_cornerFrame_outside {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D)
    (R t : ℝ) (hR : 0 < R) (s : ℂ) (hs : s ≠ 0)
    (hpos : P.pos (vert d) = s * (⟨R, t⟩ : ℂ))
    (hlo : P.arc d = Polyline.cornerSegment (s * (⟨R, t⟩ : ℂ))
      (s * (⟨5 * R, t - 4 * R⟩ : ℂ)))
    (hup : P.arc (B.map.rot d) = Polyline.cornerSegment (s * (⟨R, t⟩ : ℂ))
      (s * (⟨5 * R, t + 4 * R⟩ : ℂ)))
    (hboundary : (Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)).image ⊆ P.image)
    (hinside : P.image ⊆ closure
      (Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)).inside) :
    (B.plDartFace vert P hvert d).val =
      (Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)).outside := by
  let F := Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)
  have hF : F.IsCyclicSimple := Polyline.isCyclicSimple_mapPoints_of_affine _ _
    (Polyline.affineOnSegments_mul _ s) (mul_right_injective₀ hs)
    (Polyline.rightCornerFrame_isCyclicSimple R t hR)
  have hdirlo : (P.arc d).initialDirection = s * (⟨4 * R, -4 * R⟩ : ℂ) := by
    rw [hlo, (Polyline.cornerSegment_data _ _).2.2, ← mul_sub]
    congr 1
    apply Complex.ext <;> dsimp <;> ring
  have hdirup : (P.arc (B.map.rot d)).initialDirection = s * (⟨4 * R, 4 * R⟩ : ℂ) := by
    rw [hup, (Polyline.cornerSegment_data _ _).2.2, ← mul_sub]
    congr 1
    apply Complex.ext <;> dsimp <;> ring
  have hlow : (⟨4 * R, -4 * R⟩ : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    dsimp at hh
    linarith only [hh, hR]
  have hupp : (⟨4 * R, 4 * R⟩ : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    dsimp at hh
    linarith only [hh, hR]
  have hangle : ccwTurn (P.arc d).initialDirection s <
      ccwTurn (P.arc d).initialDirection (P.arc (B.map.rot d)).initialDirection := by
    rw [hdirlo, hdirup, frame_ccwTurn_mul_left s _ _ hs hlow hupp]
    rw [show ccwTurn (s * (⟨4 * R, -4 * R⟩ : ℂ)) s =
      ccwTurn (⟨4 * R, -4 * R⟩ : ℂ) 1 from by
        simpa only [mul_one] using frame_ccwTurn_mul_left s _ 1 hs hlow one_ne_zero]
    have hp : 0 < 4 * R := by positivity
    have h₁ : (⟨4 * R, -4 * R⟩ : ℂ).arg < (1 : ℂ).arg := by
      apply (east_arg_lt_iff_slope_lt hp (by norm_num)).mpr
      change (-4 * R) / (4 * R) < 0 / 1
      rw [zero_div]
      exact div_neg_of_neg_of_pos (by linarith only [hR]) hp
    have h₂ : (1 : ℂ).arg < (⟨4 * R, 4 * R⟩ : ℂ).arg := by
      apply (east_arg_lt_iff_slope_lt (by norm_num) hp).mpr
      change 0 / 1 < (4 * R) / (4 * R)
      rw [zero_div]
      exact div_pos hp hp
    rw [ccwTurn_eq_turn_of_arg_lt h₁, ccwTurn_eq_turn_of_arg_lt (h₁.trans h₂)]
    linarith only [h₂]
  obtain ⟨S, _⟩ := P.exists_D39PLSeparationData hvert
  let ρ := S.radius / 2
  have hρ : 0 < ρ := half_pos S.radius_pos
  have hρr : ρ < S.radius := half_lt_self S.radius_pos
  let lam := ρ / ‖s‖
  have hlam : 0 < lam := div_pos hρ (norm_pos_iff.mpr hs)
  let z := P.pos (vert d) + (lam : ℂ) * s
  have hzsector : z ∈ P.initialSector d S.radius := by
    refine ⟨(ρ, ccwTurn (P.arc d).initialDirection s),
      ⟨⟨hρ, hρr⟩, ccwTurn_pos _ _, hangle⟩, ?_⟩
    dsimp only [Prod.fst, Prod.snd]
    rw [d39_radial_testPoint_eq _ s hs]
  have hzout : z ∈ F.outside := by
    have hh := Polyline.cornerFrame_right_ray_outside R t hR s hs lam hlam
    convert hh using 1
    dsimp only [z]
    rw [hpos, mul_comm (lam : ℂ) s, ← mul_add]
    congr 1
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero]
  have hzface := B.initialSector_subset_plDartFace vert P hvert S d hzsector
  have heq : (B.plDartFace vert P hvert d).val = connectedComponentIn P.imageᶜ z := by
    obtain ⟨w, hw, heq⟩ := (B.plDartFace vert P hvert d).property
    exact heq.trans (connectedComponentIn_eq (heq ▸ hzface))
  exact heq.trans (F.outside_component_of_enclosing_set hF P.image hboundary hinside z hzout)

/-- Helper toward Proposition 5.16: in the three-side drawing of the
explicit corner frame, the straight closing segment has the correct strict
rotation slots at both endpoints. These slots follow from the closed-square
containment of the access drawing and the prescribed straight frame arcs. -/
theorem three_corner_frame_closing_turns {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D)
    (R t : ℝ) (hR : 0 < R) (ht : -R ≤ t ∧ t ≤ R) (s : ℂ) (hs : s ≠ 0)
    (hsym : ∀ z : ℂ, max |(s * z).re| |(s * z).im| = max |z.re| |z.im|)
    (hQ : Q.image ⊆ closure (Polyline.enclosingSquare R).inside)
    (hc : Q.pos (vert a) = s * (⟨R, t⟩ : ℂ)) :
    let c := Q.pos (vert a)
    let A := s * (⟨5 * R, t + 4 * R⟩ : ℂ)
    let M := s * (⟨-11 * R, t⟩ : ℂ)
    let C := s * (⟨5 * R, t - 4 * R⟩ : ℂ)
    let D₁ := B.insertPendant a
    let w₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    ∀ T : PLDrawing D₃.D (Option (Option (Option V)))
      D₃.map.edgeInv D₃.map.rot w₃,
      (∀ d : B.D, T.arc (.inl (.inl (.inl d))) = Q.arc d) →
      T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment c A →
      T.arc (.inr true) = Polyline.cornerSegment M C →
      let x : D₃.D := .inr false
      let y : D₃.D := .inl (.inl (.inl a))
      let g := Polyline.cornerSegment C c
      (ccwTurn (T.arc x).initialDirection g.initialDirection <
        ccwTurn (T.arc x).initialDirection (T.arc (D₃.map.rot x)).initialDirection) ∧
      (ccwTurn (T.arc y).initialDirection g.reverse.initialDirection <
        ccwTurn (T.arc y).initialDirection (T.arc (D₃.map.rot y)).initialDirection) := by
  dsimp only
  intro T ha hA hC
  let D₁ := B.insertPendant a
  let D₂ := D₁.insertPendant (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  have hF := (Polyline.cornerFrame_of_square_symmetry R t hR ht s hs hsym).1
  change (Polyline.ofHead (s * (⟨R, t⟩ : ℂ))
    [s * (⟨5 * R, t + 4 * R⟩ : ℂ), s * (⟨-11 * R, t⟩ : ℂ),
      s * (⟨5 * R, t - 4 * R⟩ : ℂ), s * (⟨R, t⟩ : ℂ)]).IsCyclicSimple at hF
  rw [← hc] at hF
  constructor
  · have hflip := T.arc_flip (.inr true)
    change T.arc (.inr false) = (T.arc (.inr true)).reverse at hflip
    rw [hC] at hflip
    change ccwTurn (T.arc (.inr false)).initialDirection _ <
      ccwTurn (T.arc (.inr false)).initialDirection (T.arc (.inr false)).initialDirection
    rw [hflip]
    exact Polyline.closing_side_leaf_turn _ _ _ _ hF
  · have hrot : D₃.map.rot (.inl (.inl (.inl a))) = .inl (.inl (.inr true)) := by
      change D₂.pendantRotation (.inr false) (.inl (.inl (.inl a))) = _
      rw [D₂.pendantRotation_inl_of_ne (.inr false) (.inl (.inl a)) Sum.inl_ne_inr]
      change Sum.inl (D₁.pendantRotation (.inr false) (.inl (.inl a))) = _
      rw [D₁.pendantRotation_inl_of_ne (.inr false) (.inl a) Sum.inl_ne_inr]
      change Sum.inl (Sum.inl (B.pendantRotation a (.inl a))) = _
      rw [B.pendantRotation_attachment a]
      rfl
    rw [hrot, ha, hA]
    have hsub : (Q.arc a).image ⊆ closure (Polyline.enclosingSquare R).inside :=
      fun z hz => hQ (Or.inr ⟨a, hz⟩)
    have hstart : (Q.arc a).start = s * (⟨R, t⟩ : ℂ) := (Q.arc_start a).trans hc
    have hh := (Q.arc a).cornerFrame_contact_turn R t hR s hs hsym
      (Q.arc_length a) (Q.initial_nonzero a) hsub hstart
    have hl : (Polyline.cornerSegment (s * (⟨5 * R, t - 4 * R⟩ : ℂ))
        (Q.pos (vert a))).reverse.initialDirection = s * (⟨4 * R, -4 * R⟩ : ℂ) := by
      change (Polyline.cornerSegment (Q.pos (vert a))
        (s * (⟨5 * R, t - 4 * R⟩ : ℂ))).initialDirection = _
      rw [(Polyline.cornerSegment_data _ _).2.2, hc, ← mul_sub]
      congr 1
      apply Complex.ext <;> dsimp <;> ring
    have hr : (Polyline.cornerSegment (Q.pos (vert a))
        (s * (⟨5 * R, t + 4 * R⟩ : ℂ))).initialDirection = s * (⟨4 * R, 4 * R⟩ : ℂ) := by
      rw [(Polyline.cornerSegment_data _ _).2.2, hc, ← mul_sub]
      congr 1
      apply Complex.ext <;> dsimp <;> ring
    rw [hl, hr]
    exact hh

/-- Helper toward Proposition 5.16: a leaf on an enclosing square admits
an enclosing straight corner frame, including its geometrically inserted
closing side. Every original position and entire original dart arc persists.
The final map depends only on the original map and attachment dart. -/
theorem exists_closed_corner_frame_drawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (hleaf : B.map.rot a = a) (R : ℝ) (hR : 0 < R)
    (hQ : Q.image ⊆ closure (Polyline.enclosingSquare R).inside)
    (hc : Q.pos (vert a) ∈ (Polyline.enclosingSquare R).image) :
    let D₁ := B.insertPendant a
    let w₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    let x : D₃.D := .inr false
    let y : D₃.D := .inl (.inl (.inl a))
    let E := D₃.insertChord x y (by exact Sum.inr_ne_inl)
    let v := D₃.chordVert w₃ x y
    ∃ (s : ℂ) (t : ℝ) (T : PLDrawing E.D (Option (Option (Option V)))
      E.map.edgeInv E.map.rot v),
      let c := Q.pos (vert a)
      let A := s * (⟨5 * R, t + 4 * R⟩ : ℂ)
      let M := s * (⟨-11 * R, t⟩ : ℂ)
      let C := s * (⟨5 * R, t - 4 * R⟩ : ℂ)
      let F := Polyline.ofHead c [A, M, C, c]
      s ≠ 0 ∧ (-R ≤ t ∧ t ≤ R) ∧
      (∀ z : ℂ, max |(s * z).re| |(s * z).im| = max |z.re| |z.im|) ∧
      c = s * (⟨R, t⟩ : ℂ) ∧ F.IsCyclicSimple ∧
      closure (Polyline.enclosingSquare R).inside ⊆ closure F.inside ∧
      (∀ z : V, T.pos (some (some (some z))) = Q.pos z) ∧
      (∀ d : B.D, T.arc (.inl (.inl (.inl (.inl d)))) = Q.arc d) ∧
      T.pos (some (some none)) = A ∧ T.pos (some none) = M ∧ T.pos none = C ∧
      T.arc (.inl (.inl (.inl (.inr true)))) = Polyline.cornerSegment c A ∧
      T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment A M ∧
      T.arc (.inl (.inr true)) = Polyline.cornerSegment M C ∧
      T.arc (.inr true) = Polyline.cornerSegment C c ∧
      T.image = Q.image ∪ F.image := by
  dsimp only
  let D₁ := B.insertPendant a
  let w₁ := B.pendantVert vert a
  let D₂ := D₁.insertPendant (.inr false)
  let w₂ := D₁.pendantVert w₁ (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  let w₃ := D₂.pendantVert w₂ (.inr false)
  let x : D₃.D := .inr false
  let y : D₃.D := .inl (.inl (.inl a))
  obtain ⟨s, t, hs, ht, hsym, hcs⟩ :=
    Polyline.exists_square_symmetry_of_mem_boundary R hR (Q.pos (vert a)) hc
  let c := Q.pos (vert a)
  let A := s * (⟨5 * R, t + 4 * R⟩ : ℂ)
  let M := s * (⟨-11 * R, t⟩ : ℂ)
  let C := s * (⟨5 * R, t - 4 * R⟩ : ℂ)
  let F := Polyline.ofHead c [A, M, C, c]
  have hframe := Polyline.cornerFrame_of_square_symmetry R t hR ht s hs hsym
  change (Polyline.ofHead (s * (⟨R, t⟩ : ℂ)) [A, M, C, s * (⟨R, t⟩ : ℂ)]).IsCyclicSimple ∧
    closure (Polyline.enclosingSquare R).inside ⊆
      closure (Polyline.ofHead (s * (⟨R, t⟩ : ℂ)) [A, M, C, s * (⟨R, t⟩ : ℂ)]).inside ∧
    (Polyline.ofHead (s * (⟨R, t⟩ : ℂ)) [A, M, C, s * (⟨R, t⟩ : ℂ)]).image ∩
      closure (Polyline.enclosingSquare R).inside = {s * (⟨R, t⟩ : ℂ)} at hframe
  rw [← hcs] at hframe
  have hF : F.IsCyclicSimple := hframe.1
  have hcontact : F.image ∩ Q.image = {c} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hframe.2.2.subset ⟨hz.1, hQ hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨vert a, rfl⟩⟩
  let p := Polyline.ofHead c [A, M, C]
  have hsub : p.image ⊆ F.image := by
    rintro z (hz | ⟨j, hj, hz⟩)
    · exact Or.inl hz
    · change j + 1 < 4 at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact Or.inr ⟨0, by change 1 < 5; omega, hz⟩
      · exact Or.inr ⟨1, by change 2 < 5; omega, hz⟩
      · exact Or.inr ⟨2, by change 3 < 5; omega, hz⟩
  have hct : p.image ∩ Q.image = {p.start} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hcontact.subset ⟨hsub hz.1, hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨vert a, rfl⟩⟩
  obtain ⟨T, hv, ha, hA, hM, hC, hg₀, hg₁, hg₂, hi⟩ :=
    B.exists_three_chain_sides_drawing vert Q a hleaf p
      (Polyline.isSimple_three_sides_of_quadrilateral c A M C hF) rfl rfl hct
  have hg₀' : T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment c A := hg₀
  have hg₂' : T.arc (.inr true) = Polyline.cornerSegment M C := hg₂
  obtain ⟨hta, htb⟩ := B.three_corner_frame_closing_turns vert Q a R t hR ht s hs hsym
    hQ hcs T ha hg₀' hg₂'
  let g := Polyline.cornerSegment C c
  obtain ⟨hgs, hgd⟩ := Polyline.closing_side_simple_disjoint c A M C hF Q.image hcontact
  have hdis : Disjoint g.interior T.image := hi.symm ▸ hgd
  have hxy : w₃ x ≠ w₃ y := by
    change (none : Option (Option (Option V))) ≠ some (some (some (vert a)))
    intro h
    cases h
  have hstart : g.start = T.pos (w₃ x) := hC.symm
  have hfinish : g.finish = T.pos (w₃ y) := (hv (vert a)).symm
  obtain ⟨hsa, hsga, hsb, hsgb⟩ :=
    D₃.chord_corner_successors_of_strict_turns w₃ T x y hxy g hta htb
  have hargx := Ne.symm (D₃.chord_direction_ne_old w₃ T x g.initialDirection hta x rfl)
  have hargy := Ne.symm (D₃.chord_direction_ne_old w₃ T y g.reverse.initialDirection htb y rfl)
  let U := D₃.insertChordDrawing w₃ T x y hxy g hgs hstart hfinish hdis
    hsa hsga hsb hsgb hargx hargy
  refine ⟨s, t, U, hs, ht, hsym, hcs, hF, hframe.2.1,
    hv, ?_, hA, hM, hC, hg₀, hg₁, hg₂, rfl, ?_⟩
  · intro d
    exact ha d
  · change U.image = Q.image ∪ F.image
    rw [show U.image = T.image ∪ g.image from
      D₃.insertChordDrawing_image w₃ T x y hxy g hgs hstart hfinish hdis
        hsa hsga hsb hsgb hargx hargy]
    rw [hi, Set.union_assoc]
    congr 1
    apply Set.Subset.antisymm
    · exact union_subset hsub (by
        rw [Polyline.image_cornerSegment]
        exact F.segmentAt_subset_image (i := 3) (by change 4 < 5; omega))
    · rintro z (hz | ⟨j, hj, hz⟩)
      · exact Or.inl (Or.inl hz)
      · change j + 1 < 5 at hj
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inr ⟨0, by change 1 < 4; omega, hz⟩)
        · exact Or.inl (Or.inr ⟨1, by change 2 < 4; omega, hz⟩)
        · exact Or.inl (Or.inr ⟨2, by change 3 < 4; omega, hz⟩)
        · exact Or.inr ((Polyline.image_cornerSegment C c).symm ▸ hz)

/-- Helper toward Proposition 5.16: the installed frame's closing dart
has the unbounded outside as its actual face. Its face-successor cycle has
four distinct vertices; neither face simplicity nor exterior status is an input. -/
theorem exists_closed_corner_frame_exterior {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D) (hleaf : B.map.rot a = a)
    (R : ℝ) (hR : 0 < R)
    (hQ : Q.image ⊆ closure (Polyline.enclosingSquare R).inside)
    (hc : Q.pos (vert a) ∈ (Polyline.enclosingSquare R).image) :
    let D₁ := B.insertPendant a
    let w₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    let x : D₃.D := .inr false
    let y : D₃.D := .inl (.inl (.inl a))
    let E := D₃.insertChord x y (by exact Sum.inr_ne_inl)
    let v := D₃.chordVert w₃ x y
    ∃ (s : ℂ) (t : ℝ) (T : PLDrawing E.D (Option (Option (Option V)))
      E.map.edgeInv E.map.rot v) (hv : Function.Surjective v),
      let F := Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)
      (∀ z : V, T.pos (some (some (some z))) = Q.pos z) ∧
      (∀ d : B.D, T.arc (.inl (.inl (.inl (.inl d)))) = Q.arc d) ∧
      F.IsCyclicSimple ∧ closure (Polyline.enclosingSquare R).inside ⊆ closure F.inside ∧
      T.image = Q.image ∪ F.image ∧
      (E.plDartFace v T hv (.inr false)).val = F.outside ∧
      (¬ Bornology.IsBounded (E.plDartFace v T hv (.inr false)).val) ∧
      Function.minimalPeriod E.map.faceSucc (.inr false) = 4 ∧
      Set.InjOn (fun k : ℕ => v ((E.map.faceSucc : E.D → E.D)^[k] (.inr false)))
        (Set.Iio 4) := by
  dsimp only
  let D₁ := B.insertPendant a
  let w₁ := B.pendantVert vert a
  let D₂ := D₁.insertPendant (.inr false)
  let w₂ := D₁.pendantVert w₁ (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  let w₃ := D₂.pendantVert w₂ (.inr false)
  let x : D₃.D := .inr false
  let y : D₃.D := .inl (.inl (.inl a))
  let E := D₃.insertChord x y (by exact Sum.inr_ne_inl)
  let v := D₃.chordVert w₃ x y
  obtain ⟨s, t, T, hs, ht, hsym, hcs, hF, hbox, hpos, harc, hA, hM, hC,
    hg₀, hg₁, hg₂, hg₃, himage⟩ := B.exists_closed_corner_frame_drawing vert Q a hleaf R hR hQ hc
  let F := Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)
  have hFeq : F = Polyline.ofHead (Q.pos (vert a))
      [s * (⟨5 * R, t + 4 * R⟩ : ℂ), s * (⟨-11 * R, t⟩ : ℂ),
        s * (⟨5 * R, t - 4 * R⟩ : ℂ), Q.pos (vert a)] := by
    rw [hcs]
    rfl
  rw [← hFeq] at hF hbox himage
  have hw₁ := B.pendantVert_surjective vert a hvert
  have hw₂ := D₁.pendantVert_surjective w₁ (.inr false) hw₁
  have hw₃ := D₂.pendantVert_surjective w₂ (.inr false) hw₂
  have hv : Function.Surjective v := by
    intro z
    obtain ⟨d, hd⟩ := hw₃ z
    exact ⟨.inl d, hd⟩
  have hrot : E.map.rot (.inr false) = .inl (.inl (.inl (.inr true))) := by
    change Sum.inl (D₃.map.rot y) = _
    change Sum.inl (D₂.pendantRotation (.inr false) (.inl (.inl (.inl a)))) = _
    rw [D₂.pendantRotation_inl_of_ne (.inr false) (.inl (.inl a)) Sum.inl_ne_inr]
    change Sum.inl (Sum.inl (D₁.pendantRotation (.inr false) (.inl (.inl a)))) = _
    rw [D₁.pendantRotation_inl_of_ne (.inr false) (.inl a) Sum.inl_ne_inr]
    change Sum.inl (Sum.inl (Sum.inl (B.pendantRotation a (.inl a)))) = _
    rw [B.pendantRotation_attachment a]
    rfl
  have hlo : T.arc (.inr false) = Polyline.cornerSegment (s * (⟨R, t⟩ : ℂ))
      (s * (⟨5 * R, t - 4 * R⟩ : ℂ)) := by
    have hh := T.arc_flip (.inr true)
    change T.arc (.inr false) = (T.arc (.inr true)).reverse at hh
    rw [hg₃, hcs] at hh
    exact hh
  have hup : T.arc (E.map.rot (.inr false)) = Polyline.cornerSegment
      (s * (⟨R, t⟩ : ℂ)) (s * (⟨5 * R, t + 4 * R⟩ : ℂ)) := by
    rw [hrot, hg₀, hcs]
  have hboundary : F.image ⊆ T.image := by rw [himage]; exact subset_union_right
  have hinside : T.image ⊆ closure F.inside := by
    rw [himage]
    exact union_subset (hQ.trans hbox) (F.image_subset_closure_inside_cyclic hF)
  have hout := E.plDartFace_eq_cornerFrame_outside v T hv (.inr false) R t hR s hs
    ((hpos (vert a)).trans hcs) hlo hup hboundary hinside
  have hunbounded : ¬ Bornology.IsBounded (E.plDartFace v T hv (.inr false)).val := by
    rw [hout]
    intro hb
    obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨z, hz, hnorm⟩ := F.outside_unbounded (by rw [hFeq]; rfl) L
    exact (not_le_of_gt hnorm) (hL z hz)
  exact ⟨s, t, T, hv, hpos, harc, hF, hbox, himage, hout, hunbounded,
    B.three_pendant_closing_chord_period a,
    B.three_pendant_closing_chord_vertices_injOn vert a⟩

/-- Helper toward Proposition 5.16: two drawings with boundary-contact
leaves extend on the same combinatorial map to a common unbounded four-cycle.
In each drawing its geometric face is the outside of the chosen corner
quadrilateral. Every original position and dart arc is retained. -/
theorem exists_common_unbounded_corner_four_cycle {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q Q' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D) (hleaf : B.map.rot a = a)
    (R : ℝ) (hR : 0 < R)
    (hQ : Q.image ⊆ closure (Polyline.enclosingSquare R).inside)
    (hQ' : Q'.image ⊆ closure (Polyline.enclosingSquare R).inside)
    (hc : Q.pos (vert a) ∈ (Polyline.enclosingSquare R).image)
    (hc' : Q'.pos (vert a) ∈ (Polyline.enclosingSquare R).image) :
    let D₁ := B.insertPendant a
    let w₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    let x : D₃.D := .inr false
    let y : D₃.D := .inl (.inl (.inl a))
    let C := D₃.insertChord x y (by exact Sum.inr_ne_inl)
    let v := D₃.chordVert w₃ x y
    ∃ (s s' : ℂ) (t t' : ℝ)
      (T T' : PLDrawing C.D (Option (Option (Option V))) C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v) (O : D39BallFaceCycleOrbit C),
      let F := Polyline.mapPoints (fun z => s * z) (Polyline.rightCornerFrame R t)
      let F' := Polyline.mapPoints (fun z => s' * z) (Polyline.rightCornerFrame R t')
      (∀ z : V, T.pos (some (some (some z))) = Q.pos z) ∧
      (∀ z : V, T'.pos (some (some (some z))) = Q'.pos z) ∧
      (∀ d : B.D, T.arc (.inl (.inl (.inl (.inl d)))) = Q.arc d) ∧
      (∀ d : B.D, T'.arc (.inl (.inl (.inl (.inl d)))) = Q'.arc d) ∧
      F.IsCyclicSimple ∧ F'.IsCyclicSimple ∧
      T.image = Q.image ∪ F.image ∧ T'.image = Q'.image ∪ F'.image ∧
      (.inr false : C.D) ∈ O.val ∧
      Function.minimalPeriod C.map.faceSucc (.inr false) = 4 ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] (.inr false)))
        (Set.Iio 4) ∧
      (C.plOrbitFace v T hv O).val = F.outside ∧
      (C.plOrbitFace v T' hv O).val = F'.outside ∧
      (¬ Bornology.IsBounded (C.plOrbitFace v T hv O).val) ∧
      (¬ Bornology.IsBounded (C.plOrbitFace v T' hv O).val) := by
  dsimp only
  let D₁ := B.insertPendant a
  let w₁ := B.pendantVert vert a
  let D₂ := D₁.insertPendant (.inr false)
  let w₂ := D₁.pendantVert w₁ (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  let w₃ := D₂.pendantVert w₂ (.inr false)
  let x : D₃.D := .inr false
  let y : D₃.D := .inl (.inl (.inl a))
  let C := D₃.insertChord x y (by exact Sum.inr_ne_inl)
  let v := D₃.chordVert w₃ x y
  obtain ⟨s, t, T, hv, hp, ha, hF, hbox, hi, ho, hu, hperiod, hinj⟩ :=
    B.exists_closed_corner_frame_exterior vert Q hvert a hleaf R hR hQ hc
  obtain ⟨s', t', T', hv', hp', ha', hF', hbox', hi', ho', hu', hperiod', hinj'⟩ :=
    B.exists_closed_corner_frame_exterior vert Q' hvert a hleaf R hR hQ' hc'
  let O : D39BallFaceCycleOrbit C :=
    ⟨{e | C.map.faceSucc.SameCycle (.inr false) e}, .inr false, rfl⟩
  have hd : (.inr false : C.D) ∈ O.val := Equiv.Perm.SameCycle.refl _ _
  have heq := C.plOrbitFace_eq_plDartFace_of_mem v T hv O (.inr false) hd
  have heq' := C.plOrbitFace_eq_plDartFace_of_mem v T' hv O (.inr false) hd
  refine ⟨s, s', t, t', T, T', hv, O, hp, hp', ha, ha', hF, hF', hi, hi', hd,
    hperiod, hinj, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Subtype.val heq).trans ho
  · exact (congrArg Subtype.val heq').trans ho'
  · exact (congrArg Subtype.val heq).symm ▸ hu
  · exact (congrArg Subtype.val heq').symm ▸ hu'

end D39FiniteBall

end DirectedDistances.PlanarMap

end































































