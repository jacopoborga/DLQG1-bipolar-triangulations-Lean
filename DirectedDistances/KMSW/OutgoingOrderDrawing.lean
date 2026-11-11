module

public import DirectedDistances.KMSW.LeftmostGeodesicSubmap
public import DirectedDistances.KMSW.MonotoneLimitDrawing
import DirectedDistances.PlanarMap.MonotonePolyline
import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! # Outgoing order in the monotone drawing

Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Filter

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Every present forward dart initially points east. -/
theorem outgoing_initialDirection_re_pos (e : ℕ) (he : EdgePresent w e) :
    0 < ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection.re := by
  obtain ⟨n, hn, _⟩ := he
  have ha := monotoneLimitDrawing_arc_layout w hfin hfam n e hn false
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  apply Polyline.initialDirection_re_pos
  · rw [ha]
    exact layoutArc_points_pairwise w n e hn
  · exact (monotoneLimitDrawing w hfin hfam).arc_length (e, false)

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
The initial argument of a present forward dart lies strictly in the east half-plane. -/
theorem outgoing_initialDirection_arg_bounds (e : ℕ) (he : EdgePresent w e) :
    -(Real.pi / 2) <
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection ∧
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection <
        Real.pi / 2 := by
  exact abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (outgoing_initialDirection_re_pos w hfin hfam e he)))

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Every present incoming dart initially points west. -/
theorem incoming_initialDirection_re_neg (e : ℕ) (he : EdgePresent w e) :
    ((monotoneLimitDrawing w hfin hfam).arc (e, true)).initialDirection.re < 0 := by
  obtain ⟨n, hn, _⟩ := he
  have ha := monotoneLimitDrawing_arc_layout w hfin hfam n e hn false
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  rw [monotoneLimitDrawing_arc_layout w hfin hfam n e hn true]
  apply Polyline.reverse_initialDirection_re_neg
  · exact layoutArc_points_pairwise w n e hn
  · rw [← ha]
    exact (monotoneLimitDrawing w hfin hfam).arc_length (e, false)

private theorem backward_east_turn_after_west {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : c.re < 0)
    (hba : Complex.arg b < Complex.arg a) : ccwTurn a c < ccwTurn a b := by
  have hab := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hbb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have hnot : ¬Complex.arg a < Complex.arg b := not_lt.mpr hba.le
  by_cases him : c.im < 0
  · have hcb := (west_arg_lt_lower hc him).trans hbb.1
    have hca : ¬Complex.arg a < Complex.arg c := not_lt.mpr (hcb.trans hba).le
    simp only [ccwTurn, hnot, hca, ↓reduceIte]
    linarith only [hcb]
  · have hac := hab.2.trans (west_arg_gt_upper hc (le_of_not_gt him))
    simp only [ccwTurn, hnot, hac, ↓reduceIte]
    have hcp := Complex.arg_le_pi c
    linarith only [hcp, hbb.1, Real.pi_pos]

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
A counterclockwise step between distinct outgoing darts at a non-source vertex
strictly increases their arguments; an incoming dart prevents wraparound. -/
theorem outgoing_rotation_arg_lt_of_nonzero
    (hL : ∀ j, 0 ≤ L w j) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) (hv0 : v ≠ 0)
    (e f : ℕ) (he : EdgePresent w e) (hf : EdgePresent w f)
    (hev : edgeWest w e = v) (hfv : edgeWest w f = v) (hne : e ≠ f)
    (hrot : kmswInfRot w hfin (e, false) = (f, false)) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection <
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection := by
  let G := monotoneLimitDrawing w hfin hfam
  obtain ⟨i, hi, hiv⟩ := allocated_vertex_has_incoming_present_edge w hL v hv hv0
  have hr := G.rotation_agreement (e, false)
  rw [hrot] at hr
  have hargne : Complex.arg (G.arc (e, false)).initialDirection ≠
      Complex.arg (G.arc (f, false)).initialDirection := by
    intro h
    exact hne (congrArg Prod.fst (G.initial_arg_injective _ _
      (show kmswLimitDartVertex w (e, false) = kmswLimitDartVertex w (f, false)
        from hev.trans hfv.symm) h))
  rcases hr.2.2.2 with hs | hs
  · exact (hne (congrArg Prod.fst hs.1).symm).elim
  · by_contra hn
    have hback : Complex.arg (G.arc (f, false)).initialDirection <
        Complex.arg (G.arc (e, false)).initialDirection :=
      lt_of_le_of_ne (le_of_not_gt hn) hargne.symm
    have hmin := hs.2 (i, true)
      (show kmswLimitDartVertex w (i, true) = kmswLimitDartVertex w (e, false)
        from hiv.trans hev.symm) (by simp)
    exact (not_lt_of_ge hmin) (backward_east_turn_after_west
      (outgoing_initialDirection_re_pos w hfin hfam e he)
      (outgoing_initialDirection_re_pos w hfin hfam f hf)
      (incoming_initialDirection_re_neg w hfin hfam i hi) hback)

private theorem source_layoutHeight_zero (n : ℕ) : layoutHeight w n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [layoutHeight_old_vertex w n 0, ih]
    exact lt_of_lt_of_le (show 0 < (kmswStage w 0).nextVertex by change 0 < 2; omega)
      (CutConverse.nextVertex_mono w (Nat.zero_le n))

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
The root forward dart has initial argument zero. -/
theorem root_initialDirection_arg_zero :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (0, false)).initialDirection = 0 := by
  rw [monotoneLimitDrawing_arc_layout w hfin hfam 0 0 (by change 0 < 1; omega) false]
  norm_num [layoutArc, segmentArc, layoutPos, kmswStageRank, layoutHeight,
    Polyline.initialDirection, Polyline.point, Polyline.start]
  change Complex.arg (1 - 0 : ℂ) = 0
  simp only [sub_zero, Complex.arg_one]

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
All outgoing directions at the source have nonnegative argument. -/
theorem source_outgoing_initialDirection_arg_nonneg
    (e : ℕ) (he : EdgePresent w e) (hev : edgeWest w e = 0) :
    0 ≤ Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection := by
  obtain ⟨n, hn, _⟩ := he
  rw [monotoneLimitDrawing_arc_layout w hfin hfam n e hn false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Complex.arg_nonneg_iff.mpr
  have hz : (layoutArc w n e).point 1 ∈ (layoutArc w n e).image := by
    exact Or.inr ⟨0, by
      have hh := (monotoneLimitDrawing w hfin hfam).arc_length (e, false)
      rw [monotoneLimitDrawing_arc_layout w hfin hfam n e hn false] at hh
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      omega,
      right_mem_segment ℝ _ _⟩
  have hheight := layoutArc_height_lower w n e hn _ hz
  have hnonneg : 0 ≤ ((layoutArc w n e).point 1).im :=
    (le_min (layoutHeight_nonneg w n _) (layoutHeight_nonneg w n _)).trans hheight
  have hw : (kmswStage w n).west e = 0 :=
    (edge_endpoints_eq w hn).1.trans hev
  rw [Polyline.initialDirection, Complex.sub_im, layoutArc_start w n e hn]
  change 0 ≤ ((layoutArc w n e).point 1).im - layoutHeight w n ((kmswStage w n).west e)
  rw [hw, source_layoutHeight_zero w n, sub_zero]
  exact hnonneg

private theorem source_outgoing_rotation_arg_lt
    (e f : ℕ) (hf : EdgePresent w f)
    (hev : edgeWest w e = 0) (hfv : edgeWest w f = 0)
    (hne : e ≠ f) (hf0 : f ≠ 0)
    (hrot : kmswInfRot w hfin (e, false) = (f, false)) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection <
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection := by
  let G := monotoneLimitDrawing w hfin hfam
  have hfnonneg := source_outgoing_initialDirection_arg_nonneg w hfin hfam f hf hfv
  have hfpos : 0 < Complex.arg (G.arc (f, false)).initialDirection := by
    apply lt_of_le_of_ne hfnonneg
    intro hh
    have ha : Complex.arg (G.arc (f, false)).initialDirection =
        Complex.arg (G.arc (0, false)).initialDirection :=
      hh.symm.trans (root_initialDirection_arg_zero w hfin hfam).symm
    exact hf0 (congrArg Prod.fst (G.initial_arg_injective _ _
      (show kmswLimitDartVertex w (f, false) = kmswLimitDartVertex w (0, false)
        from hfv) ha))
  have hr := G.rotation_agreement (e, false)
  rw [hrot] at hr
  rcases hr.2.2.2 with hs | hs
  · exact (hne (congrArg Prod.fst hs.1).symm).elim
  · by_contra hn
    have hfe := le_of_not_gt hn
    have hepos := hfpos.trans_le hfe
    have he0 : (0, false) ≠ (e, false) := by
      intro hh
      have hh' : e = 0 := (congrArg Prod.fst hh).symm
      rw [hh', root_initialDirection_arg_zero w hfin hfam] at hepos
      exact (lt_irrefl 0) hepos
    have hmin := hs.2 (0, false)
      (show kmswLimitDartVertex w (0, false) = kmswLimitDartVertex w (e, false)
        from hev.symm) he0
    change ccwTurn (G.arc (e, false)).initialDirection (G.arc (f, false)).initialDirection ≤
      ccwTurn (G.arc (e, false)).initialDirection (G.arc (0, false)).initialDirection at hmin
    dsimp only [G] at hmin hfpos
    simp only [ccwTurn, not_lt.mpr hfe, ↓reduceIte,
      root_initialDirection_arg_zero w hfin hfam, not_lt.mpr hepos.le] at hmin
    linarith only [hmin, hfpos]

private theorem outgoing_ccw_list_arg_pairwise
    (hL : ∀ j, 0 ≤ L w j) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) (es : List ℕ)
    (hn : es.Nodup)
    (hm : ∀ e, e ∈ es ↔ EdgePresent w e ∧ edgeWest w e = v)
    (hc : es.IsChain (fun e f => kmswInfRot w hfin (e, false) = (f, false)))
    (hh : v = 0 → es.head? = some 0) :
    es.Pairwise (fun e f =>
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection <
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection) := by
  let G := monotoneLimitDrawing w hfin hfam
  let rel := fun e f : ℕ =>
    Complex.arg (G.arc (e, false)).initialDirection <
      Complex.arg (G.arc (f, false)).initialDirection
  have : IsTrans ℕ rel := ⟨fun _ _ _ => lt_trans⟩
  apply (List.isChain_iff_pairwise (R := rel)).mp
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i < es.length := by omega
  have he := (hm es[i]).1 (List.getElem_mem hi')
  have hf := (hm es[i + 1]).1 (List.getElem_mem hi)
  have hne : es[i] ≠ es[i + 1] := by
    intro heq
    have := hn.getElem_inj.mp heq
    omega
  have hrot := (List.isChain_iff_getElem.mp hc) i hi
  by_cases hv0 : v = 0
  · have hfirst := hh hv0
    have hzero : es[0]'(by omega) = 0 := by
      have hz := List.head?_eq_getElem? (l := es)
      rw [hfirst, List.getElem?_eq_getElem (show 0 < es.length by omega)] at hz
      exact (Option.some.inj hz).symm
    have hf0 : es[i + 1] ≠ 0 := by
      intro heq
      have := hn.getElem_inj.mp (heq.trans hzero.symm)
      omega
    exact source_outgoing_rotation_arg_lt w hfin hfam _ _ hf.1
      (he.2.trans hv0) (hf.2.trans hv0) hne hf0 hrot
  · exact outgoing_rotation_arg_lt_of_nonzero w hfin hfam hL v hv hv0
      _ _ he.1 hf.1 he.2 hf.2 hne hrot

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
The exhaustive outgoing list has strictly decreasing initial arguments. -/
theorem kmswOutgoingEdgesLeftToRight_arg_pairwise
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).Pairwise (fun e f =>
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection <
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection) := by
  classical
  unfold kmswOutgoingEdgesLeftToRight
  split
  · rename_i hv0
    apply List.pairwise_reverse.mpr
    have hs := (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec
    apply outgoing_ccw_list_arg_pairwise w hfin hfam hL v hv _ hs.1
    · intro e
      rw [hv0]
      exact hs.2.2.2.1 e
    · exact hs.2.2.2.2
    · intro _
      exact hs.2.1.trans (congrArg some (kmswRightBoundaryEdge_zero w))
  · rename_i hv0
    apply List.pairwise_reverse.mpr
    have hs := (kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hv0
      ).choose_spec.choose_spec.choose_spec
    exact outgoing_ccw_list_arg_pairwise w hfin hfam hL v hv _ hs.1 hs.2.2.2.1
      hs.2.2.2.2.1 (fun h => (hv0 h).elim)

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Outgoing edge indices agree exactly with decreasing initial argument in the drawing. -/
theorem kmswOutgoingEdgesLeftToRight_idxOf_lt_iff_arg_lt
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) (e f : ℕ)
    (he : e ∈ kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv)
    (hf : f ∈ kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv) :
    (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).idxOf e <
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).idxOf f ↔
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection <
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection := by
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv
  let G := monotoneLimitDrawing w hfin hfam
  have hp := kmswOutgoingEdgesLeftToRight_arg_pairwise w hfin hfam hL htrans hR v hv
  change es.Pairwise (fun e f =>
    Complex.arg (G.arc (f, false)).initialDirection <
      Complex.arg (G.arc (e, false)).initialDirection) at hp
  have hei := List.idxOf_lt_length_of_mem he
  have hfi := List.idxOf_lt_length_of_mem hf
  have forward : ∀ {a b : ℕ}, a ∈ es → b ∈ es → es.idxOf a < es.idxOf b →
      Complex.arg (G.arc (b, false)).initialDirection <
        Complex.arg (G.arc (a, false)).initialDirection := by
    intro a b ha hb hab
    have hh := List.pairwise_iff_getElem.mp hp (es.idxOf a) (es.idxOf b)
      (List.idxOf_lt_length_of_mem ha) (List.idxOf_lt_length_of_mem hb) hab
    simpa only [List.getElem_idxOf] using hh
  constructor
  · exact forward he hf
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
    · exact (lt_asymm h (forward hf he hlt))
    · have hef : e = f := by
        have hh := congrArg (fun i => es[i]?) heq
        rw [List.getElem?_eq_getElem hfi, List.getElem?_eq_getElem hei,
          List.getElem_idxOf, List.getElem_idxOf] at hh
        exact (Option.some.inj hh).symm
      subst f
      exact (lt_irrefl _) h

end DirectedDistances.KMSW
