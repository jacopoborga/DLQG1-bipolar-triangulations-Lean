/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideRecognition

/-! The glued whole-plane rotation is the counterclockwise successor of the
polyline departure directions at every vertex. The clockwise scan therefore
uses its inverse. Least-return indices identify its cyclic order with departure
angles, including the incoming-corner wrap. The retained scan and coherent
ambient lift establish the intrinsic first-admissible selector for the
side-coded previous geodesic. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

/-- Helper toward Lemma 5.6: if a direction `x` occurs strictly before `z`
when turning counterclockwise from `y`, then the turn from `x` to `z` is the
remaining part of that turn and is strictly shorter. -/
private theorem ccwTurn_remaining_lt (y x z : ℂ)
    (h : ccwTurn y x < ccwTurn y z) :
    ccwTurn x z < ccwTurn y z := by
  unfold ccwTurn at h ⊢
  by_cases hyx : Complex.arg y < Complex.arg x
  · by_cases hyz : Complex.arg y < Complex.arg z
    · have hxz : Complex.arg x < Complex.arg z := by
        simp [hyx, hyz] at h
        linarith
      simp [hyx, hyz, hxz]
    · have hzx : Complex.arg z < Complex.arg x := by
        have := Complex.neg_pi_lt_arg z
        have := Complex.arg_le_pi x
        simp [hyx, hyz] at h
        linarith
      simp only [ite_eq_right (not_lt_of_ge hzx.le), ite_eq_right hyz]
      linarith only [hyx]
  · by_cases hyz : Complex.arg y < Complex.arg z
    · have := Complex.neg_pi_lt_arg x
      have := Complex.arg_le_pi z
      simp [hyx, hyz] at h
      linarith
    · have hxz : Complex.arg x < Complex.arg z := by
        simp [hyx, hyz] at h
        linarith
      have hx := Complex.neg_pi_lt_arg x
      have hy := Complex.arg_le_pi y
      simp [hyz, hxz]
      linarith

/-- Helper toward Lemma 5.6: with a fixed initial direction, equality of
positive turns forces equality of the terminal arguments. The canonical range
`(-pi, pi]` handles the branch cut. -/
private theorem ccwTurn_eq_arg_eq (a b c : ℂ)
    (h : ccwTurn a b = ccwTurn a c) : Complex.arg b = Complex.arg c := by
  unfold ccwTurn at h
  by_cases hab : Complex.arg a < Complex.arg b
  · by_cases hac : Complex.arg a < Complex.arg c
    · simp [hab, hac] at h
      linarith
    · simp [hab, hac] at h
      have hb := Complex.arg_le_pi b
      have hc := Complex.neg_pi_lt_arg c
      linarith
  · by_cases hac : Complex.arg a < Complex.arg c
    · simp [hab, hac] at h
      have hb := Complex.neg_pi_lt_arg b
      have hc := Complex.arg_le_pi c
      linarith
    · simp [hab, hac] at h
      linarith

/-- Helper toward Lemma 5.6: rotation agreement for the whole-plane drawing,
with its directions read from the initial directions of the actual PL arcs. -/
theorem m0WholePlaneDrawing_rotation_agreement
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (d : WholePlaneDart W) :
    CcwSuccessor
      {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d}
      (fun e =>
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc e).initialDirection)
      d (wholePlaneRotation W H d) :=
  (WholePlanePastGlueDrawing.glueDrawing W h hp H).rotation_agreement d

/-- Helper toward Lemma 5.6: a clockwise successor step in the ambient
rotation is bounded by the counterclockwise turn to every other dart in the
same star. The turn from `b` to `a` is the clockwise displacement from `a`
to its immediate clockwise successor `b`. -/
theorem m0WholePlaneDrawing_clockwiseStep_ccwTurn_le
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    {a b c : WholePlaneDart W}
    (hab : a ≠ b)
    (hstep : (wholePlaneRotation W H).symm a = b)
    (hc : wholePlaneDartVertex W c = wholePlaneDartVertex W b)
    (hcb : c ≠ b) :
    ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) ≤
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hrot : wholePlaneRotation W H b = a := by
    calc
      wholePlaneRotation W H b = wholePlaneRotation W H
          ((wholePlaneRotation W H).symm a) := congrArg (wholePlaneRotation W H) hstep.symm
      _ = a := Equiv.apply_symm_apply (wholePlaneRotation W H) a
  have hsucc : CcwSuccessor
      {e | wholePlaneDartVertex W e = wholePlaneDartVertex W b}
      (fun e => (G.arc e).initialDirection) b a := by
    simpa only [hrot] using G.rotation_agreement b
  rcases hsucc with ⟨_, _, _, hcase⟩
  rcases hcase with ⟨heq, _⟩ | ⟨_, hmin⟩
  · exact (hab heq).elim
  · exact hmin c hc hcb

/-- Helper toward Lemma 5.6: from a dart `b`, its counterclockwise
successor `a` has strictly smaller turn than any other dart in that star.
The turn from `b` to `a` is also the clockwise displacement from `a` to `b`. -/
theorem m0WholePlaneDrawing_clockwiseStep_ccwTurn_lt
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    {a b c : WholePlaneDart W}
    (hab : a ≠ b)
    (hstep : (wholePlaneRotation W H).symm a = b)
    (hc : wholePlaneDartVertex W c = wholePlaneDartVertex W b)
    (hcb : c ≠ b) (hca : c ≠ a) :
    ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hle := m0WholePlaneDrawing_clockwiseStep_ccwTurn_le
    (W := W) (H := H) (h := h) (hp := hp) hab hstep hc hcb
  have hrot : wholePlaneRotation W H b = a := by
    calc
      wholePlaneRotation W H b = wholePlaneRotation W H
          ((wholePlaneRotation W H).symm a) := congrArg (wholePlaneRotation W H) hstep.symm
      _ = a := Equiv.apply_symm_apply (wholePlaneRotation W H) a
  have hvab : wholePlaneDartVertex W a = wholePlaneDartVertex W b := by
    simpa [hrot] using G.vert_rotation b
  have hvac : wholePlaneDartVertex W a = wholePlaneDartVertex W c := hvab.trans hc.symm
  have hturn :
      ccwTurn (G.arc b).initialDirection (G.arc a).initialDirection ≠
        ccwTurn (G.arc b).initialDirection (G.arc c).initialDirection := by
    intro heq
    have harg := ccwTurn_eq_arg_eq (G.arc b).initialDirection
      (G.arc a).initialDirection (G.arc c).initialDirection heq
    have hac : a = c := G.initial_arg_injective a c hvac harg
    exact hca hac.symm
  exact lt_of_le_of_ne hle hturn

/-- Helper toward Lemma 5.6: before a clockwise orbit returns to its start,
each step after the first strictly increases clockwise departure angle from
that start. The hypotheses assert only nonreturn and that the permutation
step moves to a distinct dart. -/
theorem m0WholePlane_clockwiseIterate_departureAngle_step
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (a : WholePlaneDart W) (i : ℕ)
    (hprev : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i] a ≠ a)
    (hnext : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i + 1] a ≠ a)
    (hadj : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i] a ≠
      ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i + 1] a) :
    ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i] a)).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[i + 1] a)).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
  let σ : WholePlaneDart W → WholePlaneDart W := (wholePlaneRotation W H).symm
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hpres (d : WholePlaneDart W) : wholePlaneDartVertex W (σ d) =
      wholePlaneDartVertex W d := by
    have hrot : wholePlaneRotation W H (σ d) = d := Equiv.apply_symm_apply _ _
    have hv := G.vert_rotation (σ d)
    rw [hrot] at hv
    exact hv.symm
  have hvIter (j : ℕ) : wholePlaneDartVertex W (σ^[j] a) =
      wholePlaneDartVertex W a := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hpres _).trans ih
  have hstep : σ (σ^[i] a) = σ^[i + 1] a := by
    simpa only [Nat.add_one] using (Function.iterate_succ_apply' σ i a).symm
  have hangle := m0WholePlaneDrawing_clockwiseStep_ccwTurn_lt
    (W := W) (H := H) (h := h) (hp := hp) hadj hstep
    (hvIter (i + 1)).symm (Ne.symm hnext) (Ne.symm hprev)
  exact ccwTurn_remaining_lt (G.arc (σ^[i + 1] a)).initialDirection
    (G.arc (σ^[i] a)).initialDirection (G.arc a).initialDirection hangle

/-- Helper toward Lemma 5.6: distinct iterates before the first return
come from distinct indices. -/
private theorem clockwiseIterate_injective_before_return {α : Type*}
    (σ : Equiv.Perm α) (a : α) (r : ℕ)
    (hfirst : ∀ j, 0 < j → j < r → σ^[j] a ≠ a)
    (i j : ℕ) (hj : j < r) (hij : i < j) :
    σ^[i] a ≠ σ^[j] a := by
  intro he
  have hdecomp : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have he' : σ^[i] a = σ^[i] (σ^[j - i] a) := by
    rw [← hdecomp, Function.iterate_add_apply] at he
    exact he
  have hfix : a = σ^[j - i] a := (σ.injective.iterate i) he'
  exact hfirst (j - i) (Nat.sub_pos_of_lt hij) (by omega) hfix.symm

/-- Helper toward Lemma 5.6: along the inverse rotation orbit, clockwise
departure angles from the starting dart strictly increase between any two
positive iterates before the first return. -/
theorem m0WholePlane_clockwiseIterate_departureAngle_lt
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (a : WholePlaneDart W) (r : ℕ)
    (hfirst : ∀ j, 0 < j → j < r →
      ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[j] a ≠ a)
    {m n : ℕ} (hm : 0 < m) (hmn : m < n) (hn : n < r) :
    ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[m] a)).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[n] a)).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
  let σ : Equiv.Perm (WholePlaneDart W) := (wholePlaneRotation W H).symm
  have hstep (j : ℕ) (hj : 0 < j) (hjr : j + 1 < r) :
      ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc (σ^[j] a)).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
        ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc (σ^[j + 1] a)).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
    have hprev : σ^[j] a ≠ a := hfirst j hj (by omega)
    have hnext : σ^[j + 1] a ≠ a := hfirst (j + 1) (by omega) hjr
    have hadj : σ^[j] a ≠ σ^[j + 1] a :=
      clockwiseIterate_injective_before_return σ a r hfirst j (j + 1) hjr (by omega)
    exact m0WholePlane_clockwiseIterate_departureAngle_step
      (W := W) (H := H) (h := h) (hp := hp) a j hprev hnext hadj
  have hgrow : ∀ k j : ℕ, 0 < j → j < k → k < r →
      ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc (σ^[j] a)).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
        ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc (σ^[k] a)).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
    intro k
    induction k with
    | zero => intro j hj hjk; omega
    | succ k ih =>
      intro j hj hjk hk
      by_cases hjk' : j = k
      · subst j
        exact hstep k hj hk
      · have hjk'' : j < k := by omega
        exact lt_trans (ih j hj hjk'' (by omega)) (hstep k (by omega) hk)
  exact hgrow n m hm hmn hn

/-- Helper toward Lemma 5.6: for two darts already identified as positive
inverse-rotation iterates before the first return, their strict clockwise
encounter order is equivalent to the strict comparison of departure angles
measured clockwise from the starting dart. -/
theorem m0WholePlane_clockwiseIterate_order_iff_departureAngle
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (a b c : WholePlaneDart W) (r : ℕ)
    (_hreturn : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r] a = a)
    (hfirst : ∀ j, 0 < j → j < r →
      ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[j] a ≠ a)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmr : m < r) (hnr : n < r)
    (hb : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[m] a = b)
    (hc : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[n] a = c) :
    m < n ↔
      ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
        ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
  constructor
  · intro hmn
    have hlt := m0WholePlane_clockwiseIterate_departureAngle_lt
      (W := W) (H := H) (h := h) (hp := hp) a r hfirst hm hmn hnr
    rw [hb, hc] at hlt
    exact hlt
  · intro hang
    by_contra hmn
    have hnm : n < m := by
      by_contra h
      have hmn' : m ≤ n := Nat.le_of_not_gt h
      have hnm' : n ≤ m := Nat.le_of_not_gt hmn
      have heq : m = n := Nat.le_antisymm hmn' hnm'
      rw [← hb, ← hc, heq] at hang
      exact (lt_irrefl _) hang
    have hrev := m0WholePlane_clockwiseIterate_departureAngle_lt
      (W := W) (H := H) (h := h) (hp := hp) a r hfirst hn hnm hmr
    rw [hc, hb] at hrev
    exact (not_lt_of_gt hrev) hang

/-- Helper toward Lemma 5.6: at an actual incoming corner, the clockwise
first-return order of two outgoing iterates agrees with their departure-angle
order. Positive iterates and the least-return bound retain wraparound. -/
theorem m0WholePlane_incomingCorner_iterate_order_iff_departureAngle
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (e : ℕ) (b c : WholePlaneDart W) (r : ℕ)
    (_hreturn : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r]
      (wholePlaneDartι W 0 (e, true)) = wholePlaneDartι W 0 (e, true))
    (hfirst : ∀ j, 0 < j → j < r →
      ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[j]
        (wholePlaneDartι W 0 (e, true)) ≠ wholePlaneDartι W 0 (e, true))
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmr : m < r) (hnr : n < r)
    (hb : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[m]
      (wholePlaneDartι W 0 (e, true)) = b)
    (hc : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[n]
      (wholePlaneDartι W 0 (e, true)) = c) :
    m < n ↔
      ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
            (wholePlaneDartι W 0 (e, true))).initialDirection) <
        ccwTurn
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection)
          (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
            (wholePlaneDartι W 0 (e, true))).initialDirection) := by
  exact m0WholePlane_clockwiseIterate_order_iff_departureAngle
    (W := W) (H := H) (h := h) (hp := hp)
    (wholePlaneDartι W 0 (e, true)) b c r _hreturn hfirst m n hm hn hmr hnr hb hc

/-- Helper toward Lemma 5.6: the departure argument distinguishes any two
whole-plane darts at the same vertex. -/
theorem m0WholePlaneDrawing_departureArg_injective
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    {a b : WholePlaneDart W}
    (hv : wholePlaneDartVertex W a = wholePlaneDartVertex W b)
    (harg : Complex.arg
      (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) =
      Complex.arg
      (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)) :
    a = b :=
  (WholePlanePastGlueDrawing.glueDrawing W h hp H).initial_arg_injective a b hv harg

/-- Helper toward Lemma 5.6: every other dart at the starting vertex occurs
at a positive clockwise index before the least positive return. -/
theorem m0WholePlane_clockwiseFirstReturn_indices
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (a : WholePlaneDart W) :
    ∃ r : ℕ, 0 < r ∧
      ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r] a = a ∧
      (∀ j, 0 < j → j < r →
        ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[j] a ≠ a) ∧
      ∀ b : WholePlaneDart W, wholePlaneDartVertex W b = wholePlaneDartVertex W a →
        b ≠ a → ∃ m : ℕ, 0 < m ∧ m < r ∧
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[m] a = b := by
  classical
  let τ := wholePlaneRotation W H
  let σ : WholePlaneDart W → WholePlaneDart W := τ.symm
  have hinverse (b : WholePlaneDart W) (m : ℕ) (hm : (τ ^ m) b = a) :
      σ^[m] a = b := by
    have he := permIterateInvSub τ (Nat.le_refl m) b
    rw [permIterateEqPow τ m, hm] at he
    simpa only [Equiv.Perm.inv_def, Nat.sub_self, Function.iterate_zero_apply] using he
  obtain ⟨p, hp, hperiod⟩ := wholePlaneRotation_exists_period W H a
  have hex : ∃ r : ℕ, 0 < r ∧ σ^[r] a = a :=
    ⟨p, hp, hinverse a p hperiod⟩
  let r := Nat.find hex
  have hr : 0 < r ∧ σ^[r] a = a := Nat.find_spec hex
  refine ⟨r, hr.1, hr.2, ?_, ?_⟩
  · intro j hj hjr hret
    exact Nat.find_min hex hjr ⟨hj, hret⟩
  · intro b hvertex hba
    obtain ⟨m, hm⟩ := wholePlaneRotation_exists_pow_of_base W H b a hvertex
    have hreach : σ^[m] a = b := hinverse b m hm
    have hmod : σ^[m % r] a = b :=
      (Function.IsPeriodicPt.iterate_mod_apply hr.2 m).trans hreach
    refine ⟨m % r, ?_, Nat.mod_lt m hr.1, hmod⟩
    by_contra hnot
    have hz : m % r = 0 := by omega
    rw [hz, Function.iterate_zero_apply] at hmod
    exact hba hmod.symm

/-- Helper toward Lemma 5.6: strict encounter order in the full clockwise
first-return scan is exactly strict clockwise departure-angle order. -/
theorem m0WholePlane_clockwiseFirstReturn_before_iff_departureAngle
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (v : WholePlaneVertex W) (a b c : WholePlaneDart W)
    (ha : wholePlaneDartVertex W a = v)
    (hb : wholePlaneDartVertex W b = v)
    (hc : wholePlaneDartVertex W c = v)
    (hab : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c) :
    (∃ r m n : ℕ,
      0 < r ∧ (wholePlaneRotation W H).symm^[r] a = a ∧
      (∀ j, 0 < j → j < r → (wholePlaneRotation W H).symm^[j] a ≠ a) ∧
      0 < m ∧ m < n ∧ n < r ∧
      (wholePlaneRotation W H).symm^[m] a = b ∧
      (wholePlaneRotation W H).symm^[n] a = c) ↔
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc a).initialDirection) := by
  constructor
  · rintro ⟨r, m, n, _, hreturn, hfirst, hm, hmn, hnr, hmb, hnc⟩
    exact (m0WholePlane_clockwiseIterate_order_iff_departureAngle
      (W := W) (H := H) (h := h) (hp := hp)
      a b c r hreturn hfirst m n hm (by omega) (by omega) hnr hmb hnc).1 hmn
  · intro hang
    obtain ⟨r, hr, hreturn, hfirst, hindices⟩ :=
      m0WholePlane_clockwiseFirstReturn_indices (H := H) a
    obtain ⟨m, hm, hmr, hmb⟩ := hindices b (hb.trans ha.symm) hab.symm
    obtain ⟨n, hn, hnr, hnc⟩ := hindices c (hc.trans ha.symm) hac.symm
    have hmn := (m0WholePlane_clockwiseIterate_order_iff_departureAngle
      (W := W) (H := H) (h := h) (hp := hp)
      a b c r hreturn hfirst m n hm hn hmr hnr hmb hnc).2 hang
    exact ⟨r, m, n, hr, hreturn, hfirst, hm, hmn, hnr, hmb, hnc⟩

/-- Helper toward Lemma 5.6: full clockwise first-return order at the
reversed incoming dart agrees with clockwise departure-angle order, including
the cyclic wrap through the argument cut. -/
theorem m0WholePlane_incomingCornerFirstReturn_before_iff_departureAngle
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (v : WholePlaneVertex W) (e : ℕ) (b c : WholePlaneDart W)
    (ha : wholePlaneDartVertex W (wholePlaneDartι W 0 (e, true)) = v)
    (hb : wholePlaneDartVertex W b = v)
    (hc : wholePlaneDartVertex W c = v)
    (hab : wholePlaneDartι W 0 (e, true) ≠ b)
    (hac : wholePlaneDartι W 0 (e, true) ≠ c) (hbc : b ≠ c) :
    (∃ r m n : ℕ,
      0 < r ∧ (wholePlaneRotation W H).symm^[r]
          (wholePlaneDartι W 0 (e, true)) = wholePlaneDartι W 0 (e, true) ∧
      (∀ j, 0 < j → j < r → (wholePlaneRotation W H).symm^[j]
          (wholePlaneDartι W 0 (e, true)) ≠ wholePlaneDartι W 0 (e, true)) ∧
      0 < m ∧ m < n ∧ n < r ∧
      (wholePlaneRotation W H).symm^[m] (wholePlaneDartι W 0 (e, true)) = b ∧
      (wholePlaneRotation W H).symm^[n] (wholePlaneDartι W 0 (e, true)) = c) ↔
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc b).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (e, true))).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc c).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (e, true))).initialDirection) := by
  exact m0WholePlane_clockwiseFirstReturn_before_iff_departureAngle
    (W := W) (H := H) (h := h) (hp := hp)
    v (wholePlaneDartι W 0 (e, true)) b c ha hb hc hab hac hbc

/-- Helper toward Lemma 5.6: from a west-pointing incoming direction,
clockwise order of east-pointing departures is decreasing raw argument.
The east/west turn formula includes both branches of the argument cut. -/
theorem ccwTurn_east_west_lt_iff_arg_lt (a b c : ℂ)
    (ha : a.re < 0) (hb : 0 < b.re) (hc : 0 < c.re) :
    ccwTurn b a < ccwTurn c a ↔ Complex.arg c < Complex.arg b := by
  rw [east_west_turn_formula hb ha, east_west_turn_formula hc ha]
  constructor <;> intro h <;> linarith only [h]

/-- Helper toward Lemma 5.6: all run-zero reversed geometric darts point
west in the raw drawing, including missing boundary darts. -/
theorem m0RawDrawing_incoming_initialDirection_re_neg
    {W : ℤ → Fin 3} (H : WholePlaneRotationHypothesis W) (e : ℕ) :
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc (e, true)).initialDirection.re < 0 := by
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P) :=
    fun n => ⟨monotoneLayoutDrawing w n (monotone_family_all w n).choose,
      (monotone_family_all w n).choose_spec⟩
  let G := monotoneLimitDrawing w (H.1 0) hfam
  change (G.arc (e, true)).initialDirection.re < 0
  have hn := kmsw_edge_allocated_by_self w e
  have ha := monotoneLimitDrawing_arc_layout w (H.1 0) hfam e e hn false
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  rw [monotoneLimitDrawing_arc_layout w (H.1 0) hfam e e hn true]
  apply Polyline.reverse_initialDirection_re_neg
  · exact layoutArc_points_pairwise w e e hn
  · rw [← ha]
    exact G.arc_length (e, false)

/-- Helper toward Lemma 5.6: at an incoming run-zero corner, comparison of
clockwise departure angles in the glued drawing is exactly the reversed raw
argument comparison used by `SharedDepartureArgRightOf`. -/
theorem m0WholePlane_incomingCorner_ccwTurn_lt_iff_rawArg_lt
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    (e b c : ℕ) (hb : EdgePresent (shiftedStream W 0) b)
    (hc : EdgePresent (shiftedStream W 0) c) :
    ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (b, false))).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (e, true))).initialDirection) <
      ccwTurn
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (c, false))).initialDirection)
        (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (e, true))).initialDirection) ↔
      Complex.arg ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (c, false)).initialDirection <
      Complex.arg ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (b, false)).initialDirection := by
  rw [WholePlanePastGlueM0Restriction.restrict_arc W h hp H (b, false),
    WholePlanePastGlueM0Restriction.restrict_arc W h hp H (c, false),
    WholePlanePastGlueM0Restriction.restrict_arc W h hp H (e, true)]
  exact ccwTurn_east_west_lt_iff_arg_lt _ _ _
    (m0RawDrawing_incoming_initialDirection_re_neg H e)
    (outgoing_initialDirection_re_pos _ _ _ b hb)
    (outgoing_initialDirection_re_pos _ _ _ c hc)

/-- Helper toward Lemma 5.6: a finite ambient orbit segment induces a scan
of retained darts; every earlier scan entry has an earlier ambient index. -/
private theorem retainedEmbeddingScan_exists {α β : Type*}
    (τ : β → β) (I : α → β) (hI : Function.Injective I) (S : Set α)
    (a b : S) (n : ℕ) (hend : τ^[n] (I a.val) = I b.val) :
    ∃ (f : ℕ → S) (m : ℕ), f 0 = a ∧ f m = b ∧
      (∀ j, j < m → ∃ r : ℕ, 0 < r ∧
        τ^[r] (I (f j).val) = I (f (j + 1)).val ∧
        ∀ t : ℕ, 0 < t → t < r → τ^[t] (I (f j).val) ∉ I '' S) ∧
      ∀ j, j < m → ∃ t : ℕ, t < n ∧ τ^[t] (I a.val) = I (f j).val := by
  classical
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hab : a = b := Subtype.ext (hI hend)
      exact ⟨fun _ => a, 0, rfl, hab,
        fun _ hj => (Nat.not_lt_zero _ hj).elim,
        fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
    · have hex : ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ τ^[r] (I a.val) ∈ I '' S :=
        ⟨n, by omega, le_rfl, b.val, b.property, hend.symm⟩
      let r := Nat.find hex
      have hr : 0 < r ∧ r ≤ n ∧ τ^[r] (I a.val) ∈ I '' S := Nat.find_spec hex
      obtain ⟨cval, hcval, hc⟩ := hr.2.2
      let c : S := ⟨cval, hcval⟩
      have hskip (t : ℕ) (ht : 0 < t) (htr : t < r) :
          τ^[t] (I a.val) ∉ I '' S := by
        intro hm
        have hmin : r ≤ t := Nat.find_min' hex ⟨ht, by omega, hm⟩
        omega
      have hnext : τ^[n - r] (I c.val) = I b.val := by
        rw [hc, ← Function.iterate_add_apply, Nat.sub_add_cancel hr.2.1]
        exact hend
      obtain ⟨g, m, hg0, hgm, hstep, hearlier⟩ :=
        ih (n - r) (by omega) c b hnext
      refine ⟨fun j => Nat.casesOn j a g, m + 1, rfl, hgm, ?_, ?_⟩
      · intro j hj
        cases j with
        | zero =>
          refine ⟨r, hr.1, ?_, hskip⟩
          change τ^[r] (I a.val) = I (g 0).val
          rw [hg0]
          exact hc.symm
        | succ j => exact hstep j (by omega)
      · intro j hj
        cases j with
        | zero => exact ⟨0, by omega, rfl⟩
        | succ j =>
          obtain ⟨t, ht, he⟩ := hearlier j (by omega)
          refine ⟨t + r, by omega, ?_⟩
          rw [Function.iterate_add_apply, ← hc]
          exact he

/-- Helper toward Lemma 5.6: the side admits a clockwise scan to a retained
ambient endpoint, with all earlier entries strictly before that endpoint's
ambient iterate index. -/
theorem m0GeodesicSide_clockwiseScan_before_ambientEndpoint
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (a b : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (n : ℕ)
    (hend : ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[n]
      (wholePlaneDartι W 0 a.val) = wholePlaneDartι W 0 b.val) :
    ∃ (f : ℕ → GeometricSideCell (m0GeodesicSide hp P s)) (m : ℕ),
      geometricSideClockwiseScan (m0GeodesicSide hp P s) (.inr a) f m ∧
      f m = .inr b ∧
      ∀ j, j < m → ∃ (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
        (t : ℕ), f j = .inr d ∧ t < n ∧
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[t]
            (wholePlaneDartι W 0 a.val) = wholePlaneDartι W 0 d.val := by
  have hI : Function.Injective (wholePlaneDartι W 0) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    change (wholePlaneEdgeι W 0 a, b) = (wholePlaneEdgeι W 0 c, d) at he
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst he))
      (congrArg (fun x : WholePlaneEdge W × Bool => x.2) he)
  obtain ⟨g, m, hg0, hgm, hstep, hearlier⟩ := retainedEmbeddingScan_exists
    ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)
    (wholePlaneDartι W 0) hI {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P s).edges}
    a b n hend
  refine ⟨fun j => .inr (g j), m, ⟨congrArg Sum.inr hg0, ?_⟩,
    congrArg Sum.inr hgm, ?_⟩
  · intro j hj
    exact (m0GeodesicSide_clockwiseStep_iff_wholePlane hp P s (g j) (g (j + 1))).2
      (hstep j hj)
  · intro j hj
    obtain ⟨t, ht, he⟩ := hearlier j hj
    exact ⟨g j, t, rfl, ht, he⟩

/-- Helper toward Lemma 5.6: the supplied ambient cut-leftmost comparison
orders raw departure arguments at every shared vertex in either metric mode. -/
theorem m0CutLeftmostXdp_raw_departureArg_le
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T)
    (i j : ℕ) (hv : (P.codePath.initial i).1 = (Q.codePath.initial j).1) :
    Complex.arg ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc (Q.codePath.edge j, false)).initialDirection ≤
    Complex.arg ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc (P.codePath.edge i, false)).initialDirection := by
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
    fun n => ⟨monotoneLayoutDrawing w n (monotone_family_all w n).choose,
      (monotone_family_all w n).choose_spec⟩
  have hsub : pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
      (fun n => (Q.codePath.edge n, false)) ⊆
      closedBetween
        (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
          (fun n => (P.codePath.edge n, false)))
        (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
          (fun n => (T.edge n, false))) := by
    cases longest with
    | false =>
      exact (Xdp.Sdp.cutLeftmost_iff_runZero W H h hp hLL k P T).1 hleft Q.codePath Q.segments
    | true =>
      exact (Xdp.cutLeftmost_iff_runZero W H h hp hLL k P T).1 hleft Q.codePath Q.segments
  exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
    w (H.1 0) hfam (boundaryVertex w h k) P.codePath T Q.codePath).1 hsub).1 i j hv

/-- Helper toward Lemma 5.6: the previous ambient geodesic is the side's
intrinsic first-admissible clockwise ray. An earlier competing departure would
have a larger raw argument, contradicting the supplied cut-leftmost comparison. -/
theorem m0GeodesicSide_adjacentIntrinsicSelector_angleComparison
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSideAdjacentGeodesicCandidate
        (m0GeodesicSide hp (P k) .left) longest v d ∧
      IntrinsicallyLeftmostAdjacentRay
        (m0GeodesicSide hp (P k) .left) longest v d := by
  classical
  let M := m0GeodesicSide hp (P k) .left
  let w := shiftedStream W 0
  let d := m0GeodesicSideAdjacentDarts hp P k hcontain
  have hcand := m0GeodesicSide_realized_adjacentCandidate hp P k hcontain
  refine ⟨m0GeodesicSideAdjacentVertices hp P k hcontain, d, hcand, hcand, ?_⟩
  intro i
  have hcorner : ∃ (a : {d : ℕ × Bool // d.1 ∈ M.edges}) (e : ℕ),
      a.val = (e, true) ∧ geometricSideRayIncomingCorner M d i (.inr a) ∧
      geometricSideDartInitial M a.val = ((P (k - 1)).codePath.initial i).1.id := by
    cases i with
    | zero =>
      let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
        ⟨M.boundary 1, m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩
      refine ⟨a, (M.boundary 1).1, rfl, rfl, ?_⟩
      exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
        (m0Geodesic_initial_zero (P (k - 1))).symm
    | succ j =>
      refine ⟨⟨((P (k - 1)).codePath.edge j, true), (hcontain j).1⟩,
        (P (k - 1)).codePath.edge j, rfl, rfl, ?_⟩
      exact ((P (k - 1)).codePath.edge_incoming_at_succ w j).2
  obtain ⟨a, e, ha, hcorner, hav⟩ := hcorner
  let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((P (k - 1)).codePath.edge i, false), (hcontain i).1⟩
  have hv : wholePlaneDartVertex W (wholePlaneDartι W 0 b.val) =
      wholePlaneDartVertex W (wholePlaneDartι W 0 a.val) := by
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    apply congrArg (wholePlaneVertexι W 0)
    exact ((P (k - 1)).codePath.edge_outgoing_at_initial w i).2.trans hav.symm
  have hba : wholePlaneDartι W 0 b.val ≠ wholePlaneDartι W 0 a.val := by
    intro he
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) he
    change false = a.val.2 at hbit
    rw [ha] at hbit
    cases hbit
  obtain ⟨r, _, hreturn, hfirst, hindices⟩ :=
    m0WholePlane_clockwiseFirstReturn_indices (H := H) (wholePlaneDartι W 0 a.val)
  obtain ⟨n, hn, hnr, hnb⟩ := hindices (wholePlaneDartι W 0 b.val) hv hba
  obtain ⟨f, m, hscan, hend, hearlier⟩ :=
    m0GeodesicSide_clockwiseScan_before_ambientEndpoint hp (P k) .left a b n hnb
  refine ⟨.inr a, f, m, hcorner, hscan, hend, ?_⟩
  intro v' d' hcandidate hpref j hj heq
  obtain ⟨Q, u, q, huv, hdq, hQu, hQq⟩ :=
    m0GeodesicLeftSide_adjacentCandidate_coherentAmbientLift hp (P k) hcandidate
  have hprefEdge (t : ℕ) (ht : t < i) :
      Q.codePath.edge t = (P (k - 1)).codePath.edge t := by
    have he := (hdq t).symm.trans ((hpref t ht).trans rfl)
    have he' := congrArg Subtype.val (Sum.inr.inj he)
    exact (hQq t).trans (congrArg Prod.fst he')
  have hvertex : ((P (k - 1)).codePath.initial i).1 = (Q.codePath.initial i).1 := by
    apply InfinitePresentPath.initial_vertex_eq_of_prefix_eq
    apply congrArg List.ofFn
    funext t
    exact (hprefEdge t.val t.isLt).symm
  have harg := m0CutLeftmostXdp_raw_departureArg_le hp (P (k - 1)) Q
    (T (k - 1)) (hleft (k - 1)) i i hvertex
  obtain ⟨c, t, hfc, htn, htc⟩ := hearlier j hj
  have hcq : c.val = ((q i).val, false) := by
    exact congrArg Subtype.val (Sum.inr.inj (hfc.symm.trans (heq.trans (hdq i))))
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have htc0 : (wholePlaneDartι W 0 a.val : WholePlaneDart W) =
        wholePlaneDartι W 0 c.val := by
      subst t
      exact htc
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) htc0
    change a.val.2 = c.val.2 at hbit
    rw [ha, hcq] at hbit
    cases hbit
  have hang := m0WholePlane_clockwiseIterate_departureAngle_lt
    (W := W) (H := H) (h := h) (hp := hp) (wholePlaneDartι W 0 a.val) r
    hfirst htpos htn hnr
  rw [htc, hnb, ha, hcq, ← hQq i] at hang
  have hraw := (m0WholePlane_incomingCorner_ccwTurn_lt_iff_rawArg_lt
    (W := W) (H := H) (h := h) (hp := hp) e (Q.codePath.edge i)
    ((P (k - 1)).codePath.edge i)
    (Q.codePath.edge_outgoing_at_initial w i).1
    ((P (k - 1)).codePath.edge_outgoing_at_initial w i).1).1 hang
  exact (not_lt_of_ge harg) hraw

end DirectedDistances.PaperProofs.Section5

