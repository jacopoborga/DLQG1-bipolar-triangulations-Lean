/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart2
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFaceTriangles
public import DirectedDistances.KMSW.WholePlaneRightmostDescentAmbient
public import DirectedDistances.KMSW.WholePlaneRootedMapFields

/-! # Chronological local decoding in the whole-plane rotation

Created triangle cycles identify the two triangle steps directly in the
whole-plane colimit. The descent step is identified by the later left step
which removes its edge from the upper-left boundary. These statements concern
the actual whole-plane rotation; descent to geometric ball classes is separate. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

private theorem active_tail (W : ℤ → Fin 3) (N j : ℕ) :
    wholePlaneDartTail W (wholePlaneDartι W N (act (shiftedStream W N) j, false)) := by
  refine ⟨by change ¬ (false = true); decide, ?_⟩
  exact wholePlaneEdgePresent_ι_of_run_present W N _
    ⟨j, act_lt_nextEdge _ le_rfl, kmswStage_active_present _ _⟩

private theorem face_to_rotation (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (a b : WholePlaneDart W) (h : wholePlaneFaceSucc W H a = b) :
    wholePlaneRotation W H b = wholePlaneDartFlip W a := by
  rw [← h]
  exact (wholePlaneRotation W H).apply_symm_apply _

private theorem active_succ_triangle (w : ℕ → Fin 3) (j : ℕ)
    (h : w j = 0 ∨ w j = 1) : act w (j + 1) = (kmswStage w j).nextEdge := by
  rcases h with h | h
  · simp only [act, kmswStage, kmswStep, kmswCodeStep, h, ↓reduceIte]
    cases hl : (kmswStage w j).UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, hl, State.addEdge]
  · simp [act, kmswStage, kmswStep, kmswCodeStep, h,
      kmswStepOfStep, State.addEdge]

/-- Helper toward Proposition 3.9: a left step is decoded at its actual
chronological whole-plane dart, and the local successor is the next active
dart. Both the existing-left and fresh-left triangle branches are included. -/
theorem uibotLocalCodeLetter_wholePlane_zero
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N j : ℕ)
    (hj : shiftedStream W N j = 0) :
    let a : WholePlaneDart W := wholePlaneDartι W N (act (shiftedStream W N) j, false)
    let b : WholePlaneDart W := wholePlaneDartι W N (act (shiftedStream W N) (j + 1), false)
    uibotLocalCodeLetter (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) a = 0 ∧
    UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) a b := by
  let w := shiftedStream W N
  let t : TriangleCreationTime w := ⟨j, Or.inl hj⟩
  let a : WholePlaneDart W := wholePlaneDartι W N (act w j, false)
  let b : WholePlaneDart W := wholePlaneDartι W N (act w (j + 1), false)
  have hb : act w (j + 1) = (kmswStage w j).nextEdge :=
    active_succ_triangle w j (Or.inl hj)
  have hface : wholePlaneFaceSucc W H a = wholePlaneDartFlip W b := by
    have hc := wholePlane_stageTriangle_faceSucc_cycle W H N t
    cases hl : (kmswStage w j).UL.dropLast.reverse with
    | nil =>
        have ht := stageTriangleDartTriple_left_fresh w t hj hl
        rw [ht] at hc
        change wholePlaneFaceSucc W H a = wholePlaneDartι W N (act w (j + 1), true)
        rw [hb]
        exact hc.1
    | cons e es =>
        have ht := stageTriangleDartTriple_left_existing w t hj e es hl
        rw [ht] at hc
        change wholePlaneFaceSucc W H a = wholePlaneDartι W N (act w (j + 1), true)
        rw [hb]
        exact hc.2.1
  have hrot : ¬ wholePlaneDartTail W (wholePlaneRotation W H a) := by
    have hc := wholePlane_stageTriangle_faceSucc_cycle W H N t
    cases hl : (kmswStage w j).UL.dropLast.reverse with
    | nil =>
        have ht := stageTriangleDartTriple_left_fresh w t hj hl
        rw [ht] at hc
        have hr := face_to_rotation W H _ _ hc.2.2.1
        change wholePlaneRotation W H a = _ at hr
        rw [hr]
        exact fun h => h.1 rfl
    | cons e es =>
        have ht := stageTriangleDartTriple_left_existing w t hj e es hl
        rw [ht] at hc
        have hr := face_to_rotation W H _ _ hc.1
        change wholePlaneRotation W H a = _ at hr
        rw [hr]
        exact fun h => h.1 rfl
  have hfirst : ¬ wholePlaneDartTail W
      ((wholePlaneRotation W H).symm (wholePlaneDartFlip W a)) := by
    change ¬ wholePlaneDartTail W (wholePlaneFaceSucc W H a)
    rw [hface]
    exact fun h => h.1 rfl
  change uibotLocalCodeLetter _ _ _ a = 0 ∧ UIBOTLocalPeanoNext _ _ _ a b
  constructor
  · simp only [uibotLocalCodeLetter, hfirst, hrot, ↓reduceIte]
  · simp only [UIBOTLocalPeanoNext, hfirst, hrot, ↓reduceIte]
    change b = wholePlaneDartFlip W (wholePlaneFaceSucc W H a)
    rw [hface]
    rfl

/-- Helper toward Proposition 3.9: an up step is decoded at its actual
chronological whole-plane dart, and one rotation gives its next active dart. -/
theorem uibotLocalCodeLetter_wholePlane_one
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N j : ℕ)
    (hj : shiftedStream W N j = 1) :
    let a : WholePlaneDart W := wholePlaneDartι W N (act (shiftedStream W N) j, false)
    let b : WholePlaneDart W := wholePlaneDartι W N (act (shiftedStream W N) (j + 1), false)
    uibotLocalCodeLetter (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) a = 1 ∧
    UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) a b := by
  let w := shiftedStream W N
  let t : TriangleCreationTime w := ⟨j, Or.inr hj⟩
  let a : WholePlaneDart W := wholePlaneDartι W N (act w j, false)
  let b : WholePlaneDart W := wholePlaneDartι W N (act w (j + 1), false)
  have hb := active_succ_triangle w j (Or.inr hj)
  have hc := wholePlane_stageTriangle_faceSucc_cycle W H N t
  have ht := stageTriangleDartTriple_up w t hj
  rw [ht] at hc
  have hr : wholePlaneRotation W H a = b := by
    have hr := face_to_rotation W H _ _ hc.2.2.1
    change wholePlaneRotation W H a = wholePlaneDartι W N
      ((kmswStage w j).nextEdge, false) at hr
    exact hr.trans (congrArg (fun e => wholePlaneDartι W N (e, false)) hb.symm)
  have hfirst : ¬ wholePlaneDartTail W
      ((wholePlaneRotation W H).symm (wholePlaneDartFlip W a)) := by
    change ¬ wholePlaneDartTail W (wholePlaneFaceSucc W H a)
    have hf : wholePlaneFaceSucc W H a =
        wholePlaneDartι W N ((kmswStage w j).nextEdge + 1, true) := hc.1
    rw [hf]
    exact fun h => h.1 rfl
  have hsecond : wholePlaneDartTail W (wholePlaneRotation W H a) :=
    hr.symm ▸ active_tail W N (j + 1)
  change uibotLocalCodeLetter _ _ _ a = 1 ∧ UIBOTLocalPeanoNext _ _ _ a b
  constructor
  · simp only [uibotLocalCodeLetter, hfirst, hsecond, ↓reduceIte]
  · simp only [UIBOTLocalPeanoNext, hfirst, hsecond, ↓reduceIte]
    exact hr.symm

private theorem ul_removed (w : ℕ → Fin 3) (t e : ℕ)
    (he : e ∈ (kmswStage w t).UL) (hne : e ≠ act w t)
    (hout : e ∉ (kmswStage w (t + 1)).UL) :
    w t = 0 ∧ ∃ es, (kmswStage w t).UL.dropLast.reverse = e :: es := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
  change e ≠ (kmswStage w t).active at hne
  have hexs : e ∈ xs := by
    simpa only [hxs, List.mem_append, List.mem_singleton, hne, or_false] using he
  have hdrop : (kmswStage w t).UL.dropLast = xs := by
    rw [hxs, List.dropLast_concat]
  have hc : w t = 0 := by
    by_contra h0
    by_cases h1 : w t = 1
    · apply hout
      simpa [kmswStage, kmswStep, kmswCodeStep, h1,
        kmswStepOfStep, State.addEdge, hdrop]
        using (Or.inl hexs : e ∈ xs ∨ e = (kmswStage w t).nextEdge)
    · apply hout
      cases hUR : (kmswStage w t).UR <;>
        simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ↓reduceIte,
          kmswStepOfStep, hUR, State.addEdge, List.mem_append, List.mem_singleton]
      all_goals exact Or.inl he
  refine ⟨hc, ?_⟩
  have hrev : e ∈ xs.reverse := List.mem_reverse.mpr hexs
  cases hr : xs.reverse with
  | nil => simp only [hr, List.not_mem_nil] at hrev
  | cons a as =>
      have hu : (kmswStage w t).UL.dropLast.reverse = a :: as := by rw [hdrop, hr]
      have hea : e = a := by
        rcases List.mem_cons.mp (hr ▸ hrev) with hea | heas
        · exact hea
        · apply False.elim
          apply hout
          simp only [kmswStage, kmswStep, kmswCodeStep, hc, ↓reduceIte,
            kmswStepOfStep, hu, State.addEdge, List.mem_append, List.mem_singleton]
          exact Or.inl (List.mem_reverse.mpr heas)
      exact ⟨as, hea ▸ hu⟩

private theorem down_later_left_triangle (w : ℕ → Fin 3) (j : ℕ)
    (hj : w j = 2) (hL : ∀ a : ℤ, ∃ n, L w n ≤ a) :
    ∃ t, j < t ∧ w t = 0 ∧
      ∃ es, (kmswStage w t).UL.dropLast.reverse = act w j :: es := by
  classical
  have hactive : act w j ∈ (kmswStage w j).UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w j
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hstart : act w j ∈ (kmswStage w (j + 1)).UL := by
    cases hUR : (kmswStage w j).UR <;>
      simp [kmswStage, kmswStep, kmswCodeStep, hj, kmswStepOfStep,
        hUR, State.addEdge, hactive]
  obtain ⟨M, hM⟩ := kmswRun_UL_eventually_absent w hL (act w j)
  have hex : ∃ k : ℕ, act w j ∉ (kmswStage w (j + 1 + k)).UL :=
    ⟨M, hM _ (by omega)⟩
  let k := Nat.find hex
  have hout : act w j ∉ (kmswStage w (j + 1 + k)).UL := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.add_zero] at hout
    exact hout hstart
  have hin : act w j ∈ (kmswStage w (j + k)).UL := by
    have hmin := Nat.find_min hex (show k - 1 < k by omega)
    rw [show j + 1 + (k - 1) = j + k by omega] at hmin
    exact Classical.not_not.mp hmin
  have hne : act w j ≠ act w (j + k) := by
    intro he
    have ht := CutConverse.act_injective w he
    omega
  have hr := ul_removed w (j + k) (act w j) hin hne
    (by simpa only [show j + k + 1 = j + 1 + k by omega] using hout)
  exact ⟨j + k, by omega, hr⟩

/-- Helper toward Proposition 3.9: after a descent, the old active dart
has an outgoing face successor in the actual whole-plane rotation. The
unbounded left coordinate is used to prove, rather than assume, the later
triangle which witnesses this outgoing corner. -/
theorem uibotLocalCodeLetter_wholePlane_two_corner
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N j : ℕ)
    (hj : shiftedStream W N j = 2)
    (hL : ∀ a : ℤ, ∃ n, L (shiftedStream W N) n ≤ a) :
    wholePlaneDartTail W ((wholePlaneRotation W H).symm
      (wholePlaneDartFlip W
        (wholePlaneDartι W N (act (shiftedStream W N) j, false)))) := by
  obtain ⟨t, _, ht, es, hes⟩ := down_later_left_triangle (shiftedStream W N) j hj hL
  let q : TriangleCreationTime (shiftedStream W N) := ⟨t, Or.inl ht⟩
  have hc := wholePlane_stageTriangle_faceSucc_cycle W H N q
  have htr := stageTriangleDartTriple_left_existing (shiftedStream W N) q ht
    (act (shiftedStream W N) j) es hes
  rw [htr] at hc
  have hf : wholePlaneFaceSucc W H
      (wholePlaneDartι W N (act (shiftedStream W N) j, false)) =
      wholePlaneDartι W N (act (shiftedStream W N) t, false) := hc.1
  change wholePlaneDartTail W (wholePlaneFaceSucc W H
    (wholePlaneDartι W N (act (shiftedStream W N) j, false)))
  rw [hf]
  exact active_tail W N t

/-- Helper toward Proposition 3.9: every chronological letter is decoded
by the same two local rotation tests in the whole-plane colimit. The only
additional deterministic condition is unboundedness of the run's left
coordinate, discharged almost surely in the following file. -/
theorem uibotLocalCodeLetter_wholePlane
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N j : ℕ)
    (hL : ∀ a : ℤ, ∃ n, L (shiftedStream W N) n ≤ a) :
    uibotLocalCodeLetter (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W)
      (wholePlaneDartι W N (act (shiftedStream W N) j, false)) = shiftedStream W N j := by
  classical
  by_cases h0 : shiftedStream W N j = 0
  · rw [h0]
    exact (uibotLocalCodeLetter_wholePlane_zero W H N j h0).1
  by_cases h1 : shiftedStream W N j = 1
  · rw [h1]
    exact (uibotLocalCodeLetter_wholePlane_one W H N j h1).1
  have h2 : shiftedStream W N j = 2 := by
    have hb := (shiftedStream W N j).isLt
    apply Fin.ext
    have hn0 : (shiftedStream W N j).val ≠ 0 := fun h => h0 (Fin.ext h)
    have hn1 : (shiftedStream W N j).val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  have hc := uibotLocalCodeLetter_wholePlane_two_corner W H N j h2 hL
  rw [h2]
  simp only [uibotLocalCodeLetter, hc, ↓reduceIte]

private theorem first_outgoing_is_rightmost
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (a : WholePlaneDart W) (ha : a.2 = true)
    (hex : ∃ k : ℕ, wholePlaneDartTail W ((wholePlaneRotation W H ^ k) a)) :
    ∃ (b : WholePlaneDart W) (k : ℕ),
      b = (wholePlaneRotation W H ^ k) a ∧ wholePlaneDartTail W b ∧
      (∀ l : ℕ, l < k → ¬ wholePlaneDartTail W ((wholePlaneRotation W H ^ l) a)) ∧
      wholePlaneRightmostOutgoingAt W H (wholePlaneDartVertex W a) b.1 := by
  classical
  let rot := wholePlaneRotation W H
  let k := Nat.find hex
  let b : WholePlaneDart W := (rot ^ k) a
  have hb : wholePlaneDartTail W b := Nat.find_spec hex
  have hmin : ∀ l : ℕ, l < k → ¬ wholePlaneDartTail W ((rot ^ l) a) :=
    fun l hl => Nat.find_min hex hl
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    have hba : b = a := by simp only [b, hz, pow_zero, Equiv.Perm.one_apply]
    exact hb.1 (hba ▸ ha)
  have hbf : b.2 = false := Bool.eq_false_iff.mpr hb.1
  have hpred : rot.symm b = (rot ^ (k - 1)) a := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp only [b, hm, Nat.succ_sub_one, pow_succ', Equiv.Perm.mul_apply,
      Equiv.symm_apply_apply]
  have hn : ¬ wholePlaneDartTail W (rot.symm b) := by
    rw [hpred]
    exact hmin _ (by omega)
  have hbt : (rot.symm b).2 = true := by
    cases he : (rot.symm b).2
    · exact False.elim (hn ⟨by simpa only [he] using Bool.false_ne_true, hp _⟩)
    · rfl
  have hv : wholePlaneDartVertex W b = wholePlaneDartVertex W a :=
    wholePlaneRotation_sameCycle_dartVertex W H a b
      ⟨(k : ℤ), by simp only [zpow_natCast]; rfl⟩
  refine ⟨b, k, rfl, hb, hmin, hp _, ?_, 1, by decide, ?_, hp _, ?_⟩
  · simpa only [wholePlaneDartVertex, hbf, Bool.false_eq_true, ↓reduceIte] using hv
  · have he : (b.1, false) = b := Prod.ext rfl hbf.symm
    simpa only [pow_one, he] using hbt
  · intro l hl hl1
    omega

/-- Helper toward Proposition 3.9: on a whole-plane realization with all
edges present and both run coordinates unbounded below, the local Peano
successor advances to the next chronological active dart in all three cases. -/
theorem uibotLocalPeanoNext_wholePlane
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e) (N j : ℕ)
    (hL : ∀ a : ℤ, ∃ n, L (shiftedStream W N) n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a) :
    UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W)
      (wholePlaneDartι W N (act (shiftedStream W N) j, false))
      (wholePlaneDartι W N (act (shiftedStream W N) (j + 1), false)) := by
  classical
  by_cases h0 : shiftedStream W N j = 0
  · exact (uibotLocalCodeLetter_wholePlane_zero W H N j h0).2
  by_cases h1 : shiftedStream W N j = 1
  · exact (uibotLocalCodeLetter_wholePlane_one W H N j h1).2
  have h2 : shiftedStream W N j = 2 := by
    have hb := (shiftedStream W N j).isLt
    apply Fin.ext
    have hn0 : (shiftedStream W N j).val ≠ 0 := fun h => h0 (Fin.ext h)
    have hn1 : (shiftedStream W N j).val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  let w := shiftedStream W N
  let a : WholePlaneDart W := wholePlaneDartι W N (act w j, false)
  let b : WholePlaneDart W := wholePlaneDartι W N (act w (j + 1), false)
  have hstep : R w (j + 1) = R w j - 1 := by
    have hs : R w (j + 1) = R w j +
        (RandomWalk.lazyTwoDimensionalStep (w j)).2 := Finset.sum_range_succ _ _
    simpa [h2, w, RandomWalk.lazyTwoDimensionalStep, sub_eq_add_neg] using hs
  change R (shiftedStream W N) (j + 1) = R (shiftedStream W N) j - 1 at hstep
  obtain ⟨t, hjt, ht, hgap, hw, hright⟩ :=
    wholePlaneRightmost_descent_at_active W H N hR j
  have htime : t = j + 1 := by
    by_contra hne
    have hg := hgap (j + 1) (by omega) (by omega)
    omega
  subst t
  have hv : wholePlaneDartVertex W b = wholePlaneDartVertex W (wholePlaneDartFlip W a) := by
    change wholePlaneEdgeWest W (wholePlaneEdgeι W N (act w (j + 1))) =
      wholePlaneEdgeEast W (wholePlaneEdgeι W N (act w j))
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι, hw]
  obtain ⟨m, hm⟩ := wholePlaneRotation_exists_pow_of_base W H
    (wholePlaneDartFlip W a) b hv.symm
  have hex : ∃ k : ℕ,
      wholePlaneDartTail W ((wholePlaneRotation W H ^ k) (wholePlaneDartFlip W a)) :=
    ⟨m, hm.symm ▸ active_tail W N (j + 1)⟩
  obtain ⟨c, k, hc, hctail, hmin, hcright⟩ :=
    first_outgoing_is_rightmost W H hp (wholePlaneDartFlip W a) rfl hex
  have hvertex : wholePlaneDartVertex W (wholePlaneDartFlip W a) =
      wholePlaneVertexι W N (edgeEast w (act w j)) :=
    wholePlaneEdgeEast_ι W N (act w j)
  rw [hvertex] at hcright
  have he : c = b := Prod.ext
    (wholePlaneRightmostOutgoingAt_unique W H _ hcright hright)
    (Bool.eq_false_iff.mpr hctail.1)
  have hcorner := uibotLocalCodeLetter_wholePlane_two_corner W H N j h2 hL
  change UIBOTLocalPeanoNext _ _ _ a b
  unfold UIBOTLocalPeanoNext
  rw [ite_eq_left hcorner]
  exact ⟨k, he.symm.trans hc, active_tail W N (j + 1), hmin⟩

universe u v

/-- Helper toward Proposition 3.9: each evaluation of the local letter
decoder has finite support in the rotation data. Any map preserving these
finitely many rotations, inverse rotations, flips and orientation tests
preserves the decoded letter; no global dart equivalence is required. -/
theorem uibotLocalCodeLetter_finite_support {D : Type u}
    (rot : Equiv.Perm D) (flip : D → D) (tail : D → Prop) (a : D) :
    ∃ S : Finset D, a ∈ S ∧
      ∀ (E : Type v) (rot' : Equiv.Perm E) (flip' : E → E) (tail' : E → Prop)
        (f : D → E),
        (∀ d ∈ S, f (rot d) = rot' (f d)) →
        (∀ d ∈ S, f (rot.symm d) = rot'.symm (f d)) →
        (∀ d ∈ S, f (flip d) = flip' (f d)) →
        (∀ d ∈ S, tail' (f d) ↔ tail d) →
        uibotLocalCodeLetter rot' flip' tail' (f a) =
          uibotLocalCodeLetter rot flip tail a := by
  classical
  let S : Finset D := {a, flip a, rot.symm (flip a), rot a}
  refine ⟨S, by simp [S], ?_⟩
  intro E rot' flip' tail' f hrot hsymm hflip htail
  have ha : a ∈ S := by simp [S]
  have hf : flip a ∈ S := by simp [S]
  have hi : rot.symm (flip a) ∈ S := by simp [S]
  have hr : rot a ∈ S := by simp [S]
  unfold uibotLocalCodeLetter
  rw [← hflip a ha, ← hsymm (flip a) hf, ← hrot a ha,
    htail _ hi, htail _ hr]

/-- Helper toward Proposition 3.9: a true local successor relation has
finite support. In the descent case the finite support includes the entire
first-outgoing search, so its witness and minimality both transport. -/
theorem uibotLocalPeanoNext_finite_support {D : Type u}
    (rot : Equiv.Perm D) (flip : D → D) (tail : D → Prop) (a b : D)
    (hab : UIBOTLocalPeanoNext rot flip tail a b) :
    ∃ S : Finset D, a ∈ S ∧ b ∈ S ∧
      ∀ (E : Type v) (rot' : Equiv.Perm E) (flip' : E → E) (tail' : E → Prop)
        (f : D → E),
        (∀ d ∈ S, f (rot d) = rot' (f d)) →
        (∀ d ∈ S, f (rot.symm d) = rot'.symm (f d)) →
        (∀ d ∈ S, f (flip d) = flip' (f d)) →
        (∀ d ∈ S, tail' (f d) ↔ tail d) →
        UIBOTLocalPeanoNext rot' flip' tail' (f a) (f b) := by
  classical
  let base : Finset D := {a, b, flip a, rot.symm (flip a), rot a}
  have hbase (S : Finset D) (hS : base ⊆ S)
      (E : Type v) (rot' : Equiv.Perm E) (flip' : E → E) (tail' : E → Prop)
      (f : D → E)
      (hrot : ∀ d ∈ S, f (rot d) = rot' (f d))
      (hsymm : ∀ d ∈ S, f (rot.symm d) = rot'.symm (f d))
      (hflip : ∀ d ∈ S, f (flip d) = flip' (f d))
      (htail : ∀ d ∈ S, tail' (f d) ↔ tail d) :
      (tail' (rot'.symm (flip' (f a))) ↔ tail (rot.symm (flip a))) ∧
      (tail' (rot' (f a)) ↔ tail (rot a)) := by
    have ha : a ∈ S := hS (by simp [base])
    rw [← hflip a ha, ← hsymm (flip a) (hS (by simp [base])), ← hrot a ha]
    exact ⟨htail _ (hS (by simp [base])), htail _ (hS (by simp [base]))⟩
  unfold UIBOTLocalPeanoNext at hab
  split_ifs at hab with hfirst hsecond
  · obtain ⟨k, hb, hbt, hmin⟩ := hab
    let S := base ∪ (Finset.range (k + 1)).image (fun l => (rot ^ l) (flip a))
    have hS : base ⊆ S := Finset.subset_union_left
    have horbit (l : ℕ) (hl : l ≤ k) : (rot ^ l) (flip a) ∈ S := by
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨l, Finset.mem_range.mpr (by omega), rfl⟩)
    refine ⟨S, hS (by simp [base]), hS (by simp [base]), ?_⟩
    intro E rot' flip' tail' f hrot hsymm hflip htail
    have hh := hbase S hS E rot' flip' tail' f hrot hsymm hflip htail
    have hpow (l : ℕ) (hl : l ≤ k) :
        f ((rot ^ l) (flip a)) = (rot' ^ l) (flip' (f a)) := by
      induction l with
      | zero =>
          simpa only [pow_zero, Equiv.Perm.one_apply] using
            hflip a (hS (by simp [base]))
      | succ l ih =>
          simp only [pow_succ', Equiv.Perm.mul_apply]
          rw [hrot _ (horbit l (by omega)), ih (by omega)]
    have hf := hh.1.mpr hfirst
    simp only [UIBOTLocalPeanoNext, hf, ↓reduceIte]
    refine ⟨k, (congrArg f hb).trans (hpow k le_rfl),
      (htail b (hS (by simp [base]))).2 hbt, ?_⟩
    intro l hl
    rw [← hpow l (by omega), htail _ (horbit l (by omega))]
    exact hmin l hl
  · refine ⟨base, by simp [base], by simp [base], ?_⟩
    intro E rot' flip' tail' f hrot hsymm hflip htail
    have hh := hbase base (Finset.Subset.refl _) E rot' flip' tail' f
      hrot hsymm hflip htail
    have hf := mt hh.1.mp hfirst
    have hs := hh.2.mpr hsecond
    simp only [UIBOTLocalPeanoNext, hf, hs, ↓reduceIte]
    exact (congrArg f hab).trans (hrot a (by simp [base]))
  · refine ⟨base, by simp [base], by simp [base], ?_⟩
    intro E rot' flip' tail' f hrot hsymm hflip htail
    have hh := hbase base (Finset.Subset.refl _) E rot' flip' tail' f
      hrot hsymm hflip htail
    have hf := mt hh.1.mp hfirst
    have hs := mt hh.2.mp hsecond
    simp only [UIBOTLocalPeanoNext, hf, hs, ↓reduceIte]
    rw [← hflip a (by simp [base]), ← hsymm (flip a) (by simp [base]),
      ← hflip (rot.symm (flip a)) (by simp [base])]
    exact congrArg f hab

end DirectedDistances.PaperProofs.Section3

end
