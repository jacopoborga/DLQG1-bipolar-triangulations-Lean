/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.PaperProofs.SourceResults.FutureMapDefinition
public import DirectedDistances.RandomWalk.FutureCodesAtHits

/-! # Boundary vertex first visits

Helpers toward Proposition 3.9 consumers, from `eqn-bdy-vertex-hit`,
`eqn-bdy-vertex-kmsw` and the following monotonicity remark
are transported to the source cut labels using the installed Definition 1.3
provider. These helpers make no numbered-result completion claim. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW
open scoped Classical




theorem boundaryVertex_eq_activeInitial_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryVertex_zero, boundaryHitTime_zero]
    simp [activeInitial, edgeWest, act, kmswStage, kmswInit]
  by_cases hkpos : 1 ≤ k
  · exact boundaryVertex_right_hit_eq w h hkpos
  · exact boundaryVertex_left_hit_eq w h (by omega)




theorem boundaryHitTime_isLeast_visit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    IsLeast {n : ℕ | boundaryVertex w h k = activeInitial w n}
      (boundaryHitTime w h k) := by
  refine ⟨boundaryVertex_eq_activeInitial_hit w h k, ?_⟩
  intro n hn
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryHitTime_zero]
    exact Nat.zero_le n
  by_contra hnot
  have hlt : n < boundaryHitTime w h k := by omega
  by_cases hkpos : 1 ≤ k
  · exact boundaryVertex_first_visit_right w h hkpos n hlt hn
  · exact boundaryVertex_first_visit_left w h (by omega) n hlt hn



theorem boundaryHitTime_case_formula (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryHitTime w h k =
      if hk0 : k = 0 then 0
      else if hkpos : 0 < k then Nat.find (h.rightHit k (by omega))
      else Nat.find (h.leftHit k (by omega)) := by
  unfold boundaryHitTime
  rfl

private theorem boundaryHitTime_right_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  rw [boundaryHitTime_case_formula]
  simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_left (by omega : 0 < k)]

private theorem boundaryHitTime_left_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  rw [boundaryHitTime_case_formula]
  simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_right (by omega : ¬ 0 < k)]




theorem boundaryHitTime_right_isLeast (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    IsLeast {n : ℕ | 0 < n ∧ R w n = -k} (boundaryHitTime w h k) := by
  have hhit := boundaryHitTime_right_spec w h hk
  have hpos : 0 < boundaryHitTime w h k := by
    by_contra hnot
    have hz : boundaryHitTime w h k = 0 := by omega
    rw [hz] at hhit
    simp [R] at hhit
    omega
  refine ⟨⟨hpos, hhit⟩, ?_⟩
  intro n hn
  rw [boundaryHitTime_right_find w h hk]
  exact Nat.find_min' (h.rightHit k hk) hn.2




theorem boundaryHitTime_left_isLeast (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    IsLeast {n : ℕ | 0 < n ∧ L w n = k} (boundaryHitTime w h k) := by
  have hhit := boundaryHitTime_left_spec w h hk
  have hpos : 0 < boundaryHitTime w h k := by
    by_contra hnot
    have hz : boundaryHitTime w h k = 0 := by omega
    rw [hz] at hhit
    simp [L] at hhit
    omega
  refine ⟨⟨hpos, hhit⟩, ?_⟩
  intro n hn
  rw [boundaryHitTime_left_find w h hk]
  exact Nat.find_min' (h.leftHit k hk) hn.2

private theorem coordinate_hits_intermediate (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  let hex : ∃ j, f j ≤ a := ⟨n, hn⟩
  let m := Nat.find hex
  have hma : f m ≤ a := Nat.find_spec hex
  have hmn : m ≤ n := Nat.find_min' hex hn
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm, hzero] at hma
    omega
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hprev : a < f p := by
    have hnot := Nat.find_min hex (show p < m by omega)
    omega
  refine ⟨m, hmn, ?_⟩
  have hs := hstep p
  rw [hp] at hma ⊢
  omega

private theorem coordinate_step_lower (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) ∧ R w n - 1 ≤ R w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hR : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 ∧
      -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  omega




theorem boundaryHitTime_strictMonoOn_nonneg (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    StrictMonoOn (boundaryHitTime w h) (Set.Ici 0) := by
  intro a ha b hb hab
  have hbpos : 1 ≤ b := by simp only [Set.mem_Ici] at ha hb; omega
  by_cases ha0 : a = 0
  · subst a
    rw [boundaryHitTime_zero]
    exact (boundaryHitTime_right_isLeast w h hbpos).1.1
  have hapos : 1 ≤ a := by simp only [Set.mem_Ici] at ha; omega
  have hbhit := boundaryHitTime_right_spec w h hbpos
  obtain ⟨m, hm, hma⟩ := coordinate_hits_intermediate (R w)
    (fun n => (coordinate_step_lower w n).2) (by simp [R])
    (show -a < 0 by omega) (show R w (boundaryHitTime w h b) ≤ -a by omega)
  have hle : boundaryHitTime w h a ≤ boundaryHitTime w h b := by
    rw [boundaryHitTime_right_find w h hapos]
    exact (Nat.find_min' (h.rightHit a hapos) hma).trans hm
  have hahit := boundaryHitTime_right_spec w h hapos
  have hne : boundaryHitTime w h a ≠ boundaryHitTime w h b := by
    intro heq
    rw [heq] at hahit
    omega
  omega




theorem boundaryHitTime_strictAntiOn_nonpos (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    StrictAntiOn (boundaryHitTime w h) (Set.Iic 0) := by
  intro a ha b hb hab
  have haneg : a ≤ -1 := by simp only [Set.mem_Iic] at ha hb; omega
  by_cases hb0 : b = 0
  · subst b
    rw [boundaryHitTime_zero]
    exact (boundaryHitTime_left_isLeast w h haneg).1.1
  have hbneg : b ≤ -1 := by simp only [Set.mem_Iic] at hb; omega
  have hahit := boundaryHitTime_left_spec w h haneg
  obtain ⟨m, hm, hmb⟩ := coordinate_hits_intermediate (L w)
    (fun n => (coordinate_step_lower w n).1) (by simp [L])
    (show b < 0 by omega) (show L w (boundaryHitTime w h a) ≤ b by omega)
  have hle : boundaryHitTime w h b ≤ boundaryHitTime w h a := by
    rw [boundaryHitTime_left_find w h hbneg]
    exact (Nat.find_min' (h.leftHit b hbneg) hmb).trans hm
  have hbhit := boundaryHitTime_left_spec w h hbneg
  have hne : boundaryHitTime w h b ≠ boundaryHitTime w h a := by
    intro heq
    rw [heq] at hbhit
    omega
  omega





theorem m0Cut_boundaryHitTime_isLeast_visit (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) :
    IsLeast {n : ℕ | (m0CutData W H h hLL).x k =
      wholePlaneEdgeWest W (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n))}
      (boundaryHitTime (shiftedStream W 0) h k) := by
  have hv := boundaryHitTime_isLeast_visit (shiftedStream W 0) h k
  have heq (n : ℕ) : (m0CutData W H h hLL).x k =
      wholePlaneEdgeWest W (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n)) ↔
      boundaryVertex (shiftedStream W 0) h k = activeInitial (shiftedStream W 0) n := by
    rw [(m0CutData W H h hLL).x_eq h hLL k, wholePlaneEdgeWest_ι]
    exact (wholePlaneVertexι_injective W 0).eq_iff
  exact ⟨(heq _).2 hv.1, fun n hn => hv.2 ((heq n).1 hn)⟩





theorem ae_m0Cut_boundaryHitTime_isLeast_visit :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let D := m0CutData W H h hLL
      ∀ k : ℤ, IsLeast {n : ℕ | D.x k =
        wholePlaneEdgeWest W (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n))}
        (boundaryHitTime (shiftedStream W 0) h k) := by
  filter_upwards [SourceResults.defn_future_map_provider] with W hW
  obtain ⟨H, h, hLL, hp, hAnchor⟩ := hW
  exact ⟨H, h, hLL, fun k => m0Cut_boundaryHitTime_isLeast_visit W H h hLL k⟩

end DirectedDistances.PaperProofs.Section5
