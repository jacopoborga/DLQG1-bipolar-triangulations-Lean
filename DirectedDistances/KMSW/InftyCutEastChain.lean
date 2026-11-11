module

public import DirectedDistances.KMSW.RightBoundaryRightmost
public import DirectedDistances.KMSW.ActiveTimeMonotone
public import DirectedDistances.KMSW.UIBOTBoundaryM0

/-! # East boundary chain for the infty-cut route

Deterministic P3 ingredients for `lem-infty-cut`
`eqn-bdy-vertex-hit` / `eqn-bdy-vertex-kmsw`
present-boundary content used from `lem-uibot-bdy`
`DirectedDistances/KMSW/UIBOTBoundaryM0.lean:69`). These declarations prove
only an east-chain ingredient for P3: they are not P3 and do not prove
`lem-infty-cut`. -/

public section
namespace DirectedDistances.KMSW

open Quiver
open scoped Classical

private theorem coordinate_succ_ge_R_eastChain (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  have hR : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  rw [hR]
  omega

private theorem exists_coordinate_eq_of_le_eastChain (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem boundaryHitTime_right_eq_find_eastChain (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0),
    dite_eq_left (by omega : 0 < k)]

private theorem boundaryHitTime_right_mono_eastChain (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a b : ℤ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    boundaryHitTime w h a ≤ boundaryHitTime w h b := by
  have hb : 1 ≤ b := by omega
  have hbHit := boundaryHitTime_right_spec w h hb
  obtain ⟨m, hm, hmb⟩ := exists_coordinate_eq_of_le_eastChain (R w)
    (coordinate_succ_ge_R_eastChain w) (by simp [R]) (by omega : -a < 0)
    (by rw [hbHit]; omega)
  rw [boundaryHitTime_right_eq_find_eastChain w h ha]
  exact (Nat.find_min' (h.rightHit a ha) hmb).trans hm

/-- For every `j ≥ 1`, the edge activated at `boundaryHitTime w h j` is the
right-boundary record edge, with west and east endpoints `x_j` and `x_{j+1}`
(`eqn-bdy-vertex-hit`, `eqn-bdy-vertex-kmsw`,
ingredient for P3 only. -/
theorem boundaryHitTime_right_boundary_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {j : ℕ} (hj : 1 ≤ j) :
    act w (boundaryHitTime w h (j : ℤ)) = kmswRightBoundaryEdge w j ∧
      edgeWest w (act w (boundaryHitTime w h (j : ℤ))) =
        boundaryVertex w h (j : ℤ) ∧
      edgeEast w (act w (boundaryHitTime w h (j : ℤ))) =
        boundaryVertex w h ((j : ℤ) + 1) := by
  have he := boundaryVertex_right_edge_present_source w h hj
  have ht := boundaryHitTime_right_edge_eq_rightBoundaryEdge w h hj
  rcases he with ⟨_, hw, he⟩
  refine ⟨ht, ?_, ?_⟩
  · rw [ht]
    exact hw
  · rw [ht]
    simpa only [Nat.cast_add, Nat.cast_one] using he

private noncomputable def rightBoundaryArrow (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k) :
    (⟨boundaryVertex w h (k : ℤ)⟩ : PresentVertex w) ⟶
      ⟨boundaryVertex w h ((k + 1 : ℕ) : ℤ)⟩ := by
  obtain ⟨hp, hw, he⟩ := boundaryVertex_right_edge_present_source w h hk
  exact ⟨kmswRightBoundaryEdge w k, hp, hw,
    by simpa only [Nat.cast_add, Nat.cast_one] using he⟩

private theorem rightBoundaryPath_exists (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (τ j : ℕ) (hj : 1 ≤ j)
    (hτ : τ ≤ boundaryHitTime w h (j : ℤ)) :
    ∀ ℓ, j ≤ ℓ →
      ∃ p : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w)
          ⟨boundaryVertex w h (ℓ : ℤ)⟩,
        ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
          τ ≤ actTime w e he := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro hj0
      omega
  | succ ℓ ih =>
      intro hjl
      by_cases hlast : j = ℓ + 1
      · subst j
        refine ⟨Path.nil, ?_⟩
        intro e he
        simp [pathEdgeList] at he
      · have hjl' : j ≤ ℓ := by omega
        obtain ⟨p, hp⟩ := ih hjl'
        have hℓ : 1 ≤ ℓ := by omega
        let a := rightBoundaryArrow w h ℓ hℓ
        refine ⟨p.cons a, ?_⟩
        intro e he hePresent
        simp only [pathEdgeList, List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact hp e he hePresent
        · have he' : e = (rightBoundaryArrow w h ℓ hℓ).val := by simpa [a] using he
          subst e
          change τ ≤ actTime w (kmswRightBoundaryEdge w ℓ) hePresent
          have hindex : (j : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hjl'
          have hmono := boundaryHitTime_right_mono_eastChain w h
            (a := (j : ℤ)) (b := (ℓ : ℤ)) (by exact_mod_cast hj) hindex
          have hact : actTime w (kmswRightBoundaryEdge w ℓ) hePresent =
              boundaryHitTime w h (ℓ : ℤ) := by
            apply (actTime_eq_iff w (kmswRightBoundaryEdge w ℓ) hePresent
              (boundaryHitTime w h (ℓ : ℤ))).2
            exact (boundaryHitTime_right_edge_eq_rightBoundaryEdge w h hℓ).symm
          rw [hact]
          exact hτ.trans hmono

/-- If the `j`th positive boundary edge is activated at or after a stage time
`τ`, every later boundary vertex is reachable from `x_j` by a path whose edges
are all activated at or after `τ`. This is the deterministic east-chain
ingredient for P3 in `lem-infty-cut`, using the LR-chain content of
`lem-infty-cut`. -/
theorem boundaryVertex_right_chain_late_path (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (τ j ℓ : ℕ) (hj : 1 ≤ j)
    (hτ : τ ≤ boundaryHitTime w h (j : ℤ)) (hjl : j ≤ ℓ) :
    ∃ p : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w)
        ⟨boundaryVertex w h (ℓ : ℤ)⟩,
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        τ ≤ actTime w e he := by
  exact rightBoundaryPath_exists w h τ j hj hτ ℓ hjl

end DirectedDistances.KMSW
