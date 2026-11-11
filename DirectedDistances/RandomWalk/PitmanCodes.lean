module

public import DirectedDistances.RandomWalk.VectorPitman
public import DirectedDistances.RandomWalk.IIDVectorWalk
public import DirectedDistances.KMSW.BoundaryDynamics

/-! # The Pitman flip on source code sequences

Code-sequence form of the flip in the proof of `lem-quadrant-walk`, -/

public section
namespace DirectedDistances.RandomWalk

/-- Integrated source walk of a code sequence from (0,0): step `i` is code `c i` -/
@[expose] def integrateCodes (c : ℕ → Fin 3) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, lazyTwoDimensionalStep (c i)

/-- Flip code 0 (step `(−1,0)`) to code 2 (step `(1,−1)`) exactly at the steps where the -/
@[expose] noncomputable def pitmanCode (c : ℕ → Fin 3) (i : ℕ) : Fin 3 :=
  open Classical in
  if (∀ j ≤ i, (integrateCodes c (i + 1)).1 < (integrateCodes c j).1) then 2 else c i

private theorem integrateCodes_zero (c : ℕ → Fin 3) : integrateCodes c 0 = (0, 0) := by
  simp only [integrateCodes, Finset.range_zero, Finset.sum_empty]
  rfl

private theorem integrateCodes_succ (c : ℕ → Fin 3) (n : ℕ) :
    integrateCodes c (n + 1) = integrateCodes c n + lazyTwoDimensionalStep (c n) :=
  Finset.sum_range_succ _ _

/-- A new strict minimum can only come from code 0 -/
theorem pitmanCode_of_flip (c : ℕ → Fin 3) (i : ℕ)
    (h : ∀ j ≤ i, (integrateCodes c (i + 1)).1 < (integrateCodes c j).1) :
    c i = 0 := by
  have h1 := h i le_rfl
  rw [integrateCodes_succ] at h1
  have h2 : ((c i : ℕ) : ℤ) - 1 < 0 := by
    have : (integrateCodes c i).1 + (lazyTwoDimensionalStep (c i)).1 < (integrateCodes c i).1 := h1
    change (integrateCodes c i).1 + (((c i : ℕ) : ℤ) - 1) < _ at this
    omega
  apply Fin.ext
  have : (c i : ℕ) = 0 := by omega
  simpa using this

private theorem runningMin_succ' (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p (n + 1) = min (globalLazyRunningMinimum p n) (p (n + 1)) := by
  have h := runningMinimum_succ (fun j : Fin (n + 1 + 1) => p j.val)
    (⟨n, by omega⟩ : Fin (n + 1))
  simpa only [runningMinimum_prefix_eq_global, Fin.val_succ, Fin.val_castSucc] using h

/-- The flipped code walk is the vector Pitman image -/
theorem integrateCodes_pitmanCode (c : ℕ → Fin 3) (n : ℕ) :
    integrateCodes (pitmanCode c) n = vectorPitman (integrateCodes c) n := by
  induction n with
  | zero =>
    rw [integrateCodes_zero]
    simp only [vectorPitman, globalLazyPhi_zero, globalLazyRunningMinimum_zero,
      integrateCodes_zero]
    simp
  | succ n ih =>
    have hfst := congrArg Prod.fst ih
    have hsnd := congrArg Prod.snd ih
    simp only [vectorPitman, globalLazyPhi] at hfst hsnd ⊢
    rw [integrateCodes_succ]
    have hmin := runningMin_succ' (fun k => (integrateCodes c k).1) n
    have hle := globalLazyRunningMinimum_le (fun k => (integrateCodes c k).1) (i := n) le_rfl
    have hZ := integrateCodes_succ c n
    have hZ1 := congrArg Prod.fst hZ
    have hZ2 := congrArg Prod.snd hZ
    simp only [Prod.fst_add, Prod.snd_add] at hZ1 hZ2
    by_cases hf : ∀ j ≤ n, (integrateCodes c (n + 1)).1 < (integrateCodes c j).1
    · have hc := pitmanCode_of_flip c n hf
      have hp : pitmanCode c n = 2 := by
        unfold pitmanCode
        rw [ite_eq_left hf]
      have hlt : (integrateCodes c (n + 1)).1 ≤
          globalLazyRunningMinimum (fun k => (integrateCodes c k).1) n :=
        le_globalLazyRunningMinimum (fun k => (integrateCodes c k).1) n
          (a := (integrateCodes c (n + 1)).1) (fun i hi => (hf i hi).le)
      have hex : ∃ j ≤ n, globalLazyRunningMinimum (fun k => (integrateCodes c k).1) n =
          (integrateCodes c j).1 := by
        obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1))
          ⟨0, by simp⟩ (fun k => (integrateCodes c k).1)
        exact ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), h⟩
      obtain ⟨j, hj, hjeq⟩ := hex
      have hlt' := hf j hj
      rw [← hjeq] at hlt'
      rw [hp]
      rw [hc] at hZ1 hZ2
      simp only [lazyTwoDimensionalStep_zero] at hZ1 hZ2
      have hm' : globalLazyRunningMinimum (fun k => (integrateCodes c k).1) (n + 1) =
          (integrateCodes c (n + 1)).1 := by
        rw [hmin]; exact min_eq_right hlt
      rw [hm']
      have e2 : lazyTwoDimensionalStep (2 : Fin 3) = (1, -1) := rfl
      rw [e2]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · have hp : pitmanCode c n = c n := by
        unfold pitmanCode
        rw [ite_eq_right hf]
      have hm' : globalLazyRunningMinimum (fun k => (integrateCodes c k).1) (n + 1) =
          globalLazyRunningMinimum (fun k => (integrateCodes c k).1) n := by
        rw [hmin]
        apply min_eq_left
        by_contra hlt
        apply hf
        intro j hj
        have := globalLazyRunningMinimum_le (fun k => (integrateCodes c k).1) hj
        omega
      rw [hp, hm']
      have hs1 : (lazyTwoDimensionalStep (c n)).1 = ((c n : ℕ) : ℤ) - 1 := rfl
      have hs2 : (lazyTwoDimensionalStep (c n)).2 =
          (if c n = 0 then 0 else if c n = 1 then 1 else -1) := rfl
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- The flipped code walk has nonnegative first coordinate -/
theorem integrateCodes_pitmanCode_fst_nonneg (c : ℕ → Fin 3) (n : ℕ) :
    0 ≤ (integrateCodes (pitmanCode c) n).1 := by
  rw [integrateCodes_pitmanCode]
  exact globalLazyPhi_nonneg_of_start_zero (fun k => (integrateCodes c k).1)
    (by rw [integrateCodes_zero]) n

/-- Bridge to `codeWalk` of `IIDVectorWalk.lean`, which reads `ω (i + 1)` at step `i` -/
theorem codeWalk_eq_integrateCodes (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk ω n = integrateCodes (fun i => ω (i + 1)) n := rfl

/-- Bridge to the KMSW horizontal coordinate. -/
theorem kmsw_L_eq (w : ℕ → Fin 3) (n : ℕ) :
    DirectedDistances.KMSW.L w n = (integrateCodes w n).1 := by
  simp [DirectedDistances.KMSW.L, integrateCodes, Prod.fst_sum]

/-- Bridge to the KMSW vertical coordinate. -/
theorem kmsw_R_eq (w : ℕ → Fin 3) (n : ℕ) :
    DirectedDistances.KMSW.R w n = (integrateCodes w n).2 := by
  simp [DirectedDistances.KMSW.R, integrateCodes, Prod.snd_sum]

end DirectedDistances.RandomWalk
