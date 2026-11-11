module

public import DirectedDistances.KMSW.HatInducedEmbedding

/-! # Boundary cyclic orders of hatted stages

Hatted-half helpers for `lem-quad-kmsw`
The induction must compare the entire geometric dart image, including missing
edges. Its initial case is established below. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem boundary_time_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    quadrantRStageTime w h 0 = 0 := by
  apply quadrantRStageTime_eq_of_initial_R
  have hp := (walkNL_spec w h 0).1
  rw [walkNR_zero] at hp
  omega

/-- The initial hatted stage has induced rotation at every geometric dart.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : StageDart (kmswStage (hatCodes w h) 0).nextEdge) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswMap w (quadrantRStageTime w h 0)).rot : _ → _)^[k]
        (hatDartMap w h 0 d) = hatDartMap w h 0 ((kmswMap (hatCodes w h) 0).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h 0)).rot : _ → _)^[j]
          (hatDartMap w h 0 d) ∉ Set.range (hatDartMap w h 0) := by
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · have ht := boundary_time_zero w h
    simp only [Function.iterate_one, kmswMap_rot, stageRot_zero,
      Equiv.Perm.one_apply]
    generalize hatDartMap w h 0 d = e
    revert e
    rw [ht]
    intro e
    rfl
  · intro j hj hjk
    omega

private def boundaryCastDart {k l : ℕ} (h : k = l) (d : StageDart k) : StageDart l :=
  (Fin.cast h d.1, d.2)

private theorem boundary_transport_return {k k' l l' : ℕ}
    (hk : k' = k) (hl : l' = l)
    (σ : Equiv.Perm (StageDart k)) (σ' : Equiv.Perm (StageDart k'))
    (ρ : Equiv.Perm (StageDart l)) (ρ' : Equiv.Perm (StageDart l'))
    (i : StageDart k → StageDart l) (i' : StageDart k' → StageDart l')
    (hσ : StageRotation.resize hk σ' = σ)
    (hρ : StageRotation.resize hl ρ' = ρ)
    (hi : ∀ d, boundaryCastDart hl (i' d) = i (boundaryCastDart hk d))
    (ih : ∀ d, ∃ n : ℕ, 0 < n ∧ (ρ : _ → _)^[n] (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < n → (ρ : _ → _)^[j] (i d) ∉ Set.range i) :
    ∀ d, ∃ n : ℕ, 0 < n ∧ (ρ' : _ → _)^[n] (i' d) = i' (σ' d) ∧
      ∀ j : ℕ, 0 < j → j < n → (ρ' : _ → _)^[j] (i' d) ∉ Set.range i' := by
  cases hk
  cases hl
  change σ' = σ at hσ
  change ρ' = ρ at hρ
  subst σ'
  subst ρ'
  have he : i' = i := funext hi
  subst i'
  exact ih

/-- A non-exit down activation transports the complete induced-rotation
induction invariant. Both upper-right stacks are nonempty, so no geometric
dart is allocated and both rotation permutations are unchanged.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_step_activation (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m)
    (hc : hatCodes w h m = 2)
    (hur : (kmswStage (hatCodes w h) m).UR ≠ [])
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
          (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
            (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (m + 1)).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[k]
          (hatDartMap w h (m + 1) d) =
            hatDartMap w h (m + 1) ((kmswMap (hatCodes w h) (m + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[j]
            (hatDartMap w h (m + 1) d) ∉ Set.range (hatDartMap w h (m + 1)) := by
  let n := quadrantRStageTime w h m
  have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
    rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hm]
  have hcodes : hatCodes w h m = w n := by
    rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  have hcg : w n = 2 := hcodes.symm.trans hc
  have hcl : kmswCodeStep (hatCodes w h m) = .down := by rw [hc]; rfl
  have hcr : kmswCodeStep (w n) = .down := by rw [hcg]; rfl
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hur
  have hg : (kmswStage w n).UR =
      hatAllEdgeMap w h m e :: List.map (hatAllEdgeMap w h m) es := by
    simpa only [he, List.map_cons] using (hatAll_sim w h m).ur_eq.symm
  have hk : (kmswStage (hatCodes w h) (m + 1)).nextEdge =
      (kmswStage (hatCodes w h) m).nextEdge := by
    simp only [kmswStage, kmswStep, hcl, kmswStepOfStep, he]
  have hl : (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge =
      (kmswStage w n).nextEdge := by
    rw [ht]
    simp only [kmswStage, kmswStep, hcr, kmswStepOfStep, hg]
  apply boundary_transport_return hk hl
    (kmswMap (hatCodes w h) m).rot (kmswMap (hatCodes w h) (m + 1)).rot
    (kmswMap w n).rot (kmswMap w (quadrantRStageTime w h (m + 1))).rot
    (hatDartMap w h m) (hatDartMap w h (m + 1))
  · exact StageRotation.step_activation (kmswStage (hatCodes w h) m)
      (act_lt_nextEdge (hatCodes w h) le_rfl)
      (stageRotation_UL_bound (hatCodes w h) m) (stageRot (hatCodes w h) m)
      (hatCodes w h m) hcl e es he
  · have hr := StageRotation.step_activation (kmswStage w n)
      (act_lt_nextEdge w le_rfl) (stageRotation_UL_bound w n) (stageRot w n)
      (w n) hcr _ _ hg
    change StageRotation.resize hl
      (stageRot w (quadrantRStageTime w h (m + 1))) = stageRot w n
    revert hl
    rw [ht]
    intro hl
    exact hr
  · intro d
    apply Prod.ext
    · apply Fin.ext
      exact hatAllEdgeMap_extend w h m d.1.val (hk ▸ d.1.isLt)
    · rfl
  · exact ih

private theorem boundary_finite_first_return {D E : Type*} [Finite E]
    (ρ : Equiv.Perm E) (i : D → E) (d : D) :
    ∃ k : ℕ, 0 < k ∧ (∃ e, i e = (ρ : E → E)^[k] (i d)) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i := by
  classical
  obtain ⟨n, hn, _, he⟩ := (Equiv.Perm.SameCycle.refl ρ (i d)).exists_pow_eq''
  have hex : ∃ n : ℕ, 0 < n ∧ (ρ : E → E)^[n] (i d) ∈ Set.range i :=
    ⟨n, hn, d, he.symm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hjk hmem
  exact Nat.find_min hex hjk ⟨hj, hmem⟩

private theorem boundary_return_eq_successor_of_inner (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (d e : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (k : ℕ) (hk : 0 < k)
    (he : hatDartMap w h m e =
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k] (hatDartMap w h m d))
    (hgap : ∀ j : ℕ, 0 < j → j < k →
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
        (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m))
    (heo : (kmswMap (hatCodes w h) m).edgeInv e ∉ stageOuterWord (hatCodes w h) m) :
    e = (kmswMap (hatCodes w h) m).rot d := by
  let σ := (kmswMap (hatCodes w h) m).rot
  let ρ := (kmswMap w (quadrantRStageTime w h m)).rot
  let i := hatDartMap w h m
  have hr : ρ.symm (i e) = i (σ.symm e) :=
    hatDartMap_rot_symm_of_not_outer w h m e heo
  cases k with
  | zero => omega
  | succ t =>
    have hpred : (ρ : _ → _)^[t] (i d) = i (σ.symm e) := by
      calc
        _ = ρ.symm ((ρ : _ → _)^[t + 1] (i d)) := by
          rw [Function.iterate_succ_apply', Equiv.symm_apply_apply]
        _ = ρ.symm (i e) := congrArg ρ.symm he.symm
        _ = i (σ.symm e) := hr
    cases t with
    | zero =>
      have hde : d = σ.symm e := (hatDartMap_injective w h m) hpred
      exact (σ.eq_symm_apply.mp hde).symm
    | succ t =>
      exact (hgap (t + 1) (by omega) (by omega)
        ⟨σ.symm e, hpred.symm⟩).elim

/-- At a boundary successor corner the finite first return is an outer
corner at the same local vertex. This does not identify which outer corner
is returned when there are several. The excluded image contains all allocated
geometric darts, including missing edges. Hatted-half helper for -/
theorem hatDartMap_first_return_boundary (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : (kmswMap (hatCodes w h) m).edgeInv
      ((kmswMap (hatCodes w h) m).rot d) ∈ stageOuterWord (hatCodes w h) m) :
    ∃ k : ℕ, ∃ e : StageDart (kmswStage (hatCodes w h) m).nextEdge,
      0 < k ∧
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
        (hatDartMap w h m d) = hatDartMap w h m e ∧
      (∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
          (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)) ∧
      stageEndpoint (kmswStage (hatCodes w h) m) e =
        stageEndpoint (kmswStage (hatCodes w h) m) d ∧
      (kmswMap (hatCodes w h) m).edgeInv e ∈ stageOuterWord (hatCodes w h) m := by
  classical
  let ρ := (kmswMap w (quadrantRStageTime w h m)).rot
  let i := hatDartMap w h m
  obtain ⟨k, hk, ⟨e, he⟩, hgap⟩ := boundary_finite_first_return ρ i d
  refine ⟨k, e, hk, he.symm, hgap, ?_, ?_⟩
  · have hc : ρ.SameCycle (i d) (i e) := by
      rw [he]
      exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl ρ (i d))
    have hl := (hatDartMap_sameCycle_iff w h m d e).mp hc
    exact ((stageRot_sameCycle_iff_endpoint_eq _ m d e).mp hl).symm
  · by_contra heo
    have het := boundary_return_eq_successor_of_inner w h m d e k hk he hgap heo
    exact heo (het.symm ▸ hd)

/- Remaining induction branches for the entire induced-rotation invariant:

* Non-exit up: transport old-vertex cyclic orders through the two insertions
  and verify the new two-dart vertex.
* Non-exit existing-predecessor left: transport cyclic orders through both
  insertions, using the matched predecessor at positive phase depth.
* Non-exit down with empty UR: transport cyclic orders through pendant insertion.
* Exit: compose the down update with the skipped global excursion and prove
  that every intervening ambient dart lies outside the entire local image.

Local fresh-left is excluded by `noFreshLeftSource_hatCodes` in the import.
The initial case and non-exit down activation are proved in this module.
The boundary-return theorem proves existence, exclusion, and membership in
the correct vertex's outer-corner set; it does not select the local successor.
No induced embedding of arbitrary hatted stages is asserted here. -/

end DirectedDistances.KMSW


namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private theorem boundary_pair_old {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hxy : x ≠ y) (d : D) :
    StageRotation.pairSplice σ τ a b x y (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
  by_cases hda : d = a
  · subst d
    simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hx, hxy]
  · by_cases hdb : σ d = b <;>
      simp [StageRotation.pairSplice, insertBefore, insertAfter,
        Equiv.swap_apply_def, hda, hdb]

private theorem boundary_pair_path {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (ρ : Equiv.Perm E) (τ : Equiv.Perm F) (i : D → E)
    (a b : D) (x y : F) (hx : τ x = x) (hxy : x ≠ y)
    (d : D) (k : ℕ) (_hk : 0 < k)
    (hgap : ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i)
    (z : E ⊕ F)
    (hz : StageRotation.pairSplice ρ τ (i a) (i b) x y z =
      if ρ (i d) = i b then .inr y else .inl (ρ (i d))) :
    ∀ j, 0 < j → j ≤ k →
      (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j] z =
        if (ρ : E → E)^[j] (i d) = i b then .inr y
        else .inl ((ρ : E → E)^[j] (i d)) := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
    intro hj hjk
    cases j with
    | zero => exact hz
    | succ j =>
      have hlt : j + 1 < k := by omega
      have hn := hgap (j + 1) (by omega) hlt
      have hna : (ρ : E → E)^[j + 1] (i d) ≠ i a :=
        fun he => hn ⟨a, he.symm⟩
      have hnb : (ρ : E → E)^[j + 1] (i d) ≠ i b :=
        fun he => hn ⟨b, he.symm⟩
      rw [Function.iterate_succ_apply', ih (by omega) (by omega), ite_eq_right hnb,
        boundary_pair_old ρ τ (i a) (i b) x y hx hxy _, ite_eq_right hna]
      simp only [Function.iterate_succ_apply']

private theorem boundary_pair_induced {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (τ : Equiv.Perm F)
    (i : D → E) (hi : Function.Injective i) (a b : D) (x y : F)
    (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y)
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ d : D ⊕ F, ∃ k : ℕ, 0 < k ∧
      (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[k]
        (Sum.map i id d) =
          Sum.map i id (StageRotation.pairSplice σ τ a b x y d) ∧
      ∀ j, 0 < j → j < k →
        (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j]
          (Sum.map i id d) ∉ Set.range (Sum.map i (id : F → F)) := by
  have corridor (d : D) (z : E ⊕ F)
      (hz : StageRotation.pairSplice ρ τ (i a) (i b) x y z =
        if ρ (i d) = i b then .inr y else .inl (ρ (i d))) :
      ∃ k : ℕ, 0 < k ∧
        (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[k] z =
          (if σ d = b then .inr y else .inl (i (σ d))) ∧
        ∀ j, 0 < j → j < k →
          (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j] z ∉
            Set.range (Sum.map i (id : F → F)) := by
    obtain ⟨k, hk, he, hg⟩ := ih d
    have hp := boundary_pair_path ρ τ i a b x y hx hxy d k hk hg z hz
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hp k hk le_rfl, he]
      simp only [hi.eq_iff]
    · intro j hj hjk hm
      have hn := hg j hj hjk
      have hnb : (ρ : E → E)^[j] (i d) ≠ i b := fun he => hn ⟨b, he.symm⟩
      rw [hp j hj (by omega), ite_eq_right hnb] at hm
      obtain ⟨e, he⟩ := hm
      cases e with
      | inl e => exact hn ⟨e, Sum.inl.inj he⟩
      | inr e => cases he
  intro d
  cases d with
  | inl d =>
    by_cases hda : d = a
    · subst d
      refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inl, boundary_pair_old ρ τ (i a) (i b) x y hx hxy,
          boundary_pair_old σ τ a b x y hx hxy, ite_true, Sum.map_inr, id_eq]
      · intro j hj hjk; omega
    · have hia : i d ≠ i a := fun he => hda (hi he)
      obtain ⟨k, hk, he, hg⟩ := corridor d (.inl (i d)) (by
        rw [boundary_pair_old ρ τ (i a) (i b) x y hx hxy, ite_eq_right hia])
      refine ⟨k, hk, ?_, hg⟩
      rw [boundary_pair_old σ τ a b x y hx hxy, ite_eq_right hda]
      simpa only [Sum.map_inl, Sum.map_inr, id_eq, apply_ite] using he
  | inr z =>
    by_cases hzx : z = x
    · subst z
      have hxval (η : Equiv.Perm D) :
          StageRotation.pairSplice η τ a b x y (.inr x) =
            if η a = b then .inr y else .inl (η a) := by
        by_cases hab : η a = b <;>
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hab]
      have hxval' : StageRotation.pairSplice ρ τ (i a) (i b) x y (.inr x) =
          if ρ (i a) = i b then .inr y else .inl (ρ (i a)) := by
        by_cases hab : ρ (i a) = i b <;>
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hab]
      obtain ⟨k, hk, he, hg⟩ := corridor a (.inr x) hxval'
      refine ⟨k, hk, ?_, hg⟩
      rw [hxval]
      simpa only [Sum.map_inr, id_eq, Sum.map_inl, apply_ite] using he
    · refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inr, id_eq]
        by_cases hzy : z = y
        · subst z
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hy, hzx]
        · have hτzy : τ z ≠ y := fun he => hzy (τ.injective (he.trans hy.symm))
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hzx, hτzy]
      · intro j hj hjk; omega

private theorem boundary_congr_return {D E D' E' : Type*}
    (e : D ≃ D') (f : E ≃ E')
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E)
    (σ' : Equiv.Perm D') (ρ' : Equiv.Perm E')
    (i : D → E) (i' : D' → E')
    (hs : ∀ d, σ' (e d) = e (σ d))
    (hr : ∀ d, ρ' (f d) = f (ρ d))
    (hi : ∀ d, i' (e d) = f (i d))
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ' : E' → E')^[k] (i' d) = i' (σ' d) ∧
      ∀ j, 0 < j → j < k → (ρ' : E' → E')^[j] (i' d) ∉ Set.range i' := by
  have ht (n : ℕ) (d : E) : (ρ' : E' → E')^[n] (f d) = f ((ρ : E → E)^[n] d) := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply', hn, hr, Function.iterate_succ_apply']
  intro d
  obtain ⟨d, rfl⟩ := e.surjective d
  obtain ⟨k, hk, he, hg⟩ := ih d
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hi, ht, he, hs, hi]
  · intro j hj hjk hm
    obtain ⟨z, hz⟩ := hm
    obtain ⟨z, rfl⟩ := e.surjective z
    rw [hi, hi, ht] at hz
    exact hg j hj hjk ⟨z, f.injective hz⟩

/-- A non-exit up step preserves induced rotation on all geometric darts,
including both fresh edges. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_step_up (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m)
    (hc : hatCodes w h m = 1)
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
          (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
            (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (m + 1)).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[k]
          (hatDartMap w h (m + 1) d) =
            hatDartMap w h (m + 1) ((kmswMap (hatCodes w h) (m + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[j]
            (hatDartMap w h (m + 1) d) ∉ Set.range (hatDartMap w h (m + 1)) := by
  classical
  let n := quadrantRStageTime w h m
  let sh := kmswStage (hatCodes w h) m
  let gl := kmswStage w n
  have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
    rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hm]
  have hcodes : hatCodes w h m = w n := by
    rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  have hcl : kmswCodeStep (hatCodes w h m) = .up := by rw [hc]; rfl
  have hcr : kmswCodeStep (w n) = .up := by rw [← hcodes, hc]; rfl
  have hk : (kmswStage (hatCodes w h) (m + 1)).nextEdge = sh.nextEdge + 2 := by
    simp only [kmswStage, kmswStep, hcl, kmswStepOfStep, State.addEdge]
    rfl
  have hl : (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge = gl.nextEdge + 2 := by
    rw [ht]
    simp only [kmswStage, kmswStep, hcr, kmswStepOfStep, State.addEdge]
    rfl
  let i := hatDartMap w h m
  let J : StageDart (sh.nextEdge + 2) → StageDart (gl.nextEdge + 2) :=
    fun d => StageRotation.allocation gl.nextEdge 2
      (Sum.map i id ((StageRotation.allocation sh.nextEdge 2).symm d))
  let a : StageDart sh.nextEdge := (⟨sh.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart sh.nextEdge := (⟨sh.active, act_lt_nextEdge _ le_rfl⟩, true)
  have hia : i a = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, false) := by
    apply Prod.ext
    · exact Fin.ext (hatAll_sim w h m).incidenceSim.active
    · rfl
  have hiA : i A = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, true) := by
    apply Prod.ext
    · exact Fin.ext (hatAll_sim w h m).incidenceSim.active
    · rfl
  apply boundary_transport_return hk hl
    (StageRotation.up sh.nextEdge (stageRot (hatCodes w h) m) a A)
    (kmswMap (hatCodes w h) (m + 1)).rot
    (StageRotation.up gl.nextEdge (stageRot w n) (i a) (i A))
    (kmswMap w (quadrantRStageTime w h (m + 1))).rot J (hatDartMap w h (m + 1))
  · exact StageRotation.step_up sh (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ m) (stageRot (hatCodes w h) m) _ hcl
  · rw [hia, hiA]
    have hr := StageRotation.step_up gl (act_lt_nextEdge w le_rfl)
      (stageRotation_UL_bound w n) (stageRot w n) _ hcr
    change StageRotation.resize hl (stageRot w (quadrantRStageTime w h (m + 1))) = _
    revert hl
    rw [ht]
    intro hl
    exact hr
  · intro d
    have hmap : hatAllEdgeMap w h (m + 1) = kmswShiftUpEdgeMap sh gl (hatAllEdgeMap w h m) := by
      simp only [hatAllEdgeMap, dite_eq_right hm, hcl, kmswShiftNextEdgeMap]
      rfl
    obtain ⟨z, hz⟩ := (StageRotation.allocation sh.nextEdge 2).surjective (boundaryCastDart hk d)
    apply Prod.ext
    · apply Fin.ext
      change hatAllEdgeMap w h (m + 1) d.1.val = _
      rw [hmap]
      rw [← hz]
      cases z with
      | inl e =>
        have hv : d.1.val = e.1.val := (congrArg (fun z => z.1.val) hz).symm
        have h0 : e.1.val ≠ sh.nextEdge := ne_of_lt e.1.isLt
        have h1 : e.1.val ≠ sh.nextEdge + 1 := by have := e.1.isLt; omega
        simp only [J, Equiv.symm_apply_apply, Sum.map_inl]
        simp only [hv, kmswShiftUpEdgeMap, h0, h1, ↓reduceIte]
        rfl
      | inr e =>
        have hv : d.1.val = sh.nextEdge + e.1.val := (congrArg (fun z => z.1.val) hz).symm
        simp only [J, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
        have he := e.1.isLt
        have he' : e.1.val = 0 ∨ e.1.val = 1 := by omega
        rcases he' with he' | he' <;> simp [hv, he', kmswShiftUpEdgeMap, StageRotation.allocation]
    · change d.2 = (J (boundaryCastDart hk d)).2
      rw [← hz]
      have hb : (boundaryCastDart hk d).2 = d.2 := rfl
      rw [← hz] at hb
      cases z with
      | inl e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inl]
        simp only [i, hatDartMap]
        rw [StageRotation.allocation_old]
        rw [StageRotation.allocation_old] at hb
        exact hb.symm
      | inr e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
        rw [StageRotation.allocation_new]
        rw [StageRotation.allocation_new] at hb
        exact hb.symm
  · apply boundary_congr_return (StageRotation.allocation sh.nextEdge 2)
      (StageRotation.allocation gl.nextEdge 2)
      (StageRotation.pairSplice (stageRot (hatCodes w h) m)
        (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))
      (StageRotation.pairSplice (stageRot w n)
        (Equiv.swap (0, true) (1, false)) (i a) (i A) (0, false) (1, true))
      _ _ (Sum.map i id) J
    · intro d
      simp only [StageRotation.up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [StageRotation.up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [J, Equiv.symm_apply_apply]
    · exact boundary_pair_induced _ _ _ i (hatDartMap_injective w h m)
        a A (0, false) (1, true) (by decide) (by decide) (by decide) ih

/-- A non-exit existing-predecessor left step preserves induced rotation on all geometric darts,
including the fresh edge. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_step_leftExisting (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m)
    (hc : hatCodes w h m = 0)
    (hul : (kmswStage (hatCodes w h) m).UL.dropLast.reverse ≠ [])
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
          (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
            (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (m + 1)).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[k]
          (hatDartMap w h (m + 1) d) =
            hatDartMap w h (m + 1) ((kmswMap (hatCodes w h) (m + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[j]
            (hatDartMap w h (m + 1) d) ∉ Set.range (hatDartMap w h (m + 1)) := by
  classical
  let n := quadrantRStageTime w h m
  let sh := kmswStage (hatCodes w h) m
  let gl := kmswStage w n
  have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
    rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hm]
  have hcodes : hatCodes w h m = w n := by
    rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  have hcl : kmswCodeStep (hatCodes w h m) = .left := by rw [hc]; rfl
  have hcr : kmswCodeStep (w n) = .left := by rw [← hcodes, hc]; rfl
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil hul
  have hpos : hatPhaseDepth w n ≠ 0 := by
    intro hz
    have hphase := (quadrantRStageTime_spec w h m).1
    have hn := (quadrantRStageTime_spec w h (m + 1)).1
    rw [ht] at hn
    have he := (hatPhaseDepth_left_exit_iff w n hphase (hcodes.symm.trans hc)).2 hz
    rw [hn] at he
    contradiction
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hs := hatAll_sim w h m
  have hprefix := hs.ul_depth_prefix
  change (List.map (hatAllEdgeMap w h m) sh.UL.dropLast.reverse).take (hatPhaseDepth w n) =
    gl.UL.dropLast.reverse.take (hatPhaseDepth w n) at hprefix
  rw [hq, hp] at hprefix
  have hgne : gl.UL.dropLast.reverse ≠ [] := by
    intro he
    simp only [he, List.take_nil, List.map_cons, List.take_succ_cons] at hprefix
    cases hprefix
  obtain ⟨r, rs, hr⟩ := List.exists_cons_of_ne_nil hgne
  have hpr : hatAllEdgeMap w h m p = r := by
    rw [hr] at hprefix
    exact (List.cons.inj hprefix).1
  have hpb : p < sh.nextEdge := stageRotation_UL_bound _ m p
    (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hp]; exact List.mem_cons_self)))
  have hrb : r < gl.nextEdge := stageRotation_UL_bound w n r
    (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hr]; exact List.mem_cons_self)))
  have hk : (kmswStage (hatCodes w h) (m + 1)).nextEdge = sh.nextEdge + 1 := by
    simp only [kmswStage, kmswStep, hcl, kmswStepOfStep, hp, State.addEdge]
    rfl
  have hl : (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge = gl.nextEdge + 1 := by
    rw [ht]
    change (kmswStepOfStep gl (kmswCodeStep (w n))).nextEdge = _
    rw [hcr]
    simp only [kmswStepOfStep, hr, State.addEdge]
  let i := hatDartMap w h m
  let J : StageDart (sh.nextEdge + 1) → StageDart (gl.nextEdge + 1) :=
    fun d => StageRotation.allocation gl.nextEdge 1
      (Sum.map i id ((StageRotation.allocation sh.nextEdge 1).symm d))
  let a : StageDart sh.nextEdge := (⟨p, hpb⟩, false)
  let A : StageDart sh.nextEdge := (⟨sh.active, act_lt_nextEdge _ le_rfl⟩, true)
  have hia : i a = (⟨r, hrb⟩, false) := by
    apply Prod.ext
    · exact Fin.ext hpr
    · rfl
  have hiA : i A = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, true) := by
    apply Prod.ext
    · exact Fin.ext (hatAll_sim w h m).incidenceSim.active
    · rfl
  apply boundary_transport_return hk hl
    (StageRotation.leftExisting sh.nextEdge (stageRot (hatCodes w h) m) a A)
    (kmswMap (hatCodes w h) (m + 1)).rot
    (StageRotation.leftExisting gl.nextEdge (stageRot w n) (i a) (i A))
    (kmswMap w (quadrantRStageTime w h (m + 1))).rot J (hatDartMap w h (m + 1))
  · exact StageRotation.step_leftExisting sh (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ m) (stageRot (hatCodes w h) m) _ hcl p ps hp
  · rw [hia, hiA]
    have hrot := StageRotation.step_leftExisting gl (act_lt_nextEdge w le_rfl)
      (stageRotation_UL_bound w n) (stageRot w n) _ hcr r rs hr
    change StageRotation.resize hl (stageRot w (quadrantRStageTime w h (m + 1))) = _
    revert hl
    rw [ht]
    intro hl
    exact hrot
  · intro d
    have hmap : hatAllEdgeMap w h (m + 1) = kmswShiftFreshEdgeMap sh gl (hatAllEdgeMap w h m) := by
      simp only [hatAllEdgeMap, dite_eq_right hm, hcl, kmswShiftNextEdgeMap, hp]
      rfl
    obtain ⟨z, hz⟩ := (StageRotation.allocation sh.nextEdge 1).surjective (boundaryCastDart hk d)
    apply Prod.ext
    · apply Fin.ext
      change hatAllEdgeMap w h (m + 1) d.1.val = _
      rw [hmap]
      rw [← hz]
      cases z with
      | inl e =>
        have hv : d.1.val = e.1.val := (congrArg (fun z => z.1.val) hz).symm
        have h0 : e.1.val ≠ sh.nextEdge := ne_of_lt e.1.isLt
        simp only [J, Equiv.symm_apply_apply, Sum.map_inl]
        simp only [hv, kmswShiftFreshEdgeMap, h0, ↓reduceIte]
        rfl
      | inr e =>
        have hv : d.1.val = sh.nextEdge + e.1.val := (congrArg (fun z => z.1.val) hz).symm
        simp only [J, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
        have he : e.1.val = 0 := by have := e.1.isLt; omega
        simp [hv, kmswShiftFreshEdgeMap, StageRotation.allocation]
    · change d.2 = (J (boundaryCastDart hk d)).2
      rw [← hz]
      have hb : (boundaryCastDart hk d).2 = d.2 := rfl
      rw [← hz] at hb
      cases z with
      | inl e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inl]
        simp only [i, hatDartMap]
        rw [StageRotation.allocation_old]
        rw [StageRotation.allocation_old] at hb
        exact hb.symm
      | inr e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
        rw [StageRotation.allocation_new]
        rw [StageRotation.allocation_new] at hb
        exact hb.symm
  · apply boundary_congr_return (StageRotation.allocation sh.nextEdge 1)
      (StageRotation.allocation gl.nextEdge 1)
      (StageRotation.pairSplice (stageRot (hatCodes w h) m)
        (Equiv.refl (StageDart 1)) a A (0, false) (0, true))
      (StageRotation.pairSplice (stageRot w n)
        (Equiv.refl (StageDart 1)) (i a) (i A) (0, false) (0, true))
      _ _ (Sum.map i id) J
    · intro d
      simp only [StageRotation.leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [StageRotation.leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [J, Equiv.symm_apply_apply]
    · exact boundary_pair_induced _ _ _ i (hatDartMap_injective w h m)
        a A (0, false) (0, true) (by decide) (by decide) (by decide) ih

end DirectedDistances.KMSW

/- Continuation status: the non-exit up and existing-predecessor left branches
are proved above, in addition to the original activation branch. The remaining
induction branches are pendant down (empty local UR, hence empty ambient UR)
and exit-excursion composition. These helpers do not complete `lem-quad-kmsw`. -/
