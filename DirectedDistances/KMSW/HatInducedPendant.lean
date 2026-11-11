module

public import DirectedDistances.KMSW.HatInducedBoundary

/-! # Pendant insertion and hatted induced rotation

Hatted-half helper toward `lem-quad-kmsw`, not the paper result -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private def pendantCastDart {k l : ℕ} (h : k = l) (d : StageDart k) : StageDart l :=
  (Fin.cast h d.1, d.2)

private theorem pendantTransportReturn {k k' l l' : ℕ}
    (hk : k' = k) (hl : l' = l)
    (σ : Equiv.Perm (StageDart k)) (σ' : Equiv.Perm (StageDart k'))
    (ρ : Equiv.Perm (StageDart l)) (ρ' : Equiv.Perm (StageDart l'))
    (i : StageDart k → StageDart l) (i' : StageDart k' → StageDart l')
    (hσ : StageRotation.resize hk σ' = σ)
    (hρ : StageRotation.resize hl ρ' = ρ)
    (hi : ∀ d, pendantCastDart hl (i' d) = i (pendantCastDart hk d))
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

private theorem pendantCongrReturn {D E D' E' : Type*}
    (e : D ≃ D') (f : E ≃ E')
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E)
    (σ' : Equiv.Perm D') (ρ' : Equiv.Perm E')
    (i : D → E) (i' : D' → E')
    (hs : ∀ d, σ' (e d) = e (σ d))
    (hr : ∀ d, ρ' (f d) = f (ρ d))
    (hi : ∀ d, i' (e d) = f (i d))
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : _ → _)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : _ → _)^[j] (i d) ∉ Set.range i) :
    ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ' : _ → _)^[k] (i' d) = i' (σ' d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ' : _ → _)^[j] (i' d) ∉ Set.range i' := by
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

private theorem boundary_insert_old {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a : D) (x : F) (d : D) :
    insertBefore (Equiv.sumCongr σ τ) (.inl a) (.inr x) (.inl d) =
      if σ d = a then .inr x else .inl (σ d) := by
  by_cases h : σ d = a <;>
    simp [insertBefore, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h]

private theorem boundary_insert_new {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a : D) (x : F) (hx : τ x = x) :
    insertBefore (Equiv.sumCongr σ τ) (.inl a) (.inr x) (.inr x) = .inl a := by
  simp [insertBefore, Equiv.Perm.mul_apply, hx]

private theorem boundary_insert_other {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a : D) (x z : F)
    (hx : τ x = x) (hz : z ≠ x) :
    insertBefore (Equiv.sumCongr σ τ) (.inl a) (.inr x) (.inr z) = .inr (τ z) := by
  have hτ : τ z ≠ x := by
    intro h
    exact hz (τ.injective (h.trans hx.symm))
  simp [insertBefore, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hτ]

private theorem boundary_insert_path {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (ρ : Equiv.Perm E) (τ : Equiv.Perm F) (i : D → E)
    (a : D) (x : F) (d : D) (k : ℕ)
    (hgap : ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ j, 0 < j → j ≤ k →
      (insertBefore (Equiv.sumCongr ρ τ) (.inl (i a)) (.inr x) : _ → _)^[j]
        (.inl (i d)) =
      if (ρ : E → E)^[j] (i d) = i a then .inr x
      else .inl ((ρ : E → E)^[j] (i d)) := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
    intro hj hjk
    cases j with
    | zero =>
      simpa only [Function.iterate_one, Nat.zero_add] using
        (boundary_insert_old ρ τ (i a) x (i d))
    | succ j =>
      have hlt : j + 1 < k := by omega
      have hn := hgap (j + 1) (by omega) hlt
      have hna : (ρ : E → E)^[j + 1] (i d) ≠ i a :=
        fun he => hn ⟨a, he.symm⟩
      rw [Function.iterate_succ_apply', ih (by omega) (by omega)]
      rw [ite_eq_right hna, boundary_insert_old]
      simp only [Function.iterate_succ_apply']

private theorem boundary_single_insertion_induced {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (τ : Equiv.Perm F)
    (i : D → E) (hi : Function.Injective i) (a : D) (x : F)
    (hx : τ x = x)
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ d : D ⊕ F, ∃ k : ℕ, 0 < k ∧
      (insertBefore (Equiv.sumCongr ρ τ) (.inl (i a)) (.inr x) : _ → _)^[k]
        (Sum.map i id d) =
          Sum.map i id
            (insertBefore (Equiv.sumCongr σ τ) (.inl a) (.inr x) d) ∧
      ∀ j, 0 < j → j < k →
        (insertBefore (Equiv.sumCongr ρ τ) (.inl (i a)) (.inr x) : _ → _)^[j]
          (Sum.map i id d) ∉ Set.range (Sum.map i (id : F → F)) := by
  intro d
  cases d with
  | inl d =>
    obtain ⟨k, hk, he, hg⟩ := ih d
    have hhit : (ρ : E → E)^[k] (i d) = i a ↔ σ d = a := by
      rw [he]
      exact hi.eq_iff
    refine ⟨k, hk, ?_, ?_⟩
    · simp only [Sum.map_inl]
      rw [boundary_insert_path ρ τ i a x d k hg k hk (by omega)]
      by_cases hda : σ d = a
      · have hraw : (ρ : E → E)^[k] (i d) = i a := hhit.mpr hda
        rw [ite_eq_left hraw, boundary_insert_old σ τ a x d, ite_eq_left hda]
        simp only [Sum.map_inr, id_eq]
      · have hraw : (ρ : E → E)^[k] (i d) ≠ i a := fun heq => hda (hhit.mp heq)
        rw [ite_eq_right hraw, boundary_insert_old σ τ a x d, ite_eq_right hda, he]
        simp only [Sum.map_inl]
    · intro j hj hjk hmem
      have hn := hg j hj hjk
      have hneq : (ρ : E → E)^[j] (i d) ≠ i a :=
        fun heq => hn ⟨a, heq.symm⟩
      simp only [Sum.map_inl] at hmem
      rw [boundary_insert_path ρ τ i a x d k hg j hj (by omega),
        ite_eq_right hneq] at hmem
      obtain ⟨z, hz⟩ := hmem
      cases z with
      | inl z =>
        simp only [Sum.map_inl] at hz
        exact hn ⟨z, Sum.inl.inj hz⟩
      | inr z => cases hz
  | inr z =>
    by_cases hz : z = x
    · subst z
      refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inr, Sum.map_inl, id_eq,
          boundary_insert_new ρ τ (i a) x hx,
          boundary_insert_new σ τ a x hx]
      · intro j hj hjk
        omega
    · refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inr, id_eq,
          boundary_insert_other ρ τ (i a) x z hx hz,
          boundary_insert_other σ τ a x z hx hz]
      · intro j hj hjk
        omega

/-- The non-exit empty-UR down step preserves induced rotation through its
single pendant insertion. Helper toward `lem-quad-kmsw`; not the paper result -/
theorem hatDartMap_rot_induced_step_pendant (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m)
    (hc : hatCodes w h m = 2)
    (hur : (kmswStage (hatCodes w h) m).UR = [])
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
  have hcl : kmswCodeStep (hatCodes w h m) = .down := by rw [hc]; rfl
  have hcr : kmswCodeStep (w n) = .down := by rw [← hcodes, hc]; rfl
  have hgur : gl.UR = [] := by
    have hs := (hatAll_sim w h m).ur_eq
    change List.map (hatAllEdgeMap w h m) sh.UR = gl.UR at hs
    rw [hur] at hs
    simpa using hs.symm
  have hgurStage : (kmswStage w n).UR = [] := by simpa [gl] using hgur
  have hgurGlobal : (kmswStage w (quadrantRStageTime w h m)).UR = [] := by
    simpa only [n] using hgurStage
  have hk : (kmswStage (hatCodes w h) (m + 1)).nextEdge = sh.nextEdge + 1 := by
    simp only [kmswStage, kmswStep, hcl, kmswStepOfStep, hur, State.addEdge]
    rfl
  have hl : (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge = gl.nextEdge + 1 := by
    rw [ht]
    change (kmswStepOfStep gl (kmswCodeStep (w n))).nextEdge = _
    rw [hcr]
    simp [kmswStepOfStep, hgur, State.addEdge]
  let i := hatDartMap w h m
  let J : StageDart (sh.nextEdge + 1) → StageDart (gl.nextEdge + 1) :=
    fun d => StageRotation.allocation gl.nextEdge 1
      (Sum.map i id ((StageRotation.allocation sh.nextEdge 1).symm d))
  let A : StageDart sh.nextEdge := (⟨sh.active, act_lt_nextEdge _ le_rfl⟩, true)
  let x : StageDart 1 := (0, false)
  have hiA : i A = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, true) := by
    apply Prod.ext
    · exact Fin.ext (hatAll_sim w h m).incidenceSim.active
    · rfl
  apply pendantTransportReturn hk hl
    (StageRotation.pendant sh.nextEdge (stageRot (hatCodes w h) m) A)
    (kmswMap (hatCodes w h) (m + 1)).rot
    (StageRotation.pendant gl.nextEdge (stageRot w n) (i A))
    (kmswMap w (quadrantRStageTime w h (m + 1))).rot
    J (hatDartMap w h (m + 1))
  · exact StageRotation.step_pendant sh (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ m) (stageRot (hatCodes w h) m) _ hcl hur
  · rw [hiA]
    have hr := StageRotation.step_pendant gl (act_lt_nextEdge w le_rfl)
      (stageRotation_UL_bound w n) (stageRot w n) _ hcr hgur
    change StageRotation.resize hl (stageRot w (quadrantRStageTime w h (m + 1))) = _
    revert hl
    rw [ht]
    intro hl
    exact hr
  · intro d
    have hmap : hatAllEdgeMap w h (m + 1) =
        kmswShiftFreshEdgeMap sh gl (hatAllEdgeMap w h m) := by
      simp only [hatAllEdgeMap, dite_eq_right hm, hcl, sh, gl,
        n, kmswShiftNextEdgeMap, hur, hgurGlobal]
    obtain ⟨z, hz⟩ := (StageRotation.allocation sh.nextEdge 1).surjective
      (pendantCastDart hk d)
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
        simp only [hv, kmswShiftFreshEdgeMap, h0]
        rfl
      | inr e =>
        have hv : d.1.val = sh.nextEdge + e.1.val :=
          (congrArg (fun z => z.1.val) hz).symm
        have he : e.1.val = 0 := by have := e.1.isLt; omega
        simp [J, hv, kmswShiftFreshEdgeMap, StageRotation.allocation]
    · change d.2 = (J (pendantCastDart hk d)).2
      rw [← hz]
      have hb : (pendantCastDart hk d).2 = d.2 := rfl
      rw [← hz] at hb
      cases z with
      | inl e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inl]
        rw [StageRotation.allocation_old]
        rw [StageRotation.allocation_old] at hb
        exact hb.symm
      | inr e =>
        rcases e with ⟨e, b⟩
        simp only [J, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
        rw [StageRotation.allocation_new]
        rw [StageRotation.allocation_new] at hb
        exact hb.symm
  · apply pendantCongrReturn (StageRotation.allocation sh.nextEdge 1)
      (StageRotation.allocation gl.nextEdge 1)
      (insertBefore (Equiv.sumCongr (stageRot (hatCodes w h) m)
        (Equiv.refl (StageDart 1))) (.inl A) (.inr x))
      (insertBefore (Equiv.sumCongr (stageRot w n)
        (Equiv.refl (StageDart 1))) (.inl (i A)) (.inr x))
      _ _ (Sum.map i id) J
    · intro d
      simp only [StageRotation.pendant, x, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [StageRotation.pendant, x, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [J, Equiv.symm_apply_apply]
    · exact boundary_single_insertion_induced _ _ _ i
        (hatDartMap_injective w h m) A x rfl ih

end DirectedDistances.KMSW
