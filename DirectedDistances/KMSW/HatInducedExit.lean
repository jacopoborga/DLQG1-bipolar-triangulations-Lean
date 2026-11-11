module

public import DirectedDistances.KMSW.HatInducedBoundary

/-! # Exit alignment and rotation helpers for hatted stages

Each statement is a helper toward lem-quad-kmsw; not the paper result.
The skipped excursion and final down update are described in -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Alignment before and after the skipped global excursion: helper toward
lem-quad-kmsw; not the paper result -/
theorem hatExit_rotation_times (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageTime w h (hatExitIndex w h k) = walkNL w h k - 1 ∧
      quadrantRStageTime w h (hatExitIndex w h k + 1) = walkNR w h (k + 1) := by
  refine ⟨quadrantRStageTime_hatExitIndex w h k, ?_⟩
  rw [← hatCodeTime_succ, hatCodeTime_at_exit]
  have hp := (walkNR_succ_spec w h k).1
  omega

/-- The local exit update is exactly the down update, in both stack cases:
helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_local_update (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    kmswStage (hatCodes w h) (hatExitIndex w h k + 1) =
      kmswStepOfStep (kmswStage (hatCodes w h) (hatExitIndex w h k)) .down := by
  rw [kmswStage, hatCodes_at_exit]
  rfl

/-- At the next local stage every geometric edge image is either older than
the excursion or is the edge allocated by its final down step. This includes
missing edges: helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_edge_image_old_or_final (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (e : ℕ) (he : e < (kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).nextEdge) :
    hatAllEdgeMap w h (hatExitIndex w h k + 1) e <
        (kmswStage w (walkNL w h k - 1)).nextEdge ∨
      hatAllEdgeMap w h (hatExitIndex w h k + 1) e =
        (kmswStage w (walkNR w h (k + 1) - 1)).nextEdge := by
  classical
  let m := hatExitIndex w h k
  let sh := kmswStage (hatCodes w h) m
  let gl := kmswStage w (walkNL w h k - 1)
  have hur : List.map (hatAllEdgeMap w h m) sh.UR = gl.UR := by
    simpa only [m, sh, gl, quadrantRStageTime_hatExitIndex] using
      (hatAll_sim w h m).ur_eq
  by_cases hold : e < sh.nextEdge
  · left
    rw [hatAllEdgeMap_extend w h m e hold]
    have hb := (hatAll_sim w h m).incidenceSim.edge_bound e hold
    simpa only [m, quadrantRStageTime_hatExitIndex] using hb
  · have hlocal := hatExit_local_update w h k
    change kmswStage (hatCodes w h) (m + 1) = kmswStepOfStep sh .down at hlocal
    have hbound : e < (kmswStepOfStep sh .down).nextEdge := hlocal ▸ he
    cases hs : sh.UR with
    | cons a es =>
      simp only [kmswStepOfStep, hs] at hbound
      exact (hold hbound).elim
    | nil =>
      have heq : e = sh.nextEdge := by
        simp only [kmswStepOfStep, hs, State.addEdge] at hbound
        omega
      have hg : gl.UR = [] := by simpa only [hs, List.map_nil] using hur.symm
      have hex : ∃ l, hatExitIndex w h l = m := ⟨k, rfl⟩
      have hc : Classical.choose hex = k :=
        hatExitIndex_injective w h (Classical.choose_spec hex)
      have hm : hatAllEdgeMap w h (m + 1) =
          hatExcursionEdgeMap w h k ∘
            kmswShiftNextEdgeMap sh gl .down (hatAllEdgeMap w h m) := by
        simp only [hatAllEdgeMap, dite_eq_left hex, hc]
        rfl
      right
      change hatAllEdgeMap w h (m + 1) e = _
      rw [hm, Function.comp_apply]
      simp only [kmswShiftNextEdgeMap, hs, hg, kmswShiftFreshEdgeMap, heq, ↓reduceIte]
      simp [hatExcursionEdgeMap, show (kmswStage w (walkNL w h k - 1)).UR = [] from hg,
        kmswShiftFreshEdgeMap, gl]

/-- Every dart allocated during the skipped excursion, before its final down
update, is outside the entire next local image, including missing edges:
helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_excursion_dart_not_mem_range (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (d : StageDart
      (kmswStage w (quadrantRStageTime w h (hatExitIndex w h k + 1))).nextEdge)
    (hlo : (kmswStage w (walkNL w h k - 1)).nextEdge ≤ d.1.val)
    (hhi : d.1.val < (kmswStage w (walkNR w h (k + 1) - 1)).nextEdge) :
    d ∉ Set.range (hatDartMap w h (hatExitIndex w h k + 1)) := by
  rintro ⟨e, he⟩
  have heq : hatAllEdgeMap w h (hatExitIndex w h k + 1) e.1.val = d.1.val :=
    congrArg (fun x => x.1.val) he
  rcases hatExit_edge_image_old_or_final w h k e.1.val e.1.isLt with hold | hfinal
  · omega
  · omega

/-- First-return rotation invariants compose, with exclusion from the complete
composite image. This is the permutation composition step needed across an
exit: helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_induced_rotation_comp {D E F : Type*}
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (τ : Equiv.Perm F)
    (i : D → E) (q : E → F) (hq : Function.Injective q)
    (hi : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i)
    (hh : ∀ e, ∃ k : ℕ, 0 < k ∧ (τ : F → F)^[k] (q e) = q (ρ e) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : F → F)^[j] (q e) ∉ Set.range q) :
    ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : F → F)^[k] ((q ∘ i) d) = (q ∘ i) (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (τ : F → F)^[j] ((q ∘ i) d) ∉ Set.range (q ∘ i) := by
  intro d
  obtain ⟨k, hk, hend, hgap⟩ := hi d
  have liftPath : ∀ p : ℕ, p ≤ k → ∃ n : ℕ,
      (n = 0 ↔ p = 0) ∧
      (τ : F → F)^[n] (q (i d)) = q ((ρ : E → E)^[p] (i d)) ∧
      ∀ t : ℕ, 0 < t → t < n →
        (τ : F → F)^[t] (q (i d)) ∉ Set.range (q ∘ i) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨0, by simp, rfl, by intro t ht htn; omega⟩
    | succ p ih =>
      intro hpk
      obtain ⟨n, hn, he, hg⟩ := ih (by omega)
      obtain ⟨l, hl, hle, hlg⟩ := hh ((ρ : E → E)^[p] (i d))
      refine ⟨l + n, by omega, ?_, ?_⟩
      · rw [Function.iterate_add_apply, he, hle, Function.iterate_succ_apply']
      · intro t ht htn
        by_cases hsmall : t < n
        · exact hg t ht hsmall
        · by_cases hboundary : t = n
          · subst t
            have hp : 0 < p := by
              by_contra hp
              have hz : p = 0 := by omega
              have := hn.mpr hz
              omega
            intro hmem
            obtain ⟨z, hz⟩ := hmem
            rw [he] at hz
            exact hgap p hp (by omega) ⟨z, hq hz⟩
          · have hdiff : 0 < t - n := by omega
            have hdiff' : t - n < l := by omega
            have ht' : t = (t - n) + n := by omega
            intro hmem
            obtain ⟨z, hz⟩ := hmem
            rw [ht', Function.iterate_add_apply, he] at hz
            exact hlg (t - n) hdiff hdiff' ⟨i z, hz⟩
  obtain ⟨n, hn, he, hg⟩ := liftPath k le_rfl
  refine ⟨n, ?_, ?_, hg⟩
  · have : n ≠ 0 := fun hz => (by omega : k ≠ 0) (hn.mp hz)
    omega
  · simpa only [Function.comp_apply, hend] using he

private theorem exit_pair_old_induced {D F : Type*}
    [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y) :
    ∀ d, ∃ k : ℕ, 0 < k ∧
      (StageRotation.pairSplice σ τ a b x y : D ⊕ F → D ⊕ F)^[k] (.inl d) =
        .inl (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (StageRotation.pairSplice σ τ a b x y : D ⊕ F → D ⊕ F)^[j] (.inl d) ∉
          Set.range (Sum.inl : D → D ⊕ F) := by
  have old (d : D) : StageRotation.pairSplice σ τ a b x y (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
    by_cases hda : d = a
    · subst d
      simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hx, hxy]
    · by_cases hdb : σ d = b <;>
        simp [StageRotation.pairSplice, insertBefore, insertAfter,
          Equiv.swap_apply_def, hda, hdb]
  have newx : StageRotation.pairSplice σ τ a b x y (.inr x) =
      if σ a = b then .inr y else .inl (σ a) := by
    by_cases hab : σ a = b <;>
      simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hab]
  have newy : StageRotation.pairSplice σ τ a b x y (.inr y) = .inl b := by
    simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def,
      hy, hxy.symm]
  intro d
  by_cases hda : d = a
  · subst d
    by_cases hab : σ a = b
    · refine ⟨3, by omega, ?_, ?_⟩
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
          old, ite_true, newx, hab, newy]
      · intro j hj hjk
        have : j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl <;>
          simp [Function.iterate_succ_apply', old, newx, hab]
    · refine ⟨2, by omega, ?_, ?_⟩
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
          old, ite_true, newx, ite_eq_right hab]
      · intro j hj hjk
        have : j = 1 := by omega
        subst j
        simp [old]
  · by_cases hdb : σ d = b
    · refine ⟨2, by omega, ?_, ?_⟩
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
          old, ite_eq_right hda, hdb, ite_true, newy]
      · intro j hj hjk
        have : j = 1 := by omega
        subst j
        simp [old, hda, hdb]
    · refine ⟨1, by omega, ?_, ?_⟩
      · simp [old, hda, hdb]
      · intro j hj hjk
        omega

private theorem exit_alloc_old_induced {k l r : ℕ} (h : k ≤ l) (hl : l = k + r)
    (σ : Equiv.Perm (StageDart k)) (ρ : Equiv.Perm (StageDart l))
    (ψ : Equiv.Perm (StageDart k ⊕ StageDart r))
    (hρ : StageRotation.resize hl ρ = (StageRotation.allocation k r).permCongr ψ)
    (ih : ∀ d, ∃ n : ℕ, 0 < n ∧ (ψ : _ → _)^[n] (.inl d) = .inl (σ d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (ψ : _ → _)^[j] (.inl d) ∉ Set.range (Sum.inl : StageDart k → _)) :
    ∀ d, ∃ n : ℕ, 0 < n ∧
      (ρ : _ → _)^[n] (outerSucc_castDart h d) = outerSucc_castDart h (σ d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (ρ : _ → _)^[j] (outerSucc_castDart h d) ∉ Set.range (outerSucc_castDart h) := by
  cases hl
  change ρ = (StageRotation.allocation k r).permCongr ψ at hρ
  subst ρ
  let f := StageRotation.allocation k r
  have hit (n : ℕ) (z : StageDart k ⊕ StageDart r) :
      (f.permCongr ψ : _ → _)^[n] (f z) = f ((ψ : _ → _)^[n] z) := by
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [Function.iterate_succ_apply', hn, Equiv.permCongr_apply,
        Equiv.symm_apply_apply, Function.iterate_succ_apply']
  have hcast (d : StageDart k) : outerSucc_castDart h d = f (.inl d) := rfl
  intro d
  obtain ⟨n, hn, he, hg⟩ := ih d
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hcast, hit, he, hcast]
  · intro j hj hjn hmem
    obtain ⟨e, heq⟩ := hmem
    rw [hcast, hcast, hit] at heq
    exact hg j hj hjn ⟨e, f.injective heq⟩

private theorem exit_stage_old_step (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d, ∃ k : ℕ, 0 < k ∧
      (stageRot w (n + 1) : _ → _)^[k]
          (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) =
        outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) (stageRot w n d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (stageRot w (n + 1) : _ → _)^[j]
            (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) ∉
          Set.range (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))) := by
  classical
  let s := kmswStage w n
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w le_rfl⟩, true)
  let hnext := kmswStage_nextEdge_mono w (Nat.le_succ n)
  have same {k l : ℕ} (h : k ≤ l) (hl : l = k)
      (σ : Equiv.Perm (StageDart k)) (ρ : Equiv.Perm (StageDart l))
      (hr : StageRotation.resize hl ρ = σ) :
      ∀ d, ∃ t : ℕ, 0 < t ∧ (ρ : _ → _)^[t] (outerSucc_castDart h d) =
        outerSucc_castDart h (σ d) ∧
        ∀ j : ℕ, 0 < j → j < t →
          (ρ : _ → _)^[j] (outerSucc_castDart h d) ∉ Set.range (outerSucc_castDart h) := by
    cases hl
    change ρ = σ at hr
    subst ρ
    intro d
    exact ⟨1, by omega, rfl, by intro j hj hjt; omega⟩
  cases hc : kmswCodeStep (w n) with
  | down =>
    cases hur : s.UR with
    | cons e es =>
      have hk : (kmswStage w (n + 1)).nextEdge = s.nextEdge := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hc, kmswStepOfStep, hur]
      exact same hnext hk σ _ (StageRotation.step_activation s
        (act_lt_nextEdge w le_rfl) (stageRotation_UL_bound w n) σ (w n) hc e es hur)
    | nil =>
      have hk : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hc, kmswStepOfStep, hur, State.addEdge]
      apply exit_alloc_old_induced hnext hk σ _
        (insertBefore (Equiv.sumCongr σ (Equiv.refl (StageDart 1))) (.inl A) (.inr (0, false)))
        (StageRotation.step_pendant s (act_lt_nextEdge w le_rfl)
          (stageRotation_UL_bound w n) σ (w n) hc hur)
      let ψ := insertBefore (Equiv.sumCongr σ (Equiv.refl (StageDart 1)))
        (.inl A) (.inr (0, false))
      have old (d : StageDart s.nextEdge) : ψ (.inl d) =
          if σ d = A then .inr (0, false) else .inl (σ d) := by
        by_cases hd : σ d = A <;> simp [ψ, insertBefore, Equiv.swap_apply_def, hd]
      have fresh : ψ (.inr (0, false)) = .inl A := by
        simp [ψ, insertBefore]
      change ∀ d, ∃ k : ℕ, 0 < k ∧
        (ψ : _ → _)^[k] (.inl d) = .inl (σ d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (ψ : _ → _)^[j] (.inl d) ∉ Set.range (Sum.inl : StageDart s.nextEdge → _)
      intro d
      by_cases hd : σ d = A
      · refine ⟨2, by omega, ?_, ?_⟩
        · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
            old, hd, ite_true, fresh]
        · intro j hj hjk
          have : j = 1 := by omega
          subst j
          simp [old, hd]
      · refine ⟨1, by omega, ?_, ?_⟩
        · simp [old, hd]
        · intro j hj hjk
          omega
  | up =>
    have hk : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
      change (kmswStep s (w n)).nextEdge = _
      simp only [kmswStep, hc, kmswStepOfStep, State.addEdge]
    apply exit_alloc_old_induced hnext hk σ _
      (StageRotation.pairSplice σ (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))
      (StageRotation.step_up s (act_lt_nextEdge w le_rfl)
        (stageRotation_UL_bound w n) σ (w n) hc)
    exact exit_pair_old_induced σ _ a A (0, false) (1, true)
      (by decide) (by decide) (by decide)
  | left =>
    cases hul : s.UL.dropLast.reverse with
    | nil =>
      have hk : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hc, kmswStepOfStep, hul, State.addEdge]
      apply exit_alloc_old_induced hnext hk σ _
        (StageRotation.pairSplice σ (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true))
        (StageRotation.step_leftFresh s (act_lt_nextEdge w le_rfl)
          (stageRotation_UL_bound w n) σ (w n) hc hul)
      exact exit_pair_old_induced σ _ a A (1, true) (0, true)
        (by decide) (by decide) (by decide)
    | cons e es =>
      have he : e < s.nextEdge := stageRotation_UL_bound w n e
        (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hul]; simp)))
      let b : StageDart s.nextEdge := (⟨e, he⟩, false)
      have hk : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hc, kmswStepOfStep, hul, State.addEdge]
      apply exit_alloc_old_induced hnext hk σ _
        (StageRotation.pairSplice σ (Equiv.refl (StageDart 1)) b A (0, false) (0, true))
        (StageRotation.step_leftExisting s (act_lt_nextEdge w le_rfl)
          (stageRotation_UL_bound w n) σ (w n) hc e es hul)
      exact exit_pair_old_induced σ _ b A (0, false) (0, true)
        rfl rfl (by decide)

/-- Inclusion of any older ambient stage preserves its induced rotation on all
geometric darts. In particular this transports rotation across the skipped
excursion: helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_ambient_rotation_induced (w : ℕ → Fin 3) (m n : ℕ) (hmn : m ≤ n) :
    ∀ d, ∃ k : ℕ, 0 < k ∧
      (stageRot w n : _ → _)^[k] (outerSucc_castDart (kmswStage_nextEdge_mono w hmn) d) =
        outerSucc_castDart (kmswStage_nextEdge_mono w hmn) (stageRot w m d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (stageRot w n : _ → _)^[j]
            (outerSucc_castDart (kmswStage_nextEdge_mono w hmn) d) ∉
          Set.range (outerSucc_castDart (kmswStage_nextEdge_mono w hmn)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    intro d
    exact ⟨1, by omega, rfl, by intro j hj hjk; omega⟩
  | succ n hmn ih =>
    have hinj : Function.Injective
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))) := by
      intro d e he
      apply Prod.ext
      · exact Fin.ext (congrArg (fun z => z.1.val) he)
      · exact congrArg (fun z : StageDart (kmswStage w (n + 1)).nextEdge => z.2) he
    have hc : outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) ∘
        outerSucc_castDart (kmswStage_nextEdge_mono w hmn) =
        outerSucc_castDart (kmswStage_nextEdge_mono w (by omega : m ≤ n + 1)) := rfl
    simpa only [hc] using hatExit_induced_rotation_comp (stageRot w m) (stageRot w n)
      (stageRot w (n + 1)) (outerSucc_castDart (kmswStage_nextEdge_mono w hmn))
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)))
      hinj ih (exit_stage_old_step w n)

/-- An exit with nonempty local upper-right stack preserves the full
induced-rotation invariant, composing across the entire skipped excursion.
All geometric darts, including missing edges, are in the excluded image:
helper toward lem-quad-kmsw; not the paper result -/
theorem hatDartMap_rot_induced_exit_activation (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR ≠ [])
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k) d) =
            hatDartMap w h (hatExitIndex w h k)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k))) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k + 1) d) =
            hatDartMap w h (hatExitIndex w h k + 1)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k + 1) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k + 1)) := by
  let m := hatExitIndex w h k
  let s := kmswStage (hatCodes w h) m
  have transport {a a' b : ℕ} (ha : a' = a)
      (σ : Equiv.Perm (StageDart a)) (σ' : Equiv.Perm (StageDart a'))
      (ρ : Equiv.Perm (StageDart b))
      (i : StageDart a → StageDart b) (i' : StageDart a' → StageDart b)
      (hσ : StageRotation.resize ha σ' = σ)
      (hi : ∀ d, i' d = i (Fin.cast ha d.1, d.2))
      (ih : ∀ d, ∃ l : ℕ, 0 < l ∧ (ρ : _ → _)^[l] (i d) = i (σ d) ∧
        ∀ j : ℕ, 0 < j → j < l → (ρ : _ → _)^[j] (i d) ∉ Set.range i) :
      ∀ d, ∃ l : ℕ, 0 < l ∧ (ρ : _ → _)^[l] (i' d) = i' (σ' d) ∧
        ∀ j : ℕ, 0 < j → j < l → (ρ : _ → _)^[j] (i' d) ∉ Set.range i' := by
    cases ha
    change σ' = σ at hσ
    subst σ'
    have he : i' = i := funext hi
    subst i'
    exact ih
  have hc : kmswCodeStep (hatCodes w h m) = .down := by
    dsimp only [m]
    rw [hatCodes_at_exit]
    rfl
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hur
  change s.UR = e :: es at he
  have ha : (kmswStage (hatCodes w h) (m + 1)).nextEdge = s.nextEdge := by
    change (kmswStep s (hatCodes w h m)).nextEdge = _
    simp only [kmswStep, hc, kmswStepOfStep, he]
  let q := outerSucc_castDart (kmswStage_nextEdge_mono w
    (quadrantRStageTime_mono w h (Nat.le_succ m)))
  have hq : Function.Injective q := by
    intro d e he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) he)
    · exact congrArg (fun z : StageDart
        (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge => z.2) he
  have whole := hatExit_induced_rotation_comp
    (kmswMap (hatCodes w h) m).rot
    (kmswMap w (quadrantRStageTime w h m)).rot
    (kmswMap w (quadrantRStageTime w h (m + 1))).rot
    (hatDartMap w h m) q hq ih
    (hatExit_ambient_rotation_induced w (quadrantRStageTime w h m)
      (quadrantRStageTime w h (m + 1)) (quadrantRStageTime_mono w h (Nat.le_succ m)))
  apply transport ha (kmswMap (hatCodes w h) m).rot
    (kmswMap (hatCodes w h) (m + 1)).rot
    (kmswMap w (quadrantRStageTime w h (m + 1))).rot
    (q ∘ hatDartMap w h m) (hatDartMap w h (m + 1))
  · exact StageRotation.step_activation s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ m) (stageRot (hatCodes w h) m)
      (hatCodes w h m) hc e es he
  · intro d
    apply Prod.ext
    · exact Fin.ext (hatAllEdgeMap_extend w h m d.1.val (ha ▸ d.1.isLt))
    · rfl
  · exact whole

end DirectedDistances.KMSW
end
