module

public import DirectedDistances.KMSW.StageVertices
public import DirectedDistances.KMSW.StageOuterWordSucc
public import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Locally finite limiting KMSW rotations

The limiting permutations require finite incidence at every vertex. -/

public section
namespace DirectedDistances.KMSW

private def dartVal {k : ℕ} (d : StageDart k) : ℕ × Bool := (d.1.val, d.2)

private theorem dartVal_injective (k : ℕ) :
    Function.Injective (@dartVal k) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl

private theorem resize_val {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (e : ℕ) (he : e < k) (he' : e < l) (b : Bool) :
    dartVal (StageRotation.resize h σ (⟨e, he'⟩, b)) =
      dartVal (σ (⟨e, he⟩, b)) := by
  cases h
  rfl

private theorem unresize_old {k l r : ℕ} (h : l = k + r) (hm : k ≤ l)
    (σ : Equiv.Perm (StageDart k)) (τ : Equiv.Perm (StageDart l))
    (ρ : Equiv.Perm (StageDart (k + r)))
    (ht : StageRotation.resize h τ = ρ) (x : StageDart k)
    (hx : ρ (StageRotation.allocation k r (.inl x)) =
      StageRotation.allocation k r (.inl (σ x))) :
    τ (outerSucc_castDart hm x) = outerSucc_castDart hm (σ x) := by
  apply dartVal_injective
  have hv := congrArg (fun p => dartVal (p (StageRotation.allocation k r (.inl x)))) ht
  rw [hx] at hv
  rw [StageRotation.allocation_old] at hv
  rw [resize_val h τ x.1.val (by have := x.1.isLt; omega)] at hv
  exact hv

private theorem step_local (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hm : s.nextEdge ≤ (kmswStep s c).nextEdge)
    (hσ : ∀ x, stageEndpoint s (σ x) = stageEndpoint s x)
    (u : ℕ) (hnew : ∀ e, s.nextEdge ≤ e → e < (kmswStep s c).nextEdge →
      (kmswStep s c).west e ≠ u ∧ (kmswStep s c).east e ≠ u)
    (x : StageDart s.nextEdge) (hx : stageEndpoint s x = u) :
    StageRotation.step s ha hu σ c (outerSucc_castDart hm x) =
      outerSucc_castDart hm (σ x) := by
  have hσx : stageEndpoint s (σ x) = u := (hσ x).trans hx
  cases hc : kmswCodeStep c with
  | down =>
    cases hr : s.UR with
    | nil =>
      have hn := hnew s.nextEdge (le_refl _) (by
        simp [kmswStep, hc, kmswStepOfStep, hr, State.addEdge])
      have hA : σ x ≠ (⟨s.active, ha⟩, true) := by
        intro he
        rw [he] at hσx
        exact hn.1 (by simpa [kmswStep, hc, kmswStepOfStep, hr,
          State.addEdge, stageEndpoint] using hσx)
      apply unresize_old _ hm σ _ _ (StageRotation.step_pendant s ha hu σ c hc hr) x
      rw [StageRotation.pendant_old, ite_eq_right hA]
    | cons e es =>
      have hs : (kmswStep s c).nextEdge = s.nextEdge := by
        simp [kmswStep, hc, kmswStepOfStep, hr]
      have ht := StageRotation.step_activation s ha hu σ c hc e es hr
      apply unresize_old (r := 0) (hs.trans (Nat.add_zero _).symm) hm σ _
        (StageRotation.resize (Nat.add_zero _).symm σ) (by
          simpa only [StageRotation.resize] using ht) x
      rfl
  | left =>
    cases hl : s.UL.dropLast.reverse with
    | nil =>
      have hn0 := hnew s.nextEdge (le_refl _) (by
        simp [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
      have hn1 := hnew (s.nextEdge + 1) (by omega) (by
        simp [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
      have ha' : x ≠ (⟨s.active, ha⟩, false) := by
        intro he
        rw [he] at hx
        exact hn1.2 (by simpa [kmswStep, hc, kmswStepOfStep, hl,
          State.addEdge, stageEndpoint] using hx)
      have hA : σ x ≠ (⟨s.active, ha⟩, true) := by
        intro he
        rw [he] at hσx
        exact hn0.2 (by simpa [kmswStep, hc, kmswStepOfStep, hl,
          State.addEdge, stageEndpoint] using hσx)
      apply unresize_old _ hm σ _ _ (StageRotation.step_leftFresh s ha hu σ c hc hl) x
      rw [StageRotation.leftFresh_old, ite_eq_right ha', ite_eq_right hA]
    | cons e es =>
      have he := hu e (List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      have hn := hnew s.nextEdge (le_refl _) (by
        simp [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
      have he' : x ≠ (⟨e, he⟩, false) := by
        intro h
        rw [h] at hx
        exact hn.1 (by simpa [kmswStep, hc, kmswStepOfStep, hl,
          State.addEdge, stageEndpoint] using hx)
      have hA : σ x ≠ (⟨s.active, ha⟩, true) := by
        intro h
        rw [h] at hσx
        exact hn.2 (by simpa [kmswStep, hc, kmswStepOfStep, hl,
          State.addEdge, stageEndpoint] using hσx)
      apply unresize_old _ hm σ _ _
        (StageRotation.step_leftExisting s ha hu σ c hc e es hl) x
      rw [StageRotation.leftExisting_old, ite_eq_right he', ite_eq_right hA]
  | up =>
    have hn0 := hnew s.nextEdge (le_refl _) (by
      simp [kmswStep, hc, kmswStepOfStep, State.addEdge])
    have hn1 := hnew (s.nextEdge + 1) (by omega) (by
      simp [kmswStep, hc, kmswStepOfStep, State.addEdge])
    have ha' : x ≠ (⟨s.active, ha⟩, false) := by
      intro he
      rw [he] at hx
      exact hn0.1 (by simpa [kmswStep, hc, kmswStepOfStep,
        State.addEdge, stageEndpoint] using hx)
    have hA : σ x ≠ (⟨s.active, ha⟩, true) := by
      intro he
      rw [he] at hσx
      exact hn1.2 (by simpa [kmswStep, hc, kmswStepOfStep,
        State.addEdge, stageEndpoint] using hσx)
    apply unresize_old _ hm σ _ _ (StageRotation.step_up s ha hu σ c hc) x
    rw [StageRotation.up_old, ite_eq_right ha', ite_eq_right hA]

/-- A step changes rotation successors only at vertices receiving new edges -/
theorem stageRot_step_local (w : ℕ → Fin 3) (m u : ℕ)
    (hnew : ∀ e, (kmswStage w m).nextEdge ≤ e →
      e < (kmswStage w (m + 1)).nextEdge →
      (kmswStage w (m + 1)).west e ≠ u ∧ (kmswStage w (m + 1)).east e ≠ u)
    (x : StageDart (kmswStage w m).nextEdge)
    (hx : stageEndpoint (kmswStage w m) x = u) :
    stageRot w (m + 1) (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) x) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) (stageRot w m x) := by
  apply step_local _ _ _ _ _ _ _ u hnew x hx
  intro d
  exact ((stageRot_sameCycle_iff_endpoint_eq w m d (stageRot w m d)).1 ⟨1, rfl⟩).symm

/-- Every natural edge ID is allocated by its own index -/
theorem kmsw_edge_allocated_by_self (w : ℕ → Fin 3) (e : ℕ) :
    e < (kmswStage w e).nextEdge := by
  have := CutConverse.allocation_count w e
  omega

/-- Allocation sizes tend to infinity for every code walk -/
theorem kmsw_nextEdge_unbounded (w : ℕ → Fin 3) :
    ∀ K, ∀ n ≥ K, K < (kmswStage w n).nextEdge := by
  intro K n hn
  exact (kmsw_edge_allocated_by_self w K).trans_le (kmswStage_nextEdge_mono w hn)

/-- An activation run cannot continue forever: the finite upper-right list
loses one edge at each activation (`remark-kmsw-infinite`, -/
theorem kmsw_no_infinite_activations (w : ℕ → Fin 3) (N : ℕ) :
    ∃ m ≥ N, kmswCodeStep (w m) ≠ .down ∨ (kmswStage w m).UR = [] := by
  classical
  by_contra h
  have hlen (k : ℕ) :
      (kmswStage w (N + k)).UR.length + k = (kmswStage w N).UR.length := by
    induction k with
    | zero => simp only [Nat.add_zero]
    | succ k ih =>
      have hn : N ≤ N + k := by omega
      have hc : kmswCodeStep (w (N + k)) = .down := by
        by_contra hc
        exact h ⟨N + k, hn, Or.inl hc⟩
      cases hr : (kmswStage w (N + k)).UR with
      | nil => exact (h ⟨N + k, hn, Or.inr hr⟩).elim
      | cons e es =>
        have hs : (kmswStage w (N + k + 1)).UR = es := by
          simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr]
        rw [hr, List.length_cons] at ih
        rw [show N + (k + 1) = N + k + 1 by omega, hs]
        omega
  have := hlen ((kmswStage w N).UR.length + 1)
  omega

private def infEndpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem endpoint_eq_inf (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) x = infEndpoint w (dartVal x) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w x.1.isLt
  cases hb : x.2 <;> simp only [stageEndpoint, infEndpoint, dartVal, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

/-- A vertex is complete when all its incident geometric edge IDs have been -/
@[expose] def kmswVertexComplete (w : ℕ → Fin 3) (n u : ℕ) : Prop :=
  ∀ e, edgeWest w e = u ∨ edgeEast w e = u → e < (kmswStage w n).nextEdge

private theorem complete_mono (w : ℕ → Fin 3) {n m u : ℕ} (hnm : n ≤ m)
    (h : kmswVertexComplete w n u) : kmswVertexComplete w m u := by
  intro e he
  exact (h e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem finite_complete (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (u : ℕ) : ∃ N, kmswVertexComplete w N u := by
  obtain ⟨B, hB⟩ := (hfin u).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hmem : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)} := by
    refine ⟨e, kmsw_edge_allocated_by_self w e, ?_⟩
    exact he
  exact (hB hmem).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem complete_no_new (w : ℕ → Fin 3) {n u : ℕ}
    (h : kmswVertexComplete w n u) (e : ℕ) (he : (kmswStage w n).nextEdge ≤ e)
    (he' : e < (kmswStage w (n + 1)).nextEdge) :
    (kmswStage w (n + 1)).west e ≠ u ∧ (kmswStage w (n + 1)).east e ≠ u := by
  obtain ⟨hw, heast⟩ := edge_endpoints_eq w he'
  constructor
  · intro hu
    have := h e (Or.inl (hw.symm.trans hu))
    omega
  · intro hu
    have := h e (Or.inr (heast.symm.trans hu))
    omega

private theorem rot_cast_complete (w : ℕ → Fin 3) {N n : ℕ} (hn : N ≤ n)
    (x : StageDart (kmswStage w N).nextEdge)
    (h : kmswVertexComplete w N (stageEndpoint (kmswStage w N) x)) :
    stageRot w n (outerSucc_castDart (kmswStage_nextEdge_mono w hn) x) =
      outerSucc_castDart (kmswStage_nextEdge_mono w hn) (stageRot w N x) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hep : stageEndpoint (kmswStage w n)
        (outerSucc_castDart (kmswStage_nextEdge_mono w hn) x) =
        stageEndpoint (kmswStage w N) x := by
      rw [endpoint_eq_inf, endpoint_eq_inf]
      rfl
    have hs := stageRot_step_local w n _
      (complete_no_new w (complete_mono w hn h))
      (outerSucc_castDart (kmswStage_nextEdge_mono w hn) x) hep
    rw [ih] at hs
    exact hs

private theorem rot_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) (stageRot w n x) =
      stageEndpoint (kmswStage w n) x :=
  ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).1 ⟨1, rfl⟩).symm

private theorem symm_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((stageRot w n).symm x) =
      stageEndpoint (kmswStage w n) x := by
  have h := rot_endpoint w n ((stageRot w n).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private theorem symm_cast_complete (w : ℕ → Fin 3) {N n : ℕ} (hn : N ≤ n)
    (x : StageDart (kmswStage w N).nextEdge)
    (h : kmswVertexComplete w N (stageEndpoint (kmswStage w N) x)) :
    (stageRot w n).symm (outerSucc_castDart (kmswStage_nextEdge_mono w hn) x) =
      outerSucc_castDart (kmswStage_nextEdge_mono w hn) ((stageRot w N).symm x) := by
  apply (stageRot w n).injective
  rw [Equiv.apply_symm_apply, rot_cast_complete w hn _ (by
    rw [symm_endpoint]; exact h), Equiv.apply_symm_apply]

private def stageDir (w : ℕ → Fin 3) (inv : Bool) (n : ℕ) :
    Equiv.Perm (StageDart (kmswStage w n).nextEdge) :=
  if inv then (stageRot w n).symm else stageRot w n

private theorem dir_cast_complete (w : ℕ → Fin 3) (inv : Bool)
    {N n : ℕ} (hn : N ≤ n) (x : StageDart (kmswStage w N).nextEdge)
    (h : kmswVertexComplete w N (stageEndpoint (kmswStage w N) x)) :
    stageDir w inv n (outerSucc_castDart (kmswStage_nextEdge_mono w hn) x) =
      outerSucc_castDart (kmswStage_nextEdge_mono w hn) (stageDir w inv N x) := by
  cases inv
  · exact rot_cast_complete w hn x h
  · exact symm_cast_complete w hn x h

private theorem dir_endpoint (w : ℕ → Fin 3) (inv : Bool) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) (stageDir w inv n x) =
      stageEndpoint (kmswStage w n) x := by
  cases inv
  · exact rot_endpoint w n x
  · exact symm_endpoint w n x

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin

private theorem complete_stage_exists (d : ℕ × Bool) :
    ∃ N, d.1 < (kmswStage w N).nextEdge ∧
      kmswVertexComplete w N (infEndpoint w d) := by
  obtain ⟨N, hN⟩ := finite_complete w hfin (infEndpoint w d)
  exact ⟨max N d.1, kmsw_nextEdge_unbounded w d.1 _ (le_max_right _ _),
    complete_mono w (le_max_left _ _) hN⟩

private noncomputable def completeStage (d : ℕ × Bool) : ℕ :=
  (complete_stage_exists w hfin d).choose

private theorem completeStage_spec (d : ℕ × Bool) :
    d.1 < (kmswStage w (completeStage w hfin d)).nextEdge ∧
      kmswVertexComplete w (completeStage w hfin d) (infEndpoint w d) :=
  (complete_stage_exists w hfin d).choose_spec

private noncomputable def rotValue (inv : Bool) (d : ℕ × Bool) : ℕ × Bool :=
  dartVal (stageDir w inv (completeStage w hfin d)
    (⟨d.1, (completeStage_spec w hfin d).1⟩, d.2))

private theorem rotValue_eq_stage (inv : Bool) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) x)) :
    rotValue w hfin inv (dartVal x) = dartVal (stageDir w inv n x) := by
  let N := completeStage w hfin (dartVal x)
  let y : StageDart (kmswStage w N).nextEdge :=
    (⟨x.1.val, (completeStage_spec w hfin (dartVal x)).1⟩, x.2)
  have hy : kmswVertexComplete w N (stageEndpoint (kmswStage w N) y) := by
    rw [endpoint_eq_inf]
    exact (completeStage_spec w hfin (dartVal x)).2
  have a := congrArg dartVal (dir_cast_complete w inv (le_max_left n N) x hc)
  have b := congrArg dartVal (dir_cast_complete w inv (le_max_right n N) y hy)
  exact b.symm.trans a

private theorem rotValue_cancel (inv : Bool) (d : ℕ × Bool) :
    rotValue w hfin (!inv) (rotValue w hfin inv d) = d := by
  let N := completeStage w hfin d
  let x : StageDart (kmswStage w N).nextEdge :=
    (⟨d.1, (completeStage_spec w hfin d).1⟩, d.2)
  have hc : kmswVertexComplete w N (stageEndpoint (kmswStage w N) x) := by
    rw [endpoint_eq_inf]
    exact (completeStage_spec w hfin d).2
  change rotValue w hfin (!inv) (dartVal (stageDir w inv N x)) = d
  rw [rotValue_eq_stage w hfin (!inv) N _ (by rw [dir_endpoint]; exact hc)]
  cases inv <;> simp only [Bool.not_false, Bool.not_true, stageDir,
    Bool.false_eq_true, ↓reduceIte, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  all_goals rfl

/-- Under finite incidence every allocated dart has an eventually constant -/
theorem stageRot_eventually_constant (d : ℕ × Bool) :
    ∃ N r, ∀ n ≥ N, ∃ hd : d.1 < (kmswStage w n).nextEdge,
      ((stageRot w n (⟨d.1, hd⟩, d.2)).1.val,
        (stageRot w n (⟨d.1, hd⟩, d.2)).2) = r := by
  refine ⟨completeStage w hfin d, rotValue w hfin false d, ?_⟩
  intro n hn
  have hd := (completeStage_spec w hfin d).1.trans_le (kmswStage_nextEdge_mono w hn)
  refine ⟨hd, ?_⟩
  exact (rotValue_eq_stage w hfin false n (⟨d.1, hd⟩, d.2) (by
    rw [endpoint_eq_inf]
    exact complete_mono w hn (completeStage_spec w hfin d).2)).symm

/-- Existence of a permutation and its inverse agreeing with every complete
vertex of every stage (`remark-kmsw-infinite`, -/
theorem kmswInfRot_exists :
    ∃ σ : Equiv.Perm (ℕ × Bool),
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ (x.1.val, x.2) = ((stageRot w n x).1.val, (stageRot w n x).2)) ∧
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ.symm (x.1.val, x.2) =
          (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) := by
  refine ⟨{ toFun := rotValue w hfin false
            invFun := rotValue w hfin true
            left_inv := rotValue_cancel w hfin false
            right_inv := rotValue_cancel w hfin true }, ?_, ?_⟩
  · exact rotValue_eq_stage w hfin false
  · exact rotValue_eq_stage w hfin true

/-- Uniqueness: a permutation agreeing with the stage rotations at every complete
vertex of every stage is unique, so the limiting rotation is determined by this
characterization before any choice (`remark-kmsw-infinite`, -/
theorem kmswInfRot_existsUnique :
    ∃! σ : Equiv.Perm (ℕ × Bool),
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ (x.1.val, x.2) = ((stageRot w n x).1.val, (stageRot w n x).2)) ∧
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ.symm (x.1.val, x.2) =
          (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) := by
  obtain ⟨σ, hσ⟩ := kmswInfRot_exists w hfin
  refine ⟨σ, hσ, fun τ hτ => Equiv.ext fun d => ?_⟩
  have hspec := completeStage_spec w hfin d
  have hc : kmswVertexComplete w (completeStage w hfin d)
      (stageEndpoint (kmswStage w (completeStage w hfin d)) (⟨d.1, hspec.1⟩, d.2)) := by
    rw [endpoint_eq_inf]
    exact hspec.2
  exact (hτ.1 _ (⟨d.1, hspec.1⟩, d.2) hc).trans (hσ.1 _ (⟨d.1, hspec.1⟩, d.2) hc).symm

/-- The limiting vertex rotation, defined only with finite incidence, as the
unique permutation of `kmswInfRot_existsUnique` (`remark-kmsw-infinite`,
rotation. -/
@[expose] noncomputable def kmswInfRot : Equiv.Perm (ℕ × Bool) :=
  (kmswInfRot_existsUnique w hfin).exists.choose

/-- A complete vertex already has its limiting rotation at the given stage -/
theorem kmswInfRot_eq_stage (n : ℕ) (x : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) x)) :
    kmswInfRot w hfin (x.1.val, x.2) =
      ((stageRot w n x).1.val, (stageRot w n x).2) :=
  (kmswInfRot_existsUnique w hfin).exists.choose_spec.1 n x hc

/-- At a complete vertex the inverse limiting rotation also agrees with the -/
theorem kmswInfRot_symm_eq_stage (n : ℕ) (x : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) x)) :
    (kmswInfRot w hfin).symm (x.1.val, x.2) =
      (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2) :=
  (kmswInfRot_existsUnique w hfin).exists.choose_spec.2 n x hc

/-- Every forward rotation entry is eventually its limiting value -/
theorem kmswInfRot_eventually_eq_stage (d : ℕ × Bool) :
    ∃ N, ∀ n ≥ N, ∃ hd : d.1 < (kmswStage w n).nextEdge,
      kmswInfRot w hfin d =
        ((stageRot w n (⟨d.1, hd⟩, d.2)).1.val,
          (stageRot w n (⟨d.1, hd⟩, d.2)).2) := by
  refine ⟨completeStage w hfin d, fun n hn => ?_⟩
  have hd := (completeStage_spec w hfin d).1.trans_le (kmswStage_nextEdge_mono w hn)
  refine ⟨hd, kmswInfRot_eq_stage w hfin n (⟨d.1, hd⟩, d.2) ?_⟩
  rw [endpoint_eq_inf]
  exact complete_mono w hn (completeStage_spec w hfin d).2

/-- Infinite face successor: inverse vertex rotation after swapping the two
geometric darts of an edge (`remark-kmsw-infinite`, -/
@[expose] noncomputable def kmswInfFaceSucc : Equiv.Perm (ℕ × Bool) :=
  (kmswInfRot w hfin).symm *
    { toFun := fun d => (d.1, !d.2)
      invFun := fun d => (d.1, !d.2)
      left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
      right_inv := by rintro ⟨e, b⟩; cases b <;> rfl }

/-- Face successor agrees as soon as the opposite dart's vertex is complete -/
theorem kmswInfFaceSucc_eq_stage (n : ℕ) (x : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n
      (stageEndpoint (kmswStage w n) (edgeFlip _ x))) :
    kmswInfFaceSucc w hfin (x.1.val, x.2) =
      (((kmswMap w n).faceSucc x).1.val, ((kmswMap w n).faceSucc x).2) := by
  exact kmswInfRot_symm_eq_stage w hfin n (edgeFlip _ x) hc

/-- Each inverse rotation entry is eventually its limiting value -/
theorem kmswInfRot_symm_eventually_eq_stage (d : ℕ × Bool) :
    ∃ N, ∀ n ≥ N, ∃ hd : d.1 < (kmswStage w n).nextEdge,
      (kmswInfRot w hfin).symm d =
        (((stageRot w n).symm (⟨d.1, hd⟩, d.2)).1.val,
          ((stageRot w n).symm (⟨d.1, hd⟩, d.2)).2) := by
  refine ⟨completeStage w hfin d, fun n hn => ?_⟩
  have hd := (completeStage_spec w hfin d).1.trans_le (kmswStage_nextEdge_mono w hn)
  refine ⟨hd, kmswInfRot_symm_eq_stage w hfin n (⟨d.1, hd⟩, d.2) ?_⟩
  rw [endpoint_eq_inf]
  exact complete_mono w hn (completeStage_spec w hfin d).2

/-- Each infinite face successor is eventually the finite-stage face successor -/
theorem kmswInfFaceSucc_eventually_eq_stage (d : ℕ × Bool) :
    ∃ N, ∀ n ≥ N, ∃ hd : d.1 < (kmswStage w n).nextEdge,
      kmswInfFaceSucc w hfin d =
        (((kmswMap w n).faceSucc (⟨d.1, hd⟩, d.2)).1.val,
          ((kmswMap w n).faceSucc (⟨d.1, hd⟩, d.2)).2) := by
  let f : ℕ × Bool := (d.1, !d.2)
  refine ⟨completeStage w hfin f, fun n hn => ?_⟩
  have hd : d.1 < (kmswStage w n).nextEdge :=
    (completeStage_spec w hfin f).1.trans_le (kmswStage_nextEdge_mono w hn)
  refine ⟨hd, kmswInfFaceSucc_eq_stage w hfin n (⟨d.1, hd⟩, d.2) ?_⟩
  rw [endpoint_eq_inf]
  exact complete_mono w hn (completeStage_spec w hfin f).2

end DirectedDistances.KMSW
