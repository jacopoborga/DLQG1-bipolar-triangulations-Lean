module

public import DirectedDistances.KMSW.StageRotation
import DirectedDistances.PlanarMap.PermutationSplice
import DirectedDistances.KMSW.BoundaryRecordsUL

/-! # Vertices of the finite KMSW rotations

Geometric endpoint identification for `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private theorem cycle_lift {D E : Type*} [Finite D]
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (i : D → E)
    (hs : ∀ d, ρ.SameCycle (i d) (i (σ d))) {d d' : D}
    (h : σ.SameCycle d d') : ρ.SameCycle (i d) (i d') := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    simpa only [pow_succ', Equiv.Perm.mul_apply] using ih.trans (hs ((σ ^ n) d))

private theorem cycle_label {D : Type*} [Finite D] (σ : Equiv.Perm D)
    (E : D → ℕ) (hs : ∀ d, E (σ d) = E d) {d d' : D}
    (h : σ.SameCycle d d') : E d = E d' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [pow_succ', Equiv.Perm.mul_apply, hs] using ih

private theorem extension_identification {D E : Type*} [Finite D] [Finite E]
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (i : D → E)
    (p : D → ℕ) (q : E → ℕ) (V : ℕ)
    (hi : ∀ d d', σ.SameCycle d d' ↔ p d = p d')
    (hb : ∀ d, p d < V)
    (he : ∀ d, q (i d) = p d)
    (hs : ∀ d, ρ.SameCycle (i d) (i (σ d)))
    (hp : ∀ d, q (ρ d) = q d)
    (hc : ∀ d, (∃ a, ρ.SameCycle d (i a)) ∨
      (q d = V ∧ ∀ d', q d' = V → ρ.SameCycle d d')) :
    ∀ d d', ρ.SameCycle d d' ↔ q d = q d' := by
  intro d d'
  constructor
  · exact cycle_label ρ q hp
  · intro h
    rcases hc d with ⟨a, ha⟩ | ⟨hv, hf⟩
    · rcases hc d' with ⟨b, hb'⟩ | ⟨hv', _⟩
      · have hab : p a = p b := by
          rw [← he a, ← he b, ← cycle_label ρ q hp ha,
            ← cycle_label ρ q hp hb']
          exact h
        exact ha.trans ((cycle_lift σ ρ i hs ((hi a b).2 hab)).trans hb'.symm)
      · have hbad : p a = V :=
          (he a).symm.trans ((cycle_label ρ q hp ha).symm.trans (h.trans hv'))
        have := hb a
        omega
    · exact hf d' (h.symm.trans hv)

private theorem cycle_step {D : Type*} (σ : Equiv.Perm D) (d : D) :
    σ.SameCycle d (σ d) := ⟨1, rfl⟩

private theorem cycle_transport {D E : Type*} [Finite D] [Finite E]
    (e : D ≃ E) (σ : Equiv.Perm D) (d d' : D) :
    (e.permCongr σ).SameCycle (e d) (e d') ↔ σ.SameCycle d d' := by
  constructor
  · intro h
    have hh := cycle_lift (e.permCongr σ) σ e.symm (fun x => by
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
        cycle_step σ (e.symm x)) h
    simpa only [Equiv.symm_apply_apply] using hh
  · exact cycle_lift σ (e.permCongr σ) e (fun x => by
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
        cycle_step (e.permCongr σ) (e x))

private theorem pairSplice_paths {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y) :
    (∀ d, (StageRotation.pairSplice σ τ a b x y).SameCycle
      (.inl d) (.inl (σ d))) ∧
    (StageRotation.pairSplice σ τ a b x y).SameCycle (.inr x) (.inl a) ∧
    (StageRotation.pairSplice σ τ a b x y).SameCycle (.inr y) (.inl b) := by
  let ρ := StageRotation.pairSplice σ τ a b x y
  have ha : ρ (.inl a) = .inr x := by
    simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
      Equiv.swap_apply_def, hx, hxy]
  have hy' : ρ (.inr y) = .inl b := by
    simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
      Equiv.swap_apply_def, hy, hxy.symm]
  have hx' : ρ (.inr x) = if σ a = b then .inr y else .inl (σ a) := by
    by_cases h : σ a = b <;>
      simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
        Equiv.swap_apply_def, h]
  have hold (d : D) : ρ (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
    by_cases h : d = a
    · subst d; simpa only [↓reduceIte] using ha
    · by_cases h' : σ d = b <;>
        simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
          Equiv.swap_apply_def, h, h']
  have hya : ρ.SameCycle (.inr y) (.inl b) := by
    simpa only [hy'] using cycle_step ρ (.inr y)
  refine ⟨?_, ?_, hya⟩
  · intro d
    have hd := cycle_step ρ (.inl d)
    rw [hold] at hd
    by_cases h : d = a
    · subst d
      simp only [↓reduceIte] at hd
      have hh := cycle_step ρ (.inr x)
      rw [hx'] at hh
      by_cases h' : σ a = b
      · simp only [h', ↓reduceIte] at hh
        rw [h']
        exact hd.trans (hh.trans hya)
      · simp only [h', ↓reduceIte] at hh
        exact hd.trans hh
    · simp only [h, ↓reduceIte] at hd
      by_cases h' : σ d = b
      · simp only [h', ↓reduceIte] at hd
        rw [h']
        exact hd.trans hya
      · simpa only [h', ↓reduceIte] using hd
  · have hh : ρ.SameCycle (.inl a) (.inr x) := by
      simpa only [ha] using cycle_step ρ (.inl a)
    exact hh.symm

private theorem pairSplice_identification {D F : Type*} [Fintype D] [Fintype F]
    [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (p : D → ℕ) (q : D ⊕ F → ℕ) (V : ℕ)
    (hi : ∀ d d', σ.SameCycle d d' ↔ p d = p d')
    (hb : ∀ d, p d < V)
    (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y)
    (hold : ∀ d, q (.inl d) = p d)
    (hqx : q (.inr x) = p a) (hqy : q (.inr y) = p b)
    (hqrest : ∀ z, z ≠ x → z ≠ y → q (.inr z) = V)
    (hrest : ∀ z z', z ≠ x → z ≠ y → z' ≠ x → z' ≠ y →
      (StageRotation.pairSplice σ τ a b x y).SameCycle (.inr z) (.inr z')) :
    ∀ d d', (StageRotation.pairSplice σ τ a b x y).SameCycle d d' ↔ q d = q d' := by
  let ρ := StageRotation.pairSplice σ τ a b x y
  have hσ (d : D) : p (σ d) = p d := ((hi d (σ d)).1 (cycle_step σ d)).symm
  obtain ⟨hpaths, hxa, hyb⟩ := pairSplice_paths σ τ a b x y hx hy hxy
  have hp : ∀ d, q (ρ d) = q d := by
    intro d
    cases d with
    | inl d =>
      by_cases hda : d = a
      · subst d
        have hv : ρ (.inl a) = .inr x := by
          simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
            Equiv.swap_apply_def, hx, hxy]
        rw [hv, hqx, hold]
      · by_cases hdb : σ d = b
        · have hv : ρ (.inl d) = .inr y := by
            simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
              Equiv.swap_apply_def, hda, hdb]
          rw [hv, hqy, hold, ← hdb, hσ]
        · have hv : ρ (.inl d) = .inl (σ d) := by
            simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
              Equiv.swap_apply_def, hda, hdb]
          rw [hv, hold, hold, hσ]
    | inr z =>
      by_cases hzx : z = x
      · subst z
        have hv : ρ (.inr x) = if σ a = b then .inr y else .inl (σ a) := by
          by_cases hab : σ a = b <;>
            simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
              Equiv.swap_apply_def, hab]
        rw [hv, hqx]
        split
        next hab => rw [hqy, ← hab, hσ]
        next => rw [hold, hσ]
      · by_cases hzy : z = y
        · subst z
          have hv : ρ (.inr y) = .inl b := by
            simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
              Equiv.swap_apply_def, hy, hxy.symm]
          rw [hv, hold, hqy]
        · have hτx : τ z ≠ x := fun h => hzx (τ.injective (h.trans hx.symm))
          have hτy : τ z ≠ y := fun h => hzy (τ.injective (h.trans hy.symm))
          have hv : ρ (.inr z) = .inr (τ z) := by
            simp [ρ, StageRotation.pairSplice, insertAfter, insertBefore,
              Equiv.swap_apply_def, hzx, hτy]
          rw [hv, hqrest _ hτx hτy, hqrest _ hzx hzy]
  apply extension_identification σ ρ Sum.inl p q V hi hb hold hpaths hp
  intro d
  cases d with
  | inl d => exact Or.inl ⟨d, Equiv.Perm.SameCycle.rfl⟩
  | inr z =>
    by_cases hzx : z = x
    · subst z; exact Or.inl ⟨a, hxa⟩
    · by_cases hzy : z = y
      · subst z; exact Or.inl ⟨b, hyb⟩
      · refine Or.inr ⟨hqrest z hzx hzy, ?_⟩
        intro d' hd'
        cases d' with
        | inl d' =>
          have hh : p d' = V := (hold d').symm.trans hd'
          have := hb d'
          omega
        | inr z' =>
          by_cases hzx' : z' = x
          · subst z'
            have hh : p a = V := hqx.symm.trans hd'
            have := hb a
            omega
          · by_cases hzy' : z' = y
            · subst z'
              have hh : p b = V := hqy.symm.trans hd'
              have := hb b
              omega
            · exact hrest z z' hzx hzy hzx' hzy'

private theorem addEdge_bounds (s : State) (V a b : ℕ) (p : Bool)
    (h : ∀ e < s.nextEdge, s.west e < V ∧ s.east e < V)
    (ha : a < V) (hb : b < V) :
    ∀ e < (s.addEdge a b p).nextEdge,
      (s.addEdge a b p).west e < V ∧ (s.addEdge a b p).east e < V := by
  intro e he
  by_cases hn : e = s.nextEdge
  · subst e
    simpa only [State.addEdge, ↓reduceIte] using And.intro ha hb
  · have he' : e < s.nextEdge := by change e < s.nextEdge + 1 at he; omega
    simpa only [State.addEdge, hn, ↓reduceIte] using h e he'

private theorem step_bounds (s : State) (c : Fin 3)
    (ha : s.active < s.nextEdge) (hu : ∀ e ∈ s.UL, e < s.nextEdge)
    (h : ∀ e < s.nextEdge, s.west e < s.nextVertex ∧ s.east e < s.nextVertex) :
    ∀ e < (kmswStep s c).nextEdge,
      (kmswStep s c).west e < (kmswStep s c).nextVertex ∧
      (kmswStep s c).east e < (kmswStep s c).nextVertex := by
  have hactive := h s.active ha
  have hlarge : ∀ e < s.nextEdge,
      s.west e < s.nextVertex + 1 ∧ s.east e < s.nextVertex + 1 := by
    intro e he
    have := h e he
    omega
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    dsimp only [kmswStepOfStep]
    split
    · exact h
    · exact addEdge_bounds s (s.nextVertex + 1) (s.east s.active) s.nextVertex true
        hlarge (by omega) (by omega)
  | left =>
    dsimp only [kmswStepOfStep]
    split
    next e es hl =>
      have he := hu e (List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      exact addEdge_bounds s s.nextVertex (s.west e) (s.east s.active) true
        h (h e he).1 hactive.2
    next hl =>
      have ht := addEdge_bounds s (s.nextVertex + 1) s.nextVertex
        (s.east s.active) true hlarge (by omega) (by omega)
      exact addEdge_bounds _ (s.nextVertex + 1) s.nextVertex (s.west s.active) false
        ht (by omega) (by omega)
  | up =>
    have ht := addEdge_bounds s (s.nextVertex + 1) (s.west s.active)
      s.nextVertex true hlarge (by omega) (by omega)
    exact addEdge_bounds _ (s.nextVertex + 1) s.nextVertex (s.east s.active) false
      ht (by omega) (by omega)

/-- Every geometric endpoint is an allocated vertex ID (`def-kmsw`, -/
theorem stageEndpoint_lt_nextVertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d < (kmswStage w n).nextVertex := by
  have h : ∀ n e, e < (kmswStage w n).nextEdge →
      (kmswStage w n).west e < (kmswStage w n).nextVertex ∧
      (kmswStage w n).east e < (kmswStage w n).nextVertex := by
    intro n
    induction n with
    | zero => intro e he; change 0 < 2 ∧ 1 < 2; decide
    | succ n ih =>
      exact step_bounds _ _ (act_lt_nextEdge w (le_refl n))
        (stageRotation_UL_bound w n) ih
  have hd := h n d.1.val d.1.isLt
  cases d with
  | mk e b =>
    cases b
    · exact hd.1
    · exact hd.2

private theorem leftExisting_vertices (s : State) (σ : Equiv.Perm (StageDart s.nextEdge))
    (e A : StageDart s.nextEdge)
    (hi : ∀ d d', σ.SameCycle d d' ↔ stageEndpoint s d = stageEndpoint s d')
    (hb : ∀ d, stageEndpoint s d < s.nextVertex) :
    ∀ d d', (StageRotation.leftExisting s.nextEdge σ e A).SameCycle d d' ↔
      stageEndpoint (s.addEdge (stageEndpoint s e) (stageEndpoint s A) true) d =
      stageEndpoint (s.addEdge (stageEndpoint s e) (stageEndpoint s A) true) d' := by
  let t := s.addEdge (stageEndpoint s e) (stageEndpoint s A) true
  let q := fun d => stageEndpoint t (StageRotation.allocation s.nextEdge 1 d)
  have hh := pairSplice_identification σ (Equiv.refl (StageDart 1)) e A
    (0, false) (0, true) (stageEndpoint s) q s.nextVertex hi hb rfl rfl (by decide)
  have hqold : ∀ d, q (.inl d) = stageEndpoint s d := by
    rintro ⟨i, b⟩
    have hn : i.val ≠ s.nextEdge := by omega
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge, hn]
  have hqx : q (.inr (0, false)) = stageEndpoint s e := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqy : q (.inr (0, true)) = stageEndpoint s A := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hrest : ∀ z : StageDart 1, z ≠ (0, false) → z ≠ (0, true) → False := by
    rintro ⟨i, b⟩ hx hy
    have : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    cases b
    · exact hx rfl
    · exact hy rfl
  have hc := hh hqold hqx hqy (fun z hx hy => (hrest z hx hy).elim)
    (fun z z' hx hy _ _ => (hrest z hx hy).elim)
  intro d d'
  obtain ⟨a, rfl⟩ := (StageRotation.allocation s.nextEdge 1).surjective d
  obtain ⟨b, rfl⟩ := (StageRotation.allocation s.nextEdge 1).surjective d'
  exact (cycle_transport (StageRotation.allocation s.nextEdge 1) _ a b).trans (hc a b)

private theorem leftFresh_vertices (s : State) (σ : Equiv.Perm (StageDart s.nextEdge))
    (a A : StageDart s.nextEdge)
    (hi : ∀ d d', σ.SameCycle d d' ↔ stageEndpoint s d = stageEndpoint s d')
    (hb : ∀ d, stageEndpoint s d < s.nextVertex) :
    ∀ d d', (StageRotation.leftFresh s.nextEdge σ a A).SameCycle d d' ↔
      stageEndpoint ((s.addEdge s.nextVertex (stageEndpoint s A) true).addEdge
        s.nextVertex (stageEndpoint s a) false) d =
      stageEndpoint ((s.addEdge s.nextVertex (stageEndpoint s A) true).addEdge
        s.nextVertex (stageEndpoint s a) false) d' := by
  let t := (s.addEdge s.nextVertex (stageEndpoint s A) true).addEdge
    s.nextVertex (stageEndpoint s a) false
  let q := fun d => stageEndpoint t (StageRotation.allocation s.nextEdge 2 d)
  have hh := pairSplice_identification σ
    (Equiv.swap (0, false) (1, false) : Equiv.Perm (StageDart 2)) a A
    (1, true) (0, true) (stageEndpoint s) q s.nextVertex hi hb
    (by decide) (by decide) (by decide)
  have hqold : ∀ d, q (.inl d) = stageEndpoint s d := by
    rintro ⟨i, b⟩
    have hn : i.val ≠ s.nextEdge := by omega
    have hn' : i.val ≠ s.nextEdge + 1 := by omega
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge, hn, hn']
  have hqx : q (.inr (1, true)) = stageEndpoint s a := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqy : q (.inr (0, true)) = stageEndpoint s A := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqrest : ∀ z : StageDart 2, z ≠ (1, true) → z ≠ (0, true) →
      q (.inr z) = s.nextVertex := by
    rintro ⟨i, b⟩ hx hy
    fin_cases i <;> cases b
    · simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
    · exact (hy rfl).elim
    · simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
    · exact (hx rfl).elim
  have hrest : ∀ z z' : StageDart 2,
      z ≠ (1, true) → z ≠ (0, true) → z' ≠ (1, true) → z' ≠ (0, true) →
      (StageRotation.pairSplice σ
        (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true)).SameCycle
        (.inr z) (.inr z') := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hx hy hx' hy'
    fin_cases i <;> fin_cases j <;> cases b <;> cases c
    all_goals first
    | exact (hx rfl).elim
    | exact (hy rfl).elim
    | exact (hx' rfl).elim
    | exact (hy' rfl).elim
    | exact Equiv.Perm.SameCycle.rfl
    | refine ⟨1, ?_⟩
      simp [StageRotation.pairSplice, insertAfter, insertBefore, Equiv.swap_apply_def]
  have hc := hh hqold hqx hqy hqrest hrest
  intro d d'
  obtain ⟨u, rfl⟩ := (StageRotation.allocation s.nextEdge 2).surjective d
  obtain ⟨v, rfl⟩ := (StageRotation.allocation s.nextEdge 2).surjective d'
  exact (cycle_transport (StageRotation.allocation s.nextEdge 2) _ u v).trans (hc u v)

private theorem up_vertices (s : State) (σ : Equiv.Perm (StageDart s.nextEdge))
    (a A : StageDart s.nextEdge)
    (hi : ∀ d d', σ.SameCycle d d' ↔ stageEndpoint s d = stageEndpoint s d')
    (hb : ∀ d, stageEndpoint s d < s.nextVertex) :
    ∀ d d', (StageRotation.up s.nextEdge σ a A).SameCycle d d' ↔
      stageEndpoint ((s.addEdge (stageEndpoint s a) s.nextVertex true).addEdge
        s.nextVertex (stageEndpoint s A) false) d =
      stageEndpoint ((s.addEdge (stageEndpoint s a) s.nextVertex true).addEdge
        s.nextVertex (stageEndpoint s A) false) d' := by
  let t := (s.addEdge (stageEndpoint s a) s.nextVertex true).addEdge
    s.nextVertex (stageEndpoint s A) false
  let q := fun d => stageEndpoint t (StageRotation.allocation s.nextEdge 2 d)
  have hh := pairSplice_identification σ
    (Equiv.swap (0, true) (1, false) : Equiv.Perm (StageDart 2)) a A
    (0, false) (1, true) (stageEndpoint s) q s.nextVertex hi hb
    (by decide) (by decide) (by decide)
  have hqold : ∀ d, q (.inl d) = stageEndpoint s d := by
    rintro ⟨i, b⟩
    have hn : i.val ≠ s.nextEdge := by omega
    have hn' : i.val ≠ s.nextEdge + 1 := by omega
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge, hn, hn']
  have hqx : q (.inr (0, false)) = stageEndpoint s a := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqy : q (.inr (1, true)) = stageEndpoint s A := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqrest : ∀ z : StageDart 2, z ≠ (0, false) → z ≠ (1, true) →
      q (.inr z) = s.nextVertex := by
    rintro ⟨i, b⟩ hx hy
    fin_cases i <;> cases b
    · exact (hx rfl).elim
    · simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
    · simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
    · exact (hy rfl).elim
  have hrest : ∀ z z' : StageDart 2,
      z ≠ (0, false) → z ≠ (1, true) → z' ≠ (0, false) → z' ≠ (1, true) →
      (StageRotation.pairSplice σ
        (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true)).SameCycle
        (.inr z) (.inr z') := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hx hy hx' hy'
    fin_cases i <;> fin_cases j <;> cases b <;> cases c
    all_goals first
    | exact (hx rfl).elim
    | exact (hy rfl).elim
    | exact (hx' rfl).elim
    | exact (hy' rfl).elim
    | exact Equiv.Perm.SameCycle.rfl
    | refine ⟨1, ?_⟩
      simp [StageRotation.pairSplice, insertAfter, insertBefore, Equiv.swap_apply_def]
  have hc := hh hqold hqx hqy hqrest hrest
  intro d d'
  obtain ⟨u, rfl⟩ := (StageRotation.allocation s.nextEdge 2).surjective d
  obtain ⟨v, rfl⟩ := (StageRotation.allocation s.nextEdge 2).surjective d'
  exact (cycle_transport (StageRotation.allocation s.nextEdge 2) _ u v).trans (hc u v)

private theorem pendant_vertices (s : State) (σ : Equiv.Perm (StageDart s.nextEdge))
    (A : StageDart s.nextEdge)
    (hi : ∀ d d', σ.SameCycle d d' ↔ stageEndpoint s d = stageEndpoint s d')
    (hb : ∀ d, stageEndpoint s d < s.nextVertex) :
    ∀ d d', (StageRotation.pendant s.nextEdge σ A).SameCycle d d' ↔
      stageEndpoint (s.addEdge (stageEndpoint s A) s.nextVertex true) d =
      stageEndpoint (s.addEdge (stageEndpoint s A) s.nextVertex true) d' := by
  let t := s.addEdge (stageEndpoint s A) s.nextVertex true
  let q := fun d => stageEndpoint t (StageRotation.allocation s.nextEdge 1 d)
  let ρ := insertBefore (Equiv.sumCongr σ (Equiv.refl (StageDart 1)))
    (.inl A) (.inr (0, false))
  have hqold : ∀ d, q (.inl d) = stageEndpoint s d := by
    rintro ⟨i, b⟩
    have hn : i.val ≠ s.nextEdge := by omega
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge, hn]
  have hqx : q (.inr (0, false)) = stageEndpoint s A := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hqy : q (.inr (0, true)) = s.nextVertex := by
    simp [q, t, stageEndpoint, StageRotation.allocation, State.addEdge]
  have hx : ρ (.inr (0, false)) = .inl A := by
    simp [ρ, insertBefore]
  have hy : ρ (.inr (0, true)) = .inr (0, true) := by
    simp [ρ, insertBefore, Equiv.swap_apply_def]
  have hold (d : StageDart s.nextEdge) : ρ (.inl d) =
      if σ d = A then .inr (0, false) else .inl (σ d) := by
    by_cases h : σ d = A <;> simp [ρ, insertBefore, Equiv.swap_apply_def, h]
  have hσ (d) : stageEndpoint s (σ d) = stageEndpoint s d :=
    ((hi d (σ d)).1 (cycle_step σ d)).symm
  have hs : ∀ d, ρ.SameCycle (.inl d) (.inl (σ d)) := by
    intro d
    have hd := cycle_step ρ (.inl d)
    rw [hold] at hd
    by_cases h : σ d = A
    · simp only [h, ↓reduceIte] at hd
      rw [h]
      exact hd.trans (by simpa only [hx] using cycle_step ρ (.inr (0, false)))
    · simpa only [h, ↓reduceIte] using hd
  have hp : ∀ d, q (ρ d) = q d := by
    intro d
    cases d with
    | inl d =>
      rw [hold]
      split
      next h => rw [hqx, hqold, ← h, hσ]
      next => rw [hqold, hqold, hσ]
    | inr z =>
      obtain ⟨i, b⟩ := z
      have : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      cases b
      · rw [hx, hqold, hqx]
      · rw [hy]
  have hc : ∀ d, (∃ a, ρ.SameCycle d (.inl a)) ∨
      (q d = s.nextVertex ∧ ∀ d', q d' = s.nextVertex → ρ.SameCycle d d') := by
    intro d
    cases d with
    | inl d => exact Or.inl ⟨d, Equiv.Perm.SameCycle.rfl⟩
    | inr z =>
      obtain ⟨i, b⟩ := z
      have : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      cases b
      · exact Or.inl ⟨A, by simpa only [hx] using cycle_step ρ (.inr (0, false))⟩
      · refine Or.inr ⟨hqy, ?_⟩
        intro d' hd'
        cases d' with
        | inl d' =>
          have hbad := (hqold d').symm.trans hd'
          have := hb d'
          omega
        | inr z' =>
          obtain ⟨j, c⟩ := z'
          have : j = 0 := Fin.ext (by have := j.isLt; omega)
          subst j
          cases c
          · have hbad := hqx.symm.trans hd'
            have := hb A
            omega
          · exact Equiv.Perm.SameCycle.rfl
  have hh := extension_identification σ ρ Sum.inl (stageEndpoint s) q s.nextVertex
    hi hb hqold hs hp hc
  intro d d'
  obtain ⟨u, rfl⟩ := (StageRotation.allocation s.nextEdge 1).surjective d
  obtain ⟨v, rfl⟩ := (StageRotation.allocation s.nextEdge 1).surjective d'
  exact (cycle_transport (StageRotation.allocation s.nextEdge 1) ρ u v).trans (hh u v)

private def dartCast {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l := by
  cases h
  exact Equiv.refl _

private theorem dartCast_val {k l : ℕ} (h : k = l) (d : StageDart k) :
    (dartCast h d).1.val = d.1.val := by cases h; rfl

private theorem dartCast_bool {k l : ℕ} (h : k = l) (d : StageDart k) :
    (dartCast h d).2 = d.2 := by cases h; rfl

private theorem unresize_identification {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (p : StageDart k → ℕ) (q : StageDart l → ℕ)
    (he : ∀ d, q (dartCast h d) = p d)
    (hi : ∀ d d', (StageRotation.resize h σ).SameCycle d d' ↔ q d = q d') :
    ∀ d d', σ.SameCycle d d' ↔ p d = p d' := by
  cases h
  intro d d'
  rw [← he d, ← he d']
  exact hi d d'

private theorem step_vertices (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3)
    (hi : ∀ d d', σ.SameCycle d d' ↔ stageEndpoint s d = stageEndpoint s d')
    (hb : ∀ d, stageEndpoint s d < s.nextVertex) :
    ∀ d d', (StageRotation.step s ha hu σ c).SameCycle d d' ↔
      stageEndpoint (kmswStep s c) d = stageEndpoint (kmswStep s c) d' := by
  cases hc : kmswCodeStep c with
  | down =>
    cases hr : s.UR with
    | nil =>
      let hsize : (kmswStep s c).nextEdge = s.nextEdge + 1 := by
        simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
      apply unresize_identification hsize _ (stageEndpoint (kmswStep s c))
        (stageEndpoint (s.addEdge (s.east s.active) s.nextVertex true))
      · intro d
        dsimp only [stageEndpoint]
        rw [dartCast_bool hsize d, dartCast_val hsize d]
        simp only [kmswStep, hc,
          kmswStepOfStep, hr, State.addEdge]
      · rw [StageRotation.step_pendant s ha hu σ c hc hr]
        exact pendant_vertices s σ (⟨s.active, ha⟩, true) hi hb
    | cons e es =>
      let hsize : (kmswStep s c).nextEdge = s.nextEdge := by
        simp only [kmswStep, hc, kmswStepOfStep, hr]
      apply unresize_identification hsize _ (stageEndpoint (kmswStep s c)) (stageEndpoint s)
      · intro d
        dsimp only [stageEndpoint]
        rw [dartCast_bool hsize d, dartCast_val hsize d]
        simp only [kmswStep, hc,
          kmswStepOfStep, hr]
      · rw [StageRotation.step_activation s ha hu σ c hc e es hr]
        exact hi
  | left =>
    cases hl : s.UL.dropLast.reverse with
    | nil =>
      let hsize : (kmswStep s c).nextEdge = s.nextEdge + 2 := by
        simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
      apply unresize_identification hsize _ (stageEndpoint (kmswStep s c))
        (stageEndpoint ((s.addEdge s.nextVertex (s.east s.active) true).addEdge
          s.nextVertex (s.west s.active) false))
      · intro d
        dsimp only [stageEndpoint]
        rw [dartCast_bool hsize d, dartCast_val hsize d]
        simp only [kmswStep, hc,
          kmswStepOfStep, hl, State.addEdge]
      · rw [StageRotation.step_leftFresh s ha hu σ c hc hl]
        exact leftFresh_vertices s σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true) hi hb
    | cons e es =>
      have he := hu e (List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      let hsize : (kmswStep s c).nextEdge = s.nextEdge + 1 := by
        simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
      apply unresize_identification hsize _ (stageEndpoint (kmswStep s c))
        (stageEndpoint (s.addEdge (s.west e) (s.east s.active) true))
      · intro d
        dsimp only [stageEndpoint]
        rw [dartCast_bool hsize d, dartCast_val hsize d]
        simp only [kmswStep, hc,
          kmswStepOfStep, hl, State.addEdge]
      · rw [StageRotation.step_leftExisting s ha hu σ c hc e es hl]
        exact leftExisting_vertices s σ (⟨e, he⟩, false) (⟨s.active, ha⟩, true) hi hb
  | up =>
    let hsize : (kmswStep s c).nextEdge = s.nextEdge + 2 := by
      simp only [kmswStep, hc, kmswStepOfStep, State.addEdge]
    apply unresize_identification hsize _ (stageEndpoint (kmswStep s c))
      (stageEndpoint ((s.addEdge (s.west s.active) s.nextVertex true).addEdge
        s.nextVertex (s.east s.active) false))
    · intro d
      dsimp only [stageEndpoint]
      rw [dartCast_bool hsize d, dartCast_val hsize d]
      simp only [kmswStep, hc,
        kmswStepOfStep, State.addEdge]
    · rw [StageRotation.step_up s ha hu σ c hc]
      exact up_vertices s σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true) hi hb

/-- Rotation vertices are exactly geometric endpoint IDs in the finite KMSW -/
theorem stageRot_sameCycle_iff_endpoint_eq (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d d' : StageDart (kmswStage w n).nextEdge,
      (stageRot w n).SameCycle d d' ↔
        stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) d' := by
  induction n with
  | zero =>
    change ∀ d d' : StageDart 1, (1 : Equiv.Perm (StageDart 1)).SameCycle d d' ↔
      stageEndpoint kmswInit d = stageEndpoint kmswInit d'
    rintro ⟨e, b⟩ ⟨e', b'⟩
    rw [Equiv.Perm.sameCycle_one]
    have he : e = 0 := Fin.ext (by have := e.isLt; omega)
    have he' : e' = 0 := Fin.ext (by have := e'.isLt; omega)
    subst e
    subst e'
    cases b <;> cases b' <;>
      simp [stageEndpoint, kmswInit]
  | succ n ih =>
    exact step_vertices (kmswStage w n) (act_lt_nextEdge w (le_refl n))
      (stageRotation_UL_bound w n) (stageRot w n) (w n) ih
      (stageEndpoint_lt_nextVertex w n)

/-- Every allocated vertex ID has an incident geometric dart (`def-kmsw`, -/
theorem stageEndpoint_exists (w : ℕ → Fin 3) (n : ℕ) :
    ∀ v < (kmswStage w n).nextVertex,
      ∃ d : StageDart (kmswStage w n).nextEdge, stageEndpoint (kmswStage w n) d = v := by
  induction n with
  | zero =>
    intro v hv
    change v < 2 at hv
    have he : 0 < (kmswStage w 0).nextEdge := by change 0 < 1; decide
    by_cases h : v = 0
    · exact ⟨(⟨0, he⟩, false), h.symm⟩
    · have h' : v = 1 := by omega
      exact ⟨(⟨0, he⟩, true), h'.symm⟩
  | succ n ih =>
    intro v hv
    by_cases ho : v < (kmswStage w n).nextVertex
    · obtain ⟨⟨e, b⟩, he⟩ := ih v ho
      have he' : e.val < (kmswStage w (n + 1)).nextEdge :=
        e.isLt.trans_le (kmswStage_nextEdge_mono w (by omega))
      have hs := kmswStage_endpoints_stable w (m := n) (n := n + 1) (by omega) e.isLt
      refine ⟨(⟨e.val, he'⟩, b), ?_⟩
      cases b
      · exact hs.1.trans he
      · exact hs.2.trans he
    · cases hc : kmswCodeStep (w n) with
      | down =>
        cases hr : (kmswStage w n).UR with
        | nil =>
          have hV : v = (kmswStage w n).nextVertex := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] at hv
            omega
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
            omega
          refine ⟨(⟨(kmswStage w n).nextEdge, he⟩, true), ?_⟩
          simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, stageEndpoint,
            State.addEdge, ↓reduceIte] using hV.symm
        | cons e es =>
          have hv' : v < (kmswStage w n).nextVertex := by
            simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] using hv
          exact (ho hv').elim
      | left =>
        cases hl : (kmswStage w n).UL.dropLast.reverse with
        | nil =>
          have hV : v = (kmswStage w n).nextVertex := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl] at hv
            omega
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
            omega
          refine ⟨(⟨(kmswStage w n).nextEdge, he⟩, false), ?_⟩
          simpa [kmswStage, kmswStep, hc, kmswStepOfStep, hl, stageEndpoint,
            State.addEdge] using hV.symm
        | cons e es =>
          have hv' : v < (kmswStage w n).nextVertex := by
            simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge] using hv
          exact (ho hv').elim
      | up =>
        have hV : v = (kmswStage w n).nextVertex := by
          simp only [kmswStage, kmswStep, hc, kmswStepOfStep] at hv
          omega
        have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
          simp only [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge]
          omega
        refine ⟨(⟨(kmswStage w n).nextEdge, he⟩, true), ?_⟩
        simpa [kmswStage, kmswStep, hc, kmswStepOfStep, stageEndpoint,
          State.addEdge] using hV.symm

/-- The vertex quotient of the stage map is equivalent to its creation-order -/
@[expose] noncomputable def stageVertexEquiv (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).VertexQuotient ≃ Fin (kmswStage w n).nextVertex := by
  classical
  let f : (kmswMap w n).VertexQuotient → Fin (kmswStage w n).nextVertex :=
    Quotient.lift (fun d => ⟨stageEndpoint (kmswStage w n) d,
      stageEndpoint_lt_nextVertex w n d⟩) (fun d d' h =>
        Fin.ext ((stageRot_sameCycle_iff_endpoint_eq w n d d').1 h))
  apply Equiv.ofBijective f
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro d d' h
    apply Quotient.sound
    apply (stageRot_sameCycle_iff_endpoint_eq w n d d').2
    exact congrArg Fin.val h
  · intro v
    obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
    exact ⟨Quotient.mk _ d, Fin.ext hd⟩

/-- The number of rotation vertices equals the number of allocated KMSW -/
theorem kmswMap_numVertices (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).numVertices = (kmswStage w n).nextVertex := by
  classical
  unfold CombinatorialMap.numVertices
  simpa only [Fintype.card_fin] using Fintype.card_congr (stageVertexEquiv w n)

end DirectedDistances.KMSW
