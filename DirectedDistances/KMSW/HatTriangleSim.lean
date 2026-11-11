module

public import DirectedDistances.KMSW.QuadKMSWHatAllStages
public import DirectedDistances.KMSW.HatLimitIncidenceIso








public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

/-- Edge-triple simulation: every triangle of `sh` maps under `φ` to a triangle
of `gl` (face layer of the hatted half of `lem-quad-kmsw`, -/
@[expose] def TriSim (φ : ℕ → ℕ) (sh gl : State) : Prop :=
  ∀ t ∈ sh.triangles, (φ t.1, φ t.2.1, φ t.2.2) ∈ gl.triangles

/-- All triangle edge ids of `s` are allocated. -/
@[expose] def TriBound (s : State) : Prop :=
  ∀ t ∈ s.triangles, t.1 < s.nextEdge ∧ t.2.1 < s.nextEdge ∧ t.2.2 < s.nextEdge

theorem triangles_sub_step (s : State) (st : Step) :
    ∀ t ∈ s.triangles, t ∈ (kmswStepOfStep s st).triangles := by
  intro t ht
  cases st <;> simp only [kmswStepOfStep] <;> (try split) <;>
    simp [State.addEdge, ht]

theorem triangles_sub_stage (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    ∀ t ∈ (kmswStage w m).triangles, t ∈ (kmswStage w n).triangles := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun t ht => ht
  | succ n _ ih =>
      intro t ht
      exact triangles_sub_step _ _ t (ih t ht)

private theorem stage_pred_bound' (u : ℕ → Fin 3) (m : ℕ) :
    ∀ e ∈ (kmswStage u m).UL.dropLast.reverse,
      e < (kmswStage u m).nextEdge := by
  intro e he
  apply (kmswStage_boundary_ids_lt_nextEdge u m).2
  have hm : e ∈ (kmswStage u m).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp he)
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hm))

theorem triBound_step (s : State) (st : Step) (hb : TriBound s)
    (ha : s.active < s.nextEdge)
    (hp : ∀ e ∈ s.UL.dropLast.reverse, e < s.nextEdge) :
    TriBound (kmswStepOfStep s st) := by
  intro t ht
  cases st with
  | down =>
      cases hur : s.UR with
      | nil =>
          simp only [kmswStepOfStep, hur, State.addEdge] at ht ⊢
          have := hb t ht
          omega
      | cons e es =>
          simp only [kmswStepOfStep, hur] at ht ⊢
          exact hb t ht
  | left =>
      cases hpr : s.UL.dropLast.reverse with
      | nil =>
          simp only [kmswStepOfStep, hpr, State.addEdge, List.mem_append,
            List.mem_singleton] at ht ⊢
          rcases ht with ht | rfl
          · have := hb t ht
            omega
          · simp
            omega
      | cons e es =>
          have he : e < s.nextEdge := hp e (by rw [hpr]; exact List.mem_cons_self)
          simp only [kmswStepOfStep, hpr, State.addEdge, List.mem_append,
            List.mem_singleton] at ht ⊢
          rcases ht with ht | rfl
          · have := hb t ht
            omega
          · simp
            omega
  | up =>
      simp only [kmswStepOfStep, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · have := hb t ht
        omega
      · simp
        omega

theorem triBound_stage (w : ℕ → Fin 3) (n : ℕ) : TriBound (kmswStage w n) := by
  induction n with
  | zero => intro t ht; simp [kmswStage, kmswInit] at ht
  | succ n ih =>
      exact triBound_step _ (kmswCodeStep (w n)) ih
        (kmswStage_boundary_ids_lt_nextEdge w n).1 (stage_pred_bound' w n)

/-- Old triangles keep their images when the map only changes at fresh ids. -/
theorem triSim_old {φ φ' : ℕ → ℕ} {sh gl gl' : State} (hb : TriBound sh)
    (hT : TriSim φ sh gl) (hag : ∀ e, e < sh.nextEdge → φ' e = φ e)
    (hsub : ∀ t ∈ gl.triangles, t ∈ gl'.triangles) :
    ∀ t ∈ sh.triangles, (φ' t.1, φ' t.2.1, φ' t.2.2) ∈ gl'.triangles := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hb t ht
  rw [hag _ h1, hag _ h2, hag _ h3]
  exact hsub _ (hT t ht)

private theorem nextEdge_old_agree (sh gl : State) (st : Step) (eφ : ℕ → ℕ)
    (e : ℕ) (he : e < sh.nextEdge) :
    kmswShiftNextEdgeMap sh gl st eφ e = eφ e := by
  have hn : e ≠ sh.nextEdge := ne_of_lt he
  have hn2 : e ≠ sh.nextEdge + 1 := by omega
  cases st with
  | up => simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, hn, hn2]
  | down =>
      cases hs : sh.UR <;> cases hg : gl.UR <;>
        simp [kmswShiftNextEdgeMap, hs, hg, kmswShiftFreshEdgeMap,
          kmswShiftDownMismatchEdgeMap, hn]
  | left =>
      cases hs : sh.UL.dropLast.reverse <;> cases hg : gl.UL.dropLast.reverse <;>
        simp [kmswShiftNextEdgeMap, hs, hg, kmswShiftUpEdgeMap,
          kmswShiftFreshEdgeMap, kmswShiftLeftMismatchEdgeMap, hn, hn2]

/-- A common up step preserves triangle simulation. -/
theorem triSim_step_up (u w : ℕ → Fin 3) (m n d : ℕ) (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ d)
    (hT : TriSim eφ (kmswStage u m) (kmswStage w n)) :
    TriSim (kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .up eφ)
      (kmswStepOfStep (kmswStage u m) .up) (kmswStepOfStep (kmswStage w n) .up) := by
  intro t ht
  have hb := triBound_stage u m
  have hold := triSim_old (φ' := kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .up eφ)
    hb hT (fun e he => nextEdge_old_agree _ _ _ _ e he)
    (triangles_sub_step (kmswStage w n) .up)
  have htl : (kmswStepOfStep (kmswStage u m) .up).triangles =
      (kmswStage u m).triangles ++ [((kmswStage u m).active, (kmswStage u m).nextEdge,
        (kmswStage u m).nextEdge + 1)] := by
    simp [kmswStepOfStep, State.addEdge]
  have hgl : (kmswStepOfStep (kmswStage w n) .up).triangles =
      (kmswStage w n).triangles ++ [((kmswStage w n).active, (kmswStage w n).nextEdge,
        (kmswStage w n).nextEdge + 1)] := by
    simp [kmswStepOfStep, State.addEdge]
  rw [htl] at ht
  rw [hgl]
  rcases List.mem_append.mp ht with ht | ht
  · have := hold t ht
    rw [hgl] at this
    exact this
  · rw [List.mem_singleton] at ht
    subst ht
    refine List.mem_append_right _ ?_
    have ha := hs.incidenceSim.active
    have ha' := (kmswStage_boundary_ids_lt_nextEdge u m).1
    have h1 : (kmswStage u m).active ≠ (kmswStage u m).nextEdge := ne_of_lt ha'
    have h2 : (kmswStage u m).active ≠ (kmswStage u m).nextEdge + 1 := by omega
    simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, ha, h1, h2]

/-- A common down step preserves triangle simulation (no triangle is added). -/
theorem triSim_step_down (u w : ℕ → Fin 3) (m n : ℕ) (eφ : ℕ → ℕ)
    (hT : TriSim eφ (kmswStage u m) (kmswStage w n)) :
    TriSim (kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .down eφ)
      (kmswStepOfStep (kmswStage u m) .down) (kmswStepOfStep (kmswStage w n) .down) := by
  intro t ht
  have hb := triBound_stage u m
  have hold := triSim_old (φ' := kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .down eφ)
    hb hT (fun e he => nextEdge_old_agree _ _ _ _ e he)
    (triangles_sub_step (kmswStage w n) .down)
  have htr : (kmswStepOfStep (kmswStage u m) .down).triangles =
      (kmswStage u m).triangles := by
    cases hur : (kmswStage u m).UR <;> simp [kmswStepOfStep, hur, State.addEdge]
  rw [htr] at ht
  exact hold t ht

/-- A common left step at positive depth preserves triangle simulation. -/
theorem triSim_step_left (u w : ℕ → Fin 3) (m n d : ℕ) (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ (d + 1))
    (hT : TriSim eφ (kmswStage u m) (kmswStage w n)) :
    TriSim (kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .left eφ)
      (kmswStepOfStep (kmswStage u m) .left) (kmswStepOfStep (kmswStage w n) .left) := by
  intro t ht
  have hb := triBound_stage u m
  have hold := triSim_old
    (φ' := kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .left eφ)
    hb hT (fun e he => nextEdge_old_agree _ _ _ _ e he)
    (triangles_sub_step (kmswStage w n) .left)
  have hne : (kmswStage u m).UL.dropLast.reverse ≠ [] := by
    intro he
    have hd := hs.depth_le
    simp [he] at hd
  obtain ⟨a, as, hp⟩ := List.exists_cons_of_ne_nil hne
  have heq := hs.ul_depth_prefix
  have hglne : (kmswStage w n).UL.dropLast.reverse ≠ [] := by
    intro he
    simp [hp, he] at heq
  obtain ⟨b, bs, hgp⟩ := List.exists_cons_of_ne_nil hglne
  have hab : eφ a = b := by
    rw [hp, hgp] at heq
    simp at heq
    exact heq.1
  have ha : a < (kmswStage u m).nextEdge :=
    stage_pred_bound' u m a (by rw [hp]; exact List.mem_cons_self)
  have hact := hs.incidenceSim.active
  have hlt : a ≠ (kmswStage u m).nextEdge := ne_of_lt ha
  have hmap : kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .left eφ =
      kmswShiftFreshEdgeMap (kmswStage u m) (kmswStage w n) eφ := by
    simp [kmswShiftNextEdgeMap, hp, hgp]
  rw [hmap] at hold ⊢
  have htl : (kmswStepOfStep (kmswStage u m) .left).triangles =
      (kmswStage u m).triangles ++ [((kmswStage u m).active, (kmswStage u m).nextEdge, a)] := by
    simp [kmswStepOfStep, hp, State.addEdge]
  have hgl : (kmswStepOfStep (kmswStage w n) .left).triangles =
      (kmswStage w n).triangles ++ [((kmswStage w n).active, (kmswStage w n).nextEdge, b)] := by
    simp [kmswStepOfStep, hgp, State.addEdge]
  rw [htl] at ht
  rw [hgl]
  rcases List.mem_append.mp ht with ht | ht
  · have := hold t ht
    rw [hgl] at this
    exact this
  · rw [List.mem_singleton] at ht
    subst ht
    refine List.mem_append_right _ ?_
    have hact': (kmswStage u m).active ≠ (kmswStage u m).nextEdge :=
      ne_of_lt (kmswStage_boundary_ids_lt_nextEdge u m).1
    simp [kmswShiftFreshEdgeMap, hact', hlt, hact, hab]

private theorem exc_edge_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k e : ℕ) (he : e < (kmswStage w (walkNL w h k - 1)).nextEdge) :
    hatExcursionEdgeMap w h k e = e := by
  unfold hatExcursionEdgeMap
  split
  · simp [kmswShiftFreshEdgeMap, ne_of_lt he]
  · rfl

private theorem down_triangles (s : State) :
    (kmswStepOfStep s .down).triangles = s.triangles := by
  cases hur : s.UR <;> simp [kmswStepOfStep, hur, State.addEdge]

private theorem tri_edgeMap_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatAllEdgeMap w h (hatExitIndex w h k + 1) =
      hatExcursionEdgeMap w h k ∘
        kmswShiftNextEdgeMap (kmswStage (hatCodes w h) (hatExitIndex w h k))
          (kmswStage w (walkNL w h k - 1)) .down
          (hatAllEdgeMap w h (hatExitIndex w h k)) := by
  classical
  have hex : ∃ l, hatExitIndex w h l = hatExitIndex w h k := ⟨k, rfl⟩
  have hc : Classical.choose hex = k :=
    hatExitIndex_injective w h (Classical.choose_spec hex)
  simp only [hatAllEdgeMap, dif_pos hex, hc]

private theorem tri_time_exit_succ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageTime w h (hatExitIndex w h k + 1) = walkNR w h (k + 1) := by
  rw [← hatCodeTime_succ, hatCodeTime_at_exit]
  have hp := (walkNR_succ_spec w h k).1
  omega

/-- Triangle simulation for the exit-replaced stream at every finite stage
(face layer of the hatted half of `lem-quad-kmsw`,
planar claim. -/
theorem hatAll_triSim (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, TriSim (hatAllEdgeMap w h m) (kmswStage (hatCodes w h) m)
      (kmswStage w (quadrantRStageTime w h m)) := by
  intro m
  induction m with
  | zero => intro t ht; simp [kmswStage, kmswInit] at ht
  | succ m ih =>
      classical
      by_cases hex : ∃ k, hatExitIndex w h k = m
      · obtain ⟨k, rfl⟩ := hex
        rw [tri_time_exit_succ, tri_edgeMap_exit]
        rw [quadrantRStageTime_hatExitIndex] at ih
        have hlocal : kmswStage (hatCodes w h) (hatExitIndex w h k + 1) =
            kmswStepOfStep (kmswStage (hatCodes w h) (hatExitIndex w h k)) .down := by
          rw [kmswStage, hatCodes_at_exit]
          rfl
        have hgap : walkNL w h k + 1 ≤ walkNR w h (k + 1) := (walkNR_succ_spec w h k).1
        have hpos := (walkNL_spec w h k).1
        have hle : walkNL w h k - 1 ≤ walkNR w h (k + 1) := by omega
        intro t ht
        rw [hlocal, down_triangles] at ht
        obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) _ t ht
        have hmem := ih t ht
        have c1 : hatAllEdgeMap w h (hatExitIndex w h k) t.1 <
            (kmswStage w (walkNL w h k - 1)).nextEdge :=
          (triBound_stage w (walkNL w h k - 1) _ hmem).1
        have c2 : hatAllEdgeMap w h (hatExitIndex w h k) t.2.1 <
            (kmswStage w (walkNL w h k - 1)).nextEdge :=
          (triBound_stage w (walkNL w h k - 1) _ hmem).2.1
        have c3 : hatAllEdgeMap w h (hatExitIndex w h k) t.2.2 <
            (kmswStage w (walkNL w h k - 1)).nextEdge :=
          (triBound_stage w (walkNL w h k - 1) _ hmem).2.2
        simp only [Function.comp_apply]
        rw [nextEdge_old_agree _ _ _ _ _ b1, nextEdge_old_agree _ _ _ _ _ b2,
          nextEdge_old_agree _ _ _ _ _ b3, exc_edge_old w h k _ c1,
          exc_edge_old w h k _ c2, exc_edge_old w h k _ c3]
        exact triangles_sub_stage w hle _ hmem
      · set n := quadrantRStageTime w h m with hnn
        have hs := hatAll_sim w h m
        have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
          rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hex]
        have hp := (quadrantRStageTime_spec w h m).1
        have hn := (quadrantRStageTime_spec w h (m + 1)).1
        rw [ht] at hn
        have hc : hatCodes w h m = w n := by
          rw [hatCodes, hatCodeTime_of_not_exit w h m hex]
        have hE : hatAllEdgeMap w h (m + 1) =
            kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m) (kmswStage w n)
              (kmswCodeStep (hatCodes w h m)) (hatAllEdgeMap w h m) := by
          simp only [hatAllEdgeMap, dif_neg hex]
          rfl
        rw [hE, ht]
        change TriSim _ (kmswStepOfStep (kmswStage (hatCodes w h) m)
          (kmswCodeStep (hatCodes w h m))) (kmswStepOfStep (kmswStage w n)
          (kmswCodeStep (w n)))
        rw [hc]
        by_cases h0 : w n = 0
        · have hcs : kmswCodeStep (w n) = .left := by simp [kmswCodeStep, h0]
          have hpos : hatPhaseDepth w n ≠ 0 := by
            intro hz
            have he := (hatPhaseDepth_left_exit_iff w n hp h0).2 hz
            rw [hn] at he
            contradiction
          obtain ⟨d, he⟩ := Nat.exists_eq_succ_of_ne_zero hpos
          rw [he] at hs
          rw [hcs]
          exact triSim_step_left (hatCodes w h) w m n d _ _ hs ih
        · by_cases h1 : w n = 1
          · have hcs : kmswCodeStep (w n) = .up := by simp [kmswCodeStep, h0, h1]
            rw [hcs]
            exact triSim_step_up (hatCodes w h) w m n _ _ _ hs ih
          · have hcs : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, h0, h1]
            rw [hcs]
            exact triSim_step_down (hatCodes w h) w m n _ ih

/-- Stage-independent form: a triangle present at local stage `m` is mapped by the
stage-`m` map into the global triangle list at every later canonical R time
(face layer of the hatted half of `lem-quad-kmsw`, -/
theorem hatAll_triSim_of_le (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m n : ℕ}
    (hmn : m ≤ n) :
    ∀ t ∈ (kmswStage (hatCodes w h) m).triangles,
      (hatAllEdgeMap w h m t.1, hatAllEdgeMap w h m t.2.1, hatAllEdgeMap w h m t.2.2) ∈
        (kmswStage w (quadrantRStageTime w h n)).triangles := by
  intro t ht
  obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) m t ht
  have hn := hatAll_triSim w h n t (triangles_sub_stage (hatCodes w h) hmn t ht)
  rwa [hatAllEdgeMap_eq_of_le w h m n _ hmn b1, hatAllEdgeMap_eq_of_le w h m n _ hmn b2,
    hatAllEdgeMap_eq_of_le w h m n _ hmn b3] at hn

end DirectedDistances.KMSW
