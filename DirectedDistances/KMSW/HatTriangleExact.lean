module

public import DirectedDistances.KMSW.HatTriangleSim
public import DirectedDistances.KMSW.FlowLineTimesIff

/-! # Face (edge-triple) exactness for the hatted half of `lem-quad-kmsw`

These are edge triples, not oriented faces. Rotation and the planar
identification remain; this helper is not counted as the paper result. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk Quiver
open scoped Classical

/-- All geometric endpoints of a stored edge triple are root reachable in the -/
@[expose] def HatTriangleReachable (w : ℕ → Fin 3) (t : ℕ × ℕ × ℕ) : Prop :=
  ∀ e ∈ [t.1, t.2.1, t.2.2],
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩

private theorem new_triangle_active (s : State) (st : Step) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStepOfStep s st).triangles) (hold : t ∉ s.triangles) :
    t.2.1 = (kmswStepOfStep s st).active := by
  cases st with
  | down =>
      cases hs : s.UR <;> simp [kmswStepOfStep, hs, State.addEdge] at ht
      all_goals exact False.elim (hold ht)
  | up =>
      simp only [kmswStepOfStep, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · exact False.elim (hold ht)
      · rfl
  | left =>
      cases hs : s.UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
          List.mem_singleton] at ht ⊢
      all_goals rcases ht with ht | rfl
      all_goals first | exact False.elim (hold ht) | rfl

/-- E1: a triangle created at a primed-phase stage has an unreachable vertex,
concretely the west endpoint of its second edge (the new active edge).
The creation-stage convention includes the left entrance and excludes the
Edge triples only; rotation and planar identification remain; not counted. -/
theorem hatTriangle_lPhase_new_unreachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ) (t : ℕ × ℕ × ℕ)
    (hle : walkNL w h k ≤ n + 1) (hlt : n + 1 < walkNR w h (k + 1))
    (ht : t ∈ (kmswStage w (n + 1)).triangles)
    (hold : t ∉ (kmswStage w n).triangles) :
    t.2.1 ∈ [t.1, t.2.1, t.2.2] ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w t.2.1⟩ := by
  have ha : t.2.1 = act w (n + 1) :=
    new_triangle_active _ (kmswCodeStep (w n)) t ht hold
  refine ⟨by simp, ?_⟩
  have hb := (triBound_stage w (n + 1) t ht).2.1
  rw [← (edge_endpoints_eq w hb).1, ha]
  exact lPhase_activeWest_unreachable w h k (n + 1) hle hlt

private theorem down_triangles_exact (s : State) :
    (kmswStepOfStep s .down).triangles = s.triangles := by
  cases hs : s.UR <;> simp [kmswStepOfStep, hs, State.addEdge]

/-- No fully reachable triangle is created across an entire skipped excursion,
including its left exit and final down step (`lem-quad-kmsw`, -/
theorem hatTriangle_excursion_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w (walkNR w h (k + 1))).triangles)
    (hr : HatTriangleReachable w t) :
    t ∈ (kmswStage w (walkNL w h k - 1)).triangles := by
  have hpos := (walkNL_spec w h k).1
  have hgap := (walkNR_succ_spec w h k).1
  have hlast : walkNR w h (k + 1) - 1 + 1 = walkNR w h (k + 1) := by omega
  have hc := walkNR_succ_previous_code w h k
  rw [← hlast] at ht
  change t ∈ (kmswStepOfStep _ (kmswCodeStep (w _))).triangles at ht
  rw [hc] at ht
  change t ∈ (kmswStepOfStep _ .down).triangles at ht
  rw [down_triangles_exact] at ht
  have retreat : ∀ n, walkNL w h k - 1 ≤ n → n < walkNR w h (k + 1) →
      t ∈ (kmswStage w n).triangles →
      t ∈ (kmswStage w (walkNL w h k - 1)).triangles := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact fun _ ht => ht
    | succ n hn ih =>
        intro hlt ht
        apply ih (by omega)
        by_contra hold
        have bad := (hatTriangle_lPhase_new_unreachable w h k n t
          (by omega) hlt ht hold).2
        exact bad (hr t.2.1 (by simp)).1
  exact retreat _ (by omega) (by omega) ht


private theorem step_up_new_image (u w : ℕ → Fin 3) (m n d : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ d)
    (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStepOfStep (kmswStage w n) .up).triangles)
    (hold : t ∉ (kmswStage w n).triangles) :
    ∃ t' ∈ (kmswStepOfStep (kmswStage u m) .up).triangles,
      let f := kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .up eφ
      (f t'.1, f t'.2.1, f t'.2.2) = t := by
  simp only [kmswStepOfStep, State.addEdge, List.mem_append,
    List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact False.elim (hold ht)
  · refine ⟨((kmswStage u m).active, (kmswStage u m).nextEdge,
        (kmswStage u m).nextEdge + 1), ?_, ?_⟩
    · simp [kmswStepOfStep, State.addEdge]
    · have hb := (kmswStage_boundary_ids_lt_nextEdge u m).1
      have h1 : (kmswStage u m).active ≠ (kmswStage u m).nextEdge := ne_of_lt hb
      have h2 : (kmswStage u m).active ≠ (kmswStage u m).nextEdge + 1 := by omega
      simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, h1, h2,
        hs.incidenceSim.active]

private theorem step_left_new_image (u w : ℕ → Fin 3) (m n d : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ (d + 1))
    (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStepOfStep (kmswStage w n) .left).triangles)
    (hold : t ∉ (kmswStage w n).triangles) :
    ∃ t' ∈ (kmswStepOfStep (kmswStage u m) .left).triangles,
      let f := kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .left eφ
      (f t'.1, f t'.2.1, f t'.2.2) = t := by
  have hne : (kmswStage u m).UL.dropLast.reverse ≠ [] := by
    intro he
    have hd := hs.depth_le
    simp [he] at hd
  obtain ⟨a, as, hp⟩ := List.exists_cons_of_ne_nil hne
  have heq := hs.ul_depth_prefix
  have hgne : (kmswStage w n).UL.dropLast.reverse ≠ [] := by
    intro he
    simp [hp, he] at heq
  obtain ⟨b, bs, hgp⟩ := List.exists_cons_of_ne_nil hgne
  have hab : eφ a = b := by
    rw [hp, hgp] at heq
    simp at heq
    exact heq.1
  have ha : a < (kmswStage u m).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge u m).2
    have hm : a ∈ (kmswStage u m).UL :=
      List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hp]; simp))
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hm))
  simp only [kmswStepOfStep, hgp, State.addEdge, List.mem_append,
    List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact False.elim (hold ht)
  · refine ⟨((kmswStage u m).active, (kmswStage u m).nextEdge, a), ?_, ?_⟩
    · simp [kmswStepOfStep, hp, State.addEdge]
    · have hact : (kmswStage u m).active ≠ (kmswStage u m).nextEdge :=
        ne_of_lt (kmswStage_boundary_ids_lt_nextEdge u m).1
      simp [kmswShiftNextEdgeMap, hp, hgp, kmswShiftFreshEdgeMap,
        hact, ne_of_lt ha, hs.incidenceSim.active, hab]

/-- E2: away from an exit, each newly created global triangle is the image
of a local triangle at the corresponding next stage (`lem-quad-kmsw`,
rotation and planar identification remain; not counted. -/
private theorem nonexit_new_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : ¬ ∃ k, hatExitIndex w h k = m) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w (quadrantRStageTime w h (m + 1))).triangles)
    (hold : t ∉ (kmswStage w (quadrantRStageTime w h m)).triangles) :
    ∃ t' ∈ (kmswStage (hatCodes w h) (m + 1)).triangles,
      (hatAllEdgeMap w h (m + 1) t'.1, hatAllEdgeMap w h (m + 1) t'.2.1,
        hatAllEdgeMap w h (m + 1) t'.2.2) = t := by
  let n := quadrantRStageTime w h m
  have htime : quadrantRStageTime w h (m + 1) = n + 1 := by
    rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hm]
  have hc : hatCodes w h m = w n := by
    rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  have hmap : hatAllEdgeMap w h (m + 1) =
      kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m) (kmswStage w n)
        (kmswCodeStep (w n)) (hatAllEdgeMap w h m) := by
    simp only [hatAllEdgeMap, dite_eq_right hm, hc]
    rfl
  rw [htime] at ht
  rw [hmap]
  change ∃ t' ∈ (kmswStepOfStep (kmswStage (hatCodes w h) m)
    (kmswCodeStep (hatCodes w h m))).triangles, _
  rw [hc]
  change t ∈ (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).triangles at ht
  have hs := hatAll_sim w h m
  by_cases h0 : w n = 0
  · have hcs : kmswCodeStep (w n) = .left := by simp [kmswCodeStep, h0]
    have hpos : hatPhaseDepth w n ≠ 0 := by
      intro hz
      have hp := (quadrantRStageTime_spec w h m).1
      have hn := (quadrantRStageTime_spec w h (m + 1)).1
      rw [htime] at hn
      have he := (hatPhaseDepth_left_exit_iff w n hp h0).2 hz
      rw [hn] at he
      contradiction
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    change HatPhaseSim _ _ _ _ (hatPhaseDepth w n) at hs
    rw [hd] at hs
    rw [hcs] at ht ⊢
    exact step_left_new_image (hatCodes w h) w m n d _ _ hs t ht hold
  · by_cases h1 : w n = 1
    · have hcs : kmswCodeStep (w n) = .up := by simp [kmswCodeStep, h1]
      rw [hcs] at ht ⊢
      exact step_up_new_image (hatCodes w h) w m n _ _ _ hs t ht hold
    · have hcs : kmswCodeStep (w n) = .down := by simp [kmswCodeStep, h0, h1]
      rw [hcs, down_triangles_exact] at ht
      exact False.elim (hold ht)


/-- E2 with explicit creation: a new global triangle at a non-exit step
is the edgewise image of a new local triangle (`lem-quad-kmsw`,
planar identification remain; not counted. -/
theorem hatTriangle_nonexit_new_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : ¬ ∃ k, hatExitIndex w h k = m) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w (quadrantRStageTime w h (m + 1))).triangles)
    (hold : t ∉ (kmswStage w (quadrantRStageTime w h m)).triangles) :
    ∃ t' ∈ (kmswStage (hatCodes w h) (m + 1)).triangles,
      t' ∉ (kmswStage (hatCodes w h) m).triangles ∧
      (hatAllEdgeMap w h (m + 1) t'.1, hatAllEdgeMap w h (m + 1) t'.2.1,
        hatAllEdgeMap w h (m + 1) t'.2.2) = t := by
  obtain ⟨t', ht', heq⟩ := nonexit_new_image w h m hm t ht hold
  refine ⟨t', ht', ?_, heq⟩
  intro htold
  have hb := triBound_stage (hatCodes w h) m t' htold
  have him := hatAll_triSim w h m t' htold
  rw [hatAllEdgeMap_extend w h m _ hb.1,
    hatAllEdgeMap_extend w h m _ hb.2.1,
    hatAllEdgeMap_extend w h m _ hb.2.2] at heq
  exact hold (heq ▸ him)

private theorem image_extend (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : ∃ t' ∈ (kmswStage (hatCodes w h) m).triangles,
      (hatAllEdgeMap w h m t'.1, hatAllEdgeMap w h m t'.2.1,
        hatAllEdgeMap w h m t'.2.2) = t) :
    ∃ t' ∈ (kmswStage (hatCodes w h) (m + 1)).triangles,
      (hatAllEdgeMap w h (m + 1) t'.1, hatAllEdgeMap w h (m + 1) t'.2.1,
        hatAllEdgeMap w h (m + 1) t'.2.2) = t := by
  obtain ⟨t', ht', heq⟩ := ht
  have hb := triBound_stage (hatCodes w h) m t' ht'
  refine ⟨t', triangles_sub_stage (hatCodes w h) (Nat.le_succ m) t' ht', ?_⟩
  rwa [hatAllEdgeMap_extend w h m _ hb.1,
    hatAllEdgeMap_extend w h m _ hb.2.1,
    hatAllEdgeMap_extend w h m _ hb.2.2]

private theorem time_after_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageTime w h (hatExitIndex w h k + 1) = walkNR w h (k + 1) := by
  rw [← hatCodeTime_succ, hatCodeTime_at_exit]
  have hp := (walkNR_succ_spec w h k).1
  omega

/-- T3: every global triangle with root-reachable endpoints at a canonical
R stage is the edgewise image of a local triangle. Face (edge-triple)
exactness for the hatted half of `lem-quad-kmsw`
planar identification remain; not counted as the paper result. -/
theorem hatAll_triangle_exact (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w (quadrantRStageTime w h m)).triangles)
    (hr : HatTriangleReachable w t) :
    ∃ t' ∈ (kmswStage (hatCodes w h) m).triangles,
      (hatAllEdgeMap w h m t'.1, hatAllEdgeMap w h m t'.2.1,
        hatAllEdgeMap w h m t'.2.2) = t := by
  induction m with
  | zero =>
      have hz : quadrantRStageTime w h 0 = 0 := by
        apply quadrantRStageTime_eq_of_initial_R
        have hp := (walkNL_spec w h 0).1
        rw [walkNR_zero] at hp
        omega
      simp [hz, kmswStage, kmswInit] at ht
  | succ m ih =>
      by_cases hex : ∃ k, hatExitIndex w h k = m
      · obtain ⟨k, rfl⟩ := hex
        rw [time_after_exit] at ht
        have htold := hatTriangle_excursion_old w h k t ht hr
        rw [← quadrantRStageTime_hatExitIndex] at htold
        exact image_extend w h _ t (ih htold)
      · by_cases hold : t ∈ (kmswStage w (quadrantRStageTime w h m)).triangles
        · exact image_extend w h m t (ih hold)
        · obtain ⟨t', ht', _, heq⟩ := hatTriangle_nonexit_new_image w h m hex t ht hold
          exact ⟨t', ht', heq⟩

/-- T3 in finite-stage endpoint notation: all endpoints of the three boundary
edge ids are reachable. Face (edge-triple) exactness for the hatted half of
faces. Rotation and planar identification remain; not counted. -/
theorem hatAll_triangle_exact_stage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w (quadrantRStageTime w h m)).triangles)
    (hr : ∀ e ∈ [t.1, t.2.1, t.2.2],
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (quadrantRStageTime w h m)).west e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (quadrantRStageTime w h m)).east e⟩) :
    ∃ t' ∈ (kmswStage (hatCodes w h) m).triangles,
      (hatAllEdgeMap w h m t'.1, hatAllEdgeMap w h m t'.2.1,
        hatAllEdgeMap w h m t'.2.2) = t := by
  apply hatAll_triangle_exact w h m t ht
  intro e he
  have hb := triBound_stage w (quadrantRStageTime w h m) t ht
  have heb : e < (kmswStage w (quadrantRStageTime w h m)).nextEdge := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  have heq := edge_endpoints_eq w heb
  simpa only [heq.1, heq.2] using hr e he

end DirectedDistances.KMSW
