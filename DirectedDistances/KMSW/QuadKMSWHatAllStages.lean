module

public import DirectedDistances.KMSW.QuadKMSWHatPhaseSim
import DirectedDistances.KMSW.OutgoingInterval

/-! # All-stage simulation for the exit-replaced M-hat stream

Stagewise incidence simulation and coherent allocation maps for the stream
`hatCodes`, toward `lem-quad-kmsw`, `eqn-quad-pre`, and
Identification with `rCodeSequence` uses `ZHatCharacterization` together with
`hatCodes_pointwise`. Limit and path-lift packaging belongs to `HatImageLimit`.
These helpers assert no face or rotation correspondence and are not the full
`lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

/-- Coherent edge maps for the exit-replaced stream. At an exit the common
down-step map is followed by the excursion map (`lem-quad-kmsw`, -/
@[expose] noncomputable def hatAllEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ → ℕ
  | 0 => id
  | m + 1 => by
      classical
      exact if hex : ∃ k, hatExitIndex w h k = m then
        let k := Classical.choose hex
        hatExcursionEdgeMap w h k ∘
          kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m)
            (kmswStage w (walkNL w h k - 1)) .down (hatAllEdgeMap w h m)
      else
        kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m)
          (kmswStage w (quadrantRStageTime w h m))
          (kmswCodeStep (hatCodes w h m)) (hatAllEdgeMap w h m)

/-- Coherent vertex maps, with the same exit composition as the edge maps
(`lem-quad-kmsw`, `eqn-quad-pre`, -/
@[expose] noncomputable def hatAllVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ → ℕ
  | 0 => id
  | m + 1 => by
      classical
      exact if hex : ∃ k, hatExitIndex w h k = m then
        let k := Classical.choose hex
        hatExcursionVertexMap w h k ∘
          kmswShiftNextVertexMap (kmswStage (hatCodes w h) m)
            (kmswStage w (walkNL w h k - 1)) .down (hatAllVertexMap w h m)
      else
        kmswShiftNextVertexMap (kmswStage (hatCodes w h) m)
          (kmswStage w (quadrantRStageTime w h m))
          (kmswCodeStep (hatCodes w h m)) (hatAllVertexMap w h m)

private theorem hatAllEdgeMap_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
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

private theorem hatAllVertexMap_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatAllVertexMap w h (hatExitIndex w h k + 1) =
      hatExcursionVertexMap w h k ∘
        kmswShiftNextVertexMap (kmswStage (hatCodes w h) (hatExitIndex w h k))
          (kmswStage w (walkNL w h k - 1)) .down
          (hatAllVertexMap w h (hatExitIndex w h k)) := by
  classical
  have hex : ∃ l, hatExitIndex w h l = hatExitIndex w h k := ⟨k, rfl⟩
  have hc : Classical.choose hex = k :=
    hatExitIndex_injective w h (Classical.choose_spec hex)
  simp only [hatAllVertexMap, dif_pos hex, hc]

private theorem hatAll_time_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    quadrantRStageTime w h 0 = 0 := by
  apply quadrantRStageTime_eq_of_initial_R
  have hp := (walkNL_spec w h 0).1
  rw [walkNR_zero] at hp
  omega

private theorem hatAll_time_exit_succ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageTime w h (hatExitIndex w h k + 1) = walkNR w h (k + 1) := by
  rw [← hatCodeTime_succ, hatCodeTime_at_exit]
  have hp := (walkNR_succ_spec w h k).1
  omega

private theorem hatAll_depth_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatPhaseDepth w (walkNL w h k - 1) = 0 := by
  have hp := (quadrantRStageTime_spec w h (hatExitIndex w h k)).1
  rw [quadrantRStageTime_hatExitIndex] at hp
  apply (hatPhaseDepth_left_exit_iff w (walkNL w h k - 1) hp
    (walkNL_previous_code w h k)).1
  have hpos := (walkNL_spec w h k).1
  have ht : walkNL w h k - 1 + 1 = walkNL w h k := by omega
  rw [ht]
  exact (quadrantSplitState_at_walkNL (quadrantTrajectoryOfStageCodes w) h k).1

private theorem hatAll_refl (s : State) : HatPhaseSim s s id id 0 := by
  refine ⟨⟨fun _ he => he, fun _ _ _ _ he => he,
    fun _ hv => hv, fun _ _ _ _ hv => hv, rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ _ hp => hp, ?_⟩, Nat.zero_le _, by simp, by simp⟩
  simp

/-- Every finite stage of the exit-replaced stream simulates the global
stage at its canonical R time, at the actual splitter depth. This is the
stagewise M-hat incidence simulation for `lem-quad-kmsw`, `eqn-quad-pre`,
without a face or rotation claim. -/
theorem hatAll_sim (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, HatPhaseSim (kmswStage (hatCodes w h) m)
      (kmswStage w (quadrantRStageTime w h m))
      (hatAllEdgeMap w h m) (hatAllVertexMap w h m)
      (hatPhaseDepth w (quadrantRStageTime w h m)) := by
  intro m
  induction m with
  | zero =>
      rw [hatAll_time_zero]
      simpa [hatAllEdgeMap, hatAllVertexMap, kmswStage, hatPhaseDepth,
        quadrantSplitState, quadrantSplitStart] using hatAll_refl kmswInit
  | succ m ih =>
      classical
      by_cases hex : ∃ k, hatExitIndex w h k = m
      · obtain ⟨k, rfl⟩ := hex
        rw [hatAll_time_exit_succ, hatPhaseDepth_at_walkNR,
          hatAllEdgeMap_exit, hatAllVertexMap_exit]
        have hs := ih
        rw [quadrantRStageTime_hatExitIndex, hatAll_depth_exit] at hs
        exact hatPhaseSim_exit w h k _ _ hs
      · simpa only [hatAllEdgeMap, hatAllVertexMap, dif_neg hex] using
          hatPhaseSim_step w h m hex _ _ ih

private theorem hatNextEdgeMap_old (sh gl : State) (step : Step)
    (eφ : ℕ → ℕ) (e : ℕ) (he : e < sh.nextEdge) :
    kmswShiftNextEdgeMap sh gl step eφ e = eφ e := by
  have hn : e ≠ sh.nextEdge := ne_of_lt he
  have hn2 : e ≠ sh.nextEdge + 1 := by omega
  cases step with
  | up => simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, hn, hn2]
  | down =>
      cases hs : sh.UR <;> cases hg : gl.UR <;>
        simp [kmswShiftNextEdgeMap, hs, hg, kmswShiftFreshEdgeMap,
          kmswShiftDownMismatchEdgeMap, hn]
  | left =>
      cases hs : sh.UL.dropLast.reverse <;> cases hg : gl.UL.dropLast.reverse <;>
        simp [kmswShiftNextEdgeMap, hs, hg, kmswShiftUpEdgeMap,
          kmswShiftFreshEdgeMap, kmswShiftLeftMismatchEdgeMap, hn, hn2]

private theorem hatNextVertexMap_old (sh gl : State) (step : Step)
    (vφ : ℕ → ℕ) (v : ℕ) (hv : v < sh.nextVertex) :
    kmswShiftNextVertexMap sh gl step vφ v = vφ v := by
  have hn : v ≠ sh.nextVertex := ne_of_lt hv
  cases step with
  | up => simp [kmswShiftNextVertexMap, kmswShiftUpVertexMap, hn]
  | down =>
      cases hs : sh.UR <;> cases hg : gl.UR <;>
        simp [kmswShiftNextVertexMap, hs, hg, kmswShiftUpVertexMap,
          kmswShiftDownMismatchVertexMap, hn]
  | left =>
      cases hs : sh.UL.dropLast.reverse <;> cases hg : gl.UL.dropLast.reverse <;>
        simp [kmswShiftNextVertexMap, hs, hg, kmswShiftUpVertexMap,
          kmswShiftLeftMismatchVertexMap, hn]

private theorem hatExcursionEdgeMap_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k e : ℕ) (he : e < (kmswStage w (walkNL w h k - 1)).nextEdge) :
    hatExcursionEdgeMap w h k e = e := by
  unfold hatExcursionEdgeMap
  split
  · simp [kmswShiftFreshEdgeMap, ne_of_lt he]
  · rfl

private theorem hatExcursionVertexMap_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k v : ℕ) (hv : v < (kmswStage w (walkNL w h k - 1)).nextVertex) :
    hatExcursionVertexMap w h k v = v := by
  unfold hatExcursionVertexMap
  split
  · simp [kmswShiftUpVertexMap, ne_of_lt hv]
  · rfl

/-- Existing edge images remain unchanged at the next local stage, including -/
theorem hatAllEdgeMap_extend (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m e : ℕ)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    hatAllEdgeMap w h (m + 1) e = hatAllEdgeMap w h m e := by
  classical
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    rw [hatAllEdgeMap_exit, Function.comp_apply, hatNextEdgeMap_old _ _ _ _ _ he]
    apply hatExcursionEdgeMap_old
    have hb := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.edge_bound e he
    rwa [quadrantRStageTime_hatExitIndex] at hb
  · simp only [hatAllEdgeMap, dif_neg hex]
    exact hatNextEdgeMap_old _ _ _ _ _ he

/-- Existing vertex images remain unchanged at the next local stage,
including exits (`lem-quad-kmsw`, -/
theorem hatAllVertexMap_extend (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m v : ℕ)
    (hv : v < (kmswStage (hatCodes w h) m).nextVertex) :
    hatAllVertexMap w h (m + 1) v = hatAllVertexMap w h m v := by
  classical
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    rw [hatAllVertexMap_exit, Function.comp_apply, hatNextVertexMap_old _ _ _ _ _ hv]
    apply hatExcursionVertexMap_old
    have hb := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.vertex_bound v hv
    rwa [quadrantRStageTime_hatExitIndex] at hb
  · simp only [hatAllVertexMap, dif_neg hex]
    exact hatNextVertexMap_old _ _ _ _ _ hv

/-- Existing edge images agree at every later local stage -/
theorem hatAllEdgeMap_eq_of_le (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m n e : ℕ) (hmn : m ≤ n)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    hatAllEdgeMap w h n e = hatAllEdgeMap w h m e := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact (hatAllEdgeMap_extend w h n e
        (he.trans_le (kmswStage_nextEdge_mono (hatCodes w h) hmn))).trans ih

/-- Existing vertex images agree at every later local stage -/
theorem hatAllVertexMap_eq_of_le (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m n v : ℕ) (hmn : m ≤ n)
    (hv : v < (kmswStage (hatCodes w h) m).nextVertex) :
    hatAllVertexMap w h n v = hatAllVertexMap w h m v := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact (hatAllVertexMap_extend w h n v
        (hv.trans_le (CutConverse.nextVertex_mono (hatCodes w h) hmn))).trans ih

private theorem hatAll_reachable_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) :
    e ∈ stageReachablePresentEdges w (quadrantRStageTime w h m) ↔
      ∃ j ≤ m, e = act w (quadrantRStageTime w h j) := by
  rw [← quadrantRStagePresentEdgeMap_image_eq_reachable w h m]
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  constructor
  · rintro ⟨f, hf, hp, hmap⟩
    obtain ⟨j, hjm, hfj⟩ := stagePresent_exists_active u m f.val hf hp
    have hActPresent : EdgePresent u (act u j) :=
      ⟨j, act_lt_nextEdge u le_rfl, kmswStage_active_present u j⟩
    have hsub : f = ⟨act u j, hActPresent⟩ := Subtype.ext hfj
    have hmapActive : quadrantRStagePresentEdgeMap w h f =
        act w (quadrantRStageTime w h j) := by
      rw [hsub]
      exact quadrantRStagePresentEdgeMap_active w h j
    exact ⟨j, hjm, hmap.symm.trans hmapActive⟩
  · rintro ⟨j, hjm, he⟩
    have hb := act_lt_nextEdge u (le_rfl : j ≤ j)
    have hp := kmswStage_active_present u j
    have hs := present_mono u hb hp m hjm
    have hActPresent : EdgePresent u (act u j) := ⟨j, hb, hp⟩
    refine ⟨⟨act u j, hActPresent⟩, hs.1, hs.2, ?_⟩
    rw [quadrantRStagePresentEdgeMap_active]
    exact he.symm

/-- Every allocated present edge has an allocated present image with the
simulated endpoints (`lem-quad-kmsw`, -/
theorem hatAll_present (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m e : ℕ)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge)
    (hp : (kmswStage (hatCodes w h) m).present e = true) :
    hatAllEdgeMap w h m e < (kmswStage w (quadrantRStageTime w h m)).nextEdge ∧
      (kmswStage w (quadrantRStageTime w h m)).present (hatAllEdgeMap w h m e) = true ∧
      (kmswStage w (quadrantRStageTime w h m)).west (hatAllEdgeMap w h m e) =
        hatAllVertexMap w h m ((kmswStage (hatCodes w h) m).west e) ∧
      (kmswStage w (quadrantRStageTime w h m)).east (hatAllEdgeMap w h m e) =
        hatAllVertexMap w h m ((kmswStage (hatCodes w h) m).east e) := by
  have hs := (hatAll_sim w h m).incidenceSim
  exact ⟨hs.edge_bound e he, hs.present e he hp, hs.incidence e he⟩

/-- The stagewise edge image is exactly the reachable present part at the
canonical R time (`lem-quad-kmsw`, `eqn-quad-pre`, `lem-flow-line-times`,
image, with no face or rotation claim. -/
theorem hatAllEdgeMap_image_eq_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    {e | ∃ f, f < (kmswStage (hatCodes w h) m).nextEdge ∧
      (kmswStage (hatCodes w h) m).present f = true ∧
      hatAllEdgeMap w h m f = e} =
      stageReachablePresentEdges w (quadrantRStageTime w h m) := by
  ext e
  rw [hatAll_reachable_iff]
  constructor
  · rintro ⟨f, hf, hp, hmap⟩
    obtain ⟨j, hjm, hfj⟩ := stagePresent_exists_active (hatCodes w h) m f hf hp
    have hb := act_lt_nextEdge (hatCodes w h) (le_rfl : j ≤ j)
    have hcoh := hatAllEdgeMap_eq_of_le w h j m (act (hatCodes w h) j) hjm hb
    have hactive := (hatAll_sim w h j).incidenceSim.active
    change hatAllEdgeMap w h j (act (hatCodes w h) j) =
      act w (quadrantRStageTime w h j) at hactive
    refine ⟨j, hjm, ?_⟩
    rw [← hmap, hfj, hcoh, hactive]
  · rintro ⟨j, hjm, he⟩
    have hb := act_lt_nextEdge (hatCodes w h) (le_rfl : j ≤ j)
    have hp := kmswStage_active_present (hatCodes w h) j
    have hs := present_mono (hatCodes w h) hb hp m hjm
    refine ⟨act (hatCodes w h) j, hs.1, hs.2, ?_⟩
    rw [hatAllEdgeMap_eq_of_le w h j m _ hjm hb]
    have hactive := (hatAll_sim w h j).incidenceSim.active
    exact hactive.trans he.symm

end DirectedDistances.KMSW
