module

public import DirectedDistances.KMSW.PrimedSimCrossingInvariant
import DirectedDistances.KMSW.OutgoingInterval

/-! # Primed crossing entry transport

P2 helpers; not counted (`lem-quad-kmsw`, -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- P2 helper; not counted (`lem-quad-kmsw`, -/
theorem PrimedSimActive.crossing_after_base
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    primedIntervalBase (primedSimInput w) h (k + 1) < m + 1 :=
  sim.crossing_time.2.1

private theorem take_dropLast_of_le (xs : List ℕ) (p : ℕ)
    (hp : p ≤ xs.length - 1) : xs.dropLast.take p = xs.take p := by
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hp]

private theorem hat_protected_prefix_step (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m p : ℕ)
    (hb : p + hatPhaseDepth w (quadrantRStageTime w h m) + 1 ≤
      (kmswStage (hatCodes w h) m).UL.length) :
    (kmswStage (hatCodes w h) (m + 1)).UL.take p =
        (kmswStage (hatCodes w h) m).UL.take p ∧
      p + hatPhaseDepth w (quadrantRStageTime w h (m + 1)) + 1 ≤
        (kmswStage (hatCodes w h) (m + 1)).UL.length := by
  classical
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    have ht : quadrantRStageTime w h (hatExitIndex w h k + 1) =
        walkNR w h (k + 1) := by
      rw [← hatCodeTime_succ, hatCodeTime_at_exit]
      have hr := (walkNR_succ_spec w h k).1
      omega
    rw [ht, hatPhaseDepth_at_walkNR]
    rw [kmswStage, hatCodes_at_exit]
    cases hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hur,
        State.addEdge, List.length_append]
    all_goals omega
  · let n := quadrantRStageTime w h m
    have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
      rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hex]
    have hp := (quadrantRStageTime_spec w h m).1
    have hn := (quadrantRStageTime_spec w h (m + 1)).1
    rw [ht] at hn
    have hc : hatCodes w h m = w n := by
      rw [hatCodes, hatCodeTime_of_not_exit w h m hex]
    have hd := hatPhaseDepth_step w n hp hn
    change p + hatPhaseDepth w n + 1 ≤ _ at hb
    rw [ht, hd, kmswStage, hc]
    generalize hw : w n = c at *
    fin_cases c
    · have hpos : hatPhaseDepth w n ≠ 0 := by
        intro hz
        have he := (hatPhaseDepth_left_exit_iff w n hp hw).2 hz
        rw [hn] at he
        contradiction
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last (hatCodes w h) m
      have hlen : 2 ≤ xs.length + 1 := by
        rw [hxs, List.length_append, List.length_singleton] at hb
        omega
      cases hpred : xs.reverse with
      | nil =>
        have := congrArg List.length hpred
        simp only [List.length_reverse, List.length_nil] at this
        omega
      | cons a as =>
        have hx : xs = as.reverse ++ [a] := by
          simpa only [List.reverse_reverse, List.reverse_cons] using
            congrArg List.reverse hpred
        have hpre : (kmswStage (hatCodes w h) m).UL.dropLast.reverse = a :: as := by
          rw [hxs, List.dropLast_concat, hpred]
        have hpb : p ≤ as.reverse.length := by
          rw [hxs, hx] at hb
          simp only [List.length_append, List.length_singleton, List.length_reverse] at hb
          simp only [List.length_reverse]
          omega
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hpre,
          List.length_append, List.length_reverse]
        constructor
        · rw [hxs, hx, List.append_assoc,
            List.take_append_of_le_length hpb, List.take_append_of_le_length hpb]
        · rw [hxs, hx] at hb
          simp only [List.length_append, List.length_singleton, List.length_reverse] at hb
          omega
    · simp [kmswStep, kmswCodeStep, kmswStepOfStep,
        List.length_append, List.length_dropLast]
      refine ⟨?_, by omega⟩
      rw [List.take_append_of_le_length (by simp only [List.length_dropLast]; omega),
        take_dropLast_of_le _ p (by omega)]
    · cases hur : (kmswStage (hatCodes w h) m).UR <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hur,
          State.addEdge, List.length_append]
      all_goals exact ⟨by omega, by omega⟩

private theorem hat_exit_prefix_persistent (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k b : ℕ) (hab : hatExitIndex w h k + 1 ≤ b) :
    let xs := (kmswStage (hatCodes w h) (hatExitIndex w h k)).UL
    (kmswStage (hatCodes w h) b).UL.take xs.length = xs ∧
      xs.length + hatPhaseDepth w (quadrantRStageTime w h b) + 1 ≤
        (kmswStage (hatCodes w h) b).UL.length := by
  dsimp only
  induction b, hab using Nat.le_induction with
  | base =>
    have ht : quadrantRStageTime w h (hatExitIndex w h k + 1) =
        walkNR w h (k + 1) := by
      rw [← hatCodeTime_succ, hatCodeTime_at_exit]
      have hr := (walkNR_succ_spec w h k).1
      omega
    rw [ht, hatPhaseDepth_at_walkNR, kmswStage, hatCodes_at_exit]
    cases hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
  | succ b hab ih =>
    have hs := hat_protected_prefix_step w h b _ ih.2
    exact ⟨hs.1.trans ih.1, hs.2⟩

/-- P2 helper; not counted (`lem-quad-kmsw`,
on the next candidate cut. The hatted replacement down step protects its
entire old UL prefix from subsequent left steps. -/
theorem cutAtExit_subset_succ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    ∀ e ∈ cutAtExit w h k, e ∈ cutAtExit w h (k + 1) := by
  have hab : hatExitIndex w h k + 1 ≤ hatExitIndex w h (k + 1) := by
    by_contra hn
    have hm := quadrantRStageTime_mono w h (show
      hatExitIndex w h (k + 1) ≤ hatExitIndex w h k by omega)
    rw [quadrantRStageTime_hatExitIndex, quadrantRStageTime_hatExitIndex] at hm
    have h0 := (walkNL_spec w h k).1
    have h1 := (walkNR_succ_spec w h k).1
    have h2 := (walkNL_spec w h (k + 1)).1
    omega
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hb := (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h)
    (hatExitIndex w h k)).2 f (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hf)))
  have hp := (hat_exit_prefix_persistent w h k (hatExitIndex w h (k + 1)) hab).1
  have hf' : f ∈ (kmswStage (hatCodes w h) (hatExitIndex w h (k + 1))).UL := by
    rw [← hp] at hf
    exact List.mem_of_mem_take hf
  apply List.mem_map.mpr
  refine ⟨f, hf', ?_⟩
  exact hatAllEdgeMap_eq_of_le w h _ _ f (by omega) hb

private theorem entry_local_UR_bounds (u : ℕ → Fin 3) (m e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR) :
    e < (kmswMissingRootStage u m).nextEdge ∧
      (kmswMissingRootStage u m).west e < (kmswMissingRootStage u m).nextVertex := by
  obtain ⟨hv, hE, hw, _, _, _, _, _, hUR, _, _⟩ := kmswMissingRootStage_agree u m
  have hb : e < (kmswStage u m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (hUR ▸ he))))
  refine ⟨hE.symm ▸ hb, ?_⟩
  rw [hw, hv]
  exact (kmswStage_endpoints_lt_nextVertex u m e hb).1

/-- P2 helper; not counted (`lem-quad-kmsw`,
vertices keep their images, old cut sides stay in the next cut, and the
fresh missing side maps to the terminal edge of that next cut. -/
theorem primedURUnreachableOrCut_crossing
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    PrimedURUnreachableOrCut u w h (k + 1) (m + 1)
      (primedCrossingEdgeMap sh gl eφ) (primedCrossingVertexMap sh gl vφ) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  dsimp only
  intro e he
  have hcases : e = sh.nextEdge + 1 ∨ e ∈ sh.UR := by
    simpa only [hl, kmswStepOfStep, List.mem_cons] using he
  rcases hcases with rfl | heold
  · exact Or.inr (primedCrossing_new_missing_mem_cut w h k sh eφ)
  · obtain ⟨hb, hv⟩ := entry_local_UR_bounds u m e heold
    change e < sh.nextEdge at hb
    change sh.west e < sh.nextVertex at hv
    have hext := primedCrossing_maps_extend sh gl eφ vφ
    have hwest : (kmswMissingRootStage u (m + 1)).west e = sh.west e := by
      simp [hl, kmswStepOfStep, State.addEdge, ne_of_lt hb,
        show e ≠ sh.nextEdge + 1 from by omega]
    change (¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨primedCrossingVertexMap sh gl vφ
        ((kmswMissingRootStage u (m + 1)).west e)⟩) ∨ _
    rw [hwest, hext.2 _ hv, hext.1 e hb]
    exact (hinv e heold).imp_right (cutAtExit_subset_succ w h k (eφ e))

private theorem entry_UR_or_present_later (w : ℕ → Fin 3) (a b e : ℕ)
    (hab : a ≤ b) (he : e ∈ (kmswStage w a).UR) :
    e ∈ (kmswStage w b).UR ∨ (kmswStage w b).present e = true := by
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w a).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr he)))
  induction b, hab using Nat.le_induction with
  | base => exact Or.inl he
  | succ b hab ih =>
    rcases ih with hu | hp
    · generalize hc : w b = c
      fin_cases c
      · left
        cases hpred : (kmswStage w b).UL.dropLast.reverse <;>
          simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
            kmswStepOfStep, hpred, State.addEdge] using hu
      · left
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
          kmswStepOfStep, State.addEdge, List.mem_cons] using Or.inr hu
      · cases hur : (kmswStage w b).UR with
        | nil => rw [hur] at hu; cases hu
        | cons f fs =>
          rw [hur] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · right
            simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur]
          · left
            simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
              kmswStepOfStep, hur] using hu
    · right
      exact (present_mono w (hbound.trans_le (kmswStage_nextEdge_mono w hab))
        hp (b + 1) (Nat.le_succ b)).2


private theorem entry_missing_bounds (u : ℕ → Fin 3) (m e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR ++ (kmswMissingRootStage u m).LL) :
    e < (kmswMissingRootStage u m).nextEdge ∧
      (kmswMissingRootStage u m).present e = false := by
  obtain ⟨_, hE, _, _, hp, _, _, _, hUR, hLL, _⟩ := kmswMissingRootStage_agree u m
  have hm : e ∈ (kmswStage u m).UR ++ (kmswStage u m).LL := by
    simpa only [hUR, hLL] using he
  have hb := (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
    simp only [List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact Or.inl (Or.inl (Or.inr hm))
    · exact Or.inl (Or.inr hm))
  refine ⟨hE.symm ▸ hb, ?_⟩
  by_cases hz : e = 0
  · subst e; exact kmswMissingRootStage_present_zero u m
  · rw [hp e hz]
    exact ((kmswStage_status u m).1 e hb).mpr (List.mem_append.mp hm)

private theorem entry_UR_transport
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m e : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hb : e < (kmswMissingRootStage u m).nextEdge)
    (hp : (kmswMissingRootStage u m).present e = false)
    (hn : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨vφ ((kmswMissingRootStage u m).west e)⟩)
    (he : eφ e ∈ (kmswStage w (walkNR w h (k + 1) - 1)).UR) :
    eφ e ∈ (kmswStage w (walkNL w h (k + 1))).UR := by
  let a := walkNR w h (k + 1) - 1
  let b := walkNL w h (k + 1) - 1
  have ht := (walkNL_spec w h (k + 1)).1
  have hr := (walkNR_succ_spec w h k).1
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hbound := sim.edge_bound e hb
  have hmissing := ((kmswStage_status w a).1 (eφ e) hbound).mpr (Or.inl he)
  have hur : eφ e ∈ (kmswStage w b).UR := by
    rcases entry_UR_or_present_later w a b (eφ e) hab he with hu | hpresent
    · exact hu
    obtain ⟨j, hj, hej⟩ := stagePresent_exists_active w b (eφ e)
      (hbound.trans_le (kmswStage_nextEdge_mono w hab)) hpresent
    have haj : a < j := by
      by_contra hnot
      have hpa := (present_mono w (act_lt_nextEdge w (le_refl j))
        (kmswStage_active_present w j) a (by omega)).2
      rw [← hej, hmissing] at hpa
      contradiction
    have hwr := flowLine_phase_reachable w h (k + 1) j (by dsimp [a] at haj; omega)
      (by dsimp [b] at hj; omega)
    have hjB := act_lt_nextEdge w (le_refl j)
    have hedges := edge_endpoints_eq w hjB
    obtain ⟨path⟩ := hwr
    let arrow : (⟨(kmswStage w j).west (act w j)⟩ : PresentVertex w) ⟶
        ⟨(kmswStage w j).east (act w j)⟩ :=
      ⟨act w j, ⟨j, hjB, kmswStage_active_present w j⟩,
        hedges.1.symm, hedges.2.symm⟩
    have hi := sim.missing_incidence e hb hp
    have hs := edge_endpoints_eq w hbound
    have hm : vφ ((kmswMissingRootStage u m).west e) ∈
        ({edgeWest w (eφ e), edgeEast w (eφ e)} : Multiset ℕ) := by
      rw [← hs.1, ← hs.2, hi]
      exact Multiset.mem_cons_self _ _
    have hm' : vφ ((kmswMissingRootStage u m).west e) = edgeWest w (eφ e) ∨
        vφ ((kmswMissingRootStage u m).west e) = edgeEast w (eφ e) := by
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hm
    apply False.elim
    apply hn
    rcases hm' with hw | hw
    · rw [hw, hej, ← hedges.1]
      exact ⟨path⟩
    · rw [hw, hej, ← hedges.2]
      exact ⟨path.cons arrow⟩
  have hidx : b + 1 = walkNL w h (k + 1) := by dsimp [b]; omega
  rw [← hidx, kmswStage, walkNL_previous_code w h (k + 1)]
  cases hpred : (kmswStage w b).UL.dropLast.reverse <;>
    simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hpred, State.addEdge] using hur

private theorem entry_local_active_present
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    (kmswMissingRootStage u m).present (kmswMissingRootStage u m).active = true := by
  have hne : (kmswMissingRootStage u m).active ≠ 0 := by
    intro hz
    have ha := sim.active_alignment
    rw [hz] at ha
    have hp := kmswStage_active_present w n
    change (kmswStage w n).present (kmswStage w n).active = true at hp
    rw [← ha, sim.missing_root.2.1] at hp
    cases hp
  obtain ⟨_, _, _, _, hp, _, ha, _⟩ := kmswMissingRootStage_agree u m
  rw [hp _ hne, ha]
  exact kmswStage_active_present u m


private theorem entry_LR_mono (w : ℕ → Fin 3) {a b e : ℕ}
    (hab : a ≤ b) (he : e ∈ (kmswStage w a).LR) : e ∈ (kmswStage w b).LR := by
  induction b, hab using Nat.le_induction with
  | base => exact he
  | succ b _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w b
    rw [ht]
    exact List.mem_append_left _ ih

/-- P2 helper; not counted (`lem-quad-kmsw`,
map into the new global frontier or the next candidate cut. -/
theorem PrimedSimActive.crossing_old_missing_frontier
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) :
    ∀ e ∈ (kmswMissingRootStage u m).UR ++ (kmswMissingRootStage u m).LL,
      eφ e ∈ primedGlobalFrontier (kmswStage w (walkNL w h (k + 1))) ∨
        eφ e ∈ cutAtExit w h (k + 1) := by
  intro e he
  obtain ⟨hb, hp⟩ := entry_missing_bounds u m e he
  have ht := (walkNL_spec w h (k + 1)).1
  have hab : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) := by omega
  have hn : (¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨vφ ((kmswMissingRootStage u m).west e)⟩) ∨ eφ e ∈ cutAtExit w h k := by
    rcases List.mem_append.mp he with hu | hl
    · exact hinv e hu
    · exact Or.inl (sim.LL_west_unreachable e hl)
  rcases hn with hn | hc
  · have hfront := sim.boundary_image e (by
      simp only [List.mem_append] at he ⊢
      rcases he with he | he
      · exact Or.inl (Or.inl (Or.inr he))
      · exact Or.inl (Or.inr he))
    rcases hfront with hf | hc
    · left
      simp only [primedGlobalFrontier, List.mem_append] at hf ⊢
      rcases hf with hu | hur | hll | hlr
      · have ha : (kmswMissingRootStage u m).active <
            (kmswMissingRootStage u m).nextEdge := by
          obtain ⟨_, hE, _, _, _, _, hA, _⟩ := kmswMissingRootStage_agree u m
          rw [hA, hE]
          exact (kmswStage_boundary_ids_lt_nextEdge u m).1
        have hne : eφ e ≠ (kmswStage w (walkNR w h (k + 1) - 1)).active := by
          intro heq
          have hei := sim.edge_injective e _ hb ha (heq.trans sim.active_alignment.symm)
          have hpa := entry_local_active_present sim
          rw [← hei, hp] at hpa
          contradiction
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last w (walkNR w h (k + 1) - 1)
        have hu' : eφ e ∈ (kmswStage w (walkNR w h (k + 1) - 1)).UL.dropLast := by
          rw [hxs, List.dropLast_concat]
          rw [hxs] at hu
          exact (List.mem_append.mp hu).resolve_right (by
            simpa only [List.mem_singleton] using hne)
        exact Or.inl (by
          rw [primedCrossing_UL]
          exact List.mem_append_left _ hu')
      · exact Or.inr (Or.inl (entry_UR_transport sim hb hp hn hur))
      · exact Or.inr (Or.inr (Or.inl (primedCrossing_LL_persistent w hab hll).1))
      · exact Or.inr (Or.inr (Or.inr (entry_LR_mono w hab hlr)))
    · exact Or.inr (cutAtExit_subset_succ w h k _ hc)
  · exact Or.inr (cutAtExit_subset_succ w h k _ hc)

/-- P2 helper; not counted (`lem-quad-kmsw`,
survives crossing, including old missing sides and the fresh cut side. -/
theorem PrimedSimActiveRootLR.crossing_boundary_image
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    ∀ e, e ∈ (kmswMissingRootStage u (m + 1)).UL ++
        (kmswMissingRootStage u (m + 1)).UR ++
        (kmswMissingRootStage u (m + 1)).LL ++
        (kmswMissingRootStage u (m + 1)).LR →
      eψ e ∈ primedGlobalFrontier (kmswStage w (walkNL w h (k + 1))) ∨
        eψ e ∈ cutAtExit w h (k + 1) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  dsimp only
  intro e he
  simp only [List.mem_append] at he
  rcases he with ((hul | hur) | hll) | hlr
  · exact Or.inl (sim.crossing_UL_LR_boundary_image hu e
      (List.mem_append_left _ hul))
  · have hc : e = sh.nextEdge + 1 ∨ e ∈ sh.UR := by
      simpa only [hl, kmswStepOfStep, List.mem_cons] using hur
    rcases hc with rfl | hold
    · exact Or.inr (primedCrossing_new_missing_mem_cut w h k sh eφ)
    · have hm := List.mem_append_left sh.LL hold
      have hb := (entry_missing_bounds u m e hm).1
      rw [(primedCrossing_maps_extend sh gl eφ vφ).1 e hb]
      exact sim.forget.crossing_old_missing_frontier hinv e hm
  · have hold : e ∈ sh.LL := by
      simpa only [hl, kmswStepOfStep, State.addEdge] using hll
    have hm := List.mem_append_right sh.UR hold
    have hb := (entry_missing_bounds u m e hm).1
    rw [(primedCrossing_maps_extend sh gl eφ vφ).1 e hb]
    exact sim.forget.crossing_old_missing_frontier hinv e hm
  · exact Or.inl (sim.crossing_UL_LR_boundary_image hu e
      (List.mem_append_right _ hlr))

/-- P2 helper; not counted (`lem-quad-kmsw`, -/
theorem PrimedSimActive.crossing_time_alignment
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    walkNL w h (k + 1) = primedIntervalLeft (primedSimInput w) h (k + 1) +
      (m + 1 - primedIntervalBase (primedSimInput w) h (k + 1)) - 1 :=
  sim.crossing_time.2.2

/-- P2 helper; not counted (`lem-quad-kmsw`,
simulation survives a replacement crossing, using the cut-exempt UR
invariant for allocation separation and old frontier transport. This does
not assert the ordered planar identification required by the paper lemma. -/
theorem PrimedSimActiveRootLR.crossing
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    let vψ := primedCrossingVertexMap sh gl vφ
    PrimedSimActiveRootLR u w h (k + 1) (m + 1)
      (walkNL w h (k + 1)) eψ vψ := by
  dsimp only
  have hb := sim.forget.crossing_bounds hu
  have hi := sim.crossing_injective_of_unreachableOrCut hinv hu
  have hc := sim.forget.crossing_incidence hu
  have ha := sim.forget.crossing_active_UL hu
  obtain ⟨xs, ys, zs, _, hUR⟩ := primedCrossing_UR_restart u w h k (m + 1)
    (primedCrossingEdgeMap (kmswMissingRootStage u m)
      (kmswStage w (walkNL w h (k + 1) - 1)) eφ)
    (primedCrossingVertexMap (kmswMissingRootStage u m)
      (kmswStage w (walkNL w h (k + 1) - 1)) vφ)
  exact {
    edge_bound := hb.1
    edge_injective := hi.1
    vertex_bound := hb.2
    vertex_injective := hi.2
    present_incidence := hc.1
    missing_incidence := hc.2
    present_complement := sim.forget.crossing_present_complement hu
    missing_root := sim.forget.crossing_missing_root
    triangle_incidence := sim.forget.crossing_triangles hu
    boundary_image := sim.crossing_boundary_image hinv hu
    after_base := sim.forget.crossing_after_base
    time_alignment := sim.forget.crossing_time_alignment
    active_alignment := ha.1
    UL_alignment := ha.2
    UR_alignment := ⟨xs, ys, zs, hUR⟩
    LR_root := sim.crossing_LR_root hu }

end DirectedDistances.KMSW
