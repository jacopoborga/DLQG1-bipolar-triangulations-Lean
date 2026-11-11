module

public import DirectedDistances.PaperProofs.Section5.QuadrantWalk
public import DirectedDistances.PaperProofs.Section5.HatRootActive
public import DirectedDistances.PaperProofs.Section3.KMSWBdy
public import DirectedDistances.KMSW.HatBoundaryFacts
public import DirectedDistances.KMSW.UIBOTBoundaryM0

/-! # Selected-time facts toward the Boltzmann hit coupling

Helpers toward Lemmas 7.10-7.13 (eqn-hit-coupling); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.RandomWalk
open Quiver
open scoped Classical



theorem sourceQuadrantS_count (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : 1 ≤ m) :
    Nat.count (sourceQuadrantHatTime w) (sourceQuadrantS w h m + 1) = m := by
  exact (sourceQuadrantS_isLeast_count w h hm).1



theorem sourceQuadrantS_strictMono (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    StrictMono (sourceQuadrantS w h) := by
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    have hn : 1 ≤ n := by omega
    have hcount := sourceQuadrantS_count w h hn
    have hpos : 1 ≤ sourceQuadrantS w h n := by
      by_contra hnot
      have hz : sourceQuadrantS w h n = 0 := by omega
      have hc0 : Nat.count (sourceQuadrantHatTime w) 1 = 0 := by
        rw [Nat.count_succ]
        simp [sourceQuadrantHatTime]
      rw [hz, hc0] at hcount
      omega
    rw [sourceQuadrantS_zero]
    omega
  · have hmpos : 1 ≤ m := by omega
    have hnpos : 1 ≤ n := by omega
    have hcm := sourceQuadrantS_count w h hmpos
    have hcn := sourceQuadrantS_count w h hnpos
    by_contra hlt
    have hge : sourceQuadrantS w h n ≤ sourceQuadrantS w h m := by omega
    have hmono := Nat.count_monotone (p := sourceQuadrantHatTime w)
      (Nat.add_le_add_right hge 1)
    rw [hcn, hcm] at hmono
    omega




theorem sourceQuadrantS_le_of_count (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m n : ℕ} (hm : 1 ≤ m)
    (hn : Nat.count (sourceQuadrantHatTime w) (n + 1) = m) :
    sourceQuadrantS w h m ≤ n := by
  have hleast := sourceQuadrantS_isLeast_count w h hm
  exact hleast.2
    (by change Nat.count (sourceQuadrantHatTime w) (n + 1) = m; exact hn)




theorem sourceQuadrantS_eq_of_selected_count (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m n : ℕ} (hm : 1 ≤ m)
    (hp : sourceQuadrantHatTime w n)
    (hc : Nat.count (sourceQuadrantHatTime w) (n + 1) = m) :
    sourceQuadrantS w h m = n := by
  have hle := sourceQuadrantS_le_of_count w h hm hc
  by_contra hne
  have hlt : sourceQuadrantS w h m < n := by omega
  have hcount := sourceQuadrantS_count w h hm
  have hmono : Nat.count (sourceQuadrantHatTime w)
      (sourceQuadrantS w h m + 1) ≤ Nat.count (sourceQuadrantHatTime w) n :=
    Nat.count_monotone (p := sourceQuadrantHatTime w) (by omega)
  have hstep : Nat.count (sourceQuadrantHatTime w) n <
      Nat.count (sourceQuadrantHatTime w) (n + 1) := by
    rw [Nat.count_succ]
    simp [hp]
  rw [hcount] at hmono
  rw [hc] at hstep
  omega

private theorem sourceBoundaryHit_selected (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) {r : ℕ} (hr : 1 ≤ r) :
    sourceQuadrantHatTime w (boundaryHitTime w hb (r : ℤ)) := by
  let t := boundaryHitTime w hb (r : ℤ)
  have hhit : R w t = -(r : ℤ) := by
    exact boundaryHitTime_right_spec w hb (by exact_mod_cast hr)
  have htpos : 1 ≤ t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    rw [ht0] at hhit
    simp [R] at hhit
    omega
  have hrZ : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast (show 0 ≤ r by omega)
  have hreach := boundaryVertex_nonneg_reachable w hb
    (k := 0) (l := (r : ℤ)) (by norm_num) hrZ
  rw [boundaryVertex_zero] at hreach
  rw [boundaryVertex_right_hit_eq w hb (by exact_mod_cast hr),
    CutConverse.activeInitial_eq w t] at hreach
  change 1 ≤ t ∧ sourceLambdaInMhat w t
  refine ⟨htpos, ?_⟩
  change Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w t).west (act w t)⟩ ∧ _
  exact ⟨hreach, kmswStage_activeEast_reachable w t hreach⟩




theorem sourceQuadrantHatWalk_increment (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : 1 ≤ m) :
    sourceQuadrantHatWalk w h m - sourceQuadrantHatWalk w h (m - 1) =
      integrateCodes w (sourceQuadrantS w h m) -
        integrateCodes w (sourceQuadrantS w h m - 1) := by
  cases m with
  | zero => omega
  | succ k =>
      simp only [sourceQuadrantHatWalk, Nat.succ_sub_one]
      rw [Finset.sum_range_succ]
      exact add_sub_cancel_left _ _

private theorem hitCoupling_R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 := by
  simp only [R, Finset.sum_range_succ]




theorem sourceHatR_eq_original_at_S (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    R (hatCodes w h) m = R w (sourceQuadrantS w h m) := by
  have hglobal : ∀ m, R (hatCodes w h) m = R w (quadrantRStageTime w h m) := by
    intro m
    induction m with
    | zero =>
        have htime : quadrantRStageTime w h 0 = 0 :=
          quadrantRStageTime_eq_of_initial_R w h (by
            have hp := (walkNL_spec w h 0).1
            rw [walkNR_zero] at hp
            omega)
        simp [R, htime]
    | succ m ih =>
        rw [hitCoupling_R_succ, ih]
        by_cases hex : ∃ k, hatExitIndex w h k = m
        · obtain ⟨k, rfl⟩ := hex
          have htime0 : quadrantRStageTime w h (hatExitIndex w h k) =
              walkNL w h k - 1 := quadrantRStageTime_hatExitIndex w h k
          have htime1 : quadrantRStageTime w h (hatExitIndex w h k + 1) =
              walkNR w h (k + 1) := by
            rw [← hatCodeTime_succ, hatCodeTime_at_exit]
            have hp := (walkNR_succ_spec w h k).1
            omega
          have hleft : R w (walkNL w h k) = R w (walkNL w h k - 1) := by
            have hi : walkNL w h k - 1 + 1 = walkNL w h k := by
              have hp := (walkNL_spec w h k).1
              omega
            rw [← hi, hitCoupling_R_succ]
            rw [walkNL_previous_code w h k]
            simp [lazyTwoDimensionalStep]
          have hdrop : R w (walkNR w h (k + 1)) =
              R w (walkNL w h k - 1) - 1 := by
            rw [(walkNR_succ_spec w h k).2, hleft]
          rw [htime0, htime1, hatCodes_at_exit]
          change R w (walkNL w h k - 1) +
              (lazyTwoDimensionalStep (2 : Fin 3)).2 =
            R w (walkNR w h (k + 1))
          rw [hdrop]
          rfl
        · have hnot : ¬ ∃ k, hatExitIndex w h k = m := hex
          have htimeCode : hatCodeTime w h m = quadrantRStageTime w h m :=
            hatCodeTime_of_not_exit w h m hnot
          have htimeNext : quadrantRStageTime w h (m + 1) =
              quadrantRStageTime w h m + 1 := by
            rw [← hatCodeTime_succ, htimeCode]
          have hcode : hatCodes w h m = w (quadrantRStageTime w h m) := by
            rw [hatCodes, htimeCode]
          rw [htimeNext, hcode, hitCoupling_R_succ]
  rw [← quadrantRStageTime_eq_sourceQuadrantS w h m]
  exact hglobal m




theorem hattedRightHit_exists (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n, R (hatCodes w h) n = -(r : ℤ) := by
  obtain ⟨N, hN⟩ := hat_R_unbounded_hatted w h (-(r : ℤ))
  let H : ∃ n, R (hatCodes w h) n ≤ -(r : ℤ) := ⟨N, hN⟩
  let n := Nat.find H
  have hnle : R (hatCodes w h) n ≤ -(r : ℤ) := Nat.find_spec H
  have hnpos : n ≠ 0 := by
    intro hn0
    rw [hn0] at hnle
    simp [R] at hnle
    omega
  let p := n - 1
  have hidx : p + 1 = n := by dsimp [p]; omega
  have hpLt : p < n := by omega
  have hpNot : ¬ R (hatCodes w h) p ≤ -(r : ℤ) := Nat.find_min H hpLt
  have hpGt : -(r : ℤ) < R (hatCodes w h) p := by omega
  have hstep := hitCoupling_R_succ (hatCodes w h) p
  have hstepLower : (-1 : ℤ) ≤ (lazyTwoDimensionalStep (hatCodes w h p)).2 := by
    generalize hc : hatCodes w h p = c
    fin_cases c <;> simp [lazyTwoDimensionalStep]
  have hnle' : R (hatCodes w h) (p + 1) ≤ -(r : ℤ) := by
    rw [hidx]
    exact hnle
  have heq : R (hatCodes w h) (p + 1) = -(r : ℤ) := by
    rw [hstep] at hnle'
    omega
  refine ⟨n, ?_⟩
  rw [← hidx]
  exact heq




@[expose] noncomputable def hattedRightHitTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (r : ℕ) (hr : 1 ≤ r) : ℕ :=
  Nat.find (hattedRightHit_exists w h r hr)



theorem hattedRightHitTime_spec (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (r : ℕ) (hr : 1 ≤ r) :
    R (hatCodes w h) (hattedRightHitTime w h r hr) = -(r : ℤ) :=
  Nat.find_spec (hattedRightHit_exists w h r hr)




theorem sourceHitTime_eq_selector_hattedRightHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) :
    boundaryHitTime w hb (r : ℤ) =
      sourceQuadrantS w h (hattedRightHitTime w h r hr) := by
  let τ := boundaryHitTime w hb (r : ℤ)
  let m := Nat.count (sourceQuadrantHatTime w) (τ + 1)
  let q := hattedRightHitTime w h r hr
  let t := sourceQuadrantS w h q
  have hsel : sourceQuadrantHatTime w τ := by
    simpa [τ] using sourceBoundaryHit_selected w hb hr
  have hmpos : 1 ≤ m := by
    dsimp [m]
    rw [Nat.count_succ]
    simp [hsel]
  have hcount : Nat.count (sourceQuadrantHatTime w) (τ + 1) = m := rfl
  have hSτ : sourceQuadrantS w h m = τ :=
    sourceQuadrantS_eq_of_selected_count w h hmpos hsel hcount
  have hSq : sourceQuadrantS w h q = t := rfl
  have hhitHat : R (hatCodes w h) q = -(r : ℤ) := by
    exact hattedRightHitTime_spec w h r hr
  have hhitOrigAtT : R w t = -(r : ℤ) := by
    calc
      R w t = R w (sourceQuadrantS w h q) := by rw [hSq]
      _ = R (hatCodes w h) q := (sourceHatR_eq_original_at_S w h q).symm
      _ = -(r : ℤ) := hhitHat
  have hrZ : 1 ≤ (r : ℤ) := by exact_mod_cast hr
  have hdef : τ = Nat.find (hb.rightHit (r : ℤ) hrZ) := by
    dsimp [τ, boundaryHitTime]
    simp only [dite_eq_right (by omega : (r : ℤ) ≠ 0),
      dite_eq_left (by omega : 0 < (r : ℤ))]
  have hle : τ ≤ t := by
    rw [hdef]
    exact Nat.find_min' _ hhitOrigAtT
  by_contra hne
  change τ ≠ t at hne
  have hlt : τ < t := by omega
  have hmq : m < q := by
    by_contra hnot
    have hqm : q ≤ m := by omega
    have hmono := (sourceQuadrantS_strictMono w h).monotone hqm
    rw [hSq, hSτ] at hmono
    omega
  have hhitHatEarlier : R (hatCodes w h) m = -(r : ℤ) := by
    calc
      R (hatCodes w h) m = R w (sourceQuadrantS w h m) :=
        sourceHatR_eq_original_at_S w h m
      _ = R w τ := by rw [hSτ]
      _ = -(r : ℤ) := boundaryHitTime_right_spec w hb hrZ
  have hfind : m < Nat.find (hattedRightHit_exists w h r hr) := by
    simpa [q, hattedRightHitTime] using hmq
  exact (Nat.find_min (hattedRightHit_exists w h r hr) hfind) hhitHatEarlier




private theorem hattedActiveInitial_maps_to_source (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    hatLimitVertexMap w h (activeInitial (hatCodes w h) m) =
      activeInitial w (sourceQuadrantS w h m) := by
  have hact : act (hatCodes w h) m < (kmswStage (hatCodes w h) m).nextEdge :=
    act_lt_nextEdge (hatCodes w h) (Nat.le_refl m)
  have hvertex : activeInitial (hatCodes w h) m <
      (kmswStage (hatCodes w h) m).nextVertex := by
    rw [CutConverse.activeInitial_eq]
    exact (kmswStage_endpoints_lt_nextVertex (hatCodes w h) m
      (act (hatCodes w h) m) hact).1
  have hpresent := hatAll_present w h m (act (hatCodes w h) m) hact
    (kmswStage_active_present (hatCodes w h) m)
  have hedge : hatAllEdgeMap w h m (act (hatCodes w h) m) =
      act w (sourceQuadrantS w h m) := by
    calc
      hatAllEdgeMap w h m (act (hatCodes w h) m) =
          act w (quadrantRStageTime w h m) := by
        simpa only [act] using hat_active_edge_stage_alignment w h m
      _ = act w (sourceQuadrantS w h m) := by
        rw [quadrantRStageTime_eq_sourceQuadrantS]
  calc
    hatLimitVertexMap w h (activeInitial (hatCodes w h) m) =
        hatAllVertexMap w h m (activeInitial (hatCodes w h) m) :=
      hatLimitVertexMap_eq_stage w h m _ hvertex
    _ = hatAllVertexMap w h m
          ((kmswStage (hatCodes w h) m).west (act (hatCodes w h) m)) := by
        rw [CutConverse.activeInitial_eq]
    _ = (kmswStage w (quadrantRStageTime w h m)).west
          (hatAllEdgeMap w h m (act (hatCodes w h) m)) :=
        hpresent.2.2.1.symm
    _ = (kmswStage w (quadrantRStageTime w h m)).west
          (act w (sourceQuadrantS w h m)) := by rw [hedge]
    _ = activeInitial w (sourceQuadrantS w h m) := by
      rw [quadrantRStageTime_eq_sourceQuadrantS]
      exact (CutConverse.activeInitial_eq w (sourceQuadrantS w h m)).symm





theorem hattedRightHitTime_isLeast_sourceVertex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) :
    IsLeast {m : ℕ |
      hatLimitVertexMap w h (activeInitial (hatCodes w h) m) =
        boundaryVertex w hb (r : ℤ)}
      (hattedRightHitTime w h r hr) := by
  let q := hattedRightHitTime w h r hr
  have hτq := sourceHitTime_eq_selector_hattedRightHit w h hb r hr
  have hq : hatLimitVertexMap w h (activeInitial (hatCodes w h) q) =
      boundaryVertex w hb (r : ℤ) := by
    rw [hattedActiveInitial_maps_to_source, ← hτq]
    exact (boundaryVertex_right_hit_eq w hb (by exact_mod_cast hr)).symm
  refine ⟨hq, ?_⟩
  intro m hm
  by_contra hnot
  have hmq : m < q := by omega
  have hSmq : sourceQuadrantS w h m < sourceQuadrantS w h q :=
    (sourceQuadrantS_strictMono w h) hmq
  rw [← hτq] at hSmq
  have hm' : activeInitial w (sourceQuadrantS w h m) =
      boundaryVertex w hb (r : ℤ) := by
    rw [← hattedActiveInitial_maps_to_source]
    exact hm
  have hfirst := boundaryVertex_first_visit_right w hb
    (show (1 : ℤ) ≤ (r : ℤ) by exact_mod_cast hr)
  exact (hfirst (sourceQuadrantS w h m) hSmq) hm'.symm




theorem hattedRightVertexHit_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ m : ℕ,
      hatLimitVertexMap w h (activeInitial (hatCodes w h) m) =
        boundaryVertex w hb (r : ℤ) := by
  exact ⟨hattedRightHitTime w h r hr,
    (hattedRightHitTime_isLeast_sourceVertex w h hb r hr).1⟩




@[expose] noncomputable def hattedRightVertexHitTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) : ℕ :=
  Nat.find (hattedRightVertexHit_exists w h hb r hr)




theorem hattedRightVertexHitTime_eq_hattedRightHitTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) :
    hattedRightVertexHitTime w h hb r hr = hattedRightHitTime w h r hr := by
  apply le_antisymm
  · change Nat.find (hattedRightVertexHit_exists w h hb r hr) ≤ _
    exact Nat.find_min' (hattedRightVertexHit_exists w h hb r hr)
      ((hattedRightHitTime_isLeast_sourceVertex w h hb r hr).1)
  · change _ ≤ Nat.find (hattedRightVertexHit_exists w h hb r hr)
    exact (hattedRightHitTime_isLeast_sourceVertex w h hb r hr).2
      (Nat.find_spec (hattedRightVertexHit_exists w h hb r hr))




theorem sourceHitTime_eq_sourceHattedRightVertexHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r : ℕ) (hr : 1 ≤ r) :
    boundaryHitTime w hb (r : ℤ) =
      sourceQuadrantS w h (hattedRightVertexHitTime w h hb r hr) := by
  rw [hattedRightVertexHitTime_eq_hattedRightHitTime w h hb r hr]
  exact sourceHitTime_eq_selector_hattedRightHit w h hb r hr

end DirectedDistances.PaperProofs.Section7
