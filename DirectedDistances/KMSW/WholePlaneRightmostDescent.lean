module

public import DirectedDistances.KMSW.WholePlaneRightBoundary
public import DirectedDistances.KMSW.RightmostStability

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open scoped Classical

private def pendingEastFrontier (s : State) : List ℕ :=
  s.east s.active :: s.UR.map s.east

private theorem pendingEastFrontier_left (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      pendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = s.UR := by
    change (kmswStep s (w n)).UR = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hEast : t.east t.active = s.east s.active := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, hmap]

private theorem pendingEastFrontier_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      (kmswStage w n).nextVertex :: pendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
    change (kmswStep s (w n)).UR = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep]
  have hEast : t.east t.active = s.nextVertex := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hNewEast : t.east (s.nextEdge + 1) = s.east s.active := by
    change (kmswStep s (w n)).east (s.nextEdge + 1) = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.nextVertex :: s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, List.map_cons, hNewEast, hmap]

private theorem pendingEastFrontier_down_cons (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (e : ℕ) (es : List ℕ)
    (hUR : (kmswStage w n).UR = e :: es) :
    pendingEastFrontier (kmswStage w n) =
      (kmswStage w n).east (act w n) ::
        pendingEastFrontier (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change s.UR = e :: es at hUR
  have hEast : t.east t.active = s.east e := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = s.east e
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hUR' : t.UR = es := by
    change (kmswStep s (w n)).UR = es
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hmap : es.map t.east = es.map s.east := by
    apply List.map_congr_left
    intro f hf
    have hfmem : f ∈ s.UR := by rw [hUR]; simp [hf]
    have hfAll : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hfmem))
    have hfBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 f hfAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) hfBound).2
  change s.east s.active :: s.UR.map s.east =
    s.east s.active :: (t.east t.active :: t.UR.map t.east)
  rw [hUR, List.map_cons, hEast, hUR', hmap]

private theorem pendingEastFrontier_down_nil (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      [(kmswStage w n).nextVertex] := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change t.east t.active :: t.UR.map t.east = _
  simp [t, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc,
    hUR, State.addEdge]

private theorem pendingEastFrontier_balanced (w : ℕ → Fin 3) {t n : ℕ}
    (htn : t ≤ n)
    (habove : ∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) :
    ∃ p : List ℕ,
      pendingEastFrontier (kmswStage w n) =
        p ++ pendingEastFrontier (kmswStage w t) ∧
      (p.length : ℤ) = R w n - R w t := by
  have haux : ∀ n, t ≤ n →
      (∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) →
      ∃ p : List ℕ,
        pendingEastFrontier (kmswStage w n) =
          p ++ pendingEastFrontier (kmswStage w t) ∧
        (p.length : ℤ) = R w n - R w t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro htn hbound
        by_cases hEq : n = t
        · subst n
          refine ⟨[], ?_, ?_⟩
          · simp
          · simp [R]
        · have hnpos : 0 < n := by omega
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have htq : t ≤ q := by omega
          have hboundq : ∀ j, t ≤ j → j ≤ q → R w t ≤ R w j := by
            intro j hjt hjq
            exact hbound j hjt (by omega)
          obtain ⟨p, hp, hplen⟩ := ih q (by omega) htq hboundq
          have hpost : R w t ≤ R w (q + 1) := hbound (q + 1) (by omega) le_rfl
          have hRstep : R w (q + 1) = R w q +
              (RandomWalk.lazyTwoDimensionalStep (w q)).2 := Finset.sum_range_succ _ _
          by_cases hc0 : w q = 0
          · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 0 := by
              simp [hc0, RandomWalk.lazyTwoDimensionalStep]
            have hpending := pendingEastFrontier_left w q hc0
            refine ⟨p, ?_, ?_⟩
            · simpa [hRstep, hcode] using hpending.trans hp
            · rw [hRstep, hcode]
              omega
          · by_cases hc1 : w q = 1
            · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 1 := by
                simp [hc1, RandomWalk.lazyTwoDimensionalStep]
              have hpending := pendingEastFrontier_up w q hc1
              refine ⟨(kmswStage w q).nextVertex :: p, ?_, ?_⟩
              · rw [hpending, hp]
                simp [List.cons_append]
              · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                rw [hRstep, hcode]
                omega
            · have hc2 : w q = 2 := by
                apply Fin.ext
                have hval := (w q).isLt
                have hnot0 : (w q).val ≠ 0 := by
                  intro hv
                  exact hc0 (Fin.ext hv)
                have hnot1 : (w q).val ≠ 1 := by
                  intro hv
                  exact hc1 (Fin.ext hv)
                omega
              have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = -1 := by
                simp [hc2, RandomWalk.lazyTwoDimensionalStep]
              have hnet : 1 ≤ R w q - R w t := by
                rw [hRstep, hcode] at hpost
                omega
              have hpPos : 0 < p.length := by
                have : (0 : ℤ) < (p.length : ℤ) := by rw [hplen]; omega
                exact_mod_cast this
              have hpne : p ≠ [] := by
                intro he
                simp [he] at hpPos
              obtain ⟨a, ps, rfl⟩ := List.exists_cons_of_ne_nil hpne
              have hURne : (kmswStage w q).UR ≠ [] := by
                intro hUR
                have hlenOld : (pendingEastFrontier (kmswStage w q)).length = 1 := by
                  simp [pendingEastFrontier, hUR]
                have hbasePos : 0 <
                    (pendingEastFrontier (kmswStage w t)).length := by
                  simp [pendingEastFrontier]
                rw [hp] at hlenOld
                simp only [List.length_append, List.length_cons] at hlenOld
                omega
              obtain ⟨e, es, hUR⟩ : ∃ e es, (kmswStage w q).UR = e :: es := by
                cases h : (kmswStage w q).UR with
                | nil => exact (hURne h).elim
                | cons e es => exact ⟨e, es, rfl⟩
              have hpop := pendingEastFrontier_down_cons w q hc2 e es hUR
              have htail : ps ++ pendingEastFrontier (kmswStage w t) =
                  pendingEastFrontier (kmswStage w (q + 1)) := by
                have hcons : a :: (ps ++ pendingEastFrontier (kmswStage w t)) =
                    (kmswStage w q).east (act w q) ::
                      pendingEastFrontier (kmswStage w (q + 1)) := by
                  simpa [List.cons_append] using hp.symm.trans hpop
                exact congrArg List.tail hcons
              refine ⟨ps, htail.symm, ?_⟩
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hplen
              rw [hRstep, hcode]
              omega
  exact haux n htn habove


private theorem coord_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem coord_lower (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  rw [coord_succ]
  have hc : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    generalize w n = c
    fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
  omega

private theorem active_present (w : ℕ → Fin 3) (m : ℕ) :
    (kmswStage w m).present (act w m) = true := by
  apply (kmswStage_status w m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem first_descent (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∃ q, t ≤ q ∧ w q = 2 ∧ R w q = R w t ∧
      R w (q + 1) = R w t - 1 ∧
      (∀ s, t ≤ s → s ≤ q → R w t ≤ R w s) := by
  obtain ⟨n, hn⟩ := hR (minR w t - 1)
  have hnt : t < n := by
    by_contra h
    have := runningMin_le (R w) t n (by omega)
    change minR w t ≤ R w n at this
    omega
  have hmin := runningMin_le (R w) t t le_rfl
  change minR w t ≤ R w t at hmin
  have hex : ∃ n, t < n ∧ R w n ≤ R w t - 1 := ⟨n, hnt, by omega⟩
  let d := Nat.find hex
  obtain ⟨htd, hd⟩ := Nat.find_spec hex
  change t < d at htd
  change R w d ≤ R w t - 1 at hd
  have habove : ∀ s, t ≤ s → s < d → R w t ≤ R w s := by
    intro s hts hsd
    by_cases hst : s = t
    · subst s; exact le_rfl
    · have hh := Nat.find_min hex hsd
      change ¬ (t < s ∧ R w s ≤ R w t - 1) at hh
      omega
  have hq : t ≤ d - 1 := by omega
  have hp := habove (d - 1) hq (by omega)
  have hstep := coord_lower w (d - 1)
  have hdq : d - 1 + 1 = d := by omega
  rw [hdq] at hstep
  have hprev : R w (d - 1) = R w t := by omega
  have heq : R w d = R w t - 1 := by omega
  have hc : w (d - 1) = 2 := by
    have hs := coord_succ w (d - 1)
    rw [hdq, hprev, heq] at hs
    generalize hv : w (d - 1) = c at hs ⊢
    fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep] at hs ⊢; omega
  refine ⟨d - 1, hq, hc, hprev, ?_, ?_⟩
  · rw [hdq]; exact heq
  · intro s hts hsq
    exact habove s hts (by omega)





theorem kmswActiveTerminal_firstDescent (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∃ t', t < t' ∧ R w t' = R w t - 1 ∧
      (∀ s, t < s → s < t' → R w t - 1 < R w s) ∧
      edgeWest w (act w t') = edgeEast w (act w t) ∧
      (∀ f, f < (kmswStage w t').nextEdge →
        (kmswStage w t').present f = true →
        edgeWest w f = edgeEast w (act w t) → f = act w t') := by
  obtain ⟨q, htq, hc, hlev, hdrop, habove⟩ := first_descent w hR t
  obtain ⟨p, hp, hlen⟩ := pendingEastFrontier_balanced w htq habove
  have hp0 : p = [] := by
    apply List.length_eq_zero_iff.mp
    omega
  have heast : (kmswStage w q).east (act w q) =
      (kmswStage w t).east (act w t) := by
    rw [hp0, List.nil_append] at hp
    exact List.cons.inj hp |>.1
  have hcode : kmswCodeStep (w q) = .down := by rw [hc]; rfl
  have hwest : (kmswStage w (q + 1)).west (act w (q + 1)) =
      (kmswStage w q).east (act w q) := by
    cases hr : (kmswStage w q).UR with
    | nil =>
      simp [kmswStage, act, kmswStep, hcode, kmswStepOfStep, hr, State.addEdge]
    | cons e es =>
      have hcoh := (CutConverse.frontier_history w q).1
      have hhead : (kmswStage w q).west e =
          (kmswStage w q).east (act w q) := by
        have hh := congrArg (fun xs : List ℕ => xs.head?) hcoh
        simpa [CutConverse.pendingVertices, hr, act] using hh
      simpa only [kmswStage, act, kmswStep, hcode, kmswStepOfStep, hr] using hhead
  have hend := edge_endpoints_eq w (act_lt_nextEdge w (le_refl (q + 1)))
  have het := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))).2
  have hwest' : edgeWest w (act w (q + 1)) = edgeEast w (act w t) :=
    hend.1.symm.trans (hwest.trans (heast.trans het))
  refine ⟨q + 1, by omega, hdrop, ?_, hwest', ?_⟩
  · intro s hts hsq
    have := habove s (by omega) (by omega)
    omega
  · intro f hf hfp hfw
    have hfv : (kmswStage w (q + 1)).west f =
        (kmswStage w q).east (act w q) :=
      (edge_endpoints_eq w hf).1.trans (hfw.trans (het.symm.trans heast.symm))
    cases hr : (kmswStage w q).UR with
    | nil =>
      have he := stageOutgoing_pendant_unique w q hcode hr f hf hfp hfv
      simpa only [kmswStage, act, kmswStep, hcode, kmswStepOfStep, hr,
        State.addEdge] using he
    | cons e es =>
      have hcoh := (CutConverse.frontier_history w q).1
      have hhead : (kmswStage w q).west e =
          (kmswStage w q).east (act w q) := by
        have hh := congrArg (fun xs : List ℕ => xs.head?) hcoh
        simpa [CutConverse.pendingVertices, hr, act] using hh
      have he := stageOutgoing_activation_unique w q e es hcode hr f hf hfp
        (hfv.trans hhead.symm)
      simpa only [kmswStage, act, kmswStep, hcode, kmswStepOfStep, hr] using he





theorem kmswActiveTerminal_outgoing_iff (w : ℕ → Fin 3) (t f : ℕ) :
    (EdgePresent w f ∧ edgeWest w f = edgeEast w (act w t)) ↔
      ∃ s, t < s ∧ f = act w s ∧
        edgeWest w (act w s) = edgeEast w (act w t) := by
  constructor
  · rintro ⟨⟨n, hf, hp⟩, hw⟩
    obtain ⟨s, _, hfs⟩ := stagePresent_exists_active w n f hf hp
    have hts : t < s := by
      by_contra h
      have hst : s ≤ t := by omega
      have hb := act_lt_nextEdge w hst
      have hp' := present_mono w (act_lt_nextEdge w (le_refl s))
        (active_present w s) t hst
      have he := stageOutgoing_active_east_empty w t (⟨act w s, hb⟩, false)
        ⟨rfl, hp'.2⟩
      apply he
      change (kmswStage w t).west (act w s) = (kmswStage w t).east (act w t)
      rw [(edge_endpoints_eq w hb).1,
        (edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))).2, ← hfs, hw]
    exact ⟨s, hts, hfs, hfs ▸ hw⟩
  · rintro ⟨s, _, rfl, hw⟩
    exact ⟨⟨s, act_lt_nextEdge w (le_refl s), active_present w s⟩, hw⟩






theorem kmswActiveTerminal_firstDescent_leastId (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∃ t', t < t' ∧ R w t' = R w t - 1 ∧
      (∀ s, t < s → s < t' → R w t - 1 < R w s) ∧
      edgeWest w (act w t') = edgeEast w (act w t) ∧
      (∀ f, EdgePresent w f → edgeWest w f = edgeEast w (act w t) →
        act w t' ≤ f) := by
  obtain ⟨d, htd, hdrop, hgap, hw, hunique⟩ :=
    kmswActiveTerminal_firstDescent w hR t
  let v := edgeEast w (act w t)
  have hs : ∃ e, e < (kmswStage w d).nextEdge ∧
      (kmswStage w d).present e = true ∧ (kmswStage w d).west e = v :=
    ⟨act w d, act_lt_nextEdge w (le_refl d), active_present w d,
      (edge_endpoints_eq w (act_lt_nextEdge w (le_refl d))).1.trans hw⟩
  have hsel : (kmswStageRightmostOutgoingDart w d v hs).1.val = act w d := by
    have hb := (kmswStageRightmostOutgoingDart w d v hs).1.isLt
    obtain ⟨hp, hv⟩ := kmswStageRightmostOutgoingDart_spec w d v hs
    apply hunique _ hb hp.2
    exact (edge_endpoints_eq w hb).1.symm.trans hv
  refine ⟨d, htd, hdrop, hgap, hw, ?_⟩
  intro f hf hfw
  obtain ⟨n, hfn, hfp⟩ := hf
  let m := max d n
  have hdm : d ≤ m := Nat.le_max_left _ _
  have hnm : n ≤ m := Nat.le_max_right _ _
  obtain ⟨hfm, hfpm⟩ := present_mono w hfn hfp m hnm
  have hsm := kmswStage_outgoing_exists_of_le w hdm hs
  have hstable := kmswStageRightmostOutgoingDart_stable w hdm hs
  have hmin := kmswStageRightmostOutgoingDart_min w m v hsm f hfm hfpm
    ((edge_endpoints_eq w hfm).1.trans hfw)
  rw [hstable, hsel] at hmin
  exact hmin

end DirectedDistances.KMSW
