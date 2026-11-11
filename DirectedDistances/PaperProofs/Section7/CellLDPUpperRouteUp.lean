module

public import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryRoutes
public import DirectedDistances.PaperProofs.Section7.LongPathFutureBoundaryExit
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.StageIncidenceChains

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open scoped Classical

private def UpperEndpoint (s : State) (v : ℕ) : Prop :=
  ∃ e, e ∈ s.UL ++ s.UR ∧ (s.west e = v ∨ s.east e = v)

private theorem upper_endpoint_step (w : ℕ → Fin 3) (n v : ℕ)
    (hv : UpperEndpoint (kmswStage w n) v) :
    UpperEndpoint (kmswStage w (n + 1)) v ∨
      v = (kmswStage w n).west (act w n) := by
  let s := kmswStage w n
  have hlast : s.UL = s.UL.dropLast ++ [s.active] := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    change s.UL = xs ++ [s.active] at hxs
    rw [hxs, List.dropLast_concat]
  have keep (e : ℕ) (he : e ∈ s.UL ++ s.UR)
      (he' : e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR)
      (hend : s.west e = v ∨ s.east e = v) :
      UpperEndpoint (kmswStage w (n + 1)) v := by
    have hb := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
      (by simp only [List.mem_append] at he ⊢; tauto)
    have hs := kmswStage_endpoints_stable w (Nat.le_succ n) hb
    exact ⟨e, he', by simpa only [hs.1, hs.2] using hend⟩
  obtain ⟨e, he, hend⟩ := hv
  change e ∈ s.UL ++ s.UR at he
  change s.west e = v ∨ s.east e = v at hend
  change UpperEndpoint (kmswStep s (w n)) v ∨ v = s.west s.active
  change (∀ e ∈ s.UL ++ s.UR,
    e ∈ (kmswStep s (w n)).UL ++ (kmswStep s (w n)).UR →
    s.west e = v ∨ s.east e = v → UpperEndpoint (kmswStep s (w n)) v) at keep
  generalize w n = c at keep ⊢
  fin_cases c
  · cases hu : s.UL.dropLast.reverse with
    | nil =>
      have hd : s.UL.dropLast = [] := by
        have hh := congrArg List.reverse hu
        simpa only [List.reverse_reverse, List.reverse_nil] using hh
      have hUL : s.UL = [s.active] := by simpa only [hd, List.nil_append] using hlast
      rcases List.mem_append.mp he with he | he
      · have heq : e = s.active := by simpa only [hUL, List.mem_singleton] using he
        subst e
        rcases hend with hw | ht
        · exact Or.inr hw.symm
        · left
          refine ⟨s.nextEdge, ?_, Or.inr ?_⟩
          · simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge] using ht
      · left
        apply keep e (List.mem_append_right _ he) _ hend
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu,
          State.addEdge, he]
    | cons f fs =>
      have hd : s.UL.dropLast = fs.reverse ++ [f] := by
        have hh := congrArg List.reverse hu
        simpa only [List.reverse_reverse, List.reverse_cons] using hh
      have hUL : s.UL = fs.reverse ++ [f, s.active] := by
        rw [hlast, hd, List.append_assoc]
        rfl
      have hchain := (kmswStage_boundary_chain_invariant w n).1
      change WestEastChain s (s.UL ++ s.UR) at hchain
      have hfa : s.east f = s.west s.active := by
        change List.IsChain (fun a b => s.east a = s.west b) _ at hchain
        rw [hUL] at hchain
        simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
          hchain.left_of_append.right_of_append
      have hecases : e ∈ fs.reverse ∨ e = f ∨ e = s.active ∨ e ∈ s.UR := by
        simp only [hUL, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at he
        tauto
      rcases hecases with he | rfl | rfl | he
      · left
        apply keep e (by simp only [hUL, List.mem_append]; tauto) _ hend
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu,
          State.addEdge, he]
      · rcases hend with hw | ht
        · left
          refine ⟨s.nextEdge, ?_, Or.inl ?_⟩
          · simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge] using hw
        · exact Or.inr (ht.symm.trans hfa)
      · rcases hend with hw | ht
        · exact Or.inr hw.symm
        · left
          refine ⟨s.nextEdge, ?_, Or.inr ?_⟩
          · simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge] using ht
      · left
        apply keep e (List.mem_append_right _ he) _ hend
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu,
          State.addEdge, he]
  · rcases List.mem_append.mp he with he | he
    · rw [hlast] at he
      rcases List.mem_append.mp he with he | he
      · left
        apply keep e (by rw [hlast]; simp only [List.mem_append]; tauto) _ hend
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, he]
      · have heq := List.mem_singleton.mp he
        subst e
        rcases hend with hw | ht
        · exact Or.inr hw.symm
        · left
          refine ⟨s.nextEdge + 1, ?_, Or.inr ?_⟩
          · simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge] using ht
    · left
      apply keep e (List.mem_append_right _ he) _ hend
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, he]
  · left
    apply keep e he _ hend
    cases hu : s.UR with
    | nil =>
      simp only [hu, List.append_nil] at he
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu,
        State.addEdge, he]
    | cons f fs =>
      simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu,
        List.append_assoc] using he

private def upperStageLift (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    Prefunctor (StagePresentVertex w m) (StagePresentVertex w n) where
  obj v := ⟨v.id⟩
  map {_ _} e :=
    ⟨e.val, (present_mono w e.property.1 e.property.2.1 n hmn).1,
      (present_mono w e.property.1 e.property.2.1 n hmn).2,
      ((present_endpoints_stable w e.property.1 e.property.2.1 hmn).1).trans
        e.property.2.2.1,
      ((present_endpoints_stable w e.property.1 e.property.2.1 hmn).2).trans
        e.property.2.2.2⟩

private theorem new_vertex_upper_endpoint (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w (n + 1)).nextVertex)
    (hold : ¬ v < (kmswStage w n).nextVertex) :
    UpperEndpoint (kmswStage w (n + 1)) v := by
  by_cases hc : w n = 0
  · cases hu : (kmswStage w n).UL.dropLast.reverse with
    | nil =>
      have heq : v = (kmswStage w n).nextVertex := by
        simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hu,
          State.addEdge] at hv
        omega
      subst v
      refine ⟨(kmswStage w n).nextEdge, ?_, Or.inl ?_⟩
      all_goals simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hu,
        State.addEdge]
    | cons f fs =>
      simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hu,
        State.addEdge] at hv
      exact (hold hv).elim
  · by_cases hc1 : w n = 1
    · have heq : v = (kmswStage w n).nextVertex := by
        simp [kmswStage, kmswStep, hc1, kmswCodeStep, kmswStepOfStep,
          State.addEdge] at hv
        omega
      subst v
      refine ⟨(kmswStage w n).nextEdge, ?_, Or.inr ?_⟩
      all_goals simp [kmswStage, kmswStep, hc1, kmswCodeStep, kmswStepOfStep,
        State.addEdge]
    · have hc2 : w n = 2 := by
        apply Fin.ext
        have := (w n).isLt
        have h0 : (w n).val ≠ 0 := fun hh => hc (Fin.ext hh)
        have h1 : (w n).val ≠ 1 := fun hh => hc1 (Fin.ext hh)
        omega
      cases hu : (kmswStage w n).UR with
      | cons f fs =>
        simp [kmswStage, kmswStep, hc2, kmswCodeStep, kmswStepOfStep, hu] at hv
        exact (hold hv).elim
      | nil =>
        have heq : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, hc2, kmswCodeStep, kmswStepOfStep, hu,
            State.addEdge] at hv
          omega
        subst v
        refine ⟨(kmswStage w n).nextEdge, ?_, Or.inr ?_⟩
        all_goals simp [kmswStage, kmswStep, hc2, kmswCodeStep, kmswStepOfStep, hu,
          State.addEdge]

private theorem upper_route_core (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ z : ℕ, UpperEndpoint (kmswStage w n) z ∧
      Nonempty (Path (⟨v⟩ : StagePresentVertex w n) ⟨z⟩) := by
  induction n generalizing v with
  | zero =>
    have hcases : v = 0 ∨ v = 1 := by change v < 2 at hv; omega
    refine ⟨v, ?_, ⟨Path.nil⟩⟩
    refine ⟨0, by simp [kmswStage, kmswInit], ?_⟩
    rcases hcases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | succ n ih =>
    by_cases hold : v < (kmswStage w n).nextVertex
    · obtain ⟨z, hz, ⟨p⟩⟩ := ih v hold
      let p' := (upperStageLift w (Nat.le_succ n)).mapPath p
      rcases upper_endpoint_step w n z hz with hz' | hz'
      · exact ⟨z, hz', ⟨p'⟩⟩
      · let b := (kmswStage w n).east (act w n)
        have ha := act_lt_nextEdge w (Nat.le_refl n)
        have hb : UpperEndpoint (kmswStage w n) b := by
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
          refine ⟨act w n, List.mem_append_left _ ?_, Or.inr rfl⟩
          rw [hxs]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        have hb' : UpperEndpoint (kmswStage w (n + 1)) b := by
          rcases upper_endpoint_step w n b hb with hh | hh
          · exact hh
          · have hr := kmswStageRank_strict w n (act w n) ha
            change (kmswStage w n).east (act w n) =
              (kmswStage w n).west (act w n) at hh
            rw [hh] at hr
            exact (lt_irrefl _ hr).elim
        have hp : (kmswStage w n).present (act w n) = true := by
          apply (kmswStage_status w n).2.1
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
          rw [hxs]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        have hs := present_endpoints_stable w ha hp (Nat.le_succ n)
        have e : (⟨z⟩ : StagePresentVertex w (n + 1)) ⟶ ⟨b⟩ :=
          ⟨act w n, (present_mono w ha hp (n + 1) (Nat.le_succ n)).1,
            (present_mono w ha hp (n + 1) (Nat.le_succ n)).2,
            hs.1.trans hz'.symm, hs.2⟩
        exact ⟨b, hb', ⟨p'.comp e.toPath⟩⟩
    · exact ⟨v, new_vertex_upper_endpoint w n v hv hold, ⟨Path.nil⟩⟩




theorem stage_cell_upper_boundary_reachable (w : ℕ → Fin 3) (n : ℕ)
    (y : StagePresentVertex w n) (hy : y.id < (kmswStage w n).nextVertex) :
    ∃ v e : ℕ, e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) ∧
      Nonempty (Path y (⟨v⟩ : StagePresentVertex w n)) := by
  obtain ⟨v, ⟨e, he, hv⟩, hp⟩ := upper_route_core w n y.id hy
  cases y
  exact ⟨v, e, he, hv, hp⟩

private theorem upper_left_record_time (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : q ≤ -1) (hvalue : L w m = q)
    (hrecord : ∀ j < m, q < L w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    have ht : boundaryHitTime w h q = Nat.find (h.leftHit q hq) := by
      simp only [boundaryHitTime, dite_eq_right (by omega : q ≠ 0),
        dite_eq_right (by omega : ¬ 0 < q)]
    rw [ht]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_left_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hfirst] at hstrict
    exact (lt_irrefl q) hstrict
  omega

private theorem upper_right_record_time (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : 1 ≤ q) (hvalue : R w m = -q)
    (hrecord : ∀ j < m, R w m < R w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    have ht : boundaryHitTime w h q = Nat.find (h.rightHit q hq) := by
      simp only [boundaryHitTime, dite_eq_right (by omega : q ≠ 0),
        dite_eq_left (by omega : 0 < q)]
    rw [ht]
    exact Nat.find_min' (h.rightHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_right_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hvalue] at hstrict
    rw [hfirst] at hstrict
    exact (lt_irrefl (-q)) hstrict
  omega

private theorem finite_LL_label (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n e v : ℕ) (heLL : e ∈ (kmswStage w n).LL)
    (hend : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ k ∧ k ≤ 0 ∧
      boundaryVertex w h k = v := by
  rw [kmswStage_LL_eq] at heLL
  obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLL
  have hm' := List.mem_reverse.mp hm
  have hcond : 0 < m ∧ ∀ j < m, L w m < L w j :=
    of_decide_eq_true (List.mem_filter.mp hm').2
  have hmle : m ≤ n := by
    have := List.mem_range.mp (List.mem_filter.mp hm').1
    omega
  let q := L w m
  have hq : q ≤ -1 := by
    have hzero : L w 0 = 0 := by simp [L]
    have hrec0 := hcond.2 0 (by omega)
    dsimp [q]
    omega
  have hmin := runningMin_le (L w) n m hmle
  have hlen := kmswStage_LL_length w n
  change minL w n ≤ L w m at hmin
  have htime : boundaryHitTime w h q = m :=
    upper_left_record_time w h hq rfl (by simpa [q] using hcond.2)
  have hleft : (kmswStage w m).west (kmswLLCreatedEdge w m) = boundaryVertex w h q ∧
      (kmswStage w m).east (kmswLLCreatedEdge w m) = boundaryVertex w h (q + 1) ∧
      (kmswStage w m).present (kmswLLCreatedEdge w m) = false := by
    simpa [htime] using boundaryVertex_left_missing_edge w h hq
  have heq' : e = kmswLLCreatedEdge w m := by simpa using heq.symm
  have hnextPositive : 0 < (kmswStage w m).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (Nat.zero_le m)
    simp [kmswStage, kmswInit] at hmono
    omega
  have hebound : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
    dsimp [kmswLLCreatedEdge]
    omega
  have hstable := kmswStage_endpoints_stable w hmle hebound
  rcases hend with hwest | heast
  · refine ⟨q, by dsimp [q]; omega, by omega, ?_⟩
    calc
      boundaryVertex w h q = (kmswStage w m).west (kmswLLCreatedEdge w m) := hleft.1.symm
      _ = (kmswStage w n).west e := by rw [heq']; exact hstable.1.symm
      _ = v := hwest
  · refine ⟨q + 1, by dsimp [q]; omega, by omega, ?_⟩
    calc
      boundaryVertex w h (q + 1) = (kmswStage w m).east (kmswLLCreatedEdge w m) :=
        hleft.2.1.symm
      _ = (kmswStage w n).east e := by rw [heq']; exact hstable.2.symm
      _ = v := heast

private theorem finite_LR_label (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n e v : ℕ) (heLR : e ∈ (kmswStage w n).LR)
    (hend : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, 0 ≤ k ∧ k ≤ ((kmswStage w n).LR.length : ℤ) ∧
      boundaryVertex w h k = v := by
  rw [kmswStage_LR_eq] at heLR
  obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLR
  have hrecord : ∀ j < m, R w m < R w j := of_decide_eq_true (List.mem_filter.mp hm).2
  have hmle : m ≤ n := by
    have := List.mem_range.mp (List.mem_filter.mp hm).1
    omega
  have hmin := runningMin_le (R w) n m hmle
  have hlen := kmswStage_LR_length w n
  change minR w n ≤ R w m at hmin
  have hmin0 := runningMin_le (R w) n 0 (Nat.zero_le n)
  change minR w n ≤ 0 at hmin0
  by_cases hm0 : m = 0
  · subst m
    have heq' : e = 0 := by simpa [act, kmswStage, kmswInit] using heq.symm
    have hebound : e < (kmswStage w 0).nextEdge := by simp [heq', kmswStage, kmswInit]
    have hstable := kmswStage_endpoints_stable w hmle hebound
    rcases hend with hwest | heast
    · refine ⟨0, by omega, by omega, ?_⟩
      rw [boundaryVertex_zero]
      calc
        0 = (kmswStage w 0).west e := by rw [heq']; rfl
        _ = (kmswStage w n).west e := hstable.1.symm
        _ = v := hwest
    · refine ⟨1, by omega, by omega, ?_⟩
      rw [boundaryVertex_one]
      calc
        1 = (kmswStage w 0).east e := by rw [heq']; rfl
        _ = (kmswStage w n).east e := hstable.2.symm
        _ = v := heast
  · have hzero : R w 0 = 0 := by simp [R]
    have hrecord0 := hrecord 0 (by omega)
    let q := -R w m
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hvalue : R w m = -q := by dsimp [q]; omega
    obtain ⟨N, hNbound, hN⟩ := boundaryVertex_right_edge w h hq
    have htime : boundaryHitTime w h q = m :=
      upper_right_record_time w h hq hvalue hrecord
    have hqN : m ≤ N := by rw [← htime]; exact hNbound
    have hstableMN := kmswStage_endpoints_stable w hmle
      (act_lt_nextEdge w (Nat.le_refl m))
    have hstableMN' := kmswStage_endpoints_stable w hqN
      (act_lt_nextEdge w (Nat.le_refl m))
    have hNedge := hN N le_rfl
    have heq' : e = act w m := by simpa using heq.symm
    rcases hend with hwest | heast
    · refine ⟨q, by omega, by dsimp [q]; omega, ?_⟩
      calc
        boundaryVertex w h q = (kmswStage w N).west (act w m) := by
          rw [← htime]
          exact (hNedge.2.2.1).symm
        _ = (kmswStage w m).west (act w m) := hstableMN'.1
        _ = (kmswStage w n).west e := by rw [heq']; exact hstableMN.1.symm
        _ = v := hwest
    · refine ⟨q + 1, by omega, by dsimp [q]; omega, ?_⟩
      calc
        boundaryVertex w h (q + 1) = (kmswStage w N).east (act w m) := by
          rw [← htime]
          exact (hNedge.2.2.2).symm
        _ = (kmswStage w m).east (act w m) := hstableMN'.2
        _ = (kmswStage w n).east e := by rw [heq']; exact hstableMN.2.symm
        _ = v := heast



private theorem attained_hit_minimum (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ j, p j - 1 ≤ p (j + 1)) (K : ℕ)
    (hhit : ∃ m, p m = -(K : ℤ)) :
    ∃ m, runningMin p m = -(K : ℤ) := by
  let m := Nat.find hhit
  have hm : p m = -(K : ℤ) := Nat.find_spec hhit
  have hlo : ∀ j, j ≤ m → -(K : ℤ) ≤ p j := by
    intro j
    induction j with
    | zero => intro _; rw [hp0]; omega
    | succ j ih =>
      intro hj
      by_cases heq : j + 1 = m
      · rw [heq, hm]
      · have hprev := ih (by omega)
        have hne : p j ≠ -(K : ℤ) := Nat.find_min hhit (by omega : j < m)
        have hs := hstep j
        omega
  obtain ⟨j, hj, hmin⟩ := runningMin_attained p m
  have hupper := runningMin_le p m m le_rfl
  exact ⟨m, by have := hlo j hj; omega⟩

private theorem upper_left_edge_future_LL_bounded (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) (e : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast) :
    ∃ m f, f < (kmswStage (fun i => w (n + i)) m).nextEdge ∧
      f ∈ (kmswStage (fun i => w (n + i)) m).LL ∧
      (kmswStage (fun i => w (n + i)) m).LL.length =
        (kmswStage w n).UL.length - 1 ∧
      kmswWindowEdgeMapInf w n f = e := by
  let u := fun i => w (n + i)
  let K := (kmswStage w n).UL.dropLast.length
  have hhit : ∃ m, L u m = -(K : ℤ) := by
    by_cases hK : K = 0
    · exact ⟨0, by simp only [hK, Nat.cast_zero, neg_zero, L, Finset.sum_range_zero]⟩
    · exact hFuture.leftHit (-(K : ℤ)) (by omega)
  have hstep : ∀ j, L u j - 1 ≤ L u (j + 1) := by
    intro j
    have hs : L u (j + 1) = L u j +
        (RandomWalk.lazyTwoDimensionalStep (u j)).1 := Finset.sum_range_succ _ _
    change L u (j + 1) = L u j + ((u j : ℤ) - 1) at hs
    omega
  obtain ⟨m, hm⟩ := attained_hit_minimum (L u) rfl hstep K hhit
  change minL u m = -(K : ℤ) at hm
  have hlen : (kmswStage u m).LL.length = K := by
    have hh := kmswStage_LL_length u m
    omega
  let d := kmswWindowPatchData w n m
  have hr := kmswWindowPatchData_rel w n m
  change KMSWWindowPatchRel (kmswStage w n) (kmswStage w (n + m))
    (kmswStage u m) d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
  have hA : d.A = [] := by
    by_contra hA
    have hXL := hr.xl_nil hA
    have hres := congrArg List.length hr.left_residual
    have hsplit := congrArg List.length hr.ll_split
    simp only [List.length_append, List.length_map] at hres hsplit
    rw [hXL, List.length_nil, zero_add] at hsplit
    have hpos : 0 < d.A.length := List.length_pos_iff.mpr hA
    change K = d.A.length + d.YL.length at hres
    omega
  have hres : (kmswStage w n).UL.dropLast = d.YL.map d.φ := by
    simpa only [hA, List.nil_append] using hr.left_residual
  rw [hres] at he
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  have hfLL : f ∈ (kmswStage u m).LL := by
    rw [hr.ll_split]
    exact List.mem_append_right _ hf
  have hfalloc := (kmswStage_boundary_ids_lt_nextEdge u m).2 f
    (by simp only [List.mem_append]; tauto)
  refine ⟨m, f, hfalloc, hfLL, ?_, ?_⟩
  · simpa only [K, List.length_dropLast] using hlen
  · rw [kmswWindowEdgeMapInf_eq_stage w n m f hfalloc]
    exact hfe

private theorem upper_right_edge_future_LR_bounded (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) (e : ℕ)
    (he : e ∈ (kmswStage w n).UR) :
    ∃ m f, f < (kmswStage (fun i => w (n + i)) m).nextEdge ∧
      f ∈ (kmswStage (fun i => w (n + i)) m).LR ∧
      (kmswStage (fun i => w (n + i)) m).LR.length =
        (kmswStage w n).UR.length + 1 ∧
      kmswWindowEdgeMapInf w n f = e := by
  let u := fun i => w (n + i)
  let K := (kmswStage w n).UR.length
  have hhit : ∃ m, R u m = -(K : ℤ) := by
    by_cases hK : K = 0
    · exact ⟨0, by simp only [hK, Nat.cast_zero, neg_zero, R, Finset.sum_range_zero]⟩
    · exact hFuture.rightHit (K : ℤ) (by omega)
  have hstep : ∀ j, R u j - 1 ≤ R u (j + 1) := by
    intro j
    have hs : R u (j + 1) = R u j +
        (RandomWalk.lazyTwoDimensionalStep (u j)).2 := Finset.sum_range_succ _ _
    have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (u j)).2 := by
      unfold RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    omega
  obtain ⟨m, hm⟩ := attained_hit_minimum (R u) rfl hstep K hhit
  change minR u m = -(K : ℤ) at hm
  have hlen : (kmswStage u m).LR.length = K + 1 := by
    have hh := kmswStage_LR_length u m
    omega
  let d := kmswWindowPatchData w n m
  have hr := kmswWindowPatchData_rel w n m
  change KMSWWindowPatchRel (kmswStage w n) (kmswStage w (n + m))
    (kmswStage u m) d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
  have hB : d.B = [] := by
    by_contra hB
    have hXR := hr.xr_nil hB
    have hres := congrArg List.length hr.right_residual
    have hsplit := congrArg List.length hr.lr_split
    simp only [List.length_append, List.length_map, List.length_singleton] at hres hsplit
    rw [hXR, List.length_nil, Nat.add_zero] at hsplit
    have hpos : 0 < d.B.length := List.length_pos_iff.mpr hB
    change K = d.YR.length + d.B.length at hres
    omega
  have hres : (kmswStage w n).UR = d.YR.map d.φ := by
    simpa only [hB, List.append_nil] using hr.right_residual
  rw [hres] at he
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  have hfLR : f ∈ (kmswStage u m).LR := by
    rw [hr.lr_split]
    exact List.mem_append_left _ (List.mem_append_right _ hf)
  have hfalloc := (kmswStage_boundary_ids_lt_nextEdge u m).2 f
    (by simp only [List.mem_append]; tauto)
  refine ⟨m, f, hfalloc, hfLR, hlen, ?_⟩
  rw [kmswWindowEdgeMapInf_eq_stage w n m f hfalloc]
  exact hfe

private theorem window_endpoint_preimage (w : ℕ → Fin 3) (n m e f v : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hf : f < (kmswStage (fun i => w (n + i)) m).nextEdge)
    (hfe : kmswWindowEdgeMapInf w n f = e)
    (hv : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ z : ℕ,
      ((kmswStage (fun i => w (n + i)) m).west f = z ∨
        (kmswStage (fun i => w (n + i)) m).east f = z) ∧
      v = kmswWindowVertexMapInf w n z := by
  have hstable := kmswStage_endpoints_stable w (Nat.le_add_right n m) he
  rcases hv with hv | hv
  · refine ⟨_, Or.inl rfl, ?_⟩
    calc
      v = (kmswStage w n).west e := hv.symm
      _ = (kmswStage w (n + m)).west e := hstable.1.symm
      _ = kmswWindowVertexMapInf w n
          ((kmswStage (fun i => w (n + i)) m).west f) := by
        rw [← hfe]
        exact kmswWindowEdgeMapInf_west w n m f hf
  · refine ⟨_, Or.inr rfl, ?_⟩
    calc
      v = (kmswStage w n).east e := hv.symm
      _ = (kmswStage w (n + m)).east e := hstable.2.symm
      _ = kmswWindowVertexMapInf w n
          ((kmswStage (fun i => w (n + i)) m).east f) := by
        rw [← hfe]
        exact kmswWindowEdgeMapInf_east w n m f hf




theorem stage_upper_endpoint_future_boundary_bounded (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) (e v : ℕ)
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
    (hv : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      v = kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hFuture k) := by
  let u := fun i => w (n + i)
  have healloc := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    (by simp only [List.mem_append] at he ⊢; tauto)
  have active_case (heq : e = act w n) :
      ∃ k : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
        k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
        v = kmswWindowVertexMapInf w n (boundaryVertex u hFuture k) := by
    have hf : 0 < (kmswStage u 0).nextEdge := by change 0 < 1; omega
    have hfe : kmswWindowEdgeMapInf w n 0 = e := by
      rw [kmswWindowEdgeMapInf_eq_stage w n 0 0 hf]
      exact heq.symm
    obtain ⟨z, hz, hvz⟩ := window_endpoint_preimage w n 0 e 0 v healloc hf hfe hv
    obtain ⟨k, hk0, hk1, hlabel⟩ := finite_LR_label u hFuture 0 0 z
      (by simp [kmswStage, kmswInit]) hz
    change k ≤ 1 at hk1
    exact ⟨k, by omega, by omega, by rw [hlabel]; exact hvz⟩
  rcases List.mem_append.mp he with heUL | heUR
  · have hlast : (kmswStage w n).UL =
        (kmswStage w n).UL.dropLast ++ [act w n] := by
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
      rw [hxs, List.dropLast_concat]
      rfl
    rw [hlast] at heUL
    rcases List.mem_append.mp heUL with heLeft | heActive
    · obtain ⟨m, f, hf, hfLL, hlen, hfe⟩ :=
        upper_left_edge_future_LL_bounded w n hFuture e heLeft
      obtain ⟨z, hz, hvz⟩ := window_endpoint_preimage w n m e f v healloc hf hfe hv
      obtain ⟨k, hkL, hk0, hlabel⟩ := finite_LL_label u hFuture m f z hfLL hz
      refine ⟨k, ?_, by omega, ?_⟩
      · rw [hlen] at hkL
        exact hkL
      · rw [hlabel]
        exact hvz
    · exact active_case (List.mem_singleton.mp heActive)
  · obtain ⟨m, f, hf, hfLR, hlen, hfe⟩ :=
      upper_right_edge_future_LR_bounded w n hFuture e heUR
    obtain ⟨z, hz, hvz⟩ := window_endpoint_preimage w n m e f v healloc hf hfe hv
    obtain ⟨k, hk0, hkR, hlabel⟩ := finite_LR_label u hFuture m f z hfLR hz
    refine ⟨k, by omega, ?_, ?_⟩
    · rw [hlen] at hkR
      exact_mod_cast hkR
    · rw [hlabel]
      exact hvz




theorem stage_cell_upper_boundary_route (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i)))
    (y : StagePresentVertex w n) (hy : y.id < (kmswStage w n).nextVertex) :
    ∃ k : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      Nonempty (Path y
        ⟨kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hFuture k)⟩) := by
  obtain ⟨v, e, he, hv, hp⟩ := stage_cell_upper_boundary_reachable w n y hy
  obtain ⟨k, hkL, hkR, hlabel⟩ :=
    stage_upper_endpoint_future_boundary_bounded w n hFuture e v he hv
  refine ⟨k, hkL, hkR, ?_⟩
  rw [← hlabel]
  exact hp

end DirectedDistances.PaperProofs.Section7
