module

public import DirectedDistances.KMSW.StageStackInvariantUL
public import DirectedDistances.KMSW.StageStackInvariantUR
public import DirectedDistances.KMSW.StageActiveEdges
public import DirectedDistances.KMSW.StageIncidence
public import DirectedDistances.KMSW.CutEquivalenceConverse

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW



inductive KMSWSlot
  

  | west (t : ℕ)
  

  | east (t : ℕ)
  deriving DecidableEq



@[expose] def KMSWSlot.time : KMSWSlot → ℕ
  | .west t => t
  | .east t => t



@[expose] def kmswSlotVertex (w : ℕ → Fin 3) : KMSWSlot → ℕ
  | .west t => (kmswStage w t).west (kmswStage w t).active
  | .east t => (kmswStage w t).east (kmswStage w t).active



@[expose] def kmswSlotLink (w : ℕ → Fin 3) (S T : KMSWSlot) : Prop :=
  match S with
  | .west 0 => False
  | .east 0 => False
  | .west (t + 1) =>
      (w t = 1 ∧ T = .west t) ∨ (w t = 2 ∧ T = .east t) ∨
        (w t = 0 ∧ ∃ r, kmswLpair w r t ∧ T = .west r)
  | .east (t + 1) =>
      (w t = 0 ∧ T = .east t) ∨
        (w t = 2 ∧ ∃ s, kmswRpair w s t ∧ T = .east s)



private theorem slot_codes (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  have := c.isLt
  have h : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))



theorem kmswRpair_codes (w : ℕ → Fin 3) {s t : ℕ} (h : kmswRpair w s t) :
    w s = 1 ∧ w t = 2 := by
  have hs := h.2.2 (s + 1) (by omega) (by have := h.1; omega)
  have ht := h.2.2 t h.1 le_rfl
  have hRs : R w (s + 1) =
      R w s + (RandomWalk.lazyTwoDimensionalStep (w s)).2 :=
    Finset.sum_range_succ _ _
  have hRt : R w (t + 1) =
      R w t + (RandomWalk.lazyTwoDimensionalStep (w t)).2 :=
    Finset.sum_range_succ _ _
  have he := h.2.1
  constructor
  · rcases slot_codes (w s) with hc | hc | hc
    · simp [hc] at hRs; omega
    · exact hc
    · simp [hc] at hRs; omega
  · rcases slot_codes (w t) with hc | hc | hc
    · simp [hc] at hRt; omega
    · simp [hc] at hRt; omega
    · exact hc



theorem kmswSlot_up_missing_endpoints (w : ℕ → Fin 3) (s : ℕ) (hc : w s = 1) :
    (kmswStage w (s + 1)).west ((kmswStage w s).nextEdge + 1) =
        (kmswStage w s).nextVertex ∧
      (kmswStage w (s + 1)).east ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.east s) ∧
      (kmswStage w s).nextEdge + 1 < (kmswStage w (s + 1)).nextEdge := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
    State.addEdge, kmswSlotVertex]



theorem kmswSlot_left_pair_vertex (w : ℕ → Fin 3) {r t : ℕ}
    (hp : kmswLpair w r t) :
    kmswSlotVertex w (.west (t + 1)) = kmswSlotVertex w (.west r) := by
  have hc := (kmswLpair_codes w hp).2
  cases hh : (kmswStage w t).UL.dropLast.reverse with
  | nil => exact ((kmswStage_left_head_nil_iff w t hc).mp hh ⟨r, hp⟩).elim
  | cons e es =>
    obtain ⟨r', hr', he⟩ := kmswStage_left_head_pair w t e es hc hh
    have hr : r' = r := kmswLpair_left_unique w hr' hp
    subst r'
    have hv := (kmswStage_left_UL_cons_endpoints w t e es hc hh).1
    rw [he] at hv
    exact hv.trans (kmswStage_endpoints_stable w (Nat.le_of_lt hp.1)
      (kmswStage_active_lt w r)).1



theorem kmswSlot_down_pair_vertex (w : ℕ → Fin 3) {s t : ℕ}
    (hp : kmswRpair w s t) :
    kmswSlotVertex w (.east (t + 1)) = kmswSlotVertex w (.east s) := by
  obtain ⟨hs, ht⟩ := kmswRpair_codes w hp
  cases hh : (kmswStage w t).UR with
  | nil => exact ((kmswStage_down_head_nil_iff w t ht).mp hh ⟨s, hp⟩).elim
  | cons e es =>
    obtain ⟨s', hs', he⟩ := kmswStage_down_head_pair w t e es ht hh
    have hss : s' = s := kmswRpair_left_unique w hs' hp
    subst s'
    have ha := (kmswStage_down_UR_cons_endpoints w t e es ht hh).1
    have hm := kmswSlot_up_missing_endpoints w s hs
    change (kmswStage w (t + 1)).east (kmswStage w (t + 1)).active = _
    rw [ha, he]
    exact (kmswStage_endpoints_stable w (by have := hp.1; omega) hm.2.2).2.trans
      hm.2.1



theorem kmswSlotLink_vertex (w : ℕ → Fin 3) {S T : KMSWSlot}
    (h : kmswSlotLink w S T) : kmswSlotVertex w S = kmswSlotVertex w T := by
  cases S with
  | west t =>
    cases t with
    | zero => exact h.elim
    | succ t =>
      rcases h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩ | ⟨_, r, hp, rfl⟩
      · exact (kmswStage_up_active_endpoints w t hc).1
      · cases hh : (kmswStage w t).UR with
        | nil => exact (kmswStage_down_UR_nil_endpoints w t hc hh).1
        | cons e es => exact (kmswStage_down_UR_cons_endpoints w t e es hc hh).2
      · exact kmswSlot_left_pair_vertex w hp
  | east t =>
    cases t with
    | zero => exact h.elim
    | succ t =>
      rcases h with ⟨hc, rfl⟩ | ⟨_, s, hp, rfl⟩
      · cases hh : (kmswStage w t).UL.dropLast.reverse with
        | nil => exact (kmswStage_left_UL_nil_endpoints w t hc hh).2
        | cons e es => exact (kmswStage_left_UL_cons_endpoints w t e es hc hh).2
      · exact kmswSlot_down_pair_vertex w hp



theorem kmswSlotLink_time (w : ℕ → Fin 3) {S T : KMSWSlot}
    (h : kmswSlotLink w S T) : T.time < S.time := by
  cases S with
  | west t =>
    cases t with
    | zero => exact h.elim
    | succ t =>
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, r, hp, rfl⟩
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt hp.1
  | east t =>
    cases t with
    | zero => exact h.elim
    | succ t =>
      rcases h with ⟨_, rfl⟩ | ⟨_, s, hp, rfl⟩
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt hp.1



@[expose] def kmswSlotFresh (w : ℕ → Fin 3) (S : KMSWSlot) : Prop :=
  ¬ ∃ T, kmswSlotLink w S T



theorem kmswSlotFresh_west_succ (w : ℕ → Fin 3) (t : ℕ) :
    kmswSlotFresh w (.west (t + 1)) ↔ w t = 0 ∧ ¬ ∃ r, kmswLpair w r t := by
  rcases slot_codes (w t) with hc | hc | hc <;>
    simp [kmswSlotFresh, kmswSlotLink, hc]



theorem kmswSlotFresh_east_succ (w : ℕ → Fin 3) (t : ℕ) :
    kmswSlotFresh w (.east (t + 1)) ↔
      w t = 1 ∨ (w t = 2 ∧ ¬ ∃ s, kmswRpair w s t) := by
  rcases slot_codes (w t) with hc | hc | hc <;>
    simp [kmswSlotFresh, kmswSlotLink, hc]



theorem kmswSlotFresh_vertex_succ (w : ℕ → Fin 3) (S : KMSWSlot) (t : ℕ)
    (ht : S.time = t + 1) (hf : kmswSlotFresh w S) :
    kmswSlotVertex w S = (kmswStage w t).nextVertex ∧
      (kmswStage w (t + 1)).nextVertex = (kmswStage w t).nextVertex + 1 := by
  cases S with
  | west s =>
    change s = t + 1 at ht
    subst s
    obtain ⟨hc, hn⟩ := (kmswSlotFresh_west_succ w t).mp hf
    have hh := (kmswStage_left_head_nil_iff w t hc).mpr hn
    exact ⟨(kmswStage_left_UL_nil_endpoints w t hc hh).1, by
      simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh, State.addEdge]⟩
  | east s =>
    change s = t + 1 at ht
    subst s
    rcases (kmswSlotFresh_east_succ w t).mp hf with hc | ⟨hc, hn⟩
    · exact ⟨(kmswStage_up_active_endpoints w t hc).2, by
        simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]⟩
    · have hh := (kmswStage_down_head_nil_iff w t hc).mpr hn
      exact ⟨(kmswStage_down_UR_nil_endpoints w t hc hh).2, by
        simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh, State.addEdge]⟩



theorem kmswSlotVertex_lt (w : ℕ → Fin 3) (S : KMSWSlot) {n : ℕ}
    (hn : S.time ≤ n) : kmswSlotVertex w S < (kmswStage w n).nextVertex := by
  have hb := kmswStage_endpoints_lt_nextVertex w S.time
    (kmswStage w S.time).active (kmswStage_active_lt w S.time)
  have hm := CutConverse.nextVertex_mono w hn
  cases S with
  | west t => exact hb.1.trans_le hm
  | east t => exact hb.2.trans_le hm



theorem kmswSlotFresh_zero (w : ℕ → Fin 3) :
    kmswSlotFresh w (.west 0) ∧ kmswSlotFresh w (.east 0) ∧
      kmswSlotVertex w (.west 0) = 0 ∧ kmswSlotVertex w (.east 0) = 1 := by
  simp [kmswSlotFresh, kmswSlotLink, kmswSlotVertex, kmswStage, kmswInit]



theorem kmswSlotLink_parent_unique (w : ℕ → Fin 3) {S T U : KMSWSlot}
    (hT : kmswSlotLink w S T) (hU : kmswSlotLink w S U) : T = U := by
  cases S with
  | west t =>
    cases t with
    | zero => exact hT.elim
    | succ t =>
      rcases slot_codes (w t) with hc | hc | hc
      · simp only [kmswSlotLink, hc, show (0 : Fin 3) ≠ 1 from by decide,
          show (0 : Fin 3) ≠ 2 from by decide, false_and, true_and,
          false_or] at hT hU
        obtain ⟨r, hr, rfl⟩ := hT
        obtain ⟨s, hs, rfl⟩ := hU
        exact congrArg KMSWSlot.west (kmswLpair_left_unique w hr hs)
      · simp [kmswSlotLink, hc] at hT hU
        exact hT.trans hU.symm
      · simp [kmswSlotLink, hc] at hT hU
        exact hT.trans hU.symm
  | east t =>
    cases t with
    | zero => exact hT.elim
    | succ t =>
      rcases slot_codes (w t) with hc | hc | hc
      · simp [kmswSlotLink, hc] at hT hU
        exact hT.trans hU.symm
      · simp [kmswSlotLink, hc] at hT
      · simp only [kmswSlotLink, hc, show (2 : Fin 3) ≠ 0 from by decide,
          false_and, true_and, false_or] at hT hU
        obtain ⟨r, hr, rfl⟩ := hT
        obtain ⟨s, hs, rfl⟩ := hU
        exact congrArg KMSWSlot.east (kmswRpair_left_unique w hr hs)



theorem kmswSlotFresh_ne_of_time_lt (w : ℕ → Fin 3) {S T : KMSWSlot}
    (hT : kmswSlotFresh w T) (ht : S.time < T.time) :
    kmswSlotVertex w S ≠ kmswSlotVertex w T := by
  cases hh : T.time with
  | zero => omega
  | succ t =>
    have hv := (kmswSlotFresh_vertex_succ w T t hh hT).1
    have hb := kmswSlotVertex_lt w S (n := t) (by omega)
    omega



theorem kmswSlotFresh_injective (w : ℕ → Fin 3) {S T : KMSWSlot}
    (hS : kmswSlotFresh w S) (hT : kmswSlotFresh w T)
    (hv : kmswSlotVertex w S = kmswSlotVertex w T) : S = T := by
  have ht : S.time = T.time := by
    rcases lt_trichotomy S.time T.time with h | h | h
    · exact (kmswSlotFresh_ne_of_time_lt w hT h hv).elim
    · exact h
    · exact (kmswSlotFresh_ne_of_time_lt w hS h hv.symm).elim
  cases S with
  | west s =>
    cases T with
    | west t => exact congrArg KMSWSlot.west ht
    | east t =>
      change s = t at ht
      subst t
      cases s with
      | zero => simp [kmswSlotVertex, kmswStage, kmswInit] at hv
      | succ s =>
        have hc := (kmswSlotFresh_west_succ w s).mp hS
        have hd := (kmswSlotFresh_east_succ w s).mp hT
        rcases hd with hd | ⟨hd, _⟩ <;> simp_all
  | east s =>
    cases T with
    | east t => exact congrArg KMSWSlot.east ht
    | west t =>
      change s = t at ht
      subst t
      cases s with
      | zero => simp [kmswSlotVertex, kmswStage, kmswInit] at hv
      | succ s =>
        have hc := (kmswSlotFresh_west_succ w s).mp hT
        have hd := (kmswSlotFresh_east_succ w s).mp hS
        rcases hd with hd | ⟨hd, _⟩ <;> simp_all



@[expose] def kmswSlotConnected (w : ℕ → Fin 3) (n : ℕ) (S T : KMSWSlot) : Prop :=
  Relation.EqvGen (fun A B => kmswSlotLink w A B ∧ A.time ≤ n ∧ B.time ≤ n) S T



theorem kmswSlotConnected_vertex (w : ℕ → Fin 3) {n : ℕ} {S T : KMSWSlot}
    (h : kmswSlotConnected w n S T) : kmswSlotVertex w S = kmswSlotVertex w T := by
  induction h with
  | rel A B h => exact kmswSlotLink_vertex w h.1
  | refl A => rfl
  | symm A B _ ih => exact ih.symm
  | trans A B C _ _ ih ih' => exact ih.trans ih'



theorem kmswSlot_exists_root (w : ℕ → Fin 3) (n : ℕ) (S : KMSWSlot)
    (hS : S.time ≤ n) :
    ∃ R, kmswSlotFresh w R ∧ R.time ≤ S.time ∧ kmswSlotConnected w n S R := by
  classical
  generalize ht : S.time = t
  induction t using Nat.strong_induction_on generalizing S with
  | h t ih =>
    by_cases hf : kmswSlotFresh w S
    · exact ⟨S, hf, by omega, Relation.EqvGen.refl S⟩
    · obtain ⟨T, hT⟩ := not_not.mp hf
      have hlt := kmswSlotLink_time w hT
      obtain ⟨R, hr, hrt, hconn⟩ := ih T.time (by omega) T (by omega) rfl
      refine ⟨R, hr, by omega, ?_⟩
      exact Relation.EqvGen.trans S T R
        (Relation.EqvGen.rel S T ⟨hT, hS, by omega⟩) hconn



theorem kmswSlotVertex_eq_iff (w : ℕ → Fin 3) (n : ℕ) (S T : KMSWSlot)
    (hS : S.time ≤ n) (hT : T.time ≤ n) :
    kmswSlotVertex w S = kmswSlotVertex w T ↔
      Relation.EqvGen
        (fun A B => kmswSlotLink w A B ∧ A.time ≤ n ∧ B.time ≤ n) S T := by
  constructor
  · intro hv
    obtain ⟨R, hr, _, hSR⟩ := kmswSlot_exists_root w n S hS
    obtain ⟨Q, hq, _, hTQ⟩ := kmswSlot_exists_root w n T hT
    have hR := kmswSlotConnected_vertex w hSR
    have hQ := kmswSlotConnected_vertex w hTQ
    have he : R = Q := kmswSlotFresh_injective w hr hq (hR.symm.trans (hv.trans hQ))
    subst Q
    exact Relation.EqvGen.trans S R T hSR (Relation.EqvGen.symm T R hTQ)
  · exact kmswSlotConnected_vertex w



theorem kmswSlotVertex_surjective (w : ℕ → Fin 3) (n : ℕ) (v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ S, S.time ≤ n ∧ kmswSlotVertex w S = v := by
  induction n with
  | zero =>
    change v < 2 at hv
    have hh : v = 0 ∨ v = 1 := by omega
    rcases hh with rfl | rfl
    · exact ⟨.west 0, le_rfl, rfl⟩
    · exact ⟨.east 0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases hold : v < (kmswStage w n).nextVertex
    · obtain ⟨S, hS, he⟩ := ih hold
      exact ⟨S, by omega, he⟩
    · rcases slot_codes (w n) with hc | hc | hc
      · cases hh : (kmswStage w n).UL.dropLast.reverse with
        | nil =>
          have hnv : (kmswStage w (n + 1)).nextVertex =
              (kmswStage w n).nextVertex + 1 := by
            simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh,
              State.addEdge]
          have he : (kmswStage w n).nextVertex = v := by omega
          exact ⟨.west (n + 1), le_rfl,
            (kmswStage_left_UL_nil_endpoints w n hc hh).1.trans he⟩
        | cons e es =>
          have hnv : (kmswStage w (n + 1)).nextVertex =
              (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh,
              State.addEdge]
          omega
      · have hnv : (kmswStage w (n + 1)).nextVertex =
            (kmswStage w n).nextVertex + 1 := by
          simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
        have he : (kmswStage w n).nextVertex = v := by omega
        exact ⟨.east (n + 1), le_rfl, (kmswStage_up_active_endpoints w n hc).2.trans he⟩
      · cases hh : (kmswStage w n).UR with
        | nil =>
          have hnv : (kmswStage w (n + 1)).nextVertex =
              (kmswStage w n).nextVertex + 1 := by
            simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh,
              State.addEdge]
          have he : (kmswStage w n).nextVertex = v := by omega
          exact ⟨.east (n + 1), le_rfl,
            (kmswStage_down_UR_nil_endpoints w n hc hh).2.trans he⟩
        | cons e es =>
          have hnv : (kmswStage w (n + 1)).nextVertex =
              (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hh]
          omega

end DirectedDistances.KMSW
