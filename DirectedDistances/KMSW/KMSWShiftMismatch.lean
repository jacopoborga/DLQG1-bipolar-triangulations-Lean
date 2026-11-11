module

public import DirectedDistances.KMSW.KMSWShiftEmbedding
import DirectedDistances.KMSW.StageIncidenceChains

/-! # Mismatch-aware shifted KMSW simulations

The simulation records avoidance of the unconsumed tails of the global
upper-right and upper-left boundary stacks. This is the extra information
needed when a shifted stack is empty before its global counterpart. -/

public section
namespace DirectedDistances.KMSW

/-! `Sim2` augments `Sim` with edge and endpoint avoidance on the parts of the
global boundary stacks that are not covered by the mapped shifted prefixes. -/
structure Sim2 (sh gl : State) (eφ vφ : ℕ → ℕ) : Prop where
  sim : Sim sh gl eφ vφ
  ur_edge_avoid : ∀ e, e ∈ gl.UR → e ∉ List.map eφ sh.UR →
    ∀ f, f < sh.nextEdge → eφ f ≠ e
  ur_east_avoid : ∀ e, e ∈ gl.UR → e ∉ List.map eφ sh.UR →
    ∀ v, v < sh.nextVertex → vφ v ≠ gl.east e
  ul_edge_avoid : ∀ e, e ∈ gl.UL.dropLast.reverse →
    e ∉ List.map eφ (sh.UL.dropLast.reverse) →
    ∀ f, f < sh.nextEdge → eφ f ≠ e
  ul_west_avoid : ∀ e, e ∈ gl.UL.dropLast.reverse →
    e ∉ List.map eφ (sh.UL.dropLast.reverse) →
    ∀ v, v < sh.nextVertex → vφ v ≠ gl.west e

/-- Down-mismatch extension: the shifted fresh edge is identified with the
first unconsumed global UR edge. -/
@[expose] def kmswShiftDownMismatchEdgeMap (sh : State) (e : ℕ)
    (eφ : ℕ → ℕ) : ℕ → ℕ :=
  fun f => if f = sh.nextEdge then e else eφ f

/-- Down-mismatch vertex extension: the shifted fresh vertex is identified
with the east endpoint of the consumed global UR edge. -/
@[expose] def kmswShiftDownMismatchVertexMap (sh gl : State) (e : ℕ)
    (vφ : ℕ → ℕ) : ℕ → ℕ :=
  fun v => if v = sh.nextVertex then gl.east e else vφ v

/-- Left-mismatch extension: the shifted active edge maps to the newly
allocated global active edge, and the shifted missing side maps to the first
unconsumed global predecessor. -/
@[expose] def kmswShiftLeftMismatchEdgeMap (sh gl : State) (e : ℕ)
    (eφ : ℕ → ℕ) : ℕ → ℕ :=
  fun f => if f = sh.nextEdge then gl.nextEdge
    else if f = sh.nextEdge + 1 then e else eφ f

/-- Left-mismatch vertex extension: the shifted fresh vertex maps to the
west endpoint of the consumed global predecessor. -/
@[expose] def kmswShiftLeftMismatchVertexMap (sh gl : State) (e : ℕ)
    (vφ : ℕ → ℕ) : ℕ → ℕ :=
  fun v => if v = sh.nextVertex then gl.west e else vφ v

/-- The down-mismatch extensions agree on all previously allocated IDs and
send the newly allocated IDs to the consumed global edge and its east -/
theorem kmswShiftDownMismatchMap_spec (sh gl : State) (e : ℕ)
    (eφ vφ : ℕ → ℕ) :
    (∀ f, f < sh.nextEdge →
      kmswShiftDownMismatchEdgeMap sh e eφ f = eφ f) ∧
    kmswShiftDownMismatchEdgeMap sh e eφ sh.nextEdge = e ∧
    (∀ v, v < sh.nextVertex →
      kmswShiftDownMismatchVertexMap sh gl e vφ v = vφ v) ∧
    kmswShiftDownMismatchVertexMap sh gl e vφ sh.nextVertex = gl.east e := by
  constructor
  · intro f hf
    simp [kmswShiftDownMismatchEdgeMap, ne_of_lt hf]
  constructor
  · simp [kmswShiftDownMismatchEdgeMap]
  constructor
  · intro v hv
    simp [kmswShiftDownMismatchVertexMap, ne_of_lt hv]
  · simp [kmswShiftDownMismatchVertexMap]

/-- The left-mismatch extensions preserve old IDs and give the new active,
missing, and vertex IDs their required global images (`def-kmsw`, -/
theorem kmswShiftLeftMismatchMap_spec (sh gl : State) (e : ℕ)
    (eφ vφ : ℕ → ℕ) :
    (∀ f, f < sh.nextEdge →
      kmswShiftLeftMismatchEdgeMap sh gl e eφ f = eφ f) ∧
    kmswShiftLeftMismatchEdgeMap sh gl e eφ sh.nextEdge = gl.nextEdge ∧
    kmswShiftLeftMismatchEdgeMap sh gl e eφ (sh.nextEdge + 1) = e ∧
    (∀ v, v < sh.nextVertex →
      kmswShiftLeftMismatchVertexMap sh gl e vφ v = vφ v) ∧
    kmswShiftLeftMismatchVertexMap sh gl e vφ sh.nextVertex = gl.west e := by
  constructor
  · intro f hf
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [kmswShiftLeftMismatchEdgeMap, hne0, hne1]
  constructor
  · simp [kmswShiftLeftMismatchEdgeMap]
  constructor
  · simp [kmswShiftLeftMismatchEdgeMap]
  constructor
  · intro v hv
    simp [kmswShiftLeftMismatchVertexMap, ne_of_lt hv]
  · simp [kmswShiftLeftMismatchVertexMap]

private theorem list_isChain_head_rel {α : Type} {R : α → α → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α) (a b : α), List.IsChain R (a :: l) → b ∈ l → R a b := by
  intro l
  induction l with
  | nil => intro a b hc hb; simp at hb
  | cons c l ih =>
    intro a b hc hb
    have hcons := List.isChain_cons_cons.mp hc
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hcons.1
    · exact htrans a c b hcons.1 (ih c b hcons.2 hb)

private theorem list_pairwise_of_isChain_trans {α : Type} {R : α → α → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c) {l : List α}
    (hchain : List.IsChain R l) : l.Pairwise R := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have htail : List.IsChain R l := hchain.tail
    rw [List.pairwise_cons]
    constructor
    · intro b hb
      exact list_isChain_head_rel htrans l a b hchain hb
    · exact ih htail

private theorem kmswStage_UR_east_rank_above_active
    (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) :
    kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) <
      kmswStageRank w n ((kmswStage w n).east e) := by
  let s := kmswStage w n
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hchain : List.IsChain (fun a b =>
      kmswStageRank w n (s.east a) < kmswStageRank w n (s.east b))
      (s.UL ++ s.UR) := by
    apply List.IsChain.imp_of_mem_tail_imp
      (R := fun a b => s.east a = s.west b)
      (S := fun a b => kmswStageRank w n (s.east a) <
        kmswStageRank w n (s.east b)) (l := s.UL ++ s.UR)
    · intro a b ha hb hab
      have hb' : b ∈ s.UL ++ s.UR := List.mem_of_mem_tail hb
      have hbAll : b ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
        simp only [List.mem_append] at hb' ⊢
        tauto
      have hboundB := (kmswStage_boundary_ids_lt_nextEdge w n).2 b (by
        simpa [s] using hbAll)
      have hstrict := kmswStageRank_strict w n b hboundB
      rw [← hab] at hstrict
      exact hstrict
    · exact (kmswStage_boundary_chain_invariant w n).1
  have hActUR : List.IsChain
      (fun a b => kmswStageRank w n (s.east a) < kmswStageRank w n (s.east b))
      (s.active :: s.UR) := by
    have htmp : List.IsChain
        (fun a b => kmswStageRank w n (s.east a) < kmswStageRank w n (s.east b))
        (xs ++ (s.active :: s.UR)) := by
      simpa [s, hUL, List.append_assoc] using hchain
    exact htmp.right_of_append
  have hmem : e ∈ s.UR := by simpa [s] using he
  exact hActUR.rel_cons hmem

private theorem kmswStage_ULpred_west_rank_below_active
    (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast.reverse) :
    kmswStageRank w n ((kmswStage w n).west e) <
      kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) := by
  let s := kmswStage w n
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hULchain : List.IsChain (fun a b =>
      kmswStageRank w n (s.west a) < kmswStageRank w n (s.west b)) s.UL := by
    have hInc : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
      (kmswStage_boundary_chain_invariant w n).1.left_of_append
    apply List.IsChain.imp_of_mem_tail_imp
      (R := fun a b => s.east a = s.west b)
      (S := fun a b => kmswStageRank w n (s.west a) <
        kmswStageRank w n (s.west b)) (l := s.UL)
    · intro a b ha hb hab
      have haAll : a ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
        simp only [List.mem_append]
        tauto
      have hboundA := (kmswStage_boundary_ids_lt_nextEdge w n).2 a (by
        simpa [s] using haAll)
      have hstrict := kmswStageRank_strict w n a hboundA
      rw [hab] at hstrict
      exact hstrict
    · exact hInc
  have hRev : List.IsChain (fun a b =>
      kmswStageRank w n (s.west a) > kmswStageRank w n (s.west b))
      (s.active :: xs.reverse) := by
    have hrev := (List.isChain_reverse).2 hULchain
    simpa [s, hUL, List.reverse_append] using hrev
  have hex : e ∈ xs.reverse := by simpa [s, hUL] using he
  exact hRev.rel_cons hex

private theorem kmswStage_UR_east_rank_chain
    (w : ℕ → Fin 3) (n : ℕ) :
    List.IsChain (fun a b => kmswStageRank w n
      ((kmswStage w n).east a) < kmswStageRank w n
      ((kmswStage w n).east b)) (kmswStage w n).UR := by
  let s := kmswStage w n
  apply List.IsChain.imp_of_mem_tail_imp
    (R := fun a b => s.east a = s.west b)
    (S := fun a b => kmswStageRank w n (s.east a) <
      kmswStageRank w n (s.east b)) (l := s.UR)
  · intro a b ha hb hab
    have hb' : b ∈ s.UR := List.mem_of_mem_tail hb
    have hbAll : b ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      tauto
    have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 b (by
      simpa [s] using hbAll)
    have hstrict := kmswStageRank_strict w n b hbound
    rw [← hab] at hstrict
    exact hstrict
  · exact (kmswStage_boundary_chain_invariant w n).1.right_of_append

private theorem kmswStage_UR_east_injective
    (w : ℕ → Fin 3) (n a b : ℕ)
    (ha : a ∈ (kmswStage w n).UR) (hb : b ∈ (kmswStage w n).UR)
    (hEq : (kmswStage w n).east a = (kmswStage w n).east b) : a = b := by
  let s := kmswStage w n
  let R := fun x y => kmswStageRank w n (s.east x) <
    kmswStageRank w n (s.east y)
  have hchain : List.IsChain R s.UR := by
    simpa [R, s] using kmswStage_UR_east_rank_chain w n
  have hpairLt : s.UR.Pairwise R :=
    list_pairwise_of_isChain_trans (α := ℕ) (R := R)
      (fun x y z hxy hyz => lt_trans hxy hyz) hchain
  have hpairNe : s.UR.Pairwise (fun x y =>
      kmswStageRank w n (s.east x) ≠ kmswStageRank w n (s.east y)) :=
    hpairLt.imp (fun hlt => ne_of_lt (by simpa [R] using hlt))
  have hsymm : Std.Symm (fun x y =>
      kmswStageRank w n (s.east x) ≠ kmswStageRank w n (s.east y)) :=
    ⟨fun _ _ h => h.symm⟩
  by_cases hab : a = b
  · exact hab
  · have hforall := @List.Pairwise.forall ℕ
      (fun x y => kmswStageRank w n (s.east x) ≠ kmswStageRank w n (s.east y))
      s.UR hsymm hpairNe
    have hneRank := hforall (by simpa [s] using ha)
      (by simpa [s] using hb) hab
    have hRankEq : kmswStageRank w n (s.east a) =
        kmswStageRank w n (s.east b) := congrArg (kmswStageRank w n) hEq
    exact False.elim (hneRank hRankEq)

private theorem kmswStage_UR_east_ne_ULpred_west
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UR)
    (hf : f ∈ (kmswStage w n).UL.dropLast.reverse) :
    (kmswStage w n).east e ≠ (kmswStage w n).west f := by
  have hUR := kmswStage_UR_east_rank_above_active w n e he
  have hUL := kmswStage_ULpred_west_rank_below_active w n f hf
  have hactive := kmswStageRank_strict w n _
      (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hlt := lt_trans hUL (lt_trans hactive hUR)
  intro heq
  have hrankEq := congrArg (kmswStageRank w n) heq
  linarith

private theorem kmswStage_UR_edge_ne_ULpred
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UR)
    (hf : f ∈ (kmswStage w n).UL.dropLast.reverse) : e ≠ f := by
  have heAll : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
      (kmswStage w n).LL ++ (kmswStage w n).LR := by
    simp only [List.mem_append]
    tauto
  have hboundE := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
  have hstatus := (kmswStage_status w n).1 e hboundE
  have hmissing : (kmswStage w n).present e = false :=
    hstatus.mpr (Or.inl he)
  have hfULdrop : f ∈ (kmswStage w n).UL.dropLast :=
    List.mem_reverse.mp hf
  have hfUL : f ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ hfULdrop
  have hpresent := (kmswStage_status w n).2.1 f hfUL
  intro hef
  subst f
  rw [hpresent] at hmissing
  cases hmissing

/-- The root simulation also avoids the unmapped parts of both global
boundary stacks. The endpoint exclusions follow from the strict stage rank
along the ordered boundary chain (`def-kmsw`, -/
theorem kmswShiftSim2_init (w : ℕ → Fin 3) (t : ℕ) :
    Sim2 kmswInit (kmswStage w t)
      (kmswShiftRootEdgeNatMap w t) (kmswShiftRootVertexNatMap w t) := by
  let eφ := kmswShiftRootEdgeNatMap w t
  let vφ := kmswShiftRootVertexNatMap w t
  have hact : (kmswStage w t).active < (kmswStage w t).nextEdge := by
    simpa [act] using act_lt_nextEdge w (Nat.le_refl t)
  have hactiveRank := kmswStageRank_strict w t _ hact
  refine {
    sim := kmswShiftSim_init w t
    ur_edge_avoid := ?_
    ur_east_avoid := ?_
    ul_edge_avoid := ?_
    ul_west_avoid := ?_ }
  · intro e he hnot f hf
    have heRank := kmswStage_UR_east_rank_above_active w t e he
    have hne : (kmswStage w t).active ≠ e := by
      intro heq
      subst e
      exact (lt_irrefl _ ) heRank
    have hf0 : f = 0 := by simp [kmswInit] at hf; omega
    subst f
    simpa [eφ, kmswShiftRootEdgeNatMap, act] using hne
  · intro e he hnot v hv
    have heRank := kmswStage_UR_east_rank_above_active w t e he
    have hvcases : v = 0 ∨ v = 1 := by
      simp [kmswInit] at hv
      omega
    rcases hvcases with hv0 | hv1
    · subst v
      have hneq : (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val ≠
          (kmswStage w t).east e := by
        intro heq
        have hrankEq := congrArg (kmswStageRank w t) heq
        have hlt := heRank
        have hltActive := hactiveRank
        simp [kmswShiftRootVertexMap] at hrankEq
        rw [← hrankEq] at hlt
        linarith
      simpa [vφ, kmswShiftRootVertexNatMap] using hneq
    · subst v
      have hneq : (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val ≠
          (kmswStage w t).east e := by
        intro heq
        have hrankEq := congrArg (kmswStageRank w t) heq
        have hlt := heRank
        simp [kmswShiftRootVertexMap] at hrankEq
        rw [← hrankEq] at hlt
        exact (lt_irrefl _) hlt
      simpa [vφ, kmswShiftRootVertexNatMap] using hneq
  · intro e he hnot f hf
    have heRank := kmswStage_ULpred_west_rank_below_active w t e he
    have hne : (kmswStage w t).active ≠ e := by
      intro heq
      subst e
      exact (lt_irrefl _) heRank
    have hf0 : f = 0 := by simp [kmswInit] at hf; omega
    subst f
    simpa [eφ, kmswShiftRootEdgeNatMap, act] using hne
  · intro e he hnot v hv
    have heRank := kmswStage_ULpred_west_rank_below_active w t e he
    have hvcases : v = 0 ∨ v = 1 := by
      simp [kmswInit] at hv
      omega
    rcases hvcases with hv0 | hv1
    · subst v
      have hneq : (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val ≠
          (kmswStage w t).west e := by
        intro heq
        have hrankEq := congrArg (kmswStageRank w t) heq
        simp [kmswShiftRootVertexMap] at hrankEq
        rw [← hrankEq] at heRank
        exact (lt_irrefl _) heRank
      simpa [vφ, kmswShiftRootVertexNatMap] using hneq
    · subst v
      have hneq : (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val ≠
          (kmswStage w t).west e := by
        intro heq
        have hrankEq := congrArg (kmswStageRank w t) heq
        have hstrict := hactiveRank
        simp [kmswShiftRootVertexMap] at hrankEq
        rw [← hrankEq] at heRank
        linarith
      simpa [vφ, kmswShiftRootVertexNatMap] using hneq

/-- In the down mismatch, the consumed first global UR edge and its east
endpoint remain avoided by the mapped shifted allocation on the unconsumed
global UR tail. The stage rank proves the needed endpoint separation. -/
theorem kmswShiftDownMismatch_ur_avoidance
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (e : ℕ) (es : List ℕ)
    (hshUR : (kmswStage u m).UR = [])
    (hglUR : (kmswStage w n).UR = e :: es) :
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .down).UR →
      f ∉ List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
        (kmswStepOfStep (kmswStage u m) .down).UR →
      ∀ x, x < (kmswStepOfStep (kmswStage u m) .down).nextEdge →
        kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ x ≠ f) ∧
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .down).UR →
      f ∉ List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
        (kmswStepOfStep (kmswStage u m) .down).UR →
      ∀ v, v < (kmswStepOfStep (kmswStage u m) .down).nextVertex →
        kmswShiftDownMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ v ≠
          (kmswStepOfStep (kmswStage w n) .down).east f) := by
  have hndCons : (e :: es).Nodup := by
    simpa [hglUR] using (kmswStage_status w n).2.2.2.1
  have heNotTail : e ∉ es := (List.nodup_cons.mp hndCons).1
  have hshPostUR :
      (kmswStepOfStep (kmswStage u m) .down).UR = [] := by
    simp [kmswStepOfStep, State.addEdge, hshUR]
  have hglPostUR :
      (kmswStepOfStep (kmswStage w n) .down).UR = es := by
    simp [kmswStepOfStep, hglUR]
  have heGlobal : e ∈ (kmswStage w n).UR := by rw [hglUR]; simp
  have hnotMapped : e ∉ List.map eφ (kmswStage u m).UR := by simp [hshUR]
  constructor
  · intro f hf hnot x hx
    have hfTail : f ∈ es := by simpa [hglPostUR] using hf
    have hfGlobal : f ∈ (kmswStage w n).UR := by
      rw [hglUR]
      exact List.mem_cons_of_mem _ hfTail
    have hclass : x < (kmswStage u m).nextEdge ∨
        x = (kmswStage u m).nextEdge := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at hx
      omega
    rcases hclass with hxOld | rfl
    · have havoid := hsim.ur_edge_avoid f hfGlobal (by simp [hshUR]) x hxOld
      have hne : x ≠ (kmswStage u m).nextEdge := by omega
      simpa [kmswShiftDownMismatchEdgeMap, hne] using havoid
    · have hne : e ≠ f := by
        intro hef
        exact heNotTail (by simpa [← hef] using hfTail)
      simpa [kmswShiftDownMismatchEdgeMap] using hne
  · intro f hf hnot v hv
    have hfTail : f ∈ es := by simpa [hglPostUR] using hf
    have hfGlobal : f ∈ (kmswStage w n).UR := by
      rw [hglUR]
      exact List.mem_cons_of_mem _ hfTail
    have hclass : v < (kmswStage u m).nextVertex ∨
        v = (kmswStage u m).nextVertex := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at hv
      omega
    rcases hclass with hvOld | rfl
    · have havoid := hsim.ur_east_avoid f hfGlobal (by simp [hshUR]) v hvOld
      have hne : v ≠ (kmswStage u m).nextVertex := by omega
      simpa [kmswShiftDownMismatchVertexMap, hne,
        kmswStepOfStep, hglUR] using havoid
    · have heq := kmswStage_UR_east_injective w n e f heGlobal hfGlobal
      have hne : (kmswStage w n).east e ≠ (kmswStage w n).east f := by
        intro hEq
        have hef := heq hEq
        have hmem : e ∈ es := by rw [hef]; exact hfTail
        exact heNotTail hmem
      simpa [kmswShiftDownMismatchVertexMap,
        kmswStepOfStep, hglUR] using hne

/-- The down mismatch also preserves avoidance of the unconsumed global
UL-predecessor stack. The newly mapped edge and vertex are separated from
that stack by the global stage boundary chain. -/
theorem kmswShiftDownMismatch_ul_avoidance
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (e : ℕ) (es : List ℕ)
    (hshUR : (kmswStage u m).UR = [])
    (hglUR : (kmswStage w n).UR = e :: es) :
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .down).UL.dropLast.reverse →
      f ∉ List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
        ((kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse) →
      ∀ x, x < (kmswStepOfStep (kmswStage u m) .down).nextEdge →
        kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ x ≠ f) ∧
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .down).UL.dropLast.reverse →
      f ∉ List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
        ((kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse) →
      ∀ v, v < (kmswStepOfStep (kmswStage u m) .down).nextVertex →
        kmswShiftDownMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ v ≠
          (kmswStepOfStep (kmswStage w n) .down).west f) := by
  have hshPred : (kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse =
      (kmswStage u m).active :: (kmswStage u m).UL.dropLast.reverse := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last u m
    simp [kmswStepOfStep, hshUR, hUL, List.reverse_append]
  have hglPred : (kmswStepOfStep (kmswStage w n) .down).UL.dropLast.reverse =
      (kmswStage w n).active :: (kmswStage w n).UL.dropLast.reverse := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
    simp [kmswStepOfStep, hglUR, hUL, List.reverse_append]
  have hactBound := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hmapOld : List.map (kmswShiftDownMismatchEdgeMap
      (kmswStage u m) e eφ) ((kmswStage u m).UL.dropLast.reverse) =
      List.map eφ ((kmswStage u m).UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro f hf
    have hfUL : f ∈ (kmswStage u m).UL :=
      List.dropLast_subset _ (List.mem_reverse.mp hf)
    have hfAll : f ∈ (kmswStage u m).UL ++ (kmswStage u m).UR ++
        (kmswStage u m).LL ++ (kmswStage u m).LR := by
      simp only [List.mem_append]
      tauto
    have hbound := (kmswStage_boundary_ids_lt_nextEdge u m).2 f hfAll
    simp [kmswShiftDownMismatchEdgeMap, ne_of_lt hbound]
  have hmapPred : List.map (kmswShiftDownMismatchEdgeMap
      (kmswStage u m) e eφ)
      ((kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse) =
      (kmswStage w n).active ::
        List.map eφ ((kmswStage u m).UL.dropLast.reverse) := by
    rw [hshPred, List.map_cons, hmapOld]
    have hactiveMap : kmswShiftDownMismatchEdgeMap
        (kmswStage u m) e eφ (kmswStage u m).active =
        (kmswStage w n).active := by
      have hne : (kmswStage u m).active ≠ (kmswStage u m).nextEdge := by omega
      simpa [kmswShiftDownMismatchEdgeMap, hne] using hsim.sim.active
    rw [hactiveMap]
  have heGlobal : e ∈ (kmswStage w n).UR := by rw [hglUR]; simp
  constructor
  · intro f hf hnot x hx
    have hfParts : f = (kmswStage w n).active ∨
        f ∈ (kmswStage w n).UL.dropLast.reverse := by
      simpa [hglPred] using hf
    rcases hfParts with hfHead | hfTail
    · subst f
      have hmem : (kmswStage w n).active ∈
          List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
            ((kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    ·
      have hnotOld : f ∉ List.map eφ ((kmswStage u m).UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hclass : x < (kmswStage u m).nextEdge ∨
          x = (kmswStage u m).nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hshUR] at hx
        omega
      rcases hclass with hxOld | rfl
      · have havoid := hsim.ul_edge_avoid f hfTail hnotOld x hxOld
        have hne : x ≠ (kmswStage u m).nextEdge := by omega
        simpa [kmswShiftDownMismatchEdgeMap, hne] using havoid
      · have hne := kmswStage_UR_edge_ne_ULpred w n e f heGlobal hfTail
        simpa [kmswShiftDownMismatchEdgeMap] using hne
  · intro f hf hnot v hv
    have hfParts : f = (kmswStage w n).active ∨
        f ∈ (kmswStage w n).UL.dropLast.reverse := by
      simpa [hglPred] using hf
    rcases hfParts with hfHead | hfTail
    · subst f
      have hmem : (kmswStage w n).active ∈
          List.map (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
            ((kmswStepOfStep (kmswStage u m) .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    ·
      have hnotOld : f ∉ List.map eφ ((kmswStage u m).UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hclass : v < (kmswStage u m).nextVertex ∨
          v = (kmswStage u m).nextVertex := by
        simp [kmswStepOfStep, State.addEdge, hshUR] at hv
        omega
      rcases hclass with hvOld | rfl
      · have havoid := hsim.ul_west_avoid f hfTail hnotOld v hvOld
        have hne : v ≠ (kmswStage u m).nextVertex := by omega
        simpa [kmswShiftDownMismatchVertexMap, hne,
          kmswStepOfStep, hglUR] using havoid
      · have hne := kmswStage_UR_east_ne_ULpred_west w n e f heGlobal hfTail
        simpa [kmswShiftDownMismatchVertexMap,
          kmswStepOfStep, hglUR] using hne

end DirectedDistances.KMSW
