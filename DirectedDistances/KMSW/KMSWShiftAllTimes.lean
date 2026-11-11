module

public import DirectedDistances.KMSW.KMSWShiftStep
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.CutEquivalence

/-! # All-time shifted KMSW simulations

Finite-stage simulations for a shifted KMSW code, and their consequences for -/

public section
namespace DirectedDistances.KMSW
open Quiver

private theorem kmswShiftAll_stage_UR_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) : e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  simp only [List.mem_append]
  tauto

private theorem kmswShiftAll_stage_ULpred_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast.reverse) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  have heUL : e ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ (List.mem_reverse.mp he)
  simp only [List.mem_append]
  tauto

private theorem kmswShift_list_isChain_head_rel {α : Type} {R : α → α → Prop}
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

private theorem kmswShift_list_pairwise_of_isChain_trans {α : Type}
    {R : α → α → Prop} (htrans : ∀ a b c, R a b → R b c → R a c)
    {l : List α} (hchain : List.IsChain R l) : l.Pairwise R := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have htail : List.IsChain R l := hchain.tail
    rw [List.pairwise_cons]
    constructor
    · intro b hb
      exact kmswShift_list_isChain_head_rel htrans l a b hchain hb
    · exact ih htail

private theorem kmswShift_ULpred_west_rank_below_active
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

private theorem kmswShift_UR_east_rank_above_active
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
      (fun a b => kmswStageRank w n (s.east a) <
        kmswStageRank w n (s.east b)) (s.active :: s.UR) := by
    have htmp : List.IsChain
        (fun a b => kmswStageRank w n (s.east a) <
          kmswStageRank w n (s.east b)) (xs ++ (s.active :: s.UR)) := by
      simpa [s, hUL, List.append_assoc] using hchain
    exact htmp.right_of_append
  have hmem : e ∈ s.UR := by simpa [s] using he
  exact hActUR.rel_cons hmem

private theorem kmswShift_UR_east_ne_ULpred_west
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UR)
    (hf : f ∈ (kmswStage w n).UL.dropLast.reverse) :
    (kmswStage w n).east e ≠ (kmswStage w n).west f := by
  have hUR := kmswShift_UR_east_rank_above_active w n e he
  have hUL := kmswShift_ULpred_west_rank_below_active w n f hf
  have hactive := kmswStageRank_strict w n _
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hlt := lt_trans hUL (lt_trans hactive hUR)
  intro heq
  have hrankEq := congrArg (kmswStageRank w n) heq
  linarith

private theorem kmswShift_UR_edge_ne_ULpred
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UR)
    (hf : f ∈ (kmswStage w n).UL.dropLast.reverse) : e ≠ f := by
  have heAll : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
      (kmswStage w n).LL ++ (kmswStage w n).LR := by
    simp only [List.mem_append]
    tauto
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
  have hmissing := ((kmswStage_status w n).1 e hbound).mpr (Or.inl he)
  have hfUL : f ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ (List.mem_reverse.mp hf)
  have hpresent := (kmswStage_status w n).2.1 f hfUL
  intro hef
  subst f
  rw [hpresent] at hmissing
  cases hmissing

private theorem kmswShift_UL_west_rank_ne
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UL)
    (hf : f ∈ (kmswStage w n).UL) (hne : e ≠ f) :
    kmswStageRank w n ((kmswStage w n).west e) ≠
      kmswStageRank w n ((kmswStage w n).west f) := by
  let s := kmswStage w n
  let R := fun a b => kmswStageRank w n (s.west a) <
    kmswStageRank w n (s.west b)
  have hchain : List.IsChain R s.UL := by
    have hInc : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
      (kmswStage_boundary_chain_invariant w n).1.left_of_append
    apply List.IsChain.imp_of_mem_tail_imp
      (R := fun a b => s.east a = s.west b) (S := R) (l := s.UL)
    · intro a b ha hb hab
      have haAll : a ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
        simp only [List.mem_append]
        tauto
      have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 a (by
        simpa [s] using haAll)
      have hstrict := kmswStageRank_strict w n a hbound
      rw [hab] at hstrict
      exact hstrict
    · exact hInc
  have hpairLt := kmswShift_list_pairwise_of_isChain_trans
    (α := ℕ) (R := R) (fun a b c hab hbc => lt_trans hab hbc) hchain
  have hpairNe : s.UL.Pairwise (fun a b =>
      kmswStageRank w n (s.west a) ≠ kmswStageRank w n (s.west b)) :=
    hpairLt.imp (fun hlt => ne_of_lt (by simpa [R] using hlt))
  have hsymm : Std.Symm (fun a b =>
      kmswStageRank w n (s.west a) ≠ kmswStageRank w n (s.west b)) :=
    ⟨fun _ _ h => h.symm⟩
  have hforall := @List.Pairwise.forall ℕ
    (fun a b => kmswStageRank w n (s.west a) ≠ kmswStageRank w n (s.west b))
    s.UL hsymm hpairNe
  exact hforall (by simpa [s] using he) (by simpa [s] using hf) hne

private theorem kmswShift_ULpred_west_injective
    (w : ℕ → Fin 3) (n e f : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast.reverse)
    (hf : f ∈ (kmswStage w n).UL.dropLast.reverse)
    (hEq : (kmswStage w n).west e = (kmswStage w n).west f) : e = f := by
  by_contra hne
  have heUL : e ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ (List.mem_reverse.mp he)
  have hfUL : f ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ (List.mem_reverse.mp hf)
  have hneRank := kmswShift_UL_west_rank_ne w n e f heUL hfUL hne
  exact hneRank (congrArg (kmswStageRank w n) hEq)

private theorem kmswShift_ULpred_head_west_rank_gt_tail
    (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ) (f : ℕ)
    (hpred : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (hf : f ∈ es) :
    kmswStageRank w n ((kmswStage w n).west f) <
      kmswStageRank w n ((kmswStage w n).west e) := by
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
  have hrev : List.IsChain (fun a b =>
      kmswStageRank w n (s.west a) > kmswStageRank w n (s.west b))
      (s.active :: xs.reverse) := by
    have hrev' := (List.isChain_reverse).2 hULchain
    simpa [s, hUL, List.reverse_append] using hrev'
  have hxs : xs.reverse = e :: es := by
    simpa [s, hUL, List.reverse_append] using hpred
  have hpredChain : List.IsChain (fun a b =>
      kmswStageRank w n (s.west a) > kmswStageRank w n (s.west b))
      (e :: es) := by
    rw [← hxs]
    exact hrev.tail
  have hgt := kmswShift_list_isChain_head_rel
    (R := fun a b => kmswStageRank w n (s.west a) >
      kmswStageRank w n (s.west b))
    (fun a b c hab hbc => lt_trans hbc hab) es e f hpredChain hf
  exact hgt

private theorem kmswShiftLeftMismatch_ur_avoidance
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : (kmswStage u m).UL.dropLast.reverse = [])
    (hglPred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .left).UR →
      f ∉ List.map (kmswShiftLeftMismatchEdgeMap (kmswStage u m)
        (kmswStage w n) e eφ) ((kmswStepOfStep (kmswStage u m) .left).UR) →
      ∀ x, x < (kmswStepOfStep (kmswStage u m) .left).nextEdge →
        kmswShiftLeftMismatchEdgeMap (kmswStage u m) (kmswStage w n) e eφ x ≠ f) ∧
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .left).UR →
      f ∉ List.map (kmswShiftLeftMismatchEdgeMap (kmswStage u m)
        (kmswStage w n) e eφ) ((kmswStepOfStep (kmswStage u m) .left).UR) →
      ∀ v, v < (kmswStepOfStep (kmswStage u m) .left).nextVertex →
        kmswShiftLeftMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ v ≠
          (kmswStepOfStep (kmswStage w n) .left).east f) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftLeftMismatchEdgeMap sh gl e eφ
  let vψ := kmswShiftLeftMismatchVertexMap sh gl e vφ
  change sh.UL.dropLast.reverse = [] at hshPred
  change gl.UL.dropLast.reverse = e :: es at hglPred
  have hshURPost : (kmswStepOfStep sh .left).UR = sh.UR := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglURPost : (kmswStepOfStep gl .left).UR = gl.UR := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro f hf
    have hb := kmswShiftAll_stage_UR_bound u m f hf
    change f < sh.nextEdge at hb
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftLeftMismatchEdgeMap, hne0, hne1]
  have hePred : e ∈ gl.UL.dropLast.reverse := by rw [hglPred]; simp
  constructor
  · intro f hf hnot x hx
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
        x = sh.nextEdge + 1 := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxActive | hxMissing
    · have havoid := hsim.ur_edge_avoid f hfGlobal hnotOld x hxOld
      have hne0 : x ≠ sh.nextEdge := by omega
      have hne1 : x ≠ sh.nextEdge + 1 := by omega
      change eψ x ≠ f
      simpa [eψ, kmswShiftLeftMismatchEdgeMap, hne0, hne1] using havoid
    · subst x
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftLeftMismatchEdgeMap]
      omega
    · subst x
      have hne := kmswShift_UR_edge_ne_ULpred w n f e hfGlobal hePred
      change eψ (sh.nextEdge + 1) ≠ f
      simpa [eψ, kmswShiftLeftMismatchEdgeMap] using hne.symm
  · intro f hf hnot v hv
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | hvFresh
    · have havoid := hsim.ur_east_avoid f hfGlobal hnotOld v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hneF : f ≠ gl.nextEdge := by omega
      change vψ v ≠ (kmswStepOfStep gl .left).east f
      simpa [vψ, kmswShiftLeftMismatchVertexMap, hneV,
        kmswStepOfStep, hglPred, State.addEdge, hneF] using havoid
    · subst v
      have hsep := kmswShift_UR_east_ne_ULpred_west w n f e hfGlobal hePred
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hneF : f ≠ gl.nextEdge := by omega
      change vψ sh.nextVertex ≠ (kmswStepOfStep gl .left).east f
      simpa [vψ, kmswShiftLeftMismatchVertexMap,
        kmswStepOfStep, hglPred, State.addEdge, hneF] using hsep.symm

private theorem kmswShiftLeftMismatch_ul_avoidance
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : (kmswStage u m).UL.dropLast.reverse = [])
    (hglPred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .left).UL.dropLast.reverse →
      f ∉ List.map (kmswShiftLeftMismatchEdgeMap (kmswStage u m)
        (kmswStage w n) e eφ)
        ((kmswStepOfStep (kmswStage u m) .left).UL.dropLast.reverse) →
      ∀ x, x < (kmswStepOfStep (kmswStage u m) .left).nextEdge →
        kmswShiftLeftMismatchEdgeMap (kmswStage u m) (kmswStage w n) e eφ x ≠ f) ∧
    (∀ f, f ∈ (kmswStepOfStep (kmswStage w n) .left).UL.dropLast.reverse →
      f ∉ List.map (kmswShiftLeftMismatchEdgeMap (kmswStage u m)
        (kmswStage w n) e eφ)
        ((kmswStepOfStep (kmswStage u m) .left).UL.dropLast.reverse) →
      ∀ v, v < (kmswStepOfStep (kmswStage u m) .left).nextVertex →
        kmswShiftLeftMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ v ≠
          (kmswStepOfStep (kmswStage w n) .left).west f) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftLeftMismatchEdgeMap sh gl e eφ
  let vψ := kmswShiftLeftMismatchVertexMap sh gl e vφ
  change sh.UL.dropLast.reverse = [] at hshPred
  change gl.UL.dropLast.reverse = e :: es at hglPred
  have hshPostPred : (kmswStepOfStep sh .left).UL.dropLast.reverse = [] := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglPostPred : (kmswStepOfStep gl .left).UL.dropLast.reverse = es := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  constructor
  · intro f hf hnot x hx
    have hfTail : f ∈ es := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPostPred] at hf
      exact hf
    have hfGlobalPred : f ∈ gl.UL.dropLast.reverse := by
      rw [hglPred]
      exact List.mem_cons_of_mem e hfTail
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
        x = sh.nextEdge + 1 := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxActive | hxMissing
    · have hnotPred : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        rw [hshPred]
        simp
      have havoid := hsim.ul_edge_avoid f hfGlobalPred hnotPred x hxOld
      have hne0 : x ≠ sh.nextEdge := by omega
      have hne1 : x ≠ sh.nextEdge + 1 := by omega
      change eψ x ≠ f
      simpa [eψ, kmswShiftLeftMismatchEdgeMap, hne0, hne1] using havoid
    · subst x
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f (by
        rw [hglPred]
        exact List.mem_cons_of_mem e hfTail)
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftLeftMismatchEdgeMap]
      omega
    · subst x
      have hrank := kmswShift_ULpred_head_west_rank_gt_tail w n e es f hglPred hfTail
      have hne : e ≠ f := by
        intro heq
        rw [heq] at hrank
        exact (lt_irrefl _ hrank)
      change eψ (sh.nextEdge + 1) ≠ f
      simpa [eψ, kmswShiftLeftMismatchEdgeMap] using hne
  · intro f hf hnot v hv
    have hfTail : f ∈ es := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPostPred] at hf
      exact hf
    have hfGlobalPred : f ∈ gl.UL.dropLast.reverse := by
      rw [hglPred]
      exact List.mem_cons_of_mem e hfTail
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | hvFresh
    · have hnotPred : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        rw [hshPred]
        simp
      have havoid := hsim.ul_west_avoid f hfGlobalPred hnotPred v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f (by
        rw [hglPred]
        exact List.mem_cons_of_mem e hfTail)
      change f < gl.nextEdge at hfBound
      have hneF : f ≠ gl.nextEdge := by omega
      change vψ v ≠ (kmswStepOfStep gl .left).west f
      simpa [vψ, kmswShiftLeftMismatchVertexMap, hneV,
        kmswStepOfStep, hglPred, State.addEdge, hneF] using havoid
    · subst v
      have hrank := kmswShift_ULpred_head_west_rank_gt_tail w n e es f hglPred hfTail
      have hne : gl.west e ≠ gl.west f := by
        intro heq
        have hrankEq := congrArg (kmswStageRank w n) heq
        rw [hrankEq] at hrank
        exact (lt_irrefl _ hrank)
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hfGlobalPred
      change f < gl.nextEdge at hfBound
      have hneF : f ≠ gl.nextEdge := by omega
      change vψ sh.nextVertex ≠ (kmswStepOfStep gl .left).west f
      simpa [vψ, kmswShiftLeftMismatchVertexMap,
        kmswStepOfStep, hglPred, State.addEdge, hne, hneF] using hne

/-- A left mismatch preserves the full avoidance-aware simulation when the
shifted run has no predecessor and the global run consumes its nearest -/
theorem kmswShiftSim2_step_left_mismatch
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : (kmswStage u m).UL.dropLast.reverse = [])
    (hglPred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    Sim2 (kmswStepOfStep (kmswStage u m) .left)
      (kmswStepOfStep (kmswStage w n) .left)
      (kmswShiftLeftMismatchEdgeMap (kmswStage u m) (kmswStage w n) e eφ)
      (kmswShiftLeftMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ) := by
  refine ⟨kmswShiftSim_step_left_mismatch u w m n e es eφ vφ hsim
    hshPred hglPred, ?_, ?_, ?_, ?_⟩
  · exact (kmswShiftLeftMismatch_ur_avoidance u w m n e es eφ vφ
      hsim hshPred hglPred).1
  · exact (kmswShiftLeftMismatch_ur_avoidance u w m n e es eφ vφ
      hsim hshPred hglPred).2
  · exact (kmswShiftLeftMismatch_ul_avoidance u w m n e es eφ vφ
      hsim hshPred hglPred).1
  · exact (kmswShiftLeftMismatch_ul_avoidance u w m n e es eφ vφ
      hsim hshPred hglPred).2

/-- A matched left step with empty predecessor stacks preserves the full
avoidance-aware simulation (`def-kmsw`, -/
theorem kmswShiftSim2_step_left_empty
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : (kmswStage u m).UL.dropLast.reverse = [])
    (hglPred : (kmswStage w n).UL.dropLast.reverse = []) :
    Sim2 (kmswStepOfStep (kmswStage u m) .left)
      (kmswStepOfStep (kmswStage w n) .left)
      (kmswShiftUpEdgeMap (kmswStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswStage u m) (kmswStage w n) vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  let vψ := kmswShiftUpVertexMap sh gl vφ
  change sh.UL.dropLast.reverse = [] at hshPred
  change gl.UL.dropLast.reverse = [] at hglPred
  have hshActive : sh.active < sh.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hshEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex := by
    intro e he
    exact kmswStage_endpoints_lt_nextVertex u m e he
  have hshURBound : ∀ e ∈ sh.UR, e < sh.nextEdge := by
    intro e he
    exact kmswShiftAll_stage_UR_bound u m e he
  have hshPredBound : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    exact kmswShiftAll_stage_ULpred_bound u m e he
  have hsimStep : Sim (kmswStepOfStep sh .left) (kmswStepOfStep gl .left) eψ vψ :=
    kmswShiftSim_step_left_empty sh gl eφ vφ hshActive hshEndpoints
      hshPred hglPred hshURBound hsim.sim
  have hshURPost : (kmswStepOfStep sh .left).UR = sh.UR := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglURPost : (kmswStepOfStep gl .left).UR = gl.UR := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  have hshPredPost : (kmswStepOfStep sh .left).UL.dropLast.reverse =
      sh.UL.dropLast.reverse := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglPredPost : (kmswStepOfStep gl .left).UL.dropLast.reverse =
      gl.UL.dropLast.reverse := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro f hf
    have hb := kmswShiftAll_stage_UR_bound u m f hf
    change f < sh.nextEdge at hb
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
  have hmapPred : List.map eψ (sh.UL.dropLast.reverse) =
      List.map eφ (sh.UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro f hf
    have hb := hshPredBound f hf
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
  refine ⟨hsimStep, ?_, ?_, ?_, ?_⟩
  · intro f hf hnot x hx
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
        x = sh.nextEdge + 1 := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxActive | hxMissing
    · have havoid := hsim.ur_edge_avoid f hfGlobal hnotOld x hxOld
      have hne0 : x ≠ sh.nextEdge := by omega
      have hne1 : x ≠ sh.nextEdge + 1 := by omega
      simpa [eψ, sh, kmswShiftUpEdgeMap, hne0, hne1] using havoid
    · subst x
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftUpEdgeMap]
      omega
    · subst x
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ (sh.nextEdge + 1) ≠ f
      simp [eψ, kmswShiftUpEdgeMap]
      omega
  · intro f hf hnot v hv
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | hvFresh
    · have havoid := hsim.ur_east_avoid f hfGlobal hnotOld v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hne0 : f ≠ gl.nextEdge := by omega
      have hne1 : f ≠ gl.nextEdge + 1 := by omega
      change vψ v ≠ (kmswStepOfStep gl .left).east f
      simpa [vψ, kmswShiftUpVertexMap, hneV,
        kmswStepOfStep, hglPred, State.addEdge, hne0, hne1] using havoid
    · subst v
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hend := kmswStage_endpoints_lt_nextVertex w n f hfBound
      have hne0 : f ≠ gl.nextEdge := by omega
      have hne1 : f ≠ gl.nextEdge + 1 := by omega
      change vψ sh.nextVertex ≠ (kmswStepOfStep gl .left).east f
      simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep,
        hglPred, State.addEdge, hne0, hne1] using (ne_of_lt hend.2).symm
  · intro f hf hnot x hx
    have hfGlobal : f ∈ gl.UL.dropLast.reverse := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPredPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UL.dropLast.reverse) at hnot
      rw [hshPredPost, hmapPred] at hnot
      exact hnot
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
        x = sh.nextEdge + 1 := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxActive | hxMissing
    · have havoid := hsim.ul_edge_avoid f hfGlobal hnotOld x hxOld
      have hne0 : x ≠ sh.nextEdge := by omega
      have hne1 : x ≠ sh.nextEdge + 1 := by omega
      simpa [eψ, sh, kmswShiftUpEdgeMap, hne0, hne1] using havoid
    · subst x
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftUpEdgeMap]
      omega
    · subst x
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ (sh.nextEdge + 1) ≠ f
      simp [eψ, kmswShiftUpEdgeMap]
      omega
  · intro f hf hnot v hv
    have hfGlobal : f ∈ gl.UL.dropLast.reverse := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPredPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UL.dropLast.reverse) at hnot
      rw [hshPredPost, hmapPred] at hnot
      exact hnot
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | hvFresh
    · have havoid := hsim.ul_west_avoid f hfGlobal hnotOld v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hne0 : f ≠ gl.nextEdge := by omega
      have hne1 : f ≠ gl.nextEdge + 1 := by omega
      change vψ v ≠ (kmswStepOfStep gl .left).west f
      simpa [vψ, kmswShiftUpVertexMap, hneV,
        kmswStepOfStep, hglPred, State.addEdge, hne0, hne1] using havoid
    · subst v
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      have hend := kmswStage_endpoints_lt_nextVertex w n f hfBound
      have hne0 : f ≠ gl.nextEdge := by omega
      have hne1 : f ≠ gl.nextEdge + 1 := by omega
      change vψ sh.nextVertex ≠ (kmswStepOfStep gl .left).west f
      simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep,
        hglPred, State.addEdge, hne0, hne1] using (ne_of_lt hend.1).symm

/-- A matched left step with nonempty predecessor stacks preserves the full
avoidance-aware simulation (`def-kmsw`, -/
theorem kmswShiftSim2_step_left_nonempty
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : ∃ a as, (kmswStage u m).UL.dropLast.reverse = a :: as)
    (hglPred : ∃ b bs, (kmswStage w n).UL.dropLast.reverse = b :: bs) :
    Sim2 (kmswStepOfStep (kmswStage u m) .left)
      (kmswStepOfStep (kmswStage w n) .left)
      (kmswShiftFreshEdgeMap (kmswStage u m) (kmswStage w n) eφ) vφ := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftFreshEdgeMap sh gl eφ
  obtain ⟨a, as, hshPred⟩ := hshPred
  obtain ⟨b, bs, hglPred⟩ := hglPred
  change sh.UL.dropLast.reverse = a :: as at hshPred
  change gl.UL.dropLast.reverse = b :: bs at hglPred
  have hshActive : sh.active < sh.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hshPredBound : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    exact kmswShiftAll_stage_ULpred_bound u m e he
  have hshURBound : ∀ e ∈ sh.UR, e < sh.nextEdge := by
    intro e he
    exact kmswShiftAll_stage_UR_bound u m e he
  have hsimStep : Sim (kmswStepOfStep sh .left) (kmswStepOfStep gl .left)
      eψ vφ := by
    simpa [kmswStep, kmswCodeStep] using
      (kmswShiftSim_step_left_nonempty sh gl eφ vφ hshActive
        ⟨a, as, hshPred⟩ hshPredBound hshURBound hsim.sim)
  have hshURPost : (kmswStepOfStep sh .left).UR = sh.UR := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglURPost : (kmswStepOfStep gl .left).UR = gl.UR := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  have hshPredPost : (kmswStepOfStep sh .left).UL.dropLast.reverse = as := by
    simp [kmswStepOfStep, hshPred]
  have hglPredPost : (kmswStepOfStep gl .left).UL.dropLast.reverse = bs := by
    simp [kmswStepOfStep, hglPred]
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro f hf
    have hb := kmswShiftAll_stage_UR_bound u m f hf
    change f < sh.nextEdge at hb
    have hne : f ≠ sh.nextEdge := by omega
    simp [eψ, kmswShiftFreshEdgeMap, hne]
  have hmapTail : List.map eψ as = List.map eφ as := by
    apply List.map_congr_left
    intro f hf
    have hb := hshPredBound f (by rw [hshPred]; exact List.mem_cons_of_mem _ hf)
    have hne : f ≠ sh.nextEdge := by omega
    simp [eψ, kmswShiftFreshEdgeMap, hne]
  have hprefix0 : List.map eφ (sh.UL.dropLast.reverse) <+:
      gl.UL.dropLast.reverse := hsim.sim.ul_predecessors_prefix
  rw [hshPred, hglPred] at hprefix0
  have hprefix : eφ a :: List.map eφ as <+: b :: bs := by
    simpa only [List.map_cons] using hprefix0
  have hprefixParts := List.cons_prefix_cons.mp hprefix
  have hheadMap : eφ a = b := hprefixParts.1
  have hbNotTail : b ∉ bs := by
    intro h
    have hrank := kmswShift_ULpred_head_west_rank_gt_tail w n b bs b hglPred h
    have : kmswStageRank w n ((kmswStage w n).west b) <
        kmswStageRank w n ((kmswStage w n).west b) := by simpa using hrank
    exact (lt_irrefl _ this)
  have hnotPre (f : ℕ) (hnot : f ∉ List.map eφ as) (hf : f ∈ bs) :
      f ∉ List.map eφ (a :: as) := by
    intro hmem
    have hparts : f = eφ a ∨ f ∈ List.map eφ as := by simpa using hmem
    rcases hparts with hhead | htail
    · have hfb : f = b := hhead.trans hheadMap
      exact hbNotTail (hfb ▸ hf)
    · exact hnot htail
  have htailNotPre (f : ℕ) (hnot : f ∉ List.map eψ as) (hf : f ∈ bs) :
      f ∉ List.map eφ (a :: as) := by
    have hnotOld : f ∉ List.map eφ as := by
      rw [← hmapTail]
      exact hnot
    exact hnotPre f hnotOld hf
  refine ⟨hsimStep, ?_, ?_, ?_, ?_⟩
  · intro f hf hnot x hx
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxFresh
    · have havoid := hsim.ur_edge_avoid f hfGlobal hnotOld x hxOld
      have hne : x ≠ sh.nextEdge := by omega
      simpa [eψ, sh, kmswShiftFreshEdgeMap, hne] using havoid
    · subst x
      have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftFreshEdgeMap]
      omega
  · intro f hf hnot v hv
    have hfGlobal : f ∈ gl.UR := by
      change f ∈ (kmswStepOfStep gl .left).UR at hf
      rw [hglURPost] at hf
      exact hf
    have hnotOld : f ∉ List.map eφ sh.UR := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UR) at hnot
      rw [hshURPost, hmapUR] at hnot
      exact hnot
    have hvOld : v < sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      exact hv
    have havoid := hsim.ur_east_avoid f hfGlobal hnotOld v hvOld
    have hfBound := kmswShiftAll_stage_UR_bound w n f hfGlobal
    change f < gl.nextEdge at hfBound
    have hneF : f ≠ gl.nextEdge := by omega
    change vφ v ≠ (kmswStepOfStep gl .left).east f
    simpa [kmswStepOfStep, hglPred, State.addEdge, hneF] using havoid
  · intro f hf hnot x hx
    have hfTail : f ∈ bs := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPredPost] at hf
      exact hf
    have hnotTail : f ∉ List.map eψ as := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UL.dropLast.reverse) at hnot
      rw [hshPredPost] at hnot
      exact hnot
    have hnotOld : f ∉ List.map eφ (a :: as) := htailNotPre f hnotTail hfTail
    have hnotOriginal : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      rw [hshPred]
      exact hnotOld
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge := by
      change x < (kmswStepOfStep sh .left).nextEdge at hx
      simp [kmswStepOfStep, hshPred, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxFresh
    · have hglobalPred : f ∈ gl.UL.dropLast.reverse := by
        rw [hglPred]
        exact List.mem_cons_of_mem _ hfTail
      have havoid := hsim.ul_edge_avoid f hglobalPred hnotOriginal x hxOld
      have hne : x ≠ sh.nextEdge := by omega
      simpa [eψ, sh, kmswShiftFreshEdgeMap, hne] using havoid
    · subst x
      have hglobalPred : f ∈ gl.UL.dropLast.reverse := by
        rw [hglPred]
        exact List.mem_cons_of_mem _ hfTail
      have hfBound := kmswShiftAll_stage_ULpred_bound w n f hglobalPred
      change f < gl.nextEdge at hfBound
      change eψ sh.nextEdge ≠ f
      simp [eψ, kmswShiftFreshEdgeMap]
      omega
  · intro f hf hnot v hv
    have hfTail : f ∈ bs := by
      change f ∈ (kmswStepOfStep gl .left).UL.dropLast.reverse at hf
      rw [hglPredPost] at hf
      exact hf
    have hnotTail : f ∉ List.map eψ as := by
      change f ∉ List.map eψ ((kmswStepOfStep sh .left).UL.dropLast.reverse) at hnot
      rw [hshPredPost] at hnot
      exact hnot
    have hnotOld : f ∉ List.map eφ (a :: as) := htailNotPre f hnotTail hfTail
    have hnotOriginal : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      rw [hshPred]
      exact hnotOld
    have hglobalPred : f ∈ gl.UL.dropLast.reverse := by
      rw [hglPred]
      exact List.mem_cons_of_mem _ hfTail
    have hvOld : v < sh.nextVertex := by
      change v < (kmswStepOfStep sh .left).nextVertex at hv
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      exact hv
    have havoid := hsim.ul_west_avoid f hglobalPred hnotOriginal v hvOld
    have hfBound := kmswShiftAll_stage_ULpred_bound w n f hglobalPred
    change f < gl.nextEdge at hfBound
    have hneF : f ≠ gl.nextEdge := by omega
    change vφ v ≠ (kmswStepOfStep gl .left).west f
    simpa [kmswStepOfStep, hglPred, State.addEdge, hneF] using havoid

/-- Select the edge-map update dictated by the actual two finite-stage stack
shapes and the common step. -/
@[expose] def kmswShiftNextEdgeMap (sh gl : State) (step : Step)
    (eφ : ℕ → ℕ) : ℕ → ℕ :=
  match step with
  | .up => kmswShiftUpEdgeMap sh gl eφ
  | .down =>
    match sh.UR, gl.UR with
    | [], [] => kmswShiftFreshEdgeMap sh gl eφ
    | [], e :: _ => kmswShiftDownMismatchEdgeMap sh e eφ
    | _ :: _, _ => eφ
  | .left =>
    match sh.UL.dropLast.reverse, gl.UL.dropLast.reverse with
    | [], [] => kmswShiftUpEdgeMap sh gl eφ
    | [], e :: _ => kmswShiftLeftMismatchEdgeMap sh gl e eφ
    | _ :: _, _ => kmswShiftFreshEdgeMap sh gl eφ

/-- Select the vertex-map update dictated by the actual two finite-stage
stack shapes and the common step. -/
@[expose] def kmswShiftNextVertexMap (sh gl : State) (step : Step)
    (vφ : ℕ → ℕ) : ℕ → ℕ :=
  match step with
  | .up => kmswShiftUpVertexMap sh gl vφ
  | .down =>
    match sh.UR, gl.UR with
    | [], [] => kmswShiftUpVertexMap sh gl vφ
    | [], e :: _ => kmswShiftDownMismatchVertexMap sh gl e vφ
    | _ :: _, _ => vφ
  | .left =>
    match sh.UL.dropLast.reverse, gl.UL.dropLast.reverse with
    | [], [] => kmswShiftUpVertexMap sh gl vφ
    | [], e :: _ => kmswShiftLeftMismatchVertexMap sh gl e vφ
    | _ :: _, _ => vφ

/-- One common KMSW code step advances the shifted and global stages while
preserving `Sim2`; the next maps are selected from the actual stack shapes -/
theorem kmswShiftSim2_step
    (u w : ℕ → Fin 3) (t m : ℕ)
    (hshift : u = fun i => w (t + i))
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w (t + m)) eφ vφ) :
    Sim2 (kmswStage u (m + 1)) (kmswStage w (t + (m + 1)))
      (kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w (t + m))
        (kmswCodeStep (u m)) eφ)
      (kmswShiftNextVertexMap (kmswStage u m) (kmswStage w (t + m))
        (kmswCodeStep (u m)) vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w (t + m)
  have hcode : u m = w (t + m) := by rw [hshift]
  have hshStep : kmswStage u (m + 1) = kmswStepOfStep sh (kmswCodeStep (u m)) := rfl
  have hglStep : kmswStage w (t + (m + 1)) =
      kmswStepOfStep gl (kmswCodeStep (w (t + m))) := by
    have ht : t + (m + 1) = (t + m) + 1 := by omega
    rw [ht]
    rfl
  rw [hshStep, hglStep, hcode]
  cases hstep : kmswCodeStep (w (t + m)) with
  | up =>
      simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl, hstep] using
        (kmswShiftSim2_step_up u w m (t + m) eφ vφ hsim)
  | down =>
      cases hshUR : sh.UR with
      | nil =>
          cases hglUR : gl.UR with
          | nil =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshUR, hglUR] using
                (kmswShiftSim2_step_down_empty u w m (t + m) eφ vφ
                  hsim hshUR hglUR)
          | cons e es =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshUR, hglUR] using
                (kmswShiftSim2_step_down_mismatch u w m (t + m) e es eφ vφ
                  hsim hshUR hglUR)
      | cons a as =>
          cases hglUR : gl.UR with
          | nil =>
              have hprefix := hsim.sim.ur_prefix
              rw [hshUR, hglUR] at hprefix
              simp at hprefix
          | cons b bs =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshUR, hglUR] using
                (kmswShiftSim2_step_down_nonempty u w m (t + m) eφ vφ
                  hsim ⟨a, as, hshUR⟩ ⟨b, bs, hglUR⟩)
  | left =>
      cases hshPred : sh.UL.dropLast.reverse with
      | nil =>
          cases hglPred : gl.UL.dropLast.reverse with
          | nil =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshPred, hglPred] using
                (kmswShiftSim2_step_left_empty u w m (t + m) eφ vφ
                  hsim hshPred hglPred)
          | cons e es =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshPred, hglPred] using
                (kmswShiftSim2_step_left_mismatch u w m (t + m) e es eφ vφ
                  hsim hshPred hglPred)
      | cons a as =>
          cases hglPred : gl.UL.dropLast.reverse with
          | nil =>
              have hprefix := hsim.sim.ul_predecessors_prefix
              rw [hshPred, hglPred] at hprefix
              simp at hprefix
          | cons b bs =>
              simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, sh, gl,
                hstep, hshPred, hglPred] using
                (kmswShiftSim2_step_left_nonempty u w m (t + m) eφ vφ
                  hsim ⟨a, as, hshPred⟩ ⟨b, bs, hglPred⟩)

/-- Edge maps for all finite shifted stages, recursively extended according
to the actual common KMSW step. -/
@[expose] def kmswShiftEdgeMapAll (w : ℕ → Fin 3) (t : ℕ) :
    ℕ → ℕ → ℕ
  | 0 => kmswShiftRootEdgeNatMap w t
  | m + 1 =>
      kmswShiftNextEdgeMap (kmswStage (fun i => w (t + i)) m)
        (kmswStage w (t + m)) (kmswCodeStep (w (t + m)))
        (kmswShiftEdgeMapAll w t m)

/-- Vertex maps for all finite shifted stages, recursively extended according
to the actual common KMSW step. -/
@[expose] def kmswShiftVertexMapAll (w : ℕ → Fin 3) (t : ℕ) :
    ℕ → ℕ → ℕ
  | 0 => kmswShiftRootVertexNatMap w t
  | m + 1 =>
      kmswShiftNextVertexMap (kmswStage (fun i => w (t + i)) m)
        (kmswStage w (t + m)) (kmswCodeStep (w (t + m)))
        (kmswShiftVertexMapAll w t m)

private theorem kmswShiftNextEdgeMap_old (sh gl : State) (step : Step)
    (eφ : ℕ → ℕ) (e : ℕ) (he : e < sh.nextEdge) :
    kmswShiftNextEdgeMap sh gl step eφ e = eφ e := by
  have hneNext : e ≠ sh.nextEdge := ne_of_lt he
  have hneNextTwo : e ≠ sh.nextEdge + 1 := by omega
  cases step with
  | up =>
      simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, hneNext, hneNextTwo]
  | down =>
      cases hsh : sh.UR <;> cases hgl : gl.UR <;>
        simp [kmswShiftNextEdgeMap, hsh, hgl,
          kmswShiftFreshEdgeMap, kmswShiftDownMismatchEdgeMap, ne_of_lt he]
  | left =>
      cases hsh : sh.UL.dropLast.reverse <;>
        cases hgl : gl.UL.dropLast.reverse <;>
          simp [kmswShiftNextEdgeMap, hsh, hgl, kmswShiftUpEdgeMap,
            kmswShiftFreshEdgeMap, kmswShiftLeftMismatchEdgeMap,
            hneNext, hneNextTwo]

private theorem kmswShiftNextVertexMap_old (sh gl : State) (step : Step)
    (vφ : ℕ → ℕ) (v : ℕ) (hv : v < sh.nextVertex) :
    kmswShiftNextVertexMap sh gl step vφ v = vφ v := by
  cases step with
  | up => simp [kmswShiftNextVertexMap, kmswShiftUpVertexMap, ne_of_lt hv]
  | down =>
      cases hsh : sh.UR <;> cases hgl : gl.UR <;>
        simp [kmswShiftNextVertexMap, hsh, hgl,
          kmswShiftUpVertexMap, kmswShiftDownMismatchVertexMap, ne_of_lt hv]
  | left =>
      cases hsh : sh.UL.dropLast.reverse <;>
        cases hgl : gl.UL.dropLast.reverse <;>
          simp [kmswShiftNextVertexMap, hsh, hgl, kmswShiftUpVertexMap,
            kmswShiftLeftMismatchVertexMap, ne_of_lt hv]

/-- The recursive edge maps agree on every edge already allocated at the
previous shifted stage. -/
theorem kmswShiftEdgeMapAll_extend
    (w : ℕ → Fin 3) (t m e : ℕ)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge) :
    kmswShiftEdgeMapAll w t (m + 1) e = kmswShiftEdgeMapAll w t m e := by
  exact kmswShiftNextEdgeMap_old
    (kmswStage (fun i => w (t + i)) m) (kmswStage w (t + m))
    (kmswCodeStep (w (t + m))) (kmswShiftEdgeMapAll w t m) e he

/-- The recursive vertex maps agree on every vertex already allocated at the
previous shifted stage. -/
theorem kmswShiftVertexMapAll_extend
    (w : ℕ → Fin 3) (t m v : ℕ)
    (hv : v < (kmswStage (fun i => w (t + i)) m).nextVertex) :
    kmswShiftVertexMapAll w t (m + 1) v = kmswShiftVertexMapAll w t m v := by
  exact kmswShiftNextVertexMap_old
    (kmswStage (fun i => w (t + i)) m) (kmswStage w (t + m))
    (kmswCodeStep (w (t + m))) (kmswShiftVertexMapAll w t m) v hv

/-- The recursively chosen maps give a `Sim2` embedding at every finite time -/
theorem kmswShift_sim2_all (w : ℕ → Fin 3) (t m : ℕ) :
    Sim2 (kmswStage (fun i => w (t + i)) m) (kmswStage w (t + m))
      (kmswShiftEdgeMapAll w t m) (kmswShiftVertexMapAll w t m) := by
  induction m with
  | zero =>
      simpa [kmswStage, kmswShiftEdgeMapAll, kmswShiftVertexMapAll] using
        (kmswShiftSim2_init w t)
  | succ m ih =>
      simpa [kmswStage, kmswShiftEdgeMapAll, kmswShiftVertexMapAll] using
        (kmswShiftSim2_step (fun i => w (t + i)) w t m rfl
          (kmswShiftEdgeMapAll w t m) (kmswShiftVertexMapAll w t m) ih)

/-- The recursive edge maps are compatible at every later shifted time once
the edge has been allocated. -/
theorem kmswShiftEdgeMapAll_eq_of_le
    (w : ℕ → Fin 3) (t m n e : ℕ) (hmn : m ≤ n)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge) :
    kmswShiftEdgeMapAll w t n e = kmswShiftEdgeMapAll w t m e := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have heN : e < (kmswStage (fun i => w (t + i)) n).nextEdge :=
        he.trans_le (kmswStage_nextEdge_mono (fun i => w (t + i)) hmn)
      calc
        kmswShiftEdgeMapAll w t (n + 1) e = kmswShiftEdgeMapAll w t n e :=
          kmswShiftEdgeMapAll_extend w t n e heN
        _ = kmswShiftEdgeMapAll w t m e := ih

/-- The recursive vertex maps are compatible at every later shifted time once
the vertex has been allocated. -/
theorem kmswShiftVertexMapAll_eq_of_le
    (w : ℕ → Fin 3) (t m n v : ℕ) (hmn : m ≤ n)
    (hv : v < (kmswStage (fun i => w (t + i)) m).nextVertex) :
    kmswShiftVertexMapAll w t n v = kmswShiftVertexMapAll w t m v := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hvN : v < (kmswStage (fun i => w (t + i)) n).nextVertex :=
        hv.trans_le (CutConverse.nextVertex_mono (fun i => w (t + i)) hmn)
      calc
        kmswShiftVertexMapAll w t (n + 1) v = kmswShiftVertexMapAll w t n v :=
          kmswShiftVertexMapAll_extend w t n v hvN
        _ = kmswShiftVertexMapAll w t m v := ih

/-- An edge present at shifted stage `m` maps to an allocated present global
edge at every corresponding later stage, with the simulated endpoints. -/
theorem kmswShift_present_edge_stage
    (w : ℕ → Fin 3) (t m e : ℕ)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge)
    (hp : (kmswStage (fun i => w (t + i)) m).present e = true) :
    ∀ k, m ≤ k →
      kmswShiftEdgeMapAll w t k e < (kmswStage w (t + k)).nextEdge ∧
      (kmswStage w (t + k)).present (kmswShiftEdgeMapAll w t k e) = true ∧
      (kmswStage w (t + k)).west (kmswShiftEdgeMapAll w t k e) =
        kmswShiftVertexMapAll w t k
          ((kmswStage (fun i => w (t + i)) k).west e) ∧
      (kmswStage w (t + k)).east (kmswShiftEdgeMapAll w t k e) =
        kmswShiftVertexMapAll w t k
          ((kmswStage (fun i => w (t + i)) k).east e) := by
  intro k hmk
  have hshiftPresent :=
    present_mono (fun i => w (t + i)) he hp k hmk
  have hsim := kmswShift_sim2_all w t k
  have hbound := hsim.sim.edge_bound e hshiftPresent.1
  have hpresent := hsim.sim.present e hshiftPresent.1 hshiftPresent.2
  have hinc := hsim.sim.incidence e hshiftPresent.1
  exact ⟨hbound, hpresent, hinc.1, hinc.2⟩

/-- A present shifted edge defines a present global edge, and its stable limit
endpoints are the images of the shifted edge's stable endpoints. -/
theorem kmswShift_present_edge_maps
    (w : ℕ → Fin 3) (t m e : ℕ)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge)
    (hp : (kmswStage (fun i => w (t + i)) m).present e = true) :
    EdgePresent w (kmswShiftEdgeMapAll w t m e) ∧
      edgeWest w (kmswShiftEdgeMapAll w t m e) =
        kmswShiftVertexMapAll w t m (edgeWest (fun i => w (t + i)) e) ∧
      edgeEast w (kmswShiftEdgeMapAll w t m e) =
        kmswShiftVertexMapAll w t m (edgeEast (fun i => w (t + i)) e) := by
  have hstage := kmswShift_present_edge_stage w t m e he hp m (le_rfl)
  have hpresent : EdgePresent w (kmswShiftEdgeMapAll w t m e) :=
    EdgePresent.of_stage_present hstage.1 hstage.2.1
  have hshiftEnds := edge_endpoints_eq (fun i => w (t + i)) he
  have hglobalEnds := edge_endpoints_eq w hstage.1
  refine ⟨hpresent, ?_, ?_⟩
  · calc
      edgeWest w (kmswShiftEdgeMapAll w t m e) =
          (kmswStage w (t + m)).west (kmswShiftEdgeMapAll w t m e) :=
        hglobalEnds.1.symm
      _ = kmswShiftVertexMapAll w t m
          ((kmswStage (fun i => w (t + i)) m).west e) := hstage.2.2.1
      _ = kmswShiftVertexMapAll w t m (edgeWest (fun i => w (t + i)) e) :=
        congrArg (kmswShiftVertexMapAll w t m) hshiftEnds.1
  · calc
      edgeEast w (kmswShiftEdgeMapAll w t m e) =
          (kmswStage w (t + m)).east (kmswShiftEdgeMapAll w t m e) :=
        hglobalEnds.2.symm
      _ = kmswShiftVertexMapAll w t m
          ((kmswStage (fun i => w (t + i)) m).east e) := hstage.2.2.2
      _ = kmswShiftVertexMapAll w t m (edgeEast (fun i => w (t + i)) e) :=
        congrArg (kmswShiftVertexMapAll w t m) hshiftEnds.2

/-- The time-`m` shifted stage maps as a present-edge subgraph of the global
limit graph, using the recursively compatible edge and vertex maps. -/
@[expose] def kmswShiftStageToLimit (w : ℕ → Fin 3) (t m : ℕ) :
    Prefunctor (StagePresentVertex (fun i => w (t + i)) m) (PresentVertex w) where
  obj v := ⟨kmswShiftVertexMapAll w t m v.id⟩
  map {_ _} e := by
    let hsim := kmswShift_sim2_all w t m
    have he : e.val < (kmswStage (fun i => w (t + i)) m).nextEdge := e.property.1
    have hf := hsim.sim.edge_bound e.val he
    have hp := hsim.sim.present e.val he e.property.2.1
    have hinc := hsim.sim.incidence e.val he
    exact ⟨kmswShiftEdgeMapAll w t m e.val,
      EdgePresent.of_stage_present hf hp,
      (edge_endpoints_eq w hf).1.symm.trans
        (hinc.1.trans (congrArg (kmswShiftVertexMapAll w t m)
          e.property.2.2.1)),
      (edge_endpoints_eq w hf).2.symm.trans
        (hinc.2.trans (congrArg (kmswShiftVertexMapAll w t m)
          e.property.2.2.2))⟩

/-- The shifted finite-stage map preserves the directed path length. -/
theorem kmswShiftStageToLimit_length
    (w : ℕ → Fin 3) (t m : ℕ)
    {a b : StagePresentVertex (fun i => w (t + i)) m}
    (p : Path a b) :
    ((kmswShiftStageToLimit w t m).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- A finite present stage includes into every later stage by retaining edge
and vertex IDs (`remark-kmsw-infinite`, -/
@[expose] def kmswStageInclusion (w : ℕ → Fin 3) (n k : ℕ) (hnk : n ≤ k) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w k) where
  obj v := ⟨v.id⟩
  map {_ _} e := by
    have hp := present_mono w e.property.1 e.property.2.1 k hnk
    have hEnds := present_endpoints_stable w e.property.1 e.property.2.1 hnk
    exact ⟨e.val, hp.1, hp.2,
      hEnds.1.trans e.property.2.2.1,
      hEnds.2.trans e.property.2.2.2⟩

/-- Stage inclusion preserves the length of finite directed paths. -/
theorem kmswStageInclusion_length
    (w : ℕ → Fin 3) (n k : ℕ) (hnk : n ≤ k)
    {a b : StagePresentVertex w n} (p : Path a b) :
    ((kmswStageInclusion w n k hnk).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem kmswPresentPath_lift_stage
    (w : ℕ → Fin 3) {a b : PresentVertex w} (p : Path a b) :
    ∃ n, Nonempty (Path (⟨a.id⟩ : StagePresentVertex w n)
      (⟨b.id⟩ : StagePresentVertex w n)) := by
  induction p with
  | nil => exact ⟨0, ⟨Path.nil⟩⟩
  | @cons mid final p e ih =>
      obtain ⟨n, ⟨pn⟩⟩ := ih
      obtain ⟨N, heN, hpN⟩ := e.property.1
      let k := max n N
      have hnk : n ≤ k := Nat.le_max_left n N
      have hNk : N ≤ k := Nat.le_max_right n N
      have hpath : Path (⟨a.id⟩ : StagePresentVertex w k)
          (⟨mid.id⟩ : StagePresentVertex w k) := by
        simpa [kmswStageInclusion] using
          (kmswStageInclusion w n k hnk).mapPath pn
      have heK := present_mono w heN hpN k hNk
      let eK : (⟨mid.id⟩ : StagePresentVertex w k) ⟶
          (⟨final.id⟩ : StagePresentVertex w k) :=
        ⟨e.val, heK.1, heK.2,
          (edge_endpoints_eq w heK.1).1.trans e.property.2.1,
          (edge_endpoints_eq w heK.1).2.trans e.property.2.2⟩
      exact ⟨k, ⟨Path.cons hpath eK⟩⟩

end DirectedDistances.KMSW
