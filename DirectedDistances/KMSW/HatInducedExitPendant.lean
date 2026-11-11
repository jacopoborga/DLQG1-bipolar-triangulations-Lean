module

public import DirectedDistances.KMSW.HatInducedExit

/-! # Pendant exits of the hatted stage embedding

Helpers toward `lem-quad-kmsw`; not the paper result -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private theorem exit_chain_terminal (s : State) (r : ℕ → ℚ)
    (xs : List ℕ) (hne : xs ≠ []) (hc : WestEastChain s xs)
    (hr : ∀ e ∈ xs, r (s.west e) < r (s.east e)) :
    ∀ e ∈ xs, r (s.west e) < r (s.east (xs.getLast hne)) ∧
      r (s.east e) ≤ r (s.east (xs.getLast hne)) ∧
      (s.east e = s.east (xs.getLast hne) → e = xs.getLast hne) := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons a xs ih =>
    cases xs with
    | nil =>
      intro e he
      have heq : e = a := by simpa only [List.mem_singleton] using he
      subst e
      exact ⟨hr a (by simp), le_rfl, fun _ => rfl⟩
    | cons b bs =>
      have htail : WestEastChain s (b :: bs) := hc.tail
      have ht := ih (by simp) htail (fun e he => hr e (List.mem_cons_of_mem a he))
      have hab : s.east a = s.west b := by
        simpa using hc.rel_head? (by simp)
      have hlast : (a :: b :: bs).getLast hne = (b :: bs).getLast (by simp) := rfl
      intro e he
      rw [hlast]
      rcases List.mem_cons.mp he with hea | he
      · subst e
        have hb := ht b List.mem_cons_self
        have ha : r (s.east a) < r (s.east ((b :: bs).getLast (by simp))) := by
          rw [hab]
          exact hb.1
        simpa only [List.getLast_cons] using
          And.intro ((hr a List.mem_cons_self).trans ha)
            (And.intro ha.le (fun heq => False.elim ((ne_of_lt ha) (congrArg r heq))))
      · simpa only [List.getLast_cons] using ht e he

private theorem exit_top_corner (u : ℕ → Fin 3) (n : ℕ)
    (hur : (kmswStage u n).UR = [])
    (d : StageDart (kmswStage u n).nextEdge)
    (hd : (kmswMap u n).edgeInv d ∈ stageOuterWord u n)
    (hv : stageEndpoint (kmswStage u n) d =
      (kmswStage u n).east (kmswStage u n).active) :
    d = (⟨(kmswStage u n).active, act_lt_nextEdge u le_rfl⟩, true) := by
  let s := kmswStage u n
  let r := kmswStageRank u n
  have hi := kmswStage_boundary_chain_invariant u n
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last u n
  have hULne : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last u n).1
  have hlast : s.UL.getLast hULne = s.active := by
    change (kmswStage u n).UL.getLast _ = _
    simp only [hxs, List.getLast_append_singleton]
    rfl
  have hUL : WestEastChain s s.UL := by
    have hc := hi.1
    simpa only [hur, List.append_nil] using hc
  have bound (es : List ℕ) (hsub : ∀ e ∈ es, e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR) :
      ∀ e ∈ es, r (s.west e) < r (s.east e) := by
    intro e he
    exact kmswStageRank_strict u n e
      ((kmswStage_boundary_ids_lt_nextEdge u n).2 e (hsub e he))
  have hu := exit_chain_terminal s r s.UL hULne hUL (bound _ (by
    intro e he
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl he))))
  rw [hlast] at hu
  have hlowne : s.LL ++ s.LR ≠ [] := by
    have hn := hi.2.2.2.2.1
    intro he
    exact hn (List.append_eq_nil_iff.mp he).2
  have hlow := exit_chain_terminal s r (s.LL ++ s.LR) hlowne hi.2.1
    (bound _ (by
      intro e he
      simp only [List.mem_append] at he ⊢
      rcases he with he | he
      · exact Or.inl (Or.inr he)
      · exact Or.inr he))
  have hend : s.east ((s.LL ++ s.LR).getLast hlowne) = s.east s.active := by
    have he := hi.2.2.2.1
    change boundaryEnd s (s.UL ++ s.UR) = boundaryEnd s (s.LL ++ s.LR) at he
    change s.UR = [] at hur
    rw [hur, List.append_nil] at he
    simp only [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hULne,
      List.getLast?_eq_getLast_of_ne_nil hlowne, Option.map_some, Option.some.injEq,
      hlast] at he
    exact he.symm
  rw [hend] at hlow
  rw [stageOuterWord_mem_iff] at hd
  change (((!d.2) = false ∧ (d.1.val ∈ s.UL ∨ d.1.val ∈ s.UR)) ∨
    ((!d.2) = true ∧ (d.1.val ∈ s.LR ∨ d.1.val ∈ s.LL))) at hd
  change s.UR = [] at hur
  cases hb : d.2
  · have he : d.1.val ∈ s.LR ∨ d.1.val ∈ s.LL := by
      simpa only [hb, Bool.not_false,
        Bool.true_eq_false, false_and, true_and, false_or] using hd
    have hm : d.1.val ∈ s.LL ++ s.LR := by
      simpa only [List.mem_append, or_comm] using he
    have hv' : s.west d.1.val = s.east s.active := by
      simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hv
    have hh := (hlow d.1.val hm).1
    rw [hv'] at hh
    exact (lt_irrefl _ hh).elim
  · have he : d.1.val ∈ s.UL := by
      simpa only [hb, Bool.not_true,
        Bool.false_eq_true, true_and, false_and, or_false, hur, List.not_mem_nil] using hd
    have hv' : s.east d.1.val = s.east s.active := by
      simpa only [stageEndpoint, hb, ↓reduceIte] using hv
    exact Prod.ext (Fin.ext ((hu d.1.val he).2.2 hv')) hb

private theorem exit_pendant_corner_candidates (u : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (u n) = .down) (hur : (kmswStage u n).UR = [])
    (d : StageDart (kmswStage u (n + 1)).nextEdge)
    (hd : (kmswMap u (n + 1)).edgeInv d ∈ stageOuterWord u (n + 1))
    (hv : stageEndpoint (kmswStage u (n + 1)) d =
      (kmswStage u n).east (kmswStage u n).active) :
    (d.1.val = (kmswStage u n).nextEdge ∧ d.2 = false) ∨
      (d.1.val = (kmswStage u n).active ∧ d.2 = true) := by
  let s := kmswStage u n
  change s.UR = [] at hur
  have hs : kmswStage u (n + 1) = kmswStepOfStep s .down := by
    change kmswStep s (u n) = _
    rw [kmswStep, hc]
  have hk : (kmswStage u (n + 1)).nextEdge = s.nextEdge + 1 := by
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  rw [stageOuterWord_mem_iff] at hd
  change (((!d.2) = false ∧
      (d.1.val ∈ (kmswStage u (n + 1)).UL ∨
        d.1.val ∈ (kmswStage u (n + 1)).UR)) ∨
    ((!d.2) = true ∧
      (d.1.val ∈ (kmswStage u (n + 1)).LR ∨
        d.1.val ∈ (kmswStage u (n + 1)).LL))) at hd
  simp only [hs] at hd
  simp only [kmswStepOfStep, hur, State.addEdge, List.mem_append,
    List.mem_singleton, List.not_mem_nil, or_false] at hd
  change (if d.2 then (kmswStage u (n + 1)).east d.1.val
    else (kmswStage u (n + 1)).west d.1.val) = s.east s.active at hv
  simp only [hs] at hv
  by_cases hold : d.1.val < s.nextEdge
  · let d₀ : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
    have hne : d.1.val ≠ s.nextEdge := ne_of_lt hold
    have hv₀ : stageEndpoint s d₀ = s.east s.active := by
      simpa only [kmswStepOfStep, hur, State.addEdge, hne, ↓reduceIte,
        stageEndpoint, d₀] using hv
    have ho₀ : (kmswMap u n).edgeInv d₀ ∈ stageOuterWord u n := by
      rw [stageOuterWord_mem_iff]
      change (((!d.2) = false ∧ (d.1.val ∈ s.UL ∨ d.1.val ∈ s.UR)) ∨
        ((!d.2) = true ∧ (d.1.val ∈ s.LR ∨ d.1.val ∈ s.LL)))
      simpa only [hne, hur, List.not_mem_nil, or_false] using hd
    have he := exit_top_corner u n hur d₀ ho₀ hv₀
    exact Or.inr ⟨congrArg (fun z => z.1.val) he, congrArg Prod.snd he⟩
  · have hid : d.1.val = s.nextEdge := by have hb := d.1.isLt; omega
    left
    refine ⟨hid, ?_⟩
    cases hb : d.2
    · rfl
    · have hvb := (kmswStage_endpoints_lt_nextVertex u n s.active
        (act_lt_nextEdge u le_rfl)).2
      simp only [kmswStepOfStep, hur, State.addEdge, hid, hb, ↓reduceIte] at hv
      exact (ne_of_lt hvb hv.symm).elim

/-- The first return from the final global pendant's west dart is the local
active-east attachment corner. The excluded image includes missing edges.
This is a helper toward lem-quad-kmsw; not the paper result -/
theorem hatExit_pendant_attachment_corner (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = []) :
    let m := hatExitIndex w h k
    let A : StageDart (kmswStage (hatCodes w h) m).nextEdge :=
      (⟨(kmswStage (hatCodes w h) m).active, act_lt_nextEdge _ le_rfl⟩, true)
    let A' := outerSucc_castDart
      (kmswStage_nextEdge_mono (hatCodes w h) (Nat.le_succ m)) A
    let b := (kmswRootedStage (hatCodes w h) (m + 1)).root
    ∃ l : ℕ, 0 < l ∧
      ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[l]
        (hatDartMap w h (m + 1) b) = hatDartMap w h (m + 1) A' ∧
      ∀ j : ℕ, 0 < j → j < l →
        ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[j]
          (hatDartMap w h (m + 1) b) ∉ Set.range (hatDartMap w h (m + 1)) := by
  let m := hatExitIndex w h k
  let u := hatCodes w h
  let s := kmswStage u m
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge u le_rfl⟩, true)
  let A' := outerSucc_castDart (kmswStage_nextEdge_mono u (Nat.le_succ m)) A
  let b := (kmswRootedStage u (m + 1)).root
  let i := hatDartMap w h (m + 1)
  let ρ := (kmswMap w (quadrantRStageTime w h (m + 1))).rot
  change s.UR = [] at hur
  have hc : kmswCodeStep (u m) = .down := by
    dsimp only [u, m]
    rw [hatCodes_at_exit]
    rfl
  have hs : kmswStage u (m + 1) = kmswStepOfStep s .down := by
    change kmswStep s (u m) = _
    rw [kmswStep, hc]
  have hk : (kmswStage u (m + 1)).nextEdge = s.nextEdge + 1 := by
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  have hb : b.1.val = s.nextEdge ∧ b.2 = false := by
    change (kmswStage u (m + 1)).active = s.nextEdge ∧ (false : Bool) = false
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge, and_self]
  have hvb : stageEndpoint (kmswStage u (m + 1)) b = s.east s.active := by
    change (if b.2 then (kmswStage u (m + 1)).east b.1.val
      else (kmswStage u (m + 1)).west b.1.val) = _
    simp only [hb.2, Bool.false_eq_true, ↓reduceIte, hs, kmswStepOfStep,
      hur, State.addEdge, hb.1]
  have hvA : stageEndpoint (kmswStage u (m + 1)) A' = s.east s.active := by
    change (kmswStage u (m + 1)).east s.active = _
    have hact : s.active ≠ s.nextEdge := ne_of_lt (act_lt_nextEdge u le_rfl)
    simp only [hs, kmswStepOfStep, hur, State.addEdge, hact, ↓reduceIte]
  have hne : b ≠ A' := by
    intro he
    have hh : s.nextEdge = s.active := hb.1.symm.trans (congrArg (fun z => z.1.val) he)
    exact (ne_of_lt (act_lt_nextEdge u (Nat.le_refl m))) hh.symm
  have table {a N : ℕ} (hN : N = a + 1)
      (σ : Equiv.Perm (StageDart a)) (τ : Equiv.Perm (StageDart N))
      (B : StageDart a) (ht : StageRotation.resize hN τ = StageRotation.pendant a σ B)
      (z : StageDart N) (hz : z.1.val = a ∧ z.2 = false) :
      (τ z).1.val = B.1.val ∧ (τ z).2 = B.2 := by
    cases hN
    change τ = StageRotation.pendant a σ B at ht
    subst τ
    have hz' : z = StageRotation.allocation a 1 (.inr (0, false)) :=
      Prod.ext (Fin.ext (by
        change z.1.val = a + 0
        simpa only [Nat.add_zero] using hz.1)) hz.2
    rw [hz', (StageRotation.pendant_new a σ B).1]
    exact ⟨rfl, rfl⟩
  have ht := StageRotation.step_pendant s (act_lt_nextEdge u le_rfl)
    (stageRotation_UL_bound u m) (stageRot u m) (u m) hc hur
  have hrot : (kmswMap u (m + 1)).rot b = A' := by
    have hv := table hk (stageRot u m) (stageRot u (m + 1)) A ht b hb
    exact Prod.ext (Fin.ext hv.1) hv.2
  have hout : (kmswMap u (m + 1)).edgeInv
      ((kmswMap u (m + 1)).rot b) ∈ stageOuterWord u (m + 1) := by
    rw [hrot, stageOuterWord_mem_iff]
    change ((!true) = false ∧
      (s.active ∈ (kmswStage u (m + 1)).UL ∨
        s.active ∈ (kmswStage u (m + 1)).UR)) ∨ _
    left
    refine ⟨rfl, Or.inl ?_⟩
    simp only [hs, kmswStepOfStep, hur, State.addEdge, List.mem_append]
    left
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
    change s.UL = xs ++ [s.active] at hxs
    rw [hxs]
    simp only [List.mem_append, List.mem_singleton, or_true]
  obtain ⟨l, e, hl, he, hgap, hv, ho⟩ :=
    hatDartMap_first_return_boundary w h (m + 1) b hout
  have hve : stageEndpoint (kmswStage u (m + 1)) e = s.east s.active := hv.trans hvb
  rcases exit_pendant_corner_candidates u m hc hur e ho hve with heB | heA
  · have heb : e = b := Prod.ext (Fin.ext (heB.1.trans hb.1.symm)) (heB.2.trans hb.2.symm)
    have hcycle : ρ.SameCycle (i b) (i A') :=
      (hatDartMap_sameCycle_iff w h (m + 1) b A').mpr
        ((stageRot_sameCycle_iff_endpoint_eq u (m + 1) b A').mpr (hvb.trans hvA.symm))
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    have hex : ∃ n : ℕ, (ρ : _ → _)^[n] (i b) = i A' := ⟨n, hn⟩
    have hmin := Nat.find_spec hex
    have hp : 0 < Nat.find hex := by
      by_contra hbad
      have hz : Nat.find hex = 0 := by omega
      rw [hz, Function.iterate_zero_apply] at hmin
      exact hne ((hatDartMap_injective w h (m + 1)) hmin)
    have hperiod : (ρ : _ → _)^[l] (i b) = i b := by simpa only [heb] using he
    by_cases hsmall : Nat.find hex < l
    · exact (hgap (Nat.find hex) hp hsmall ⟨A', hmin.symm⟩).elim
    · have hdecomp : Nat.find hex = (Nat.find hex - l) + l := by omega
      rw [hdecomp, Function.iterate_add_apply, hperiod] at hmin
      exact (Nat.find_min hex (by omega : Nat.find hex - l < Nat.find hex) hmin).elim
  · have heq : e = A' := Prod.ext (Fin.ext heA.1) heA.2
    exact ⟨l, hl, he.trans (congrArg i heq), hgap⟩

private theorem exit_extend_return {D E F : Type*} [Finite F] [DecidableEq D]
    (σ : Equiv.Perm D) (σ' : Equiv.Perm E) (ρ : Equiv.Perm F)
    (p : D → E) (j : E → F) (hp : Function.Injective p) (hj : Function.Injective j)
    (A : D) (x y : E)
    (hx : x ∉ Set.range p) (hy : y ∉ Set.range p)
    (cover : ∀ z, (∃ d, p d = z) ∨ z = x ∨ z = y)
    (old : ∀ d, σ' (p d) = if σ d = A then x else p (σ d))
    (newx : σ' x = p A) (newy : σ' y = y) (ry : ρ (j y) = j y)
    (ih : ∀ d, ∃ l : ℕ, 0 < l ∧
      (ρ : F → F)^[l] (j (p d)) = j (p (σ d)) ∧
      ∀ t : ℕ, 0 < t → t < l →
        (ρ : F → F)^[t] (j (p d)) ∉ Set.range (j ∘ p))
    (attach : ∃ l : ℕ, 0 < l ∧ (ρ : F → F)^[l] (j x) = j (p A) ∧
      ∀ t : ℕ, 0 < t → t < l → (ρ : F → F)^[t] (j x) ∉ Set.range j) :
    ∀ z, ∃ l : ℕ, 0 < l ∧ (ρ : F → F)^[l] (j z) = j (σ' z) ∧
      ∀ t : ℕ, 0 < t → t < l → (ρ : F → F)^[t] (j z) ∉ Set.range j := by
  classical
  have first (z : E) : ∃ l : ℕ, ∃ e : E, 0 < l ∧
      (ρ : F → F)^[l] (j z) = j e ∧
      ∀ t : ℕ, 0 < t → t < l → (ρ : F → F)^[t] (j z) ∉ Set.range j := by
    obtain ⟨n, hn, _, he⟩ := (Equiv.Perm.SameCycle.refl ρ (j z)).exists_pow_eq''
    have hex : ∃ n : ℕ, 0 < n ∧ (ρ : F → F)^[n] (j z) ∈ Set.range j :=
      ⟨n, hn, z, he.symm⟩
    obtain ⟨e, he⟩ := (Nat.find_spec hex).2
    exact ⟨Nat.find hex, e, (Nat.find_spec hex).1, he.symm,
      fun t ht htl hmem => Nat.find_min hex htl ⟨ht, hmem⟩⟩
  have unique (i : D → F) (a : F) (l n : ℕ) (hl : 0 < l) (hn : 0 < n)
      (e f : D) (he : (ρ : F → F)^[l] a = i e)
      (hf : (ρ : F → F)^[n] a = i f)
      (gl : ∀ t, 0 < t → t < l → (ρ : F → F)^[t] a ∉ Set.range i)
      (gn : ∀ t, 0 < t → t < n → (ρ : F → F)^[t] a ∉ Set.range i) : i e = i f := by
    have hln : l = n := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact gn l hl hlt ⟨e, he.symm⟩
      · exact gl n hn hgt ⟨f, hf.symm⟩
    subst n
    exact he.symm.trans hf
  have back (a b c : E) (l n : ℕ) (hl : 0 < l) (hn : 0 < n)
      (he : (ρ : F → F)^[l] (j a) = j c)
      (hf : (ρ : F → F)^[n] (j b) = j c)
      (gl : ∀ t, 0 < t → t < l → (ρ : F → F)^[t] (j a) ∉ Set.range j)
      (gn : ∀ t, 0 < t → t < n → (ρ : F → F)^[t] (j b) ∉ Set.range j) : a = b := by
    by_cases hln : l = n
    · subst n
      exact hj ((ρ.injective.iterate l) (he.trans hf.symm))
    · rcases lt_or_gt_of_ne hln with hlt | hgt
      · have hf' := hf
        rw [show n = l + (n - l) by omega, Function.iterate_add_apply] at hf'
        have hh := (ρ.injective.iterate l) (hf'.trans he.symm)
        exact (gn (n - l) (by omega) (by omega) ⟨a, hh.symm⟩).elim
      · have he' := he
        rw [show l = n + (l - n) by omega, Function.iterate_add_apply] at he'
        have hh := (ρ.injective.iterate n) (he'.trans hf.symm)
        exact (gl (l - n) (by omega) (by omega) ⟨b, hh.symm⟩).elim
  have hyit (n : ℕ) : (ρ : F → F)^[n] (j y) = j y := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, ry]
  obtain ⟨a, ha, hea, hga⟩ := attach
  intro z
  rcases cover z with ⟨d, rfl⟩ | rfl | rfl
  · obtain ⟨l, e, hl, he, hg⟩ := first (p d)
    obtain ⟨n, hn, hen, hgn⟩ := ih d
    rcases cover e with ⟨f, rfl⟩ | rfl | rfl
    · have hgf : ∀ t, 0 < t → t < l →
          (ρ : F → F)^[t] (j (p d)) ∉ Set.range (j ∘ p) := by
        intro t ht htl ⟨v, hv⟩
        exact hg t ht htl ⟨p v, hv⟩
      have hef := unique (j ∘ p) (j (p d)) l n hl hn f (σ d) he hen hgf hgn
      have hfe : p f = p (σ d) := hj hef
      have hpA : σ d ≠ A := by
        intro heq
        have hback := back (p d) x (p A) l a hl ha
          (by simpa only [hfe, heq] using he) hea hg hga
        exact hx ⟨d, hback⟩
      refine ⟨l, hl, ?_, hg⟩
      rw [old, ite_eq_right hpA]
      exact he.trans (congrArg j hfe)
    · have hpath : (ρ : F → F)^[a + l] (j (p d)) = j (p A) := by
        rw [Function.iterate_add_apply, he, hea]
      have hgap : ∀ t, 0 < t → t < a + l →
          (ρ : F → F)^[t] (j (p d)) ∉ Set.range (j ∘ p) := by
        intro t ht htl ⟨v, hv⟩
        by_cases hsmall : t < l
        · exact hg t ht hsmall ⟨p v, hv⟩
        · by_cases heq : t = l
          · subst t
            exact hx ⟨v, hj (hv.trans he)⟩
          · have hdec : t = (t - l) + l := by omega
            rw [hdec, Function.iterate_add_apply, he] at hv
            exact hga (t - l) (by omega) (by omega) ⟨p v, hv⟩
      have heq := unique (j ∘ p) (j (p d)) (a + l) n (by omega) hn A (σ d)
        hpath hen hgap hgn
      have hσ : σ d = A := (hp (hj heq)).symm
      refine ⟨l, hl, ?_, hg⟩
      rw [old, ite_eq_left hσ]
      exact he
    · have heq := (ρ.injective.iterate l) (he.trans (hyit l).symm)
      exact (hy ⟨d, hj heq⟩).elim
  · exact ⟨a, ha, by simpa only [newx] using hea, hga⟩
  · exact ⟨1, by omega, by simpa only [Function.iterate_one, newy] using ry,
      by intro t ht htl; omega⟩

private theorem exit_stage_pendant_tables (u : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (u n) = .down) (hur : (kmswStage u n).UR = []) :
    let p := outerSucc_castDart (kmswStage_nextEdge_mono u (Nat.le_succ n))
    let A : StageDart (kmswStage u n).nextEdge :=
      (⟨(kmswStage u n).active, act_lt_nextEdge u le_rfl⟩, true)
    let x := (kmswRootedStage u (n + 1)).root
    let y := (kmswMap u (n + 1)).edgeInv x
    (∀ d, (stageRot u (n + 1)) (p d) =
      if stageRot u n d = A then x else p (stageRot u n d)) ∧
      stageRot u (n + 1) x = p A ∧ stageRot u (n + 1) y = y := by
  have tables {a N : ℕ} (ha : a ≤ N) (hN : N = a + 1)
      (σ : Equiv.Perm (StageDart a)) (τ : Equiv.Perm (StageDart N))
      (A : StageDart a) (x y : StageDart N)
      (hx : x.1.val = a ∧ x.2 = false) (hy : y.1.val = a ∧ y.2 = true)
      (ht : StageRotation.resize hN τ = StageRotation.pendant a σ A) :
      (∀ d, τ (outerSucc_castDart ha d) =
        if σ d = A then x else outerSucc_castDart ha (σ d)) ∧
        τ x = outerSucc_castDart ha A ∧ τ y = y := by
    cases hN
    change τ = StageRotation.pendant a σ A at ht
    subst τ
    have hx' : x = StageRotation.allocation a 1 (.inr (0, false)) :=
      Prod.ext (Fin.ext (by change x.1.val = a + 0; omega)) hx.2
    have hy' : y = StageRotation.allocation a 1 (.inr (0, true)) :=
      Prod.ext (Fin.ext (by change y.1.val = a + 0; omega)) hy.2
    have hold (d : StageDart a) :
        outerSucc_castDart ha d = StageRotation.allocation a 1 (.inl d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro d
      rw [hold, StageRotation.pendant_old]
      by_cases hd : σ d = A
      · simp only [hd, ite_true]
        exact hx'.symm
      · simp only [hd, ite_false]
        rfl
    · rw [hx', (StageRotation.pendant_new a σ A).1]
      rfl
    · rw [hy', (StageRotation.pendant_new a σ A).2]
  let s := kmswStage u n
  change s.UR = [] at hur
  have hs : kmswStage u (n + 1) = kmswStepOfStep s .down := by
    change kmswStep s (u n) = _
    rw [kmswStep, hc]
  have hk : (kmswStage u (n + 1)).nextEdge = s.nextEdge + 1 := by
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  have hx : (kmswRootedStage u (n + 1)).root.1.val = s.nextEdge := by
    change (kmswStage u (n + 1)).active = _
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  exact tables (kmswStage_nextEdge_mono u (Nat.le_succ n)) hk
    (stageRot u n) (stageRot u (n + 1)) _ _ _ ⟨hx, rfl⟩ ⟨hx, rfl⟩
    (StageRotation.step_pendant s (act_lt_nextEdge u le_rfl)
      (stageRotation_UL_bound u n) (stageRot u n) (u n) hc hur)

/-- The pendant exit transports the complete induced-rotation invariant
across the skipped excursion. This is a helper toward lem-quad-kmsw; -/
theorem hatDartMap_rot_induced_exit_pendant (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = [])
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k) d) =
            hatDartMap w h (hatExitIndex w h k)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k))) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k + 1) d) =
            hatDartMap w h (hatExitIndex w h k + 1)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k + 1) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k + 1)) := by
  let m := hatExitIndex w h k
  let u := hatCodes w h
  let s := kmswStage u m
  let p := outerSucc_castDart (kmswStage_nextEdge_mono u (Nat.le_succ m))
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge u le_rfl⟩, true)
  let x := (kmswRootedStage u (m + 1)).root
  let y := (kmswMap u (m + 1)).edgeInv x
  let j := hatDartMap w h (m + 1)
  let ρ := (kmswMap w (quadrantRStageTime w h (m + 1))).rot
  change s.UR = [] at hur
  have hc : kmswCodeStep (u m) = .down := by
    dsimp only [u, m]
    rw [hatCodes_at_exit]
    rfl
  have hs : kmswStage u (m + 1) = kmswStepOfStep s .down := by
    change kmswStep s (u m) = _
    rw [kmswStep, hc]
  have hk : (kmswStage u (m + 1)).nextEdge = s.nextEdge + 1 := by
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  have hx : x.1.val = s.nextEdge := by
    change (kmswStage u (m + 1)).active = _
    rw [hs]
    simp only [kmswStepOfStep, hur, State.addEdge]
  have hy : y.1.val = s.nextEdge := hx
  have hp : Function.Injective p := by
    intro d e he
    exact Prod.ext (Fin.ext (congrArg (fun z => z.1.val) he)) (congrArg (fun z : StageDart (kmswStage u (m + 1)).nextEdge => z.2) he)
  have hxr : x ∉ Set.range p := by
    rintro ⟨d, hd⟩
    have he : d.1.val = s.nextEdge := (congrArg (fun z => z.1.val) hd).trans hx
    exact (ne_of_lt d.1.isLt) he
  have hyr : y ∉ Set.range p := by
    rintro ⟨d, hd⟩
    have he : d.1.val = s.nextEdge := (congrArg (fun z => z.1.val) hd).trans hy
    exact (ne_of_lt d.1.isLt) he
  have hcover : ∀ z, (∃ d, p d = z) ∨ z = x ∨ z = y := by
    intro z
    by_cases hold : z.1.val < s.nextEdge
    · exact Or.inl ⟨(⟨z.1.val, hold⟩, z.2), rfl⟩
    · have hid : z.1.val = s.nextEdge := by
        have hb : z.1.val < s.nextEdge + 1 := lt_of_lt_of_le z.1.isLt hk.le
        omega
      right
      cases hb : z.2
      · exact Or.inl (Prod.ext (Fin.ext (hid.trans hx.symm)) hb)
      · exact Or.inr (Prod.ext (Fin.ext (hid.trans hy.symm)) hb)
  let q := outerSucc_castDart (kmswStage_nextEdge_mono w
    (quadrantRStageTime_mono w h (Nat.le_succ m)))
  have hq : Function.Injective q := by
    intro d e he
    exact Prod.ext (Fin.ext (congrArg (fun z => z.1.val) he)) (congrArg (fun z : StageDart (kmswStage w (quadrantRStageTime w h (m + 1))).nextEdge => z.2) he)
  have hmap : q ∘ hatDartMap w h m = j ∘ p := by
    funext d
    apply Prod.ext
    · exact Fin.ext (hatAllEdgeMap_extend w h m d.1.val d.1.isLt).symm
    · rfl
  have whole := hatExit_induced_rotation_comp
    (stageRot u m) (kmswMap w (quadrantRStageTime w h m)).rot ρ
    (hatDartMap w h m) q hq ih
    (hatExit_ambient_rotation_induced w (quadrantRStageTime w h m)
      (quadrantRStageTime w h (m + 1))
      (quadrantRStageTime_mono w h (Nat.le_succ m)))
  rw [hmap] at whole
  have hglobalUR : (kmswStage w (walkNL w h k - 1)).UR = [] := by
    have he := (hatAll_sim w h m).ur_eq
    change List.map (hatAllEdgeMap w h m) s.UR = _ at he
    rw [hur, List.map_nil] at he
    simpa only [m, quadrantRStageTime_hatExitIndex] using he.symm
  let t := walkNR w h (k + 1) - 1
  have ht : quadrantRStageTime w h (m + 1) = t + 1 := by
    have htime := (hatExit_rotation_times w h k).2
    have hpos := (walkNR_succ_spec w h k).1
    dsimp only [m, t]
    omega
  have hURt : (kmswStage w t).UR = [] :=
    (hatLPhase_right_boundary w h k).1.trans hglobalUR
  have hct : kmswCodeStep (w t) = .down := by
    dsimp only [t]
    rw [walkNR_succ_previous_code w h k]
    rfl
  have hyglobal : j y = (kmswMap w (quadrantRStageTime w h (m + 1))).edgeInv
      (kmswRootedStage w (quadrantRStageTime w h (m + 1))).root := by
    change hatDartMap w h (m + 1)
      ((kmswMap u (m + 1)).edgeInv (kmswRootedStage u (m + 1)).root) = _
    rw [← hatDartMap_edgeInv]
    exact congrArg _ (hatDartMap_root w h (m + 1))
  have ry : ρ (j y) = j y := by
    rw [hyglobal]
    change stageRot w (quadrantRStageTime w h (m + 1)) _ = _
    rw [ht]
    exact (exit_stage_pendant_tables w t hct hURt).2.2
  have tab := exit_stage_pendant_tables u m hc hur
  exact exit_extend_return (stageRot u m) (stageRot u (m + 1)) ρ p j hp
    (hatDartMap_injective w h (m + 1)) A x y hxr hyr hcover
    tab.1 tab.2.1 tab.2.2 ry whole (hatExit_pendant_attachment_corner w h k hur)

/-- Both exit stack cases transport the entire induced-rotation invariant.
This is a helper toward lem-quad-kmsw; not the paper result -/
theorem hatDartMap_rot_induced_exit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ)
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k) d) =
            hatDartMap w h (hatExitIndex w h k)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k))) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).nextEdge,
      ∃ l : ℕ, 0 < l ∧
        ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[l]
          (hatDartMap w h (hatExitIndex w h k + 1) d) =
            hatDartMap w h (hatExitIndex w h k + 1)
              ((kmswMap (hatCodes w h) (hatExitIndex w h k + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < l →
          ((kmswMap w (quadrantRStageTime w h (hatExitIndex w h k + 1))).rot : _ → _)^[j]
            (hatDartMap w h (hatExitIndex w h k + 1) d) ∉
              Set.range (hatDartMap w h (hatExitIndex w h k + 1)) := by
  by_cases hur : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR = []
  · exact hatDartMap_rot_induced_exit_pendant w h k hur ih
  · exact hatDartMap_rot_induced_exit_activation w h k hur ih

end DirectedDistances.KMSW
end
