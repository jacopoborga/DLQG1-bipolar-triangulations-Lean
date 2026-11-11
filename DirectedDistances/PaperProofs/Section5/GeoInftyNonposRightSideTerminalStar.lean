/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideTerminal

/-! Terminal-star rotation transport for the nonpositive right side. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: strict ranks along a finite boundary chain
identify its last edge from its terminal rank. -/
private theorem rMinus_chain_terminal_rank (s : State) (r : ℕ → ℚ)
    (es : List ℕ) (hne : es ≠ []) (hc : WestEastChain s es)
    (hr : ∀ e ∈ es, r (s.west e) < r (s.east e)) :
    ∀ e ∈ es,
      r (s.west e) < r (s.east (es.getLast hne)) ∧
      r (s.east e) ≤ r (s.east (es.getLast hne)) ∧
      (r (s.east e) = r (s.east (es.getLast hne)) → e = es.getLast hne) := by
  induction es with
  | nil => exact (hne rfl).elim
  | cons a es ih =>
    cases es with
    | nil =>
      intro e he
      have heq : e = a := List.mem_singleton.mp he
      subst e
      exact ⟨hr a (by simp), le_rfl, fun _ => rfl⟩
    | cons b bs =>
      have hchain := List.isChain_cons_cons.mp hc
      have hi := ih (by simp) hchain.2 (fun e he => hr e (List.mem_cons_of_mem a he))
      have hb := hi b (List.mem_cons_self)
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        have ha : r (s.east a) < r (s.east ((b :: bs).getLast (by simp))) := by
          rw [hchain.1]
          exact hb.1
        exact ⟨(hr a (List.mem_cons_self)).trans ha, ha.le,
          fun heq => (ne_of_lt ha heq).elim⟩
      · exact hi e he

/-- Helper toward Lemma 5.5: the exterior lower-right corner closes at
the terminal shared dart in the finite prefix rotation. -/
theorem rMinus_terminal_prefix_exterior_corner (w : ℕ → Fin 3) (n : ℕ) :
    let F := kmswStage w n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    ∃ p : StageDart F.nextEdge,
      p ∈ stageOuterWord w n ∧ p.2 = true ∧
      stageRot w n p = rMinusPrefixBoundaryDart w n (i, true) := by
  dsimp only
  let F := kmswStage w n
  let N := (F.active :: F.UR).length
  let i : Fin N := ⟨N - 1, by dsimp only [N]; simp only [List.length_cons]; omega⟩
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hword : stageOuterWordVal w n =
      xs.map (fun e => (e, false)) ++
        (F.active :: F.UR).map (fun e => (e, false)) ++
          F.LR.reverse.map (fun e => (e, true)) ++
            F.LL.reverse.map (fun e => (e, true)) := by
    rw [stageOuterWordVal_eq_runs, hxs]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    rfl
  have hN : 0 < N := by dsimp only [N]; simp only [List.length_cons]; omega
  have hLR : 0 < F.LR.length := List.length_pos_iff.mpr (kmswStage_LR_nonempty w n)
  have hindex : xs.length + N - 1 < (stageOuterWordVal w n).length := by
    rw [hword]
    simp only [List.length_append, List.length_map, List.length_reverse]
    omega
  have hval : (stageOuterWordVal w n)[xs.length + N - 1]? =
      some ((F.active :: F.UR)[i.val], false) := by
    rw [hword]
    simp only [List.append_assoc]
    rw [List.getElem?_append_right (by simp only [List.length_map]; omega),
      List.length_map]
    have hs : xs.length + N - 1 - xs.length = N - 1 := by omega
    rw [hs, List.getElem?_append_left (by simp only [List.length_map]; omega),
      List.getElem?_map, List.getElem?_eq_getElem i.isLt]
    rfl
  obtain ⟨d, p, hd, hp, hface⟩ :=
    outer_faceSucc_exists w n (stageOuterWord_faceSucc w n) _ hindex
  have hdv := Option.some.inj (hd.symm.trans hval)
  have hdp : d = ((rMinusPrefixBoundaryDart w n (i, true)).1, false) := by
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hdv)) (congrArg (fun z : ℕ × Bool => z.2) hdv)
  have hnext : (xs.length + N - 1 + 1) % (stageOuterWordVal w n).length =
      xs.length + N := by
    rw [show xs.length + N - 1 + 1 = xs.length + N by omega]
    apply Nat.mod_eq_of_lt
    rw [hword]
    simp only [List.length_append, List.length_map, List.length_reverse]
    omega
  rw [hnext, hword] at hp
  simp only [List.append_assoc] at hp
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega),
    List.length_map, Nat.add_sub_cancel_left,
    List.getElem?_append_right (by simp only [List.length_map, N]; omega),
    List.length_map, show N - (F.active :: F.UR).length = 0 from Nat.sub_self N,
    List.getElem?_append_left (by simp only [List.length_map, List.length_reverse]; omega),
    List.getElem?_map] at hp
  have hpbit : p.2 = true := by
    cases he : F.LR.reverse[0]? with
    | none => simp only [he, Option.map_none] at hp; cases hp
    | some e =>
      simp only [he, Option.map_some] at hp
      exact (congrArg Prod.snd (Option.some.inj hp)).symm
  have hpm : p ∈ stageOuterWord w n := by
    apply (stageOuterWord_mem_val w n p).mpr
    exact List.mem_iff_getElem?.mpr ⟨xs.length + N, by
      rw [hword]
      simp only [List.append_assoc]
      rw [List.getElem?_append_right (by simp only [List.length_map]; omega),
        List.length_map, Nat.add_sub_cancel_left,
        List.getElem?_append_right (by simp only [List.length_map, N]; omega),
        List.length_map, show N - (F.active :: F.UR).length = 0 from Nat.sub_self N,
        List.getElem?_append_left (by simp only [List.length_map, List.length_reverse]; omega),
        List.getElem?_map]
      exact hp⟩
  refine ⟨p, hpm, hpbit, ?_⟩
  rw [hdp] at hface
  change (stageRot w n).symm (rMinusPrefixBoundaryDart w n (i, true)) = p at hface
  exact ((stageRot w n).symm_apply_eq.mp hface).symm

/-- Helper toward Lemma 5.5: the terminal vertex has only one finite
exterior corner, whose successor is the terminal shared dart. -/
theorem rMinus_terminal_outer_rotation (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : d ∈ stageOuterWord w n) :
    let F := kmswStage w n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    stageEndpoint F d = stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) →
      stageRot w n d = rMinusPrefixBoundaryDart w n (i, true) := by
  dsimp only
  intro hv
  let F := kmswStage w n
  let U := F.active :: F.UR
  let i : Fin U.length := ⟨U.length - 1, by dsimp only [U]; simp only [List.length_cons]; omega⟩
  let c := rMinusPrefixBoundaryDart w n (i, true)
  let r := kmswStageRank w n
  have hb := kmswStage_boundary_chain_invariant w n
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hu : F.UL ++ F.UR = xs ++ U := by
    rw [show F.UL = xs ++ [F.active] from hxs, List.append_assoc]
    rfl
  have hUne : F.UL ++ F.UR ≠ [] := by simp [hu, U]
  have hLne : F.LL ++ F.LR ≠ [] := by
    intro he
    exact (kmswStage_LR_nonempty w n) (List.append_eq_nil_iff.mp he).2
  have htop : F.east ((F.UL ++ F.UR).getLast hUne) = stageEndpoint F c := by
    have hUneU : U ≠ [] := by simp [U]
    have he : (F.UL ++ F.UR).getLast hUne = U.getLast hUneU := by
      simp only [hu, List.getLast_append_of_right_ne_nil xs U hUneU]
    rw [he, List.getLast_eq_getElem]
    rfl
  have hlow : F.east ((F.LL ++ F.LR).getLast hLne) = stageEndpoint F c := by
    have he := hb.2.2.2.1
    change (F.UL ++ F.UR).getLast?.map F.east =
      (F.LL ++ F.LR).getLast?.map F.east at he
    rw [List.getLast?_eq_some_getLast hUne, List.getLast?_eq_some_getLast hLne] at he
    exact (Option.some.inj he).symm.trans htop
  have hr (e : ℕ) (he : e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR) :
      r (F.west e) < r (F.east e) :=
    kmswStageRank_strict w n e ((kmswStage_boundary_ids_lt_nextEdge w n).2 e he)
  have hupper := rMinus_chain_terminal_rank F r (F.UL ++ F.UR) hUne hb.1
    (fun e he => hr e (List.mem_append_left _ (List.mem_append_left _ he)))
  have hlower := rMinus_chain_terminal_rank F r (F.LL ++ F.LR) hLne hb.2.1
    (fun e he => hr e (by
      simp only [List.mem_append] at he ⊢
      tauto))
  have hclass (a : StageDart F.nextEdge) (ha : a ∈ stageOuterWord w n)
      (hav : stageEndpoint F a = stageEndpoint F c) :
      a = (⟨(F.LL ++ F.LR).getLast hLne, by
        apply (kmswStage_boundary_ids_lt_nextEdge w n).2
        have hm := List.getLast_mem hLne
        simp only [List.mem_append] at hm ⊢
        tauto⟩, true) := by
    rcases (stageOuterWord_mem_iff w n a).mp ha with ⟨hab, ham⟩ | ⟨hab, ham⟩
    · have hm : a.1.val ∈ F.UL ++ F.UR := List.mem_append.mpr ham
      have hh := (hupper a.1.val hm).1
      rw [htop] at hh
      have he : F.west a.1.val = stageEndpoint F c := by
        simpa only [stageEndpoint, hab, Bool.false_eq_true, ↓reduceIte] using hav
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
    · have hm : a.1.val ∈ F.LL ++ F.LR := List.mem_append.mpr ham.symm
      have he : F.east a.1.val = stageEndpoint F c := by
        simpa only [stageEndpoint, hab, ↓reduceIte] using hav
      exact Prod.ext (Fin.ext ((hlower a.1.val hm).2.2 (by rw [he, hlow]))) hab
  obtain ⟨p, hp, _, hpc⟩ := rMinus_terminal_prefix_exterior_corner w n
  have hpv : stageEndpoint F p = stageEndpoint F c := by
    apply (stageRot_sameCycle_iff_endpoint_eq w n p c).mp
    exact ⟨1, by simpa only [zpow_one] using hpc⟩
  have hdp : d = p := (hclass d hd hv).trans (hclass p hp hpv).symm
  exact hdp ▸ hpc

/-- Helper toward Lemma 5.5: the terminal star meets the finite shared
segment in exactly its final reverse dart. -/
theorem rMinus_terminal_shared_prefix_star (w : ℕ → Fin 3) (n : ℕ)
    (b : StageDart ((kmswStage w n).active :: (kmswStage w n).UR).length) :
    let F := kmswStage w n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    stageEndpoint F (rMinusPrefixBoundaryDart w n b) =
        stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) →
      rMinusPrefixBoundaryDart w n b = rMinusPrefixBoundaryDart w n (i, true) := by
  dsimp only
  intro hv
  let F := kmswStage w n
  let U := F.active :: F.UR
  have hne : U ≠ [] := by simp [U]
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hu : F.UL ++ F.UR = xs ++ U := by
    rw [show F.UL = xs ++ [F.active] from hxs, List.append_assoc]
    rfl
  have hc : WestEastChain F U := by
    have hh := (kmswStage_boundary_chain_invariant w n).1
    rw [hu] at hh
    exact hh.right_of_append
  have hh := rMinus_chain_terminal_rank F (kmswStageRank w n) U hne hc (by
    intro e he
    apply kmswStageRank_strict w n e
    rcases List.mem_cons.mp he with he | he
    · rw [he]
      exact act_lt_nextEdge w le_rfl
    · exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        tauto)) U[b.1.val] (List.getElem_mem b.1.isLt)
  cases hb : b.2 with
  | false =>
    have he : F.west (U[b.1.val]) = F.east (U.getLast hne) := by
      simpa only [stageEndpoint, rMinusPrefixBoundaryDart, hb, Bool.false_eq_true,
        ↓reduceIte, List.getLast_eq_getElem] using hv
    exact (lt_irrefl _ (he ▸ hh.1)).elim
  | true =>
    have he : F.east (U[b.1.val]) = F.east (U.getLast hne) := by
      simpa only [stageEndpoint, rMinusPrefixBoundaryDart, hb, ↓reduceIte,
        List.getLast_eq_getElem] using hv
    have heq := hh.2.2 (congrArg (kmswStageRank w n) he)
    rw [List.getLast_eq_getElem] at heq
    exact Prod.ext (Fin.ext (heq)) hb

/-- Helper toward Lemma 5.5: before every nonshared terminal prefix
dart, the ambient predecessor is already the finite prefix predecessor. -/
theorem rMinus_terminal_prefix_predecessor (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    let F := kmswStage w n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    let c := rMinusPrefixBoundaryDart w n (i, true)
    stageEndpoint F d = stageEndpoint F c → d ≠ c →
      kmswInfRot w hfin
        (((stageRot w n).symm d).1.val, ((stageRot w n).symm d).2) =
          (d.1.val, d.2) := by
  dsimp only
  intro hv hne
  let p := (stageRot w n).symm d
  have hpv : stageEndpoint (kmswStage w n) p = stageEndpoint (kmswStage w n) d := by
    apply (stageRot_sameCycle_iff_endpoint_eq w n p d).mp
    exact ⟨1, by simp only [zpow_one, p, Equiv.apply_symm_apply]⟩
  have hpnot : p ∉ stageOuterWord w n := by
    intro hp
    have he := rMinus_terminal_outer_rotation w n p hp (hpv.trans hv)
    exact hne ((stageRot w n).apply_symm_apply d |>.symm.trans he)
  have he := rMinusInfRot_of_not_outer w hfin n p hpnot
  simpa only [p, Equiv.apply_symm_apply] using he

section TerminalStarGeometry

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime (shiftedStream W 0) h k
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
local notation "q" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q
local notation "N" => List.length (State.active (kmswStage (shiftedStream W 0)
  (boundaryHitTime (shiftedStream W 0) h k)) ::
  State.UR (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)))
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hfin in
/-- Helper toward Lemma 5.5: the common terminal darts of the prefix
and retained hatted blocks form one literal shared port. -/
theorem rMinus_terminal_common_dart
    (p : StageDart (F).nextEdge)
    (a : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (he : (p.1.val, p.2) = (EH a.val.1, a.val.2)) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    stageEndpoint F p = stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) →
      p = rMinusPrefixBoundaryDart w n (i, true) := by
  dsimp only
  intro hv
  have hedge := congrArg (fun z : ℕ × Bool => z.1) he
  obtain ⟨j, hj, _⟩ := (rMinus_cross_edge_eq_iff hτ hqMode hfin
    ⟨p.1.val, p.1.isLt⟩ ⟨a.val.1, a.property⟩).mp hedge
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have hpeq : p = rMinusPrefixBoundaryDart w n (⟨j, hjlt⟩, p.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (List.getElem?_eq_some_iff.mp hj).2.symm
    · rfl
  rw [hpeq] at hv ⊢
  exact rMinus_terminal_shared_prefix_star w n _ hv

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a terminal hatted dart other than the shared
port returns through the hatted block without meeting a prefix dart. -/
theorem rMinus_terminal_hatted_nonshared_side_rotation
    (a : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    let c := rMinusPrefixBoundaryDart w n (i, true)
    kmswLimitDartVertex w (EH a.val.1, a.val.2) = stageEndpoint F c →
    (EH a.val.1, a.val.2) ≠ (c.1.val, c.2) →
    (S).rotation (EH a.val.1, a.val.2)
      (EH (rMinusHattedRotation _ q a).val.1, (rMinusHattedRotation _ q a).val.2) := by
  dsimp only
  intro hv hne
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let c := rMinusPrefixBoundaryDart w n (i, true)
  let cH : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
  let σ := kmswInfRot w (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let x := J a
  have hch : (c.1.val, c.2) = J cH :=
    rMinusPrefixDartImage_boundary hτ hqMode i.val _
      (List.getElem?_eq_getElem i.isLt) true
  have hvertex (j : ℕ) : kmswLimitDartVertex w ((σ : _ → _)^[j] x) =
      stageEndpoint F c := by
    induction j with
    | zero => exact hv
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (kmswLimitDartVertex_rot w (H.1 0) _).trans ih
  have hpvertex (j : ℕ) (p : StageDart (F).nextEdge)
      (he : (p.1.val, p.2) = (σ : _ → _)^[j] x) :
      stageEndpoint F p = stageEndpoint F c := by
    have hh := (congrArg (kmswLimitDartVertex w) he).trans (hvertex j)
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then (F).east p.1.val else (F).west p.1.val) = _
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _ at hh
    simpa only [he.1, he.2] using hh
  obtain ⟨t, ht, hte, hgap⟩ :=
    rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin a
  change (σ : _ → _)^[t] x = J (rMinusHattedRotation _ q a) at hte
  change ∀ j : ℕ, 0 < j → j < t → (σ : _ → _)^[j] x ∉ Set.range J at hgap
  have hnotP (j : ℕ) (hjt : j < t) :
      (σ : _ → _)^[j] x ∉ Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
    induction j with
    | zero =>
      rintro ⟨p, hp⟩
      have hp' : (p.1.val, p.2) = J a := hp
      have he := rMinus_terminal_common_dart hτ hqMode hfin p a hp'
        (hpvertex 0 p hp')
      exact hne (hp'.symm.trans (congrArg (fun d : StageDart (F).nextEdge =>
        (d.1.val, d.2)) he))
    | succ j ih =>
      rintro ⟨p, hp⟩
      have hp' : (p.1.val, p.2) = (σ : _ → _)^[j + 1] x := hp
      have hpv := hpvertex (j + 1) p hp'
      have hpc : p ≠ c := by
        intro he
        apply hgap (j + 1) (by omega) hjt
        exact ⟨cH, hch.symm.trans (he ▸ hp')⟩
      have hpred := rMinus_terminal_prefix_predecessor w (H.1 0) n p hpv hpc
      apply ih (by omega)
      refine ⟨(stageRot w n).symm p, ?_⟩
      apply σ.injective
      rw [show rMinusPrefixDartImage (h := h) ((stageRot w n).symm p) =
        (((stageRot w n).symm p).1.val, ((stageRot w n).symm p).2) from rfl,
        hpred]
      exact hp'.trans (Function.iterate_succ_apply' _ _ _)
  refine ⟨t, ht, hte, ?_⟩
  intro j hj hjt hm
  rcases (Set.ext_iff.mp (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hpref | hh
  · exact hnotP j hjt hpref
  · exact hgap j hj hjt hh

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at the terminal exterior corner, the first
return to the glued side continues into the next hatted boundary edge. -/
theorem rMinus_terminal_outer_side_rotation (hneg : k < 0)
    (p : StageDart (F).nextEdge) (hpout : p ∈ stageOuterWord w n) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    let c := rMinusPrefixBoundaryDart w n (i, true)
    let cH : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
    stageEndpoint F p = stageEndpoint F c →
    (S).rotation (p.1.val, p.2)
      (EH (rMinusHattedRotation _ q cH).val.1,
        (rMinusHattedRotation _ q cH).val.2) := by
  dsimp only
  intro hpv
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let c := rMinusPrefixBoundaryDart w n (i, true)
  let cH : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
  let σ := kmswInfRot w (H.1 0)
  let ρ := stageRot w n
  let I : StageDart (F).nextEdge → ℕ × Bool := fun a => (a.1.val, a.2)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun a => (EH a.val.1, a.val.2)
  have hI : Function.Injective I := by
    intro a b he
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) he))
      (congrArg (fun z : ℕ × Bool => z.2) he)
  have hch : I c = J cH :=
    rMinusPrefixDartImage_boundary hτ hqMode i.val _
      (List.getElem?_eq_getElem i.isLt) true
  have hpc : ρ p = c := rMinus_terminal_outer_rotation w n p hpout hpv
  have hcnot : c ∉ stageOuterWord w n :=
    rMinus_negative_shared_reverse_not_outer w h hneg i
  have hpne : p ≠ c := fun he => hcnot (he ▸ hpout)
  have hcycle := (stageRot_sameCycle_iff_endpoint_eq w n c p).mpr hpv.symm
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hex : ∃ j : ℕ, (ρ : _ → _)^[j] c = p :=
    ⟨m, by simpa only [Equiv.Perm.coe_pow] using hm⟩
  let l := Nat.find hex
  have hl : (ρ : _ → _)^[l] c = p := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j < l) : (ρ : _ → _)^[j] c ≠ p := Nat.find_min hex hj
  have hrotv (a : StageDart (F).nextEdge) : stageEndpoint F (ρ a) = stageEndpoint F a := by
    exact ((stageRot_sameCycle_iff_endpoint_eq w n a (ρ a)).mp ⟨1, rfl⟩).symm
  have hvert (j : ℕ) : stageEndpoint F ((ρ : _ → _)^[j] c) = stageEndpoint F c := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hrotv, ih]
  have hwalk (j : ℕ) (hj : j ≤ l) :
      (σ : _ → _)^[j] (I c) = I ((ρ : _ → _)^[j] c) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : (ρ : _ → _)^[j] c ∉ stageOuterWord w n := by
        intro ho
        have he := rMinus_terminal_outer_rotation w n _ ho (hvert j)
        apply hmin j (by omega)
        exact ρ.injective (he.trans hpc.symm)
      have he := rMinusInfRot_of_not_outer w (H.1 0) n _ hno
      rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
      exact he
  have hlp : (σ : _ → _)^[l] (I c) = I p := (hwalk l le_rfl).trans (congrArg I hl)
  have hpnotH : I p ∉ Set.range J := by
    rintro ⟨a, ha⟩
    exact hpne (rMinus_terminal_common_dart hτ hqMode hfin p a ha.symm hpv)
  obtain ⟨t, ht, hte, hgap⟩ :=
    rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin cH
  change (σ : _ → _)^[t] (J cH) = J (rMinusHattedRotation _ q cH) at hte
  change ∀ j : ℕ, 0 < j → j < t → (σ : _ → _)^[j] (J cH) ∉ Set.range J at hgap
  rw [← hch] at hte hgap
  have hlt : l < t := by
    by_contra hn
    have htwalk := hwalk t (by omega)
    have he : I ((ρ : _ → _)^[t] c) = J (rMinusHattedRotation _ q cH) := htwalk.symm.trans hte
    have hc' := rMinus_terminal_common_dart hτ hqMode hfin _ _ he (hvert t)
    have hret : (ρ : _ → _)^[t] c = c := hc'
    have hpred : (ρ : _ → _)^[t - 1] c = p := by
      apply ρ.injective
      rw [hpc, ← Function.iterate_succ_apply' (ρ : _ → _) (t - 1) c,
        show (t - 1).succ = t by omega, hret]
    exact hmin (t - 1) (by omega) hpred
  obtain ⟨s, hs, hse, hsgap⟩ := rMinusPrefixDartImage_firstReturn (H := H) p
  change (σ : _ → _)^[s] (I p) = I (ρ p) at hse
  change ∀ j : ℕ, 0 < j → j < s → (σ : _ → _)^[j] (I p) ∉ Set.range I at hsgap
  rw [hpc] at hse
  have hts : t - l < s := by
    by_contra hn
    have he : (σ : _ → _)^[l + s] (I c) = I c := by
      rw [Nat.add_comm, Function.iterate_add_apply, hlp, hse]
    have hle : l + s ≤ t := by omega
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exact hgap (l + s) (by omega) hlt' ⟨cH, hch.symm.trans he.symm⟩
    · have he' : J (rMinusHattedRotation _ q cH) = J cH := by
        rw [← hte, ← heq, he, hch]
      have hb := congrArg (fun z : ℕ × Bool => z.2) he'
      have hcorner := rMinusHattedRotation_boundary_corner hqMode i.val
      change rMinusHattedRotation _ q cH = _ at hcorner
      rw [hcorner] at hb
      exact Bool.false_ne_true hb
  refine ⟨t - l, by omega, ?_, ?_⟩
  · have he : (σ : _ → _)^[t - l] (I p) = (σ : _ → _)^[t] (I c) := by
      rw [← hlp, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    exact he.trans hte
  · intro j hj hjt hm
    rcases (Set.ext_iff.mp (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hpref | hh
    · exact hsgap j hj (by omega) hpref
    · apply hgap (l + j) (by omega) (by omega)
      rw [Nat.add_comm l j, Function.iterate_add_apply, hlp]
      exact hh

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the initial conjugating transposition fixes
every terminal-star dart. -/
theorem rMinus_terminal_initial_swap_fixed
    (d : RMinusCodeGluedDart F Q) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
    let A := rMinusCodeBoundaryDart w n Q (i₀, false)
    let B := rMinusCodePrefixDart F Q
      (stageRot w n (rMinusPrefixBoundaryDart w n (i₀, false)))
    kmswLimitDartVertex w (D d).val =
        stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) →
      Equiv.swap A B d = d := by
  dsimp only
  intro hv
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let a := rMinusPrefixBoundaryDart w n (i₀, false)
  let c := rMinusPrefixBoundaryDart w n (i, true)
  have hne : stageEndpoint F a ≠ stageEndpoint F c := by
    intro he
    have hh := rMinus_terminal_shared_prefix_star w n (i₀, false) he
    exact Bool.false_ne_true (congrArg (fun z : StageDart (F).nextEdge => z.2) hh)
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he
    apply hne
    rw [he, rMinusCodeBoundaryDart_eq_prefix] at hv
    exact (hvpref a).symm.trans hv
  · intro he
    apply hne
    have hrot := (stageRot_sameCycle_iff_endpoint_eq w n a (stageRot w n a)).mp ⟨1, rfl⟩
    rw [he] at hv
    exact hrot.trans ((hvpref (stageRot w n a)).symm.trans hv)

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the original splice has the geometric
successor throughout the terminal star. -/
theorem rMinusCodeSpliceRotation_terminal_star_side_rotation (hneg : k < 0)
    (d : RMinusCodeGluedDart F Q) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    kmswLimitDartVertex w (D d).val =
        stageEndpoint F (rMinusPrefixBoundaryDart w n (i, true)) →
      (S).rotation (D d).val (D (rMinusCodeSpliceRotation w n q d)).val := by
  dsimp only
  intro hv
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let c := rMinusPrefixBoundaryDart w n (i, true)
  let cH : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hC (b : StageDart N) : (rMinusBoundaryCornerPerm N).extendDomain Cemb
      (rMinusCodeBoundaryDart w n Q b) =
        rMinusCodeBoundaryDart w n Q (rMinusBoundaryCornerPerm N b) :=
    (rMinusBoundaryCornerPerm N).extendDomain_apply_image Cemb b
  have hH (a : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
      (rMinusHattedRotation _ q).extendDomain Hemb (rMinusCodeHattedDart F Q a) =
        rMinusCodeHattedDart F Q (rMinusHattedRotation _ q a) :=
    (rMinusHattedRotation _ q).extendDomain_apply_image Hemb a
  have hCsub : Set.range (rMinusCodeBoundaryDart w n Q) ⊆
      Set.range (rMinusCodeHattedDart F Q) := by
    rintro _ ⟨⟨j, b⟩, rfl⟩
    rw [rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  have hvpref (p : StageDart (F).nextEdge) :
      kmswLimitDartVertex w (D (rMinusCodePrefixDart F Q p)).val = stageEndpoint F p := by
    rw [rMinusCodeGluedDartEquiv_prefix]
    have he := edge_endpoints_eq w p.1.isLt
    change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _
    simp only [stageEndpoint, he.1, he.2]
  by_cases hdP : d ∈ Set.range (rMinusCodePrefixDart F Q)
  · obtain ⟨p, rfl⟩ := hdP
    have hpv : stageEndpoint F p = stageEndpoint F c := (hvpref p).symm.trans hv
    have hrotv : stageEndpoint F (stageRot w n p) = stageEndpoint F c :=
      ((stageRot_sameCycle_iff_endpoint_eq w n p (stageRot w n p)).mp ⟨1, rfl⟩).symm.trans hpv
    have hP : (stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p) =
        rMinusCodePrefixDart F Q (stageRot w n p) :=
      (stageRot w n).extendDomain_apply_image Pemb p
    change (S).rotation (D (rMinusCodePrefixDart F Q p)).val
      (D ((rMinusHattedRotation _ q).extendDomain Hemb
        ((rMinusBoundaryCornerPerm N).extendDomain Cemb
          ((stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q p))))).val
    rw [hP]
    by_cases hpout : p ∈ stageOuterWord w n
    · have hpc := rMinus_terminal_outer_rotation w n p hpout hpv
      rw [hpc]
      have hcC : rMinusCodePrefixDart F Q c = rMinusCodeBoundaryDart w n Q (i, true) := rfl
      rw [hcC, hC]
      have hcorner : rMinusBoundaryCornerPerm N (i, true) = (i, true) := by
        change rMinusBoundaryCorner N (i, true) = _
        simp only [rMinusBoundaryCorner, ↓reduceIte, show ¬i.val + 1 < N by
          dsimp only [i]; omega, ↓reduceDIte]
      rw [hcorner, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk,
        hH,
        rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_hatted]
      exact rMinus_terminal_outer_side_rotation hτ hp P hqMode Tpath hfin hleft hk hneg p hpout hpv
    · have hnotH : rMinusCodePrefixDart F Q (stageRot w n p) ∉
          Set.range (rMinusCodeHattedDart F Q) := by
        rintro ⟨a, ha⟩
        have he := congrArg (fun z => (D z).val) ha
        rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at he
        have hc' := rMinus_terminal_common_dart hτ hqMode hfin _ a he.symm hrotv
        obtain ⟨p₀, hp₀, _, hp₀c⟩ := rMinus_terminal_prefix_exterior_corner w n
        exact hpout ((stageRot w n).injective (hc'.trans hp₀c.symm) ▸ hp₀)
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ Cemb (fun hm => hnotH (hCsub hm)),
        Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hnotH,
        rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
      exact ⟨1, Nat.zero_lt_one, rMinusInfRot_of_not_outer w (H.1 0) n p hpout,
        fun j hj hj1 _ => by omega⟩
  · have hm : (D d).val ∈ {a : ℕ × Bool | a.1 ∈ (S).edges} := (D d).property
    rw [rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk] at hm
    rcases hm with ⟨p, hp'⟩ | ⟨a, ha⟩
    · apply False.elim
      apply hdP
      refine ⟨p, ?_⟩
      apply (D).injective
      apply Subtype.ext
      rw [rMinusCodeGluedDartEquiv_prefix]
      exact hp'
    · have had : rMinusCodeHattedDart F Q a = d := by
        apply (D).injective
        apply Subtype.ext
        rw [rMinusCodeGluedDartEquiv_hatted]
        exact ha
      have hnotC : d ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
        rintro ⟨b, hb⟩
        exact hdP ⟨rMinusPrefixBoundaryDart w n b, hb⟩
      have hne : (EH a.val.1, a.val.2) ≠ (c.1.val, c.2) := by
        intro he
        apply hdP
        refine ⟨c, ?_⟩
        apply (D).injective
        apply Subtype.ext
        rw [rMinusCodeGluedDartEquiv_prefix]
        exact he.symm.trans ha
      change (S).rotation (D d).val
        (D ((rMinusHattedRotation _ q).extendDomain Hemb
          ((rMinusBoundaryCornerPerm N).extendDomain Cemb
            ((stageRot w n).extendDomain Pemb d)))).val
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hdP,
        Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnotC, ← had,
        hH,
        rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_hatted]
      exact rMinus_terminal_hatted_nonshared_side_rotation hτ hp P hqMode Tpath hfin hleft hk
        a ((congrArg (kmswLimitDartVertex w) ha).trans hv) hne

end TerminalStarGeometry

/-- Helper toward Lemma 5.5: every dart in the terminal endpoint star
has its actual geometric successor under the adjusted candidate. -/
theorem rMinusCodeInitialAdjustedRotation_terminal_star_side_rotation
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .right q
    let n := boundaryHitTime (shiftedStream W 0) h k
    let F := kmswStage (shiftedStream W 0) n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    ∀ d : RMinusCodeGluedDart F M,
      kmswLimitDartVertex (shiftedStream W 0) (D d).val =
        stageEndpoint F (rMinusPrefixBoundaryDart (shiftedStream W 0) n (i, true)) →
      (m0GeodesicSide hp P .right).rotation (D d).val
        (D (rMinusCodeInitialAdjustedRotation (shiftedStream W 0) n q d)).val

    := by
  dsimp only
  intro d hv
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  let F := kmswStage w n
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  by_cases hk0 : k = 0
  · have ht : n = 0 := by dsimp only [n]; rw [hk0, boundaryHitTime_zero]
    have he : rMinusCodeInitialAdjustedRotation w n q = rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [he]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 d
  have hr := rMinusCodeSpliceRotation_terminal_star_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk (by omega : k < 0) d hv
  have hinput := rMinus_terminal_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk d hv
  have hnext : kmswLimitDartVertex w (D (rMinusCodeSpliceRotation w n q d)).val =
      kmswLimitDartVertex w (D d).val := by
    obtain ⟨t, _, he, _⟩ := hr
    have hvert (j : ℕ) : kmswLimitDartVertex w
        ((kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val) =
          kmswLimitDartVertex w (D d).val := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact (kmswLimitDartVertex_rot w (H.1 0) _).trans ih
    exact (congrArg (kmswLimitDartVertex w) he).symm.trans (hvert t)
  have houtput := rMinus_terminal_initial_swap_fixed hτ hp P hqMode Tpath hfin hleft hk
    (rMinusCodeSpliceRotation w n q d) (hnext.trans hv)
  change (m0GeodesicSide hp P .right).rotation (D d).val
    (D (Equiv.swap _ _ (rMinusCodeSpliceRotation w n q (Equiv.swap _ _ d)))).val
  rw [hinput, houtput]
  exact hr


















































end DirectedDistances.PaperProofs.Section5
