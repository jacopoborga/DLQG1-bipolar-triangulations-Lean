module

public import DirectedDistances.KMSW.BoundaryEnumeration
public import DirectedDistances.KMSW.RightmostCoalescenceM0
public import DirectedDistances.KMSW.OutgoingIntervalFreshLeft
public import DirectedDistances.KMSW.WalkRecordCounts

/-! # Right boundary edges and rotation-order rightmost paths

hit-indexed positive boundary chain is compared with the right-boundary
record enumeration, then with the last entry of the rotation-order outgoing
list.

Scope: these are deterministic results for the combinatorial one-sided KMSW
carrier `M_{0,∞}` at `n = 0` only, under the displayed hypotheses. The LR
boundary chain is identified with the rotation-order rightmost path from `x₁`
inside `m_{0,∞}`, NOT inside `m_{−∞,∞}`. Ambient rightmostness in
`m_{−∞,∞}` and the coalescence assertion of `lem-uibot-bdy` are not
established here. The theorem `kmswInfFaceSucc_right_of_unbounded_below` is
not used by the main rightmost theorem (which uses `kmswInfFaceSucc_right`
under `hL`). -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory Quiver
open scoped Classical

private theorem rightCoordinate_step_abs (w : ℕ → Fin 3) (i : ℕ) :
    |R w (i + 1) - R w i| ≤ 1 := by
  have hR : R w (i + 1) = R w i +
      (RandomWalk.lazyTwoDimensionalStep (w i)).2 := Finset.sum_range_succ _ _
  have hinc : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w i)).2 ∧
      (RandomWalk.lazyTwoDimensionalStep (w i)).2 ≤ 1 := by
    have hcoord (c : Fin 3) : -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 ∧
        (RandomWalk.lazyTwoDimensionalStep c).2 ≤ 1 := by
      fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
    exact hcoord (w i)
  rw [hR]
  have hcalc : R w i + (RandomWalk.lazyTwoDimensionalStep (w i)).2 - R w i =
      (RandomWalk.lazyTwoDimensionalStep (w i)).2 := by omega
  rw [hcalc]
  apply abs_le.mpr
  constructor <;> omega

private theorem rightHitTime_is_record_index (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℕ} (hk : 1 ≤ k) :
    natSelect (fun m => ∀ j, j < m → R w m < R w j) k =
      boundaryHitTime w h (k : ℤ) := by
  let t := boundaryHitTime w h (k : ℤ)
  let P : ℕ → Prop := fun m => ∀ j, j < m → R w m < R w j
  have hvalue : R w t = -k := by
    exact boundaryHitTime_right_spec w h (by exact_mod_cast hk)
  have hhit : ∃ n, R w n = -(k : ℤ) := h.rightHit (k : ℤ) (by exact_mod_cast hk)
  have hkz : (k : ℤ) ≠ 0 := by omega
  have hkpos : 0 < (k : ℤ) := by omega
  have hfirst : t = Nat.find hhit := by
    dsimp [t, boundaryHitTime]
    simp only [dite_eq_right hkz, dite_eq_left hkpos]
  have hrecordMem := (strict_running_minimum_iff_first_hit (R w)
    (by simp [R]) (rightCoordinate_step_abs w) t t (-(k : ℤ)) (by omega) hhit).2
      ⟨le_rfl, hvalue, hfirst⟩
  have hrecord : P t := by
    exact (Finset.mem_filter.mp hrecordMem.1).2
  have hminimum : RandomWalk.globalLazyRunningMinimum (R w) t = -(k : ℤ) := by
    apply le_antisymm
    · calc
        RandomWalk.globalLazyRunningMinimum (R w) t ≤ R w t :=
          RandomWalk.globalLazyRunningMinimum_le (R w) le_rfl
        _ = -(k : ℤ) := hvalue
    · apply RandomWalk.le_globalLazyRunningMinimum
      intro j hj
      by_cases hlt : j < t
      · have hstrict := hrecord j hlt
        exact le_of_lt (by simpa [hvalue] using hstrict)
      · have : j = t := by omega
        subst j
        exact le_of_eq hvalue.symm
  have hcountZ : ((Nat.count P (t + 1) : ℕ) : ℤ) = k + 1 := by
    have hcard := card_weak_first_minima (R w) (by simp [R])
      (rightCoordinate_step_abs w) t
    rw [hminimum] at hcard
    rw [Nat.count_eq_card_filter_range]
    simpa [P] using hcard
  have hcount : Nat.count P (t + 1) = k + 1 := by
    apply_mod_cast hcountZ
  have hcount_succ := Nat.count_succ (p := P) t
  simp only [hrecord, ↓reduceIte] at hcount_succ
  have htcount : Nat.count P t = k := by omega
  have hselect := natSelect_count hrecord
  rw [htcount] at hselect
  simpa [P, t] using hselect

private theorem outgoingChain_head_of_incoming_predecessor
    (σ : Equiv.Perm (ℕ × Bool)) : ∀ {es : List ℕ} {e : ℕ},
    List.IsChain (fun a b => σ (a, false) = (b, false)) es →
    e ∈ es → (σ.symm (e, false)).2 = true → es.head? = some e := by
  intro es
  induction es with
  | nil =>
    intro e _ he _
    simp at he
  | cons a tail ih =>
    intro e hchain he hpred
    rcases List.mem_cons.mp he with he | he
    · subst e
      rfl
    · cases tail with
      | nil => simp at he
      | cons b rest =>
        have hchain' := List.isChain_cons_cons.mp hchain
        have hnext : σ (a, false) = (b, false) := hchain'.1
        have hhead : e = b := by
          have h := ih hchain'.2 he hpred
          simpa using h.symm
        subst e
        have hback : σ.symm (b, false) = (a, false) := by
          rw [← hnext]
          exact Equiv.symm_apply_apply σ (a, false)
        rw [hback] at hpred
        simp at hpred

private theorem rightBoundaryEdge_present (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (k : ℕ) :
    EdgePresent w (kmswRightBoundaryEdge w k) := by
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually w hR k
  have hentry := hN N le_rfl
  obtain ⟨hidx, hval⟩ := List.getElem?_eq_some_iff.mp hentry
  have hmem : kmswRightBoundaryEdge w k ∈ (kmswStage w N).LR := by
    rw [← hval]
    exact List.getElem_mem hidx
  have hbound : kmswRightBoundaryEdge w k < (kmswStage w N).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w N).2 _ (by
      simp only [List.mem_append]
      tauto)
  exact ⟨N, hbound, (kmswStage_status w N).2.2.1 _ hmem⟩

private theorem rightBoundaryEdge_source_eq_activeInitial (w : ℕ → Fin 3)
    {k : ℕ} :
    edgeWest w (kmswRightBoundaryEdge w k) =
      activeInitial w (natSelect (fun m => ∀ j, j < m → R w m < R w j) k) := rfl

private theorem rightBoundaryEdge_source_ne_zero (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    edgeWest w (kmswRightBoundaryEdge w k) ≠ 0 := by
  let P : ℕ → Prop := fun m => ∀ j, j < m → R w m < R w j
  let t := natSelect P k
  have hspec := natSelect_spec (right_record_infinite w hR) k
  have htpos : 0 < t := by
    have hcount : Nat.count P t = k := by simpa [t, P] using hspec.2
    by_contra hnot
    have ht0 : t = 0 := by omega
    rw [ht0] at hcount
    simp at hcount
    omega
  have hrec : ∀ j < t, R w t ≤ R w j - 1 := by
    intro j hj
    have h := hspec.1 j hj
    have hlt : R w t < R w j := by simpa [t, P] using h
    omega
  have hne := activeInitial_ne_of_right_record w t hrec 0 htpos
  have hP0 : P 0 := by simp [P]
  have hsel0 : natSelect P 0 = 0 := by
    simpa [P] using (natSelect_count hP0)
  have hroot : activeInitial w 0 = 0 := by
    have hpath := kmswRightBoundary_infinite_path w hL hR
    have hs := hpath.2.2.1
    change edgeWest w (act w (natSelect P 0)) = 0 at hs
    rw [hsel0] at hs
    exact hs
  have hsource : edgeWest w (kmswRightBoundaryEdge w k) = activeInitial w t := by
    simpa [t, P] using rightBoundaryEdge_source_eq_activeInitial w (k := k)
  intro hz
  apply hne
  calc
    activeInitial w 0 = 0 := hroot
    _ = edgeWest w (kmswRightBoundaryEdge w k) := hz.symm
    _ = activeInitial w t := hsource

/-- The positive hit-indexed edge agrees, with both endpoints, with the
corresponding strict right-record edge (`eqn-bdy-vertex-hit`, -/
theorem boundaryVertex_right_edge_present_source
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) {k : ℕ} (hk : 1 ≤ k) :
    EdgePresent w (kmswRightBoundaryEdge w k) ∧
      edgeWest w (kmswRightBoundaryEdge w k) = boundaryVertex w h (k : ℤ) ∧
      edgeEast w (kmswRightBoundaryEdge w k) = boundaryVertex w h (k + 1 : ℤ) := by
  obtain ⟨N, hN, hstage⟩ := boundaryVertex_right_edge w h
    (k := (k : ℤ)) (by exact_mod_cast hk)
  have hdata := hstage N le_rfl
  have htime : act w (boundaryHitTime w h (k : ℤ)) = kmswRightBoundaryEdge w k := by
    unfold kmswRightBoundaryEdge
    rw [rightHitTime_is_record_index w h hk]
  have hlt : act w (boundaryHitTime w h (k : ℤ)) < (kmswStage w N).nextEdge :=
    (act_lt_nextEdge w (by omega : boundaryHitTime w h (k : ℤ) ≤ N))
  have hlt' : kmswRightBoundaryEdge w k < (kmswStage w N).nextEdge := by
    rw [← htime]
    exact hlt
  have hend := edge_endpoints_eq w hlt'
  refine ⟨⟨N, hlt', ?_⟩, ?_, ?_⟩
  · rw [← htime]
    exact hdata.2.1
  · have hstageWest : (kmswStage w N).west (kmswRightBoundaryEdge w k) =
        boundaryVertex w h (k : ℤ) := by
      rw [← htime]
      exact hdata.2.2.1
    exact hend.1.symm.trans hstageWest
  · have hstageEast : (kmswStage w N).east (kmswRightBoundaryEdge w k) =
        boundaryVertex w h (k + 1 : ℤ) := by
      rw [← htime]
      exact hdata.2.2.2
    exact hend.2.symm.trans hstageEast

private theorem outerWordVal_getElem?_LR_any (w : ℕ → Fin 3) (n j e : ℕ)
    (he : (kmswStage w n).LR[j]? = some e) :
    (stageOuterWordVal w n)[(kmswStage w n).UL.length +
      (kmswStage w n).UR.length + ((kmswStage w n).LR.length - 1 - j)]? =
        some (e, true) := by
  let s := kmswStage w n
  have hj : j < s.LR.length := (List.getElem?_eq_some_iff.mp he).1
  rw [stageOuterWordVal_eq_runs]
  have houter : s.UL.length + s.UR.length + (s.LR.length - 1 - j) <
      ((s.UL.map fun e => (e, false)) ++ (s.UR.map fun e => (e, false)) ++
        (s.LR.reverse.map fun e => (e, true))).length := by
    simp only [List.length_append, List.length_map, List.length_reverse]
    omega
  rw [List.getElem?_append_left houter]
  have hleft : ((s.UL.map fun e => (e, false)) ++
      (s.UR.map fun e => (e, false))).length ≤
        s.UL.length + s.UR.length + (s.LR.length - 1 - j) := by
    simp only [List.length_append, List.length_map]
    omega
  rw [List.getElem?_append_right hleft]
  have hsub : s.UL.length + s.UR.length + (s.LR.length - 1 - j) -
      ((s.UL.map fun e => (e, false)) ++ (s.UR.map fun e => (e, false))).length =
        s.LR.length - 1 - j := by
    simp only [List.length_append, List.length_map]
    omega
  have hidx : s.LR.length - 1 - (s.LR.length - 1 - j) = j := by omega
  rw [hsub, List.getElem?_map, List.getElem?_reverse (by omega), hidx, he]
  rfl

/-- Consecutive strict right-record edges are successive darts on the outer
face even when the finite stage still has LL edges. This theorem is unused
by the main theorem `kmswRightBoundaryEdge_is_rightmost`. -/
theorem kmswInfFaceSucc_right_of_unbounded_below (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
      (kmswRightBoundaryEdge w i, true) := by
  obtain ⟨N1, h1⟩ := kmswStage_LR_getElem?_eventually w hR i
  obtain ⟨N2, h2⟩ := kmswStage_LR_getElem?_eventually w hR (i + 1)
  refine kmswInfFaceSucc_eq_of_stages w hfin _ _
    ⟨max N1 N2, fun n hn => ?_⟩
  let s := kmswStage w n
  have e0 := h1 n (le_trans (le_max_left _ _) hn)
  have e1 := h2 n (le_trans (le_max_right _ _) hn)
  have v0 := outerWordVal_getElem?_LR_any w n i _ e0
  have v1 := outerWordVal_getElem?_LR_any w n (i + 1) _ e1
  let q0 := s.UL.length + s.UR.length + (s.LR.length - 1 - i)
  let q1 := s.UL.length + s.UR.length + (s.LR.length - 1 - (i + 1))
  have hi1 : i + 1 < s.LR.length := (List.getElem?_eq_some_iff.mp e1).1
  have hq0 : q0 < (stageOuterWordVal w n).length :=
    (List.getElem?_eq_some_iff.mp v0).1
  have hmod : (q1 + 1) % (stageOuterWordVal w n).length = q0 := by
    have heq : q1 + 1 = q0 := by dsimp only [q0, q1]; omega
    rw [heq]
    exact Nat.mod_eq_of_lt hq0
  have hp := (List.getElem?_eq_some_iff.mp v1).1
  obtain ⟨d, d', hd, hd', hf⟩ := outer_faceSucc_exists w n
    (stageOuterWord_faceSucc w n) q1 hp
  rw [hmod] at hd'
  refine ⟨d, d', ?_, ?_, hf⟩
  · rw [v1] at hd
    exact (Option.some.inj hd).symm
  · rw [v0] at hd'
    exact (Option.some.inj hd').symm

/-- Every positive right-boundary record edge is the last item in the
rotation-order outgoing list at its source. The outer-face successor puts an
incoming dart immediately before it in the rotation (`lem-uibot-bdy`,
carrier `M_{0,∞}`; rightmostness is with respect to the outgoing list inside
`m_{0,∞}`, not inside `m_{−∞,∞}`, and coalescence is not established here. -/
theorem kmswRightBoundaryEdge_is_rightmost
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    {k : ℕ} (hk : 1 ≤ k) :
    kmswRightmostOutgoingEdge w hfin hL htrans hR
      (kmsw_vertex_allocated_of_finite_incidence w hfin)
      (edgeWest w (kmswRightBoundaryEdge w k)) = kmswRightBoundaryEdge w k := by
  let v := edgeWest w (kmswRightBoundaryEdge w k)
  let hv := kmsw_vertex_allocated_of_finite_incidence w hfin v
  let e := kmswRightBoundaryEdge w k
  have hp := rightBoundaryEdge_present w hR k
  have hvne : v ≠ 0 := by
    exact rightBoundaryEdge_source_ne_zero w hL hR hk
  let hEnum := kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hvne
  let r := hEnum.choose
  let es := hEnum.choose_spec.choose_spec.choose
  have hspec := hEnum.choose_spec.choose_spec.choose_spec
  have hhead : es.head? = some r := hspec.2.1
  have hmem : e ∈ es := by
    exact (hspec.2.2.2.1 e).2 ⟨hp, by simp [v, e]⟩
  have hface := kmswInfFaceSucc_right w hfin (stageOuterWord_faceSucc w)
    hL hR (k - 1)
  have hface' : (kmswInfRot w hfin).symm (e, false) =
      (kmswRightBoundaryEdge w (k - 1), true) := by
    simpa [kmswInfFaceSucc, e, Nat.sub_add_cancel hk] using hface
  have hchain : List.IsChain
      (fun a b => kmswInfRot w hfin (a, false) = (b, false)) es :=
    hspec.2.2.2.2.1
  have hfirst : es.head? = some e :=
    outgoingChain_head_of_incoming_predecessor (kmswInfRot w hfin)
      hchain hmem (by rw [hface'])
  have her : r = e := Option.some.inj (hhead.symm.trans hfirst)
  have hneEs : es ≠ [] := by
    intro hnil
    rw [hnil] at hhead
    simp at hhead
  have hrev : es.reverse ≠ [] := by simpa using hneEs
  have hlast : (es.reverse).getLast hrev = e := by
    rw [List.getLast_reverse hrev]
    have hheadE : es.head hneEs = e :=
      (List.head_eq_iff_head?_eq_some hneEs).2 hfirst
    exact hheadE
  have horder : kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv = es.reverse := by
    unfold kmswOutgoingEdgesLeftToRight
    split
    · rename_i hz
      exact (hvne hz).elim
    · rfl
  let outgoing := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv
  have hlastOption : (es.reverse).getLast? = some e := by
    rw [List.getLast?_eq_getLast_of_ne_nil hrev, List.getLast_reverse hrev]
    have hheadE : es.head hneEs = e :=
      (List.head_eq_iff_head?_eq_some hneEs).2 hfirst
    exact congrArg some hheadE
  have hlastOutgoing : outgoing.getLast? = some e := by
    dsimp only [outgoing]
    rw [horder]
    exact hlastOption
  have houtgoingNe : outgoing ≠ [] :=
    kmswOutgoingEdgesLeftToRight_ne_nil w hfin hL htrans hR v hv
  have houtgoingLast := List.getLast?_eq_getLast_of_ne_nil houtgoingNe
  have hlastOutgoing' : some (outgoing.getLast houtgoingNe) = some e := by
    rw [← houtgoingLast]
    exact hlastOutgoing
  unfold kmswRightmostOutgoingEdge
  change outgoing.getLast _ = e
  exact Option.some.inj hlastOutgoing'

/-- At every finite stage, a present dart leaving a positive boundary vertex
is either the boundary dart itself or occurs strictly before it in the
left-to-right outgoing list. The finite-stage present edge is retained as its -/
theorem rightBoundaryEdge_stage_outgoing_precedes
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    {k : ℕ} (hk : 1 ≤ k)
    (n f : ℕ) (hf : f < (kmswStage w n).nextEdge)
    (hpresent : (kmswStage w n).present f = true)
    (hwest : (kmswStage w n).west f = edgeWest w (kmswRightBoundaryEdge w k)) :
    f = kmswRightBoundaryEdge w k ∨
      f ∈ (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (edgeWest w (kmswRightBoundaryEdge w k))
        ((kmsw_vertex_allocated_of_finite_incidence w hfin)
          (edgeWest w (kmswRightBoundaryEdge w k)))).dropLast := by
  let v := edgeWest w (kmswRightBoundaryEdge w k)
  let out := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v
    ((kmsw_vertex_allocated_of_finite_incidence w hfin) v)
  have hright := kmswRightBoundaryEdge_is_rightmost w hfin hL htrans hR hk
  have hlast : out.getLast
      (kmswOutgoingEdgesLeftToRight_ne_nil w hfin hL htrans hR v
        ((kmsw_vertex_allocated_of_finite_incidence w hfin) v)) =
      kmswRightBoundaryEdge w k := by
    simpa [out, v, kmswRightmostOutgoingEdge] using hright
  have hpresentEdge : EdgePresent w f := ⟨n, hf, hpresent⟩
  have hwestEdge : edgeWest w f = v := by
    have hend := edge_endpoints_eq w hf
    exact hend.1.symm.trans (by simpa [v] using hwest)
  have hmem : f ∈ out := by
    exact (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v
      ((kmsw_vertex_allocated_of_finite_incidence w hfin) v) f).2
        ⟨hpresentEdge, hwestEdge⟩
  by_cases hfe : f = kmswRightBoundaryEdge w k
  · exact Or.inl hfe
  · apply Or.inr
    apply List.mem_dropLast_of_mem_of_ne_getLast hmem
    intro heq
    apply hfe
    calc
      f = out.getLast (List.ne_nil_of_mem hmem) := heq
      _ = kmswRightBoundaryEdge w k := by simpa using hlast

/-- Iterating the rotation-order rightmost choice from the source of `r₁`
follows the lower-right record chain (`lem-uibot-bdy`,
one-sided carrier `M_{0,∞}`, i.e. inside `m_{0,∞}` and not `m_{−∞,∞}`;
coalescence is not established here. -/
theorem kmswRightmostOrbit_from_rightBoundaryEdge_one
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (j : ℕ) :
    kmswRightmostOrbit w hfin hL htrans hR
      (edgeWest w (kmswRightBoundaryEdge w 1)) j =
      edgeWest w (kmswRightBoundaryEdge w (j + 1)) := by
  induction j with
  | zero => simp [kmswRightmostOrbit]
  | succ j ih =>
    change kmswRightmostNext w hfin hL htrans hR
        (kmswRightmostOrbit w hfin hL htrans hR
          (edgeWest w (kmswRightBoundaryEdge w 1)) j) = _
    rw [ih]
    change edgeEast w (kmswRightmostOutgoingEdge w hfin hL htrans hR
      (kmsw_vertex_allocated_of_finite_incidence w hfin)
      (edgeWest w (kmswRightBoundaryEdge w (j + 1)))) = _
    rw [kmswRightBoundaryEdge_is_rightmost w hfin hL htrans hR
      (k := j + 1) (by omega)]
    exact (kmswRightBoundary_infinite_path w hL hR).2.1 (j + 1)

/-- The `j`th vertex of the rotation-order rightmost path from the source of
`r₁` is the source of `r_{1+j}` (`lem-uibot-bdy`,
one-sided carrier `M_{0,∞}`, i.e. inside `m_{0,∞}` and not `m_{−∞,∞}`;
coalescence is not established here. -/
theorem kmswRightmostPath_from_rightBoundaryEdge_one
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (j : ℕ) :
    ((kmswRightmostPath w hfin hL htrans hR
      (edgeWest w (kmswRightBoundaryEdge w 1))).initial j).1.id =
      edgeWest w (kmswRightBoundaryEdge w (j + 1)) := by
  simpa [kmswRightmostPath] using
    kmswRightmostOrbit_from_rightBoundaryEdge_one w hfin hL htrans hR j

/-- The edge created at the first hit of `R = -k` is the `k`th right-boundary -/
theorem boundaryHitTime_right_edge_eq_rightBoundaryEdge
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) {k : ℕ} (hk : 1 ≤ k) :
    act w (boundaryHitTime w h (k : ℤ)) = kmswRightBoundaryEdge w k := by
  have htime := rightHitTime_is_record_index w h hk
  unfold kmswRightBoundaryEdge
  rw [htime]

/-- Almost surely, the raw shifted iid code has an existential hit witness
whose positive hit edges are exactly the strict right-record edges. The
witness is chosen once for the whole chain (`eqn-bdy-vertex-hit`, -/
theorem iidCodes_ae_boundaryRightEdge_records :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ k : ℕ, 1 ≤ k →
          EdgePresent (fun i => ω (i + 1))
            (kmswRightBoundaryEdge (fun i => ω (i + 1)) k) ∧
          edgeWest (fun i => ω (i + 1))
            (kmswRightBoundaryEdge (fun i => ω (i + 1)) k) =
              boundaryVertex (fun i => ω (i + 1)) h (k : ℤ) ∧
          edgeEast (fun i => ω (i + 1))
            (kmswRightBoundaryEdge (fun i => ω (i + 1)) k) =
              boundaryVertex (fun i => ω (i + 1)) h (k + 1 : ℤ) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, fun k hk =>
    boundaryVertex_right_edge_present_source (fun i => ω (i + 1)) h hk⟩

end DirectedDistances.KMSW
