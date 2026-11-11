module

public import DirectedDistances.KMSW.PastLeftmostEqGeodesicPrefix

/-! # Past-stage selected edges before the first cut visit

The step comparison below uses the actual chosen infinite leftmost path. It
identifies the head of the eligible stage order with the next edge, for every
source or incoming-block corner at the current vertex. The first visit index
exists and the comparison holds at every strictly earlier index.

The dart-valued stage iteration has exactly the infinite path's prefix edge
IDs at every index up to the cut, and stops there. Packaging this trace as a
`SimpleDirectedDartPath` and identifying it with the existing finite walk-class
`canonicalLeftmostXDPStep` construction remain separate obligations. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result.

The option-valued stage selector chooses a source or incoming-block corner at
vertex `v` and takes the first eligible edge in its rotation order. It is `none`
when there is no such corner or no eligible edge. -/
@[expose] noncomputable def pastStageLeftmostXDPStep
    (w : ℕ → Fin 3) (t : ℕ) (x : XDP) (v : ℕ) : Option ℕ := by
  classical
  exact if hc : ∃ corner : StageDart (kmswStage w (t - 1)).nextEdge,
      (corner = stageULHeadDart w (t - 1) ∨
        corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true) ∧
      stageEndpoint (kmswStage w (t - 1)) corner = v then
    (stageEligibleOutgoingEdgeOrder w (t - 1) x
      ⟨0⟩ ⟨(recordVertex w t).id⟩ hc.choose).head?
  else none

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
@[expose] noncomputable def pastStageLeftmostXDPTrace
    (w : ℕ → Fin 3) (t : ℕ) (x : XDP) :
    ℕ → Option (ℕ × List (StageDart (kmswStage w (t - 1)).nextEdge))
  | 0 => some (0, [])
  | k + 1 => (pastStageLeftmostXDPTrace w t x k).bind fun z =>
      (pastStageLeftmostXDPStep w t x z.1).bind fun e =>
        if he : e < (kmswStage w (t - 1)).nextEdge then
          some ((kmswStage w (t - 1)).east e, z.2 ++ [(⟨e, he⟩, false)])
        else none

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem pastStageLeftmostXDPStep_sink (w : ℕ → Fin 3) (t : ℕ) (x : XDP) :
    pastStageLeftmostXDPStep w t x (recordVertex w t).id = none := by
  classical
  unfold pastStageLeftmostXDPStep
  split
  next hc =>
    have he : stageEligibleOutgoingEdgeOrder w (t - 1) x
        ⟨0⟩ ⟨(recordVertex w t).id⟩ hc.choose = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      obtain ⟨hout, hgeo⟩ := List.mem_filter.mp he
      have ho := (mem_stageOutgoingEdgeOrder w (t - 1) hc.choose e).1 hout
      obtain ⟨a, b, f, hf, p, q, _⟩ := of_decide_eq_true hgeo
      have ha : a = (⟨(recordVertex w t).id⟩ : StagePresentVertex w (t - 1)) := by
        apply congrArg (StagePresentVertex.mk (w := w) (n := t - 1))
        exact f.property.2.2.1.symm.trans
          ((congrArg (kmswStage w (t - 1)).west hf).trans
            (ho.2.2.trans hc.choose_spec.2))
      subst a
      let loop := f.toPath.comp q
      have hlen := presentVertex_acyclic w _ ((stageToLimit w (t - 1)).mapPath loop)
      rw [stageToLimit_length, Path.length_comp, Path.length_toPath] at hlen
      omega
    rw [he]
    rfl
  next => rfl

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_initial_edge_stage {w : ℕ → Fin 3} {t : ℕ}
    (P : InfinitePresentPath w ⟨0⟩) {i : ℕ}
    (hi : (P.initial i).1 = recordVertex w t) {k : ℕ} (hk : k < i) :
    P.edge k < (kmswStage w (t - 1)).nextEdge ∧
      (kmswStage w (t - 1)).present (P.edge k) = true := by
  have hedges := P.prefix_edges i
  generalize hq : P.initial i = q at hi hedges
  rcases q with ⟨v, p⟩
  dsimp only at hi hedges
  subst v
  have hm : P.edge k ∈ pathEdgeList p := by
    rw [hedges]
    exact List.mem_ofFn.mpr ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨j, hj, he⟩ := (presentPath_to_record_edges_before p).2 (P.edge k) hm
  have hjt : j ≤ t - 1 := by omega
  have hp : (kmswStage w j).present (act w j) = true := by
    apply (kmswStage_status w j).2.1
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w j
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  rw [he]
  exact ⟨act_lt_nextEdge w hjt,
    (present_mono w (act_lt_nextEdge w (Nat.le_refl j)) hp (t - 1) hjt).2⟩
/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_LR_head (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih
/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_source_corner (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j) (n : ℕ) :
    stageEndpoint (kmswStage w n) (stageULHeadDart w n) = 0 := by
  have hs := (kmswStage_boundary_chain_invariant w n).2.2.1
  have hUL := (kmswStage_UL_nonempty_active_last w n).1
  rw [kmswStage_LL_eq_nil w hL n, List.nil_append] at hs
  have hu := List.head?_eq_some_head hUL
  simp only [boundaryStart, List.head?_append_of_ne_nil _ hUL, hu,
    past_LR_head, Option.map_some] at hs
  exact (Option.some.inj hs).trans (initial_edge_endpoints w n).1
/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_transition_corner (w : ℕ → Fin 3) (n : ℕ)
    (a b : StageDart (kmswStage w n).nextEdge)
    (ha : a.2 = false) (hb : b.2 = true)
    (hab : stageEndpoint (kmswStage w n) a = stageEndpoint (kmswStage w n) b) :
    ∃ d : StageDart (kmswStage w n).nextEdge,
      d.2 = false ∧ (stageRot w n d).2 = true ∧
        stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) a := by
  obtain ⟨m, hm⟩ := ((stageRot_sameCycle_iff_endpoint_eq w n a b).2 hab).exists_nat_pow_eq
  have hex : ∃ m : ℕ, (((stageRot w n) ^ m) a).2 = true := ⟨m, hm ▸ hb⟩
  let j := Nat.find hex
  have hj : (((stageRot w n) ^ j) a).2 = true := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    simp only [hj0, pow_zero, Equiv.Perm.one_apply, ha] at hj
    contradiction
  let d := ((stageRot w n) ^ (j - 1)) a
  have hd : d.2 = false := by
    have hne := Nat.find_min hex (show j - 1 < j by omega)
    cases h : d.2
    · rfl
    · exact (hne h).elim
  refine ⟨d, hd, ?_, ?_⟩
  · have hjs : j = (j - 1) + 1 := by omega
    rw [hjs, pow_succ', Equiv.Perm.mul_apply] at hj
    exact hj
  · apply (stageRot_sameCycle_iff_endpoint_eq w n d a).1
    exact Equiv.Perm.SameCycle.rfl.pow_left
/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_prefix_corner_exists (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j)
    (t : ℕ) (P : InfinitePresentPath w ⟨0⟩) {i : ℕ}
    (hi : (P.initial i).1 = recordVertex w t) {k : ℕ} (hk : k < i) :
    ∃ corner : StageDart (kmswStage w (t - 1)).nextEdge,
      (corner = stageULHeadDart w (t - 1) ∨
        corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true) ∧
      stageEndpoint (kmswStage w (t - 1)) corner = (P.initial k).1.id := by
  cases k with
  | zero =>
    refine ⟨stageULHeadDart w (t - 1), Or.inl rfl, ?_⟩
    have hv := (P.initial 0).2.eq_of_length_zero (P.prefix_length 0)
    rw [← hv]
    exact past_source_corner w hL (t - 1)
  | succ k =>
    have ha := past_initial_edge_stage P hi hk
    have hb := past_initial_edge_stage P hi (show k < i by omega)
    let a : StageDart (kmswStage w (t - 1)).nextEdge := (⟨P.edge (k + 1), ha.1⟩, false)
    let b : StageDart (kmswStage w (t - 1)).nextEdge := (⟨P.edge k, hb.1⟩, true)
    have hav : stageEndpoint (kmswStage w (t - 1)) a = (P.initial (k + 1)).1.id :=
      (edge_endpoints_eq w ha.1).1.trans (P.edge_outgoing_at_initial w (k + 1)).2
    have hbval : stageEndpoint (kmswStage w (t - 1)) b = (P.initial (k + 1)).1.id :=
      (edge_endpoints_eq w hb.1).2.trans (P.edge_incoming_at_succ w k).2
    obtain ⟨d, hd, hrot, hv⟩ := past_transition_corner w (t - 1) a b rfl rfl
      (hav.trans hbval.symm)
    exact ⟨d, Or.inr ⟨hd, hrot⟩, hv.trans hav⟩


/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem past_trace_prefix (w : ℕ → Fin 3) (t : ℕ) (x : XDP)
    (P : InfinitePresentPath w ⟨0⟩) {i : ℕ}
    (hi : (P.initial i).1 = recordVertex w t) :
    ∀ j ≤ i,
      (∀ k < j, pastStageLeftmostXDPStep w t x (P.initial k).1.id = some (P.edge k)) →
      ∃ ds : List (StageDart (kmswStage w (t - 1)).nextEdge),
        pastStageLeftmostXDPTrace w t x j = some ((P.initial j).1.id, ds) ∧
          ds.map (fun d => d.1.val) = pathEdgeList (P.initial j).2 := by
  intro j
  induction j with
  | zero =>
    intro _ _
    have hv := (P.initial 0).2.eq_of_length_zero (P.prefix_length 0)
    have he := P.prefix_edges 0
    refine ⟨[], ?_, he.symm⟩
    apply congrArg Option.some
    exact Prod.ext (congrArg PresentVertex.id hv) rfl
  | succ j ih =>
    intro hj hstep
    obtain ⟨ds, hds, hids⟩ := ih (by omega) (fun k hk => hstep k (by omega))
    have he := past_initial_edge_stage P hi (show j < i by omega)
    refine ⟨ds ++ [(⟨P.edge j, he.1⟩, false)], ?_, ?_⟩
    · rw [pastStageLeftmostXDPTrace, hds]
      simp only [Option.bind_some, hstep j (by omega), dite_eq_left he.1]
      apply congrArg Option.some
      apply Prod.ext
      · exact (edge_endpoints_eq w he.1).2.trans (P.edge_incoming_at_succ w j).2
      · rfl
    · simp only [List.map_append, List.map_cons, List.map_nil]
      rw [hids, P.prefix_edges, P.prefix_edges, List.ofFn_succ']
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

variable (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hcut : mapCutVertex w hfin (recordVertex w t).id)

include hcut

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. This helper proves the selected-edge comparison at each
pre-cut index and each source or incoming-block corner there. -/
private theorem past_ldp_firstVisit_stage_steps
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ k < i, ∀ corner : StageDart (kmswStage w (t - 1)).nextEdge,
        (corner = stageULHeadDart w (t - 1) ∨
          corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true) →
        stageEndpoint (kmswStage w (t - 1)) corner = (P.initial k).1.id →
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ j ≤ k, stageEndpoint (kmswStage w (t - 1)) d = (P.initial j).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        (stageEligibleOutgoingEdgeOrder w (t - 1) .ldp
          ⟨0⟩ ⟨(recordVertex w t).id⟩ corner).head? = some (P.edge k) := by
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  have hP := kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isLongest
    w hfin htrans hR hL hcut hP
  refine ⟨i, hi, hfirst, ?_⟩
  intro k hki corner hkind hcorner hord
  have hbefore : ∀ j ≤ k, (P.initial j).1 ≠ recordVertex w t := by
    intro j hj
    exact hfirst j (lt_of_le_of_lt hj hki)
  have hhead := past_ldp_first_eligible_eq_extension w hfin hL htrans hR t hcut
    P hP k hbefore corner hkind hcorner hord
  have hselected := kmswLeftmostLdpEdge_selected w hfin hL htrans hR 0 hg k
  rw [kmswLeftmostLdpPrefixes_eq_ofFn] at hselected
  exact hhead.trans hselected

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. This helper proves the selected-edge comparison at each
pre-cut index and each source or incoming-block corner there. -/
private theorem past_sdp_firstVisit_stage_steps
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ k < i, ∀ corner : StageDart (kmswStage w (t - 1)).nextEdge,
        (corner = stageULHeadDart w (t - 1) ∨
          corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true) →
        stageEndpoint (kmswStage w (t - 1)) corner = (P.initial k).1.id →
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ j ≤ k, stageEndpoint (kmswStage w (t - 1)) d = (P.initial j).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        (stageEligibleOutgoingEdgeOrder w (t - 1) .sdp
          ⟨0⟩ ⟨(recordVertex w t).id⟩ corner).head? = some (P.edge k) := by
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  have hP := kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isShortest
    w hfin htrans hR hL hcut hP
  refine ⟨i, hi, hfirst, ?_⟩
  intro k hki corner hkind hcorner hord
  have hbefore : ∀ j ≤ k, (P.initial j).1 ≠ recordVertex w t := by
    intro j hj
    exact hfirst j (lt_of_le_of_lt hj hki)
  have hhead := past_sdp_first_eligible_eq_extension w hfin hL htrans hR t hcut
    P hP k hbefore corner hkind hcorner hord
  have hselected := kmswLeftmostSdpEdge_selected w hfin hL htrans hR 0 hg k
  rw [kmswLeftmostSdpPrefixes_eq_ofFn] at hselected
  exact hhead.trans hselected

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. This is the index-wise stage-selector conclusion. -/
theorem past_ldp_firstVisit_step_eq_edge
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ k < i,
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ j ≤ k, stageEndpoint (kmswStage w (t - 1)) d = (P.initial j).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        pastStageLeftmostXDPStep w t .ldp (P.initial k).1.id = some (P.edge k) := by
  classical
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, hstep⟩ := past_ldp_firstVisit_stage_steps
    w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro k hk hord
  have hc := past_prefix_corner_exists w hL t P hi hk
  unfold pastStageLeftmostXDPStep
  rw [dite_eq_left hc]
  exact hstep k hk hc.choose hc.choose_spec.1 hc.choose_spec.2 hord

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. This is the index-wise stage-selector conclusion. -/
theorem past_sdp_firstVisit_step_eq_edge
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ k < i,
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ j ≤ k, stageEndpoint (kmswStage w (t - 1)) d = (P.initial j).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        pastStageLeftmostXDPStep w t .sdp (P.initial k).1.id = some (P.edge k) := by
  classical
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, hstep⟩ := past_sdp_firstVisit_stage_steps
    w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro k hk hord
  have hc := past_prefix_corner_exists w hL t P hi hk
  unfold pastStageLeftmostXDPStep
  rw [dite_eq_left hc]
  exact hstep k hk hc.choose hc.choose_spec.1 hc.choose_spec.2 hord

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem past_ldp_firstVisit_trace_eq_prefix
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ j ≤ i,
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        ∃ ds : List (StageDart (kmswStage w (t - 1)).nextEdge),
          pastStageLeftmostXDPTrace w t .ldp j = some ((P.initial j).1.id, ds) ∧
            ds.map (fun d => d.1.val) = pathEdgeList (P.initial j).2 ∧
            (j = i → pastStageLeftmostXDPTrace w t .ldp (j + 1) = none) := by
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, hstep⟩ := past_ldp_firstVisit_step_eq_edge
    w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro j hj hord
  have hsteps : ∀ k < j,
      pastStageLeftmostXDPStep w t .ldp (P.initial k).1.id = some (P.edge k) := by
    intro k hk
    apply hstep k (lt_of_lt_of_le hk hj)
    intro d hd hseen
    obtain ⟨a, ha, hv⟩ := hseen
    exact hord d hd ⟨a, ha.trans (Nat.le_of_lt hk), hv⟩
  obtain ⟨ds, htrace, hids⟩ := past_trace_prefix w t .ldp P hi j hj hsteps
  refine ⟨ds, htrace, hids, ?_⟩
  intro hji
  subst j
  have hsink : pastStageLeftmostXDPStep w t .ldp (P.initial i).1.id = none := by
    rw [hi, pastStageLeftmostXDPStep_sink]
  simp only [pastStageLeftmostXDPTrace, htrace, Option.bind_some, hsink, Option.bind_none]

/-- the finite canonical leftmost XDP geodesic of the past stage map equals the prefix
of the infinite leftmost geodesic up to the cut record vertex, under the explicit
stage/infinite rotation-order agreement hord; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem past_sdp_firstVisit_trace_eq_prefix
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ j ≤ i,
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (d = stageULHeadDart w (t - 1) ∨
            d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
          (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
          stageOutgoingEdgeOrder w (t - 1) d =
            (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
              (stageEndpoint (kmswStage w (t - 1)) d)
              ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
                (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
                  (kmswStage w (t - 1)).present e = true))) →
        ∃ ds : List (StageDart (kmswStage w (t - 1)).nextEdge),
          pastStageLeftmostXDPTrace w t .sdp j = some ((P.initial j).1.id, ds) ∧
            ds.map (fun d => d.1.val) = pathEdgeList (P.initial j).2 ∧
            (j = i → pastStageLeftmostXDPTrace w t .sdp (j + 1) = none) := by
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, hstep⟩ := past_sdp_firstVisit_step_eq_edge
    w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro j hj hord
  have hsteps : ∀ k < j,
      pastStageLeftmostXDPStep w t .sdp (P.initial k).1.id = some (P.edge k) := by
    intro k hk
    apply hstep k (lt_of_lt_of_le hk hj)
    intro d hd hseen
    obtain ⟨a, ha, hv⟩ := hseen
    exact hord d hd ⟨a, ha.trans (Nat.le_of_lt hk), hv⟩
  obtain ⟨ds, htrace, hids⟩ := past_trace_prefix w t .sdp P hi j hj hsteps
  refine ⟨ds, htrace, hids, ?_⟩
  intro hji
  subst j
  have hsink : pastStageLeftmostXDPStep w t .sdp (P.initial i).1.id = none := by
    rw [hi, pastStageLeftmostXDPStep_sink]
  simp only [pastStageLeftmostXDPTrace, htrace, Option.bind_some, hsink, Option.bind_none]

end DirectedDistances.KMSW
