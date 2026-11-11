module

public import DirectedDistances.KMSW.StageInfiniteOutgoingOrder
public import DirectedDistances.KMSW.LeftmostGeodesicCutPrefix
public import DirectedDistances.KMSW.XDPStageIdentificationAtCuts

/-! Helpers for the finite prefix identification in `lem-finite-ind`, line 317.
We use stage `t - 1`. The strict bound in `presentPath_to_record_edges_before`
places every traversed `act w k`, `k < t`, in this stage. The lift below sharpens
`presentPath_to_record_lifts`, which uses stage `t`, to the past stage `t - 1`.

* `past_ldp_prefix_eligible_iff_stage` / `past_sdp_prefix_eligible_iff_stage` concern an
  arbitrary infinite path `P` with longest (resp. shortest) segments, not necessarily
  leftmost, and take no rotation-order hypothesis.
* `past_ldp_first_eligible_eq_extension` / `past_sdp_first_eligible_eq_extension` compare
  with the leftmost extensions `kmswLeftmostLdpExtension` / `kmswLeftmostSdpExtension`
  and take the explicit rotation-order hypothesis `hord` (proved separately as
  `stageOutgoingEdgeOrder_hord` in `KMSW/StageInfiniteOutgoingOrderSource.lean`).

T_m, F4c and both-mode scope are not treated; this is not the paper result. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private def pastOptimal {V : Type} [Quiver V] (x : XDP) {a b : V}
    (p : Path a b) : Prop :=
  match x with
  | .ldp => IsLongest p
  | .sdp => IsShortest p

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private def pastPathIds {V : Type} [Quiver V]
    (ids : ∀ {a b : V}, (a ⟶ b) → ℕ) {a : V} : ∀ {b : V}, Path a b → List ℕ
  | _, .nil => []
  | _, .cons p e => pastPathIds ids p ++ [ids e]

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem pastPathIds_comp {V : Type} [Quiver V]
    (ids : ∀ {a b : V}, (a ⟶ b) → ℕ) {a b c : V}
    (p : Path a b) (q : Path b c) :
    pastPathIds ids (p.comp q) = pastPathIds ids p ++ pastPathIds ids q := by
  induction q with
  | nil => simp only [Path.comp_nil, pastPathIds, List.append_nil]
  | cons q e ih => simp only [Path.comp_cons, pastPathIds, ih, List.append_assoc]

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem pastPathIds_split {V : Type} [Quiver V]
    (ids : ∀ {a b : V}, (a ⟶ b) → ℕ) {a b : V} (r : Path a b) {e : ℕ}
    (he : e ∈ pastPathIds ids r) :
    ∃ (u z : V) (f : u ⟶ z) (p : Path a u) (q : Path z b),
      ids f = e ∧ r = (p.cons f).comp q := by
  induction r with
  | nil => simp only [pastPathIds, List.not_mem_nil] at he
  | @cons u z r f ih =>
    rcases List.mem_append.mp he with he | he
    · obtain ⟨c, d, g, p, q, hg, hr⟩ := ih he
      exact ⟨c, d, g, p, q.cons f, hg, by rw [Path.comp_cons, ← hr]⟩
    · have hf : ids f = e := (List.mem_singleton.mp he).symm
      exact ⟨u, z, f, r, .nil, hf, rfl⟩

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private def pastLimitId {w : ℕ → Fin 3} {a b : PresentVertex w}
    (e : a ⟶ b) : ℕ := e.val

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private def pastStageId {w : ℕ → Fin 3} {t : ℕ} {a b : StagePresentVertex w t}
    (e : a ⟶ b) : ℕ := e.val

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem pastPathIds_limit {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) : pastPathIds (@pastLimitId w) p = pathEdgeList p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [pastPathIds, pathEdgeList, pastLimitId, ih]

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem pastPathIds_stage {w : ℕ → Fin 3} {t : ℕ}
    {a b : StagePresentVertex w t} (p : Path a b) :
    pastPathIds (@pastStageId w t) p =
      pathEdgeList ((stageToLimit w t).mapPath p) := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [pastPathIds, Prefunctor.mapPath_cons, pathEdgeList, ← ih]; rfl

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem pastPath_lift {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, ∃ k < t, e = act w k) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨b.id⟩,
      (stageToLimit w (t - 1)).mapPath q = p := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons a b p e ih =>
    obtain ⟨q, hq⟩ := ih (fun f hf => hp f (List.mem_append_left _ hf))
    obtain ⟨k, hk, he⟩ := hp e.val
      (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have hkt : k ≤ t - 1 := by omega
    have hactive : (kmswStage w k).present (act w k) = true := by
      apply (kmswStage_status w k).2.1
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w k
      rw [hxs]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have halloc : e.val < (kmswStage w (t - 1)).nextEdge := by
      rw [he]
      exact act_lt_nextEdge w hkt
    have hpres : (kmswStage w (t - 1)).present e.val = true := by
      rw [he]
      exact (present_mono w (act_lt_nextEdge w (Nat.le_refl k)) hactive (t - 1) hkt).2
    let f : (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟶ ⟨b.id⟩ :=
      ⟨e.val, halloc, hpres,
        (edge_endpoints_eq w halloc).1.trans e.property.2.1,
        (edge_endpoints_eq w halloc).2.trans e.property.2.2⟩
    refine ⟨q.cons f, ?_⟩
    rw [Prefunctor.mapPath_cons, hq]
    have hf : (stageToLimit w (t - 1)).map f = e := Subtype.ext rfl
    exact congrArg (Path.cons p) hf

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem past_to_record_lifts {w : ℕ → Fin 3} {t : ℕ}
    {a : PresentVertex w} (p : Path a (recordVertex w t)) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨(recordVertex w t).id⟩,
      (stageToLimit w (t - 1)).mapPath q = p :=
  pastPath_lift p (presentPath_to_record_edges_before p).2

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem pastOptimal_map_record_iff (w : ℕ → Fin 3) (t : ℕ) (x : XDP)
    {a : StagePresentVertex w (t - 1)}
    (p : Path a (⟨(recordVertex w t).id⟩ : StagePresentVertex w (t - 1))) :
    pastOptimal x p ↔ pastOptimal x ((stageToLimit w (t - 1)).mapPath p) := by
  have hlen := stageToLimit_length w (t - 1) p
  cases x with
  | ldp =>
    constructor
    · intro hp r
      obtain ⟨q, hq⟩ := past_to_record_lifts r
      have hlq := stageToLimit_length w (t - 1) q
      rw [hq] at hlq
      exact hlq.le.trans ((hp q).trans_eq hlen.symm)
    · intro hp q
      have h := hp ((stageToLimit w (t - 1)).mapPath q)
      rwa [stageToLimit_length, stageToLimit_length] at h
  | sdp =>
    constructor
    · intro hp r
      obtain ⟨q, hq⟩ := past_to_record_lifts r
      have hlq := stageToLimit_length w (t - 1) q
      rw [hq] at hlq
      exact hlen.le.trans ((hp q).trans_eq hlq.symm)
    · intro hp q
      have h := hp ((stageToLimit w (t - 1)).mapPath q)
      rwa [stageToLimit_length, stageToLimit_length] at h

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/
private theorem past_stage_eligible_iff (w : ℕ → Fin 3) (t : ℕ) (x : XDP) (e : ℕ) :
    StageCodeXDPEligible w (t - 1) x ⟨0⟩ ⟨(recordVertex w t).id⟩ e ↔
      ∃ q : Path (⟨0⟩ : PresentVertex w) (recordVertex w t),
        pastOptimal x q ∧ e ∈ pathEdgeList q := by
  constructor
  · rintro ⟨a, b, f, hf, p, q, h⟩
    let r := (p.cons f).comp q
    refine ⟨(stageToLimit w (t - 1)).mapPath r,
      (pastOptimal_map_record_iff w t x r).1 h, ?_⟩
    have hr : pastPathIds (@pastStageId w (t - 1)) r =
        (pastPathIds (@pastStageId w (t - 1)) p ++ [f.val]) ++
          pastPathIds (@pastStageId w (t - 1)) q := by
      exact pastPathIds_comp (@pastStageId w (t - 1)) (p.cons f) q
    have hem : e ∈ pastPathIds (@pastStageId w (t - 1)) r := by
      rw [hr, hf]
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact (pastPathIds_stage r) ▸ hem
  · rintro ⟨q, hq, he⟩
    obtain ⟨r, hr⟩ := past_to_record_lifts q
    have he' : e ∈ pastPathIds (@pastStageId w (t - 1)) r := by
      rw [pastPathIds_stage, hr]
      exact he
    obtain ⟨a, b, f, p, s, hf, hs⟩ := pastPathIds_split (@pastStageId w (t - 1)) r he'
    refine ⟨a, b, f, hf, p, s, ?_⟩
    have h := (pastOptimal_map_record_iff w t x r).2 (by rwa [hr])
    rwa [hs] at h

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private def pastSegments {w : ℕ → Fin 3} (x : XDP)
    (P : InfinitePresentPath w ⟨0⟩) : Prop :=
  match x with
  | .ldp => P.HasLongestSegments
  | .sdp => P.HasShortestSegments

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private def pastStarts (w : ℕ → Fin 3) (x : XDP) (es : List ℕ) : Prop :=
  ∃ P : InfinitePresentPath w ⟨0⟩, pastSegments x P ∧
    List.ofFn (fun i : Fin es.length => P.edge i.val) = es

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem pastStarts_append_left {w : ℕ → Fin 3} {x : XDP}
    {es fs : List ℕ} (h : pastStarts w x (es ++ fs)) : pastStarts w x es := by
  obtain ⟨P, hP, he⟩ := h
  simp only [List.length_append, List.ofFn_add] at he
  exact ⟨P, hP, List.append_inj_left he (by simp only [List.length_ofFn])⟩

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem pastOptimal_replace_prefix {w : ℕ → Fin 3} (x : XDP)
    {a b c : PresentVertex w} (p p' : Path (⟨0⟩ : PresentVertex w) a)
    (e : a ⟶ b) (q : Path b c) (h : pastOptimal x ((p.cons e).comp q))
    (hp' : pastOptimal x p') : pastOptimal x ((p'.cons e).comp q) := by
  cases x with
  | ldp =>
    have hp : IsLongest p := by
      intro r
      have hr := h ((r.cons e).comp q)
      simp only [Path.length_comp, Path.length_cons] at hr
      omega
    have hl : p'.length = p.length := Nat.le_antisymm (hp p') (hp' p)
    exact IsLongest.of_length_eq h (by simp only [Path.length_comp, Path.length_cons, hl])
  | sdp =>
    have hp : IsShortest p := by
      intro r
      have hr := h ((r.cons e).comp q)
      simp only [Path.length_comp, Path.length_cons] at hr
      omega
    have hl : p'.length = p.length := Nat.le_antisymm (hp' p) (hp p')
    exact IsShortest.of_length_eq h (by simp only [Path.length_comp, Path.length_cons, hl])

variable (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hcut : mapCutVertex w hfin (recordVertex w t).id)

include hfin hL htrans hR hcut

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem past_firstVisit (x : XDP) (P : InfinitePresentPath w ⟨0⟩)
    (hP : pastSegments x P) :
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      pastOptimal x (P.initial i).2 := by
  cases x with
  | ldp =>
    obtain ⟨i, hi, _, hgeo, _⟩ :=
      P.firstVisit_mapCutVertex_prefix_isLongest w hfin htrans hR hL hcut hP
    exact ⟨i, hi, hgeo⟩
  | sdp =>
    obtain ⟨i, hi, _, hgeo, _⟩ :=
      P.firstVisit_mapCutVertex_prefix_isShortest w hfin htrans hR hL hcut hP
    exact ⟨i, hi, hgeo⟩

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem past_splice_starts (x : XDP) (P : InfinitePresentPath w ⟨0⟩)
    (hP : pastSegments x P)
    (q : Path (⟨0⟩ : PresentVertex w) (recordVertex w t)) (hq : pastOptimal x q) :
    pastStarts w x (pathEdgeList q) := by
  have hex : ∃ S : InfinitePresentPath w ⟨0⟩, pastSegments x S ∧
      ∀ n, S.edge n = if hn : n < q.length then
        (pathEdgeList q).get ⟨n, by rw [pathEdgeList_length]; exact hn⟩ else P.edge n := by
    cases x with
    | ldp =>
      obtain ⟨_, _, _, _, S, hS, he⟩ :=
        P.exists_firstVisit_mapCutVertex_splice w hfin htrans hR hL hcut hP q hq
      exact ⟨S, hS, he⟩
    | sdp =>
      obtain ⟨_, _, _, _, S, hS, he⟩ :=
        P.exists_firstVisit_mapCutVertex_sdp_splice w hfin htrans hR hL hcut hP q hq
      exact ⟨S, hS, he⟩
  obtain ⟨S, hS, he⟩ := hex
  refine ⟨S, hS, ?_⟩
  apply List.ext_get
  · simp only [List.length_ofFn]
  · intro n hn hq
    have hn' : n < q.length := by simpa only [pathEdgeList_length] using hq
    simp only [List.get_eq_getElem, List.getElem_ofFn, he n, dite_eq_left hn']

/-- comparing the past stage `t - 1` with prefixes of an infinite path; it takes no
rotation-order hypothesis unless its statement shows `hord`; T_m, F4c and both-mode scope are not
treated; not the paper result. -/

private theorem past_prefix_eligible_iff_stage (x : XDP)
    (P : InfinitePresentPath w ⟨0⟩) (hP : pastSegments x P) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t) (e : ℕ)
    (hout : EdgePresent w e ∧ edgeWest w e = (P.initial j).1.id) :
    pastStarts w x ((List.ofFn (fun k : Fin j => P.edge k.val)) ++ [e]) ↔
      StageCodeXDPEligible w (t - 1) x ⟨0⟩ ⟨(recordVertex w t).id⟩ e := by
  rw [past_stage_eligible_iff]
  constructor
  · rintro ⟨Q, hQ, he⟩
    have hs : List.ofFn (fun k : Fin j => Q.edge k.val) ++ [Q.edge j] =
        List.ofFn (fun k : Fin j => P.edge k.val) ++ [e] := by
      simpa only [List.length_append, List.length_ofFn, List.length_singleton,
        List.ofFn_succ', List.concat_eq_append, Fin.val_cast,
        Fin.val_castSucc, Fin.val_last] using he
    have hpre := List.append_inj_left' hs rfl
    have hqe := List.singleton_inj.mp (List.append_inj_right' hs rfl)
    have hcommon : ∀ k < j, Q.edge k = P.edge k := by
      intro k hk
      exact congrFun (List.ofFn_injective hpre) ⟨k, hk⟩
    obtain ⟨i, hi, hgeo⟩ := past_firstVisit w hfin hL htrans hR t hcut x Q hQ
    have hji : j < i := by
      by_contra hn
      have hij : i ≤ j := by omega
      have hpq : List.ofFn (fun k : Fin i => P.edge k.val) =
          List.ofFn (fun k : Fin i => Q.edge k.val) := by
        apply congrArg List.ofFn
        funext k
        exact (hcommon k.val (lt_of_lt_of_le k.isLt hij)).symm
      exact hbefore i hij ((P.initial_vertex_eq_of_prefix_eq Q i hpq).trans hi)
    have hm : e ∈ pathEdgeList (Q.initial i).2 := by
      rw [Q.prefix_edges]
      exact List.mem_ofFn.mpr ⟨⟨j, hji⟩, hqe⟩
    generalize hqi : Q.initial i = qi at hi hgeo hm
    obtain ⟨z, r⟩ := qi
    dsimp only at hi hgeo hm
    subst z
    exact ⟨r, hgeo, hm⟩
  · rintro ⟨q, hq, he⟩
    have he' : e ∈ pastPathIds (@pastLimitId w) q := by
      rw [pastPathIds_limit]
      exact he
    obtain ⟨a, b, f, p, r, hf, hr⟩ := pastPathIds_split (@pastLimitId w) q he'
    have hf' : f.val = e := hf
    have ha : a = (P.initial j).1 := by
      have hid : a.id = (P.initial j).1.id :=
        f.property.2.1.symm.trans ((congrArg (edgeWest w) hf').trans hout.2)
      exact congrArg (fun n : ℕ => (⟨n⟩ : PresentVertex w)) hid
    subst a
    have hp : pastOptimal x (P.initial j).2 := by
      cases x with
      | ldp => exact P.initial_isLongest w hP j
      | sdp => exact P.initial_isShortest w hP j
    have hopt : pastOptimal x (((P.initial j).2.cons f).comp r) := by
      apply pastOptimal_replace_prefix x p (P.initial j).2 f r _ hp
      rwa [← hr]
    have hstarts := past_splice_starts w hfin hL htrans hR t hcut x P hP
      (((P.initial j).2.cons f).comp r) hopt
    rw [pathEdgeList_comp, pathEdgeList, P.prefix_edges, hf'] at hstarts
    exact pastStarts_append_left hstarts

/-- arbitrary infinite path `P` with longest segments (not necessarily leftmost), an edge `e`
leaving the vertex `(P.initial j).1`, before any record vertex, extends the prefix of `P`
to an infinite longest-path prefix iff `e` is eligible in the past stage `t - 1`. No
rotation-order hypothesis is taken; T_m, F4c and both-mode scope are not treated; not the paper result. -/

theorem past_ldp_prefix_eligible_iff_stage
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t) (e : ℕ)
    (hout : EdgePresent w e ∧ edgeWest w e = (P.initial j).1.id) :
    StartsInfiniteLdpGeodesicWithPrefix w 0
      ((List.ofFn (fun k : Fin j => P.edge k.val)) ++ [e]) ↔
      StageCodeXDPEligible w (t - 1) .ldp ⟨0⟩ ⟨(recordVertex w t).id⟩ e := by
  exact past_prefix_eligible_iff_stage w hfin hL htrans hR t hcut .ldp P hP j hbefore e hout

/-- arbitrary infinite path `P` with shortest segments (not necessarily leftmost), an edge `e`
leaving the vertex `(P.initial j).1`, before any record vertex, extends the prefix of `P`
to an infinite shortest-path prefix iff `e` is eligible in the past stage `t - 1`. No
rotation-order hypothesis is taken; T_m, F4c and both-mode scope are not treated; not the paper result. -/

theorem past_sdp_prefix_eligible_iff_stage
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t) (e : ℕ)
    (hout : EdgePresent w e ∧ edgeWest w e = (P.initial j).1.id) :
    StartsInfiniteSdpGeodesicWithPrefix w 0
      ((List.ofFn (fun k : Fin j => P.edge k.val)) ++ [e]) ↔
      StageCodeXDPEligible w (t - 1) .sdp ⟨0⟩ ⟨(recordVertex w t).id⟩ e := by
  exact past_prefix_eligible_iff_stage w hfin hL htrans hR t hcut .sdp P hP j hbefore e hout

/-- eligible outgoing-edge order of the past stage `t - 1` at a corner equals the filtered
prefix outgoing edges, given the explicit rotation-order hypothesis `hord` for the
vertices visited by the prefix; T_m, F4c and both-mode scope are not treated; not the paper result. -/

private theorem past_eligible_order_eq (x : XDP)
    (P : InfinitePresentPath w ⟨0⟩) (hP : pastSegments x P) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t)
    (corner : StageDart (kmswStage w (t - 1)).nextEdge)
    (hkind : corner = stageULHeadDart w (t - 1) ∨
      corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true)
    (hcorner : stageEndpoint (kmswStage w (t - 1)) corner = (P.initial j).1.id)
    (hord : ∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
      (d = stageULHeadDart w (t - 1) ∨ d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
      (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
      stageOutgoingEdgeOrder w (t - 1) d =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w (t - 1)) d)
          ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
            (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
              (kmswStage w (t - 1)).present e = true))) :
    stageEligibleOutgoingEdgeOrder w (t - 1) x ⟨0⟩ ⟨(recordVertex w t).id⟩ corner =
      (by
        classical
        exact (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
          (List.ofFn (fun k : Fin j => P.edge k.val))).filter
            (fun e => decide (pastStarts w x
              ((List.ofFn (fun k : Fin j => P.edge k.val)) ++ [e])))) := by
  classical
  have hend : geodesicPrefixEnd w 0 (List.ofFn (fun k : Fin j => P.edge k.val)) =
      (P.initial j).1.id := by
    rw [← P.prefix_edges]
    exact pathEdgeList_endpoint (P.initial j).2
  have ho := hord corner hkind ⟨j, le_rfl, hcorner⟩
  have ho' : stageOutgoingEdgeOrder w (t - 1) corner =
      (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
        (List.ofFn (fun k : Fin j => P.edge k.val))).filter
          (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
            (kmswStage w (t - 1)).present e = true)) := by
    simpa only [kmswPrefixOutgoingEdges, hend, hcorner] using ho
  rw [stageEligibleOutgoingEdgeOrder, ho', List.filter_filter]
  apply List.filter_congr
  intro e he
  have hout : EdgePresent w e ∧ edgeWest w e = (P.initial j).1.id := by
    have h := (mem_kmswPrefixOutgoingEdges w hfin hL htrans hR 0
      (List.ofFn (fun k : Fin j => P.edge k.val)) e).1 he
    rwa [hend] at h
  have hmatch := past_prefix_eligible_iff_stage w hfin hL htrans hR t hcut
    x P hP j hbefore e hout
  by_cases hs : pastStarts w x ((List.ofFn (fun k : Fin j => P.edge k.val)) ++ [e])
  · have hg := hmatch.mp hs
    have hp : e < (kmswStage w (t - 1)).nextEdge ∧ (kmswStage w (t - 1)).present e = true := by
      obtain ⟨a, b, f, hf, _, _, _⟩ := hg
      exact hf ▸ ⟨f.property.1, f.property.2.1⟩
    simp only [hs, hg, hp, true_and, decide_true, Bool.true_and]
  · have hg : ¬ StageCodeXDPEligible w (t - 1) x ⟨0⟩ ⟨(recordVertex w t).id⟩ e :=
      fun h => hs (hmatch.mpr h)
    simp only [hs, hg, decide_false, Bool.false_and]

/-- first eligible outgoing edge of the past stage `t - 1` at a corner equals the leftmost
longest-path extension `kmswLeftmostLdpExtension` of the prefix of `P`. This takes the
explicit stage/infinite rotation-order hypothesis `hord` (proved separately as
`stageOutgoingEdgeOrder_hord` in `KMSW/StageInfiniteOutgoingOrderSource.lean`, not here);
T_m, F4c and both-mode scope are not treated; not the paper result. -/

theorem past_ldp_first_eligible_eq_extension
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t)
    (corner : StageDart (kmswStage w (t - 1)).nextEdge)
    (hkind : corner = stageULHeadDart w (t - 1) ∨
      corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true)
    (hcorner : stageEndpoint (kmswStage w (t - 1)) corner = (P.initial j).1.id)
    (hord : ∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
      (d = stageULHeadDart w (t - 1) ∨
        d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
      (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
      stageOutgoingEdgeOrder w (t - 1) d =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w (t - 1)) d)
          ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
            (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
              (kmswStage w (t - 1)).present e = true))) :
    (stageEligibleOutgoingEdgeOrder w (t - 1) .ldp
      ⟨0⟩ ⟨(recordVertex w t).id⟩ corner).head? =
        kmswLeftmostLdpExtension w hfin hL htrans hR 0
          (List.ofFn (fun k : Fin j => P.edge k.val)) := by
  classical
  have h := congrArg List.head? (past_eligible_order_eq w hfin hL htrans hR t hcut
    .ldp P hP j hbefore corner hkind hcorner hord)
  rw [List.head?_filter] at h
  refine h.trans ?_
  unfold kmswLeftmostLdpExtension
  apply congrArg (fun f : ℕ → Bool =>
    (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
      (List.ofFn (fun k : Fin j => P.edge k.val))).find? f)
  funext e
  apply decide_eq_decide.mpr
  rfl

/-- first eligible outgoing edge of the past stage `t - 1` at a corner equals the leftmost
shortest-path extension `kmswLeftmostSdpExtension` of the prefix of `P`. This takes the
explicit stage/infinite rotation-order hypothesis `hord` (proved separately as
`stageOutgoingEdgeOrder_hord` in `KMSW/StageInfiniteOutgoingOrderSource.lean`, not here);
T_m, F4c and both-mode scope are not treated; not the paper result. -/

theorem past_sdp_first_eligible_eq_extension
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments) (j : ℕ)
    (hbefore : ∀ k ≤ j, (P.initial k).1 ≠ recordVertex w t)
    (corner : StageDart (kmswStage w (t - 1)).nextEdge)
    (hkind : corner = stageULHeadDart w (t - 1) ∨
      corner.2 = false ∧ (stageRot w (t - 1) corner).2 = true)
    (hcorner : stageEndpoint (kmswStage w (t - 1)) corner = (P.initial j).1.id)
    (hord : ∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
      (d = stageULHeadDart w (t - 1) ∨
        d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
      (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
      stageOutgoingEdgeOrder w (t - 1) d =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w (t - 1)) d)
          ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
            (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
              (kmswStage w (t - 1)).present e = true))) :
    (stageEligibleOutgoingEdgeOrder w (t - 1) .sdp
      ⟨0⟩ ⟨(recordVertex w t).id⟩ corner).head? =
        kmswLeftmostSdpExtension w hfin hL htrans hR 0
          (List.ofFn (fun k : Fin j => P.edge k.val)) := by
  classical
  have h := congrArg List.head? (past_eligible_order_eq w hfin hL htrans hR t hcut
    .sdp P hP j hbefore corner hkind hcorner hord)
  rw [List.head?_filter] at h
  refine h.trans ?_
  unfold kmswLeftmostSdpExtension
  apply congrArg (fun f : ℕ → Bool =>
    (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
      (List.ofFn (fun k : Fin j => P.edge k.val))).find? f)
  funext e
  apply decide_eq_decide.mpr
  rfl

end DirectedDistances.KMSW
