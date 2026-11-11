module

import DirectedDistances.KMSW.LeftmostGeodesic
import DirectedDistances.KMSW.InfiniteGeodesicAnyStart
public import DirectedDistances.KMSW.OutgoingIntervalSplices
import DirectedDistances.KMSW.ActiveTimeMonotone

public import DirectedDistances.KMSW.PathSpaceTransferCarrier
import DirectedDistances.KMSW.EventuallyPresent
import Mathlib.Data.List.FinRange

/-! # Boundary-anchored outgoing rotation order

The false geometric dart of a present edge is its outgoing dart. -/

public section
namespace DirectedDistances.KMSW

open Filter

variable (w : ℕ → Fin 3)

/-- Under the UIQBOT code conditions every geometric edge is present -/
theorem edgePresent_of_nonneg_of_unbounded
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) :
    EdgePresent w e := by
  obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL hR e
  exact ⟨N, hN N le_rfl⟩

/-- The geometric darts based at the source are exactly the present outgoing -/
theorem source_dart_iff_outgoing
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (d : ℕ × Bool) :
    (if d.2 then edgeEast w d.1 else edgeWest w d.1) = 0 ↔
      d.2 = false ∧ EdgePresent w d.1 ∧ edgeWest w d.1 = 0 := by
  have hp := edgePresent_of_nonneg_of_unbounded w hL hR d.1
  cases d with
  | mk e b =>
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
      exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
    · have hn := zero_no_incoming_present_edge w hL e hp
      simp only [↓reduceIte, Bool.true_eq_false, false_and, iff_false]
      exact hn

variable
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

private def dartEndpoint (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem endpoint_stage (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d = dartEndpoint w (d.1.val, d.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;>
    simp only [stageEndpoint, dartEndpoint, hb, Bool.false_eq_true, ↓reduceIte, hw, he]

include hfin in
private theorem complete_exists (v : ℕ) : ∃ N, kmswVertexComplete w N v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

/-- Two geometric darts lie in the same forward rotation orbit exactly when
based at the same vertex (`remark-kmsw-infinite`, -/
theorem kmswInfRot_exists_pow_iff_endpoint (d e : ℕ × Bool) :
    (∃ k : ℕ, (kmswInfRot w hfin ^ k) d = e) ↔
      (if d.2 then edgeEast w d.1 else edgeWest w d.1) =
        (if e.2 then edgeEast w e.1 else edgeWest w e.1) := by
  change (∃ k : ℕ, (kmswInfRot w hfin ^ k) d = e) ↔
    dartEndpoint w d = dartEndpoint w e
  obtain ⟨N, hN⟩ := complete_exists w hfin (dartEndpoint w d)
  let n := max N (max d.1 e.1)
  have hn : N ≤ n := le_max_left _ _
  have hd : d.1 < (kmswStage w n).nextEdge :=
    kmsw_nextEdge_unbounded w d.1 n ((le_max_left _ _).trans (le_max_right _ _))
  have he : e.1 < (kmswStage w n).nextEdge :=
    kmsw_nextEdge_unbounded w e.1 n ((le_max_right _ _).trans (le_max_right _ _))
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  let y : StageDart (kmswStage w n).nextEdge := (⟨e.1, he⟩, e.2)
  have hx : kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) := by
    rw [endpoint_stage]
    intro f hf
    exact (hN f hf).trans_le (kmswStage_nextEdge_mono w hn)
  constructor
  · rintro ⟨k, hk⟩
    have hp := kmswInfRot_pow_eq_stage w hfin n x hx k
    change (kmswInfRot w hfin ^ k) d = _ at hp
    have hv : dartEndpoint w e =
        stageEndpoint (kmswStage w n) ((stageRot w n ^ k) x) := by
      rw [endpoint_stage, ← hp, hk]
    have hc := (stageRot_sameCycle_iff_endpoint_eq w n x ((stageRot w n ^ k) x)).1
      ⟨(k : ℤ), by simp only [zpow_natCast]⟩
    exact (endpoint_stage w n x).symm.trans (hc.trans hv.symm)
  · intro hv
    have hxy : stageEndpoint (kmswStage w n) x = stageEndpoint (kmswStage w n) y := by
      rw [endpoint_stage, endpoint_stage]
      exact hv
    obtain ⟨k, hk⟩ := ((stageRot_sameCycle_iff_endpoint_eq w n x y).2 hxy).exists_nat_pow_eq
    refine ⟨k, ?_⟩
    have hp := kmswInfRot_pow_eq_stage w hfin n x hx k
    rw [hk] at hp
    exact hp

include hfin in
/-- The darts at each vertex form a finite set under geometric local -/
theorem kmsw_darts_at_vertex_finite (v : ℕ) :
    {d : ℕ × Bool | (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v}.Finite := by
  apply ((hfin v).prod (Set.finite_univ (α := Bool))).subset
  rintro ⟨e, b⟩ hd
  refine ⟨⟨e, kmsw_edge_allocated_by_self w e, ?_⟩, Set.mem_univ b⟩
  cases b
  · exact Or.inl hd
  · exact Or.inr hd

/-- The limiting rotation is one cycle on all geometric darts at a vertex -/
theorem kmswInfRot_isCycleOn_vertex (v : ℕ) :
    (kmswInfRot w hfin).IsCycleOn
      {d : ℕ × Bool | (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v} := by
  let σ := kmswInfRot w hfin
  have hep (d : ℕ × Bool) : dartEndpoint w d = dartEndpoint w (σ d) :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin d (σ d)).1 ⟨1, by simp only [pow_one]; rfl⟩
  refine ⟨⟨?_, σ.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (hep d).symm.trans hd
  · intro d hd
    refine ⟨σ.symm d, ?_, σ.apply_symm_apply d⟩
    have he := hep (σ.symm d)
    rw [Equiv.apply_symm_apply] at he
    exact he.trans hd
  · intro d hd e he
    obtain ⟨k, hk⟩ := (kmswInfRot_exists_pow_iff_endpoint w hfin d e).2 (hd.trans he.symm)
    exact ⟨(k : ℤ), by simpa only [zpow_natCast] using hk⟩

private theorem arc_eq_of_unmarked_predecessor {D : Type*}
    (σ : Equiv.Perm D) (p : D → Prop) (d r : D)
    (hr : ¬p (σ.symm r)) (h : RotationArc σ p d r) : d = r := by
  obtain ⟨k, hk, hp⟩ := h
  cases k with
  | zero => exact hk
  | succ k =>
    have he : (σ ^ k) d = σ.symm r := by
      apply σ.injective
      rw [Equiv.apply_symm_apply]
      exact (congrArg (fun τ : Equiv.Perm D => τ d) (pow_succ' σ k)).symm.trans hk
    exact (hr (he ▸ hp k (Nat.le_succ k))).elim

private theorem cycle_marked_start {D : Type*} [DecidableEq D]
    (σ : Equiv.Perm D) (s : Finset D) (hs : σ.IsCycleOn (s : Set D))
    (p : D → Prop) (i o : D) (hi : i ∈ s) (ho : o ∈ s)
    (hpi : ¬p i) (hpo : p o) :
    ∃ r ∈ s, p r ∧ ¬p (σ.symm r) := by
  classical
  have hex : ∃ k : ℕ, p ((σ ^ k) i) := by
    obtain ⟨k, _, hk⟩ := hs.exists_pow_eq hi ho
    exact ⟨k, hk ▸ hpo⟩
  let k := Nat.find hex
  have hk : p ((σ ^ k) i) := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz] at hk
    exact hpi hk
  refine ⟨(σ ^ k) i, hs.1.mapsTo.perm_pow k hi, hk, ?_⟩
  have he : σ.symm ((σ ^ k) i) = (σ ^ (k - 1)) i := by
    apply σ.injective
    rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hkpos]
  rw [he]
  exact Nat.find_min hex (by change k - 1 < k; omega)

private theorem marked_cycle_enumeration {D : Type*} [DecidableEq D]
    (σ : Equiv.Perm D) (s : Finset D) (hs : σ.IsCycleOn (s : Set D))
    (p : D → Prop) (r : D) (hr : r ∈ s) (hpr : p r) (hprev : ¬p (σ.symm r))
    (hint : ∀ d ∈ s, p d → RotationArc σ p r d ∨ RotationArc σ p d r) :
    ∃ (l : D) (ds : List D), ds.Nodup ∧ ds.head? = some r ∧ ds.getLast? = some l ∧
      (∀ d, d ∈ ds ↔ d ∈ s ∧ p d) ∧
      ds.IsChain (fun d e => σ d = e) ∧ ¬p (σ l) := by
  classical
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨r, hr⟩
  have hlast : (σ ^ (s.card - 1)) r = σ.symm r := by
    apply σ.injective
    rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ',
      Nat.sub_add_cancel hpos, hs.pow_card_apply hr]
  have hex : ∃ k : ℕ, ¬p ((σ ^ k) r) := ⟨s.card - 1, hlast ▸ hprev⟩
  let k := Nat.find hex
  have hk : ¬p ((σ ^ k) r) := Nat.find_spec hex
  have hkbound : k ≤ s.card - 1 := Nat.find_min' hex (hlast ▸ hprev)
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz] at hk
    exact hk hpr
  have hmarked (i : ℕ) (hi : i < k) : p ((σ ^ i) r) :=
    Classical.not_not.mp (Nat.find_min hex hi)
  let f : Fin k → D := fun i => (σ ^ i.val) r
  refine ⟨(σ ^ (k - 1)) r, List.ofFn f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact Fin.ext (hs.injOn_pow_apply hr (by change i.val < s.card; have := i.isLt; omega)
      (by change j.val < s.card; have := j.isLt; omega) hij)
  · simp only [List.head?_eq_getElem?, List.getElem?_ofFn, hkpos, ↓reduceDIte]
    rfl
  · simp only [List.getLast?_eq_getElem?, List.length_ofFn, List.getElem?_ofFn,
      show k - 1 < k by omega, ↓reduceDIte, f]
  · intro d
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨hs.1.mapsTo.perm_pow i.val hr, hmarked i.val i.isLt⟩
    · rintro ⟨hd, hpd⟩
      have ha : RotationArc σ p r d := by
        rcases hint d hd hpd with ha | ha
        · exact ha
        · have he := arc_eq_of_unmarked_predecessor σ p d r hprev ha
          rw [he]
          exact RotationArc.refl σ p r hpr
      obtain ⟨j, hj, hpj⟩ := ha
      have hjk : j < k := by
        by_contra h
        exact hk (hpj k (by omega))
      exact ⟨⟨j, hjk⟩, hj⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn, f]
    exact (congrArg (fun τ : Equiv.Perm D => τ r) (pow_succ' σ i)).symm
  · rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hkpos]
    exact hk

private theorem cycle_enumeration {D : Type*} [DecidableEq D]
    (σ : Equiv.Perm D) (s : Finset D) (hs : σ.IsCycleOn (s : Set D))
    (r l : D) (hr : r ∈ s) (hl : σ l = r) :
    ∃ ds : List D, ds.Nodup ∧ ds.head? = some r ∧ ds.getLast? = some l ∧
      (∀ d, d ∈ ds ↔ d ∈ s) ∧ ds.IsChain (fun d e => σ d = e) := by
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨r, hr⟩
  let f : Fin s.card → D := fun i => (σ ^ i.val) r
  refine ⟨List.ofFn f, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact Fin.ext (hs.injOn_pow_apply hr i.isLt j.isLt hij)
  · simp only [List.head?_eq_getElem?, List.getElem?_ofFn, hpos, ↓reduceDIte]
    rfl
  · have hlast : (σ ^ (s.card - 1)) r = l := by
      apply σ.injective
      rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos, hs.pow_card_apply hr, hl]
    simpa only [List.getLast?_eq_getElem?, List.length_ofFn, List.getElem?_ofFn,
      show s.card - 1 < s.card by omega, ↓reduceDIte, f] using congrArg some hlast
  · intro d
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact hs.1.mapsTo.perm_pow i.val hr
    · intro hd
      obtain ⟨i, hi, hid⟩ := hs.exists_pow_eq hr hd
      exact ⟨⟨i, hi⟩, hid⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn, f]
    exact (congrArg (fun τ : Equiv.Perm D => τ r) (pow_succ' σ i)).symm

/-- The outer corner closes the source rotation from the left boundary to -/
theorem kmswInfRot_source_outer_corner
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    kmswInfRot w hfin (kmswLeftBoundaryEdge w 0, false) =
      (kmswRightBoundaryEdge w 0, false) := by
  have h := kmswInfFaceSucc_junction w hfin (stageOuterWord_faceSucc w) hL htrans hR
  change (kmswInfRot w hfin).symm (kmswRightBoundaryEdge w 0, false) =
    (kmswLeftBoundaryEdge w 0, false) at h
  have hr := congrArg (kmswInfRot w hfin) h
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- The source outgoing edges, exhaustively and without repetition, in
counterclockwise order from the right boundary to the left boundary.
The outside corner is between the last and first entries (`lem-geo-exist`, -/
theorem kmsw_source_outgoing_enumeration
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    ∃ es : List ℕ, es.Nodup ∧
      es.head? = some (kmswRightBoundaryEdge w 0) ∧
      es.getLast? = some (kmswLeftBoundaryEdge w 0) ∧
      (∀ e, e ∈ es ↔ EdgePresent w e ∧ edgeWest w e = 0) ∧
      es.IsChain (fun e f => kmswInfRot w hfin (e, false) = (f, false)) := by
  classical
  let S := {d : ℕ × Bool | dartEndpoint w d = 0}
  have hS : S.Finite := kmsw_darts_at_vertex_finite w hfin 0
  have hr : (kmswRightBoundaryEdge w 0, false) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]
    change edgeWest w (kmswRightBoundaryEdge w 0) = 0
    exact (kmswRightBoundary_infinite_present_path w hL hR).2.2.1
  have hc : (kmswInfRot w hfin).IsCycleOn (hS.toFinset : Set (ℕ × Bool)) := by
    simpa only [Set.Finite.coe_toFinset, S, dartEndpoint] using kmswInfRot_isCycleOn_vertex w hfin 0
  obtain ⟨ds, hd, hh, ht, hm, hchain⟩ := cycle_enumeration (kmswInfRot w hfin)
    hS.toFinset hc (kmswRightBoundaryEdge w 0, false) (kmswLeftBoundaryEdge w 0, false)
    hr (kmswInfRot_source_outer_corner w hfin hL htrans hR)
  have hmem (d : ℕ × Bool) : d ∈ ds ↔
      d.2 = false ∧ EdgePresent w d.1 ∧ edgeWest w d.1 = 0 := by
    rw [hm, Set.Finite.mem_toFinset]
    exact source_dart_iff_outgoing w hL hR d
  refine ⟨ds.map Prod.fst, ?_, ?_, ?_, ?_, ?_⟩
  · apply hd.map_on
    intro d hd e he hde
    exact Prod.ext hde (((hmem d).1 hd).1.trans (((hmem e).1 he).1.symm))
  · simp only [List.head?_map, hh, Option.map_some]
  · simp only [List.getLast?_map, ht, Option.map_some]
  · intro e
    rw [List.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ((hmem d).1 hd).2
    · intro he
      exact ⟨(e, false), (hmem (e, false)).2 ⟨rfl, he⟩, rfl⟩
  · rw [List.isChain_map]
    apply hchain.imp_of_mem_imp
    intro d e hd he hde
    have hdb := ((hmem d).1 hd).1
    have heb := ((hmem e).1 he).1
    have hdd : (d.1, false) = d := Prod.ext rfl hdb.symm
    have hee : (e.1, false) = e := Prod.ext rfl heb.symm
    rw [hdd, hee]
    exact hde

/-- At an allocated non-source vertex, the exhaustive counterclockwise
outgoing list runs from the rightmost outgoing edge to the leftmost one.
Its predecessor and successor darts are incoming, which specifies both
endpoints of the outgoing interval (`lem-geo-exist`, -/
theorem kmsw_nonzero_outgoing_enumeration
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) (hne : v ≠ 0) :
    ∃ (r l : ℕ) (es : List ℕ), es.Nodup ∧ es.head? = some r ∧ es.getLast? = some l ∧
      (∀ e, e ∈ es ↔ EdgePresent w e ∧ edgeWest w e = v) ∧
      es.IsChain (fun e f => kmswInfRot w hfin (e, false) = (f, false)) ∧
      ((kmswInfRot w hfin).symm (r, false)).2 = true ∧
      (kmswInfRot w hfin (l, false)).2 = true := by
  classical
  let σ := kmswInfRot w hfin
  let S := {d : ℕ × Bool | dartEndpoint w d = v}
  let p := fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1
  have hS : S.Finite := kmsw_darts_at_vertex_finite w hfin v
  have hc : σ.IsCycleOn (hS.toFinset : Set (ℕ × Bool)) := by
    simpa only [Set.Finite.coe_toFinset, S, dartEndpoint, σ] using
      kmswInfRot_isCycleOn_vertex w hfin v
  obtain ⟨i, hi, hiv⟩ := allocated_vertex_has_incoming_present_edge w hL v hv hne
  obtain ⟨o, ho, hov⟩ := allocated_vertex_outgoing_present_edge w hR v hv
  have him : (i, true) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hiv
  have hom : (o, false) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hov
  obtain ⟨r, hr, hpr, hprev⟩ := cycle_marked_start σ hS.toFinset hc p
    (i, true) (o, false) him hom (by simp only [p, Bool.true_eq_false, false_and, not_false_eq_true])
    ⟨rfl, ho⟩
  have rr : (r.1, false) = r := Prod.ext rfl hpr.1.symm
  have hint (d : ℕ × Bool) (hd : d ∈ hS.toFinset) (hpd : p d) :
      RotationArc σ p r d ∨ RotationArc σ p d r := by
    have dd : (d.1, false) = d := Prod.ext rfl hpd.1.symm
    have hrv : edgeWest w r.1 = v := by
      have ht := (hS.mem_toFinset).mp hr
      change dartEndpoint w r = v at ht
      rw [← rr] at ht
      exact ht
    have hdv : edgeWest w d.1 = v := by
      have ht := (hS.mem_toFinset).mp hd
      change dartEndpoint w d = v at ht
      rw [← dd] at ht
      exact ht
    have ht := kmswInfRot_outgoing_interval w hL hfin r.1 d.1
      (hrv.trans hdv.symm) hpr.2 hpd.2
    rw [rr, dd] at ht
    exact ht
  obtain ⟨l, ds, hn, hh, ht, hm, hchain, hnext⟩ :=
    marked_cycle_enumeration σ hS.toFinset hc p r hr hpr hprev hint
  have hmem (d : ℕ × Bool) : d ∈ ds ↔
      d.2 = false ∧ EdgePresent w d.1 ∧ edgeWest w d.1 = v := by
    rw [hm, Set.Finite.mem_toFinset]
    change (dartEndpoint w d = v ∧ p d) ↔ _
    constructor
    · rintro ⟨hdv, hb, hp⟩
      exact ⟨hb, hp, by simpa only [dartEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hdv⟩
    · rintro ⟨hb, hp, hdv⟩
      exact ⟨by simpa only [dartEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hdv, hb, hp⟩
  have hlb := ((hmem l).1 (List.mem_of_getLast? ht)).1
  have ll : (l.1, false) = l := Prod.ext rfl hlb.symm
  have incoming (d : ℕ × Bool) (hd : ¬p d) : d.2 = true := by
    cases hb : d.2
    · exact (hd ⟨hb, edgePresent_of_nonneg_of_unbounded w hL hR d.1⟩).elim
    · rfl
  refine ⟨r.1, l.1, ds.map Prod.fst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hn.map_on
    intro d hd e he hde
    exact Prod.ext hde (((hmem d).1 hd).1.trans (((hmem e).1 he).1.symm))
  · simp only [List.head?_map, hh, Option.map_some]
  · simp only [List.getLast?_map, ht, Option.map_some]
  · intro e
    rw [List.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ((hmem d).1 hd).2
    · intro he
      exact ⟨(e, false), (hmem (e, false)).2 ⟨rfl, he⟩, rfl⟩
  · rw [List.isChain_map]
    apply hchain.imp_of_mem_imp
    intro d e hd he hde
    have dd : (d.1, false) = d := Prod.ext rfl ((hmem d).1 hd).1.symm
    have ee : (e.1, false) = e := Prod.ext rfl ((hmem e).1 he).1.symm
    rw [dd, ee]
    exact hde
  · rw [rr]
    exact incoming _ hprev
  · rw [ll]
    exact incoming _ hnext

/-- The first edge of an infinite present path is present and starts at
its specified initial vertex (`def-infinite-geo`, -/
theorem InfinitePresentPath.first_edge_outgoing {x : PresentVertex w}
    (P : InfinitePresentPath w x) :
    EdgePresent w (P.edge 0) ∧ edgeWest w (P.edge 0) = x.id := by
  have hlen := P.prefix_length 1
  have hedges := P.prefix_edges 1
  generalize hq : P.initial 1 = zq at hlen hedges
  rcases zq with ⟨z, q⟩
  dsimp only at hlen hedges
  cases q with
  | nil => simp only [Quiver.Path.length_nil] at hlen; omega
  | @cons y z q a =>
    cases q with
    | nil =>
      have he : a.val = P.edge 0 := by
        simpa only [pathEdgeList, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.cons.injEq, and_true, Fin.val_zero] using hedges
      rw [← he]
      exact ⟨a.property.1, a.property.2.1⟩
    | cons q b =>
      simp only [Quiver.Path.length_cons] at hlen
      omega

/-- Outgoing edges in left-to-right order, with the source cut at the outer
corner and every other allocated vertex cut at its incoming block -/
@[expose] noncomputable def kmswOutgoingEdgesLeftToRight
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) : List ℕ := by
  classical
  exact if h : v = 0 then
    (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose.reverse
  else
    (kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv h).choose_spec.choose_spec.choose.reverse

/-- Membership in the outgoing order is exactly presence with the specified -/
theorem mem_kmswOutgoingEdgesLeftToRight
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) (e : ℕ) :
    e ∈ kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv ↔
      EdgePresent w e ∧ edgeWest w e = v := by
  classical
  unfold kmswOutgoingEdgesLeftToRight
  split
  · rename_i h
    rw [List.mem_reverse, h]
    exact (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.2.2.1 e
  · rename_i h
    rw [List.mem_reverse]
    exact (kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv h).choose_spec.choose_spec.choose_spec.2.2.2.1 e

/-- A candidate first edge starts an actual infinite LDP geodesic, retaining -/
@[expose] def StartsInfiniteLdpGeodesic (v e : ℕ) : Prop :=
  ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧ P.edge 0 = e

/-- Search the finite outgoing list from left to right for an edge starting
an infinite LDP geodesic (`lem-geo-exist`, -/
@[expose] noncomputable def kmswLeftmostLdpStep
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) : Option ℕ := by
  classical
  exact (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).find?
    (fun e => decide (StartsInfiniteLdpGeodesic w v e))

include hfin in
/-- There are finitely many candidate first edges at every vertex -/
theorem startsInfiniteLdpGeodesic_finite (v : ℕ) :
    {e : ℕ | StartsInfiniteLdpGeodesic w v e}.Finite := by
  apply (hfin v).subset
  rintro e ⟨P, _, rfl⟩
  have hp := InfinitePresentPath.first_edge_outgoing w P
  exact ⟨P.edge 0, kmsw_edge_allocated_by_self w (P.edge 0), Or.inl hp.2⟩

/-- The selected edge is eligible and every earlier edge in the left-to-right -/
theorem kmswLeftmostLdpStep_eq_some_iff
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) (e : ℕ) :
    kmswLeftmostLdpStep w hfin hL htrans hR v hv = some e ↔
      StartsInfiniteLdpGeodesic w v e ∧ ∃ as bs : List ℕ,
        kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv = as ++ e :: bs ∧
        ∀ a ∈ as, ¬StartsInfiniteLdpGeodesic w v a := by
  classical
  simp only [kmswLeftmostLdpStep, List.find?_eq_some_iff_append,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

/-- Simultaneously at every vertex, almost surely the finite leftmost search
returns an edge. Nonemptiness uses an actual infinite LDP geodesic from the
all-start existence theorem (`lem-geo-exist`, -/
theorem pitmanCodes_ae_leftmostLdpStep_isSome :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
        (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex),
        ∀ v, (kmswLeftmostLdpStep w hfin hL htrans hR v (halloc v)).isSome = true := by
  classical
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices,
    pitmanCodes_ae_exists_allocated_infinite_extremal] with ω hmap hgeo
  obtain ⟨hf, htrans, hR, hL, _⟩ := hmap
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  have halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex :=
    fun v => kmsw_vertex_allocated_of_finite_incidence w hf v
  refine ⟨hf, hL, htrans, hR, halloc, fun v => ?_⟩
  obtain ⟨P, hP⟩ := (hgeo ⟨v⟩ (halloc v)).1
  change ((kmswOutgoingEdgesLeftToRight w hf hL htrans hR v (halloc v)).find?
    (fun e => decide (StartsInfiniteLdpGeodesic w v e))).isSome = true
  apply List.find?_isSome.mpr
  refine ⟨P.edge 0, ?_, ?_⟩
  · exact (mem_kmswOutgoingEdgesLeftToRight w hf hL htrans hR v (halloc v) (P.edge 0)).2
      (InfinitePresentPath.first_edge_outgoing w P)
  · exact decide_eq_true ⟨P, hP, rfl⟩

end DirectedDistances.KMSW
