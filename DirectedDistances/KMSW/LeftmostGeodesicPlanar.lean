module

public import DirectedDistances.KMSW.LeftmostGeodesicAssembly

/-! # Incoming rotation intervals and comparisons at shared vertices

Helpers for `def-infinite-geo` and `lem-geo-exist`,

The incoming interval is the complement of the outgoing interval. At a
shared vertex, longest-prefix optimality forces equal visit indices, and
equal-length prefix replacement constructs an infinite geodesic splice.
Consequently the constructed path is minimal at every shared departure,
simultaneously at every start almost surely, with a unique edge stream.

Remaining geometric obligation: construct the submap between this path and
the rightmost directed path and prove containment of every competing geodesic.
No path-cut/face-side separation theorem or incoming-side comparison for all
competitors is asserted here. In particular `SharedVertexWeaklyRight` is a
local rotation predicate, not a replacement definition of submap containment. -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

private theorem rotation_pow_add {D : Type*} (σ : Equiv.Perm D)
    (a : D) (i j : ℕ) : (σ ^ i) ((σ ^ j) a) = (σ ^ (i + j)) a := by
  rw [pow_add, Equiv.Perm.mul_apply]

private theorem marked_arc_no_wrap {D : Type*} (σ : Equiv.Perm D)
    (s : Finset D) (hs : σ.IsCycleOn (s : Set D)) (p : D → Prop)
    (a : D) (ha : a ∈ s) (hpa : ¬p a) (i : ℕ) (hi : i < s.card)
    {d : D} (h : RotationArc σ p ((σ ^ i) a) d) :
    ∃ k, k + i < s.card ∧ (σ ^ (k + i)) a = d ∧
      ∀ j, j ≤ k → p ((σ ^ (j + i)) a) := by
  obtain ⟨k, hk, hp⟩ := h
  have hb : k < s.card - i := by
    by_contra hn
    have ht := hp (s.card - i) (by omega)
    rw [rotation_pow_add, Nat.sub_add_cancel (by omega), hs.pow_card_apply ha] at ht
    exact hpa ht
  refine ⟨k, by omega, ?_, ?_⟩
  · rw [← rotation_pow_add]
    exact hk
  · intro j hj
    rw [← rotation_pow_add]
    exact hp j hj

private theorem marked_positions_convex {D : Type*} (σ : Equiv.Perm D)
    (s : Finset D) (hs : σ.IsCycleOn (s : Set D)) (p : D → Prop)
    (a : D) (ha : a ∈ s) (hpa : ¬p a)
    (hint : ∀ d ∈ s, ∀ e ∈ s, p d → p e →
      RotationArc σ p d e ∨ RotationArc σ p e d)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hk : k < s.card)
    (hpi : p ((σ ^ i) a)) (hpk : p ((σ ^ k) a)) : p ((σ ^ j) a) := by
  have hi : i < s.card := by omega
  rcases hint _ (hs.1.mapsTo.perm_pow i ha) _ (hs.1.mapsTo.perm_pow k ha)
    hpi hpk with h | h
  · obtain ⟨n, hn, he, hp⟩ := marked_arc_no_wrap σ s hs p a ha hpa i hi h
    have heq : n + i = k := hs.injOn_pow_apply ha hn hk he
    have ht := hp (j - i) (by omega)
    simpa only [Nat.sub_add_cancel hij] using ht
  · obtain ⟨n, hn, he, hp⟩ := marked_arc_no_wrap σ s hs p a ha hpa k hk h
    have heq : n + k = i := hs.injOn_pow_apply ha hn hi he
    have hji : j = i := by omega
    exact hji ▸ hpi

private theorem complementary_rotation_interval {D : Type*} (σ : Equiv.Perm D)
    (s : Finset D) (hs : σ.IsCycleOn (s : Set D)) (p : D → Prop)
    (hint : ∀ d ∈ s, ∀ e ∈ s, p d → p e →
      RotationArc σ p d e ∨ RotationArc σ p e d)
    (a b : D) (ha : a ∈ s) (hb : b ∈ s) (hpa : ¬p a) (hpb : ¬p b) :
    RotationArc σ (fun d => ¬p d) a b ∨ RotationArc σ (fun d => ¬p d) b a := by
  classical
  obtain ⟨k, hk, hkb⟩ := hs.exists_pow_eq ha hb
  by_cases hfront : ∀ i, i ≤ k → ¬p ((σ ^ i) a)
  · exact Or.inl ⟨k, hkb, hfront⟩
  · push Not at hfront
    obtain ⟨i, hi, hpi⟩ := hfront
    right
    refine ⟨s.card - k, ?_, ?_⟩
    · rw [← hkb, rotation_pow_add, Nat.sub_add_cancel (by omega), hs.pow_card_apply ha]
    · intro j hj hp
      rw [← hkb, rotation_pow_add] at hp
      by_cases he : j + k = s.card
      · rw [he, hs.pow_card_apply ha] at hp
        exact hpa hp
      · have hlt : j + k < s.card := by omega
        apply hpb
        rw [← hkb]
        exact marked_positions_convex σ s hs p a ha hpa hint i k (j + k)
          hi (by omega) hlt hpi hp

private theorem planar_arc_eq_of_unmarked_predecessor {D : Type*}
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

private theorem planar_marked_cycle_enumeration {D : Type*} [DecidableEq D]
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
        · have he := planar_arc_eq_of_unmarked_predecessor σ p d r hprev ha
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

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Present incoming darts at a vertex form one rotation interval, complementary
to the outgoing interval. All geometric edges are present under these code -/
theorem kmswInfRot_incoming_interval
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (e f : ℕ) (hv : edgeEast w e = edgeEast w f) :
    RotationArc (kmswInfRot w hfin)
      (fun d => d.2 = true ∧ EdgePresent w d.1) (e, true) (f, true) ∨
    RotationArc (kmswInfRot w hfin)
      (fun d => d.2 = true ∧ EdgePresent w d.1) (f, true) (e, true) := by
  classical
  let S := {d : ℕ × Bool |
    (if d.2 then edgeEast w d.1 else edgeWest w d.1) = edgeEast w e}
  have hS : S.Finite := kmsw_darts_at_vertex_finite w hfin _
  have hc : (kmswInfRot w hfin).IsCycleOn (hS.toFinset : Set (ℕ × Bool)) := by
    simpa only [Set.Finite.coe_toFinset, S] using
      kmswInfRot_isCycleOn_vertex w hfin (edgeEast w e)
  let p := fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1
  have hint : ∀ d ∈ hS.toFinset, ∀ g ∈ hS.toFinset, p d → p g →
      RotationArc (kmswInfRot w hfin) p d g ∨
      RotationArc (kmswInfRot w hfin) p g d := by
    intro d hd g hg hpd hpg
    have dd : (d.1, false) = d := Prod.ext rfl hpd.1.symm
    have gg : (g.1, false) = g := Prod.ext rfl hpg.1.symm
    have hdv := (hS.mem_toFinset).mp hd
    have hgv := (hS.mem_toFinset).mp hg
    change (if d.2 then edgeEast w d.1 else edgeWest w d.1) = _ at hdv
    change (if g.2 then edgeEast w g.1 else edgeWest w g.1) = _ at hgv
    simp only [hpd.1, hpg.1, Bool.false_eq_true, ↓reduceIte] at hdv hgv
    have ht := kmswInfRot_outgoing_interval w hL hfin d.1 g.1
      (hdv.trans hgv.symm) hpd.2 hpg.2
    rw [dd, gg] at ht
    exact ht
  have he : (e, true) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact rfl
  have hf : (f, true) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hv.symm
  have ht := complementary_rotation_interval (kmswInfRot w hfin) hS.toFinset hc p hint
    (e, true) (f, true) he hf (by simp only [p, Bool.true_eq_false, false_and, not_false_eq_true])
    (by simp only [p, Bool.true_eq_false, false_and, not_false_eq_true])
  have heq : (fun d => ¬p d) = (fun d => d.2 = true ∧ EdgePresent w d.1) := by
    funext d
    have hp := edgePresent_of_nonneg_of_unbounded w hL hR d.1
    cases d with
    | mk a b => cases b <;> simp only [p, hp, and_true, Bool.false_eq_true,
        Bool.true_eq_false, not_true_eq_false, not_false_eq_true]
  rw [heq] at ht
  exact ht

/-- Exhaustive incoming edge enumeration in counterclockwise order, starting
immediately after the outgoing block and ending immediately before it.
The neighbouring darts are outgoing (`lem-geo-exist`, -/
theorem kmsw_nonzero_incoming_enumeration
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) (hne : v ≠ 0) :
    ∃ (l r : ℕ) (es : List ℕ), es.Nodup ∧ es.head? = some l ∧ es.getLast? = some r ∧
      (∀ e, e ∈ es ↔ EdgePresent w e ∧ edgeEast w e = v) ∧
      es.IsChain (fun e f => kmswInfRot w hfin (e, true) = (f, true)) ∧
      ((kmswInfRot w hfin).symm (l, true)).2 = false ∧
      (kmswInfRot w hfin (r, true)).2 = false := by
  classical
  let σ := kmswInfRot w hfin
  let S := {d : ℕ × Bool |
    (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v}
  let p := fun d : ℕ × Bool => d.2 = true ∧ EdgePresent w d.1
  have hS : S.Finite := kmsw_darts_at_vertex_finite w hfin v
  have hc : σ.IsCycleOn (hS.toFinset : Set (ℕ × Bool)) := by
    simpa only [Set.Finite.coe_toFinset, S, σ] using
      kmswInfRot_isCycleOn_vertex w hfin v
  obtain ⟨o, z, os, _, _, hz, hom, _, _, hn⟩ :=
    kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hne
  have hzv := ((hom z).1 (List.mem_of_getLast? hz)).2
  have hzm : (z, false) ∈ hS.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hzv
  let l := σ (z, false)
  have hl : l ∈ hS.toFinset := hc.1.mapsTo hzm
  have hpl : p l := ⟨hn, edgePresent_of_nonneg_of_unbounded w hL hR l.1⟩
  have hprev : ¬p (σ.symm l) := by
    simp only [l, Equiv.symm_apply_apply, p, Bool.false_eq_true, false_and,
      not_false_eq_true]
  have hint (d : ℕ × Bool) (hd : d ∈ hS.toFinset) (hpd : p d) :
      RotationArc σ p l d ∨ RotationArc σ p d l := by
    have ll : (l.1, true) = l := Prod.ext rfl hpl.1.symm
    have dd : (d.1, true) = d := Prod.ext rfl hpd.1.symm
    have hlv := (hS.mem_toFinset).mp hl
    have hdv := (hS.mem_toFinset).mp hd
    change (if l.2 then edgeEast w l.1 else edgeWest w l.1) = v at hlv
    change (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v at hdv
    simp only [hpl.1, hpd.1, ↓reduceIte] at hlv hdv
    have ht := kmswInfRot_incoming_interval w hfin hL hR l.1 d.1
      (hlv.trans hdv.symm)
    rw [ll, dd] at ht
    exact ht
  obtain ⟨r, ds, hnd, hh, ht, hm, hchain, hnext⟩ :=
    planar_marked_cycle_enumeration σ hS.toFinset hc p l hl hpl hprev hint
  have hmem (d : ℕ × Bool) : d ∈ ds ↔
      d.2 = true ∧ EdgePresent w d.1 ∧ edgeEast w d.1 = v := by
    rw [hm, Set.Finite.mem_toFinset]
    change ((if d.2 then edgeEast w d.1 else edgeWest w d.1) = v ∧ p d) ↔ _
    constructor
    · rintro ⟨hdv, hb, hp⟩
      exact ⟨hb, hp, by simpa only [hb, ↓reduceIte] using hdv⟩
    · rintro ⟨hb, hp, hdv⟩
      exact ⟨by simpa only [hb, ↓reduceIte] using hdv, hb, hp⟩
  have hrb := ((hmem r).1 (List.mem_of_getLast? ht)).1
  have ll : (l.1, true) = l := Prod.ext rfl hpl.1.symm
  have rr : (r.1, true) = r := Prod.ext rfl hrb.symm
  have outgoing (d : ℕ × Bool) (hd : ¬p d) : d.2 = false := by
    cases hb : d.2
    · rfl
    · exact (hd ⟨hb, edgePresent_of_nonneg_of_unbounded w hL hR d.1⟩).elim
  refine ⟨l.1, r.1, ds.map Prod.fst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hnd.map_on
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
      exact ⟨(e, true), (hmem (e, true)).2 ⟨rfl, he⟩, rfl⟩
  · rw [List.isChain_map]
    apply hchain.imp_of_mem_imp
    intro d e hd he hde
    have dd : (d.1, true) = d := Prod.ext rfl ((hmem d).1 hd).1.symm
    have ee : (e.1, true) = e := Prod.ext rfl ((hmem e).1 he).1.symm
    rw [dd, ee]
    exact hde
  · rw [ll]
    exact outgoing _ hprev
  · rw [rr]
    exact outgoing _ hnext

/-- Incoming edges in left-to-right order: counterclockwise rotation from
the end of the outgoing block. The source has no incoming edges -/
@[expose] noncomputable def kmswIncomingEdgesLeftToRight
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) : List ℕ :=
  if h : v = 0 then [] else
    (kmsw_nonzero_incoming_enumeration w hfin hL hR v
      (kmsw_vertex_allocated_of_finite_incidence w hfin v) h).choose_spec.choose_spec.choose

/-- Membership in the incoming order is exactly incoming present incidence,
including the empty source case (`def-uiqbot`, -/
theorem mem_kmswIncomingEdgesLeftToRight
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v e : ℕ) :
    e ∈ kmswIncomingEdgesLeftToRight w hfin hL hR v ↔
      EdgePresent w e ∧ edgeEast w e = v := by
  classical
  unfold kmswIncomingEdgesLeftToRight
  split
  · rename_i h
    subst v
    constructor
    · intro he; exact (List.not_mem_nil he).elim
    · rintro ⟨hp, he⟩
      exact (zero_no_incoming_present_edge w hL e hp he).elim
  · rename_i h
    exact (kmsw_nonzero_incoming_enumeration w hfin hL hR v
      (kmsw_vertex_allocated_of_finite_incidence w hfin v) h).choose_spec.choose_spec.choose_spec.2.2.2.1 e

/-- The incoming order has no repetitions and consecutive entries are related
by the actual vertex rotation (`lem-geo-exist`, -/
theorem kmswIncomingEdgesLeftToRight_rotation
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    (kmswIncomingEdgesLeftToRight w hfin hL hR v).Nodup ∧
    (kmswIncomingEdgesLeftToRight w hfin hL hR v).IsChain
      (fun e f => kmswInfRot w hfin (e, true) = (f, true)) := by
  classical
  unfold kmswIncomingEdgesLeftToRight
  split
  · exact ⟨List.nodup_nil, List.IsChain.nil⟩
  · rename_i h
    have hs := (kmsw_nonzero_incoming_enumeration w hfin hL hR v
      (kmsw_vertex_allocated_of_finite_incidence w hfin v) h).choose_spec.choose_spec.choose_spec
    exact ⟨hs.1, hs.2.2.2.2.1⟩

/-- Both ends of the chosen incoming order are anchored by outgoing
neighbours, so its cut is a direction transition, not an edge-ID choice -/
theorem kmswIncomingEdgesLeftToRight_endpoints
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hne : v ≠ 0) :
    ∃ l r : ℕ,
      (kmswIncomingEdgesLeftToRight w hfin hL hR v).head? = some l ∧
      (kmswIncomingEdgesLeftToRight w hfin hL hR v).getLast? = some r ∧
      ((kmswInfRot w hfin).symm (l, true)).2 = false ∧
      (kmswInfRot w hfin (r, true)).2 = false := by
  classical
  unfold kmswIncomingEdgesLeftToRight
  rw [dite_eq_right hne]
  let H := kmsw_nonzero_incoming_enumeration w hfin hL hR v
    (kmsw_vertex_allocated_of_finite_incidence w hfin v) hne
  have hs := H.choose_spec.choose_spec.choose_spec
  exact ⟨H.choose, H.choose_spec.choose, hs.2.1, hs.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩

/-- The edge at index `n` arrives at the vertex after `n + 1` edges -/
theorem InfinitePresentPath.edge_incoming_at_succ {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ) :
    EdgePresent w (P.edge n) ∧ edgeEast w (P.edge n) = (P.initial (n + 1)).1.id := by
  refine ⟨(P.edge_outgoing n).1, ?_⟩
  have ht := pathEdgeList_endpoint (P.initial (n + 1)).2
  rw [P.prefix_edges, List.ofFn_succ'] at ht
  simpa only [geodesicPrefixEnd, List.concat_eq_append, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.elim_some, Fin.val_last] using ht

/-- The edge at index `n` departs from the vertex after `n` edges -/
theorem InfinitePresentPath.edge_outgoing_at_initial {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ) :
    EdgePresent w (P.edge n) ∧ edgeWest w (P.edge n) = (P.initial n).1.id := by
  obtain ⟨hp, he⟩ := P.edge_outgoing n
  refine ⟨hp, he.trans ?_⟩
  rw [← P.prefix_edges]
  exact pathEdgeList_endpoint (P.initial n).2

/-- The incoming dart used in a later shared-vertex comparison belongs to
the actual incoming rotation order (`def-infinite-geo`, -/
theorem InfinitePresentPath.incoming_mem_rotation_order
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ) (hn : 0 < n) :
    P.edge (n - 1) ∈ kmswIncomingEdgesLeftToRight w hfin hL hR (P.initial n).1.id := by
  apply (mem_kmswIncomingEdgesLeftToRight w hfin hL hR _ _).2
  have he := P.edge_incoming_at_succ w (n - 1)
  simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using he

variable (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- Compare the outgoing darts of two paths at a common vertex. The indices
may differ, and the initial departure is included. The order is the anchored
rotation order, retaining edge IDs (`def-infinite-geo`, -/
@[expose] def SharedDepartureWeaklyRight {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (m n : ℕ) : Prop :=
  (P.initial m).1 = (Q.initial n).1 ∧
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin m => P.edge i.val))).idxOf (P.edge m) ≤
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin m => P.edge i.val))).idxOf (Q.edge n)

/-- Compare the incoming darts at a later common vertex. Positivity excludes
the nonexistent incoming edge at the start; the incoming block is traversed
counterclockwise from left to right (`def-infinite-geo`, -/
@[expose] def SharedArrivalWeaklyRight {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ (P.initial m).1 = (Q.initial n).1 ∧
    (kmswIncomingEdgesLeftToRight w hfin hL hR (P.initial m).1.id).idxOf
      (P.edge (m - 1)) ≤
    (kmswIncomingEdgesLeftToRight w hfin hL hR (P.initial m).1.id).idxOf
      (Q.edge (n - 1))

/-- The local side of a competitor at a later shared vertex is determined by
both its incoming and its outgoing position in the two rotation intervals.
This predicate records weakly right on both sides of the vertex; it does not
assert submap containment (`def-infinite-geo`, -/
@[expose] def SharedVertexWeaklyRight {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (m n : ℕ) : Prop :=
  SharedArrivalWeaklyRight w hfin hL hR P Q m n ∧
    SharedDepartureWeaklyRight w hfin hL htrans hR P Q m n

private theorem pathEdgeList_head {w : ℕ → Fin 3} {u z : PresentVertex w}
    (p : Path u z) (e : ℕ) (he : (pathEdgeList p).head? = some e) :
    edgeWest w e = u.id := by
  induction p with
  | nil => simp only [pathEdgeList, List.head?_nil, reduceCtorEq] at he
  | @cons y z p f ih =>
    cases hp : pathEdgeList p with
    | nil =>
      have hz : u = y := p.eq_of_length_zero (by rw [← pathEdgeList_length, hp]; rfl)
      have hfe : f.val = e := by
        simpa only [pathEdgeList, hp, List.nil_append, List.head?_cons,
          Option.some.injEq] using he
      rw [← hfe]
      exact f.property.2.1.trans (congrArg PresentVertex.id hz.symm)
    | cons g gs =>
      have hge : g = e := by
        simpa only [pathEdgeList, hp, List.cons_append, List.head?_cons,
          Option.some.injEq] using he
      apply ih
      rw [hp, List.head?_cons, hge]

/-- Every stored prefix of an infinite LDP geodesic is itself longest,
including the empty prefix (`def-infinite-geo`, -/
theorem InfinitePresentPath.initial_isLongest {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) (n : ℕ) :
    IsLongest (P.initial n).2 := by
  cases n with
  | zero =>
    have hempty {u z : PresentVertex w} (p : Path u z) (hp : p.length = 0) :
        IsLongest p := by
      have hz := p.eq_of_length_zero hp
      subst z
      intro q
      rw [hp, presentVertex_acyclic w u q]
    exact hempty _ (P.prefix_length 0)
  | succ n =>
    obtain ⟨z, q, hlen, he, hq⟩ := hP 1 (n + 1) le_rfl (by omega)
    have hs : edgeWest w (P.edge 0) = z.id := by
      apply pathEdgeList_head q
      rw [he, Nat.sub_self, List.drop_zero, List.ofFn_succ, List.head?_cons]
      rfl
    have hz : z = (⟨v⟩ : PresentVertex w) := by
      have hi : z.id = v := hs.symm.trans (InfinitePresentPath.first_edge_outgoing w P).2
      cases z
      exact congrArg (fun t : ℕ => (⟨t⟩ : PresentVertex w)) hi
    subst z
    apply hq.of_length_eq
    rw [P.prefix_length]
    omega

/-- Two infinite LDP geodesics from the same start reach any shared vertex
at the same index, since both prefixes maximize length -/
theorem InfinitePresentPath.index_eq_of_initial_eq {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments)
    (hQ : Q.HasLongestSegments) (m n : ℕ)
    (hs : (P.initial m).1 = (Q.initial n).1) : m = n := by
  have hlen {z t : PresentVertex w} (p : Path (⟨v⟩ : PresentVertex w) z)
      (q : Path (⟨v⟩ : PresentVertex w) t) (hp : IsLongest p) (hq : IsLongest q)
      (hzt : z = t) : p.length = q.length := by
    subst t
    exact Nat.le_antisymm (hq p) (hp q)
  have he := hlen (P.initial m).2 (Q.initial n).2
    (P.initial_isLongest w hP m) (Q.initial_isLongest w hQ n) hs
  simpa only [P.prefix_length, Q.prefix_length] using he

private theorem spliced_prefix_exists {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments)
    (hQ : Q.HasLongestSegments) (n : ℕ)
    (hs : (P.initial n).1 = (Q.initial n).1) (b : ℕ) :
    ∃ z, ∃ p : Path (⟨v⟩ : PresentVertex w) z,
      p.length = b ∧
      pathEdgeList p = List.ofFn (fun i : Fin b =>
        if i.val < n then P.edge i.val else Q.edge i.val) ∧ IsLongest p := by
  by_cases hb : b ≤ n
  · refine ⟨_, (P.initial b).2, P.prefix_length b, ?_, P.initial_isLongest w hP b⟩
    rw [P.prefix_edges]
    apply congrArg List.ofFn
    funext i
    rw [ite_eq_left (by have := i.isLt; omega)]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show n ≤ b by omega)
    obtain ⟨z, p, q, hpq, hp⟩ := (Q.initial (n + k)).2.exists_eq_comp_of_le_length
      (show n ≤ (Q.initial (n + k)).2.length by rw [Q.prefix_length]; omega)
    have hlist : pathEdgeList p ++ pathEdgeList q =
        List.ofFn (fun i : Fin n => Q.edge i.val) ++
        List.ofFn (fun i : Fin k => Q.edge (n + i.val)) := by
      rw [← pathEdgeList_comp, ← hpq, Q.prefix_edges, List.ofFn_add]
      rfl
    have hpfx := List.append_inj_left hlist
      (by rw [pathEdgeList_length, hp, List.length_ofFn])
    have hqs := List.append_inj_right hlist
      (by rw [pathEdgeList_length, hp, List.length_ofFn])
    have hz : z = (Q.initial n).1 := by
      have he := pathEdgeList_endpoint p
      rw [hpfx] at he
      have hqe := pathEdgeList_endpoint (Q.initial n).2
      rw [Q.prefix_edges] at hqe
      exact congrArg (fun t : ℕ => (⟨t⟩ : PresentVertex w)) (he.symm.trans hqe)
    have hPz : (P.initial n).1 = z := hs.trans hz.symm
    cases hPz
    refine ⟨_, (P.initial n).2.comp q, ?_, ?_, ?_⟩
    · have hlen := Q.prefix_length (n + k)
      rw [hpq, Path.length_comp, hp] at hlen
      rw [Path.length_comp, P.prefix_length]
      exact hlen
    · rw [pathEdgeList_comp, P.prefix_edges, hqs, List.ofFn_add]
      congr 1
      · apply congrArg List.ofFn
        funext i
        simp only [Fin.val_castLE, ite_eq_left i.isLt]
      · apply congrArg List.ofFn
        funext i
        simp only [Fin.val_natAdd, ite_eq_right (show ¬n + i.val < n by omega)]
    · have hopt := Q.initial_isLongest w hQ (n + k)
      rw [hpq] at hopt
      apply hopt.of_length_eq
      rw [Path.length_comp, Path.length_comp, P.prefix_length, hp]

/-- Splicing two infinite LDP geodesics from the same start at a shared
vertex preserves all longest-segment conditions. This is an equal-length
prefix replacement, requiring no planar separation premise -/
theorem InfinitePresentPath.exists_geodesic_splice {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments)
    (hQ : Q.HasLongestSegments) (n : ℕ)
    (hs : (P.initial n).1 = (Q.initial n).1) :
    ∃ S : InfinitePresentPath w ⟨v⟩, S.HasLongestSegments ∧
      ∀ i, S.edge i = if i < n then P.edge i else Q.edge i := by
  classical
  let H := spliced_prefix_exists w P Q hP hQ n hs
  let S : InfinitePresentPath w ⟨v⟩ := {
    edge := fun i => if i < n then P.edge i else Q.edge i
    initial := fun b => ⟨(H b).choose, (H b).choose_spec.choose⟩
    prefix_length := fun b => (H b).choose_spec.choose_spec.1
    prefix_edges := fun b => (H b).choose_spec.choose_spec.2.1 }
  have hlong (b : ℕ) : IsLongest (S.initial b).2 := (H b).choose_spec.choose_spec.2.2
  refine ⟨S, ?_, fun _ => rfl⟩
  intro a b ha hab
  obtain ⟨z, p, q, hpq, hp⟩ := (S.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (S.initial b).2.length by rw [S.prefix_length]; omega)
  refine ⟨z, q, ?_, ?_, ?_⟩
  · have hlen := S.prefix_length b
    rw [hpq, Path.length_comp, hp] at hlen
    omega
  · rw [← S.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := hlong b
    rw [hpq] at hopt
    exact hopt.of_comp_right

/-- Every shared departure, including the start and all rejoins, is compared
in the geometric outgoing order. This is an edge-order predicate, separate
from submap containment (`def-infinite-geo`, -/
@[expose] def GeodesicSharedDeparturesRightOf (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩) : Prop :=
  ∀ m n, (P.initial m).1 = (Q.initial n).1 →
    SharedDepartureWeaklyRight w hfin hL htrans hR P Q m n

/-- Every infinite LDP geodesic departs weakly right of the constructed path
at every shared vertex. Prefix splicing upgrades first-divergence minimality
without a Jordan-curve assumption. Submap containment is not asserted -/
theorem kmswLeftmostLdpPath_sharedDeparturesRightOf (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (Q : InfinitePresentPath w ⟨v⟩) (hQ : Q.HasLongestSegments) :
    GeodesicSharedDeparturesRightOf w hfin hL htrans hR v
      (kmswLeftmostLdpPath w hfin hL htrans hR v hg) Q := by
  let P := kmswLeftmostLdpPath w hfin hL htrans hR v hg
  have hP := kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR v hg
  intro m n hs
  have hmn := P.index_eq_of_initial_eq w Q hP hQ m n hs
  subst n
  obtain ⟨S, hS, he⟩ := P.exists_geodesic_splice w Q hP hQ m hs
  have hmin := kmswLeftmostLdpPath_firstDivergenceRightOf w hfin hL htrans hR
    v hg S hS m (by
      intro i hi
      rw [he i, ite_eq_left hi])
  rw [he m, ite_eq_right (Nat.lt_irrefl m)] at hmin
  exact ⟨hs, hmin⟩

/-- Comparison at every shared departure includes first-divergence comparison -/
theorem GeodesicSharedDeparturesRightOf.firstDivergence (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩)
    (h : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v P Q) :
    GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q := by
  intro n hn
  have hpfx : List.ofFn (fun i : Fin n => P.edge i.val) =
      List.ofFn (fun i : Fin n => Q.edge i.val) := by
    apply congrArg List.ofFn
    funext i
    exact hn i.val i.isLt
  exact (h n n (P.initial_vertex_eq_of_prefix_eq Q n hpfx)).2

/-- Mutual comparison at all shared departures forces equality of edge
streams, including parallel-edge identities (`def-infinite-geo`, -/
theorem GeodesicSharedDeparturesRightOf.antisymm (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩)
    (hPQ : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v P Q)
    (hQP : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v Q P) :
    P.edge = Q.edge := by
  exact GeodesicFirstDivergenceRightOf.antisymm w hfin hL htrans hR v P Q
    (GeodesicSharedDeparturesRightOf.firstDivergence w hfin hL htrans hR v P Q hPQ)
    (GeodesicSharedDeparturesRightOf.firstDivergence w hfin hL htrans hR v Q P hQP)

/-- Simultaneously from every start, almost surely there is an infinite LDP
geodesic with every competitor weakly right at every shared departure. Its
edge stream is unique with this property. The submap-containment clause of
`def-infinite-geo` remains a separate planar separation obligation -/
theorem pitmanCodes_ae_exists_unique_sharedDepartureLeftmostLdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
          (∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
            GeodesicSharedDeparturesRightOf w hf hL ht hR v P Q) ∧
          ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
            (∀ S : InfinitePresentPath w ⟨v⟩, S.HasLongestSegments →
              GeodesicSharedDeparturesRightOf w hf hL ht hR v Q S) → Q.edge = P.edge := by
  filter_upwards [pitmanCodes_ae_exists_unique_firstDivergenceLeftmostLdp] with ω h
  obtain ⟨hf, hL, ht, hR, hall⟩ := h
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  obtain ⟨P₀, hP₀, _⟩ := hall v
  have hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments := ⟨P₀, hP₀⟩
  let P := kmswLeftmostLdpPath w hf hL ht hR v hg
  have hP : P.HasLongestSegments := kmswLeftmostLdpPath_hasLongestSegments w hf hL ht hR v hg
  refine ⟨P, hP, kmswLeftmostLdpPath_sharedDeparturesRightOf w hf hL ht hR v hg, ?_⟩
  intro Q hQ hleft
  exact GeodesicSharedDeparturesRightOf.antisymm w hf hL ht hR v Q P
    (hleft P hP) (kmswLeftmostLdpPath_sharedDeparturesRightOf w hf hL ht hR v hg Q hQ)

end DirectedDistances.KMSW
