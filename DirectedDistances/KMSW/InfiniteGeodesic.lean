module

public import DirectedDistances.KMSW.CutSeparation
public import DirectedDistances.DirectedPath.Bounded
public import DirectedDistances.DirectedPath.Separator
import Mathlib.Data.Fintype.Vector

/-! # Directed paths between KMSW records

Vertices retain their allocation IDs, and arrows retain their edge IDs.
Only edges which are present at an allocated stage are directed arrows. -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver

/-- A vertex ID in the directed graph of present KMSW edges -/
structure PresentVertex (w : ℕ → Fin 3) where
  id : ℕ
  deriving DecidableEq

/-- Presence at an allocated stage of the KMSW construction -/
def EdgePresent (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  ∃ n, e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true

/-- The graph has one arrow for each present edge ID, retaining parallel edges. -/
instance presentVertexQuiver (w : ℕ → Fin 3) : Quiver (PresentVertex w) where
  Hom u v := {e : ℕ // EdgePresent w e ∧ edgeWest w e = u.id ∧ edgeEast w e = v.id}

/-- An allocated present edge remains present forever, so the arrow predicate
agrees with eventual permanent presence (`remark-kmsw-infinite`, -/
theorem EdgePresent.eventually_present {w : ℕ → Fin 3} {e : ℕ} (h : EdgePresent w e) :
    ∃ N, ∀ m, N ≤ m → e < (kmswStage w m).nextEdge ∧
      (kmswStage w m).present e = true := by
  obtain ⟨N, he, hp⟩ := h
  refine ⟨N, fun m hm => ⟨he.trans_le (kmswStage_nextEdge_mono w hm), ?_⟩⟩
  induction m, hm using Nat.le_induction with
  | base => exact hp
  | succ m hm ih =>
    change (kmswStep (kmswStage w m) (w m)).present e = true
    rw [kmswStep_present_existing _ _ (he.trans_le (kmswStage_nextEdge_mono w hm))]
    split
    · rfl
    · exact ih

private theorem allocated_by_self (w : ℕ → Fin 3) (e : ℕ) :
    e < (kmswStage w e).nextEdge := by
  have := CutConverse.allocation_count w e
  omega

private theorem path_eventual_rank {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) : ∃ N, ∀ m, N ≤ m →
      kmswStageRank w m u.id ≤ kmswStageRank w m v.id ∧
      (0 < p.length → kmswStageRank w m u.id < kmswStageRank w m v.id) := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨le_refl _, by simp⟩⟩
  | @cons v z p e ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max N e.val, fun m hm => ?_⟩
    have he : e.val < (kmswStage w m).nextEdge :=
      (allocated_by_self w e.val).trans_le
        (kmswStage_nextEdge_mono w (by omega : e.val ≤ m))
    have hr := kmswStageRank_strict w m e.val he
    have hends := edge_endpoints_eq w he
    rw [hends.1, hends.2, e.property.2.1, e.property.2.2] at hr
    have hprev := (hN m (by omega)).1
    exact ⟨hprev.trans hr.le, fun _ => hprev.trans_lt hr⟩

/-- Every finite directed cycle in the present-edge graph is empty, by realizing
its finitely many edges at a common stage (`def-infinite-geo`, -/
theorem presentVertex_acyclic (w : ℕ → Fin 3) : acyclic (PresentVertex w) := by
  intro u p
  obtain ⟨N, hN⟩ := path_eventual_rank p
  by_contra hn
  exact (lt_irrefl _) ((hN N le_rfl).2 (Nat.pos_of_ne_zero hn))

/-- The vertex used by the explicit record hypotheses; no renewal times are -/
def recordVertex (w : ℕ → Fin 3) (n : ℕ) : PresentVertex w :=
  ⟨(kmswStage w n).west (act w n)⟩

/-- At time zero the record vertex is the original source -/
theorem recordVertex_zero (w : ℕ → Fin 3) : (recordVertex w 0).id = 0 := rfl

/-- Distinct strict vertical record times have distinct record vertices -/
theorem recordVertex_ne (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hA : ∀ j < n, R w n ≤ R w j - 1) : recordVertex w m ≠ recordVertex w n := by
  intro h
  apply activeInitial_ne_of_right_record w n hA m hmn
  rw [CutConverse.activeInitial_eq, CutConverse.activeInitial_eq]
  exact congrArg PresentVertex.id h

private theorem lr_present (w : ℕ → Fin 3) (n : ℕ) {e : ℕ}
    (he : e ∈ (kmswStage w n).LR) : EdgePresent w e := by
  refine ⟨n, ?_, (kmswStage_status w n).2.2.1 e he⟩
  exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append]
    tauto)

private theorem stable_lr_chain (w : ℕ → Fin 3) (n : ℕ) :
    List.IsChain (fun e f => edgeEast w e = edgeWest w f) (kmswStage w n).LR := by
  have hc := (kmswStage_boundary_chain_invariant w n).2.1.right_of_append
  apply hc.imp_of_mem_imp
  intro e f he hf h
  have ends (g) (hg : g ∈ (kmswStage w n).LR) :=
    edge_endpoints_eq w ((kmswStage_boundary_ids_lt_nextEdge w n).2 g (by
      simp only [List.mem_append]
      tauto))
  exact (ends e he).2.symm.trans (h.trans (ends f hf).1)

private theorem chain_reachable_last (w : ℕ → Fin 3) (xs : List ℕ) (f : ℕ)
    (hc : List.IsChain (fun e f => edgeEast w e = edgeWest w f) (xs ++ [f]))
    (hp : ∀ e ∈ xs ++ [f], EdgePresent w e) :
    ∀ e ∈ xs, Reachable (⟨edgeWest w e⟩ : PresentVertex w) ⟨edgeWest w f⟩ := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    have ht := ih hc.tail (fun g hg => hp g (List.mem_cons_of_mem e hg))
    intro g hg
    rcases List.mem_cons.mp hg with hge | hg
    · subst g
      cases es with
      | nil =>
        have hr : edgeEast w e = edgeWest w f := by
          simpa using hc.rel_head? (by simp)
        exact ⟨(Hom.toPath (⟨e, hp e (by simp), rfl, hr⟩ :
          (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeWest w f⟩))⟩
      | cons a as =>
        have hr : edgeEast w e = edgeWest w a := by
          simpa using hc.rel_head? (by simp)
        obtain ⟨p⟩ := ht a (by simp)
        exact ⟨(Hom.toPath (⟨e, hp e (by simp), rfl, hr⟩ :
          (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeWest w a⟩)).comp p⟩
    · exact ht g hg

private theorem lr_record_snoc (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    (kmswStage w n).LR =
      (((List.range n).filter
        (fun m => decide (∀ j, j < m → R w m < R w j))).map (act w)) ++ [act w n] := by
  rw [kmswStage_LR_eq, List.range_succ, List.filter_append, List.map_append]
  have hn : ∀ j, j < n → R w n < R w j := by
    intro j hj
    have := hA j hj
    omega
  simp only [List.filter_cons, decide_eq_true_eq, List.filter_nil]
  rw [ite_eq_left hn]
  rfl

/-- Earlier and later strict vertical record vertices are joined by present LR
edges. Reachability is proved from the actual boundary chain, without any
assumption of an intermediate path (`def-infinite-geo`, -/
theorem recordVertex_reachable (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hAn : ∀ j < n, R w n ≤ R w j - 1) :
    Reachable (recordVertex w m) (recordVertex w n) := by
  let xs := ((List.range n).filter
    (fun t => decide (∀ j, j < t → R w t < R w j))).map (act w)
  have hLR : (kmswStage w n).LR = xs ++ [act w n] := lr_record_snoc w n hAn
  have hm : act w m ∈ xs := by
    apply List.mem_map.mpr
    refine ⟨m, List.mem_filter.mpr ⟨List.mem_range.mpr hmn, ?_⟩, rfl⟩
    apply decide_eq_true
    intro j hj
    have := hAm j hj
    omega
  have hc := stable_lr_chain w n
  rw [hLR] at hc
  have hp : ∀ e ∈ xs ++ [act w n], EdgePresent w e := by
    intro e he
    exact lr_present w n (hLR ▸ he)
  have hr := chain_reachable_last w xs (act w n) hc hp (act w m) hm
  have hem := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl m))).1
  have hen := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl n))).1
  simpa only [recordVertex, ← hem, ← hen] using hr

/-- The allocated vertices strictly before a record, excluding both active -/
def recordBefore (w : ℕ → Fin 3) (n : ℕ) : Set (PresentVertex w) :=
  {u | u.id < (kmswStage w n).nextVertex ∧
    u.id ≠ (recordVertex w n).id ∧ u.id ≠ (kmswStage w n).east (act w n)}

private theorem vertex_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

/-- A present arrow cannot leave the old side without ending at the record -/
theorem presentArrow_no_crossing (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u z : PresentVertex w} (e : u ⟶ z) :
    ¬ (u ∈ recordBefore w n ∧ z ∉ recordBefore w n ∧ z ≠ recordVertex w n) := by
  let m := max n e.val
  have he : e.val < (kmswStage w m).nextEdge :=
    (allocated_by_self w e.val).trans_le (kmswStage_nextEdge_mono w (Nat.le_max_right n e.val))
  have hs := kmswFiniteStage_cutSeparation w n hA hB m
    (Nat.le_max_left n e.val) e.val he
  have hends := edge_endpoints_eq w he
  dsimp only at hs
  rw [hends.1, hends.2, e.property.2.1, e.property.2.2] at hs
  rintro ⟨hu, hz, hneq⟩
  exact hs.1 ⟨hu, hz, fun h => hneq (vertex_ext h)⟩

private theorem path_endpoint_before {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u z : PresentVertex w} (p : Path u z) (hu : u ∈ recordBefore w n)
    (havoid : recordVertex w n ∉ p.vertices) : z ∈ recordBefore w n := by
  induction p with
  | nil => exact hu
  | @cons y z p e ih =>
    have hy : y ∈ recordBefore w n := ih (by
      intro hmem
      exact havoid (Path.mem_vertices_cons p e |>.2 (Or.inl hmem)))
    by_contra hz
    apply presentArrow_no_crossing w n hA hB e
    refine ⟨hy, hz, ?_⟩
    intro heq
    exact havoid (heq ▸ (Path.mem_vertices_cons p e |>.2 (Or.inr rfl)))

private theorem path_to_record_confined {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u : PresentVertex w} (hu : u ∈ recordBefore w n)
    (p : Path u (recordVertex w n)) :
    ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} := by
  intro z hz
  by_cases heq : z = recordVertex w n
  · exact Or.inr heq
  · left
    obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices hz
    apply path_endpoint_before hA hB p₁ hu
    intro hv
    obtain ⟨q₁, q₂, _⟩ := p₁.exists_eq_comp_of_mem_vertices hv
    have hcycle := presentVertex_acyclic w _ (q₂.comp p₂)
    rw [Path.length_comp] at hcycle
    have hq₂ : q₂.length = 0 := by omega
    exact heq (q₂.eq_of_length_zero hq₂).symm

private theorem earlier_record_before (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAn : ∀ j < n, R w n ≤ R w j - 1) : recordVertex w m ∈ recordBefore w n := by
  have hbound := (kmswStage_endpoints_lt_nextVertex w n (act w m)
    (act_lt_nextEdge w hmn.le)).1
  have hends := (edge_endpoints_eq w (act_lt_nextEdge w hmn.le)).1
  rw [hends, ← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl m))).1] at hbound
  refine ⟨hbound, ?_, ?_⟩
  · intro heq
    exact recordVertex_ne w hmn hAn (vertex_ext heq)
  · intro heq
    apply activeEast_ne_activeInitial w hmn.le
    rw [CutConverse.activeInitial_eq]
    exact heq.symm

/-- Every path between successive (or any two ordered) record vertices stays
on the finite old side of the later record (`def-infinite-geo`, -/
theorem recordVertex_path_confined (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    (hBn : ∀ j, n ≤ j → L w n ≤ L w j)
    (p : Path (recordVertex w m) (recordVertex w n)) :
    ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} :=
  path_to_record_confined hAn hBn (earlier_record_before w hmn hAn) p

private theorem record_region_finite (w : ℕ → Fin 3) (n : ℕ) :
    (recordBefore w n ∪ {recordVertex w n}).Finite := by
  apply Set.Finite.union _ (Set.finite_singleton _)
  apply Set.Finite.subset (Set.finite_range
    (fun i : Fin (kmswStage w n).nextVertex => (⟨i.val⟩ : PresentVertex w)))
  intro u hu
  exact ⟨⟨u.id, hu.1⟩, vertex_ext rfl⟩

/-- Both extremal paths exist between ordered records. The longest-path
argument uses proved confinement and acyclicity; LR proves reachability -/
theorem recordVertex_exists_extremal (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    (hBn : ∀ j, n ≤ j → L w n ≤ L w j) :
    (∃ p : Path (recordVertex w m) (recordVertex w n), IsLongest p) ∧
    (∃ p : Path (recordVertex w m) (recordVertex w n), IsShortest p) := by
  have hr := recordVertex_reachable w hmn hAm hAn
  exact ⟨exists_isLongest_of_finite_vertex_confinement (presentVertex_acyclic w)
    _ (record_region_finite w n) (recordVertex_path_confined w hmn hAn hBn) hr,
    exists_isShortest hr⟩

private theorem lr_increasing (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).LR, edgeWest w e < edgeEast w e := by
  induction n with
  | zero =>
    intro e he
    have heq : e = 0 := by simpa only [kmswStage, kmswInit, List.mem_singleton] using he
    subst e
    simp only [edgeWest, edgeEast, kmswStage, kmswInit]
    omega
  | succ n ih =>
    intro e he
    by_cases hold : e ∈ (kmswStage w n).LR
    · exact ih e hold
    · have hnew : e = (kmswStage w n).nextEdge ∧
          w n = 2 ∧ (kmswStage w n).UR = [] := by
        unfold kmswStage kmswStep kmswCodeStep at he
        split at he
        · cases hs : (kmswStage w n).UL.dropLast.reverse <;>
            simp [kmswStepOfStep, hs, State.addEdge] at he
          all_goals exact (hold he).elim
        · split at he
          · exact (hold he).elim
          · rename_i h0 h1
            have hw : w n = 2 := by
              apply Fin.ext
              have hlt := (w n).isLt
              have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
              have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
              omega
            cases hs : (kmswStage w n).UR with
            | nil =>
              simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
                List.mem_singleton] at he
              exact ⟨he.resolve_left hold, hw, rfl⟩
            | cons f fs =>
              simp only [kmswStepOfStep, hs] at he
              exact (hold he).elim
      obtain ⟨rfl, hw, hUR⟩ := hnew
      have hbound := (kmswStage_endpoints_lt_nextVertex w n (act w n)
        (act_lt_nextEdge w le_rfl)).2
      have healloc : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
        simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hUR, State.addEdge]
      have hends := edge_endpoints_eq w healloc
      rw [← hends.1, ← hends.2]
      simpa [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hUR,
        State.addEdge, act] using hbound

private theorem increasing_chain_last (w : ℕ → Fin 3) (xs : List ℕ) (f : ℕ)
    (hc : List.IsChain (fun e f => edgeEast w e = edgeWest w f) (xs ++ [f]))
    (hp : ∀ e ∈ xs ++ [f], edgeWest w e < edgeEast w e) :
    ∀ e ∈ xs, edgeEast w e ≤ edgeWest w f := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    have ht := ih hc.tail (fun g hg => hp g (List.mem_cons_of_mem e hg))
    intro g hg
    rcases List.mem_cons.mp hg with hge | hg
    · subst g
      cases es with
      | nil =>
        have hr : edgeEast w e = edgeWest w f := by
          simpa using hc.rel_head? (by simp)
        exact hr.le
      | cons a as =>
        have hr : edgeEast w e = edgeWest w a := by
          simpa using hc.rel_head? (by simp)
        exact hr.le.trans ((hp a (by simp)).le.trans (ht a (by simp)))
    · exact ht g hg

private theorem record_east_successor (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    (kmswStage w n).east (act w n) + 1 = (kmswStage w n).nextVertex := by
  cases n with
  | zero => rfl
  | succ n =>
    have hstep : R w (n + 1) = R w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
    have hw : w n = 2 := by
      have ha := hA n (by omega)
      rw [hstep] at ha
      by_cases h0 : w n = 0
      · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at ha
        omega
      · by_cases h1 : w n = 1
        · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at ha
          omega
        · apply Fin.ext
          have hlt := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
    have hUR : (kmswStage w n).UR = [] := by
      obtain ⟨i, hi, hmin⟩ := runningMin_attained (R w) n
      have ha := hA i (by omega)
      have hle := runningMin_le (R w) n n le_rfl
      have hlen := kmswStage_UR_length w n
      rw [hstep, hw, RandomWalk.lazyTwoDimensionalStep_two] at ha
      change minR w n = R w i at hmin
      change minR w n ≤ R w n at hle
      have hz : (kmswStage w n).UR.length = 0 := by omega
      exact List.length_eq_zero_iff.mp hz
    simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hUR,
      State.addEdge, act]

private theorem later_record_not_before (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hAn : ∀ j < n, R w n ≤ R w j - 1) : recordVertex w n ∉ recordBefore w m := by
  let xs := ((List.range n).filter
    (fun t => decide (∀ j, j < t → R w t < R w j))).map (act w)
  have hLR : (kmswStage w n).LR = xs ++ [act w n] := lr_record_snoc w n hAn
  have hm : act w m ∈ xs := by
    apply List.mem_map.mpr
    refine ⟨m, List.mem_filter.mpr ⟨List.mem_range.mpr hmn, ?_⟩, rfl⟩
    apply decide_eq_true
    intro j hj
    have := hAm j hj
    omega
  have hc := stable_lr_chain w n
  rw [hLR] at hc
  have hp : ∀ e ∈ xs ++ [act w n], edgeWest w e < edgeEast w e := by
    intro e he
    exact lr_increasing w n e (hLR ▸ he)
  have hle := increasing_chain_last w xs (act w n) hc hp (act w m) hm
  rw [← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl m))).2,
    ← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl n))).1] at hle
  have ha := record_east_successor w m hAm
  rintro ⟨hlt, _, hne⟩
  dsimp only [recordVertex] at hlt hne
  omega

/-- Every path across three ordered records contains the middle record vertex.
The separation premise is proved from the literal coordinate barriers -/
theorem recordVertex_mem_path (w : ℕ → Fin 3) {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hAb : ∀ j < b, R w b ≤ R w j - 1)
    (hBb : ∀ j, b ≤ j → L w b ≤ L w j)
    (hAc : ∀ j < c, R w c ≤ R w j - 1)
    (p : Path (recordVertex w a) (recordVertex w c)) :
    recordVertex w b ∈ p.vertices := by
  by_contra hmiss
  exact later_record_not_before w hbc hAb hAc
    (path_endpoint_before hAb hBb p (earlier_record_before w hab hAb) hmiss)

/-! The sector argument is reproduced locally because its helpers in -/
namespace GeodesicSector

private theorem record_forces_pendant (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) (hn : 0 < n) :
    w (n - 1) = 2 ∧ (kmswStage w (n - 1)).UR = [] := by
  let k := n - 1
  have hnk : n = k + 1 := by dsimp [k]; omega
  have hpast (j : ℕ) (hj : j < n) : R w n ≤ R w j - 1 := hA j hj
  have hR : R w (k + 1) = R w k + (RandomWalk.lazyTwoDimensionalStep (w k)).2 :=
    Finset.sum_range_succ _ _
  have hdown : w k = 2 := by
    have hstrict := hpast k (by omega)
    rw [hnk, hR] at hstrict
    by_cases h2 : (w k).val = 2
    · exact Fin.ext h2
    · have hval : (w k).val = 0 ∨ (w k).val = 1 := by
        have hlt := (w k).isLt
        omega
      rcases hval with h0 | h1
      · have hc : w k = 0 := Fin.ext h0
        rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hstrict
        omega
      · have hc : w k = 1 := Fin.ext h1
        rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstrict
        omega
  have hRstep : R w (k + 1) = R w k - 1 := by
    rw [hR, hdown, RandomWalk.lazyTwoDimensionalStep_two]
    ring
  have hmin : minR w k = R w k := by
    obtain ⟨i, hik, hmin⟩ := runningMin_attained (R w) k
    change minR w k = R w i at hmin
    have hlow : R w k ≤ R w i := by
      have hi := hpast i (by omega)
      rw [hnk, hRstep] at hi
      omega
    have hle := runningMin_le (R w) k k (le_refl k)
    change minR w k ≤ R w k at hle
    omega
  have hlen := kmswStage_UR_length w k
  have hURlen : ((kmswStage w k).UR.length : ℤ) = 0 := by
    rw [hlen, hmin]
    ring
  have hUR : (kmswStage w k).UR.length = 0 := by omega
  simpa [k] using And.intro hdown (List.length_eq_zero_iff.mp hUR)

private theorem minL_frozen (w : ℕ → Fin 3) (n : ℕ)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) {m : ℕ} (hnm : n ≤ m) :
    minL w m = minL w n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    change min (minL w m) (L w (m + 1)) = minL w n
    rw [ih]
    have hmin := runningMin_le (L w) n n (le_refl n)
    change minL w n ≤ L w n at hmin
    have hfuture := hB (m + 1) (by omega)
    exact min_eq_left (hmin.trans hfuture)

private theorem left_step_increases_UL_lower_bound (w : ℕ → Fin 3) (n m : ℕ)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) (hnm : n ≤ m)
    (hleft : w m = 0) :
    (kmswStage w m).UL.length > (kmswStage w n).UL.length := by
  have hLnext := hB (m + 1) (by omega)
  have hLs : L w (m + 1) = L w m - 1 := by
    rw [show L w (m + 1) = L w m + (RandomWalk.lazyTwoDimensionalStep (w m)).1 from
      Finset.sum_range_succ _ _]
    rw [hleft, RandomWalk.lazyTwoDimensionalStep_zero]
    ring
  have hLfrozen := minL_frozen w n hB hnm
  have hM := minL_frozen w n hB (by omega : n ≤ m + 1)
  have hlenN := kmswStage_UL_length w n
  have hlenM := kmswStage_UL_length w m
  have hstepL : L w m ≥ L w n + 1 := by omega
  rw [hLfrozen] at hlenM
  have hcast : ((kmswStage w m).UL.length : ℤ) >
      ((kmswStage w n).UL.length : ℤ) := by
    rw [hlenM, hlenN]
    omega
  omega

private def sectorPoint (v a x : ℕ) : Prop := x = v ∨ a ≤ x

private def sectorEdge (w : ℕ → Fin 3) (v a e : ℕ) : Prop :=
  sectorPoint v a (edgeWest w e) ∧ sectorPoint v a (edgeEast w e)

private theorem sectorEdge_of_stage (w : ℕ → Fin 3) (v a m e : ℕ)
    (he : e < (kmswStage w m).nextEdge)
    (hw : sectorPoint v a ((kmswStage w m).west e))
    (hh : sectorPoint v a ((kmswStage w m).east e)) :
    sectorEdge w v a e := by
  rcases edge_endpoints_eq w he with ⟨hW, hE⟩
  constructor
  · rw [← hW]
    exact hw
  · rw [← hE]
    exact hh

private theorem sectorEdge_at_stage (w : ℕ → Fin 3) (v a m e : ℕ)
    (he : e < (kmswStage w m).nextEdge) (h : sectorEdge w v a e) :
    sectorPoint v a ((kmswStage w m).west e) ∧
      sectorPoint v a ((kmswStage w m).east e) := by
  rcases edge_endpoints_eq w he with ⟨hW, hE⟩
  exact ⟨hW ▸ h.1, hE ▸ h.2⟩

private theorem left_predecessor_suffix (p q : List ℕ) (e : ℕ)
    (es : List ℕ) (x : ℕ) (hq : 2 ≤ q.length) (hqne : q ≠ [])
    (hstack : (p ++ q).dropLast.reverse = e :: es) :
    ∃ r, q = r ++ [e, q.getLast hqne] ∧ es.reverse ++ [x] = p ++ r ++ [x] := by
  have hqdropne : q.dropLast ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_dropLast, List.length_nil] at hlen
    omega
  let r := q.dropLast.dropLast
  let e' := q.dropLast.getLast hqdropne
  let last := q.getLast hqne
  have hqdrop : q.dropLast = r ++ [e'] := by
    simpa [r, e'] using (List.dropLast_append_getLast hqdropne).symm
  have hqeq : q = r ++ [e', last] := by
    calc
      q = q.dropLast ++ [last] := (List.dropLast_append_getLast hqne).symm
      _ = r ++ [e', last] := by rw [hqdrop]; simp [List.append_assoc]
  have hform : (p ++ q).dropLast.reverse = e' :: (r.reverse ++ p.reverse) := by
    rw [hqeq]
    simp
  have heq : e = e' := (List.cons.inj (hstack.symm.trans hform)).1
  have hes : es = r.reverse ++ p.reverse := (List.cons.inj (hstack.symm.trans hform)).2
  refine ⟨r, ?_, ?_⟩
  · simpa [heq] using hqeq
  · rw [hes]
    simp [List.reverse_append, List.append_assoc]

private theorem dropLast_append_suffix {α : Type} (p q : List α) (hq : q ≠ []) :
    (p ++ q).dropLast = p ++ q.dropLast := by
  rw [← List.dropLast_append_getLast hq]
  simp

private theorem sector_stage_invariant (w : ℕ → Fin 3) (n v a : ℕ)
    (p : List ℕ) (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (ha0 : a + 1 = (kmswStage w n).nextVertex)
    (hUL0 : (kmswStage w n).UL = p ++ [act w n])
    (hUR0 : (kmswStage w n).UR = [])
    (hact0 : sectorEdge w v a (act w n)) :
    ∀ m, n ≤ m → ∃ q,
      (kmswStage w m).UL = p ++ q ∧ q ≠ [] ∧
      (∀ e ∈ q, sectorEdge w v a e) ∧
      (∀ e ∈ (kmswStage w m).UR, sectorEdge w v a e) ∧
      sectorEdge w v a (act w m) ∧
      (∀ e, (kmswStage w n).nextEdge ≤ e → e < (kmswStage w m).nextEdge →
        sectorEdge w v a e) := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base =>
    refine ⟨[act w n], ?_, by simp, ?_, ?_, hact0, ?_⟩
    · simpa using hUL0
    · intro e he
      simp only [List.mem_singleton] at he
      simpa [he] using hact0
    · simp [hUR0]
    · intro e helo hehi
      omega
  | succ j hj ih =>
    obtain ⟨q, hUL, hqne, hqgood, hURgood, hactgood, hcreated⟩ := ih
    let s := kmswStage w j
    have hULs : s.UL = p ++ q := by simpa [s] using hUL
    have hvertex : a ≤ s.nextVertex := by
      have hmono := CutConverse.nextVertex_mono w hj
      have hbase : a ≤ (kmswStage w n).nextVertex := by omega
      dsimp [s]
      exact hbase.trans hmono
    have hactStage : sectorPoint v a (s.west s.active) ∧
        sectorPoint v a (s.east s.active) := by
      have hh := sectorEdge_at_stage w v a j (act w j)
        (act_lt_nextEdge w (le_refl j)) hactgood
      simpa [s, act] using hh
    have hcodes : w j = 0 ∨ w j = 1 ∨ w j = 2 := by
      have hv := (w j).isLt
      by_cases h0 : (w j).val = 0
      · exact Or.inl (Fin.ext h0)
      · by_cases h1 : (w j).val = 1
        · exact Or.inr (Or.inl (Fin.ext h1))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hcodes with hleft | hup | hdown
    ·  
      have hgrow := left_step_increases_UL_lower_bound w n j hB hj hleft
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .left := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hleft]
      by_cases hnil : s.UL.dropLast.reverse = []
      · have hlen : (s.UL.length : ℕ) ≤ 1 := by
          have hh := congrArg List.length hnil
          simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hh
          omega
        have hpos : 0 < (kmswStage w n).UL.length :=
          List.length_pos_iff.mpr (kmswStage_UL_nonempty_active_last w n).1
        have hULlen : s.UL.length > (kmswStage w n).UL.length := by
          simpa [s] using hgrow
        omega
      · cases hpred : s.UL.dropLast.reverse with
        | nil => exact (hnil hpred).elim
        | cons e es =>
          have hplen : p.length + 1 = (kmswStage w n).UL.length := by
            rw [hUL0]
            simp
          have hq2 : 2 ≤ q.length := by
            have hlen : s.UL.length = p.length + q.length := by
              rw [hUL]
              simp
            have hULlen : s.UL.length > (kmswStage w n).UL.length := by
              simpa [s] using hgrow
            omega
          obtain ⟨r, hqsplit, hULnext⟩ := left_predecessor_suffix p q e es s.nextEdge hq2 hqne (by
            simpa [s, hUL] using hpred)
          have heUL : e ∈ s.UL := by
            apply List.dropLast_subset _
            apply List.mem_reverse.mp
            rw [hpred]
            simp
          have healloc : e < s.nextEdge := by
            apply (kmswStage_boundary_ids_lt_nextEdge w j).2 e
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inl heUL))
          have hqmem : e ∈ q := by rw [hqsplit]; simp
          have hgoodEStage := sectorEdge_at_stage w v a j e (by simpa [s] using healloc)
            (hqgood e hqmem)
          have hnew : sectorEdge w v a s.nextEdge := by
            apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
            · simp [hNext, kmswStepOfStep, hpred, State.addEdge]
            · simpa [hNext, kmswStepOfStep, hpred, State.addEdge] using hgoodEStage.1
            · simpa [hNext, kmswStepOfStep, hpred, State.addEdge] using
                (hactStage.2)
          have hULnext' : (kmswStage w (j + 1)).UL = p ++ (r ++ [s.nextEdge]) := by
            rw [hNext]
            simpa [kmswStepOfStep, hpred, State.addEdge] using hULnext
          have hnextcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
              f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
            intro f hlo hf
            by_cases hold : f < s.nextEdge
            · exact hcreated f hlo (by simpa [s] using hold)
            · have hf' : f = s.nextEdge := by
                have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 1 := by
                  simp [hNext, kmswStepOfStep, hpred, State.addEdge]
                omega
              subst f
              exact hnew
          refine ⟨r ++ [s.nextEdge], hULnext', by simp, ?_, ?_, ?_, hnextcreated⟩
          · intro f hf
            simp only [List.mem_append, List.mem_singleton] at hf
            rcases hf with hf | hf
            · have hfq : f ∈ q := by
                rw [hqsplit]
                exact List.mem_append_left _ hf
              exact hqgood f hfq
            · subst f
              exact hnew
          · intro f hf
            have hf' : f ∈ s.UR := by
              simpa [hNext, s, kmswStepOfStep, hpred, State.addEdge] using hf
            exact hURgood f (by simpa [s] using hf')
          · simpa [act, hNext, kmswStepOfStep, hpred, State.addEdge] using hnew
    · -- Up steps replace the active edge and prepend the new missing side.
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .up := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hup]
      have hdrop : (p ++ q).dropLast = p ++ q.dropLast := dropLast_append_suffix p q hqne
      have hnew₁ : sectorEdge w v a s.nextEdge := by
        apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
        · simp [hNext, kmswStepOfStep, State.addEdge]
        · simpa [hNext, kmswStepOfStep, State.addEdge] using hactStage.1
        · have hnewv : sectorPoint v a s.nextVertex := by
            unfold sectorPoint
            exact Or.inr hvertex
          simpa [hNext, kmswStepOfStep, State.addEdge] using hnewv
      have hnew₂ : sectorEdge w v a (s.nextEdge + 1) := by
        apply sectorEdge_of_stage w v a (j + 1) (s.nextEdge + 1)
        · simp [hNext, kmswStepOfStep, State.addEdge]
        · have hnewv : sectorPoint v a s.nextVertex := by
            unfold sectorPoint
            exact Or.inr hvertex
          simpa [hNext, kmswStepOfStep, State.addEdge] using hnewv
        · simpa [hNext, kmswStepOfStep, State.addEdge] using hactStage.2
      have hULnext : (kmswStage w (j + 1)).UL = p ++ (q.dropLast ++ [s.nextEdge]) := by
        rw [hNext]
        simp only [kmswStepOfStep]
        rw [hULs]
        simp [hdrop, List.append_assoc]
      have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
          f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
        intro f hlo hf
        by_cases hold : f < s.nextEdge
        · exact hcreated f hlo (by simpa [s] using hold)
        · have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 2 := by
            simp [hNext, kmswStepOfStep, State.addEdge]
          rcases (show f = s.nextEdge ∨ f = s.nextEdge + 1 by omega) with he | he
          · simpa [he] using hnew₁
          · simpa [he] using hnew₂
      refine ⟨q.dropLast ++ [s.nextEdge], hULnext, by simp, ?_, ?_, ?_, hnewcreated⟩
      · intro f hf
        simp only [List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | hf
        · exact hqgood f (List.mem_of_mem_dropLast hf)
        · subst f
          exact hnew₁
      · intro f hf
        simp only [hNext, kmswStepOfStep, List.mem_cons] at hf
        rcases hf with hf | hf
        · subst f
          exact hnew₂
        · exact hURgood f hf
      · simpa [act, hNext, kmswStepOfStep, State.addEdge] using hnew₁
    · -- Down steps either activate UR or create a pendant edge.
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .down := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hdown]
      cases hur : s.UR with
      | nil =>
        have hnew : sectorEdge w v a s.nextEdge := by
          apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
          · simp [hNext, kmswStepOfStep, hur, State.addEdge]
          · simpa [hNext, kmswStepOfStep, hur, State.addEdge] using hactStage.2
          · have hnewv : sectorPoint v a s.nextVertex := by
              unfold sectorPoint
              exact Or.inr hvertex
            simpa [hNext, kmswStepOfStep, hur, State.addEdge] using hnewv
        have hULnext : (kmswStage w (j + 1)).UL = p ++ (q ++ [s.nextEdge]) := by
          rw [hNext]
          simp only [kmswStepOfStep, hur]
          rw [hULs]
          simp [List.append_assoc]
        have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
            f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
          intro f hlo hf
          by_cases hold : f < s.nextEdge
          · exact hcreated f hlo (by simpa [s] using hold)
          · have heq : f = s.nextEdge := by
              have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 1 := by
                simp [hNext, kmswStepOfStep, hur, State.addEdge]
              omega
            subst f
            exact hnew
        refine ⟨q ++ [s.nextEdge], hULnext, by simp, ?_, ?_, ?_, hnewcreated⟩
        · intro f hf
          simp only [List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | hf
          · exact hqgood f hf
          · subst f
            exact hnew
        · intro f hf
          have hmem : f ∈ ([] : List ℕ) := by
            simp [hNext, s, kmswStepOfStep, hur, State.addEdge] at hf
          simp at hmem
        · simpa [act, hNext, kmswStepOfStep, hur, State.addEdge] using hnew
      | cons e es =>
        have hgoodE : sectorEdge w v a e := by
          exact hURgood e (by rw [hur]; simp)
        have hULnext : (kmswStage w (j + 1)).UL = p ++ (q ++ [e]) := by
          rw [hNext]
          simp only [kmswStepOfStep, hur]
          rw [hULs]
          simp [List.append_assoc]
        have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
            f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
          intro f hlo hf
          have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge := by
            simp [hNext, kmswStepOfStep, hur]
          rw [hne] at hf
          exact hcreated f hlo (by simpa [s] using hf)
        refine ⟨q ++ [e], hULnext, by simp [hqne], ?_, ?_, ?_, hnewcreated⟩
        · intro f hf
          simp only [List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | hf
          · exact hqgood f hf
          · subst f
            exact hgoodE
        · intro f hf
          have hf' : f ∈ es := by
            simpa [hNext, s, kmswStepOfStep, hur] using hf
          have hfUR : f ∈ s.UR := by rw [hur]; exact List.mem_cons_of_mem e hf'
          exact hURgood f (by simpa [s] using hfUR)
        · simpa [act, hNext, kmswStepOfStep, hur] using hgoodE


private theorem future_sector (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) (e : ℕ)
    (he : (kmswStage w n).nextEdge ≤ e) :
    sectorEdge w ((recordVertex w n).id) ((kmswStage w n).east (act w n)) e := by
  let m := max n e
  have halloc : e < (kmswStage w m).nextEdge :=
    (allocated_by_self w e).trans_le (kmswStage_nextEdge_mono w (Nat.le_max_right n e))
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hUL : (kmswStage w n).UL = xs ++ [act w n] := by simpa [act] using hxs
  have hUR : (kmswStage w n).UR = [] := by
    by_cases hn : n = 0
    · subst n
      rfl
    · obtain ⟨hw, hu⟩ := record_forces_pendant w n hA (Nat.pos_of_ne_zero hn)
      have hn' : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn']
      simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hu, State.addEdge]
  have hact : sectorEdge w ((recordVertex w n).id)
      ((kmswStage w n).east (act w n)) (act w n) := by
    apply sectorEdge_of_stage _ _ _ n _ (act_lt_nextEdge w le_rfl)
    · exact Or.inl rfl
    · exact Or.inr le_rfl
  obtain ⟨q, _, _, _, _, _, hcreated⟩ := sector_stage_invariant w n
    ((recordVertex w n).id) ((kmswStage w n).east (act w n)) xs hB
    (record_east_successor w n hA) hUL hUR hact m (Nat.le_max_left n e)
  exact hcreated e he halloc

end GeodesicSector

private def pathEdges {w : ℕ → Fin 3} {u : PresentVertex w} :
    {v : PresentVertex w} → Path u v → List ℕ
  | _, .nil => []
  | _, .cons p e => e.val :: pathEdges p

private theorem pathEdges_length {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) : (pathEdges p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [pathEdges, List.length_cons, Path.length_cons, ih]

private theorem pathEdges_injective {w : ℕ → Fin 3} {u v : PresentVertex w} :
    Function.Injective (pathEdges (u := u) (v := v)) := by
  intro p
  induction p with
  | nil =>
    intro q hq
    cases q with
    | nil => rfl
    | cons q f => cases hq
  | @cons a b p e ih =>
    intro q hq
    cases q with
    | nil => simp only [pathEdges, List.cons_ne_nil] at hq
    | @cons c d q f =>
      have he : e.val = f.val := (List.cons.inj hq).1
      have hac : a = c := vertex_ext (e.property.2.1.symm.trans
        ((congrArg (edgeWest w) he).trans f.property.2.1))
      subst c
      have hef : e = f := Subtype.ext he
      subst f
      exact congrArg (fun r => r.cons e) (ih (List.cons.inj hq).2)

private theorem pathEdges_allocated {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u v : PresentVertex w} (p : Path u v)
    (hc : ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n}) :
    ∀ e ∈ pathEdges p, e < (kmswStage w n).nextEdge := by
  induction p with
  | nil => simp only [pathEdges, List.not_mem_nil, false_implies, implies_true]
  | @cons a b p e ih =>
    intro f hf
    rcases List.mem_cons.mp hf with hfe | hf
    · subst f
      by_contra hlate
      have hs := GeodesicSector.future_sector w n hA hB e.val (by omega)
      have ha := record_east_successor w n hA
      have hregion (z : PresentVertex w) (hz : z ∈ recordBefore w n ∪ {recordVertex w n})
          (hsz : z.id = (recordVertex w n).id ∨
            (kmswStage w n).east (act w n) ≤ z.id) : z.id = (recordVertex w n).id := by
        rcases hz with hz | hz
        · rcases hsz with hsz | hsz
          · exact hsz
          · have hlt := hz.1
            have hne := hz.2.2
            omega
        · exact congrArg PresentVertex.id hz
      have hmemA : a ∈ (p.cons e).vertices :=
        (Path.mem_vertices_cons p e).2 (Or.inl p.end_mem_vertices)
      have hmemB := (p.cons e).end_mem_vertices
      have hsA : a.id = (recordVertex w n).id := hregion a (hc a hmemA)
        (by simpa only [GeodesicSector.sectorEdge, GeodesicSector.sectorPoint,
          e.property.2.1] using hs.1)
      have hsB : b.id = (recordVertex w n).id := hregion b (hc b hmemB)
        (by simpa only [GeodesicSector.sectorEdge, GeodesicSector.sectorPoint,
          e.property.2.2] using hs.2)
      have hab : a = b := vertex_ext (hsA.trans hsB.symm)
      subst b
      have hz := presentVertex_acyclic w a (Hom.toPath e)
      cases hz
    · exact ih (fun z hz => hc z ((Path.mem_vertices_cons p e).2 (Or.inl hz))) f hf

private theorem bounded_lists_finite (E N : ℕ) :
    {l : List (Fin E) | l.length ≤ N}.Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun a : (k : Fin (N + 1)) × List.Vector (Fin E) k.val => a.2.val))
  intro l hl
  change l.length ≤ N at hl
  exact ⟨⟨⟨l.length, by omega⟩, ⟨l, rfl⟩⟩, rfl⟩

/-- There are finitely many arrow-valued paths between ordered records.
In addition to finite vertex confinement, every edge of such a path is
allocated by the later record stage; parallel edges remain distinguished -/
theorem recordVertex_paths_finite (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    (hBn : ∀ j, n ≤ j → L w n ≤ L w j) :
    Finite (Path (recordVertex w m) (recordVertex w n)) := by
  classical
  let S := record_region_finite w n
  let N := S.toFinset.card
  let E := (kmswStage w n).nextEdge
  have hbound (p : Path (recordVertex w m) (recordVertex w n)) : p.length ≤ N := by
    have hsub : p.vertices.toFinset ⊆ S.toFinset := by
      intro z hz
      exact S.mem_toFinset.2
        (recordVertex_path_confined w hmn hAn hBn p z (List.mem_toFinset.1 hz))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (vertices_nodup_of_acyclic (presentVertex_acyclic w) p),
      Path.vertices_length] at hcard
    exact Nat.le_of_succ_le hcard
  have he (p : Path (recordVertex w m) (recordVertex w n)) :
      ∀ e ∈ pathEdges p, e < E :=
    pathEdges_allocated hAn hBn p (recordVertex_path_confined w hmn hAn hBn p)
  let enc (p : Path (recordVertex w m) (recordVertex w n)) : List (Fin E) :=
    (pathEdges p).pmap (fun e h => ⟨e, h⟩) (he p)
  have henc (p : Path (recordVertex w m) (recordVertex w n)) :
      (enc p).map Fin.val = pathEdges p := by
    simp only [enc, List.map_pmap, List.pmap_eq_map]
    exact List.map_id _
  have hlen (p : Path (recordVertex w m) (recordVertex w n)) : (enc p).length ≤ N := by
    simpa only [enc, List.length_pmap, pathEdges_length] using hbound p
  let f (p : Path (recordVertex w m) (recordVertex w n)) :
      {l : List (Fin E) | l.length ≤ N} := ⟨enc p, hlen p⟩
  have : Finite {l : List (Fin E) | l.length ≤ N} := bounded_lists_finite E N
  apply Finite.of_injective f
  intro p q hpq
  apply pathEdges_injective
  rw [← henc p, ← henc q]
  exact congrArg (List.map Fin.val) (congrArg Subtype.val hpq)

/-- The actual edge IDs in traversal order, preserving parallel edges -/
def pathEdgeList {w : ℕ → Fin 3} {u : PresentVertex w} :
    {v : PresentVertex w} → Path u v → List ℕ
  | _, .nil => []
  | _, .cons p e => pathEdgeList p ++ [e.val]

private theorem pathEdgeList_eq_reverse {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) : pathEdgeList p = (pathEdges p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [pathEdgeList, pathEdges, List.reverse_cons, ih]

private theorem pathEdges_comp {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (q : Path v z) : pathEdges (p.comp q) = pathEdges q ++ pathEdges p := by
  induction q with
  | nil => rfl
  | cons q e ih => simp only [Path.comp_cons, pathEdges, ih, List.cons_append]

/-- Edge lists concatenate in traversal order (`def-infinite-geo`, -/
theorem pathEdgeList_comp {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (q : Path v z) : pathEdgeList (p.comp q) = pathEdgeList p ++ pathEdgeList q := by
  simp only [pathEdgeList_eq_reverse, pathEdges_comp, List.reverse_append]

/-- The edge list has the actual path length (`def-infinite-geo`, -/
theorem pathEdgeList_length {w : ℕ → Fin 3} {u v : PresentVertex w} (p : Path u v) :
    (pathEdgeList p).length = p.length := by
  simp only [pathEdgeList_eq_reverse, List.length_reverse, pathEdges_length]

/-- A genuine infinite edge path from `start`: each finite prefix is realized
by a path in the present-edge quiver, of exactly the prescribed length -/
structure InfinitePresentPath (w : ℕ → Fin 3) (start : PresentVertex w) where
  edge : ℕ → ℕ
  initial : (N : ℕ) → (v : PresentVertex w) × Path start v
  prefix_length : ∀ N, (initial N).2.length = N
  prefix_edges : ∀ N, pathEdgeList (initial N).2 = List.ofFn (fun i : Fin N => edge i.val)

private def optimal {w : ℕ → Fin 3} (longest : Bool) {u v : PresentVertex w} (p : Path u v) : Prop :=
  if longest then IsLongest p else IsShortest p

private theorem optimal_prefix {w : ℕ → Fin 3} {longest : Bool} {u v z : PresentVertex w}
    {p : Path u v} {q : Path v z} (hp : optimal longest (p.comp q)) : optimal longest p := by
  cases longest
  · exact IsShortest.of_comp_left hp
  · exact IsLongest.of_comp_left hp

private theorem exists_infinite_of_prefixes {w : ℕ → Fin 3} (longest : Bool)
    (v : ℕ → PresentVertex w) (Q : (k : ℕ) → Path (v 0) (v k))
    (hQ : ∀ k, optimal longest (Q k))
    (hext : ∀ k, ∃ r : Path (v k) (v (k + 1)), Q (k + 1) = (Q k).comp r)
    (hlen : ∀ k, k ≤ (Q k).length) :
    ∃ P : InfinitePresentPath w (v 0), (∀ N, optimal longest (P.initial N).2) ∧
      ∀ k, pathEdgeList (Q k) = List.ofFn (fun i : Fin (Q k).length => P.edge i.val) := by
  classical
  have hmono {a b : ℕ} (hab : a ≤ b) : pathEdgeList (Q a) <+: pathEdgeList (Q b) := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨[], List.append_nil _⟩
    | succ b hab ih =>
      obtain ⟨r, hr⟩ := hext b
      apply ih.trans
      exact ⟨pathEdgeList r, (pathEdgeList_comp (Q b) r).symm.trans (congrArg pathEdgeList hr).symm⟩
  have hex (N : ℕ) : ∃ t : (z : PresentVertex w) × Path (v 0) z,
      ∃ r : Path t.1 (v N), Q N = t.2.comp r ∧ t.2.length = N := by
    obtain ⟨z, p, q, hp, hl⟩ := (Q N).exists_eq_comp_of_le_length (hlen N)
    exact ⟨⟨z, p⟩, q, hp, hl⟩
  choose t r hr htlen using hex
  have htpre (N : ℕ) : pathEdgeList (t N).2 <+: pathEdgeList (Q N) := by
    refine ⟨pathEdgeList (r N), ?_⟩
    rw [hr N, pathEdgeList_comp]
  let edge (i : ℕ) : ℕ := (pathEdgeList (Q (i + 1)))[i]'(by
    rw [pathEdgeList_length]
    have := hlen (i + 1)
    omega)
  have hedge (N : ℕ) : pathEdgeList (t N).2 = List.ofFn (fun i : Fin N => edge i.val) := by
    apply List.ext_getElem
    · simp only [pathEdgeList_length, htlen, List.length_ofFn]
    · intro i hi hj
      have hiN : i < N := by simpa only [List.length_ofFn] using hj
      rw [List.getElem_ofFn]
      change (pathEdgeList (t N).2)[i] = edge i
      dsimp only [edge]
      exact ((htpre N).getElem hi).trans
        ((hmono (by omega : i + 1 ≤ N)).getElem (by
          rw [pathEdgeList_length]
          have := hlen (i + 1)
          omega)).symm
  refine ⟨⟨edge, t, htlen, hedge⟩, ?_, ?_⟩
  · intro N
    have hopt := hQ N
    rw [hr N] at hopt
    exact optimal_prefix hopt
  · intro k
    apply List.ext_getElem
    · simp only [pathEdgeList_length, List.length_ofFn]
    · intro i hi hj
      rw [List.getElem_ofFn]
      change (pathEdgeList (Q k))[i] = edge i
      dsimp only [edge]
      have hlarge := hmono (Nat.le_max_right (i + 1) k)
      have hsmall := hmono (Nat.le_max_left (i + 1) k)
      exact (hlarge.getElem hi).trans (hsmall.getElem (by
        rw [pathEdgeList_length]
        have := hlen (i + 1)
        omega)).symm

/-- Concatenation of the first `k` selected record-to-record paths -/
def recordPathPrefix {w : ℕ → Fin 3} (n : ℕ → ℕ)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1)))) :
    (k : ℕ) → Path (recordVertex w (n 0)) (recordVertex w (n k))
  | 0 => .nil
  | k + 1 => (recordPathPrefix n p k).comp (p k)

private theorem recordPathPrefix_optimal (w : ℕ → Fin 3) (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (longest : Bool)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, optimal longest (p k)) :
    ∀ k, optimal longest (recordPathPrefix n p k) := by
  intro k
  induction k with
  | zero =>
    cases longest
    · intro q
      exact Nat.zero_le _
    · intro q
      exact Nat.le_of_eq (presentVertex_acyclic w _ q)
  | succ k ih =>
    change optimal longest ((recordPathPrefix n p k).comp (p k))
    have hsep : ∀ q : Path (recordVertex w (n 0)) (recordVertex w (n (k + 1))),
        recordVertex w (n k) ∈ q.vertices := by
      intro q
      by_cases hk : k = 0
      · subst k
        exact q.start_mem_vertices
      · exact recordVertex_mem_path w (hn (Nat.pos_of_ne_zero hk)) (hn (by omega))
          (hA k) (hB k) (hA (k + 1)) q
    cases longest
    · exact IsShortest.comp_of_forall_mem_vertices ih (hp k) hsep
    · exact IsLongest.comp_of_forall_mem_vertices ih (hp k) hsep

private theorem infinite_of_record_blocks (w : ℕ → Fin 3) (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (longest : Bool)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, optimal longest (p k)) :
    ∃ P : InfinitePresentPath w (recordVertex w (n 0)),
      (∀ N, optimal longest (P.initial N).2) ∧
      ∀ k, pathEdgeList (recordPathPrefix n p k) =
        List.ofFn (fun i : Fin (recordPathPrefix n p k).length => P.edge i.val) := by
  apply exists_infinite_of_prefixes longest (fun k => recordVertex w (n k)) (recordPathPrefix n p)
    (recordPathPrefix_optimal w n hn hA hB longest p hp)
  · intro k
    exact ⟨p k, rfl⟩
  · intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hpos : 0 < (p k).length := by
        by_contra h
        have hz : (p k).length = 0 := by omega
        exact recordVertex_ne w (hn (by omega)) (hA (k + 1)) ((p k).eq_of_length_zero hz)
      change k + 1 ≤ ((recordPathPrefix n p k).comp (p k)).length
      rw [Path.length_comp]
      omega

/-- Every nonempty finite edge interval, indexed as `1 ≤ a ≤ b` in
The stream uses zero-based Lean indices, so this interval drops `a - 1`
edges from its first `b` edges. -/
def InfinitePresentPath.HasLongestSegments {w : ℕ → Fin 3} {start : PresentVertex w}
    (P : InfinitePresentPath w start) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
    q.length = b + 1 - a ∧
    pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧ IsLongest q

/-- Shortest-path counterpart of `HasLongestSegments`, with the same literal -/
def InfinitePresentPath.HasShortestSegments {w : ℕ → Fin 3} {start : PresentVertex w}
    (P : InfinitePresentPath w start) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
    q.length = b + 1 - a ∧
    pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧ IsShortest q

private theorem optimal_segments {w : ℕ → Fin 3} {start : PresentVertex w}
    (longest : Bool) (P : InfinitePresentPath w start)
    (hP : ∀ N, optimal longest (P.initial N).2) :
    ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧
      optimal longest q := by
  intro a b ha hab
  obtain ⟨z, p, q, hpq, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, q, ?_, ?_, ?_⟩
  · have hlen := P.prefix_length b
    rw [hpq, Path.length_comp, hp] at hlen
    omega
  · rw [← P.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := hP b
    rw [hpq] at hopt
    cases longest
    · exact IsShortest.of_comp_right hopt
    · exact IsLongest.of_comp_right hopt

/-- Concatenating any selected longest paths between consecutive records
gives a genuine infinite present-edge path, with every finite subpath longest.
The last clause identifies the concatenation with the edge stream, retaining -/
theorem recordPaths_concat_longest (w : ℕ → Fin 3) (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, IsLongest (p k)) :
    ∃ P : InfinitePresentPath w (recordVertex w (n 0)), P.HasLongestSegments ∧
      ∀ k, pathEdgeList (recordPathPrefix n p k) =
        List.ofFn (fun i : Fin (recordPathPrefix n p k).length => P.edge i.val) := by
  obtain ⟨P, hP, he⟩ := infinite_of_record_blocks w n hn hA hB true p hp
  exact ⟨P, optimal_segments true P hP, he⟩

/-- Concatenating selected shortest record-to-record paths has the analogous -/
theorem recordPaths_concat_shortest (w : ℕ → Fin 3) (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, IsShortest (p k)) :
    ∃ P : InfinitePresentPath w (recordVertex w (n 0)), P.HasShortestSegments ∧
      ∀ k, pathEdgeList (recordPathPrefix n p k) =
        List.ofFn (fun i : Fin (recordPathPrefix n p k).length => P.edge i.val) := by
  obtain ⟨P, hP, he⟩ := infinite_of_record_blocks w n hn hA hB false p hp
  exact ⟨P, optimal_segments false P hP, he⟩

/-- For every code word and every increasing sequence satisfying the explicit
past and future record barriers, both kinds of infinite geodesic exist from
the first record vertex. No inter-record reachability premise is needed -/
theorem recordSequence_exists_infinite_extremal (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) :
    (∃ P : InfinitePresentPath w (recordVertex w (n 0)), P.HasLongestSegments) ∧
    (∃ P : InfinitePresentPath w (recordVertex w (n 0)), P.HasShortestSegments) := by
  classical
  have he (k : ℕ) := recordVertex_exists_extremal w (hn (by omega : k < k + 1))
    (hA k) (hA (k + 1)) (hB (k + 1))
  choose p hp using fun k => (he k).1
  choose q hq using fun k => (he k).2
  obtain ⟨P, hP, _⟩ := recordPaths_concat_longest w n hn hA hB p hp
  obtain ⟨Q, hQ, _⟩ := recordPaths_concat_shortest w n hn hA hB q hq
  exact ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩

end DirectedDistances.KMSW
