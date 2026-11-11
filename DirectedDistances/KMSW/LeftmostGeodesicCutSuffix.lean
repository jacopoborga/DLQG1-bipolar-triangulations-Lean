module

public import DirectedDistances.KMSW.LeftmostGeodesicSdpPlanar
public import DirectedDistances.KMSW.InfinitePresentPathCutVisit
import DirectedDistances.KMSW.InfiniteGeodesicAnyStart






public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable {w : ℕ → Fin 3}

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.exists_shift_split {x : PresentVertex w}
    (P : InfinitePresentPath w x) (i n : ℕ) :
    ∃ (p : Path x (P.initial i).1)
      (q : Path (P.initial i).1 (P.initial (i + n)).1),
      (P.initial (i + n)).2 = p.comp q ∧ p.length = i ∧ q.length = n ∧
      pathEdgeList q = List.ofFn (fun k : Fin n => P.edge (i + k.val)) := by
  obtain ⟨z, p, q, hpq, hp⟩ := (P.initial (i + n)).2.exists_eq_comp_of_le_length
    (show i ≤ (P.initial (i + n)).2.length by rw [P.prefix_length]; omega)
  have hl : pathEdgeList p ++ pathEdgeList q =
      List.ofFn (fun k : Fin i => P.edge k.val) ++
        List.ofFn (fun k : Fin n => P.edge (i + k.val)) := by
    rw [← pathEdgeList_comp, ← hpq, P.prefix_edges, List.ofFn_add]
    rfl
  have hpre := List.append_inj_left hl
    (by rw [pathEdgeList_length, hp, List.length_ofFn])
  have hsuf := List.append_inj_right hl
    (by rw [pathEdgeList_length, hp, List.length_ofFn])
  have hz : z = (P.initial i).1 := by
    have he := pathEdgeList_endpoint p
    have he' := pathEdgeList_endpoint (P.initial i).2
    rw [hpre] at he
    rw [P.prefix_edges] at he'
    exact congrArg (fun t : ℕ => (⟨t⟩ : PresentVertex w)) (he.symm.trans he')
  subst z
  refine ⟨p, q, hpq, hp, ?_, hsuf⟩
  have hlen := P.prefix_length (i + n)
  rw [hpq, Path.length_comp, hp] at hlen
  omega

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
@[expose] noncomputable def InfinitePresentPath.shift {x : PresentVertex w}
    (P : InfinitePresentPath w x) (i : ℕ) : InfinitePresentPath w (P.initial i).1 where
  edge n := P.edge (i + n)
  initial n := ⟨(P.initial (i + n)).1, (P.exists_shift_split i n).choose_spec.choose⟩
  prefix_length n := (P.exists_shift_split i n).choose_spec.choose_spec.2.2.1
  prefix_edges n := (P.exists_shift_split i n).choose_spec.choose_spec.2.2.2

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private def cutOptimal (longest : Bool) {x y : PresentVertex w}
    (p : Path x y) : Prop := if longest then IsLongest p else IsShortest p

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cutOptimal_right {longest : Bool} {x y z : PresentVertex w}
    {p : Path x y} {q : Path y z} (h : cutOptimal longest (p.comp q)) :
    cutOptimal longest q := by
  cases longest
  · exact IsShortest.of_comp_right h
  · exact IsLongest.of_comp_right h

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cutOptimal_segments {x : PresentVertex w} (longest : Bool)
    (P : InfinitePresentPath w x) (hP : ∀ n, cutOptimal longest (P.initial n).2) :
    ∀ a b, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧
      cutOptimal longest q := by
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
    exact cutOptimal_right hopt

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.shift_hasLongestSegments {x : PresentVertex w}
    (P : InfinitePresentPath w x) (hP : P.HasLongestSegments) (i : ℕ) :
    (P.shift i).HasLongestSegments := by
  apply cutOptimal_segments true
  intro n
  have hopt := P.initial_isLongest w hP (i + n)
  rw [(P.exists_shift_split i n).choose_spec.choose_spec.1] at hopt
  exact hopt.of_comp_right

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_spliced_prefix {x : ℕ} (longest : Bool)
    (P : InfinitePresentPath w ⟨x⟩) (i : ℕ)
    (Q : InfinitePresentPath w (P.initial i).1)
    (hP : ∀ n, cutOptimal longest (P.initial n).2)
    (hQ : ∀ n, cutOptimal longest (Q.initial n).2)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices) (b : ℕ) :
    ∃ z, ∃ p : Path (⟨x⟩ : PresentVertex w) z,
      p.length = b ∧
      pathEdgeList p = List.ofFn (fun k : Fin b =>
        if k.val < i then P.edge k.val else Q.edge (k.val - i)) ∧
      cutOptimal longest p := by
  by_cases hb : b ≤ i
  · refine ⟨_, (P.initial b).2, P.prefix_length b, ?_, hP b⟩
    rw [P.prefix_edges]
    apply congrArg List.ofFn
    funext k
    rw [ite_eq_left (by have := k.isLt; omega)]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show i ≤ b by omega)
    refine ⟨_, (P.initial i).2.comp (Q.initial n).2, ?_, ?_, ?_⟩
    · rw [Path.length_comp, P.prefix_length, Q.prefix_length]
    · rw [pathEdgeList_comp, P.prefix_edges, Q.prefix_edges, List.ofFn_add]
      congr 1
      · apply congrArg List.ofFn
        funext k
        simp only [Fin.val_castLE, ite_eq_left k.isLt]
      · apply congrArg List.ofFn
        funext k
        simp only [Fin.val_natAdd, Nat.add_sub_cancel_left,
          ite_eq_right (show ¬i + k.val < i by omega)]
    · have hs := hsep (Q.initial n).1 ⟨(Q.initial n).2⟩
      cases longest
      · exact IsShortest.comp_of_forall_mem_vertices (hP i) (hQ n) hs
      · exact IsLongest.comp_of_forall_mem_vertices (hP i) (hQ n) hs

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_exists_splice {x : ℕ} (longest : Bool)
    (P : InfinitePresentPath w ⟨x⟩) (i : ℕ)
    (Q : InfinitePresentPath w (P.initial i).1)
    (hP : ∀ n, cutOptimal longest (P.initial n).2)
    (hQ : ∀ n, cutOptimal longest (Q.initial n).2)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices) :
    ∃ S : InfinitePresentPath w ⟨x⟩,
      (∀ n, cutOptimal longest (S.initial n).2) ∧
      ∀ k, S.edge k = if k < i then P.edge k else Q.edge (k - i) := by
  classical
  let H := cut_spliced_prefix longest P i Q hP hQ hsep
  let S : InfinitePresentPath w ⟨x⟩ := {
    edge := fun k => if k < i then P.edge k else Q.edge (k - i)
    initial := fun b => ⟨(H b).choose, (H b).choose_spec.choose⟩
    prefix_length := fun b => (H b).choose_spec.choose_spec.1
    prefix_edges := fun b => (H b).choose_spec.choose_spec.2.1 }
  exact ⟨S, fun b => (H b).choose_spec.choose_spec.2.2, fun _ => rfl⟩

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.exists_ldp_splice_at_separator {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (hP : P.HasLongestSegments) (i : ℕ)
    (Q : InfinitePresentPath w (P.initial i).1) (hQ : Q.HasLongestSegments)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices) :
    ∃ S : InfinitePresentPath w ⟨x⟩, S.HasLongestSegments ∧
      ∀ k, S.edge k = if k < i then P.edge k else Q.edge (k - i) := by
  obtain ⟨S, hS, he⟩ := cut_exists_splice true P i Q
    (P.initial_isLongest w hP) (Q.initial_isLongest w hQ) hsep
  exact ⟨S, cutOptimal_segments true S hS, he⟩

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.shift_hasShortestSegments {x : PresentVertex w}
    (P : InfinitePresentPath w x) (hP : P.HasShortestSegments) (i : ℕ) :
    (P.shift i).HasShortestSegments := by
  apply cutOptimal_segments false
  intro n
  have hopt := P.initial_isShortest w hP (i + n)
  rw [(P.exists_shift_split i n).choose_spec.choose_spec.1] at hopt
  exact hopt.of_comp_right

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.exists_sdp_splice_at_separator {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (hP : P.HasShortestSegments) (i : ℕ)
    (Q : InfinitePresentPath w (P.initial i).1) (hQ : Q.HasShortestSegments)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices) :
    ∃ S : InfinitePresentPath w ⟨x⟩, S.HasShortestSegments ∧
      ∀ k, S.edge k = if k < i then P.edge k else Q.edge (k - i) := by
  obtain ⟨S, hS, he⟩ := cut_exists_splice false P i Q
    (P.initial_isShortest w hP) (Q.initial_isShortest w hQ) hsep
  exact ⟨S, cutOptimal_segments false S hS, he⟩

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_shift_order {x : ℕ} (P : InfinitePresentPath w ⟨x⟩) (i n : ℕ) :
    kmswPrefixOutgoingEdges w hfin hL htrans hR x
      (List.ofFn (fun k : Fin (i + n) => P.edge k.val)) =
    kmswPrefixOutgoingEdges w hfin hL htrans hR (P.initial i).1.id
      (List.ofFn (fun k : Fin n => (P.shift i).edge k.val)) := by
  let f := fun v => kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v
    (kmsw_vertex_allocated_of_finite_incidence w hfin v)
  change f _ = f _
  apply congrArg f
  rw [← P.prefix_edges, pathEdgeList_endpoint,
    ← (P.shift i).prefix_edges, pathEdgeList_endpoint]
  rfl

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.shift_firstDivergenceLeftmost_ldp {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (hP : P.HasLongestSegments)
    (hleft : ∀ Q : InfinitePresentPath w ⟨x⟩, Q.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x P Q) (i : ℕ)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (Q : InfinitePresentPath w (P.initial i).1) (hQ : Q.HasLongestSegments) :
    GeodesicFirstDivergenceRightOf w hfin hL htrans hR (P.initial i).1.id
      (P.shift i) Q := by
  obtain ⟨S, hS, he⟩ := P.exists_ldp_splice_at_separator hP i Q hQ hsep
  intro n hn
  have hp : ∀ k, k < i + n → P.edge k = S.edge k := by
    intro k hk
    rw [he k]
    by_cases hki : k < i
    · rw [ite_eq_left hki]
    · rw [ite_eq_right hki]
      have ht := hn (k - i) (by omega)
      change P.edge (i + (k - i)) = Q.edge (k - i) at ht
      simpa only [Nat.add_sub_of_le (show i ≤ k by omega)] using ht
  have hm := hleft S hS (i + n) hp
  rw [he (i + n), ite_eq_right (by omega : ¬i + n < i),
    Nat.add_sub_cancel_left, cut_shift_order w hfin hL htrans hR P i n] at hm
  exact hm

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem kmswLeftmostLdpPath_shift_edge (x : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨x⟩, P.HasLongestSegments) (i : ℕ)
    (hsep : ∀ z : PresentVertex w,
      Reachable ((kmswLeftmostLdpPath w hfin hL htrans hR x hg).initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z,
        ((kmswLeftmostLdpPath w hfin hL htrans hR x hg).initial i).1 ∈ r.vertices) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR x hg
    (P.shift i).edge =
      (kmswLeftmostLdpPath w hfin hL htrans hR (P.initial i).1.id
        ⟨P.shift i, P.shift_hasLongestSegments
          (kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR x hg) i⟩).edge := by
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR x hg
  have hP := kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR x hg
  apply kmswLeftmostLdpPath_unique_edge w hfin hL htrans hR (P.initial i).1.id
  · exact P.shift_hasLongestSegments hP i
  · exact P.shift_firstDivergenceLeftmost_ldp w hfin hL htrans hR hP
      (kmswLeftmostLdpPath_firstDivergenceRightOf w hfin hL htrans hR x hg) i hsep

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_leftmost_edge_eq {x y : PresentVertex w}
    (P : InfinitePresentPath w x) (Q : InfinitePresentPath w y) (hxy : x = y)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ T : InfinitePresentPath w x, T.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x.id P T)
    (hleftQ : ∀ T : InfinitePresentPath w y, T.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR y.id Q T) :
    P.edge = Q.edge := by
  subst y
  exact GeodesicFirstDivergenceRightOf.antisymm w hfin hL htrans hR x.id P Q
    (hleftP Q hQ) (hleftQ P hP)

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.ldp_coalescence_at_separator {x y : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ T : InfinitePresentPath w ⟨x⟩, T.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x P T)
    (hleftQ : ∀ T : InfinitePresentPath w ⟨y⟩, T.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR y Q T)
    (i j : ℕ) (hv : (P.initial i).1 = (Q.initial j).1)
    (hsepP : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (hsepQ : ∀ z : PresentVertex w, Reachable (Q.initial j).1 z →
      ∀ r : Path (⟨y⟩ : PresentVertex w) z, (Q.initial j).1 ∈ r.vertices) :
    (P.shift i).edge = (Q.shift j).edge := by
  exact cut_leftmost_edge_eq w hfin hL htrans hR (P.shift i) (Q.shift j) hv
    (P.shift_hasLongestSegments hP i) (Q.shift_hasLongestSegments hQ j)
    (P.shift_firstDivergenceLeftmost_ldp w hfin hL htrans hR hP hleftP i hsepP)
    (Q.shift_firstDivergenceLeftmost_ldp w hfin hL htrans hR hQ hleftQ j hsepQ)

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.shift_firstDivergenceLeftmost_sdp {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (hP : P.HasShortestSegments)
    (hleft : ∀ Q : InfinitePresentPath w ⟨x⟩, Q.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x P Q) (i : ℕ)
    (hsep : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (Q : InfinitePresentPath w (P.initial i).1) (hQ : Q.HasShortestSegments) :
    GeodesicFirstDivergenceRightOf w hfin hL htrans hR (P.initial i).1.id
      (P.shift i) Q := by
  obtain ⟨S, hS, he⟩ := P.exists_sdp_splice_at_separator hP i Q hQ hsep
  intro n hn
  have hp : ∀ k, k < i + n → P.edge k = S.edge k := by
    intro k hk
    rw [he k]
    by_cases hki : k < i
    · rw [ite_eq_left hki]
    · rw [ite_eq_right hki]
      have ht := hn (k - i) (by omega)
      change P.edge (i + (k - i)) = Q.edge (k - i) at ht
      simpa only [Nat.add_sub_of_le (show i ≤ k by omega)] using ht
  have hm := hleft S hS (i + n) hp
  rw [he (i + n), ite_eq_right (by omega : ¬i + n < i),
    Nat.add_sub_cancel_left, cut_shift_order w hfin hL htrans hR P i n] at hm
  exact hm

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem kmswLeftmostSdpPath_shift_edge (x : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨x⟩, P.HasShortestSegments) (i : ℕ)
    (hsep : ∀ z : PresentVertex w,
      Reachable ((kmswLeftmostSdpPath w hfin hL htrans hR x hg).initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z,
        ((kmswLeftmostSdpPath w hfin hL htrans hR x hg).initial i).1 ∈ r.vertices) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR x hg
    (P.shift i).edge =
      (kmswLeftmostSdpPath w hfin hL htrans hR (P.initial i).1.id
        ⟨P.shift i, P.shift_hasShortestSegments
          (kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR x hg) i⟩).edge := by
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR x hg
  have hP := kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR x hg
  apply kmswLeftmostSdpPath_unique_edge w hfin hL htrans hR (P.initial i).1.id
  · exact P.shift_hasShortestSegments hP i
  · exact P.shift_firstDivergenceLeftmost_sdp w hfin hL htrans hR hP
      (kmswLeftmostSdpPath_firstDivergenceRightOf w hfin hL htrans hR x hg) i hsep

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_leftmost_sdp_edge_eq {x y : PresentVertex w}
    (P : InfinitePresentPath w x) (Q : InfinitePresentPath w y) (hxy : x = y)
    (hP : P.HasShortestSegments) (hQ : Q.HasShortestSegments)
    (hleftP : ∀ T : InfinitePresentPath w x, T.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x.id P T)
    (hleftQ : ∀ T : InfinitePresentPath w y, T.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR y.id Q T) :
    P.edge = Q.edge := by
  subst y
  exact GeodesicFirstDivergenceRightOf.antisymm w hfin hL htrans hR x.id P Q
    (hleftP Q hQ) (hleftQ P hP)

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
theorem InfinitePresentPath.sdp_coalescence_at_separator {x y : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : P.HasShortestSegments) (hQ : Q.HasShortestSegments)
    (hleftP : ∀ T : InfinitePresentPath w ⟨x⟩, T.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR x P T)
    (hleftQ : ∀ T : InfinitePresentPath w ⟨y⟩, T.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR y Q T)
    (i j : ℕ) (hv : (P.initial i).1 = (Q.initial j).1)
    (hsepP : ∀ z : PresentVertex w, Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (hsepQ : ∀ z : PresentVertex w, Reachable (Q.initial j).1 z →
      ∀ r : Path (⟨y⟩ : PresentVertex w) z, (Q.initial j).1 ∈ r.vertices) :
    (P.shift i).edge = (Q.shift j).edge := by
  exact cut_leftmost_sdp_edge_eq w hfin hL htrans hR (P.shift i) (Q.shift j) hv
    (P.shift_hasShortestSegments hP i) (Q.shift_hasShortestSegments hQ j)
    (P.shift_firstDivergenceLeftmost_sdp w hfin hL htrans hR hP hleftP i hsepP)
    (Q.shift_firstDivergenceLeftmost_sdp w hfin hL htrans hR hQ hleftQ j hsepQ)

/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/
private theorem cut_endpoint_before {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u z : PresentVertex w} (p : Path u z) (hu : u ∈ recordBefore w n)
    (havoid : recordVertex w n ∉ p.vertices) : z ∈ recordBefore w n := by
  induction p with
  | nil => exact hu
  | @cons y z p e ih =>
    have hy : y ∈ recordBefore w n := ih (by
      intro hmem
      exact havoid ((Path.mem_vertices_cons p e).2 (Or.inl hmem)))
    by_contra hz
    apply presentArrow_no_crossing w n hA hB e
    refine ⟨hy, hz, ?_⟩
    intro heq
    exact havoid (heq ▸ (Path.mem_vertices_cons p e).2 (Or.inr rfl))

include hL htrans hR in
/-- Helper toward lem-finite-ind / lem-filtration-mono
separating vertex; leftmost means first-divergence leftmost; renewal times and
future-map statements are not used; not the paper result. -/

theorem mapCutVertex_separates_reachable {v : ℕ} (hcut : mapCutVertex w hfin v)
    (z : PresentVertex w) (hz : Reachable (⟨v⟩ : PresentVertex w) z)
    (r : Path (⟨0⟩ : PresentVertex w) z) :
    (⟨v⟩ : PresentVertex w) ∈ r.vertices := by
  obtain ⟨n, hnv, _, hA, hB, _⟩ :=
    mapCutVertex_firstVisit_records w hfin htrans hR hL hcut
  have hv : (⟨v⟩ : PresentVertex w) = recordVertex w n := by
    cases hnv.trans (CutConverse.activeInitial_eq w n)
    rfl
  by_cases hn : n = 0
  · subst n
    rw [hv]
    exact r.start_mem_vertices
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsource : (⟨0⟩ : PresentVertex w) ∈ recordBefore w n := by
      have hbound := (kmswStage_endpoints_lt_nextVertex w n (act w 0)
        (act_lt_nextEdge w hnpos.le)).1
      have hends := (edge_endpoints_eq w (act_lt_nextEdge w hnpos.le)).1
      rw [hends, ← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl 0))).1] at hbound
      refine ⟨hbound, ?_, ?_⟩
      · intro heq
        exact recordVertex_ne w hnpos hA
          (congrArg (fun t : ℕ => (⟨t⟩ : PresentVertex w)) heq)
      · intro heq
        apply activeEast_ne_activeInitial w hnpos.le
        rw [CutConverse.activeInitial_eq]
        exact heq.symm
    by_contra hmiss
    have hzold := cut_endpoint_before w hA hB r hsource (by rwa [← hv])
    obtain ⟨t⟩ := allocated_reachable_record w n hR hA hB z
      (kmsw_vertex_allocated_of_finite_incidence w hfin z.id) (Or.inl hzold)
    obtain ⟨q⟩ := hz
    rw [hv] at q
    have hcycle := presentVertex_acyclic w _ (q.comp t)
    rw [Path.length_comp] at hcycle
    have heq : recordVertex w n = z := q.eq_of_length_zero (by omega)
    apply hmiss
    rw [hv, heq]
    exact r.end_mem_vertices

end DirectedDistances.KMSW
