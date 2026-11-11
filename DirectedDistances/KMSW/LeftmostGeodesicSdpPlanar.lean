module

public import DirectedDistances.KMSW.LeftmostGeodesicPlanar
public import DirectedDistances.KMSW.LeftmostGeodesicSdpAssembly

/- # SDP shared-departure comparison

SDP (X = S) helpers toward `def-infinite-geo` / `lem-geo-exist`
The incoming rotation orders and local comparison predicates are reused unchanged.
Shortest prefixes reaching a common vertex have equal length; equal-length prefix
replacement preserves shortestness. These helpers assert shared-departure order. -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable (w : ℕ → Fin 3)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
private theorem sdp_pathEdgeList_head {w : ℕ → Fin 3} {u z : PresentVertex w}
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

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem InfinitePresentPath.initial_isShortest {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments) (n : ℕ) :
    IsShortest (P.initial n).2 := by
  cases n with
  | zero =>
    intro q
    rw [P.prefix_length]
    exact Nat.zero_le q.length
  | succ n =>
    obtain ⟨z, q, hlen, he, hq⟩ := hP 1 (n + 1) le_rfl (by omega)
    have hs : edgeWest w (P.edge 0) = z.id := by
      apply sdp_pathEdgeList_head q
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

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem InfinitePresentPath.index_eq_of_initial_eq_sdp {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments)
    (hQ : Q.HasShortestSegments) (m n : ℕ)
    (hs : (P.initial m).1 = (Q.initial n).1) : m = n := by
  have hlen {z t : PresentVertex w} (p : Path (⟨v⟩ : PresentVertex w) z)
      (q : Path (⟨v⟩ : PresentVertex w) t) (hp : IsShortest p) (hq : IsShortest q)
      (hzt : z = t) : p.length = q.length := by
    subst t
    exact Nat.le_antisymm (hp q) (hq p)
  have he := hlen (P.initial m).2 (Q.initial n).2
    (P.initial_isShortest w hP m) (Q.initial_isShortest w hQ n) hs
  simpa only [P.prefix_length, Q.prefix_length] using he

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
private theorem sdp_spliced_prefix_exists {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments)
    (hQ : Q.HasShortestSegments) (n : ℕ)
    (hs : (P.initial n).1 = (Q.initial n).1) (b : ℕ) :
    ∃ z, ∃ p : Path (⟨v⟩ : PresentVertex w) z,
      p.length = b ∧
      pathEdgeList p = List.ofFn (fun i : Fin b =>
        if i.val < n then P.edge i.val else Q.edge i.val) ∧ IsShortest p := by
  by_cases hb : b ≤ n
  · refine ⟨_, (P.initial b).2, P.prefix_length b, ?_, P.initial_isShortest w hP b⟩
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
    · have hopt := Q.initial_isShortest w hQ (n + k)
      rw [hpq] at hopt
      apply hopt.of_length_eq
      rw [Path.length_comp, Path.length_comp, P.prefix_length, hp]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem InfinitePresentPath.exists_sdp_geodesic_splice {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments)
    (hQ : Q.HasShortestSegments) (n : ℕ)
    (hs : (P.initial n).1 = (Q.initial n).1) :
    ∃ S : InfinitePresentPath w ⟨v⟩, S.HasShortestSegments ∧
      ∀ i, S.edge i = if i < n then P.edge i else Q.edge i := by
  classical
  let H := sdp_spliced_prefix_exists w P Q hP hQ n hs
  let S : InfinitePresentPath w ⟨v⟩ := {
    edge := fun i => if i < n then P.edge i else Q.edge i
    initial := fun b => ⟨(H b).choose, (H b).choose_spec.choose⟩
    prefix_length := fun b => (H b).choose_spec.choose_spec.1
    prefix_edges := fun b => (H b).choose_spec.choose_spec.2.1 }
  have hshort (b : ℕ) : IsShortest (S.initial b).2 := (H b).choose_spec.choose_spec.2.2
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
  · have hopt := hshort b
    rw [hpq] at hopt
    exact hopt.of_comp_right

variable
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem kmswLeftmostSdpPath_sharedDeparturesRightOf (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments)
    (Q : InfinitePresentPath w ⟨v⟩) (hQ : Q.HasShortestSegments) :
    GeodesicSharedDeparturesRightOf w hfin hL htrans hR v
      (kmswLeftmostSdpPath w hfin hL htrans hR v hg) Q := by
  let P := kmswLeftmostSdpPath w hfin hL htrans hR v hg
  have hP := kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR v hg
  intro m n hs
  have hmn := P.index_eq_of_initial_eq_sdp w Q hP hQ m n hs
  subst n
  obtain ⟨S, hS, he⟩ := P.exists_sdp_geodesic_splice w Q hP hQ m hs
  have hmin := kmswLeftmostSdpPath_firstDivergenceRightOf w hfin hL htrans hR
    v hg S hS m (by
      intro i hi
      rw [he i, ite_eq_left hi])
  rw [he m, ite_eq_right (Nat.lt_irrefl m)] at hmin
  exact ⟨hs, hmin⟩

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem pitmanCodes_ae_exists_unique_sharedDepartureLeftmostSdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments ∧
          (∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
            GeodesicSharedDeparturesRightOf w hf hL ht hR v P Q) ∧
          ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
            (∀ S : InfinitePresentPath w ⟨v⟩, S.HasShortestSegments →
              GeodesicSharedDeparturesRightOf w hf hL ht hR v Q S) → Q.edge = P.edge := by
  filter_upwards [pitmanCodes_ae_exists_unique_firstDivergenceLeftmostSdp] with ω h
  obtain ⟨hf, hL, ht, hR, hall⟩ := h
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  obtain ⟨P₀, hP₀, _⟩ := hall v
  have hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments := ⟨P₀, hP₀⟩
  let P := kmswLeftmostSdpPath w hf hL ht hR v hg
  have hP : P.HasShortestSegments := kmswLeftmostSdpPath_hasShortestSegments w hf hL ht hR v hg
  refine ⟨P, hP, kmswLeftmostSdpPath_sharedDeparturesRightOf w hf hL ht hR v hg, ?_⟩
  intro Q hQ hleft
  exact GeodesicSharedDeparturesRightOf.antisymm w hf hL ht hR v Q P
    (hleft P hP) (kmswLeftmostSdpPath_sharedDeparturesRightOf w hf hL ht hR v hg Q hQ)

end DirectedDistances.KMSW
