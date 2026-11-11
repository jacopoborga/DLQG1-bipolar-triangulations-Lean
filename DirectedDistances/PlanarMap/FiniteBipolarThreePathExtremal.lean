/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarThreePathWalk
import Mathlib.Data.List.Lex

/-! # Extremal connectors for the three-path region

Helper toward Definition 3.13, in the finite bipolar scope of the author

Finite lexicographic optimization of clockwise departure ranks produces a
connector dominating every same-index departure. For extremal connectors,
the acyclic cross-splice theorem forces every common vertex to have the
same visit index. The departure criterion then gives the required filled
region containment. Mutual containment proves uniqueness of the dart list.
This module does not identify extremality with the ordinary-distance API
or establish the finite-submap transport needed for infinite-map applications. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- Helper toward Definition 3.13: simple connector lengths are bounded by
the finite vertex carrier, independently of their endpoints. -/
theorem SimpleDirectedDartPath.length_lt_card_three_path
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) : n < M.toCombinatorialMap.numVertices := by
  classical
  have h := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at h
  change n + 1 ≤ M.toCombinatorialMap.numVertices at h
  omega

/-- Helper toward Definition 3.13: whenever a connector exists, its finite
length family attains either extremum. -/
theorem BipolarMapWithBoundaryBase.exists_extremal_connector_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {k : ℕ}
    (R : SimpleDirectedDartPath B.map x y k) :
    ∃ n, ∃ _P : SimpleDirectedDartPath B.map x y n,
      (match choice with
       | .ldp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map x y m), m ≤ n
       | .sdp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map x y m), n ≤ m) := by
  classical
  let S := (Finset.range B.map.toCombinatorialMap.numVertices).filter
    (fun n => Nonempty (SimpleDirectedDartPath B.map x y n))
  have hmem {n : ℕ} (P : SimpleDirectedDartPath B.map x y n) : n ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr P.length_lt_card_three_path, ⟨P⟩⟩
  have hne : S.Nonempty := ⟨k, hmem R⟩
  cases choice with
  | ldp =>
    obtain ⟨P⟩ := (Finset.mem_filter.mp (S.max'_mem hne)).2
    exact ⟨S.max' hne, P, fun Q => S.le_max' _ (hmem Q)⟩
  | sdp =>
    obtain ⟨P⟩ := (Finset.mem_filter.mp (S.min'_mem hne)).2
    exact ⟨S.min' hne, P, fun Q => S.min'_le _ (hmem Q)⟩

namespace BipolarMapWithBoundaryBase

/-- Helper toward Definition 3.13: clockwise distance to the outgoing
extreme. At the sink this auxiliary rank is zero; no directed departure
there exists. All other incident darts have a unique first hitting time. -/
@[expose] noncomputable def threePathDepartureRank
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) : ℕ := by
  classical
  exact if ht : dartTailVertex B.map d ≠ B.sink then
    let hc : Equiv.Perm.SameCycle B.map.rot.symm d
        (B.out (dartTailVertex B.map d) ht) := Equiv.Perm.sameCycle_inv.mpr
      (Quotient.exact (B.out_spec (dartTailVertex B.map d) ht).1.symm)
    Nat.find hc.exists_nat_pow_eq
  else 0

/-- Helper toward Definition 3.13: the departure rank is precisely the
first clockwise hitting time of the outgoing extreme. -/
theorem threePathDepartureRank_spec
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D)
    (ht : dartTailVertex B.map d ≠ B.sink) :
    (B.map.rot.symm ^ B.threePathDepartureRank d) d =
        B.out (dartTailVertex B.map d) ht ∧
      ∀ j < B.threePathDepartureRank d,
        (B.map.rot.symm ^ j) d ≠ B.out (dartTailVertex B.map d) ht := by
  classical
  unfold threePathDepartureRank
  rw [dite_eq_left ht]
  dsimp only
  constructor
  · exact Nat.find_spec (p := fun k => (B.map.rot.symm ^ k) d =
      B.out (dartTailVertex B.map d) ht) _
  · intro j hj
    exact Nat.find_min (p := fun k => (B.map.rot.symm ^ k) d =
      B.out (dartTailVertex B.map d) ht) _ hj

/-- Helper toward Definition 3.13: the clockwise weak-right departure
sector is exactly comparison of the first hitting ranks. -/
theorem clockwise_departure_iff_rank_le_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {p q : D}
    (_hp : B.map.tail p) (_hq : B.map.tail q)
    (hv : dartTailVertex B.map q = dartTailVertex B.map p)
    (ht : dartTailVertex B.map p ≠ B.sink) :
    (q = p ∨
      q ∈ openRotationInterval_three_path B.map.rot.symm p
        (B.out (dartTailVertex B.map p) ht) ∨
      (q = B.out (dartTailVertex B.map p) ht ∧ q ≠ p)) ↔
      B.threePathDepartureRank q ≤ B.threePathDepartureRank p := by
  let ρ := B.map.rot.symm
  let o := B.out (dartTailVertex B.map p) ht
  let k := B.threePathDepartureRank p
  let l := B.threePathDepartureRank q
  obtain ⟨hk, hkmin⟩ := B.threePathDepartureRank_spec p ht
  obtain ⟨hl, hlmin⟩ := B.threePathDepartureRank_spec q (fun he => ht (hv.symm.trans he))
  have hl' : (ρ ^ l) q = o := by simpa only [hv] using hl
  have hlmin' : ∀ j < l, (ρ ^ j) q ≠ o := by simpa only [hv] using hlmin
  change (ρ ^ k) p = o at hk
  change (∀ j < k, (ρ ^ j) p ≠ o) at hkmin
  change _ ↔ l ≤ k
  constructor
  · rintro (rfl | ⟨k', hk', hkmin', j, hj, hjk, hjq⟩ | ⟨hqo, _⟩)
    · exact le_rfl
    · have hkeq : k' = k := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with hlt | hgt
        · exact hkmin k' hlt hk'
        · exact hkmin' k hgt hk
      subst k'
      have hhit : (ρ ^ (k - j)) q = o := by
        rw [← hjq, ← Equiv.Perm.mul_apply, ← pow_add,
          Nat.sub_add_cancel (by omega : j ≤ k), hk]
      have hle : l ≤ k - j := by
        by_contra hn
        exact hlmin' (k - j) (by omega) hhit
      omega
    · have hz : l = 0 := by
        by_contra hn
        exact hlmin' 0 (by omega) (by simpa only [pow_zero, Equiv.Perm.one_apply] using hqo)
      omega
  · intro hlk
    have hqp : q = (ρ ^ (k - l)) p := by
      apply (ρ ^ l).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hlk, hk, hl']
    by_cases he : l = k
    · left
      simpa only [he, Nat.sub_self, pow_zero, Equiv.Perm.one_apply] using hqp
    · by_cases hz : l = 0
      · right; right
        have hqo : q = o := by simpa only [hz, pow_zero, Equiv.Perm.one_apply] using hl'
        refine ⟨hqo, ?_⟩
        intro hqeq
        have hzero := hkmin 0 (by omega : 0 < k)
        exact hzero (by simpa only [pow_zero, Equiv.Perm.one_apply] using hqeq.symm.trans hqo)
      · exact .inr (.inl ⟨k, hk, hkmin, k - l, by omega, by omega, hqp.symm⟩)

/-- Helper toward Definition 3.13: the lists of darts realized by
connectors of any fixed length form a finite set, proved from the finite
dart carrier without a finiteness premise on paths. -/
theorem finite_connector_dart_lists_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (x y : MapVertex B.map) (n : ℕ) :
    Set.Finite {ds : List D | ∃ P : SimpleDirectedDartPath B.map x y n, P.darts = ds} := by
  classical
  apply (Set.finite_range (fun f : Fin n → D => List.ofFn f)).subset
  rintro ds ⟨P, rfl⟩
  have h : P.darts.length = n := P.darts_length
  have hrep : ∀ (ds : List D), ds.length = n →
      ds ∈ Set.range (fun f : Fin n → D => List.ofFn f) := by
    intro ds hds
    subst n
    exact ⟨ds.get, List.ofFn_get ds⟩
  exact hrep P.darts h

/-- Helper toward Definition 3.13: at each fixed realized length, a
connector maximizes the lexicographic list of clockwise departure ranks. -/
theorem exists_lex_max_connector_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (R : SimpleDirectedDartPath B.map x y n) :
    ∃ P : SimpleDirectedDartPath B.map x y n,
      ∀ Q : SimpleDirectedDartPath B.map x y n,
        Q.darts.map B.threePathDepartureRank ≤ P.darts.map B.threePathDepartureRank := by
  classical
  obtain ⟨ds, ⟨P, hP⟩, hmax⟩ := Set.exists_max_image
    {ds : List D | ∃ P : SimpleDirectedDartPath B.map x y n, P.darts = ds}
    (List.map B.threePathDepartureRank)
    (B.finite_connector_dart_lists_three_path x y n) ⟨R.darts, R, rfl⟩
  refine ⟨P, fun Q => ?_⟩
  rw [← hP] at hmax
  exact hmax Q.darts ⟨Q, rfl⟩

 
private theorem cast_length_darts_three_path
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M x y a) (h : a = b) :
    (h ▸ P : SimpleDirectedDartPath M x y b).darts = P.darts := by
  cases h
  rfl

/-- Helper toward Definition 3.13: finite lexicographic optimization gives
a connector dominating all competitors at every contact with the same
visit index. Splicing is simple by acyclicity. -/
theorem exists_connector_rank_dominating_same_index_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (R : SimpleDirectedDartPath B.map x y n) :
    ∃ P : SimpleDirectedDartPath B.map x y n,
      ∀ (Q : SimpleDirectedDartPath B.map x y n) (i : Fin n),
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ →
        B.threePathDepartureRank (Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩) ≤
          B.threePathDepartureRank (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩) := by
  obtain ⟨P, hmax⟩ := B.exists_lex_max_connector_three_path R
  refine ⟨P, ?_⟩
  intro Q i hv
  by_contra hn
  have hlt := Nat.lt_of_not_ge hn
  let iv : Fin (n + 1) := ⟨i.val, by have := i.isLt; omega⟩
  let QS := Q.suffix iv
  let S : SimpleDirectedDartPath B.map
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; have := i.isLt; omega⟩) y
      (n - i.val) :=
    { QS with start_vertex := QS.start_vertex.trans hv.symm }
  let T₀ := (P.prefix iv).appendAcyclic B.map B.acyclic S
  have hlen : i.val + (n - i.val) = n := by have := i.isLt; omega
  let T : SimpleDirectedDartPath B.map x y n := hlen ▸ T₀
  have hTdarts : T.darts = P.darts.take i.val ++ Q.darts.drop i.val := by
    rw [cast_length_darts_three_path T₀ hlen,
      SimpleDirectedDartPath.appendAcyclic_darts, SimpleDirectedDartPath.prefix_darts]
    exact congrArg (fun ds => P.darts.take i.val ++ ds) (Q.suffix_darts iv)
  have hiP : i.val < P.darts.length := by rw [P.darts_length]; exact i.isLt
  have hiQ : i.val < Q.darts.length := by rw [Q.darts_length]; exact i.isLt
  have hlex : P.darts.map B.threePathDepartureRank < T.darts.map B.threePathDepartureRank := by
    rw [hTdarts, List.map_append]
    have hsplit : P.darts.map B.threePathDepartureRank =
        (P.darts.take i.val).map B.threePathDepartureRank ++
          (P.darts.drop i.val).map B.threePathDepartureRank := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit]
    apply List.Lex.append_left (· < ·)
    rw [List.drop_eq_getElem_cons hiP, List.drop_eq_getElem_cons hiQ, List.map_cons, List.map_cons]
    exact List.Lex.rel hlt
  exact (not_lt_of_ge (hmax T)) hlex

/-- Helper toward Definition 3.13: there exists an extremal connector
whose closed three-path region contains every extremal connector. The
endpoints are arbitrary, overlaps are allowed, and the supplied connector
is the only reachability hypothesis. -/
theorem exists_extremal_connector_containing_all_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {k : ℕ}
    (R : SimpleDirectedDartPath B.map x y k) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map x y n,
      (match choice with
       | .ldp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map x y m), m ≤ n
       | .sdp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map x y m), n ≤ m) ∧
      ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
        (match choice with
         | .ldp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), j ≤ m
         | .sdp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), m ≤ j) →
        ∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P := by
  obtain ⟨n, R₀, hR⟩ := B.exists_extremal_connector_three_path choice R
  obtain ⟨P, hdom⟩ := B.exists_connector_rank_dominating_same_index_three_path R₀
  refine ⟨n, P, hR, ?_⟩
  intro m Q hQ
  have hmn : m = n := by
    cases choice with
    | ldp => exact Nat.le_antisymm (hR Q) (hQ P)
    | sdp => exact Nat.le_antisymm (hQ P) (hR Q)
  subst m
  apply (B.connector_subset_threePathFilledDarts_iff_clockwise_departures P Q).mpr
  intro i q hq hv ht
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hq
  have hv' :
      P.vertices.get ⟨i.val, by have := i.isLt; have := P.darts_length; rw [P.vertices_length]; omega⟩ =
      Q.vertices.get ⟨j.val, by have := j.isLt; have := Q.darts_length; rw [Q.vertices_length]; omega⟩ :=
    (P.edge_step i).2.2.1.trans (hv.symm.trans (Q.edge_step j).2.2.1.symm)
  let i' : Fin (n + 1) := ⟨i.val, by have := i.isLt; have := P.darts_length; omega⟩
  let j' : Fin (n + 1) := ⟨j.val, by have := j.isLt; have := Q.darts_length; omega⟩
  have hij := B.extremal_connector_common_indices_eq_three_path choice P Q hR i' j' hv'
  have hijval : i.val = j.val := congrArg Fin.val hij
  apply (B.clockwise_departure_iff_rank_le_three_path
    (P.edge_step i).2.1 (Q.edge_step j).2.1 hv ht).mpr
  have hv'' :
      P.vertices.get ⟨i.val, by have := i.isLt; have := P.darts_length; rw [P.vertices_length]; omega⟩ =
      Q.vertices.get ⟨i.val, by have := i.isLt; have := P.darts_length; rw [Q.vertices_length]; omega⟩ := by
    simpa only [hijval] using hv'
  have hr := hdom Q ⟨i.val, by have := i.isLt; have := P.darts_length; omega⟩ hv''
  have hji : j = ⟨i.val, by have := i.isLt; have := P.darts_length; rw [Q.darts_length]; omega⟩ :=
    Fin.ext hijval.symm
  rw [hji]
  exact hr

/-- Helper toward Definition 3.13: two extremal connectors satisfying the
three-path containment characterization have identical dart lists. -/
theorem extremal_connector_darts_eq_of_containing_all_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m)
    (hP : match choice with
      | .ldp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), j ≤ n
      | .sdp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), n ≤ j)
    (hQ : match choice with
      | .ldp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), j ≤ m
      | .sdp => ∀ {j : ℕ} (_S : SimpleDirectedDartPath B.map x y j), m ≤ j)
    (hPc : ∀ {j : ℕ} (S : SimpleDirectedDartPath B.map x y j),
      (match choice with
       | .ldp => ∀ {a : ℕ} (_T : SimpleDirectedDartPath B.map x y a), a ≤ j
       | .sdp => ∀ {a : ℕ} (_T : SimpleDirectedDartPath B.map x y a), j ≤ a) →
      ∀ d ∈ S.darts, d ∈ B.threePathFilledDarts P)
    (hQc : ∀ {j : ℕ} (S : SimpleDirectedDartPath B.map x y j),
      (match choice with
       | .ldp => ∀ {a : ℕ} (_T : SimpleDirectedDartPath B.map x y a), a ≤ j
       | .sdp => ∀ {a : ℕ} (_T : SimpleDirectedDartPath B.map x y a), j ≤ a) →
      ∀ d ∈ S.darts, d ∈ B.threePathFilledDarts Q) : P.darts = Q.darts := by
  cases choice <;>
    exact B.darts_eq_of_mutual_threePathFilledDarts P Q (hPc Q hQ) (hQc P hP)

end BipolarMapWithBoundaryBase
end DirectedDistances.PlanarMap
