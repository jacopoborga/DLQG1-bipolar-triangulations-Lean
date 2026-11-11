module

public import DirectedDistances.KMSW.XDPAdditivityAtCuts
public import DirectedDistances.KMSW.InfinitePresentPathCutVisit
public import DirectedDistances.KMSW.LeftmostGeodesicAssembly
public import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix

public section
namespace DirectedDistances.KMSW

open Quiver

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem presentVertex_eq_of_id_eq {w : ℕ → Fin 3}
    {x y : PresentVertex w} (h : x.id = y.id) : x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      simp only at h
      subst y
      rfl

/-- leftmost infinite LDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem InfinitePresentPath.firstVisit_mapCutVertex_prefix_isLongest
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments) :
    ∃ i,
      (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      IsLongest (P.initial i).2 ∧
      presentLdp (⟨0⟩ : PresentVertex w) ⟨v⟩ =
        (((P.initial i).2.length : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨j, hj⟩ := InfinitePresentPath.visits_mapCutVertex
    w hfin htrans hR hL hcut P
  have hex : ∃ n, (P.initial n).1 = (⟨v⟩ : PresentVertex w) := by
    rcases hj with hw | he
    · have hwest := InfinitePresentPath.edge_outgoing_at_initial w P j |>.2
      have hid : (P.initial j).1.id = v := hwest.symm.trans hw
      exact ⟨j, presentVertex_eq_of_id_eq hid⟩
    · have heast := InfinitePresentPath.edge_incoming_at_succ w P j |>.2
      have hid : (P.initial (j + 1)).1.id = v := heast.symm.trans he
      exact ⟨j + 1, presentVertex_eq_of_id_eq hid⟩
  let S : Set ℕ := {n | (P.initial n).1 = (⟨v⟩ : PresentVertex w)}
  have hS : S.Nonempty := by
    obtain ⟨n, hn⟩ := hex
    exact ⟨n, hn⟩
  let i := Nat.find hS
  have hi : (P.initial i).1 = (⟨v⟩ : PresentVertex w) := Nat.find_spec hS
  have hfirst : ∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w) := by
    intro j hji heq
    exact (Nat.find_min hS hji) heq
  have hpi := P.initial_isLongest w hP i
  refine ⟨i, hi, hfirst, hpi, ?_⟩
  rw [← hi]
  exact presentLdp_eq_length hpi

/-- leftmost infinite SDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem InfinitePresentPath.firstVisit_mapCutVertex_prefix_isShortest
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments) :
    ∃ i,
      (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      IsShortest (P.initial i).2 ∧
      sdp (⟨0⟩ : PresentVertex w) ⟨v⟩ = ((P.initial i).2.length : ℕ∞) := by
  obtain ⟨j, hj⟩ := InfinitePresentPath.visits_mapCutVertex
    w hfin htrans hR hL hcut P
  have hex : ∃ n, (P.initial n).1 = (⟨v⟩ : PresentVertex w) := by
    rcases hj with hw | he
    · have hwest := InfinitePresentPath.edge_outgoing_at_initial w P j |>.2
      have hid : (P.initial j).1.id = v := hwest.symm.trans hw
      exact ⟨j, presentVertex_eq_of_id_eq hid⟩
    · have heast := InfinitePresentPath.edge_incoming_at_succ w P j |>.2
      have hid : (P.initial (j + 1)).1.id = v := heast.symm.trans he
      exact ⟨j + 1, presentVertex_eq_of_id_eq hid⟩
  let S : Set ℕ := {n | (P.initial n).1 = (⟨v⟩ : PresentVertex w)}
  have hS : S.Nonempty := by
    obtain ⟨n, hn⟩ := hex
    exact ⟨n, hn⟩
  let i := Nat.find hS
  have hi : (P.initial i).1 = (⟨v⟩ : PresentVertex w) := Nat.find_spec hS
  have hfirst : ∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w) := by
    intro j hji heq
    exact (Nat.find_min hS hji) heq
  have hpi := P.initial_isShortest w hP i
  refine ⟨i, hi, hfirst, hpi, ?_⟩
  rw [← hi]
  exact ((isShortest_iff_length_eq_sdp _).1 hpi).symm

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem presentPath_split_at_length {w : ℕ → Fin 3}
    {x y : PresentVertex w} (q : Path x y) (n : ℕ) (hn : n ≤ q.length) :
    ∃ z, ∃ p : Path x z, ∃ r : Path z y, q = p.comp r ∧ p.length = n ∧
      pathEdgeList p = (pathEdgeList q).take n := by
  obtain ⟨z, p, r, hcomp, hlen⟩ := q.exists_eq_comp_of_le_length hn
  have hqEdges : pathEdgeList q = pathEdgeList p ++ pathEdgeList r := by
    rw [hcomp, pathEdgeList_comp]
  have htotal : q.length = n + r.length := by
    rw [hcomp, Path.length_comp, hlen]
  have hconcat : pathEdgeList p ++ pathEdgeList r =
      (pathEdgeList q).take n ++ (pathEdgeList q).drop n := by
    exact hqEdges.symm.trans (List.take_append_drop n (pathEdgeList q)).symm
  have hright : (pathEdgeList r).length = ((pathEdgeList q).drop n).length := by
    rw [pathEdgeList_length, List.length_drop, pathEdgeList_length, htotal]
    omega
  have hleft : (pathEdgeList p).length = ((pathEdgeList q).take n).length := by
    calc
      (pathEdgeList p).length = n := by rw [pathEdgeList_length, hlen]
      _ = min n (pathEdgeList q).length := by
        rw [pathEdgeList_length]
        exact (Nat.min_eq_left hn).symm
      _ = ((pathEdgeList q).take n).length := by rw [List.length_take]
  exact ⟨z, p, r, hcomp, hlen, List.append_inj_left hconcat hleft⟩

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem list_ofFn_get_take {α : Type} (xs : List α) (n : ℕ)
    (hn : n ≤ xs.length) :
    List.ofFn (fun j : Fin n => xs.get ⟨j.val, lt_of_lt_of_le j.isLt hn⟩) = xs.take n := by
  apply List.ext_get
  · simp only [List.length_ofFn, List.length_take]
    exact (Nat.min_eq_left hn).symm
  · intro j hj₁ hj₂
    simp only [List.get_eq_getElem] at hj₁ hj₂ ⊢
    rw [List.getElem_take]
    simp only [List.getElem_ofFn]

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private def prefixOptimal (longest : Bool) {w : ℕ → Fin 3}
    {x y : PresentVertex w} (p : Path x y) : Prop :=
  if longest then IsLongest p else IsShortest p

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem prefixOptimal_left {longest : Bool} {w : ℕ → Fin 3}
    {x y z : PresentVertex w} {p : Path x y} {q : Path y z}
    (h : prefixOptimal longest (p.comp q)) : prefixOptimal longest p := by
  cases longest
  · exact IsShortest.of_comp_left h
  · exact IsLongest.of_comp_left h

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem prefixOptimal_right {longest : Bool} {w : ℕ → Fin 3}
    {x y z : PresentVertex w} {p : Path x y} {q : Path y z}
    (h : prefixOptimal longest (p.comp q)) : prefixOptimal longest q := by
  cases longest
  · exact IsShortest.of_comp_right h
  · exact IsLongest.of_comp_right h

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem prefixOptimal_length_eq {longest : Bool} {w : ℕ → Fin 3}
    {x y z : PresentVertex w} (p : Path x y) (q : Path x z) (hyz : y = z)
    (hp : prefixOptimal longest p) (hq : prefixOptimal longest q) :
    p.length = q.length := by
  subst z
  cases longest
  · exact Nat.le_antisymm (hp q) (hq p)
  · exact Nat.le_antisymm (hq p) (hp q)

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem prefix_reendpoint {longest : Bool} {w : ℕ → Fin 3}
    {x y z : PresentVertex w} (q : Path x y) (hyz : y = z)
    (hq : prefixOptimal longest q) :
    ∃ q' : Path x z, prefixOptimal longest q' ∧ q'.length = q.length ∧
      pathEdgeList q' = pathEdgeList q := by
  subst z
  exact ⟨q, hq, rfl, rfl⟩

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private def firstVisitSplicedEdge {w : ℕ → Fin 3} {y : PresentVertex w}
    (P : InfinitePresentPath w ⟨0⟩) (q : Path (⟨0⟩ : PresentVertex w) y)
    (n : ℕ) : ℕ :=
  if hn : n < q.length then
    (pathEdgeList q).get ⟨n, by rw [pathEdgeList_length]; exact hn⟩
  else P.edge n

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem firstVisitSpliced_prefix_exists {w : ℕ → Fin 3}
    (longest : Bool) (P : InfinitePresentPath w ⟨0⟩)
    (hP : ∀ n, prefixOptimal longest (P.initial n).2) (i : ℕ)
    (q : Path (⟨0⟩ : PresentVertex w) (P.initial i).1)
    (hq : prefixOptimal longest q) (hqi : q.length = i) (b : ℕ) :
    ∃ z, ∃ p : Path (⟨0⟩ : PresentVertex w) z,
      p.length = b ∧
      pathEdgeList p = List.ofFn (fun j : Fin b => firstVisitSplicedEdge P q j.val) ∧
      prefixOptimal longest p := by
  by_cases hb : b ≤ i
  · obtain ⟨z, p, r, hcomp, hlen, hprefix⟩ :=
      presentPath_split_at_length q b (by rw [hqi]; exact hb)
    have hp : prefixOptimal longest p := by
      rw [hcomp] at hq
      exact prefixOptimal_left hq
    refine ⟨z, p, hlen, ?_, hp⟩
    calc
      pathEdgeList p = (pathEdgeList q).take b := hprefix
      _ = List.ofFn (fun j : Fin b =>
          (pathEdgeList q).get ⟨j.val, by rw [pathEdgeList_length, hqi]; omega⟩) :=
        (list_ofFn_get_take (pathEdgeList q) b
          (by rw [pathEdgeList_length, hqi]; exact hb)).symm
      _ = List.ofFn (fun j : Fin b => firstVisitSplicedEdge P q j.val) := by
        apply congrArg List.ofFn
        funext j
        have hj : j.val < q.length := by rw [hqi]; omega
        simp only [firstVisitSplicedEdge, dite_eq_left hj]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show i ≤ b by omega)
    obtain ⟨p, r, hcomp, hlen, hrlen, htail⟩ := P.exists_shift_split i k
    have hlen' : (q.comp r).length = i + k := by
      rw [Path.length_comp, hqi, hrlen]
    have hp : prefixOptimal longest (q.comp r) := by
      have hp := hP (i + k)
      have he : (q.comp r).length = (P.initial (i + k)).2.length := by
        rw [hlen', P.prefix_length]
      cases longest
      · exact IsShortest.of_length_eq hp he
      · exact IsLongest.of_length_eq hp he
    refine ⟨_, q.comp r, hlen', ?_, hp⟩
    rw [pathEdgeList_comp, htail, List.ofFn_add]
    have hfirst : List.ofFn (fun j : Fin i => firstVisitSplicedEdge P q j.val) =
        pathEdgeList q := by
      apply List.ext_get
      · simp only [List.length_ofFn, pathEdgeList_length, hqi]
      · intro j hj₁ hj₂
        have hj : j < q.length := by
          simpa only [pathEdgeList_length] using hj₂
        simp only [List.get_eq_getElem, List.getElem_ofFn,
          firstVisitSplicedEdge, dite_eq_left hj]
    have hlast : List.ofFn (fun j : Fin k => firstVisitSplicedEdge P q (i + j.val)) =
        List.ofFn (fun j : Fin k => P.edge (i + j.val)) := by
      apply congrArg List.ofFn
      funext j
      have hj : ¬i + j.val < q.length := by rw [hqi]; omega
      simp only [firstVisitSplicedEdge, dite_eq_right hj]
    simp only [Fin.val_castLE, Fin.val_natAdd, hfirst, hlast]

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem prefixOptimal_segments {w : ℕ → Fin 3}
    (longest : Bool) (P : InfinitePresentPath w ⟨0⟩)
    (hP : ∀ b, prefixOptimal longest (P.initial b).2) :
    ∀ a b, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun j : Fin b => P.edge j.val)).drop (a - 1) ∧
      prefixOptimal longest q := by
  intro a b ha hab
  obtain ⟨z, p, q, hcomp, hlen⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, q, ?_, ?_, ?_⟩
  · have htotal := P.prefix_length b
    rw [hcomp, Path.length_comp, hlen] at htotal
    omega
  · rw [← P.prefix_edges b, hcomp, pathEdgeList_comp, ← hlen,
      ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := hP b
    rw [hcomp] at hopt
    exact prefixOptimal_right hopt

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem exists_prefixOptimal_splice {w : ℕ → Fin 3}
    (longest : Bool) (P : InfinitePresentPath w ⟨0⟩)
    (hP : ∀ n, prefixOptimal longest (P.initial n).2)
    {y : PresentVertex w} (i : ℕ) (hi : (P.initial i).1 = y)
    (q : Path (⟨0⟩ : PresentVertex w) y) (hq : prefixOptimal longest q) :
    q.length = i ∧ ∃ S : InfinitePresentPath w ⟨0⟩,
      (∀ n, prefixOptimal longest (S.initial n).2) ∧
      ∀ n, S.edge n = firstVisitSplicedEdge P q n := by
  classical
  have hqi : q.length = i := by
    have he := prefixOptimal_length_eq (P.initial i).2 q hi (hP i) hq
    rw [P.prefix_length] at he
    exact he.symm
  obtain ⟨q', hq', hlen, he⟩ := prefix_reendpoint q hi.symm hq
  let H := firstVisitSpliced_prefix_exists longest P hP i q' hq' (hlen.trans hqi)
  let S : InfinitePresentPath w ⟨0⟩ := {
    edge := firstVisitSplicedEdge P q'
    initial b := ⟨(H b).choose, (H b).choose_spec.choose⟩
    prefix_length b := (H b).choose_spec.choose_spec.1
    prefix_edges b := (H b).choose_spec.choose_spec.2.1 }
  refine ⟨hqi, S, fun b => (H b).choose_spec.choose_spec.2.2, ?_⟩
  intro n
  change firstVisitSplicedEdge P q' n = firstVisitSplicedEdge P q n
  simp only [firstVisitSplicedEdge, hlen]
  split
  · simp only [List.get_eq_getElem]
    congr 1
  · rfl

/-- leftmost infinite LDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem InfinitePresentPath.exists_firstVisit_mapCutVertex_splice
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments)
    (q : Path (⟨0⟩ : PresentVertex w) ⟨v⟩) (hq : IsLongest q) :
    ∃ i, (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      q.length = i ∧
      ∃ S : InfinitePresentPath w ⟨0⟩, S.HasLongestSegments ∧
        ∀ n, S.edge n = if hn : n < q.length then
          (pathEdgeList q).get ⟨n, by rw [pathEdgeList_length]; exact hn⟩ else P.edge n := by
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isLongest
    w hfin htrans hR hL hcut hP
  obtain ⟨hqi, S, hS, he⟩ := exists_prefixOptimal_splice true P
    (P.initial_isLongest w hP) i hi q hq
  exact ⟨i, hi, hfirst, hqi, S, prefixOptimal_segments true S hS, he⟩
/-- leftmost infinite SDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem InfinitePresentPath.exists_firstVisit_mapCutVertex_sdp_splice
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments)
    (q : Path (⟨0⟩ : PresentVertex w) ⟨v⟩) (hq : IsShortest q) :
    ∃ i, (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      q.length = i ∧
      ∃ S : InfinitePresentPath w ⟨0⟩, S.HasShortestSegments ∧
        ∀ n, S.edge n = if hn : n < q.length then
          (pathEdgeList q).get ⟨n, by rw [pathEdgeList_length]; exact hn⟩ else P.edge n := by
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isShortest
    w hfin htrans hR hL hcut hP
  obtain ⟨hqi, S, hS, he⟩ := exists_prefixOptimal_splice false P
    (P.initial_isShortest w hP) i hi q hq
  exact ⟨i, hi, hfirst, hqi, S, prefixOptimal_segments false S hS, he⟩

/-- leftmost infinite XDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
private theorem finite_prefix_comparison
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (P S : InfinitePresentPath w ⟨0⟩) {y : PresentVertex w}
    (q : Path (⟨0⟩ : PresentVertex w) y) (i : ℕ) (hlen : q.length = i)
    (he : ∀ n, S.edge n = firstVisitSplicedEdge P q n)
    (hleft : GeodesicFirstDivergenceRightOf w hfin hL htrans hR 0 P S) :
    pathEdgeList q = pathEdgeList (P.initial i).2 ∨
      ∃ n : Fin q.length,
        (∀ k : Fin q.length, k.val < n.val →
          P.edge k.val = (pathEdgeList q).get
            ⟨k.val, by rw [pathEdgeList_length]; exact k.isLt⟩) ∧
        (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
          (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf (P.edge n.val) <
        (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
          (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf
          ((pathEdgeList q).get ⟨n.val, by rw [pathEdgeList_length]; exact n.isLt⟩) := by
  classical
  by_cases hall : ∀ n : Fin q.length, P.edge n.val = (pathEdgeList q).get
      ⟨n.val, by rw [pathEdgeList_length]; exact n.isLt⟩
  · left
    rw [P.prefix_edges, ← hlen]
    apply List.ext_get
    · rw [pathEdgeList_length, List.length_ofFn]
    · intro n hn hn'
      have hnq : n < q.length := by simpa only [pathEdgeList_length] using hn
      simpa only [List.get_eq_getElem, List.getElem_ofFn] using (hall ⟨n, hnq⟩).symm
  · push Not at hall
    obtain ⟨n₀, hn₀⟩ := hall
    have hex : ∃ n, ∃ hn : n < q.length, P.edge n ≠ (pathEdgeList q).get
        ⟨n, by rw [pathEdgeList_length]; exact hn⟩ := ⟨n₀.val, n₀.isLt, hn₀⟩
    let n := Nat.find hex
    obtain ⟨hn, hne⟩ := Nat.find_spec hex
    have hbefore : ∀ k (hk : k < q.length), k < n → P.edge k =
        (pathEdgeList q).get ⟨k, by rw [pathEdgeList_length]; exact hk⟩ := by
      intro k hk hkn
      by_contra hne
      exact Nat.find_min hex hkn ⟨hk, hne⟩
    have hstream (k : ℕ) (hk : k < q.length) :
        S.edge k = (pathEdgeList q).get
          ⟨k, by rw [pathEdgeList_length]; exact hk⟩ := by
      rw [he, firstVisitSplicedEdge, dite_eq_left hk]
    have hprior : ∀ k, k < n → P.edge k = S.edge k := by
      intro k hk
      have hkq : k < q.length := lt_trans hk hn
      rw [hstream k hkq]
      exact hbefore k hkq hk
    have hdiff : P.edge n ≠ S.edge n := by
      rw [hstream n hn]
      exact hne
    have hstrict := GeodesicFirstDivergenceRightOf.strict_of_ne
      w hfin hL htrans hR 0 P S hleft n hprior hdiff
    rw [hstream n hn] at hstrict
    exact Or.inr ⟨⟨n, hn⟩, fun k hk => hbefore k.val k.isLt hk, hstrict⟩

/-- leftmost infinite LDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem kmswLeftmostLdpPath_firstVisit_mapCutVertex_prefix_leftmost
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      ∀ q : Path (⟨0⟩ : PresentVertex w) ⟨v⟩, IsLongest q →
        q.length = i ∧ (pathEdgeList q = pathEdgeList (P.initial i).2 ∨
          ∃ n : Fin q.length,
            (∀ k : Fin q.length, k.val < n.val →
              P.edge k.val = (pathEdgeList q).get
                ⟨k.val, by rw [pathEdgeList_length]; exact k.isLt⟩) ∧
            (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
              (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf (P.edge n.val) <
            (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
              (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf
              ((pathEdgeList q).get
                ⟨n.val, by rw [pathEdgeList_length]; exact n.isLt⟩)) := by
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  have hP := kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isLongest
    w hfin htrans hR hL hcut hP
  refine ⟨i, hi, hfirst, ?_⟩
  intro q hq
  obtain ⟨hlen, S, hS, he⟩ := exists_prefixOptimal_splice true P
    (P.initial_isLongest w hP) i hi q hq
  have hleft := kmswLeftmostLdpPath_firstDivergenceRightOf w hfin hL htrans hR 0 hg
    S (prefixOptimal_segments true S hS)
  exact ⟨hlen, finite_prefix_comparison w hfin hL htrans hR P S q i hlen he hleft⟩
/-- leftmost infinite SDP geodesic restricted to the past of a map cut vertex;
leftmost means first-divergence leftmost; renewal times T_m are not defined or
used; not the paper result. -/
theorem kmswLeftmostSdpPath_firstVisit_mapCutVertex_prefix_leftmost
    (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    {v : ℕ} (hcut : mapCutVertex w hfin v)
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = (⟨v⟩ : PresentVertex w) ∧
      (∀ j < i, (P.initial j).1 ≠ (⟨v⟩ : PresentVertex w)) ∧
      ∀ q : Path (⟨0⟩ : PresentVertex w) ⟨v⟩, IsShortest q →
        q.length = i ∧ (pathEdgeList q = pathEdgeList (P.initial i).2 ∨
          ∃ n : Fin q.length,
            (∀ k : Fin q.length, k.val < n.val →
              P.edge k.val = (pathEdgeList q).get
                ⟨k.val, by rw [pathEdgeList_length]; exact k.isLt⟩) ∧
            (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
              (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf (P.edge n.val) <
            (kmswPrefixOutgoingEdges w hfin hL htrans hR 0
              (List.ofFn (fun k : Fin n.val => P.edge k.val))).idxOf
              ((pathEdgeList q).get
                ⟨n.val, by rw [pathEdgeList_length]; exact n.isLt⟩)) := by
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  have hP := kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, _⟩ := P.firstVisit_mapCutVertex_prefix_isShortest
    w hfin htrans hR hL hcut hP
  refine ⟨i, hi, hfirst, ?_⟩
  intro q hq
  obtain ⟨hlen, S, hS, he⟩ := exists_prefixOptimal_splice false P
    (P.initial_isShortest w hP) i hi q hq
  have hleft := kmswLeftmostSdpPath_firstDivergenceRightOf w hfin hL htrans hR 0 hg
    S (prefixOptimal_segments false S hS)
  exact ⟨hlen, finite_prefix_comparison w hfin hL htrans hR P S q i hlen he hleft⟩

end DirectedDistances.KMSW
