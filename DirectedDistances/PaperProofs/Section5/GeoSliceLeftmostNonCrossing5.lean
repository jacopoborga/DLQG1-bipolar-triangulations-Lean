/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing4
public import DirectedDistances.PaperProofs.Section5.GeoInftyCommonMeeting

/-! # Leftmost non-crossing for adjacent geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

private def meetingOptimal (longest : Bool) {w : ℕ → Fin 3}
    {x y : PresentVertex w} (p : Path x y) : Prop :=
  if longest then IsLongest p else IsShortest p

private theorem meetingOptimal_initial {w : ℕ → Fin 3} {x : ℕ}
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments) (n : ℕ) :
    meetingOptimal longest (P.initial n).2 := by
  cases longest
  · exact P.initial_isShortest w hP n
  · exact P.initial_isLongest w hP n

private theorem meetingOptimal_replace {w : ℕ → Fin 3} {x y : PresentVertex w}
    {longest : Bool} {p q : Path x y} (hp : meetingOptimal longest p)
    (hlen : q.length = p.length) : meetingOptimal longest q := by
  cases longest
  · exact hp.of_length_eq hlen
  · exact hp.of_length_eq hlen

private theorem meetingOptimal_left {w : ℕ → Fin 3} {x y z : PresentVertex w}
    {longest : Bool} {p : Path x y} {q : Path y z}
    (hp : meetingOptimal longest (p.comp q)) : meetingOptimal longest p := by
  cases longest
  · exact hp.of_comp_left
  · exact hp.of_comp_left

private theorem meetingOptimal_right {w : ℕ → Fin 3} {x y z : PresentVertex w}
    {longest : Bool} {p : Path x y} {q : Path y z}
    (hp : meetingOptimal longest (p.comp q)) : meetingOptimal longest q := by
  cases longest
  · exact hp.of_comp_right
  · exact hp.of_comp_right

private theorem meetingOptimal_segments {w : ℕ → Fin 3} {x : ℕ}
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩)
    (hP : ∀ n, meetingOptimal longest (P.initial n).2) :
    if longest then P.HasLongestSegments else P.HasShortestSegments := by
  have hs : ∀ a b, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun j : Fin b => P.edge j.val)).drop (a - 1) ∧
      meetingOptimal longest q := by
    intro a b ha hab
    obtain ⟨z, p, q, hpq, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
      (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
    refine ⟨z, q, ?_, ?_, ?_⟩
    · have hl := P.prefix_length b
      rw [hpq, Path.length_comp, hp] at hl
      omega
    · rw [← P.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
      exact List.drop_left.symm
    · have ho := hP b
      rw [hpq] at ho
      exact meetingOptimal_right ho
  cases longest <;> exact hs

private def meetingReplacementEdge {w : ℕ → Fin 3} {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) {y : PresentVertex w}
    (q : Path (⟨x⟩ : PresentVertex w) y) (n : ℕ) : ℕ :=
  if hn : n < q.length then
    (pathEdgeList q).get ⟨n, by rw [pathEdgeList_length]; exact hn⟩
  else P.edge n

private theorem meetingReplacement_prefix {w : ℕ → Fin 3} {x : ℕ}
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments)
    (a : ℕ) (q : Path (⟨x⟩ : PresentVertex w) (P.initial a).1)
    (hq : q.length = a) (b : ℕ) :
    ∃ z, ∃ p : Path (⟨x⟩ : PresentVertex w) z,
      p.length = b ∧
      pathEdgeList p = List.ofFn (fun j : Fin b => meetingReplacementEdge P q j.val) ∧
      meetingOptimal longest p := by
  have hopt : meetingOptimal longest q :=
    meetingOptimal_replace (meetingOptimal_initial longest P hP a)
      (hq.trans (P.prefix_length a).symm)
  by_cases hb : b ≤ a
  · obtain ⟨z, p, r, hcomp, hlen⟩ := q.exists_eq_comp_of_le_length (n := b) (by omega)
    have hp : meetingOptimal longest p := by
      rw [hcomp] at hopt
      exact meetingOptimal_left hopt
    refine ⟨z, p, hlen, ?_, hp⟩
    have he : pathEdgeList p = (pathEdgeList q).take b := by
      rw [hcomp, pathEdgeList_comp, ← hlen, ← pathEdgeList_length p]
      simp only [List.take_left]
    rw [he]
    apply List.ext_get
    · simp only [List.length_take, pathEdgeList_length, hq, List.length_ofFn,
        Nat.min_eq_left hb]
    · intro j hj₁ hj₂
      have hj : j < q.length := by
        simp only [List.length_ofFn] at hj₂
        omega
      simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn,
        meetingReplacementEdge, dite_eq_left hj]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ b by omega)
    obtain ⟨p, r, hcomp, hlen, hrlen, htail⟩ := P.exists_shift_split a n
    refine ⟨_, q.comp r, by rw [Path.length_comp, hq, hrlen], ?_, ?_⟩
    · rw [pathEdgeList_comp, htail, List.ofFn_add]
      have hfirst : List.ofFn (fun j : Fin a => meetingReplacementEdge P q j.val) =
          pathEdgeList q := by
        apply List.ext_get
        · simp only [List.length_ofFn, pathEdgeList_length, hq]
        · intro j hj₁ hj₂
          have hj : j < q.length := by simpa only [pathEdgeList_length] using hj₂
          simp only [List.get_eq_getElem, List.getElem_ofFn,
            meetingReplacementEdge, dite_eq_left hj]
      have hlast : List.ofFn (fun j : Fin n => meetingReplacementEdge P q (a + j.val)) =
          List.ofFn (fun j : Fin n => P.edge (a + j.val)) := by
        apply congrArg List.ofFn
        funext j
        have hj : ¬a + j.val < q.length := by omega
        simp only [meetingReplacementEdge, dite_eq_right hj]
      simp only [Fin.val_castLE, Fin.val_natAdd, hfirst, hlast]
    · apply meetingOptimal_replace (meetingOptimal_initial longest P hP (a + n))
      rw [Path.length_comp, hq, hrlen, P.prefix_length]

private theorem exists_meetingReplacement {w : ℕ → Fin 3} {x : ℕ}
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments)
    (a : ℕ) (q : Path (⟨x⟩ : PresentVertex w) (P.initial a).1) (hq : q.length = a) :
    ∃ S : InfinitePresentPath w ⟨x⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) ∧
      ∀ n, S.edge n = meetingReplacementEdge P q n := by
  classical
  let hp := meetingReplacement_prefix longest P hP a q hq
  let S : InfinitePresentPath w ⟨x⟩ := {
    edge := meetingReplacementEdge P q
    initial := fun b => ⟨(hp b).choose, (hp b).choose_spec.choose⟩
    prefix_length := fun b => (hp b).choose_spec.choose_spec.1
    prefix_edges := fun b => (hp b).choose_spec.choose_spec.2.1 }
  exact ⟨S, meetingOptimal_segments longest S
    (fun b => (hp b).choose_spec.choose_spec.2.2), fun _ => rfl⟩

private theorem meetingOptimal_length_eq {w : ℕ → Fin 3}
    {x x' y y' : PresentVertex w} {longest : Bool}
    (p : Path x y) (q : Path x' y') (hx : x = x') (hy : y = y')
    (hp : meetingOptimal longest p) (hq : meetingOptimal longest q) :
    p.length = q.length := by
  subst x'
  subst y'
  cases longest
  · exact Nat.le_antisymm (hp q) (hq p)
  · exact Nat.le_antisymm (hq p) (hp q)

private theorem meeting_transport_path {w : ℕ → Fin 3}
    {x x' y y' : PresentVertex w} (q : Path x y) (hx : x = x') (hy : y = y') :
    ∃ q' : Path x' y', q'.length = q.length ∧ pathEdgeList q' = pathEdgeList q := by
  subst x'
  subst y'
  exact ⟨q, rfl, rfl⟩

private theorem exists_competitor_departing_at_meeting {w : ℕ → Fin 3} {x y : ℕ}
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments)
    (hQ : if longest then Q.HasLongestSegments else Q.HasShortestSegments)
    (i j a b : ℕ) (hia : i < a) (hjb : j < b)
    (hij : (P.initial i).1 = (Q.initial j).1)
    (hab : (P.initial a).1 = (Q.initial b).1) :
    ∃ S : InfinitePresentPath w ⟨x⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) ∧
      S.edge i = Q.edge j := by
  obtain ⟨pp, pr, hpr, hpp, hprlen, hpre⟩ := P.exists_shift_split i (a - i)
  obtain ⟨qp, qr, hqr, hqp, hqrlen, hqre⟩ := Q.exists_shift_split j (b - j)
  have hai : i + (a - i) = a := by omega
  have hbj : j + (b - j) = b := by omega
  have hoptP := meetingOptimal_initial longest P hP (i + (a - i))
  have hoptQ := meetingOptimal_initial longest Q hQ (j + (b - j))
  rw [hpr] at hoptP
  rw [hqr] at hoptQ
  have hlen := meetingOptimal_length_eq pr qr hij (by simpa only [hai, hbj] using hab)
    (meetingOptimal_right hoptP) (meetingOptimal_right hoptQ)
  obtain ⟨r, hrlen, hre⟩ := meeting_transport_path qr hij.symm
    (by simpa only [hai, hbj] using hab.symm)
  let q := (P.initial i).2.comp r
  have hq : q.length = a := by
    dsimp [q]
    rw [Path.length_comp, P.prefix_length, hrlen, ← hlen, hprlen, hai]
  obtain ⟨S, hS, he⟩ := exists_meetingReplacement longest P hP a q hq
  refine ⟨S, hS, ?_⟩
  have hiq : i < q.length := by omega
  rw [he, meetingReplacementEdge, dite_eq_left hiq]
  change (pathEdgeList q)[i]'(by rw [pathEdgeList_length]; exact hiq) = Q.edge j
  simp only [q, pathEdgeList_comp, List.getElem_append, pathEdgeList_length,
    P.prefix_length, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self, hre, hqre,
    List.getElem_ofFn, Nat.add_zero]

private theorem presentVertex_eq_of_meeting_id {w : ℕ → Fin 3}
    {u v : PresentVertex w} (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem initial_eq_of_edge_eq {w : ℕ → Fin 3} {x y : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    {i j : ℕ} (he : P.edge i = Q.edge j) : (P.initial i).1 = (Q.initial j).1 := by
  apply presentVertex_eq_of_meeting_id
  exact (P.edge_outgoing_at_initial w i).2.symm.trans
    ((congrArg (edgeWest w) he).trans (Q.edge_outgoing_at_initial w j).2)

private theorem leftmost_edge_eq_at_meeting {w : ℕ → Fin 3} {x y : ℕ}
    (hf : KMSWFiniteIncidence w)
    (hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A))
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments)
    (hQ : if longest then Q.HasLongestSegments else Q.HasShortestSegments)
    (hleftP : ∀ S : InfinitePresentPath w ⟨x⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w hf hfam P S)
    (hleftQ : ∀ S : InfinitePresentPath w ⟨y⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w hf hfam Q S)
    (hco : ∃ a b, ∀ n, P.edge (a + n) = Q.edge (b + n))
    (i j : ℕ) (hij : (P.initial i).1 = (Q.initial j).1) : P.edge i = Q.edge j := by
  obtain ⟨a, b, hco⟩ := hco
  let N := i + j + 1
  have hab := initial_eq_of_edge_eq P Q (hco N)
  obtain ⟨S, hS, heS⟩ := exists_competitor_departing_at_meeting longest P Q hP hQ
    i j (a + N) (b + N) (by dsimp [N]; omega) (by dsimp [N]; omega) hij hab
  obtain ⟨T, hT, heT⟩ := exists_competitor_departing_at_meeting longest Q P hQ hP
    j i (b + N) (a + N) (by dsimp [N]; omega) (by dsimp [N]; omega) hij.symm hab.symm
  have hs : (P.initial i).1 = (S.initial i).1 :=
    hij.trans (initial_eq_of_edge_eq S Q heS).symm
  have ht : (Q.initial j).1 = (T.initial j).1 :=
    hij.symm.trans (initial_eq_of_edge_eq T P heT).symm
  have hargP := hleftP S hS i i hs
  have hargQ := hleftQ T hT j j ht
  rw [heS] at hargP
  rw [heT] at hargQ
  have hv : kmswLimitDartVertex w (P.edge i, false) =
      kmswLimitDartVertex w (Q.edge j, false) := by
    change edgeWest w (P.edge i) = edgeWest w (Q.edge j)
    rw [(P.edge_outgoing_at_initial w i).2, (Q.edge_outgoing_at_initial w j).2, hij]
  exact congrArg Prod.fst ((monotoneLimitDrawing w hf hfam).initial_arg_injective
    (P.edge i, false) (Q.edge j, false) hv (le_antisymm hargQ hargP))

private theorem leftmost_tails_eq_at_meeting {w : ℕ → Fin 3} {x y : ℕ}
    (hf : KMSWFiniteIncidence w)
    (hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A))
    (longest : Bool) (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments)
    (hQ : if longest then Q.HasLongestSegments else Q.HasShortestSegments)
    (hleftP : ∀ S : InfinitePresentPath w ⟨x⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w hf hfam P S)
    (hleftQ : ∀ S : InfinitePresentPath w ⟨y⟩,
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w hf hfam Q S)
    (hco : ∃ a b, ∀ n, P.edge (a + n) = Q.edge (b + n))
    (i j : ℕ) (hij : (P.initial i).1 = (Q.initial j).1) :
    ∀ n, P.edge (i + n) = Q.edge (j + n) := by
  have hmeet : ∀ n, (P.initial (i + n)).1 = (Q.initial (j + n)).1 := by
    intro n
    induction n with
    | zero => simpa only [Nat.add_zero] using hij
    | succ n ih =>
      have he := leftmost_edge_eq_at_meeting hf hfam longest P Q hP hQ
        hleftP hleftQ hco (i + n) (j + n) ih
      apply presentVertex_eq_of_meeting_id
      exact (P.edge_incoming_at_succ w (i + n)).2.symm.trans
        ((congrArg (edgeEast w) he).trans (Q.edge_incoming_at_succ w (j + n)).2)
  intro n
  exact leftmost_edge_eq_at_meeting hf hfam longest P Q hP hQ hleftP hleftQ
    hco (i + n) (j + n) (hmeet n)

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}




theorem m0CutAdjacentGeodesicSegments_shared_vertex_contradicts_leastness
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (i : ℕ) (hi : i < a) (j : ℕ) (hj : j < b)
    (hij : ((P (k - 1)).codePath.initial i).1 =
      ((P k).codePath.initial j).1) :
    False := by
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hang (a : ℤ) (S : InfinitePresentPath w (boundaryPresentVertex w h a))
      (hS : if longest then S.HasLongestSegments else S.HasShortestSegments) :
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w (H.1 0) hfam
        (P a).codePath S := by
    cases longest with
    | false =>
      have ht := (Xdp.Sdp.cutLeftmost_iff_runZero W H h hp hLL a (P a) (T a)).1
        (hleft a) S hS
      exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
        w (H.1 0) hfam (boundaryVertex w h a) (P a).codePath (T a) S).1 ht).1
    | true =>
      have ht := (Xdp.cutLeftmost_iff_runZero W H h hp hLL a (P a) (T a)).1
        (hleft a) S hS
      exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
        w (H.1 0) hfam (boundaryVertex w h a) (P a).codePath (T a) S).1 ht).1
  have hcode : ∃ c d, ∀ n, (P (k - 1)).codePath.edge (c + n) =
      (P k).codePath.edge (d + n) :=
    ⟨a, b, fun n => wholePlaneEdgeι_injective W 0 (hab.1 n)⟩
  have htail := leftmost_tails_eq_at_meeting (H.1 0) hfam longest
    (P (k - 1)).codePath (P k).codePath
    (P (k - 1)).segments (P k).segments
    (hang (k - 1)) (hang k) hcode i j hij
  have hleast : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) i j :=
    fun n => congrArg (wholePlaneEdgeι W 0) (htail n)
  have hai := (hab.2 i j hleast).1
  have hcontra : ¬ (i < a ∧ j < b) := fun hs => Nat.not_lt_of_ge hai hs.1
  exact hcontra ⟨hi, hj⟩

private theorem presentVertex_eq_of_id_eq {w : ℕ → Fin 3}
    {u v : PresentVertex w} (h : u.id = v.id) : u = v := by
  cases u with
  | mk u =>
    cases v with
    | mk v =>
      simp only at h
      subst v
      rfl

/-- A present infinite path cannot revisit an earlier vertex, since the
intervening segment would be a directed cycle -/
private theorem path_initial_vertex_ne_of_lt {w : ℕ → Fin 3}
    {x : PresentVertex w} (P : InfinitePresentPath w x) {i j : ℕ}
    (hij : i < j) : (P.initial i).1 ≠ (P.initial j).1 := by
  intro heq
  let p := (P.initial j).2
  have hpLen : p.length = j := P.prefix_length j
  obtain ⟨z, p₁, p₂, hp, hp₁⟩ :=
    p.exists_eq_comp_of_le_length (n := i) (by omega)
  have hfull : pathEdgeList p₁ ++ pathEdgeList p₂ =
      List.ofFn (fun n : Fin j => P.edge n.val) := by
    rw [← pathEdgeList_comp, ← hp, P.prefix_edges]
  let full : List ℕ := List.ofFn (fun n : Fin j => P.edge n.val)
  have hsplit : full.take i ++ full.drop i = full := List.take_append_drop i full
  have hconcat : pathEdgeList p₁ ++ pathEdgeList p₂ =
      full.take i ++ full.drop i := by
    calc
      pathEdgeList p₁ ++ pathEdgeList p₂ = full := by simpa [full] using hfull
      _ = full.take i ++ full.drop i := hsplit.symm
  have htake : pathEdgeList p₁ = full.take i :=
    List.append_inj_left hconcat (by
      rw [pathEdgeList_length, hp₁, List.length_take]
      simp [full, Nat.min_eq_left (Nat.le_of_lt hij)])
  have hprefix : List.ofFn (fun n : Fin i => P.edge n.val) = full.take i := by
    apply List.ext_get
    · simp [full, Nat.min_eq_left (Nat.le_of_lt hij)]
    · intro n hn₁ hn₂
      simp [full, List.get_eq_getElem]
  have hz : z.id = (P.initial i).1.id := by
    have hp₁end := pathEdgeList_endpoint p₁
    have hinitial := pathEdgeList_endpoint (P.initial i).2
    rw [P.prefix_edges] at hinitial
    rw [htake, ← hprefix] at hp₁end
    exact hp₁end.symm.trans hinitial
  let q := p₁.comp p₂
  have hqLen : q.length = j := (congrArg Path.length hp).symm.trans hpLen
  have hqi : i < q.vertices.length := by
    rw [Path.vertices_length, hqLen]
    omega
  have hqj : j < q.vertices.length := by
    rw [Path.vertices_length, hqLen]
    omega
  have hvertex : q.vertices.get ⟨i, hqi⟩ = (P.initial i).1 := by
    have hz' := Path.vertices_comp_get_length_eq p₁ p₂
    have hz'' : q.vertices.get ⟨i, hqi⟩ = z := by
      have hp₁bound : p₁.length < q.vertices.length := by
        have hi : i < q.vertices.length := hqi
        omega
      have hidx : (⟨i, hqi⟩ : Fin q.vertices.length) =
          ⟨p₁.length, hp₁bound⟩ := by
        apply Fin.ext
        exact hp₁.symm
      rw [hidx]
      exact hz'
    exact hz''.trans (presentVertex_eq_of_id_eq hz)
  have hlast : q.vertices.get ⟨j, hqj⟩ = (P.initial j).1 := by
    have hlenSub : q.vertices.length - 1 < q.vertices.length := by
      rw [Path.vertices_length, hqLen]
      omega
    have hget := List.get_length_sub_one hlenSub
    have hend := Path.vertices_getLast q q.vertices_ne_nil
    rw [hend] at hget
    have hidx : (⟨q.vertices.length - 1, hlenSub⟩ : Fin q.vertices.length) =
        ⟨j, hqj⟩ := by
      have hval : q.vertices.length - 1 = j := by
        have hlen : q.vertices.length = j + 1 := by
          rw [Path.vertices_length, hqLen]
        omega
      apply Fin.ext
      exact hval
    rw [hidx] at hget
    exact hget
  have hsame : q.vertices.get ⟨i, hqi⟩ = q.vertices.get ⟨j, hqj⟩ :=
    hvertex.trans (heq.trans hlast.symm)
  have hidx := (List.Nodup.get_inj_iff
    (vertices_nodup_of_acyclic (presentVertex_acyclic w) q)).mp hsame
  have hval : i = j := congrArg Fin.val hidx
  exact (Nat.ne_of_lt hij) hval

/-- Vertices along a present infinite path are pairwise distinct by acyclicity -/
private theorem path_initial_vertices_injective {w : ℕ → Fin 3}
    {x : PresentVertex w} (P : InfinitePresentPath w x) :
    Function.Injective (fun n => (P.initial n).1) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    exact path_initial_vertex_ne_of_lt P hlt hij
  · exact heq
  · exfalso
    exact path_initial_vertex_ne_of_lt P hgt hij.symm


private theorem m0CutAdjacentGeodesicSegments_no_early_shared_vertex
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hp : BoundaryHitWitnesses (kmswPastCode W)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (i : ℕ) (hi : i < a) (j : ℕ) :
    ((P (k - 1)).codePath.initial i).1 ≠ ((P k).codePath.initial j).1 := by
  intro heq
  by_cases hj : j < b
  · exact m0CutAdjacentGeodesicSegments_shared_vertex_contradicts_leastness
      P T hleft k a b hab i hi j hj heq
  · have htail : ∀ t : ℕ,
        ((P (k - 1)).codePath.initial (a + t)).1 =
          ((P k).codePath.initial (b + t)).1 := by
      intro t
      induction t with
      | zero =>
          exact m0Cut_initial_vertex_eq_of_edge_tails_coalesce
            (P (k - 1)) (P k) hab.1
      | succ t ih =>
          apply presentVertex_eq_of_id_eq
          have he := wholePlaneEdgeι_injective W 0 (hab.1 t)
          have h₁ : ((P (k - 1)).codePath.initial (a + (t + 1))).1.id =
              edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge (a + t)) := by
            have hs := (P (k - 1)).codePath.edge_incoming_at_succ
              (shiftedStream W 0) (a + t)
            have hidx : a + t + 1 = a + (t + 1) := by omega
            calc
              ((P (k - 1)).codePath.initial (a + (t + 1))).1.id =
                  ((P (k - 1)).codePath.initial (a + t + 1)).1.id := by rw [← hidx]
              _ = edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge (a + t)) := hs.2.symm
          have h₂ : edgeEast (shiftedStream W 0) ((P k).codePath.edge (b + t)) =
              ((P k).codePath.initial (b + (t + 1))).1.id := by
            have hs := (P k).codePath.edge_incoming_at_succ
              (shiftedStream W 0) (b + t)
            have hidx : b + t + 1 = b + (t + 1) := by omega
            calc
              edgeEast (shiftedStream W 0) ((P k).codePath.edge (b + t)) =
                  ((P k).codePath.initial (b + t + 1)).1.id := hs.2
              _ = ((P k).codePath.initial (b + (t + 1))).1.id := by rw [hidx]
          exact h₁.trans ((congrArg (edgeEast (shiftedStream W 0)) he).trans h₂)
    have hfuture : ((P (k - 1)).codePath.initial (a + (j - b))).1 =
        ((P k).codePath.initial j).1 := by
      have hm : b + (j - b) = j := by omega
      simpa only [hm] using htail (j - b)
    have hrepeat := heq.trans hfuture.symm
    exact path_initial_vertex_ne_of_lt (P (k - 1)).codePath
      (by omega) hrepeat



theorem m0CutAdjacentGeodesics_ordered_before_coalescence {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    (∀ i < a,
      (P (k - 1)).codePath.edge i ∈ m0GeodesicSideEdges hp (P k) .left) ∧
    (∀ j < b,
      (P k).codePath.edge j ∈
        m0GeodesicSideEdges hp (P (k - 1)) .right) := by
  constructor
  · intro i hi
    have havoid (n : ℕ) (hn : n < a) :
        ((P (k - 1)).codePath.initial n).1.id ∉ m0GeodesicVertices (P k) := by
      intro hmem
      obtain ⟨m, hm⟩ := Set.mem_range.mp hmem
      have heq : ((P (k - 1)).codePath.initial n).1 =
          ((P k).codePath.initial m).1 :=
        (presentVertex_eq_of_id_eq hm).symm
      exact m0CutAdjacentGeodesicSegments_no_early_shared_vertex
        P T hleft k a b hab n hn m heq
    have hvertices : ∀ n, n ≤ a →
        ((P (k - 1)).codePath.initial n).1.id ∈
          m0GeodesicSideVertices hp (P k) .left := by
      intro n
      induction n with
      | zero =>
          intro _
          have hz := ((P (k - 1)).codePath.initial 0).2.eq_of_length_zero
            ((P (k - 1)).codePath.prefix_length 0)
          have hzero : ((P (k - 1)).codePath.initial 0).1.id =
              boundaryVertex (shiftedStream W 0) h (k - 1) :=
            congrArg PresentVertex.id hz.symm
          rw [hzero]
          exact m0Cut_previous_boundary_mem_left_side (P k)
      | succ n ih =>
          intro hn
          have hnlt : n < a := by omega
          have hnot := havoid n hnlt
          rcases m0GeodesicSideEdges_cover hp (P k)
              ((P (k - 1)).codePath.edge n) with he | he
          · have hend := (m0GeodesicSide_endpoints hp (P k) .left
                ((P (k - 1)).codePath.edge n) he).2
            change edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge n) ∈
              m0GeodesicSideVertices hp (P k) .left at hend
            rw [((P (k - 1)).codePath.edge_incoming_at_succ
              (shiftedStream W 0) n).2] at hend
            exact hend
          · have hwest := (m0GeodesicSide_endpoints hp (P k) .right
                ((P (k - 1)).codePath.edge n) he).1
            change edgeWest (shiftedStream W 0) ((P (k - 1)).codePath.edge n) ∈
              m0GeodesicSideVertices hp (P k) .right at hwest
            rw [((P (k - 1)).codePath.edge_outgoing_at_initial
              (shiftedStream W 0) n).2] at hwest
            have hboth : ((P (k - 1)).codePath.initial n).1.id ∈
                m0GeodesicSideVertices hp (P k) .left ∩
                  m0GeodesicSideVertices hp (P k) .right :=
              ⟨ih (by omega), hwest⟩
            have hpv : ((P (k - 1)).codePath.initial n).1.id ∈
                m0GeodesicVertices (P k) := by
              rw [← m0GeodesicSideVertices_inter hp (P k)]
              exact hboth
            exact (hnot hpv).elim
    rcases m0GeodesicSideEdges_cover hp (P k)
        ((P (k - 1)).codePath.edge i) with he | he
    · exact he
    · have hwest := (m0GeodesicSide_endpoints hp (P k) .right
          ((P (k - 1)).codePath.edge i) he).1
      change edgeWest (shiftedStream W 0) ((P (k - 1)).codePath.edge i) ∈
        m0GeodesicSideVertices hp (P k) .right at hwest
      rw [((P (k - 1)).codePath.edge_outgoing_at_initial
        (shiftedStream W 0) i).2] at hwest
      have hboth : ((P (k - 1)).codePath.initial i).1.id ∈
          m0GeodesicSideVertices hp (P k) .left ∩
            m0GeodesicSideVertices hp (P k) .right :=
        ⟨hvertices i hi.le, hwest⟩
      have hpv : ((P (k - 1)).codePath.initial i).1.id ∈
          m0GeodesicVertices (P k) := by
        rw [← m0GeodesicSideVertices_inter hp (P k)]
        exact hboth
      exact (havoid i hi hpv).elim
  · intro j hj
    have havoid (n : ℕ) (hn : n < b) :
        ((P k).codePath.initial n).1.id ∉ m0GeodesicVertices (P (k - 1)) := by
      intro hmem
      obtain ⟨m, hm⟩ := Set.mem_range.mp hmem
      have heq : ((P k).codePath.initial n).1 =
          ((P (k - 1)).codePath.initial m).1 :=
        (presentVertex_eq_of_id_eq hm).symm
      by_cases hm' : m < a
      · exact m0CutAdjacentGeodesicSegments_shared_vertex_contradicts_leastness
          P T hleft k a b hab m hm' n hn heq.symm
      · have htail : ∀ t : ℕ,
            ((P (k - 1)).codePath.initial (a + t)).1 =
              ((P k).codePath.initial (b + t)).1 := by
          intro t
          induction t with
          | zero =>
              exact m0Cut_initial_vertex_eq_of_edge_tails_coalesce
                (P (k - 1)) (P k) hab.1
          | succ t ih =>
              apply presentVertex_eq_of_id_eq
              have he := wholePlaneEdgeι_injective W 0 (hab.1 t)
              have h₁ : ((P (k - 1)).codePath.initial (a + (t + 1))).1.id =
                  edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge (a + t)) := by
                have hs := (P (k - 1)).codePath.edge_incoming_at_succ
                  (shiftedStream W 0) (a + t)
                have hidx : a + t + 1 = a + (t + 1) := by omega
                calc
                  ((P (k - 1)).codePath.initial (a + (t + 1))).1.id =
                      ((P (k - 1)).codePath.initial (a + t + 1)).1.id := by rw [← hidx]
                  _ = edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge (a + t)) := hs.2.symm
              have h₂ : edgeEast (shiftedStream W 0) ((P k).codePath.edge (b + t)) =
                  ((P k).codePath.initial (b + (t + 1))).1.id := by
                have hs := (P k).codePath.edge_incoming_at_succ
                  (shiftedStream W 0) (b + t)
                have hidx : b + t + 1 = b + (t + 1) := by omega
                calc
                  edgeEast (shiftedStream W 0) ((P k).codePath.edge (b + t)) =
                      ((P k).codePath.initial (b + t + 1)).1.id := hs.2
                  _ = ((P k).codePath.initial (b + (t + 1))).1.id := by rw [hidx]
              exact h₁.trans ((congrArg (edgeEast (shiftedStream W 0)) he).trans h₂)
        have hmge : a ≤ m := by omega
        have heq' : ((P k).codePath.initial n).1 =
            ((P k).codePath.initial (b + (m - a))).1 := by
          have hmidx : a + (m - a) = m := by omega
          have ht := htail (m - a)
          rw [hmidx] at ht
          exact heq.trans ht
        exact path_initial_vertex_ne_of_lt (P k).codePath
          (by omega) heq'
    have hvertices : ∀ n, n ≤ b →
        ((P k).codePath.initial n).1.id ∈
          m0GeodesicSideVertices hp (P (k - 1)) .right := by
      intro n
      induction n with
      | zero =>
          intro _
          have hz := ((P k).codePath.initial 0).2.eq_of_length_zero
            ((P k).codePath.prefix_length 0)
          have hzero : ((P k).codePath.initial 0).1.id =
              boundaryVertex (shiftedStream W 0) h k :=
            congrArg PresentVertex.id hz.symm
          rw [hzero]
          exact m0Cut_next_boundary_mem_right_side (P (k - 1))
      | succ n ih =>
          intro hn
          have hnlt : n < b := by omega
          have hnot := havoid n hnlt
          rcases m0GeodesicSideEdges_cover hp (P (k - 1))
              ((P k).codePath.edge n) with he | he
          · have hwest := (m0GeodesicSide_endpoints hp (P (k - 1)) .left
                ((P k).codePath.edge n) he).1
            change edgeWest (shiftedStream W 0) ((P k).codePath.edge n) ∈
              m0GeodesicSideVertices hp (P (k - 1)) .left at hwest
            rw [((P k).codePath.edge_outgoing_at_initial
              (shiftedStream W 0) n).2] at hwest
            have hboth : ((P k).codePath.initial n).1.id ∈
                m0GeodesicSideVertices hp (P (k - 1)) .left ∩
                  m0GeodesicSideVertices hp (P (k - 1)) .right :=
              ⟨hwest, ih (by omega)⟩
            have hpv : ((P k).codePath.initial n).1.id ∈
                m0GeodesicVertices (P (k - 1)) := by
              rw [← m0GeodesicSideVertices_inter hp (P (k - 1))]
              exact hboth
            exact (hnot hpv).elim
          · have hend := (m0GeodesicSide_endpoints hp (P (k - 1)) .right
                ((P k).codePath.edge n) he).2
            change edgeEast (shiftedStream W 0) ((P k).codePath.edge n) ∈
              m0GeodesicSideVertices hp (P (k - 1)) .right at hend
            rw [((P k).codePath.edge_incoming_at_succ
              (shiftedStream W 0) n).2] at hend
            exact hend
    rcases m0GeodesicSideEdges_cover hp (P (k - 1)) ((P k).codePath.edge j) with he | he
    · have hwest := (m0GeodesicSide_endpoints hp (P (k - 1)) .left
          ((P k).codePath.edge j) he).1
      change edgeWest (shiftedStream W 0) ((P k).codePath.edge j) ∈
        m0GeodesicSideVertices hp (P (k - 1)) .left at hwest
      rw [((P k).codePath.edge_outgoing_at_initial
        (shiftedStream W 0) j).2] at hwest
      have hboth : ((P k).codePath.initial j).1.id ∈
          m0GeodesicSideVertices hp (P (k - 1)) .left ∩
            m0GeodesicSideVertices hp (P (k - 1)) .right :=
        ⟨hwest, hvertices j hj.le⟩
      have hpv : ((P k).codePath.initial j).1.id ∈
          m0GeodesicVertices (P (k - 1)) := by
        rw [← m0GeodesicSideVertices_inter hp (P (k - 1))]
        exact hboth
      exact (havoid j hj hpv).elim
    · exact he

end DirectedDistances.PaperProofs.Section5

