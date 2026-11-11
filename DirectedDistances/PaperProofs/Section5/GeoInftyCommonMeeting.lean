/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostXdp
public import DirectedDistances.PaperProofs.Section5.BusemannClsIdentity

/-! # Coalescence from any meeting of the route-54 leftmost paths

Helpers toward Lemma 5.5/5.6. The meeting assertion is the step in Lemma 5.4,
Finite equal-length replacement upgrades the existing eventual coalescence
conjunct to coalescence at every meeting, retaining geometric edge identities. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

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





theorem m0Cut_edge_tails_coalesce_of_meeting {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hcoal : ∀ k l, ∃ a b, M0CutEdgeTailsCoalesce (P k) (P l) a b)
    (k l : ℤ) (i j : ℕ)
    (hmeet : wholePlaneVertexι W 0 ((P k).codePath.initial i).1.id =
      wholePlaneVertexι W 0 ((P l).codePath.initial j).1.id) :
    M0CutEdgeTailsCoalesce (P k) (P l) i j := by
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
  obtain ⟨a, b, hab⟩ := hcoal k l
  have hcode : ∃ a b, ∀ n, (P k).codePath.edge (a + n) =
      (P l).codePath.edge (b + n) :=
    ⟨a, b, fun n => wholePlaneEdgeι_injective W 0 (hab n)⟩
  have hij : ((P k).codePath.initial i).1 = ((P l).codePath.initial j).1 :=
    presentVertex_eq_of_meeting_id (wholePlaneVertexι_injective W 0 hmeet)
  have he := leftmost_tails_eq_at_meeting (H.1 0) hfam longest
    (P k).codePath (P l).codePath (P k).segments (P l).segments
    (hang k) (hang l) hcode i j hij
  exact fun n => congrArg (wholePlaneEdgeι W 0) (he n)




theorem m0Cut_ae_leftmost_xdp_coalesce_at_every_meeting :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∀ k l, ∃ a b, M0CutEdgeTailsCoalesce (P k) (P l) a b) ∧
        ∀ (k l : ℤ) (i j : ℕ),
          wholePlaneVertexι W 0 ((P k).codePath.initial i).1.id =
            wholePlaneVertexι W 0 ((P l).codePath.initial j).1.id →
          M0CutEdgeTailsCoalesce (P k) (P l) i j := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hall⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal⟩ := hall longest
  exact ⟨R, T, P, hR, hleft, huniq, hcoal,
    m0Cut_edge_tails_coalesce_of_meeting P T hleft hcoal⟩

end DirectedDistances.PaperProofs.Section5
