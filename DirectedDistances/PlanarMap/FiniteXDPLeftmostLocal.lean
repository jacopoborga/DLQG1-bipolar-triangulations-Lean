/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPCanonicalLeftmost

import Mathlib.Data.List.GetD

/-! # Local finite XDP geodesic order helpers

Helpers toward `lem-lr-ind`; not the paper result
paper's geometric leftmost notion requires path-cut separation
(`PlanarPathCutData` / `PlanarFaceCycleSpace`) and is a separate obligation. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem list_exists_firstDiff_decomp
    {α : Type*} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.length = ys.length → xs ≠ ys →
      ∃ pre a b xs' ys', a ≠ b ∧
        xs = pre ++ a :: xs' ∧ ys = pre ++ b :: ys' := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen hne
      cases ys with
      | nil => exact (hne rfl).elim
      | cons b ys => simp at hlen
  | cons a xs ih =>
      intro ys hlen hne
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          simp only [List.length_cons] at hlen
          by_cases hab : a = b
          · subst b
            have htail : xs ≠ ys := by
              intro heq
              subst ys
              exact hne rfl
            obtain ⟨pre, c, d, xs', ys', hcd, hx, hy⟩ :=
              ih (by omega) htail
            refine ⟨a :: pre, c, d, xs', ys', hcd, ?_, ?_⟩
            · simpa [List.cons_append] using congrArg (fun zs => a :: zs) hx
            · simpa [List.cons_append] using congrArg (fun zs => a :: zs) hy
          · exact ⟨[], a, b, xs, ys, hab, rfl, rfl⟩

private theorem path_vertices_eq_of_dart_prefix
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P Q : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi : i ≤ n)
    (hpre : ∀ j : Fin i,
      P.darts.get ⟨j.val, by simpa [P.darts_length] using
        (show j.val < n by omega)⟩ =
        Q.darts.get ⟨j.val, by simpa [Q.darts_length] using
          (show j.val < n by omega)⟩) :
    P.vertices.get ⟨i, by simpa [P.vertices_length] using (show i < n + 1 by omega)⟩ =
      Q.vertices.get ⟨i, by simpa [Q.vertices_length] using (show i < n + 1 by omega)⟩ := by
  induction i with
  | zero =>
      exact P.start_vertex.trans Q.start_vertex.symm
  | succ i ih =>
      have hi' : i ≤ n := by omega
      have hprev := ih hi' (fun j => hpre ⟨j.val, by omega⟩)
      have hd := hpre ⟨i, by omega⟩
      have hstepP := (P.edge_step ⟨i,
        by simpa [P.darts_length] using (show i < n by omega)⟩).2.2.2
      have hstepQ := (Q.edge_step ⟨i,
        by simpa [Q.darts_length] using (show i < n by omega)⟩).2.2.2
      calc
        P.vertices.get ⟨i + 1, by simpa [P.vertices_length] using
            (show i + 1 < n + 1 by omega)⟩ =
            dartHeadVertex B.map (P.darts.get ⟨i, by
              simpa [P.darts_length] using (show i < n by omega)⟩) :=
          hstepP
        _ = dartHeadVertex B.map (Q.darts.get ⟨i, by
              simpa [Q.darts_length] using (show i < n by omega)⟩) :=
          congrArg (dartHeadVertex B.map) hd
        _ = Q.vertices.get ⟨i + 1, by simpa [Q.vertices_length] using
            (show i + 1 < n + 1 by omega)⟩ := hstepQ.symm

private theorem idxOf_lt_of_filter_cons
    {α : Type*} [DecidableEq α] {xs : List α} {p : α → Bool}
    {a : α} {rest : List α} (hxs : xs.Nodup)
    (hfilter : xs.filter p = a :: rest) {b : α} (hb : b ∈ rest) :
    xs.idxOf a < xs.idxOf b := by
  induction xs generalizing a rest b with
  | nil => simp at hfilter
  | cons c cs ih =>
      by_cases hc : p c = true
      · simp [hc] at hfilter
        rcases hfilter with ⟨hca, hrest⟩
        subst a
        have hnodup := hxs.filter p
        simp [hc] at hnodup
        rw [hrest] at hnodup
        have hb' : b ∈ cs.filter p := by simpa [hrest] using hb
        have hbc : b ≠ c := by
          intro h
          subst b
          exact (List.nodup_cons.mp hxs).1 (List.mem_filter.mp hb').1
        have hidxB : (c :: cs).idxOf b = cs.idxOf b + 1 := by
          exact List.idxOf_cons_ne cs (Ne.symm hbc)
        simp [List.idxOf_cons_self, hidxB]
      · have hcfalse : p c = false := Bool.eq_false_of_not_eq_true hc
        simp [hcfalse] at hfilter
        have htailNodup : cs.Nodup := (List.nodup_cons.mp hxs).2
        have hlt := ih htailNodup hfilter hb
        have haMem : a ∈ cs.filter p := by rw [hfilter]; simp
        have hbMem : b ∈ cs.filter p := by
          rw [hfilter]
          exact List.mem_cons_of_mem a hb
        have hpa : p a = true := (List.mem_filter.mp haMem).2
        have hpb : p b = true := (List.mem_filter.mp hbMem).2
        have hca : c ≠ a := by
          intro h
          subst a
          exact hc hpa
        have hcb : c ≠ b := by
          intro h
          subst b
          exact hc hpb
        rw [List.idxOf_cons_ne cs hca, List.idxOf_cons_ne cs hcb]
        omega

/-- Two distinct XDP-geodesic dart lists have a first differing index. Their
darts there have the same tail vertex because their preceding dart prefixes
agree. Helper toward `lem-lr-ind`; not the paper result -/
theorem exists_firstDivergence
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n m : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (Q : SimpleDirectedDartPath B.map B.source B.sink m)
    (hP : IsXDPGeodesicBase B x P) (hQ : IsXDPGeodesicBase B x Q)
    (hne : P.darts ≠ Q.darts) :
    ∃ hnm : n = m, ∃ i : Fin n,
      P.darts.get ⟨i.val, by simp [P.darts_length]⟩ ≠
        Q.darts.get ⟨i.val, by
          have hi : i.val < m := by omega
          simp [Q.darts_length, hi]⟩ ∧
      P.darts.take i.val = Q.darts.take i.val ∧
      dartTailVertex B.map
          (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) =
        dartTailVertex B.map
          (Q.darts.get ⟨i.val, by
            have hi : i.val < m := by omega
            simp [Q.darts_length, hi]⟩) := by
  classical
  have hnm : n = m := by
    cases x with
    | ldp => exact Nat.le_antisymm (hQ P) (hP Q)
    | sdp => exact Nat.le_antisymm (hP Q) (hQ P)
  have hnmOut := hnm
  subst m
  have hlen : P.darts.length = Q.darts.length := by
    rw [P.darts_length, Q.darts_length]
  obtain ⟨pre, a, b, suffixP, suffixQ, hab, hPsplit, hQsplit⟩ :=
    list_exists_firstDiff_decomp hlen hne
  have hsplitLen := congrArg List.length hPsplit
  simp only [List.length_append, List.length_cons] at hsplitLen
  have hi_lt : pre.length < n := by
    rw [← P.darts_length]
    omega
  let i := pre.length
  have hPbound : pre.length < P.darts.length := by
    rw [hPsplit]
    simp
  have hQbound : pre.length < Q.darts.length := by
    rw [hQsplit]
    simp
  have hPgetElem : P.darts[pre.length] = a :=
    List.getElem_of_append hPsplit rfl
  have hQgetElem : Q.darts[pre.length] = b :=
    List.getElem_of_append hQsplit rfl
  have hPget : P.darts.get ⟨pre.length, hPbound⟩ = a := by
    simpa only [List.get_eq_getElem] using hPgetElem
  have hQget : Q.darts.get ⟨pre.length, hQbound⟩ = b := by
    simpa only [List.get_eq_getElem] using hQgetElem
  have htake : P.darts.take i = Q.darts.take i := by
    rw [hPsplit, hQsplit]
    simp [i]
  have hpre : ∀ j : Fin i,
      P.darts.get ⟨j.val, by simpa [P.darts_length, i] using
        (show j.val < n by omega)⟩ =
      Q.darts.get ⟨j.val, by simpa [Q.darts_length, i] using
        (show j.val < n by omega)⟩ := by
    intro j
    have hjP : j.val < P.darts.length := by
      have hj : j.val < pre.length := by simp [i]
      omega
    have hjQ : j.val < Q.darts.length := by
      have hj : j.val < pre.length := by simp [i]
      omega
    have hjTake : j.val < (P.darts.take i).length := by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨j.isLt, by omega⟩
    have hTakeJ : (P.darts.take i)[j.val] =
        (Q.darts.take i)[j.val]'(htake ▸ hjTake) :=
      List.getElem_of_eq htake hjTake
    have hPj := List.getElem_take' hjP j.isLt
    have hQj := List.getElem_take' hjQ j.isLt
    simpa only [List.get_eq_getElem] using hPj.trans (hTakeJ.trans hQj.symm)
  have hvertices := path_vertices_eq_of_dart_prefix B P Q i (by omega) hpre
  have htail : dartTailVertex B.map
      (P.darts.get ⟨i, by simpa [P.darts_length] using (show i < n by omega)⟩) =
      dartTailVertex B.map
        (Q.darts.get ⟨i, by simpa [Q.darts_length] using (show i < n by omega)⟩) := by
    have hstepP := (P.edge_step ⟨i,
      by simpa [P.darts_length] using (show i < n by omega)⟩).2.2.1
    have hstepQ := (Q.edge_step ⟨i,
      by simpa [Q.darts_length] using (show i < n by omega)⟩).2.2.1
    calc
      dartTailVertex B.map (P.darts.get ⟨i, by
          simpa [P.darts_length] using (show i < n by omega)⟩) =
          P.vertices.get ⟨i, by
            simpa [P.vertices_length] using (show i < n + 1 by omega)⟩ := hstepP.symm
      _ = Q.vertices.get ⟨i, by
            simpa [Q.vertices_length] using (show i < n + 1 by omega)⟩ := hvertices
      _ = dartTailVertex B.map (Q.darts.get ⟨i, by
          simpa [Q.darts_length] using (show i < n by omega)⟩) := hstepQ
  have hdifferent : P.darts.get ⟨i, by
      simpa [P.darts_length] using (show i < n by omega)⟩ ≠
    Q.darts.get ⟨i, by simpa [Q.darts_length] using (show i < n by omega)⟩ := by
    intro heq
    apply hab
    calc
      a = P.darts.get ⟨i, by simpa [P.darts_length] using (show i < n by omega)⟩ := by
        have hPget' : P.darts.get ⟨i, by
            simpa [P.darts_length] using (show i < n by omega)⟩ = a := by
          simpa [i] using hPget
        exact hPget'.symm
      _ = Q.darts.get ⟨i, by simpa [Q.darts_length] using (show i < n by omega)⟩ := heq
      _ = b := by
        have hQget' : Q.darts.get ⟨i, by
            simpa [Q.darts_length] using (show i < n by omega)⟩ = b := by
          simpa [i] using hQget
        exact hQget'
  exact ⟨hnmOut, ⟨⟨i, hi_lt⟩, hdifferent, htake, htail⟩⟩

/-- A canonical greedy XDP geodesic takes the earlier outgoing dart than
any distinct XDP geodesic at their first divergence. The comparison is in
`canonicalOutgoingOrder`; identifying this order-theoretic property with the
paper's geometric leftmost notion still requires path-cut separation.
Helper toward `lem-lr-ind`; not the paper result -/
theorem canonicalLeftmost_path_precedes
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (Pc : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x))
    (hPc : IsXDPGeodesicBase B x Pc)
    (hsteps : ∀ i : Fin (xdpLengthBase B x),
      Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩ =
        canonicalLeftmostXDPStep B x
          (selectorVertex B (canonicalLeftmostXDPStep B x) i.val))
    {m : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink m)
    (hP : IsXDPGeodesicBase B x P) (hne : Pc.darts ≠ P.darts) :
    ∃ hnm : xdpLengthBase B x = m, ∃ i : Fin (xdpLengthBase B x),
      ∃ hvs : selectorVertex B (canonicalLeftmostXDPStep B x) i.val ≠ B.sink,
        (canonicalOutgoingOrder B
          (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) hvs).idxOf
            (Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩) <
          (canonicalOutgoingOrder B
            (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) hvs).idxOf
              (P.darts.get ⟨i.val, by
                have hi : i.val < m := by omega
                simp [P.darts_length, hi]⟩) := by
  classical
  let sel : MapVertex B.map → D := canonicalLeftmostXDPStep B x
  have hsel : ∀ v, (∃ n, ∃ Q : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x Q ∧ v ∈ Q.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v) := by
    intro v hv hvs
    exact canonicalLeftmostXDPStep_spec B x v hv hvs
  obtain ⟨hnm, ⟨i, hdiff, _hprefix, htailEq⟩⟩ :=
    exists_firstDivergence B x Pc P hPc hP hne
  let v := selectorVertex B sel i.val
  have hv := selectorVertex_mem_XDPGeodesic B x sel hsel i.val
  have hvs : v ≠ B.sink := by
    simpa [v, sel] using
      selectorVertex_ne_sink_of_lt_length B x sel hsel i.val i.isLt
  have hspec := canonicalLeftmostXDPStep_spec B x v hv hvs
  obtain ⟨rest, hfirst, hlocal⟩ := canonicalLeftmostXDPStep_first B x v hv hvs
  have hPcStep : Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩ =
      canonicalLeftmostXDPStep B x v := by
    simpa [v, sel] using hsteps i
  have htailPc : dartTailVertex B.map
      (Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩) = v := by
    rw [hPcStep]
    exact hspec.1
  have htailP : dartTailVertex B.map
      (P.darts.get ⟨i.val, by
        have hi : i.val < m := by omega
        simp [P.darts_length, hi]⟩) = v := htailEq.symm.trans htailPc
  have hgeoP : IsXDPGeodesicDart B x
      (P.darts.get ⟨i.val, by
        have hi : i.val < m := by omega
        simp [P.darts_length, hi]⟩) := by
    exact ⟨m, P, hP, List.get_mem _ _⟩
  have hPne : P.darts.get ⟨i.val, by
      have hi : i.val < m := by omega
      simp [P.darts_length, hi]⟩ ≠ canonicalLeftmostXDPStep B x v := by
    intro heq
    apply hdiff
    calc
      Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩ =
          canonicalLeftmostXDPStep B x v := hPcStep
      _ = P.darts.get ⟨i.val, by
          have hi : i.val < m := by omega
          simp [P.darts_length, hi]⟩ := heq.symm
  have hrest : P.darts.get ⟨i.val, by
      have hi : i.val < m := by omega
      simp [P.darts_length, hi]⟩ ∈ rest := by
    rcases hlocal _ htailP hgeoP with heq | hmem
    · exact (hPne heq).elim
    · exact hmem
  have hfilter :
      (canonicalOutgoingOrder B v hvs).filter
          (fun d => decide (IsXDPGeodesicDart B x d)) =
        canonicalLeftmostXDPStep B x v :: rest := by
    simpa only [canonicalXDPGeodesicDartOrder] using hfirst
  have hlt := idxOf_lt_of_filter_cons
    (canonicalOutgoingOrder_nodup B v hvs) hfilter hrest
  have hltPc :
      (canonicalOutgoingOrder B
        (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) hvs).idxOf
          (Pc.darts.get ⟨i.val, by simp [Pc.darts_length]⟩) <
        (canonicalOutgoingOrder B
          (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) hvs).idxOf
            (P.darts.get ⟨i.val, by
              have hi : i.val < m := by omega
              simp [P.darts_length, hi]⟩) := by
    rw [hPcStep]
    simpa [v] using hlt
  exact ⟨hnm, ⟨i, hvs, hltPc⟩⟩

/-- Order-theoretic lexicographic leftmostness for an XDP geodesic: at every
first divergence from another XDP geodesic, the dart of `P` has smaller list
index in `canonicalOutgoingOrder` at their common tail. This is not yet the
paper's geometric “lies weakly to the right” characterization; that
equivalence requires path-cut separation (`PlanarPathCutData` /
`PlanarFaceCycleSpace`) as a separate obligation. Helper toward `lem-lr-ind`, -/
@[expose] def IsLexLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  IsXDPGeodesicBase B x P ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesicBase B x Q → Q.darts ≠ P.darts →
      ∀ (hnm : n = m) (i : Fin n),
        P.darts.take i.val = Q.darts.take i.val →
        P.darts.get ⟨i.val, by simp [P.darts_length]⟩ ≠
          Q.darts.get ⟨i.val, by
            have hi : i.val < m := by omega
            simp [Q.darts_length, hi]⟩ →
        ∃ hvs : dartTailVertex B.map
            (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) ≠ B.sink,
          (canonicalOutgoingOrder B
            (dartTailVertex B.map
              (P.darts.get ⟨i.val, by simp [P.darts_length]⟩)) hvs).idxOf
                (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) <
            (canonicalOutgoingOrder B
              (dartTailVertex B.map
                (P.darts.get ⟨i.val, by simp [P.darts_length]⟩)) hvs).idxOf
                  (Q.darts.get ⟨i.val, by
                    have hi : i.val < m := by omega
                    simp [Q.darts_length, hi]⟩)

/-- Every dart of an XDP geodesic is an XDP-geodesic dart by definition.
Helper toward `lem-lr-ind`; not the paper result -/
theorem xdpGeodesic_dart_isGeodesicDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B x P) {d : D} (hd : d ∈ P.darts) :
    IsXDPGeodesicDart B x d :=
  ⟨n, P, hP, hd⟩

/-- At any non-sink vertex of an XDP geodesic, its outgoing path dart lies
in the canonical outgoing geodesic order. In particular this applies at a
shared vertex with the canonical path from
`exists_canonicalLeftmost_XDPGeodesic_path`. Helper toward `lem-lr-ind`; -/
theorem xdpGeodesic_dart_mem_canonicalOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B x P) {v : MapVertex B.map}
    (hv : v ∈ P.vertices) (hvs : v ≠ B.sink) :
    ∃ d, dartTailVertex B.map d = v ∧
      IsXDPGeodesicDart B x d ∧
      d ∈ canonicalXDPGeodesicDartOrder B x v hvs := by
  classical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hi_lt : i.val < n := by
    have hi_bound : i.val < n + 1 := by
      simpa [P.vertices_length] using i.isLt
    by_contra h
    have hi_eq : i.val = n := by omega
    apply hvs
    calc
      v = P.vertices.get i := hi.symm
      _ = P.vertices.get ⟨n, by simp [P.vertices_length]⟩ := by
        congr 1
        exact Fin.ext hi_eq
      _ = B.sink := P.end_vertex
  let j : Fin P.darts.length := ⟨i.val, by simpa [P.darts_length] using hi_lt⟩
  let d : D := P.darts.get j
  have hi' : (⟨i.val, i.isLt⟩ : Fin P.vertices.length) = i := Fin.ext rfl
  have htail : dartTailVertex B.map d = v := by
    have hstep := (P.edge_step j).2.2.1
    rw [hi'] at hstep
    exact hstep.symm.trans hi
  have hgeo : IsXDPGeodesicDart B x d :=
    ⟨n, P, hP, List.get_mem _ _⟩
  refine ⟨d, htail, hgeo, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨(mem_canonicalOutgoingOrder_iff B v hvs d).2
    ⟨htail, (IsXDPGeodesicDart.present_tail B x d hgeo).2⟩, ?_⟩
  exact decide_eq_true hgeo

/-- Two order-theoretic lex-leftmost XDP geodesics have the same dart list.
This uniqueness is only for the order-theoretic helper notion; its
equivalence to the paper's planar leftmost path still requires path-cut
separation. Helper toward `lem-lr-ind`; not the paper result -/
theorem dartLists_eq_of_isLexLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n m : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (Q : SimpleDirectedDartPath B.map B.source B.sink m)
    (hP : IsLexLeftmostXDPGeodesic B x P)
    (hQ : IsLexLeftmostXDPGeodesic B x Q) : P.darts = Q.darts := by
  classical
  by_contra hne
  have hnm : n = m := by
    cases x with
    | ldp => exact Nat.le_antisymm (hQ.1 P) (hP.1 Q)
    | sdp => exact Nat.le_antisymm (hP.1 Q) (hQ.1 P)
  subst m
  obtain ⟨_hnm, ⟨i, hdiff, htake, htail⟩⟩ :=
    exists_firstDivergence B x P Q hP.1 hQ.1 hne
  rcases hP with ⟨hPg, hPlex⟩
  rcases hQ with ⟨hQg, hQlex⟩
  obtain ⟨hvsP, hltP⟩ := hPlex Q hQg (Ne.symm hne) rfl i htake hdiff
  obtain ⟨hvsQ, hltQ⟩ := hQlex P hPg hne rfl i htake.symm hdiff.symm
  have hvsQ' : dartTailVertex B.map
      (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) ≠ B.sink := by
    intro h
    apply hvsQ
    exact htail.symm.trans h
  have hvsEq : hvsQ' = hvsP := Subsingleton.elim _ _
  have hltQ' :
      (canonicalOutgoingOrder B
        (dartTailVertex B.map
          (P.darts.get ⟨i.val, by simp [P.darts_length]⟩)) hvsP).idxOf
            (Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩) <
        (canonicalOutgoingOrder B
          (dartTailVertex B.map
            (P.darts.get ⟨i.val, by simp [P.darts_length]⟩)) hvsP).idxOf
              (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) := by
    simpa only [htail.symm, hvsEq] using hltQ
  omega

/-- The canonically selected geodesic is leftmost for the internal
lexicographic dart order. This helper toward `lem-lr-ind` uses the local
first-admissible-dart property; equivalence with the paper's region -/
theorem canonical_isLexLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    IsLexLeftmostXDPGeodesic B x
      (Classical.choose (exists_canonicalLeftmost_XDPGeodesic_path B x)) := by
  classical
  let hcanonical := exists_canonicalLeftmost_XDPGeodesic_path B x
  let P := Classical.choose hcanonical
  have hcanonicalSpec := Classical.choose_spec hcanonical
  obtain ⟨hP, hsteps, _hfirst⟩ := hcanonicalSpec
  change IsLexLeftmostXDPGeodesic B x P
  change IsXDPGeodesicBase B x P ∧ _
  refine ⟨hP, ?_⟩
  intro m Q hQ hne hnm i htake hdiff
  subst m
  let sel : MapVertex B.map → D := canonicalLeftmostXDPStep B x
  have hsel : ∀ v, (∃ n, ∃ R : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x R ∧ v ∈ R.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v) := by
    intro v hv hvs
    exact canonicalLeftmostXDPStep_spec B x v hv hvs
  let v := selectorVertex B sel i.val
  have hv := selectorVertex_mem_XDPGeodesic B x sel hsel i.val
  have hvs : v ≠ B.sink := by
    simpa [v, sel] using
      selectorVertex_ne_sink_of_lt_length B x sel hsel i.val i.isLt
  have hstepP : P.darts.get ⟨i.val, by simp [P.darts_length]⟩ =
      canonicalLeftmostXDPStep B x v := by
    simpa [v, sel] using hsteps i
  let d : D := P.darts.get ⟨i.val, by simp [P.darts_length]⟩
  let e : D := Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩
  have hdiff' : d ≠ e := hdiff
  have htailP : dartTailVertex B.map d = v := by
    change dartTailVertex B.map
      (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) = v
    rw [hstepP]
    exact (canonicalLeftmostXDPStep_spec B x v hv hvs).1
  have hpre : ∀ j : Fin i.val,
      P.darts.get ⟨j.val, by simpa [P.darts_length] using
        (show j.val < xdpLengthBase B x by omega)⟩ =
      Q.darts.get ⟨j.val, by simpa [Q.darts_length] using
        (show j.val < xdpLengthBase B x by omega)⟩ := by
    intro j
    have hjP : j.val < P.darts.length := by
      rw [P.darts_length]
      omega
    have hjQ : j.val < Q.darts.length := by
      rw [Q.darts_length]
      omega
    have hjTake : j.val < (P.darts.take i.val).length := by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨j.isLt, by rw [P.darts_length]; omega⟩
    have hTakeJ : (P.darts.take i.val)[j.val] =
        (Q.darts.take i.val)[j.val]'(htake ▸ hjTake) :=
      List.getElem_of_eq htake hjTake
    have hPj := List.getElem_take' hjP j.isLt
    have hQj := List.getElem_take' hjQ j.isLt
    simpa only [List.get_eq_getElem] using hPj.trans (hTakeJ.trans hQj.symm)
  have hvertices := path_vertices_eq_of_dart_prefix B P Q i.val (by omega) hpre
  have htailQ : dartTailVertex B.map e = v := by
    change dartTailVertex B.map
      (Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩) = v
    have hstepQ := (Q.edge_step ⟨i.val,
      by simp [Q.darts_length]⟩).2.2.1
    have hstepP' := (P.edge_step ⟨i.val,
      by simp [P.darts_length]⟩).2.2.1
    calc
      dartTailVertex B.map e = Q.vertices.get ⟨i.val,
          by simp [Q.vertices_length]⟩ := hstepQ.symm
      _ = P.vertices.get ⟨i.val,
          by simp [P.vertices_length]⟩ := hvertices.symm
      _ = dartTailVertex B.map d := hstepP'
      _ = v := htailP
  have hgeoE : IsXDPGeodesicDart B x e :=
    ⟨xdpLengthBase B x, Q, hQ, List.get_mem _ _⟩
  obtain ⟨rest, hfirst, hlocal⟩ :=
    canonicalLeftmostXDPStep_first B x v hv hvs
  have hrest : e ∈ rest := by
    rcases hlocal e htailQ hgeoE with heq | heq
    · exact (hdiff' (hstepP.trans heq.symm)).elim
    · exact heq
  have hfilter :
      (canonicalOutgoingOrder B v hvs).filter
          (fun dart => decide (IsXDPGeodesicDart B x dart)) =
        canonicalLeftmostXDPStep B x v :: rest := by
    simpa only [canonicalXDPGeodesicDartOrder] using hfirst
  have hlt := idxOf_lt_of_filter_cons
    (canonicalOutgoingOrder_nodup B v hvs) hfilter hrest
  have hvsD : dartTailVertex B.map d ≠ B.sink := by
    simpa [htailP] using hvs
  refine ⟨hvsD, ?_⟩
  have hsub : (⟨v, hvs⟩ : {w : MapVertex B.map // w ≠ B.sink}) =
      ⟨dartTailVertex B.map d, hvsD⟩ := by
    apply Subtype.ext
    exact htailP.symm
  have horders := congrArg
    (fun w : {v : MapVertex B.map // v ≠ B.sink} =>
      canonicalOutgoingOrder B w.val w.property) hsub
  rw [← horders]
  change (canonicalOutgoingOrder B v hvs).idxOf
      (P.darts.get ⟨i.val, by simp [P.darts_length]⟩) <
    (canonicalOutgoingOrder B v hvs).idxOf
      (Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩)
  rw [hstepP]
  simpa [e] using hlt

/-- There is a canonical lexicographically leftmost XDP geodesic, and any
other such geodesic has the same dart list. This uniqueness is only for the
internal lexicographic notion; the paper's region equivalence remains -/
theorem existsUnique_lexLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
      IsLexLeftmostXDPGeodesic B x P ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
          IsLexLeftmostXDPGeodesic B x Q → Q.darts = P.darts := by
  let hcanonical := exists_canonicalLeftmost_XDPGeodesic_path B x
  let P := Classical.choose hcanonical
  have hP : IsLexLeftmostXDPGeodesic B x P := by
    dsimp [P, hcanonical]
    exact canonical_isLexLeftmostXDPGeodesic B x
  refine ⟨P, hP, ?_⟩
  intro m Q hQ
  exact (dartLists_eq_of_isLexLeftmostXDPGeodesic B x P Q hP hQ).symm

/-- At the source, `canonicalOutgoingOrder` contains the entire rotation
cycle. This is a pole-case helper for the internal lexicographic notion; -/
theorem canonicalOutgoingOrder_source_covers_rotationCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B) ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) d := by
  have hleft := canonicalLeftmostOutgoing_spec B B.source
    (bipolar_source_ne_sink B)
  constructor
  · intro hd
    have hout := (mem_canonicalOutgoingOrder_iff B B.source
      (bipolar_source_ne_sink B) d).mp hd
    exact Quotient.exact (hleft.1.trans hout.1.symm)
  · intro hcycle
    have hsame : dartTailVertex B.map
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) =
      dartTailVertex B.map d := Quotient.sound hcycle
    have hdv : dartTailVertex B.map d = B.source := hsame.symm.trans hleft.1
    have htail := source_vertexRotationCycle_all_outgoing B ⟨d, hdv⟩
    exact (mem_canonicalOutgoingOrder_iff B B.source
      (bipolar_source_ne_sink B) d).mpr ⟨hdv, htail⟩

end DirectedDistances.PlanarMap
