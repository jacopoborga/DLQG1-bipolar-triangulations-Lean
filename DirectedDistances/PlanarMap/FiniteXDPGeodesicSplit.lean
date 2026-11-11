/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPDistances

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The initial segment of a simple directed dart path, including its endpoint -/
def SimpleDirectedDartPath.prefix
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    SimpleDirectedDartPath M s
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) i.val := by
  refine {
    darts := P.darts.take i.val
    vertices := P.vertices.take (i.val + 1)
    darts_length := by
      simp [P.darts_length, Nat.min_eq_left (by omega : i.val ≤ n)]
    vertices_length := by
      simp [P.vertices_length, Nat.min_eq_left (by omega : i.val + 1 ≤ n + 1)]
    vertices_nodup := P.vertices_nodup.take
    start_vertex := by
      change (P.vertices.take (i.val + 1))[0]'(by
        simp [List.length_take, P.vertices_length]) = s
      rw [List.getElem_take]
      simpa [List.get_eq_getElem] using P.start_vertex
    end_vertex := by
      change (P.vertices.take (i.val + 1))[i.val]'(by
        simp [List.length_take, P.vertices_length]
        omega) = P.vertices[i.val]'(by rw [P.vertices_length]; omega)
      exact (List.getElem_take' (xs := P.vertices) (i := i.val) (j := i.val + 1)
        (by rw [P.vertices_length]; omega) (by omega)).symm
    edge_step := by
      intro j
      have hj : j.val < i.val := by
        have h := j.isLt
        simp [List.length_take, P.darts_length, Nat.min_eq_left (by omega : i.val ≤ n)] at h
        exact h
      have hstep := P.edge_step ⟨j.val, by rw [P.darts_length]; omega⟩
      have hd : (P.darts.take i.val).get j = P.darts.get ⟨j.val, by rw [P.darts_length]; omega⟩ := by
        change (P.darts.take i.val)[j.val]'j.isLt =
          P.darts[j.val]'(by rw [P.darts_length]; omega)
        exact (List.getElem_take' (xs := P.darts) (i := j.val) (j := i.val)
          (by rw [P.darts_length]; omega) hj).symm
      have hv : (P.vertices.take (i.val + 1)).get ⟨j.val, by
          simp [List.length_take, P.vertices_length, Nat.min_eq_left (by omega : i.val + 1 ≤ n + 1)]
          omega⟩ =
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := by
        change (P.vertices.take (i.val + 1))[j.val]'(by
          simp [List.length_take, P.vertices_length]
          omega) = P.vertices[j.val]'(by rw [P.vertices_length]; omega)
        exact (List.getElem_take' (xs := P.vertices) (i := j.val) (j := i.val + 1)
          (by rw [P.vertices_length]; omega) (by omega)).symm
      have hv' : (P.vertices.take (i.val + 1)).get ⟨j.val + 1, by
          simp [List.length_take, P.vertices_length, Nat.min_eq_left (by omega : i.val + 1 ≤ n + 1)]
          omega⟩ =
          P.vertices.get ⟨j.val + 1, by rw [P.vertices_length]; omega⟩ := by
        change (P.vertices.take (i.val + 1))[j.val + 1]'(by
          simp [List.length_take, P.vertices_length]
          omega) = P.vertices[j.val + 1]'(by rw [P.vertices_length]; omega)
        exact (List.getElem_take' (xs := P.vertices) (i := j.val + 1) (j := i.val + 1)
          (by rw [P.vertices_length]; omega) (by omega)).symm
      simpa [hd, hv, hv'] using hstep
  }

/-- The terminal segment of a simple directed dart path, beginning at the -/
def SimpleDirectedDartPath.suffix
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    SimpleDirectedDartPath M
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) t (n - i.val) := by
  refine {
    darts := P.darts.drop i.val
    vertices := P.vertices.drop i.val
    darts_length := by simp [P.darts_length]
    vertices_length := by simp [P.vertices_length]; omega
    vertices_nodup := P.vertices_nodup.drop
    start_vertex := by
      change (P.vertices.drop i.val)[0]'(by
        simp [List.length_drop, P.vertices_length]
        omega) = P.vertices[i.val]'(by rw [P.vertices_length]; omega)
      simp
    end_vertex := by
      have hlast : i.val + (n - i.val) = n := by omega
      change (P.vertices.drop i.val).get ⟨n - i.val, by
        simp [List.length_drop, P.vertices_length]
        omega⟩ = t
      let iend : Fin P.vertices.length := ⟨i.val + (n - i.val), by
        rw [P.vertices_length]
        omega⟩
      let nend : Fin P.vertices.length := ⟨n, by rw [P.vertices_length]; omega⟩
      have hdrop : (P.vertices.drop i.val).get ⟨n - i.val, by
          simp [List.length_drop, P.vertices_length]
          omega⟩ = P.vertices.get iend := by
        simp [List.get_eq_getElem, iend]
      have hindex : iend = nend := Fin.ext hlast
      calc
        (P.vertices.drop i.val).get ⟨n - i.val, by
          simp [List.length_drop, P.vertices_length]
          omega⟩ = P.vertices.get iend := hdrop
        _ = P.vertices.get nend := by rw [hindex]
        _ = t := P.end_vertex
    edge_step := by
      intro j
      have hj : j.val < n - i.val := by
        have h := j.isLt
        simp [List.length_drop, P.darts_length, Nat.sub_add_cancel (show i.val ≤ n by omega)] at h
        omega
      have hstep := P.edge_step ⟨i.val + j.val, by rw [P.darts_length]; omega⟩
      have hd : (P.darts.drop i.val).get j = P.darts.get ⟨i.val + j.val, by rw [P.darts_length]; omega⟩ := by
        change (P.darts.drop i.val)[j.val]'j.isLt =
          P.darts[i.val + j.val]'(by rw [P.darts_length]; omega)
        exact List.getElem_drop
      have hv : (P.vertices.drop i.val).get ⟨j.val, by
          simp [List.length_drop, P.vertices_length]
          omega⟩ =
          P.vertices.get ⟨i.val + j.val, by rw [P.vertices_length]; omega⟩ := by
        change (P.vertices.drop i.val)[j.val]'(by
          simp [List.length_drop, P.vertices_length]
          omega) = P.vertices[i.val + j.val]'(by rw [P.vertices_length]; omega)
        exact List.getElem_drop
      have hv' : (P.vertices.drop i.val).get ⟨j.val + 1, by
          simp [List.length_drop, P.vertices_length]
          omega⟩ =
          P.vertices.get ⟨i.val + j.val + 1, by rw [P.vertices_length]; omega⟩ := by
        change (P.vertices.drop i.val)[j.val + 1]'(by
          simp [List.length_drop, P.vertices_length]
          omega) = P.vertices[i.val + j.val + 1]'(by rw [P.vertices_length]; omega)
        calc
          (P.vertices.drop i.val)[j.val + 1]'(by
            simp [List.length_drop, P.vertices_length]
            omega) = P.vertices[i.val + (j.val + 1)]'(by
            rw [P.vertices_length]
            omega) := List.getElem_drop
          _ = P.vertices[i.val + j.val + 1]'(by rw [P.vertices_length]; omega) := by
            congr 1 <;> omega
      simpa [hd, hv, hv', Nat.add_assoc] using hstep
  }

/-- Splitting at any vertex yields a prefix and suffix whose lengths add to -/
theorem SimpleDirectedDartPath.split
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    ∃ P₁ : SimpleDirectedDartPath M s
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) i.val,
    ∃ P₂ : SimpleDirectedDartPath M
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) t (n - i.val), True :=
  ⟨P.prefix i, P.suffix i, trivial⟩

private theorem path_vertex_reaches_end
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin P.vertices.length) :
    Relation.ReflTransGen M.directedStep (P.vertices.get i) t := by
  generalize hdist : n - i.val = k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
      have hi : i.val ≤ n := by
        have h := i.isLt
        have hlen := P.vertices_length
        omega
      by_cases hik : i.val = n
      · have hiend : i = ⟨n, by have hlen := P.vertices_length; omega⟩ := Fin.ext hik
        have hend : P.vertices.get i = t := by
          rw [hiend]
          exact P.end_vertex
        rw [hend]
      · have hik' : i.val < n := by omega
        let j : Fin P.vertices.length := ⟨i.val + 1, by
          have hlen := P.vertices_length
          omega⟩
        have hstepIdx : i.val < P.darts.length := by
          have hlen := P.darts_length
          omega
        have hstep := P.edge_step ⟨i.val, hstepIdx⟩
        have hstepRel : M.directedStep (P.vertices.get i) (P.vertices.get j) := by
          refine ⟨P.darts.get ⟨i.val, by have hlen := P.darts_length; omega⟩,
            hstep.1, hstep.2.1, ?_, ?_⟩
          · exact hstep.2.2.1.symm
          · exact hstep.2.2.2.symm
        have hjdist : n - j.val < k := by dsimp [j]; omega
        have hj : Relation.ReflTransGen M.directedStep (P.vertices.get j) t :=
          ih (n - j.val) hjdist j rfl
        exact hj.head hstepRel

private theorem path_start_reaches_vertex
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin P.vertices.length) :
    Relation.ReflTransGen M.directedStep s (P.vertices.get i) := by
  generalize hval : i.val = k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
      have hk : i.val = k := hval
      have hkbound : k ≤ n := by
        have h := i.isLt
        have hlen := P.vertices_length
        omega
      by_cases hk0 : k = 0
      · let i0 : Fin P.vertices.length := ⟨0, by
          have hlen := P.vertices_length
          omega⟩
        have hi : i = i0 := Fin.ext (by dsimp [i0]; omega)
        rw [hi]
        rw [P.start_vertex]
      · have hkpos : 0 < k := by omega
        let j : Fin P.vertices.length := ⟨k - 1, by
          have hlen := P.vertices_length
          omega⟩
        have hjlt : j.val < k := by dsimp [j]; omega
        have jdlt : j.val < P.darts.length := by
          have hlen := P.darts_length
          omega
        have hstep := P.edge_step ⟨j.val, jdlt⟩
        have hi : i = ⟨j.val + 1, by
          have hlen := P.vertices_length
          omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        have hstepRel : M.directedStep (P.vertices.get j) (P.vertices.get i) := by
          refine ⟨P.darts.get ⟨j.val, jdlt⟩, hstep.1, hstep.2.1, ?_, ?_⟩
          · exact hstep.2.2.1.symm
          · rw [hi]
            exact hstep.2.2.2.symm
        have hrec : Relation.ReflTransGen M.directedStep s (P.vertices.get j) :=
          ih j.val hjlt j rfl
        exact hrec.tail hstepRel

private theorem path_end_not_mem_take
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) : t ∉ P.vertices.take n := by
  intro ht
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  have hi_lt : i.val < n := by
    have h := i.isLt
    simp [List.length_take, P.vertices_length] at h
    omega
  let iP : Fin P.vertices.length := ⟨i.val, by
    have hlen := P.vertices_length
    omega⟩
  let nP : Fin P.vertices.length := ⟨n, by
    have hlen := P.vertices_length
    omega⟩
  have htake : (P.vertices.take n).get i = P.vertices.get iP := by
    change (P.vertices.take n)[i.val]'i.isLt = P.vertices[i.val]'(by
      have hlen := P.vertices_length
      omega)
    exact (List.getElem_take' (xs := P.vertices) (i := i.val) (j := n)
      (by have hlen := P.vertices_length; omega) hi_lt).symm
  have hEq : P.vertices.get iP = P.vertices.get nP := by
    calc
      P.vertices.get iP = (P.vertices.take n).get i := htake.symm
      _ = t := hi
      _ = P.vertices.get nP := P.end_vertex.symm
  have hfin := P.vertices_nodup.get_inj_iff.mp hEq
  have hval := congrArg Fin.val hfin
  have : i.val = n := by simpa [iP, nP] using hval
  omega

/-- If two directed paths meet away from their common joining vertex, their
union would contain a directed cycle (`lem-lr-ind`, -/
theorem path_common_vertex_eq_join
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n)
    (Q : SimpleDirectedDartPath M x t m)
    {v : MapVertex M} (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices) :
    v = x := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvP
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hvQ
  have hQraw := path_start_reaches_vertex M Q j
  have hPraw := path_vertex_reaches_end M P i
  have hmeet : P.vertices.get i = Q.vertices.get j := hi.trans hj.symm
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hQraw with hQeq | hforward
  · calc
      v = P.vertices.get i := hi.symm
      _ = Q.vertices.get j := hmeet
      _ = x := hQeq
  · have hbackClosure : Relation.ReflTransGen M.directedStep (Q.vertices.get j) x :=
      Eq.mp (congrArg (fun w => Relation.ReflTransGen M.directedStep w x) hmeet) hPraw
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hbackClosure with hbackEq | hback
    · have hcycle : Relation.TransGen M.directedStep x x :=
        Eq.mp (congrArg (fun w => Relation.TransGen M.directedStep x w) hbackEq.symm) hforward
      exact False.elim (hacyclic x hcycle)
    · exact False.elim (hacyclic x (Relation.TransGen.trans hforward hback))

private def appendSimplePathStep
    (M : DirectedMapWithMissing D) {s y v : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s y n) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = y) (hhy : dartHeadVertex M d = v)
    (hv : v ∉ P.vertices) : SimpleDirectedDartPath M s v (n + 1) := by
  refine {
    darts := P.darts ++ [d]
    vertices := P.vertices ++ [v]
    darts_length := by simp [P.darts_length]
    vertices_length := by simp [P.vertices_length]
    vertices_nodup := by
      rw [List.nodup_append]
      refine ⟨P.vertices_nodup, by simp, ?_⟩
      intro a ha b hb hab
      have hbv : b = v := List.mem_singleton.mp hb
      have hav : a = v := hab.trans hbv
      exact hv (hav ▸ ha)
    start_vertex := by
      have h0 : (0 : ℕ) < P.vertices.length := by
        have hlen := P.vertices_length
        omega
      calc
        (P.vertices ++ [v]).get ⟨0, by simp [List.length_append, P.vertices_length]⟩ =
            P.vertices.get ⟨0, h0⟩ := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left h0
        _ = s := P.start_vertex
    end_vertex := by simp [List.get_eq_getElem, P.vertices_length]
    edge_step := by
      intro i
      have hi : i.val ≤ n := by
        have h := i.isLt
        simp only [List.length_append, List.length_singleton, P.darts_length] at h
        omega
      by_cases hlt : i.val < n
      · let j : Fin P.darts.length := ⟨i.val, by have hlen := P.darts_length; omega⟩
        let jv : Fin P.vertices.length := ⟨i.val, by have hlen := P.vertices_length; omega⟩
        let jv' : Fin P.vertices.length := ⟨i.val + 1, by have hlen := P.vertices_length; omega⟩
        have hs := P.edge_step j
        have hltD : i.val < P.darts.length := by
          have hlen := P.darts_length
          omega
        have hltV : i.val < P.vertices.length := by
          have hlen := P.vertices_length
          omega
        have hltV' : i.val + 1 < P.vertices.length := by
          have hlen := P.vertices_length
          omega
        have hgetD : (P.darts ++ [d]).get i = P.darts.get j := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left hltD
        have hgetV : (P.vertices ++ [v]).get ⟨i.val, by
            simp [List.length_append, P.vertices_length]
            omega⟩ = P.vertices.get jv := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left hltV
        have hgetV' : (P.vertices ++ [v]).get ⟨i.val + 1, by
            simp [List.length_append, P.vertices_length]
            omega⟩ = P.vertices.get jv' := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left hltV'
        rw [hgetD, hgetV, hgetV']
        exact hs
      · have hieq : i.val = n := by omega
        have hifin : i = ⟨n, by simp [List.length_append, P.darts_length]⟩ := Fin.ext hieq
        subst i
        have hlast : (P.darts ++ [d]).get ⟨n, by simp [List.length_append, P.darts_length]⟩ = d := by
          simp [List.get_eq_getElem, P.darts_length]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlast]
          exact hmiss
        · rw [hlast]
          exact htail
        · rw [hlast]
          simpa [List.get_eq_getElem, P.vertices_length] using P.end_vertex.trans hty.symm
        · rw [hlast]
          simpa [List.get_eq_getElem, P.vertices_length] using hhy.symm
  }

private def appendSimplePathStep_of_acyclic
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s x n) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = x) (hhy : dartHeadVertex M d = y) :
    SimpleDirectedDartPath M s y (n + 1) := by
  have hnot : y ∉ P.vertices := by
    intro hy
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hy
    have hraw := path_vertex_reaches_end M P i
    have hreach : Relation.ReflTransGen M.directedStep y x :=
      Eq.mp (congrArg (fun v => Relation.ReflTransGen M.directedStep v x) hi) hraw
    have hstep : M.directedStep x y := ⟨d, hmiss, htail, hty, hhy⟩
    exact hacyclic y (Relation.TransGen.tail' hreach hstep)
  exact appendSimplePathStep M P d hmiss htail hty hhy hnot

/-- Acyclic concatenation of two simple directed paths with a common endpoint -/
def SimpleDirectedDartPath.concat
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n)
    (Q : SimpleDirectedDartPath M x t m) :
    SimpleDirectedDartPath M s t (n + m) := by
  induction m generalizing s x t n P with
  | zero =>
      have hxt : x = t := Q.start_vertex.symm.trans Q.end_vertex
      subst t
      simpa using P
  | succ m ih =>
      let i0 : Fin Q.darts.length := ⟨0, by rw [Q.darts_length]; omega⟩
      let q0 : Fin Q.vertices.length := ⟨0, by
        have hlen := Q.vertices_length
        omega⟩
      let q1n : Fin (m + 1 + 1) := ⟨1, by omega⟩
      let q1 : Fin Q.vertices.length := ⟨q1n.val, by
        rw [Q.vertices_length]
        exact q1n.isLt⟩
      let d := Q.darts.get i0
      have hfirst := Q.edge_step i0
      have htailEq : Q.vertices.get q0 = dartTailVertex M d := by
        simpa [i0, q0, d] using hfirst.2.2.1
      have hheadEq : Q.vertices.get q1 = dartHeadVertex M d := by
        simpa [i0, q1, d] using hfirst.2.2.2
      have htail : dartTailVertex M d = x := by
        calc
          dartTailVertex M d = Q.vertices.get q0 := htailEq.symm
          _ = x := by simpa [q0] using Q.start_vertex
      have hhead : dartHeadVertex M d = Q.vertices.get q1 := hheadEq.symm
      let P' := appendSimplePathStep_of_acyclic M hacyclic P d
        hfirst.1 hfirst.2.1 htail hhead
      let hQ0 : SimpleDirectedDartPath M (Q.vertices.get q1) t ((m + 1) - 1) :=
        Q.suffix q1n
      have hlen : (m + 1) - 1 = m := by omega
      let hQ' : SimpleDirectedDartPath M (Q.vertices.get q1) t m :=
        cast (congrArg (fun k => SimpleDirectedDartPath M (Q.vertices.get q1) t k)
          hlen) hQ0
      have hresult := ih P' hQ'
      convert hresult using 1 <;> omega

/-- Concatenate a simple path, one present directed dart, and a simple path
at the dart endpoints (`lem-lr-ind`, -/
def SimpleDirectedDartPath.concat_dart
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x y t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = x) (hhy : dartHeadVertex M d = y)
    (Q : SimpleDirectedDartPath M y t m) :
    SimpleDirectedDartPath M s t (n + 1 + m) := by
  let P' := appendSimplePathStep_of_acyclic M hacyclic P d hmiss htail hty hhy
  have hresult := SimpleDirectedDartPath.concat M hacyclic P' Q
  convert hresult using 1 <;> omega

/-- The prefix and suffix distances on an LDP geodesic equal their segment -/
theorem IsLDPGeodesicBase.prefix_suffix_distanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsLDPGeodesicBase B P) (i : Fin (n + 1)) :
    ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      exact i.isLt⟩) = i.val ∧
    ldpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      exact i.isLt⟩) = n - i.val := by
  let v := P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩
  constructor
  · apply Nat.le_antisymm
    · unfold ldpSourceDistanceNatBase
      apply (sourceVertexPathLengthsBase B v).max'_le
      intro k hk
      obtain ⟨Q, _⟩ := (mem_sourceVertexPathLengthsBase B v k).1 hk
      have hR := SimpleDirectedDartPath.concat B.map B.acyclic Q (P.suffix i)
      have hgeo := hP hR
      omega
    · have hmem := (mem_sourceVertexPathLengthsBase B v i.val).2
        ⟨P.prefix i, trivial⟩
      unfold ldpSourceDistanceNatBase
      exact (sourceVertexPathLengthsBase B v).le_max' i.val hmem
  · apply Nat.le_antisymm
    · unfold ldpSinkDistanceNatBase
      apply (vertexSinkPathLengthsBase B v).max'_le
      intro k hk
      obtain ⟨Q, _⟩ := (mem_vertexSinkPathLengthsBase B v k).1 hk
      have hR := SimpleDirectedDartPath.concat B.map B.acyclic (P.prefix i) Q
      have hgeo := hP hR
      omega
    · have hmem := (mem_vertexSinkPathLengthsBase B v (n - i.val)).2
        ⟨P.suffix i, trivial⟩
      unfold ldpSinkDistanceNatBase
      exact (vertexSinkPathLengthsBase B v).le_max' (n - i.val) hmem

/-- The prefix and suffix distances on an SDP geodesic equal their segment -/
theorem IsSDPGeodesicBase.prefix_suffix_distanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsSDPGeodesicBase B P) (i : Fin (n + 1)) :
    sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      exact i.isLt⟩) = i.val ∧
    sdpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      exact i.isLt⟩) = n - i.val := by
  let v := P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩
  constructor
  · apply Nat.le_antisymm
    · have hmem := (mem_sourceVertexPathLengthsBase B v i.val).2
        ⟨P.prefix i, trivial⟩
      unfold sdpSourceDistanceNatBase
      exact (sourceVertexPathLengthsBase B v).min'_le i.val hmem
    · unfold sdpSourceDistanceNatBase
      apply (sourceVertexPathLengthsBase B v).le_min'
      intro k hk
      obtain ⟨Q, _⟩ := (mem_sourceVertexPathLengthsBase B v k).1 hk
      have hR := SimpleDirectedDartPath.concat B.map B.acyclic Q (P.suffix i)
      have hgeo := hP hR
      omega
  · apply Nat.le_antisymm
    · have hmem := (mem_vertexSinkPathLengthsBase B v (n - i.val)).2
        ⟨P.suffix i, trivial⟩
      unfold sdpSinkDistanceNatBase
      exact (vertexSinkPathLengthsBase B v).min'_le (n - i.val) hmem
    · unfold sdpSinkDistanceNatBase
      apply (vertexSinkPathLengthsBase B v).le_min'
      intro k hk
      obtain ⟨Q, _⟩ := (mem_vertexSinkPathLengthsBase B v k).1 hk
      have hR := SimpleDirectedDartPath.concat B.map B.acyclic (P.prefix i) Q
      have hgeo := hP hR
      omega

/-- The head vertex of a geodesic dart remains on that geodesic and has
source distance one greater than its tail (`def-ldp`, -/
theorem IsXDPGeodesicDart.headVertex_sourceDistanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) (d : D)
    (v : MapVertex B.map) (hd : IsXDPGeodesicDart B x d)
    (htail : dartTailVertex B.map d = v) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ dartHeadVertex B.map d ∈ P.vertices ∧
      (match x with
       | .ldp => ldpSourceDistanceNatBase B (dartHeadVertex B.map d) =
           ldpSourceDistanceNatBase B v + 1
       | .sdp => sdpSourceDistanceNatBase B (dartHeadVertex B.map d) =
           sdpSourceDistanceNatBase B v + 1) := by
  cases x with
  | ldp =>
      obtain ⟨n, P, hP, hdmem⟩ := hd
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdmem
      have hstep := P.edge_step i
      rw [hi] at hstep
      have hin : i.val < n := by
        have hlen := P.darts_length
        omega
      let iN : Fin (n + 1) := ⟨i.val, by
        omega⟩
      let jN : Fin (n + 1) := ⟨i.val + 1, by
        omega⟩
      have htailV : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = v := by
        calc
          P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
              dartTailVertex B.map d := by simpa using hstep.2.2.1
          _ = v := htail
      have hheadV : P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩ =
          dartHeadVertex B.map d := by simpa using hstep.2.2.2
      have hheadMem : dartHeadVertex B.map d ∈ P.vertices :=
        List.mem_iff_get.mpr ⟨⟨i.val + 1, by rw [P.vertices_length]; omega⟩, hheadV⟩
      have hdist := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP iN
      have hdistHead := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP jN
      have htailDist : ldpSourceDistanceNatBase B v = i.val := by
        calc
          ldpSourceDistanceNatBase B v = ldpSourceDistanceNatBase B
              (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩) :=
                congrArg (ldpSourceDistanceNatBase B) htailV.symm
          _ = i.val := by simpa [iN] using hdist.1
      have hheadDist : ldpSourceDistanceNatBase B (dartHeadVertex B.map d) = i.val + 1 := by
        calc
          ldpSourceDistanceNatBase B (dartHeadVertex B.map d) =
              ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩) :=
                congrArg (ldpSourceDistanceNatBase B) hheadV.symm
          _ = i.val + 1 := by simpa [jN] using hdistHead.1
      refine ⟨n, P, hP, hheadMem, ?_⟩
      rw [hheadDist, htailDist]
  | sdp =>
      obtain ⟨n, P, hP, hdmem⟩ := hd
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdmem
      have hstep := P.edge_step i
      rw [hi] at hstep
      have hin : i.val < n := by
        have hlen := P.darts_length
        omega
      let iN : Fin (n + 1) := ⟨i.val, by
        omega⟩
      let jN : Fin (n + 1) := ⟨i.val + 1, by
        omega⟩
      have htailV : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = v := by
        calc
          P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
              dartTailVertex B.map d := by simpa using hstep.2.2.1
          _ = v := htail
      have hheadV : P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩ =
          dartHeadVertex B.map d := by simpa using hstep.2.2.2
      have hheadMem : dartHeadVertex B.map d ∈ P.vertices :=
        List.mem_iff_get.mpr ⟨⟨i.val + 1, by rw [P.vertices_length]; omega⟩, hheadV⟩
      have hdist := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP iN
      have hdistHead := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP jN
      have htailDist : sdpSourceDistanceNatBase B v = i.val := by
        calc
          sdpSourceDistanceNatBase B v = sdpSourceDistanceNatBase B
              (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩) :=
                congrArg (sdpSourceDistanceNatBase B) htailV.symm
          _ = i.val := by simpa [iN] using hdist.1
      have hheadDist : sdpSourceDistanceNatBase B (dartHeadVertex B.map d) = i.val + 1 := by
        calc
          sdpSourceDistanceNatBase B (dartHeadVertex B.map d) =
              sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩) :=
                congrArg (sdpSourceDistanceNatBase B) hheadV.symm
          _ = i.val + 1 := by simpa [jN] using hdistHead.1
      refine ⟨n, P, hP, hheadMem, ?_⟩
      rw [hheadDist, htailDist]

end DirectedDistances.PlanarMap

namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- Internal unfolding fact for `SimpleDirectedDartPath.prefix_darts`. -/
private theorem prefix_darts_internal
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.prefix i).darts = P.darts.take i.val := rfl

/-- The dart list of a path prefix is the corresponding initial dart segment.
`def-geodesic`; not the paper result. -/
theorem SimpleDirectedDartPath.prefix_darts
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.prefix i).darts = P.darts.take i.val := prefix_darts_internal P i

/-- The vertex list of a path prefix is the corresponding initial vertex
segment, including its endpoint. Helper toward `lem-lr-ind`
result. -/
private theorem prefix_vertices_internal
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.prefix i).vertices = P.vertices.take (i.val + 1) := rfl

/-- The vertex list of a path prefix is the corresponding initial vertex
segment, including its endpoint. Helper toward `lem-lr-ind`
result. -/
theorem SimpleDirectedDartPath.prefix_vertices
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.prefix i).vertices = P.vertices.take (i.val + 1) := prefix_vertices_internal P i

/-- The dart list of a path suffix is the corresponding terminal dart segment.
`def-geodesic`; not the paper result. -/
private theorem suffix_darts_internal
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.suffix i).darts = P.darts.drop i.val := rfl

/-- The dart list of a path suffix is the corresponding terminal dart segment.
`def-geodesic`; not the paper result. -/
theorem SimpleDirectedDartPath.suffix_darts
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.suffix i).darts = P.darts.drop i.val := suffix_darts_internal P i

/-- The vertex list of a path suffix is the corresponding terminal vertex
and `def-geodesic`; not the paper result. -/
private theorem suffix_vertices_internal
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.suffix i).vertices = P.vertices.drop i.val := rfl

/-- The vertex list of a path suffix is the corresponding terminal vertex
and `def-geodesic`; not the paper result. -/
theorem SimpleDirectedDartPath.suffix_vertices
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin (n + 1)) :
    (P.suffix i).vertices = P.vertices.drop i.val := suffix_vertices_internal P i

end DirectedDistances.PlanarMap
