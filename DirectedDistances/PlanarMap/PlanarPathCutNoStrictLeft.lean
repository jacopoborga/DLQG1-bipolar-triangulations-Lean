module

public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion
public import DirectedDistances.PlanarMap.PlanarPathCutStrictLeftEntry

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}



@[expose] def SimpleDirectedDartPath.appendAcyclic
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s v t : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M s v a) (Q : SimpleDirectedDartPath M v t b) :
    SimpleDirectedDartPath M s t (a + b) := by
  have hplen := P.vertices_length
  have hqlen := Q.vertices_length
  have htake : (P.vertices.take a).length = a := by
    simp only [List.length_take, hplen, Nat.min_eq_left (by omega : a ≤ a + 1)]
  let V := P.vertices.take a ++ Q.vertices
  have hvlen : V.length = a + b + 1 := by
    simp only [V, List.length_append, htake, hqlen, Nat.add_assoc]
  have hright (k : ℕ) (hk : k < a + b + 1) (hka : a ≤ k) :
      V[k]'(by omega) = Q.vertices[k - a]'(by omega) := by
    dsimp [V]
    rw [List.getElem_append_right (by omega)]
    simp only [htake]
  have hleft (k : ℕ) (hk : k ≤ a) :
      V[k]'(by omega) = P.vertices[k]'(by omega) := by
    by_cases hlt : k < a
    · dsimp [V]
      rw [List.getElem_append_left (by omega), List.getElem_take]
    · have heq : k = a := by omega
      subst k
      rw [hright a (by omega) (by omega)]
      simpa only [Nat.sub_self, List.get_eq_getElem] using
        Q.start_vertex.trans P.end_vertex.symm
  refine {
    darts := P.darts ++ Q.darts
    vertices := V
    darts_length := by simp only [List.length_append, P.darts_length, Q.darts_length]
    vertices_length := hvlen
    vertices_nodup := ?_
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_
  }
  · rw [List.nodup_append]
    refine ⟨P.vertices_nodup.take, Q.vertices_nodup, ?_⟩
    intro w hw z hz hwz
    have hwQ : w ∈ Q.vertices := hwz.symm ▸ hz
    have hwv := path_common_vertex_eq_join M hacyclic P Q
      (List.mem_of_mem_take hw) hwQ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hw
    have hia : i.val < a := by have := i.isLt; omega
    have heq : P.vertices.get ⟨i.val, by omega⟩ =
        P.vertices.get ⟨a, by omega⟩ := by
      simpa only [List.get_eq_getElem, List.getElem_take] using
        hi.trans (hwv.trans P.end_vertex.symm)
    have hiend := P.vertices_nodup.get_inj_iff.mp heq
    have hiv : i.val = a := congrArg Fin.val hiend
    omega
  · simpa only [List.get_eq_getElem, hleft 0 (by omega)] using P.start_vertex
  · simpa only [List.get_eq_getElem, hright (a + b) (by omega) (by omega),
      Nat.add_sub_cancel_left] using Q.end_vertex
  · intro i
    have hib : i.val < a + b := by
      have := i.isLt
      simp only [List.length_append, P.darts_length, Q.darts_length] at this
      exact this
    simp only [List.get_eq_getElem]
    by_cases hia : i.val < a
    · have hs := P.edge_step ⟨i.val, by rw [P.darts_length]; exact hia⟩
      simp only [List.get_eq_getElem] at hs
      rw [List.getElem_append_left (by rw [P.darts_length]; exact hia),
        hleft i.val (by omega), hleft (i.val + 1) (by omega)]
      exact hs
    · have hs := Q.edge_step ⟨i.val - a, by rw [Q.darts_length]; omega⟩
      simp only [List.get_eq_getElem] at hs
      rw [List.getElem_append_right (by rw [P.darts_length]; omega),
        hright i.val (by omega) (by omega),
        hright (i.val + 1) (by omega) (by omega)]
      simpa only [P.darts_length, Nat.sub_add_comm (by omega : a ≤ i.val)] using hs



theorem SimpleDirectedDartPath.appendAcyclic_darts
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s v t : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M s v a) (Q : SimpleDirectedDartPath M v t b) :
    (P.appendAcyclic M hacyclic Q).darts = P.darts ++ Q.darts := rfl



theorem lexLeftmost_no_strict_left_dart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsLexLeftmostXDPGeodesic B x P)
    {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m)
    (hQ : IsXDPGeodesicBase B x Q) (d : D) (hd : d ∈ Q.darts)
    (hleft : d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P) : False := by
  classical
  have hmn : m = n := by
    cases x with
    | ldp => exact Nat.le_antisymm (hP.1 Q) (hQ P)
    | sdp => exact Nat.le_antisymm (hQ P) (hP.1 Q)
  subst m
  have hex : ∃ j : ℕ, ∃ hj : j < Q.darts.length,
      Q.darts.get ⟨j, hj⟩ ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P := by
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    exact ⟨j.val, j.isLt, hj.symm ▸ hleft⟩
  let j := Nat.find hex
  obtain ⟨hjd, hjleft⟩ := Nat.find_spec hex
  have hjn : j < n := by simpa only [j, Q.darts_length] using hjd
  let jD : Fin Q.darts.length := ⟨j, hjd⟩
  let jN : Fin (n + 1) := ⟨j, by omega⟩
  have hjleft' : Q.darts.get jD ∈
      pathCutLeftDarts B P \ pathCutSeamDarts B P := hjleft
  have hfirst : ∀ k : Fin n, k.val < j →
      Q.darts.get ⟨k.val, by rw [Q.darts_length]; exact k.isLt⟩ ∉
        pathCutLeftDarts B P \ pathCutSeamDarts B P := by
    intro k hkj hk
    exact Nat.find_min hex hkj ⟨by rw [Q.darts_length]; exact k.isLt, hk⟩
  have htail := pathCut_firstStrictLeft_tail_mem_all B P Q
    ⟨j, hjn⟩ hjleft' hfirst
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp htail
  have hplen := P.vertices_length
  have hqlen := Q.vertices_length
  have hvertex : P.vertices.get i =
      Q.vertices.get ⟨j, by omega⟩ :=
    hi.trans (Q.edge_step jD).2.2.1.symm
  have hpi := xdpGeodesic_prefix_suffix_distanceNat B x P hP.1
    ⟨i.val, by have := i.isLt; omega⟩
  have hqj := xdpGeodesic_prefix_suffix_distanceNat B x Q hQ jN
  have hij : i.val = j := by
    cases x <;> dsimp only at hpi hqj <;>
      rw [hvertex] at hpi <;> exact hpi.1.symm.trans hqj.1
  have hmeet : P.vertices.get ⟨j, by omega⟩ =
      Q.vertices.get ⟨j, by omega⟩ := by
    have hiEq : i = ⟨j, by omega⟩ := Fin.ext hij
    rw [hiEq] at hvertex
    exact hvertex
  let QS := Q.suffix jN
  let S : SimpleDirectedDartPath B.map
      (P.vertices.get ⟨j, by omega⟩) B.sink (n - j) :=
    { QS with start_vertex := QS.start_vertex.trans hmeet.symm }
  have hSd : S.darts = Q.darts.drop j := Q.suffix_darts jN
  let R₀ := (P.prefix jN).appendAcyclic B.map B.acyclic S
  have hlen : j + (n - j) = n := by omega
  let R : SimpleDirectedDartPath B.map B.source B.sink n := {
    darts := R₀.darts
    vertices := R₀.vertices
    darts_length := R₀.darts_length.trans hlen
    vertices_length := R₀.vertices_length.trans (congrArg (· + 1) hlen)
    vertices_nodup := R₀.vertices_nodup
    start_vertex := R₀.start_vertex
    end_vertex := by
      have he := R₀.end_vertex
      simpa only [show jN.val = j from rfl, hlen] using he
    edge_step := R₀.edge_step }
  have hRd : R.darts = P.darts.take j ++ Q.darts.drop j := by
    change R₀.darts = _
    rw [SimpleDirectedDartPath.appendAcyclic_darts, P.prefix_darts, hSd]
  have hR : IsXDPGeodesicBase B x R := by cases x <;> exact hP.1
  have htake : (P.darts.take j).length = j := by
    simp only [List.length_take, P.darts_length, Nat.min_eq_left (by omega : j ≤ n)]
  have hpre : P.darts.take j = R.darts.take j := by
    rw [hRd, List.take_append]
    simp only [List.take_take, Nat.min_self, htake, Nat.sub_self, List.take_zero,
      List.append_nil]
  have hget : R.darts.get ⟨j, by rw [R.darts_length]; exact hjn⟩ =
      Q.darts.get jD := by
    simp only [List.get_eq_getElem]
    calc
      R.darts[j]'(by rw [R.darts_length]; exact hjn) =
          (P.darts.take j ++ Q.darts.drop j)[j]'(by
          simp only [List.length_append, htake, List.length_drop, Q.darts_length]
          omega) := List.getElem_of_eq hRd _
      _ = Q.darts[jD.val]'jD.isLt := by
        rw [List.getElem_append_right (by omega)]
        simp only [htake, Nat.sub_self, List.getElem_drop, Nat.add_zero]
        rfl
  have hRleft : R.darts.get ⟨j, by rw [R.darts_length]; exact hjn⟩ ∈
      pathCutLeftDarts B P \ pathCutSeamDarts B P := hget ▸ hjleft'
  have hdiff : P.darts.get ⟨j, by rw [P.darts_length]; exact hjn⟩ ≠
      R.darts.get ⟨j, by rw [R.darts_length]; exact hjn⟩ := by
    intro heq
    apply hRleft.2
    exact Or.inl (heq ▸ List.get_mem P.darts ⟨j, by rw [P.darts_length]; exact hjn⟩)
  by_cases hj0 : j = 0
  · exact lexLeftmost_no_strict_left_dart_at_firstDivergence_source B x P R hP hR
      (by simpa only [hj0] using hdiff) (by simpa only [hj0] using hRleft)
  · exact lexLeftmost_no_strict_left_dart_at_firstDivergence B x P R hP hR
      ⟨j, hjn⟩ (Nat.pos_of_ne_zero hj0) hpre hdiff hRleft

end DirectedDistances.PlanarMap
