/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPLeftmost

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}


/-- Every vertex listed on a simple directed path reaches its endpoint along
the remaining directed steps (`lem-lr-ind`, -/
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
      · have hiend : i = ⟨n, by omega⟩ := Fin.ext hik
        have hend : P.vertices.get i = t := by
          simpa [hiend] using P.end_vertex
        rw [hend]
      · have hik' : i.val < n := by omega
        let j : Fin P.vertices.length := ⟨i.val + 1, by have hlen := P.vertices_length; omega⟩
        have hstepIdx : i.val < P.darts.length := by
          have h := P.darts_length
          omega
        have hstep := P.edge_step ⟨i.val, hstepIdx⟩
        have hstepRel : M.directedStep (P.vertices.get i) (P.vertices.get j) := by
          change ∃ e, ¬M.missing e ∧ M.tail e ∧
            dartTailVertex M e = P.vertices.get i ∧
            dartHeadVertex M e = P.vertices.get j
          refine ⟨P.darts.get ⟨i.val, hstepIdx⟩, hstep.1, hstep.2.1, ?_, ?_⟩
          · exact hstep.2.2.1.symm
          · exact hstep.2.2.2.symm
        have hjdist : n - j.val < k := by
          dsimp [j]
          omega
        have hj : Relation.ReflTransGen M.directedStep (P.vertices.get j) t :=
          ih (n - j.val) hjdist j rfl
        exact hj.head hstepRel


/-- Every vertex listed on a simple directed path is reachable from its start
along the preceding steps (`lem-lr-ind`, -/
private theorem path_start_reaches_vertex
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : Fin P.vertices.length) :
    Relation.ReflTransGen M.directedStep s (P.vertices.get i) := by
  generalize hval : i.val = k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
      have hik : i.val = k := hval
      have hkbound : k ≤ n := by
        have h := i.isLt
        have hlen := P.vertices_length
        omega
      by_cases hk0 : k = 0
      · let i0 : Fin P.vertices.length := ⟨0, by simp [P.vertices_length]⟩
        have hi : i = i0 := by
          apply Fin.ext
          simpa [i0] using hik.trans hk0
        have hstart : P.vertices.get i = s := by
          calc
            P.vertices.get i = P.vertices.get i0 := congrArg P.vertices.get hi
            _ = s := P.start_vertex
        rw [hstart]
      · have hkpos : 0 < k := by omega
        let j : Fin P.vertices.length := ⟨k - 1, by have h := P.vertices_length; omega⟩
        have hjlt : j.val < k := by dsimp [j]; omega
        have jdlt : j.val < P.darts.length := by
          have h := P.darts_length
          omega
        let jd : Fin P.darts.length := ⟨j.val, jdlt⟩
        have hstep := P.edge_step jd
        have hi : i = ⟨j.val + 1, by have h := P.vertices_length; omega⟩ := by
          apply Fin.ext
          dsimp [j]
          omega
        have hnext : P.vertices.get ⟨j.val + 1, by have h := P.vertices_length; omega⟩ = P.vertices.get i :=
          congrArg P.vertices.get hi.symm
        have hstepRel : M.directedStep (P.vertices.get j) (P.vertices.get i) := by
          change ∃ e, ¬M.missing e ∧ M.tail e ∧
            dartTailVertex M e = P.vertices.get j ∧
            dartHeadVertex M e = P.vertices.get i
          refine ⟨P.darts.get jd, hstep.1, hstep.2.1, ?_, ?_⟩
          · exact hstep.2.2.1.symm
          · exact hstep.2.2.2.symm.trans hnext
        have hrec : Relation.ReflTransGen M.directedStep s (P.vertices.get j) :=
          ih j.val hjlt j rfl
        exact hrec.tail hstepRel

/-- Append a final directed dart while retaining simplicity, when acyclicity
shows its head was not visited earlier (`lem-lr-ind`, -/
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
      have h0 : (0 : ℕ) < P.vertices.length := by have hlen := P.vertices_length; omega
      calc
        (P.vertices ++ [v]).get ⟨0, by simp [List.length_append, P.vertices_length]⟩ =
            P.vertices.get ⟨0, h0⟩ := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left h0
        _ = s := P.start_vertex
    end_vertex := by
      simp [List.get_eq_getElem, P.vertices_length]
    edge_step := by
      intro i
      have hi : i.val ≤ n := by
        have h := i.isLt
        simp only [List.length_append, List.length_singleton, P.darts_length] at h
        omega
      by_cases hlt : i.val < n
      · let j : Fin P.darts.length := ⟨i.val, by have h := P.darts_length; omega⟩
        let jv : Fin P.vertices.length := ⟨i.val, by have h := P.vertices_length; omega⟩
        let jv' : Fin P.vertices.length := ⟨i.val + 1, by have h := P.vertices_length; omega⟩
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
        have hgetV : (P.vertices ++ [v]).get ⟨i.val, by simp [List.length_append, P.vertices_length]; omega⟩ = P.vertices.get jv := by
          simp only [List.get_eq_getElem]
          exact List.getElem_append_left hltV
        have hgetV' : (P.vertices ++ [v]).get ⟨i.val + 1, by simp [List.length_append, P.vertices_length]; omega⟩ = P.vertices.get jv' := by
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



/-- Prepend a directed dart to a simple path when its tail has not already -/
private def prependSimplePathStep
    (M : DirectedMapWithMissing D) {s y t : MapVertex M} {n : ℕ}
    (d : D) (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = s) (hhy : dartHeadVertex M d = y)
    (P : SimpleDirectedDartPath M y t n) (hs : s ∉ P.vertices) :
    SimpleDirectedDartPath M s t (n + 1) := by
  refine {
    darts := d :: P.darts
    vertices := s :: P.vertices
    darts_length := by simp [P.darts_length]
    vertices_length := by simp [P.vertices_length]
    vertices_nodup := by simp [List.nodup_cons, hs, P.vertices_nodup]
    start_vertex := by simp
    end_vertex := by simpa [List.get_eq_getElem] using P.end_vertex
    edge_step := by
      intro i
      have hi : i.val ≤ n := by
        have h := i.isLt
        simp only [List.length_cons, P.darts_length] at h
        omega
      by_cases hi0 : i.val = 0
      · have hifin : i = ⟨0, by simp [List.length_cons, P.darts_length]⟩ := Fin.ext hi0
        subst i
        have hstart : P.vertices.get ⟨0, by simp [P.vertices_length]⟩ = y := P.start_vertex
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [List.get_eq_getElem] using hmiss
        · simpa [List.get_eq_getElem] using htail
        · simpa [List.get_eq_getElem] using hty.symm
        · simpa [List.get_eq_getElem] using hstart.trans hhy.symm
      · have hpos : 0 < i.val := by omega
        have hdlen := P.darts_length
        have hvlen := P.vertices_length
        let j : Fin P.darts.length := ⟨i.val - 1, by omega⟩
        let jv : Fin P.vertices.length := ⟨i.val - 1, by omega⟩
        let jv' : Fin P.vertices.length := ⟨i.val, by omega⟩
        have hidx : i.val = j.val + 1 := by dsimp [j]; omega
        have hsP := P.edge_step j
        have hgetD : (d :: P.darts).get i = P.darts.get j := by
          simp only [List.get_eq_getElem]
          simp [hidx]
        have hgetV : (s :: P.vertices).get ⟨i.val, by simp [List.length_cons, P.vertices_length]; omega⟩ = P.vertices.get jv := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv]
        have hgetV' : (s :: P.vertices).get ⟨i.val + 1, by simp [List.length_cons, P.vertices_length]; omega⟩ = P.vertices.get jv' := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv']
        rw [hgetD, hgetV, hgetV']
        simpa [jv, jv', hidx] using hsP
  }


/-- Every vertex reaches the unique sink by a simple directed path -/
theorem exists_simple_sink_pathBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ∃ n : ℕ, ∃ _P : SimpleDirectedDartPath B.map v B.sink n, True := by
  let R : MapVertex B.map → MapVertex B.map → Prop :=
    fun a b => Relation.TransGen (fun x y => B.map.directedStep y x) a b
  have hwf : WellFounded R := by
    have htrans : IsTrans (MapVertex B.map) R :=
      ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
    have hirrefl : ∀ a : MapVertex B.map, ¬ R a a := by
      intro a h
      exact B.acyclic a (Relation.transGen_swap.mp h)
    letI : IsTrans (MapVertex B.map) R := htrans
    letI : Std.Irrefl R := ⟨hirrefl⟩
    letI : IsStrictOrder (MapVertex B.map) R := ⟨⟩
    exact Set.wellFoundedOn_univ.mp (Set.finite_univ.wellFoundedOn (r := R))
  letI : WellFounded R := hwf
  refine WellFounded.fix' R (motive := fun v =>
    ∃ n : ℕ, ∃ _P : SimpleDirectedDartPath B.map v B.sink n, True) ?_ v
  intro v ih
  by_cases hout : ∃ w, B.map.directedStep v w
  · obtain ⟨w, hstepWitness⟩ := hout
    obtain ⟨d, hmiss, htail, htailV, hheadV⟩ := hstepWitness
    have hstep : B.map.directedStep v w := ⟨d, hmiss, htail, htailV, hheadV⟩
    have hrecStep : (fun x y => B.map.directedStep y x) w v := hstep
    obtain ⟨n, P, _⟩ := ih w (Relation.TransGen.single hrecStep)
    have hnot : v ∉ P.vertices := by
      intro hv
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      have hreach : Relation.ReflTransGen B.map.directedStep w v := by
        rw [← hi]
        exact path_start_reaches_vertex B.map P i
      have hcycle : Relation.TransGen B.map.directedStep w w :=
        Relation.TransGen.tail' hreach hstep
      exact B.acyclic w hcycle
    exact ⟨n + 1,
      prependSimplePathStep B.map d hmiss htail htailV hheadV P hnot, trivial⟩
  · have hvsink : v = B.sink := B.sink_unique v hout
    subst v
    let P : SimpleDirectedDartPath B.map B.sink B.sink 0 := {
      darts := []
      vertices := [B.sink]
      darts_length := by simp
      vertices_length := by simp
      vertices_nodup := by simp
      start_vertex := by simp
      end_vertex := by simp
      edge_step := by intro i; exact Fin.elim0 i
    }
    exact ⟨0, P, trivial⟩

/-- Acyclicity on a finite vertex type makes the positive reachability
relation well founded (`lem-lr-ind`, -/
private theorem directedReach_wellFounded
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    WellFounded (Relation.TransGen B.map.directedStep) := by
  let R := Relation.TransGen B.map.directedStep
  letI : IsTrans (MapVertex B.map) R :=
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
  letI : Std.Irrefl R := ⟨B.acyclic⟩
  letI : IsStrictOrder (MapVertex B.map) R := ⟨⟩
  exact Set.wellFoundedOn_univ.mp (Set.finite_univ.wellFoundedOn (r := R))

/-- Every vertex is reachable from the unique source by a simple directed -/
theorem exists_simple_source_pathBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ∃ n : ℕ, ∃ _P : SimpleDirectedDartPath B.map B.source v n, True := by
  let R := Relation.TransGen B.map.directedStep
  have hwf : WellFounded R := directedReach_wellFounded B
  letI : WellFounded R := hwf
  refine WellFounded.fix' R (motive := fun v =>
    ∃ n : ℕ, ∃ _P : SimpleDirectedDartPath B.map B.source v n, True) ?_ v
  intro v ih
  by_cases hpred : ∃ u, B.map.directedStep u v
  · obtain ⟨u, hu⟩ := hpred
    obtain ⟨d, hmiss, htail, htailV, hheadV⟩ := hu
    have hstep : B.map.directedStep u v := ⟨d, hmiss, htail, htailV, hheadV⟩
    obtain ⟨n, P, _⟩ := ih u (Relation.TransGen.single hstep)
    have hnot : v ∉ P.vertices := by
      intro hv
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      have hreach : Relation.ReflTransGen B.map.directedStep v u := by
        rw [← hi]
        exact path_vertex_reaches_end B.map P i
      have hcycle : Relation.TransGen B.map.directedStep v v := Relation.TransGen.tail' hreach hstep
      exact B.acyclic v hcycle
    exact ⟨n + 1,
      appendSimplePathStep B.map P d hmiss htail htailV hheadV hnot, trivial⟩
  · have hvsrc : v = B.source := B.source_unique v hpred
    subst v
    let P : SimpleDirectedDartPath B.map B.source B.source 0 := {
      darts := []
      vertices := [B.source]
      darts_length := by simp
      vertices_length := by simp
      vertices_nodup := by simp
      start_vertex := by simp
      end_vertex := by simp
      edge_step := by intro i; exact Fin.elim0 i
    }
    exact ⟨0, P, trivial⟩

/-- The source-to-vertex simple path length set is nonempty on every vertex -/
theorem sourceVertexPathLengthsBase_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    (sourceVertexPathLengthsBase B v).Nonempty := by
  obtain ⟨n, P, _⟩ := exists_simple_source_pathBase B v
  exact ⟨n, (mem_sourceVertexPathLengthsBase B v n).2 ⟨P, trivial⟩⟩

/-- The vertex-to-sink simple path length set is nonempty on every vertex -/
theorem vertexSinkPathLengthsBase_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    (vertexSinkPathLengthsBase B v).Nonempty := by
  obtain ⟨n, P, _⟩ := exists_simple_sink_pathBase B v
  exact ⟨n, (mem_vertexSinkPathLengthsBase B v n).2 ⟨P, trivial⟩⟩


/-- The finite natural-valued LDP distance from the source, defined using the
nonempty path family (`lem-lr-ind`, -/
@[expose] noncomputable def ldpSourceDistanceNatBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) : ℕ :=
  (sourceVertexPathLengthsBase B v).max' (sourceVertexPathLengthsBase_nonempty B v)

/-- The finite natural-valued SDP distance from the source (`lem-lr-ind`, -/
@[expose] noncomputable def sdpSourceDistanceNatBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) : ℕ :=
  (sourceVertexPathLengthsBase B v).min' (sourceVertexPathLengthsBase_nonempty B v)

/-- The finite natural-valued LDP distance to the sink (`lem-lr-ind`, -/
@[expose] noncomputable def ldpSinkDistanceNatBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) : ℕ :=
  (vertexSinkPathLengthsBase B v).max' (vertexSinkPathLengthsBase_nonempty B v)

/-- The finite natural-valued SDP distance to the sink (`lem-lr-ind`, -/
@[expose] noncomputable def sdpSinkDistanceNatBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) : ℕ :=
  (vertexSinkPathLengthsBase B v).min' (vertexSinkPathLengthsBase_nonempty B v) -- placeholder


/-- The extended LDP source distance is the coercion of its finite natural -/
theorem ldpSourceDistanceBase_eq_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ldpSourceDistanceBase B v = (ldpSourceDistanceNatBase B v : WithBot ℕ) := by
  unfold ldpSourceDistanceBase ldpSourceDistanceNatBase
  exact (Finset.coe_max' (sourceVertexPathLengthsBase_nonempty B v)).symm

/-- The extended SDP source distance is the coercion of its finite natural -/
theorem sdpSourceDistanceBase_eq_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    sdpSourceDistanceBase B v = (sdpSourceDistanceNatBase B v : WithTop ℕ) := by
  unfold sdpSourceDistanceBase sdpSourceDistanceNatBase
  exact (Finset.coe_min' (sourceVertexPathLengthsBase_nonempty B v)).symm

/-- The extended LDP sink distance is the coercion of its finite natural -/
theorem ldpSinkDistanceBase_eq_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ldpSinkDistanceBase B v = (ldpSinkDistanceNatBase B v : WithBot ℕ) := by
  unfold ldpSinkDistanceBase ldpSinkDistanceNatBase
  exact (Finset.coe_max' (vertexSinkPathLengthsBase_nonempty B v)).symm

/-- The extended SDP sink distance is the coercion of its finite natural -/
theorem sdpSinkDistanceBase_eq_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    sdpSinkDistanceBase B v = (sdpSinkDistanceNatBase B v : WithTop ℕ) := by
  unfold sdpSinkDistanceBase sdpSinkDistanceNatBase
  exact (Finset.coe_min' (vertexSinkPathLengthsBase_nonempty B v)).symm

theorem ldpSourceDistanceBase_ne_bot
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ldpSourceDistanceBase B v ≠ ⊥ := by rw [ldpSourceDistanceBase_eq_coe]; simp

theorem sdpSourceDistanceBase_ne_top
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    sdpSourceDistanceBase B v ≠ ⊤ := by rw [sdpSourceDistanceBase_eq_coe]; simp

theorem ldpSinkDistanceBase_ne_bot
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ldpSinkDistanceBase B v ≠ ⊥ := by rw [ldpSinkDistanceBase_eq_coe]; simp

theorem sdpSinkDistanceBase_ne_top
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    sdpSinkDistanceBase B v ≠ ⊤ := by rw [sdpSinkDistanceBase_eq_coe]; simp


/-- Along a present directed dart, the longest source distance strictly
increases by at least one (`lem-lr-ind`, -/
theorem ldpSourceDistanceNatBase_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (htail : B.map.tail d) :
    ldpSourceDistanceNatBase B (dartTailVertex B.map d) + 1 ≤
      ldpSourceDistanceNatBase B (dartHeadVertex B.map d) := by
  let u := dartTailVertex B.map d
  let v := dartHeadVertex B.map d
  let S := sourceVertexPathLengthsBase B u
  let n := ldpSourceDistanceNatBase B u
  have hstep : B.map.directedStep u v := ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
  have hnmem : n ∈ S := by
    dsimp [S, n, ldpSourceDistanceNatBase]
    exact Finset.max'_mem _ _
  obtain ⟨P, _⟩ := (mem_sourceVertexPathLengthsBase B u n).1 hnmem
  have hnot : v ∉ P.vertices := by
    intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    have hreach : Relation.ReflTransGen B.map.directedStep v u := by
      rw [← hi]
      exact path_vertex_reaches_end B.map P i
    exact B.acyclic v (Relation.TransGen.tail' hreach hstep)
  have hpath := appendSimplePathStep B.map P d (B.noMissingDarts d) htail rfl rfl hnot
  have hmem : n + 1 ∈ sourceVertexPathLengthsBase B v :=
    (mem_sourceVertexPathLengthsBase B v (n + 1)).2 ⟨hpath, trivial⟩
  have hbound := (sourceVertexPathLengthsBase B v).le_max' (n + 1) hmem
  simpa [u, v, n, ldpSourceDistanceNatBase] using hbound

/-- Along a present directed dart, the shortest source distance increases -/
theorem sdpSourceDistanceNatBase_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (htail : B.map.tail d) :
    sdpSourceDistanceNatBase B (dartHeadVertex B.map d) ≤
      sdpSourceDistanceNatBase B (dartTailVertex B.map d) + 1 := by
  let u := dartTailVertex B.map d
  let v := dartHeadVertex B.map d
  let S := sourceVertexPathLengthsBase B u
  let n := sdpSourceDistanceNatBase B u
  have hstep : B.map.directedStep u v := ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
  have hnmem : n ∈ S := by
    dsimp [S, n, sdpSourceDistanceNatBase]
    exact Finset.min'_mem _ _
  obtain ⟨P, _⟩ := (mem_sourceVertexPathLengthsBase B u n).1 hnmem
  have hnot : v ∉ P.vertices := by
    intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    have hreach : Relation.ReflTransGen B.map.directedStep v u := by
      rw [← hi]
      exact path_vertex_reaches_end B.map P i
    exact B.acyclic v (Relation.TransGen.tail' hreach hstep)
  have hpath := appendSimplePathStep B.map P d (B.noMissingDarts d) htail rfl rfl hnot
  have hmem : n + 1 ∈ sourceVertexPathLengthsBase B v :=
    (mem_sourceVertexPathLengthsBase B v (n + 1)).2 ⟨hpath, trivial⟩
  have hbound := (sourceVertexPathLengthsBase B v).min'_le (n + 1) hmem
  simpa [u, v, n, sdpSourceDistanceNatBase] using hbound

/-- Along a present directed dart, the longest sink distance decreases by at -/
theorem ldpSinkDistanceNatBase_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (htail : B.map.tail d) :
    ldpSinkDistanceNatBase B (dartHeadVertex B.map d) + 1 ≤
      ldpSinkDistanceNatBase B (dartTailVertex B.map d) := by
  let u := dartTailVertex B.map d
  let v := dartHeadVertex B.map d
  let S := vertexSinkPathLengthsBase B v
  let n := ldpSinkDistanceNatBase B v
  have hstep : B.map.directedStep u v := ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
  have hnmem : n ∈ S := by
    dsimp [S, n, ldpSinkDistanceNatBase]
    exact Finset.max'_mem _ _
  obtain ⟨P, _⟩ := (mem_vertexSinkPathLengthsBase B v n).1 hnmem
  have hnot : u ∉ P.vertices := by
    intro hu
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    have hreach : Relation.ReflTransGen B.map.directedStep v u := by
      rw [← hi]
      exact path_start_reaches_vertex B.map P i
    exact B.acyclic v (Relation.TransGen.tail' hreach hstep)
  have hpath := prependSimplePathStep B.map d (B.noMissingDarts d) htail rfl rfl P hnot
  have hmem : n + 1 ∈ vertexSinkPathLengthsBase B u :=
    (mem_vertexSinkPathLengthsBase B u (n + 1)).2 ⟨hpath, trivial⟩
  have hbound := (vertexSinkPathLengthsBase B u).le_max' (n + 1) hmem
  simpa [u, v, n, ldpSinkDistanceNatBase] using hbound

/-- Along a present directed dart, the shortest sink distance decreases by at -/
theorem sdpSinkDistanceNatBase_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (htail : B.map.tail d) :
    sdpSinkDistanceNatBase B (dartTailVertex B.map d) ≤
      sdpSinkDistanceNatBase B (dartHeadVertex B.map d) + 1 := by
  let u := dartTailVertex B.map d
  let v := dartHeadVertex B.map d
  let S := vertexSinkPathLengthsBase B v
  let n := sdpSinkDistanceNatBase B v
  have hstep : B.map.directedStep u v := ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
  have hnmem : n ∈ S := by
    dsimp [S, n, sdpSinkDistanceNatBase]
    exact Finset.min'_mem _ _
  obtain ⟨P, _⟩ := (mem_vertexSinkPathLengthsBase B v n).1 hnmem
  have hnot : u ∉ P.vertices := by
    intro hu
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    have hreach : Relation.ReflTransGen B.map.directedStep v u := by
      rw [← hi]
      exact path_start_reaches_vertex B.map P i
    exact B.acyclic v (Relation.TransGen.tail' hreach hstep)
  have hpath := prependSimplePathStep B.map d (B.noMissingDarts d) htail rfl rfl P hnot
  have hmem : n + 1 ∈ vertexSinkPathLengthsBase B u :=
    (mem_vertexSinkPathLengthsBase B u (n + 1)).2 ⟨hpath, trivial⟩
  have hbound := (vertexSinkPathLengthsBase B u).min'_le (n + 1) hmem
  simpa [u, v, n, sdpSinkDistanceNatBase] using hbound

end DirectedDistances.PlanarMap
