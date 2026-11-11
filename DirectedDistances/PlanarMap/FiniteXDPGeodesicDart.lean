/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPGeodesicSplit

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem SimpleDirectedDartPath.reaches
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) :
    Relation.ReflTransGen M.directedStep s t := by
  induction n generalizing s t with
  | zero =>
      have hst : s = t := P.start_vertex.symm.trans P.end_vertex
      subst t
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      let iD : Fin P.darts.length := ⟨0, by rw [P.darts_length]; omega⟩
      let iV0 : Fin P.vertices.length := ⟨0, by rw [P.vertices_length]; omega⟩
      let iV1 : Fin P.vertices.length := ⟨1, by rw [P.vertices_length]; omega⟩
      let iN : Fin (n + 1 + 1) := ⟨1, by omega⟩
      have hstep := P.edge_step iD
      have hstepRel : M.directedStep s (P.vertices.get iV1) := by
        change ∃ e, ¬ M.missing e ∧ M.tail e ∧
          dartTailVertex M e = s ∧ dartHeadVertex M e = P.vertices.get iV1
        refine ⟨P.darts.get iD, hstep.1, hstep.2.1, ?_, ?_⟩
        · exact hstep.2.2.1.symm.trans P.start_vertex
        · exact hstep.2.2.2.symm
      have htail : SimpleDirectedDartPath M (P.vertices.get iV1) t n := by
        simpa [iV1, iN] using P.suffix iN
      exact (ih htail).head hstepRel

private theorem exists_simplePath_concatDart
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x y t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = x) (hhy : dartHeadVertex M d = y)
    (Q : SimpleDirectedDartPath M y t m) :
    ∃ R : SimpleDirectedDartPath M s t (n + 1 + m), d ∈ R.darts := by
  have hcross : ∀ a ∈ P.vertices, a ∉ Q.vertices := by
    intro a haP haQ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp haP
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp haQ
    let iN : Fin (n + 1) := ⟨i.val, by have hi := i.isLt; have hl := P.vertices_length; omega⟩
    let jN : Fin (m + 1) := ⟨j.val, by have hj := j.isLt; have hl := Q.vertices_length; omega⟩
    have hPi : P.vertices.get i = P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩ := by
      exact congrArg P.vertices.get (Fin.ext rfl)
    have hQj : Q.vertices.get j = Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩ := by
      exact congrArg Q.vertices.get (Fin.ext rfl)
    have hreachP : Relation.ReflTransGen M.directedStep
        (P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩) x :=
      (P.suffix iN).reaches M
    have hreachQ : Relation.ReflTransGen M.directedStep y
        (Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩) :=
      (Q.prefix jN).reaches M
    have hsame : P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩ =
        Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩ := by
      rw [← hPi, ← hQj]
      exact hi.trans hj.symm
    have hreachP' : Relation.ReflTransGen M.directedStep
        (Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩) x := by
      rw [← hsame]
      exact hreachP
    have hback : Relation.ReflTransGen M.directedStep y x := hreachQ.trans hreachP'
    have hstep : M.directedStep x y := ⟨d, hmiss, htail, hty, hhy⟩
    exact hacyclic x (Relation.TransGen.head' hstep hback)
  refine ⟨{
    darts := P.darts ++ (d :: Q.darts)
    vertices := P.vertices ++ Q.vertices
    darts_length := by
      simp only [List.length_append, List.length_cons, P.darts_length, Q.darts_length]
      ac_rfl
    vertices_length := by
      simp only [List.length_append, P.vertices_length, Q.vertices_length]
      ac_rfl
    vertices_nodup := by
      rw [List.nodup_append]
      exact ⟨P.vertices_nodup, Q.vertices_nodup, by
        intro a ha b hb hab
        exact hcross a ha (hab ▸ hb)⟩
    start_vertex := by
      simp [List.get_eq_getElem, P.vertices_length]
      exact P.start_vertex
    end_vertex := by
      simp [List.get_eq_getElem, P.vertices_length]
      exact Q.end_vertex
    edge_step := by
      intro i
      have hiBound : i.val < n + 1 + m := by
        have hi := i.isLt
        simp only [List.length_append, List.length_cons, P.darts_length, Q.darts_length] at hi
        omega
      by_cases hin : i.val < n
      · let jD : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hin⟩
        let jV0 : Fin P.vertices.length := ⟨i.val, by rw [P.vertices_length]; omega⟩
        let jV1 : Fin P.vertices.length := ⟨i.val + 1, by rw [P.vertices_length]; omega⟩
        have hD : (P.darts ++ d :: Q.darts).get i = P.darts.get jD := by
          change (P.darts ++ d :: Q.darts)[i.val]'i.isLt = P.darts[i.val]'jD.isLt
          exact List.getElem_append_left (by rw [P.darts_length]; exact hin)
        have hV0 : (P.vertices ++ Q.vertices).get ⟨i.val, by
            simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
            P.vertices.get jV0 := by
          change (P.vertices ++ Q.vertices)[i.val]'_ = P.vertices[i.val]'jV0.isLt
          exact List.getElem_append_left (by rw [P.vertices_length]; omega)
        have hV1 : (P.vertices ++ Q.vertices).get ⟨i.val + 1, by
            simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
            P.vertices.get jV1 := by
          change (P.vertices ++ Q.vertices)[i.val + 1]'_ = P.vertices[i.val + 1]'jV1.isLt
          exact List.getElem_append_left (by rw [P.vertices_length]; omega)
        rw [hD, hV0, hV1]
        exact P.edge_step jD
      · by_cases hieq : i.val = n
        · have hiFin : i = ⟨n, by
              simp [List.length_append, List.length_cons, P.darts_length, Q.darts_length]⟩ := Fin.ext hieq
          subst i
          have hD : (P.darts ++ d :: Q.darts).get ⟨n, by
              simp [List.length_append, List.length_cons, P.darts_length, Q.darts_length]⟩ = d := by
            simp [List.get_eq_getElem, P.darts_length]
          have hV0 : (P.vertices ++ Q.vertices).get ⟨n, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]
              omega⟩ = dartTailVertex M d := by
            calc
              (P.vertices ++ Q.vertices).get ⟨n, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]
                  omega⟩ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
                    change (P.vertices ++ Q.vertices)[n]'_ = P.vertices[n]'_
                    exact List.getElem_append_left (by rw [P.vertices_length]; omega)
              _ = x := P.end_vertex
              _ = dartTailVertex M d := hty.symm
          have hV1 : (P.vertices ++ Q.vertices).get ⟨n + 1, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]⟩ = dartHeadVertex M d := by
            calc
              (P.vertices ++ Q.vertices).get ⟨n + 1, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]⟩ = Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ := by
                    change (P.vertices ++ Q.vertices)[n + 1]'_ = Q.vertices[0]'_
                    calc
                      (P.vertices ++ Q.vertices)[n + 1]'_ = Q.vertices[n + 1 - P.vertices.length]'_ :=
                        List.getElem_append_right (by have hl := P.vertices_length; omega)
                      _ = Q.vertices[0]'_ := by
                        have hidx : n + 1 - P.vertices.length = 0 := by
                          have hl := P.vertices_length
                          omega
                        simp only [hidx]
              _ = y := Q.start_vertex
              _ = dartHeadVertex M d := hhy.symm
          exact ⟨by rw [hD]; exact hmiss, by rw [hD]; exact htail,
            by rw [hD, hV0], by rw [hD, hV1]⟩
        · have hgt : n < i.val := by omega
          let k : ℕ := i.val - (n + 1)
          have hk : k < m := by dsimp [k]; omega
          let jD : Fin Q.darts.length := ⟨k, by rw [Q.darts_length]; exact hk⟩
          let jV0 : Fin Q.vertices.length := ⟨k, by rw [Q.vertices_length]; omega⟩
          let jV1 : Fin Q.vertices.length := ⟨k + 1, by rw [Q.vertices_length]; omega⟩
          have hD : (P.darts ++ d :: Q.darts).get i = Q.darts.get jD := by
            change (P.darts ++ d :: Q.darts)[i.val]'i.isLt = Q.darts[k]'jD.isLt
            rw [List.getElem_append_right (by rw [P.darts_length]; omega)]
            have hidx : i.val - P.darts.length = k + 1 := by
              have hlen := P.darts_length
              dsimp [k]
              omega
            simp only [hidx, List.getElem_cons_succ]
          have hV0 : (P.vertices ++ Q.vertices).get ⟨i.val, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
              Q.vertices.get jV0 := by
            change (P.vertices ++ Q.vertices)[i.val]'_ = Q.vertices[k]'jV0.isLt
            rw [List.getElem_append_right (by rw [P.vertices_length]; omega)]
            have hidx : i.val - P.vertices.length = k := by
              have hlen := P.vertices_length
              dsimp [k]
              omega
            simp only [hidx]
          have hV1 : (P.vertices ++ Q.vertices).get ⟨i.val + 1, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
              Q.vertices.get jV1 := by
            change (P.vertices ++ Q.vertices)[i.val + 1]'_ = Q.vertices[k + 1]'jV1.isLt
            rw [List.getElem_append_right (by rw [P.vertices_length]; omega)]
            have hidx : i.val + 1 - P.vertices.length = k + 1 := by
              have hlen := P.vertices_length
              dsimp [k]
              omega
            simp only [hidx]
          rw [hD, hV0, hV1]
          exact Q.edge_step jD
  }, by simp [List.mem_append]⟩

/-- A present dart is on an LDP geodesic exactly when the longest source
distance to its tail, plus the dart and the longest continuation from its
head, has the LDP length (`lem-geo-infty-ind`, -/
theorem isXDPGeodesicDart_ldp_iff_distanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    IsXDPGeodesicDart B .ldp d ↔
      B.map.tail d ∧
        ldpSourceDistanceNatBase B (dartTailVertex B.map d) + 1 +
          ldpSinkDistanceNatBase B (dartHeadVertex B.map d) = ldpLengthBase B := by
  constructor
  · rintro ⟨n, P, hP, hd⟩
    change IsLDPGeodesicBase B P at hP
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    have hstep := P.edge_step i
    rw [hi] at hstep
    have hi_lt : i.val < n := by
      have hlen := P.darts_length
      omega
    let iN : Fin (n + 1) := ⟨i.val, by omega⟩
    let jN : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have htailV : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
        dartTailVertex B.map d := by simpa using hstep.2.2.1
    have hheadV : P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩ =
        dartHeadVertex B.map d := by simpa using hstep.2.2.2
    have hdist := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP iN
    have hdistHead := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP jN
    have htailDist : ldpSourceDistanceNatBase B (dartTailVertex B.map d) = i.val := by
      calc
        ldpSourceDistanceNatBase B (dartTailVertex B.map d) =
            ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩) :=
          congrArg (ldpSourceDistanceNatBase B) htailV.symm
        _ = i.val := by simpa [iN] using hdist.1
    have hheadDist : ldpSinkDistanceNatBase B (dartHeadVertex B.map d) = n - (i.val + 1) := by
      calc
        ldpSinkDistanceNatBase B (dartHeadVertex B.map d) =
            ldpSinkDistanceNatBase B (P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩) :=
          congrArg (ldpSinkDistanceNatBase B) hheadV.symm
        _ = n - (i.val + 1) := by simpa [jN] using hdistHead.2
    have hlen : n = ldpLengthBase B :=
      (isLDPGeodesicBase_iff_length_eq B P).mp hP
    refine ⟨hstep.2.1, ?_⟩
    rw [htailDist, hheadDist]
    omega
  · rintro ⟨htail, hsum⟩
    let n := ldpSourceDistanceNatBase B (dartTailVertex B.map d)
    let m := ldpSinkDistanceNatBase B (dartHeadVertex B.map d)
    have hsrcmem : n ∈ sourceVertexPathLengthsBase B (dartTailVertex B.map d) := by
      dsimp [n, ldpSourceDistanceNatBase]
      exact Finset.max'_mem _ _
    have hsnk_mem : m ∈ vertexSinkPathLengthsBase B (dartHeadVertex B.map d) := by
      dsimp [m, ldpSinkDistanceNatBase]
      exact Finset.max'_mem _ _
    obtain ⟨P₁, _⟩ := (mem_sourceVertexPathLengthsBase B (dartTailVertex B.map d) n).mp hsrcmem
    obtain ⟨P₂, _⟩ := (mem_vertexSinkPathLengthsBase B (dartHeadVertex B.map d) m).mp hsnk_mem
    obtain ⟨P, hdmem⟩ := exists_simplePath_concatDart B.map B.acyclic P₁ d
      (B.noMissingDarts d) htail rfl rfl P₂
    have hlen : n + 1 + m = ldpLengthBase B := by
      simpa [n, m] using hsum
    have hgeo : IsLDPGeodesicBase B P := by
      apply (isLDPGeodesicBase_iff_length_eq B P).mpr
      exact hlen
    exact ⟨n + 1 + m, P, hgeo, hdmem⟩

/-- A present dart is on an SDP geodesic exactly when the shortest source
distance to its tail, plus the dart and the shortest continuation from its
head, has the SDP length (`lem-geo-infty-ind`, -/
theorem isXDPGeodesicDart_sdp_iff_distanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    IsXDPGeodesicDart B .sdp d ↔
      B.map.tail d ∧
        sdpSourceDistanceNatBase B (dartTailVertex B.map d) + 1 +
          sdpSinkDistanceNatBase B (dartHeadVertex B.map d) = sdpLengthBase B := by
  constructor
  · rintro ⟨n, P, hP, hd⟩
    change IsSDPGeodesicBase B P at hP
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    have hstep := P.edge_step i
    rw [hi] at hstep
    have hi_lt : i.val < n := by
      have hlen := P.darts_length
      omega
    let iN : Fin (n + 1) := ⟨i.val, by omega⟩
    let jN : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have htailV : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
        dartTailVertex B.map d := by simpa using hstep.2.2.1
    have hheadV : P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩ =
        dartHeadVertex B.map d := by simpa using hstep.2.2.2
    have hdist := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP iN
    have hdistHead := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP jN
    have htailDist : sdpSourceDistanceNatBase B (dartTailVertex B.map d) = i.val := by
      calc
        sdpSourceDistanceNatBase B (dartTailVertex B.map d) =
            sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩) :=
          congrArg (sdpSourceDistanceNatBase B) htailV.symm
        _ = i.val := by simpa [iN] using hdist.1
    have hheadDist : sdpSinkDistanceNatBase B (dartHeadVertex B.map d) = n - (i.val + 1) := by
      calc
        sdpSinkDistanceNatBase B (dartHeadVertex B.map d) =
            sdpSinkDistanceNatBase B (P.vertices.get ⟨i.val + 1, by rw [P.vertices_length]; omega⟩) :=
          congrArg (sdpSinkDistanceNatBase B) hheadV.symm
        _ = n - (i.val + 1) := by simpa [jN] using hdistHead.2
    have hlen : n = sdpLengthBase B :=
      (isSDPGeodesicBase_iff_length_eq B P).mp hP
    refine ⟨hstep.2.1, ?_⟩
    rw [htailDist, hheadDist]
    omega
  · rintro ⟨htail, hsum⟩
    let n := sdpSourceDistanceNatBase B (dartTailVertex B.map d)
    let m := sdpSinkDistanceNatBase B (dartHeadVertex B.map d)
    have hsrcmem : n ∈ sourceVertexPathLengthsBase B (dartTailVertex B.map d) := by
      dsimp [n, sdpSourceDistanceNatBase]
      exact Finset.min'_mem _ _
    have hsnk_mem : m ∈ vertexSinkPathLengthsBase B (dartHeadVertex B.map d) := by
      dsimp [m, sdpSinkDistanceNatBase]
      exact Finset.min'_mem _ _
    obtain ⟨P₁, _⟩ := (mem_sourceVertexPathLengthsBase B (dartTailVertex B.map d) n).mp hsrcmem
    obtain ⟨P₂, _⟩ := (mem_vertexSinkPathLengthsBase B (dartHeadVertex B.map d) m).mp hsnk_mem
    obtain ⟨P, hdmem⟩ := exists_simplePath_concatDart B.map B.acyclic P₁ d
      (B.noMissingDarts d) htail rfl rfl P₂
    have hlen : n + 1 + m = sdpLengthBase B := by
      simpa [n, m] using hsum
    have hgeo : IsSDPGeodesicBase B P := by
      apply (isSDPGeodesicBase_iff_length_eq B P).mpr
      exact hlen
    exact ⟨n + 1 + m, P, hgeo, hdmem⟩

end DirectedDistances.PlanarMap
