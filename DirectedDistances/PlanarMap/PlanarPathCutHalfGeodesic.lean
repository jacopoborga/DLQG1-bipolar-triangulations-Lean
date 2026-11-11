/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfPathProject

/-! # Geodesic lengths in the path-cut halves

paper result. A base geodesic bounds the lengths of paths in either cut half. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- The length of every left-half source-to-sink path is bounded by the base
LDP or SDP length witnessed by `P`. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_sourceSinkPath_length_bound
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (x : XDP) (hP : IsXDPGeodesicBase B x P) {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k) :
    match x with
    | .ldp => k ≤ n
    | .sdp => n ≤ k := by
  have Q' := pathCutLeftHalf_projectPath B P Q
  have Qbase : SimpleDirectedDartPath B.map B.source B.sink k := by
    simpa only [pathCutLeftHalfSource_map, pathCutLeftHalfSink_map] using Q'
  cases x with
  | ldp => exact hP Qbase
  | sdp => exact hP Qbase

/-- The length of every right-half source-to-sink path is bounded by the base
LDP or SDP length witnessed by `P`. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_sourceSinkPath_length_bound
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (x : XDP) (hP : IsXDPGeodesicBase B x P) {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) :
    match x with
    | .ldp => k ≤ n
    | .sdp => n ≤ k := by
  have Q' := pathCutRightHalf_projectPath B P Q
  have Qbase : SimpleDirectedDartPath B.map B.source B.sink k := by
    simpa only [pathCutRightHalfSource_map, pathCutRightHalfSink_map] using Q'
  cases x with
  | ldp => exact hP Qbase
  | sdp => exact hP Qbase

/-- The lifted left cut path realizes the LDP or SDP extremal length among
left-half source-to-sink paths. Helper toward `lem-lr-ind` -/
theorem cutPathHalf_isXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (x : XDP) (hP : IsXDPGeodesicBase B x P) :
    match x with
    | .ldp => ∀ {k : ℕ},
        (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
          (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k) →
            k ≤ (cutPathHalf B P).darts.length
    | .sdp => ∀ {k : ℕ},
        (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
          (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k) →
            (cutPathHalf B P).darts.length ≤ k := by
  cases x with
  | ldp =>
      intro k Q
      rw [(cutPathHalf B P).darts_length]
      exact pathCutLeftHalf_sourceSinkPath_length_bound B P .ldp hP Q
  | sdp =>
      intro k Q
      rw [(cutPathHalf B P).darts_length]
      exact pathCutLeftHalf_sourceSinkPath_length_bound B P .sdp hP Q

/-- The lifted right cut path realizes the LDP or SDP extremal length among
right-half source-to-sink paths. Helper toward `lem-lr-ind` -/
theorem cutPathRightHalf_isXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (x : XDP) (hP : IsXDPGeodesicBase B x P) :
    match x with
    | .ldp => ∀ {k : ℕ},
        (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
          (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) →
            k ≤ (cutPathRightHalf B P).darts.length
    | .sdp => ∀ {k : ℕ},
        (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
          (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) →
            (cutPathRightHalf B P).darts.length ≤ k := by
  cases x with
  | ldp =>
      intro k Q
      rw [(cutPathRightHalf B P).darts_length]
      exact pathCutRightHalf_sourceSinkPath_length_bound B P .ldp hP Q
  | sdp =>
      intro k Q
      rw [(cutPathRightHalf B P).darts_length]
      exact pathCutRightHalf_sourceSinkPath_length_bound B P .sdp hP Q

private theorem pathCut_dart_eq_of_tail_eq_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : Fin n) {d : D} (hd : d ∈ P.darts)
    (htail : dartTailVertex B.map d = P.vertices.get
      ⟨i.val, by rw [P.vertices_length]; omega⟩) :
    d = P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
  have hjlt : j.val < n := by simpa [P.darts_length] using j.isLt
  have hstep := P.edge_step j
  have hvertices : P.vertices.get
      ⟨j.val, by rw [P.vertices_length]; omega⟩ = P.vertices.get
      ⟨i.val, by rw [P.vertices_length]; omega⟩ := by
    calc
      P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex B.map (P.darts.get j) := hstep.2.2.1
      _ = dartTailVertex B.map d := congrArg (dartTailVertex B.map) hj
      _ = P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := htail
  have hidx := P.vertices_nodup.get_inj_iff.mp hvertices
  have hval : j.val = i.val := congrArg Fin.val hidx
  calc
    d = P.darts.get j := hj.symm
    _ = P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ := by
      congr 1
      exact Fin.ext hval

private theorem pathCut_darts_eq_of_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P Q : SimpleDirectedDartPath B.map B.source B.sink n)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ P.darts) : Q.darts = P.darts := by
  have hvertices : ∀ j : ℕ, ∀ hj : j ≤ n,
      Q.vertices.get ⟨j, by rw [Q.vertices_length]; omega⟩ =
        P.vertices.get ⟨j, by rw [P.vertices_length]; omega⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        calc
          Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ = B.source := Q.start_vertex
          _ = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := P.start_vertex.symm
    | succ j ih =>
        intro hj
        have hjlt : j < n := by omega
        have hprev := ih (by omega)
        let iQ : Fin Q.darts.length := ⟨j, by rw [Q.darts_length]; exact hjlt⟩
        let iP : Fin n := ⟨j, hjlt⟩
        have hstepQ := Q.edge_step iQ
        have htail : dartTailVertex B.map (Q.darts.get iQ) = P.vertices.get
            ⟨j, by rw [P.vertices_length]; omega⟩ := by
          calc
            dartTailVertex B.map (Q.darts.get iQ) = Q.vertices.get
                ⟨j, by rw [Q.vertices_length]; omega⟩ := hstepQ.2.2.1.symm
            _ = P.vertices.get ⟨j, by rw [P.vertices_length]; omega⟩ := hprev
        have hdart := pathCut_dart_eq_of_tail_eq_vertex B P iP
          (hmem _ (List.get_mem _ _)) htail
        have hstepP := P.edge_step ⟨j, by rw [P.darts_length]; exact hjlt⟩
        calc
          Q.vertices.get ⟨j + 1, by rw [Q.vertices_length]; omega⟩ =
              dartHeadVertex B.map (Q.darts.get iQ) := hstepQ.2.2.2
          _ = dartHeadVertex B.map
              (P.darts.get ⟨j, by rw [P.darts_length]; exact hjlt⟩) :=
                congrArg (dartHeadVertex B.map) hdart
          _ = P.vertices.get ⟨j + 1, by rw [P.vertices_length]; omega⟩ :=
                hstepP.2.2.2.symm
  apply List.ext_get
  · rw [Q.darts_length, P.darts_length]
  · intro i hiQ hiP
    have hi : i < n := by simpa [Q.darts_length] using hiQ
    let iQ : Fin Q.darts.length := ⟨i, hiQ⟩
    let iP : Fin n := ⟨i, hi⟩
    have hvi := hvertices i (by omega)
    have htail : dartTailVertex B.map (Q.darts.get iQ) = P.vertices.get
        ⟨i, by rw [P.vertices_length]; omega⟩ := by
      calc
        dartTailVertex B.map (Q.darts.get iQ) = Q.vertices.get
            ⟨i, by rw [Q.vertices_length]; omega⟩ := (Q.edge_step iQ).2.2.1.symm
        _ = P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ := hvi
    exact pathCut_dart_eq_of_tail_eq_vertex B P iP
      (hmem _ (List.get_mem _ _)) htail

private theorem pathCut_pathDarts_mpr_source
    {M : DirectedMapWithMissing D} {s s' t : MapVertex M} {k : ℕ}
    (h : s = s') (Q : SimpleDirectedDartPath M s' t k) :
    (Eq.mpr (congrArg (fun z => SimpleDirectedDartPath M z t k) h) Q).darts =
      Q.darts := by
  cases h
  rfl

private theorem pathCut_pathDarts_mpr_sink
    {M : DirectedMapWithMissing D} {s t t' : MapVertex M} {k : ℕ}
    (h : t = t') (Q : SimpleDirectedDartPath M s t' k) :
    (Eq.mpr (congrArg (fun z => SimpleDirectedDartPath M s z k) h) Q).darts =
      Q.darts := by
  cases h
  rfl

/-- Conditional on the named no-strict-left hypothesis, every left-half
source-to-sink path of the same geodesic length has the same dart list as `P`.
paper result. -/
theorem pathCutLeftHalf_geodesic_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (x : XDP) (hP : IsXDPGeodesicBase B x P)
    (hno : ∀ {m} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesicBase B x Q → ∀ d ∈ Q.darts,
        d ∉ pathCutLeftDarts B P \ pathCutSeamDarts B P)
    (Q' : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) n) :
    Q'.darts.unattach = P.darts := by
  have hsource := pathCutLeftHalfSource_map B P
  have hsink := pathCutLeftHalfSink_map B P
  let Qproj := pathCutLeftHalf_projectPath B P Q'
  let Qsource : SimpleDirectedDartPath B.map B.source
      (pathCutLeftHalfVertexMap B P (pathCutLeftHalfSink B P)) n :=
    Eq.mpr (congrArg (fun z => SimpleDirectedDartPath B.map z
      (pathCutLeftHalfVertexMap B P (pathCutLeftHalfSink B P)) n)
      hsource.symm) Qproj
  let Qbase : SimpleDirectedDartPath B.map B.source B.sink n :=
    Eq.mpr (congrArg (fun z => SimpleDirectedDartPath B.map B.source z n)
      hsink.symm) Qsource
  have hQbaseDarts : Qbase.darts = Q'.darts.map Subtype.val := by
    calc
      Qbase.darts = Qsource.darts := pathCut_pathDarts_mpr_sink hsink.symm Qsource
      _ = Qproj.darts := pathCut_pathDarts_mpr_source hsource.symm Qproj
      _ = Q'.darts.map Subtype.val := pathCutLeftHalf_projectPath_darts B P Q'
  have hQgeo : IsXDPGeodesicBase B x Qbase := by
    cases x with
    | ldp =>
        apply (isLDPGeodesicBase_iff_length_eq B Qbase).2
        exact (isLDPGeodesicBase_iff_length_eq B P).1 hP
    | sdp =>
        apply (isSDPGeodesicBase_iff_length_eq B Qbase).2
        exact (isSDPGeodesicBase_iff_length_eq B P).1 hP
  have hseam : ∀ d, d ∈ Qbase.darts → d ∈ pathCutSeamDarts B P := by
    intro d hd
    have hdproj : d ∈ Q'.darts.map Subtype.val := by
      rw [← hQbaseDarts]
      exact hd
    obtain ⟨e, he, hval⟩ := List.mem_map.mp hdproj
    subst d
    have hebase : e.val ∈ Qbase.darts := by
      rw [hQbaseDarts]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hhalf : e.val ∈ pathCutLeftHalfDarts B P := e.property
    change e.val ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P at hhalf
    rcases hhalf with hleft | hseam
    · by_cases hseam : e.val ∈ pathCutSeamDarts B P
      · exact hseam
      · have hnot := hno Qbase hQgeo e.val hebase
        exact (hnot ⟨hleft, hseam⟩).elim
    · exact hseam
  have hmem : ∀ d, d ∈ Qbase.darts → d ∈ P.darts := by
    intro d hd
    rcases hseam d hd with hforward | hreverse
    · exact hforward
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
      have htailQ : B.map.tail d := by
        have hstep := Qbase.edge_step i
        rw [hi] at hstep
        exact hstep.2.1
      have hnotTail := (B.map.tail_iff d (B.noMissingDarts d)).mp htailQ
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hreverse
      have htailInv : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
        rw [← hj]
        exact (P.edge_step j).2.1
      exact (hnotTail htailInv).elim
  have hdarts := pathCut_darts_eq_of_mem B P Qbase hmem
  calc
    Q'.darts.unattach = Qproj.darts := by
      rw [pathCutLeftHalf_projectPath_darts]
      rfl
    _ = Qbase.darts := by
      rw [pathCutLeftHalf_projectPath_darts]
      exact hQbaseDarts.symm
    _ = P.darts := hdarts

end DirectedDistances.PlanarMap
