/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.MirrorMap
public import DirectedDistances.PlanarMap.FiniteXDPGeodesicDart

/-! # Finite directed path lengths under reflection

they are not the paper result and do not close simple-boundary restriction or Lemma 5.18. -/

public section
namespace DirectedDistances.PlanarMap

open DirectedMapWithMissing

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The vertex correspondence viewed as an equivalence. Helper toward
result. -/
@[expose] noncomputable def mirrorVertexEquiv (M : DirectedMapWithMissing D) :
    MapVertex M ≃ MapVertex M.mirror :=
  Equiv.ofBijective (mirrorVertexMap M) (mirrorVertexMap_bijective M)

/-- Inverse path transport for the reflection path equivalence. Helper toward
result. -/
@[expose] noncomputable def unmirrorSimpleDirectedDartPath (M : DirectedMapWithMissing D)
    {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M.mirror
      (mirrorVertexMap M s) (mirrorVertexMap M t) n) :
    SimpleDirectedDartPath M s t n := by
  let e := mirrorVertexEquiv M
  have hlen : (P.vertices.map e.symm).length = n + 1 := by
    simp [P.vertices_length]
  refine {
    darts := P.darts
    vertices := P.vertices.map e.symm
    darts_length := P.darts_length
    vertices_length := by simp [P.vertices_length]
    vertices_nodup := P.vertices_nodup.map (by
      intro a b hab
      exact e.symm.injective hab)
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_ }
  · calc
      (P.vertices.map e.symm).get ⟨0, by rw [hlen]; omega⟩ =
          e.symm (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) := by
        simp only [List.get_eq_getElem, List.getElem_map]
      _ = e.symm (mirrorVertexMap M s) := congrArg e.symm P.start_vertex
      _ = s := e.symm_apply_apply s
  · calc
      (P.vertices.map e.symm).get ⟨n, by rw [hlen]; omega⟩ =
          e.symm (P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩) := by
        simp only [List.get_eq_getElem, List.getElem_map]
      _ = e.symm (mirrorVertexMap M t) := congrArg e.symm P.end_vertex
      _ = t := e.symm_apply_apply t
  · intro i
    obtain ⟨hmiss, htail, htailV, hheadV⟩ := P.edge_step i
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [DirectedMapWithMissing.mirror] using hmiss
    · simpa [DirectedMapWithMissing.mirror] using htail
    · calc
        (P.vertices.map e.symm).get ⟨i.val, by
          rw [hlen]
          have hi : i.val < n := by simpa [P.darts_length] using i.isLt
          omega⟩ = e.symm (P.vertices.get ⟨i.val, by
            rw [P.vertices_length]
            have hi : i.val < n := by simpa [P.darts_length] using i.isLt
            omega⟩) := by
              simp only [List.get_eq_getElem, List.getElem_map]
        _ = e.symm (dartTailVertex M.mirror (P.darts.get i)) :=
          congrArg e.symm htailV
        _ = dartTailVertex M (P.darts.get i) := by
          have hmirror : e (dartTailVertex M (P.darts.get i)) =
              dartTailVertex M.mirror (P.darts.get i) := by
            change mirrorVertexMap M (dartTailVertex M (P.darts.get i)) = _
            rw [mirrorVertexMap_eq]
            exact mirror_dartTailVertex M (P.darts.get i)
          rw [← hmirror, e.symm_apply_apply]
    · calc
        (P.vertices.map e.symm).get ⟨i.val + 1, by
          rw [hlen]
          have hi : i.val < n := by simpa [P.darts_length] using i.isLt
          omega⟩ = e.symm (P.vertices.get ⟨i.val + 1, by
            rw [P.vertices_length]
            have hi : i.val < n := by simpa [P.darts_length] using i.isLt
            omega⟩) := by
              simp only [List.get_eq_getElem, List.getElem_map]
        _ = e.symm (dartHeadVertex M.mirror (P.darts.get i)) :=
          congrArg e.symm hheadV
        _ = dartHeadVertex M (P.darts.get i) := by
          have hmirror : e (dartHeadVertex M (P.darts.get i)) =
              dartHeadVertex M.mirror (P.darts.get i) := by
            change mirrorVertexMap M (dartHeadVertex M (P.darts.get i)) = _
            rw [mirrorVertexMap_eq]
            exact mirror_dartHeadVertex M (P.darts.get i)
          rw [← hmirror, e.symm_apply_apply]

/-- Reflection gives a length-preserving bijection between simple directed
dart paths with specified endpoints. The mirrored path retains the same
darts and has the same natural-number length. Helper toward `prop-uihbot-sym` -/
@[expose] noncomputable def SimpleDirectedDartPath.mirrorEquiv
    (M : DirectedMapWithMissing D) (s t : MapVertex M) (n : ℕ) :
    SimpleDirectedDartPath M s t n ≃
      SimpleDirectedDartPath M.mirror
        (mirrorVertexMap M s) (mirrorVertexMap M t) n where
  toFun := DirectedMapWithMissing.SimpleDirectedDartPath.mirror
  invFun := unmirrorSimpleDirectedDartPath M
  left_inv := by
    intro P
    cases P
    simp [unmirrorSimpleDirectedDartPath,
      DirectedMapWithMissing.SimpleDirectedDartPath.mirror,
      mirrorVertexEquiv, List.map_map, Function.comp_def]
  right_inv := by
    intro P
    cases P
    have hmap : ∀ L : List (MapVertex M.mirror),
        L.map (fun v => mirrorVertexMap M ((mirrorVertexEquiv M).symm v)) = L := by
      intro L
      induction L with
      | nil => rfl
      | cons v L ih =>
          simp only [List.map_cons]
          have hpoint : mirrorVertexMap M ((mirrorVertexEquiv M).symm v) = v := by
            change (mirrorVertexEquiv M) ((mirrorVertexEquiv M).symm v) = v
            exact (mirrorVertexEquiv M).apply_symm_apply v
          rw [hpoint, ih]
    simp [unmirrorSimpleDirectedDartPath,
      DirectedMapWithMissing.SimpleDirectedDartPath.mirror,
      mirrorVertexEquiv, List.map_map, Function.comp_def]
    all_goals exact hmap _

private theorem simplePath_length_lt_numVertices
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) :
    n < M.toCombinatorialMap.numVertices := by
  classical
  have hlen := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hlen
  have hcard : n + 1 ≤ M.toCombinatorialMap.numVertices := by
    simpa [CombinatorialMap.numVertices] using hlen
  omega

/-- The finite set of lengths of simple directed dart paths between two
vertices. Its empty case is retained, so the LDP maximum is `⊥` and the SDP
minimum is `⊤` when no such path exists. Helper toward `prop-uihbot-sym` -/
@[expose] noncomputable def simpleDirectedPathLengthSet
    (M : DirectedMapWithMissing D) (s t : MapVertex M) : Finset ℕ := by
  classical
  exact (Finset.range M.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath M s t n, True

/-- Membership in the finite path-length set is exactly existence of a path
of that length. Helper toward `prop-uihbot-sym` -/
theorem mem_simpleDirectedPathLengthSet
    (M : DirectedMapWithMissing D) (s t : MapVertex M) (n : ℕ) :
    n ∈ simpleDirectedPathLengthSet M s t ↔
      ∃ _P : SimpleDirectedDartPath M s t n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_numVertices M P), ⟨P, trivial⟩⟩

/-- Reflection preserves every finite simple directed path length, including
the empty-family case. Helper toward `prop-uihbot-sym` -/
theorem simpleDirectedPathLengthSet_mirror
    (M : DirectedMapWithMissing D) (s t : MapVertex M) :
    simpleDirectedPathLengthSet M.mirror
        (mirrorVertexMap M s) (mirrorVertexMap M t) =
      simpleDirectedPathLengthSet M s t := by
  classical
  apply Finset.ext
  intro n
  rw [mem_simpleDirectedPathLengthSet, mem_simpleDirectedPathLengthSet]
  constructor
  · rintro ⟨P, _⟩
    exact ⟨(SimpleDirectedDartPath.mirrorEquiv M s t n).symm P, trivial⟩
  · rintro ⟨P, _⟩
    exact ⟨(SimpleDirectedDartPath.mirrorEquiv M s t n) P, trivial⟩

/-- The finite LDP distance between vertices, with `⊥` for an unreachable
not the paper result. -/
@[expose] noncomputable def simpleDirectedPathLDPLength
    (M : DirectedMapWithMissing D) (s t : MapVertex M) : WithBot ℕ :=
  (simpleDirectedPathLengthSet M s t).max

/-- The finite SDP distance between vertices, with `⊤` for an unreachable
not the paper result. -/
@[expose] noncomputable def simpleDirectedPathSDPLength
    (M : DirectedMapWithMissing D) (s t : MapVertex M) : WithTop ℕ :=
  (simpleDirectedPathLengthSet M s t).min

/-- The LDP distance is unchanged by reflection, including its `⊥`
unreachable value. Helper toward `prop-uihbot-sym` -/
theorem simpleDirectedPathLDPLength_mirror
    (M : DirectedMapWithMissing D) (s t : MapVertex M) :
    simpleDirectedPathLDPLength M.mirror
        (mirrorVertexMap M s) (mirrorVertexMap M t) =
      simpleDirectedPathLDPLength M s t := by
  rw [simpleDirectedPathLDPLength, simpleDirectedPathLDPLength,
    simpleDirectedPathLengthSet_mirror]

/-- The SDP distance is unchanged by reflection, including its `⊤`
unreachable value. Helper toward `prop-uihbot-sym` -/
theorem simpleDirectedPathSDPLength_mirror
    (M : DirectedMapWithMissing D) (s t : MapVertex M) :
    simpleDirectedPathSDPLength M.mirror
        (mirrorVertexMap M s) (mirrorVertexMap M t) =
      simpleDirectedPathSDPLength M s t := by
  rw [simpleDirectedPathSDPLength, simpleDirectedPathSDPLength,
    simpleDirectedPathLengthSet_mirror]

/-- The source-to-sink LDP length of a finite bipolar base, viewed at the
explicit source and sink vertices of its mirrored directed map, is unchanged.
There is no general-base mirror carrier in the current API, so the target is
stated at that directed-map level. Helper toward `prop-uihbot-sym` -/
theorem ldpLengthBase_eq_mirrorEndpoints
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (ldpLengthBase B : WithBot ℕ) =
      simpleDirectedPathLDPLength B.map.mirror
        (mirrorVertexMap B.map B.source) (mirrorVertexMap B.map B.sink) := by
  rw [simpleDirectedPathLDPLength, simpleDirectedPathLengthSet_mirror]
  change (ldpLengthBase B : WithBot ℕ) =
    (sourceSinkPathLengthsBase B).max
  unfold ldpLengthBase
  exact Finset.coe_max' (sourceSinkPathLengthsBase_nonempty B)

/-- The source-to-sink SDP length of a finite bipolar base, viewed at the
explicit source and sink vertices of its mirrored directed map, is unchanged.
There is no general-base mirror carrier in the current API, so the target is
stated at that directed-map level. Helper toward `prop-uihbot-sym` -/
theorem sdpLengthBase_eq_mirrorEndpoints
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (sdpLengthBase B : WithTop ℕ) =
      simpleDirectedPathSDPLength B.map.mirror
        (mirrorVertexMap B.map B.source) (mirrorVertexMap B.map B.sink) := by
  rw [simpleDirectedPathSDPLength, simpleDirectedPathLengthSet_mirror]
  change (sdpLengthBase B : WithTop ℕ) =
    (sourceSinkPathLengthsBase B).min
  unfold sdpLengthBase
  exact Finset.coe_min' (sourceSinkPathLengthsBase_nonempty B)

end DirectedDistances.PlanarMap
