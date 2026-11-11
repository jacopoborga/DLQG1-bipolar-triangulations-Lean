/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier

/-! # Incoming-edge characterization of boundary channeling

description of boundary channeling on the restricted carrier. A directed
edge is represented by its unique present tail dart; edge identity remains
the edge-involution orbit, so an orbit witness with the same orientation is
proved to be the same dart. Helper only, not the paper result; simple-boundary restriction is not
assumed.

boundary paths re-merge at an internal vertex using distinct predecessor
edges, that vertex has two incoming boundary edges. Internal vertex
disjointness on the restricted carrier rules out this obstruction. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem path_tail_mem
    (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : B.map.tail d := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  simpa [← hi] using (P.edge_step i).2.1

private theorem path_head_mem_vertices
    (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : dartHeadVertex B.map d ∈ P.vertices := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hs := P.edge_step i
  rw [← hi, ← hs.2.2.2]
  exact List.get_mem _ _

private theorem path_exists_incoming_dart
    (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) (hvs : v ≠ B.source) :
    ∃ d, d ∈ P.darts ∧ ¬ B.map.missing d ∧ B.map.tail d ∧
      dartHeadVertex B.map d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hiLt : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
  have hi0 : i.val ≠ 0 := by
    intro h
    have hifin : i = ⟨0, by rw [P.vertices_length]; omega⟩ := Fin.ext h
    apply hvs
    calc
      v = P.vertices.get i := hi.symm
      _ = B.source := by rw [hifin, P.start_vertex]
  let j : Fin P.darts.length := ⟨i.val - 1, by rw [P.darts_length]; omega⟩
  have hji : j.val + 1 = i.val := by dsimp [j]; omega
  have hs := P.edge_step j
  have hindex : (⟨j.val + 1, by rw [P.vertices_length]; omega⟩ :
      Fin P.vertices.length) = i := Fin.ext hji
  refine ⟨P.darts.get j, List.get_mem _ _, hs.1, hs.2.1, ?_⟩
  calc
    dartHeadVertex B.map (P.darts.get j) =
        P.vertices.get ⟨j.val + 1, by rw [P.vertices_length]; omega⟩ :=
      hs.2.2.2.symm
    _ = P.vertices.get i := congrArg P.vertices.get hindex
    _ = v := hi

private theorem path_incoming_dart_unique
    (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} {d e : D}
    (hd : d ∈ P.darts) (he : e ∈ P.darts)
    (hheadD : dartHeadVertex B.map d = v)
    (hheadE : dartHeadVertex B.map e = v) : d = e := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  have hsi := P.edge_step i
  have hsj := P.edge_step j
  have hiLt : i.val < n := by simpa [P.darts_length] using i.isLt
  have hjLt : j.val < n := by simpa [P.darts_length] using j.isLt
  let iNext : Fin P.vertices.length := ⟨i.val + 1, by
    rw [P.vertices_length]
    omega⟩
  let jNext : Fin P.vertices.length := ⟨j.val + 1, by
    rw [P.vertices_length]
    omega⟩
  have hnext : P.vertices.get iNext = P.vertices.get jNext := by
    calc
      P.vertices.get iNext = dartHeadVertex B.map (P.darts.get i) := by
        simpa [iNext] using hsi.2.2.2
      _ = dartHeadVertex B.map d := by rw [← hi]
      _ = dartHeadVertex B.map e := hheadD.trans hheadE.symm
      _ = dartHeadVertex B.map (P.darts.get j) := by rw [← hj]
      _ = P.vertices.get jNext := by simpa [jNext] using hsj.2.2.2.symm
  have hidx := P.vertices_nodup.get_inj_iff.mp hnext
  have hij : i = j := Fin.ext (by
    have hval := congrArg Fin.val hidx
    dsimp [iNext, jNext] at hval
    omega)
  calc
    d = P.darts.get i := hi.symm
    _ = P.darts.get j := by rw [hij]
    _ = e := hj

private theorem boundaryEdge_tail_eq_pathDart
    (B : BipolarTriangulationWithBoundary D ℓ r) {d : D}
    (hd : B.boundaryEdge d) (htail : B.map.tail d) :
    ∃ e ∈ B.leftPath.darts ++ B.rightPath.darts, d = e := by
  rcases hd with ⟨e, he, hcycle⟩
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      hcycle with hde | hrev
  · exact ⟨e, he, hde.symm⟩
  · have hnotInv : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) :=
      (B.map.tail_iff d (B.noMissingDarts d)).mp htail
    have htailE : B.map.tail e := by
      rcases List.mem_append.mp he with heL | heR
      · exact path_tail_mem B B.leftPath heL
      · exact path_tail_mem B B.rightPath heR
    exact False.elim (hnotInv (hrev ▸ htailE))

private theorem exists_boundary_path_incoming
    (B : BipolarTriangulationWithBoundary D ℓ r)
    {v : MapVertex B.map} (hv : v ∈ B.boundaryVertices)
    (hvs : v ≠ B.source) :
    ∃ d, ¬ B.map.missing d ∧ B.map.tail d ∧ dartHeadVertex B.map d = v ∧
      B.boundaryEdge d := by
  rcases hv with hvL | hvR
  · obtain ⟨d, hd, hmiss, htail, hhead⟩ :=
      path_exists_incoming_dart B B.leftPath hvL hvs
    exact ⟨d, hmiss, htail, hhead,
      ⟨d, List.mem_append_left _ hd, Equiv.Perm.SameCycle.rfl⟩⟩
  · obtain ⟨d, hd, hmiss, htail, hhead⟩ :=
      path_exists_incoming_dart B B.rightPath hvR hvs
    exact ⟨d, hmiss, htail, hhead,
      ⟨d, List.mem_append_right _ hd, Equiv.Perm.SameCycle.rfl⟩⟩

/-- that every boundary vertex other than source and sink has exactly one
incoming edge. The quantified object is a present tail dart with the given
head vertex; because every present edge has exactly one tail dart, these
objects correspond one-to-one with incoming oriented edges. This is the
equivalence on the restricted carrier; helper, not the paper result; simple-boundary restriction is
not assumed. -/
theorem isBoundaryChanneled_iff_exactlyOneIncoming
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    B.IsBoundaryChanneled ↔
      ∀ v, v ∈ B.boundaryVertices → v ≠ B.source → v ≠ B.sink →
        ∃! d, ¬ B.map.missing d ∧ B.map.tail d ∧
          dartHeadVertex B.map d = v := by
  constructor
  · intro hbc v hv hvs hvt
    rcases hv with hvL | hvR
    · obtain ⟨d₀, hd₀, hm₀, ht₀, hh₀⟩ :=
        path_exists_incoming_dart B B.leftPath hvL hvs
      refine ⟨d₀, ⟨hm₀, ht₀, hh₀⟩, ?_⟩
      intro d hd
      have hboundD : dartHeadVertex B.map d ∈ B.boundaryVertices := by
        rw [hd.2.2]
        exact Or.inl hvL
      have hnotSinkD : dartHeadVertex B.map d ≠ B.sink := by
        rw [hd.2.2]
        exact hvt
      have hbd : B.boundaryEdge d := hbc d hd.1 hd.2.1 hboundD hnotSinkD
      obtain ⟨e, he, hde⟩ := boundaryEdge_tail_eq_pathDart B hbd hd.2.1
      have hheadE : dartHeadVertex B.map e = v := by simpa [hde] using hd.2.2
      rcases List.mem_append.mp he with heL | heR
      · exact hde.trans (path_incoming_dart_unique B B.leftPath hd₀ heL hh₀ hheadE).symm
      · have hvR : v ∈ B.rightPath.vertices := by
          rw [← hheadE]
          exact path_head_mem_vertices B B.rightPath heR
        rcases B.paths_internally_vertex_disjoint v hvL hvR with hs | ht
        · exact (hvs hs).elim
        · exact (hvt ht).elim
    · obtain ⟨d₀, hd₀, hm₀, ht₀, hh₀⟩ :=
        path_exists_incoming_dart B B.rightPath hvR hvs
      refine ⟨d₀, ⟨hm₀, ht₀, hh₀⟩, ?_⟩
      intro d hd
      have hboundD : dartHeadVertex B.map d ∈ B.boundaryVertices := by
        rw [hd.2.2]
        exact Or.inr hvR
      have hnotSinkD : dartHeadVertex B.map d ≠ B.sink := by
        rw [hd.2.2]
        exact hvt
      have hbd : B.boundaryEdge d := hbc d hd.1 hd.2.1 hboundD hnotSinkD
      obtain ⟨e, he, hde⟩ := boundaryEdge_tail_eq_pathDart B hbd hd.2.1
      have hheadE : dartHeadVertex B.map e = v := by simpa [hde] using hd.2.2
      rcases List.mem_append.mp he with heL | heR
      · have hvL : v ∈ B.leftPath.vertices := by
          rw [← hheadE]
          exact path_head_mem_vertices B B.leftPath heL
        rcases B.paths_internally_vertex_disjoint v hvL hvR with hs | ht
        · exact (hvs hs).elim
        · exact (hvt ht).elim
      · exact hde.trans (path_incoming_dart_unique B B.rightPath hd₀ heR hh₀ hheadE).symm
  · intro hone d hmiss htail hbound hnotSink
    let v := dartHeadVertex B.map d
    have hv : v ∈ B.boundaryVertices := hbound
    have hvs : v ≠ B.source := by
      intro hsource
      have hstep : B.map.directedStep (dartTailVertex B.map d) B.source := by
        exact ⟨d, hmiss, htail, rfl, hsource⟩
      exact B.isSource ⟨dartTailVertex B.map d, hstep⟩
    have hvt : v ≠ B.sink := hnotSink
    rcases hv with hvL | hvR
    · obtain ⟨d₀, hd₀, hm₀, ht₀, hh₀⟩ :=
        path_exists_incoming_dart B B.leftPath hvL hvs
      obtain ⟨w, hw, huniq⟩ := hone v (Or.inl hvL) hvs hvt
      have hdEq : d = w := huniq d ⟨hmiss, htail, rfl⟩
      have hd₀Eq : d₀ = w := huniq d₀ ⟨hm₀, ht₀, hh₀⟩
      have heq : d = d₀ := hdEq.trans hd₀Eq.symm
      rw [heq]
      exact ⟨d₀, List.mem_append_left _ hd₀, Equiv.Perm.SameCycle.rfl⟩
    · obtain ⟨d₀, hd₀, hm₀, ht₀, hh₀⟩ :=
        path_exists_incoming_dart B B.rightPath hvR hvs
      obtain ⟨w, hw, huniq⟩ := hone v (Or.inr hvR) hvs hvt
      have hdEq : d = w := huniq d ⟨hmiss, htail, rfl⟩
      have hd₀Eq : d₀ = w := huniq d₀ ⟨hm₀, ht₀, hh₀⟩
      have heq : d = d₀ := hdEq.trans hd₀Eq.symm
      rw [heq]
      exact ⟨d₀, List.mem_append_right _ hd₀, Equiv.Perm.SameCycle.rfl⟩

end DirectedDistances.PlanarMap
