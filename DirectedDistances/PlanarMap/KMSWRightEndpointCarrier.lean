/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier

/-! # Endpoint carrier helper for the KMSW right-boundary argument

`(1,r)` side of the restricted endpoint reversal carrier, with boundary
channeling as in `def-reverse-map` (Definition 3.17,
paper result.

This file supports the procedure reading of the KMSW increments. The author
rulings legal-step convention and the S7 items (count, inverse direction, singleton case) remain -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Vertices of a length-one left boundary path are its source and sink.
`(1,r)` side of the restricted endpoint reversal carrier; simple-boundary restriction is not assumed
and this is not the paper result. -/
theorem leftPath_vertex_mem_endpoint
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r)
    {v : MapVertex B.map} (hv : v ∈ B.leftPath.vertices) :
    v = B.source ∨ v = B.sink := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hi' : i.val = 0 ∨ i.val = 1 := by
    have hlt : i.val < 2 := by
      simpa [B.leftPath.vertices_length] using i.isLt
    omega
  rcases hi' with hi0 | hi1
  · have hei : i = ⟨0, by rw [B.leftPath.vertices_length]; omega⟩ := Fin.ext hi0
    rw [hei] at hi
    left
    simpa using hi.symm.trans B.leftPath.start_vertex
  · have hei : i = ⟨1, by rw [B.leftPath.vertices_length]; omega⟩ := Fin.ext hi1
    rw [hei] at hi
    right
    simpa [B.leftPath.vertices_length] using hi.symm.trans B.leftPath.end_vertex

/-- The length-one left boundary dart is edge-disjoint from the right path
when `r ≥ 2`; simplicity of the right path rules out both orientations of a
the `(1,r)` side of the restricted endpoint reversal carrier; simple-boundary restriction is not
assumed and this is not the paper result. -/
theorem right_left_path_edge_disjoint
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (hr : 2 ≤ r) :
    ∀ d, d ∈ B.rightPath.darts → ∀ e, e ∈ B.leftPath.darts →
      ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e := by
  intro d hd e he hcycle
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  have hj0 : j.val = 0 := by
    have : j.val < 1 := by simpa [B.leftPath.darts_length] using j.isLt
    omega
  have hjFin : j = ⟨0, by rw [B.leftPath.darts_length]; omega⟩ :=
    Fin.ext (by simpa using hj0)
  rw [hjFin] at hj
  rw [← hj] at hcycle
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv
    (B.rightPath.darts.get i)
    (B.leftPath.darts.get ⟨0, by rw [B.leftPath.darts_length]; omega⟩) at hcycle
  let e₀ := B.leftPath.darts.get
    ⟨0, by rw [B.leftPath.darts_length]; omega⟩
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv
    (B.rightPath.darts.get i) e₀ at hcycle
  have hL := B.leftPath.edge_step ⟨0, by rw [B.leftPath.darts_length]; omega⟩
  have hLtail : dartTailVertex B.map e₀ = B.source := by
    calc
      dartTailVertex B.map e₀ = B.leftPath.vertices.get
          ⟨0, by rw [B.leftPath.vertices_length]; omega⟩ := hL.2.2.1.symm
      _ = B.source := B.leftPath.start_vertex
  have hLhead : dartHeadVertex B.map e₀ = B.sink := by
    calc
      dartHeadVertex B.map e₀ = B.leftPath.vertices.get
          ⟨1, by rw [B.leftPath.vertices_length]; omega⟩ := hL.2.2.2.symm
      _ = B.sink := B.leftPath.end_vertex
  have hiD : i.val < r := by simpa [B.rightPath.darts_length] using i.isLt
  let vi : Fin B.rightPath.vertices.length :=
    ⟨i.val, by rw [B.rightPath.vertices_length]; omega⟩
  let vnext : Fin B.rightPath.vertices.length :=
    ⟨i.val + 1, by rw [B.rightPath.vertices_length]; omega⟩
  let vlast : Fin B.rightPath.vertices.length :=
    ⟨r, by rw [B.rightPath.vertices_length]; omega⟩
  let vzero : Fin B.rightPath.vertices.length :=
    ⟨0, by rw [B.rightPath.vertices_length]; omega⟩
  have hR := B.rightPath.edge_step i
  have htailR : B.rightPath.vertices.get vi = dartTailVertex B.map
      (B.rightPath.darts.get i) := by simpa [vi] using hR.2.2.1
  have hheadR : B.rightPath.vertices.get vnext = dartHeadVertex B.map
      (B.rightPath.darts.get i) := by simpa [vnext] using hR.2.2.2
  have hlast : B.rightPath.vertices.get vlast = B.sink := by
    simpa [vlast, B.rightPath.vertices_length] using B.rightPath.end_vertex
  have hzero : B.rightPath.vertices.get vzero = B.source := by
    simpa [vzero] using B.rightPath.start_vertex
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap
      (B.rightPath.darts.get i) e₀).mp hcycle with hsame | hrev
  · have htail : B.rightPath.vertices.get vi = B.source := by
      calc
        _ = dartTailVertex B.map (B.rightPath.darts.get i) := htailR
        _ = dartTailVertex B.map e₀ := congrArg (dartTailVertex B.map) hsame.symm
        _ = B.source := hLtail
    have hidx := B.rightPath.vertices_nodup.get_inj_iff.mp (htail.trans hzero.symm)
    have hi0 : i.val = 0 := congrArg Fin.val hidx
    have hhead : B.rightPath.vertices.get vnext = B.sink := by
      calc
        _ = dartHeadVertex B.map (B.rightPath.darts.get i) := hheadR
        _ = dartHeadVertex B.map e₀ := congrArg (dartHeadVertex B.map) hsame.symm
        _ = B.sink := hLhead
    have hidx' := B.rightPath.vertices_nodup.get_inj_iff.mp (hhead.trans hlast.symm)
    have hbad : i.val + 1 = r := by
      have := congrArg Fin.val hidx'
      simpa [vnext, vlast] using this
    omega
  · have hrev' : B.rightPath.darts.get i = B.map.toCombinatorialMap.edgeInv e₀ := by
      simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        congrArg B.map.toCombinatorialMap.edgeInv hrev.symm
    have htail : B.rightPath.vertices.get vi = B.sink := by
      calc
        _ = dartTailVertex B.map (B.rightPath.darts.get i) := htailR
        _ = dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e₀) :=
          congrArg (dartTailVertex B.map) hrev'
        _ = dartHeadVertex B.map e₀ := rfl
        _ = B.sink := hLhead
    have hidx := B.rightPath.vertices_nodup.get_inj_iff.mp (htail.trans hlast.symm)
    have hbad : i.val = r := by
      have := congrArg Fin.val hidx
      simpa [vi, vlast] using this
    omega

/-- The single left-boundary dart is absent from the right path when `r ≥ 2`.
`(1,r)` side of the restricted endpoint reversal carrier; simple-boundary restriction is not assumed
and this is not the paper result. -/
theorem leftEndpoint_dart_not_mem_rightPath
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (hr : 2 ≤ r) :
    ∀ e, e ∈ B.leftPath.darts → e ∉ B.rightPath.darts := by
  intro e he hmem
  exact (right_left_path_edge_disjoint B hr e hmem e he)
    (Equiv.Perm.SameCycle.rfl)

/-- The left and right paths meet only at source and sink in this endpoint
the `(1,r)` side of the restricted endpoint reversal carrier; simple-boundary restriction is not
assumed and this is not the paper result. -/
theorem right_left_paths_meet_only_at_endpoints
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (_hr : 2 ≤ r) :
    ∀ v, v ∈ B.rightPath.vertices → v ∈ B.leftPath.vertices →
      v = B.source ∨ v = B.sink := by
  intro v _ hvL
  exact leftPath_vertex_mem_endpoint B hvL

/-- Place a base representative with left boundary length one and right
length at least two in the restricted simple-boundary carrier. Helper toward
restricted endpoint reversal carrier; simple-boundary restriction is not assumed and this is not
the paper result. -/
@[expose] def toStrongRightEndpoint
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (hr : 2 ≤ r) :
    BipolarTriangulationWithBoundary D 1 r :=
  B.toStrong
    (fun _v hvL _hvR => leftPath_vertex_mem_endpoint B hvL)
    (fun d hd e he =>
      fun hcycle => (right_left_path_edge_disjoint B hr e he d hd) hcycle.symm)

/-- Boundary channeling on the base carrier is exactly the restricted
boundary-channeling predicate after this endpoint carrier construction.
side of the restricted endpoint reversal carrier; simple-boundary restriction is not assumed and
this is not the paper result. -/
theorem isBoundaryChanneledBase_iff_toStrongRightEndpoint
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (_hr : 2 ≤ r) :
    B.IsBoundaryChanneledBase ↔
      (toStrongRightEndpoint B _hr).IsBoundaryChanneled := Iff.rfl

/-- Turn a boundary-channeled base representative of type `(1,r)`, `r ≥ 2`,
into the restricted carrier accepted by the endpoint reversal equivalence.
side of the restricted endpoint reversal carrier; simple-boundary restriction is not assumed and
this is not the paper result. -/
@[expose] def toBoundaryMbcClassRightEndpoint
    {r : ℕ} (B : BipolarTriangulationWithBoundaryBase D 1 r) (hr : 2 ≤ r)
    (hbc : B.IsBoundaryChanneledBase) : BoundaryMbcClass D 1 r :=
  ⟨toStrongRightEndpoint B hr,
    (isBoundaryChanneledBase_iff_toStrongRightEndpoint B hr).mp hbc⟩

/-- The restricted boundary-channeling predicate implies its general-base
form for any boundary lengths. Helper toward `lem-kmsw-left`
paper result. -/
theorem isBoundaryChanneledBase_of_strong
    {a b : ℕ} (B : BipolarTriangulationWithBoundary D a b) :
    B.IsBoundaryChanneled → B.toBase.IsBoundaryChanneledBase := by
  intro hbc
  change B.IsBoundaryChanneled
  exact hbc

end DirectedDistances.PlanarMap

