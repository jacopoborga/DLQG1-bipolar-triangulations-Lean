/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseLeftEndpoint
public import DirectedDistances.PlanarMap.KMSWMapIsoClass

/-! # Endpoint carrier helper for the KMSW left-boundary argument

result; does not assume Lemma 3.18 or simple-boundary restriction.

This file supports the procedure reading of the KMSW increments. The author
rulings legal-step convention (printed step `(1,0)` versus the procedure's `(0,1)`) and the S7 -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The vertices of a length-one right boundary path are its endpoints. -/
theorem rightPath_vertex_mem_endpoint
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    {v : MapVertex B.map} (hv : v ∈ B.rightPath.vertices) :
    v = B.source ∨ v = B.sink := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hi' : i.val = 0 ∨ i.val = 1 := by
    have hlt : i.val < 2 := by
      simpa [B.rightPath.vertices_length] using i.isLt
    omega
  rcases hi' with hi0 | hi1
  · have hei : i = ⟨0, by rw [B.rightPath.vertices_length]; omega⟩ := Fin.ext hi0
    rw [hei] at hi
    left
    simpa using hi.symm.trans B.rightPath.start_vertex
  · have hei : i = ⟨1, by rw [B.rightPath.vertices_length]; omega⟩ := Fin.ext hi1
    rw [hei] at hi
    right
    simpa [B.rightPath.vertices_length] using hi.symm.trans B.rightPath.end_vertex

/-- A left boundary path of length at least two cannot use the single edge
of the right boundary path. Simplicity of the left path supplies the
contradiction. Helper toward `lem-kmsw-left` -/
theorem left_right_path_edge_disjoint
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) :
    ∀ d, d ∈ B.leftPath.darts → ∀ e, e ∈ B.rightPath.darts →
      ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e := by
  intro d hd e he hcycle
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  have hj0 : j.val = 0 := by
    have : j.val < 1 := by simpa [B.rightPath.darts_length] using j.isLt
    omega
  have hjFin : j = ⟨0, by rw [B.rightPath.darts_length]; omega⟩ :=
    Fin.ext (by simpa using hj0)
  rw [hjFin] at hj
  rw [← hj] at hcycle
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv
    (B.leftPath.darts.get i)
    (B.rightPath.darts.get ⟨0, by rw [B.rightPath.darts_length]; omega⟩) at hcycle
  let e₀ := B.rightPath.darts.get
    ⟨0, by rw [B.rightPath.darts_length]; omega⟩
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv
    (B.leftPath.darts.get i) e₀ at hcycle
  have hR := B.rightPath.edge_step ⟨0, by rw [B.rightPath.darts_length]; omega⟩
  have hRtail : dartTailVertex B.map e₀ = B.source := by
    calc
      dartTailVertex B.map e₀ = B.rightPath.vertices.get
          ⟨0, by rw [B.rightPath.vertices_length]; omega⟩ := hR.2.2.1.symm
      _ = B.source := B.rightPath.start_vertex
  have hRhead : dartHeadVertex B.map e₀ = B.sink := by
    calc
      dartHeadVertex B.map e₀ = B.rightPath.vertices.get
          ⟨1, by rw [B.rightPath.vertices_length]; omega⟩ := hR.2.2.2.symm
      _ = B.sink := B.rightPath.end_vertex
  have hiD : i.val < ℓ := by simpa [B.leftPath.darts_length] using i.isLt
  let vi : Fin B.leftPath.vertices.length :=
    ⟨i.val, by rw [B.leftPath.vertices_length]; omega⟩
  let vnext : Fin B.leftPath.vertices.length :=
    ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩
  let vlast : Fin B.leftPath.vertices.length :=
    ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩
  let vzero : Fin B.leftPath.vertices.length :=
    ⟨0, by rw [B.leftPath.vertices_length]; omega⟩
  have hL := B.leftPath.edge_step i
  have htailL : B.leftPath.vertices.get vi = dartTailVertex B.map
      (B.leftPath.darts.get i) := by simpa [vi] using hL.2.2.1
  have hheadL : B.leftPath.vertices.get vnext = dartHeadVertex B.map
      (B.leftPath.darts.get i) := by simpa [vnext] using hL.2.2.2
  have hlast : B.leftPath.vertices.get vlast = B.sink := by
    simpa [vlast, B.leftPath.vertices_length] using B.leftPath.end_vertex
  have hzero : B.leftPath.vertices.get vzero = B.source := by
    simpa [vzero] using B.leftPath.start_vertex
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap
      (B.leftPath.darts.get i) e₀).mp hcycle with hsame | hrev
  · have htail : B.leftPath.vertices.get vi = B.source := by
      calc
        _ = dartTailVertex B.map (B.leftPath.darts.get i) := htailL
        _ = dartTailVertex B.map e₀ := congrArg (dartTailVertex B.map) hsame.symm
        _ = B.source := hRtail
    have hidx := B.leftPath.vertices_nodup.get_inj_iff.mp (htail.trans hzero.symm)
    have hi0 : i.val = 0 := congrArg Fin.val hidx
    have hhead : B.leftPath.vertices.get vnext = B.sink := by
      calc
        _ = dartHeadVertex B.map (B.leftPath.darts.get i) := hheadL
        _ = dartHeadVertex B.map e₀ := congrArg (dartHeadVertex B.map) hsame.symm
        _ = B.sink := hRhead
    have hidx' := B.leftPath.vertices_nodup.get_inj_iff.mp (hhead.trans hlast.symm)
    have hbad : i.val + 1 = ℓ := by
      have := congrArg Fin.val hidx'
      simpa [vnext, vlast] using this
    omega
  · have hrev' : B.leftPath.darts.get i = B.map.toCombinatorialMap.edgeInv e₀ := by
      simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        congrArg B.map.toCombinatorialMap.edgeInv hrev.symm
    have htail : B.leftPath.vertices.get vi = B.sink := by
      calc
        _ = dartTailVertex B.map (B.leftPath.darts.get i) := htailL
        _ = dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e₀) :=
          congrArg (dartTailVertex B.map) hrev'
        _ = dartHeadVertex B.map e₀ := rfl
        _ = B.sink := hRhead
    have hidx := B.leftPath.vertices_nodup.get_inj_iff.mp (htail.trans hlast.symm)
    have hbad : i.val = ℓ := by
      have := congrArg Fin.val hidx
      simpa [vi, vlast] using this
    omega

/-- The unique right-boundary dart is absent from the left path when
`ℓ ≥ 2`. Helper toward `lem-kmsw-left` -/
theorem rightEndpoint_dart_not_mem_leftPath
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) :
    ∀ e, e ∈ B.rightPath.darts → e ∉ B.leftPath.darts := by
  intro e he hmem
  exact (left_right_path_edge_disjoint B hℓ e hmem e he)
    (Equiv.Perm.SameCycle.rfl)

/-- The left and right paths meet only at their source and sink for this -/
theorem left_right_paths_meet_only_at_endpoints
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (_hℓ : 2 ≤ ℓ) :
    ∀ v, v ∈ B.leftPath.vertices → v ∈ B.rightPath.vertices →
      v = B.source ∨ v = B.sink := by
  intro v _ hvR
  exact rightPath_vertex_mem_endpoint B hvR

/-- For `ℓ ≥ 2`, a base representative with right boundary length one lies
on the restricted simple-boundary carrier: its right path has only the two
endpoints, and path simplicity excludes sharing its edge with the left path.
`def-reverse-map` (`:391–393`); not the paper result; does not assume Lemma
3.18 or simple-boundary restriction. -/
@[expose] def toStrongLeftEndpoint
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) :
    BipolarTriangulationWithBoundary D ℓ 1 :=
  B.toStrong
    (fun _v _hvL hvR => rightPath_vertex_mem_endpoint B hvR)
    (left_right_path_edge_disjoint B hℓ)

/-- The vertices on either boundary path of a general base representative -/
@[expose] def BipolarTriangulationWithBoundaryBase.boundaryVerticesBase
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Set (MapVertex B.map) := {v | v ∈ B.leftPath.vertices ∨ v ∈ B.rightPath.vertices}

/-- The boundary edges of a general base representative, with edge identity
retained through the involution orbit (`def-reverse-map`, -/
@[expose] def BipolarTriangulationWithBoundaryBase.boundaryEdgeBase
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) : Prop :=
  ∃ e ∈ B.leftPath.darts ++ B.rightPath.darts,
    Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e

/-- Boundary channeling on a general base representative: every incoming
edge at a boundary vertex other than the sink belongs to one of the boundary
paths. This is the no-incoming-nonboundary-edge form of
`lem-kmsw-left`, not the paper result; does not assume Lemma 3.18 or simple-boundary restriction. -/
@[expose] def BipolarTriangulationWithBoundaryBase.IsBoundaryChanneledBase
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Prop :=
  ∀ d, ¬ B.map.missing d → B.map.tail d →
    dartHeadVertex B.map d ∈ B.boundaryVerticesBase →
    dartHeadVertex B.map d ≠ B.sink → B.boundaryEdgeBase d

/-- The base and restricted-carrier formulations of boundary channeling
coincide under the endpoint carrier construction. Helper toward -/
theorem isBoundaryChanneledBase_iff_toStrongLeftEndpoint
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (_hℓ : 2 ≤ ℓ) :
    B.IsBoundaryChanneledBase ↔
      (toStrongLeftEndpoint B _hℓ).IsBoundaryChanneled := Iff.rfl

/-- Turn a boundary-channeled general `(ℓ,1)` representative, for `ℓ ≥ 2`,
into the restricted carrier accepted by the endpoint reversal equivalence.
`def-reverse-map` (`:391–393`); not the paper result; does not assume Lemma
3.18 or simple-boundary restriction. -/
@[expose] def toBoundaryMbcClassLeftEndpoint
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ)
    (hbc : B.IsBoundaryChanneledBase) : BoundaryMbcClass D ℓ 1 :=
  ⟨toStrongLeftEndpoint B hℓ,
    (isBoundaryChanneledBase_iff_toStrongLeftEndpoint B hℓ).mp hbc⟩

namespace BipolarBoundaryBaseIso

variable {D' : Type*} [Fintype D'] [DecidableEq D']
variable {ℓ r : ℕ}
variable {B : BipolarTriangulationWithBoundaryBase D ℓ r}
variable {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}

omit [DecidableEq D] [Fintype D'] [DecidableEq D'] in
private theorem sameCycle_map_leftEndpoint (e : D ≃ D') (f : Equiv.Perm D)
    (f' : Equiv.Perm D') (hcomm : ∀ x, e (f x) = f' (e x))
    {x y : D} (hxy : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle f' (e x) (e y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have hpow : ∀ (n : ℕ) (x : D), e ((f ^ n) x) = (f' ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (f x)).trans (congrArg (f' ^ n) (hcomm x))
  calc
    (f' ^ n) (e x) = e ((f ^ n) x) := (hpow n x).symm
    _ = e y := congrArg e hn

/-- Transport a simple directed boundary path across a base isomorphism.
Helper toward channeling invariance for `def-reverse-map` -/
@[expose] noncomputable def transportPath (I : BipolarBoundaryBaseIso B B')
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    SimpleDirectedDartPath B'.map B'.source B'.sink n where
  darts := P.darts.map I.toEquiv
  vertices := P.vertices.map I.vertexEquiv
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map I.vertexEquiv.injective
  start_vertex := by
    simpa using (congrArg I.vertexEquiv P.start_vertex).trans I.vertexEquiv_source
  end_vertex := by
    simpa using (congrArg I.vertexEquiv P.end_vertex).trans I.vertexEquiv_sink
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by rw [P.vertices_length]; omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by rw [P.vertices_length]; omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        _ = I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) := congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) := I.vertexEquiv_dartTailVertex _
    · calc
        _ = I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) := congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) := I.vertexEquiv_dartHeadVertex _

/-- The transported path has the pointwise image of the original dart list. -/
theorem transportPath_darts (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (I.transportPath P).darts = P.darts.map I.toEquiv := rfl

private theorem transportPath_eq_left (I : BipolarBoundaryBaseIso B B') :
    I.transportPath B.leftPath = B'.leftPath := by
  apply SimpleDirectedDartPath.eq_of_darts_eq
  rw [transportPath_darts, I.leftDarts]

private theorem transportPath_eq_right (I : BipolarBoundaryBaseIso B B') :
    I.transportPath B.rightPath = B'.rightPath := by
  apply SimpleDirectedDartPath.eq_of_darts_eq
  rw [transportPath_darts, I.rightDarts]

/-- A base isomorphism preserves membership in the left boundary vertex -/
theorem mem_leftPath_vertices_iff (I : BipolarBoundaryBaseIso B B')
    {v : MapVertex B.map} :
    v ∈ B.leftPath.vertices ↔ I.vertexEquiv v ∈ B'.leftPath.vertices := by
  constructor
  · intro hv
    have hm : I.vertexEquiv v ∈ (I.transportPath B.leftPath).vertices := by
      simp only [transportPath, List.mem_map]
      exact ⟨v, hv, rfl⟩
    simpa only [transportPath_eq_left] using hm
  · intro hv
    have hm : I.vertexEquiv v ∈ (I.transportPath B.leftPath).vertices := by
      simpa only [transportPath_eq_left] using hv
    simp only [transportPath, List.mem_map] at hm
    rcases hm with ⟨w, hw, hweq⟩
    have : w = v := I.vertexEquiv.injective hweq
    simpa [this] using hw

/-- A base isomorphism preserves membership in the right boundary vertex -/
theorem mem_rightPath_vertices_iff (I : BipolarBoundaryBaseIso B B')
    {v : MapVertex B.map} :
    v ∈ B.rightPath.vertices ↔ I.vertexEquiv v ∈ B'.rightPath.vertices := by
  constructor
  · intro hv
    have hm : I.vertexEquiv v ∈ (I.transportPath B.rightPath).vertices := by
      simp only [transportPath, List.mem_map]
      exact ⟨v, hv, rfl⟩
    simpa only [transportPath_eq_right] using hm
  · intro hv
    have hm : I.vertexEquiv v ∈ (I.transportPath B.rightPath).vertices := by
      simpa only [transportPath_eq_right] using hv
    simp only [transportPath, List.mem_map] at hm
    rcases hm with ⟨w, hw, hweq⟩
    have : w = v := I.vertexEquiv.injective hweq
    simpa [this] using hw

private theorem boundaryEdgeBase_map (I : BipolarBoundaryBaseIso B B') {d : D}
    (hd : B.boundaryEdgeBase d) : B'.boundaryEdgeBase (I.toEquiv d) := by
  rcases hd with ⟨e, he, hcycle⟩
  have he' : I.toEquiv e ∈ B'.leftPath.darts ++ B'.rightPath.darts := by
    rcases List.mem_append.mp he with hL | hR
    · have hm : I.toEquiv e ∈ (B.leftPath.darts.map I.toEquiv) :=
        List.mem_map.mpr ⟨e, hL, rfl⟩
      exact List.mem_append.mpr (Or.inl (by simpa [I.leftDarts] using hm))
    · have hm : I.toEquiv e ∈ (B.rightPath.darts.map I.toEquiv) :=
        List.mem_map.mpr ⟨e, hR, rfl⟩
      exact List.mem_append.mpr (Or.inr (by simpa [I.rightDarts] using hm))
  refine ⟨I.toEquiv e, he', ?_⟩
  exact sameCycle_map_leftEndpoint I.toEquiv B.map.toCombinatorialMap.edgeInv
    B'.map.toCombinatorialMap.edgeInv I.edgeInv_comm hcycle

/-- Boundary edge membership is invariant under base isomorphism. -/
theorem boundaryEdgeBase_iff (I : BipolarBoundaryBaseIso B B') (d : D) :
    B.boundaryEdgeBase d ↔ B'.boundaryEdgeBase (I.toEquiv d) := by
  constructor
  · exact boundaryEdgeBase_map I
  · intro h
    have hm := boundaryEdgeBase_map I.symm h
    change B.boundaryEdgeBase (I.toEquiv.symm (I.toEquiv d)) at hm
    simpa using hm

end BipolarBoundaryBaseIso

private theorem isBoundaryChanneledBase_map
    {D' : Type*} [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (h : B.IsBoundaryChanneledBase) : B'.IsBoundaryChanneledBase := by
    intro d' hmiss' htail' hbound' hdsink'
    let d := I.toEquiv.symm d'
    have hmiss : ¬ B.map.missing d := by
      intro hm
      apply hmiss'
      simpa [d] using (I.missing_iff d).mpr hm
    have htail : B.map.tail d := (I.tail_iff d).mp (by simpa [d] using htail')
    have hhead : I.vertexEquiv (dartHeadVertex B.map d) = dartHeadVertex B'.map d' := by
      simpa [d] using I.vertexEquiv_dartHeadVertex d
    have hbound : dartHeadVertex B.map d ∈ B.boundaryVerticesBase := by
      change dartHeadVertex B'.map d' ∈ B'.leftPath.vertices ∨
        dartHeadVertex B'.map d' ∈ B'.rightPath.vertices at hbound'
      rw [← hhead] at hbound'
      change dartHeadVertex B.map d ∈ B.leftPath.vertices ∨
        dartHeadVertex B.map d ∈ B.rightPath.vertices
      rcases hbound' with hleft | hright
      · exact Or.inl (I.mem_leftPath_vertices_iff.mpr hleft)
      · exact Or.inr (I.mem_rightPath_vertices_iff.mpr hright)
    have hnotSink : dartHeadVertex B.map d ≠ B.sink := by
      intro heq
      apply hdsink'
      calc
        dartHeadVertex B'.map d' = I.vertexEquiv (dartHeadVertex B.map d) := hhead.symm
        _ = I.vertexEquiv B.sink := congrArg I.vertexEquiv heq
        _ = B'.sink := I.vertexEquiv_sink
    have hbc := h d hmiss htail hbound hnotSink
    have hmap := (I.boundaryEdgeBase_iff d).mp hbc
    simpa [d] using hmap

/-- Boundary channeling on the general base carrier is invariant under a
boundary base isomorphism. Helper toward `def-reverse-map`
(`:415–440`); does not assume Lemma 3.18 or simple-boundary restriction. -/
theorem isBoundaryChanneledBase_iff_of_iso
    {D' : Type*} [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    B.IsBoundaryChanneledBase ↔ B'.IsBoundaryChanneledBase := by
  constructor
  · exact isBoundaryChanneledBase_map I
  · intro h
    exact isBoundaryChanneledBase_map I.symm h

namespace KMSWMapRep

variable {ℓ n : ℕ}

/-- Boundary channeling for the `(ℓ,1)` representatives in the KMSW
left-endpoint class, expressed on the full base carrier. It is invariant
under representative isomorphism; helper toward `lem-kmsw-left`
not the paper result; does not assume Lemma 3.18 or simple-boundary restriction. -/
@[expose] def IsBoundaryChanneled (R : KMSWMapRep ℓ 1 n) : Prop :=
  R.B.IsBoundaryChanneledBase

/-- Channeling is preserved by an isomorphism of KMSW representatives. -/
theorem isBoundaryChanneled_iff_of_iso
    (R R' : KMSWMapRep ℓ 1 n) (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.IsBoundaryChanneled ↔ R'.IsBoundaryChanneled :=
  isBoundaryChanneledBase_iff_of_iso I

end KMSWMapRep

namespace KMSWMapIsoClass

variable {ℓ n : ℕ}

/-- The boundary-channeled predicate descended to KMSW map isomorphism
classes with right boundary length one. Helper toward `lem-kmsw-left`
not the paper result; does not assume Lemma 3.18 or simple-boundary restriction. -/
@[expose] def IsBoundaryChanneled (q : KMSWMapIsoClass ℓ 1 n) : Prop :=
  Quotient.lift (fun R : KMSWMapRep ℓ 1 n => R.IsBoundaryChanneled)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact propext (KMSWMapRep.isBoundaryChanneled_iff_of_iso R R' I)) q

/-- The descended predicate agrees with the representative predicate. -/
@[simp] theorem isBoundaryChanneled_mk (R : KMSWMapRep ℓ 1 n) :
    IsBoundaryChanneled (KMSWMapIsoClass.mk R) ↔ R.IsBoundaryChanneled := Iff.rfl

end KMSWMapIsoClass

end DirectedDistances.PlanarMap
