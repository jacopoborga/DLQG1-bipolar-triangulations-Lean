module

public import DirectedDistances.PlanarMap.MirrorMap
public import DirectedDistances.PlanarMap.KMSWMapSimpleBoundary
public import DirectedDistances.PlanarMap.KMSWLeftPartialInjective
public import DirectedDistances.PlanarMap.KMSWRightReversePartial
public import DirectedDistances.PlanarMap.DirectedMapMarkMissing

/-! Mirroring finite KMSW map representatives and classes. These are helpers only; -/

public section
namespace DirectedDistances.PlanarMap

variable {ℓ r N : ℕ}

private theorem mirror_vertex_eq_iff {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (d : D) (v : MapVertex M) :
    dartTailVertex M.mirror d = M.mirrorVertexMap v ↔ dartTailVertex M d = v := by
  rw [M.mirrorVertexMap_eq, ← M.mirror_dartTailVertex]
  exact (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap).injective.eq_iff

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswStrongMirrorBaseIso {D D' : Type*}
    [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    (B : BipolarTriangulationWithBoundary D ℓ r)
    (B' : BipolarTriangulationWithBoundary D' ℓ r)
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase) :
    BipolarBoundaryBaseIso B.mirror.toBase B'.mirror.toBase where
  toEquiv := I.toEquiv
  rot_comm := by
    intro d
    change I.toEquiv (B.map.rot.symm d) = B'.map.rot.symm (I.toEquiv d)
    apply B'.map.rot.injective
    have hc (e : D) : I.toEquiv (B.map.rot e) = B'.map.rot (I.toEquiv e) :=
      I.rot_comm e
    rw [← hc]
    simp only [Equiv.apply_symm_apply]
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  outer_iff := by
    intro d
    change B'.map.mirror.IsOuter (I.toEquiv d) ↔ B.map.mirror.IsOuter d
    rw [DirectedMapWithMissing.mirror_isOuter_iff,
      DirectedMapWithMissing.mirror_isOuter_iff]
    have hc : B'.map.edgeInv (I.toEquiv d) = I.toEquiv (B.map.edgeInv d) :=
      (I.edgeInv_comm d).symm
    rw [hc]
    exact I.outer_iff _
  source_map := by
    intro d
    change dartTailVertex B.map.mirror d = B.map.mirrorVertexMap B.source ↔
      dartTailVertex B'.map.mirror (I.toEquiv d) = B'.map.mirrorVertexMap B'.source
    rw [mirror_vertex_eq_iff, mirror_vertex_eq_iff]
    exact I.source_map d
  sink_map := by
    intro d
    change dartTailVertex B.map.mirror d = B.map.mirrorVertexMap B.sink ↔
      dartTailVertex B'.map.mirror (I.toEquiv d) = B'.map.mirrorVertexMap B'.sink
    rw [mirror_vertex_eq_iff, mirror_vertex_eq_iff]
    exact I.sink_map d
  leftDarts := I.rightDarts
  rightDarts := I.leftDarts

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswStrongMirrorMirrorBaseIso {D : Type*}
    [Fintype D] [DecidableEq D] (B : BipolarTriangulationWithBoundary D ℓ r) :
    BipolarBoundaryBaseIso B.mirror.mirror.toBase B.toBase where
  toEquiv := Equiv.refl D
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by intro d; rfl
  tail_iff := by intro d; rfl
  outer_iff := by
    intro d
    change B.map.IsOuter d ↔ B.map.mirror.mirror.IsOuter d
    rw [DirectedMapWithMissing.mirror_isOuter_iff,
      DirectedMapWithMissing.mirror_isOuter_iff]
    change B.map.IsOuter d ↔ B.map.IsOuter (B.map.edgeInv (B.map.edgeInv d))
    rw [B.map.edgeInv_invol]
  source_map := by
    intro d
    change dartTailVertex B.map.mirror.mirror d =
      B.map.mirror.mirrorVertexMap (B.map.mirrorVertexMap B.source) ↔
        dartTailVertex B.map d = B.source
    rw [mirror_vertex_eq_iff, mirror_vertex_eq_iff]
  sink_map := by
    intro d
    change dartTailVertex B.map.mirror.mirror d =
      B.map.mirror.mirrorVertexMap (B.map.mirrorVertexMap B.sink) ↔
        dartTailVertex B.map d = B.sink
    rw [mirror_vertex_eq_iff, mirror_vertex_eq_iff]
  leftDarts := by change List.map id _ = _; exact List.map_id _
  rightDarts := by change List.map id _ = _; exact List.map_id _

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswMirrorRep (R : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) : KMSWMapRep r ℓ N where
  dartCount := R.dartCount
  B := (R.toStrong h).mirror.toBase
  edges := (CombinatorialMap.numEdges_mirror _).trans R.edges

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
theorem kmswMirrorRep_isSimpleOuterBoundary (R : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) : (kmswMirrorRep R h).IsSimpleOuterBoundary :=
  ⟨(R.toStrong h).mirror.paths_internally_vertex_disjoint,
    (R.toStrong h).mirror.paths_edge_disjoint⟩

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswMirrorRep_baseIso (R R' : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) (h' : R'.IsSimpleOuterBoundary)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    BipolarBoundaryBaseIso (kmswMirrorRep R h).B (kmswMirrorRep R' h').B :=
  kmswStrongMirrorBaseIso (R.toStrong h) (R'.toStrong h') I

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswMirrorRep_mirror_baseIso (R : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) :
    BipolarBoundaryBaseIso
      (kmswMirrorRep (kmswMirrorRep R h) (kmswMirrorRep_isSimpleOuterBoundary R h)).B
      R.B := by
  change BipolarBoundaryBaseIso
    (((kmswMirrorRep R h).toStrong _).mirror.toBase) R.B
  have he : (kmswMirrorRep R h).toStrong
      (kmswMirrorRep_isSimpleOuterBoundary R h) = (R.toStrong h).mirror :=
    BipolarTriangulationWithBoundaryBase.toBase_toStrong _ _ _
  rw [he]
  exact kmswStrongMirrorMirrorBaseIso (R.toStrong h)

private theorem mirror_channeled (R : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    (kmswMirrorRep R h).IsChanneled :=
  BipolarTriangulationWithBoundary.mirror_isBoundaryChanneled hc

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
theorem kmswMirrorRep_isChanneled_iff (R : KMSWMapRep ℓ r N)
    (h : R.IsSimpleOuterBoundary) : (kmswMirrorRep R h).IsChanneled ↔ R.IsChanneled := by
  constructor
  · intro hc
    exact (KMSWMapRep.isChanneled_iff_of_iso _ _
      (kmswMirrorRep_mirror_baseIso R h)).mp
        (mirror_channeled _ (kmswMirrorRep_isSimpleOuterBoundary R h) hc)
  · exact mirror_channeled R h

private theorem out_simple
    (q : {q : KMSWMapIsoClass ℓ r N // q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    q.val.out.IsSimpleOuterBoundary := by
  have h := q.property.2
  rw [← Quotient.out_eq q.val] at h
  exact h

private theorem out_channeled
    (q : {q : KMSWMapIsoClass ℓ r N // q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    q.val.out.IsChanneled := by
  have h := q.property.1
  rw [← Quotient.out_eq q.val] at h
  exact h

private noncomputable def mirrorClassMap
    (q : {q : KMSWMapIsoClass ℓ r N // q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    {q : KMSWMapIsoClass r ℓ N // q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
  ⟨KMSWMapIsoClass.mk (kmswMirrorRep q.val.out (out_simple q)),
    (kmswMirrorRep_isChanneled_iff _ _).mpr (out_channeled q),
    kmswMirrorRep_isSimpleOuterBoundary _ _⟩

private theorem mirrorClassMap_mk (R : KMSWMapRep ℓ r N)
    (hc : R.IsChanneled) (h : R.IsSimpleOuterBoundary) :
    (mirrorClassMap ⟨KMSWMapIsoClass.mk R, hc, h⟩).val =
      KMSWMapIsoClass.mk (kmswMirrorRep R h) := by
  apply (KMSWMapIsoClass.mk_eq_mk_iff _ _).mpr
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff (KMSWMapIsoClass.mk R).out R).mp
    (Quotient.out_eq _)
  exact ⟨kmswMirrorRep_baseIso _ _ _ h I⟩

private theorem mirrorClassMap_involutive
    (q : {q : KMSWMapIsoClass ℓ r N // q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    mirrorClassMap (mirrorClassMap q) = q := by
  let R := q.val.out
  have hc : R.IsChanneled := out_channeled q
  have h : R.IsSimpleOuterBoundary := out_simple q
  have hq : q = ⟨KMSWMapIsoClass.mk R, hc, h⟩ :=
    Subtype.ext (Quotient.out_eq q.val).symm
  rw [hq]
  have hfirst : mirrorClassMap ⟨KMSWMapIsoClass.mk R, hc, h⟩ =
      ⟨KMSWMapIsoClass.mk (kmswMirrorRep R h), mirror_channeled R h hc,
        kmswMirrorRep_isSimpleOuterBoundary R h⟩ :=
    Subtype.ext (mirrorClassMap_mk R hc h)
  rw [hfirst]
  apply Subtype.ext
  rw [mirrorClassMap_mk _ (mirror_channeled R h hc)
    (kmswMirrorRep_isSimpleOuterBoundary R h)]
  exact (KMSWMapIsoClass.mk_eq_mk_iff _ _).mpr
    ⟨kmswMirrorRep_mirror_baseIso R h⟩

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
noncomputable def kmswMirrorClassEquiv (ℓ r N : ℕ) :
    {q : KMSWMapIsoClass ℓ r N // q.IsChanneled ∧ q.IsSimpleOuterBoundary} ≃
      {q : KMSWMapIsoClass r ℓ N // q.IsChanneled ∧ q.IsSimpleOuterBoundary} where
  toFun := mirrorClassMap
  invFun := mirrorClassMap
  left_inv := mirrorClassMap_involutive
  right_inv := mirrorClassMap_involutive

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
theorem kmswMirrorClassEquiv_mk (R : KMSWMapRep ℓ r N)
    (hc : R.IsChanneled) (h : R.IsSimpleOuterBoundary) :
    (kmswMirrorClassEquiv ℓ r N ⟨KMSWMapIsoClass.mk R, hc, h⟩).val =
      KMSWMapIsoClass.mk (kmswMirrorRep R h) :=
  mirrorClassMap_mk R hc h

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
theorem kmswMirrorRep_rightPrefixDarts (R : KMSWMapRep ℓ 1 N)
    (h : R.IsSimpleOuterBoundary) :
    rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1) = leftMissingDarts R.B := by
  ext d
  change (∃ i : Fin R.B.leftPath.darts.length,
    i.val < ℓ - 1 ∧ R.B.leftPath.darts.get i = d) ↔
      ∃ i : Fin R.B.leftPath.darts.length,
        i.val + 1 < R.B.leftPath.darts.length ∧ d = R.B.leftPath.darts.get i
  have hlen := R.B.leftPath.darts_length
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, by omega, he.symm⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, by omega, he.symm⟩

/-- orientation-reversing mirror on boundary-channeled KMSW map classes; -/
@[expose] noncomputable def kmswMirrorRep_partialMapIso (R : KMSWMapRep ℓ 1 N)
    (h : R.IsSimpleOuterBoundary) :
    DirectedMapWithMissingIso R.partialMap.mirror
      ((kmswMirrorRep R h).B.map.markMissing
        (rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1))
        (rightPrefixDarts_outer (kmswMirrorRep R h).B (ℓ - 1))) where
  toEquiv := Equiv.refl _
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by
    intro d
    change (R.B.map.missing d ∨
      d ∈ rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1) ∨
      R.B.map.edgeInv d ∈ rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1)) ↔
        d ∈ leftMissingDarts R.B ∨ R.B.map.edgeInv d ∈ leftMissingDarts R.B
    rw [kmswMirrorRep_rightPrefixDarts]
    simp only [R.B.noMissingDarts d, false_or]
    exact Iff.rfl
  tail_iff := by
    intro d
    change (R.B.map.tail d ∧ ¬
      (d ∈ rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1) ∨
      R.B.map.edgeInv d ∈ rightPrefixDarts (kmswMirrorRep R h).B (ℓ - 1))) ↔
        R.B.map.tail d ∧ ¬
          (d ∈ leftMissingDarts R.B ∨ R.B.map.edgeInv d ∈ leftMissingDarts R.B)
    rw [kmswMirrorRep_rightPrefixDarts]
    exact Iff.rfl
  outer_iff := by intro d; rfl

end DirectedDistances.PlanarMap
