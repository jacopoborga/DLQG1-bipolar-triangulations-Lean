module

public import DirectedDistances.PlanarMap.KMSWMapMirrorClass
public import DirectedDistances.KMSW.KMSWLeftProcedureEndpointFinal
public import DirectedDistances.PlanarMap.KMSWRightReversePartial
public import DirectedDistances.PlanarMap.KMSWMapSimpleBoundary
public import DirectedDistances.KMSW.KMSWLeftProcedureUniform
public import DirectedDistances.KMSW.KMSWLeftUniformLaw

/-! Finite mirror symmetry on endpoint classes and procedure-reading walks. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
@[expose] noncomputable def kmswMirrorEndpointEquiv (ℓ N : ℕ) (hℓ : 2 ≤ ℓ) :
    {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} ≃
      {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled} :=
  let e₁ : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} ≃
      {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    { toFun := fun q => ⟨q.val, q.property,
        KMSWMapIsoClass.isSimpleOuterBoundary_of_rightEndpoint hℓ q.val⟩
      invFun := fun q => ⟨q.val, q.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled ∧ q.IsSimpleOuterBoundary} ≃
      {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled} :=
    { toFun := fun q => ⟨q.val, q.property.1⟩
      invFun := fun q => ⟨q.val, q.property,
        KMSWMapIsoClass.isSimpleOuterBoundary_of_leftEndpoint hℓ q.val⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e₁.trans ((kmswMirrorClassEquiv ℓ 1 N).trans e₂)

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswMirrorEndpointEquiv_mk {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (R : KMSWMapRep ℓ 1 N) (hc : R.IsChanneled) :
    (kmswMirrorEndpointEquiv ℓ N hℓ ⟨KMSWMapIsoClass.mk R, hc⟩).val =
      KMSWMapIsoClass.mk (kmswMirrorRep R
        (R.isSimpleOuterBoundary_of_rightEndpoint hℓ)) := by
  exact kmswMirrorClassEquiv_mk R hc _

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
@[expose] noncomputable def kmswMirrorSymmetryEquiv (ℓ N : ℕ) (hℓ : 2 ≤ ℓ) :
    {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} ≃
      {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} :=
  (kmswMirrorEndpointEquiv ℓ N hℓ).trans
    (Equiv.ofBijective (rightRevClass hℓ)
      ⟨rightRevClass_injective hℓ (fun R R' hc hc' h => h.elim fun I =>
        kmswLeftEndpointReverseRep_iso hℓ R R' hc hc' I),
        rightRevClass_surjective hℓ⟩)

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswMirrorSymmetryEquiv_mk {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (R : KMSWMapRep ℓ 1 N) (hc : R.IsChanneled) :
    (kmswMirrorSymmetryEquiv ℓ N hℓ ⟨KMSWMapIsoClass.mk R, hc⟩).val =
      KMSWMapIsoClass.mk (kmswRightEndpointReverseRep
        (kmswMirrorRep R (R.isSimpleOuterBoundary_of_rightEndpoint hℓ)) hℓ
        ((kmswMirrorRep_isChanneled_iff _ _).mpr hc)) := by
  have hm := kmswMirrorEndpointEquiv_mk hℓ R hc
  have hs : kmswMirrorEndpointEquiv ℓ N hℓ ⟨KMSWMapIsoClass.mk R, hc⟩ =
      ⟨KMSWMapIsoClass.mk (kmswMirrorRep R
        (R.isSimpleOuterBoundary_of_rightEndpoint hℓ)),
        (kmswMirrorRep_isChanneled_iff _ _).mpr hc⟩ := Subtype.ext hm
  change (rightRevClass hℓ
    (kmswMirrorEndpointEquiv ℓ N hℓ ⟨KMSWMapIsoClass.mk R, hc⟩)).val = _
  rw [hs, rightRevClass_mk]

private theorem channeled_out {ℓ r N : ℕ}
    (q : {q : KMSWMapIsoClass ℓ r N // q.IsChanneled}) : q.val.out.IsChanneled := by
  have h := q.property
  rw [← Quotient.out_eq q.val] at h
  exact h

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswMirrorSymmetryEquiv_partialMapIso (ℓ N : ℕ) (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}) :
    Nonempty (DirectedMapWithMissingIso
      (kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.partialMap q.val.out.partialMap.mirror) := by
  let R := q.val.out
  have hc : R.IsChanneled := channeled_out q
  have hq : q = ⟨KMSWMapIsoClass.mk R, hc⟩ :=
    Subtype.ext (Quotient.out_eq q.val).symm
  have hv := kmswMirrorSymmetryEquiv_mk hℓ R hc
  rw [← hq] at hv
  let M := kmswMirrorRep R (R.isSimpleOuterBoundary_of_rightEndpoint hℓ)
  have hM : M.IsChanneled := (kmswMirrorRep_isChanneled_iff _ _).mpr hc
  obtain ⟨I⟩ := KMSWMapRep.partialMapIso_of_mk_eq_mk
    (kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out
    (kmswRightEndpointReverseRep M hℓ hM) ((Quotient.out_eq _).trans hv)
  exact ⟨I.trans ((kmswRightEndpointReverseRep_partialMapIso M hℓ hM).trans
    (kmswMirrorRep_partialMapIso R (R.isSimpleOuterBoundary_of_rightEndpoint hℓ)).symm)⟩

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswMirrorSymmetryEquiv_uniform (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).map
        (kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ) =
      uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  exact uniformCountingMeasure_map_of_bijective _
    (kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ).bijective

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswMirrorSymmetryEquiv_uniform_prod (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => (kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ p.1, Fin.rev p.2)) =
      (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1))) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  have : SFinite (uniformCountingMeasure (Fin (ℓ - 1))) := by
    unfold uniformCountingMeasure
    infer_instance
  have hrev := uniformCountingMeasure_map_of_bijective
    (Fin.rev (n := ℓ - 1)) Fin.rev_bijective
  have hm := Measure.map_prod_map
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled})
    (uniformCountingMeasure (Fin (ℓ - 1)))
    (measurable_of_countable (kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ))
    (measurable_of_countable (Fin.rev (n := ℓ - 1)))
  simpa only [kmswMirrorSymmetryEquiv_uniform ℓ n hℓ, hrev, Prod.map_def] using hm.symm

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
@[expose] noncomputable def kmswWalkMirrorEquiv (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    KMSWLeftWalkClass ℓ n ≃ KMSWLeftWalkClass ℓ n :=
  let e := kmswLeftEndpointSideEquiv ℓ n hℓ
  e.trans ((kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ).trans e.symm)

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswWalkMirrorEquiv_uniform (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    (uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).map
        (kmswWalkMirrorEquiv ℓ n hℓ) =
      uniformCountingMeasure (KMSWLeftWalkClass ℓ n) := by
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  exact uniformCountingMeasure_map_of_bijective _ (kmswWalkMirrorEquiv ℓ n hℓ).bijective

private def mirrorIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {M : DirectedMapWithMissing D}
    {M' : DirectedMapWithMissing E} (I : DirectedMapWithMissingIso M M') :
    DirectedMapWithMissingIso M.mirror M'.mirror where
  toEquiv := I.toEquiv
  rot_comm := by
    intro d
    change I.toEquiv (M.rot.symm d) = M'.rot.symm (I.toEquiv d)
    apply M'.rot.injective
    rw [← I.rot_comm]
    simp only [Equiv.apply_symm_apply]
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  outer_iff := by
    intro d
    rw [DirectedMapWithMissing.mirror_isOuter_iff,
      DirectedMapWithMissing.mirror_isOuter_iff]
    rw [← I.edgeInv_comm]
    exact I.outer_iff _

/-- mirror symmetry of channeled (ℓ,1) KMSW classes (endpoint classes only, simple-boundary restriction not needed); -/
theorem kmswWalkMirrorEquiv_partialMapIso (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    Nonempty (DirectedMapWithMissingIso
      (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1) (kmswWalkMirrorEquiv ℓ n hℓ c).val) n)
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).mirror) := by
  have hI := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ
    (kmswWalkMirrorEquiv ℓ n hℓ c)
  have he : kmswLeftEndpointSideEquiv ℓ n hℓ (kmswWalkMirrorEquiv ℓ n hℓ c) =
      kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ (kmswLeftEndpointSideEquiv ℓ n hℓ c) :=
    (kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply _
  rw [he] at hI
  obtain ⟨I⟩ := hI
  obtain ⟨J⟩ := kmswMirrorSymmetryEquiv_partialMapIso ℓ (n + ℓ) hℓ
    (kmswLeftEndpointSideEquiv ℓ n hℓ c)
  obtain ⟨K⟩ := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ c
  exact ⟨I.symm.trans (J.trans (mirrorIso K))⟩

end DirectedDistances.KMSW
