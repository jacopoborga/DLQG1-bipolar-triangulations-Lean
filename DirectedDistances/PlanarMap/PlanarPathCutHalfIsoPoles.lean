/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfIso
public import DirectedDistances.PlanarMap.PlanarPathCutHalfFaces
public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfFaces

/-! # Pole and path transport for isomorphic cut halves

paper result. Isomorphisms of the input map and cut path induce isomorphisms
of the half-map vertex quotients and lifted paths. -/

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r n : ℕ}

private theorem sameCycle_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hcomm : ∀ x, e (f x) = g (e x)) {x y : α}
    (hxy : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle g (e x) (e y) := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  refine ⟨k, ?_⟩
  have hpow : ∀ (k : ℕ) (x : α), e ((f ^ k) x) = (g ^ k) (e x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
        exact (ih (f x)).trans (congrArg (g ^ k) (hcomm x))
  calc
    (g ^ k) (e x) = e ((f ^ k) x) := (hpow k x).symm
    _ = e y := congrArg e hk

/-- A dart-carrier equivalence commuting with two permutations induces an
equivalence of their rotation-cycle quotients. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def sameCycleVertexQuotientEquiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hcomm : ∀ x, e (f x) = g (e x)) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ≃
      Quotient (Equiv.Perm.SameCycle.setoid g) := by
  classical
  let fwd : Quotient (Equiv.Perm.SameCycle.setoid f) →
      Quotient (Equiv.Perm.SameCycle.setoid g) :=
    Quotient.map e (by
      intro a b hab
      exact sameCycle_map_equiv e f g hcomm hab)
  let back : Quotient (Equiv.Perm.SameCycle.setoid g) →
      Quotient (Equiv.Perm.SameCycle.setoid f) :=
    Quotient.map e.symm (by
      intro a b hab
      have hback : ∀ x, e.symm (g x) = f (e.symm x) := by
        intro x
        apply e.injective
        simpa using (hcomm (e.symm x)).symm
      exact sameCycle_map_equiv e.symm g f hback hab)
  exact
    { toFun := fwd
      invFun := back
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        simp [fwd, back]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        simp [fwd, back] }

/-- The left half rotation-cycle vertices are carried to the corresponding
not the paper result. -/
@[expose] noncomputable def pathCutLeftHalfVertexEquiv
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    MapVertex (pathCutLeftHalfDirectedMap B P) ≃
      MapVertex (pathCutLeftHalfDirectedMap B' P') := by
  classical
  exact sameCycleVertexQuotientEquiv (halfLeftCongr I P P' hP')
    (pathCutLeftHalfDirectedMap B P).rot
    (pathCutLeftHalfDirectedMap B' P').rot
    (halfLeftCongr_rot I P P' hP')

/-- The left half vertex equivalence preserves dart-tail vertices. Helper
result. -/
theorem pathCutLeftHalfVertexEquiv_dartTailVertex
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    pathCutLeftHalfVertexEquiv I P P' hP'
        (dartTailVertex (pathCutLeftHalfDirectedMap B P) d) =
      dartTailVertex (pathCutLeftHalfDirectedMap B' P')
        (halfLeftCongr I P P' hP' d) := by
  rfl

/-- The left half vertex equivalence preserves dart-head vertices. Helper
result. -/
theorem pathCutLeftHalfVertexEquiv_dartHeadVertex
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    pathCutLeftHalfVertexEquiv I P P' hP'
        (dartHeadVertex (pathCutLeftHalfDirectedMap B P) d) =
      dartHeadVertex (pathCutLeftHalfDirectedMap B' P')
        (halfLeftCongr I P P' hP' d) := by
  change pathCutLeftHalfVertexEquiv I P P' hP'
      (dartTailVertex (pathCutLeftHalfDirectedMap B P)
        ((pathCutLeftHalfDirectedMap B P).edgeInv d)) =
    dartTailVertex (pathCutLeftHalfDirectedMap B' P')
      ((pathCutLeftHalfDirectedMap B' P').edgeInv
        (halfLeftCongr I P P' hP' d))
  rw [pathCutLeftHalfVertexEquiv_dartTailVertex, halfLeftCongr_edgeInv]

/-- The left half vertex equivalence commutes with inclusion into the base
vertices and `I.vertexEquiv`. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfVertexEquiv_vertexMap
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (v : MapVertex (pathCutLeftHalfDirectedMap B P)) :
    pathCutLeftHalfVertexMap B' P'
        (pathCutLeftHalfVertexEquiv I P P' hP' v) =
      I.vertexEquiv (pathCutLeftHalfVertexMap B P v) := by
  refine Quotient.inductionOn v ?_
  intro d
  rfl

/-- The left half source is carried to the primed left half source. Helper
result. -/
theorem pathCutLeftHalfVertexEquiv_source
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    pathCutLeftHalfVertexEquiv I P P' hP' (pathCutLeftHalfSource B P) =
      pathCutLeftHalfSource B' P' := by
  apply pathCutLeftHalfVertexMap_injective B' P'
  rw [pathCutLeftHalfSource_map, pathCutLeftHalfVertexEquiv_vertexMap,
    pathCutLeftHalfSource_map, I.vertexEquiv_source]

/-- The left half sink is carried to the primed left half sink. Helper
result. -/
theorem pathCutLeftHalfVertexEquiv_sink
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    pathCutLeftHalfVertexEquiv I P P' hP' (pathCutLeftHalfSink B P) =
      pathCutLeftHalfSink B' P' := by
  apply pathCutLeftHalfVertexMap_injective B' P'
  rw [pathCutLeftHalfSink_map, pathCutLeftHalfVertexEquiv_vertexMap,
    pathCutLeftHalfSink_map, I.vertexEquiv_sink]

/-- The lifted left boundary paths have corresponding subtype dart lists.
paper result. -/
theorem leftPathHalf_darts_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    (leftPathHalf B' P').darts =
      (leftPathHalf B P).darts.map (halfLeftCongr I P P' hP') := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  change (leftPathHalf B' P').darts.unattach =
    ((leftPathHalf B P).darts.map (halfLeftCongr I P P' hP')).unattach
  calc
    _ = B'.leftPath.darts := leftPathHalf_darts B' P'
    _ = B.leftPath.darts.map I.toEquiv := I.leftDarts.symm
    _ = (leftPathHalf B P).darts.unattach.map I.toEquiv := by
      rw [leftPathHalf_darts]
    _ = ((leftPathHalf B P).darts.map (halfLeftCongr I P P' hP')).unattach := by
      simp only [List.unattach, List.map_map, Function.comp_def,
        halfLeftCongr, Equiv.subtypeEquiv_apply]

/-- The lifted cut paths have corresponding subtype dart lists. Helper
result. -/
theorem cutPathHalf_darts_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    (cutPathHalf B' P').darts =
      (cutPathHalf B P).darts.map (halfLeftCongr I P P' hP') := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  change (cutPathHalf B' P').darts.unattach =
    ((cutPathHalf B P).darts.map (halfLeftCongr I P P' hP')).unattach
  calc
    _ = P'.darts := cutPathHalf_darts B' P'
    _ = P.darts.map I.toEquiv := hP'
    _ = (cutPathHalf B P).darts.unattach.map I.toEquiv := by
      rw [cutPathHalf_darts]
    _ = ((cutPathHalf B P).darts.map (halfLeftCongr I P P' hP')).unattach := by
      simp only [List.unattach, List.map_map, Function.comp_def,
        halfLeftCongr, Equiv.subtypeEquiv_apply]

/-- The right half rotation-cycle vertices are carried to the corresponding
not the paper result. -/
@[expose] noncomputable def pathCutRightHalfVertexEquiv
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    MapVertex (pathCutRightHalfDirectedMap B P) ≃
      MapVertex (pathCutRightHalfDirectedMap B' P') := by
  classical
  exact sameCycleVertexQuotientEquiv (halfRightCongr I P P' hP')
    (pathCutRightHalfDirectedMap B P).rot
    (pathCutRightHalfDirectedMap B' P').rot
    (halfRightCongr_rot I P P' hP')

/-- The right half vertex equivalence preserves dart-tail vertices. Helper
result. -/
theorem pathCutRightHalfVertexEquiv_dartTailVertex
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    pathCutRightHalfVertexEquiv I P P' hP'
        (dartTailVertex (pathCutRightHalfDirectedMap B P) d) =
      dartTailVertex (pathCutRightHalfDirectedMap B' P')
        (halfRightCongr I P P' hP' d) := by
  rfl

/-- The right half vertex equivalence preserves dart-head vertices. Helper
result. -/
theorem pathCutRightHalfVertexEquiv_dartHeadVertex
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    pathCutRightHalfVertexEquiv I P P' hP'
        (dartHeadVertex (pathCutRightHalfDirectedMap B P) d) =
      dartHeadVertex (pathCutRightHalfDirectedMap B' P')
        (halfRightCongr I P P' hP' d) := by
  change pathCutRightHalfVertexEquiv I P P' hP'
      (dartTailVertex (pathCutRightHalfDirectedMap B P)
        ((pathCutRightHalfDirectedMap B P).edgeInv d)) =
    dartTailVertex (pathCutRightHalfDirectedMap B' P')
      ((pathCutRightHalfDirectedMap B' P').edgeInv
        (halfRightCongr I P P' hP' d))
  rw [pathCutRightHalfVertexEquiv_dartTailVertex, halfRightCongr_edgeInv]

/-- The right half vertex equivalence commutes with inclusion into the base
vertices and `I.vertexEquiv`. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfVertexEquiv_vertexMap
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (v : MapVertex (pathCutRightHalfDirectedMap B P)) :
    pathCutRightHalfVertexMap B' P'
        (pathCutRightHalfVertexEquiv I P P' hP' v) =
      I.vertexEquiv (pathCutRightHalfVertexMap B P v) := by
  refine Quotient.inductionOn v ?_
  intro d
  rfl

/-- The right half source is carried to the primed right half source. Helper
result. -/
theorem pathCutRightHalfVertexEquiv_source
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    pathCutRightHalfVertexEquiv I P P' hP' (pathCutRightHalfSource B P) =
      pathCutRightHalfSource B' P' := by
  apply pathCutRightHalfVertexMap_injective B' P'
  rw [pathCutRightHalfSource_map, pathCutRightHalfVertexEquiv_vertexMap,
    pathCutRightHalfSource_map, I.vertexEquiv_source]

/-- The right half sink is carried to the primed right half sink. Helper
result. -/
theorem pathCutRightHalfVertexEquiv_sink
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    pathCutRightHalfVertexEquiv I P P' hP' (pathCutRightHalfSink B P) =
      pathCutRightHalfSink B' P' := by
  apply pathCutRightHalfVertexMap_injective B' P'
  rw [pathCutRightHalfSink_map, pathCutRightHalfVertexEquiv_vertexMap,
    pathCutRightHalfSink_map, I.vertexEquiv_sink]

/-- The lifted right boundary paths have corresponding subtype dart lists.
paper result. -/
theorem rightPathHalf_darts_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    (rightPathHalf B' P').darts =
      (rightPathHalf B P).darts.map (halfRightCongr I P P' hP') := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  change (rightPathHalf B' P').darts.unattach =
    ((rightPathHalf B P).darts.map (halfRightCongr I P P' hP')).unattach
  calc
    _ = B'.rightPath.darts := rightPathHalf_darts B' P'
    _ = B.rightPath.darts.map I.toEquiv := I.rightDarts.symm
    _ = (rightPathHalf B P).darts.unattach.map I.toEquiv := by
      rw [rightPathHalf_darts]
    _ = ((rightPathHalf B P).darts.map (halfRightCongr I P P' hP')).unattach := by
      simp only [List.unattach, List.map_map, Function.comp_def,
        halfRightCongr, Equiv.subtypeEquiv_apply]

/-- The lifted right cut paths have corresponding subtype dart lists.
paper result. -/
theorem cutPathRightHalf_darts_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    (cutPathRightHalf B' P').darts =
      (cutPathRightHalf B P).darts.map (halfRightCongr I P P' hP') := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  change (cutPathRightHalf B' P').darts.unattach =
    ((cutPathRightHalf B P).darts.map (halfRightCongr I P P' hP')).unattach
  calc
    _ = P'.darts := cutPathRightHalf_darts B' P'
    _ = P.darts.map I.toEquiv := hP'
    _ = (cutPathRightHalf B P).darts.unattach.map I.toEquiv := by
      rw [cutPathRightHalf_darts]
    _ = ((cutPathRightHalf B P).darts.map (halfRightCongr I P P' hP')).unattach := by
      simp only [List.unattach, List.map_map, Function.comp_def,
        halfRightCongr, Equiv.subtypeEquiv_apply]

private theorem pathCutIso_pathDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ P.darts ↔ I.toEquiv d ∈ P'.darts := by
  rw [hP']
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    rcases List.mem_map.mp hd with ⟨e, he, hde⟩
    apply I.toEquiv.injective at hde
    simpa [hde] using he

/-- Boundary-dart membership for the left half is preserved by the input
isomorphism and cut-path correspondence. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfBoundaryDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutLeftHalfBoundaryDarts B P ↔
      I.toEquiv d ∈ pathCutLeftHalfBoundaryDarts B' P' := by
  change ((d ∈ pathCutLeftHalfDarts B P ∧ B.map.IsOuter d) ∨
      ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p) ↔
    ((I.toEquiv d ∈ pathCutLeftHalfDarts B' P' ∧
        B'.map.IsOuter (I.toEquiv d)) ∨
      ∃ q ∈ P'.darts,
        I.toEquiv d = B'.map.toCombinatorialMap.edgeInv q)
  constructor
  · rintro (⟨hd, ho⟩ | ⟨p, hp, hdp⟩)
    · exact Or.inl ⟨(pathCutLeftHalfDarts_mem_iff I P P' hP' d).mp hd,
        (I.outer_iff d).mpr ho⟩
    · refine Or.inr ⟨I.toEquiv p,
        (pathCutIso_pathDarts_mem_iff I P P' hP' p).mp hp, ?_⟩
      calc
        I.toEquiv d = I.toEquiv (B.map.toCombinatorialMap.edgeInv p) :=
          congrArg I.toEquiv hdp
        _ = B'.map.toCombinatorialMap.edgeInv (I.toEquiv p) := I.edgeInv_comm p
  · rintro (⟨hd, ho⟩ | ⟨q, hq, hdq⟩)
    · exact Or.inl ⟨(pathCutLeftHalfDarts_mem_iff I P P' hP' d).mpr hd,
        (I.outer_iff d).mp ho⟩
    · let p := I.toEquiv.symm q
      refine Or.inr ⟨p,
        (pathCutIso_pathDarts_mem_iff I P P' hP' p).mpr (by simpa [p] using hq),
        ?_⟩
      apply I.toEquiv.injective
      calc
        I.toEquiv d = B'.map.toCombinatorialMap.edgeInv q := hdq
        _ = I.toEquiv (B.map.toCombinatorialMap.edgeInv p) := by
          rw [I.edgeInv_comm]
          simp [p]

/-- Boundary-dart membership for the right half is preserved by the input
isomorphism and cut-path correspondence. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfBoundaryDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutRightHalfBoundaryDarts B P ↔
      I.toEquiv d ∈ pathCutRightHalfBoundaryDarts B' P' := by
  change ((d ∈ pathCutRightHalfDarts B P ∧ B.map.IsOuter d) ∨
      d ∈ P.darts) ↔
    ((I.toEquiv d ∈ pathCutRightHalfDarts B' P' ∧
        B'.map.IsOuter (I.toEquiv d)) ∨ I.toEquiv d ∈ P'.darts)
  constructor
  · rintro (⟨hd, ho⟩ | hp)
    · exact Or.inl ⟨(pathCutRightHalfDarts_mem_iff I P P' hP' d).mp hd,
        (I.outer_iff d).mpr ho⟩
    · exact Or.inr ((pathCutIso_pathDarts_mem_iff I P P' hP' d).mp hp)
  · rintro (⟨hd, ho⟩ | hp)
    · exact Or.inl ⟨(pathCutRightHalfDarts_mem_iff I P P' hP' d).mpr hd,
        (I.outer_iff d).mp ho⟩
    · exact Or.inr ((pathCutIso_pathDarts_mem_iff I P P' hP' d).mpr hp)

end DirectedDistances.PlanarMap
