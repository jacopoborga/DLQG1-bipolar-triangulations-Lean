/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}

/-- An orientation-preserving isomorphism of bipolar triangulations with
boundary. It preserves the directed dart data, the exterior face orbit, and
the ordered boundary paths, while forgetting dart labels and the auxiliary
outer-word choice. These isomorphisms are the representative-level
prerequisite for the isomorphism-class Boltzmann spaces in Lemma -/
structure BipolarBoundaryIso
    (B : BipolarTriangulationWithBoundary D ℓ r)
    (B' : BipolarTriangulationWithBoundary D' ℓ r) where
  toEquiv : D ≃ D'
  rot_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (toEquiv d)
  edgeInv_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (toEquiv d)
  missing_iff : ∀ d, B'.map.missing (toEquiv d) ↔ B.map.missing d
  tail_iff : ∀ d, B'.map.tail (toEquiv d) ↔ B.map.tail d
  leftDarts : B.leftPath.darts.map toEquiv = B'.leftPath.darts
  rightDarts : B.rightPath.darts.map toEquiv = B'.rightPath.darts
  outer_face : Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
    (toEquiv B.map.outer) B'.map.outer

namespace BipolarBoundaryIso

variable {B : BipolarTriangulationWithBoundary D ℓ r}
  {B' : BipolarTriangulationWithBoundary D' ℓ r}

private theorem sameCycle_map (e : D ≃ D') (f : Equiv.Perm D)
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

/-- The dart equivalence induces an equivalence of rotation-cycle vertices. -/
@[expose] noncomputable def vertexEquiv (I : BipolarBoundaryIso B B') :
    CombinatorialMap.VertexQuotient B.map.toCombinatorialMap ≃
      CombinatorialMap.VertexQuotient B'.map.toCombinatorialMap := by
  classical
  let fwd : CombinatorialMap.VertexQuotient B.map.toCombinatorialMap →
      CombinatorialMap.VertexQuotient B'.map.toCombinatorialMap :=
    Quotient.map I.toEquiv (by
      intro x y h
      exact sameCycle_map I.toEquiv B.map.toCombinatorialMap.rot
        B'.map.toCombinatorialMap.rot I.rot_comm h)
  let back : CombinatorialMap.VertexQuotient B'.map.toCombinatorialMap →
      CombinatorialMap.VertexQuotient B.map.toCombinatorialMap :=
    Quotient.map I.toEquiv.symm (by
      intro x y h
      apply sameCycle_map I.toEquiv.symm B'.map.toCombinatorialMap.rot
        B.map.toCombinatorialMap.rot (fun d => by
          have hc := I.rot_comm (I.toEquiv.symm d)
          simpa using (congrArg I.toEquiv.symm hc).symm) h)
  exact
    { toFun := fwd
      invFun := back
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back] }

/-- The vertex equivalence sends the tail vertex of each dart to its image. -/
theorem vertexEquiv_dartTailVertex (I : BipolarBoundaryIso B B') (d : D) :
    I.vertexEquiv (dartTailVertex B.map d) = dartTailVertex B'.map (I.toEquiv d) := by
  simp [dartTailVertex, vertexEquiv]

/-- The vertex equivalence sends the head vertex of each dart to its image. -/
theorem vertexEquiv_dartHeadVertex (I : BipolarBoundaryIso B B') (d : D) :
    I.vertexEquiv (dartHeadVertex B.map d) = dartHeadVertex B'.map (I.toEquiv d) := by
  simp [dartHeadVertex, vertexEquiv, I.edgeInv_comm]

/-- The dart equivalence induces an equivalence of edge orbits. -/
@[expose] noncomputable def edgeEquiv (I : BipolarBoundaryIso B B') :
    CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap ≃
      CombinatorialMap.EdgeQuotient B'.map.toCombinatorialMap := by
  classical
  let fwd : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap →
      CombinatorialMap.EdgeQuotient B'.map.toCombinatorialMap :=
    Quotient.map I.toEquiv (by
      intro x y h
      exact sameCycle_map I.toEquiv B.map.toCombinatorialMap.edgeInv
        B'.map.toCombinatorialMap.edgeInv I.edgeInv_comm h)
  let back : CombinatorialMap.EdgeQuotient B'.map.toCombinatorialMap →
      CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
    Quotient.map I.toEquiv.symm (by
      intro x y h
      apply sameCycle_map I.toEquiv.symm B'.map.toCombinatorialMap.edgeInv
        B.map.toCombinatorialMap.edgeInv (fun d => by
          have hc := I.edgeInv_comm (I.toEquiv.symm d)
          simpa using (congrArg I.toEquiv.symm hc).symm) h)
  exact
    { toFun := fwd
      invFun := back
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back] }

/-- Isomorphic maps have the same number of edge orbits, retaining loops and
parallel edges as distinct edge identities. -/
theorem numEdges_eq (I : BipolarBoundaryIso B B') :
    B.map.toCombinatorialMap.numEdges = B'.map.toCombinatorialMap.numEdges := by
  classical
  unfold CombinatorialMap.numEdges
  exact Fintype.card_congr I.edgeEquiv

/-- Isomorphic maps have the same number of rotation-cycle vertices. -/
theorem numVertices_eq (I : BipolarBoundaryIso B B') :
    B.map.toCombinatorialMap.numVertices = B'.map.toCombinatorialMap.numVertices := by
  classical
  unfold CombinatorialMap.numVertices
  exact Fintype.card_congr I.vertexEquiv

private theorem rot_symm_comm (I : BipolarBoundaryIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.rot.symm d) =
      B'.map.toCombinatorialMap.rot.symm (I.toEquiv d) := by
  apply B'.map.toCombinatorialMap.rot.injective
  calc
    B'.map.toCombinatorialMap.rot (I.toEquiv (B.map.toCombinatorialMap.rot.symm d)) =
        I.toEquiv (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.rot.symm d)) :=
      (I.rot_comm _).symm
    _ = I.toEquiv d := by simp
    _ = B'.map.toCombinatorialMap.rot
        (B'.map.toCombinatorialMap.rot.symm (I.toEquiv d)) := by simp

/-- The exterior face permutation commutes with a boundary isomorphism. -/
theorem faceSucc_comm (I : BipolarBoundaryIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.faceSucc d) =
      B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) := by
  simp [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    rot_symm_comm I, I.edgeInv_comm]

/-- A face-orbit relation transports along a boundary isomorphism. -/
private theorem faceCycle_map (I : BipolarBoundaryIso B B') {x y : D}
    (h : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc x y) :
    Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      (I.toEquiv x) (I.toEquiv y) :=
  sameCycle_map I.toEquiv B.map.toCombinatorialMap.faceSucc
    B'.map.toCombinatorialMap.faceSucc I.faceSucc_comm h

/-- The dart equivalence induces an equivalence of face orbits. -/
@[expose] noncomputable def faceEquiv (I : BipolarBoundaryIso B B') :
    CombinatorialMap.FaceQuotient B.map.toCombinatorialMap ≃
      CombinatorialMap.FaceQuotient B'.map.toCombinatorialMap := by
  classical
  let fwd : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap →
      CombinatorialMap.FaceQuotient B'.map.toCombinatorialMap :=
    Quotient.map I.toEquiv (by
      intro x y h
      exact faceCycle_map I h)
  let back : CombinatorialMap.FaceQuotient B'.map.toCombinatorialMap →
      CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    Quotient.map I.toEquiv.symm (by
      intro x y h
      have hcomm : ∀ d,
          I.toEquiv.symm (B'.map.toCombinatorialMap.faceSucc d) =
            B.map.toCombinatorialMap.faceSucc (I.toEquiv.symm d) := by
        intro d
        simpa using
          (congrArg I.toEquiv.symm (I.faceSucc_comm (I.toEquiv.symm d))).symm
      exact sameCycle_map I.toEquiv.symm B'.map.toCombinatorialMap.faceSucc
        B.map.toCombinatorialMap.faceSucc hcomm h)
  exact
    { toFun := fwd
      invFun := back
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        simp [fwd, back] }

/-- Isomorphic maps have the same number of face orbits. -/
theorem numFaces_eq (I : BipolarBoundaryIso B B') :
    B.map.toCombinatorialMap.numFaces = B'.map.toCombinatorialMap.numFaces := by
  classical
  unfold CombinatorialMap.numFaces
  exact Fintype.card_congr I.faceEquiv

/-- A directed step transports through a boundary isomorphism. -/
theorem directedStep_map (I : BipolarBoundaryIso B B') {u v : MapVertex B.map}
    (h : B.map.directedStep u v) :
    B'.map.directedStep (I.vertexEquiv u) (I.vertexEquiv v) := by
  rcases h with ⟨d, hmiss, htail, htailV, hheadV⟩
  refine ⟨I.toEquiv d, ?_, ?_, ?_, ?_⟩
  · intro hm
    exact hmiss ((I.missing_iff d).mp hm)
  · exact (I.tail_iff d).2 htail
  · calc
      dartTailVertex B'.map (I.toEquiv d) =
          I.vertexEquiv (dartTailVertex B.map d) :=
        (I.vertexEquiv_dartTailVertex d).symm
      _ = I.vertexEquiv u := congrArg I.vertexEquiv htailV
  · calc
      dartHeadVertex B'.map (I.toEquiv d) =
          I.vertexEquiv (dartHeadVertex B.map d) :=
        (I.vertexEquiv_dartHeadVertex d).symm
      _ = I.vertexEquiv v := congrArg I.vertexEquiv hheadV

/-- Directed-step preservation is an equivalence. -/
theorem directedStep_iff (I : BipolarBoundaryIso B B') {u v : MapVertex B.map} :
    B.map.directedStep u v ↔
      B'.map.directedStep (I.vertexEquiv u) (I.vertexEquiv v) := by
  constructor
  · exact I.directedStep_map
  · intro h
    rcases h with ⟨d', hmiss, htail, htailV, hheadV⟩
    refine ⟨I.toEquiv.symm d', ?_, ?_, ?_, ?_⟩
    · intro hm
      exact hmiss (by simpa using (I.missing_iff (I.toEquiv.symm d')).mpr hm)
    · exact (I.tail_iff (I.toEquiv.symm d')).mp (by simpa using htail)
    · apply I.vertexEquiv.injective
      calc
        I.vertexEquiv (dartTailVertex B.map (I.toEquiv.symm d')) =
            dartTailVertex B'.map (I.toEquiv (I.toEquiv.symm d')) :=
          I.vertexEquiv_dartTailVertex _
        _ = dartTailVertex B'.map d' := by simp
        _ = I.vertexEquiv u := htailV
    · apply I.vertexEquiv.injective
      calc
        I.vertexEquiv (dartHeadVertex B.map (I.toEquiv.symm d')) =
            dartHeadVertex B'.map (I.toEquiv (I.toEquiv.symm d')) :=
          I.vertexEquiv_dartHeadVertex _
        _ = dartHeadVertex B'.map d' := by simp
        _ = I.vertexEquiv v := hheadV

/-- The induced vertex equivalence sends the unique source to the unique
source. -/
theorem vertexEquiv_source (I : BipolarBoundaryIso B B') :
    I.vertexEquiv B.source = B'.source := by
  apply B'.source_unique
  intro h
  rcases h with ⟨u, hu⟩
  have hu' : B'.map.directedStep
      (I.vertexEquiv (I.vertexEquiv.symm u)) (I.vertexEquiv B.source) := by
    simpa using hu
  have hback := (I.directedStep_iff (u := I.vertexEquiv.symm u)
    (v := B.source)).mpr hu'
  exact B.isSource ⟨I.vertexEquiv.symm u, hback⟩

/-- The induced vertex equivalence sends the unique sink to the unique
sink. -/
theorem vertexEquiv_sink (I : BipolarBoundaryIso B B') :
    I.vertexEquiv B.sink = B'.sink := by
  apply B'.sink_unique
  intro h
  rcases h with ⟨v, hv⟩
  have hv' : B'.map.directedStep
      (I.vertexEquiv B.sink) (I.vertexEquiv (I.vertexEquiv.symm v)) := by
    simpa using hv
  have hback := (I.directedStep_iff (u := B.sink)
    (v := I.vertexEquiv.symm v)).mpr hv'
  exact B.isSink ⟨I.vertexEquiv.symm v, hback⟩

/-- Transport a simple directed dart path across a boundary isomorphism.
This path-level helper supports invariance of the finite XDP geodesic
predicates used toward `lem-lr-ind` and `prop-thin-ind`; it does not define
those predicates. -/
@[expose] noncomputable def transportPath (I : BipolarBoundaryIso B B')
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
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by
      simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by
      simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartTailVertex _
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
              I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartHeadVertex _

/-- The transported path's dart list is the pointwise image of the original
dart list. -/
theorem transportPath_darts (I : BipolarBoundaryIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (I.transportPath P).darts = P.darts.map I.toEquiv := rfl

/-- Invert a boundary isomorphism. Helper toward `lem-lr-ind` and `hLR`;
not counted as a paper result. -/
@[expose] def symm (I : BipolarBoundaryIso B B') : BipolarBoundaryIso B' B where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    simpa using (congrArg I.toEquiv.symm (I.rot_comm (I.toEquiv.symm d))).symm
  edgeInv_comm := by
    intro d
    simpa using
      (congrArg I.toEquiv.symm (I.edgeInv_comm (I.toEquiv.symm d))).symm
  missing_iff := by
    intro d
    simpa using (I.missing_iff (I.toEquiv.symm d)).symm
  tail_iff := by
    intro d
    simpa using (I.tail_iff (I.toEquiv.symm d)).symm
  leftDarts := by
    calc
      B'.leftPath.darts.map I.toEquiv.symm =
          (B.leftPath.darts.map I.toEquiv).map I.toEquiv.symm :=
        congrArg (List.map I.toEquiv.symm) I.leftDarts.symm
      _ = B.leftPath.darts := by simp
  rightDarts := by
    calc
      B'.rightPath.darts.map I.toEquiv.symm =
          (B.rightPath.darts.map I.toEquiv).map I.toEquiv.symm :=
        congrArg (List.map I.toEquiv.symm) I.rightDarts.symm
      _ = B.rightPath.darts := by simp
  outer_face := by
    have hcomm : ∀ d,
        I.toEquiv.symm (B'.map.toCombinatorialMap.faceSucc d) =
          B.map.toCombinatorialMap.faceSucc (I.toEquiv.symm d) := by
      intro d
      simpa using
        (congrArg I.toEquiv.symm (I.faceSucc_comm (I.toEquiv.symm d))).symm
    simpa using sameCycle_map I.toEquiv.symm B'.map.toCombinatorialMap.faceSucc
      B.map.toCombinatorialMap.faceSucc hcomm I.outer_face.symm

/-- Compose boundary isomorphisms. Helper toward `lem-lr-ind` and `hLR`;
not counted as a paper result. -/
@[expose] def trans {D'' : Type*} [Fintype D''] [DecidableEq D'']
    {B'' : BipolarTriangulationWithBoundary D'' ℓ r}
    (I : BipolarBoundaryIso B B') (J : BipolarBoundaryIso B' B'') :
    BipolarBoundaryIso B B'' where
  toEquiv := I.toEquiv.trans J.toEquiv
  rot_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.rot_comm, J.rot_comm]
  edgeInv_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.edgeInv_comm, J.edgeInv_comm]
  missing_iff := by
    intro d
    exact (J.missing_iff (I.toEquiv d)).trans (I.missing_iff d)
  tail_iff := by
    intro d
    exact (J.tail_iff (I.toEquiv d)).trans (I.tail_iff d)
  leftDarts := by
    calc
      B.leftPath.darts.map (I.toEquiv.trans J.toEquiv) =
          (B.leftPath.darts.map I.toEquiv).map J.toEquiv := by simp
      _ = B''.leftPath.darts := by rw [I.leftDarts, J.leftDarts]
  rightDarts := by
    calc
      B.rightPath.darts.map (I.toEquiv.trans J.toEquiv) =
          (B.rightPath.darts.map I.toEquiv).map J.toEquiv := by simp
      _ = B''.rightPath.darts := by rw [I.rightDarts, J.rightDarts]
  outer_face := by
    have h := faceCycle_map J I.outer_face
    exact h.trans J.outer_face

/-- Identity boundary isomorphism. Helper toward `lem-lr-ind`;
not counted as a paper result. -/
@[expose] def refl (B : BipolarTriangulationWithBoundary D ℓ r) :
    BipolarBoundaryIso B B where
  toEquiv := Equiv.refl D
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by intro d; rfl
  tail_iff := by intro d; rfl
  leftDarts := by simp
  rightDarts := by simp
  outer_face := Equiv.Perm.SameCycle.rfl

/-- The boundary-isomorphism relation on a fixed dart carrier is an
equivalence relation. This is the setoid-level helper needed before forming
the quotient sample space for `lem-lr-ind`; it does not construct a
Boltzmann measure. -/
theorem equivalence (ℓ r : ℕ) :
    Equivalence (fun B B' : BipolarTriangulationWithBoundary D ℓ r =>
      Nonempty (BipolarBoundaryIso B B')) where
  refl B := ⟨BipolarBoundaryIso.refl B⟩
  symm h := h.elim (fun I => ⟨I.symm⟩)
  trans h₁ h₂ := h₁.elim fun I => h₂.elim fun J => ⟨I.trans J⟩

end BipolarBoundaryIso
end DirectedDistances.PlanarMap
