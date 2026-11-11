/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryIso
public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

/-! Supporting lemmas for paper labels `def-bipolar`, `def-bipolar-bdy`, `lem-lr-ind`, `thm-kmsw` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}

omit [DecidableEq D] [Fintype D'] [DecidableEq D'] in
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

/-- The representative-independent vertex map induced by a dart equivalence
that commutes with rotation. This is a helper toward `thm-kmsw` and -/
@[expose] noncomputable def bipolarBoundaryVertexEquiv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d)) :
    MapVertex B.map ≃ MapVertex B'.map := by
  classical
  let fwd : MapVertex B.map → MapVertex B'.map :=
    Quotient.map e (by
      intro x y h
      exact sameCycle_map e B.map.toCombinatorialMap.rot
        B'.map.toCombinatorialMap.rot hrot h)
  let back : MapVertex B'.map → MapVertex B.map :=
    Quotient.map e.symm (by
      intro x y h
      have hcomm : ∀ d,
          e.symm (B'.map.toCombinatorialMap.rot d) =
            B.map.toCombinatorialMap.rot (e.symm d) := by
        intro d
        simpa using
          (congrArg e.symm (hrot (e.symm d))).symm
      exact sameCycle_map e.symm B'.map.toCombinatorialMap.rot
        B.map.toCombinatorialMap.rot hcomm h)
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

/-- An unrooted orientation-preserving isomorphism of general bipolar
triangulations with boundary. Each field matches Definition
flip preserve the oriented planar-map structure; `tail_iff` preserves its
orientation; `missing_iff` is retained although both base carriers have no
missing darts; `outer_iff` preserves the exterior face as a face orbit, not
its marked dart. The source and sink and the ordered left and right dart lists
are preserved. The auxiliary `outerWord` and the choice of a dart naming the
outer face are forgotten, as the definition identifies the boundary paths,
not these representatives. The general base carrier permits shared boundary
edges, including the one-edge map `m₀`. This is a helper toward `thm-kmsw`
and `lem-lr-ind`; it is not the paper result. -/
structure BipolarBoundaryBaseIso
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r) where
  /-- The bijection of dart identities (`def-bipolar-bdy`, -/
  toEquiv : D ≃ D'
  /-- Preserve cyclic order around vertices (`def-bipolar-bdy`, -/
  rot_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (toEquiv d)
  /-- Preserve the opposite dart of each edge (`def-bipolar-bdy`, -/
  edgeInv_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (toEquiv d)
  

  missing_iff : ∀ d, B'.map.missing (toEquiv d) ↔ B.map.missing d
  /-- Preserve the direction of each dart (`def-bipolar-bdy`, -/
  tail_iff : ∀ d, B'.map.tail (toEquiv d) ↔ B.map.tail d
  

  outer_iff : ∀ d, B'.map.IsOuter (toEquiv d) ↔ B.map.IsOuter d
  /-- Carry the source rotation-cycle vertex to the source -/
  source_map : ∀ d, (dartTailVertex B.map d = B.source) ↔
    (dartTailVertex B'.map (toEquiv d) = B'.source)
  /-- Carry the sink rotation-cycle vertex to the sink -/
  sink_map : ∀ d, (dartTailVertex B.map d = B.sink) ↔
    (dartTailVertex B'.map (toEquiv d) = B'.sink)
  /-- Preserve the left boundary as an ordered dart path -/
  leftDarts : B.leftPath.darts.map toEquiv = B'.leftPath.darts
  /-- Preserve the right boundary as an ordered dart path -/
  rightDarts : B.rightPath.darts.map toEquiv = B'.rightPath.darts

namespace BipolarBoundaryBaseIso

variable {B : BipolarTriangulationWithBoundaryBase D ℓ r}
  {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}

/-- The vertex equivalence induced by the dart map. Helper toward `thm-kmsw` -/
@[expose] noncomputable def vertexEquiv (I : BipolarBoundaryBaseIso B B') :
    MapVertex B.map ≃ MapVertex B'.map :=
  bipolarBoundaryVertexEquiv B B' I.toEquiv I.rot_comm

/-- The induced vertex equivalence sends each dart's initial vertex to that
of its image. Helper toward `thm-kmsw` and `lem-lr-ind`; not the paper -/
theorem vertexEquiv_dartTailVertex (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.vertexEquiv (dartTailVertex B.map d) =
      dartTailVertex B'.map (I.toEquiv d) := by
  simp [dartTailVertex, vertexEquiv, bipolarBoundaryVertexEquiv]

/-- The induced vertex equivalence sends each dart's terminal vertex to that
of its image. Helper toward `thm-kmsw` and `lem-lr-ind`; not the paper -/
theorem vertexEquiv_dartHeadVertex (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.vertexEquiv (dartHeadVertex B.map d) =
      dartHeadVertex B'.map (I.toEquiv d) := by
  simp [dartHeadVertex, vertexEquiv, bipolarBoundaryVertexEquiv, I.edgeInv_comm]

/-- The induced vertex equivalence sends source to source. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem vertexEquiv_source (I : BipolarBoundaryBaseIso B B') :
    I.vertexEquiv B.source = B'.source := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep B.source
  change Quotient.mk _ d = B.source at hd
  have hd' := (I.source_map d).mp hd
  calc
    I.vertexEquiv B.source = I.vertexEquiv (dartTailVertex B.map d) :=
      congrArg I.vertexEquiv hd.symm
    _ = dartTailVertex B'.map (I.toEquiv d) := I.vertexEquiv_dartTailVertex d
    _ = B'.source := hd'

/-- The induced vertex equivalence sends sink to sink. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem vertexEquiv_sink (I : BipolarBoundaryBaseIso B B') :
    I.vertexEquiv B.sink = B'.sink := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep B.sink
  change Quotient.mk _ d = B.sink at hd
  have hd' := (I.sink_map d).mp hd
  calc
    I.vertexEquiv B.sink = I.vertexEquiv (dartTailVertex B.map d) :=
      congrArg I.vertexEquiv hd.symm
    _ = dartTailVertex B'.map (I.toEquiv d) := I.vertexEquiv_dartTailVertex d
    _ = B'.sink := hd'

private theorem rot_symm_comm (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.rot.symm d) =
      B'.map.toCombinatorialMap.rot.symm (I.toEquiv d) := by
  apply B'.map.toCombinatorialMap.rot.injective
  calc
    B'.map.toCombinatorialMap.rot
        (I.toEquiv (B.map.toCombinatorialMap.rot.symm d)) =
        I.toEquiv (B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.rot.symm d)) := (I.rot_comm _).symm
    _ = I.toEquiv d := by simp
    _ = B'.map.toCombinatorialMap.rot
        (B'.map.toCombinatorialMap.rot.symm (I.toEquiv d)) := by simp

/-- The face permutation commutes with the isomorphism, so every face orbit
is carried to a face orbit. Helper toward `thm-kmsw` and `lem-lr-ind`; not -/
theorem faceSucc_comm (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.faceSucc d) =
      B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) := by
  simp [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    rot_symm_comm I, I.edgeInv_comm]

private theorem faceCycle_map (I : BipolarBoundaryBaseIso B B') {x y : D}
    (h : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc x y) :
    Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      (I.toEquiv x) (I.toEquiv y) :=
  sameCycle_map I.toEquiv B.map.toCombinatorialMap.faceSucc
    B'.map.toCombinatorialMap.faceSucc I.faceSucc_comm h

/-- The dart equivalence induces an equivalence of edge orbits, retaining
parallel edges and loops. Helper toward `thm-kmsw` and `lem-lr-ind`; not the -/
@[expose] noncomputable def edgeEquiv (I : BipolarBoundaryBaseIso B B') :
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
      have hcomm : ∀ d,
          I.toEquiv.symm (B'.map.toCombinatorialMap.edgeInv d) =
            B.map.toCombinatorialMap.edgeInv (I.toEquiv.symm d) := by
        intro d
        simpa using
          (congrArg I.toEquiv.symm
            (I.edgeInv_comm (I.toEquiv.symm d))).symm
      exact sameCycle_map I.toEquiv.symm B'.map.toCombinatorialMap.edgeInv
        B.map.toCombinatorialMap.edgeInv hcomm h)
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

/-- The dart equivalence induces an equivalence of face orbits. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
@[expose] noncomputable def faceEquiv (I : BipolarBoundaryBaseIso B B') :
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
          (congrArg I.toEquiv.symm
            (I.faceSucc_comm (I.toEquiv.symm d))).symm
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

/-- Isomorphic base maps have the same number of vertices. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem numVertices_eq (I : BipolarBoundaryBaseIso B B') :
    B.map.toCombinatorialMap.numVertices =
      B'.map.toCombinatorialMap.numVertices := by
  classical
  unfold CombinatorialMap.numVertices
  exact Fintype.card_congr I.vertexEquiv

/-- Isomorphic base maps have the same number of edges. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem numEdges_eq (I : BipolarBoundaryBaseIso B B') :
    B.map.toCombinatorialMap.numEdges =
      B'.map.toCombinatorialMap.numEdges := by
  classical
  unfold CombinatorialMap.numEdges
  exact Fintype.card_congr I.edgeEquiv

/-- Isomorphic base maps have the same number of faces. Helper toward
`thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem numFaces_eq (I : BipolarBoundaryBaseIso B B') :
    B.map.toCombinatorialMap.numFaces =
      B'.map.toCombinatorialMap.numFaces := by
  classical
  unfold CombinatorialMap.numFaces
  exact Fintype.card_congr I.faceEquiv

/-- Isomorphic base maps have the same number of inner faces, excluding the
exterior face. Helper toward `thm-kmsw` and `lem-lr-ind`; not the paper -/
theorem numInnerFaces_eq (I : BipolarBoundaryBaseIso B B') :
    B.map.numInnerFaces = B'.map.numInnerFaces := by
  unfold DirectedMapWithMissing.numInnerFaces
  rw [I.numFaces_eq]

/-- Invert a base boundary isomorphism. Helper toward `thm-kmsw` and
`lem-lr-ind`; not the paper result (`def-bipolar-bdy`, -/
@[expose] def symm (I : BipolarBoundaryBaseIso B B') :
    BipolarBoundaryBaseIso B' B where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    simpa using (congrArg I.toEquiv.symm
      (I.rot_comm (I.toEquiv.symm d))).symm
  edgeInv_comm := by
    intro d
    simpa using (congrArg I.toEquiv.symm
      (I.edgeInv_comm (I.toEquiv.symm d))).symm
  missing_iff := by
    intro d
    simpa using (I.missing_iff (I.toEquiv.symm d)).symm
  tail_iff := by
    intro d
    simpa using (I.tail_iff (I.toEquiv.symm d)).symm
  outer_iff := by
    intro d
    simpa using (I.outer_iff (I.toEquiv.symm d)).symm
  source_map := by
    intro d
    simpa using (I.source_map (I.toEquiv.symm d)).symm
  sink_map := by
    intro d
    simpa using (I.sink_map (I.toEquiv.symm d)).symm
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

/-- Compose base boundary isomorphisms. Helper toward `thm-kmsw` and
`lem-lr-ind`; not the paper result (`def-bipolar-bdy`, -/
@[expose] def trans {D'' : Type*} [Fintype D''] [DecidableEq D'']
    {B'' : BipolarTriangulationWithBoundaryBase D'' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (J : BipolarBoundaryBaseIso B' B'') :
    BipolarBoundaryBaseIso B B'' where
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
  outer_iff := by
    intro d
    exact (J.outer_iff (I.toEquiv d)).trans (I.outer_iff d)
  source_map := by
    intro d
    exact (I.source_map d).trans (J.source_map (I.toEquiv d))
  sink_map := by
    intro d
    exact (I.sink_map d).trans (J.sink_map (I.toEquiv d))
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

/-- The identity base boundary isomorphism. Helper toward `thm-kmsw` and
`lem-lr-ind`; not the paper result (`def-bipolar-bdy`, -/
@[expose] def refl (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    BipolarBoundaryBaseIso B B where
  toEquiv := Equiv.refl D
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by intro d; rfl
  tail_iff := by intro d; rfl
  outer_iff := by intro d; rfl
  source_map := by intro d; rfl
  sink_map := by intro d; rfl
  leftDarts := by simp
  rightDarts := by simp

/-- Boundary isomorphism on the base carrier for the fixed-dart setoid.
Helper toward `thm-kmsw` and `lem-lr-ind`; not the paper result -/
theorem equivalence (D : Type*) [Fintype D] [DecidableEq D] (ℓ r : ℕ) :
    Equivalence (fun B B' : BipolarTriangulationWithBoundaryBase D ℓ r =>
      Nonempty (BipolarBoundaryBaseIso B B')) where
  refl B := ⟨BipolarBoundaryBaseIso.refl B⟩
  symm h := h.elim (fun I => ⟨I.symm⟩)
  trans h₁ h₂ := h₁.elim fun I => h₂.elim fun J => ⟨I.trans J⟩

/-- A strong-carrier isomorphism induces an isomorphism of the underlying
general base carriers. This forgets both the extra disjointness proofs and
the outer-word representative; it is a helper toward `thm-kmsw` and -/
@[expose] def toBase
    {C : BipolarTriangulationWithBoundary D ℓ r}
    {C' : BipolarTriangulationWithBoundary D' ℓ r}
    (I : BipolarBoundaryIso C C') :
    BipolarBoundaryBaseIso C.toBase C'.toBase where
  toEquiv := I.toEquiv
  rot_comm := I.rot_comm
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  outer_iff := by
    intro d
    change Equiv.Perm.SameCycle C'.map.toCombinatorialMap.faceSucc
        C'.map.outer (I.toEquiv d) ↔
      Equiv.Perm.SameCycle C.map.toCombinatorialMap.faceSucc C.map.outer d
    constructor
    · intro h
      have hcomm : ∀ x,
          I.toEquiv.symm (C'.map.toCombinatorialMap.faceSucc x) =
            C.map.toCombinatorialMap.faceSucc (I.toEquiv.symm x) := by
        intro x
        simpa using
          (congrArg I.toEquiv.symm
            (I.faceSucc_comm (I.toEquiv.symm x))).symm
      simpa using sameCycle_map I.toEquiv.symm C'.map.toCombinatorialMap.faceSucc
        C.map.toCombinatorialMap.faceSucc hcomm (I.outer_face.trans h)
    · intro h
      exact I.outer_face.symm.trans
        (sameCycle_map I.toEquiv C.map.toCombinatorialMap.faceSucc
          C'.map.toCombinatorialMap.faceSucc I.faceSucc_comm h)
  source_map := by
    intro d
    change (dartTailVertex C.map d = C.source) ↔
      (dartTailVertex C'.map (I.toEquiv d) = C'.source)
    constructor
    · intro hd
      have h := I.vertexEquiv_dartTailVertex d
      rw [hd, I.vertexEquiv_source] at h
      exact h.symm
    · intro hd
      apply I.vertexEquiv.injective
      rw [I.vertexEquiv_dartTailVertex, I.vertexEquiv_source]
      exact hd
  sink_map := by
    intro d
    change (dartTailVertex C.map d = C.sink) ↔
      (dartTailVertex C'.map (I.toEquiv d) = C'.sink)
    constructor
    · intro hd
      have h := I.vertexEquiv_dartTailVertex d
      rw [hd, I.vertexEquiv_sink] at h
      exact h.symm
    · intro hd
      apply I.vertexEquiv.injective
      rw [I.vertexEquiv_dartTailVertex, I.vertexEquiv_sink]
      exact hd
  leftDarts := I.leftDarts
  rightDarts := I.rightDarts

end BipolarBoundaryBaseIso
end DirectedDistances.PlanarMap
