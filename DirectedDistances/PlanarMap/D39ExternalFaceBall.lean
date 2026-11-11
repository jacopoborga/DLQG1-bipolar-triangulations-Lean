/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PlanarMap.GeneralPlaneMapFiniteExternalFace

public section

namespace DirectedDistances.PlanarMap

/-- A face-cycle orbit of a finite local topology ball, represented as its set of darts.
This is the combinatorial face data retained when the drawing is restricted
to the finite induced ball. Helper toward Definition 3.8 -/
@[expose] def D39BallFaceCycleOrbit (B : D39FiniteBall) : Type :=
  {S : Set B.D // ∃ d, S = {e | Equiv.Perm.SameCycle B.map.faceSucc d e}}

/-- A finite local topology ball with one of its face-cycle orbits marked external. The
subtype field states that the marker is an actual face-cycle orbit; it does
not assert that the orbit is unbounded. Helper toward Definition 3.8 -/
structure D39FiniteBallWithExternal where
  /-- The finite induced ball with its retained local topology data. -/
  toD39FiniteBall : D39FiniteBall
  /-- The marked external face-cycle orbit, required to be a face cycle. -/
  externalOrbit : D39BallFaceCycleOrbit toD39FiniteBall

/-- An isomorphism of finite local topology balls that preserves the marked external
face-cycle orbit. Helper toward Definition 3.8 -/
structure D39BallIsoWithExternal (B C : D39FiniteBallWithExternal) where
  /-- The underlying isomorphism preserving all other retained ball data. -/
  toD39BallIso : D39BallIso B.toD39FiniteBall C.toD39FiniteBall
  /-- The marked orbit is preserved dart by dart under the isomorphism. -/
  external_iff : ∀ d,
    toD39BallIso.toEquiv d ∈ C.externalOrbit.1 ↔ d ∈ B.externalOrbit.1

namespace D39BallIsoWithExternal

/-- Identity isomorphism preserving the marked external orbit. Helper toward -/
@[expose] def refl (B : D39FiniteBallWithExternal) : D39BallIsoWithExternal B B where
  toD39BallIso := D39BallIso.refl B.toD39FiniteBall
  external_iff := fun _ => Iff.rfl

/-- Inverse isomorphism preserving the marked external orbit. Helper toward -/
@[expose] def symm {B C : D39FiniteBallWithExternal}
    (I : D39BallIsoWithExternal B C) : D39BallIsoWithExternal C B where
  toD39BallIso := I.toD39BallIso.symm
  external_iff := by
    intro d
    have h := I.external_iff (I.toD39BallIso.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- Composition of isomorphisms preserving the marked external orbit. Helper -/
@[expose] def trans {B C E : D39FiniteBallWithExternal}
    (I : D39BallIsoWithExternal B C) (J : D39BallIsoWithExternal C E) :
    D39BallIsoWithExternal B E where
  toD39BallIso := I.toD39BallIso.trans J.toD39BallIso
  external_iff := by
    intro d
    exact (J.external_iff (I.toD39BallIso.toEquiv d)).trans (I.external_iff d)

end D39BallIsoWithExternal

/-- An explicit realization relation for the face cycles of a finite local topology ball
by the complementary components of a finite plane drawing. The equivalence
identifies every face-successor orbit with exactly one component of the
drawing image complement. In applications the drawing is the source drawing
restricted to the ball's retained vertices and induced geometric edges; this
relation is data, not a theorem that every ball admits such a realization. -/
structure D39BallFaceCycleRealization {V E : Type*} [Finite V] [Finite E]
    (B : D39FiniteBall) (D : PlaneGraphDrawing V E) where
  /-- The face-cycle orbit and complementary-face correspondence supplied by
  this realization of the finite induced ball. -/
  faceOrbitEquiv : D39BallFaceCycleOrbit B ≃ D.Face

/-- The unique unbounded component of a finite drawing selects a unique
external face-cycle orbit under an explicit realization of the ball's face
cycles. Helper toward Definition 3.8 -/
theorem D39BallFaceCycleRealization.existsUnique_externalOrbit
    {V E : Type*} [Finite V] [Finite E] (B : D39FiniteBall)
    (D : PlaneGraphDrawing V E) (R : D39BallFaceCycleRealization B D) :
    ∃! O : D39BallFaceCycleOrbit B, D.IsExternal (R.faceOrbitEquiv O) := by
  obtain ⟨F, hF, hUnique⟩ := D.existsUnique_isExternal
  refine ⟨R.faceOrbitEquiv.symm F, ?_, ?_⟩
  · simpa using hF
  intro O hO
  apply R.faceOrbitEquiv.injective
  simpa using hUnique (R.faceOrbitEquiv O) hO

/-- An isomorphism with external-face data forgets to the underlying local topology ball
isomorphism. Helper toward Definition 3.8 -/
def D39BallIsoWithExternal.forget
    {B C : D39FiniteBallWithExternal} (I : D39BallIsoWithExternal B C) :
    D39BallIso B.toD39FiniteBall C.toD39FiniteBall := I.toD39BallIso

end DirectedDistances.PlanarMap

end
