/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry3

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: every vertex of the finite boundary
representative is the tail vertex of a dart. -/
theorem boundaryChanneled_dartTailVertex_surjective
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) :
    Function.Surjective (dartTailVertex R.B.map) := by
  intro v
  exact ⟨v.out, Quotient.out_eq v⟩

/-- Helper toward Definition 3.2: bordering a geometric face is constant
on each combinatorial face-successor cycle. This propagation does not
identify which cycle is unbounded. -/
theorem boundaryChanneled_dartBorders_sameCycle_iff
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (d e : Fin R.dartCount)
    (h : R.B.map.toCombinatorialMap.faceSucc.SameCycle d e) (F : G.Face) :
    G.dartBorders d F ↔ G.dartBorders e F := by
  let B : D39FiniteBall := {
    D := Fin R.dartCount
    map := R.B.map.toCombinatorialMap
    missing := R.B.map.missing
    tail := R.B.map.tail
    rootDart := R.B.map.outer
    original := Set.univ
    original_closed := by intro x; simp only [Set.mem_univ]
  }
  have hvert := boundaryChanneled_dartTailVertex_surjective R
  have hfaces := B.plDartFace_eq_of_sameCycle (dartTailVertex R.B.map) G hvert d e h
  rw [← B.plDartFace_eq_iff (dartTailVertex R.B.map) G hvert d F,
    ← B.plDartFace_eq_iff (dartTailVertex R.B.map) G hvert e F, hfaces]

/-- Helper toward Definition 3.2: the marked combinatorial outer cycle
does identify a unique geometric face. Unboundedness of this face is a
separate obligation, absent from the drawing alias. -/
theorem boundaryChanneled_existsUnique_markedOuterFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    ∃! F : G.Face, ∀ d : Fin R.dartCount,
      G.dartBorders d F ↔ R.B.map.IsOuter d := by
  let B : D39FiniteBall := {
    D := Fin R.dartCount
    map := R.B.map.toCombinatorialMap
    missing := R.B.map.missing
    tail := R.B.map.tail
    rootDart := R.B.map.outer
    original := Set.univ
    original_closed := by intro x; simp only [Set.mem_univ]
  }
  have hvert := boundaryChanneled_dartTailVertex_surjective R
  have hconn : ∀ x y : B.D, Relation.EqvGen
      (fun a b => B.map.rot a = b ∨ B.map.edgeInv a = b) x y := by
    intro x y
    have hpath := R.B.planar.1 x y
    refine Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => Relation.EqvGen
        (fun p q => B.map.rot p = q ∨ B.map.edgeInv p = q) a y)
      hpath (Relation.EqvGen.refl y) ?_
    intro a b hab _ ih
    have hstep : Relation.EqvGen
        (fun p q => B.map.rot p = q ∨ B.map.edgeInv p = q) a b := by
      rcases hab with hab | hab | hab | hab
      · exact Relation.EqvGen.rel _ _ (Or.inl hab.symm)
      · exact (Relation.EqvGen.rel b a
          (Or.inl (by rw [hab, Equiv.apply_symm_apply]))).symm
      · exact Relation.EqvGen.rel _ _ (Or.inr hab.symm)
      · exact (Relation.EqvGen.rel b a
          (Or.inr (by rw [hab, Equiv.apply_symm_apply]))).symm
    exact hstep.trans _ _ _ ih
  let O : D39BallFaceCycleOrbit B :=
    ⟨{d | B.map.faceSucc.SameCycle R.B.map.outer d}, R.B.map.outer, rfl⟩
  let F := B.plOrbitFace (dartTailVertex R.B.map) G hvert O
  have hborder (d : Fin R.dartCount) :
      G.dartBorders d F ↔ R.B.map.IsOuter d :=
    B.dartBorders_plOrbitFace_iff (dartTailVertex R.B.map) G hvert hconn O d
  refine ⟨F, hborder, ?_⟩
  intro U hU
  have hout : R.B.map.IsOuter R.B.map.outer := Equiv.Perm.SameCycle.rfl
  exact G.dartBorders_face_unique R.B.map.outer U F
    ((hU _).mpr hout) ((hborder _).mpr hout)









































































































end DirectedDistances.PaperProofs.Section3

end
end
