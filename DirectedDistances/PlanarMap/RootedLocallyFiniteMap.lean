/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.PaperProofs.Section3.BSTopologyDefinitionProvider

public section
namespace DirectedDistances.PlanarMap

open Equiv



abbrev RootedLocallyFiniteVertex (D : Type) (rot : Equiv.Perm D) :=
  Quotient (Equiv.Perm.SameCycle.setoid rot)



@[expose] def rootedLocallyFiniteVertexClass {D : Type}
    (rot : Equiv.Perm D) (d : D) : RootedLocallyFiniteVertex D rot :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid rot) d



@[expose] def rootedLocallyFiniteGeometricStep {D : Type}
    (rot edgeInv : Equiv.Perm D)
    (v w : RootedLocallyFiniteVertex D rot) : Prop :=
  ∃ d, rootedLocallyFiniteVertexClass rot d = v ∧
    rootedLocallyFiniteVertexClass rot (edgeInv d) = w



@[expose] def rootedLocallyFiniteDirectedStep {D : Type}
    (rot edgeInv : Equiv.Perm D) (missing tail : D → Prop)
    (v w : RootedLocallyFiniteVertex D rot) : Prop :=
  ∃ d, ¬ missing d ∧ tail d ∧
    rootedLocallyFiniteVertexClass rot d = v ∧
    rootedLocallyFiniteVertexClass rot (edgeInv d) = w





structure RootedLocallyFiniteMap where
  

  D : Type
  

  countableD : Countable D
  

  rot : Equiv.Perm D
  

  edgeInv : Equiv.Perm D
  

  edgeInv_invol : ∀ d, edgeInv (edgeInv d) = d
  

  edgeInv_ne : ∀ d, edgeInv d ≠ d
  

  missing : D → Prop
  

  missing_edgeInv : ∀ d, missing d ↔ missing (edgeInv d)
  

  tail : D → Prop
  

  tail_iff : ∀ d, ¬ missing d → (tail d ↔ ¬ tail (edgeInv d))
  

  tail_missing : ∀ d, missing d → ¬ tail d
  

  outer : D
  

  missing_outer : ∀ d, missing d →
    Equiv.Perm.SameCycle (rot.symm * edgeInv) outer d ∨
      Equiv.Perm.SameCycle (rot.symm * edgeInv) outer (edgeInv d)
  

  rootDart : D
  

  frameEdgeDart : D
  

  frameEdge_missing : missing frameEdgeDart
  

  frameEdge_at_root : rot.SameCycle rootDart frameEdgeDart
  

  frameOtherDart : Option D
  

  frameOtherDart_valid : ∀ y, frameOtherDart = some y →
    rot.SameCycle (edgeInv frameEdgeDart) y
  

  locallyFinite : ∀ d, {e : D | rot.SameCycle d e}.Finite
  

  connected : ∀ d e, Relation.ReflTransGen
    (fun x y : D => y = rot x ∨ y = rot.symm x ∨
      y = edgeInv x ∨ y = edgeInv.symm x) d e
  

  acyclic : ∀ v : RootedLocallyFiniteVertex D rot,
    ¬ Relation.TransGen (rootedLocallyFiniteDirectedStep rot edgeInv missing tail) v v



instance (M : RootedLocallyFiniteMap) : Countable M.D := M.countableD



@[expose] def rootedLocallyFiniteVertexClassOf (M : RootedLocallyFiniteMap)
    (d : M.D) : RootedLocallyFiniteVertex M.D M.rot :=
  rootedLocallyFiniteVertexClass M.rot d



@[expose] def rootedLocallyFiniteVertexDarts (M : RootedLocallyFiniteMap)
    (v : RootedLocallyFiniteVertex M.D M.rot) : Set M.D :=
  {d | rootedLocallyFiniteVertexClassOf M d = v}



theorem rootedLocallyFiniteVertexDarts_finite (M : RootedLocallyFiniteMap)
    (v : RootedLocallyFiniteVertex M.D M.rot) :
    (rootedLocallyFiniteVertexDarts M v).Finite := by
  classical
  let d := Quotient.out v
  have hd : rootedLocallyFiniteVertexClass M.rot d = v := Quotient.out_eq' v
  have heq : {e : M.D | M.rot.SameCycle d e} = rootedLocallyFiniteVertexDarts M v := by
    ext e
    constructor
    · intro he
      change rootedLocallyFiniteVertexClass M.rot e = v
      exact (Quotient.sound he).symm.trans hd
    · intro he
      change rootedLocallyFiniteVertexClass M.rot e = v at he
      exact Quotient.exact (hd.trans he.symm)
  rw [← heq]
  exact M.locallyFinite d



@[expose] noncomputable def rootedLocallyFiniteVertexDartFinset
    (M : RootedLocallyFiniteMap)
    (v : RootedLocallyFiniteVertex M.D M.rot) : Finset M.D := by
  classical
  exact (rootedLocallyFiniteVertexDarts_finite M v).toFinset



theorem mem_rootedLocallyFiniteVertexDartFinset (M : RootedLocallyFiniteMap)
    (v : RootedLocallyFiniteVertex M.D M.rot) (d : M.D) :
    d ∈ rootedLocallyFiniteVertexDartFinset M v ↔
      rootedLocallyFiniteVertexClassOf M d = v := by
  classical
  simp [rootedLocallyFiniteVertexDartFinset, rootedLocallyFiniteVertexDarts]




@[expose] noncomputable def rootedLocallyFiniteNeighbors
    (M : RootedLocallyFiniteMap)
    (v : RootedLocallyFiniteVertex M.D M.rot) :
    Finset (RootedLocallyFiniteVertex M.D M.rot) := by
  classical
  exact (rootedLocallyFiniteVertexDartFinset M v).image
    (fun d => rootedLocallyFiniteVertexClassOf M (M.edgeInv d))




theorem mem_rootedLocallyFiniteNeighbors (M : RootedLocallyFiniteMap)
    (v w : RootedLocallyFiniteVertex M.D M.rot) :
    w ∈ rootedLocallyFiniteNeighbors M v ↔
      ∃ d, rootedLocallyFiniteVertexClassOf M d = v ∧
        rootedLocallyFiniteVertexClassOf M (M.edgeInv d) = w := by
  classical
  simp [rootedLocallyFiniteNeighbors, mem_rootedLocallyFiniteVertexDartFinset]



inductive rootedLocallyFiniteWithinRadius (M : RootedLocallyFiniteMap) :
    ℕ → RootedLocallyFiniteVertex M.D M.rot → Prop
  

  | root : rootedLocallyFiniteWithinRadius M 0
      (rootedLocallyFiniteVertexClassOf M M.rootDart)
  

  | stay {r v} : rootedLocallyFiniteWithinRadius M r v →
      rootedLocallyFiniteWithinRadius M (r + 1) v
  

  | edge {r v w} : rootedLocallyFiniteWithinRadius M r v →
      rootedLocallyFiniteGeometricStep M.rot M.edgeInv v w →
      rootedLocallyFiniteWithinRadius M (r + 1) w



@[expose] noncomputable def rootedLocallyFiniteRadiusVertices
    (M : RootedLocallyFiniteMap) :
    ℕ → Finset (RootedLocallyFiniteVertex M.D M.rot)
  | 0 => by
      classical
      exact {rootedLocallyFiniteVertexClassOf M M.rootDart}
  | r + 1 => by
      classical
      exact rootedLocallyFiniteRadiusVertices M r ∪
        (rootedLocallyFiniteRadiusVertices M r).biUnion
          (rootedLocallyFiniteNeighbors M)




theorem mem_rootedLocallyFiniteRadiusVertices (M : RootedLocallyFiniteMap)
    (r : ℕ) (v : RootedLocallyFiniteVertex M.D M.rot) :
    v ∈ rootedLocallyFiniteRadiusVertices M r ↔
      rootedLocallyFiniteWithinRadius M r v := by
  classical
  induction r generalizing v with
  | zero =>
      constructor
      · intro h
        have hv : v = rootedLocallyFiniteVertexClassOf M M.rootDart := by
          simpa [rootedLocallyFiniteRadiusVertices] using h
        subst v
        exact .root
      · intro h
        cases h with
        | root => simp [rootedLocallyFiniteRadiusVertices]
  | succ r ih =>
      change v ∈ rootedLocallyFiniteRadiusVertices M r ∪
        (rootedLocallyFiniteRadiusVertices M r).biUnion
          (rootedLocallyFiniteNeighbors M) ↔ _
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact .stay ((ih v).mp h)
        · rcases Finset.mem_biUnion.mp h with ⟨u, hu, hv⟩
          rcases (mem_rootedLocallyFiniteNeighbors M u v).mp hv with
            ⟨d, hd, he⟩
          exact .edge ((ih u).mp hu) ⟨d, hd, he⟩
      · intro h
        cases h with
        | stay hprev =>
            exact Finset.mem_union_left _ ((ih v).mpr hprev)
        | edge hprev hedge =>
            apply Finset.mem_union_right
            apply Finset.mem_biUnion.mpr
            refine ⟨_, (ih _).mpr hprev, ?_⟩
            exact (mem_rootedLocallyFiniteNeighbors M _ _).mpr hedge






@[expose] noncomputable def rootedLocallyFiniteBallDarts
    (M : RootedLocallyFiniteMap) (r : ℕ) : Finset M.D := by
  classical
  let V := rootedLocallyFiniteRadiusVertices M r
  let S := V.biUnion (rootedLocallyFiniteVertexDartFinset M)
  exact S.filter fun d => rootedLocallyFiniteVertexClassOf M (M.edgeInv d) ∈ V




theorem mem_rootedLocallyFiniteBallDarts (M : RootedLocallyFiniteMap)
    (r : ℕ) (d : M.D) :
    d ∈ rootedLocallyFiniteBallDarts M r ↔
      rootedLocallyFiniteVertexClassOf M d ∈ rootedLocallyFiniteRadiusVertices M r ∧
      rootedLocallyFiniteVertexClassOf M (M.edgeInv d) ∈
        rootedLocallyFiniteRadiusVertices M r := by
  classical
  simp only [rootedLocallyFiniteBallDarts, Finset.mem_filter,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨v, hv, hd⟩, he⟩
    have hsource := (mem_rootedLocallyFiniteVertexDartFinset M v d).mp hd
    exact ⟨hsource ▸ hv, he⟩
  · rintro ⟨hd, he⟩
    refine ⟨⟨rootedLocallyFiniteVertexClassOf M d, hd, ?_⟩, he⟩
    exact (mem_rootedLocallyFiniteVertexDartFinset M _ _).mpr rfl

end DirectedDistances.PlanarMap
end
