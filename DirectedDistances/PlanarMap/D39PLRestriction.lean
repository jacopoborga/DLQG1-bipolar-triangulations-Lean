module

public import DirectedDistances.PlanarMap.D39PLCornerSector
public import DirectedDistances.PlanarMap.EdgeRestrictedDrawing

/-! # Restricting a finite plane drawing to a flip-closed dart set -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Proposition 5.16: the first-return rotation of the
original rotation on a set of retained dart identities. -/
@[expose] noncomputable def firstReturnRot {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D) :
    Equiv.Perm (RestrictedDart D S) :=
  drawingFirstReturnPerm P S

/-- Helper toward Proposition 5.16: first return preserves the original
vertex of each dart. -/
theorem firstReturnRot_sameVertex {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : RestrictedDart D S) :
    vert ((firstReturnRot P S d).1) = vert d.1 :=
  drawingFirstReturn_sameVertex P S d

/-- Helper toward Proposition 5.16: every first-return dart lies in the
original rotation cycle of its starting dart. -/
theorem firstReturnRot_sameCycle {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : RestrictedDart D S) :
    Equiv.Perm.SameCycle rot d.1 (firstReturnRot P S d).1 :=
  drawingFirstReturn_sameCycle P S d

/-- Helper toward Proposition 5.16: if the original rotation successor is
retained, it remains the first-return successor. -/
theorem firstReturnRot_eq_rot_of_mem {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : RestrictedDart D S) (h : rot d.1 ∈ S) :
    (firstReturnRot P S d).1 = rot d.1 :=
  drawingFirstReturn_eq_next P S d h

/-- Helper toward Proposition 5.16: a counterclockwise successor remains a
successor after restricting its star to a subset containing both darts. -/
theorem ccwSuccessor_of_subset {D : Type*} (star T : Set D)
    (dir : D → ℂ) (d e : D)
    (hsub : T ⊆ star) (hd : d ∈ T) (he : e ∈ T)
    (hsucc : CcwSuccessor star dir d e) : CcwSuccessor T dir d e := by
  rcases hsucc with ⟨hfinite, _, _, hcase⟩
  refine ⟨hfinite.subset hsub, hd, he, ?_⟩
  rcases hcase with hsingle | hminimal
  · left
    refine ⟨hsingle.1, ?_⟩
    apply Set.ext
    intro x
    constructor
    · intro hx
      have hx' := hsub hx
      rw [hsingle.2] at hx'
      exact hx'
    · intro hx
      have : x = d := Set.mem_singleton_iff.mp hx
      subst x
      exact hd
  · right
    refine ⟨hminimal.1, ?_⟩
    intro f hf hfd
    exact hminimal.2 f (hsub hf) hfd

/-- Helper toward Proposition 5.16: the first-return dart is the
counterclockwise successor in the retained part of its vertex star. This
records explicitly how deleting intervening darts restricts a `CcwSuccessor`. -/
theorem firstReturnRot_ccwSuccessor {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : RestrictedDart D S) :
    CcwSuccessor {e : D | e ∈ S ∧ vert e = vert d.1}
      (fun e => (P.arc e).initialDirection) d.1 (firstReturnRot P S d).1 := by
  exact drawingFirstReturnCcwObligation_holds P S d

/-- Helper toward Proposition 5.16: one-way flip closure is equivalent to
two-way closure because the dart reversal is an involution. -/
theorem flipClosed_iff {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S → flip d ∈ S) :
    ∀ d, d ∈ S ↔ flip d ∈ S := by
  intro d
  constructor
  · exact hS d
  · intro h
    have h' := hS (flip d) h
    simpa [P.flip_involutive d] using h'

/-- Helper toward Proposition 5.16: restrict a finite plane drawing to a
flip-closed dart set, retaining the original vertex type and positions. -/
@[expose] noncomputable def firstReturnDrawing {D V : Type*} [Finite D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S → flip d ∈ S) :
    PLDrawing (RestrictedDart D S) V (restrictedFlip P S (flipClosed_iff P S hS))
      (firstReturnRot P S) (fun d => vert d.1) := by
  classical
  letI : Finite (RestrictedDart D S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (RestrictedDart D S) := Fintype.ofFinite _
  refine {
    flip_involutive := ?_
    flip_ne := ?_
    vert_rotation := ?_
    pos := P.pos
    pos_injective := P.pos_injective
    arc := fun d => P.arc d.1
    arc_simple := fun d => P.arc_simple d.1
    arc_length := fun d => P.arc_length d.1
    arc_start := fun d => P.arc_start d.1
    arc_finish := fun d => P.arc_finish d.1
    arc_flip := ?_
    interior_disjoint := ?_
    interior_avoids_vertices := fun d v => P.interior_avoids_vertices d.1 v
    locally_finite := ?_
    initial_nonzero := fun d => P.initial_nonzero d.1
    initial_arg_injective := ?_
    rotation_agreement := ?_
  }
  · intro d
    apply Subtype.ext
    exact P.flip_involutive d.1
  · intro d h
    apply P.flip_ne d.1
    exact congrArg Subtype.val h
  · intro d
    exact firstReturnRot_sameVertex P S d
  · intro d
    change P.arc (flip d.1) = (P.arc d.1).reverse
    exact P.arc_flip d.1
  · intro d e hed hef
    apply P.interior_disjoint d.1 e.1
    · intro h
      exact hed (Subtype.ext h)
    · intro h
      apply hef
      apply Subtype.ext
      change e.1 = flip d.1 at h
      exact h
  · intro K hK
    exact Set.toFinite _
  · intro d e hvert harg
    apply Subtype.ext
    apply P.initial_arg_injective d.1 e.1
    · exact hvert
    · exact harg
  · intro d
    have hc := firstReturnRot_ccwSuccessor P S d
    unfold CcwSuccessor
    rcases hc with ⟨_, hd, hr, hcase⟩
    refine ⟨Set.toFinite _, ?_, ?_, ?_⟩
    · rfl
    · exact firstReturnRot_sameVertex P S d
    · rcases hcase with hsingle | hminimal
      · left
        refine ⟨?_, ?_⟩
        · apply Subtype.ext
          exact hsingle.1
        · apply Set.ext
          intro e
          constructor
          · intro he
            have heBase : e.1 ∈ {x : D | x ∈ S ∧ vert x = vert d.1} :=
              ⟨e.2, he⟩
            rw [hsingle.2] at heBase
            exact Subtype.ext (Set.mem_singleton_iff.mp heBase)
          · intro he
            have he' : e = d := by
              exact Set.mem_singleton_iff.mp
                (show e ∈ ({d} : Set (RestrictedDart D S)) from he)
            subst e
            rfl
      · right
        refine ⟨?_, ?_⟩
        · intro he
          exact hminimal.1 (congrArg Subtype.val he)
        · intro e he heq
          apply hminimal.2 e.1 ⟨e.2, he⟩
          · intro h
            exact heq (Subtype.ext h)

/-- Helper toward Proposition 5.16: the image of the restricted drawing is
the original vertex-position range together with exactly the retained arcs. -/
theorem firstReturnDrawing_image_eq {D V : Type*} [Finite D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S → flip d ∈ S) :
    (firstReturnDrawing P S hS).image =
      Set.range P.pos ∪
        {z | ∃ d : RestrictedDart D S, z ∈ (P.arc d.1).image} := by
  simp [PLDrawing.image, firstReturnDrawing]

/-- Helper toward Proposition 5.16: the restricted rotation and edge
reversal form the combinatorial map on the retained dart subtype. -/
@[expose] noncomputable def firstReturnCombinatorialMap {D V : Type*}
    [Finite D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S → flip d ∈ S)
    [Fintype (RestrictedDart D S)] [DecidableEq (RestrictedDart D S)] :
    CombinatorialMap (RestrictedDart D S) := by
  classical
  refine {
    edgeInv := {
      toFun := restrictedFlip P S (flipClosed_iff P S hS)
      invFun := restrictedFlip P S (flipClosed_iff P S hS)
      left_inv := ?_
      right_inv := ?_
    }
    edgeInv_invol := ?_
    edgeInv_ne := ?_
    rot := firstReturnRot P S
  }
  · intro d
    apply Subtype.ext
    exact P.flip_involutive d.1
  · intro d
    apply Subtype.ext
    exact P.flip_involutive d.1
  · intro d
    apply Subtype.ext
    exact P.flip_involutive d.1
  · intro d h
    apply P.flip_ne d.1
    exact congrArg Subtype.val h

end DirectedDistances.PlanarMap
