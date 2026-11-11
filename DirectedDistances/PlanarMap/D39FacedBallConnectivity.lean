module

public import DirectedDistances.PlanarMap.D39FacedBallClass

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- Helper toward Proposition 5.16. A rotation-cycle pair is connected by forward
rotation steps, hence also by the equivalence closure of rotation and edge reversal. -/
private theorem d39EqvGen_of_sameCycle {α : Type*} [Finite α]
    (rot edgeInv : Equiv.Perm α) (x y : α)
    (h : rot.SameCycle x y) :
    Relation.EqvGen (fun a b => rot a = b ∨ edgeInv a = b) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  clear hn
  induction n with
  | zero => exact Relation.EqvGen.refl x
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.rel _ _ (Or.inl rfl))

/-- Helper toward Proposition 5.16. Ambient vertex-radius reachability persists -/
private theorem d39FacedBall_ambient_mono (M : D39RootedMap)
    {r s : ℕ} (hrs : r ≤ s) {v} (h : D39WithinRadius M r v) :
    D39WithinRadius M s v :=
  (mem_d39BallVertices M s v).1
    (d39BallVertices_mono M hrs ((mem_d39BallVertices M r v).2 h))

/-- Helper toward Proposition 5.16. Ambient vertex-radius reachability lifts to
the corresponding finite faced ball whenever the radius is no larger than the -/
private theorem d39FacedBall_ambient_to_within (M : D39RootedMap)
    (s : ℕ) (hs : 0 < s) {n v}
    (h : D39WithinRadius M n v)
    (hn : n ≤ s) (d : (d39FacedBall M s hs).D)
    (hd : d39VertexClass M d.1 = v) :
    D39FiniteBallWithinRadius (d39FacedBall M s hs) n d := by
  classical
  let B := d39FacedBall M s hs
  induction h generalizing d with
  | root =>
      apply D39FiniteBallWithinRadius.root
      exact (d39Ball_rot_sameCycle_iff M s _ _).2 (Quotient.exact hd).symm
  | stay hp ih => exact .stay (ih (by omega) d hd)
  | @edge n v w hp he ih =>
      obtain ⟨e, hev, hew⟩ := he
      have heS : e ∈ d39BallDarts M s := by
        apply (mem_d39BallDarts M s e).2
        constructor
        · exact (mem_d39BallVertices M s _).2
            (d39FacedBall_ambient_mono M (by omega) (hev.symm ▸ hp))
        · exact (mem_d39BallVertices M s _).2
            (d39FacedBall_ambient_mono M hn
              (D39WithinRadius.edge hp ⟨e, hev, rfl⟩))
      let e' : B.D := ⟨e, heS⟩
      apply D39FiniteBallWithinRadius.edge (ih (by omega) e' hev)
      exact (d39Ball_rot_sameCycle_iff M s _ _).2 (Quotient.exact (hew.trans hd.symm))

/-- Helper toward Proposition 5.16. Each finite-ball radius witness gives a
rotation and edge-reversal path from the ordered root dart. -/
private theorem d39FiniteBallWithin_connected (B : D39FiniteBall) :
    ∀ {n : ℕ} {d : B.D}, D39FiniteBallWithinRadius B n d →
      Relation.EqvGen
        (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) B.rootDart d := by
  intro n d h
  induction h with
  | @root d hcycle =>
      exact d39EqvGen_of_sameCycle B.map.rot B.map.edgeInv B.rootDart d hcycle
  | @stay n d hprev ih => exact ih
  | @edge n d e hprev hcycle ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inr rfl))
          (d39EqvGen_of_sameCycle B.map.rot B.map.edgeInv
            (B.map.edgeInv d) e hcycle))

/-- Helper toward Proposition 5.16. Every dart of the faced ball is connected
to the ordered root dart by rotation and edge-reversal steps. The proof follows
the all-geometric vertex-radius induction defining the ball. -/
theorem d39FacedBall_dart_connected_to_root (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D) :
    Relation.EqvGen
      (fun x y => (d39FacedBall M r hr).map.rot x = y ∨
        (d39FacedBall M r hr).map.edgeInv x = y)
      (d39FacedBall M r hr).rootDart d := by
  classical
  let B := d39FacedBall M r hr
  let d' : B.D := d
  have hwithin : D39FiniteBallWithinRadius B r d' := by
    have hvertex : D39WithinRadius M r (d39VertexClass M d.1) :=
      (mem_d39BallVertices M r _).1
        ((mem_d39BallDarts M r d.1).1 d.2).1
    have h := d39FacedBall_ambient_to_within M r hr hvertex le_rfl d' rfl
    exact h
  change Relation.EqvGen (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y)
    B.rootDart d'
  exact d39FiniteBallWithin_connected B hwithin

/-- Helper toward Proposition 5.16. Darts representing the same ambient vertex
remain in one rotation cycle under the first-return rotation of the faced ball. -/
theorem d39FacedBall_same_vertex_rotation_connected (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r) (d e : (d39FacedBall M r hr).D)
    (h : d39VertexClass M d.1 = d39VertexClass M e.1) :
    (d39FacedBall M r hr).map.rot.SameCycle d e := by
  classical
  exact (d39Ball_rot_sameCycle_iff M r d e).2 (Quotient.exact h)

/-- Helper toward Proposition 5.16. Any two darts of a positive-radius faced
ball are connected by its restricted rotations and edge reversals. -/
theorem d39FacedBall_connected (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r) (d e : (d39FacedBall M r hr).D) :
    Relation.EqvGen
      (fun x y => (d39FacedBall M r hr).map.rot x = y ∨
        (d39FacedBall M r hr).map.edgeInv x = y) d e := by
  exact Relation.EqvGen.trans _ _ _
    (d39FacedBall_dart_connected_to_root M r hr d).symm
    (d39FacedBall_dart_connected_to_root M r hr e)

end DirectedDistances.PlanarMap
