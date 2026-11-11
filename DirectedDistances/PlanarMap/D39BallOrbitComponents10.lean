/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents9









public section
noncomputable section
namespace DirectedDistances.PlanarMap

namespace Polyline

/-- Helper toward Proposition 5.16: a nontrivial simple interval polyline
has distinct endpoints, by injectivity of its traversal. -/
theorem start_ne_finish_of_isSimple (p : Polyline)
    (hlen : 2 ≤ p.points.length) (hp : p.IsSimple) : p.start ≠ p.finish := by
  intro heq
  have hpath : p.toPath 0 = p.toPath 1 := by
    rw [Path.source, Path.target]
    exact heq
  exact zero_ne_one (p.toPath_injective hlen hp hpath)

end Polyline

namespace PLDrawing

/-- Helper toward Proposition 5.16: every edge in the current drawing
carrier has distinct incident vertices; in particular loops are excluded. -/
theorem vert_ne_flip {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (d : D) :
    vert d ≠ vert (flip d) := by
  intro heq
  apply (P.arc d).start_ne_finish_of_isSimple (P.arc_length d) (P.arc_simple d)
  rw [P.arc_start, P.arc_finish, heq]

/-- Helper toward Proposition 5.16: the arc fields cannot supply cyclic
simplicity for the proposed loop base, since such an arc would be closed. -/
theorem not_isCyclicSimple_arc {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (d : D) :
    ¬ (P.arc d).IsCyclicSimple := by
  intro hc
  apply (P.arc d).start_ne_finish_of_isSimple (P.arc_length d) (P.arc_simple d)
  rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
  exact hc.2.1

end PLDrawing

namespace CombinatorialMap

/-- Helper toward Proposition 5.16: both darts of the single loop are
fixed by `faceSucc = rot⁻¹ * edgeInv`. -/
theorem oneLoopDeletionCounterexample_faceSucc :
    oneLoopDeletionCounterexample.faceSucc = 1 := by
  ext d
  cases d <;> rfl

/-- Helper toward Proposition 5.16: the two face-successor orbits of
the single loop are exactly its two singleton dart sets. -/
theorem oneLoopDeletionCounterexample_face_sameCycle_iff (d e : Bool) :
    oneLoopDeletionCounterexample.faceSucc.SameCycle d e ↔ d = e := by
  rw [oneLoopDeletionCounterexample_faceSucc]
  exact Equiv.Perm.sameCycle_one

/-- Helper toward Proposition 5.16: the single loop has two combinatorial
faces, each represented by one of its darts. -/
theorem oneLoopDeletionCounterexample_numFaces :
    oneLoopDeletionCounterexample.numFaces = 2 := by
  classical
  let e : FaceQuotient oneLoopDeletionCounterexample ≃ Bool :=
    { toFun := Quotient.lift id (fun d e h =>
        (oneLoopDeletionCounterexample_face_sameCycle_iff d e).mp h)
      invFun := fun d => Quotient.mk _ d
      left_inv := by
        intro q
        induction q using Quotient.inductionOn with
        | _ d => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (by decide)

/-- Helper toward Proposition 5.16: the single loop has combinatorial
Euler characteristic `1 - 1 + 2 = 2`, without any drawing premise. -/
theorem oneLoopDeletionCounterexample_eulerChar :
    oneLoopDeletionCounterexample.eulerChar = 2 := by
  rw [eulerChar, oneLoopDeletionCounterexample_numVertices,
    oneLoopDeletionCounterexample_numEdges, oneLoopDeletionCounterexample_numFaces]
  norm_num

/-- Helper toward Proposition 5.16: no incidence function realizes the
single-loop rotation system as a drawing of the present interval-arc type. -/
theorem oneLoopDeletionCounterexample_not_nonempty_plDrawing
    {V : Type*} (vert : Bool → V) :
    ¬ Nonempty (PLDrawing Bool V oneLoopDeletionCounterexample.edgeInv
      oneLoopDeletionCounterexample.rot vert) := by
  rintro ⟨P⟩
  apply P.vert_ne_flip false
  exact (P.vert_rotation false).symm

end CombinatorialMap
end DirectedDistances.PlanarMap
end








































































































