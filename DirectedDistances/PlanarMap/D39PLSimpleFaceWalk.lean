/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLCutVertexFace2
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12

/-! # Simple face walks toward Proposition 5.16

The orbit image and repeated-vertex consequences are recorded here for the
finite PL drawing. Geometric injectivity is a separate obligation. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the minimal-period face walk has image
exactly the union of the closed arcs in its face-successor orbit. -/
theorem faceWalkPolyline_image_eq_plOrbitBoundary {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (O : D39BallFaceCycleOrbit B) (d : B.D) (hd : d ∈ O.val) :
    (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).image =
      B.plOrbitBoundary vert P O := by
  let f : B.D → B.D := B.map.faceSucc
  let m := Function.minimalPeriod f d
  apply Set.Subset.antisymm
  · exact B.image_faceWalkPolyline_subset_plOrbitBoundary vert P O d hd (m - 1)
  · intro z hz
    change z ∈ ⋃ e ∈ O.val, (P.arc e).image at hz
    obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
    obtain ⟨e₀, hO⟩ := O.property
    have hed : B.map.faceSucc.SameCycle e₀ d := by
      simpa only [hO, Set.mem_ofPred_eq] using hd
    have hde : B.map.faceSucc.SameCycle d e := hed.symm.trans (by
      simpa only [hO, Set.mem_ofPred_eq] using he)
    obtain ⟨i, hi⟩ := hde.exists_nat_pow_eq
    have hm : 0 < m := by
      change 0 < Function.minimalPeriod f d
      have hperiod : Function.IsPeriodicPt f (orderOf B.map.faceSucc) d := by
        change f^[orderOf B.map.faceSucc] d = d
        have hpow := congrArg (fun σ : Equiv.Perm B.D => σ d)
          (pow_orderOf_eq_one B.map.faceSucc)
        change (B.map.faceSucc ^ orderOf B.map.faceSucc) d = d at hpow
        simpa only [Equiv.Perm.coe_pow] using hpow
      exact Function.IsPeriodicPt.minimalPeriod_pos
        (orderOf_pos B.map.faceSucc) hperiod
    have hmod := Function.iterate_mod_minimalPeriod_eq (f := f) (x := d) (n := i)
    let j := i % m
    have hj : j < m := Nat.mod_lt _ hm
    have hiter : f^[i] d = e := by
      simpa only [Equiv.Perm.coe_pow] using hi
    have hindex : f^[j] d = e := hmod.trans hiter
    rw [image_faceWalkPolyline]
    change ∃ k, k ≤ m - 1 ∧ z ∈ (P.arc (f^[k] d)).image
    refine ⟨j, by omega, ?_⟩
    rw [hindex]
    exact hze

/-- Helper toward Proposition 5.16: with no cut vertices, the darts before
completion of a face-successor cycle have distinct initial vertices. -/
theorem faceWalk_iterate_initialVertex_injective_of_noCutVertex {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hnocut : ∀ v, ¬ B.map.isCutVertex v) (d : B.D) :
    ∀ i j : ℕ,
      i < j → j < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      vert ((B.map.faceSucc : B.D → B.D)^[i] d) ≠
        vert ((B.map.faceSucc : B.D → B.D)^[j] d) := by
  intro i j hij hj hvertices
  apply hnocut (vertexClass B.map ((B.map.faceSucc : B.D → B.D)^[i] d))
  exact B.faceWalk_repeatedVertex_isCutVertex vert P d i j hij hj
    (Quotient.sound (P.rot_sameCycle_of_vert_eq _ _ hvertices))

/-- Helper toward Proposition 5.16: a face-walk polyline with `n + 1`
arcs has at least `n + 2` listed points. -/
private theorem faceWalkPolyline_points_length_ge {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) :
    ∀ n : ℕ, n + 2 ≤ (faceWalkPolyline B vert P d n).points.length := by
  intro n
  induction n with
  | zero => simpa only [faceWalkPolyline] using P.arc_length d
  | succ n ih =>
      rw [faceWalkPolyline, Polyline.length_boundaryConcat]
      have hlen := P.arc_length ((B.map.faceSucc : B.D → B.D)^[n + 1] d)
      omega

/-- Helper toward Proposition 5.16: the full minimal-period face walk is
closed. -/
theorem faceWalkPolyline_fullPeriod_closed {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) :
    let m := Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d
    (faceWalkPolyline B vert P d (m - 1)).start =
      (faceWalkPolyline B vert P d (m - 1)).finish := by
  dsimp
  exact faceWalkPolyline_closed B vert P d

/-- Helper toward Proposition 5.16: at least three darts in a full
face-successor period give at least four listed polyline points. -/
theorem faceWalkPolyline_fullPeriod_points_length_ge_four {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D)
    (hperiod : 3 ≤ Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d) :
    4 ≤ (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).points.length := by
  let m := Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d
  change 4 ≤ (faceWalkPolyline B vert P d (m - 1)).points.length
  change 3 ≤ m at hperiod
  have hlen := faceWalkPolyline_points_length_ge B vert P d (m - 1)
  omega

end D39FiniteBall

end DirectedDistances.PlanarMap




























































end
