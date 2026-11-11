/- Copyright (c) 2026 DirectedDistances contributors. All rights reserved. -/
module

public import DirectedDistances.PaperProofs.Section3.D39GeomMirror2

/-! Helper toward Proposition 5.9: double reflection of the ordered-root map.
The ordered missing-root convention is fixed by
No equality-in-law or paper-completion result is claimed here. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.9: the identity plane homeomorphism identifies
a twice reflected drawing with the original drawing, preserving edge identity,
incidences, and complete and open arcs. -/
@[expose] def PlaneGraphDrawing.geomMirrorTwiceEquiv {V E : Type*}
    (D : PlaneGraphDrawing V E) : D.HomeoEquiv D.geomMirror.geomMirror where
  h := Homeomorph.refl ℂ
  σV := Equiv.refl _
  σE := Equiv.refl _
  pos_map := by intro v; exact Complex.conj_conj _
  src_map := by intro e; rfl
  tgt_map := by intro e; rfl
  arc_range_map := by
    intro e
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨D.arc e t, ⟨t, rfl⟩, (Complex.conj_conj _).symm⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, Complex.conj_conj _⟩
  openArc_map := by
    intro e
    ext z
    constructor
    · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, Complex.conj_conj _⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨D.arc e t, ⟨t, ht, rfl⟩, (Complex.conj_conj _).symm⟩

/-- Helper toward Proposition 5.9: images of complementary faces under the
two conjugations recover their original subsets of the plane. -/
theorem PlaneGraphDrawing.geomMirror_face_twice_val {V E : Type*}
    (D : PlaneGraphDrawing V E) (F : D.Face) :
    (D.geomMirror.geomMirrorEquiv.faceEquiv
      (D.geomMirrorEquiv.faceEquiv F)).val = F.val := by
  change geomConj '' (geomConj '' F.val) = F.val
  ext z
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    change conj (conj x) ∈ F.val
    rwa [Complex.conj_conj]
  · intro hz
    exact ⟨geomConj z, ⟨z, hz, rfl⟩, Complex.conj_conj z⟩

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9: double reflection is a rooted local topology
isomorphism via the identity homeomorphism. It preserves every vertex and edge,
missing tags and all present-edge directions, and restores the ordered mark -/
@[expose] def d39GeomMirrorTwiceIso {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    D39GeomRootedMapIsoV2 M rho M.geomMirror.geomMirror
      (d39GeomMirrorRoot (d39GeomMirrorRoot rho)) where
  h := Homeomorph.refl ℂ
  orientationPreserving := orientationPreserving_refl
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  edgeFlip := fun _ => false
  edgeParam := fun _ => Homeomorph.refl _
  edgeParam_mono := by intro _ _; exact strictMono_id
  edgeParam_anti := by intro e hf; simp only [Bool.false_eq_true] at hf
  pos_map := by intro v; exact (Complex.conj_conj _).symm
  arc_map := by intro e t; exact (Complex.conj_conj _).symm
  src_map := by intro e; rfl
  tgt_map := by intro e; rfl
  missing_map := by intro e; rfl
  orientation_map := by intro e he; exact (Bool.xor_false _).symm
  root_edge_map := rfl
  root_bool_map := by simp only [d39GeomMirrorRoot_involutive, Bool.xor_false]

/-- Helper toward Proposition 5.9: after both ordered-root reversals, double
reflection restores exactly the original retained-face predicate at every
radius. This does not assert a same-radius transport for a single reversal. -/
theorem d39GeomMirror_face_twice_retained_iff {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ)
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    F ∈ d39GeomRetainedFaces M rho r ↔
      M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirror.geomMirrorEquiv.faceEquiv
        (M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv.faceEquiv F) ∈
      d39GeomRetainedFaces M.geomMirror.geomMirror
        (d39GeomMirrorRoot (d39GeomMirrorRoot rho)) r := by
  rw [d39GeomMirrorRoot_involutive]
  exact (d39GeomMirror_face_retained_iff M rho r F).trans
    (d39GeomMirror_face_retained_iff M.geomMirror rho r _)

end DirectedDistances.PaperProofs.Section3
end
