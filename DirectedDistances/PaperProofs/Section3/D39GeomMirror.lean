/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso
public import DirectedDistances.PaperProofs.Section3.D39GeometricDomain
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv

/-! # Conjugation and the geometric mirror

The ordered missing-root convention is fixed by
That ruling explicitly warns that swapping the marked endpoints changes the
ball center and requires radius control, rather than a same-radius isometry. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology ComplexConjugate


/-- Helper toward Proposition 5.9: the conjugated-loop winding condition is
exactly the original winding condition with opposite integer sign. -/
theorem hasWinding_conj_iff {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ) :
    HasWinding (L.map Complex.continuous_conj) (conj w) (-n) ↔
      HasWinding L w n := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hinc⟩ :=
      hasWinding_conj (L.map Complex.continuous_conj) (conj w) (-n) h
    refine ⟨φ, ?_, ?_⟩
    · intro t
      simpa using hφ t
    · simpa using hinc
  · exact hasWinding_conj L w n

/-- Helper toward Proposition 5.9: conjugation as a plane homeomorphism. -/
@[expose] def geomConj : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph

/-- Helper toward Proposition 5.9: conjugate a plane homeomorphism on both
sides by reflection. -/
@[expose] def geomMirrorHomeomorph (h : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ :=
  (geomConj.trans h).trans geomConj

/-- Helper toward Proposition 5.9: the pointwise formula for conjugating a
plane homeomorphism. -/
@[simp] theorem geomMirrorHomeomorph_apply (h : ℂ ≃ₜ ℂ) (z : ℂ) :
    geomMirrorHomeomorph h z = conj (h (conj z)) := rfl
/-- Helper toward Proposition 5.9: orientation preservation survives
conjugation on both sides, since the two winding sign changes cancel. -/
theorem OrientationPreserving.mirror_conjugation {h : ℂ ≃ₜ ℂ}
    (hh : OrientationPreserving h) :
    OrientationPreserving (geomMirrorHomeomorph h) := by
  intro z L w hw n
  have hwc : conj w ∉ Set.range (L.map Complex.continuous_conj) := by
    rintro ⟨t, ht⟩
    apply hw
    exact ⟨t, by simpa using congrArg conj ht⟩
  have hmid := hh (L.map Complex.continuous_conj) (conj w) hwc (-n)
  have hend := hasWinding_conj_iff
    ((L.map Complex.continuous_conj).map h.continuous) (h (conj w)) (-n)
  have heq : HasWinding
      (((L.map Complex.continuous_conj).map h.continuous).map
        Complex.continuous_conj) (conj (h (conj w))) (- -n) ↔
      HasWinding (L.map (geomMirrorHomeomorph h).continuous)
        (geomMirrorHomeomorph h w) n := by
    constructor <;> rintro ⟨φ, hφ, hinc⟩ <;> refine ⟨φ, ?_, ?_⟩
    · exact hφ
    · simpa using hinc
    · exact hφ
    · simpa using hinc
  exact (hasWinding_conj_iff L w n).symm.trans
    (hmid.trans (hend.symm.trans heq))

/-- Helper toward Proposition 5.9: reflecting a plane homeomorphism twice
recovers the original homeomorphism. -/
@[simp] theorem geomMirrorHomeomorph_involutive (h : ℂ ≃ₜ ℂ) :
    geomMirrorHomeomorph (geomMirrorHomeomorph h) = h := by
  ext z
  simp only [geomMirrorHomeomorph_apply, Complex.conj_conj]

/-- Helper toward Proposition 5.9: conjugation on both sides preserves and
reflects the orientation-preserving property. -/
theorem orientationPreserving_geomMirrorHomeomorph_iff (h : ℂ ≃ₜ ℂ) :
    OrientationPreserving (geomMirrorHomeomorph h) ↔ OrientationPreserving h := by
  constructor
  · intro hh
    have hf : OrientationPreserving (geomMirrorHomeomorph (geomMirrorHomeomorph h)) :=
      OrientationPreserving.mirror_conjugation hh
    rwa [geomMirrorHomeomorph_involutive] at hf
  · exact OrientationPreserving.mirror_conjugation
/-- Helper toward Proposition 5.9: reflect positions and parameterized arcs,
retaining every vertex, edge identity and stored endpoint. -/
@[expose] def PlaneGraphDrawing.geomMirror {V E : Type*}
    (D : PlaneGraphDrawing V E) : PlaneGraphDrawing V E where
  src := D.src
  tgt := D.tgt
  pos := fun v => conj (D.pos v)
  pos_injective := geomConj.injective.comp D.pos_injective
  arc := fun e => (D.arc e).map Complex.continuous_conj
  arc_injOn := by
    intro e x hx y hy hxy
    apply D.arc_injOn e hx hy
    exact geomConj.injective hxy
  openArc_disjoint := by
    intro e f hef
    apply Set.disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    have hst : D.arc e s = D.arc f t := geomConj.injective (hsz.trans htz.symm)
    exact Set.disjoint_left.mp (D.openArc_disjoint e f hef)
      ⟨s, hs, rfl⟩ ⟨t, ht, hst.symm⟩
  openArc_avoids := by
    rintro e v ⟨t, ht, heq⟩
    exact D.openArc_avoids e v ⟨t, ht, geomConj.injective heq⟩

/-- Helper toward Proposition 5.9: the reflection equivalence transports
complete and open edge images, and therefore complementary faces. -/
@[expose] def PlaneGraphDrawing.geomMirrorEquiv {V E : Type*}
    (D : PlaneGraphDrawing V E) : D.HomeoEquiv D.geomMirror where
  h := geomConj
  σV := Equiv.refl _
  σE := Equiv.refl _
  pos_map := by intro v; rfl
  src_map := by intro e; rfl
  tgt_map := by intro e; rfl
  arc_range_map := by
    intro e
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨D.arc e t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  openArc_map := by
    intro e
    ext z
    constructor
    · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨D.arc e t, ⟨t, ht, rfl⟩, rfl⟩

/-- Helper toward Proposition 5.9: reflect the geometric map without
orienting missing edges or changing any present-edge direction. -/
@[expose] def DirectedPlaneMapWithMissing.geomMirror {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) : DirectedPlaneMapWithMissing V E where
  toPlaneMapWithMissing := {
    toPlaneGraphDrawing := M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirror
    missing := M.toPlaneMapWithMissing.missing
    missing_on_external := by
      intro e he
      obtain ⟨F, hF, hsub⟩ := M.toPlaneMapWithMissing.missing_on_external e he
      let eqv := M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv
      refine ⟨eqv.faceMap F, (eqv.isExternal_faceMap_iff F).mpr hF, ?_⟩
      rw [eqv.faceMap_val, ← eqv.h.image_closure]
      intro z hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨M.toPlaneMapWithMissing.arc e t, hsub ⟨t, rfl⟩, rfl⟩ }
  forward := M.forward

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.9: reverse an ordered root mark on the same
geometric edge. This convention is used only for the canonical missing root. -/
@[expose] def d39GeomMirrorRoot {E : Type*} (rho : E × Bool) : E × Bool :=
  (rho.1, !rho.2)

/-- Helper toward Proposition 5.9: reflection and root reversal preserve the
geometric domain when the marked root is missing, as required by the ruling. -/
theorem D39GeomDomain.geomMirror {V E : Type*}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    (hM : D39GeomDomain M rho) (hm : M.toPlaneMapWithMissing.missing rho.1) :
    D39GeomDomain M.geomMirror (d39GeomMirrorRoot rho) where
  connected := hM.connected
  locallyFinite := hM.locallyFinite
  rootValid := Or.inl hm
/-- Helper toward Proposition 5.9: root reversal under reflection changes the
first marked endpoint to the old second endpoint. -/
@[simp] theorem d39GeomRootVertex_geomMirror {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    d39GeomRootVertex M.geomMirror (d39GeomMirrorRoot rho) =
      d39GeomRootOtherVertex M rho := by
  cases hb : rho.2 <;>
    simp [d39GeomRootVertex, d39GeomRootOtherVertex, d39GeomMirrorRoot,
      DirectedPlaneMapWithMissing.geomMirror, PlaneGraphDrawing.geomMirror, hb]

/-- Helper toward Proposition 5.9: a present root cannot have its ordered
mark reversed while its direction is preserved and remain a valid root. -/
theorem D39GeomDomain.geomMirror_iff_missing {V E : Type*}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    (hM : D39GeomDomain M rho) :
    D39GeomDomain M.geomMirror (d39GeomMirrorRoot rho) ↔
      M.toPlaneMapWithMissing.missing rho.1 := by
  constructor
  · intro h
    rcases hM.rootValid with hm | ⟨hp, hf⟩
    · exact hm
    · rcases h.rootValid with hm | ⟨hp', hf'⟩
      · exact hm
      · change M.forward ⟨rho.1, hp'⟩ = !rho.2 at hf'
        rw [hf] at hf'
        cases hb : rho.2 <;> simp [hb] at hf'
  · exact hM.geomMirror

/-- Helper toward Proposition 5.9: the two ordered root endpoints are at
undirected geometric distance at most one, including a loop root. -/
theorem d39GeomRootEndpoints_edist_le_one {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    d39GeomGraphDistance M (d39GeomRootVertex M rho)
      (d39GeomRootOtherVertex M rho) ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases he : d39GeomRootVertex M rho = d39GeomRootOtherVertex M rho
  · exact Or.inr he
  · left
    refine ⟨he, rho.1, ?_⟩
    cases hb : rho.2
    · right
      simp [d39GeomRootVertex, d39GeomRootOtherVertex, hb]
    · left
      simp [d39GeomRootVertex, d39GeomRootOtherVertex, hb]

/-- Helper toward Proposition 5.9: a ball about the reversed root is
contained in the original ball with radius increased by one. -/
theorem d39GeomMirror_ballVertices_subset {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) :
    d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r ⊆
      d39GeomBallVertices M rho (r + 1) := by
  intro v hv
  change d39GeomGraphDistance M.geomMirror
    (d39GeomRootVertex M.geomMirror (d39GeomMirrorRoot rho)) v ≤ (r : ℕ∞) at hv
  rw [d39GeomRootVertex_geomMirror] at hv
  have hg : d39GeomGraph M.geomMirror = d39GeomGraph M := rfl
  change (d39GeomGraph M.geomMirror).edist (d39GeomRootOtherVertex M rho) v ≤ _ at hv
  rw [hg] at hv
  change (d39GeomGraph M).edist (d39GeomRootVertex M rho) v ≤ _
  calc
    _ ≤ (d39GeomGraph M).edist (d39GeomRootVertex M rho)
        (d39GeomRootOtherVertex M rho) +
        (d39GeomGraph M).edist (d39GeomRootOtherVertex M rho) v :=
      (d39GeomGraph M).edist_triangle
    _ ≤ 1 + (r : ℕ∞) := add_le_add (d39GeomRootEndpoints_edist_le_one M rho) hv
    _ = ((r + 1 : ℕ) : ℕ∞) := by simp [add_comm]

/-- Helper toward Proposition 5.9: reversing the ordered root mark twice
recovers the original mark. -/
@[simp] theorem d39GeomMirrorRoot_involutive {E : Type*} (rho : E × Bool) :
    d39GeomMirrorRoot (d39GeomMirrorRoot rho) = rho := by
  cases rho with
  | mk e b => cases b <;> rfl











































end DirectedDistances.PaperProofs.Section3

end
