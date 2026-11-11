/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59ProviderMirror
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassSpace
public import Mathlib.Analysis.Complex.Basic

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`), source -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9. Complex conjugation reflects the plane
drawing while preserving each stored edge direction and its missing tag. -/
def prop59Conjugation : ℂ ≃ₜ ℂ :=
  Homeomorph.mk
    ⟨conj, conj, star_star, star_star⟩
    continuous_star continuous_star

/-- Helper toward Proposition 5.9. Reflect a plane drawing in the real axis,
transporting each complete edge path by complex conjugation. -/
def mirrorDrawing {V E : Type*}
    (D : PlaneGraphDrawing V E) : PlaneGraphDrawing V E := by
  let h := prop59Conjugation
  refine ⟨D.src, D.tgt, h ∘ D.pos, ?_, (fun e => (D.arc e).map h.continuous),
    ?_, ?_, ?_⟩
  · intro v w hvw
    apply D.pos_injective
    exact h.injective hvw
  · intro e x hx y hy hxy
    apply D.arc_injOn e hx hy
    exact h.injective hxy
  · intro e e' hee'
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hz with ⟨t, ht, rfl⟩
    rcases hz' with ⟨s, hs, hs'⟩
    have hEq : (D.arc e') s = (D.arc e) t := h.injective (by simpa using hs')
    exact (Set.disjoint_left.mp (D.openArc_disjoint e e' hee'))
      ⟨t, ht, rfl⟩ ⟨s, hs, hEq⟩
  · intro e v hev
    rcases hev with ⟨t, ht, ht'⟩
    exact D.openArc_avoids e v ⟨t, ht, h.injective ht'⟩

/-- Helper toward Proposition 5.9. Reflect a directed map with missing edges
geometrically, leaving the orientation of each present edge unchanged. -/
def d39GeomMirrorMap {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) : DirectedPlaneMapWithMissing V E := by
  let D := M.toPlaneMapWithMissing.toPlaneGraphDrawing
  let D' := mirrorDrawing D
  let h := prop59Conjugation
  let e : PlaneGraphDrawing.HomeoEquiv D D' := {
    h := h
    σV := Equiv.refl V
    σE := Equiv.refl E
    pos_map := by intro v; rfl
    src_map := by intro f; rfl
    tgt_map := by intro f; rfl
    arc_range_map := by
      intro f
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(M.toPlaneMapWithMissing.toPlaneGraphDrawing.arc f) t,
          ⟨t, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, rfl⟩
    openArc_map := by
      intro f
      ext z
      constructor
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(M.toPlaneMapWithMissing.toPlaneGraphDrawing.arc f) t,
          ⟨t, ht, rfl⟩, rfl⟩ }
  let M' : PlaneMapWithMissing V E := {
    toPlaneGraphDrawing := D'
    missing := M.toPlaneMapWithMissing.missing
    missing_on_external := by
      intro f hm
      obtain ⟨F, hF, hcl⟩ :=
        M.toPlaneMapWithMissing.missing_on_external f hm
      refine ⟨e.faceMap F, e.isExternal_faceMap_iff F |>.mpr hF, ?_⟩
      have hArc : Set.range (D'.arc f) = h '' Set.range (D.arc f) := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨(D.arc f) t, ⟨t, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
          exact ⟨t, rfl⟩
      rw [hArc, e.faceMap_val, ← e.h.image_closure]
      exact Set.image_mono hcl }
  exact {
    toPlaneMapWithMissing := M'
    forward := M.forward }

/-- Helper toward Proposition 5.9. Complex conjugation preserves the local topology
geometric domain: it does not change endpoints, edge identities, missing tags,
or the ordered root mark. -/
theorem d39GeomDomain_mirror {V E : Type*}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    (hM : D39GeomDomain M rho) :
    D39GeomDomain (d39GeomMirrorMap M) rho := by
  rcases hM with ⟨hconn, hfinite, hroot⟩
  refine ⟨?_, ?_, ?_⟩
  · have hgraph : d39GeomGraph (d39GeomMirrorMap M) = d39GeomGraph M := by
      ext v w
      simp [d39GeomGraph, d39GeomAdj, d39GeomMirrorMap, mirrorDrawing]
    rw [hgraph]
    exact hconn
  · simpa [d39GeomMirrorMap, mirrorDrawing] using hfinite
  · simpa [d39GeomMirrorMap, mirrorDrawing] using hroot




def D39DomainRootedMap.mirror (A : D39DomainRootedMap) :
    D39DomainRootedMap :=
  ⟨A.V, A.E, d39GeomMirrorMap A.map, A.root,
    d39GeomDomain_mirror A.domain⟩
























































end DirectedDistances.PaperProofs.Section5
end
