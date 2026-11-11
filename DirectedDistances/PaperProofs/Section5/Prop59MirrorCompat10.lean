/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat7
public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
import DirectedDistances.PlanarMap.D39DrawingRepresentation3
import DirectedDistances.PlanarMap.D39RadialOrder6
import DirectedDistances.PaperProofs.Section3.D39GeomMirror

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This continuation proves
the reversal law for the topological cyclic-successor field. The full reflected
representation and OPEN 1 remain recorded below with their exact binders. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9. Equal arguments after conjugation imply
equal original arguments, including the branch-cut endpoint at `Real.pi`. -/
theorem prop59_arg_conj_injective {a b : ℂ}
    (h : Complex.arg (conj a) = Complex.arg (conj b)) :
    Complex.arg a = Complex.arg b := by
  by_cases ha : Complex.arg a = Real.pi <;>
    by_cases hb : Complex.arg b = Real.pi <;>
    simp [Complex.arg_conj, ha, hb] at h ⊢ <;>
    linarith [Complex.neg_pi_lt_arg a, Complex.neg_pi_lt_arg b]

/-- Helper toward Proposition 5.9. Conjugation sends the counterclockwise
successor of a finite angular star to the successor with the two darts
reversed. -/
theorem prop59_ccwSuccessor_conj_reverse {D : Type*} {star : Set D}
    {dir : D → ℂ} {d e : D}
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (hsucc : CcwSuccessor star dir d e) :
    CcwSuccessor star (fun x => conj (dir x)) e d := by
  rcases hsucc with ⟨hfin, hd, he, hcase⟩
  refine ⟨hfin, he, hd, ?_⟩
  rcases hcase with ⟨hed, hsingle⟩ | ⟨hed, hmin⟩
  · exact Or.inl ⟨hed.symm, by simpa [hed] using hsingle⟩
  · apply Or.inr
    refine ⟨Ne.symm hed, ?_⟩
    intro f hf hfe
    have hdeArg : Complex.arg (dir d) ≠ Complex.arg (dir e) := by
      intro hEq
      exact hed (harg d hd e he hEq).symm
    by_cases hfd : f = d
    · subst f
      exact le_rfl
    · have hfeArg : Complex.arg (dir e) ≠ Complex.arg (dir f) := by
        intro hEq
        exact hfe (harg e he f hf hEq).symm
      have hdfArg : Complex.arg (dir d) ≠ Complex.arg (dir f) := by
        intro hEq
        have hfd' : f = d := (harg d hd f hf hEq).symm
        exact hfd hfd'
      rw [d39_ccwTurn_conj (a := dir e) (b := dir d) hdeArg.symm,
        d39_ccwTurn_conj (a := dir e) (b := dir f) hfeArg]
      have hstrict : ccwTurn (dir d) (dir e) <
        ccwTurn (dir d) (dir f) := by
        apply lt_of_le_of_ne (hmin f hf hfd)
        intro heq
        have hargEq := ccwTurn_left_injective heq
        exact hfe (harg e he f hf hargEq).symm
      have hcomp := ccwTurn_comp_add hstrict
      have hreverse := ccwTurn_add_reverse (dir e) (dir f) hfeArg
      have hbound := d39_ccwTurn_lt_two_pi (u := dir d) (v := dir f) hdfArg
      linarith

/-- Helper toward Proposition 5.9. Reflecting every arc in a topological
cyclic-successor witness reverses that successor, using the orientation
preserving conjugate of its straightening homeomorphism. -/
theorem prop59_topologicalCcwSuccessor_geomMirror {D : Type*}
    {star : Set D} {arc : D → I → ℂ} {d e : D}
    (h : D39TopologicalCcwSuccessor star arc d e) :
    D39TopologicalCcwSuccessor star
      (fun x t => conj (arc x t)) e d := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hstraight⟩
  refine ⟨geomMirrorHomeomorph H, hH.mirror_conjugation,
    fun x => conj (dir x), ?_, ?_, ?_, ?_⟩
  · intro x hx
    intro hzero
    apply hdir x hx
    have hzero' := congrArg conj hzero
    simpa using hzero'
  · intro x hx y hy hxy
    exact harg x hx y hy (prop59_arg_conj_injective hxy)
  · exact prop59_ccwSuccessor_conj_reverse harg hsucc
  · intro x hx
    obtain ⟨t, ht0, ht1, hstraightX⟩ := hstraight x hx
    have himage :
        geomMirrorHomeomorph H ''
            ((fun s => conj (arc x s)) '' Set.Icc (0 : I) t) =
          (fun z : ℂ => conj z) ''
            (H '' (arc x '' Set.Icc (0 : I) t)) := by
      ext z
      constructor
      · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨H (arc x t), ⟨arc x t, ⟨t, ht, rfl⟩, rfl⟩, by
          simp [geomMirrorHomeomorph_apply]⟩
      · rintro ⟨w, ⟨u, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
        exact ⟨conj (arc x t), ⟨t, ht, rfl⟩, by
          simp [geomMirrorHomeomorph_apply]⟩
    refine ⟨t, ht0, ht1, ?_⟩
    rw [himage, hstraightX]
    ext z
    constructor
    · rintro ⟨w, ⟨s, hs0, hs1, rfl⟩, rfl⟩
      exact ⟨s, hs0, hs1, by simp [map_mul]⟩
    · rintro ⟨s, hs0, hs1, rfl⟩
      exact ⟨(s : ℂ) * dir x, ⟨s, hs0, hs1, rfl⟩, by simp [map_mul]⟩

/-- Helper toward Proposition 5.9. On reversing the rotation permutation,
the reflected dart arcs satisfy the topological-successor field at every dart.
This isolates the cyclic-order field from the remaining representation fields. -/
theorem prop59_mirrorRepresentation_rotation_field
    (M : D39RootedMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M B) (d : M.core.D) :
    D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass M.core.rot.symm e =
        rootedLocallyFiniteVertexClass M.core.rot.symm d}
      (fun e t => conj (d39DrawingDartArc B
        x.toD39DrawingRepresentationData e t)) d (M.core.rot.symm d) := by
  let V := prop59_mirrorRotationVertexEquiv M.core.rot
  have hclass (e : M.core.D) :
      V.symm (rootedLocallyFiniteVertexClass M.core.rot.symm e) =
        rootedLocallyFiniteVertexClass M.core.rot e := rfl
  have hrotClass :
      rootedLocallyFiniteVertexClass M.core.rot (M.core.rot.symm d) =
        rootedLocallyFiniteVertexClass M.core.rot d := by
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_symm_apply_left).2
      (Equiv.Perm.SameCycle.rfl : M.core.rot.SameCycle d d)
  have hstar :
      {e | rootedLocallyFiniteVertexClass M.core.rot.symm e =
        rootedLocallyFiniteVertexClass M.core.rot.symm d} =
      {e | rootedLocallyFiniteVertexClass M.core.rot e =
        rootedLocallyFiniteVertexClass M.core.rot (M.core.rot.symm d)} := by
    ext e
    constructor
    · intro he
      have he' := congrArg V.symm he
      rw [hclass e, hclass d] at he'
      rw [← hrotClass] at he'
      exact he'
    · intro he
      have he' : V.symm (rootedLocallyFiniteVertexClass M.core.rot.symm e) =
          V.symm (rootedLocallyFiniteVertexClass M.core.rot.symm d) := by
        rw [hclass e, hclass d]
        rw [hrotClass] at he
        exact he
      exact V.symm.injective he'
  have hrev := prop59_topologicalCcwSuccessor_geomMirror
    (x.rotation_topological_successor (M.core.rot.symm d))
  rw [← hstar] at hrev
  simpa [Equiv.apply_symm_apply] using hrev

/-- Helper toward Proposition 5.9. Under conjugation, the face of mirrored
dart `d` is represented by the reflected old face of `edgeInv d`; its frontier
incidence clause transports with the reversed face cycle. -/
theorem prop59_mirrorRepresentation_frontier_field
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (d : M.D)
    (v : RootedLocallyFiniteVertex M.D M.rot.symm) :
    (B.map.geomMirror.toPlaneMapWithMissing.pos
        ((prop59_mirrorRotationVertexEquiv M.rot).symm.trans x.vertexEquiv v)) ∈
      frontier ((B.map.geomMirrorEquiv.faceMap
        (x.faceOfDart (M.edgeInv d))).val) ↔
    ∃ e, Equiv.Perm.SameCycle (M.rot * M.edgeInv) d e ∧
      rootedLocallyFiniteVertexClass M.rot.symm e = v := by
  let V := prop59_mirrorRotationVertexEquiv M.rot
  let G := B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv
  have hclass (e : M.D) :
      V.symm (rootedLocallyFiniteVertexClass M.rot.symm e) =
        rootedLocallyFiniteVertexClass M.rot e := rfl
  have hrotOrbit (e : M.D) :
      rootedLocallyFiniteVertexClass M.rot (M.rot e) =
        rootedLocallyFiniteVertexClass M.rot e := by
    apply Quotient.sound
    exact ((Equiv.Perm.SameCycle.refl M.rot e).apply_right).symm
  have hrotSymmOrbit (e : M.D) :
      rootedLocallyFiniteVertexClass M.rot (M.rot.symm e) =
        rootedLocallyFiniteVertexClass M.rot e := by
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_symm_apply_left).2
      (Equiv.Perm.SameCycle.rfl : M.rot.SameCycle e e)
  have hgeom :
      (B.map.geomMirror.toPlaneMapWithMissing.pos
          (V.symm.trans x.vertexEquiv v)) ∈
        frontier ((G.faceMap (x.faceOfDart (M.edgeInv d))).val) ↔
      B.map.toPlaneMapWithMissing.pos (x.vertexEquiv (V.symm v)) ∈
        frontier (x.faceOfDart (M.edgeInv d)).val := by
    change geomConj (B.map.toPlaneMapWithMissing.pos
        (x.vertexEquiv (V.symm v))) ∈
      frontier (geomConj '' (x.faceOfDart (M.edgeInv d)).val) ↔ _
    rw [← geomConj.image_frontier]
    constructor
    · rintro ⟨z, hz, hEq⟩
      have hzEq : z = B.map.toPlaneMapWithMissing.pos
          (x.vertexEquiv (V.symm v)) := geomConj.injective hEq
      simpa [hzEq] using hz
    · intro hz
      exact ⟨B.map.toPlaneMapWithMissing.pos
        (x.vertexEquiv (V.symm v)), hz, rfl⟩
  rw [hgeom]
  change B.map.toPlaneMapWithMissing.pos (x.vertexEquiv (V.symm v)) ∈
      frontier (x.faceOfDart (M.edgeInv d)).val ↔ _
  rw [x.vertex_frontier_incidence (M.edgeInv d) (V.symm v)]
  constructor
  · rintro ⟨e₀, hcycle, hv⟩
    have hcycleBase : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
        (M.edgeInv d) e₀ := by
      exact hcycle
    let e := M.rot e₀
    refine ⟨e, ?_, ?_⟩
    · have hstep : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
          (M.edgeInv (M.rot e₀)) e₀ := by
        have h : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
            (M.edgeInv (M.rot e₀))
            ((M.rot.symm * M.edgeInv) (M.edgeInv (M.rot e₀))) :=
          (Equiv.Perm.SameCycle.refl (M.rot.symm * M.edgeInv)
            (M.edgeInv (M.rot e₀))).apply_right
        have hF : (M.rot.symm * M.edgeInv)
            (M.edgeInv (M.rot e₀)) = e₀ := by
          change M.rot.symm (M.edgeInv (M.edgeInv (M.rot e₀))) = e₀
          rw [M.edgeInv_invol]
          exact M.rot.symm_apply_apply e₀
        rw [hF] at h
        exact h
      have hcycle' := hcycleBase.trans hstep.symm
      have hmirror :=
        (prop59_mirrorFaceCycle M (M.edgeInv d)
          (M.edgeInv (M.rot e₀))).mpr hcycle'
      simpa [M.edgeInv_invol] using hmirror
    · apply V.symm.injective
      rw [hclass e]
      change rootedLocallyFiniteVertexClass M.rot (M.rot e₀) =
        V.symm v
      exact (hrotOrbit e₀).trans hv
  · rintro ⟨e, hcycle, hv⟩
    have hcycleM : Equiv.Perm.SameCycle (M.rot * M.edgeInv) d e := by
      exact hcycle
    let e₀ := M.rot.symm e
    refine ⟨e₀, ?_, ?_⟩
    · have hOld : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
          (M.edgeInv d) (M.edgeInv e) :=
        (prop59_mirrorFaceCycle M (M.edgeInv d) (M.edgeInv e)).mp
          (by simpa [M.edgeInv_invol] using hcycleM)
      have hcycle' := hOld.apply_right
      have hcycleBase : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
          (M.edgeInv d) (M.rot.symm e) := by
        simpa [Equiv.Perm.mul_apply, M.edgeInv_invol] using hcycle'
      change Equiv.Perm.SameCycle
        (M.toD39RootedMap.core.rot.symm * M.toD39RootedMap.core.edgeInv)
        (M.edgeInv d) (M.rot.symm e)
      exact hcycleBase
    · have hv' : rootedLocallyFiniteVertexClass M.rot e = V.symm v := by
        have h := congrArg V.symm hv
        rw [hclass e] at h
        exact h
      change rootedLocallyFiniteVertexClass M.rot (M.rot.symm e) = V.symm v
      exact (hrotSymmOrbit e).trans hv'











































































end DirectedDistances.PaperProofs.Section5

end
