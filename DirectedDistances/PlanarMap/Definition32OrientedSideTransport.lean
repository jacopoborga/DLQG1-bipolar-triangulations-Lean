/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.Definition32SideTransport

/-! # Orientation-sensitive side transport with missing edges

The per-edge interval homeomorphism records the parameter direction, including
for loops. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

variable {V E V' E' : Type*}

namespace PlaneGraphDrawing.HomeoEquiv

variable {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}

/-- Helper toward Definition 3.2: identity drawing transport. -/
@[expose] def refl (D : PlaneGraphDrawing V E) :
    PlaneGraphDrawing.HomeoEquiv D D where
  h := Homeomorph.refl ℂ
  σV := Equiv.refl V
  σE := Equiv.refl E
  pos_map := by intro v; rfl
  src_map := by intro e; rfl
  tgt_map := by intro e; rfl
  arc_range_map := by intro e; simp; rfl
  openArc_map := by intro e; simp

/-- Helper toward Definition 3.2: composition of drawing transports. -/
@[expose] def trans (e : PlaneGraphDrawing.HomeoEquiv D D')
    {V'' E'' : Type*} {D'' : PlaneGraphDrawing V'' E''}
    (f : PlaneGraphDrawing.HomeoEquiv D' D'') :
    PlaneGraphDrawing.HomeoEquiv D D'' where
  h := e.h.trans f.h
  σV := e.σV.trans f.σV
  σE := e.σE.trans f.σE
  pos_map := by
    intro v
    calc
      D''.pos ((e.σV.trans f.σV) v) = f.h (D'.pos (e.σV v)) := f.pos_map _
      _ = f.h (e.h (D.pos v)) := congrArg f.h (e.pos_map v)
      _ = (e.h.trans f.h) (D.pos v) := rfl
  src_map := by
    intro a
    calc
      D''.src ((e.σE.trans f.σE) a) = f.σV (D'.src (e.σE a)) := f.src_map _
      _ = f.σV (e.σV (D.src a)) := congrArg f.σV (e.src_map a)
      _ = (e.σV.trans f.σV) (D.src a) := rfl
  tgt_map := by
    intro a
    calc
      D''.tgt ((e.σE.trans f.σE) a) = f.σV (D'.tgt (e.σE a)) := f.tgt_map _
      _ = f.σV (e.σV (D.tgt a)) := congrArg f.σV (e.tgt_map a)
      _ = (e.σV.trans f.σV) (D.tgt a) := rfl
  arc_range_map := by
    intro a
    calc
      Set.range (D''.arc ((e.σE.trans f.σE) a)) =
          f.h '' Set.range (D'.arc (e.σE a)) := f.arc_range_map _
      _ = f.h '' (e.h '' Set.range (D.arc a)) :=
        congrArg (Set.image f.h) (e.arc_range_map a)
      _ = (e.h.trans f.h) '' Set.range (D.arc a) := by
        rw [Set.image_image]
        rfl
  openArc_map := by
    intro a
    calc
      (e.h.trans f.h) '' D.openArc a = f.h '' (e.h '' D.openArc a) := by
        rw [Set.image_image]
        rfl
      _ = f.h '' D'.openArc (e.σE a) := congrArg (Set.image f.h) (e.openArc_map a)
      _ = D''.openArc ((e.σE.trans f.σE) a) := f.openArc_map _

end PlaneGraphDrawing.HomeoEquiv

namespace PlaneMapWithMissing.HomeoEquiv

variable {D : PlaneMapWithMissing V E} {D' : PlaneMapWithMissing V' E'}

/-- Helper toward Definition 3.2: composition of missing-edge drawing
transports. -/
@[expose] def trans (e : PlaneMapWithMissing.HomeoEquiv D D')
    {V'' E'' : Type*} {D'' : PlaneMapWithMissing V'' E''}
    (f : PlaneMapWithMissing.HomeoEquiv D' D'') :
    PlaneMapWithMissing.HomeoEquiv D D'' where
  drawing := e.drawing.trans f.drawing
  missing_map := by
    intro a
    exact (f.missing_map (e.drawing.σE a)).trans (e.missing_map a)

end PlaneMapWithMissing.HomeoEquiv

namespace DirectedPlaneMapWithMissing.HomeoEquiv

variable {M : DirectedPlaneMapWithMissing V E}
  {M' : DirectedPlaneMapWithMissing V' E'}

/-- Helper toward Definition 3.2: identity transport of a directed map with
missing edges. -/
@[expose] def refl (M : DirectedPlaneMapWithMissing V E) :
    DirectedPlaneMapWithMissing.HomeoEquiv M M where
  drawing := {
    drawing := PlaneGraphDrawing.HomeoEquiv.refl M.toPlaneMapWithMissing.toPlaneGraphDrawing
    missing_map := fun _ => Iff.rfl }
  forward_map := by intro e; rfl

/-- Helper toward Definition 3.2: inverse transport of a directed map with
missing edges. -/
@[expose] noncomputable def symm
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M') :
    DirectedPlaneMapWithMissing.HomeoEquiv M' M where
  drawing := e.drawing.symm
  forward_map := by
    intro f
    let g : {a : E // ¬ M.toPlaneMapWithMissing.missing a} :=
      ⟨e.drawing.drawing.σE.symm f.1, by
        intro hm
        have hm' := (e.drawing.missing_map
          (e.drawing.drawing.σE.symm f.1)).mpr hm
        rw [e.drawing.drawing.σE.apply_symm_apply] at hm'
        exact f.2 hm'⟩
    have hval : e.presentEdgeEquiv g = f := by
      apply Subtype.ext
      exact e.drawing.drawing.σE.apply_symm_apply f.1
    have hσ : e.drawing.symm.drawing.σE f.1 =
        e.drawing.drawing.σE.symm f.1 := by
      rfl
    have hval' :
        (⟨e.drawing.symm.drawing.σE f.1,
          show ¬ M.toPlaneMapWithMissing.missing
            (e.drawing.symm.drawing.σE f.1) from by
              intro hm
              have hm' := (e.drawing.symm.missing_map f.1).mp hm
              exact f.2 hm'⟩ : {a : E // ¬ M.toPlaneMapWithMissing.missing a}) = g := by
      apply Subtype.ext
      exact hσ
    change M.forward
      (⟨e.drawing.symm.drawing.σE f.1, _⟩ :
        {a : E // ¬ M.toPlaneMapWithMissing.missing a}) = M'.forward f
    rw [hval']
    exact (e.forward_map g).symm.trans (congrArg M'.forward hval)

/-- Helper toward Definition 3.2: composition of directed missing-edge
transports. -/
@[expose] def trans (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    {V'' E'' : Type*} {M'' : DirectedPlaneMapWithMissing V'' E''}
    (f : DirectedPlaneMapWithMissing.HomeoEquiv M' M'') :
    DirectedPlaneMapWithMissing.HomeoEquiv M M'' where
  drawing := e.drawing.trans f.drawing
  forward_map := by
    intro a
    let ea := e.presentEdgeEquiv a
    have h₁ := f.forward_map ea
    have h₂ := e.forward_map a
    let ca : {b : E'' // ¬ M''.toPlaneMapWithMissing.missing b} :=
      ⟨(e.drawing.trans f.drawing).drawing.σE a.1, by
        intro hm
        exact a.2 (((e.drawing.trans f.drawing).missing_map a.1).mp hm)⟩
    have hval :
        ca =
          f.presentEdgeEquiv (e.presentEdgeEquiv a) := by
      apply Subtype.ext
      rfl
    change M''.forward ca = M.forward a
    rw [hval]
    exact h₁.trans h₂

end DirectedPlaneMapWithMissing.HomeoEquiv

/-- Helper toward Definition 3.2: an orientation-preserving equivalence of
directed plane maps with missing edges, with an endpoint-preserving parameter
homeomorphism for each stored edge. -/
structure OrientedMissingHomeoEquiv
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E') where
  toHomeoEquiv : DirectedPlaneMapWithMissing.HomeoEquiv M M'
  orientationPreserving :
    OrientationPreserving toHomeoEquiv.drawing.drawing.h
  edgeReparam : E → I ≃ₜ I
  edgeReparam_zero : ∀ e, edgeReparam e 0 = 0
  edgeReparam_one : ∀ e, edgeReparam e 1 = 1
  edgeReparam_arc : ∀ e t,
    toHomeoEquiv.drawing.drawing.h (M.toPlaneMapWithMissing.arc e t) =
      M'.toPlaneMapWithMissing.arc
        (toHomeoEquiv.drawing.drawing.σE e) (edgeReparam e t)

namespace OrientedMissingHomeoEquiv

variable {M : DirectedPlaneMapWithMissing V E}
  {M' : DirectedPlaneMapWithMissing V' E'}

/-- Helper toward Definition 3.2: endpoint-fixing interval homeomorphisms
preserve the order of edge parameters. -/
theorem edgeReparam_strictMono (e : OrientedMissingHomeoEquiv M M')
    (a : E) : StrictMono (e.edgeReparam a) :=
  (e.edgeReparam a).continuous.strictMono_of_inj_boundedOrder
    (by change e.edgeReparam a 0 ≤ e.edgeReparam a 1
        rw [e.edgeReparam_zero, e.edgeReparam_one]
        exact zero_le_one)
    (e.edgeReparam a).injective

/-- Helper toward Definition 3.2: the parameter change for the directed arc
induced by a stored-edge parameter change. Reversing the stored edge conjugates
the parameter homeomorphism by interval reversal. -/
@[expose] def orientedEdgeReparam (e : OrientedMissingHomeoEquiv M M')
    (d : PresentEdge M) : I ≃ₜ I :=
  if M.forward d then e.edgeReparam d.1 else
    (unitInterval.symmHomeomorph.trans (e.edgeReparam d.1)).trans
      unitInterval.symmHomeomorph

/-- The directed-edge parameter change fixes its initial endpoint. -/
theorem orientedEdgeReparam_zero (e : OrientedMissingHomeoEquiv M M')
    (d : PresentEdge M) : e.orientedEdgeReparam d 0 = 0 := by
  by_cases h : M.forward d
  · simp [orientedEdgeReparam, h, e.edgeReparam_zero]
  · simp [orientedEdgeReparam, h, e.edgeReparam_one,
      unitInterval.symm_one,
      unitInterval.symm_zero]

/-- The directed-edge parameter change fixes its terminal endpoint. -/
theorem orientedEdgeReparam_one (e : OrientedMissingHomeoEquiv M M')
    (d : PresentEdge M) : e.orientedEdgeReparam d 1 = 1 := by
  by_cases h : M.forward d
  · simp [orientedEdgeReparam, h, e.edgeReparam_one]
  · simp [orientedEdgeReparam, h, e.edgeReparam_zero,
      unitInterval.symm_one, unitInterval.symm_zero]

/-- The directed-edge parameter change is strictly increasing. -/
theorem orientedEdgeReparam_strictMono (e : OrientedMissingHomeoEquiv M M')
    (d : PresentEdge M) : StrictMono (e.orientedEdgeReparam d) := by
  by_cases h : M.forward d
  · simpa [orientedEdgeReparam, h] using e.edgeReparam_strictMono d.1
  · intro x y hxy
    have hφ : e.orientedEdgeReparam d =
        (unitInterval.symmHomeomorph.trans (e.edgeReparam d.1)).trans
          unitInterval.symmHomeomorph := by
      simp [orientedEdgeReparam, h]
    rw [hφ]
    change σ (e.edgeReparam d.1 (σ x)) <
      σ (e.edgeReparam d.1 (σ y))
    exact unitInterval.strictAnti_symm
      (e.edgeReparam_strictMono d.1 (unitInterval.strictAnti_symm hxy))

/-- Helper toward Definition 3.2: identity oriented transport. -/
@[expose] def refl (M : DirectedPlaneMapWithMissing V E) :
    OrientedMissingHomeoEquiv M M where
  toHomeoEquiv := DirectedPlaneMapWithMissing.HomeoEquiv.refl M
  orientationPreserving := orientationPreserving_refl
  edgeReparam := fun _ => Homeomorph.refl I
  edgeReparam_zero := by intro a; rfl
  edgeReparam_one := by intro a; rfl
  edgeReparam_arc := by intro a t; rfl

/-- Helper toward Definition 3.2: inverse oriented transport. -/
@[expose] noncomputable def symm (e : OrientedMissingHomeoEquiv M M') :
    OrientedMissingHomeoEquiv M' M where
  toHomeoEquiv := e.toHomeoEquiv.symm
  orientationPreserving := OrientationPreserving.symm e.orientationPreserving
  edgeReparam := fun b =>
    (e.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE.symm b)).symm
  edgeReparam_zero := by
    intro b
    apply (e.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE.symm b)).injective
    rw [(e.edgeReparam_zero _), (e.edgeReparam _).apply_symm_apply]
  edgeReparam_one := by
    intro b
    apply (e.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE.symm b)).injective
    rw [(e.edgeReparam_one _), (e.edgeReparam _).apply_symm_apply]
  edgeReparam_arc := by
    intro b t
    let a := e.toHomeoEquiv.drawing.drawing.σE.symm b
    have h := e.edgeReparam_arc a ((e.edgeReparam a).symm t)
    have hσ : e.toHomeoEquiv.drawing.drawing.σE a = b :=
      e.toHomeoEquiv.drawing.drawing.σE.apply_symm_apply b
    change e.toHomeoEquiv.drawing.drawing.h.symm
      (M'.toPlaneMapWithMissing.arc b t) =
      M.toPlaneMapWithMissing.arc a ((e.edgeReparam a).symm t)
    rw [← hσ]
    simpa [a] using
      (congrArg e.toHomeoEquiv.drawing.drawing.h.symm h).symm

/-- Helper toward Definition 3.2: composition of oriented transports. -/
@[expose] def trans (e : OrientedMissingHomeoEquiv M M')
    {V'' E'' : Type*} {M'' : DirectedPlaneMapWithMissing V'' E''}
    (f : OrientedMissingHomeoEquiv M' M'') :
    OrientedMissingHomeoEquiv M M'' where
  toHomeoEquiv := e.toHomeoEquiv.trans f.toHomeoEquiv
  orientationPreserving :=
    OrientationPreserving.trans e.orientationPreserving f.orientationPreserving
  edgeReparam := fun a =>
    (e.edgeReparam a).trans
      (f.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE a))
  edgeReparam_zero := by
    intro a
    simp [e.edgeReparam_zero, f.edgeReparam_zero]
  edgeReparam_one := by
    intro a
    simp [e.edgeReparam_one, f.edgeReparam_one]
  edgeReparam_arc := by
    intro a t
    calc
      (e.toHomeoEquiv.drawing.drawing.h.trans
        f.toHomeoEquiv.drawing.drawing.h)
          (M.toPlaneMapWithMissing.arc a t) =
        f.toHomeoEquiv.drawing.drawing.h
          (e.toHomeoEquiv.drawing.drawing.h
            (M.toPlaneMapWithMissing.arc a t)) := rfl
      _ = f.toHomeoEquiv.drawing.drawing.h
          (M'.toPlaneMapWithMissing.arc
            (e.toHomeoEquiv.drawing.drawing.σE a) (e.edgeReparam a t)) :=
        congrArg f.toHomeoEquiv.drawing.drawing.h (e.edgeReparam_arc a t)
      _ = M''.toPlaneMapWithMissing.arc
          (f.toHomeoEquiv.drawing.drawing.σE
            (e.toHomeoEquiv.drawing.drawing.σE a))
          (f.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE a)
            (e.edgeReparam a t)) :=
        f.edgeReparam_arc (e.toHomeoEquiv.drawing.drawing.σE a)
          (e.edgeReparam a t)
      _ = M''.toPlaneMapWithMissing.arc
          ((e.toHomeoEquiv.trans f.toHomeoEquiv).drawing.drawing.σE a)
          ((e.edgeReparam a).trans
            (f.edgeReparam (e.toHomeoEquiv.drawing.drawing.σE a)) t) := rfl

end OrientedMissingHomeoEquiv

/-- Helper toward Definition 3.2: a left-side test transports under an
orientation-preserving plane homeomorphism and an increasing, endpoint-fixing
change of edge parameter. -/
theorem leftAtOn_map_reparam_iff {x y x' y' : ℂ} (F : Set ℂ)
    (γ : Path x y) (γ' : Path x' y') (s s' : {t : I // t ∈ openParams})
    (h : ℂ ≃ₜ ℂ) (hh : OrientationPreserving h) (φ : I ≃ₜ I)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (hpath : ∀ t, h (γ t) = γ' (φ t)) (hs' : φ s.1 = s'.1) :
    LeftAtOn F γ s ↔ LeftAtOn (h '' F) γ' s' := by
  have hmap := leftAtOn_map_iff F γ s h hh
  have hfun : ∀ t, (γ.map h.continuous) t =
      (γ'.reparam φ φ.continuous h0 h1) t := by
    intro t
    change h (γ t) = γ' (φ t)
    exact hpath t
  have hcongr := leftAtOn_congr_fun (h '' F) (γ.map h.continuous)
    (γ'.reparam φ φ.continuous h0 h1) s hfun
  exact hmap.trans (hcongr.trans
    (leftAtOn_reparam_iff (h '' F) γ' φ h0 h1 s s' hs'))

/-- Helper toward Definition 3.2: a right-side test transports under an
orientation-preserving plane homeomorphism and an increasing, endpoint-fixing
change of edge parameter. -/
theorem rightAtOn_map_reparam_iff {x y x' y' : ℂ} (F : Set ℂ)
    (γ : Path x y) (γ' : Path x' y') (s s' : {t : I // t ∈ openParams})
    (h : ℂ ≃ₜ ℂ) (hh : OrientationPreserving h) (φ : I ≃ₜ I)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (hpath : ∀ t, h (γ t) = γ' (φ t)) (hs' : φ s.1 = s'.1) :
    RightAtOn F γ s ↔ RightAtOn (h '' F) γ' s' := by
  have hmap := rightAtOn_map_iff F γ s h hh
  have hfun : ∀ t, (γ.map h.continuous) t =
      (γ'.reparam φ φ.continuous h0 h1) t := by
    intro t
    change h (γ t) = γ' (φ t)
    exact hpath t
  have hcongr := rightAtOn_congr_fun (h '' F) (γ.map h.continuous)
    (γ'.reparam φ φ.continuous h0 h1) s hfun
  exact hmap.trans (hcongr.trans
    (rightAtOn_reparam_iff (h '' F) γ' φ h0 h1 s s' hs'))
























end DirectedDistances.PlanarMap

end
