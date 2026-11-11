/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Winding-side dependencies for the supplied Definition 3.2 boundary

The unrestricted carriers permit isolated vertices. In particular, dropping
dart-vertex surjectivity from the general dart-border-to-left-side theorem
is false. The exact v7 boundary equivalences are separate obligations. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 3.2: a one-vertex drawing with no geometric
edges is allowed by the map carrier. Its vertex is isolated. -/
@[expose] def isolatedVertexMap32 : DirectedPlaneMapWithMissing Unit Empty where
  src := Empty.elim
  tgt := Empty.elim
  pos := fun _ => 0
  pos_injective := fun _ _ _ => Subsingleton.elim _ _
  arc := fun e => e.elim
  arc_injOn := fun e => e.elim
  openArc_disjoint := fun e => e.elim
  openArc_avoids := fun e => e.elim
  missing := fun _ => False
  missing_on_external := fun e => e.elim
  forward := fun e => e.val.elim

/-- Helper toward Definition 3.2: surjectivity of dart initial vertices
does not follow from the fields of `DirectedPlaneMapWithMissing`. -/
theorem isolatedVertexMap32_not_surjective :
    ¬ Function.Surjective (boundaryDartInitial isolatedVertexMap32) := by
  intro h
  obtain ⟨d, _⟩ := h ()
  exact d.1.elim

/-- Helper toward Definition 3.2: removing surjectivity from the generic
dart-border-to-winding-side implication contradicts an existing drawing
counterexample, even for two darts and a straight edge. -/
theorem PLDrawing.not_forall_dartBorders_toPath_leftAtOn :
    ¬ (∀ (V : Type) (vert : Bool → V)
      (P : PLDrawing Bool V Bool.not (Equiv.refl Bool) vert)
      (F : P.Face) (s : {t : I // t ∈ openParams}),
      P.dartBorders false F → LeftAtOn F.val (P.arc false).toPath s) := by
  obtain ⟨V, vert, P, F, s, hb, _, hn⟩ :=
    PLDrawing.exists_dartBorders_not_mem_closure_toPath
  intro h
  exact hn (h V vert P F s hb)

/-- Helper toward Definition 3.2: two simple paths with the same endpoints
and image differ by an endpoint-fixing interval homeomorphism. This avoids
assuming that their segment parameter schedules agree. -/
theorem exists_path_reparam_of_injective_range_eq {x y : ℂ}
    (γ δ : Path x y) (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    ∃ φ : I ≃ₜ I, ∃ h0 : φ 0 = 0, ∃ h1 : φ 1 = 1,
      δ = γ.reparam φ φ.continuous h0 h1 := by
  let eγ : I ≃ₜ Set.range γ :=
    (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  let eδ : I ≃ₜ Set.range δ :=
    (δ.continuous.isClosedEmbedding hδ).isEmbedding.toHomeomorph
  let φ : I ≃ₜ I := (eδ.trans (Homeomorph.setCongr hrange)).trans eγ.symm
  have hmatch (t : I) : γ (φ t) = δ t := by
    have h := congrArg Subtype.val (eγ.apply_symm_apply
      ((Homeomorph.setCongr hrange) (eδ t)))
    exact h
  have h0 : φ 0 = 0 := hγ (by rw [hmatch, γ.source, δ.source])
  have h1 : φ 1 = 1 := hγ (by rw [hmatch, γ.target, δ.target])
  refine ⟨φ, h0, h1, ?_⟩
  ext t
  exact (hmatch t).symm

/-- Helper toward Definition 3.2: simultaneous left-side tests depend only
on an injective path's oriented image, including its two endpoints. -/
theorem forall_leftAtOn_iff_of_injective_range_eq {x y : ℂ}
    (F : Set ℂ) (γ δ : Path x y)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    (∀ s : {t : I // t ∈ openParams}, LeftAtOn F δ s) ↔
      ∀ s : {t : I // t ∈ openParams}, LeftAtOn F γ s := by
  obtain ⟨φ, h0, h1, heq⟩ :=
    exists_path_reparam_of_injective_range_eq γ δ hγ hδ hrange
  rw [heq]
  exact forall_leftAtOn_reparam_iff F γ φ h0 h1

/-- Helper toward Definition 3.2: reversing the vertex list of a simple
polyline interchanges its simultaneous left and right winding tests. The
proof transports the actual traversal schedules through a homeomorphism. -/
theorem Polyline.forall_leftAtOn_reverse_toPath_iff_forall_rightAtOn
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hp : p.IsSimple) (F : Set ℂ) :
    (∀ s : {t : I // t ∈ openParams}, LeftAtOn F p.reverse.toPath s) ↔
      ∀ s : {t : I // t ∈ openParams}, RightAtOn F p.toPath s := by
  let δ : Path p.finish p.start :=
    p.reverse.toPath.cast (Polyline.start_reverse p).symm
      (Polyline.finish_reverse p).symm
  have hγ : Function.Injective p.toPath.symm :=
    (p.toPath_injective hlen hp).comp unitInterval.symm_bijective.injective
  have hδ : Function.Injective δ :=
    p.reverse.toPath_injective (by simpa only [Polyline.reverse, List.length_reverse]
      using hlen) (p.isSimple_reverse_transfer hp)
  have hrange : Set.range δ = Set.range p.toPath.symm := by
    change Set.range p.reverse.toPath = Set.range p.toPath.symm
    rw [Path.symm_range, Polyline.range_toPath, Polyline.range_toPath,
      Polyline.image_reverse_transfer]
  have hleft :
      (∀ s : {t : I // t ∈ openParams}, LeftAtOn F p.reverse.toPath s) ↔
        ∀ s : {t : I // t ∈ openParams}, LeftAtOn F δ s := by
    exact forall_congr' (fun s => leftAtOn_congr_fun F _ δ s (fun _ => rfl))
  exact hleft.trans ((forall_leftAtOn_iff_of_injective_range_eq
    F p.toPath.symm δ hγ hδ hrange).trans (forall_leftAtOn_symm_iff F p.toPath))

/-- Helper toward Definition 3.2: the left test along the flipped dart is
equivalent, over all open parameters, to the right test along the original
dart, without a dart-vertex surjectivity hypothesis. -/
theorem PLDrawing.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : Set ℂ) :
    (∀ s : {t : I // t ∈ openParams}, LeftAtOn F (P.arc (flip d)).toPath s) ↔
      ∀ s : {t : I // t ∈ openParams}, RightAtOn F (P.arc d).toPath s := by
  rw [P.arc_flip d]
  exact (P.arc d).forall_leftAtOn_reverse_toPath_iff_forall_rightAtOn
    (P.arc_length d) (P.arc_simple d) F

/-- Helper toward Definition 3.2: the established surjective-vertex left-side
theorem also yields the complete right-side theorem, including every bend.
This generic helper retains that theorem's surjectivity assumption and does
not discharge either exact v7 target recorded below. -/
theorem PLDrawing.dartBorders_flip_toPath_rightAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders (flip d) F)
    (s : {t : I // t ∈ openParams}) :
    RightAtOn F.val (P.arc d).toPath s := by
  exact (P.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn d F.val).mp
    (fun t => P.dartBorders_toPath_leftAtOn hvert (flip d) F hborder t) s









































































end DirectedDistances.PlanarMap

end
