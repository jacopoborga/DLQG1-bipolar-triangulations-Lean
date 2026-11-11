module

public import DirectedDistances.PlanarMap.FiniteDrawingExterior
public import DirectedDistances.PlanarMap.ComponentTransfer
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Bounded

/-! # Faces of agreeing and transported drawings

Generic drawing helpers toward Theorem 1.4; no paper result is asserted here. -/

public section

open Set

namespace DirectedDistances.PlanarMap.PLDrawing

variable {D V D' V' : Type*}
variable {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
variable (P : PLDrawing D V flip rot vert)
variable (G : PLDrawing D' V' flip' rot' vert')

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Every vertex position is the start of an incident arc. -/
theorem image_eq_union_arcs (hvert : Function.Surjective vert) :
    P.image = ⋃ d, (P.arc d).image := by
  ext z
  change (z ∈ range P.pos ∨ ∃ d, z ∈ (P.arc d).image) ↔
    z ∈ ⋃ d, (P.arc d).image
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · obtain ⟨d, rfl⟩ := hvert v
      apply mem_iUnion.mpr
      refine ⟨d, ?_⟩
      rw [← P.arc_start d]
      exact Or.inl rfl
    · exact mem_iUnion.mpr ⟨d, hd⟩
  · intro hz
    exact Or.inr (mem_iUnion.mp hz)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Compact arc images form a locally finite family. -/
theorem image_isClosed (hvert : Function.Surjective vert) : IsClosed P.image := by
  rw [P.image_eq_union_arcs hvert]
  have hlocal : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
    have hfin := P.locally_finite (Metric.ball z 1) Metric.isBounded_ball
    simpa only [inter_comm] using hfin
  exact hlocal.isClosed_iUnion fun d => (P.arc d).isCompact_image.isClosed

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Agreement around an entire face preserves its component set. -/
theorem face_of_agree (hvert : Function.Surjective vert) {A : Set ℂ}
    (hXY : P.image ∩ closure A ⊆ G.image) (hYX : G.image ∩ A ⊆ P.image)
    (F : P.Face) (hFA : F.val ⊆ A) : ∃ F' : G.Face, F'.val = F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  have hUA : connectedComponentIn P.imageᶜ z ⊆ A := by
    rw [← hF]
    exact hFA
  obtain ⟨hzG, hcomp⟩ := connectedComponentIn_compl_eq_of_agree
    (P.image_isClosed hvert) hz hUA hXY hYX
  exact ⟨⟨F.val, z, hzG, hF.trans hcomp.symm⟩, rfl⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Unboundedness depends only on the underlying face set. -/
theorem isUnbounded_congr (F : P.Face) (F' : G.Face) (hF : F'.val = F.val) :
    G.IsUnbounded F' ↔ P.IsUnbounded F := by
  unfold IsUnbounded
  rw [hF]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Equal arcs border equal face sets in precisely the same way. -/
theorem dartBorders_congr {d : D} {d' : D'} (F : P.Face) (F' : G.Face)
    (harc : G.arc d' = P.arc d) (hF : F'.val = F.val) :
    G.dartBorders d' F' ↔ P.dartBorders d F := by
  simp only [dartBorders, harc, hF]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. Transporting positions and arc images transports the entire image. -/
theorem image_of_transfer (T : ℂ ≃ₜ ℂ) (P' : PLDrawing D V flip rot vert)
    (hpos : P'.pos = T ∘ P.pos)
    (harc : ∀ d, (P'.arc d).image = T '' (P.arc d).image) :
    P'.image = T '' P.image := by
  ext z
  change (z ∈ range P'.pos ∨ ∃ d, z ∈ (P'.arc d).image) ↔ z ∈ T '' P.image
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact ⟨P.pos v, Or.inl ⟨v, rfl⟩, (congrFun hpos v).symm⟩
    · rw [harc d] at hd
      obtain ⟨x, hx, rfl⟩ := hd
      exact ⟨x, Or.inr ⟨d, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x ∈ range P.pos ∨ (∃ d, x ∈ (P.arc d).image) at hx
    rcases hx with ⟨v, rfl⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨v, congrFun hpos v⟩
    · exact Or.inr ⟨d, (harc d).symm ▸ mem_image_of_mem T hd⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: faces transfer between agreeing drawings);
not a paper result. A homeomorphism transports all faces, in both directions. -/
theorem face_image_of_transfer (T : ℂ ≃ₜ ℂ) (P' : PLDrawing D V flip rot vert)
    (hpos : P'.pos = T ∘ P.pos)
    (harc : ∀ d, (P'.arc d).image = T '' (P.arc d).image) :
    P'.image = T '' P.image ∧
      (∀ F : P.Face, ∃ F' : P'.Face, F'.val = T '' F.val) ∧
      (∀ F' : P'.Face, ∃ F : P.Face, F'.val = T '' F.val) := by
  have himage := P.image_of_transfer T P' hpos harc
  refine ⟨himage, ?_, ?_⟩
  · intro F
    obtain ⟨z, hz, hF⟩ := F.property
    have hz' : T z ∉ P'.image := by
      rw [himage]
      rintro ⟨x, hx, he⟩
      exact hz (T.injective he ▸ hx)
    refine ⟨⟨T '' F.val, T z, hz', ?_⟩, rfl⟩
    rw [hF, himage]
    exact Homeomorph.image_connectedComponentIn_compl T P.image z
  · intro F'
    obtain ⟨z, hz, hF'⟩ := F'.property
    have hzP : T.symm z ∉ P.image := by
      intro h
      apply hz
      rw [himage]
      exact ⟨T.symm z, h, T.apply_symm_apply z⟩
    let F : P.Face :=
      ⟨connectedComponentIn P.imageᶜ (T.symm z), T.symm z, hzP, rfl⟩
    refine ⟨F, ?_⟩
    change F'.val = T '' connectedComponentIn P.imageᶜ (T.symm z)
    rw [Homeomorph.image_connectedComponentIn_compl, ← himage, T.apply_symm_apply]
    exact hF'

end DirectedDistances.PlanarMap.PLDrawing
