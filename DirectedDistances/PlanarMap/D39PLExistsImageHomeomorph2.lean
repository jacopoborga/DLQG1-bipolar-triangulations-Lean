/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLExistsImageHomeomorph
public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph2

/-! Helpers toward Proposition 5.16: gluing the drawing-image homeomorphism
over representative arcs and named vertices. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: a dart representative is fixed by the
representative operation. -/
theorem dartRepresentative_idempotent (d : B.D) :
    B.dartRepresentative (B.dartRepresentative d) = B.dartRepresentative d := by
  rcases B.dart_eq_representative_or_edgeInv d with h | h
  · exact congrArg B.dartRepresentative h
  · calc
      B.dartRepresentative (B.dartRepresentative d) =
          B.dartRepresentative (B.map.edgeInv d) := congrArg B.dartRepresentative h
      _ = B.dartRepresentative d := B.dartRepresentative_edgeInv d

/-- Helper toward Proposition 5.16: the closed pieces indexed by
representative darts and vertices. -/
@[expose] def drawingImagePiece : B.D ⊕ V → Set ℂ
  | Sum.inl d => (P.arc (B.dartRepresentative d)).image
  | Sum.inr v => {P.pos v}

/-- Helper toward Proposition 5.16: the prescribed homeomorphism on each
representative arc or named-vertex singleton. -/
@[expose] noncomputable def drawingImagePieceHomeomorph (i : B.D ⊕ V) :
    B.drawingImagePiece vert P i ≃ₜ B.drawingImagePiece vert P' i := by
  cases i with
  | inl d => exact B.dartArcHomeomorph vert P P' (B.dartRepresentative d)
  | inr v =>
    exact
      { toFun := fun _ => ⟨P'.pos v, by simp [drawingImagePiece]⟩
        invFun := fun _ => ⟨P.pos v, by simp [drawingImagePiece]⟩
        left_inv := by
          intro x
          apply Subtype.ext
          change P.pos v = x.val
          exact (mem_singleton_iff.mp x.property).symm
        right_inv := by
          intro x
          apply Subtype.ext
          change P'.pos v = x.val
          exact (mem_singleton_iff.mp x.property).symm
        continuous_toFun := continuous_const.subtype_mk (fun _ => by
          simp [drawingImagePiece])
        continuous_invFun := continuous_const.subtype_mk (fun _ => by
          simp [drawingImagePiece]) }

/-- Helper toward Proposition 5.16: every point of an arc that is also a
named vertex is one of that arc's two endpoints. -/
theorem arc_mem_vertex_eq_endpoint (d : B.D) (v : V) {z : ℂ}
    (hz : z ∈ (P.arc d).image) (hv : z = P.pos v) :
    z = (P.arc d).start ∨ z = (P.arc d).finish := by
  by_contra h
  have hint : z ∈ (P.arc d).interior := by
    refine ⟨hz, ?_⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using h
  exact P.interior_avoids_vertices d v (hv ▸ hint)

/-- Helper toward Proposition 5.16: a representative arc map sends any
named vertex on the arc to its corresponding target vertex. -/
theorem dartArcHomeomorph_apply_vertex (d : B.D) (v : V) {z : ℂ}
    (hz : z ∈ (P.arc d).image)
    (hv : z = P.pos v) :
    (B.dartArcHomeomorph vert P P' d ⟨z, hz⟩ : ℂ) = P'.pos v := by
  rcases B.arc_mem_vertex_eq_endpoint vert P d v hz hv with hstart | hfinish
  · have hlabel : v = vert d :=
      P.pos_injective (hv.symm.trans (hstart.trans (P.arc_start d)))
    have hx : (⟨z, hz⟩ : (P.arc d).image) = ⟨(P.arc d).start, Or.inl rfl⟩ :=
      Subtype.ext hstart
    rw [hx]
    simpa [hlabel] using (B.dartArcHomeomorph_endpoints vert P P' d).1
  · have hlabel : v = vert (B.map.edgeInv d) :=
      P.pos_injective (hv.symm.trans (hfinish.trans (P.arc_finish d)))
    have hx : (⟨z, hz⟩ : (P.arc d).image) = ⟨(P.arc d).finish, by
        rw [← (P.arc d).point_last_eq_finish]
        exact (P.arc d).point_mem_image (by
          have hpos : 0 < (P.arc d).points.length :=
            List.length_pos_iff.mpr (P.arc d).nonempty
          omega)⟩ := Subtype.ext hfinish
    rw [hx]
    simpa [hlabel] using (B.dartArcHomeomorph_endpoints vert P P' d).2

/-- Helper toward Proposition 5.16: the inverse representative arc map sends
any named target vertex on the arc to the corresponding source vertex. -/
theorem dartArcHomeomorph_symm_apply_vertex (d : B.D) (v : V) {z : ℂ}
    (hz : z ∈ (P'.arc d).image)
    (hv : z = P'.pos v) :
    ((B.dartArcHomeomorph vert P P' d).symm ⟨z, hz⟩ : ℂ) = P.pos v := by
  let e := B.dartArcHomeomorph vert P P' d
  change (e.symm ⟨z, hz⟩ : ℂ) = P.pos v
  rcases B.arc_mem_vertex_eq_endpoint vert P' d v hz hv with hstart | hfinish
  · have hlabel : v = vert d :=
      P'.pos_injective (hv.symm.trans (hstart.trans (P'.arc_start d)))
    let xt : (P'.arc d).image := ⟨(P'.arc d).start, Or.inl rfl⟩
    let xs : (P.arc d).image := ⟨(P.arc d).start, Or.inl rfl⟩
    have hx : (⟨z, hz⟩ : (P'.arc d).image) = xt := Subtype.ext hstart
    have he : (e xs : ℂ) = (xt : ℂ) := by
      simpa [e, xs, xt, hlabel, P'.arc_start] using
        (B.dartArcHomeomorph_endpoints vert P P' d).1
    rw [hx]
    have he' : e.symm xt = xs := by
      calc
        e.symm xt = e.symm (e xs) := congrArg e.symm (Subtype.ext he).symm
        _ = xs := e.symm_apply_apply xs
    simpa [e, xs, P.arc_start, hlabel] using congrArg Subtype.val he'
  · have hlabel : v = vert (B.map.edgeInv d) :=
      P'.pos_injective (hv.symm.trans (hfinish.trans (P'.arc_finish d)))
    let xt : (P'.arc d).image := ⟨(P'.arc d).finish, by
      rw [← (P'.arc d).point_last_eq_finish]
      exact (P'.arc d).point_mem_image (by
        have hpos : 0 < (P'.arc d).points.length :=
          List.length_pos_iff.mpr (P'.arc d).nonempty
        omega)⟩
    let xs : (P.arc d).image := ⟨(P.arc d).finish, by
      rw [← (P.arc d).point_last_eq_finish]
      exact (P.arc d).point_mem_image (by
        have hpos : 0 < (P.arc d).points.length :=
          List.length_pos_iff.mpr (P.arc d).nonempty
        omega)⟩
    have hx : (⟨z, hz⟩ : (P'.arc d).image) = xt := Subtype.ext hfinish
    have he : (e xs : ℂ) = (xt : ℂ) := by
      simpa [e, xs, xt, hlabel, P'.arc_finish] using
        (B.dartArcHomeomorph_endpoints vert P P' d).2
    rw [hx]
    have he' : e.symm xt = xs := by
      calc
        e.symm xt = e.symm (e xs) := congrArg e.symm (Subtype.ext he).symm
        _ = xs := e.symm_apply_apply xs
    simpa [e, xs, P.arc_finish, hlabel] using congrArg Subtype.val he'

/-- Helper toward Proposition 5.16: every representative-arc and vertex
piece is closed. -/
theorem drawingImagePiece_isClosed (i : B.D ⊕ V) :
    IsClosed (B.drawingImagePiece vert P i) := by
  cases i with
  | inl d => exact (Polyline.isCompact_image _).isClosed
  | inr v => exact isClosed_singleton

/-- Helper toward Proposition 5.16: representative-arc and vertex pieces
cover the complete drawing image, including isolated named vertices. -/
theorem iUnion_drawingImagePiece :
    (⋃ i : B.D ⊕ V, B.drawingImagePiece vert P i) = P.image := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    cases i with
    | inl d =>
        right
        exact ⟨B.dartRepresentative d, hi⟩
    | inr v =>
        have hzv : z = P.pos v := by simpa [drawingImagePiece] using hi
        exact Or.inl ⟨v, hzv.symm⟩
  · intro hz
    rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
    · refine mem_iUnion.mpr ⟨Sum.inr v, ?_⟩
      change z = P.pos v
      exact hv.symm
    · have hrep := B.arc_image_eq_representative vert P d
      refine mem_iUnion.mpr ⟨Sum.inl d, ?_⟩
      change z ∈ (P.arc (B.dartRepresentative d)).image
      exact hrep.symm ▸ hd

/-- Helper toward Proposition 5.16: the singleton piece map takes its
source point to the named target vertex. -/
theorem drawingImagePieceHomeomorph_apply_vertex (v : V) :
    (B.drawingImagePieceHomeomorph vert P P' (Sum.inr v)
      ⟨P.pos v, by simp [drawingImagePiece]⟩ : ℂ) = P'.pos v := by
  rfl

/-- Helper toward Proposition 5.16: the inverse singleton piece map takes
its target point to the named source vertex. -/
theorem drawingImagePieceHomeomorph_symm_apply_vertex (v : V) :
    ((B.drawingImagePieceHomeomorph vert P P' (Sum.inr v)).symm
      ⟨P'.pos v, by simp [drawingImagePiece]⟩ : ℂ) = P.pos v := by
  rfl

/-- Helper toward Proposition 5.16: representative-arc maps agree at every
point shared by two pieces, because distinct geometric arcs meet at named
endpoints. -/
theorem representativeArcHomeomorph_agree (r s : B.D)
    (hr : B.dartRepresentative r = r) (hs : B.dartRepresentative s = s)
    {z : ℂ} (hzr : z ∈ (P.arc r).image) (hzs : z ∈ (P.arc s).image) :
    (B.dartArcHomeomorph vert P P' r ⟨z, hzr⟩ : ℂ) =
      (B.dartArcHomeomorph vert P P' s ⟨z, hzs⟩ : ℂ) := by
  by_cases h : r = s
  · subst s
    rfl
  · have hflip : s ≠ B.map.edgeInv r := by
      intro hflip
      have hrep := congrArg B.dartRepresentative hflip
      have hleft : B.dartRepresentative s = s := hs
      have hright : B.dartRepresentative (B.map.edgeInv r) = r := by
        rw [B.dartRepresentative_edgeInv, hr]
      exact h (hleft.symm.trans (hrep.trans hright)).symm
    have hne : s ≠ r := fun heq => h heq.symm
    obtain ⟨hendR, _hendS⟩ := P.arc_intersection_endpoints r s hne hflip hzr hzs
    rcases hendR with hstart | hfinish
    · have hv : z = P.pos (vert r) := hstart.trans (P.arc_start r)
      have hR := B.dartArcHomeomorph_apply_vertex vert P P' r (vert r) hzr hv
      have hS := B.dartArcHomeomorph_apply_vertex vert P P' s (vert r)
        hzs hv
      calc
        (B.dartArcHomeomorph vert P P' r ⟨z, hzr⟩ : ℂ) = P'.pos (vert r) := hR
        _ = (B.dartArcHomeomorph vert P P' s ⟨z, hzs⟩ : ℂ) := by
          exact hS.symm
    · have hv : z = P.pos (vert (B.map.edgeInv r)) := hfinish.trans (P.arc_finish r)
      have hR := B.dartArcHomeomorph_apply_vertex vert P P' r
        (vert (B.map.edgeInv r)) hzr hv
      have hS := B.dartArcHomeomorph_apply_vertex vert P P' s
        (vert (B.map.edgeInv r)) hzs hv
      calc
        (B.dartArcHomeomorph vert P P' r ⟨z, hzr⟩ : ℂ) =
            P'.pos (vert (B.map.edgeInv r)) := hR
        _ = (B.dartArcHomeomorph vert P P' s ⟨z, hzs⟩ : ℂ) := by
          exact hS.symm

/-- Helper toward Proposition 5.16: inverse representative-arc maps agree
at every point shared by two target pieces. -/
theorem representativeArcHomeomorph_symm_agree (r s : B.D)
    (hr : B.dartRepresentative r = r) (hs : B.dartRepresentative s = s)
    {z : ℂ} (hzr : z ∈ (P'.arc r).image) (hzs : z ∈ (P'.arc s).image) :
    ((B.dartArcHomeomorph vert P P' r).symm ⟨z, hzr⟩ : ℂ) =
      ((B.dartArcHomeomorph vert P P' s).symm ⟨z, hzs⟩ : ℂ) := by
  by_cases h : r = s
  · subst s
    rfl
  · have hflip : s ≠ B.map.edgeInv r := by
      intro hflip
      have hrep := congrArg B.dartRepresentative hflip
      have hleft : B.dartRepresentative s = s := hs
      have hright : B.dartRepresentative (B.map.edgeInv r) = r := by
        rw [B.dartRepresentative_edgeInv, hr]
      exact h (hleft.symm.trans (hrep.trans hright)).symm
    have hne : s ≠ r := fun heq => h heq.symm
    obtain ⟨hendR, _hendS⟩ := P'.arc_intersection_endpoints r s hne hflip hzr hzs
    rcases hendR with hstart | hfinish
    · have hv : z = P'.pos (vert r) := hstart.trans (P'.arc_start r)
      have hR := B.dartArcHomeomorph_symm_apply_vertex vert P P' r (vert r) hzr hv
      have hS := B.dartArcHomeomorph_symm_apply_vertex vert P P' s (vert r) hzs hv
      calc
        ((B.dartArcHomeomorph vert P P' r).symm ⟨z, hzr⟩ : ℂ) = P.pos (vert r) := by
          exact hR
        _ = ((B.dartArcHomeomorph vert P P' s).symm ⟨z, hzs⟩ : ℂ) := by
          exact hS.symm
    · have hv : z = P'.pos (vert (B.map.edgeInv r)) :=
          hfinish.trans (P'.arc_finish r)
      have hR := B.dartArcHomeomorph_symm_apply_vertex vert P P' r
        (vert (B.map.edgeInv r)) hzr hv
      have hS := B.dartArcHomeomorph_symm_apply_vertex vert P P' s
        (vert (B.map.edgeInv r)) hzs hv
      calc
        ((B.dartArcHomeomorph vert P P' r).symm ⟨z, hzr⟩ : ℂ) =
            P.pos (vert (B.map.edgeInv r)) := hR
        _ = ((B.dartArcHomeomorph vert P P' s).symm ⟨z, hzs⟩ : ℂ) := by
          exact hS.symm

/-- Helper toward Proposition 5.16: all forward maps on drawing-image
pieces agree on every overlap. -/
theorem drawingImagePieceHomeomorph_agree (i j : B.D ⊕ V) {z : ℂ}
    (hi : z ∈ B.drawingImagePiece vert P i)
    (hj : z ∈ B.drawingImagePiece vert P j) :
    (B.drawingImagePieceHomeomorph vert P P' i ⟨z, hi⟩ : ℂ) =
      (B.drawingImagePieceHomeomorph vert P P' j ⟨z, hj⟩ : ℂ) := by
  cases i with
  | inl d =>
      cases j with
      | inl e =>
          have h := B.representativeArcHomeomorph_agree vert P P'
            (B.dartRepresentative d) (B.dartRepresentative e)
            (B.dartRepresentative_idempotent d) (B.dartRepresentative_idempotent e)
            hi hj
          change (B.dartArcHomeomorph vert P P' (B.dartRepresentative d) ⟨z, hi⟩ : ℂ) =
            (B.dartArcHomeomorph vert P P' (B.dartRepresentative e) ⟨z, hj⟩ : ℂ)
          exact h
      | inr v =>
          have hv : z = P.pos v := by simpa [drawingImagePiece] using hj
          have hx : (⟨z, hj⟩ : B.drawingImagePiece vert P (Sum.inr v)) =
              ⟨P.pos v, by simp [drawingImagePiece]⟩ := Subtype.ext hv
          rw [hx]
          have h := B.dartArcHomeomorph_apply_vertex vert P P'
            (B.dartRepresentative d) v hi hv
          change (B.dartArcHomeomorph vert P P' (B.dartRepresentative d) ⟨z, hi⟩ : ℂ) =
            P'.pos v
          exact h
  | inr v =>
      cases j with
      | inl d =>
          have hv : z = P.pos v := by simpa [drawingImagePiece] using hi
          have hx : (⟨z, hi⟩ : B.drawingImagePiece vert P (Sum.inr v)) =
              ⟨P.pos v, by simp [drawingImagePiece]⟩ := Subtype.ext hv
          rw [hx]
          have h := B.dartArcHomeomorph_apply_vertex vert P P'
            (B.dartRepresentative d) v hj hv
          change P'.pos v =
            (B.dartArcHomeomorph vert P P' (B.dartRepresentative d) ⟨z, hj⟩ : ℂ)
          exact h.symm
      | inr w =>
          have hv : z = P.pos v := by simpa [drawingImagePiece] using hi
          have hw : z = P.pos w := by simpa [drawingImagePiece] using hj
          have hvw : v = w := P.pos_injective (hv.symm.trans hw)
          subst w
          rfl

/-- Helper toward Proposition 5.16: all inverse maps on drawing-image
pieces agree on every overlap. -/
theorem drawingImagePieceHomeomorph_symm_agree (i j : B.D ⊕ V) {z : ℂ}
    (hi : z ∈ B.drawingImagePiece vert P' i)
    (hj : z ∈ B.drawingImagePiece vert P' j) :
    ((B.drawingImagePieceHomeomorph vert P P' i).symm ⟨z, hi⟩ : ℂ) =
      ((B.drawingImagePieceHomeomorph vert P P' j).symm ⟨z, hj⟩ : ℂ) := by
  cases i with
  | inl d =>
      cases j with
      | inl e =>
          have h := B.representativeArcHomeomorph_symm_agree vert P P'
            (B.dartRepresentative d) (B.dartRepresentative e)
            (B.dartRepresentative_idempotent d) (B.dartRepresentative_idempotent e)
            hi hj
          change ((B.dartArcHomeomorph vert P P' (B.dartRepresentative d)).symm
            ⟨z, hi⟩ : ℂ) =
            ((B.dartArcHomeomorph vert P P' (B.dartRepresentative e)).symm
              ⟨z, hj⟩ : ℂ)
          exact h
      | inr v =>
          have hv : z = P'.pos v := by simpa [drawingImagePiece] using hj
          have hx : (⟨z, hj⟩ : B.drawingImagePiece vert P' (Sum.inr v)) =
              ⟨P'.pos v, by simp [drawingImagePiece]⟩ := Subtype.ext hv
          rw [hx]
          have h := B.dartArcHomeomorph_symm_apply_vertex vert P P'
            (B.dartRepresentative d) v hi hv
          change ((B.dartArcHomeomorph vert P P' (B.dartRepresentative d)).symm
            ⟨z, hi⟩ : ℂ) = P.pos v
          exact h
  | inr v =>
      cases j with
      | inl d =>
          have hv : z = P'.pos v := by simpa [drawingImagePiece] using hi
          have hx : (⟨z, hi⟩ : B.drawingImagePiece vert P' (Sum.inr v)) =
              ⟨P'.pos v, by simp [drawingImagePiece]⟩ := Subtype.ext hv
          rw [hx]
          have h := B.dartArcHomeomorph_symm_apply_vertex vert P P'
            (B.dartRepresentative d) v hj hv
          change P.pos v = ((B.dartArcHomeomorph vert P P' (B.dartRepresentative d)).symm
            ⟨z, hj⟩ : ℂ)
          exact h.symm
      | inr w =>
          have hv : z = P'.pos v := by simpa [drawingImagePiece] using hi
          have hw : z = P'.pos w := by simpa [drawingImagePiece] using hj
          have hvw : v = w := P'.pos_injective (hv.symm.trans hw)
          subst w
          rfl

/-- Helper toward Proposition 5.16: the compatible closed-piece maps glue
to a homeomorphism of the complete drawing images. -/
theorem exists_drawingImage_homeomorph [Finite V] :
    ∃ H : P.image ≃ₜ P'.image,
      ∀ i (x : B.drawingImagePiece vert P i),
        (H ⟨x.val, (B.iUnion_drawingImagePiece vert P).symm ▸
          mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) =
          (B.drawingImagePieceHomeomorph vert P P' i x : ℂ) := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨G, hG⟩ := exists_homeomorph_iUnion_closed_sets
    (B.drawingImagePiece vert P) (B.drawingImagePiece vert P')
    (B.drawingImagePiece_isClosed vert P) (B.drawingImagePiece_isClosed vert P')
    (B.drawingImagePieceHomeomorph vert P P')
    (fun i j z hi hj => B.drawingImagePieceHomeomorph_agree vert P P' i j hi hj)
    (fun i j z hi hj => B.drawingImagePieceHomeomorph_symm_agree vert P P' i j hi hj)
  let hs := B.iUnion_drawingImagePiece vert P
  let ht := B.iUnion_drawingImagePiece vert P'
  let H := (Homeomorph.setCongr hs.symm).trans
    (G.trans (Homeomorph.setCongr ht))
  refine ⟨H, ?_⟩
  intro i x
  have hval := hG i x
  simpa [H, hs, Homeomorph.setCongr] using hval

/-- Helper toward Proposition 5.16: representative-arc gluing yields the
prescribed homeomorphism of drawing images, including all labeled arcs and
named vertices. -/
theorem exists_plImageHomeomorph [Finite V] :
    Nonempty (B.PLImageHomeomorph vert P P') := by
  classical
  obtain ⟨H, hH⟩ := B.exists_drawingImage_homeomorph vert P P'
  let hs := B.iUnion_drawingImagePiece vert P
  refine ⟨{
    toHomeomorph := H
    arc_image := ?_
    vertex_image := ?_ }⟩
  · intro d
    let r := B.dartRepresentative d
    have hsrc := B.arc_image_eq_representative vert P d
    have htgt := B.arc_image_eq_representative vert P' d
    rw [← hsrc, ← htgt]
    have hRep (x : (P.arc r).image) :
        (H ⟨x.val, (hs.symm ▸ mem_iUnion.mpr ⟨Sum.inl d, x.property⟩)⟩ : ℂ) =
          (B.dartArcHomeomorph vert P P' r x : ℂ) := hH (Sum.inl d) x
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      let xp : (P.arc r).image := ⟨x.val, hx⟩
      let xP : P.image := ⟨x.val, Or.inr ⟨r, hx⟩⟩
      have hxeq : x = xP := Subtype.ext rfl
      have hfx : (H x : ℂ) = (B.dartArcHomeomorph vert P P' r xp : ℂ) := by
        rw [hxeq]
        exact hRep xp
      rw [hxy.symm.trans hfx]
      exact (B.dartArcHomeomorph vert P P' r xp).property
    · intro hy
      let yp : (P'.arc r).image := ⟨y, hy⟩
      let xp := (B.dartArcHomeomorph vert P P' r).symm yp
      let xP : P.image := ⟨xp.val, Or.inr ⟨r, xp.property⟩⟩
      have hxeq : (⟨xp.val, (hs.symm ▸ mem_iUnion.mpr
          ⟨Sum.inl d, xp.property⟩)⟩ : P.image) = xP := Subtype.ext rfl
      have hfx : (H xP : ℂ) = y := by
        rw [← hxeq]
        calc
          (H ⟨xp.val, hs.symm ▸ mem_iUnion.mpr ⟨Sum.inl d, xp.property⟩⟩ : ℂ) =
              (B.dartArcHomeomorph vert P P' r xp : ℂ) := hRep xp
          _ = y := by simp [xp, yp]
      exact ⟨xP, xp.property, hfx⟩
  · intro v
    have hval := hH (Sum.inr v) ⟨P.pos v, by simp [drawingImagePiece]⟩
    simpa [hs, Homeomorph.setCongr, drawingImagePieceHomeomorph] using hval

end D39FiniteBall

end DirectedDistances.PlanarMap
end
