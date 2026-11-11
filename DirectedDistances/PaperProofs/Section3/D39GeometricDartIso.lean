/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDistance
public import DirectedDistances.PlanarMap.GeneralPlaneMapEndpointSwap

/-! # Geometric dart isomorphism for Definition 3.8 -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open unitInterval
open scoped ENNReal Topology

universe uV uE uV' uE'

/-- Helper toward Definition 3.8: a rooted geometric ball isomorphism that
allows either edge to be stored in either endpoint order. `edgeParam` records
the corresponding interval reparameterization as a homeomorphism; its
monotonicity records whether the dart direction is preserved or reversed. -/
structure D39GeomBallIsoV2 {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'} (r : ℕ)
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  radius_pos : 0 < r
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : {v // v ∈ d39GeomBallVertices M rho r} ≃
    {v // v ∈ d39GeomBallVertices M' rho' r}
  edgeEquiv : {e // e ∈ d39GeomBallEdges M rho r} ≃
    {e // e ∈ d39GeomBallEdges M' rho' r}
  faceEquiv : {F // F ∈ d39GeomRetainedFaces M rho r} ≃
    {F // F ∈ d39GeomRetainedFaces M' rho' r}
  edgeFlip : {e // e ∈ d39GeomBallEdges M rho r} → Bool
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v.1) =
    M'.toPlaneMapWithMissing.pos (vertexEquiv v).1
  edgeParam : ∀ e, Homeomorph unitInterval unitInterval
  edgeParam_mono : ∀ e, edgeFlip e = false → StrictMono (edgeParam e)
  edgeParam_anti : ∀ e, edgeFlip e = true → StrictAnti (edgeParam e)
  arc_map : ∀ e t, h (M.toPlaneMapWithMissing.arc e.1 t) =
    M'.toPlaneMapWithMissing.arc (edgeEquiv e).1 (edgeParam e t)
  src_map : ∀ e,
    (vertexEquiv ⟨M.toPlaneMapWithMissing.src e.1, e.2.1⟩).1 =
      if edgeFlip e then M'.toPlaneMapWithMissing.tgt (edgeEquiv e).1
      else M'.toPlaneMapWithMissing.src (edgeEquiv e).1
  tgt_map : ∀ e,
    (vertexEquiv ⟨M.toPlaneMapWithMissing.tgt e.1, e.2.2⟩).1 =
      if edgeFlip e then M'.toPlaneMapWithMissing.src (edgeEquiv e).1
      else M'.toPlaneMapWithMissing.tgt (edgeEquiv e).1
  missing_map : ∀ e,
    M'.toPlaneMapWithMissing.missing (edgeEquiv e).1 ↔
      M.toPlaneMapWithMissing.missing e.1
  orientation_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e.1),
    M'.forward ⟨(edgeEquiv e).1, by simpa [missing_map e] using he⟩ =
      Bool.xor (M.forward ⟨e.1, he⟩) (edgeFlip e)
  root_edge_map :
    (edgeEquiv ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩).1 = rho'.1
  root_bool_map : rho'.2 = Bool.xor rho.2
    (edgeFlip ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩)
  face_image_map : ∀ F, h '' F.1 = (faceEquiv F).1

namespace D39GeomBallIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: source endpoints map to the endpoint selected
by the edge flip. -/
theorem src_endpoint_map (e : D39GeomBallIsoV2 r M rho M' rho')
    (a : {e // e ∈ d39GeomBallEdges M rho r}) :
    (e.vertexEquiv ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩).1 =
      if e.edgeFlip a then M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1
      else M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1 :=
  e.src_map a

/-- Helper toward Definition 3.8: target endpoints map to the endpoint selected
by the edge flip. -/
theorem tgt_endpoint_map (e : D39GeomBallIsoV2 r M rho M' rho')
    (a : {e // e ∈ d39GeomBallEdges M rho r}) :
    (e.vertexEquiv ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩).1 =
      if e.edgeFlip a then M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1
      else M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1 :=
  e.tgt_map a

/-- Helper toward Definition 3.8: a dart isomorphism carries the complete image
of each ball arc to the complete image of its corresponding arc. -/
theorem arc_range_map (e : D39GeomBallIsoV2 r M rho M' rho')
    (a : {e // e ∈ d39GeomBallEdges M rho r}) :
    e.h '' Set.range (M.toPlaneMapWithMissing.arc a.1) =
      Set.range (M'.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) := by
  ext z
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, hw⟩
    refine ⟨e.edgeParam a t, ?_⟩
    exact (e.arc_map a t).symm.trans hw
  · rintro ⟨t, rfl⟩
    refine ⟨M.toPlaneMapWithMissing.arc a.1 ((e.edgeParam a).symm t),
      ⟨(e.edgeParam a).symm t, rfl⟩, ?_⟩
    simpa using (e.arc_map a ((e.edgeParam a).symm t))


/-- Helper toward Definition 3.8: the initial vertex of the marked root dart
is preserved by the root-direction and endpoint maps. -/
theorem root_initial_map (e : D39GeomBallIsoV2 r M rho M' rho') :
    (e.vertexEquiv ⟨d39GeomRootVertex M rho, by
      simp [d39GeomBallVertices, d39GeomGraphDistance]⟩).1 =
      d39GeomRootVertex M' rho' := by
  let a : {e // e ∈ d39GeomBallEdges M rho r} :=
    ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
  have he : (e.edgeEquiv a).1 = rho'.1 := e.root_edge_map
  have hs : (e.vertexEquiv ⟨M.toPlaneMapWithMissing.src rho.1,
      (d39GeomRootEdge_mem M rho e.radius_pos).1⟩).1 =
      if e.edgeFlip a then M'.toPlaneMapWithMissing.tgt rho'.1
      else M'.toPlaneMapWithMissing.src rho'.1 := by
    simpa [a, he] using e.src_map a
  have ht : (e.vertexEquiv ⟨M.toPlaneMapWithMissing.tgt rho.1,
      (d39GeomRootEdge_mem M rho e.radius_pos).2⟩).1 =
      if e.edgeFlip a then M'.toPlaneMapWithMissing.src rho'.1
      else M'.toPlaneMapWithMissing.tgt rho'.1 := by
    simpa [a, he] using e.tgt_map a
  have hbool' : rho'.2 = Bool.xor rho.2 (e.edgeFlip a) := by
    simpa [a] using e.root_bool_map
  cases hb : rho.2 <;> cases hf : e.edgeFlip a
  · have hbool : rho'.2 = false := by simpa [hb, hf] using hbool'
    simp [d39GeomRootVertex, hb, hf, hbool, hs, ht]
  · have hbool : rho'.2 = true := by simpa [hb, hf] using hbool'
    simp [d39GeomRootVertex, hb, hf, hbool, hs, ht]
  · have hbool : rho'.2 = true := by simpa [hb, hf] using hbool'
    simp [d39GeomRootVertex, hb, hf, hbool, hs, ht]
  · have hbool : rho'.2 = false := by simpa [hb, hf] using hbool'
    simp [d39GeomRootVertex, hb, hf, hbool, hs, ht]


end D39GeomBallIsoV2

/-- Helper toward Definition 3.8: the local distance using endpoint-storage
invariant rooted geometric ball isomorphisms. -/
@[expose] noncomputable def d39GeomDistanceV2 {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) : ℝ≥0∞ :=
  ⨅ r : {r : ℕ // 0 < r},
    ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 M rho M' rho')),
      ((1 / 2 : ℝ≥0∞) ^ r.1)

/-- Helper toward Definition 3.8: identity maps provide a dart isomorphism. -/
@[expose] def refl {r : ℕ} {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    (hr : 0 < r) : D39GeomBallIsoV2 r M rho M rho where
  radius_pos := hr
  h := Homeomorph.refl ℂ
  orientationPreserving := orientationPreserving_refl
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  faceEquiv := Equiv.refl _
  edgeFlip := fun _ => false
  pos_map := by intro v; rfl
  edgeParam := fun _ => Homeomorph.refl _
  edgeParam_mono := by intro a _; exact strictMono_id
  edgeParam_anti := by intro a h; simp at h
  arc_map := by intro a t; rfl
  src_map := by intro a; simp
  tgt_map := by intro a; simp
  missing_map := by intro a; rfl
  orientation_map := by intro a ha; simp
  root_edge_map := rfl
  root_bool_map := by simp
  face_image_map := by intro F; simp

/-- Helper toward Definition 3.8: compose geometric dart ball isomorphisms. -/
@[expose] def trans {r : ℕ} {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {V' : Type uV'} {E' : Type uE'}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    {V'' : Type*} {E'' : Type*}
    {M'' : DirectedPlaneMapWithMissing V'' E''} {rho'' : E'' × Bool}
    (e : D39GeomBallIsoV2 r M rho M' rho')
    (f : D39GeomBallIsoV2 r M' rho' M'' rho'') :
    D39GeomBallIsoV2 r M rho M'' rho'' where
  radius_pos := e.radius_pos
  h := e.h.trans f.h
  orientationPreserving := OrientationPreserving.trans e.orientationPreserving f.orientationPreserving
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  edgeFlip := fun a => Bool.xor (e.edgeFlip a) (f.edgeFlip (e.edgeEquiv a))
  pos_map := by
    intro v
    rw [Homeomorph.trans_apply, Equiv.trans_apply, e.pos_map]
    exact f.pos_map (e.vertexEquiv v)
  edgeParam := fun a => (e.edgeParam a).trans (f.edgeParam (e.edgeEquiv a))
  edgeParam_mono := by
    intro a ha
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a)
    · intro x y hxy
      exact f.edgeParam_mono (e.edgeEquiv a) h2
        (e.edgeParam_mono a h1 hxy)
    · simp [h1, h2] at ha
    · simp [h1, h2] at ha
    · intro x y hxy
      exact f.edgeParam_anti (e.edgeEquiv a) h2
        (e.edgeParam_anti a h1 hxy)
  edgeParam_anti := by
    intro a ha
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a)
    · simp [h1, h2] at ha
    · intro x y hxy
      exact f.edgeParam_anti (e.edgeEquiv a) h2
        (e.edgeParam_mono a h1 hxy)
    · intro x y hxy
      exact f.edgeParam_mono (e.edgeEquiv a) h2
        (e.edgeParam_anti a h1 hxy)
    · simp [h1, h2] at ha
  arc_map := by
    intro a t
    calc
      (e.h.trans f.h) (M.toPlaneMapWithMissing.arc a.1 t) =
          f.h (e.h (M.toPlaneMapWithMissing.arc a.1 t)) := rfl
      _ = f.h (M'.toPlaneMapWithMissing.arc (e.edgeEquiv a).1
          (e.edgeParam a t)) := by rw [e.arc_map]
      _ = M''.toPlaneMapWithMissing.arc (f.edgeEquiv (e.edgeEquiv a)).1
          (f.edgeParam (e.edgeEquiv a) (e.edgeParam a t)) := f.arc_map _ _
  src_map := by
    intro a
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩
    let ysrc : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1, (e.edgeEquiv a).2.1⟩
    let ytgt : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1, (e.edgeEquiv a).2.2⟩
    have he : e.vertexEquiv x = if e.edgeFlip a then ytgt else ysrc := by
      apply Subtype.ext
      by_cases hf : e.edgeFlip a <;> simp [x, ysrc, ytgt, hf, e.src_map a]
    have hm := congrArg (fun z => (f.vertexEquiv z).1) he
    have hs := f.src_map (e.edgeEquiv a)
    have ht := f.tgt_map (e.edgeEquiv a)
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a) <;>
      simp [x, ysrc, ytgt, h1, h2, hs, ht, Bool.xor_false, Bool.xor_true] at hm ⊢ <;>
      simpa using hm
  tgt_map := by
    intro a
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩
    let ysrc : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1, (e.edgeEquiv a).2.1⟩
    let ytgt : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1, (e.edgeEquiv a).2.2⟩
    have he : e.vertexEquiv x = if e.edgeFlip a then ysrc else ytgt := by
      apply Subtype.ext
      by_cases hf : e.edgeFlip a <;> simp [x, ysrc, ytgt, hf, e.tgt_map a]
    have hm := congrArg (fun z => (f.vertexEquiv z).1) he
    have hs := f.src_map (e.edgeEquiv a)
    have ht := f.tgt_map (e.edgeEquiv a)
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a) <;>
      simp [x, ysrc, ytgt, h1, h2, hs, ht, Bool.xor_false, Bool.xor_true] at hm ⊢ <;>
      simpa using hm
  missing_map := by
    intro a
    exact (f.missing_map (e.edgeEquiv a)).trans (e.missing_map a)
  orientation_map := by
    intro a ha
    have ha' : ¬ M'.toPlaneMapWithMissing.missing (e.edgeEquiv a).1 := by
      intro hm
      exact ha ((e.missing_map a).mp hm)
    have h1 := e.orientation_map a ha
    have h2 := f.orientation_map (e.edgeEquiv a) ha'
    have h2' : M''.forward ⟨(f.edgeEquiv (e.edgeEquiv a)).1,
        by simpa [f.missing_map] using ha'⟩ =
        Bool.xor (M'.forward ⟨(e.edgeEquiv a).1, ha'⟩)
          (f.edgeFlip (e.edgeEquiv a)) := h2
    change M''.forward ⟨(f.edgeEquiv (e.edgeEquiv a)).1, _⟩ = _
    rw [h2', h1]
    cases e.edgeFlip a <;> cases f.edgeFlip (e.edgeEquiv a) <;> simp [Bool.xor_assoc]
  root_edge_map := by
    let a : {e // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    let b : {e // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    let c : {e // e ∈ d39GeomBallEdges M'' rho'' r} :=
      ⟨rho''.1, d39GeomRootEdge_mem M'' rho'' e.radius_pos⟩
    have hab : e.edgeEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map
    have hbc : f.edgeEquiv b = c := by
      apply Subtype.ext
      simpa [b, c] using f.root_edge_map
    calc
      (f.edgeEquiv (e.edgeEquiv a)).1 = (f.edgeEquiv b).1 := by rw [hab]
      _ = rho''.1 := congrArg Subtype.val hbc
  root_bool_map := by
    let a : {e // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    let b : {e // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    have hab : e.edgeEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map
    have h1 := e.root_bool_map
    have h2 : rho''.2 = Bool.xor rho'.2 (f.edgeFlip (e.edgeEquiv a)) := by
      simpa [b, hab] using f.root_bool_map
    rw [h1] at h2
    simpa [Bool.xor_assoc] using h2
  face_image_map := by
    intro F
    calc
      (e.h.trans f.h) '' F.1 = f.h '' (e.h '' F.1) := by
        ext z
        simp [Homeomorph.trans_apply]
      _ = f.h '' (e.faceEquiv F).1 := by rw [e.face_image_map F]
      _ = (f.faceEquiv (e.faceEquiv F)).1 := f.face_image_map (e.faceEquiv F)

/-- Helper toward Definition 3.8: the Boolean indicator of membership in an
edge set. -/
@[expose] noncomputable def d39GeomEdgeFlipBit {E : Type*} (S : Set E) (e : E) : Bool := by
  classical
  exact decide (e ∈ S)

/-- Helper toward Definition 3.8: re-store selected edge endpoints in the
opposite order, reversing their arc parametrizations and present orientations. -/
@[expose] noncomputable def flipEdges {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (S : Set E) :
    DirectedPlaneMapWithMissing V E := by
  classical
  exact M.endpointSwap (d39GeomEdgeFlipBit S)


















end DirectedDistances.PaperProofs.Section3

end

