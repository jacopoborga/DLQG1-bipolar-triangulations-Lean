/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso
public import DirectedDistances.PaperProofs.Section3.D39GeometricDomainTransport

/-! # Geometric dart invariance for Definition 3.8 -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open unitInterval
open scoped ENNReal Topology

universe uV uE uV' uE'

/-- Helper toward Definition 3.8: an orientation preserving isomorphism of
rooted plane maps that allows every edge to be stored in either endpoint
order. -/
structure D39GeomRootedMapIsoV2 {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : V ≃ V'
  edgeEquiv : E ≃ E'
  edgeFlip : E → Bool
  edgeParam : ∀ e, Homeomorph unitInterval unitInterval
  edgeParam_mono : ∀ e, edgeFlip e = false → StrictMono (edgeParam e)
  edgeParam_anti : ∀ e, edgeFlip e = true → StrictAnti (edgeParam e)
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v) =
    M'.toPlaneMapWithMissing.pos (vertexEquiv v)
  arc_map : ∀ e t, h (M.toPlaneMapWithMissing.arc e t) =
    M'.toPlaneMapWithMissing.arc (edgeEquiv e) (edgeParam e t)
  src_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.src e) =
    if edgeFlip e then M'.toPlaneMapWithMissing.tgt (edgeEquiv e)
    else M'.toPlaneMapWithMissing.src (edgeEquiv e)
  tgt_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.tgt e) =
    if edgeFlip e then M'.toPlaneMapWithMissing.src (edgeEquiv e)
    else M'.toPlaneMapWithMissing.tgt (edgeEquiv e)
  missing_map : ∀ e,
    M'.toPlaneMapWithMissing.missing (edgeEquiv e) ↔
      M.toPlaneMapWithMissing.missing e
  orientation_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e),
    M'.forward ⟨edgeEquiv e, by simpa [missing_map e] using he⟩ =
      Bool.xor (M.forward ⟨e, he⟩) (edgeFlip e)
  root_edge_map : edgeEquiv rho.1 = rho'.1
  root_bool_map : rho'.2 = Bool.xor rho.2 (edgeFlip rho.1)

namespace D39GeomRootedMapIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: forget the geometric data to obtain the
combinatorial dart isomorphism used for graph distance transport. -/
@[expose] def toCombDartIso (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    D39CombDartIso M rho M' rho' where
  vertexEquiv := e.vertexEquiv
  edgeEquiv := e.edgeEquiv
  flip := e.edgeFlip
  src_map := e.src_map
  tgt_map := e.tgt_map
  missing_map := e.missing_map
  forward_map := e.orientation_map
  root_edge := e.root_edge_map
  root_bool := e.root_bool_map

/-- Helper toward Definition 3.8: the identity rooted geometric dart
isomorphism. -/
@[expose] def refl (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    D39GeomRootedMapIsoV2 M rho M rho where
  h := Homeomorph.refl ℂ
  orientationPreserving := orientationPreserving_refl
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  edgeFlip := fun _ => false
  edgeParam := fun _ => Homeomorph.refl _
  edgeParam_mono := by intro _ _; exact strictMono_id
  edgeParam_anti := by intro e hf; simp at hf
  pos_map := by intro v; rfl
  arc_map := by intro e t; rfl
  src_map := by intro e; simp
  tgt_map := by intro e; simp
  missing_map := by intro e; rfl
  orientation_map := by intro e he; simp
  root_edge_map := rfl
  root_bool_map := by simp

/-- Helper toward Definition 3.8: reverse a rooted geometric dart
isomorphism. -/
@[expose] def symm (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    D39GeomRootedMapIsoV2 M' rho' M rho where
  h := e.h.symm
  orientationPreserving := OrientationPreserving.symm e.orientationPreserving
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  edgeFlip := fun b => e.edgeFlip (e.edgeEquiv.symm b)
  edgeParam := fun b => (e.edgeParam (e.edgeEquiv.symm b)).symm
  edgeParam_mono := by
    intro b hb
    have hb' : e.edgeFlip (e.edgeEquiv.symm b) = false := hb
    intro x y hxy
    have h := e.edgeParam_mono (e.edgeEquiv.symm b) hb'
    have hvals : e.edgeParam (e.edgeEquiv.symm b) ((e.edgeParam (e.edgeEquiv.symm b)).symm x) <
        e.edgeParam (e.edgeEquiv.symm b) ((e.edgeParam (e.edgeEquiv.symm b)).symm y) := by
      simpa using hxy
    exact h.lt_iff_lt.mp hvals
  edgeParam_anti := by
    intro b hb
    have h := e.edgeParam_anti (e.edgeEquiv.symm b) hb
    intro x y hxy
    have hvals : e.edgeParam (e.edgeEquiv.symm b) ((e.edgeParam (e.edgeEquiv.symm b)).symm x) <
        e.edgeParam (e.edgeEquiv.symm b) ((e.edgeParam (e.edgeEquiv.symm b)).symm y) := by
      simpa using hxy
    have hh := h.lt_iff_gt.mp hvals
    simpa using hh
  pos_map := by
    intro v
    simpa using congrArg e.h.symm (e.pos_map (e.vertexEquiv.symm v)).symm
  arc_map := by
    intro b t
    have h := e.arc_map (e.edgeEquiv.symm b) ((e.edgeParam (e.edgeEquiv.symm b)).symm t)
    rw [e.edgeEquiv.apply_symm_apply] at h
    have h' : e.h (M.toPlaneMapWithMissing.arc (e.edgeEquiv.symm b)
        ((e.edgeParam (e.edgeEquiv.symm b)).symm t)) =
        M'.toPlaneMapWithMissing.arc b t := by
      simpa only [Homeomorph.apply_symm_apply] using h
    calc
      e.h.symm (M'.toPlaneMapWithMissing.arc b t) =
          e.h.symm (e.h (M.toPlaneMapWithMissing.arc (e.edgeEquiv.symm b)
            ((e.edgeParam (e.edgeEquiv.symm b)).symm t))) := by rw [← h']
      _ = M.toPlaneMapWithMissing.arc (e.edgeEquiv.symm b)
          ((e.edgeParam (e.edgeEquiv.symm b)).symm t) := by simp
  src_map := by
    intro b
    have hs := e.src_map (e.edgeEquiv.symm b)
    have ht := e.tgt_map (e.edgeEquiv.symm b)
    have heq := e.edgeEquiv.apply_symm_apply b
    cases hb : e.edgeFlip (e.edgeEquiv.symm b)
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm hs).symm
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm ht).symm
  tgt_map := by
    intro b
    have hs := e.src_map (e.edgeEquiv.symm b)
    have ht := e.tgt_map (e.edgeEquiv.symm b)
    have heq := e.edgeEquiv.apply_symm_apply b
    cases hb : e.edgeFlip (e.edgeEquiv.symm b)
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm ht).symm
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm hs).symm
  missing_map := by intro b; exact e.toCombDartIso.symm.missing_map b
  orientation_map := by intro b hb; exact e.toCombDartIso.symm.forward_map b hb
  root_edge_map := e.toCombDartIso.symm.root_edge
  root_bool_map := e.toCombDartIso.symm.root_bool

/-- Helper toward Definition 3.8: compose rooted geometric dart
isomorphisms. -/
@[expose] def trans {V'' : Type*} {E'' : Type*}
    {M'' : DirectedPlaneMapWithMissing V'' E''} {rho'' : E'' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (f : D39GeomRootedMapIsoV2 M' rho' M'' rho'') :
    D39GeomRootedMapIsoV2 M rho M'' rho'' where
  h := e.h.trans f.h
  orientationPreserving := OrientationPreserving.trans e.orientationPreserving f.orientationPreserving
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  edgeFlip := fun a => Bool.xor (e.edgeFlip a) (f.edgeFlip (e.edgeEquiv a))
  edgeParam := fun a => (e.edgeParam a).trans (f.edgeParam (e.edgeEquiv a))
  edgeParam_mono := by
    intro a ha
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a)
    · intro x y hxy
      exact f.edgeParam_mono (e.edgeEquiv a) h2 (e.edgeParam_mono a h1 hxy)
    · simp [h1, h2] at ha
    · simp [h1, h2] at ha
    · intro x y hxy
      exact f.edgeParam_anti (e.edgeEquiv a) h2 (e.edgeParam_anti a h1 hxy)
  edgeParam_anti := by
    intro a ha
    cases h1 : e.edgeFlip a <;> cases h2 : f.edgeFlip (e.edgeEquiv a)
    · simp [h1, h2] at ha
    · intro x y hxy
      exact f.edgeParam_anti (e.edgeEquiv a) h2 (e.edgeParam_mono a h1 hxy)
    · intro x y hxy
      exact f.edgeParam_mono (e.edgeEquiv a) h2 (e.edgeParam_anti a h1 hxy)
    · simp [h1, h2] at ha
  pos_map := by
    intro v
    rw [Homeomorph.trans_apply, Equiv.trans_apply, e.pos_map]
    exact f.pos_map (e.vertexEquiv v)
  arc_map := by
    intro a t
    calc
      (e.h.trans f.h) (M.toPlaneMapWithMissing.arc a t) =
          f.h (e.h (M.toPlaneMapWithMissing.arc a t)) := rfl
      _ = f.h (M'.toPlaneMapWithMissing.arc (e.edgeEquiv a) (e.edgeParam a t)) := by
        rw [e.arc_map]
      _ = M''.toPlaneMapWithMissing.arc (f.edgeEquiv (e.edgeEquiv a))
          (f.edgeParam (e.edgeEquiv a) (e.edgeParam a t)) := f.arc_map _ _
  src_map := by intro a; exact (e.toCombDartIso.trans f.toCombDartIso).src_map a
  tgt_map := by intro a; exact (e.toCombDartIso.trans f.toCombDartIso).tgt_map a
  missing_map := by intro a; exact (e.toCombDartIso.trans f.toCombDartIso).missing_map a
  orientation_map := by intro a ha; exact (e.toCombDartIso.trans f.toCombDartIso).forward_map a ha
  root_edge_map := (e.toCombDartIso.trans f.toCombDartIso).root_edge
  root_bool_map := (e.toCombDartIso.trans f.toCombDartIso).root_bool

end D39GeomRootedMapIsoV2

namespace D39GeomRootedMapIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: the homeomorphism carries each complete
geometric edge arc onto the reparameterized target arc. -/
theorem arc_range_map (e : D39GeomRootedMapIsoV2 M rho M' rho') (a : E) :
    e.h '' Set.range (M.toPlaneMapWithMissing.arc a) =
      Set.range (M'.toPlaneMapWithMissing.arc (e.edgeEquiv a)) := by
  ext z
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, hy⟩
    refine ⟨e.edgeParam a t, ?_⟩
    exact (e.arc_map a t).symm.trans hy
  · rintro ⟨t, rfl⟩
    refine ⟨M.toPlaneMapWithMissing.arc a ((e.edgeParam a).symm t),
      ⟨(e.edgeParam a).symm t, rfl⟩, ?_⟩
    simpa only [Homeomorph.apply_symm_apply] using
      e.arc_map a ((e.edgeParam a).symm t)

/-- Helper toward Definition 3.8: the plane homeomorphism carries the full
drawing image, including every geometric edge, onto the target drawing. -/
theorem drawing_image_map (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    e.h '' M.toPlaneMapWithMissing.toPlaneGraphDrawing.image =
      M'.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
  let D := M.toPlaneMapWithMissing.toPlaneGraphDrawing
  let D' := M'.toPlaneMapWithMissing.toPlaneGraphDrawing
  have hp : e.h '' Set.range D.pos = Set.range D'.pos := by
    ext z
    constructor
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨e.vertexEquiv v, (e.pos_map v).symm⟩
    · rintro ⟨v', rfl⟩
      obtain ⟨v, hv⟩ := e.vertexEquiv.surjective v'
      refine ⟨D.pos v, ⟨v, rfl⟩, ?_⟩
      rw [e.pos_map v, hv]
  have he : e.h '' (⋃ a : E, Set.range (D.arc a)) =
      ⋃ b : E', Set.range (D'.arc b) := by
    rw [Set.image_iUnion]
    calc
      (⋃ a : E, e.h '' Set.range (D.arc a)) =
          ⋃ a : E, Set.range (D'.arc (e.edgeEquiv a)) := by
            apply iUnion_congr
            exact e.arc_range_map
      _ = ⋃ b : E', Set.range (D'.arc b) := by
        ext z
        simp only [mem_iUnion]
        constructor
        · rintro ⟨a, ha⟩
          exact ⟨e.edgeEquiv a, ha⟩
        · rintro ⟨b, hb⟩
          obtain ⟨a, rfl⟩ := e.edgeEquiv.surjective b
          exact ⟨a, hb⟩
  change e.h '' (Set.range D.pos ∪ ⋃ a : E, Set.range (D.arc a)) =
    Set.range D'.pos ∪ ⋃ b : E', Set.range (D'.arc b)
  rw [Set.image_union, hp, he]

/-- Helper toward Definition 3.8: the homeomorphism carries the complement
of the drawing image onto the complement of the target drawing image. -/
theorem drawing_compl_image_map (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    e.h '' M.toPlaneMapWithMissing.toPlaneGraphDrawing.imageᶜ =
      M'.toPlaneMapWithMissing.toPlaneGraphDrawing.imageᶜ := by
  have hi := e.drawing_image_map
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ hz
    have hx' : e.h x ∈ e.h '' M.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
      rw [hi]
      exact hz
    rcases hx' with ⟨y, hy, hxy⟩
    have hyz : y = x := e.h.injective hxy
    exact hx (hyz ▸ hy)
  · intro hz
    refine ⟨e.h.symm z, ?_, e.h.apply_symm_apply z⟩
    intro hx
    apply hz
    rw [← hi]
    exact ⟨e.h.symm z, hx, e.h.apply_symm_apply z⟩

/-- Helper toward Definition 3.8: transport a drawing face by the plane
homeomorphism. -/
@[expose] def faceMap (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face := by
  classical
  let z := Classical.choose F.property
  have hzF := Classical.choose_spec F.property
  have hz := hzF.1
  have hF := hzF.2
  have hc := e.drawing_compl_image_map
  refine ⟨e.h '' F.val, ?_⟩
  refine ⟨e.h z, ?_, ?_⟩
  · intro hz'
    have hmem : e.h z ∈ e.h '' M.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
      rw [e.drawing_image_map]
      exact hz'
    rcases hmem with ⟨y, hy, hzy⟩
    have hyz : y = z := e.h.injective hzy
    subst y
    exact hz hy
  · rw [hF]
    rw [e.h.image_connectedComponentIn hz, hc]

@[simp] theorem faceMap_val (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    (e.faceMap F).val = e.h '' F.val := rfl

/-- Helper toward Definition 3.8: faces correspond bijectively under the
rooted geometric dart isomorphism. -/
@[expose] def faceEquiv (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face ≃
      M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face where
  toFun := e.faceMap
  invFun := e.symm.faceMap
  left_inv := by
    intro F
    apply Subtype.ext
    change e.h.symm '' (e.h '' F.val) = F.val
    rw [Set.image_image]
    ext z
    simp
  right_inv := by
    intro F
    apply Subtype.ext
    change e.h '' (e.h.symm '' F.val) = F.val
    rw [Set.image_image]
    ext z
    simp

@[simp] theorem faceEquiv_val (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    (e.faceEquiv F).val = e.h '' F.val := rfl

/-- Helper toward Definition 3.8: the ordered root dart's initial vertex is
preserved by the endpoint flip and root Boolean transport. -/
theorem rootVertex_map (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    e.vertexEquiv (d39GeomRootVertex M rho) =
      d39GeomRootVertex M' rho' := e.toCombDartIso.rootVertex_map

/-- Helper toward Definition 3.8: extended graph distance is preserved. -/
@[simp] theorem graphDistance_map (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (v w : V) :
    d39GeomGraphDistance M v w =
      d39GeomGraphDistance M' (e.vertexEquiv v) (e.vertexEquiv w) :=
  e.toCombDartIso.graphDistance_map v w

/-- Helper toward Definition 3.8: root-centered ball membership is preserved
and reflected. -/
theorem ballVertices_map (e : D39GeomRootedMapIsoV2 M rho M' rho') (r : ℕ)
    (v : V) :
    v ∈ d39GeomBallVertices M rho r ↔
      e.vertexEquiv v ∈ d39GeomBallVertices M' rho' r := by
  change d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (r : ℕ∞) ↔
    d39GeomGraphDistance M' (d39GeomRootVertex M' rho') (e.vertexEquiv v) ≤ (r : ℕ∞)
  rw [e.graphDistance_map, e.rootVertex_map]

/-- Helper toward Definition 3.8: the vertices of corresponding geometric
balls are equivalent. -/
@[expose] def ballVertexEquiv (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (r : ℕ) :
    {v // v ∈ d39GeomBallVertices M rho r} ≃
      {v' // v' ∈ d39GeomBallVertices M' rho' r} where
  toFun v := ⟨e.vertexEquiv v.1, (e.ballVertices_map r v.1).mp v.2⟩
  invFun v := ⟨e.vertexEquiv.symm v.1, (e.symm.ballVertices_map r v.1).mp v.2⟩
  left_inv := by intro v; apply Subtype.ext; simp
  right_inv := by intro v; apply Subtype.ext; simp

/-- Helper toward Definition 3.8: geometric edge-ball membership is preserved
and reflected, retaining edge identities under endpoint flips. -/
theorem ballEdges_map (e : D39GeomRootedMapIsoV2 M rho M' rho') (r : ℕ)
    (a : E) :
    a ∈ d39GeomBallEdges M rho r ↔
      e.edgeEquiv a ∈ d39GeomBallEdges M' rho' r := by
  change (M.toPlaneMapWithMissing.src a ∈ d39GeomBallVertices M rho r ∧
      M.toPlaneMapWithMissing.tgt a ∈ d39GeomBallVertices M rho r) ↔
    (M'.toPlaneMapWithMissing.src (e.edgeEquiv a) ∈
        d39GeomBallVertices M' rho' r ∧
      M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a) ∈
        d39GeomBallVertices M' rho' r)
  cases hf : e.edgeFlip a
  · rw [e.ballVertices_map r (M.toPlaneMapWithMissing.src a),
      e.ballVertices_map r (M.toPlaneMapWithMissing.tgt a), e.src_map, e.tgt_map]
    simp [hf]
  · rw [e.ballVertices_map r (M.toPlaneMapWithMissing.src a),
      e.ballVertices_map r (M.toPlaneMapWithMissing.tgt a), e.src_map, e.tgt_map]
    simp [hf, and_comm]

/-- Helper toward Definition 3.8: edge identities in corresponding balls are
equivalent, retaining parallel edges and missing tags. -/
@[expose] def ballEdgeEquiv (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (r : ℕ) :
    {a // a ∈ d39GeomBallEdges M rho r} ≃
      {b // b ∈ d39GeomBallEdges M' rho' r} where
  toFun a := ⟨e.edgeEquiv a.1, (e.ballEdges_map r a.1).mp a.2⟩
  invFun b := ⟨e.edgeEquiv.symm b.1, (e.symm.ballEdges_map r b.1).mp b.2⟩
  left_inv := by intro a; apply Subtype.ext; simp
  right_inv := by intro b; apply Subtype.ext; simp

/-- Helper toward Definition 3.8: retained-face membership is preserved and
reflected by the homeomorphism and graph-distance ball correspondence. -/
theorem retainedFaces_map (e : D39GeomRootedMapIsoV2 M rho M' rho') (r : ℕ)
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    F ∈ d39GeomRetainedFaces M rho r ↔
      e.faceEquiv F ∈ d39GeomRetainedFaces M' rho' r := by
  constructor
  · intro hF v' hv'
    change ∀ v, M.toPlaneMapWithMissing.pos v ∈ closure F.val →
      v ∈ d39GeomBallVertices M rho r at hF
    let v := e.vertexEquiv.symm v'
    have hpos : M'.toPlaneMapWithMissing.pos v' =
        e.h (M.toPlaneMapWithMissing.pos v) := by simp [v, e.pos_map]
    have hcl : e.h (M.toPlaneMapWithMissing.pos v) ∈ closure (e.h '' F.val) := by
      simpa [hpos] using hv'
    have hcl' : e.h (M.toPlaneMapWithMissing.pos v) ∈ e.h '' closure F.val := by
      rw [e.h.image_closure F.val]
      exact hcl
    rcases hcl' with ⟨z, hz, hzeq⟩
    have hz' : z = M.toPlaneMapWithMissing.pos v := e.h.injective hzeq
    have hv : M.toPlaneMapWithMissing.pos v ∈ closure F.val := hz' ▸ hz
    have hb := (e.ballVertices_map r v).mp (hF v hv)
    simpa [v] using hb
  · intro hF v hv
    change ∀ v', M'.toPlaneMapWithMissing.pos v' ∈
      closure (e.faceEquiv F).val → v' ∈ d39GeomBallVertices M' rho' r at hF
    have hcl : e.h (M.toPlaneMapWithMissing.pos v) ∈ closure (e.h '' F.val) := by
      rw [← e.h.image_closure F.val]
      exact Set.mem_image_of_mem _ hv
    have hcl' : M'.toPlaneMapWithMissing.pos (e.vertexEquiv v) ∈
        closure (e.faceEquiv F).val := by simpa [e.pos_map, e.faceEquiv_val] using hcl
    exact (e.ballVertices_map r v).mpr (hF (e.vertexEquiv v) hcl')

/-- Helper toward Definition 3.8: retained original faces in corresponding
balls are equivalent. -/
@[expose] def retainedFaceEquiv (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (r : ℕ) :
    {F // F ∈ d39GeomRetainedFaces M rho r} ≃
      {F' // F' ∈ d39GeomRetainedFaces M' rho' r} where
  toFun F := ⟨e.faceEquiv F.1, (e.retainedFaces_map r F.1).mp F.2⟩
  invFun F := ⟨e.symm.faceEquiv F.1, (e.symm.retainedFaces_map r F.1).mp F.2⟩
  left_inv := by intro F; apply Subtype.ext; exact e.faceEquiv.left_inv F.1
  right_inv := by intro F; apply Subtype.ext; exact e.faceEquiv.right_inv F.1

/-- Helper toward Definition 3.8: a rooted geometric dart isomorphism induces
an isomorphism of every positive-radius geometric ball. -/
@[expose] def toBallIsoV2 (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (r : ℕ) (hr : 0 < r) : D39GeomBallIsoV2 r M rho M' rho' where
  radius_pos := hr
  h := e.h
  orientationPreserving := e.orientationPreserving
  vertexEquiv := e.ballVertexEquiv r
  edgeEquiv := e.ballEdgeEquiv r
  faceEquiv := e.retainedFaceEquiv r
  edgeFlip := fun a => e.edgeFlip a.1
  pos_map := by intro v; exact e.pos_map v.1
  edgeParam := fun a => e.edgeParam a.1
  edgeParam_mono := by intro a ha; exact e.edgeParam_mono a.1 ha
  edgeParam_anti := by intro a ha; exact e.edgeParam_anti a.1 ha
  arc_map := by intro a t; exact e.arc_map a.1 t
  src_map := by intro a; exact e.src_map a.1
  tgt_map := by intro a; exact e.tgt_map a.1
  missing_map := by intro a; exact e.missing_map a.1
  orientation_map := by intro a ha; exact e.orientation_map a.1 ha
  root_edge_map := by
    change e.edgeEquiv rho.1 = rho'.1
    exact e.root_edge_map
  root_bool_map := e.root_bool_map
  face_image_map := by intro F; exact e.faceEquiv_val F.1

private theorem ballIso_nonempty_congr_left
    {V'' : Type*} {E'' : Type*}
    {N : DirectedPlaneMapWithMissing V'' E''} {sigma : E'' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho') (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r M rho N sigma) ↔
      Nonempty (D39GeomBallIsoV2 r M' rho' N sigma) := by
  constructor
  · rintro ⟨b⟩
    exact ⟨DirectedDistances.PaperProofs.Section3.trans
      (e.symm.toBallIsoV2 r hr) b⟩
  · rintro ⟨b⟩
    exact ⟨DirectedDistances.PaperProofs.Section3.trans
      (e.toBallIsoV2 r hr) b⟩

private theorem ballIso_nonempty_congr_right
    {V'' : Type*} {E'' : Type*}
    {N : DirectedPlaneMapWithMissing V'' E''} {sigma : E'' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho') (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r N sigma M rho) ↔
      Nonempty (D39GeomBallIsoV2 r N sigma M' rho') := by
  constructor
  · rintro ⟨b⟩
    exact ⟨DirectedDistances.PaperProofs.Section3.trans
      b (e.toBallIsoV2 r hr)⟩
  · rintro ⟨b⟩
    exact ⟨DirectedDistances.PaperProofs.Section3.trans
      b (e.symm.toBallIsoV2 r hr)⟩

/-- Helper toward Definition 3.8: the local distance is invariant under a
rooted geometric dart isomorphism in its first argument. -/
theorem d39GeomDistanceV2_congr_left
    {V'' : Type*} {E'' : Type*}
    {N : DirectedPlaneMapWithMissing V'' E''} {sigma : E'' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    d39GeomDistanceV2 M rho N sigma = d39GeomDistanceV2 M' rho' N sigma := by
  unfold d39GeomDistanceV2
  apply iInf_congr
  intro r
  rw [propext (ballIso_nonempty_congr_left e r.1 r.2)]

/-- Helper toward Definition 3.8: the local distance is invariant under a
rooted geometric dart isomorphism in its second argument. -/
theorem d39GeomDistanceV2_congr_right
    {V'' : Type*} {E'' : Type*}
    {N : DirectedPlaneMapWithMissing V'' E''} {sigma : E'' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho') :
    d39GeomDistanceV2 N sigma M rho = d39GeomDistanceV2 N sigma M' rho' := by
  unfold d39GeomDistanceV2
  apply iInf_congr
  intro r
  rw [propext (ballIso_nonempty_congr_right e r.1 r.2)]

end D39GeomRootedMapIsoV2

end DirectedDistances.PaperProofs.Section3

end
