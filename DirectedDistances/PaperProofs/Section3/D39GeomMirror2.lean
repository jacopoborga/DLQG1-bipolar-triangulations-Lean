/- Copyright (c) 2026 DirectedDistances contributors. All rights reserved. -/
module

public import DirectedDistances.PaperProofs.Section3.D39GeomMirror
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso5
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassMetric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Helper toward Proposition 5.9: radius control for the reflected ordered root.
The convention is fixed by -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.PlanarMap Set
open scoped ENNReal Topology ComplexConjugate

namespace D39GeomBallIsoV2

variable {V E V' E' : Type*} {R r : ℕ}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {N : DirectedPlaneMapWithMissing V' E'} {sigma : E' × Bool}

/-- Helper toward Proposition 5.9: a ball isomorphism carries the second
ordered root endpoint to the second ordered root endpoint. -/
theorem root_other_map (e : D39GeomBallIsoV2 R M rho N sigma) :
    (e.vertexEquiv ⟨d39GeomRootOtherVertex M rho, by
      have h := d39GeomRootEdge_mem M rho e.radius_pos
      cases hb : rho.2
      · simpa [d39GeomRootOtherVertex, hb] using h.1
      · simpa [d39GeomRootOtherVertex, hb] using h.2⟩).1 =
      d39GeomRootOtherVertex N sigma := by
  let a := (⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩ :
    {a // a ∈ d39GeomBallEdges M rho R})
  have hs := e.src_map a
  have ht := e.tgt_map a
  have he : (e.edgeEquiv a).1 = sigma.1 := e.root_edge_map
  have hb : sigma.2 = Bool.xor rho.2 (e.edgeFlip a) := e.root_bool_map
  cases hρ : rho.2 <;> cases hf : e.edgeFlip a <;>
    simp only [hρ, hf, Bool.false_xor, Bool.true_xor, Bool.not_false,
      Bool.not_true] at hb <;>
    simp [d39GeomRootOtherVertex, hρ, hb, hf, he] at hs ht ⊢ <;>
    assumption

/-- Helper toward Proposition 5.9: adjacency transports inside the enclosing
ball, with edge identities and endpoint flips retained. -/
theorem mirror_adj_map (e : D39GeomBallIsoV2 R M rho N sigma)
    (v w : {v // v ∈ d39GeomBallVertices M rho R})
    (hv : (d39GeomGraph M).Adj v.1 w.1) :
    (d39GeomGraph N).Adj (e.vertexEquiv v).1 (e.vertexEquiv w).1 := by
  rcases hv with ⟨hne, a, ha | ha⟩
  all_goals
    have hne' : (e.vertexEquiv v).1 ≠ (e.vertexEquiv w).1 := by
      intro h
      exact hne (congrArg Subtype.val (e.vertexEquiv.injective (Subtype.ext h)))
  · let b : {a // a ∈ d39GeomBallEdges M rho R} :=
      ⟨a, by simp [d39GeomBallEdges, ha.1, ha.2]⟩
    have hs : (e.vertexEquiv v).1 =
        if e.edgeFlip b then N.tgt (e.edgeEquiv b).1 else N.src (e.edgeEquiv b).1 := by
      simpa [b, ha.1] using e.src_map b
    have ht : (e.vertexEquiv w).1 =
        if e.edgeFlip b then N.src (e.edgeEquiv b).1 else N.tgt (e.edgeEquiv b).1 := by
      simpa [b, ha.2] using e.tgt_map b
    refine ⟨hne', (e.edgeEquiv b).1, ?_⟩
    cases hf : e.edgeFlip b
    · exact Or.inl ⟨by simpa [hf] using hs.symm, by simpa [hf] using ht.symm⟩
    · exact Or.inr ⟨by simpa [hf] using ht.symm, by simpa [hf] using hs.symm⟩
  · let b : {a // a ∈ d39GeomBallEdges M rho R} :=
      ⟨a, by simp [d39GeomBallEdges, ha.1, ha.2]⟩
    have hs : (e.vertexEquiv w).1 =
        if e.edgeFlip b then N.tgt (e.edgeEquiv b).1 else N.src (e.edgeEquiv b).1 := by
      simpa [b, ha.1] using e.src_map b
    have ht : (e.vertexEquiv v).1 =
        if e.edgeFlip b then N.src (e.edgeEquiv b).1 else N.tgt (e.edgeEquiv b).1 := by
      simpa [b, ha.2] using e.tgt_map b
    refine ⟨hne', (e.edgeEquiv b).1, ?_⟩
    cases hf : e.edgeFlip b
    · exact Or.inr ⟨by simpa [hf] using hs.symm, by simpa [hf] using ht.symm⟩
    · exact Or.inl ⟨by simpa [hf] using ht.symm, by simpa [hf] using hs.symm⟩

/-- Helper toward Proposition 5.9: walks contained in an enclosing ball
transport without changing their lengths. -/
theorem mirror_map_walk (e : D39GeomBallIsoV2 R M rho N sigma) {v w : V}
    (p : (d39GeomGraph M).Walk v w)
    (hp : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M rho R) :
    ∃ q : (d39GeomGraph N).Walk
      (e.vertexEquiv ⟨v, by simpa using hp 0 (Nat.zero_le _)⟩).1
      (e.vertexEquiv ⟨w, by simpa using hp p.length le_rfl⟩).1,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons v x w hadj p ih =>
    have hx : x ∈ d39GeomBallVertices M rho R := by simpa using hp 1 (by simp)
    have htail : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M rho R := by
      intro i hi
      simpa using hp (i + 1) (by simpa using Nat.succ_le_succ hi)
    obtain ⟨q, hq⟩ := ih htail
    have ha := e.mirror_adj_map ⟨v, by simpa using hp 0 (Nat.zero_le _)⟩ ⟨x, hx⟩ hadj
    exact ⟨SimpleGraph.Walk.cons ha q, by simp [hq]⟩

/-- Helper toward Proposition 5.9: a radius-`r` ball about the second root
endpoint maps into its counterpart under an enclosing radius-`r+1` map. -/
theorem mirror_vertex_mem (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (v : {v // v ∈ d39GeomBallVertices M rho (r + 1)})
    (hv : v.1 ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r) :
    (e.vertexEquiv v).1 ∈
      d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r := by
  have hv' : (d39GeomGraph M).edist (d39GeomRootOtherVertex M rho) v.1 ≤ (r : ℕ∞) := by
    change d39GeomGraphDistance M.geomMirror
      (d39GeomRootVertex M.geomMirror (d39GeomMirrorRoot rho)) v.1 ≤ _ at hv
    rw [d39GeomRootVertex_geomMirror] at hv
    exact hv
  have hfinite : (d39GeomGraph M).edist (d39GeomRootOtherVertex M rho) v.1 ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hv'
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ r := by
    have hh : (p.length : ℕ∞) ≤ (r : ℕ∞) := hp.trans_le hv'
    exact_mod_cast hh
  have hpath : ∀ i, i ≤ p.length →
      p.getVert i ∈ d39GeomBallVertices M rho (r + 1) := by
    intro i hi
    apply d39GeomMirror_ballVertices_subset M rho r
    change (d39GeomGraph M).edist
      (d39GeomRootVertex M.geomMirror (d39GeomMirrorRoot rho)) _ ≤ (r : ℕ∞)
    rw [d39GeomRootVertex_geomMirror]
    exact (p.take i).edist_le.trans (by
      have hh : (p.take i).length ≤ r := by
        rw [SimpleGraph.Walk.take_length]
        omega
      exact_mod_cast hh)
  obtain ⟨q, hq⟩ := e.mirror_map_walk p hpath
  have hs : (e.vertexEquiv ⟨d39GeomRootOtherVertex M rho,
      by simpa using hpath 0 (Nat.zero_le _)⟩).1 =
      d39GeomRootOtherVertex N sigma := e.root_other_map
  have ht : (e.vertexEquiv ⟨v.1, v.2⟩).1 =
      (e.vertexEquiv v).1 := rfl
  change (d39GeomGraph N).edist
    (d39GeomRootVertex N.geomMirror (d39GeomMirrorRoot sigma)) _ ≤ (r : ℕ∞)
  rw [d39GeomRootVertex_geomMirror]
  calc
    _ ≤ ((q.copy hs ht).length : ℕ∞) := (q.copy hs ht).edist_le
    _ = (p.length : ℕ∞) := by rw [SimpleGraph.Walk.length_copy, hq]
    _ ≤ (r : ℕ∞) := by exact_mod_cast hlen

/-- Helper toward Proposition 5.9: the enclosing vertex equivalence preserves
membership in the reflected, recentered smaller balls in both directions. -/
theorem mirror_vertex_mem_iff (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (v : {v // v ∈ d39GeomBallVertices M rho (r + 1)}) :
    v.1 ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r ↔
      (e.vertexEquiv v).1 ∈
        d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r := by
  constructor
  · exact e.mirror_vertex_mem v
  · intro h
    have hh := (D39GeomBallIsoV2.symm e).mirror_vertex_mem (e.vertexEquiv v) h
    simpa [D39GeomBallIsoV2.symm] using hh

/-- Helper toward Proposition 5.9: restrict the enclosing vertex equivalence
to the reflected smaller balls. -/
@[expose] def mirrorVertices (e : D39GeomBallIsoV2 (r + 1) M rho N sigma) :
    {v // v ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r} ≃
      {v // v ∈ d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r} :=
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun v => v ∈ d39GeomBallVertices M rho (r + 1))
    (q := fun v => v ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r)
    (fun {_} h => d39GeomMirror_ballVertices_subset M rho r h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun v => v ∈ d39GeomBallVertices N sigma (r + 1))
    (q := fun v => v ∈ d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r)
    (fun {_} h => d39GeomMirror_ballVertices_subset N sigma r h)
  L.symm.trans ((e.vertexEquiv.subtypeEquiv (fun v => e.mirror_vertex_mem_iff v)).trans R)

/-- Helper toward Proposition 5.9: reflected edge balls lie in the enclosing
original edge balls. -/
theorem mirror_edge_subset (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (r : ℕ) :
    d39GeomBallEdges M.geomMirror (d39GeomMirrorRoot rho) r ⊆
      d39GeomBallEdges M rho (r + 1) := by
  intro a ha
  exact ⟨d39GeomMirror_ballVertices_subset M rho r ha.1,
    d39GeomMirror_ballVertices_subset M rho r ha.2⟩

/-- Helper toward Proposition 5.9: edge membership in reflected smaller
balls is preserved by the enclosing edge equivalence. -/
theorem mirror_edge_mem_iff (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (a : {a // a ∈ d39GeomBallEdges M rho (r + 1)}) :
    a.1 ∈ d39GeomBallEdges M.geomMirror (d39GeomMirrorRoot rho) r ↔
      (e.edgeEquiv a).1 ∈
        d39GeomBallEdges N.geomMirror (d39GeomMirrorRoot sigma) r := by
  have hs := e.mirror_vertex_mem_iff ⟨M.src a.1, a.2.1⟩
  have ht := e.mirror_vertex_mem_iff ⟨M.tgt a.1, a.2.2⟩
  rw [e.src_map a] at hs
  rw [e.tgt_map a] at ht
  change (M.src a.1 ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r ∧
      M.tgt a.1 ∈ d39GeomBallVertices M.geomMirror (d39GeomMirrorRoot rho) r) ↔
    (N.src (e.edgeEquiv a).1 ∈ d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r ∧
      N.tgt (e.edgeEquiv a).1 ∈ d39GeomBallVertices N.geomMirror (d39GeomMirrorRoot sigma) r)
  cases hf : e.edgeFlip a
  · simpa [hf] using and_congr hs ht
  · simpa [hf, and_comm] using and_congr hs ht

/-- Helper toward Proposition 5.9: restrict the enclosing edge equivalence
to reflected smaller balls while keeping all edge identities. -/
@[expose] def mirrorEdges (e : D39GeomBallIsoV2 (r + 1) M rho N sigma) :
    {a // a ∈ d39GeomBallEdges M.geomMirror (d39GeomMirrorRoot rho) r} ≃
      {a // a ∈ d39GeomBallEdges N.geomMirror (d39GeomMirrorRoot sigma) r} :=
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun a => a ∈ d39GeomBallEdges M rho (r + 1))
    (q := fun a => a ∈ d39GeomBallEdges M.geomMirror (d39GeomMirrorRoot rho) r)
    (fun {_} h => mirror_edge_subset M rho r h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun a => a ∈ d39GeomBallEdges N sigma (r + 1))
    (q := fun a => a ∈ d39GeomBallEdges N.geomMirror (d39GeomMirrorRoot sigma) r)
    (fun {_} h => mirror_edge_subset N sigma r h)
  L.symm.trans ((e.edgeEquiv.subtypeEquiv (fun a => e.mirror_edge_mem_iff a)).trans R)

/-- Helper toward Proposition 5.9: before applying conjugation to faces,
recenter the retained-face predicate at the second root endpoint. -/
theorem mirror_original_face_map (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (F : {F // F ∈ d39GeomRetainedFaces M rho (r + 1)})
    (hF : F.1 ∈ d39GeomRetainedFaces M (d39GeomMirrorRoot rho) r) :
    (e.faceEquiv F).1 ∈ d39GeomRetainedFaces N (d39GeomMirrorRoot sigma) r := by
  intro w hw
  have hwR := (e.faceEquiv F).2 w hw
  let v := e.vertexEquiv.symm ⟨w, hwR⟩
  have hp : e.h (M.pos v.1) = N.pos w := by simpa [v] using e.pos_map v
  have hc : M.pos v.1 ∈ closure F.1.val := by
    have hh : N.pos w ∈ e.h '' closure F.1.val := by
      rw [e.h.image_closure, e.face_image_map F]
      exact hw
    obtain ⟨z, hz, he⟩ := hh
    have hz' : z = M.pos v.1 := e.h.injective (he.trans hp.symm)
    simpa [hz'] using hz
  have hs := e.mirror_vertex_mem v (hF v.1 hc)
  change (e.vertexEquiv v).1 ∈ d39GeomBallVertices N (d39GeomMirrorRoot sigma) r at hs
  simpa [v] using hs

/-- Helper toward Proposition 5.9: the original face equivalence preserves
the predicate obtained by recentering at the second root endpoint. -/
theorem mirror_original_face_iff (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (F : {F // F ∈ d39GeomRetainedFaces M rho (r + 1)}) :
    F.1 ∈ d39GeomRetainedFaces M (d39GeomMirrorRoot rho) r ↔
      (e.faceEquiv F).1 ∈ d39GeomRetainedFaces N (d39GeomMirrorRoot sigma) r := by
  constructor
  · exact e.mirror_original_face_map F
  · intro h
    have hh := (D39GeomBallIsoV2.symm e).mirror_original_face_map (e.faceEquiv F) h
    simpa [D39GeomBallIsoV2.symm] using hh

/-- Helper toward Proposition 5.9: the original smaller recentered faces
belong to the enclosing original retained-face set. -/
theorem mirror_original_face_subset
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) :
    d39GeomRetainedFaces M (d39GeomMirrorRoot rho) r ⊆
      d39GeomRetainedFaces M rho (r + 1) := by
  intro F hF v hv
  exact d39GeomMirror_ballVertices_subset M rho r (hF v hv)

/-- Helper toward Proposition 5.9: recenter the original retained-face
equivalence, before reflecting the complementary faces. -/
@[expose] def mirrorOriginalFaces (e : D39GeomBallIsoV2 (r + 1) M rho N sigma) :
    {F // F ∈ d39GeomRetainedFaces M (d39GeomMirrorRoot rho) r} ≃
      {F // F ∈ d39GeomRetainedFaces N (d39GeomMirrorRoot sigma) r} :=
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun F => F ∈ d39GeomRetainedFaces M rho (r + 1))
    (q := fun F => F ∈ d39GeomRetainedFaces M (d39GeomMirrorRoot rho) r)
    (fun {_} h => mirror_original_face_subset M rho r h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun F => F ∈ d39GeomRetainedFaces N sigma (r + 1))
    (q := fun F => F ∈ d39GeomRetainedFaces N (d39GeomMirrorRoot sigma) r)
    (fun {_} h => mirror_original_face_subset N sigma r h)
  L.symm.trans ((e.faceEquiv.subtypeEquiv
    (fun F => e.mirror_original_face_iff F)).trans R)

end D39GeomBallIsoV2

/-- Helper toward Proposition 5.9: reflection identifies original faces
with reflected faces, preserving the recentered retained-face predicate. -/
theorem d39GeomMirror_face_retained_iff {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ)
    (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    F ∈ d39GeomRetainedFaces M rho r ↔
      M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv.faceEquiv F ∈
        d39GeomRetainedFaces M.geomMirror rho r := by
  have hc : ∀ v, M.geomMirror.pos v ∈
      closure (M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv.faceEquiv F).val ↔
      M.pos v ∈ closure F.val := by
    intro v
    change geomConj (M.pos v) ∈ closure (geomConj '' F.val) ↔ _
    rw [← geomConj.image_closure]
    exact geomConj.injective.mem_set_image
  constructor
  · intro h v hv
    exact h v ((hc v).mp hv)
  · intro h v hv
    exact h v ((hc v).mpr hv)

/-- Helper toward Proposition 5.9: reflection of retained original faces is
a bijection of retained-face carriers, without changing the root mark. -/
@[expose] def d39GeomMirrorFaces {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) :
    {F // F ∈ d39GeomRetainedFaces M rho r} ≃
      {F // F ∈ d39GeomRetainedFaces M.geomMirror rho r} :=
  M.toPlaneMapWithMissing.toPlaneGraphDrawing.geomMirrorEquiv.faceEquiv.subtypeEquiv
    (fun F => d39GeomMirror_face_retained_iff M rho r F)

/-- Helper toward Proposition 5.9: reflection sends a retained face to its
pointwise complex-conjugate image. -/
theorem d39GeomMirrorFaces_val {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ)
    (F : {F // F ∈ d39GeomRetainedFaces M rho r}) :
    (d39GeomMirrorFaces M rho r F).1.val = geomConj '' F.1.val := rfl

namespace D39GeomBallIsoV2
variable {V E V' E' : Type*} {r : ℕ}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {N : DirectedPlaneMapWithMissing V' E'} {sigma : E' × Bool}

/-- Helper toward Proposition 5.9: the reflected recentered smaller faces
are transported by the enclosing ball isomorphism. -/
@[expose] def mirrorFaces (e : D39GeomBallIsoV2 (r + 1) M rho N sigma) :
    {F // F ∈ d39GeomRetainedFaces M.geomMirror (d39GeomMirrorRoot rho) r} ≃
      {F // F ∈ d39GeomRetainedFaces N.geomMirror (d39GeomMirrorRoot sigma) r} :=
  (d39GeomMirrorFaces M (d39GeomMirrorRoot rho) r).symm.trans
    (e.mirrorOriginalFaces.trans (d39GeomMirrorFaces N (d39GeomMirrorRoot sigma) r))

/-- Helper toward Proposition 5.9: conjugation of the enclosing
homeomorphism realizes the reflected face equivalence. -/
theorem mirror_faces_image (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (F : {F // F ∈ d39GeomRetainedFaces M.geomMirror (d39GeomMirrorRoot rho) r}) :
    geomMirrorHomeomorph e.h '' F.1.val = (e.mirrorFaces F).1.val := by
  let F0 := (d39GeomMirrorFaces M (d39GeomMirrorRoot rho) r).symm F
  have hF : F.1.val = geomConj '' F0.1.val := by
    have hh := d39GeomMirrorFaces_val M (d39GeomMirrorRoot rho) r F0
    simpa [F0] using hh
  have hmap : e.h '' F0.1.val = (e.mirrorOriginalFaces F0).1.val :=
    e.face_image_map ⟨F0.1, mirror_original_face_subset M rho r F0.2⟩
  change geomMirrorHomeomorph e.h '' F.1.val =
    geomConj '' (e.mirrorOriginalFaces F0).1.val
  rw [hF, ← hmap]
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e.h x, ⟨x, hx, rfl⟩, by simp [geomMirrorHomeomorph_apply, geomConj]⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨geomConj x, ⟨x, hx, rfl⟩, by simp [geomMirrorHomeomorph_apply, geomConj]⟩

/-- Helper toward Proposition 5.9: an enclosing radius-`r+1` geometric
isomorphism induces a radius-`r` isomorphism after reflection and root reversal.
The ordered-root convention is -/
@[expose] def mirrorShift (e : D39GeomBallIsoV2 (r + 1) M rho N sigma)
    (hr : 0 < r) :
    D39GeomBallIsoV2 r M.geomMirror (d39GeomMirrorRoot rho)
      N.geomMirror (d39GeomMirrorRoot sigma) where
  radius_pos := hr
  h := geomMirrorHomeomorph e.h
  orientationPreserving := OrientationPreserving.mirror_conjugation e.orientationPreserving
  vertexEquiv := e.mirrorVertices
  edgeEquiv := e.mirrorEdges
  faceEquiv := e.mirrorFaces
  edgeFlip := fun a => e.edgeFlip ⟨a.1, mirror_edge_subset M rho r a.2⟩
  pos_map := by
    intro v
    change conj (e.h (conj (conj (M.pos v.1)))) =
      conj (N.pos (e.vertexEquiv
        ⟨v.1, d39GeomMirror_ballVertices_subset M rho r v.2⟩).1)
    rw [Complex.conj_conj]
    exact congrArg conj (e.pos_map
      ⟨v.1, d39GeomMirror_ballVertices_subset M rho r v.2⟩)
  edgeParam := fun a => e.edgeParam ⟨a.1, mirror_edge_subset M rho r a.2⟩
  edgeParam_mono := by intro a ha; exact e.edgeParam_mono _ ha
  edgeParam_anti := by intro a ha; exact e.edgeParam_anti _ ha
  arc_map := by
    intro a t
    change conj (e.h (conj (conj (M.arc a.1 t)))) =
      conj (N.arc (e.edgeEquiv ⟨a.1, mirror_edge_subset M rho r a.2⟩).1
        (e.edgeParam ⟨a.1, mirror_edge_subset M rho r a.2⟩ t))
    rw [Complex.conj_conj]
    exact congrArg conj (e.arc_map ⟨a.1, mirror_edge_subset M rho r a.2⟩ t)
  src_map := by
    intro a
    exact e.src_map ⟨a.1, mirror_edge_subset M rho r a.2⟩
  tgt_map := by
    intro a
    exact e.tgt_map ⟨a.1, mirror_edge_subset M rho r a.2⟩
  missing_map := by
    intro a
    exact e.missing_map ⟨a.1, mirror_edge_subset M rho r a.2⟩
  orientation_map := by
    intro a ha
    exact e.orientation_map ⟨a.1, mirror_edge_subset M rho r a.2⟩ ha
  root_edge_map := e.root_edge_map
  root_bool_map := by
    change (!sigma.2) = Bool.xor (!rho.2)
      (e.edgeFlip ⟨rho.1, mirror_edge_subset M rho r
        (d39GeomRootEdge_mem M.geomMirror (d39GeomMirrorRoot rho) hr)⟩)
    have hb := e.root_bool_map
    generalize e.edgeFlip ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩ = b at hb ⊢
    cases hρ : rho.2 <;> cases b <;> simp_all
  face_image_map := e.mirror_faces_image

end D39GeomBallIsoV2



theorem d39GeomMirror_shift_transport {V E V' E' : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (N : DirectedPlaneMapWithMissing V' E') (sigma : E' × Bool)
    (_hM : D39GeomDomain M rho) (_hN : D39GeomDomain N sigma)
    (_hm : M.toPlaneMapWithMissing.missing rho.1)
    (_hn : N.toPlaneMapWithMissing.missing sigma.1)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 (r + 1) M rho N sigma) →
      Nonempty (D39GeomBallIsoV2 r M.geomMirror (d39GeomMirrorRoot rho)
        N.geomMirror (d39GeomMirrorRoot sigma)) := by
  rintro ⟨e⟩
  exact ⟨e.mirrorShift hr⟩

/-- Helper toward Proposition 5.9: on distances at most one quarter,
reflection and reversal of the ordered root enlarge distance by at most two.
This is the small-distance form recorded in `D39GeomMirror.lean`. -/
theorem d39GeomDistanceV2_mirror_le_two_mul {V E V' E' : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (N : DirectedPlaneMapWithMissing V' E') (sigma : E' × Bool)
    (hsmall : d39GeomDistanceV2 M rho N sigma ≤ (1 / 4 : ℝ≥0∞)) :
    d39GeomDistanceV2 M.geomMirror (d39GeomMirrorRoot rho)
        N.geomMirror (d39GeomMirrorRoot sigma) ≤
      2 * d39GeomDistanceV2 M rho N sigma := by
  have h2 : Nonempty (D39GeomBallIsoV2 2 M rho N sigma) := by
    apply (d39GeomDistanceV2_le_iff_nonempty (r := 2) (by omega)).mp
    convert hsmall using 1
    norm_num [← ENNReal.inv_pow]
  have hbase : d39GeomDistanceV2 M.geomMirror (d39GeomMirrorRoot rho)
      N.geomMirror (d39GeomMirrorRoot sigma) ≤ (1 / 2 : ℝ≥0∞) := by
    obtain ⟨e⟩ := h2
    simpa using d39GeomDistanceV2_le_of_nonempty (r := 1) (by omega)
      ⟨e.mirrorShift (r := 1) (by omega)⟩
  unfold d39GeomDistanceV2
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro q
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  rintro ⟨e⟩
  change d39GeomDistanceV2 M.geomMirror (d39GeomMirrorRoot rho)
    N.geomMirror (d39GeomMirrorRoot sigma) ≤ 2 * (1 / 2 : ℝ≥0∞) ^ q.1
  by_cases hq : q.1 = 1
  · exact hbase.trans (by norm_num [hq, ENNReal.mul_inv_cancel])
  · have hs : 0 < q.1 - 1 := by have := q.2; omega
    have heq : q.1 = (q.1 - 1) + 1 := by have := q.2; omega
    have e' : D39GeomBallIsoV2 ((q.1 - 1) + 1) M rho N sigma := heq ▸ e
    have hb := d39GeomDistanceV2_le_of_nonempty hs ⟨e'.mirrorShift hs⟩
    apply hb.trans_eq
    rw [heq, pow_succ]
    calc
      (1 / 2 : ℝ≥0∞) ^ (q.1 - 1) =
          (2 * (1 / 2 : ℝ≥0∞)) * (1 / 2 : ℝ≥0∞) ^ (q.1 - 1) := by
            norm_num [ENNReal.mul_inv_cancel]
      _ = 2 * ((1 / 2 : ℝ≥0∞) ^ (q.1 - 1) * (1 / 2 : ℝ≥0∞)) := by ac_rfl

namespace D39GeomRootedMapIsoV2

/-- Helper toward Proposition 5.9: a whole-map rooted geometric isomorphism
survives reflection and reversal of both ordered root marks. -/
@[expose] def geomMirror {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {sigma : E' × Bool}
    (e : D39GeomRootedMapIsoV2 M rho N sigma) :
    D39GeomRootedMapIsoV2 M.geomMirror (d39GeomMirrorRoot rho)
      N.geomMirror (d39GeomMirrorRoot sigma) where
  h := geomMirrorHomeomorph e.h
  orientationPreserving := OrientationPreserving.mirror_conjugation e.orientationPreserving
  vertexEquiv := e.vertexEquiv
  edgeEquiv := e.edgeEquiv
  edgeFlip := e.edgeFlip
  edgeParam := e.edgeParam
  edgeParam_mono := e.edgeParam_mono
  edgeParam_anti := e.edgeParam_anti
  pos_map := by
    intro v
    change conj (e.h (conj (conj (M.pos v)))) = conj (N.pos (e.vertexEquiv v))
    rw [Complex.conj_conj]
    exact congrArg conj (e.pos_map v)
  arc_map := by
    intro a t
    change conj (e.h (conj (conj (M.arc a t)))) =
      conj (N.arc (e.edgeEquiv a) (e.edgeParam a t))
    rw [Complex.conj_conj]
    exact congrArg conj (e.arc_map a t)
  src_map := e.src_map
  tgt_map := e.tgt_map
  missing_map := e.missing_map
  orientation_map := e.orientation_map
  root_edge_map := e.root_edge_map
  root_bool_map := by
    change (!sigma.2) = Bool.xor (!rho.2) (e.edgeFlip rho.1)
    have hb := e.root_bool_map
    cases hρ : rho.2 <;> cases hf : e.edgeFlip rho.1 <;> simp_all

end D39GeomRootedMapIsoV2



abbrev D39MissingRootedMap :=
  {A : D39DomainRootedMap // A.map.toPlaneMapWithMissing.missing A.root.1}



@[expose] def d39MissingMirror (A : D39MissingRootedMap) : D39MissingRootedMap :=
  ⟨{ V := A.1.V, E := A.1.E, map := A.1.map.geomMirror,
      root := d39GeomMirrorRoot A.1.root,
      domain := A.1.domain.geomMirror A.2 }, A.2⟩



@[expose] def d39MissingSetoid : Setoid D39MissingRootedMap :=
  Setoid.comap Subtype.val d39DomainSetoid

/-- Helper toward Proposition 5.9: the source class space restricted to
maps with a missing ordered root. -/
abbrev D39MissingMapClass := Quotient d39MissingSetoid

/-- Helper toward Proposition 5.9: forget the missing-root certificate
without changing the rooted geometric class. -/
@[expose] def d39MissingClassForget : D39MissingMapClass → D39GeomRootedMapClass :=
  Quotient.map Subtype.val (by intro A B h; exact h)

/-- Helper toward Proposition 5.9: reflection descends to whole-map
isomorphism classes on the missing-root source carrier. -/
@[expose] def d39MissingClassMirror : D39MissingMapClass → D39MissingMapClass :=
  Quotient.map d39MissingMirror (by
    intro A B h
    obtain ⟨e⟩ := h
    exact ⟨e.geomMirror⟩)

/-- Helper toward Proposition 5.9: the missing-root class topology is the
source pseudoemetric topology restricted by forgetting the certificate. -/
noncomputable instance : PseudoEMetricSpace D39MissingMapClass :=
  PseudoEMetricSpace.induced d39MissingClassForget inferInstance



theorem d39MissingMapClass_edist_mk (A B : D39MissingRootedMap) :
    edist (Quotient.mk d39MissingSetoid A) (Quotient.mk d39MissingSetoid B) =
      d39GeomDistanceV2 A.1.map A.1.root B.1.map B.1.root := rfl

/-- Helper toward Proposition 5.9: the descended mirror satisfies the
recorded factor-two estimate whenever source distance is at most one quarter. -/
theorem d39MissingClassMirror_edist_le (A B : D39MissingMapClass)
    (hsmall : edist A B ≤ (1 / 4 : ℝ≥0∞)) :
    edist (d39MissingClassMirror A) (d39MissingClassMirror B) ≤ 2 * edist A B := by
  induction A using Quotient.inductionOn with
  | _ A =>
    induction B using Quotient.inductionOn with
    | _ B =>
      exact d39GeomDistanceV2_mirror_le_two_mul A.1.map A.1.root B.1.map B.1.root hsmall

/-- Helper toward Proposition 5.9: forgetting the missing-root certificate
embeds these classes into the existing source class space without identifying
any additional maps. -/
theorem d39MissingClassForget_injective : Function.Injective d39MissingClassForget := by
  intro A B
  refine Quotient.inductionOn₂ A B ?_
  intro A B h
  change Quotient.mk d39DomainSetoid A.1 = Quotient.mk d39DomainSetoid B.1 at h
  apply Quotient.sound
  change d39DomainSetoid A.1 B.1
  exact Quotient.exact h



theorem d39MissingClassForget_isometry : Isometry d39MissingClassForget := by
  intro A B
  rfl

/-- Helper toward Proposition 5.9: the mirror on the missing-root source
class space is uniformly continuous, using the local factor-two estimate. -/
theorem d39MissingClassMirror_uniformContinuous : UniformContinuous d39MissingClassMirror := by
  apply EMetric.uniformContinuous_iff_le.mpr
  intro ε hε
  refine ⟨min (1 / 4 : ℝ≥0∞) (ε / 2), lt_min (by norm_num)
    (ENNReal.div_pos (ne_of_gt hε) (by norm_num)), ?_⟩
  intro A B hAB
  have hsmall : edist A B ≤ (1 / 4 : ℝ≥0∞) :=
    hAB.trans (min_le_left _ _)
  calc
    edist (d39MissingClassMirror A) (d39MissingClassMirror B) ≤ 2 * edist A B :=
      d39MissingClassMirror_edist_le A B hsmall
    _ ≤ 2 * (ε / 2) := by gcongr; exact hAB.trans (min_le_right _ _)
    _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Helper toward Proposition 5.9: root-swapping reflection is continuous
for the source pseudometric topology on missing-root geometric classes. -/
theorem d39MissingClassMirror_continuous : Continuous d39MissingClassMirror :=
  d39MissingClassMirror_uniformContinuous.continuous

/-- Helper toward Proposition 5.9: root-swapping reflection is measurable
for the Borel sigma algebras of the source pseudometric topology. -/
theorem d39MissingClassMirror_borel_measurable :
    @Measurable D39MissingMapClass D39MissingMapClass
      (borel D39MissingMapClass) (borel D39MissingMapClass) d39MissingClassMirror :=
  d39MissingClassMirror_continuous.borel_measurable

end DirectedDistances.PaperProofs.Section3
end
