/- Copyright (c) 2026 DirectedDistances contributors. All rights reserved. -/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso
public import DirectedDistances.PaperProofs.Section3.D39GeometricDomainTransport

/-! # Symmetry and storage invariance for geometric dart isomorphisms -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open unitInterval
open scoped ENNReal Topology

universe uV uE uV' uE'

private theorem strictMono_homeomorph_symm {α : Type*} [LinearOrder α] [TopologicalSpace α]
    (f : Homeomorph α α) (hf : StrictMono f) : StrictMono f.symm := by
  intro x y hxy
  rcases lt_trichotomy (f.symm x) (f.symm y) with hlt | heq | hgt
  · exact hlt
  · have hxy' : x = y := by simpa using congrArg f heq
    exfalso
    exact (ne_of_lt hxy) hxy'
  · have hyx : y < x := by simpa using hf hgt
    exfalso
    exact (not_lt_of_ge (le_of_lt hxy)) hyx

private theorem strictAnti_homeomorph_symm {α : Type*} [LinearOrder α] [TopologicalSpace α]
    (f : Homeomorph α α) (hf : StrictAnti f) : StrictAnti f.symm := by
  intro x y hxy
  rcases lt_trichotomy (f.symm y) (f.symm x) with hlt | heq | hgt
  · exact hlt
  · have hxy' : x = y := by simpa using (congrArg f heq).symm
    exfalso
    exact (ne_of_lt hxy) hxy'
  · have hyx : y < x := by simpa using hf hgt
    exfalso
    exact (not_lt_of_ge (le_of_lt hxy)) hyx

namespace D39GeomBallIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: reverse a geometric dart ball isomorphism. -/
@[expose] def symm (e : D39GeomBallIsoV2 r M rho M' rho') :
    D39GeomBallIsoV2 r M' rho' M rho where
  radius_pos := e.radius_pos
  h := e.h.symm
  orientationPreserving := OrientationPreserving.symm e.orientationPreserving
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  faceEquiv := e.faceEquiv.symm
  edgeFlip := fun a => e.edgeFlip (e.edgeEquiv.symm a)
  pos_map := by
    intro v
    have h := congrArg e.h.symm (e.pos_map (e.vertexEquiv.symm v))
    simpa using h.symm
  edgeParam := fun a => (e.edgeParam (e.edgeEquiv.symm a)).symm
  edgeParam_mono := by
    intro a ha
    exact strictMono_homeomorph_symm _
      (e.edgeParam_mono (e.edgeEquiv.symm a) ha)
  edgeParam_anti := by
    intro a ha
    exact strictAnti_homeomorph_symm _
      (e.edgeParam_anti (e.edgeEquiv.symm a) ha)
  arc_map := by
    intro a t
    let b := e.edgeEquiv.symm a
    have he : e.edgeEquiv b = a := e.edgeEquiv.apply_symm_apply a
    have h := e.arc_map b ((e.edgeParam b).symm t)
    rw [he, (e.edgeParam b).apply_symm_apply] at h
    calc
      e.h.symm (M'.toPlaneMapWithMissing.arc a.1 t) =
          e.h.symm (e.h (M.toPlaneMapWithMissing.arc b.1 ((e.edgeParam b).symm t))) :=
            congrArg e.h.symm h.symm
      _ = M.toPlaneMapWithMissing.arc b.1 ((e.edgeParam b).symm t) := by simp
  src_map := by
    intro a
    let b := e.edgeEquiv.symm a
    have he : e.edgeEquiv b = a := e.edgeEquiv.apply_symm_apply a
    cases hf : e.edgeFlip b
    · have hs : e.vertexEquiv
          ⟨M.toPlaneMapWithMissing.src b.1, b.2.1⟩ =
          ⟨M'.toPlaneMapWithMissing.src (e.edgeEquiv b).1, (e.edgeEquiv b).2.1⟩ := by
        apply Subtype.ext
        simpa [hf, he] using e.src_map b
      have hv := congrArg e.vertexEquiv.symm hs
      simpa [b, he] using (congrArg Subtype.val hv).symm
    · have ht : e.vertexEquiv
          ⟨M.toPlaneMapWithMissing.tgt b.1, b.2.2⟩ =
          ⟨M'.toPlaneMapWithMissing.src (e.edgeEquiv b).1, (e.edgeEquiv b).2.1⟩ := by
        apply Subtype.ext
        simpa [hf, he] using e.tgt_map b
      have hv := congrArg e.vertexEquiv.symm ht
      simpa [b, he] using (congrArg Subtype.val hv).symm
  tgt_map := by
    intro a
    let b := e.edgeEquiv.symm a
    have he : e.edgeEquiv b = a := e.edgeEquiv.apply_symm_apply a
    cases hf : e.edgeFlip b
    · have ht : e.vertexEquiv
          ⟨M.toPlaneMapWithMissing.tgt b.1, b.2.2⟩ =
          ⟨M'.toPlaneMapWithMissing.tgt (e.edgeEquiv b).1, (e.edgeEquiv b).2.2⟩ := by
        apply Subtype.ext
        simpa [hf, he] using e.tgt_map b
      have hv := congrArg e.vertexEquiv.symm ht
      simpa [b, he] using (congrArg Subtype.val hv).symm
    · have hs : e.vertexEquiv
          ⟨M.toPlaneMapWithMissing.src b.1, b.2.1⟩ =
          ⟨M'.toPlaneMapWithMissing.tgt (e.edgeEquiv b).1, (e.edgeEquiv b).2.2⟩ := by
        apply Subtype.ext
        simpa [hf, he] using e.src_map b
      have hv := congrArg e.vertexEquiv.symm hs
      simpa [b, he] using (congrArg Subtype.val hv).symm
  missing_map := by
    intro a
    simpa using (e.missing_map (e.edgeEquiv.symm a)).symm
  orientation_map := by
    intro a ha
    let b := e.edgeEquiv.symm a
    have hm : ¬ M.toPlaneMapWithMissing.missing b.1 := by
      intro hmiss
      exact ha (by simpa [b, e.edgeEquiv.apply_symm_apply] using
        (e.missing_map b).mpr hmiss)
    have h := e.orientation_map b hm
    have hsub : (⟨(e.edgeEquiv b).1,
        by simpa [e.missing_map b] using hm⟩ :
        {x : E' // ¬ M'.toPlaneMapWithMissing.missing x}) = ⟨a.1, ha⟩ := by
      apply Subtype.ext
      change (e.edgeEquiv (e.edgeEquiv.symm a)).1 = a.1
      exact congrArg Subtype.val (e.edgeEquiv.apply_symm_apply a)
    rw [hsub] at h
    cases hf : e.edgeFlip b
    · simpa [b, hf, e.edgeEquiv.apply_symm_apply] using h.symm
    · cases hmval : M.forward ⟨b.1, hm⟩ <;>
        cases hpval : M'.forward ⟨a.1, ha⟩ <;>
        simp_all [b, e.edgeEquiv.apply_symm_apply]
  root_edge_map := by
    let a : {e // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    let b : {e // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    have he : e.edgeEquiv b = a := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map
    have hv := congrArg e.edgeEquiv.symm he
    simpa [a, b] using (congrArg Subtype.val hv).symm
  root_bool_map := by
    let a : {e // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    let b : {e // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    have he : e.edgeEquiv b = a := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map
    have hflip : e.edgeFlip (e.edgeEquiv.symm a) = e.edgeFlip b := by
      have hh := congrArg e.edgeEquiv.symm he
      have hh' : e.edgeEquiv.symm a = b := by simpa using hh.symm
      exact congrArg e.edgeFlip hh'
    have hroot := e.root_bool_map
    rw [← hflip] at hroot
    cases hb : rho.2 <;> cases hf : e.edgeFlip b <;>
      simp [a, b, hflip, hb, hf, hroot]
  face_image_map := by
    intro F
    have hF : e.h '' (e.faceEquiv.symm F).1 = F.1 := by
      simpa using e.face_image_map (e.faceEquiv.symm F)
    calc
      e.h.symm '' F.1 = e.h.symm '' (e.h '' (e.faceEquiv.symm F).1) := by rw [hF]
      _ = (e.faceEquiv.symm F).1 := by
        rw [Set.image_image]
        simp

end D39GeomBallIsoV2

/-- Helper toward Definition 3.8: the geometric distance is symmetric. -/
theorem d39GeomDistanceV2_comm {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) :
    d39GeomDistanceV2 M rho M' rho' = d39GeomDistanceV2 M' rho' M rho := by
  unfold d39GeomDistanceV2
  apply iInf_congr
  intro r
  apply le_antisymm
  · apply le_iInf
    intro h'
    have h : Nonempty (D39GeomBallIsoV2 r.1 M rho M' rho') := by
      rcases h' with ⟨e⟩
      exact ⟨e.symm⟩
    exact iInf_le (fun _ : Nonempty (D39GeomBallIsoV2 r.1 M rho M' rho') =>
      ((1 / 2 : ℝ≥0∞) ^ r.1)) h
  · apply le_iInf
    intro h
    have h' : Nonempty (D39GeomBallIsoV2 r.1 M' rho' M rho) := by
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    exact iInf_le (fun _ : Nonempty (D39GeomBallIsoV2 r.1 M' rho' M rho) =>
      ((1 / 2 : ℝ≥0∞) ^ r.1)) h'

/-- Helper toward Definition 3.8: endpoint storage preserves the rooted
geometric vertex ball. -/
private theorem d39GeomBallVertices_flipEdges {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (r : ℕ) :
    d39GeomBallVertices (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) r =
      d39GeomBallVertices M rho r := by
  classical
  let e := D39CombDartIso.storeFlip M rho S
  ext v
  change d39GeomGraphDistance (flipEdges M S)
      (d39GeomRootVertex (flipEdges M S)
        (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1))) v ≤ (r : ℕ∞) ↔
    d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (r : ℕ∞)
  have hbit : d39GeomEdgeFlipBit S = D39CombDartIso.membershipFlip S := by
    funext a
    simp [d39GeomEdgeFlipBit, D39CombDartIso.membershipFlip]
  have hMflip : flipEdges M S =
      M.endpointSwap (D39CombDartIso.membershipFlip S) := by
    simp [flipEdges, hbit]
  have hroot : d39GeomRootVertex
      (M.endpointSwap (D39CombDartIso.membershipFlip S))
        (rho.1, Bool.xor rho.2 (D39CombDartIso.membershipFlip S rho.1)) =
      d39GeomRootVertex M rho := by
    cases hb : rho.2 <;> cases hf : D39CombDartIso.membershipFlip S rho.1 <;>
      simp [d39GeomRootVertex, DirectedPlaneMapWithMissing.endpointSwap,
        PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hb, hf]
  have hd : d39GeomGraphDistance (flipEdges M S)
        (d39GeomRootVertex (flipEdges M S)
          (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1))) v =
      d39GeomGraphDistance M (d39GeomRootVertex M rho) v := by
    rw [hMflip, hbit]
    rw [hroot]
    simpa [e, D39CombDartIso.storeFlip, D39CombDartIso.membershipFlip] using
        (e.graphDistance_map (d39GeomRootVertex M rho) v).symm
  rw [hd]

/-- Helper toward Definition 3.8: endpoint storage preserves the identities
of edges in the rooted geometric ball. -/
private theorem d39GeomBallEdges_flipEdges {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (r : ℕ) :
    d39GeomBallEdges (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) r =
      d39GeomBallEdges M rho r := by
  classical
  ext a
  simp only [d39GeomBallEdges, Set.mem_ofPred_eq]
  rw [d39GeomBallVertices_flipEdges]
  by_cases hf : d39GeomEdgeFlipBit S a = true <;>
    simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap,
      PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hf,
      and_comm]

/-- Helper toward Definition 3.8: endpoint storage identifies the retained
faces of the rooted geometric ball. -/
private def d39GeomRetainedFaces_flipEquiv {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (r : ℕ) :
    {F // F ∈ d39GeomRetainedFaces M rho r} ≃
      {F // F ∈ d39GeomRetainedFaces (flipEdges M S)
        (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) r} := by
  classical
  let D := M.toPlaneMapWithMissing.toPlaneGraphDrawing
  let swap := d39GeomEdgeFlipBit S
  let φ := D.endpointSwapFaceEquiv swap
  have hVerts := d39GeomBallVertices_flipEdges M rho S r
  have hpos (v : V) :
      (flipEdges M S).toPlaneMapWithMissing.pos v =
        M.toPlaneMapWithMissing.pos v := by
    simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap,
      PlaneMapWithMissing.endpointSwap]
  refine {
    toFun := fun F => ⟨φ F.1, ?_⟩
    invFun := fun F => ⟨φ.symm F.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro v hv
    have hface : (φ F.1).val = F.1.val := by
      exact endpointSwapFace_val D swap F.1
    have hmem := F.2 v (by simpa [hpos, hface] using hv)
    exact hVerts.symm ▸ hmem
  · intro v hv
    have hface : (φ.symm F.1).val = F.1.val := by
      rfl
    have hmem := F.2 v (by simpa [hpos, hface] using hv)
    exact hVerts ▸ hmem
  · intro F
    apply Subtype.ext
    exact φ.symm_apply_apply F.1
  · intro F
    apply Subtype.ext
    exact φ.apply_symm_apply F.1








end DirectedDistances.PaperProofs.Section3
