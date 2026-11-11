module

public import DirectedDistances.PlanarMap.D39RootedMapIsoBall
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport
public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2


























public section

namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

private theorem d39StrictMonoIntervalEndpoints (φ : I ≃ₜ I)
    (hφ : StrictMono φ) : φ 0 = 0 ∧ φ 1 = 1 := by
  have h0 : φ 0 ≤ 0 := by
    have h := hφ.monotone (show (0 : I) ≤ φ.symm 0 from (φ.symm 0).property.1)
    simpa using h
  have h1 : 1 ≤ φ 1 := by
    have hle : φ.symm 1 ≤ (1 : I) := by
      change (φ.symm 1).val ≤ (1 : ℝ)
      exact (φ.symm 1).property.2
    have h := hφ.monotone hle
    simpa using h
  exact ⟨le_antisymm h0 (show (0 : I) ≤ φ 0 from (φ 0).property.1),
    le_antisymm (φ 1).property.2 h1⟩

private theorem d39StrictAntiIntervalEndpoints (φ : I ≃ₜ I)
    (hφ : StrictAnti φ) : φ 0 = 1 ∧ φ 1 = 0 := by
  have h0 : 1 ≤ φ 0 := by
    have h := hφ.antitone (show (0 : I) ≤ φ.symm 1 from (φ.symm 1).property.1)
    simpa using h
  have h1 : φ 1 ≤ 0 := by
    have hle : φ.symm 0 ≤ (1 : I) := by
      change (φ.symm 0).val ≤ (1 : ℝ)
      exact (φ.symm 0).property.2
    have h := hφ.antitone hle
    simpa using h
  exact ⟨le_antisymm (show φ 0 ≤ (1 : I) from (φ 0).property.2) h0,
    le_antisymm h1 (show (0 : I) ≤ φ 1 from (φ 1).property.1)⟩

/-- Helper toward Definition 3.8. An orientation-preserving geometric
isomorphism carries the face on the left of a dart to the left side when the
stored arc direction is retained, and to the right side when it is reversed. -/
theorem d39GeomRootedMapIsoV2_sideLeftOf_map
    {V E V' E' : Type*} {A : DirectedPlaneMapWithMissing V E}
    {rho : E × Bool} {A' : DirectedPlaneMapWithMissing V' E'}
    {rho' : E' × Bool}
    (R : D39GeomRootedMapIsoV2 A rho A' rho')
    (F : A.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (a : E) :
    A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a ↔
      if R.edgeFlip a then
        A'.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (R.faceEquiv F) (R.edgeEquiv a)
      else
        A'.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (R.faceEquiv F) (R.edgeEquiv a) := by
  cases hflip : R.edgeFlip a
  · have hmono := R.edgeParam_mono a hflip
    obtain ⟨h0, h1⟩ := d39StrictMonoIntervalEndpoints (R.edgeParam a) hmono
    have hpath : ∀ t : I,
        ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) t =
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).reparam
            (R.edgeParam a) (R.edgeParam a).continuous h0 h1 t := by
      intro t
      exact R.arc_map a t
    change A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a ↔ _
    change (∀ s, LeftAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔ _
    change _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
      (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s)
    calc
      (∀ s, LeftAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔
          (∀ s, LeftAtOn (R.h '' F.val)
            ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_map_iff _ _ s R.h R.orientationPreserving
      _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).reparam
            (R.edgeParam a) (R.edgeParam a).continuous h0 h1) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) :=
        forall_leftAtOn_reparam_iff _ _ (R.edgeParam a) h0 h1
      _ = (∀ s, LeftAtOn (R.faceEquiv F).val
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) := by
        rw [R.faceEquiv_val]
  · have hanti := R.edgeParam_anti a hflip
    obtain ⟨h0, h1⟩ := d39StrictAntiIntervalEndpoints (R.edgeParam a) hanti
    let ψ := (R.edgeParam a).trans unitInterval.symmHomeomorph
    have hψ0 : ψ 0 = 0 := by
      change σ (R.edgeParam a 0) = 0
      rw [h0, unitInterval.symm_one]
    have hψ1 : ψ 1 = 1 := by
      change σ (R.edgeParam a 1) = 1
      rw [h1, unitInterval.symm_zero]
    have hpath : ∀ t : I,
        ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) t =
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm.reparam
            ψ ψ.continuous hψ0 hψ1) t := by
      intro t
      change R.h (A.toPlaneMapWithMissing.arc a t) =
        A'.toPlaneMapWithMissing.arc (R.edgeEquiv a) (σ (σ (R.edgeParam a t)))
      rw [unitInterval.symm_symm]
      exact R.arc_map a t
    change A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a ↔ _
    change (∀ s, LeftAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔ _
    change _ ↔ (∀ s, RightAtOn (R.h '' F.val)
      (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s)
    calc
      (∀ s, LeftAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔
          (∀ s, LeftAtOn (R.h '' F.val)
            ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_map_iff _ _ s R.h R.orientationPreserving
      _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm.reparam
            ψ ψ.continuous hψ0 hψ1) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm s) :=
        forall_leftAtOn_reparam_iff _ _ ψ hψ0 hψ1
      _ ↔ (∀ s, RightAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) :=
        forall_leftAtOn_symm_iff _ _
      _ = (∀ s, RightAtOn (R.faceEquiv F).val
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) := by
        rw [R.faceEquiv_val]

theorem d39GeomRootedMapIsoV2_sideRightOf_map
    {V E V' E' : Type*} {A : DirectedPlaneMapWithMissing V E}
    {rho : E × Bool} {A' : DirectedPlaneMapWithMissing V' E'}
    {rho' : E' × Bool}
    (R : D39GeomRootedMapIsoV2 A rho A' rho')
    (F : A.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (a : E) :
    A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a ↔
      if R.edgeFlip a then
        A'.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (R.faceEquiv F) (R.edgeEquiv a)
      else
        A'.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (R.faceEquiv F) (R.edgeEquiv a) := by
  cases hflip : R.edgeFlip a
  · have hmono := R.edgeParam_mono a hflip
    obtain ⟨h0, h1⟩ := d39StrictMonoIntervalEndpoints (R.edgeParam a) hmono
    have hpath : ∀ t : I,
        ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) t =
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).reparam
            (R.edgeParam a) (R.edgeParam a).continuous h0 h1 t := by
      intro t
      exact R.arc_map a t
    change A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a ↔ _
    change (∀ s, RightAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔ _
    change _ ↔ (∀ s, RightAtOn (R.h '' F.val)
      (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s)
    calc
      (∀ s, RightAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔
          (∀ s, RightAtOn (R.h '' F.val)
            ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_map_iff _ _ s R.h R.orientationPreserving
      _ ↔ (∀ s, RightAtOn (R.h '' F.val)
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).reparam
            (R.edgeParam a) (R.edgeParam a).continuous h0 h1) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, RightAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) :=
        forall_rightAtOn_reparam_iff _ _ (R.edgeParam a) h0 h1
      _ = (∀ s, RightAtOn (R.faceEquiv F).val
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) := by
        rw [R.faceEquiv_val]
  · have hanti := R.edgeParam_anti a hflip
    obtain ⟨h0, h1⟩ := d39StrictAntiIntervalEndpoints (R.edgeParam a) hanti
    let ψ := (R.edgeParam a).trans unitInterval.symmHomeomorph
    have hψ0 : ψ 0 = 0 := by
      change σ (R.edgeParam a 0) = 0
      rw [h0, unitInterval.symm_one]
    have hψ1 : ψ 1 = 1 := by
      change σ (R.edgeParam a 1) = 1
      rw [h1, unitInterval.symm_zero]
    have hpath : ∀ t : I,
        ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) t =
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm.reparam
            ψ ψ.continuous hψ0 hψ1) t := by
      intro t
      change R.h (A.toPlaneMapWithMissing.arc a t) =
        A'.toPlaneMapWithMissing.arc (R.edgeEquiv a) (σ (σ (R.edgeParam a t)))
      rw [unitInterval.symm_symm]
      exact R.arc_map a t
    change A.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a ↔ _
    change (∀ s, RightAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔ _
    change _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
      (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s)
    calc
      (∀ s, RightAtOn F.val (A.toPlaneMapWithMissing.arc a) s) ↔
          (∀ s, RightAtOn (R.h '' F.val)
            ((A.toPlaneMapWithMissing.arc a).map R.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_map_iff _ _ s R.h R.orientationPreserving
      _ ↔ (∀ s, RightAtOn (R.h '' F.val)
          ((A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm.reparam
            ψ ψ.continuous hψ0 hψ1) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, RightAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)).symm s) :=
        forall_rightAtOn_reparam_iff _ _ ψ hψ0 hψ1
      _ ↔ (∀ s, LeftAtOn (R.h '' F.val)
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) :=
        forall_rightAtOn_symm_iff _ _
      _ = (∀ s, LeftAtOn (R.faceEquiv F).val
          (A'.toPlaneMapWithMissing.arc (R.edgeEquiv a)) s) := by
        rw [R.faceEquiv_val]

/-- Helper toward Definition 3.8. A proposed faithful representation of the
rooted dart map by a concrete geometric drawing. The dart Boolean records
whether the dart follows the drawing's stored source-to-target parameterization.
The root equality retains its order even when its geometric edge is missing. -/
structure D39DrawingRepresentationData (M : D39RootedMap)
    (B : D39DomainRootedMapV2) where
  /-- The bijection from rotation-orbit vertices to drawing vertices. -/
  vertexEquiv : RootedLocallyFiniteVertex M.core.D M.core.rot ≃ B.V
  /-- Vertex positions are injective, as required for a plane drawing. -/
  positions_injective : Function.Injective B.map.toPlaneMapWithMissing.pos
  /-- A bijection of individual darts with edge identities and endpoint order. -/
  dartEquiv : M.core.D ≃ B.E × Bool
  /-- The dart's initial rotation-orbit vertex is the corresponding geometric
  endpoint, using the stored parameter direction bit. -/
  dart_tail_vertex : ∀ d,
    vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
      if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.src (dartEquiv d).1
      else B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1
  /-- The opposite dart reaches the other endpoint of the same geometric edge. -/
  dart_head_vertex : ∀ d,
    vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) =
      if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1
      else B.map.toPlaneMapWithMissing.src (dartEquiv d).1
  /-- Reversing a combinatorial dart preserves the edge identity and reverses
  its stored endpoint order. -/
  dart_edgeInv : ∀ d,
    dartEquiv (M.core.edgeInv d) = ((dartEquiv d).1, !(dartEquiv d).2)
  /-- Missing/present tags agree on each matched edge, including the root edge. -/
  dart_missing : ∀ d,
    B.map.toPlaneMapWithMissing.missing (dartEquiv d).1 ↔ M.core.missing d
  /-- On present edges only, the combinatorial tail tag agrees with the
  geometric orientation relative to the stored arc direction. -/
  dart_orientation : ∀ d (hd : ¬ M.core.missing d),
    M.core.tail d ↔
      B.map.forward ⟨(dartEquiv d).1,
        (dart_missing d).not.mpr hd⟩ = (dartEquiv d).2
  /-- Preserve the ordered root dart. This also applies to a missing root;
  its Boolean records the chosen first endpoint and does not orient the edge. -/
  root_mark : dartEquiv M.rootMark.dart = B.root
   
  faceOfDart : M.core.D → B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face
  

  faceOrbit_iff : ∀ d e,
    faceOfDart d = faceOfDart e ↔
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e
  /-- Every complementary component is represented by a combinatorial face orbit. -/
  face_surjective : Function.Surjective faceOfDart
  /-- The mapped combinatorial face borders each represented dart on its left,
  with the right side used when the dart reverses the stored arc. This records
  the rotation/face convention rather than assuming a separate face match. -/
  face_left_of_dart : ∀ d,
    if (dartEquiv d).2 then
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
        (faceOfDart d) (dartEquiv d).1
    else
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
        (faceOfDart d) (dartEquiv d).1




def D39DrawingRepresents (M : D39RootedMap)
    (B : D39DomainRootedMapV2) : Prop :=
  Nonempty (D39DrawingRepresentationData M B)

namespace D39DrawingRepresentationData

variable {M N : D39RootedMap} {B : D39DomainRootedMapV2}

@[expose] def d39DrawingDartOrderEquiv {C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root) :
    B.E × Bool ≃ C.E × Bool where
  toFun p := (R.edgeEquiv p.1, Bool.xor p.2 (R.edgeFlip p.1))
  invFun p :=
    (R.edgeEquiv.symm p.1,
      Bool.xor p.2 (R.edgeFlip (R.edgeEquiv.symm p.1)))
  left_inv := by
    rintro ⟨e, b⟩
    cases b <;> cases hf : R.edgeFlip e <;> simp [hf]
  right_inv := by
    rintro ⟨e, b⟩
    cases b <;> cases R.edgeFlip (R.edgeEquiv.symm e) <;> simp

/-- Helper toward Definition 3.8. Transport a candidate drawing representation
across a whole-map combinatorial isomorphism. -/
@[expose] noncomputable def transportCombinatorialData
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresentationData M B) :
    D39DrawingRepresentationData N B := by
  classical
  refine ⟨iso.vertexEquiv.symm.trans h.vertexEquiv, h.positions_injective,
    iso.toEquiv.symm.trans h.dartEquiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    let dM := iso.toEquiv.symm d
    have hclass : iso.vertexEquiv.symm
        (rootedLocallyFiniteVertexClass N.core.rot d) =
          rootedLocallyFiniteVertexClass M.core.rot dM := by
      change iso.symm.vertexMap (d39VertexClass N d) =
        d39VertexClass M (iso.toEquiv.symm d)
      exact iso.symm.vertexMap_dart d
    change h.vertexEquiv
        (iso.vertexEquiv.symm (rootedLocallyFiniteVertexClass N.core.rot d)) = _
    rw [hclass]
    change h.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot
        (iso.toEquiv.symm d)) =
      if (h.dartEquiv (iso.toEquiv.symm d)).2 then
        B.map.toPlaneMapWithMissing.src (h.dartEquiv (iso.toEquiv.symm d)).1
      else B.map.toPlaneMapWithMissing.tgt (h.dartEquiv (iso.toEquiv.symm d)).1
    exact h.dart_tail_vertex (iso.toEquiv.symm d)
  · intro d
    let dM := iso.toEquiv.symm d
    have hcomm : iso.toEquiv.symm (N.core.edgeInv d) = M.core.edgeInv dM := by
      calc
        iso.toEquiv.symm (N.core.edgeInv d) =
            iso.toEquiv.symm (iso.toEquiv (M.core.edgeInv dM)) := by
          rw [iso.edgeInv_comm dM, Equiv.apply_symm_apply]
        _ = M.core.edgeInv dM := iso.toEquiv.symm_apply_apply _
    have hclass : iso.vertexEquiv.symm
        (rootedLocallyFiniteVertexClass N.core.rot (N.core.edgeInv d)) =
          rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv dM) := by
      change iso.symm.vertexMap (d39VertexClass N (N.core.edgeInv d)) =
        d39VertexClass M (M.core.edgeInv dM)
      rw [← hcomm]
      exact iso.symm.vertexMap_dart (N.core.edgeInv d)
    change h.vertexEquiv
        (iso.vertexEquiv.symm
          (rootedLocallyFiniteVertexClass N.core.rot (N.core.edgeInv d))) = _
    rw [hclass]
    change h.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot
        (M.core.edgeInv (iso.toEquiv.symm d))) =
      if (h.dartEquiv (iso.toEquiv.symm d)).2 then
        B.map.toPlaneMapWithMissing.tgt (h.dartEquiv (iso.toEquiv.symm d)).1
      else B.map.toPlaneMapWithMissing.src (h.dartEquiv (iso.toEquiv.symm d)).1
    exact h.dart_head_vertex (iso.toEquiv.symm d)
  · intro d
    let dM := iso.toEquiv.symm d
    have hcomm : iso.toEquiv.symm (N.core.edgeInv d) = M.core.edgeInv dM := by
      calc
        iso.toEquiv.symm (N.core.edgeInv d) =
            iso.toEquiv.symm (iso.toEquiv (M.core.edgeInv dM)) := by
          rw [iso.edgeInv_comm dM, Equiv.apply_symm_apply]
        _ = M.core.edgeInv dM := iso.toEquiv.symm_apply_apply _
    simpa [Equiv.trans_apply, dM, hcomm] using h.dart_edgeInv dM
  · intro d
    let dM := iso.toEquiv.symm d
    simpa [dM] using (h.dart_missing dM).trans (iso.missing_iff dM).symm
  · intro d hd
    let dM := iso.toEquiv.symm d
    have hdM : ¬ M.core.missing dM := by
      intro hm
      exact hd (by simpa [dM] using (iso.missing_iff dM).mpr hm)
    have ht := iso.tail_iff dM hdM
    have ho := h.dart_orientation dM hdM
    simpa [Equiv.trans_apply, dM] using ht.trans ho
  ·
    let hroot : iso.toEquiv.symm N.rootMark.dart = M.rootMark.dart := by
      calc
        iso.toEquiv.symm N.rootMark.dart =
            iso.toEquiv.symm (iso.toEquiv M.rootMark.dart) := by
          rw [← iso.root_dart_comm]
        _ = M.rootMark.dart := iso.toEquiv.symm_apply_apply _
    change h.dartEquiv (iso.toEquiv.symm N.rootMark.dart) = B.root
    rw [hroot]
    exact h.root_mark
  · exact fun d => h.faceOfDart (iso.toEquiv.symm d)
  · intro d e
    let dM := iso.toEquiv.symm d
    let eM := iso.toEquiv.symm e
    simpa [dM, eM] using
      (h.faceOrbit_iff dM eM).trans (iso.faceSameCycle_iff dM eM)
  · intro F
    obtain ⟨d, hd⟩ := h.face_surjective F
    exact ⟨iso.toEquiv d, by simpa [Equiv.trans_apply] using hd⟩
  · intro d
    change if (h.dartEquiv (iso.toEquiv.symm d)).2 then
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (h.faceOfDart (iso.toEquiv.symm d)) (h.dartEquiv (iso.toEquiv.symm d)).1
      else
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (h.faceOfDart (iso.toEquiv.symm d)) (h.dartEquiv (iso.toEquiv.symm d)).1
    exact h.face_left_of_dart (iso.toEquiv.symm d)

/-- Helper toward Definition 3.8. Transport a candidate drawing representation
across an orientation-preserving geometric isomorphism, including edge-order
flips. -/
@[expose] noncomputable def transportGeometricData {C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (h : D39DrawingRepresentationData M B) : D39DrawingRepresentationData M C := by
  classical
  refine ⟨h.vertexEquiv.trans R.vertexEquiv,
    C.map.toPlaneMapWithMissing.pos_injective,
    h.dartEquiv.trans (d39DrawingDartOrderEquiv R), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    let p := h.dartEquiv d
    change R.vertexEquiv (h.vertexEquiv
        (rootedLocallyFiniteVertexClass M.core.rot d)) = _
    rw [h.dart_tail_vertex d]
    cases hb : p.2 <;> cases hf : R.edgeFlip p.1 <;>
      simp [p, d39DrawingDartOrderEquiv, hb, hf, R.src_map, R.tgt_map]
  · intro d
    let p := h.dartEquiv d
    change R.vertexEquiv (h.vertexEquiv
        (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d))) = _
    rw [h.dart_head_vertex d]
    cases hb : p.2 <;> cases hf : R.edgeFlip p.1 <;>
      simp [p, d39DrawingDartOrderEquiv, hb, hf, R.src_map, R.tgt_map]
  · intro d
    let p := h.dartEquiv d
    rw [Equiv.trans_apply, h.dart_edgeInv]
    cases hb : p.2 <;> cases hf : R.edgeFlip p.1 <;>
      simp [d39DrawingDartOrderEquiv, p, hb, hf]
  · intro d
    change C.map.toPlaneMapWithMissing.missing
      (R.edgeEquiv (h.dartEquiv d).1) ↔ M.core.missing d
    exact (R.missing_map (h.dartEquiv d).1).trans (h.dart_missing d)
  · intro d hd
    let p := h.dartEquiv d
    have hpresent : ¬ B.map.toPlaneMapWithMissing.missing p.1 :=
      (h.dart_missing d).not.mpr hd
    have htag : ¬ C.map.toPlaneMapWithMissing.missing (R.edgeEquiv p.1) := by
      simpa [R.missing_map] using hpresent
    have horient := h.dart_orientation d hd
    have hflip := R.orientation_map p.1 hpresent
    change M.core.tail d ↔
      C.map.forward ⟨R.edgeEquiv p.1, htag⟩ =
        Bool.xor p.2 (R.edgeFlip p.1)
    exact horient.trans (by
      rw [hflip]
      constructor
      · intro hb
        rw [hb]
      · intro hb
        have hc := congrArg
          (fun b : Bool => Bool.xor b (R.edgeFlip p.1)) hb
        simpa [Bool.xor_assoc] using hc)
  · change d39DrawingDartOrderEquiv R (h.dartEquiv M.rootMark.dart) = C.root
    rw [h.root_mark]
    apply Prod.ext
    · change R.edgeEquiv B.root.1 = C.root.1
      exact R.root_edge_map
    · change Bool.xor B.root.2 (R.edgeFlip B.root.1) = C.root.2
      exact R.root_bool_map.symm
  · exact fun d => R.faceEquiv (h.faceOfDart d)
  · intro d e
    simpa using h.faceOrbit_iff d e
  · intro F
    obtain ⟨F0, hF0⟩ := R.faceEquiv.surjective F
    obtain ⟨d, hd⟩ := h.face_surjective F0
    exact ⟨d, by simpa [hd] using hF0⟩
  · intro d
    let p := h.dartEquiv d
    have hside := h.face_left_of_dart d
    have hleft := DirectedDistances.PlanarMap.d39GeomRootedMapIsoV2_sideLeftOf_map
      R (h.faceOfDart d) p.1
    have hright := DirectedDistances.PlanarMap.d39GeomRootedMapIsoV2_sideRightOf_map
      R (h.faceOfDart d) p.1
    cases hb : p.2 <;> cases hf : R.edgeFlip p.1
    · have hs : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (h.faceOfDart d) p.1 := by simpa [p, hb] using hside
      simpa [p, d39DrawingDartOrderEquiv, hb, hf] using hright.mp hs
    · have hs : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (h.faceOfDart d) p.1 := by simpa [p, hb] using hside
      simpa [p, d39DrawingDartOrderEquiv, hb, hf] using hright.mp hs
    · have hs : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (h.faceOfDart d) p.1 := by simpa [p, hb] using hside
      simpa [p, d39DrawingDartOrderEquiv, hb, hf] using hleft.mp hs
    · have hs : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (h.faceOfDart d) p.1 := by simpa [p, hb] using hside
      simpa [p, d39DrawingDartOrderEquiv, hb, hf] using hleft.mp hs

end D39DrawingRepresentationData

/-- Helper toward Definition 3.8. Transport a candidate drawing representation
across a whole-map combinatorial isomorphism. -/
theorem D39DrawingRepresents.transportCombinatorial
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresents M B) :
    D39DrawingRepresents N B := by
  rcases h with ⟨data⟩
  exact ⟨data.transportCombinatorialData iso⟩


























end DirectedDistances.PlanarMap

end
