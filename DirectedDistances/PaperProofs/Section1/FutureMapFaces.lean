/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.FutureMapDefinition
public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull
public import DirectedDistances.KMSW.WholePlaneM0CutDrawn
import DirectedDistances.RandomWalk.PastCodeLaw

/-! # Realized faces of the future cut

The cut dart carrier is written in run-zero coordinates: its inclusion is
injective and its image is exactly `M0CutData.darts`. The successor below is
characterized by geometric reversal followed by the cut's first-return inverse
rotation. Internal orbits exclude the single exterior orbit, rather than deleting
missing geometric edges. No claim about an arbitrary topological notion of left
is built into these definitions. -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped Classical

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)

local notation "w" => shiftedStream W 0
local notation "P" => monotoneFamilyDrawing w ((And.left H) 0) (monotone_family_all w)
local notation "s" => kmswInfFaceSucc w ((And.left H) 0)



abbrev FutureMapCutFaceOrbit := Quotient (Equiv.Perm.SameCycle.setoid s)



@[expose] noncomputable def futureMapExteriorOrbit : FutureMapCutFaceOrbit W H :=
  Quotient.mk _ futureMapOuterDart



abbrev FutureMapInternalFaceOrbit :=
  {q : FutureMapCutFaceOrbit W H // q ≠ futureMapExteriorOrbit W H}

variable (D : M0CutData W H)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

include h hLL



theorem futureMap_dart_coordinates :
    Function.Injective (wholePlaneDartι W 0) ∧
      Set.range (wholePlaneDartι W 0) = D.darts := by
  refine ⟨?_, (D.darts_eq h hLL).symm⟩
  intro a b hab
  change (wholePlaneEdgeι W 0 a.1, a.2) = (wholePlaneEdgeι W 0 b.1, b.2) at hab
  apply Prod.ext
  · exact wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hab)
  · exact congrArg (fun x : WholePlaneEdge W × Bool => x.2) hab



theorem futureMap_face_successor_iff (d : ℕ × Bool) (a : WholePlaneDart W) :
    D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d)) a ↔
      a = wholePlaneDartι W 0 (s d) := by
  exact futureMap_rotation_iff D h hLL (futureMapEdgeInv d) a

omit hLL in


theorem futureMap_dart_face_exists_unique (d : ℕ × Bool) :
    ∃! F : (P).Face, (P).dartBorders d F :=
  dart_borders_unique w (H.1 0) h d

omit hLL in


@[expose] noncomputable def futureMapDartFace (d : ℕ × Bool) : (P).Face :=
  (futureMap_dart_face_exists_unique W H h d).choose

omit hLL in


theorem futureMap_dart_face_eq_iff (d : ℕ × Bool) (F : (P).Face) :
    futureMapDartFace W H h d = F ↔ (P).dartBorders d F := by
  have hd := (futureMap_dart_face_exists_unique W H h d).choose_spec.1
  exact ⟨fun he => he ▸ hd,
    fun hF => dart_border_face_unique w (H.1 0) d _ F hd hF⟩

omit hLL in


theorem futureMap_dart_face_eq_iff_sameCycle (d e : ℕ × Bool) :
    futureMapDartFace W H h d = futureMapDartFace W H h e ↔ (s).SameCycle d e := by
  constructor
  · intro he
    exact (faceOrbit_iff_common_face w (H.1 0) h d e).mpr
      ⟨_, (futureMap_dart_face_eq_iff W H h d _).mp he,
        (futureMap_dart_face_eq_iff W H h e _).mp rfl⟩
  · intro hde
    obtain ⟨F, hd, he⟩ := (faceOrbit_iff_common_face w (H.1 0) h d e).mp hde
    exact ((futureMap_dart_face_eq_iff W H h d F).mpr hd).trans
      ((futureMap_dart_face_eq_iff W H h e F).mpr he).symm

omit hLL in
 
@[expose] noncomputable def futureMapOrbitFace : FutureMapCutFaceOrbit W H → (P).Face :=
  Quotient.lift (futureMapDartFace W H h)
    (fun _ _ he => (futureMap_dart_face_eq_iff_sameCycle W H h _ _).mpr he)

omit hLL in


theorem futureMap_orbit_face_eq_iff (d : ℕ × Bool) (F : (P).Face) :
    futureMapOrbitFace W H h (Quotient.mk _ d) = F ↔ (P).dartBorders d F :=
  futureMap_dart_face_eq_iff W H h d F

omit hLL in


theorem futureMap_orbit_face_bijective :
    Function.Bijective (futureMapOrbitFace W H h) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro d e he
    exact Quotient.sound ((futureMap_dart_face_eq_iff_sameCycle W H h d e).mp he)
  · intro F
    obtain ⟨d, hd⟩ := face_bordered w (H.1 0) h F
    exact ⟨Quotient.mk _ d, (futureMap_orbit_face_eq_iff W H h d F).mpr hd⟩

omit hLL in


@[expose] noncomputable def futureMapFaceOrbitEquiv : FutureMapCutFaceOrbit W H ≃ (P).Face :=
  Equiv.ofBijective (futureMapOrbitFace W H h) (futureMap_orbit_face_bijective W H h)

omit hLL in


theorem futureMap_dartBorders_faceOrbitEquiv_iff (d : ℕ × Bool)
    (q : FutureMapCutFaceOrbit W H) :
    (P).dartBorders d (futureMapFaceOrbitEquiv W H h q) ↔ Quotient.mk _ d = q := by
  rw [← futureMap_orbit_face_eq_iff W H h]
  change futureMapOrbitFace W H h (Quotient.mk _ d) =
    futureMapOrbitFace W H h q ↔ Quotient.mk _ d = q
  exact (futureMap_orbit_face_bijective W H h).1.eq_iff

omit hLL in


theorem futureMap_orbit_face_unbounded_iff (q : FutureMapCutFaceOrbit W H) :
    (P).IsUnbounded (futureMapFaceOrbitEquiv W H h q) ↔
      q = futureMapExteriorOrbit W H := by
  obtain ⟨U, hU, huniq, horbit, _, _, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w (H.1 0) h
  have houter : futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H) = U :=
    (futureMap_orbit_face_eq_iff W H h futureMapOuterDart U).mpr
      ((horbit futureMapOuterDart).mpr Equiv.Perm.SameCycle.rfl)
  constructor
  · intro hq
    exact (futureMapFaceOrbitEquiv W H h).injective ((huniq _ hq).trans houter.symm)
  · rintro rfl
    exact houter.symm ▸ hU

omit hLL in


@[expose] noncomputable def futureMapInternalFaceEquiv :
    FutureMapInternalFaceOrbit W H ≃ {F : (P).Face // ¬ (P).IsUnbounded F} where
  toFun q := ⟨futureMapFaceOrbitEquiv W H h q.val,
    fun hu => q.property ((futureMap_orbit_face_unbounded_iff W H h q.val).mp hu)⟩
  invFun F := ⟨(futureMapFaceOrbitEquiv W H h).symm F.val, by
    intro he
    apply F.property
    have hu := (futureMap_orbit_face_unbounded_iff W H h
      ((futureMapFaceOrbitEquiv W H h).symm F.val)).mpr he
    simpa only [Equiv.apply_symm_apply] using hu⟩
  left_inv q := Subtype.ext ((futureMapFaceOrbitEquiv W H h).symm_apply_apply q.val)
  right_inv F := Subtype.ext ((futureMapFaceOrbitEquiv W H h).apply_symm_apply F.val)

omit hLL in


theorem futureMap_exterior_border_iff (d : ℕ × Bool) :
    (P).dartBorders d
      (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
      ∃ k : ℤ, d = futureMapBoundaryDart w h k := by
  obtain ⟨U, hU, huniq, _, hb, _, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w (H.1 0) h
  have he := huniq _ ((futureMap_orbit_face_unbounded_iff W H h _).mpr rfl)
  rw [he]
  exact hb d



theorem futureMap_exterior_border_iff_seam (d : ℕ × Bool) :
    (P).dartBorders d
      (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
      d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1) := by
  rw [futureMap_exterior_border_iff W H h]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨rfl, (m0Cut_seamEdge_iff W H h hLL _).mpr ?_⟩
    exact ⟨boundaryOuterEdge w h k,
      (boundaryOuterEdge_range w h) ▸ Set.mem_range_self k, rfl⟩
  · rintro ⟨hb, hs⟩
    obtain ⟨e, he, heq⟩ := (m0Cut_seamEdge_iff W H h hLL _).mp hs
    rw [← boundaryOuterEdge_range w h] at he
    obtain ⟨k, rfl⟩ := he
    refine ⟨k, Prod.ext ?_ hb⟩
    exact (wholePlaneEdgeι_injective W 0 heq).symm

omit hLL in


theorem futureMap_internal_face_triangle (q : FutureMapInternalFaceOrbit W H) :
    ∃ j : TriangleCreationTime w,
      {d | (P).dartBorders d (futureMapFaceOrbitEquiv W H h q.val)} =
        {d | d ∈ stageTriangleDartList w j} ∧
      FaceSucc3Cycle s (stageTriangleDartTriple w j).1
        (stageTriangleDartTriple w j).2.1 (stageTriangleDartTriple w j).2.2 ∧
      (stageTriangleDartList w j).toFinset.card = 3 := by
  obtain ⟨j, hb, _, hc, hn⟩ := boundedFace_orbit_is_triangle w (H.1 0) h
    (futureMapInternalFaceEquiv W H h q).val
    (futureMapInternalFaceEquiv W H h q).property
  exact ⟨j, hb, hc, hn⟩



theorem futureMap_cut_acyclic :
    ∀ v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w (H.1 0)),
      ¬ Relation.TransGen
        (rootedLocallyFiniteDirectedStep (kmswInfRot w (H.1 0)) futureMapEdgeInv
          (fun d => D.missing (wholePlaneDartι W 0 d).1)
          (fun d => D.tail (wholePlaneDartι W 0 d))) v v := by
  have hm : (fun d : ℕ × Bool => D.missing (wholePlaneDartι W 0 d).1) =
      futureMapMissing w := by
    funext d
    exact propext (D.missing_eq h hLL d.1)
  have ht : (fun d : ℕ × Bool => D.tail (wholePlaneDartι W 0 d)) =
      futureMapTail w := by
    funext d
    exact propext (D.tail_eq h hLL d)
  rw [hm, ht]
  exact futureMap_acyclic w (H.1 0)

omit hLL

variable (hp : BoundaryHitWitnesses (kmswPastCode W))

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hp H
local notation "Upper" => Set.ofPred (fun z : ℂ =>
  seamFun w h ((And.left H) 0) (Complex.re z) < Complex.im z)



theorem futureMap_internal_glued_face_exists (q : FutureMapInternalFaceOrbit W H) :
    ∃ F : (G).Face, F.val = (futureMapFaceOrbitEquiv W H h q.val).val :=
  WholePlanePastGlueM0Restriction.bounded_face_is_glued_face W h hp H
    (futureMapInternalFaceEquiv W H h q).val
    (futureMapInternalFaceEquiv W H h q).property



@[expose] noncomputable def futureMapInternalGluedFace
    (q : FutureMapInternalFaceOrbit W H) : (G).Face :=
  (futureMap_internal_glued_face_exists W H h hp q).choose



theorem futureMap_internal_glued_face_val (q : FutureMapInternalFaceOrbit W H) :
    (futureMapInternalGluedFace W H h hp q).val =
      (futureMapFaceOrbitEquiv W H h q.val).val :=
  (futureMap_internal_glued_face_exists W H h hp q).choose_spec



theorem futureMap_internal_glued_border_iff (d : ℕ × Bool)
    (q : FutureMapInternalFaceOrbit W H) :
    (G).dartBorders (wholePlaneDartι W 0 d) (futureMapInternalGluedFace W H h hp q) ↔
      Quotient.mk _ d = q.val := by
  rw [PLDrawing.dartBorders_congr P G
    (futureMapFaceOrbitEquiv W H h q.val) (futureMapInternalGluedFace W H h hp q)
    (WholePlanePastGlueM0Restriction.restrict_arc W h hp H d)
    (futureMap_internal_glued_face_val W H h hp q)]
  exact futureMap_dartBorders_faceOrbitEquiv_iff W H h d q.val



theorem futureMap_internal_glued_face_range (F : (G).Face) :
    (∃ q, futureMapInternalGluedFace W H h hp q = F) ↔ F.val ⊆ Upper := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [futureMap_internal_glued_face_val]
    exact boundedFace_subset_upper w h (H.1 0)
      (futureMapInternalFaceEquiv W H h q).val
      (futureMapInternalFaceEquiv W H h q).property
  · intro hF
    obtain ⟨F0, hF0, hv⟩ := (WholePlaneM0Drawing.m0_face_iff W h hp H F).mp hF
    let q := (futureMapInternalFaceEquiv W H h).symm ⟨F0, hF0⟩
    refine ⟨q, Subtype.ext ?_⟩
    calc
      (futureMapInternalGluedFace W H h hp q).val =
          (futureMapInternalFaceEquiv W H h q).val.val :=
        futureMap_internal_glued_face_val W H h hp q
      _ = F0.val := congrArg (fun x => x.val.val)
        ((futureMapInternalFaceEquiv W H h).apply_symm_apply ⟨F0, hF0⟩)
      _ = F.val := hv.symm



theorem futureMap_internal_glued_face_injective :
    Function.Injective (futureMapInternalGluedFace W H h hp) := by
  intro q r he
  apply Subtype.ext
  apply (futureMapFaceOrbitEquiv W H h).injective
  apply Subtype.ext
  calc
    (futureMapFaceOrbitEquiv W H h q.val).val =
        (futureMapInternalGluedFace W H h hp q).val :=
      (futureMap_internal_glued_face_val W H h hp q).symm
    _ = (futureMapInternalGluedFace W H h hp r).val := congrArg Subtype.val he
    _ = (futureMapFaceOrbitEquiv W H h r.val).val :=
      futureMap_internal_glued_face_val W H h hp r



@[expose] noncomputable def futureMapInternalGluedFaceEquiv :
    FutureMapInternalFaceOrbit W H ≃ {F : (G).Face // F.val ⊆ Upper} :=
  Equiv.ofBijective
    (fun q => ⟨futureMapInternalGluedFace W H h hp q,
      (futureMap_internal_glued_face_range W H h hp _).mp ⟨q, rfl⟩⟩)
    ⟨fun _ _ he => futureMap_internal_glued_face_injective W H h hp
      (congrArg Subtype.val he), fun F => by
        obtain ⟨q, hq⟩ :=
          (futureMap_internal_glued_face_range W H h hp F.val).mpr F.property
        exact ⟨q, Subtype.ext hq⟩⟩



theorem futureMap_internal_glued_s3_iff (d : ℕ × Bool)
    (q : FutureMapInternalFaceOrbit W H) :
    WholePlaneGlueFaceCorrespondenceFull.faceOrbitEquiv W h hp H
      (Quotient.mk _ (wholePlaneDartι W 0 d)) = futureMapInternalGluedFace W H h hp q ↔
      Quotient.mk _ d = q.val := by
  exact (WholePlaneGlueFaceCorrespondenceFull.faceOrbitEquiv_eq_iff W h hp H
    (wholePlaneDartι W 0 d) (futureMapInternalGluedFace W H h hp q)).trans
    (futureMap_internal_glued_border_iff W H h hp d q)



theorem futureMap_internal_glued_border_mem_range
    (q : FutureMapInternalFaceOrbit W H) (a : WholePlaneDart W)
    (ha : (G).dartBorders a (futureMapInternalGluedFace W H h hp q)) :
    a ∈ Set.range (wholePlaneDartι W 0) := by
  rcases WholePlaneGlueFaceCorrespondenceFull.bordered_face_cases W h hp H a _ ha with
    ⟨d, F0, rfl, _, _, _⟩ | ⟨d, Fp, rfl, hFp, hv, _⟩
  · exact Set.mem_range_self d
  · obtain ⟨z, hz, hcomp⟩ := (futureMapInternalGluedFace W H h hp q).property
    have hzF : z ∈ (futureMapInternalGluedFace W H h hp q).val :=
      hcomp ▸ mem_connectedComponentIn hz
    have hup := (futureMap_internal_glued_face_range W H h hp _).mp ⟨q, rfl⟩ hzF
    rw [hv] at hzF
    have hlo := PastFacesLower.image_boundedFace_subset_lower W h hp H Fp hFp hzF
    change seamFun w h (H.1 0) z.re < z.im at hup
    change z.im < seamFun w h (H.1 0) z.re at hlo
    exact (not_lt_of_gt hup hlo).elim

include hLL in


theorem futureMap_internal_glued_border_mem_cut
    (q : FutureMapInternalFaceOrbit W H) (a : WholePlaneDart W)
    (ha : (G).dartBorders a (futureMapInternalGluedFace W H h hp q)) : a ∈ D.darts := by
  rw [D.darts_eq h hLL]
  exact futureMap_internal_glued_border_mem_range W H h hp q a ha



theorem futureMap_internal_glued_triangle (q : FutureMapInternalFaceOrbit W H) :
    ∃ j : TriangleCreationTime w,
      {a | (G).dartBorders a (futureMapInternalGluedFace W H h hp q)} =
        wholePlaneDartι W 0 '' {d | d ∈ stageTriangleDartList w j} ∧
      ((stageTriangleDartList w j).toFinset.image (wholePlaneDartι W 0)).card = 3 := by
  classical
  obtain ⟨j, hb, _, hn⟩ := futureMap_internal_face_triangle W H h q
  refine ⟨j, Set.ext (fun a => ?_), ?_⟩
  · constructor
    · intro ha
      obtain ⟨d, rfl⟩ := futureMap_internal_glued_border_mem_range W H h hp q a ha
      refine ⟨d, ?_, rfl⟩
      have hd := (futureMap_internal_glued_border_iff W H h hp d q).mp ha
      have hp := (futureMap_dartBorders_faceOrbitEquiv_iff W H h d q.val).mpr hd
      exact (Set.ext_iff.mp hb d).mp hp
    · rintro ⟨d, hd, rfl⟩
      apply (futureMap_internal_glued_border_iff W H h hp d q).mpr
      apply (futureMap_dartBorders_faceOrbitEquiv_iff W H h d q.val).mp
      exact (Set.ext_iff.mp hb d).mpr hd
  · rw [Finset.card_image_of_injective _
      (WholePlanePastGlueM0Restriction.m0_restriction W h hp H).2.1]
    exact hn

include hLL in


theorem futureMap_interface_trace_eq_graph :
    {z | ∃ a : WholePlaneDart W, D.seam a.1 ∧ z ∈ ((G).arc a).image} =
      {z : ℂ | z.im = seamFun w h (H.1 0) z.re} :=
  WholePlaneM0CutDrawn.cut_union_eq_graph W h hp H hLL

include hLL in


theorem futureMap_left_vertex_iff_above (v : WholePlaneVertex W) :
    v ∈ m0CutLeftVertices W H D.seam ↔
      seamFun w h (H.1 0) ((G).pos v).re ≤ ((G).pos v).im := by
  rw [m0Cut_leftVertices_eq_runZero W H h D.seam (m0Cut_seamEdge_iff W H h hLL)]
  exact (WholePlaneM0Drawing.m0_vertex_iff W h hp H v).symm

include hLL in


theorem futureMap_left_edge_iff_above (e : WholePlaneEdge W) :
    e ∈ D.edges ↔ ((G).arc (e, false)).image ⊆
      {z : ℂ | seamFun w h (H.1 0) z.re ≤ z.im} := by
  constructor
  · intro he
    apply (WholePlaneM0Drawing.m0_dart_iff W h hp H (e, false)).mpr
    rw [D.edges_eq h hLL] at he
    obtain ⟨a, rfl⟩ := he
    exact ⟨(a, false), rfl⟩
  · intro he
    obtain ⟨d, hd⟩ := (WholePlaneM0Drawing.m0_dart_iff W h hp H (e, false)).mp he
    rw [D.edges_eq h hLL]
    exact ⟨d.1, congrArg Prod.fst hd⟩

include hLL in


theorem futureMap_missing_edge_on_exterior (e : WholePlaneEdge W)
    (he : e ∈ D.edges) (hm : D.missing e) :
    (∃ d : ℕ × Bool, (wholePlaneDartι W 0 d).1 = e ∧
      (P).dartBorders d (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H))) ∧
      ¬ D.tail (e, false) ∧ ¬ D.tail (e, true) := by
  have hs := (futureMap_seam_iff D h hLL e).mpr
    (Or.inr (Or.inr ((futureMap_missing_iff_betaL D h hLL he).mp hm)))
  obtain ⟨a, ha, hae⟩ := (m0Cut_seamEdge_iff W H h hLL e).mp hs
  rw [← boundaryOuterEdge_range w h] at ha
  obtain ⟨k, rfl⟩ := ha
  refine ⟨⟨futureMapBoundaryDart w h k, hae, ?_⟩, fun ht => ht.2 hm,
    fun ht => ht.2 hm⟩
  exact (futureMap_exterior_border_iff W H h _).mpr ⟨k, rfl⟩

end DirectedDistances.PaperProofs.Section1

namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped Classical





theorem futureMap_faces_characterization_ae :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let D := m0CutData W H h hLL
      let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
      let f := seamFun (shiftedStream W 0) h (H.1 0)
      (∀ d a, D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d)) a ↔
        a = wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) ∧
      (∀ F : G.Face, (∃ q, futureMapInternalGluedFace W H h hp q = F) ↔
        F.val ⊆ {z : ℂ | f z.re < z.im}) ∧
      (∀ d q, G.dartBorders (wholePlaneDartι W 0 d)
        (futureMapInternalGluedFace W H h hp q) ↔ Quotient.mk _ d = q.val) ∧
      (∀ d, P.dartBorders d
        (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
        d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1)) ∧
      (∀ q : FutureMapInternalFaceOrbit W H,
        ∃ j : TriangleCreationTime (shiftedStream W 0),
          {a | G.dartBorders a (futureMapInternalGluedFace W H h hp q)} =
            wholePlaneDartι W 0 '' {d | d ∈ stageTriangleDartList (shiftedStream W 0) j} ∧
          ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image
            (wholePlaneDartι W 0)).card = 3) ∧
      (∀ v : RootedLocallyFiniteVertex (ℕ × Bool)
          (kmswInfRot (shiftedStream W 0) (H.1 0)),
        ¬ Relation.TransGen
          (rootedLocallyFiniteDirectedStep (kmswInfRot (shiftedStream W 0) (H.1 0))
            futureMapEdgeInv (fun d => D.missing (wholePlaneDartι W 0 d).1)
            (fun d => D.tail (wholePlaneDartι W 0 d))) v v) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      ({z | ∃ a : WholePlaneDart W, D.seam a.1 ∧ z ∈ (G.arc a).image} =
        {z : ℂ | z.im = f z.re}) ∧
      (∀ v, v ∈ m0CutLeftVertices W H D.seam ↔ f (G.pos v).re ≤ (G.pos v).im) ∧
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im}) := by
  filter_upwards [futureMap_combinatorial_characterization_ae,
    RandomWalk.wholePlaneIID_ae_pastCode_boundaryHitWitnesses] with W hW hp
  obtain ⟨H, h, hLL, _⟩ := hW
  change BoundaryHitWitnesses (kmswPastCode W) at hp
  let D := m0CutData W H h hLL
  exact ⟨H, h, hLL, hp,
    futureMap_face_successor_iff W H D h hLL,
    futureMap_internal_glued_face_range W H h hp,
    futureMap_internal_glued_border_iff W H h hp,
    futureMap_exterior_border_iff_seam W H D h hLL,
    futureMap_internal_glued_triangle W H h hp,
    futureMap_cut_acyclic W H D h hLL,
    fun _ he => futureMap_missing_iff_betaL D h hLL he,
    futureMap_interface_trace_eq_graph W H D h hLL hp,
    futureMap_left_vertex_iff_above W H D h hLL hp,
    futureMap_left_edge_iff_above W H D h hLL hp⟩

end DirectedDistances.PaperProofs.Section1






