/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer51Submaps
public import DirectedDistances.PaperProofs.Section5.FutureMapsExhaustWholePlane













public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open scoped Topology

/-- Helper toward Proposition 3.9: the retained geometric darts at an integer
start, with both sides of each edge and with missing edges still retained. -/
@[expose] def retainedDarts (W : ℤ → Fin 3) (n : ℤ) (K : Set ℕ) :
    Set (WholePlaneDart W) :=
  {d | d.1 ∈ lemma38StartEdgeι W n '' K}

/-- Helper toward Proposition 3.9: every start isomorphism identifies exactly
the same retained dart carrier, without any assumption about drawing geometry. -/
theorem retained_darts_eq_image (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) (K : Set ℕ) :
    retainedDarts W n K =
      (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) ''
        {d : ℕ × Bool | d.1 ∈ K} := by
  ext d
  constructor
  · rintro ⟨e, he, hed⟩
    refine ⟨(e, d.2), he, ?_⟩
    change J.dart (wholePlaneDartι (shiftWordInt W n) 0 (e, d.2)) = d
    erw [J.dart_apply]
    exact Prod.ext ((J.iota_edge e).trans hed) rfl
  · rintro ⟨d, hd, rfl⟩
    change (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)).1 ∈
      lemma38StartEdgeι W n '' K
    erw [J.dart_apply]
    exact ⟨d.1, hd, (J.iota_edge d.1).symm⟩

/-- Helper toward Proposition 3.9: the actual inherited restriction of the
fixed drawing at any integer start and any retained geometric edge set. -/
@[expose] def inheritedDrawing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) :=
  restrictDrawing G (retainedDarts W n K) (fun _ => Iff.rfl)

/-- Helper toward Proposition 3.9: inherited restrictions keep the entire
ambient polyline of every retained dart. -/
theorem inherited_arc (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (n : ℤ) (K : Set ℕ)
    (d : RestrictedDart (WholePlaneDart W) (retainedDarts W n K)) :
    (inheritedDrawing W H G n K).arc d = G.arc d.val :=
  restrictDrawing_arc G _ _ d

/-- Helper toward Proposition 3.9: the inherited drawing image is a subset
of the fixed drawing image, including all retained missing-edge arcs. -/
theorem inherited_image_subset (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) :
    (inheritedDrawing W H G n K).image ⊆ G.image :=
  restrictDrawing_image_subset G _ _

/-- Helper toward Proposition 3.9: the start isomorphism retains the base
vertex of each dart, including both incidences of a geometric edge. -/
theorem start_iso_dart_vertex (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) (d : WholePlaneDart (shiftWordInt W n)) :
    wholePlaneDartVertex W (J.dart d) =
      J.vertex (wholePlaneDartVertex (shiftWordInt W n) d) := by
  erw [J.dart_apply]
  rcases d with ⟨e, b⟩
  cases b
  · exact J.west e
  · exact J.east e

/-- Helper toward Proposition 3.9: the inherited vertex carrier consists
exactly of the incident run vertices transported by any start isomorphism. -/
theorem inherited_vertices_eq_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n) (K : Set ℕ) :
    Set.range (fun v : RestrictedVertex G (retainedDarts W n K) => v.val) =
      (fun v => J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v)) ''
        intrinsicConsumer51RunVertices (shiftedStream (shiftWordInt W n) 0) K := by
  ext v
  constructor
  · rintro ⟨⟨v, d, hd, hdv⟩, rfl⟩
    rw [retained_darts_eq_image W n J K] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    refine ⟨kmswLimitDartVertex (shiftedStream (shiftWordInt W n) 0) a,
      ⟨a, ha, rfl⟩, ?_⟩
    dsimp only
    erw [← wholePlaneDartVertex_ι]
    exact (start_iso_dart_vertex W n J _).symm.trans hdv
  · rintro ⟨v, ⟨d, hd, hdv⟩, rfl⟩
    refine ⟨⟨_, J.dart (wholePlaneDartι (shiftWordInt W n) 0 d), ?_, ?_⟩, rfl⟩
    · rw [retained_darts_eq_image W n J K]
      exact ⟨d, hd, rfl⟩
    · erw [start_iso_dart_vertex, wholePlaneDartVertex_ι, hdv]

/-- Helper toward Proposition 3.9: a full-drawing face meeting an inherited
complementary region is contained in that entire region. -/
theorem face_subset_of_mem (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) (F : (inheritedDrawing W H G n K).Face)
    (B : G.Face) (z : ℂ) (hzF : z ∈ F.val) (hzB : z ∈ B.val) :
    B.val ⊆ F.val := by
  obtain ⟨x, _, hF⟩ := F.property
  obtain ⟨y, _, hB⟩ := B.property
  have hFz : F.val = connectedComponentIn
      (inheritedDrawing W H G n K).imageᶜ z :=
    hF.trans (connectedComponentIn_eq (hF ▸ hzF))
  have hBz : B.val = connectedComponentIn G.imageᶜ z :=
    hB.trans (connectedComponentIn_eq (hB ▸ hzB))
  rw [hFz, hBz]
  exact connectedComponentIn_mono z
    (Set.compl_subset_compl.mpr (inherited_image_subset W H G n K))

/-- Helper toward Proposition 3.9: off the full drawing, each inherited
complementary region is exactly the union of the full faces it contains.
Deleted edge interiors are excluded explicitly, rather than silently lost. -/
theorem face_diff_image_eq_iUnion (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) (F : (inheritedDrawing W H G n K).Face) :
    F.val \ G.image = ⋃ (B : G.Face) (_ : B.val ⊆ F.val), B.val := by
  ext z
  constructor
  · rintro ⟨hzF, hzG⟩
    obtain ⟨B, hzB⟩ := (G.faces_cover_compl z).mpr hzG
    exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr
      ⟨face_subset_of_mem W H G n K F B z hzF hzB, hzB⟩⟩
  · intro hz
    obtain ⟨B, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hBF, hzB⟩ := Set.mem_iUnion.mp hz
    exact ⟨hBF hzB, G.face_subset_compl B hzB⟩

/-- Helper toward Proposition 3.9: all inherited complementary regions are
open, by local finiteness of the restricted drawing. -/
theorem inherited_face_isOpen (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) (F : (inheritedDrawing W H G n K).Face) :
    IsOpen F.val := by
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n K)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  obtain ⟨z, _, hF⟩ := F.property
  rw [hF]
  exact ((inheritedDrawing W H G n K).image_isClosed hvert).isOpen_compl.connectedComponentIn

/-- Helper toward Proposition 3.9: inherited externality is exactly
unboundedness of the complete region, including deleted edge interiors. -/
theorem inherited_isUnbounded_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (K : Set ℕ) (F : (inheritedDrawing W H G n K).Face) :
    (inheritedDrawing W H G n K).IsUnbounded F ↔ ¬ Bornology.IsBounded F.val := by
  constructor
  · intro hF hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨z, hz, hlt⟩ := hF R
    exact hlt.not_ge (hR z hz)
  · intro hb R
    by_contra hR
    exact hb (isBounded_iff_forall_norm_le.mpr ⟨R, fun z hz =>
      le_of_not_gt (fun hlt => hR ⟨z, hz, hlt⟩)⟩)

/-- Helper toward Proposition 3.9: each glued face contributing to a retained
region occurs in a future-run restriction with identical region and dart
incidence. This does not identify the shifted monotone drawing. -/
theorem glued_face_capture_inside (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (K : Set ℕ)
    (F : (inheritedDrawing W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) n K).Face)
    (z : ℂ) (hzF : z ∈ F.val)
    (hzG : z ∉ (WholePlanePastGlueDrawing.glueDrawing W h hpast H).image) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∃ (B : G.Face) (N : ℕ) (B' : (futureMapsRunDrawing W H G N).Face),
      z ∈ B.val ∧ B.val ⊆ F.val ∧ B'.val = B.val ∧
      ∀ d : RestrictedDart (WholePlaneDart W) (Set.range (wholePlaneDartι W N)),
        (futureMapsRunDrawing W H G N).dartBorders d B' ↔ G.dartBorders d.val B := by
  intro G
  obtain ⟨B, hzB⟩ := (G.faces_cover_compl z).mpr hzG
  obtain ⟨N, B', hB', hinc⟩ := futureMaps_glued_face_capture W H h hpast B
  exact ⟨B, N, B', hzB, face_subset_of_mem W H G n K F B z hzF hzB, hB', hinc⟩

section Representative

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "C" => uibotCut2SourceDartEquiv W H h hpast hp

private theorem dart_arc_range (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    Set.range (intrinsicFutureDartArc A d) = Set.range (A.map.arc d.1) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact Path.symm_range _
  · rfl

/-- Helper toward Proposition 3.9: source geometric edges have the full
glued polyline image at every whole-plane dart, independently of the start. -/
theorem source_edge_range (d : WholePlaneDart W) :
    Set.range ((S).map.arc d.1) = ((G).arc d).image := by
  obtain ⟨φ, _, hφ⟩ := uibotCut2SourceDartEquiv_arc_param W H h hpast hp d
  have hr : Set.range (intrinsicFutureDartArc S (C d)) =
      Set.range ((G).arc d).toPath := by
    rw [show intrinsicFutureDartArc S (C d) = ((G).arc d).toPath ∘ φ from funext hφ,
      Set.range_comp, Set.range_eq_univ.mpr φ.surjective, Set.image_univ]
  rw [dart_arc_range, Polyline.range_toPath] at hr
  exact hr

/-- Helper toward Proposition 3.9: the actual source submap trace at any
integer start is exactly its inherited drawing image. This statement compares
two uses of the fixed drawing, not the shifted monotone drawing. -/
theorem source_trace (n : ℤ) (K : Set ℕ) :
    intrinsicConsumer51Trace S
      (Set.range (fun v : RestrictedVertex G (retainedDarts W n K) => v.val))
      (lemma38StartEdgeι W n '' K) = (inheritedDrawing W H G n K).image := by
  ext z
  constructor
  · rintro (⟨v, ⟨v', rfl⟩, rfl⟩ | ⟨e, he, hz⟩)
    · exact Or.inl ⟨v', rfl⟩
    · rw [source_edge_range W H h hpast hp (e, false)] at hz
      exact Or.inr ⟨⟨(e, false), he⟩, hz⟩
  · rintro (⟨v, rfl⟩ | ⟨d, hz⟩)
    · exact Or.inl ⟨v.val, ⟨v, rfl⟩, rfl⟩
    · refine Or.inr ⟨d.val.1, d.property, ?_⟩
      rw [source_edge_range W H h hpast hp d.val]
      exact hz

variable (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)

include h hpast I

/-- Helper toward Proposition 3.9: the vertex and edge embeddings from
any start identify the representative's actual trace with the transported
inherited drawing image. No shifted-drawing equivalence is assumed. -/
theorem representative_trace (n : ℤ) (J : WholePlaneStartIso W n) (K : Set ℕ) :
    let U := shiftWordInt W n
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    intrinsicConsumer51Trace A
      (V '' intrinsicConsumer51RunVertices (shiftedStream U 0) K) (E '' K) =
        I.h '' (inheritedDrawing W H G n K).image := by
  intro U V E
  have hv : V '' intrinsicConsumer51RunVertices (shiftedStream U 0) K =
      I.vertexEquiv ''
        Set.range (fun v : RestrictedVertex G (retainedDarts W n K) => v.val) := by
    rw [inherited_vertices_eq_image W H G n J K, Set.image_image]
  have he : E '' K = I.edgeEquiv '' (lemma38StartEdgeι W n '' K) := by
    rw [Set.image_image]
    exact congrArg (fun f => f '' K) (funext fun e =>
      congrArg I.edgeEquiv (J.iota_edge e))
  rw [hv, he]
  exact (intrinsicConsumer51_trace_map (A := S) (B := A) I _ _).trans
    (congrArg (fun T => I.h '' T) (source_trace W H h hpast hp n K))

/-- Helper toward Proposition 3.9: all complementary regions of the
inherited restriction transport bijectively into the representative's actual
submap. This is the target side of the remaining shifted-drawing comparison. -/
theorem representative_faceRegions (n : ℤ) (J : WholePlaneStartIso W n) (K : Set ℕ) :
    let U := shiftWordInt W n
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A
        (V '' intrinsicConsumer51RunVertices (shiftedStream U 0) K) (E '' K)) =
      Set.range (fun F : (inheritedDrawing W H G n K).Face => I.h '' F.val) := by
  intro U V E
  rw [representative_trace W H h hpast hp A I n J K]
  let Q := inheritedDrawing W H G n K
  ext F
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨z, rfl⟩ := I.h.surjective z
    have hz' : z ∉ Q.image := by
      rwa [I.h.injective.mem_set_image] at hz
    refine ⟨⟨connectedComponentIn Q.imageᶜ z, z, hz', rfl⟩, ?_⟩
    change I.h '' connectedComponentIn Q.imageᶜ z =
      connectedComponentIn (I.h '' Q.image)ᶜ (I.h z)
    rw [I.h.image_connectedComponentIn hz', I.h.image_compl]
  · rintro ⟨F, rfl⟩
    obtain ⟨z, hz, hF⟩ := F.property
    refine ⟨I.h z, ?_, ?_⟩
    · rwa [I.h.injective.mem_set_image]
    · change I.h '' F.val = connectedComponentIn (I.h '' Q.image)ᶜ (I.h z)
      rw [hF, I.h.image_connectedComponentIn hz, I.h.image_compl]

/-- Helper toward Proposition 3.9: representative transport preserves
the exterior designation of every inherited complementary region. -/
theorem representative_external (n : ℤ) (K : Set ℕ)
    (F : (inheritedDrawing W H G n K).Face) :
    (¬ Bornology.IsBounded (I.h '' F.val)) ↔
      (inheritedDrawing W H G n K).IsUnbounded F := by
  rw [PastFacesLower.isBounded_image_iff]
  exact (inherited_isUnbounded_iff W H G n K F).symm

/-- Helper toward Proposition 3.9: the actual representative's winding-left
incidence is exactly that of the inherited restricted drawing. -/
theorem representative_face_side (n : ℤ) (K : Set ℕ)
    (d : RestrictedDart (WholePlaneDart W) (retainedDarts W n K))
    (F : (inheritedDrawing W H G n K).Face) :
    (∀ s, LeftAtOn (I.h '' F.val)
      (intrinsicFutureDartArc A (intrinsicFutureDartEquiv (A := S) I (C d.val))) s) ↔
        (inheritedDrawing W H G n K).dartBorders d F := by
  let Q := inheritedDrawing W H G n K
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n K)) := by
    rintro ⟨v, q, hq, hqv⟩
    exact ⟨⟨q, hq⟩, Subtype.ext hqv⟩
  apply (intrinsicFuture_leftAtOn_map (A := S) (B := A) I F.val (C d.val)).symm.trans
  apply (uibotCut2_source_leftAtOn_iff W H h hpast hp d.val F.val).trans
  exact ⟨LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective Q hvert d F,
    fun hF s => Q.dartBorders_toPath_leftAtOn hvert d F hF s⟩

/-- Helper toward Proposition 3.9: inherited cyclic successors transport to
the representative's geometric rotation on the same retained edge set. -/
theorem representative_rotation (n : ℤ) (K : Set ℕ)
    (d : RestrictedDart (WholePlaneDart W) (retainedDarts W n K)) :
    let D := fun q => intrinsicFutureDartEquiv (A := S) I (C q)
    intrinsicFutureRotation A (I.edgeEquiv '' (lemma38StartEdgeι W n '' K))
      (D (drawingFirstReturnPerm G (retainedDarts W n K) d).val) (D d.val) := by
  intro D
  let T := retainedDarts W n K
  let Q := inheritedDrawing W H G n K
  let R := drawingFirstReturnPerm G T
  let f := fun q : T => q.val
  let shiftedStartGeometryRestrictedDartNonempty : Nonempty T := ⟨d⟩
  have hvr : wholePlaneDartVertex W (R d).val = wholePlaneDartVertex W d.val :=
    congrArg Subtype.val (Q.vert_rotation d)
  have hstar : C '' (f '' {q : T | restrictedVertex G T q = restrictedVertex G T d}) =
      {q : (S).E × Bool | q.1 ∈ lemma38StartEdgeι W n '' K ∧
        d39GeomRootVertex (S).map q = d39GeomRootVertex (S).map (C (f (R d)))} := by
    ext q
    obtain ⟨q, rfl⟩ := (C).surjective q
    rw [(C).injective.mem_set_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex, hvr]
      exact congrArg Subtype.val ha
    · rintro ⟨hq, hqv⟩
      refine ⟨⟨q, hq⟩, ?_, rfl⟩
      apply Subtype.ext
      erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex, hvr] at hqv
      exact hqv
  have ht := plDrawing_toPath_rotation_topological_ccwSuccessor Q d
  have ht' := intrinsicFutureCut2_topological_image f Subtype.val_injective _
    (fun q t => (Q.arc q).toPath t) (fun q t => ((G).arc q).toPath t)
    (fun _ _ => rfl) ht
  have ht'' := uibotCut2_source_topological_map W H h hpast hp _ ht'
  change D39TopologicalCcwSuccessor
    (C '' (f '' {q : T | restrictedVertex G T q = restrictedVertex G T d}))
    (fun q t => intrinsicFutureDartArc S q t) (C (f d)) (C (f (R d))) at ht''
  rw [hstar] at ht''
  apply intrinsicFutureRotation_map (A := S) (B := A) I
  refine ⟨(R d).property, d.property, ?_, ht''⟩
  erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex, hvr]

end Representative

/- REMAINING OBLIGATIONS. These are comments, not assumptions or declarations.
They are to hold on the common event of the assignment. All witness binders
are displayed; none of the statements below is claimed proved by this file.

1. Ambient comparison of the entire shifted run with its inherited drawing.
This supplies the same homeomorphism for the hatted and primed restrictions.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (n : ℤ) (J : WholePlaneStartIso W n),
  let U := shiftWordInt W n
  let u := shiftedStream U 0
  ∀ (hfin : hatLimitFiniteIncidence u),
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ Φ : ℂ ≃ₜ ℂ, OrientationPreserving Φ ∧
    (∀ v, Φ (P.pos v) = G.pos (J.vertex (wholePlaneVertexι U 0 v))) ∧
    (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
      StrictMono φ ∧ ∀ t,
        Φ ((P.arc d).toPath t) =
          (G.arc (J.dart (wholePlaneDartι U 0 d))).toPath (φ t))

The missing mathematical construction is a compatible ambient extension over
the infinite drawing. `WholePlaneStartIso.rot` proves no arc identity.
`uibotFiniteWindow_final_ambient_canonical` compares a single finite window;
it imposes no agreement between its homeomorphisms for different windows.
`futureMaps_iUnion_run_drawing_image` and `futureMaps_glued_face_capture`
concern restrictions of G and supply no such compatibility either.

2. Exact Proposition 5.1 remainder from IntrinsicConsumer51Submaps.lean:482.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
  (n : ℤ) (J : WholePlaneStartIso W n),
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  ∀ (hflow : HasFlowLineHits u)
    (hhat : hatLimitFiniteIncidence u)
    (hprime : primedLimitFiniteIncidence u)
    (hb : BoundaryHitWitnesses u),
  ∀ K : Set ℕ,
    K = {e | MhatGeometricEdge u e} ∨ K = {e | primeGeomEdge u hprime hb e} →
    let U := shiftWordInt W n
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp (J.dart (wholePlaneDartι U 0 d)))
    let P := monotoneFamilyDrawing u hhat (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    ∃ R : Q.Face → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

3. Lemma 5.2 analogue, using the stopped embeddings exported by
IntrinsicConsumer52.lean. As in (2), this compares the shifted certificate's
actual drawing Q with the representative submap, not merely two inherited
restrictions. The existing `hatRootedMapClause u hτ hfin` then supplies its
rotation, geometric-face and exterior certificate on the common event.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (k : ℤ),
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
  let S := uibotWholePlaneSourceDomain W H G hp
  let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
  let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
  let D := fun d : ℕ × Bool => intrinsicFutureDartEquiv (A := S) I
    (uibotCut2SourceDartEquiv W H h hpast hp
      (wholePlaneDartι W 0 (kmswWindowEdgeMapInf w t d.1, d.2)))
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let T := {d : ℕ × Bool | MhatGeometricEdge u d.1}
  let Q := hatRealizedDrawing u hfin
  ∃ R : Q.Face → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
    (∀ F, IsOpen (R F)) ∧
    (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
    (∀ d : T, intrinsicFutureRotation A (Set.range E)
      (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
    (∀ (d : T) (F : Q.Face),
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

No intrinsic qualifier is removed. No numbered paper result is closed. -/

end DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
