/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers38And51And53
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7
import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect7
import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField











public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Topology

/-- Helper toward Proposition 3.9: the drawing trace of the specified
retained vertices and geometric edges, including missing edges. -/
@[expose] def intrinsicConsumer51Trace (A : D39DomainRootedMap.{0})
    (V : Set A.V) (E : Set A.E) : Set ℂ :=
  A.map.pos '' V ∪ {z | ∃ e ∈ E, z ∈ Set.range (A.map.arc e)}

/-- Helper toward Proposition 3.9: faces of a retained drawing are its
actual complementary components, specified as entire plane regions. -/
@[expose] def intrinsicConsumer51FaceRegions (T : Set ℂ) : Set (Set ℂ) :=
  {F | ∃ z, z ∉ T ∧ F = connectedComponentIn Tᶜ z}

section Transport
variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: restricting the vertex and geometric
edge carriers commutes with the actual ambient plane homeomorphism. -/
theorem intrinsicConsumer51_trace_map (V : Set A.V) (E : Set A.E) :
    intrinsicConsumer51Trace B (I.vertexEquiv '' V) (I.edgeEquiv '' E) =
      I.h '' intrinsicConsumer51Trace A V E := by
  ext z
  constructor
  · rintro (⟨_, ⟨v, hv, rfl⟩, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, hz⟩)
    · exact ⟨A.map.pos v, Or.inl ⟨v, hv, rfl⟩, I.pos_map v⟩
    · rw [← I.arc_range_map e] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, Or.inr ⟨e, he, hy⟩, rfl⟩
  · rintro ⟨y, (⟨v, hv, rfl⟩ | ⟨e, he, hy⟩), rfl⟩
    · exact Or.inl ⟨I.vertexEquiv v, ⟨v, hv, rfl⟩, (I.pos_map v).symm⟩
    · exact Or.inr ⟨I.edgeEquiv e, ⟨e, he, rfl⟩,
        I.arc_range_map e ▸ ⟨y, hy, rfl⟩⟩

/-- Helper toward Proposition 3.9: every retained drawing component is
transported as a full region, rather than just as a boundary orbit. -/
theorem intrinsicConsumer51_component_map (V : Set A.V) (E : Set A.E)
    (z : ℂ) (hz : z ∉ intrinsicConsumer51Trace A V E) :
    connectedComponentIn
      (intrinsicConsumer51Trace B (I.vertexEquiv '' V) (I.edgeEquiv '' E))ᶜ (I.h z) =
      I.h '' connectedComponentIn (intrinsicConsumer51Trace A V E)ᶜ z := by
  rw [I.h.image_connectedComponentIn hz, I.h.image_compl,
    intrinsicConsumer51_trace_map I]

/-- Helper toward Proposition 3.9: the internal and exterior candidate
regions are exactly the complementary regions of the transported drawing. -/
theorem intrinsicConsumer51_faceRegions_map (V : Set A.V) (E : Set A.E) :
    intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace B (I.vertexEquiv '' V) (I.edgeEquiv '' E)) =
      (fun F => I.h '' F) ''
        intrinsicConsumer51FaceRegions (intrinsicConsumer51Trace A V E) := by
  ext F
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨z, rfl⟩ := I.h.surjective z
    have hz' : z ∉ intrinsicConsumer51Trace A V E := by
      rwa [intrinsicConsumer51_trace_map I, I.h.injective.mem_set_image] at hz
    exact ⟨connectedComponentIn (intrinsicConsumer51Trace A V E)ᶜ z,
      ⟨z, hz', rfl⟩, (intrinsicConsumer51_component_map I V E z hz').symm⟩
  · rintro ⟨F, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨I.h z, ?_, (intrinsicConsumer51_component_map I V E z hz).symm⟩
    rw [intrinsicConsumer51_trace_map I, I.h.injective.mem_set_image]
    exact hz

/-- Helper toward Proposition 3.9: geometric externality of every
retained complementary region is preserved and reflected. -/
theorem intrinsicConsumer51_external_map (F : Set ℂ) :
    (¬ Bornology.IsBounded (I.h '' F)) ↔ ¬ Bornology.IsBounded F :=
  (PastFacesLower.isBounded_image_iff I.h F).not

/-- Helper toward Proposition 3.9: the induced rotation, complete face
regions and their winding-left incidences transport simultaneously. -/
theorem intrinsicConsumer51_geometry_map (V : Set A.V) (E : Set A.E) :
    (∀ d a : A.E × Bool,
      intrinsicFutureRotation B (I.edgeEquiv '' E)
        (intrinsicFutureDartEquiv I d) (intrinsicFutureDartEquiv I a) ↔
          intrinsicFutureRotation A E d a) ∧
    intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace B (I.vertexEquiv '' V) (I.edgeEquiv '' E)) =
      (fun F => I.h '' F) ''
        intrinsicConsumer51FaceRegions (intrinsicConsumer51Trace A V E) ∧
    (∀ (F : Set ℂ) (d : A.E × Bool),
      (∀ s, LeftAtOn (I.h '' F)
        (intrinsicFutureDartArc B (intrinsicFutureDartEquiv I d)) s) ↔
          ∀ s, LeftAtOn F (intrinsicFutureDartArc A d) s) ∧
    (∀ F : Set ℂ, (¬ Bornology.IsBounded (I.h '' F)) ↔ ¬ Bornology.IsBounded F) :=
  ⟨intrinsicFutureRotation_map_iff I E,
    intrinsicConsumer51_faceRegions_map I V E,
    fun F d => (intrinsicFuture_leftAtOn_map I F d).symm,
    intrinsicConsumer51_external_map I⟩

end Transport

/-- Helper toward Proposition 3.9: the vertices incident to a specified
KMSW geometric edge set, with both incidences retained. -/
@[expose] def intrinsicConsumer51RunVertices (u : ℕ → Fin 3) (K : Set ℕ) : Set ℕ :=
  {v | ∃ d : ℕ × Bool, d.1 ∈ K ∧ kmswLimitDartVertex u d = v}

/-- Helper toward Proposition 3.9: the hatted incident vertices are
exactly the reachable vertices, with no isolated root lost. -/
theorem intrinsicConsumer51_hat_vertices (u : ℕ → Fin 3) :
    intrinsicConsumer51RunVertices u {e | MhatGeometricEdge u e} =
      {v | MhatVertex u v} := by
  ext v
  exact hatRealizedVertex_iff_reachable u v

/-- Helper toward Proposition 3.9: the primed incident vertices are
exactly the g18 KMSW-defined geometric vertex carrier. -/
theorem intrinsicConsumer51_primed_vertices (u : ℕ → Fin 3)
    (hprime : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u) :
    intrinsicConsumer51RunVertices u {e | primeGeomEdge u hprime hb e} =
      {v | primeVertex u hprime hb v} := by
  ext v
  constructor
  · rintro ⟨⟨e, b⟩, he, hv⟩
    refine ⟨e, he, ?_⟩
    cases b
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro ⟨e, he, hv | hv⟩
    · exact ⟨(e, false), he, hv⟩
    · exact ⟨(e, true), he, hv⟩

private theorem intrinsicConsumer51_dart_range (A : D39DomainRootedMap.{0})
    (d : A.E × Bool) :
    Set.range (intrinsicFutureDartArc A d) = Set.range (A.map.arc d.1) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact Path.symm_range _
  · rfl

section RunZero
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "u" => shiftedStream W 0
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "C" => uibotCut2SourceDartEquiv W H h hpast hp
local notation "P" => monotoneFamilyDrawing u ((And.left H) 0) (monotone_family_all u)

/-- Helper toward Proposition 3.9: each retained geometric edge of run
zero has precisely its original polyline image in the glued drawing. -/
theorem intrinsicConsumer51_source_edge_range (e : ℕ) :
    Set.range ((S).map.arc (wholePlaneEdgeι W 0 e)) = ((P).arc (e, false)).image := by
  let d := wholePlaneDartι W 0 (e, false)
  obtain ⟨φ, _, hφ⟩ := uibotCut2SourceDartEquiv_arc_param W H h hpast hp d
  have hr : Set.range (intrinsicFutureDartArc S (C d)) =
      Set.range ((G).arc d).toPath := by
    rw [show intrinsicFutureDartArc S (C d) = ((G).arc d).toPath ∘ φ from funext hφ,
      Set.range_comp, Set.range_eq_univ.mpr φ.surjective, Set.image_univ]
  rw [intrinsicConsumer51_dart_range] at hr
  change Set.range ((S).map.arc (wholePlaneEdgeι W 0 e)) = _ at hr
  rw [hr, Polyline.range_toPath, WholePlanePastGlueM0Restriction.restrict_arc]

/-- Helper toward Proposition 3.9: the actual run-zero submap trace is
exactly the image of its KMSW restricted drawing, for every retained edge set. -/
theorem intrinsicConsumer51_source_trace (K : Set ℕ) :
    intrinsicConsumer51Trace S
      (wholePlaneVertexι W 0 '' intrinsicConsumer51RunVertices u K)
      (wholePlaneEdgeι W 0 '' K) =
      (restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)).image := by
  let Q := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
  have hv (v : ℕ) : (S).map.pos (wholePlaneVertexι W 0 v) = (P).pos v :=
    WholePlanePastGlueM0Restriction.restrict_pos W h hpast H v
  have he (e : ℕ) : ((P).arc (e, true)).image = ((P).arc (e, false)).image := by
    have hf := (P).arc_flip (e, false)
    change (P).arc (e, true) = ((P).arc (e, false)).reverse at hf
    rw [hf, Polyline.image_reverse_transfer]
  ext z
  constructor
  · rintro (⟨_, ⟨v, ⟨d, hd, hdv⟩, rfl⟩, rfl⟩ | ⟨_, ⟨e, heK, rfl⟩, hz⟩)
    · left
      refine ⟨⟨v, d, hd, hdv⟩, ?_⟩
      exact (hv v).symm
    · rw [intrinsicConsumer51_source_edge_range W H h hpast hp] at hz
      exact Or.inr ⟨⟨(e, false), heK⟩, hz⟩
  · rintro (⟨v, rfl⟩ | ⟨⟨⟨e, b⟩, heK⟩, hz⟩)
    · exact Or.inl ⟨wholePlaneVertexι W 0 v.val, ⟨v.val, v.property, rfl⟩, hv v.val⟩
    · refine Or.inr ⟨wholePlaneEdgeι W 0 e, ⟨e, heK, rfl⟩, ?_⟩
      rw [intrinsicConsumer51_source_edge_range W H h hpast hp]
      cases b
      · exact hz
      · exact he e ▸ hz

variable (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)

include h hpast I

/-- Helper toward Proposition 3.9: the restricted drawing's cyclic
successor is the induced geometric rotation on the actual run-zero submap. -/
theorem intrinsicConsumer51_runZero_rotation (K : Set ℕ)
    (d : {d : ℕ × Bool // d.1 ∈ K}) :
    let R := drawingFirstReturnPerm P {q : ℕ × Bool | q.1 ∈ K}
    let J := fun q => intrinsicFutureDartEquiv (A := S) I (C (wholePlaneDartι W 0 q))
    intrinsicFutureRotation A (I.edgeEquiv '' (wholePlaneEdgeι W 0 '' K))
      (J (R d).val) (J d.val) := by
  intro R J
  let T := {q : ℕ × Bool | q.1 ∈ K}
  let Q := restrictDrawing P T (fun _ => Iff.rfl)
  let f := fun q : T => wholePlaneDartι W 0 q.val
  let intrinsicConsumer51RestrictedDartNonempty : Nonempty T := ⟨d⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hab))
      (congrArg (fun q : WholePlaneDart W => q.2) hab)
  have hvr : kmswLimitDartVertex u (R d).val = kmswLimitDartVertex u d.val :=
    congrArg Subtype.val (Q.vert_rotation d)
  have hstar : C '' (f '' {q : T | restrictedVertex P T q = restrictedVertex P T d}) =
      {q : (S).E × Bool | q.1 ∈ wholePlaneEdgeι W 0 '' K ∧
        d39GeomRootVertex (S).map q = d39GeomRootVertex (S).map (C (f (R d)))} := by
    ext q
    obtain ⟨q, rfl⟩ := (C).surjective q
    rw [(C).injective.mem_set_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a.val.1, a.property, rfl⟩, ?_⟩
      erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex,
        wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hvr]
      exact congrArg (wholePlaneVertexι W 0) (congrArg Subtype.val ha)
    · rintro ⟨⟨e, he, heq⟩, hqv⟩
      have hq : q = f ⟨(e, q.2), he⟩ := Prod.ext heq.symm rfl
      rw [hq] at hqv ⊢
      refine ⟨⟨(e, q.2), he⟩, ?_, rfl⟩
      apply Subtype.ext
      erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex,
        wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hvr] at hqv
      exact wholePlaneVertexι_injective W 0 hqv
  have ht := plDrawing_toPath_rotation_topological_ccwSuccessor Q d
  have ht' := intrinsicFutureCut2_topological_image f hi _
    (fun q t => (Q.arc q).toPath t) (fun q t => ((G).arc q).toPath t)
    (fun q t => congrArg (fun p : Polyline => p.toPath t)
      (WholePlanePastGlueM0Restriction.restrict_arc W h hpast H q.val)) ht
  have ht'' := uibotCut2_source_topological_map W H h hpast hp _ ht'
  change D39TopologicalCcwSuccessor
    (C '' (f '' {q : T | restrictedVertex P T q = restrictedVertex P T d}))
    (fun q t => intrinsicFutureDartArc S q t) (C (f d)) (C (f (R d))) at ht''
  rw [hstar] at ht''
  apply intrinsicFutureRotation_map (A := S) (B := A) I
  refine ⟨⟨(R d).val.1, (R d).property, rfl⟩,
    ⟨d.val.1, d.property, rfl⟩, ?_, ht''⟩
  erw [uibotCut2SourceDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex,
    wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hvr]

/-- Helper toward Proposition 3.9: every run-zero restricted face is
an actual complementary component of the corresponding representative submap,
and all its complementary components are obtained this way. -/
theorem intrinsicConsumer51_runZero_faceRegions (K : Set ℕ) :
    let V := fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)
    let E := fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)
    let Q := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
    intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) =
        Set.range (fun F : Q.Face => I.h '' F.val) := by
  intro V E Q
  have hv : V '' intrinsicConsumer51RunVertices u K =
      I.vertexEquiv '' (wholePlaneVertexι W 0 '' intrinsicConsumer51RunVertices u K) :=
    (Set.image_image _ _ _).symm
  have he : E '' K = I.edgeEquiv '' (wholePlaneEdgeι W 0 '' K) :=
    (Set.image_image _ _ _).symm
  have hT : intrinsicConsumer51Trace A
      (V '' intrinsicConsumer51RunVertices u K) (E '' K) = I.h '' Q.image := by
    rw [hv, he]
    exact (intrinsicConsumer51_trace_map (A := S) (B := A) I _ _).trans
      (congrArg (fun T => I.h '' T)
        (intrinsicConsumer51_source_trace W H h hpast hp K))
  rw [hT]
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

/-- Helper toward Proposition 3.9: each run-zero restricted face's
winding-left incidence in the representative equals its original geometric
dart-border incidence, including exterior faces and missing geometric edges. -/
theorem intrinsicConsumer51_runZero_face_side (K : Set ℕ)
    (d : {d : ℕ × Bool // d.1 ∈ K})
    (F : (restrictDrawing P {q : ℕ × Bool | q.1 ∈ K} (fun _ => Iff.rfl)).Face) :
    let J := fun q => intrinsicFutureDartEquiv (A := S) I (C (wholePlaneDartι W 0 q))
    (∀ s, LeftAtOn (I.h '' F.val) (intrinsicFutureDartArc A (J d.val)) s) ↔
      (restrictDrawing P {q : ℕ × Bool | q.1 ∈ K} (fun _ => Iff.rfl)).dartBorders d F := by
  intro J
  let T := {q : ℕ × Bool | q.1 ∈ K}
  let Q := restrictDrawing P T (fun _ => Iff.rfl)
  have hvert : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, q, hq, hqv⟩
    exact ⟨⟨q, hq⟩, Subtype.ext hqv⟩
  have hi := (intrinsicFuture_leftAtOn_map (A := S) (B := A) I F.val
    (C (wholePlaneDartι W 0 d.val))).symm
  have hs := uibotCut2_source_leftAtOn_iff W H h hpast hp
    (wholePlaneDartι W 0 d.val) F.val
  have hb : (∀ s, LeftAtOn F.val (Q.arc d).toPath s) ↔ Q.dartBorders d F :=
    ⟨LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective Q hvert d F,
      fun hF s => Q.dartBorders_toPath_leftAtOn hvert d F hF s⟩
  apply hi.trans
  apply hs.trans
  rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H d.val]
  exact hb

/-- Helper toward Proposition 3.9: externality of every restricted
run-zero face is tested in the representative's plane. -/
theorem intrinsicConsumer51_runZero_external (K : Set ℕ)
    (F : (restrictDrawing P {q : ℕ × Bool | q.1 ∈ K} (fun _ => Iff.rfl)).Face) :
    (¬ Bornology.IsBounded (I.h '' F.val)) ↔
      (restrictDrawing P {q : ℕ × Bool | q.1 ∈ K} (fun _ => Iff.rfl)).IsUnbounded F := by
  rw [PastFacesLower.isBounded_image_iff]
  constructor
  · intro hb R
    by_contra hR
    apply hb
    exact isBounded_iff_forall_norm_le.mpr ⟨R, fun z hz => le_of_not_gt
      (fun hlt => hR ⟨z, hz, hlt⟩)⟩
  · intro hF hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨z, hz, hlt⟩ := hF R
    exact hlt.not_ge (hR z hz)

/-- Helper toward Proposition 3.9: every transported restricted face
is an open region in the representative's own plane. -/
theorem intrinsicConsumer51_runZero_face_open (K : Set ℕ)
    (F : (restrictDrawing P {q : ℕ × Bool | q.1 ∈ K} (fun _ => Iff.rfl)).Face) :
    IsOpen (I.h '' F.val) := by
  let T := {q : ℕ × Bool | q.1 ∈ K}
  let Q := restrictDrawing P T (fun _ => Iff.rfl)
  have hvert : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, q, hq, hqv⟩
    exact ⟨⟨q, hq⟩, Subtype.ext hqv⟩
  apply I.h.isOpenMap
  obtain ⟨z, _, hF⟩ := F.property
  rw [hF]
  exact (Q.image_isClosed hvert).isOpen_compl.connectedComponentIn

end RunZero

/-- Helper toward Proposition 3.9: on the common Proposition 5.1 event,
both run-zero certificates have their rotation, complete geometric face
incidences and exterior incidence in every actual representative. The integer
shift extension is a separate obligation. -/
theorem intrinsicConsumer51_runZero_sample :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (A : D39DomainRootedMap.{0})
        (I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
          (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
          A.map A.root),
        let u := shiftedStream W 0
        let S := uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
        let J := fun d => intrinsicFutureDartEquiv (A := S) I
          (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 d))
        ∃ (hflow : HasFlowLineHits u) (hhat : hatLimitFiniteIncidence u)
          (hprime : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          hatRootedMapClause u hflow hhat ∧ primedRootedMapClause u hflow hprime hb ∧
          ∃ (Dh : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge u d.1})
            (Fh : HatFaceOrbit u hflow hhat ≃ (hatRealizedDrawing u hhat).Face)
            (Dp : (ℕ × Bool) ≃ {d // d ∈ primeDartSet u hprime hb})
            (Fp : PrimedFaceOrbit u hflow hprime ≃
              (mhatPrimeDrawing u hprime hb (monotone_family_all u)).Face),
            (∀ d, (Dh d).val = (hatLimitEdgeMap u hflow d.1, d.2)) ∧
            (∀ d, (Dp d).val = primedLimitDartMap u hflow d) ∧
            (∀ d, intrinsicFutureRotation A
              (I.edgeEquiv '' (wholePlaneEdgeι W 0 '' {e | MhatGeometricEdge u e}))
              (J (Dh (kmswInfRot (hatCodes u hflow)
                (hatCodes_finiteIncidence u hflow hhat) d)).val) (J (Dh d).val)) ∧
            (∀ d, intrinsicFutureRotation A
              (I.edgeEquiv '' (wholePlaneEdgeι W 0 '' {e | primeGeomEdge u hprime hb e}))
              (J (Dp (kmswInfRot (primedCode (primedSimInput u) hflow)
                (primedCode_finiteIncidence u hflow hprime) d)).val) (J (Dp d).val)) ∧
            (∀ d q, (∀ s, LeftAtOn (I.h '' (Fh q).val)
              (intrinsicFutureDartArc A (J (Dh d).val)) s) ↔ Quotient.mk _ d = q) ∧
            (∀ d q, (∀ s, LeftAtOn (I.h '' (Fp q).val)
              (intrinsicFutureDartArc A (J (Dp d).val)) s) ↔ Quotient.mk _ d = q) ∧
            (∀ q, (¬ Bornology.IsBounded (I.h '' (Fh q).val)) ↔
              q = Quotient.mk _ futureMapOuterDart) ∧
            (∀ q, (¬ Bornology.IsBounded (I.h '' (Fp q).val)) ↔
              q = Quotient.mk _ futureMapOuterDart) ∧
            (∀ d, (∀ s, LeftAtOn (I.h '' (Fh (Quotient.mk _ futureMapOuterDart)).val)
              (intrinsicFutureDartArc A (J (Dh d).val)) s) ↔
                limitExternalDart (hatCodes u hflow) d) ∧
            (∀ d, (∀ s, LeftAtOn (I.h '' (Fp (Quotient.mk _ futureMapOuterDart)).val)
              (intrinsicFutureDartArc A (J (Dp d).val)) s) ↔
                limitExternalDart (primedCode (primedSimInput u) hflow) d) := by
  filter_upwards [DirectedDistances.Paper.Section5.future_map_law.2.2] with W hW
  intro H h hpast hp A I u S J
  have hraw : (fun i => futureMapShiftedCodePath 0 W (i + 1)) = u := by
    rw [futureMapShiftedCodePath_tail]
    funext i
    simp only [futureMapShiftedStream_apply, add_zero, shiftedStream, Nat.cast_zero, sub_zero, u]
  have hw := hW 0
  dsimp only at hw
  rw [hraw] at hw
  obtain ⟨_, hflow, hhat, hprime, hb, _, _, hhc, hpc⟩ := hw
  refine ⟨hflow, hhat, hprime, hb, hhc, hpc, ?_⟩
  obtain ⟨Dh, Fh, hDh, _, _, _, _, _, hhr, _, hhf, hhe, hhx⟩ := hhc
  obtain ⟨Dp, _, Fp, hDp, _, _, _, _, _, _, _, _, _, _, hpr, _, hpf, hpe, hpx⟩ := hpc
  refine ⟨Dh, Fh, Dp, Fp, hDh, hDp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [hhr d]
    exact intrinsicConsumer51_runZero_rotation W H h hpast hp A I
      {e | MhatGeometricEdge u e} (Dh d)
  · intro d
    rw [hpr d]
    exact intrinsicConsumer51_runZero_rotation W H h hpast hp A I
      {e | primeGeomEdge u hprime hb e} (Dp d)
  · intro d q
    exact (intrinsicConsumer51_runZero_face_side W H h hpast hp A I
      {e | MhatGeometricEdge u e} (Dh d) (Fh q)).trans
      (hhf d q)
  · intro d q
    exact (intrinsicConsumer51_runZero_face_side W H h hpast hp A I
      {e | primeGeomEdge u hprime hb e} (Dp d) (Fp q)).trans
      (hpf d q)
  · intro q
    exact (intrinsicConsumer51_runZero_external W H h hpast hp A I
      {e | MhatGeometricEdge u e} (Fh q)).trans (hhe q)
  · intro q
    exact (intrinsicConsumer51_runZero_external W H h hpast hp A I
      {e | primeGeomEdge u hprime hb e} (Fp q)).trans (hpe q)
  · intro d
    exact (intrinsicConsumer51_runZero_face_side W H h hpast hp A I
      {e | MhatGeometricEdge u e} (Dh d) (Fh (Quotient.mk _ futureMapOuterDart))).trans (hhx d)
  · intro d
    exact (intrinsicConsumer51_runZero_face_side W H h hpast hp A I
      {e | primeGeomEdge u hprime hb e} (Dp d) (Fp (Quotient.mk _ futureMapOuterDart))).trans (hpx d)




















































end DirectedDistances.PaperProofs.Section3
