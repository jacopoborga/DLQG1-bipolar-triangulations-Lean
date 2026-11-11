/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.IntrinsicFutureCut
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart1
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3Transport

/-! # Geometric comparison with an intrinsic future cut

The comparisons below retain actual edge identities and stored endpoint
reversals. They do not identify a coordinate upper half-plane with the
intrinsic winding-positive side without proving that identification. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1

section Transport
variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: the geometric map carries each directed
tail to the directed tail, allowing a reversal of stored edge endpoints. -/
theorem intrinsicFuture_tail_map
    (e : {e : A.E // ¬ A.map.missing e}) :
    I.vertexEquiv (A.map.tail e) =
      B.map.tail ⟨I.edgeEquiv e.val, fun hm => e.property ((I.missing_map e.val).mp hm)⟩ := by
  have ho := I.orientation_map e.val e.property
  have hs := I.src_map e.val
  have ht := I.tgt_map e.val
  cases hf : A.map.forward e <;> cases hb : I.edgeFlip e.val <;>
    simp only [hf, hb, Bool.xor_false, Bool.false_xor, Bool.true_xor,
      Bool.not_true] at ho hs ht <;>
    simp only [DirectedPlaneMapWithMissing.tail, hf, ho, Bool.false_eq_true,
      ↓reduceIte, hs, ht]

/-- Helper toward Proposition 3.9: the geometric map carries each directed
head to the directed head, allowing a reversal of stored edge endpoints. -/
theorem intrinsicFuture_head_map
    (e : {e : A.E // ¬ A.map.missing e}) :
    I.vertexEquiv (A.map.head e) =
      B.map.head ⟨I.edgeEquiv e.val, fun hm => e.property ((I.missing_map e.val).mp hm)⟩ := by
  have ho := I.orientation_map e.val e.property
  have hs := I.src_map e.val
  have ht := I.tgt_map e.val
  cases hf : A.map.forward e <;> cases hb : I.edgeFlip e.val <;>
    simp only [hf, hb, Bool.xor_false, Bool.false_xor, Bool.true_xor,
      Bool.not_true] at ho hs ht <;>
    simp only [DirectedPlaneMapWithMissing.head, hf, ho, Bool.false_eq_true,
      ↓reduceIte, hs, ht]

/-- Helper toward Proposition 3.9: actual geometric darts are transported
with the storage-flip bit; parallel edges are never identified. -/
@[expose] def intrinsicFutureDartEquiv : (A.E × Bool) ≃ (B.E × Bool) where
  toFun d := (I.edgeEquiv d.1, Bool.xor d.2 (I.edgeFlip d.1))
  invFun d := (I.edgeEquiv.symm d.1, Bool.xor d.2 (I.edgeFlip (I.edgeEquiv.symm d.1)))
  left_inv := by intro d; simp only [Equiv.symm_apply_apply, Bool.xor_assoc, Bool.xor_self,
    Bool.xor_false, Prod.mk.eta]
  right_inv := by intro d; simp only [Equiv.apply_symm_apply, Bool.xor_assoc, Bool.xor_self,
    Bool.xor_false, Prod.mk.eta]

/-- Helper toward Proposition 3.9: dart transport preserves the incident
vertex, including both incidences of a loop. -/
theorem intrinsicFutureDartEquiv_vertex (d : A.E × Bool) :
    d39GeomRootVertex B.map (intrinsicFutureDartEquiv I d) =
      I.vertexEquiv (d39GeomRootVertex A.map d) := by
  have hs := I.src_map d.1
  have ht := I.tgt_map d.1
  cases hb : d.2 <;> cases hf : I.edgeFlip d.1 <;>
    simp only [hf, Bool.false_eq_true, ite_false, ite_true] at hs ht <;>
    simp only [intrinsicFutureDartEquiv, Equiv.coe_fn_mk, d39GeomRootVertex,
      hb, hf, Bool.xor_false, Bool.false_xor, Bool.true_xor, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, hs, ht]

/-- Helper toward Proposition 3.9: the marked directed root dart is
preserved, including its storage bit. -/
theorem intrinsicFutureDartEquiv_root : intrinsicFutureDartEquiv I A.root = B.root :=
  Prod.ext I.root_edge_map I.root_bool_map.symm

/-- Helper toward Proposition 3.9: the dart's interval parameter accounts
for both storage conventions and the edge parameter of the isomorphism. -/
@[expose] def intrinsicFutureDartParam (d : A.E × Bool) :
    unitInterval ≃ₜ unitInterval :=
  ((d39DartParamReversal d.2).trans (I.edgeParam d.1)).trans
    (d39DartParamReversal (Bool.xor d.2 (I.edgeFlip d.1)))

/-- Helper toward Proposition 3.9: the parameter on an oriented geometric
dart is increasing even if the stored edge parameter is decreasing. -/
theorem intrinsicFutureDartParam_strictMono (d : A.E × Bool) :
    StrictMono (intrinsicFutureDartParam I d) := by
  have hs := unitInterval.strictAnti_symm
  cases hb : d.2 <;> cases hf : I.edgeFlip d.1 <;>
    simp only [intrinsicFutureDartParam, d39DartParamReversal, hb, hf,
      Bool.xor_false, Bool.false_xor, Bool.true_xor, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true]
  · change StrictMono (fun t => unitInterval.symm (I.edgeParam d.1 (unitInterval.symm t)))
    exact hs.comp (I.edgeParam_mono d.1 hf |>.comp_strictAnti hs)
  · change StrictMono (fun t => I.edgeParam d.1 (unitInterval.symm t))
    exact (I.edgeParam_anti d.1 hf).comp hs
  · change StrictMono (fun t => I.edgeParam d.1 t)
    exact I.edgeParam_mono d.1 hf
  · change StrictMono (fun t => unitInterval.symm (I.edgeParam d.1 t))
    exact hs.comp (I.edgeParam_anti d.1 hf)

/-- Helper toward Proposition 3.9: point evaluation of a geometric dart
uses the selected stored orientation, without any endpoint transport casts. -/
theorem intrinsicFutureDartArc_apply (d : A.E × Bool) (t : unitInterval) :
    intrinsicFutureDartArc A d t =
      if d.2 then A.map.arc d.1 t else A.map.arc d.1 (unitInterval.symm t) := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- Helper toward Proposition 3.9: every point of an oriented dart arc
is carried to the corresponding target dart with the increasing parameter. -/
theorem intrinsicFutureDartArc_map (d : A.E × Bool) (t : unitInterval) :
    I.h (intrinsicFutureDartArc A d t) =
      intrinsicFutureDartArc B (intrinsicFutureDartEquiv I d)
        (intrinsicFutureDartParam I d t) := by
  rw [intrinsicFutureDartArc_apply (A := A) d t,
    intrinsicFutureDartArc_apply (A := B) (intrinsicFutureDartEquiv I d)
      (intrinsicFutureDartParam I d t)]
  rcases d with ⟨e, b⟩
  cases b <;> cases hf : I.edgeFlip e <;>
    simp [intrinsicFutureDartEquiv, intrinsicFutureDartParam,
      d39DartParamReversal, hf, I.arc_map] <;> rfl

/-- Helper toward Proposition 3.9: the ambient tail predicate is invariant
under the dart equivalence, with absence of orientation on missing edges. -/
theorem intrinsicFutureAmbientTail_map (d : A.E × Bool) :
    intrinsicFutureAmbientTail B (intrinsicFutureDartEquiv I d) ↔
      intrinsicFutureAmbientTail A d := by
  constructor
  · rintro ⟨he, hb⟩
    have heA : ¬ A.map.missing d.1 := fun hn => he ((I.missing_map d.1).mpr hn)
    refine ⟨heA, ?_⟩
    have ho := I.orientation_map d.1 heA
    change B.map.forward ⟨I.edgeEquiv d.1, he⟩ = Bool.xor d.2 (I.edgeFlip d.1) at hb
    rw [ho] at hb
    have hc := congrArg (fun b => Bool.xor b (I.edgeFlip d.1)) hb
    simpa only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] using hc
  · rintro ⟨he, hb⟩
    refine ⟨fun hn => he ((I.missing_map d.1).mp hn), ?_⟩
    exact (I.orientation_map d.1 he).trans (congrArg (fun b => Bool.xor b (I.edgeFlip d.1)) hb)

/-- Helper toward Proposition 3.9: inverse topological rotation transports
on every retained edge set, including all geometric missing-edge incidences. -/
theorem intrinsicFutureRotation_map (S : Set A.E) (d a : A.E × Bool)
    (hr : intrinsicFutureRotation A S d a) :
    intrinsicFutureRotation B (I.edgeEquiv '' S)
      (intrinsicFutureDartEquiv I d) (intrinsicFutureDartEquiv I a) := by
  let E := intrinsicFutureDartEquiv I
  have hv (b c : A.E × Bool) :
      d39GeomRootVertex B.map (E b) = d39GeomRootVertex B.map (E c) ↔
        d39GeomRootVertex A.map b = d39GeomRootVertex A.map c := by
    rw [intrinsicFutureDartEquiv_vertex, intrinsicFutureDartEquiv_vertex]
    exact I.vertexEquiv.injective.eq_iff
  have hstar : E '' {q : A.E × Bool | q.1 ∈ S ∧
      d39GeomRootVertex A.map q = d39GeomRootVertex A.map d} =
      {q : B.E × Bool | q.1 ∈ I.edgeEquiv '' S ∧
        d39GeomRootVertex B.map q = d39GeomRootVertex B.map (E d)} := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [E.injective.mem_set_image]
    change (_ ∧ _) ↔ (I.edgeEquiv p.1 ∈ I.edgeEquiv '' S ∧ _)
    rw [I.edgeEquiv.injective.mem_set_image, hv]
  refine ⟨⟨d.1, hr.1, rfl⟩, ⟨a.1, hr.2.1, rfl⟩, (hv a d).mpr hr.2.2.1, ?_⟩
  have hm := d39TopologicalCcwSuccessor_map_equiv E hr.2.2.2
  rw [hstar] at hm
  apply d39TopologicalCcwSuccessor_map_orientedHomeomorph _ _ _
    (fun q => intrinsicFutureDartParam I (E.symm q)) (E a) (E d)
    I.h I.orientationPreserving _ _ hm
  · intro q _
    exact intrinsicFutureDartParam_strictMono I (E.symm q)
  · intro q _ t
    have hc := intrinsicFutureDartArc_map I (E.symm q) t
    change I.h (intrinsicFutureDartArc A (E.symm q) t) =
      intrinsicFutureDartArc B (E (E.symm q)) (intrinsicFutureDartParam I (E.symm q) t) at hc
    exact hc.trans (congrArg
      (fun b => intrinsicFutureDartArc B b (intrinsicFutureDartParam I (E.symm q) t))
      (E.apply_symm_apply q))

/-- Helper toward Proposition 3.9: the full geometric seam trace commutes
with an arbitrary rooted geometric isomorphism. -/
theorem intrinsicFuture_seam_trace_map (seam : A.E → Prop) :
    intrinsicFutureSeamTrace B (fun e => seam (I.edgeEquiv.symm e)) =
      I.h '' intrinsicFutureSeamTrace A seam := by
  ext z
  constructor
  · rintro ⟨e, he, hz⟩
    have hr := I.arc_range_map (I.edgeEquiv.symm e)
    rw [I.edgeEquiv.apply_symm_apply] at hr
    obtain ⟨y, hy, rfl⟩ := hr.symm ▸ hz
    exact ⟨y, ⟨I.edgeEquiv.symm e, he, hy⟩, rfl⟩
  · rintro ⟨y, ⟨e, he, hy⟩, rfl⟩
    refine ⟨I.edgeEquiv e, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using he
    · rw [← I.arc_range_map]
      exact ⟨y, hy, rfl⟩

/-- Helper toward Proposition 3.9: simultaneous winding-positive side
tests along a dart transport through the increasing dart parameter. -/
theorem intrinsicFuture_leftAtOn_map (F : Set ℂ) (d : A.E × Bool) :
    (∀ s, LeftAtOn F (intrinsicFutureDartArc A d) s) ↔
      ∀ s, LeftAtOn (I.h '' F)
        (intrinsicFutureDartArc B (intrinsicFutureDartEquiv I d)) s := by
  let φ := intrinsicFutureDartParam I d
  have hend := d39StrictMonoIntervalEndpoints φ (intrinsicFutureDartParam_strictMono I d)
  let γ := intrinsicFutureDartArc A d
  let δ := intrinsicFutureDartArc B (intrinsicFutureDartEquiv I d)
  calc
    (∀ s, LeftAtOn F γ s) ↔ ∀ s, LeftAtOn (I.h '' F) (γ.map I.h.continuous) s :=
      forall_congr' fun s => leftAtOn_map_iff F γ s I.h I.orientationPreserving
    _ ↔ ∀ s, LeftAtOn (I.h '' F) (δ.reparam φ φ.continuous hend.1 hend.2) s := by
      apply forall_congr'
      intro s
      exact leftAtOn_congr_fun _ _ _ s (intrinsicFutureDartArc_map I d)
    _ ↔ ∀ s, LeftAtOn (I.h '' F) δ s :=
      forall_leftAtOn_reparam_iff _ δ φ hend.1 hend.2

/-- Helper toward Proposition 3.9: the intrinsically defined open left
side is preserved by every rooted orientation-preserving geometric isomorphism. -/
theorem intrinsicFuture_openLeft_map (seam : A.E → Prop) :
    intrinsicFutureOpenLeft B (fun e => seam (I.edgeEquiv.symm e)) =
      I.h '' intrinsicFutureOpenLeft A seam := by
  let T := intrinsicFutureSeamTrace A seam
  let T' := intrinsicFutureSeamTrace B (fun e => seam (I.edgeEquiv.symm e))
  have hT : T' = I.h '' T := intrinsicFuture_seam_trace_map I seam
  have hcomp (w : ℂ) (hw : w ∉ T) :
      I.h '' connectedComponentIn Tᶜ w = connectedComponentIn T'ᶜ (I.h w) := by
    rw [I.h.image_connectedComponentIn hw, I.h.image_compl, ← hT]
  have hleft (F : Set ℂ) :
      (∀ s, LeftAtOn F (intrinsicFutureDartArc A A.root) s) ↔
        ∀ s, LeftAtOn (I.h '' F) (intrinsicFutureDartArc B B.root) s := by
    exact (intrinsicFuture_leftAtOn_map I F A.root).trans
      (Iff.of_eq (congrArg
        (fun d : B.E × Bool => ∀ s, LeftAtOn (I.h '' F) (intrinsicFutureDartArc B d) s)
        (intrinsicFutureDartEquiv_root I)))
  ext z
  obtain ⟨z, rfl⟩ := I.h.surjective z
  rw [I.h.injective.mem_set_image]
  constructor
  · rintro ⟨w, hw, hz, hl⟩
    obtain ⟨w, rfl⟩ := I.h.surjective w
    have hw' : w ∉ T := by
      change I.h w ∉ T' at hw
      rwa [hT, I.h.injective.mem_set_image] at hw
    change I.h z ∈ connectedComponentIn T'ᶜ (I.h w) at hz
    change ∀ s, LeftAtOn (connectedComponentIn T'ᶜ (I.h w))
      (intrinsicFutureDartArc B B.root) s at hl
    rw [← hcomp w hw'] at hz hl
    exact ⟨w, hw', I.h.injective.mem_set_image.mp hz, (hleft _).mpr hl⟩
  · rintro ⟨w, hw, hz, hl⟩
    refine ⟨I.h w, ?_, ?_, ?_⟩
    · change I.h w ∉ T'
      rwa [hT, I.h.injective.mem_set_image]
    · change I.h z ∈ connectedComponentIn T'ᶜ (I.h w)
      rw [← hcomp w hw]
      exact ⟨z, hz, rfl⟩
    · change ∀ s, LeftAtOn (connectedComponentIn T'ᶜ (I.h w))
        (intrinsicFutureDartArc B B.root) s
      rw [← hcomp w hw]
      exact (hleft _).mp hl

/-- Helper toward Proposition 3.9: the closed left side transports as a
closed subset of the plane, including its entire geometric interface. -/
theorem intrinsicFuture_closedLeft_map (seam : A.E → Prop) :
    closure (intrinsicFutureOpenLeft B (fun e => seam (I.edgeEquiv.symm e))) =
      I.h '' closure (intrinsicFutureOpenLeft A seam) := by
  rw [intrinsicFuture_openLeft_map, I.h.image_closure]

/-- Helper toward Proposition 3.9: inverse rotation is reflected as well
as preserved by the geometric dart equivalence on a retained edge set. -/
theorem intrinsicFutureRotation_map_iff (S : Set A.E) (d a : A.E × Bool) :
    intrinsicFutureRotation B (I.edgeEquiv '' S)
      (intrinsicFutureDartEquiv I d) (intrinsicFutureDartEquiv I a) ↔
        intrinsicFutureRotation A S d a := by
  constructor
  · intro hr
    have hh := intrinsicFutureRotation_map I.symm (I.edgeEquiv '' S)
      (intrinsicFutureDartEquiv I d) (intrinsicFutureDartEquiv I a) hr
    have hs : I.symm.edgeEquiv '' (I.edgeEquiv '' S) = S := by
      change I.edgeEquiv.symm '' (I.edgeEquiv '' S) = S
      ext e
      simp only [Set.mem_image, Equiv.symm_apply_eq]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
        exact I.edgeEquiv.injective he ▸ ha
      · intro he
        exact ⟨I.edgeEquiv e, ⟨e, he, rfl⟩, rfl⟩
    have hd : intrinsicFutureDartEquiv I.symm (intrinsicFutureDartEquiv I d) = d :=
      (intrinsicFutureDartEquiv I).symm_apply_apply d
    have ha : intrinsicFutureDartEquiv I.symm (intrinsicFutureDartEquiv I a) = a :=
      (intrinsicFutureDartEquiv I).symm_apply_apply a
    rw [hs, hd, ha] at hh
    exact hh
  · exact intrinsicFutureRotation_map I S d a

/-- Helper toward Proposition 3.9: reversal of a geometric dart commutes
with its image, including an isomorphism that reverses stored endpoints. -/
theorem intrinsicFutureDartEquiv_flip (d : A.E × Bool) :
    intrinsicFutureDartEquiv I (d.1, !d.2) =
      ((intrinsicFutureDartEquiv I d).1, !(intrinsicFutureDartEquiv I d).2) := by
  rcases d with ⟨e, b⟩
  cases b <;> cases hf : I.edgeFlip e <;>
    simp only [intrinsicFutureDartEquiv, Equiv.coe_fn_mk, hf, Bool.not_false,
      Bool.not_true, Bool.false_xor, Bool.true_xor]

/-- Helper toward Proposition 3.9: the rightmost outgoing selector is
preserved on arbitrary representatives by cyclic order and orientation. -/
theorem intrinsicFutureRightmostOutgoingAt_map (v : A.V) (e : A.E)
    (hr : intrinsicFutureRightmostOutgoingAt A v e) :
    intrinsicFutureRightmostOutgoingAt B (I.vertexEquiv v) (I.edgeEquiv e) := by
  obtain ⟨b, hb, hv, a, ha, ht⟩ := hr
  have hp : I.edgeEquiv '' {e | ¬ A.map.missing e} = {e | ¬ B.map.missing e} := by
    ext e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.injective.mem_set_image]
    exact not_congr (I.missing_map e).symm
  refine ⟨Bool.xor b (I.edgeFlip e), (intrinsicFutureAmbientTail_map I (e, b)).mpr hb,
    (intrinsicFutureDartEquiv_vertex I (e, b)).trans (congrArg I.vertexEquiv hv),
    intrinsicFutureDartEquiv I a, ?_, ?_⟩
  · have hh := intrinsicFutureRotation_map I _ (e, b) a ha
    rwa [hp] at hh
  · have hh := (intrinsicFutureAmbientTail_map I (a.1, !a.2)).mpr ht
    rwa [intrinsicFutureDartEquiv_flip] at hh

/-- Helper toward Proposition 3.9: the leftmost incoming selector is
preserved with the incoming-chain orientation required by D18. -/
theorem intrinsicFutureLeftmostIncomingAt_map (v : A.V) (e : A.E)
    (hr : intrinsicFutureLeftmostIncomingAt A v e) :
    intrinsicFutureLeftmostIncomingAt B (I.vertexEquiv v) (I.edgeEquiv e) := by
  obtain ⟨b, hb, hv, a, ha, ht⟩ := hr
  have hp : I.edgeEquiv '' {e | ¬ A.map.missing e} = {e | ¬ B.map.missing e} := by
    ext e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.injective.mem_set_image]
    exact not_congr (I.missing_map e).symm
  refine ⟨Bool.xor b (I.edgeFlip e), ?_,
    (intrinsicFutureDartEquiv_vertex I (e, b)).trans (congrArg I.vertexEquiv hv),
    intrinsicFutureDartEquiv I a, ?_, (intrinsicFutureAmbientTail_map I a).mpr ht⟩
  · have hh := (intrinsicFutureAmbientTail_map I (e, !b)).mpr hb
    have hf := intrinsicFutureDartEquiv_flip I (e, b)
    exact hf ▸ hh
  · have hh := intrinsicFutureRotation_map I _ (e, b) a ha
    rwa [hp] at hh

/-- Helper toward Proposition 3.9: the vertex, entire-edge and open-face
clauses of an intrinsic cut hold for their actual geometric images. -/
theorem intrinsicFutureCut_geometry_map (C : IntrinsicFutureCut A) :
    (∀ v : B.V, v ∈ I.vertexEquiv '' C.vertices ↔ B.map.pos v ∈
      closure (intrinsicFutureOpenLeft B (fun e => C.seam (I.edgeEquiv.symm e)))) ∧
    (∀ e : B.E, e ∈ I.edgeEquiv '' C.edges ↔ Set.range (B.map.arc e) ⊆
      closure (intrinsicFutureOpenLeft B (fun e => C.seam (I.edgeEquiv.symm e)))) ∧
    (∀ F : B.map.toPlaneGraphDrawing.Face, F ∈ I.faceEquiv '' C.faces ↔
      F.val ⊆ intrinsicFutureOpenLeft B (fun e => C.seam (I.edgeEquiv.symm e))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨v, rfl⟩ := I.vertexEquiv.surjective v
    rw [I.vertexEquiv.injective.mem_set_image, intrinsicFuture_closedLeft_map,
      ← I.pos_map, I.h.injective.mem_set_image]
    exact C.vertices_iff v
  · intro e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.injective.mem_set_image, intrinsicFuture_closedLeft_map,
      ← I.arc_range_map, Set.image_subset_image_iff I.h.injective]
    exact C.edges_iff e
  · intro F
    obtain ⟨F, rfl⟩ := I.faceEquiv.surjective F
    rw [I.faceEquiv.injective.mem_set_image, intrinsicFuture_openLeft_map,
      I.faceEquiv_val, Set.image_subset_image_iff I.h.injective]
    exact C.faces_iff F

end Transport

section Source
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "D" => m0CutData W H h (fun _ _ => hp _)
local notation "f" => seamFun (shiftedStream W 0) h ((And.left H) 0)

/-- Helper toward Proposition 3.9: membership of the entire geometric
edge in the source cut transports to the upper-side image in any representative. -/
theorem uibotCut_edge_in_representative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (e : WholePlaneEdge W) :
    e ∈ (D).edges ↔ Set.range (A.map.arc (I.edgeEquiv e)) ⊆
      I.h '' {z : ℂ | f z.re ≤ z.im} := by
  have hr : Set.range ((uibotWholePlaneSourceMap W H G hp).arc e) =
      ((G).arc (e, false)).image :=
    (G).toPlaneGraphDrawing_arc_range (e, false)
  rw [← I.arc_range_map, hr]
  exact (futureMap_left_edge_iff_above W H D h (fun _ _ => hp _) hpast e).trans
    (Set.image_subset_image_iff I.h.injective).symm

/-- Helper toward Proposition 3.9: a retained directed code edge is
exactly the corresponding present edge of the representative, lying on the
transported closed side and outside the left-chain edge range, with the
same ordered endpoints. No geometric identification premise is supplied. -/
theorem uibotCut_present_edge_in_representative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (e : WholePlaneEdge W) (a b : WholePlaneVertex W) :
    (e ∈ (D).edges ∧ ¬ (D).missing e ∧
      wholePlaneEdgeWest W e = a ∧ wholePlaneEdgeEast W e = b) ↔
    ∃ he : ¬ A.map.missing (I.edgeEquiv e),
      Set.range (A.map.arc (I.edgeEquiv e)) ⊆ I.h '' {z : ℂ | f z.re ≤ z.im} ∧
      I.edgeEquiv e ∉ Set.range (fun n : ℕ => I.edgeEquiv ((D).betaL.edge n)) ∧
      A.map.tail ⟨I.edgeEquiv e, he⟩ = I.vertexEquiv a ∧
      A.map.head ⟨I.edgeEquiv e, he⟩ = I.vertexEquiv b := by
  let S := uibotWholePlaneSourceDomain W H G hp
  have he : ¬ S.map.missing e := fun hn => hn (hp e)
  have he' : ¬ A.map.missing (I.edgeEquiv e) := fun hn => he ((I.missing_map e).mp hn)
  have ht := intrinsicFuture_tail_map (A := S) (B := A) I ⟨e, he⟩
  have hh := intrinsicFuture_head_map (A := S) (B := A) I ⟨e, he⟩
  have hend := uibotWholePlaneSourceMap_endpoints W H G hp e
  change I.vertexEquiv ((uibotWholePlaneSourceMap W H G hp).tail ⟨e, he⟩) = _ at ht
  change I.vertexEquiv ((uibotWholePlaneSourceMap W H G hp).head ⟨e, he⟩) = _ at hh
  rw [hend.1] at ht
  rw [hend.2] at hh
  have hr : I.edgeEquiv e ∈ Set.range (fun n : ℕ => I.edgeEquiv ((D).betaL.edge n)) ↔
      e ∈ Set.range (D).betaL.edge := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, I.edgeEquiv.injective hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, congrArg I.edgeEquiv hn⟩
  constructor
  · rintro ⟨hedge, hm, ha, hb⟩
    refine ⟨he', (uibotCut_edge_in_representative W H h hpast hp A I e).mp hedge,
      ?_, ht.symm.trans (congrArg I.vertexEquiv ha),
      hh.symm.trans (congrArg I.vertexEquiv hb)⟩
    exact fun hn => hm ((futureMap_missing_iff_betaL D h (fun _ _ => hp _) hedge).mpr
      (hr.mp hn))
  · rintro ⟨_, hedge, hm, ha, hb⟩
    have hed := (uibotCut_edge_in_representative W H h hpast hp A I e).mpr hedge
    refine ⟨hed, ?_, I.vertexEquiv.injective (ht.trans ha),
      I.vertexEquiv.injective (hh.trans hb)⟩
    exact fun hn => hm (hr.mpr
      ((futureMap_missing_iff_betaL D h (fun _ _ => hp _) hed).mp hn))

/-- Helper toward Proposition 3.9: retained vertices, including the whole
seam, transport to the same closed upper-side image as the geometric edges. -/
theorem uibotCut_vertex_in_representative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (v : WholePlaneVertex W) :
    v ∈ m0CutLeftVertices W H (D).seam ↔
      A.map.pos (I.vertexEquiv v) ∈ I.h '' {z : ℂ | f z.re ≤ z.im} := by
  rw [← I.pos_map]
  rw [I.h.injective.mem_set_image]
  exact futureMap_left_vertex_iff_above W H D h (fun _ _ => hp _) hpast v

/-- Helper toward Proposition 3.9: the image of the source seam is the
complete geometric interface in every representative, including lower-chain
edges whose orientation is deleted in the cut. -/
theorem uibotCut_seam_trace_in_representative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root) :
    intrinsicFutureSeamTrace A (fun e => (D).seam (I.edgeEquiv.symm e)) =
      I.h '' {z : ℂ | z.im = f z.re} := by
  let S := uibotWholePlaneSourceDomain W H G hp
  refine (intrinsicFuture_seam_trace_map (A := S) (B := A) I (D).seam).trans ?_
  apply congrArg (fun T : Set ℂ => I.h '' T)
  rw [← futureMap_interface_trace_eq_graph W H D h (fun _ _ => hp _) hpast]
  ext z
  constructor
  · rintro ⟨e, he, hz⟩
    refine ⟨(e, false), he, ?_⟩
    exact ((G).toPlaneGraphDrawing_arc_range (e, false)) ▸ hz
  · rintro ⟨⟨e, b⟩, he, hz⟩
    refine ⟨e, he, ?_⟩
    have hz0 : z ∈ ((G).arc (e, false)).image := by
      cases b
      · exact hz
      · have hf := (G).arc_image_flip (e, false)
        exact hf ▸ hz
    exact ((G).toPlaneGraphDrawing_arc_range (e, false)).symm ▸ hz0

/-- Helper toward Proposition 3.9: every source internal face has a
canonical image in an arbitrary representative, with its entire open region
transported by the same plane homeomorphism. -/
@[expose] def uibotCutFaceInRepresentative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (q : FutureMapInternalFaceOrbit W H) : A.map.toPlaneGraphDrawing.Face :=
  I.faceEquiv ((uibotWholePlaneSourceIso W H G hp).symm.faceEquiv
    ((G).toPlaneGraphDrawingFaceEquiv.symm (futureMapInternalGluedFace W H h hpast q)))

/-- Helper toward Proposition 3.9: the transported internal face keeps
exactly the homeomorphic image of the source complementary component. -/
theorem uibotCutFaceInRepresentative_val
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (q : FutureMapInternalFaceOrbit W H) :
    (uibotCutFaceInRepresentative W H h hpast hp A I q).val =
      I.h '' (futureMapInternalGluedFace W H h hpast q).val := by
  change I.h '' (id '' (futureMapInternalGluedFace W H h hpast q).val) = _
  rw [Set.image_id]

/-- Helper toward Proposition 3.9: the transported source internal faces
are exactly the representative's faces contained in the transported strict
upper side. No face-equality assumption is used. -/
theorem uibotCut_face_in_representative
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (F : A.map.toPlaneGraphDrawing.Face) :
    (∃ q, uibotCutFaceInRepresentative W H h hpast hp A I q = F) ↔
      F.val ⊆ I.h '' {z : ℂ | f z.re < z.im} := by
  let E := ((G).toPlaneGraphDrawingFaceEquiv.symm.trans
    (uibotWholePlaneSourceIso W H G hp).symm.faceEquiv).trans I.faceEquiv
  have hv (F0 : (G).Face) : (E F0).val = I.h '' F0.val := by
    change I.h '' (id '' F0.val) = _
    rw [Set.image_id]
  obtain ⟨F0, rfl⟩ := E.surjective F
  rw [hv, Set.image_subset_image_iff I.h.injective]
  change (∃ q, E (futureMapInternalGluedFace W H h hpast q) = E F0) ↔ _
  simp only [E.injective.eq_iff]
  exact futureMap_internal_glued_face_range W H h hpast F0

end Source

/- REMAINING TARGETS — signatures only, not declarations or assumptions.

1. The unresolved source-side identification is precisely:

  ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let D := m0CutData W H h (fun _ _ => hp _)
    intrinsicFutureOpenLeft (uibotWholePlaneSourceDomain W H G hp) D.seam =
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im}

The inspected FutureMapFaces provider characterizes the strict upper region
but does not identify it with the winding-positive complementary component.
GeneralPlaneMapOrientedSideTransport transports an already established
LeftAtOn test. The proofs above do not supply the missing source test or its
converse. It has NOT been added as a theorem premise.

2. Full deterministic source satisfaction and arbitrary-representative
identification still require the following single statement (all data, not
only the selected edges). The raw KMSW incidence bit is first converted to
the source drawing's stored bit, then transported with I's storage flip:

  ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let D := m0CutData W H h (fun _ _ => hp _)
    ∀ (A : D39DomainRootedMap.{0})
      (I : D39GeomRootedMapIsoV2
        (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root),
    let J : WholePlaneDart W → A.E × Bool := fun d =>
      (I.edgeEquiv d.1, Bool.xor
        (Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2))
        (I.edgeFlip d.1))
    ∃ C : IntrinsicFutureCut A,
      C.vertices = I.vertexEquiv '' m0CutLeftVertices W H D.seam ∧
      C.edges = I.edgeEquiv '' D.edges ∧
      C.faces = Set.range (uibotCutFaceInRepresentative W H h hpast hp A I) ∧
      (∀ e, C.seam (I.edgeEquiv e) ↔ D.seam e) ∧
      (∀ e, C.missing (I.edgeEquiv e) ↔ D.missing e) ∧
      (∀ d, C.tail (J d) ↔ d ∈ D.darts ∧ D.tail d) ∧
      (∀ d a, C.rotation (J d) (J a) ↔ D.IsRot d a) ∧
      (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
      (∀ n, C.betaRVertex n = I.vertexEquiv (D.betaR.vertex n) ∧
        C.betaLVertex n = I.vertexEquiv (D.betaL.vertex n) ∧
        C.betaREdge n = I.edgeEquiv (D.betaR.edge n) ∧
        C.betaLEdge n = I.edgeEquiv (D.betaL.edge n))

The identity isomorphism specializes this target to source satisfaction.
Composing this target with uibotIntrinsicCut_sample_realization is the
remaining iid assertion: the SAME event and witnesses must work for EVERY
representative of the sampled class. No such IntrinsicFutureCut-valued iid
assertion is proved in this file.

3. Full intrinsic pushforward remains to be assembled. The proved side,
selector, rotation, incidence and carrier lemmas above do not yet constitute:

  ∀ (A B : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicFutureCut A),
    ∃ C' : IntrinsicFutureCut B,
      C'.vertices = I.vertexEquiv '' C.vertices ∧
      C'.edges = I.edgeEquiv '' C.edges ∧
      C'.faces = I.faceEquiv '' C.faces ∧
      (∀ e, C'.seam (I.edgeEquiv e) ↔ C.seam e) ∧
      (∀ e, C'.missing (I.edgeEquiv e) ↔ C.missing e) ∧
      (∀ d, C'.tail (intrinsicFutureDartEquiv I d) ↔ C.tail d) ∧
      (∀ d a, C'.rotation (intrinsicFutureDartEquiv I d)
        (intrinsicFutureDartEquiv I a) ↔ C.rotation d a) ∧
      (∀ k, C'.x k = I.vertexEquiv (C.x k)) ∧
      (∀ n, C'.betaRVertex n = I.vertexEquiv (C.betaRVertex n) ∧
        C'.betaLVertex n = I.vertexEquiv (C.betaLVertex n) ∧
        C'.betaREdge n = I.edgeEquiv (C.betaREdge n) ∧
        C'.betaLEdge n = I.edgeEquiv (C.betaLEdge n))

In particular, acyclicity and ambient face-degree transport must accompany
the constructor; no face-degree or acyclicity premise may be added.

4. Uniqueness is open on the source realization class. It is not asserted
on all D39DomainRootedMap objects, whose ambient orientations need not be
bipolar. The exact source-domain target is:

  ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ (A : D39DomainRootedMap.{0})
      (I : D39GeomRootedMapIsoV2
        (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root)
      (C C' : IntrinsicFutureCut A), C = C'

files contain no placeholders, and no choice-defined intrinsic cut is made. -/

end DirectedDistances.PaperProofs.Section3
end
