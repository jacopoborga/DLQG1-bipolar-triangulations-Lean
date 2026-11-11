/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart6
import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect7

/-! # Uniqueness of the intrinsic future cut on sampled representatives

are identified with the code selectors before using their uniqueness. All
geometric data remain in the ambient representative's own carriers.
qualification-removal or paper-completion claim. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1
open MeasureTheory Filter

local instance uibotIntrinsicCutPart7DartDecidableEq (A : D39DomainRootedMap.{0}) :
    DecidableEq (A.E × Bool) := Classical.decEq _

local instance uibotIntrinsicCutPart7EdgeDecidableEq (W : ℤ → Fin 3) :
    DecidableEq (WholePlaneEdge W) := Classical.decEq _

local instance uibotIntrinsicCutPart7CodeDartDecidableEq (W : ℤ → Fin 3) :
    DecidableEq (WholePlaneDart W) := Classical.decEq _

section Source
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "E" => uibotCut2SourceDartEquiv W H h hpast hp
local notation "D" => m0CutData W H h (fun _ _ => hp _)
local notation "seamHeight" => seamFun (shiftedStream W 0) h ((And.left H) 0)
local notation "P" => monotoneFamilyDrawing (shiftedStream W 0) ((And.left H) 0)
  (monotone_family_all (shiftedStream W 0))

/-- Helper toward Proposition 3.9: the ambient geometric rotation on the
source drawing determines the inverse code rotation, with every incidence
present. -/
theorem uibotCut2_source_rotation_inverse (d a : WholePlaneDart W)
    (hr : intrinsicFutureRotation S Set.univ (E d) (E a)) :
    a = (wholePlaneRotation W H).symm d := by
  have hf := uibotCut2SourceDartEquiv_rotation W H h hpast hp a
  have hc : d39GeomRootVertex (S).map (E (wholePlaneRotation W H a)) =
      d39GeomRootVertex (S).map (E d) :=
    hf.2.2.1.symm.trans hr.2.2.1
  have ht := hf.2.2.2
  change D39TopologicalCcwSuccessor
    {q : (S).E × Bool | q.1 ∈ (Set.univ : Set (S).E) ∧
      d39GeomRootVertex (S).map q =
        d39GeomRootVertex (S).map (E (wholePlaneRotation W H a))}
    (fun q t => intrinsicFutureDartArc S q t)
    (E a) (E (wholePlaneRotation W H a)) at ht
  rw [hc] at ht
  have he := (E).injective
    (DirectedDistances.PaperProofs.Section5.d39TopologicalCcwSuccessor_unique hr.2.2.2 ht)
  exact ((wholePlaneRotation W H).symm_apply_apply a).symm.trans
    (congrArg (wholePlaneRotation W H).symm he.symm)

/-- Helper toward Proposition 3.9: an intrinsic rightmost outgoing edge
in the source drawing is the code's rightmost outgoing edge. -/
theorem uibotCut2_source_rightmost_of_intrinsic (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) (he : intrinsicFutureRightmostOutgoingAt S v e) :
    wholePlaneRightmostOutgoingAt W H v e := by
  obtain ⟨b, hb, hv, a, hr, ha⟩ := he
  let d := (E).symm (e, b)
  let a₀ := (E).symm a
  have htail : wholePlaneDartTail W d :=
    (uibotCut2SourceDartEquiv_tail W H h hpast hp d).mp
      (by simpa only [d, Equiv.apply_symm_apply] using hb)
  have hd : d = (e, false) := by
    apply Prod.ext
    · rfl
    · cases hb' : d.2 <;> simp_all only [wholePlaneDartTail, Bool.false_eq_true,
        not_false_eq_true, not_true_eq_false, false_and]
  have hE : E (e, false) = (e, b) := by
    rw [← hd]
    exact (E).apply_symm_apply (e, b)
  have hat : wholePlaneDartTail W (wholePlaneDartFlip W a₀) := by
    apply (uibotCut2SourceDartEquiv_tail W H h hpast hp _).mp
    rw [uibotCut2SourceDartEquiv_flip]
    simpa only [a₀, Equiv.apply_symm_apply] using ha
  have haBit : a₀.2 = true := by
    change ¬ (!a₀.2) = true ∧ _ at hat
    cases hbit : a₀.2 <;> simp_all only [Bool.not_false, Bool.not_true,
      not_true_eq_false, false_and]
  have hset : {edge : (S).E | ¬ (S).map.missing edge} = Set.univ := by
    ext edge
    exact iff_true_intro (uibotWholePlaneSourceMap_noMissing W H G hp edge)
  have hrot : intrinsicFutureRotation S Set.univ (E (e, false)) (E a₀) := by
    rw [hE, show E a₀ = a from (E).apply_symm_apply a, ← hset]
    exact hr
  have hai := uibotCut2_source_rotation_inverse W H h hpast hp _ _ hrot
  refine ⟨hp e, ?_, 1, by decide, ?_, hp _, ?_⟩
  · exact (uibotCut2SourceDartEquiv_vertex W H h hpast hp (e, false)).symm.trans
      (by rw [hE]; exact hv)
  · simpa only [pow_one, ← hai] using haBit
  · intro j hj hj1
    omega

/-- Helper toward Proposition 3.9: an intrinsic leftmost incoming edge
in the source drawing is the code's leftmost incoming edge. -/
theorem uibotCut2_source_leftmost_of_intrinsic (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) (he : intrinsicFutureLeftmostIncomingAt S v e) :
    wholePlaneLeftmostIncomingAt W H v e := by
  obtain ⟨b, hb, hv, a, hr, ha⟩ := he
  let d := (E).symm (e, b)
  let a₀ := (E).symm a
  have htail : wholePlaneDartTail W (wholePlaneDartFlip W d) := by
    apply (uibotCut2SourceDartEquiv_tail W H h hpast hp _).mp
    rw [uibotCut2SourceDartEquiv_flip]
    simpa only [d, Equiv.apply_symm_apply] using hb
  have hd : d = (e, true) := by
    apply Prod.ext
    · rfl
    · change ¬ (!d.2) = true ∧ _ at htail
      cases hb' : d.2 <;> simp_all only [Bool.not_false, Bool.not_true,
        not_true_eq_false, false_and]
  have hE : E (e, true) = (e, b) := by
    rw [← hd]
    exact (E).apply_symm_apply (e, b)
  have hat : wholePlaneDartTail W a₀ :=
    (uibotCut2SourceDartEquiv_tail W H h hpast hp a₀).mp
      (by simpa only [a₀, Equiv.apply_symm_apply] using ha)
  have haBit : a₀.2 = false := by
    cases hbit : a₀.2 <;> simp_all only [wholePlaneDartTail, Bool.false_eq_true,
      not_false_eq_true, not_true_eq_false, false_and]
  have hset : {edge : (S).E | ¬ (S).map.missing edge} = Set.univ := by
    ext edge
    exact iff_true_intro (uibotWholePlaneSourceMap_noMissing W H G hp edge)
  have hrot : intrinsicFutureRotation S Set.univ (E (e, true)) (E a₀) := by
    rw [hE, show E a₀ = a from (E).apply_symm_apply a, ← hset]
    exact hr
  have hai := uibotCut2_source_rotation_inverse W H h hpast hp _ _ hrot
  refine ⟨hp e, ?_, 1, by decide, ?_, hp _, ?_⟩
  · exact (uibotCut2SourceDartEquiv_vertex W H h hpast hp (e, true)).symm.trans
      (by rw [hE]; exact hv)
  · simpa only [pow_one, ← hai] using haBit
  · intro j hj hj1
    omega

/-- Helper toward Proposition 3.9: winding-left tests on any planar
region agree between source geometric darts and their chronological arcs. -/
theorem uibotCut2_source_leftAtOn_iff (d : WholePlaneDart W) (F : Set ℂ) :
    (∀ s, LeftAtOn F (intrinsicFutureDartArc S (E d)) s) ↔
      ∀ s, LeftAtOn F ((G).arc d).toPath s := by
  obtain ⟨φ, hφ, harc⟩ := uibotCut2SourceDartEquiv_arc_param W H h hpast hp d
  have hend := d39StrictMonoIntervalEndpoints φ hφ
  calc
    (∀ s, LeftAtOn F (intrinsicFutureDartArc S (E d)) s) ↔
        ∀ s, LeftAtOn F
          (((G).arc d).toPath.reparam φ φ.continuous hend.1 hend.2) s := by
      apply forall_congr'
      intro s
      exact leftAtOn_congr_fun _ _ _ s harc
    _ ↔ ∀ s, LeftAtOn F ((G).arc d).toPath s :=
      forall_leftAtOn_reparam_iff _ _ φ hend.1 hend.2

/-- Helper toward Proposition 3.9: intrinsic winding-left incidence on
the source drawing is exactly geometric dart bordering, in both directions. -/
theorem uibotCut2_source_face_side_iff (d : WholePlaneDart W) (F : (G).Face) :
    (∀ s, LeftAtOn F.val (intrinsicFutureDartArc S (E d)) s) ↔
      (G).dartBorders d F := by
  rw [uibotCut2_source_leftAtOn_iff]
  have hvert := uibhbot_faceOrbit_dartVertex_surjective W H
  exact ⟨DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective
    G hvert d F, fun hb s => (G).dartBorders_toPath_leftAtOn hvert d F hb s⟩

variable (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)

include h hpast I

/-- Helper toward Proposition 3.9: rightmost outgoing edges are unique
in every geometric representative of the source map. -/
theorem uibotCut2_rightmost_unique (v : A.V) {e f : A.E}
    (he : intrinsicFutureRightmostOutgoingAt A v e)
    (hf : intrinsicFutureRightmostOutgoingAt A v f) : e = f := by
  apply I.edgeEquiv.symm.injective
  exact wholePlaneRightmostOutgoingAt_unique W H (I.vertexEquiv.symm v)
    (uibotCut2_source_rightmost_of_intrinsic W H h hpast hp _ _
      (intrinsicFutureRightmostOutgoingAt_map (A := A) (B := S) I.symm v e he))
    (uibotCut2_source_rightmost_of_intrinsic W H h hpast hp _ _
      (intrinsicFutureRightmostOutgoingAt_map (A := A) (B := S) I.symm v f hf))

/-- Helper toward Proposition 3.9: leftmost incoming edges are unique
in every geometric representative of the source map. -/
theorem uibotCut2_leftmost_unique (v : A.V) {e f : A.E}
    (he : intrinsicFutureLeftmostIncomingAt A v e)
    (hf : intrinsicFutureLeftmostIncomingAt A v f) : e = f := by
  apply I.edgeEquiv.symm.injective
  exact wholePlaneLeftmostIncomingAt_unique W H (I.vertexEquiv.symm v)
    (uibotCut2_source_leftmost_of_intrinsic W H h hpast hp _ _
      (intrinsicFutureLeftmostIncomingAt_map (A := A) (B := S) I.symm v e he))
    (uibotCut2_source_leftmost_of_intrinsic W H h hpast hp _ _
      (intrinsicFutureLeftmostIncomingAt_map (A := A) (B := S) I.symm v f hf))

/-- Helper toward Proposition 3.9: every intrinsic cut has the same
extremal rays, including the actual edge identities and all ray vertices. -/
theorem uibotCut2_rays_unique (C C' : IntrinsicFutureCut2 A) :
    (∀ n, C.betaRVertex n = C'.betaRVertex n ∧ C.betaREdge n = C'.betaREdge n) ∧
    (∀ n, C.betaLVertex n = C'.betaLVertex n ∧ C.betaLEdge n = C'.betaLEdge n) := by
  constructor
  · intro n
    induction n with
    | zero =>
      have hv : C.betaRVertex 0 = C'.betaRVertex 0 :=
        C.betaR_start.trans (C.root_terminal.trans
          (C'.root_terminal.symm.trans C'.betaR_start.symm))
      refine ⟨hv, uibotCut2_rightmost_unique W H h hpast hp A I _
        (C.betaR_extremal 0) ?_⟩
      rw [hv]
      exact C'.betaR_extremal 0
    | succ n ih =>
      obtain ⟨he, _, hh⟩ := C.betaR_step n
      obtain ⟨he', _, hh'⟩ := C'.betaR_step n
      have hv : C.betaRVertex (n + 1) = C'.betaRVertex (n + 1) := by
        rw [← hh, ← hh']
        congr 1
        exact Subtype.ext ih.2
      refine ⟨hv, uibotCut2_rightmost_unique W H h hpast hp A I _
        (C.betaR_extremal (n + 1)) ?_⟩
      rw [hv]
      exact C'.betaR_extremal (n + 1)
  · intro n
    induction n with
    | zero =>
      have hv : C.betaLVertex 0 = C'.betaLVertex 0 :=
        C.betaL_start.trans (C.root_initial.trans
          (C'.root_initial.symm.trans C'.betaL_start.symm))
      refine ⟨hv, uibotCut2_leftmost_unique W H h hpast hp A I _
        (C.betaL_extremal 0) ?_⟩
      rw [hv]
      exact C'.betaL_extremal 0
    | succ n ih =>
      obtain ⟨he, _, hh⟩ := C.betaL_step n
      obtain ⟨he', _, hh'⟩ := C'.betaL_step n
      have hv : C.betaLVertex (n + 1) = C'.betaLVertex (n + 1) := by
        rw [← hh, ← hh']
        congr 1
        exact Subtype.ext ih.2
      refine ⟨hv, uibotCut2_leftmost_unique W H h hpast hp A I _
        (C.betaL_extremal (n + 1)) ?_⟩
      rw [hv]
      exact C'.betaL_extremal (n + 1)

/-- Helper toward Proposition 3.9: all intrinsically characterized cuts
on a source representative are equal. The geometric side, all carriers,
missingness, orientation and restricted rotation follow from the unique rays. -/
theorem uibotCut2_unique (C C' : IntrinsicFutureCut2 A) : C = C' := by
  obtain ⟨hR, hL⟩ := uibotCut2_rays_unique W H h hpast hp A I C C'
  have hRV : C.betaRVertex = C'.betaRVertex := funext (fun n => (hR n).1)
  have hRE : C.betaREdge = C'.betaREdge := funext (fun n => (hR n).2)
  have hLV : C.betaLVertex = C'.betaLVertex := funext (fun n => (hL n).1)
  have hLE : C.betaLEdge = C'.betaLEdge := funext (fun n => (hL n).2)
  have hx : C.x = C'.x := by
    funext k
    cases k with
    | ofNat n =>
      cases n with
      | zero => exact C.root_initial.trans C'.root_initial.symm
      | succ n =>
        change C.x ((n : ℤ) + 1) = C'.x ((n : ℤ) + 1)
        rw [C.x_right, C'.x_right, hRV]
    | negSucc n =>
      change C.x (-((n + 1 : ℕ) : ℤ)) = C'.x (-((n + 1 : ℕ) : ℤ))
      rw [C.x_left, C'.x_left, hLV]
  have hs : C.seam = C'.seam := by
    funext e
    apply propext
    rw [C.seam_iff, C'.seam_iff, hRE, hLE]
  have hv : C.vertices = C'.vertices := by
    ext v
    rw [C.vertices_iff, C'.vertices_iff, hs]
  have he : C.edges = C'.edges := by
    ext e
    rw [C.edges_iff, C'.edges_iff, hs]
  have hF : C.faces = C'.faces := by
    ext F
    rw [C.faces_iff, C'.faces_iff, hs]
  have hm : C.missing = C'.missing := by
    funext e
    apply propext
    rw [C.missing_iff, C'.missing_iff, hLE]
  have ht : C.tail = C'.tail := by
    funext d
    apply propext
    rw [C.tail_iff, C'.tail_iff, he, hm]
  have hr : C.rotation = C'.rotation := by
    funext d a
    apply propext
    rw [C.rotation_iff, C'.rotation_iff, he]
  cases C
  cases C'
  congr

/-- Helper toward Proposition 3.9: the actual open internal faces are
not identified with one another by transport to a representative. -/
theorem uibotCut2_internal_face_injective :
    Function.Injective (uibotCutFaceInRepresentative W H h hpast hp A I) := by
  intro q r hqr
  apply futureMap_internal_glued_face_injective W H h hpast
  apply (G).toPlaneGraphDrawingFaceEquiv.symm.injective
  apply (uibotWholePlaneSourceIso W H G hp).symm.faceEquiv.injective
  exact I.faceEquiv.injective hqr

/-- Helper toward Proposition 3.9: every ambient dart borders a transported
internal face exactly when its own geometric arc has that face on its left. -/
theorem uibotCut2_representative_face_side_iff (d : WholePlaneDart W)
    (q : FutureMapInternalFaceOrbit W H) :
    (∀ s, LeftAtOn (uibotCutFaceInRepresentative W H h hpast hp A I q).val
      (intrinsicFutureDartArc A (intrinsicFutureDartEquiv (A := S) I (E d))) s) ↔
      (G).dartBorders d (futureMapInternalGluedFace W H h hpast q) := by
  rw [uibotCutFaceInRepresentative_val]
  exact (intrinsicFuture_leftAtOn_map (A := S) (B := A) I
    (futureMapInternalGluedFace W H h hpast q).val (E d)).symm.trans
    (uibotCut2_source_face_side_iff W H h hpast hp d _)

/-- Helper toward Proposition 3.9: the anchor's internal face-orbit
incidence is expressed using only the representative's geometric arcs and
actual open faces on the left side of those arcs. -/
theorem uibotCut2_internal_face_incidence (d : ℕ × Bool)
    (q : FutureMapInternalFaceOrbit W H) :
    (∀ s, LeftAtOn (uibotCutFaceInRepresentative W H h hpast hp A I q).val
      (intrinsicFutureDartArc A
        (intrinsicFutureDartEquiv (A := S) I (E (wholePlaneDartι W 0 d)))) s) ↔
      Quotient.mk _ d = q.val :=
  (uibotCut2_representative_face_side_iff W H h hpast hp A I _ q).trans
    (futureMap_internal_glued_border_iff W H h hpast d q)

/-- Helper toward Proposition 3.9: the complete bordering dart set of
each actual internal face is a transported creation triangle, with exactly
three distinct darts. All parallel edge identities are retained. -/
theorem uibotCut2_internal_face_triangle (q : FutureMapInternalFaceOrbit W H) :
    let J := (E).trans (intrinsicFutureDartEquiv (A := S) (B := A) I)
    ∃ j : TriangleCreationTime (shiftedStream W 0),
      {a | ∀ s, LeftAtOn (uibotCutFaceInRepresentative W H h hpast hp A I q).val
        (intrinsicFutureDartArc A a) s} =
        J '' (wholePlaneDartι W 0 ''
          {d | d ∈ stageTriangleDartList (shiftedStream W 0) j}) ∧
      ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image
        (fun d => J (wholePlaneDartι W 0 d))).card = 3 := by
  intro J
  obtain ⟨j, hj, hcard⟩ := futureMap_internal_glued_triangle W H h hpast q
  refine ⟨j, ?_, ?_⟩
  · ext a
    obtain ⟨a, rfl⟩ := J.surjective a
    rw [J.injective.mem_set_image]
    exact (uibotCut2_representative_face_side_iff W H h hpast hp A I a q).trans
      (Set.ext_iff.mp hj a)
  · have hi := (futureMap_dart_coordinates W H D h (fun _ _ => hp _)).1
    rw [Finset.card_image_of_injective _ hi] at hcard
    erw [Finset.card_image_of_injective _ (J.injective.comp hi)]
    exact hcard

/-- Helper toward Proposition 3.9: the closed intrinsic future region
is the homeomorphic image of the closed code-side region, for every cut. -/
theorem uibotCut2_closedLeft_image (C : IntrinsicFutureCut2 A) :
    closure (intrinsicFutureOpenLeft A C.seam) =
      I.h '' {z : ℂ | seamHeight z.re ≤ z.im} := by
  rw [uibotCut2_unique W H h hpast hp A I C
    (intrinsicFutureCut2Pushforward (A := S) (B := A) I (uibotCut2Source W H h hpast hp))]
  change closure (intrinsicFutureOpenLeft A (fun e => (D).seam (I.edgeEquiv.symm e))) = _
  erw [intrinsicFuture_closedLeft_map (A := S) (B := A) I,
    uibotCut2_source_closedLeft_eq_upper W H h hpast hp]

/-- Helper toward Proposition 3.9: the geometric exterior of the cut
is specified in the representative's own plane, as the complement of its
closed future region. It is exactly the image of the code-side lower region. -/
theorem uibotCut2_exterior_image (C : IntrinsicFutureCut2 A) :
    (closure (intrinsicFutureOpenLeft A C.seam))ᶜ =
      I.h '' {z : ℂ | z.im < seamHeight z.re} := by
  ext z
  obtain ⟨z, rfl⟩ := I.h.surjective z
  rw [Set.mem_compl_iff, uibotCut2_closedLeft_image W H h hpast hp A I C,
    I.h.injective.mem_set_image, I.h.injective.mem_set_image]
  exact not_le (α := ℝ)

/-- Helper toward Proposition 3.9: the exterior-border clause of the
anchor holds intrinsically, using the cut's own exterior region and actual
geometric dart arcs, including the missing left boundary edges. -/
theorem uibotCut2_exterior_incidence (C : IntrinsicFutureCut2 A) (d : ℕ × Bool) :
    (∀ s, LeftAtOn (closure (intrinsicFutureOpenLeft A C.seam))ᶜ
      (intrinsicFutureDartArc A
        (intrinsicFutureDartEquiv (A := S) I (E (wholePlaneDartι W 0 d)))) s) ↔
      d.2 = true ∧ C.seam (I.edgeEquiv (wholePlaneEdgeι W 0 d.1)) := by
  have hs (e : WholePlaneEdge W) : C.seam (I.edgeEquiv e) ↔ (D).seam e := by
    obtain ⟨C', _, _, _, hs, _⟩ := uibotCut2_in_representative W H h hpast hp A I
    rw [uibotCut2_unique W H h hpast hp A I C C']
    exact hs e
  rw [hs, uibotCut2_exterior_image W H h hpast hp A I C,
    ← intrinsicFuture_leftAtOn_map (A := S) (B := A) I]
  erw [
    uibotCut2_source_leftAtOn_iff W H h hpast hp,
    WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
  let F := futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)
  have hF : F.val = {z : ℂ | z.im < seamHeight z.re} :=
    (unbounded_face_eq_lower (shiftedStream W 0) h (H.1 0) F).mp
      ((futureMap_orbit_face_unbounded_iff W H h _).mpr rfl)
  rw [← hF]
  have hvert := kmswLimitDartVertex_surjective (shiftedStream W 0) (H.1 0)
  have hb : (∀ s, LeftAtOn F.val ((P).arc d).toPath s) ↔ (P).dartBorders d F :=
    ⟨DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective
      P hvert d F, fun hh s => (P).dartBorders_toPath_leftAtOn hvert d F hh s⟩
  exact hb.trans (futureMap_exterior_border_iff_seam W H D h (fun _ _ => hp _) d)

/-- Helper toward Proposition 3.9: the run-zero coordinates enumerate
exactly the intrinsic cut vertices, edges and geometric darts, injectively. -/
theorem uibotCut2_coordinates (C : IntrinsicFutureCut2 A) :
    let V := fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)
    let Q := fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)
    let J := fun d => intrinsicFutureDartEquiv (A := S) I (E (wholePlaneDartι W 0 d))
    Function.Injective V ∧ Set.range V = C.vertices ∧
    Function.Injective Q ∧ Set.range Q = C.edges ∧
    Function.Injective J ∧ Set.range J = {d : A.E × Bool | d.1 ∈ C.edges} ∧
    (∀ k, C.x k = V (boundaryVertex (shiftedStream W 0) h k)) ∧
    (∀ d, J (futureMapEdgeInv d) = ((J d).1, !(J d).2)) ∧
    (∀ d, d39GeomRootVertex A.map (J d) = V (kmswLimitDartVertex (shiftedStream W 0) d)) := by
  intro V Q J
  obtain ⟨C', hv, he, _, _, _, _, _, hx, _⟩ :=
    uibotCut2_in_representative W H h hpast hp A I
  have hCC := uibotCut2_unique W H h hpast hp A I C' C
  subst C'
  have hi := (futureMap_dart_coordinates W H D h (fun _ _ => hp _)).1
  refine ⟨I.vertexEquiv.injective.comp (wholePlaneVertexι_injective W 0), ?_,
    I.edgeEquiv.injective.comp (wholePlaneEdgeι_injective W 0), ?_,
    (intrinsicFutureDartEquiv (A := S) I).injective.comp ((E).injective.comp hi),
    ?_, ?_, ?_, ?_⟩
  · rw [hv, m0Cut_leftVertices_eq_runZero W H h (D).seam
      (m0Cut_seamEdge_iff W H h (fun _ _ => hp _))]
    exact Set.range_comp I.vertexEquiv (wholePlaneVertexι W 0)
  · rw [he, (D).edges_eq h (fun _ _ => hp _)]
    exact Set.range_comp I.edgeEquiv (wholePlaneEdgeι W 0)
  · ext a
    obtain ⟨a, rfl⟩ := (intrinsicFutureDartEquiv (A := S) I).surjective a
    obtain ⟨a, rfl⟩ := (E).surjective a
    change (∃ d, J d = intrinsicFutureDartEquiv (A := S) I (E a)) ↔
      I.edgeEquiv a.1 ∈ C.edges
    rw [he, I.edgeEquiv.injective.mem_set_image]
    change (∃ d, J d = intrinsicFutureDartEquiv (A := S) I (E a)) ↔ a ∈ (D).darts
    rw [(D).darts_eq h (fun _ _ => hp _)]
    exact exists_congr fun d =>
      ((intrinsicFutureDartEquiv (A := S) I).injective.eq_iff.trans (E).injective.eq_iff)
  · intro k
    exact (hx k).trans (congrArg I.vertexEquiv ((D).x_eq h (fun _ _ => hp _) k))
  · intro d
    have hf := intrinsicFutureDartEquiv_flip (A := S) (B := A) I (E (wholePlaneDartι W 0 d))
    erw [← uibotCut2SourceDartEquiv_flip W H h hpast hp] at hf
    exact hf
  · intro d
    exact (intrinsicFutureDartEquiv_vertex (A := S) (B := A) I _).trans
      (congrArg I.vertexEquiv ((uibotCut2SourceDartEquiv_vertex W H h hpast hp _).trans
        (wholePlaneDartVertex_ι W 0 d)))

/-- Helper toward Proposition 3.9: cut rotation in the retained dart
coordinates is the inverse run-zero rotation, with no outside starting dart. -/
theorem uibotCut2_rotation_coordinates (C : IntrinsicFutureCut2 A) (d a : ℕ × Bool) :
    let J := fun d => intrinsicFutureDartEquiv (A := S) I (E (wholePlaneDartι W 0 d))
    C.rotation (J d) (J a) ↔ a = (kmswInfRot (shiftedStream W 0) (H.1 0)).symm d := by
  intro J
  obtain ⟨C', _, _, _, _, _, _, hr, _⟩ :=
    uibotCut2_in_representative W H h hpast hp A I
  rw [uibotCut2_unique W H h hpast hp A I C C']
  have hm (q : ℕ × Bool) : wholePlaneDartι W 0 q ∈ (D).darts := by
    rw [(D).darts_eq h (fun _ _ => hp _)]
    exact Set.mem_range_self q
  have hi := (futureMap_dart_coordinates W H D h (fun _ _ => hp _)).1
  exact (hr _ _).trans ((and_iff_right (hm d)).trans
    ((and_iff_right (hm a)).trans
      ((futureMap_rotation_iff D h (fun _ _ => hp _) d _).trans hi.eq_iff)))

/-- Helper toward Proposition 3.9: reversal followed by intrinsic cut
rotation is the anchor's face successor on every retained geometric dart. -/
theorem uibotCut2_face_successor_coordinates (C : IntrinsicFutureCut2 A)
    (d a : ℕ × Bool) :
    let J := fun d => intrinsicFutureDartEquiv (A := S) I (E (wholePlaneDartι W 0 d))
    C.rotation ((J d).1, !(J d).2) (J a) ↔
      a = kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d := by
  intro J
  have hf := (uibotCut2_coordinates W H h hpast hp A I C).2.2.2.2.2.2.2.1 d
  rw [← hf]
  exact uibotCut2_rotation_coordinates W H h hpast hp A I C (futureMapEdgeInv d) a

/-- Helper toward Proposition 3.9: the full intrinsic interface trace,
including all missing geometric edges, is the image of the code seam graph. -/
theorem uibotCut2_seam_trace_image (C : IntrinsicFutureCut2 A) :
    intrinsicFutureSeamTrace A C.seam =
      I.h '' {z : ℂ | z.im = seamHeight z.re} := by
  rw [uibotCut2_unique W H h hpast hp A I C
    (intrinsicFutureCut2Pushforward (A := S) (B := A) I (uibotCut2Source W H h hpast hp))]
  change intrinsicFutureSeamTrace A (fun e => (D).seam (I.edgeEquiv.symm e)) = _
  erw [intrinsicFuture_seam_trace_map (A := S) (B := A) I,
    uibotCut_source_seam_trace_eq_graph W H h hpast hp]

/-- Helper toward Proposition 3.9: the transported chronological boundary
edge has exactly the two consecutive intrinsic integer labels as its ambient
directed endpoints, even when its cut orientation is missing. -/
theorem uibotCut2_boundary_coordinates (C : IntrinsicFutureCut2 A) (k : ℤ) :
    let e := I.edgeEquiv (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k))
    ∃ he : ¬ A.map.missing e,
      A.map.tail ⟨e, he⟩ = C.x k ∧ A.map.head ⟨e, he⟩ = C.x (k + 1) := by
  intro e
  let e₀ := wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)
  have he₀ := uibotWholePlaneSourceMap_noMissing W H G hp e₀
  have hb := (m0Cut_boundaryLabel_consecutive W H h (fun _ _ => hp _) k
    ((D).x_label k) ((D).x_label (k + 1))).2
  have hend := uibotWholePlaneSourceMap_endpoints W H G hp e₀
  obtain ⟨C', _, _, _, _, _, _, _, hx, _⟩ :=
    uibotCut2_in_representative W H h hpast hp A I
  have hCC := uibotCut2_unique W H h hpast hp A I C' C
  subst C'
  refine ⟨fun hm => he₀ ((I.missing_map e₀).mp hm), ?_, ?_⟩
  · exact (intrinsicFuture_tail_map (A := S) (B := A) I ⟨e₀, he₀⟩).symm.trans
      ((congrArg I.vertexEquiv (hend.1.trans hb.1)).trans (hx k).symm)
  · exact (intrinsicFuture_head_map (A := S) (B := A) I ⟨e₀, he₀⟩).symm.trans
      ((congrArg I.vertexEquiv (hend.2.trans hb.2)).trans (hx (k + 1)).symm)

end Source

/-- Helper toward Proposition 3.9: the intrinsic integer boundary labels
are joined consecutively by the actual ambient directed seam edges, including
the edges whose orientation is removed in the cut. -/
theorem uibotCut2_boundary_edges (A : D39DomainRootedMap.{0})
    (C : IntrinsicFutureCut2 A) (k : ℤ) :
    ∃ e : A.E, C.seam e ∧ ∃ he : ¬ A.map.missing e,
      A.map.tail ⟨e, he⟩ = C.x k ∧ A.map.head ⟨e, he⟩ = C.x (k + 1) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      obtain ⟨he, ht, hh⟩ := intrinsicFuture_dart_endpoints_of_tail A A.root C.root_tail
      exact ⟨A.root.1, (C.seam_iff _).mpr (Or.inl rfl), he,
        ht.symm.trans C.root_initial.symm, hh.symm.trans C.root_terminal.symm⟩
    | succ n =>
      obtain ⟨he, ht, hh⟩ := C.betaR_step n
      refine ⟨C.betaREdge n, (C.seam_iff _).mpr
        (Or.inr (Or.inl (Set.mem_range_self n))), he, ?_, ?_⟩
      · exact ht.trans (C.x_right n).symm
      · exact hh.trans (C.x_right (n + 1)).symm
  | negSucc n =>
    obtain ⟨he, hh, ht⟩ := C.betaL_step n
    refine ⟨C.betaLEdge n, (C.seam_iff _).mpr
      (Or.inr (Or.inr (Set.mem_range_self n))), he, ?_, ?_⟩
    · exact ht.trans (C.x_left (n + 1)).symm
    · rw [show Int.negSucc n + 1 = -(n : ℤ) by omega]
      exact hh.trans (C.x_left n).symm

/-- Helper toward Proposition 3.9: on the single iid source event every
representative of the sampled class has exactly one intrinsic future cut.
The same cut is the image of the code cut for every source isomorphism.
This statement concerns sampled classes and makes no reconstruction claim
for the separately specified whole-plane class measure. -/
theorem uibotCut2_sample_unique_realization :
    ∀ᵐ W ∂DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let D := m0CutData W H h (fun _ _ => hp _)
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∃! C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
            (uibotWholePlaneSourceRoot W H G) A.map A.root,
          let J := fun d => intrinsicFutureDartEquiv
            (A := uibotWholePlaneSourceDomain W H G hp) I
            (uibotCut2SourceDartEquiv W H h hpast hp d)
          let V := fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)
          let Q := fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)
          let K := fun d => J (wholePlaneDartι W 0 d)
          let face := uibotCutFaceInRepresentative W H h hpast hp A I
          C.vertices = I.vertexEquiv '' m0CutLeftVertices W H D.seam ∧
          C.edges = I.edgeEquiv '' D.edges ∧
          C.faces = Set.range (uibotCutFaceInRepresentative W H h hpast hp A I) ∧
          (∀ e, C.seam (I.edgeEquiv e) ↔ D.seam e) ∧
          (∀ e, C.missing (I.edgeEquiv e) ↔ D.missing e) ∧
          (∀ d, C.tail (J d) ↔ d ∈ D.darts ∧ D.tail d) ∧
          (∀ d a, C.rotation (J d) (J a) ↔
            d ∈ D.darts ∧ a ∈ D.darts ∧ D.IsRot d a) ∧
          (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
          (∀ n, C.betaRVertex n = I.vertexEquiv (D.betaR.vertex n) ∧
            C.betaLVertex n = I.vertexEquiv (D.betaL.vertex n) ∧
            C.betaREdge n = I.edgeEquiv (D.betaR.edge n) ∧
            C.betaLEdge n = I.edgeEquiv (D.betaL.edge n)) ∧
          (Function.Injective V ∧ Set.range V = C.vertices ∧
            Function.Injective Q ∧ Set.range Q = C.edges ∧
            Function.Injective K ∧ Set.range K = {d : A.E × Bool | d.1 ∈ C.edges} ∧
            (∀ k, C.x k = V (boundaryVertex (shiftedStream W 0) h k)) ∧
            (∀ d, K (futureMapEdgeInv d) = ((K d).1, !(K d).2)) ∧
            (∀ d, d39GeomRootVertex A.map (K d) =
              V (kmswLimitDartVertex (shiftedStream W 0) d))) ∧
          (∀ d a, C.rotation (K d) (K a) ↔
            a = (kmswInfRot (shiftedStream W 0) (H.1 0)).symm d) ∧
          (∀ d a, C.rotation ((K d).1, !(K d).2) (K a) ↔
            a = kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) ∧
          Function.Injective face ∧
          (∀ d q, (∀ s, LeftAtOn (face q).val (intrinsicFutureDartArc A (K d)) s) ↔
            Quotient.mk _ d = q.val) ∧
          (∀ q, ∃ j : TriangleCreationTime (shiftedStream W 0),
            {a | ∀ s, LeftAtOn (face q).val (intrinsicFutureDartArc A a) s} =
              J '' (wholePlaneDartι W 0 ''
                {d | d ∈ stageTriangleDartList (shiftedStream W 0) j}) ∧
            ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image K).card = 3) ∧
          (∀ d, (∀ s, LeftAtOn (closure (intrinsicFutureOpenLeft A C.seam))ᶜ
            (intrinsicFutureDartArc A (K d)) s) ↔
              d.2 = true ∧ C.seam (Q d.1)) ∧
          intrinsicFutureSeamTrace A C.seam =
            I.h '' {z : ℂ | z.im = seamFun (shiftedStream W 0) h (H.1 0) z.re} ∧
          closure (intrinsicFutureOpenLeft A C.seam) =
            I.h '' {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im} ∧
          (∀ k : ℤ, let e := Q (boundaryOuterEdge (shiftedStream W 0) h k)
            ∃ he : ¬ A.map.missing e, A.map.tail ⟨e, he⟩ = C.x k ∧
              A.map.head ⟨e, he⟩ = C.x (k + 1)) := by
  filter_upwards [uibotCut2_sample_realization, uibotRecoveredCode_ae] with U hU hcode
  dsimp only at hU ⊢
  rw [hcode] at hU
  obtain ⟨H, h, hpast, hp, hrep⟩ := hU
  refine ⟨H, h, hpast, hp, ?_⟩
  intro A hA
  obtain ⟨hI, hcut⟩ := hrep A hA
  obtain ⟨I₀⟩ := hI
  obtain ⟨C, _⟩ := hcut I₀
  refine ⟨⟨I₀⟩, C, ⟨fun C' => uibotCut2_unique _ H h hpast hp A I₀ C' C, ?_⟩, ?_⟩
  · intro I
    obtain ⟨C', hC'⟩ := hcut I
    have heq := uibotCut2_unique _ H h hpast hp A I C C'
    subst C'
    obtain ⟨hv, he, hF, hs, hm, ht, hr, hx, hb⟩ := hC'
    exact ⟨hv, he, hF, hs, hm, ht, hr, hx, hb,
      uibotCut2_coordinates _ H h hpast hp A I C,
      uibotCut2_rotation_coordinates _ H h hpast hp A I C,
      uibotCut2_face_successor_coordinates _ H h hpast hp A I C,
      uibotCut2_internal_face_injective _ H h hpast hp A I,
      uibotCut2_internal_face_incidence _ H h hpast hp A I,
      uibotCut2_internal_face_triangle _ H h hpast hp A I,
      uibotCut2_exterior_incidence _ H h hpast hp A I C,
      uibotCut2_seam_trace_image _ H h hpast hp A I C,
      uibotCut2_closedLeft_image _ H h hpast hp A I C,
      uibotCut2_boundary_coordinates _ H h hpast hp A I C⟩
  · intro C' _
    exact uibotCut2_unique _ H h hpast hp A I₀ C' C

/-- Helper toward Proposition 3.9: uniqueness is among all intrinsic
cuts, without imposing a code-image predicate on the competing cut. -/
theorem uibotCut2_sample_existsUnique :
    ∀ᵐ W ∂DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure,
      ∀ A : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W →
        ∃! _C : IntrinsicFutureCut2 A, True := by
  filter_upwards [uibotCut2_sample_unique_realization] with W hW
  dsimp only at hW
  obtain ⟨H, h, hpast, hp, hrep⟩ := hW
  intro A hA
  obtain ⟨_, C, hC, _⟩ := hrep A hA
  exact ⟨C, trivial, fun C' _ => hC.1 C'⟩

end DirectedDistances.PaperProofs.Section3
end
