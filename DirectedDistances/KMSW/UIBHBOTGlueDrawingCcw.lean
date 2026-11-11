/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingRotation
import DirectedDistances.KMSW.WholePlaneRunRotationRestrict
import DirectedDistances.KMSW.StageReversalRotation
import DirectedDistances.KMSW.WholePlaneGlueSeamStar
import DirectedDistances.PlanarMap.CcwSectorMerge
import DirectedDistances.KMSW.OutgoingInterval
import all DirectedDistances.KMSW.RunInfDartPartition
import all DirectedDistances.KMSW.PastFaceSucc
import Mathlib.Tactic.Linarith









public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.PlanarMap Set
open DirectedDistances.PaperProofs.Section5

noncomputable section

/-- A nondegenerate simple polyline has distinct endpoints. -/
private theorem uibhbotCcw_simple_endpoints_ne (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) : p.start ≠ p.finish := by
  intro heq
  have ha : p.start ∈ p.segmentAt 0 := by
    rw [Polyline.segmentAt, Polyline.point_zero_eq_start]
    exact left_mem_segment ℝ _ _
  have hb : p.start ∈ p.segmentAt (p.points.length - 2) := by
    rw [heq, Polyline.segmentAt,
      show p.points.length - 2 + 1 = p.points.length - 1 by omega,
      Polyline.point_last_eq_finish]
    exact right_mem_segment ℝ _ _
  by_cases htwo : p.points.length = 2
  · apply hp.1 0 (by omega)
    rw [Polyline.point_zero_eq_start, heq, ← Polyline.point_last_eq_finish, htwo]
  by_cases hthree : p.points.length = 3
  · have hb' : p.start ∈ p.segmentAt 1 := by simpa only [hthree] using hb
    have hxmem : p.start ∈ ({p.point 1} : Set ℂ) :=
      hp.2.1 0 (by omega) ▸ ⟨ha, hb'⟩
    have hx : p.start = p.point 1 := hxmem
    exact hp.1 0 (by omega) ((Polyline.point_zero_eq_start p).trans hx)
  · exact Set.disjoint_left.mp (hp.2.2 0 (p.points.length - 2)
      (by omega) (by omega) (by omega)) ha hb

/-- Two nonzero initial segments with equal arguments and a common start meet
away from both endpoints of the first polyline. -/
private theorem uibhbotCcw_initial_ray_meets (p q : Polyline)
    (hpl : 2 ≤ p.points.length) (hql : 2 ≤ q.points.length)
    (hp : p.initialDirection ≠ 0) (hq : q.initialDirection ≠ 0)
    (hstart : p.start = q.start)
    (harg : Complex.arg p.initialDirection = Complex.arg q.initialDirection) :
    (p.interior ∩ q.image).Nonempty := by
  let ρ := ‖q.initialDirection‖ / ‖p.initialDirection‖
  have hρ : 0 < ρ := div_pos (norm_pos_iff.mpr hq) (norm_pos_iff.mpr hp)
  have hdir : (ρ : ℂ) * p.initialDirection = q.initialDirection := by
    simpa only [ρ, Complex.ofReal_div] using (Complex.arg_eq_arg_iff hp hq).mp harg
  let z : ℝ → ℂ := fun s => p.start + (s : ℂ) * p.initialDirection
  have himages (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hsρ : s ≤ ρ) :
      z s ∈ p.image ∩ q.image := by
    constructor
    · refine Or.inr ⟨0, by omega, ?_⟩
      rw [Polyline.segmentAt, Polyline.point_zero_eq_start, segment_eq_image']
      exact ⟨s, ⟨hs.le, hs1⟩, by
        dsimp only
        rw [Complex.real_smul]
        rfl⟩
    · refine Or.inr ⟨0, by omega, ?_⟩
      rw [Polyline.segmentAt, Polyline.point_zero_eq_start, segment_eq_image']
      refine ⟨s / ρ, ⟨div_nonneg hs.le hρ.le, (div_le_one hρ).mpr hsρ⟩, ?_⟩
      dsimp only
      rw [Complex.real_smul, ← Polyline.initialDirection, ← hdir,
        ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ s hρ.ne', ← hstart]
  have hne_start (s : ℝ) (hs : 0 < s) : z s ≠ p.start := by
    intro heq
    have hmul : (s : ℂ) * p.initialDirection = 0 :=
      add_left_cancel (a := p.start) (heq.trans (add_zero _).symm)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') hp hmul
  let t := min 1 ρ / 2
  have ht : 0 < t := half_pos (lt_min zero_lt_one hρ)
  have ht1 : t ≤ 1 :=
    (half_le_self (lt_min zero_lt_one hρ).le).trans (min_le_left _ _)
  have htρ : t ≤ ρ :=
    (half_le_self (lt_min zero_lt_one hρ).le).trans (min_le_right _ _)
  have hhalf : t / 2 ≤ t := half_le_self ht.le
  have hdiff : z t ≠ z (t / 2) := by
    intro heq
    have hmul : (t : ℂ) * p.initialDirection = (t / 2 : ℝ) * p.initialDirection :=
      add_left_cancel heq
    have hreal : t = t / 2 :=
      Complex.ofReal_injective (mul_right_cancel₀ hp hmul)
    linarith only [ht, hreal]
  have hmem (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hsρ : s ≤ ρ)
      (hf : z s ≠ p.finish) : z s ∈ p.interior ∩ q.image := by
    obtain ⟨hsp, hsq⟩ := himages s hs hs1 hsρ
    exact ⟨⟨hsp, by
      simpa only [mem_insert_iff, mem_singleton_iff, not_or] using
        And.intro (hne_start s hs) hf⟩, hsq⟩
  by_cases hf : z t = p.finish
  · exact ⟨z (t / 2), hmem (t / 2) (half_pos ht) (hhalf.trans ht1)
      (hhalf.trans htρ) (fun heq => hdiff (hf.trans heq.symm))⟩
  · exact ⟨z t, hmem t ht ht1 htρ hf⟩

/-- The geometric separation clauses force initial argument injectivity. This is
a structural lemma about polylines, with every geometric premise explicit. -/
private theorem uibhbotCcw_initial_arg_injective {D V : Type*}
    (flip : D → D) (vert : D → V) (pos : V → ℂ) (arc : D → Polyline)
    (hsimple : ∀ d, (arc d).IsSimple)
    (hlen : ∀ d, 2 ≤ (arc d).points.length)
    (hstart : ∀ d, (arc d).start = pos (vert d))
    (hfinish : ∀ d, (arc d).finish = pos (vert (flip d)))
    (hdisjoint : ∀ d e, e ≠ d → e ≠ flip d →
      Disjoint (arc d).interior (arc e).interior)
    (havoid : ∀ d v, pos v ∉ (arc d).interior)
    (hdir : ∀ d, (arc d).initialDirection ≠ 0)
    (d e : D) (hv : vert d = vert e)
    (harg : Complex.arg (arc d).initialDirection =
      Complex.arg (arc e).initialDirection) : d = e := by
  by_contra hne
  have hflip : e ≠ flip d := by
    intro heq
    apply uibhbotCcw_simple_endpoints_ne (arc d) (hsimple d) (hlen d)
    rw [hstart, hfinish, ← heq, hv]
  obtain ⟨z, hzd, hze⟩ := uibhbotCcw_initial_ray_meets (arc d) (arc e)
    (hlen d) (hlen e) (hdir d) (hdir e)
    (by rw [hstart, hstart, hv]) harg
  have hzei : z ∈ (arc e).interior := by
    refine ⟨hze, ?_⟩
    intro hend
    rcases hend with he | he
    · apply havoid d (vert e)
      rw [← hstart, ← he]
      exact hzd
    · apply havoid d (vert (flip e))
      rw [← hfinish, ← he]
      exact hzd
  exact Set.disjoint_left.mp (hdisjoint d e (Ne.symm hne) hflip) hzd hzei




theorem uibhbotCodeLawRel_ae_candidate_glue_geometry_initial_arg_injective :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ _H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
        Function.Injective pos ∧
        (∀ D E, E ≠ D → E ≠ wholePlaneDartFlip W D →
          Disjoint (arc D).interior (arc E).interior) ∧
        (∀ D V, pos V ∉ (arc D).interior) ∧
        (∀ D E, wholePlaneDartVertex W D = wholePlaneDartVertex W E →
          Complex.arg (arc D).initialDirection =
            Complex.arg (arc E).initialDirection → D = E) ∧
        (∀ D, (arc D).IsSimple) ∧
        (∀ D, 2 ≤ (arc D).points.length) ∧
        (∀ D, (arc D).start = pos (wholePlaneDartVertex W D)) ∧
        (∀ D, (arc D).finish = pos (wholePlaneDartVertex W (wholePlaneDartFlip W D))) ∧
        (∀ D, arc (wholePlaneDartFlip W D) = (arc D).reverse) ∧
        (∀ D, (arc D).initialDirection ≠ 0) ∧
        (∀ K : Set ℂ, Bornology.IsBounded K →
          {D | (K ∩ (arc D).image).Nonempty}.Finite) ∧
        (∀ k : ℤ, pos (wholePlaneVertexι W 0
          (boundaryVertex (shiftedStream W 0) h0 k)) = ⟨-(k : ℝ), 0⟩) ∧
        (∀ v : ℕ, (pos (wholePlaneVertexι W 0 v)).im ≤ 0) ∧
        (∀ v : ℕ, 0 ≤ (pos (kmswPastVertex W v)).im) ∧
        (∀ k : ℤ, ∀ b : Bool,
          (arc (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, b))).image
            ⊆ {z : ℂ | z.im = 0}) ∧
        (∀ d : ℕ × Bool, ¬ kmswPastSeamEdge W d.1 →
          (arc (kmswPastDart W d)).image ⊆ {z : ℂ | 0 ≤ z.im}) ∧
        ∀ d : ℕ × Bool,
          (arc (wholePlaneDartι W 0 d)).image ⊆ {z : ℂ | z.im ≤ 0} := by
  filter_upwards [uibhbotCodeLawRel_ae_candidate_glue_geometry_avoids_vertices] with W h
  obtain ⟨H, h0, pos, arc, hinj, hdisjoint, havoid, hsimple, hlen, hstart,
    hfinish, hflip, hdir, hlocal, hboundary, hfuture, hpast, hseam, hpastArc,
    hfutureArc⟩ := h
  exact ⟨H, h0, pos, arc, hinj, hdisjoint, havoid,
    uibhbotCcw_initial_arg_injective (wholePlaneDartFlip W) (wholePlaneDartVertex W)
      pos arc hsimple hlen hstart hfinish hdisjoint havoid hdir,
    hsimple, hlen, hstart, hfinish, hflip, hdir, hlocal, hboundary, hfuture,
    hpast, hseam, hpastArc, hfutureArc⟩

/-- An injective relabeling transports the angular successor on its image star. -/
private theorem uibhbotCcw_successor_image {A B : Type*} (i : A → B)
    (hi : Function.Injective i) (S : Set A) (dir : A → ℂ) (dir' : B → ℂ)
    (hdir : ∀ a ∈ S, dir' (i a) = dir a) (d e : A)
    (hs : CcwSuccessor S dir d e) :
    CcwSuccessor (i '' S) dir' (i d) (i e) := by
  obtain ⟨hfin, hd, he, hcase⟩ := hs
  refine ⟨hfin.image i, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · exact Or.inl ⟨congrArg i heq, by rw [hsingle, Set.image_singleton]⟩
  · refine Or.inr ⟨fun h => hne (hi h), ?_⟩
    rintro _ ⟨f, hf, rfl⟩ hfd
    rw [hdir d hd, hdir e he, hdir f hf]
    exact hmin f hf (fun h => hfd (congrArg i h))

/-- The inclusion of a run retains both the edge identity and the dart side. -/
private theorem uibhbotCcw_dart_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneDartι W N) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  change (wholePlaneEdgeι W N e, b) = (wholePlaneEdgeι W N f, c) at h
  exact Prod.ext (wholePlaneEdgeι_injective W N (congrArg Prod.fst h))
    (show b = c from congrArg Prod.snd h)

/-- If a run contains an entire whole-plane vertex star, its rotation already is
the whole-plane rotation there. The first return has length one. -/
private theorem uibhbotCcw_rotation_of_star_in_run (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hstar : ∀ E, wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W N d) →
      E ∈ range (wholePlaneDartι W N)) :
    wholePlaneRotation W H (wholePlaneDartι W N d) =
      wholePlaneDartι W N (kmswInfRot (shiftedStream W N) (H.1 N) d) := by
  let r := kmswInfRot (shiftedStream W N) (H.1 N) d
  obtain ⟨k, hk, heq, hfirst⟩ :=
    wholePlaneRotation_symm_firstReturn_run W H N r
  have hv : wholePlaneDartVertex W (wholePlaneDartι W N r) =
      wholePlaneDartVertex W (wholePlaneDartι W N d) := by
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    exact congrArg (wholePlaneVertexι W N)
      (kmswLimitDartVertex_rot (shiftedStream W N) (H.1 N) d)
  have hinv : wholePlaneDartVertex W
      ((wholePlaneRotation W H).symm (wholePlaneDartι W N r)) =
      wholePlaneDartVertex W (wholePlaneDartι W N d) := by
    have h := wholePlaneRotation_preserves_dartVertex W H
      ((wholePlaneRotation W H).symm (wholePlaneDartι W N r))
    exact h.symm.trans ((congrArg (wholePlaneDartVertex W)
      ((wholePlaneRotation W H).apply_symm_apply (wholePlaneDartι W N r))).trans hv)
  have hk1 : k = 1 := by
    by_contra h
    have hlt : 1 < k := by omega
    have hnot := hfirst 1 zero_lt_one hlt
    simp only [pow_one] at hnot
    exact hnot (hstar _ hinv)
  rw [hk1, pow_one] at heq
  have heq' : (wholePlaneRotation W H).symm (wholePlaneDartι W N r) =
      wholePlaneDartι W N d := by
    simpa only [r, Equiv.symm_apply_apply] using heq
  exact ((wholePlaneRotation W H).symm_apply_eq.mp heq').symm

/-- At a future vertex not shared with the past, the assembled arcs have the
whole-plane angular successor of G4b. This includes unglued boundary vertices
and uses the future component drawing's own rotation agreement. -/
theorem uibhbotCcw_assembly_rotation_future_unshared (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (p : (ℕ × Bool) → Polyline)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (d : ℕ × Bool)
    (hv : wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) d) ∉
      range (kmswPastVertex W)) :
    CcwSuccessor
      {E | wholePlaneDartVertex W E =
        wholePlaneDartVertex W (wholePlaneDartι W 0 d)}
      (fun E => (uibhbotAssemblyArc W p F.arc E).initialDirection)
      (wholePlaneDartι W 0 d) (wholePlaneRotation W H (wholePlaneDartι W 0 d)) := by
  have hstar : {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d)} =
      wholePlaneDartι W 0 ''
        {e | kmswLimitDartVertex (shiftedStream W 0) e =
          kmswLimitDartVertex (shiftedStream W 0) d} := by
    ext E
    change (wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d)) ↔ _
    constructor
    · intro he
      rcases WholePlanePastGlueData.dart_cover W E with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · refine ⟨e, ?_, rfl⟩
        exact wholePlaneVertexι_injective W 0
          ((wholePlaneDartVertex_ι W 0 e).symm.trans
            (he.trans (wholePlaneDartVertex_ι W 0 d)))
      · exact (hv ⟨_, ((WholePlanePastGlueData.pastDart_vertex W e).symm.trans
          (he.trans (wholePlaneDartVertex_ι W 0 d)))⟩).elim
    · rintro ⟨e, he, rfl⟩
      rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, he]
  have hcover : ∀ E, wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d) →
      E ∈ range (wholePlaneDartι W 0) := by
    intro E he
    have hm : E ∈ {E | wholePlaneDartVertex W E =
        wholePlaneDartVertex W (wholePlaneDartι W 0 d)} := he
    rw [hstar] at hm
    obtain ⟨e, _, he⟩ := hm
    exact ⟨e, he⟩
  rw [uibhbotCcw_rotation_of_star_in_run W H 0 d hcover, hstar]
  exact uibhbotCcw_successor_image (wholePlaneDartι W 0)
    (uibhbotCcw_dart_injective W 0) _ _ _
    (fun e _ => congrArg Polyline.initialDirection (uibhbotAssemblyArc_future W p F.arc e))
    d _ (F.rotation_agreement d)

/-- An unshared past vertex has precisely the included past star. -/
private theorem uibhbotCcw_star_past_unshared (W : ℤ → Fin 3) (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∉
      range (wholePlaneVertexι W 0)) :
    {E | wholePlaneDartVertex W E = wholePlaneDartVertex W (kmswPastDart W d)} =
      kmswPastDart W ''
        {e | kmswLimitDartVertex (kmswPastCode W) e =
          kmswLimitDartVertex (kmswPastCode W) d} := by
  ext E
  change (wholePlaneDartVertex W E =
    wholePlaneDartVertex W (kmswPastDart W d)) ↔ _
  constructor
  · intro he
    rcases WholePlanePastGlueData.dart_cover W E with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact (hv ⟨_, (wholePlaneDartVertex_ι W 0 e).symm.trans
        (he.trans (WholePlanePastGlueData.pastDart_vertex W d))⟩).elim
    · refine ⟨e, ?_, rfl⟩
      exact kmswPastVertex_injective W
        ((WholePlanePastGlueData.pastDart_vertex W e).symm.trans
          (he.trans (WholePlanePastGlueData.pastDart_vertex W d)))
  · rintro ⟨e, he, rfl⟩
    rw [WholePlanePastGlueData.pastDart_vertex,
      WholePlanePastGlueData.pastDart_vertex, he]

/-- The finite and infinite dart vertices agree on allocated edges. -/
private theorem uibhbotCcw_stage_vertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d = kmswLimitDartVertex w (reversalDartVal d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;>
    simp only [stageEndpoint, kmswLimitDartVertex, reversalDartVal, hb,
      Bool.false_eq_true, ite_false, ite_true, hw, he]

/-- A complete finite past star at an unshared vertex is already complete in the
corresponding shifted run. This uses finite reversal, including outer darts. -/
private theorem uibhbotCcw_past_complete_run (W : ℤ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) (reversalDartVal d)) ∉
      range (wholePlaneVertexι W 0))
    (hc : kmswVertexComplete (kmswPastCode W) n
      (kmswLimitDartVertex (kmswPastCode W) (reversalDartVal d))) :
    kmswVertexComplete (shiftedStream W n) n
      (stageEndpoint (kmswStage (shiftedStream W n) n)
        (kmswRevDart (shiftedStream W n) (kmswPastCode W) n
          (kmswPastCode_rev W n) d)) := by
  let y := kmswRevDart (shiftedStream W n) (kmswPastCode W) n
    (kmswPastCode_rev W n) d
  have hrep : wholePlaneDartι W n (reversalDartVal y) =
      kmswPastDart W (reversalDartVal d) :=
    (kmswPastDart_eq_stage W n (reversalDartVal d) d.1.isLt).symm
  have hbound (q : ℕ × Bool)
      (hq : kmswLimitDartVertex (shiftedStream W n) q =
        kmswLimitDartVertex (shiftedStream W n) (reversalDartVal y)) :
      q.1 < (kmswStage (shiftedStream W n) n).nextEdge := by
    have hm : wholePlaneDartι W n q ∈
        {E | wholePlaneDartVertex W E =
          wholePlaneDartVertex W (kmswPastDart W (reversalDartVal d))} := by
      change wholePlaneDartVertex W (wholePlaneDartι W n q) = _
      rw [← hrep, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hq]
    rw [uibhbotCcw_star_past_unshared W (reversalDartVal d) hv] at hm
    obtain ⟨e, he, heq⟩ := hm
    change kmswLimitDartVertex (kmswPastCode W) e =
      kmswLimitDartVertex (kmswPastCode W) (reversalDartVal d) at he
    have heb : e.1 < (kmswStage (kmswPastCode W) n).nextEdge := by
      apply hc e.1
      cases hb : e.2 with
      | false => exact Or.inl (by simpa only [kmswLimitDartVertex, hb,
          Bool.false_eq_true, ite_false] using he)
      | true => exact Or.inr (by simpa only [kmswLimitDartVertex, hb, ite_true] using he)
    let x : StageDart (kmswStage (kmswPastCode W) n).nextEdge := (⟨e.1, heb⟩, e.2)
    let z := kmswRevDart (shiftedStream W n) (kmswPastCode W) n
      (kmswPastCode_rev W n) x
    have hz : wholePlaneDartι W n (reversalDartVal z) = wholePlaneDartι W n q :=
      (kmswPastDart_eq_stage W n e heb).symm.trans heq
    have heq' : reversalDartVal z = q := uibhbotCcw_dart_injective W n hz
    exact (congrArg Prod.fst heq') ▸ z.1.isLt
  intro e he
  rw [uibhbotCcw_stage_vertex] at he
  rcases he with hw | ht
  · exact hbound (e, false) hw
  · exact hbound (e, true) ht

/-- The whole-plane rotation retains the past rotation at every unshared past
vertex, including vertices on the unglued past boundary. No past boundary-hit
witness is used. -/
private theorem uibhbotCcw_rotation_past_unshared (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∉
      range (wholePlaneVertexι W 0)) :
    wholePlaneRotation W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfRot (kmswPastCode W) hfin d) := by
  obtain ⟨B, hB⟩ := (hfin (kmswLimitDartVertex (kmswPastCode W) d)).bddAbove
  let n := max B d.1
  have hd : d.1 < (kmswStage (kmswPastCode W) n).nextEdge :=
    (kmsw_edge_allocated_by_self _ d.1).trans_le
      (kmswStage_nextEdge_mono _ (Nat.le_max_right _ _))
  have hc : kmswVertexComplete (kmswPastCode W) n
      (kmswLimitDartVertex (kmswPastCode W) d) := by
    intro e he
    exact (hB ⟨e, kmsw_edge_allocated_by_self _ e, he⟩).trans_lt
      ((kmsw_edge_allocated_by_self _ B).trans_le
        (kmswStage_nextEdge_mono _ (Nat.le_max_left _ _)))
  let x : StageDart (kmswStage (kmswPastCode W) n).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := kmswRevDart (shiftedStream W n) (kmswPastCode W) n
    (kmswPastCode_rev W n) x
  have hrep (e : StageDart (kmswStage (kmswPastCode W) n).nextEdge) :
      wholePlaneDartι W n (reversalDartVal
        (kmswRevDart (shiftedStream W n) (kmswPastCode W) n (kmswPastCode_rev W n) e)) =
      kmswPastDart W (reversalDartVal e) :=
    (kmswPastDart_eq_stage W n (reversalDartVal e) e.1.isLt).symm
  have hcover : ∀ E, wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W n (reversalDartVal y)) →
      E ∈ range (wholePlaneDartι W n) := by
    intro E he
    rw [hrep x] at he
    have hm : E ∈ {E | wholePlaneDartVertex W E =
        wholePlaneDartVertex W (kmswPastDart W d)} := he
    rw [uibhbotCcw_star_past_unshared W d hv] at hm
    obtain ⟨e, heV, heE⟩ := hm
    change kmswLimitDartVertex (kmswPastCode W) e =
      kmswLimitDartVertex (kmswPastCode W) d at heV
    have heb : e.1 < (kmswStage (kmswPastCode W) n).nextEdge := by
      apply hc e.1
      cases hb : e.2 with
      | false => exact Or.inl (by simpa only [kmswLimitDartVertex, hb,
          Bool.false_eq_true, ite_false] using heV)
      | true => exact Or.inr (by simpa only [kmswLimitDartVertex, hb, ite_true] using heV)
    exact ⟨_, (hrep (⟨e.1, heb⟩, e.2)).trans heE⟩
  have hcx : kmswVertexComplete (kmswPastCode W) n
      (stageEndpoint (kmswStage (kmswPastCode W) n) x) := by
    rw [uibhbotCcw_stage_vertex]
    exact hc
  have hcy := uibhbotCcw_past_complete_run W n x hv hc
  have hr := uibhbotCcw_rotation_of_star_in_run W H n (reversalDartVal y) hcover
  have hs := kmswInfRot_eq_stage (shiftedStream W n) (H.1 n) n y hcy
  have ht : wholePlaneDartι W n (reversalDartVal (stageRot (shiftedStream W n) n y)) =
      kmswPastDart W (reversalDartVal (stageRot (kmswPastCode W) n x)) := by
    rw [kmswStage_rev_rot]
    exact hrep (stageRot (kmswPastCode W) n x)
  exact (congrArg (wholePlaneRotation W H) (hrep x).symm).trans
    (hr.trans ((congrArg (wholePlaneDartι W n) hs).trans
      (ht.trans (congrArg (kmswPastDart W)
        (kmswInfRot_eq_stage _ hfin n x hcx).symm))))

/-- Negation shifts a nonzero direction's argument by a half turn. -/
private theorem uibhbotCcw_arg_neg_cases (z : ℂ) (hz : z ≠ 0) :
    (0 < Complex.arg z ∧ Complex.arg (-z) = Complex.arg z - Real.pi) ∨
    (Complex.arg z ≤ 0 ∧ Complex.arg (-z) = Complex.arg z + Real.pi) := by
  rcases lt_trichotomy z.im 0 with hi | hi | hi
  · exact Or.inr ⟨(Complex.arg_neg_iff.mpr hi).le,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hi⟩
  · by_cases hr : z.re < 0
    · exact Or.inl ⟨(Complex.arg_eq_pi_iff.mpr ⟨hr, hi⟩) ▸ Real.pi_pos,
        Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨hi, hr⟩)⟩
    · have hr' : 0 < z.re := lt_of_le_of_ne (le_of_not_gt hr) (by
        intro he
        apply hz
        apply Complex.ext
        · exact he.symm
        · exact hi)
      exact Or.inr ⟨(Complex.arg_eq_zero_iff.mpr ⟨hr'.le, hi⟩).le,
        Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨hi, hr'⟩)⟩
  · have harg : 0 < Complex.arg z := by
      apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le)
      intro he
      exact hi.ne' (Complex.arg_eq_zero_iff.mp he.symm).2
    exact Or.inl ⟨harg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi⟩

/-- The attachment half-turn preserves the cyclic turn between nonzero directions. -/
private theorem uibhbotCcw_turn_neg (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ccwTurn (-u) (-v) = ccwTurn u v := by
  have huarg := Complex.arg_mem_Ioc u
  have hvarg := Complex.arg_mem_Ioc v
  rcases uibhbotCcw_arg_neg_cases u hu with ⟨hup, hnu⟩ | ⟨hup, hnu⟩ <;>
    rcases uibhbotCcw_arg_neg_cases v hv with ⟨hvp, hnv⟩ | ⟨hvp, hnv⟩ <;>
    unfold ccwTurn <;> rw [hnu, hnv] <;> split_ifs <;>
    linarith [huarg.1, huarg.2, hvarg.1, hvarg.2, Real.pi_pos]

/-- Mapping the polyline points by the attachment map negates its initial direction. -/
private theorem uibhbotCcw_halfTurn_initial (p : Polyline) :
    (Polyline.mapPoints uibhbotAssemblyHalfTurn p).initialDirection = -p.initialDirection := by
  simp only [Polyline.initialDirection, Polyline.point_mapPoints, Polyline.start_mapPoints,
    uibhbotAssemblyHalfTurn]
  ring

/-- At an unshared past vertex, the same assembled arcs have the whole-plane
angular successor of G4b, including on the unglued past boundary. The half-turn
preserves cyclic turns and no past boundary-hit witness is assumed. -/
theorem uibhbotCcw_assembly_rotation_past_unshared (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (f : (ℕ × Bool) → Polyline) (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∉
      range (wholePlaneVertexι W 0)) :
    CcwSuccessor
      {E | wholePlaneDartVertex W E = wholePlaneDartVertex W (kmswPastDart W d)}
      (fun E => (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) f E).initialDirection)
      (kmswPastDart W d) (wholePlaneRotation W H (kmswPastDart W d)) := by
  have hn (e : ℕ × Bool)
      (he : kmswLimitDartVertex (kmswPastCode W) e =
        kmswLimitDartVertex (kmswPastCode W) d) : ¬ kmswPastSeamEdge W e.1 := by
    intro hs
    apply hv
    rw [← he]
    exact uibhbotSeparation_seam_incident_shared W h0 e hs
  have hs : CcwSuccessor
      {e | kmswLimitDartVertex (kmswPastCode W) e =
        kmswLimitDartVertex (kmswPastCode W) d}
      (fun e => -(P.arc e).initialDirection) d (kmswInfRot (kmswPastCode W) hfin d) := by
    obtain ⟨hfin', hd, hr, hcase⟩ := P.rotation_agreement d
    refine ⟨hfin', hd, hr, ?_⟩
    rcases hcase with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · refine Or.inr ⟨hne, ?_⟩
      intro e he hed
      rw [uibhbotCcw_turn_neg _ _ (P.initial_nonzero d) (P.initial_nonzero _),
        uibhbotCcw_turn_neg _ _ (P.initial_nonzero d) (P.initial_nonzero e)]
      exact hmin e he hed
  rw [uibhbotCcw_rotation_past_unshared W H hfin d hv,
    uibhbotCcw_star_past_unshared W d hv]
  apply uibhbotCcw_successor_image (kmswPastDart W) (kmswPastDart_injective W)
    _ (fun e => -(P.arc e).initialDirection) _ _ d _ hs
  intro e he
  rw [uibhbotAssemblyArc_past W h0 _ _ e (hn e he), uibhbotCcw_halfTurn_initial]

/-- G4b holds for the concrete candidate assembly at every vertex outside the
intersection of the past and future vertex carriers. Both component rotations
are used; this leaves precisely the shared seam stars. -/
theorem uibhbotCcw_assembly_rotation_unshared (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (D : WholePlaneDart W)
    (hv : wholePlaneDartVertex W D ∉
      range (wholePlaneVertexι W 0) ∩ range (kmswPastVertex W)) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
      (fun E => (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc E).initialDirection)
      D (wholePlaneRotation W H D) := by
  rcases WholePlanePastGlueData.dart_cover W D with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · apply uibhbotCcw_assembly_rotation_future_unshared W H _ F d
    intro hp
    apply hv
    rw [wholePlaneDartVertex_ι]
    exact ⟨⟨_, rfl⟩, hp⟩
  · apply uibhbotCcw_assembly_rotation_past_unshared W H h0 hfin P F.arc d
    intro hf
    apply hv
    rw [WholePlanePastGlueData.pastDart_vertex]
    exact ⟨hf, ⟨_, rfl⟩⟩



theorem uibhbotCodeLawRel_ae_candidate_glue_geometry_rotation_unshared :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ pos : WholePlaneVertex W → ℂ,
      ∃ arc : WholePlaneDart W → Polyline,
        Function.Injective pos ∧
        (∀ D E, E ≠ D → E ≠ wholePlaneDartFlip W D →
          Disjoint (arc D).interior (arc E).interior) ∧
        (∀ D V, pos V ∉ (arc D).interior) ∧
        (∀ D E, wholePlaneDartVertex W D = wholePlaneDartVertex W E →
          Complex.arg (arc D).initialDirection =
            Complex.arg (arc E).initialDirection → D = E) ∧
        (∀ D, wholePlaneDartVertex W D ∉
          range (wholePlaneVertexι W 0) ∩ range (kmswPastVertex W) →
          CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
            (fun E => (arc E).initialDirection) D (wholePlaneRotation W H D)) ∧
        (∀ D, (arc D).IsSimple) ∧
        (∀ D, 2 ≤ (arc D).points.length) ∧
        (∀ D, (arc D).start = pos (wholePlaneDartVertex W D)) ∧
        (∀ D, (arc D).finish = pos (wholePlaneDartVertex W (wholePlaneDartFlip W D))) ∧
        (∀ D, arc (wholePlaneDartFlip W D) = (arc D).reverse) ∧
        (∀ D, (arc D).initialDirection ≠ 0) ∧
        (∀ K : Set ℂ, Bornology.IsBounded K →
          {D | (K ∩ (arc D).image).Nonempty}.Finite) ∧
        (∀ k : ℤ, pos (wholePlaneVertexι W 0
          (boundaryVertex (shiftedStream W 0) h0 k)) = ⟨-(k : ℝ), 0⟩) ∧
        (∀ v : ℕ, (pos (wholePlaneVertexι W 0 v)).im ≤ 0) ∧
        (∀ v : ℕ, 0 ≤ (pos (kmswPastVertex W v)).im) ∧
        (∀ k : ℤ, ∀ b : Bool,
          (arc (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, b))).image
            ⊆ {z : ℂ | z.im = 0}) ∧
        (∀ d : ℕ × Bool, ¬ kmswPastSeamEdge W d.1 →
          (arc (kmswPastDart W d)).image ⊆ {z : ℂ | 0 ≤ z.im}) ∧
        ∀ d : ℕ × Bool,
          (arc (wholePlaneDartι W 0 d)).image ⊆ {z : ℂ | z.im ≤ 0} := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses, uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg, uibhbotCodeLawRel_ae_past_finiteIncidence]
    with W hH hhit hL hR hfin
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨P, hPquad, hppos, hparc⟩ :=
    uibhbotAssembly_past_straightDrawing_quadrant W hL hR.1 hfin
  have hPim : P.image ⊆ {z : ℂ | z.im ≤ 0} := fun z hz => (hPquad hz).1
  obtain ⟨F, hFim, hFpos, hfpos, hFarc⟩ :=
    uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hp : uibhbotAssemblyHalfTurn ∘ P.pos =
      uibhbotSeparationPastPos W hL hR.1 hfin := by
    funext v
    rw [Function.comp_apply, hppos]
    rfl
  have hf : F.pos = uibhbotSeparationFuturePos W H h0 := by
    rw [hfpos]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    change F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v
    rw [hp, hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR.1 hfin u v huv
  let pos := uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
  let arc := uibhbotAssemblyArc W
    (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc
  have hsimple : ∀ D, (arc D).IsSimple := uibhbotAssemblyArc_simple W H hfin P F
  have hlen : ∀ D, 2 ≤ (arc D).points.length := uibhbotAssemblyArc_length W H hfin P F
  have hstart : ∀ D, (arc D).start = pos (wholePlaneDartVertex W D) :=
    uibhbotAssemblyArc_start W H hfin P F h0 hc
  have hfinish : ∀ D, (arc D).finish =
      pos (wholePlaneDartVertex W (wholePlaneDartFlip W D)) :=
    uibhbotAssemblyArc_finish W H hfin P F h0 hc
  have hdis : ∀ D E, E ≠ D → E ≠ wholePlaneDartFlip W D →
      Disjoint (arc D).interior (arc E).interior :=
    uibhbotInteriors_assembly_interior_disjoint W hL hR.1 hfin P hppos hparc H h0 F hFim
  have havoid : ∀ D V, pos V ∉ (arc D).interior :=
    uibhbotRotation_assembly_interior_avoids_vertices W H h0 hL hR.1 hfin
      P hppos hparc F hf hFim
  have hdir : ∀ D, (arc D).initialDirection ≠ 0 := by
    intro D hz
    apply (hsimple D).1 0 (by have := hlen D; omega)
    rw [Polyline.point_zero_eq_start]
    exact (sub_eq_zero.mp hz).symm
  refine ⟨H, h0, pos, arc, ?_, hdis, havoid,
    uibhbotCcw_initial_arg_injective (wholePlaneDartFlip W) (wholePlaneDartVertex W)
      pos arc hsimple hlen hstart hfinish hdis havoid hdir,
    uibhbotCcw_assembly_rotation_unshared W H h0 hfin P F,
    hsimple, hlen, hstart, hfinish, uibhbotAssemblyArc_flip W H hfin P F, hdir,
    uibhbotAssemblyArc_locally_finite W H hfin P F h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Function.Injective (uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos)
    rw [hp, hf]
    exact uibhbotSeparation_assembly_pos_injective W H h0 hL hR.1 hfin
  · intro k
    exact (uibhbotAssemblyPos_future W _ _ _).trans (hFpos k)
  · intro v
    change (uibhbotAssemblyPos W _ _ _).im ≤ 0
    rw [uibhbotAssemblyPos_future]
    exact hFim (Or.inl ⟨v, rfl⟩)
  · intro v
    change 0 ≤ (uibhbotAssemblyPos W _ _ _).im
    rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc]
    have hpv : (P.pos v).im ≤ 0 := hPim (Or.inl ⟨v, rfl⟩)
    change 0 ≤ -(P.pos v).im - 0
    linarith only [hpv]
  · intro k b z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 _)).image at hz
    rw [uibhbotAssemblyArc_future, hFarc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hg := uibhbotAssembly_future_seam_graph (shiftedStream W 0) h0 (H.1 0) k b hy
    change -y.im + 0 + seamFun (shiftedStream W 0) h0 (H.1 0) y.re = 0
    rw [← hg]
    ring
  · intro d hd z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (kmswPastDart W d)).image at hz
    rw [uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hpv : y.im ≤ 0 := hPim (Or.inr ⟨d, hy⟩)
    change 0 ≤ -y.im - 0
    linarith only [hpv]
  · intro d z hz
    change z ∈ (uibhbotAssemblyArc W _ _ (wholePlaneDartι W 0 d)).image at hz
    rw [uibhbotAssemblyArc_future] at hz
    exact hFim (Or.inr ⟨d, hz⟩)

/-- At a shared vertex, the whole star is the disjoint union of the future star
and the retained past darts. This is the one-sided decomposition: it does not
complete the past boundary or assume past boundary-hit witnesses. -/
theorem uibhbotCcw_star_shared (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (u v : ℕ)
    (huv : wholePlaneVertexι W 0 u = kmswPastVertex W v) :
    {E | wholePlaneDartVertex W E = wholePlaneVertexι W 0 u} =
      wholePlaneDartι W 0 '' {d | kmswLimitDartVertex (shiftedStream W 0) d = u} ∪
        kmswPastDart W '' {d | kmswLimitDartVertex (kmswPastCode W) d = v ∧
          ¬ kmswPastSeamEdge W d.1} := by
  ext E
  constructor
  · intro he
    rcases WholePlanePastGlueData.dart_cover_off_seam W h0 E with
      ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
    · exact Or.inl ⟨d, wholePlaneVertexι_injective W 0
        ((wholePlaneDartVertex_ι W 0 d).symm.trans he), rfl⟩
    · exact Or.inr ⟨d, ⟨kmswPastVertex_injective W
        ((WholePlanePastGlueData.pastDart_vertex W d).symm.trans (he.trans huv)), hd⟩, rfl⟩
  · rintro (⟨d, hd, rfl⟩ | ⟨d, ⟨hd, _⟩, rfl⟩)
    · exact (wholePlaneDartVertex_ι W 0 d).trans (congrArg (wholePlaneVertexι W 0) hd)
    · exact (WholePlanePastGlueData.pastDart_vertex W d).trans
        ((congrArg (kmswPastVertex W) hd).trans huv.symm)

/-- The two parts of the one-sided shared-star decomposition are disjoint. -/
theorem uibhbotCcw_star_shared_disjoint (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (u v : ℕ) :
    Disjoint
      (wholePlaneDartι W 0 '' {d | kmswLimitDartVertex (shiftedStream W 0) d = u})
      (kmswPastDart W '' {d | kmswLimitDartVertex (kmswPastCode W) d = v ∧
        ¬ kmswPastSeamEdge W d.1}) := by
  apply disjoint_left.mpr
  rintro E ⟨d, _, hd⟩ ⟨e, ⟨_, he⟩, heq⟩
  apply he
  apply (kmswPastEdge_mem_runZero_iff W h0 e.1).mp
  exact ⟨d.1, congrArg Prod.fst (hd.trans heq.symm)⟩

/-- Every shared vertex has a nonnegative future boundary label. The endpoint
label zero is retained; no extension of the past seam to a line is made. -/
theorem uibhbotCcw_shared_label_nonneg (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (u v : ℕ) (huv : wholePlaneVertexι W 0 u = kmswPastVertex W v) :
    ∃ k : ℤ, 0 ≤ k ∧ u = boundaryVertex (shiftedStream W 0) h0 k := by
  obtain ⟨n, e, he, hev⟩ := uibhbotGlue_shared_vertex_mem_seam W v ⟨u, huv⟩
  obtain ⟨j, hj, hje, _, _⟩ := uibhbotGlue_past_seam_match W h0 hR n e he
  have heb := (kmswStage_boundary_ids_lt_nextEdge (kmswPastCode W) n).2 e (by
    simp only [List.mem_append] at he ⊢
    tauto)
  have hends := edge_endpoints_eq (kmswPastCode W) heb
  rcases hev with hw | ht
  · have hi := congrArg (wholePlaneEdgeEast W) hje
    rw [kmswPastEdge_east, ← hends.1, hw, wholePlaneEdgeEast_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).2.1, ← huv] at hi
    exact ⟨j + 1, by omega, wholePlaneVertexι_injective W 0 hi⟩
  · have hi := congrArg (wholePlaneEdgeWest W) hje
    rw [kmswPastEdge_west, ← hends.2, ht, wholePlaneEdgeWest_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 j).1, ← huv] at hi
    exact ⟨j, hj, wholePlaneVertexι_injective W 0 hi⟩

/-- At a labelled seam vertex, an overlapping dart is one of the two horizontal
boundary darts, and its boundary edge has a nonnegative label. In particular
the right dart cannot overlap at the half-line endpoint. -/
theorem uibhbotCcw_overlap_shared (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (k : ℤ) (d e : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0) d =
      boundaryVertex (shiftedStream W 0) h0 k)
    (he : kmswPastDart W e = wholePlaneDartι W 0 d) :
    (d = (boundaryOuterEdge (shiftedStream W 0) h0 k, false) ∧ 0 ≤ k) ∨
      (d = (boundaryOuterEdge (shiftedStream W 0) h0 (k - 1), true) ∧ 1 ≤ k) := by
  have hs := (kmswPastEdge_mem_runZero_iff W h0 e.1).mp
    ⟨d.1, (congrArg Prod.fst he).symm⟩
  obtain ⟨n, hn⟩ := hs
  obtain ⟨j, hj, hje, _, _⟩ := uibhbotGlue_past_seam_match W h0 hR n e.1 hn
  have hde : d.1 = boundaryOuterEdge (shiftedStream W 0) h0 j :=
    wholePlaneEdgeι_injective W 0 ((congrArg Prod.fst he).symm.trans hje)
  have hinj : Function.Injective (boundaryOuterEdge (shiftedStream W 0) h0) := by
    intro a b hab
    apply boundaryVertex_injective (shiftedStream W 0) h0
    exact ((boundaryOuterEdge_endpoints (shiftedStream W 0) h0 a).1).symm.trans
      ((congrArg (edgeWest (shiftedStream W 0)) hab).trans
        (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 b).1)
  rcases WholePlaneGlueSeamStar.runZero_seam_darts W h0 k d hd ⟨j, hde⟩ with h | h
  · left
    refine ⟨h, ?_⟩
    have hjk := hinj (hde.symm.trans (congrArg Prod.fst h))
    omega
  · right
    refine ⟨h, ?_⟩
    have hjk := hinj (hde.symm.trans (congrArg Prod.fst h))
    omega

/-- The right horizontal dart at the half-line endpoint is absent from the past
dart carrier. This isolates the endpoint from the two-anchor interior seam. -/
theorem uibhbotCcw_endpoint_right_not_past (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) :
    wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (-1), true) ∉
      range (kmswPastDart W) := by
  rintro ⟨e, he⟩
  have hv : kmswLimitDartVertex (shiftedStream W 0)
      (boundaryOuterEdge (shiftedStream W 0) h0 (-1), true) =
      boundaryVertex (shiftedStream W 0) h0 0 := by
    exact (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 (-1)).2.1
  rcases uibhbotCcw_overlap_shared W h0 hR 0 _ e hv he with ⟨hf, _⟩ | ⟨_, hk⟩
  · have hb := congrArg Prod.snd hf
    cases hb
  · omega

/-- The midpoint of the first segment of a simple polyline belongs to its
interior. This gives strict sector information even for a two-point arc. -/
private theorem uibhbotCcw_initial_midpoint_interior (p : Polyline)
    (hp : p.IsSimple) (hlen : 2 ≤ p.points.length) :
    p.start + (1 / 2 : ℂ) * p.initialDirection ∈ p.interior := by
  have hz : p.start + (1 / 2 : ℂ) * p.initialDirection ∈ p.segmentAt 0 := by
    rw [Polyline.segmentAt, Polyline.point_zero_eq_start, segment_eq_image']
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    dsimp only
    rw [Complex.real_smul]
    norm_num [Polyline.initialDirection]
  have hs : p.point 0 ≠ p.point 1 := hp.1 0 (by omega)
  have hn : p.initialDirection ≠ 0 := by
    intro he
    apply hs
    rw [Polyline.point_zero_eq_start]
    exact (sub_eq_zero.mp he).symm
  refine ⟨Or.inr ⟨0, by omega, hz⟩, ?_⟩
  rintro (he | he)
  · have he' : (1 / 2 : ℂ) * p.initialDirection = 0 := by
      simpa only [add_eq_left] using he
    exact mul_ne_zero (by norm_num) hn he'
  · by_cases ht : p.points.length = 2
    · have hf : p.finish = p.point 1 := by
        rw [← Polyline.point_last_eq_finish, ht]
      rw [hf] at he
      have hdir : p.point 1 = p.start + p.initialDirection := by
        unfold Polyline.initialDirection
        ring
      rw [hdir] at he
      have he' : (1 / 2 : ℂ) * p.initialDirection = p.initialDirection := add_left_cancel he
      have he'' : (1 / 2 : ℂ) = 1 :=
        mul_right_cancel₀ hn (he'.trans (one_mul p.initialDirection).symm)
      norm_num at he''
    · have hb : p.finish ∈ p.segmentAt (p.points.length - 2) := by
        rw [Polyline.segmentAt, show p.points.length - 2 + 1 = p.points.length - 1 by omega,
          Polyline.point_last_eq_finish]
        exact right_mem_segment ℝ _ _
      rw [he] at hz
      by_cases hthree : p.points.length = 3
      · have hmem : p.finish ∈ ({p.point 1} : Set ℂ) := by
          have hboth : p.finish ∈ p.segmentAt 0 ∩ p.segmentAt 1 :=
            ⟨hz, by simpa only [hthree] using hb⟩
          rwa [hp.2.1 0 (by omega)] at hboth
        have heq : p.point 1 = p.point 2 := by
          rw [← hmem, ← Polyline.point_last_eq_finish, hthree]
        exact hp.1 1 (by omega) heq
      · exact disjoint_left.mp
          (hp.2.2 0 (p.points.length - 2) (by omega) (by omega) (by omega)) hz hb

/-- Every retained past dart at a shared vertex points into the open upper
half-plane. The strict inequality is derived from its actual interior. -/
theorem uibhbotCcw_shared_past_direction_pos (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (f : (ℕ × Bool) → Polyline) (u v : ℕ)
    (huv : wholePlaneVertexι W 0 u = kmswPastVertex W v)
    (d : ℕ × Bool) (hv : kmswLimitDartVertex (kmswPastCode W) d = v)
    (hd : ¬ kmswPastSeamEdge W d.1) :
    0 < (uibhbotAssemblyArc W
      (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) f
      (kmswPastDart W d)).initialDirection.im := by
  let q := Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)
  have hsimple : q.IsSimple := Polyline.isSimple_mapPoints _ _
    (uibhbotAssemblyHalfTurn_affine _) uibhbotAssemblyHalfTurn_involutive.injective.injOn
    (P.arc_simple d)
  have hlen : 2 ≤ q.points.length := by
    simpa only [q, Polyline.mapPoints, List.length_map] using P.arc_length d
  have hs : q.start = uibhbotSeparationPastPos W hL hR hfin v := by
    rw [Polyline.start_mapPoints, P.arc_start, hv, hp]
    rfl
  have hpos := uibhbotSeparation_positions_compatible W H h0 hL hR hfin u v huv
  obtain ⟨k, hk⟩ := uibhbotAssembly_shared_vertex_future_boundary W h0 u v huv
  rw [hk, uibhbotSeparation_future_boundary_pos] at hpos
  have hs0 : q.start.im = 0 := by rw [hs, ← hpos]
  have hmid := uibhbotInteriors_past_attached_pos W hL hR hfin P hp ha d hd
    (uibhbotCcw_initial_midpoint_interior q hsimple hlen)
  change 0 < (q.start + (1 / 2 : ℂ) * q.initialDirection).im at hmid
  norm_num [Complex.mul_im, hs0] at hmid
  rw [uibhbotAssemblyArc_past W h0 _ _ d hd]
  change 0 < q.initialDirection.im
  linarith only [hmid]

/-- Every future dart at a boundary vertex points into the closed lower
half-plane, using the candidate future drawing itself. -/
theorem uibhbotCcw_shared_future_direction_nonpos (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
    (hFpos : ∀ k : ℤ, F.pos (boundaryVertex (shiftedStream W 0) h0 k) = ⟨-(k : ℝ), 0⟩)
    (p : (ℕ × Bool) → Polyline) (k : ℤ) (d : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0) d =
      boundaryVertex (shiftedStream W 0) h0 k) :
    (uibhbotAssemblyArc W p F.arc (wholePlaneDartι W 0 d)).initialDirection.im ≤ 0 := by
  rw [uibhbotAssemblyArc_future]
  have hmem := (F.arc d).point_mem_image (i := 1) (by have := F.arc_length d; omega)
  have hle := hFim (Or.inr ⟨d, hmem⟩)
  change (F.arc d).initialDirection.im ≤ 0
  simp only [Polyline.initialDirection, Complex.sub_im, F.arc_start, hd, hFpos,
    sub_zero]
  exact hle

/-- Straight future boundary arcs stay between their exact consecutive integer
abscissas, in both orientations. -/
private theorem uibhbotCcw_future_boundary_bounds (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (ha : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer w h hfin ''
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image)
    (k : ℤ) (b : Bool) {z : ℂ}
    (hz : z ∈ (F.arc (boundaryOuterEdge w h k, b)).image) :
    -((k : ℝ) + 1) ≤ z.re ∧ z.re ≤ -(k : ℝ) ∧ z.im = 0 := by
  rw [ha] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hg := uibhbotAssembly_future_seam_graph w h hfin k b hy
  have hy' : y ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k)).image := by
    cases b with
    | true => exact hy
    | false =>
      have hr := (monotoneFamilyDrawing w hfin (monotone_family_all w)).arc_flip
        (boundaryOuterEdge w h k, true)
      change (monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        (boundaryOuterEdge w h k, false) =
        ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
          (boundaryOuterEdge w h k, true)).reverse at hr
      rw [hr, Polyline.image_reverse_transfer] at hy
      exact hy
  obtain ⟨g, hg'⟩ := seam_arc_image_graph w h hfin k
  rw [hg'] at hy'
  rw [uibhbotGlue_seamX_eq_int, uibhbotGlue_seamX_eq_int] at hy'
  change -((k : ℝ) + 1) ≤ -y.re ∧ -y.re ≤ -(k : ℝ) ∧
    -y.im + 0 + seamFun w h hfin y.re = 0
  push_cast at hy'
  exact ⟨neg_le_neg hy'.2.1, neg_le_neg hy'.1, by rw [← hg]; ring⟩

/-- The future left and right horizontal darts have arguments pi and zero.
This uses their actual arcs and includes the half-line endpoint. -/
theorem uibhbotCcw_future_boundary_args (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hfin : KMSWFiniteIncidence w)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hp : ∀ k : ℤ, F.pos (boundaryVertex w h k) = ⟨-(k : ℝ), 0⟩)
    (ha : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer w h hfin ''
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image)
    (k : ℤ) :
    Complex.arg (F.arc (boundaryOuterEdge w h k, false)).initialDirection = Real.pi ∧
      Complex.arg (F.arc (boundaryOuterEdge w h (k - 1), true)).initialDirection = 0 := by
  have hdata (j : ℤ) (b : Bool) := uibhbotCcw_future_boundary_bounds w h hfin F ha j b
    ((F.arc (boundaryOuterEdge w h j, b)).point_mem_image (i := 1)
      (by have := F.arc_length (boundaryOuterEdge w h j, b); omega))
  have hleftStart : (F.arc (boundaryOuterEdge w h k, false)).start = ⟨-(k : ℝ), 0⟩ := by
    rw [F.arc_start]
    change F.pos (edgeWest w (boundaryOuterEdge w h k)) = _
    rw [(boundaryOuterEdge_endpoints w h k).1, hp]
  have hrightStart : (F.arc (boundaryOuterEdge w h (k - 1), true)).start =
      ⟨-(k : ℝ), 0⟩ := by
    rw [F.arc_start]
    change F.pos (edgeEast w (boundaryOuterEdge w h (k - 1))) = _
    rw [(boundaryOuterEdge_endpoints w h (k - 1)).2.1, sub_add_cancel, hp]
  have hlIm : (F.arc (boundaryOuterEdge w h k, false)).initialDirection.im = 0 := by
    simp only [Polyline.initialDirection, Complex.sub_im, hleftStart, sub_zero]
    exact (hdata k false).2.2
  have hrIm : (F.arc (boundaryOuterEdge w h (k - 1), true)).initialDirection.im = 0 := by
    simp only [Polyline.initialDirection, Complex.sub_im, hrightStart, sub_zero]
    exact (hdata (k - 1) true).2.2
  have hlRe : (F.arc (boundaryOuterEdge w h k, false)).initialDirection.re ≤ 0 := by
    simp only [Polyline.initialDirection, Complex.sub_re, hleftStart]
    linarith only [(hdata k false).2.1]
  have hrRe : 0 ≤ (F.arc (boundaryOuterEdge w h (k - 1), true)).initialDirection.re := by
    simp only [Polyline.initialDirection, Complex.sub_re, hrightStart]
    have hb := (hdata (k - 1) true).1
    push_cast at hb
    linarith only [hb]
  refine ⟨Complex.arg_eq_pi_iff.mpr ⟨lt_of_le_of_ne hlRe ?_, hlIm⟩,
    Complex.arg_eq_zero_iff.mpr ⟨hrRe, hrIm⟩⟩
  intro he
  apply F.initial_nonzero (boundaryOuterEdge w h k, false)
  exact Complex.ext he hlIm

/-- Opening an upper sector does not change the lower successor except at the
right anchor. This is the one-sided use of `CcwSectorMerge`; its augmented
upper star also applies at the half-line endpoint. -/
private theorem uibhbotCcw_lower_merge {D : Type*}
    (U A : Set D) (dir : D → ℂ) (r l : D)
    (hfin : (A ∪ U).Finite) (hdis : Disjoint U A)
    (hr : r ∈ U) (hl : l ∈ U) (hrl : r ≠ l)
    (har : Complex.arg (dir r) = 0) (hal : Complex.arg (dir l) = Real.pi)
    (hup : ∀ a ∈ A, 0 < (dir a).im)
    (hlo : ∀ b ∈ U, (dir b).im ≤ 0)
    (harg : ∀ x y, x ∈ A ∪ U → y ∈ A ∪ U →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (d e : D) (hd : d ∈ U) (hdr : d ≠ r) :
    (CcwSuccessor (A ∪ U) dir d e ↔ CcwSuccessor U dir d e) ∧
      (CcwSuccessor U dir d e → e ≠ l) := by
  let B := U \ {r, l}
  have hAR : r ∉ A := fun ha => disjoint_left.mp hdis hr ha
  have hAL : l ∉ A := fun ha => disjoint_left.mp hdis hl ha
  have hU : U = B ∪ {r, l} := by
    ext x
    simp only [B, mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hx
      by_cases hxr : x = r
      · exact Or.inr (Or.inl hxr)
      by_cases hxl : x = l
      · exact Or.inr (Or.inr hxl)
      exact Or.inl ⟨hx, not_or.mpr ⟨hxr, hxl⟩⟩
    · rintro (⟨hx, _⟩ | rfl | rfl)
      · exact hx
      · exact hr
      · exact hl
  have hB (b : D) (hb : b ∈ B) : Complex.arg (dir b) < 0 := by
    have hbr : b ≠ r := fun he => hb.2 (by simp only [he, mem_insert_iff, true_or])
    have hbl : b ≠ l := fun he => hb.2 (by simp only [he, mem_insert_iff,
      mem_singleton_iff, or_true])
    have him : (dir b).im < 0 := by
      apply lt_of_le_of_ne (hlo b hb.1)
      intro hz
      rcases lt_or_ge (dir b).re 0 with hre | hre
      · exact hbl (harg b l (Or.inr hb.1) (Or.inr hl)
          ((Complex.arg_eq_pi_iff.mpr ⟨hre, hz⟩).trans hal.symm))
      · exact hbr (harg b r (Or.inr hb.1) (Or.inr hr)
          ((Complex.arg_eq_zero_iff.mpr ⟨hre, hz⟩).trans har.symm))
    exact Complex.arg_neg_iff.mpr him
  have hsectorA (a : D) (ha : a ∈ A) :
      0 < ccwTurn (dir r) (dir a) ∧
        ccwTurn (dir r) (dir a) < ccwTurn (dir r) (dir l) := by
    have hapos : 0 < Complex.arg (dir a) := by
      apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr (hup a ha).le)
      intro hz
      exact (hup a ha).ne' (Complex.arg_eq_zero_iff.mp hz.symm).2
    have hapi : Complex.arg (dir a) < Real.pi :=
      Complex.arg_lt_pi_iff.mpr (Or.inr (hup a ha).ne')
    simp only [ccwTurn, har, hal, ite_eq_left hapos, ite_eq_left Real.pi_pos]
    exact ⟨by linarith only [hapos], by linarith only [hapi]⟩
  have hsectorB (b : D) (hb : b ∈ B) :
      ccwTurn (dir r) (dir l) < ccwTurn (dir r) (dir b) := by
    have hargb := Complex.arg_mem_Ioc (dir b)
    simp only [ccwTurn, har, hal, ite_eq_left Real.pi_pos,
      ite_eq_right (not_lt_of_ge (hB b hb).le)]
    linarith only [hargb.1]
  have hd' : d ∈ B ∪ {l} := by
    by_cases hdl : d = l
    · exact Or.inr hdl
    · exact Or.inl ⟨hd, by simpa only [mem_insert_iff, mem_singleton_iff, not_or]
        using (And.intro hdr hdl)⟩
  have hmerge := ccwSuccessor_lower_star_merge (A ∪ U) (A ∪ {r, l}) U A B dir r l
    rfl hU (by rw [hU]; ext x; simp only [mem_union]; tauto) hfin
    (disjoint_left.mpr (fun x hx hxB => disjoint_left.mp hdis hxB.1 hx))
    hAR hAL (by simp only [B, mem_sdiff, mem_insert_iff, true_or, not_true_eq_false,
      and_false, not_false_eq_true])
    (by simp only [B, mem_sdiff, mem_insert_iff, mem_singleton_iff, or_true,
      not_true_eq_false, and_false, not_false_eq_true]) hrl hsectorA hsectorB
    (fun x y hx hy hne he => hne (harg x y hx hy he)) d e hd'
  refine ⟨hmerge, ?_⟩
  intro hs hel
  have hnot : U ≠ {d} := by
    intro he
    exact hdr (show r = d from (by simpa only [he, mem_singleton_iff] using hr)).symm
  have hm := hs.2.2.2.resolve_left (fun h => hnot h.2)
  have hle := hm.2 r hr (Ne.symm hdr)
  rw [hel] at hle
  rcases hd' with hdB | hdl
  · have hbd := hB d hdB
    simp only [ccwTurn, hal, har, ite_eq_left (hbd.trans Real.pi_pos), ite_eq_left hbd] at hle
    linarith only [hle, Real.pi_pos]
  · have hdl' : d = l := hdl
    rw [hdl'] at hle
    simp only [ccwTurn, hal, har, lt_self_iff_false, ite_false,
      ite_eq_right (not_lt_of_ge Real.pi_pos.le)] at hle
    linarith only [hle, Real.pi_pos]

/-- G4a for the concrete deterministic candidate drawings used in the seam proof.
All geometric clauses are proved from the same one-sided witnesses. -/
theorem uibhbotCcw_assembly_arg_injective (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (hf : F.pos = uibhbotSeparationFuturePos W H h0)
    (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0}) :
    ∀ D E, wholePlaneDartVertex W D = wholePlaneDartVertex W E →
      Complex.arg (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc D).initialDirection =
      Complex.arg (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc E).initialDirection →
      D = E := by
  let pos := uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
  let arc := uibhbotAssemblyArc W
    (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
  have hp' : uibhbotAssemblyHalfTurn ∘ P.pos = uibhbotSeparationPastPos W hL hR hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    change F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v
    rw [hp', hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR hfin u v huv
  have hs := uibhbotAssemblyArc_simple W H hfin P F
  have hl := uibhbotAssemblyArc_length W H hfin P F
  have hdir : ∀ D, (arc D).initialDirection ≠ 0 := by
    intro D hz
    apply (hs D).1 0 (by have := hl D; omega)
    rw [Polyline.point_zero_eq_start]
    exact (sub_eq_zero.mp hz).symm
  exact uibhbotCcw_initial_arg_injective (wholePlaneDartFlip W) (wholePlaneDartVertex W)
    pos arc hs hl (uibhbotAssemblyArc_start W H hfin P F h0 hc)
    (uibhbotAssemblyArc_finish W H hfin P F h0 hc)
    (uibhbotInteriors_assembly_interior_disjoint W hL hR hfin P hp ha H h0 F hFim)
    (uibhbotRotation_assembly_interior_avoids_vertices W H h0 hL hR hfin P hp ha F hf hFim)
    hdir

/-- G4b at every shared future dart except the right horizontal dart. The upper
past sector is obtained from retained past interiors, and the lower successor
is spliced by `CcwSectorMerge`. The statement also covers the endpoint k = 0. -/
theorem uibhbotCcw_assembly_rotation_shared_future (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (hf : F.pos = uibhbotSeparationFuturePos W H h0)
    (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
    (k : ℤ) (v : ℕ)
    (hv : wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k) = kmswPastVertex W v)
    (d : ℕ × Bool)
    (hdv : kmswLimitDartVertex (shiftedStream W 0) d = boundaryVertex (shiftedStream W 0) h0 k)
    (hd : d ≠ (boundaryOuterEdge (shiftedStream W 0) h0 (k - 1), true)) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W (wholePlaneDartι W 0 d)}
      (fun E => (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc E).initialDirection)
      (wholePlaneDartι W 0 d) (wholePlaneRotation W H (wholePlaneDartι W 0 d)) := by
  let U := wholePlaneDartι W 0 ''
    {e | kmswLimitDartVertex (shiftedStream W 0) e = boundaryVertex (shiftedStream W 0) h0 k}
  let A := kmswPastDart W ''
    {e | kmswLimitDartVertex (kmswPastCode W) e = v ∧ ¬ kmswPastSeamEdge W e.1}
  let arc := uibhbotAssemblyArc W
    (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
  let dir := fun E => (arc E).initialDirection
  let r := wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (k - 1), true)
  let l := wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, false)
  have hstar : {E | wholePlaneDartVertex W E =
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k)} = A ∪ U := by
    rw [uibhbotCcw_star_shared W h0 _ v hv]
    exact union_comm _ _
  have hFpos (j : ℤ) : F.pos (boundaryVertex (shiftedStream W 0) h0 j) = ⟨-(j : ℝ), 0⟩ := by
    rw [hf, uibhbotSeparation_future_boundary_pos]
  have hmem := WholePlaneGlueSeamStar.runZero_seam_darts_incident W h0 k
  have hr : r ∈ U := ⟨_, hmem.2.2, rfl⟩
  have hl : l ∈ U := ⟨_, hmem.2.1, rfl⟩
  have hrl : r ≠ l := fun he => hmem.1 (uibhbotCcw_dart_injective W 0 he).symm
  have hargs := uibhbotCcw_future_boundary_args (shiftedStream W 0) h0 (H.1 0) F hFpos hFa k
  have har : Complex.arg (dir r) = 0 := by
    dsimp only [dir, arc, r]
    rw [uibhbotAssemblyArc_future]
    exact hargs.2
  have hal : Complex.arg (dir l) = Real.pi := by
    dsimp only [dir, arc, l]
    rw [uibhbotAssemblyArc_future]
    exact hargs.1
  have hup : ∀ a ∈ A, 0 < (dir a).im := by
    rintro _ ⟨e, ⟨he, hse⟩, rfl⟩
    exact uibhbotCcw_shared_past_direction_pos W H h0 hL hR hfin P hp ha F.arc
      _ v hv e he hse
  have hlo : ∀ b ∈ U, (dir b).im ≤ 0 := by
    rintro _ ⟨e, he, rfl⟩
    exact uibhbotCcw_shared_future_direction_nonpos W H h0 F hFim hFpos _ k e he
  have harg : ∀ x y, x ∈ A ∪ U → y ∈ A ∪ U →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y := by
    intro x y hx hy he
    rw [← hstar] at hx hy
    exact uibhbotCcw_assembly_arg_injective W H h0 hL hR hfin P hp ha F hf hFim x y
      (hx.trans hy.symm) he
  have hfin' : (A ∪ U).Finite := hstar ▸ wholePlaneStar_finite W H _
  have hdis : Disjoint U A := uibhbotCcw_star_shared_disjoint W h0 _ v
  have hdr : wholePlaneDartι W 0 d ≠ r := fun he => hd (uibhbotCcw_dart_injective W 0 he)
  have hs := F.rotation_agreement d
  rw [hdv] at hs
  have hs' : CcwSuccessor U dir (wholePlaneDartι W 0 d)
      (wholePlaneDartι W 0 (kmswInfRot (shiftedStream W 0) (H.1 0) d)) :=
    uibhbotCcw_successor_image _ (uibhbotCcw_dart_injective W 0) _ _ dir
      (fun e _ => congrArg Polyline.initialDirection (uibhbotAssemblyArc_future W _ F.arc e))
      d _ hs
  have hm := uibhbotCcw_lower_merge U A dir r l hfin' hdis hr hl hrl har hal
    hup hlo harg (wholePlaneDartι W 0 d)
    (wholePlaneDartι W 0 (kmswInfRot (shiftedStream W 0) (H.1 0) d))
    (show wholePlaneDartι W 0 d ∈ U from ⟨d, hdv, rfl⟩) hdr
  have hnext := hm.2 hs'
  have hrot := WholePlaneGlueSeamStar.rot_seam_runZero W h0 H k d hdv
    (fun he => hnext (congrArg (wholePlaneDartι W 0) he))
  rw [hrot]
  change CcwSuccessor {E | wholePlaneDartVertex W E =
    wholePlaneDartVertex W (wholePlaneDartι W 0 d)} dir _ _
  rw [wholePlaneDartVertex_ι, hdv, hstar]
  exact hm.1.mpr hs'

/-- Each lower-left west endpoint has a present outgoing edge, created together
with its missing lower edge. Missing edges themselves are retained. -/
private theorem uibhbotCcw_LL_west_present (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL) :
    ∃ f, f < (kmswStage w n).nextEdge ∧ (kmswStage w n).present f = true ∧
      (kmswStage w n).west f = (kmswStage w n).west e := by
  obtain ⟨s, hs, hc, hm, heq⟩ := kmswStage_LL_exists_revLeftRecord w n e he
  have hnil := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w s).mpr hm
  let f := (kmswStage w s).nextEdge
  have hf : f < (kmswStage w (s + 1)).nextEdge := by
    simp [f, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]
  have hp : (kmswStage w (s + 1)).present f = true := by
    simp [f, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]
  have he' : e < (kmswStage w (s + 1)).nextEdge := by
    simp [heq, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]
  have hw : (kmswStage w (s + 1)).west f = (kmswStage w (s + 1)).west e := by
    simp [heq, f, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]
  obtain ⟨hfn, hpn⟩ := present_mono w hf hp n (by omega)
  refine ⟨f, hfn, hpn, ?_⟩
  rw [(kmswStage_endpoints_stable w (by omega : s + 1 ≤ n) hf).1,
    (kmswStage_endpoints_stable w (by omega : s + 1 ≤ n) he').1]
  exact hw

/-- A past lower-seam endpoint either has a present outgoing edge or is the
initial terminal vertex 1. This includes the half-line endpoint explicitly. -/
private theorem uibhbotCcw_lower_endpoint_present_or_one (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (n e v : ℕ)
    (he : e ∈ (kmswStage (kmswPastCode W) n).LL ++ (kmswStage (kmswPastCode W) n).LR)
    (hv : (kmswStage (kmswPastCode W) n).west e = v ∨
      (kmswStage (kmswPastCode W) n).east e = v) :
    v = 1 ∨ ∃ f, f < (kmswStage (kmswPastCode W) n).nextEdge ∧
      (kmswStage (kmswPastCode W) n).present f = true ∧
      (kmswStage (kmswPastCode W) n).west f = v := by
  let w := kmswPastCode W
  let s := kmswStage w n
  have hLR : s.LR = [0] := uibhbotPastStage_LR_eq_root W hR n
  have hwest (f : ℕ) (hf : f ∈ s.LL ++ s.LR) :
      ∃ g, g < s.nextEdge ∧ s.present g = true ∧ s.west g = s.west f := by
    rcases List.mem_append.mp hf with hLL | hLR'
    · exact uibhbotCcw_LL_west_present w n f hLL
    · exact ⟨f, (kmswStage_boundary_ids_lt_nextEdge w n).2 f
        (by simp only [List.mem_append]; tauto), (kmswStage_status w n).2.2.1 f hLR', rfl⟩
  rcases hv with hw | ht
  · exact Or.inr (hw ▸ hwest e he)
  · obtain ⟨a, b, hab⟩ := List.mem_iff_append.mp he
    cases b with
    | nil =>
      have he0 : e = 0 := by
        have hlast : (s.LL ++ s.LR).getLast? = some 0 := by
          rw [hLR]
          simp [List.getLast?_append]
        rw [hab] at hlast
        simpa [List.getLast?_append] using hlast
      have heb : e < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
        (by simp only [List.mem_append] at he ⊢; tauto)
      have hend := (edge_endpoints_eq w heb).2
      left
      rw [← ht, hend, he0]
      rfl
    | cons f b =>
      have hchain := (kmswStage_boundary_chain_invariant w n).2.1
      change List.IsChain (fun x y => s.east x = s.west y) (s.LL ++ s.LR) at hchain
      rw [hab] at hchain
      have hrel : s.east e = s.west f := hchain.right_of_append.rel_head? (by simp)
      have hf : f ∈ s.LL ++ s.LR := by rw [hab]; simp
      obtain ⟨g, hg, hgp, hgw⟩ := hwest f hf
      exact Or.inr ⟨g, hg, hgp, hgw.trans (hrel.symm.trans ht)⟩

/-- Under the one-sided past bound, vertex 1 is never the west endpoint of a
geometric edge. The strict rank inequality rules out even missing edges. -/
private theorem uibhbotCcw_past_west_ne_one (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (n e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) n).nextEdge) :
    (kmswStage (kmswPastCode W) n).west e ≠ 1 := by
  intro hw
  let P := uibhbotPastMonotoneDrawing W hfin
  have hends := kmswStage_endpoints_lt_nextVertex (kmswPastCode W) n e he
  have hwp := uibhbotPastMonotoneDrawing_pos_layout W hfin n _ hends.1
  have hep := uibhbotPastMonotoneDrawing_pos_layout W hfin n _ hends.2
  have hone := uibhbotPastMonotoneDrawing_pos_layout W hfin 0 1 (by change 1 < 2; omega)
  have hstrict := kmswStageRank_strict (kmswPastCode W) n e he
  have hstrict' : (P.pos ((kmswStage (kmswPastCode W) n).west e)).re <
      (P.pos ((kmswStage (kmswPastCode W) n).east e)).re := by
    rw [hwp, hep]
    change (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).west e) : ℝ) <
      (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).east e) : ℝ)
    exact_mod_cast hstrict
  rw [hw, hone] at hstrict'
  norm_num [kmswStageRank] at hstrict'
  have hle := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR
    (Or.inl ⟨(kmswStage (kmswPastCode W) n).east e, rfl⟩)
  exact (not_lt_of_ge hle) hstrict'

/-- Every retained past dart based at a shared vertex lies on a recorded triangle.
Only the left coordinate is unbounded below; the right coordinate is bounded
below as in the conditioned law. No past boundary-hit witness is used. -/
theorem uibhbotCcw_shared_past_triangle (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∈
      range (wholePlaneVertexι W 0))
    (hd : ¬ kmswPastSeamEdge W d.1) :
    ∃ j : TriangleCreationTime (kmswPastCode W), d ∈ stageTriangleDartList (kmswPastCode W) j := by
  let w := kmswPastCode W
  rcases run_outer_or_triangle w d with ⟨N, hN⟩ | ⟨j, hj, _⟩
  · obtain ⟨n, e, he, hev⟩ := uibhbotGlue_shared_vertex_mem_seam W _ hv
    have hLu : ∀ a : ℤ, ∃ n, L w n ≤ a := by
      intro a
      obtain ⟨n, hn⟩ := hL (min a (-1)) (min_le_right _ _)
      exact ⟨n, hn.le.trans (min_le_left _ _)⟩
    obtain ⟨M, hM⟩ := kmswRun_UL_eventually_absent w hLu d.1
    let m := max n (max N M)
    have hnm : n ≤ m := Nat.le_max_left _ _
    have hNm : N ≤ m := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hMm : M ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    rcases (run_outer_mem_iff w m d).mp (hN m hNm) with ⟨hb, hu | hu⟩ | ⟨_, hl | hl⟩
    · exact (hM m hMm hu).elim
    · have hdb := (kmswStage_boundary_ids_lt_nextEdge w m).2 d.1
        (by simp only [List.mem_append]; tauto)
      have hwest : (kmswStage w m).west d.1 = kmswLimitDartVertex w d := by
        rw [(edge_endpoints_eq w hdb).1]
        simp only [kmswLimitDartVertex, hb, Bool.false_eq_true, ite_false]
      rcases uibhbotCcw_lower_endpoint_present_or_one W hR n e _ he hev with h1 | ⟨f, hf, hp, hw⟩
      · exact (uibhbotCcw_past_west_ne_one W hR hfin m d.1 hdb (hwest.trans h1)).elim
      · obtain ⟨hfm, hpm⟩ := present_mono w hf hp m hnm
        apply False.elim
        apply stageOutgoing_UR_west_empty w m d.1 hu f hfm hpm
        exact ((kmswStage_endpoints_stable w hnm hf).1.trans hw).trans hwest.symm
    · exact (hd ⟨m, List.mem_append_right _ hl⟩).elim
    · exact (hd ⟨m, List.mem_append_left _ hl⟩).elim
  · exact ⟨j, hj⟩

/-- A past triangle dart has its actual rotation successor in the whole-plane
map. The predecessor triangle dart supplies the face-successor calculation. -/
private theorem uibhbotCcw_rotation_past_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (kmswPastCode W),
      d ∈ stageTriangleDartList (kmswPastCode W) j) :
    wholePlaneRotation W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfRot (kmswPastCode W) hfin d) := by
  classical
  obtain ⟨j, hj⟩ := hd
  let a := (stageTriangleDartList (kmswPastCode W) j).formPerm.symm d
  have ha : a ∈ stageTriangleDartList (kmswPastCode W) j := by
    apply List.mem_of_formPerm_apply_mem
    rw [Equiv.apply_symm_apply]
    exact hj
  have hfa : kmswInfFaceSucc (kmswPastCode W) hfin a = d :=
    (pastFace_inf_triangle (kmswPastCode W) hfin j a ha).trans
      ((stageTriangleDartList (kmswPastCode W) j).formPerm.apply_symm_apply d)
  have hflip : (a.1, !a.2) = kmswInfRot (kmswPastCode W) hfin d := by
    have h := congrArg (kmswInfRot (kmswPastCode W) hfin) hfa
    exact (Equiv.apply_symm_apply _ _).symm.trans h
  have hf : wholePlaneFaceSucc W H (kmswPastDart W a) = kmswPastDart W d :=
    (kmswPastDart_faceSucc_of_triangle W H hfin a ⟨j, ha⟩).trans
      (congrArg (kmswPastDart W) hfa)
  have h := congrArg (wholePlaneRotation W H) hf
  change wholePlaneRotation W H ((wholePlaneRotation W H).symm
    (wholePlaneDartFlip W (kmswPastDart W a))) = _ at h
  rw [Equiv.apply_symm_apply, WholePlanePastGlueData.pastDart_flip, hflip] at h
  exact h.symm

/-- The whole-plane rotation at every retained past dart on the shared seam is
the past rotation. This is proved with one-sided hypotheses only. -/
theorem uibhbotCcw_rotation_past_shared_nonseam (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∈
      range (wholePlaneVertexι W 0)) (hd : ¬ kmswPastSeamEdge W d.1) :
    wholePlaneRotation W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfRot (kmswPastCode W) hfin d) :=
  uibhbotCcw_rotation_past_triangle W H hfin d
    (uibhbotCcw_shared_past_triangle W hL hR hfin d hv hd)

/-- Replacing a covered past seam arc by its future representative preserves
the initial argument after the attachment half-turn. -/
private theorem uibhbotCcw_past_seam_arg (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))
    (hFp : ∀ k : ℤ, F.pos (boundaryVertex (shiftedStream W 0) h0 k) = ⟨-(k : ℝ), 0⟩)
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0) (monotone_family_all _)).arc d).image)
    (d : ℕ × Bool) (hd : kmswPastSeamEdge W d.1) :
    Complex.arg (uibhbotAssemblyArc W
      (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
      (kmswPastDart W d)).initialDirection =
    Complex.arg (Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)).initialDirection := by
  obtain ⟨n, hn⟩ := hd
  obtain ⟨j, _, hje, hjw, hjt⟩ := uibhbotGlue_past_seam_match W h0 hR n d.1 hn
  have he := (kmswStage_boundary_ids_lt_nextEdge (kmswPastCode W) n).2 d.1 (by
    simp only [List.mem_append] at hn ⊢; tauto)
  let P0 := uibhbotPastMonotoneDrawing W hfin
  let q := Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)
  have hbounds : ∀ z ∈ q.image,
      -((j : ℝ) + 1) ≤ z.re ∧ z.re ≤ -(j : ℝ) ∧ z.im = 0 := by
    intro z hz
    rw [Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [ha] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : x ∈ (P0.arc (d.1, false)).image := by
      cases hb : d.2 with
      | false => simpa only [← hb] using hx
      | true =>
        have hr := P0.arc_flip (d.1, false)
        change P0.arc (d.1, true) = (P0.arc (d.1, false)).reverse at hr
        have hx'' : x ∈ (P0.arc (d.1, true)).image := by simpa only [← hb] using hx
        rwa [hr, Polyline.image_reverse_transfer] at hx''
    have hseam := uibhbotPastSeamHeight_eq_of_mem W hL hR
      (uibhbotPastMonotoneDrawing_lower_arc_subset W hfin n d.1 hn hx')
    rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n d.1 he false] at hx'
    simp only [Bool.false_eq_true, ite_false] at hx'
    obtain ⟨g, hg⟩ := layoutArc_image_graph (kmswPastCode W) n d.1 he
    rw [hg] at hx'
    change (kmswStageRank (kmswPastCode W) n
      ((kmswStage (kmswPastCode W) n).west d.1) : ℝ) ≤ x.re ∧
      x.re ≤ (kmswStageRank (kmswPastCode W) n
        ((kmswStage (kmswPastCode W) n).east d.1) : ℝ) ∧ _ at hx'
    rw [hjw, hjt] at hx'
    push_cast at hx'
    change -((j : ℝ) + 1) ≤ -(-x.re) - 1 ∧ -(-x.re) - 1 ≤ -(j : ℝ) ∧
      -(-x.im + 0 + uibhbotPastSeamHeight W hL hR x.re) - 0 = 0
    refine ⟨by linarith only [hx'.1], by linarith only [hx'.2.1], ?_⟩
    rw [← hseam]
    ring
  have hpos : uibhbotAssemblyHalfTurn ∘ P.pos = uibhbotSeparationPastPos W hL hR hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hends := uibhbotSeparation_past_lower_pos W hL hR hfin n d.1 hn
  rw [hjw, hjt] at hends
  have hstart : q.start = if d.2 then (⟨-(j : ℝ), 0⟩ : ℂ)
      else ⟨-((j : ℝ) + 1), 0⟩ := by
    rw [Polyline.start_mapPoints, P.arc_start]
    change (uibhbotAssemblyHalfTurn ∘ P.pos) (kmswLimitDartVertex _ d) = _
    rw [hpos]
    have hend := edge_endpoints_eq (kmswPastCode W) he
    cases hb : d.2 <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true,
      kmswLimitDartVertex, ← hend.1, ← hend.2] <;>
      simp only [hends.1, hends.2] <;> push_cast <;>
      apply Complex.ext <;> dsimp <;> ring
  have hqmem := q.point_mem_image (i := 1) (by
    have hlen : 2 ≤ q.points.length := by
      simpa only [q, Polyline.mapPoints, List.length_map] using P.arc_length d
    omega)
  have hqb := hbounds _ hqmem
  have hqim : q.initialDirection.im = 0 := by
    simp only [Polyline.initialDirection, Complex.sub_im, hstart]
    split_ifs <;> exact sub_eq_zero.mpr hqb.2.2
  have hqn : q.initialDirection ≠ 0 := by
    rw [uibhbotCcw_halfTurn_initial]
    exact neg_ne_zero.mpr (P.initial_nonzero d)
  have hD : kmswPastDart W d = wholePlaneDartι W 0
      (boundaryOuterEdge (shiftedStream W 0) h0 j, !d.2) := by
    apply Prod.ext hje
    rfl
  rw [hD, uibhbotAssemblyArc_future]
  have hargs := uibhbotCcw_future_boundary_args (shiftedStream W 0) h0 (H.1 0) F hFp hFa
  cases hb : d.2 with
  | false =>
    have hre : 0 ≤ q.initialDirection.re := by
      simp only [Polyline.initialDirection, Complex.sub_re, hstart, hb,
        Bool.false_eq_true, ite_false]
      linarith only [hqb.1]
    have hright := (hargs (j + 1)).2
    rw [add_sub_cancel_right] at hright
    change Complex.arg (F.arc (boundaryOuterEdge (shiftedStream W 0) h0 j, true)).initialDirection = _
    rw [hright, Complex.arg_eq_zero_iff.mpr ⟨hre, hqim⟩]
  | true =>
    have hre : q.initialDirection.re < 0 := by
      apply lt_of_le_of_ne
      · simp only [Polyline.initialDirection, Complex.sub_re, hstart, hb, ite_true]
        linarith only [hqb.2.1]
      · intro hz
        exact hqn (Complex.ext hz hqim)
    change Complex.arg (F.arc (boundaryOuterEdge (shiftedStream W 0) h0 j, false)).initialDirection = _
    rw [(hargs j).1, Complex.arg_eq_pi_iff.mpr ⟨hre, hqim⟩]

/-- An injective dart map transports successors when initial arguments agree. -/
private theorem uibhbotCcw_successor_image_arg {A B : Type*} (i : A → B)
    (hi : Function.Injective i) (S : Set A) (dir : A → ℂ) (dir' : B → ℂ)
    (harg : ∀ a ∈ S, Complex.arg (dir' (i a)) = Complex.arg (dir a))
    (d e : A) (hs : CcwSuccessor S dir d e) :
    CcwSuccessor (i '' S) dir' (i d) (i e) := by
  obtain ⟨hfin, hd, he, hcase⟩ := hs
  refine ⟨hfin.image i, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · exact Or.inl ⟨congrArg i heq, by rw [hsingle, Set.image_singleton]⟩
  · refine Or.inr ⟨fun h => hne (hi h), ?_⟩
    rintro _ ⟨f, hf, rfl⟩ hfd
    unfold ccwTurn
    rw [harg d hd, harg e he, harg f hf]
    exact hmin f hf (fun h => hfd (congrArg i h))

/-- Adding lower directions preserves a successor based strictly above the axis
when the left horizontal anchor is already in the smaller star. -/
private theorem uibhbotCcw_upper_extend {D : Type*} (S T : Set D) (dir : D → ℂ)
    (hfin : S.Finite) (hsub : T ⊆ S)
    (harg : ∀ x y, x ∈ S → y ∈ S →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (l d e : D) (hl : l ∈ T) (hal : Complex.arg (dir l) = Real.pi)
    (hdim : 0 < (dir d).im)
    (hlo : ∀ f ∈ S, f ∉ T → (dir f).im ≤ 0)
    (hs : CcwSuccessor T dir d e) : CcwSuccessor S dir d e := by
  have hda : 0 < Complex.arg (dir d) := by
    apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hdim.le)
    intro hz
    exact hdim.ne' (Complex.arg_eq_zero_iff.mp hz.symm).2
  have hdpi : Complex.arg (dir d) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hdim.ne')
  have hld : l ≠ d := by intro he; rw [he] at hal; linarith only [hdpi, hal]
  have hnot : T ≠ {d} := by
    intro he
    exact hld (by simpa only [he, mem_singleton_iff] using hl)
  have hm := hs.2.2.2.resolve_left (fun h => hnot h.2)
  refine ⟨hfin, hsub hs.2.1, hsub hs.2.2.1, Or.inr ⟨hm.1, ?_⟩⟩
  intro f hf hfd
  by_cases hft : f ∈ T
  · exact hm.2 f hft hfd
  · have hle := hm.2 l hl hld
    have haf : Complex.arg (dir f) ≤ 0 := by
      have hi := hlo f hf hft
      rcases lt_or_eq_of_le hi with hi | hi
      · exact (Complex.arg_neg_iff.mpr hi).le
      · rcases lt_or_ge (dir f).re 0 with hre | hre
        · have hfl : f = l := harg f l hf (hsub hl)
            ((Complex.arg_eq_pi_iff.mpr ⟨hre, hi⟩).trans hal.symm)
          exact (hft (hfl ▸ hl)).elim
        · exact (Complex.arg_eq_zero_iff.mpr ⟨hre, hi⟩).le
    have hafbound := Complex.arg_mem_Ioc (dir f)
    have hfar : ccwTurn (dir d) (dir l) < ccwTurn (dir d) (dir f) := by
      simp only [ccwTurn, hal, ite_eq_left hdpi, ite_eq_right (not_lt_of_ge (haf.trans hda.le))]
      linarith only [hafbound.1]
    exact hle.trans hfar.le

/-- Distinct directions in a finite star give a unique predecessor for each
counterclockwise successor. -/
private theorem uibhbotCcw_successor_predecessor_unique {D : Type*}
    (S : Set D) (dir : D → ℂ)
    (harg : ∀ x y, x ∈ S → y ∈ S →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (d q e : D) (hd : CcwSuccessor S dir d e) (hq : CcwSuccessor S dir q e) : d = q := by
  by_contra hdq
  rcases hd.2.2.2 with ⟨_, hs⟩ | ⟨hed, hminD⟩
  · have hqd : q = d := by simpa only [hs, mem_singleton_iff] using hq.2.1
    exact hdq hqd.symm
  rcases hq.2.2.2 with ⟨_, hs⟩ | ⟨heq, hminQ⟩
  · have hdq' : d = q := by simpa only [hs, mem_singleton_iff] using hd.2.1
    exact hdq hdq'
  have hD : ccwTurn (dir d) (dir e) < ccwTurn (dir d) (dir q) := by
    apply lt_of_le_of_ne (hminD q hq.2.1 (Ne.symm hdq))
    intro he
    exact heq (harg e q hd.2.2.1 hq.2.1 (ccwTurn_left_injective he))
  have hQ : ccwTurn (dir q) (dir e) < ccwTurn (dir q) (dir d) := by
    apply lt_of_le_of_ne (hminQ d hd.2.1 hdq)
    intro he
    exact hed (harg e d hd.2.2.1 hd.2.1 (ccwTurn_left_injective he))
  have hDE := ccwTurn_add_reverse (dir d) (dir e)
    (fun he => hed (harg d e hd.2.1 hd.2.2.1 he).symm)
  have hQE := ccwTurn_add_reverse (dir q) (dir e)
    (fun he => heq (harg q e hq.2.1 hq.2.2.1 he).symm)
  have hDQ := ccwTurn_add_reverse (dir d) (dir q)
    (fun he => hdq (harg d q hd.2.1 hq.2.1 he))
  have hcD := ccwTurn_comp_add hD
  have hcQ := ccwTurn_comp_add hQ
  linarith only [hDE, hQE, hDQ, hcD, hcQ, Real.pi_pos]

/-- A permutation of a finite star with all but one angular successor proved has
the last successor as well. This closes a one-sided seam endpoint without an
invented past right anchor. -/
private theorem uibhbotCcw_last_successor {D : Type*} (S : Set D) (dir : D → ℂ)
    (rot : Equiv.Perm D) (hfin : S.Finite)
    (harg : ∀ x y, x ∈ S → y ∈ S →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (_hrot : ∀ x ∈ S, rot x ∈ S) (hsymm : ∀ x ∈ S, rot.symm x ∈ S)
    (r l : D) (hr : r ∈ S) (hl : l ∈ S) (hlr : l ≠ r)
    (hs : ∀ d ∈ S, d ≠ r → CcwSuccessor S dir d (rot d)) :
    CcwSuccessor S dir r (rot r) := by
  classical
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image (S \ {r})
    (fun e => ccwTurn (dir r) (dir e)) hfin.sdiff ⟨l, hl, hlr⟩
  have her : e ≠ r := he.2
  have hnext : CcwSuccessor S dir r e :=
    ⟨hfin, hr, he.1, Or.inr ⟨her, fun f hf hfr => hmin f ⟨hf, hfr⟩⟩⟩
  have hq : rot.symm e = r := by
    by_contra hn
    have hqnext := hs (rot.symm e) (hsymm e he.1) hn
    rw [Equiv.apply_symm_apply] at hqnext
    exact hn (uibhbotCcw_successor_predecessor_unique S dir harg r (rot.symm e) e hnext hqnext).symm
  have heq : e = rot r := by rw [← hq, Equiv.apply_symm_apply]
  exact heq ▸ hnext

/-- Every nonnegative future boundary edge has a past seam representative. The
midpoint of its unit horizontal interval locates it in the one-sided graph. -/
theorem uibhbotCcw_nonneg_boundary_in_past (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) (k : ℤ) (hk : 0 ≤ k) :
    ∃ e, kmswPastSeamEdge W e ∧
      kmswPastEdge W e = wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k) := by
  let x : ℝ := 1 / 2 - (k : ℝ)
  have hx : x ≤ 1 := by
    have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [x]
    linarith only [hk']
  obtain ⟨y, hy⟩ := (uibhbotPastSeamGraph_domain W hL hR x).mpr hx
  obtain ⟨e, ⟨n, hn⟩, he⟩ := uibhbotPastSeamGraph_mem_arc W hfin hy
  obtain ⟨j, _, hje, hjw, hjt⟩ := uibhbotGlue_past_seam_match W h0 hR n e hn
  have heb := (kmswStage_boundary_ids_lt_nextEdge (kmswPastCode W) n).2 e (by
    simp only [List.mem_append] at hn ⊢; tauto)
  rw [uibhbotPastMonotoneDrawing_arc_layout W hfin n e heb false] at he
  simp only [Bool.false_eq_true, ite_false] at he
  obtain ⟨g, hg⟩ := layoutArc_image_graph (kmswPastCode W) n e heb
  rw [hg] at he
  change (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).west e) : ℝ) ≤ x ∧
    x ≤ (kmswStageRank (kmswPastCode W) n ((kmswStage (kmswPastCode W) n).east e) : ℝ) ∧ _ at he
  rw [hjw, hjt] at he
  push_cast at he
  have hlo : (k : ℝ) - 1 < j := by dsimp only [x] at he; linarith only [he.1]
  have hhi : (j : ℝ) < (k : ℝ) + 1 := by dsimp only [x] at he; linarith only [he.2.1]
  have hlo' : k - 1 < j := by exact_mod_cast hlo
  have hhi' : j < k + 1 := by exact_mod_cast hhi
  have hjk : j = k := by omega
  exact ⟨e, ⟨n, hn⟩, hjk ▸ hje⟩

/-- G4b at every retained past dart based at a shared vertex. Seam argument
transport and the existing left anchor handle the endpoint as well. -/
theorem uibhbotCcw_assembly_rotation_shared_past (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))
    (hf : F.pos = uibhbotSeparationFuturePos W H h0)
    (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0) (monotone_family_all _)).arc d).image)
    (d : ℕ × Bool)
    (hv : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∈ range (wholePlaneVertexι W 0))
    (hd : ¬ kmswPastSeamEdge W d.1) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W (kmswPastDart W d)}
      (fun E => (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc E).initialDirection)
      (kmswPastDart W d) (wholePlaneRotation W H (kmswPastDart W d)) := by
  let v := kmswLimitDartVertex (kmswPastCode W) d
  obtain ⟨u, hu⟩ := hv
  obtain ⟨k, hk, huk⟩ := uibhbotCcw_shared_label_nonneg W h0 hR u v hu
  have huv : wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k) =
      kmswPastVertex W v := by rw [← huk]; exact hu
  let S := {E | wholePlaneDartVertex W E = wholePlaneDartVertex W (kmswPastDart W d)}
  let T := kmswPastDart W '' {e | kmswLimitDartVertex (kmswPastCode W) e = v}
  let arc := uibhbotAssemblyArc W
    (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
  let dir := fun E => (arc E).initialDirection
  let l := wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, false)
  have hFp (j : ℤ) : F.pos (boundaryVertex (shiftedStream W 0) h0 j) = ⟨-(j : ℝ), 0⟩ := by
    rw [hf, uibhbotSeparation_future_boundary_pos]
  have hargpast (e : ℕ × Bool) :
      Complex.arg (dir (kmswPastDart W e)) =
        Complex.arg (-(P.arc e).initialDirection) := by
    by_cases he : kmswPastSeamEdge W e.1
    · exact (uibhbotCcw_past_seam_arg W H h0 hL hR hfin P hp ha F hFp hFa e he).trans
        (congrArg Complex.arg (uibhbotCcw_halfTurn_initial (P.arc e)))
    · dsimp only [dir, arc]
      rw [uibhbotAssemblyArc_past W h0 _ _ e he, uibhbotCcw_halfTurn_initial]
  have hs : CcwSuccessor {e | kmswLimitDartVertex (kmswPastCode W) e = v}
      (fun e => -(P.arc e).initialDirection) d (kmswInfRot (kmswPastCode W) hfin d) := by
    obtain ⟨hfin', hd', hr, hcase⟩ := P.rotation_agreement d
    refine ⟨hfin', hd', hr, ?_⟩
    rcases hcase with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · refine Or.inr ⟨hne, ?_⟩
      intro e he hed
      rw [uibhbotCcw_turn_neg _ _ (P.initial_nonzero d) (P.initial_nonzero _),
        uibhbotCcw_turn_neg _ _ (P.initial_nonzero d) (P.initial_nonzero e)]
      exact hmin e he hed
  have hs' : CcwSuccessor T dir (kmswPastDart W d)
      (kmswPastDart W (kmswInfRot (kmswPastCode W) hfin d)) :=
    uibhbotCcw_successor_image_arg _ (kmswPastDart_injective W) _ _ dir
      (fun e _ => hargpast e) d _ hs
  have hsub : T ⊆ S := by
    rintro _ ⟨e, he, rfl⟩
    change wholePlaneDartVertex W (kmswPastDart W e) = wholePlaneDartVertex W (kmswPastDart W d)
    rw [WholePlanePastGlueData.pastDart_vertex, WholePlanePastGlueData.pastDart_vertex, he]
  obtain ⟨e, _, he⟩ := uibhbotCcw_nonneg_boundary_in_past W h0 hL hR hfin k hk
  have hlrep : kmswPastDart W (e, true) = l := Prod.ext he rfl
  have hlv : wholePlaneDartVertex W l = kmswPastVertex W v := by
    dsimp only [l]
    rw [wholePlaneDartVertex_ι]
    exact (congrArg (wholePlaneVertexι W 0)
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 k).1).trans huv
  have hl : l ∈ T := by
    refine ⟨(e, true), ?_, hlrep⟩
    apply kmswPastVertex_injective W
    exact (WholePlanePastGlueData.pastDart_vertex W (e, true)).symm.trans
      ((congrArg (wholePlaneDartVertex W) hlrep).trans hlv)
  have hal : Complex.arg (dir l) = Real.pi := by
    dsimp only [dir, arc, l]
    rw [uibhbotAssemblyArc_future]
    exact (uibhbotCcw_future_boundary_args (shiftedStream W 0) h0 (H.1 0) F hFp hFa k).1
  have harg : ∀ x y, x ∈ S → y ∈ S →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y := by
    intro x y hx hy he
    exact uibhbotCcw_assembly_arg_injective W H h0 hL hR hfin P hp ha F hf hFim x y
      (hx.trans hy.symm) he
  have hdim : 0 < (dir (kmswPastDart W d)).im :=
    uibhbotCcw_shared_past_direction_pos W H h0 hL hR hfin P hp ha F.arc u v hu d rfl hd
  have hlo : ∀ f ∈ S, f ∉ T → (dir f).im ≤ 0 := by
    intro f hfs hft
    rcases WholePlanePastGlueData.dart_cover W f with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have hav : kmswLimitDartVertex (shiftedStream W 0) a = boundaryVertex (shiftedStream W 0) h0 k := by
        apply wholePlaneVertexι_injective W 0
        exact (wholePlaneDartVertex_ι W 0 a).symm.trans
          (hfs.trans ((WholePlanePastGlueData.pastDart_vertex W d).trans huv.symm))
      exact uibhbotCcw_shared_future_direction_nonpos W H h0 F hFim hFp _ k a hav
    · exfalso
      apply hft
      refine ⟨a, ?_, rfl⟩
      apply kmswPastVertex_injective W
      exact (WholePlanePastGlueData.pastDart_vertex W a).symm.trans
        (hfs.trans (WholePlanePastGlueData.pastDart_vertex W d))
  rw [uibhbotCcw_rotation_past_shared_nonseam W H hL hR hfin d ⟨u, hu⟩ hd]
  exact uibhbotCcw_upper_extend S T dir (wholePlaneStar_finite W H _) hsub harg
    l _ _ hl hal hdim hlo hs'

section Shared

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘ (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0)) (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0) (monotone_family_all _)).arc d).image)

local notation "arc" => uibhbotAssemblyArc W
  (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc

include hp ha hf hFim hFa in
/-- G4b at every shared seam dart. The endpoint is closed by finite-star
permutation uniqueness, using no fictitious past right boundary dart. -/
theorem uibhbotCcw_assembly_rotation_shared (D : WholePlaneDart W)
    (hv : wholePlaneDartVertex W D ∈ range (wholePlaneVertexι W 0) ∩ range (kmswPastVertex W)) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
      (fun E => (arc E).initialDirection) D (wholePlaneRotation W H D) := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hv
  have huv := hu.trans hv.symm
  obtain ⟨k, _, huk⟩ := uibhbotCcw_shared_label_nonneg W h0 hR u v huv
  have hkv : wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k) =
      kmswPastVertex W v := by rw [← huk]; exact huv
  let S := {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
  let r := wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (k - 1), true)
  let l := wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, false)
  have hDk : wholePlaneDartVertex W D =
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k) := by rw [← huk]; exact hu.symm
  have hmem := WholePlaneGlueSeamStar.runZero_seam_darts_incident W h0 k
  have hr : r ∈ S := by
    change wholePlaneDartVertex W r = wholePlaneDartVertex W D
    rw [wholePlaneDartVertex_ι, hmem.2.2, hDk]
  have hl : l ∈ S := by
    change wholePlaneDartVertex W l = wholePlaneDartVertex W D
    rw [wholePlaneDartVertex_ι, hmem.2.1, hDk]
  have hlr : l ≠ r := fun he => hmem.1 (uibhbotCcw_dart_injective W 0 he)
  have hs : ∀ E ∈ S, E ≠ r →
      CcwSuccessor S (fun E => (arc E).initialDirection) E (wholePlaneRotation W H E) := by
    intro E he her
    have hEk : wholePlaneDartVertex W E =
        wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 k) := he.trans hDk
    have hstar : {A | wholePlaneDartVertex W A = wholePlaneDartVertex W E} = S := by
      ext A
      exact ⟨fun h => h.trans he, fun h => h.trans he.symm⟩
    rw [← hstar]
    rcases WholePlanePastGlueData.dart_cover_off_seam W h0 E with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
    · have hdv := wholePlaneVertexι_injective W 0 ((wholePlaneDartVertex_ι W 0 d).symm.trans hEk)
      exact uibhbotCcw_assembly_rotation_shared_future W H h0 hL hR hfin P hp ha F hf hFim hFa
        k v hkv d hdv (fun h => her (congrArg (wholePlaneDartι W 0) h))
    · have hshared : kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) ∈
          range (wholePlaneVertexι W 0) :=
        ⟨_, hEk.symm.trans (WholePlanePastGlueData.pastDart_vertex W d)⟩
      exact uibhbotCcw_assembly_rotation_shared_past W H h0 hL hR hfin P hp ha F hf hFim hFa
        d hshared hd
  have harg : ∀ x y, x ∈ S → y ∈ S →
      Complex.arg (arc x).initialDirection = Complex.arg (arc y).initialDirection → x = y := by
    intro x y hx hy he
    exact uibhbotCcw_assembly_arg_injective W H h0 hL hR hfin P hp ha F hf hFim x y
      (hx.trans hy.symm) he
  have hrot : ∀ E ∈ S, wholePlaneRotation W H E ∈ S := by
    intro E he
    exact (wholePlaneRotation_preserves_dartVertex W H E).trans he
  have hsymm : ∀ E ∈ S, (wholePlaneRotation W H).symm E ∈ S := by
    intro E he
    have h := wholePlaneRotation_preserves_dartVertex W H ((wholePlaneRotation W H).symm E)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans he
  by_cases hDr : D = r
  · have hlast := uibhbotCcw_last_successor S (fun E => (arc E).initialDirection)
      (wholePlaneRotation W H) (wholePlaneStar_finite W H _) harg hrot hsymm r l hr hl hlr hs
    simpa only [S, hDr] using hlast
  · exact hs D rfl hDr

include hp ha hf hFim hFa in
/-- G4b for all darts of the concrete one-sided candidate assembly, combining
the shared seam proof with the unchanged unshared-vertex proof. -/
theorem uibhbotCcw_assembly_rotation (D : WholePlaneDart W) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
      (fun E => (arc E).initialDirection) D (wholePlaneRotation W H D) := by
  by_cases hv : wholePlaneDartVertex W D ∈ range (wholePlaneVertexι W 0) ∩ range (kmswPastVertex W)
  · exact uibhbotCcw_assembly_rotation_shared W H h0 hL hR hfin P hp ha F hf hFim hFa D hv
  · exact uibhbotCcw_assembly_rotation_unshared W H h0 hfin P F D hv

include hp ha hf hFim hFa in
/-- The actual PL drawing obtained from the one-sided candidate. Every field,
including whole-plane cyclic order, is supplied by a proved geometric lemma. -/
@[expose] def uibhbotCcw_assemblyDrawing : WholePlaneDrawing W H := by
  have hp' : uibhbotAssemblyHalfTurn ∘ P.pos = uibhbotSeparationPastPos W hL hR hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    change F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v
    rw [hp', hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR hfin u v huv
  refine {
    flip_involutive := wholePlaneDartFlip_involutive W
    flip_ne := wholePlaneDartFlip_ne W
    vert_rotation := wholePlaneRotation_preserves_dartVertex W H
    pos := uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos
    pos_injective := ?_
    «arc» := uibhbotAssemblyArc W
      (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
    arc_simple := uibhbotAssemblyArc_simple W H hfin P F
    arc_length := uibhbotAssemblyArc_length W H hfin P F
    arc_start := uibhbotAssemblyArc_start W H hfin P F h0 hc
    arc_finish := uibhbotAssemblyArc_finish W H hfin P F h0 hc
    arc_flip := uibhbotAssemblyArc_flip W H hfin P F
    interior_disjoint := uibhbotInteriors_assembly_interior_disjoint W hL hR hfin P hp ha H h0 F hFim
    interior_avoids_vertices :=
      uibhbotRotation_assembly_interior_avoids_vertices W H h0 hL hR hfin P hp ha F hf hFim
    locally_finite := uibhbotAssemblyArc_locally_finite W H hfin P F h0
    initial_nonzero := ?_
    initial_arg_injective := uibhbotCcw_assembly_arg_injective W H h0 hL hR hfin P hp ha F hf hFim
    rotation_agreement := uibhbotCcw_assembly_rotation W H h0 hL hR hfin P hp ha F hf hFim hFa }
  · rw [hp', hf]
    exact uibhbotSeparation_assembly_pos_injective W H h0 hL hR hfin
  · intro D hz
    apply (uibhbotAssemblyArc_simple W H hfin P F D).1 0
      (by have := uibhbotAssemblyArc_length W H hfin P F D; omega)
    rw [Polyline.point_zero_eq_start]
    exact (sub_eq_zero.mp hz).symm

include hp ha hf hFim hFa in
/-- The assembled drawing retains exactly the candidate vertex positions. -/
theorem uibhbotCcw_assemblyDrawing_pos :
    (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).pos =
      uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos := rfl

include hp ha hf hFim hFa in
/-- The assembled drawing retains exactly the candidate geometric arcs. -/
theorem uibhbotCcw_assemblyDrawing_arc :
    (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).arc = arc := rfl

end Shared

/-- Almost surely the concrete assembly is a whole-plane PL drawing, with image
in the complement of the open first quadrant. The entire future seam remains
on the real axis. Flattening the remaining missing boundary is not asserted. -/
theorem uibhbotCodeLawRel_ae_glueDrawing_wedge :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h0 : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ G : WholePlaneDrawing W H,
        G.image ⊆ {z : ℂ | z.re ≤ 0 ∨ z.im ≤ 0} ∧
        ∀ k : ℤ, ∀ b : Bool,
          (G.arc (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, b))).image
            ⊆ {z : ℂ | z.im = 0} := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses, uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg, uibhbotCodeLawRel_ae_past_finiteIncidence]
    with W hH hhit hL hR hfin
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨P, hPquad, hp, ha⟩ := uibhbotAssembly_past_straightDrawing_quadrant W hL hR.1 hfin
  obtain ⟨F, hFim, hFp, hf', hFa⟩ := uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hf : F.pos = uibhbotSeparationFuturePos W H h0 := by rw [hf']; rfl
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR.1 hfin P hp ha F hf hFim hFa
  have hp' : uibhbotAssemblyHalfTurn ∘ P.pos = uibhbotSeparationPastPos W hL hR.1 hfin := by
    funext v
    rw [Function.comp_apply, hp]
    rfl
  have hc : ∀ u v, wholePlaneVertexι W 0 u = kmswPastVertex W v →
      F.pos u = uibhbotAssemblyHalfTurn (P.pos v) := by
    intro u v huv
    change F.pos u = (uibhbotAssemblyHalfTurn ∘ P.pos) v
    rw [hp', hf]
    exact uibhbotSeparation_positions_compatible W H h0 hL hR.1 hfin u v huv
  refine ⟨H, h0, G, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨V, rfl⟩ | ⟨D, hz⟩
    · change (uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos V).re ≤ 0 ∨
        (uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos V).im ≤ 0
      rcases WholePlanePastGlueData.vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · rw [uibhbotAssemblyPos_future]
        exact Or.inr (hFim (Or.inl ⟨v, rfl⟩))
      · rw [uibhbotAssemblyPos_past W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos hc]
        have hx := (hPquad (Or.inl ⟨v, rfl⟩)).2
        left
        change -(P.pos v).re - 1 ≤ 0
        linarith only [hx]
    · change z ∈ (uibhbotAssemblyArc W
        (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc D).image at hz
      rcases WholePlanePastGlueData.dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
      · rw [uibhbotAssemblyArc_future] at hz
        exact Or.inr (hFim (Or.inr ⟨d, hz⟩))
      · rw [uibhbotAssemblyArc_past W h0 _ _ d hd,
          Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        have hx := (hPquad (Or.inr ⟨d, hy⟩)).2
        left
        change -y.re - 1 ≤ 0
        linarith only [hx]
  · intro k b z hz
    change z ∈ (uibhbotAssemblyArc W
      (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc
      (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k, b))).image at hz
    rw [uibhbotAssemblyArc_future] at hz
    exact (uibhbotCcw_future_boundary_bounds (shiftedStream W 0) h0 (H.1 0) F hFa k b hz).2.2

/-! The following obstruction concerns the concrete straightening above, not the
existence of a different half-plane drawing. -/

/-- An off-seam past edge survives as missing exactly when it stays on the past
upper-right boundary at every stage at which it is allocated. -/
theorem uibhbotCcw_missing_past_iff_UR (W : ℤ → Fin 3) (e : ℕ)
    (hs : ¬ kmswPastSeamEdge W e) :
    ¬ wholePlaneEdgePresent W (kmswPastEdge W e) ↔
      ∀ n, e < (kmswStage (kmswPastCode W) n).nextEdge →
        e ∈ (kmswStage (kmswPastCode W) n).UR := by
  constructor
  · intro hm n hn
    have hp : (kmswStage (kmswPastCode W) n).present e = false := by
      cases h : (kmswStage (kmswPastCode W) n).present e with
      | false => rfl
      | true => exact (hm (kmswPastEdge_present W e ⟨n, hn, h⟩)).elim
    exact ((kmswStage_missing_iff_UR_or_LL _ n e hn).mp hp).resolve_right
      (fun he => hs ⟨n, List.mem_append_left _ he⟩)
  · intro hu hp
    rcases (kmswPastEdge_present_iff_present_or_LL W e).mp hp with hp | ⟨n, hn, _⟩
    · obtain ⟨n, hn, hp⟩ := hp
      exact kmswStage_UR_LL_not_present _ n e (Or.inl (hu n hn)) hp
    · exact hs ⟨n, List.mem_append_left _ hn⟩

/-- Strict positivity of the past vertical coordinate forces its first up-step. -/
theorem uibhbotCcw_past_first_up (W : ℤ → Fin 3)
    (hRpos : ∀ n, 0 < n → 0 < R (kmswPastCode W) n) :
    kmswPastCode W 0 = 1 := by
  have h := hRpos 1 (by omega)
  have hstep : R (kmswPastCode W) 1 =
      (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (kmswPastCode W 0)).2 := by
    simp only [R, Finset.sum_range_one]
  rw [hstep] at h
  by_cases h0 : kmswPastCode W 0 = 0
  · rw [h0, DirectedDistances.RandomWalk.lazyTwoDimensionalStep_zero] at h
    exact (lt_irrefl 0 h).elim
  by_cases h1 : kmswPastCode W 0 = 1
  · exact h1
  have h2 : kmswPastCode W 0 = 2 := by
    apply Fin.ext
    have hv := (kmswPastCode W 0).isLt
    have hn0 : (kmswPastCode W 0).val ≠ 0 := fun he => h0 (Fin.ext he)
    have hn1 : (kmswPastCode W 0).val ≠ 1 := fun he => h1 (Fin.ext he)
    omega
  rw [h2, DirectedDistances.RandomWalk.lazyTwoDimensionalStep_two] at h
  omega

/-- The first missing past up-edge is outside the glued lower seam. -/
theorem uibhbotCcw_past_two_not_seam (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n) (hc : kmswPastCode W 0 = 1) :
    ¬ kmswPastSeamEdge W 2 := by
  have halloc : (kmswStage (kmswPastCode W) 1).nextEdge = 3 := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit,
      State.addEdge]
  rintro ⟨n, hn⟩
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨s, _, hs, _, he⟩ := kmswStage_LL_exists_revLeftRecord _ n 2 hn
    by_cases hz : s = 0
    · subst s
      rw [hc] at hs
      cases hs
    · have hm := kmswStage_nextEdge_mono (kmswPastCode W) (show 1 ≤ s by omega)
      rw [halloc] at hm
      omega
  · rw [uibhbotPastStage_LR_eq_root W hR n] at hn
    simp only [List.mem_singleton] at hn
    omega

/-- The first past missing edge remains on every positive-stage upper-right boundary. -/
theorem uibhbotCcw_past_two_mem_UR (W : ℤ → Fin 3)
    (hRpos : ∀ n, 0 < n → 0 < R (kmswPastCode W) n) (n : ℕ) (hn : 0 < n) :
    2 ∈ (kmswStage (kmswPastCode W) n).UR := by
  apply kmswRevUpRecord_mem_UR _ n 2 0
  refine ⟨hn, uibhbotCcw_past_first_up W hRpos, ?_, rfl⟩
  intro j hj _
  simpa only [R, Finset.range_zero, Finset.sum_empty] using hRpos j hj

/-- The first missing past up-edge survives as a missing whole-plane edge. -/
theorem uibhbotCcw_past_two_missing (W : ℤ → Fin 3)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hRpos : ∀ n, 0 < n → 0 < R (kmswPastCode W) n) :
    ¬ wholePlaneEdgePresent W (kmswPastEdge W 2) := by
  apply (uibhbotCcw_missing_past_iff_UR W 2
    (uibhbotCcw_past_two_not_seam W hR (uibhbotCcw_past_first_up W hRpos))).mpr
  intro n hn
  apply uibhbotCcw_past_two_mem_UR W hRpos n
  cases n with
  | zero => change 2 < 1 at hn; omega
  | succ n => omega

/-- The original root segment forces the straightening height at its midpoint to zero. -/
theorem uibhbotCcw_past_seamHeight_half (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :
    uibhbotPastSeamHeight W hL hR (1 / 2) = 0 := by
  have hz : (⟨(1 / 2 : ℝ), 0⟩ : ℂ) ∈
      ((uibhbotPastMonotoneDrawing W hfin).arc (0, false)).image := by
    rw [uibhbotPastMonotoneDrawing_arc_layout W hfin 0 0 (by change 0 < 1; omega) false]
    have hzero : layoutPos (kmswPastCode W) 0 0 = 0 := by
      apply Complex.ext <;> norm_num [layoutPos, kmswStageRank, layoutHeight]
    have hone : layoutPos (kmswPastCode W) 0 1 = 1 := by
      apply Complex.ext <;> norm_num [layoutPos, kmswStageRank, layoutHeight]
    simp only [Bool.false_eq_true, ↓reduceIte, layoutArc, hzero, hone]
    rw [segmentArc_image (by norm_num : (0 : ℂ).re < (1 : ℂ).re)]
    norm_num [segmentHeight]
  have hs := uibhbotPastMonotoneDrawing_lower_arc_subset W hfin 0 0
    (by simp [kmswStage, kmswInit]) hz
  exact (uibhbotPastSeamHeight_eq_of_mem W hL hR hs).symm

/-- The first up-step's new vertex is strictly inside the straightened past quadrant,
at `(-1/2,-1)`, rather than on either boundary ray. -/
theorem uibhbotCcw_pastStraight_pos_two (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hc : kmswPastCode W 0 = 1) :
    uibhbotPastStraightTransfer W hL hR ((uibhbotPastMonotoneDrawing W hfin).pos 2) =
      (⟨-(1 / 2 : ℝ), -1⟩ : ℂ) := by
  have hv : 2 < (kmswStage (kmswPastCode W) 1).nextVertex := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  rw [uibhbotPastMonotoneDrawing_pos_layout W hfin 1 2 hv]
  have hpos : (⟨(kmswStageRank (kmswPastCode W) 1 2 : ℝ),
      layoutHeight (kmswPastCode W) 1 2⟩ : ℂ) = ⟨(1 / 2 : ℝ), 1⟩ := by
    norm_num [kmswStageRank, layoutHeight, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, kmswInit, State.addEdge]
  rw [hpos]
  change (⟨-(1 / 2 : ℝ), -1 + 0 + uibhbotPastSeamHeight W hL hR (1 / 2)⟩ : ℂ) = _
  rw [uibhbotCcw_past_seamHeight_half W hL hR hfin]
  norm_num

/-- Every drawing with the prescribed straightened positions retains this endpoint
of the first missing up-edge, strictly away from the quadrant boundary rays. -/
theorem uibhbotCcw_pastStraight_arc_two_contains (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hc : kmswPastCode W 0 = 1)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos) :
    (⟨-(1 / 2 : ℝ), -1⟩ : ℂ) ∈ (P.arc (2, false)).image := by
  have he : 2 < (kmswStage (kmswPastCode W) 1).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  have hv : kmswLimitDartVertex (kmswPastCode W) (2, false) = 2 := by
    change edgeWest (kmswPastCode W) 2 = 2
    rw [← (edge_endpoints_eq (kmswPastCode W) he).1]
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, kmswInit, State.addEdge]
  have hp2 : P.pos 2 = (⟨-(1 / 2 : ℝ), -1⟩ : ℂ) := by
    rw [hp]
    exact uibhbotCcw_pastStraight_pos_two W hL hR hfin hc
  have hstart : (P.arc (2, false)).start = (⟨-(1 / 2 : ℝ), -1⟩ : ℂ) :=
    (P.arc_start (2, false)).trans ((congrArg P.pos hv).trans hp2)
  rw [← hstart]
  exact Or.inl rfl

/-- The concrete past straightening does not place the first missing edge on the
two boundary rays of its quadrant. This refutes the proposed direct G5 route. -/
theorem uibhbotCcw_pastStraight_arc_two_not_rays (W : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hc : kmswPastCode W 0 = 1)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos) :
    ¬ (P.arc (2, false)).image ⊆ {z : ℂ | z.im = 0 ∨ z.re = -1} := by
  intro h
  have hz := h (uibhbotCcw_pastStraight_arc_two_contains W hL hR hfin hc P hp)
  norm_num at hz

/-- After attachment, the surviving first missing past edge has an endpoint at
`(-1/2,1)`, strictly inside the northwest quadrant. -/
theorem uibhbotCcw_assembly_arc_two_contains (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hc : kmswPastCode W 0 = 1)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (f : (ℕ × Bool) → Polyline) :
    (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) ∈
      (uibhbotAssemblyArc W
        (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) f
        (kmswPastEdge W 2, true)).image := by
  change (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) ∈
    (uibhbotAssemblyArc W _ f (kmswPastDart W (2, false))).image
  rw [uibhbotAssemblyArc_past W h0 _ _ (2, false)
    (uibhbotCcw_past_two_not_seam W hR hc),
    Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)]
  refine ⟨_, uibhbotCcw_pastStraight_arc_two_contains W hL hR hfin hc P hp, ?_⟩
  apply Complex.ext <;> norm_num [uibhbotAssemblyHalfTurn]

/-- The wedge map sends the obstructing endpoint to height `1/2`, not to the axis. -/
theorem uibhbotCcw_wedgeMap_obstructing_endpoint :
    uibhbotAssemblyWedgeMap (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) =
      (⟨(3 / 2 : ℝ), 1 / 2⟩ : ℂ) := by
  apply Complex.ext <;> norm_num [uibhbotAssemblyWedgeMap]

/-- Applying the proposed wedge map directly to the concrete candidate fails the
missing-east-arc clause at the first past missing edge. -/
theorem uibhbotCcw_assembly_wedge_arc_two_not_axis (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hc : kmswPastCode W 0 = 1)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (f : (ℕ × Bool) → Polyline) :
    ¬ uibhbotAssemblyWedgeMap ''
      (uibhbotAssemblyArc W
        (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) f
        (kmswPastEdge W 2, true)).image ⊆ {z : ℂ | z.im = 0} := by
  intro h
  have hz := h ⟨_, uibhbotCcw_assembly_arc_two_contains W h0 hL hR hfin hc P hp f, rfl⟩
  rw [uibhbotCcw_wedgeMap_obstructing_endpoint] at hz
  norm_num at hz

/-- Almost surely the actual assembled whole-plane drawing has a surviving missing
east arc containing `(-1/2,1)`. Its direct wedge image therefore fails the
required axis condition. This is an obstruction to this normalization, not to
the existence of a different half-plane drawing. -/
theorem uibhbotCodeLawRel_ae_glueDrawing_direct_wedge_obstruction :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ G : WholePlaneDrawing W H,
        ¬ wholePlaneEdgePresent W (kmswPastEdge W 2) ∧
        (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) ∈ (G.arc (kmswPastEdge W 2, true)).image ∧
        ¬ uibhbotAssemblyWedgeMap '' (G.arc (kmswPastEdge W 2, true)).image ⊆
          {z : ℂ | z.im = 0} := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses, uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg, uibhbotCodeLawRel_ae_past_finiteIncidence]
    with W hH hhit hL hR hfin
  obtain ⟨H, _, _⟩ := hH
  let h0 := hhit 0
  obtain ⟨P, _, hp, ha⟩ := uibhbotAssembly_past_straightDrawing_quadrant W hL hR.1 hfin
  obtain ⟨F, hFim, _, hf', hFa⟩ :=
    uibhbotGlue_future_straightDrawing (shiftedStream W 0) h0 (H.1 0)
  have hf : F.pos = uibhbotSeparationFuturePos W H h0 := by rw [hf']; rfl
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR.1 hfin P hp ha F hf hFim hFa
  have hc := uibhbotCcw_past_first_up W hR.2
  refine ⟨H, G, uibhbotCcw_past_two_missing W hR.1 hR.2, ?_, ?_⟩
  · change (⟨-(1 / 2 : ℝ), 1⟩ : ℂ) ∈
      (uibhbotAssemblyArc W
        (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc
        (kmswPastEdge W 2, true)).image
    exact uibhbotCcw_assembly_arc_two_contains W h0 hL hR.1 hfin hc P hp F.arc
  · change ¬ uibhbotAssemblyWedgeMap ''
      (uibhbotAssemblyArc W
        (fun d => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc d)) F.arc
        (kmswPastEdge W 2, true)).image ⊆ {z : ℂ | z.im = 0}
    exact uibhbotCcw_assembly_wedge_arc_two_not_axis W h0 hL hR.1 hfin hc P hp F.arc

end
end DirectedDistances.KMSW

