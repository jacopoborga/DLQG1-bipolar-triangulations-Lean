/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion5

/-! # Endpoint and exterior obstructions for graph rays

The first ray is upper and the second is lower. Coincident rays are allowed.
The exterior cannot in general be excluded by denying right incidence on
the first ray or left incidence on the second: on the diagonal it touches
both sides. Also, if the upper endpoint is smaller, the strict region has
fibers beyond the common domain. These facts do not identify the selected
belongs to the sole coordinator. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set
open scoped Topology

private theorem intrinsicBetween6_leftAtOn_mono {F U : Set ℂ} (hFU : F ⊆ U)
    {x y : ℂ} {γ : Path x y} {s : {t : unitInterval // t ∈ openParams}}
    (hs : LeftAtOn F γ s) : LeftAtOn U γ s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩ := hs
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, fun t ht => hFU (hq t ht), ?_⟩
  apply closure_mono (s := {w : ℂ | w ∈ F ∧
    HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w 1}) ?_ hcl
  exact fun _ hz => ⟨hFU hz.1, hz.2⟩

/-- Helper toward Proposition 3.9: the complement of a single source
present-ray trace touches either prescribed side of that ray. An ambient
face bordering its first dart supplies all winding tests. -/
theorem intrinsicBetween6_source_trace_compl_touches_side
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) (reverse : Bool) :
    intrinsicRayTouchesSide
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n))
      (intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n)))ᶜ reverse := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  let F := futureMapDartFace W H h (P.edge 0, reverse)
  have hb : M.dartBorders (P.edge 0, reverse) F :=
    (futureMap_dart_face_eq_iff W H h _ _).mp rfl
  have hsub : F.val ⊆ (intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H G hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)))ᶜ := by
    intro z hz ht
    rw [intrinsicGeodesicSource_trace W H G hp] at ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hpast H
      (P.edge n, false)
    change G.arc (wholePlaneDartι W 0 (P.edge n, false)) =
      M.arc (P.edge n, false) at harc
    change z ∈ (G.arc (wholePlaneDartι W 0 (P.edge n, false))).image at hn
    rw [harc] at hn
    exact M.face_subset_compl F hz (Or.inr ⟨(P.edge n, false), hn⟩)
  apply (intrinsicBetween_source_ray_touches_side_iff W H h hpast hp P _ reverse).mpr
  refine ⟨0, ?_⟩
  have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hpast H
    (P.edge 0, reverse)
  change G.arc (wholePlaneDartι W 0 (P.edge 0, reverse)) =
    M.arc (P.edge 0, reverse) at harc
  rw [harc]
  intro s
  exact intrinsicBetween6_leftAtOn_mono hsub
    (M.dartBorders_toPath_leftAtOn
      (kmswLimitDartVertex_surjective _ (H.1 0)) (P.edge 0, reverse) F hb s)

/-- Helper toward Proposition 3.9: on the coincident-ray diagonal,
the exterior of `closedBetween` touches both sides. Thus exterior selection
must use the opposite-side exclusions, rather than deny the two desired
incidences. -/
theorem intrinsicBetween6_source_coincident_exterior_touches_side
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) (reverse : Bool) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let T := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (P.edge n))
    intrinsicRayTouchesSide A (fun n => wholePlaneEdgeι W 0 (P.edge n))
      (closedBetween T T)ᶜ reverse := by
  dsimp only
  rw [intrinsicBetween_closedBetween_self
    (intrinsicBetween_source_trace_properGraphRay W H h hpast hp P)]
  exact intrinsicBetween6_source_trace_compl_touches_side W H h hpast hp P reverse

/-- Helper toward Proposition 3.9: in the full graph-domain case of
`intrinsicBetween4_component_eq_exterior`, the coincident-ray exterior
component satisfies both desired winding incidences. -/
theorem intrinsicBetween6_source_coincident_exterior_component_touches_side
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) (reverse : Bool)
    {x₀ : ℝ} {f : ℝ → ℝ}
    (hgraph : IsGraphRay
      (intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n))) x₀ f)
    (hf : Continuous f)
    {z : ℂ}
    (hz : z ∉ intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n))) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let T := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (P.edge n))
    intrinsicRayTouchesSide A (fun n => wholePlaneEdgeι W 0 (P.edge n))
      (connectedComponentIn (T ∪ T)ᶜ z) reverse := by
  dsimp only
  have hself := intrinsicBetween_closedBetween_self
    (intrinsicBetween_source_trace_properGraphRay W H h hpast hp P)
  have hzext : z ∉ closedBetween
      (intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n)))
      (intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n))) := by
    rw [hself]
    exact hz
  rw [intrinsicBetween4_component_eq_exterior hgraph hgraph hf hf rfl
    (fun _ _ => le_refl _) hzext]
  exact intrinsicBetween6_source_coincident_exterior_touches_side
    W H h hpast hp P reverse

/-- Helper toward Proposition 3.9: beyond the upper ray's finite
endpoint, a strict fiber is an upper half-line, not a finite band over
the common domain. -/
theorem intrinsicBetween6_mem_strictRegion_beyond_upper_endpoint
    {P R : Set ℂ} {x₀ b : ℝ} {XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ (b : WithTop ℝ) ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    {z : ℂ} (hzR : z.re ∈ rayDomain x₀ XR) (hb : b ≤ z.re)
    (hheight : fR z.re < z.im) :
    z ∈ closedBetween P R \ (P ∪ R) ∧
      z.re ∉ rayDomain x₀ (b : WithTop ℝ) := by
  have hnP : z.re ∉ rayDomain x₀ (b : WithTop ℝ) :=
    fun hd => (WithTop.coe_lt_coe.mp hd.2).not_ge hb
  refine ⟨⟨(mem_closedBetween_iff hP hR z).mpr
    ⟨hzR, hheight.le, fun hd => False.elim (hnP hd)⟩, ?_⟩, hnP⟩
  rw [hP, hR]
  rintro (⟨hd, _⟩ | ⟨_, he⟩)
  · exact hnP hd
  · exact hheight.ne' he

/-- Helper toward Proposition 3.9: strictly unequal upper and lower
endpoints force points of the strict region outside the common domain.
This witnesses the missing terminal half-line fibers. -/
theorem intrinsicBetween6_exists_strictRegion_beyond_upper_endpoint
    {P R : Set ℂ} {x₀ b : ℝ} {XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ (b : WithTop ℝ) ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hstart : x₀ < b) (hend : (b : WithTop ℝ) < XR) :
    ∃ z : ℂ, z ∈ closedBetween P R \ (P ∪ R) ∧
      z.re ∉ rayDomain x₀ (b : WithTop ℝ) := by
  refine ⟨⟨b, fR b + 1⟩, ?_⟩
  exact intrinsicBetween6_mem_strictRegion_beyond_upper_endpoint hP hR
    ⟨hstart.le, hend⟩ (le_refl _) (by change fR b < fR b + 1; linarith)

/-- Helper toward Proposition 3.9: for unequal endpoints with the
upper ray ending first, complementary components cannot all be classified
as exterior or subsets of the common-domain fibers. -/
theorem intrinsicBetween6_not_component_cover_common_domain
    {P R : Set ℂ} {x₀ b : ℝ} {XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ (b : WithTop ℝ) ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hstart : x₀ < b) (hend : (b : WithTop ℝ) < XR) :
    ¬ ∀ z : ℂ, z ∉ P ∪ R →
      z ∉ closedBetween P R ∨
        connectedComponentIn (P ∪ R)ᶜ z ⊆
          {q : ℂ | q.re ∈ rayDomain x₀ (b : WithTop ℝ) ∩ rayDomain x₀ XR} := by
  obtain ⟨z, hz, houtside⟩ :=
    intrinsicBetween6_exists_strictRegion_beyond_upper_endpoint hP hR hstart hend
  intro hcover
  rcases hcover z hz.2 with hext | hcommon
  · exact hext hz.1
  · exact houtside (hcommon (mem_connectedComponentIn hz.2)).1








































































end DirectedDistances.PaperProofs.Section3
end
