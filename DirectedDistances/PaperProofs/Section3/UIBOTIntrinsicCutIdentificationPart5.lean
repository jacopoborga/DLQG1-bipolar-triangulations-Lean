/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart4
import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect7
import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides








public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set
open unitInterval

private theorem graph_upper_connected (f : ℝ → ℝ) (hf : Continuous f) :
    IsConnected {z : ℂ | f z.re < z.im} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2 + f p.1⟩
  have hT : Continuous T :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)))
  have heq : T '' ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) =
      {z : ℂ | f z.re < z.im} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨_, hy⟩, rfl⟩
      change f x < y + f x
      exact lt_add_of_pos_left _ hy
    · intro hz
      refine ⟨(z.re, z.im - f z.re), ⟨mem_univ _, sub_pos.mpr hz⟩, ?_⟩
      exact Complex.ext rfl (sub_add_cancel _ _)
  rw [← heq]
  exact (isConnected_univ.prod (isConnected_Ioi : IsConnected (Ioi (0 : ℝ)))).image
    T hT.continuousOn

private theorem graph_component_upper (f : ℝ → ℝ) (hf : Continuous f)
    (z : ℂ) (hz : f z.re < z.im) :
    connectedComponentIn {q : ℂ | q.im = f q.re}ᶜ z =
      {q : ℂ | f q.re < q.im} := by
  apply subset_antisymm
  · intro q hq
    by_contra hn
    have hzC : z ∈ connectedComponentIn {q : ℂ | q.im = f q.re}ᶜ z :=
      mem_connectedComponentIn (ne_of_gt hz)
    obtain ⟨p, hp, heq⟩ :=
      isPreconnected_connectedComponentIn.intermediate_value₂ hq hzC
        Complex.continuous_im.continuousOn (hf.comp Complex.continuous_re).continuousOn
        (not_lt.mp hn) hz.le
    exact connectedComponentIn_subset _ _ hp heq
  · exact (graph_upper_connected f hf).isPreconnected.subset_connectedComponentIn
      hz (fun q hq => ne_of_gt hq)

private theorem graph_component_lower (f : ℝ → ℝ) (hf : Continuous f)
    (hlower : IsConnected {q : ℂ | q.im < f q.re})
    (z : ℂ) (hz : z.im < f z.re) :
    connectedComponentIn {q : ℂ | q.im = f q.re}ᶜ z =
      {q : ℂ | q.im < f q.re} := by
  apply subset_antisymm
  · intro q hq
    by_contra hn
    have hzC : z ∈ connectedComponentIn {q : ℂ | q.im = f q.re}ᶜ z :=
      mem_connectedComponentIn (ne_of_lt hz)
    obtain ⟨p, hp, heq⟩ :=
      isPreconnected_connectedComponentIn.intermediate_value₂ hzC hq
        Complex.continuous_im.continuousOn (hf.comp Complex.continuous_re).continuousOn
        hz.le (not_lt.mp hn)
    exact connectedComponentIn_subset _ _ hp heq
  · exact hlower.isPreconnected.subset_connectedComponentIn
      hz (fun q hq => ne_of_lt hq)

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "D" => m0CutData W H h (fun _ _ => hp _)
local notation "f" => seamFun (shiftedStream W 0) h ((And.left H) 0)
local notation "P" => monotoneFamilyDrawing (shiftedStream W 0) ((And.left H) 0)
  (monotone_family_all (shiftedStream W 0))

/-- Helper toward Proposition 3.9: the intrinsic source seam trace is the
entire continuous graph, with the missing geometric edges retained. -/
theorem uibotCut_source_seam_trace_eq_graph :
    intrinsicFutureSeamTrace S (D).seam = {z : ℂ | z.im = f z.re} := by
  rw [← futureMap_interface_trace_eq_graph W H D h (fun _ _ => hp _) hpast]
  ext z
  constructor
  · rintro ⟨e, he, hz⟩
    exact ⟨(e, false), he, ((G).toPlaneGraphDrawing_arc_range (e, false)) ▸ hz⟩
  · rintro ⟨⟨e, b⟩, he, hz⟩
    refine ⟨e, he, ?_⟩
    have hz0 : z ∈ ((G).arc (e, false)).image := by
      cases b
      · exact hz
      · exact (G).arc_image_flip (e, false) ▸ hz
    exact ((G).toPlaneGraphDrawing_arc_range (e, false)).symm ▸ hz0

/-- Helper toward Proposition 3.9: the full strict upper region is one
connected component of the complement of the intrinsic source seam. -/
theorem uibotCut_source_component_upper (z : ℂ) (hz : f z.re < z.im) :
    connectedComponentIn (intrinsicFutureSeamTrace S (D).seam)ᶜ z =
      {q : ℂ | f q.re < q.im} := by
  rw [uibotCut_source_seam_trace_eq_graph W H h hpast hp]
  exact graph_component_upper f (seamFun_continuous _ _ _) z hz

/-- Helper toward Proposition 3.9: the full strict lower region is the
other connected component of the complement of the intrinsic source seam. -/
theorem uibotCut_source_component_lower (z : ℂ) (hz : z.im < f z.re) :
    connectedComponentIn (intrinsicFutureSeamTrace S (D).seam)ᶜ z =
      {q : ℂ | q.im < f q.re} := by
  rw [uibotCut_source_seam_trace_eq_graph W H h hpast hp]
  exact graph_component_lower f (seamFun_continuous _ _ _)
    (lower_isConnected _ _ _) z hz

/-- Helper toward Proposition 3.9: every complementary component of the
intrinsic source seam is exactly one of its strict upper and lower regions. -/
theorem uibotCut_source_component_upper_or_lower (z : ℂ)
    (hz : z ∉ intrinsicFutureSeamTrace S (D).seam) :
    connectedComponentIn (intrinsicFutureSeamTrace S (D).seam)ᶜ z =
        {q : ℂ | f q.re < q.im} ∨
      connectedComponentIn (intrinsicFutureSeamTrace S (D).seam)ᶜ z =
        {q : ℂ | q.im < f q.re} := by
  rw [uibotCut_source_seam_trace_eq_graph W H h hpast hp] at hz
  rcases lt_or_gt_of_ne hz with hl | hu
  · exact Or.inr (uibotCut_source_component_lower W H h hpast hp z hl)
  · exact Or.inl (uibotCut_source_component_upper W H h hpast hp z hu)

/-- Helper toward Proposition 3.9: the intrinsic directed root has the
same simultaneous winding tests as the west-to-east run-zero root, including
the possible reversal of the stored geometric edge representative. -/
theorem uibotCut_source_root_leftAtOn_iff (F : Set ℂ) :
    (∀ s, LeftAtOn F (intrinsicFutureDartArc S (S).root) s) ↔
      ∀ s, LeftAtOn F ((P).arc (0, false)).toPath s := by
  let e := wholePlaneEdgeι W 0 0
  let q := uibotWholePlaneSourceEdgeEquiv W H G e
  have hq : q.out.1 = e := uibotWholePlaneSourceEdgeEquiv_out W H G e
  have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hpast H (0, false)
  change (G).arc (e, false) = (P).arc (0, false) at harc
  suffices hh : (∀ s, LeftAtOn F (intrinsicFutureDartArc S (S).root) s) ↔
      ∀ s, LeftAtOn F ((G).arc (e, false)).toPath s by
    refine hh.trans (forall_congr' (fun s => ?_))
    exact leftAtOn_congr_fun F _ _ s
      (fun t => congrArg (fun p : Polyline => p.toPath t) harc)
  cases hb : q.out.2 with
  | false =>
    apply forall_congr'
    intro s
    apply leftAtOn_congr_fun
    intro t
    rw [intrinsicFutureDartArc_apply]
    change (if !q.out.2 then (S).map.arc e t else
      (S).map.arc e (unitInterval.symm t)) = _
    simp only [hb, Bool.not_false, ite_true]
    change ((G).arc q.out).toPath t = _
    rw [show q.out = (e, false) from Prod.ext hq hb]
  | true =>
    have hc : (∀ s, LeftAtOn F (intrinsicFutureDartArc S (S).root) s) ↔
        ∀ s, LeftAtOn F ((G).arc (e, true)).toPath.symm s := by
      apply forall_congr'
      intro s
      apply leftAtOn_congr_fun
      intro t
      rw [intrinsicFutureDartArc_apply]
      change (if !q.out.2 then (S).map.arc e t else
        (S).map.arc e (unitInterval.symm t)) = _
      simp only [hb, Bool.not_true, Bool.false_eq_true, ite_false]
      change ((G).arc q.out).toPath (unitInterval.symm t) = _
      rw [show q.out = (e, true) from Prod.ext hq hb]
      rfl
    exact hc.trans ((forall_leftAtOn_symm_iff F _).trans
      ((G).forall_leftAtOn_flip_toPath_iff_forall_rightAtOn (e, true) F).symm)

private theorem leftAtOn_mono {F U : Set ℂ} (hFU : F ⊆ U)
    {x y : ℂ} {γ : Path x y} {s : {t : I // t ∈ openParams}}
    (hs : LeftAtOn F γ s) : LeftAtOn U γ s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩ := hs
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, fun t ht => hFU (hq t ht), ?_⟩
  apply closure_mono (s := {w : ℂ | w ∈ F ∧
    HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w 1}) ?_ hcl
  exact fun _ hz => ⟨hFU hz.1, hz.2⟩

private theorem root_not_border_exterior :
    ¬ (P).dartBorders (0, false)
      (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) := by
  intro hb
  obtain ⟨k, hk⟩ := (futureMap_exterior_border_iff W H h (0, false)).mp hb
  have he := congrArg Prod.snd hk
  change false = true at he
  cases he

/-- Helper toward Proposition 3.9: the upper component passes every
winding-positive side test along the intrinsic directed source root. -/
theorem uibotCut_source_upper_leftAtOn :
    ∀ s, LeftAtOn {z : ℂ | f z.re < z.im}
      (intrinsicFutureDartArc S (S).root) s := by
  apply (uibotCut_source_root_leftAtOn_iff W H h hpast hp _).mpr
  let F := futureMapDartFace W H h (0, false)
  have hb : (P).dartBorders (0, false) F :=
    (futureMap_dart_face_eq_iff W H h _ _).mp rfl
  have hbounded : ¬ (P).IsUnbounded F := by
    intro hu
    have hlow := (unbounded_face_eq_lower _ h _ F).mp hu
    have houter := (unbounded_face_eq_lower _ h _
      (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H))).mp
        ((futureMap_orbit_face_unbounded_iff W H h _).mpr rfl)
    have he : F = futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H) :=
      Subtype.ext (hlow.trans houter.symm)
    exact root_not_border_exterior W H h (he ▸ hb)
  intro s
  exact leftAtOn_mono (boundedFace_subset_upper _ h _ F hbounded)
    ((P).dartBorders_toPath_leftAtOn
      (kmswLimitDartVertex_surjective _ (H.1 0)) (0, false) F hb s)

/-- Helper toward Proposition 3.9: the lower component fails the
simultaneous winding-positive tests along the intrinsic directed source root. -/
theorem uibotCut_source_not_lower_leftAtOn :
    ¬ ∀ s, LeftAtOn {z : ℂ | z.im < f z.re}
      (intrinsicFutureDartArc S (S).root) s := by
  intro hs
  have hraw := (uibotCut_source_root_leftAtOn_iff W H h hpast hp _).mp hs
  let U := futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)
  have hU : U.val = {z : ℂ | z.im < f z.re} :=
    (unbounded_face_eq_lower _ h _ U).mp
      ((futureMap_orbit_face_unbounded_iff W H h _).mpr rfl)
  have hb := DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective (P)
      (kmswLimitDartVertex_surjective _ (H.1 0)) (0, false) U
      (hU ▸ hraw)
  exact root_not_border_exterior W H h hb

/-- Helper toward Proposition 3.9: the source's winding-positive left
component of the complete seam is exactly the strict upper region. -/
theorem uibotCut_source_openLeft_eq_upper :
    intrinsicFutureOpenLeft S (D).seam = {z : ℂ | f z.re < z.im} := by
  ext z
  constructor
  · rintro ⟨w, hw, hz, hs⟩
    rcases uibotCut_source_component_upper_or_lower W H h hpast hp w hw with hu | hl
    · exact hu ▸ hz
    · exact False.elim (uibotCut_source_not_lower_leftAtOn W H h hpast hp (hl ▸ hs))
  · intro hz
    have hn : z ∉ intrinsicFutureSeamTrace S (D).seam := by
      rw [uibotCut_source_seam_trace_eq_graph W H h hpast hp]
      exact ne_of_gt hz
    refine ⟨z, hn, mem_connectedComponentIn hn, ?_⟩
    rw [uibotCut_source_component_upper W H h hpast hp z hz]
    exact uibotCut_source_upper_leftAtOn W H h hpast hp

include hpast in
private theorem source_cut_darts_ne_univ : ¬ ∀ d : WholePlaneDart W, d ∈ (D).darts := by
  intro hall
  have hupper : (G).image ⊆ {z : ℂ | f z.re ≤ z.im} := by
    rw [(G).image_eq_union_arcs (WholePlanePastGlueData.vertex_incident W)]
    intro z hz
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
    have hD := hall d
    rw [(D).darts_eq h (fun _ _ => hp _)] at hD
    obtain ⟨a, rfl⟩ := hD
    exact WholePlanePastGlueGeometry.runZero_arc_above W h hpast H a hd
  have hlower : {q : ℂ | q.im < f q.re} ⊆ (G).imageᶜ := by
    intro q hq hmem
    exact (show f q.re ≤ q.im from hupper hmem).not_gt hq
  let z : ℂ := ⟨0, f 0 - 1⟩
  have hz : z.im < f z.re := by change f 0 - 1 < f 0; linarith
  have hcomp := (lower_isConnected _ h (H.1 0)).isPreconnected.subset_connectedComponentIn hz hlower
  have hb : Bornology.IsBounded (connectedComponentIn (G).imageᶜ z) := by
    have hn := hlower hz
    rw [WholePlanePastGlueDrawing.glueDrawing_image] at hn ⊢
    exact WholePlanePastGlueFaces.component_isBounded W h hpast H z hn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (hb.subset hcomp)
  let q : ℂ := ⟨R + 1, f (R + 1) - 1⟩
  have hq : q.im < f q.re := by change f (R + 1) - 1 < f (R + 1); linarith
  have hn := hR q hq
  have hre : R + 1 ≤ ‖q‖ := (le_abs_self q.re).trans (Complex.abs_re_le_norm q)
  linarith only [hn, hre]

include hpast in
/-- Helper toward Proposition 3.9: the current combinatorial `IsRot`
predicate also admits a first entrance from outside the cut. Consequently
its unrestricted ambient-dart relation cannot equal intrinsic cut rotation. -/
theorem uibotCut_source_isRot_from_outside :
    ∃ d a : WholePlaneDart W, d ∉ (D).darts ∧ (D).IsRot d a := by
  classical
  by_contra hn
  have hsource : ∀ d a : WholePlaneDart W, (D).IsRot d a → d ∈ (D).darts := by
    intro d a ha
    by_contra hd
    exact hn ⟨d, a, hd, ha⟩
  let R := wholePlaneRotation W H
  have hforward (d : WholePlaneDart W) (hd : d ∈ (D).darts) :
      R d ∈ (D).darts := by
    apply hsource (R d) d
    refine ⟨hd, 1, Nat.zero_lt_one, ?_, ?_⟩
    · change ((wholePlaneRotation W H).symm ^ 1) (wholePlaneRotation W H d) = d
      rw [pow_one, Equiv.symm_apply_apply]
    · intro j hj hj1
      omega
  have hbackward (d : WholePlaneDart W) (hd : d ∈ (D).darts) :
      R.symm d ∈ (D).darts := by
    rw [(D).darts_eq h (fun _ _ => hp _)] at hd
    obtain ⟨b, rfl⟩ := hd
    obtain ⟨ha, k, hk, he, hfirst⟩ := (D).rot_eq h (fun _ _ => hp _) b
    by_cases hk1 : k = 1
    · rw [← he] at ha
      simpa only [hk1, pow_one] using ha
    · apply hsource (R.symm (wholePlaneDartι W 0 b)) _
      refine ⟨ha, k - 1, by omega, ?_, ?_⟩
      · have hpow : (R.symm ^ (k - 1)) (R.symm (wholePlaneDartι W 0 b)) =
            (R.symm ^ k) (wholePlaneDartι W 0 b) := by
          change ((R.symm ^ (k - 1)) * R.symm) _ = _
          rw [← pow_succ, Nat.sub_add_cancel hk]
        exact hpow.trans he
      · intro j hj hjk hmem
        apply hfirst (j + 1) (by omega) (by omega)
        rw [pow_succ]
        exact hmem
  apply source_cut_darts_ne_univ W H h hpast hp
  intro d
  have hpath := wholePlaneDart_connected W H (wholePlaneDartι W 0 (0, false)) d
  induction hpath with
  | refl =>
    rw [(D).darts_eq h (fun _ _ => hp _)]
    exact Set.mem_range_self _
  | tail hpath hstep ih =>
    rcases hstep with rfl | rfl | rfl | rfl
    · exact hforward _ ih
    · exact hbackward _ ih
    · exact ih
    · exact ih




theorem uibotCut_no_unguarded_rotation_identification
    (A : D39DomainRootedMap.{0})
    (iso : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) :
    let J : WholePlaneDart W → A.E × Bool := fun d =>
      (iso.edgeEquiv d.1, Bool.xor
        (Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2))
        (iso.edgeFlip d.1))
    ¬ ∃ C : IntrinsicFutureCut A,
      C.edges = iso.edgeEquiv '' (D).edges ∧
        ∀ d a, C.rotation (J d) (J a) ↔ (D).IsRot d a := by
  dsimp only
  rintro ⟨C, he, hr⟩
  obtain ⟨d, a, hd, ha⟩ := uibotCut_source_isRot_from_outside W H h hpast hp
  have hm := ((C.rotation_iff _ _).mp ((hr d a).mpr ha)).1
  change iso.edgeEquiv d.1 ∈ C.edges at hm
  rw [he, iso.edgeEquiv.injective.mem_set_image] at hm
  exact hd hm


























































































end DirectedDistances.PaperProofs.Section3
end
