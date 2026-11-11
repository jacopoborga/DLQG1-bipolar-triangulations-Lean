/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblySeamTrace
public import DirectedDistances.KMSW.UIBHBOTTransportedCapBounded
import DirectedDistances.KMSW.MonotoneFamilyFacesUpper
import DirectedDistances.PlanarMap.PLDrawingFaceTransfer

/-! # Creation caps as faces of the UIBHBOT assembly

Helper toward Definition 5.8 -/

public section

namespace DirectedDistances.KMSW

open Set DirectedDistances.PlanarMap WholePlanePastGlueData
open DirectedDistances.PaperProofs.Section5
open scoped Topology

/-- Helper toward Definition 5.8: creation caps are open connected sets with
their entire frontier in the original drawing. -/
theorem uibhbot_cap_topology (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (j : TriangleCreationTime w) :
    let Q := monotoneFamilyDrawing w hfin (monotone_family_all w)
    IsOpen (capFace w hfin j).val ∧ IsConnected (capFace w hfin j).val ∧
      frontier (capFace w hfin j).val ⊆ Q.image := by
  let n := j.val + 1
  let i := (stageTriangleRecord_fin_index w j).choose
  let G := familyG w (monotone_family_all w) n
  let Q := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hcap : (capFace w hfin j).val = (G.cap i).region := (capFace_spec w hfin j).1
  have hopen : IsOpen (capFace w hfin j).val := by
    rw [hcap]
    exact isOpen_graphRegion (G.cap i).low_continuous (G.cap i).high_continuous
  have hconn : IsConnected (capFace w hfin j).val := by
    obtain ⟨z, hz, heq⟩ := (capFace w hfin j).property
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hz
  refine ⟨hopen, hconn, ?_⟩
  rw [hcap]
  change frontier (graphRegion _ _ _ _) ⊆ _
  rw [frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
    (G.cap i).left_join (G.cap i).right_join]
  rw [G.cap_lower_trace i, G.cap_upper_trace i]
  have htrace (e : ℕ) : stageEdgeTrace (familyQ w (monotone_family_all w) n) e ⊆ Q.image := by
    unfold stageEdgeTrace
    split
    · rename_i he
      intro z hz
      apply Or.inr
      refine ⟨(e, false), ?_⟩
      rw [familyDrawing_arc w hfin (monotone_family_all w) n (⟨e, he⟩, false)]
      exact hz
    · exact empty_subset _
  rintro z (hz | hz)
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact htrace e hz
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact htrace e hz

section Assembly

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
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
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "Q0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Qp" => uibhbotPastMonotoneDrawing W hfin
local notation "Tf" => uibhbotGlueFutureTransfer w0 h0 ((And.left H) 0)
local notation "Tp" => uibhbotPastStraightTransfer W hL hR
local notation "A" => uibhbotAssemblyHalfTurn
local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "C0" => fun j : TriangleCreationTime w0 =>
  Tf '' Subtype.val (capFace w0 ((And.left H) 0) j)
local notation "Cp" => fun j : TriangleCreationTime wp =>
  A '' (Tp '' Subtype.val (capFace wp hfin j))

/-- Helper toward Definition 5.8: all future cap interiors lie on the strict
lower side, including the caps whose frontier touches the seam. -/
theorem uibhbot_future_transported_cap_im_neg (j : TriangleCreationTime w0) :
    C0 j ⊆ {z : ℂ | z.im < 0} := by
  rintro z ⟨y, hy, rfl⟩
  have hu := boundedFace_subset_upper w0 h0 (H.1 0) (capFace w0 (H.1 0) j)
    (capFace_not_unbounded w0 (H.1 0) j) hy
  change seamFun w0 h0 (H.1 0) y.re < y.im at hu
  change -y.im + 0 + seamFun w0 h0 (H.1 0) y.re < 0
  linarith only [hu]

include hp ha in
/-- Helper toward Definition 5.8: the supplied straight past drawing lies
below the axis, as follows from its exact transfer characterization. -/
theorem uibhbot_assembly_past_image_im_nonpos : P.image ⊆ {z : ℂ | z.im ≤ 0} := by
  rw [(Qp).image_of_transfer Tp P hp ha]
  rintro z ⟨y, hy, rfl⟩
  have hx := uibhbotPastMonotoneDrawing_image_re_le_one W hfin hR hy
  have hs := uibhbotPastSeamHeight_mem W hL hR y.re
  rw [min_eq_left hx] at hs
  have hb := uibhbotPastMonotoneDrawing_above_seam W hfin hy hs
  change -y.im + 0 + uibhbotPastSeamHeight W hL hR y.re ≤ 0
  linarith only [hb]

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the complete attached past trace is retained,
both on and off the seam. -/
theorem uibhbot_assembly_past_arc_trace (d : ℕ × Bool) :
    ((G).arc (kmswPastDart W d)).image = A '' (P.arc d).image := by
  by_cases hd : kmswPastSeamEdge W d.1
  · exact uibhbotCcw_assembly_seam_trace W H h0 hL hR hfin P hp ha F hf hFim hFa d hd
  · rw [uibhbotCcw_assemblyDrawing_arc,
      uibhbotAssemblyArc_past W h0 _ _ d hd,
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _)]

private theorem uibhbot_cap_dartVertex_surjective (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) :
    Function.Surjective (kmswLimitDartVertex w) := by
  intro v
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v hn
  refine ⟨(d.1.val, d.2), ?_⟩
  have he := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;>
    simpa only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
      ite_false, ite_true, he.1, he.2] using hd

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: the assembly image is precisely the union
of the future image and the complete attached past image. -/
theorem uibhbot_assembly_image_eq : (G).image = F.image ∪ A '' P.image := by
  have hfuture (d : ℕ × Bool) : (G).arc (wholePlaneDartι W 0 d) = F.arc d := by
    rw [uibhbotCcw_assemblyDrawing_arc, uibhbotAssemblyArc_future]
  have hpast := uibhbot_assembly_past_arc_trace W H h0 hL hR hfin P hp ha F hf hFim hFa
  rw [(G).image_eq_union_arcs (vertex_incident W),
    F.image_eq_union_arcs (uibhbot_cap_dartVertex_surjective w0 (H.1 0)),
    P.image_eq_union_arcs (uibhbot_cap_dartVertex_surjective wp hfin)]
  ext z
  constructor
  · intro hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    rcases dart_cover W d with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact Or.inl (mem_iUnion.mpr ⟨e, (hfuture e) ▸ hd⟩)
    · rw [hpast e] at hd
      obtain ⟨y, hy, rfl⟩ := hd
      exact Or.inr ⟨y, mem_iUnion.mpr ⟨e, hy⟩, rfl⟩
  · rintro (hz | ⟨y, hy, rfl⟩)
    · obtain ⟨d, hd⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨wholePlaneDartι W 0 d, (hfuture d).symm ▸ hd⟩
    · obtain ⟨d, hd⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨kmswPastDart W d, (hpast d).symm ▸ ⟨y, hd, rfl⟩⟩

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: every transported future creation cap is
a face of the assembly, including caps incident to the seam. -/
theorem uibhbot_assembly_future_cap_face (j : TriangleCreationTime w0) :
    ∃ K : (G).Face, K.val = C0 j := by
  have hfp : F.pos = Tf ∘ (Q0).pos := hf
  obtain ⟨_, hfaces, _⟩ := (Q0).face_image_of_transfer Tf F hfp hFa
  obtain ⟨K, hK⟩ := hfaces (capFace w0 (H.1 0) j)
  have htop := uibhbot_cap_topology w0 (H.1 0) j
  have hopen : IsOpen (C0 j) := (Tf).isOpenMap _ htop.1
  have hconn : IsConnected (C0 j) := htop.2.1.image Tf (Tf).continuous.continuousOn
  have hdisj : C0 j ∩ (G).image = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzG⟩
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
    rcases hzG with hzF | ⟨y, hy, rfl⟩
    · exact F.face_subset_compl K (hK.symm ▸ hz) hzF
    · have hn := uibhbot_future_transported_cap_im_neg W H h0 j hz
      have hpast := uibhbot_assembly_past_image_im_nonpos W hL hR hfin P hp ha hy
      change -y.im - 0 < 0 at hn
      change y.im ≤ 0 at hpast
      linarith only [hn, hpast]
  have hfront : frontier (C0 j) ⊆ (G).image := by
    rw [← (Tf).image_frontier]
    intro z hz
    have hzF : z ∈ F.image := by
      rw [(Q0).image_of_transfer Tf F hfp hFa]
      exact image_mono htop.2.2 hz
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa]
    exact Or.inl hzF
  obtain ⟨z, hz⟩ := hconn.nonempty
  refine ⟨⟨C0 j, z, ?_, ?_⟩, rfl⟩
  · intro hzG
    exact (eq_empty_iff_forall_notMem.mp hdisj z) ⟨hz, hzG⟩
  · exact (connectedComponentIn_compl_eq_of_open_connected hopen hconn
      hconn.nonempty hdisj hfront hz).symm

/-- Helper toward Definition 5.8: past cap interiors lie strictly above the
persistent lower graph. This uses its one-sided seam, without right hits. -/
theorem uibhbot_past_cap_above_seam (j : TriangleCreationTime wp) :
    ∀ y ∈ (capFace wp hfin j).val,
      uibhbotPastSeamHeight W hL hR y.re < y.im := by
  intro y hy
  let n := j.val + 1
  let i := (stageTriangleRecord_fin_index wp j).choose
  let S := familyG wp (monotone_family_all wp) n
  have hcap : (capFace wp hfin j).val = (S.cap i).region := (capFace_spec wp hfin j).1
  have hb : y ∈ closedGraphRegion S.xmin S.xmax S.lower S.upper := by
    rw [← S.toMonotoneStageCertificate.cover]
    exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure (hcap ▸ hy)⟩)
  have hx : y.re ∈ Icc S.xmin S.xmax := ⟨hb.1, hb.2.1⟩
  have hs : uibhbotPastSeamHeight W hL hR y.re = S.lower y.re :=
    uibhbotPastSeamHeight_eq_lower W hL hR n y.re hx
  have hle : uibhbotPastSeamHeight W hL hR y.re ≤ y.im := hs ▸ hb.2.2.1
  have hne : uibhbotPastSeamHeight W hL hR y.re ≠ y.im := by
    intro heq
    have hx1 : y.re ≤ 1 := by
      simpa only [S, uibhbotPastStage_xmax_eq_one W hR n] using hb.2.1
    have hseam := uibhbotPastSeamHeight_mem W hL hR y.re
    rw [min_eq_left hx1, heq] at hseam
    have hyimage : y ∈ (Qp).image := by
      have hymk : (⟨y.re, y.im⟩ : ℂ) = y := Complex.eta y
      exact hymk ▸ uibhbotPastSeamGraph_subset_image W hfin hseam
    exact (Qp).face_subset_compl (capFace wp hfin j) hy hyimage
  exact lt_of_le_of_ne hle hne

/-- Helper toward Definition 5.8: attached past cap interiors lie strictly
above the real axis, including caps with seam edges on their frontier. -/
theorem uibhbot_past_transported_cap_im_pos (j : TriangleCreationTime wp) :
    Cp j ⊆ {z : ℂ | 0 < z.im} := by
  rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩
  have hs := uibhbot_past_cap_above_seam W hL hR hfin j y hy
  change 0 < -(-y.im + 0 + uibhbotPastSeamHeight W hL hR y.re) - 0
  linarith only [hs]

/-- Helper toward Definition 5.8: the attaching half-turn as a plane homeomorphism. -/
private def uibhbot_cap_halfTurnHomeomorph : ℂ ≃ₜ ℂ where
  toFun := uibhbotAssemblyHalfTurn
  invFun := uibhbotAssemblyHalfTurn
  left_inv := uibhbotAssemblyHalfTurn_involutive
  right_inv := uibhbotAssemblyHalfTurn_involutive
  continuous_toFun := continuous_uibhbotAssemblyHalfTurn
  continuous_invFun := continuous_uibhbotAssemblyHalfTurn

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: every attached past creation cap is a
face of the assembly. Complete seam traces retain its entire frontier. -/
theorem uibhbot_assembly_past_cap_face (j : TriangleCreationTime wp) :
    ∃ K : (G).Face, K.val = Cp j := by
  let T : ℂ ≃ₜ ℂ := (Tp).trans uibhbot_cap_halfTurnHomeomorph
  have hC : T '' (capFace wp hfin j).val = Cp j := by
    exact (image_image A Tp _).symm
  have htop := uibhbot_cap_topology wp hfin j
  have hopen : IsOpen (Cp j) := hC ▸ T.isOpenMap _ htop.1
  have hconn : IsConnected (Cp j) :=
    hC ▸ htop.2.1.image T T.continuous.continuousOn
  have hdisj : Cp j ∩ (G).image = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzG⟩
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa] at hzG
    rcases hzG with hzF | ⟨x, hx, hxz⟩
    · have hpos := uibhbot_past_transported_cap_im_pos W hL hR hfin j hz
      have hneg := hFim hzF
      exact (show 0 < z.im from hpos).not_ge hneg
    · obtain ⟨x', ⟨y, hy, rfl⟩, heq⟩ := hz
      have hxT : Tp y = x := uibhbotAssemblyHalfTurn_involutive.injective (heq.trans hxz.symm)
      rw [(Qp).image_of_transfer Tp P hp ha] at hx
      obtain ⟨y', hy', heq'⟩ := hx
      have hyy : y' = y := (Tp).injective (heq'.trans hxT.symm)
      exact (Qp).face_subset_compl (capFace wp hfin j) hy (hyy ▸ hy')
  have hfront : frontier (Cp j) ⊆ (G).image := by
    rw [← hC, ← T.image_frontier]
    intro z hz
    have hzP : z ∈ A '' P.image := by
      rw [(Qp).image_of_transfer Tp P hp ha, image_image]
      exact image_mono htop.2.2 hz
    rw [uibhbot_assembly_image_eq W H h0 hL hR hfin P hp ha F hf hFim hFa]
    exact Or.inr hzP
  obtain ⟨z, hz⟩ := hconn.nonempty
  refine ⟨⟨Cp j, z, ?_, ?_⟩, rfl⟩
  · intro hzG
    exact (eq_empty_iff_forall_notMem.mp hdisj z) ⟨hz, hzG⟩
  · exact (connectedComponentIn_compl_eq_of_open_connected hopen hconn
      hconn.nonempty hdisj hfront hz).symm

end Assembly

end DirectedDistances.KMSW
