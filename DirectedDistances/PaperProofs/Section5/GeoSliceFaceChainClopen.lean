/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightEnclosedSlice
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceNeighborhood
public import DirectedDistances.KMSW.WholePlaneM0Drawing

/-! Local geometric neighborhoods for the face-chain clopen argument.
The global exhaustion statements remain separate proof obligations. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Set Metric
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}

/-- Helper toward Lemma 5.6: the two actual faces bordering an edge,
together with the edge itself, form a neighborhood of every interior point.
This includes bends and does not assume a local separation statement. -/
theorem m0Geodesic_two_faces_arc_mem_nhds
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (d : WholePlaneDart W)
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders d F)
    (hG : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartFlip W d) G)
    {q : ℂ}
    (hq : q ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).interior) :
    F.val ∪ G.val ∪
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).image ∈ 𝓝 q := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  obtain ⟨ra, hra, harc⟩ := P.interior_contact_local_arc_image hv d hq
  obtain ⟨rf, hrf, hfaces⟩ := P.interior_contact_local_bordering_dart hv d hq
  apply Metric.mem_nhds_iff.mpr
  refine ⟨min ra rf, lt_min hra hrf, ?_⟩
  intro y hy
  by_cases hyim : y ∈ P.image
  · exact Or.inr (harc y ((mem_ball.mp hy).trans_le (min_le_left ra rf)) hyim)
  · obtain ⟨K, hyK⟩ := (P.faces_cover_compl y).mpr hyim
    rcases hfaces K y ((mem_ball.mp hy).trans_le (min_le_right ra rf)) hyK with
      hb | hb
    · have heq := P.dartBorders_face_unique d K F hb hF
      exact Or.inl (Or.inl (heq ▸ hyK))
    · have heq := P.dartBorders_face_unique (wholePlaneDartFlip W d) K G hb hG
      exact Or.inl (Or.inr (heq ▸ hyK))

/-- Helper toward Lemma 5.6: near a vertex of the glued drawing, every
drawing point lies on an incident geometric edge. The finite star is not
assumed to describe the local drawing; that fact follows from local finiteness. -/
theorem m0Geodesic_vertex_local_arc_star
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (v : WholePlaneVertex W) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos v) r,
      y ∈ (WholePlanePastGlueDrawing.glueDrawing W h hp H).image →
      ∃ d : WholePlaneDart W, wholePlaneDartVertex W d = v ∧
        y ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).image := by
  classical
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let B : WholePlaneDart W → Set ℂ := fun d =>
    if wholePlaneDartVertex W d = v ∨
      wholePlaneDartVertex W (wholePlaneDartFlip W d) = v then ∅
    else (P.arc d).image
  have hBsub (d : WholePlaneDart W) : B d ⊆ (P.arc d).image := by
    dsimp only [B]
    split_ifs
    · exact empty_subset _
    · exact Subset.rfl
  have hlocal : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have hclosed : IsClosed (⋃ d, B d) := by
    apply (hlocal.subset hBsub).isClosed_iUnion
    intro d
    dsimp only [B]
    split_ifs
    · exact isClosed_empty
    · exact (P.arc d).isCompact_image.isClosed
  have hvB : P.pos v ∉ ⋃ d, B d := by
    intro hmem
    obtain ⟨d, hd⟩ := mem_iUnion.mp hmem
    dsimp only [B] at hd
    split_ifs at hd with hinc
    · exact notMem_empty _ hd
    · apply P.interior_avoids_vertices d v
      refine ⟨hd, ?_⟩
      rintro (he | he)
      · apply hinc
        exact Or.inl (P.pos_injective (he.trans (P.arc_start d))).symm
      · apply hinc
        exact Or.inr (P.pos_injective (he.trans (P.arc_finish d))).symm
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds hvB)
  refine ⟨r, hr, ?_⟩
  intro y hyr hy
  have hyB := hball hyr
  rw [P.image_eq_union_arcs (uibhbot_faceOrbit_dartVertex_surjective W H)] at hy
  obtain ⟨d, hd⟩ := mem_iUnion.mp hy
  by_cases hinc : wholePlaneDartVertex W d = v ∨
      wholePlaneDartVertex W (wholePlaneDartFlip W d) = v
  · rcases hinc with hinc | hinc
    · exact ⟨d, hinc, hd⟩
    · refine ⟨wholePlaneDartFlip W d, hinc, ?_⟩
      rw [P.arc_flip, Polyline.image_reverse_transfer]
      exact hd
  · exact (hyB (mem_iUnion.mpr ⟨d, by
      simpa only [B, ite_eq_right hinc] using hd⟩)).elim

/-- Helper toward Lemma 5.6: geometric dual adjacency crosses an actual
edge at an interior point of the specified region. Parallel geometric edges
retain their identities and the two bordering darts retain their orientation. -/
@[expose] def m0GeodesicFaceChainStep
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (C : Set ℂ)
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) : Prop :=
  ∃ d : WholePlaneDart W,
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders d F ∧
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartFlip W d) G ∧
    (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).interior ∩ C).Nonempty

/-- Helper toward Lemma 5.6: crossing a geometric edge is reversible. -/
theorem m0GeodesicFaceChainStep_symm
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (C : Set ℂ)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp C F G) :
    m0GeodesicFaceChainStep hp C G F := by
  obtain ⟨d, hd, hf, q, hq, hqC⟩ := hFG
  refine ⟨wholePlaneDartFlip W d, hf, ?_, q, ?_, hqC⟩
  · simpa only [wholePlaneDartFlip_involutive W d] using hd
  · rw [PLDrawing.arc_flip, Polyline.interior_reverse_transfer]
    exact hq

/-- Helper toward Lemma 5.6: the complement of the glued drawing is
dense. Every drawn arc lies in the closure of an actual bordering face. -/
theorem m0Geodesic_drawing_compl_dense
    (hp : BoundaryHitWitnesses (kmswPastCode W)) :
    Dense (WholePlanePastGlueDrawing.glueDrawing W h hp H).imageᶜ := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  intro q
  by_cases hq : q ∈ P.image
  · rw [P.image_eq_union_arcs (uibhbot_faceOrbit_dartVertex_surjective W H)] at hq
    obtain ⟨d, hd⟩ := mem_iUnion.mp hq
    obtain ⟨F, hb⟩ := WholePlaneGlueFaceCorrespondenceFull.dart_borders_exists W h hp H d
    exact closure_mono (P.face_subset_compl F)
      (P.dartBorders_arc_subset_closure (uibhbot_faceOrbit_dartVertex_surjective W H)
        d F hb hd)
  · exact subset_closure hq

/-- Helper toward Lemma 5.6: away from graph vertices, all faces meeting
a sufficiently small ball have the same reachability status. The crossing
edge is constructed at the center of the ball; no dual connectivity is assumed. -/
theorem m0GeodesicFaceChain_locally_constant_off_vertices
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (C : Set ℂ)
    (F0 : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    {q : ℂ} (hqC : q ∈ C)
    (hqv : ∀ v : WholePlaneVertex W,
      q ≠ (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos v) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) (z w : ℂ),
        z ∈ ball q r → z ∈ F.val → w ∈ ball q r → w ∈ G.val →
        (Relation.ReflTransGen (m0GeodesicFaceChainStep hp C) F0 F ↔
          Relation.ReflTransGen (m0GeodesicFaceChainStep hp C) F0 G) := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  by_cases hq : q ∈ P.image
  · rw [P.image_eq_union_arcs hv] at hq
    obtain ⟨d, hd⟩ := mem_iUnion.mp hq
    have hqi : q ∈ (P.arc d).interior := by
      refine ⟨hd, ?_⟩
      rintro (he | he)
      · exact hqv _ (he.trans (P.arc_start d))
      · exact hqv _ (he.trans (P.arc_finish d))
    obtain ⟨r, hr, hlocal⟩ := P.interior_contact_local_bordering_dart hv d hqi
    refine ⟨r, hr, ?_⟩
    intro F G z w hzr hzF hwr hwG
    have hF := hlocal F z hzr hzF
    have hG := hlocal G w hwr hwG
    have hstep (A B : P.Face) (ha : P.dartBorders d A)
        (hb : P.dartBorders (wholePlaneDartFlip W d) B) :
        m0GeodesicFaceChainStep hp C A B := ⟨d, ha, hb, q, hqi, hqC⟩
    rcases hF with hF | hF <;> rcases hG with hG | hG
    · have heq := P.dartBorders_face_unique d F G hF hG
      rw [heq]
    · exact ⟨fun hh => hh.tail (hstep F G hF hG),
        fun hh => hh.tail (m0GeodesicFaceChainStep_symm hp C (hstep F G hF hG))⟩
    · exact ⟨fun hh => hh.tail (m0GeodesicFaceChainStep_symm hp C (hstep G F hG hF)),
        fun hh => hh.tail (hstep G F hG hF)⟩
    · have heq := P.dartBorders_face_unique (wholePlaneDartFlip W d) F G hF hG
      rw [heq]
  · obtain ⟨K, hqK⟩ := (P.faces_cover_compl q).mpr hq
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      ((P.face_open_frontier_subset_image hv K).1.mem_nhds hqK)
    refine ⟨r, hr, ?_⟩
    intro F G z w hzr hzF hwr hwG
    have hFK := P.faces_eq_of_mem hzF (hball hzr)
    have hGK := P.faces_eq_of_mem hwG (hball hwr)
    rw [hFK, hGK]

/-- Helper toward Lemma 5.6: faces meeting one open preconnected geometric
region admit a finite dual chain crossing edges inside that region. The proof
uses a clopen partition, local edge neighborhoods and punctured vertex disks;
neither face-graph connectivity nor local drawing structure is a premise. -/
theorem m0GeodesicFaceChain_reaches_of_isOpen_isPreconnected
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (C : Set ℂ) (hCo : IsOpen C) (hCc : IsPreconnected C)
    (F0 F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF0 : (C ∩ F0.val).Nonempty) (hF : (C ∩ F.val).Nonempty) :
    Relation.ReflTransGen (m0GeodesicFaceChainStep hp C) F0 F := by
  classical
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let R : P.Face → Prop := Relation.ReflTransGen (m0GeodesicFaceChainStep hp C) F0
  let A : Set ℂ := ⋃ K : P.Face, ⋃ (_ : R K), K.val
  let B : Set ℂ := ⋃ K : P.Face, ⋃ (_ : ¬ R K), K.val
  have hAo : IsOpen A := by
    apply isOpen_iUnion
    intro K
    apply isOpen_iUnion
    intro _
    exact (P.face_open_frontier_subset_image
      (uibhbot_faceOrbit_dartVertex_surjective W H) K).1
  have hBo : IsOpen B := by
    apply isOpen_iUnion
    intro K
    apply isOpen_iUnion
    intro _
    exact (P.face_open_frontier_subset_image
      (uibhbot_faceOrbit_dartVertex_surjective W H) K).1
  have hABdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨K, hK, hzK⟩ := mem_iUnion.mp hzA |>.imp fun _ => mem_iUnion.mp
    obtain ⟨L, hL, hzL⟩ := mem_iUnion.mp hzB |>.imp fun _ => mem_iUnion.mp
    exact hL ((P.faces_eq_of_mem hzK hzL) ▸ hK)
  have hAB : A ∪ B = P.imageᶜ := by
    ext z
    constructor
    · rintro (hz | hz)
      · obtain ⟨K, _, hzK⟩ := mem_iUnion.mp hz |>.imp fun _ => mem_iUnion.mp
        exact P.face_subset_compl K hzK
      · obtain ⟨K, _, hzK⟩ := mem_iUnion.mp hz |>.imp fun _ => mem_iUnion.mp
        exact P.face_subset_compl K hzK
    · intro hz
      obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr hz
      by_cases hK : R K
      · exact Or.inl (mem_iUnion.mpr ⟨K, mem_iUnion.mpr ⟨hK, hzK⟩⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨K, mem_iUnion.mpr ⟨hK, hzK⟩⟩)
  have hcover (z : ℂ) : z ∈ closure A ∨ z ∈ closure B := by
    have hz := m0Geodesic_drawing_compl_dense (H := H) (h := h) hp z
    rw [← hAB, closure_union] at hz
    exact hz
  let U : Set ℂ := (closure B)ᶜ
  let V : Set ℂ := (closure A)ᶜ
  have hUo : IsOpen U := isClosed_closure.isOpen_compl
  have hVo : IsOpen V := isClosed_closure.isOpen_compl
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro z hzU hzV
    rcases hcover z with hz | hz
    · exact hzV hz
    · exact hzU hz
  have hAU : A ⊆ U := by
    have hsub : B ⊆ Aᶜ := fun z hzB hzA => disjoint_left.mp hABdisj hzA hzB
    have hcl := closure_mono hsub
    rw [hAo.isClosed_compl.closure_eq] at hcl
    exact fun z hzA hzB => hcl hzB hzA
  have hBV : B ⊆ V := by
    have hsub : A ⊆ Bᶜ := fun z hzA hzB => disjoint_left.mp hABdisj hzA hzB
    have hcl := closure_mono hsub
    rw [hBo.isClosed_compl.closure_eq] at hcl
    exact fun z hzB hzA => hcl hzA hzB
  have hnotcommon {q : ℂ} (hqC : q ∈ C)
      (hqv : ∀ v : WholePlaneVertex W, q ≠ P.pos v)
      (hqA : q ∈ closure A) (hqB : q ∈ closure B) : False := by
    obtain ⟨r, hr, hloc⟩ :=
      m0GeodesicFaceChain_locally_constant_off_vertices hp C F0 hqC hqv
    obtain ⟨z, hzA, hz⟩ := Metric.mem_closure_iff.mp hqA r hr
    obtain ⟨w, hwB, hw⟩ := Metric.mem_closure_iff.mp hqB r hr
    obtain ⟨K, hK, hzK⟩ := mem_iUnion.mp hzA |>.imp fun _ => mem_iUnion.mp
    obtain ⟨L, hL, hwL⟩ := mem_iUnion.mp hwB |>.imp fun _ => mem_iUnion.mp
    apply hL
    exact (hloc K L z w (by rwa [mem_ball, dist_comm]) hzK
      (by rwa [mem_ball, dist_comm]) hwL).mp hK
  have hCnotcommon {q : ℂ} (hqC : q ∈ C)
      (hqA : q ∈ closure A) (hqB : q ∈ closure B) : False := by
    by_cases hqv : ∃ v : WholePlaneVertex W, q = P.pos v
    · obtain ⟨v, hv⟩ := hqv
      obtain ⟨rc, hrc, hballC⟩ := Metric.mem_nhds_iff.mp (hCo.mem_nhds hqC)
      obtain ⟨rv, hrv, hisolate⟩ := P.polyline_vertices_locally_isolated q
      let r := min rc rv
      have hr : 0 < r := lt_min hrc hrv
      have hqimage : q ∈ P.image := Or.inl ⟨v, hv.symm⟩
      have hpunct : ball q r \ {q} ⊆ U ∪ V := by
        intro y hy
        have hyC := hballC ((mem_ball.mp hy.1).trans_le (min_le_left rc rv))
        have hyv : ∀ w : WholePlaneVertex W, y ≠ P.pos w := by
          intro w heq
          obtain ⟨d, hd⟩ := uibhbot_faceOrbit_dartVertex_surjective W H w
          have hp0 : (P.arc d).point 0 = P.pos w :=
            ((P.arc d).point_zero_eq_start).trans ((P.arc_start d).trans (congrArg P.pos hd))
          have hpq : (P.arc d).point 0 = q := by
            apply hisolate d 0 (by have := P.arc_length d; omega)
            rw [hp0, ← heq]
            exact (mem_ball.mp hy.1).trans_le (min_le_right rc rv)
          exact hy.2 (heq.trans (hp0.symm.trans hpq))
        by_cases hyA : y ∈ closure A
        · exact Or.inl (fun hyB => hnotcommon hyC hyv hyA hyB)
        · exact Or.inr hyA
      obtain ⟨z, hzA, hz⟩ := Metric.mem_closure_iff.mp hqA r hr
      obtain ⟨w, hwB, hw⟩ := Metric.mem_closure_iff.mp hqB r hr
      have hzq : z ≠ q := by
        intro he
        have hzoff : z ∈ P.imageᶜ := by rw [← hAB]; exact Or.inl hzA
        exact hzoff (he ▸ hqimage)
      have hwq : w ≠ q := by
        intro he
        have hwoff : w ∈ P.imageᶜ := by rw [← hAB]; exact Or.inr hwB
        exact hwoff (he ▸ hqimage)
      obtain ⟨y, _, hyU, hyV⟩ := PLDrawing.punctured_ball_isPreconnected q r hr U V
        hUo hVo hpunct
        ⟨z, ⟨by rwa [mem_ball, dist_comm], hzq⟩, hAU hzA⟩
        ⟨w, ⟨by rwa [mem_ball, dist_comm], hwq⟩, hBV hwB⟩
      exact disjoint_left.mp hUV hyU hyV
    · exact hnotcommon hqC (fun v he => hqv ⟨v, he⟩) hqA hqB
  have hCcover : C ⊆ U ∪ V := by
    intro q hqC
    by_cases hqA : q ∈ closure A
    · exact Or.inl (fun hqB => hCnotcommon hqC hqA hqB)
    · exact Or.inr hqA
  obtain ⟨z, hzC, hzF0⟩ := hF0
  have hzA : z ∈ A := mem_iUnion.mpr ⟨F0, mem_iUnion.mpr ⟨.refl, hzF0⟩⟩
  have hCU : C ⊆ U := by
    rcases hCc.subset_or_subset hUo hVo hUV hCcover with hCU | hCV
    · exact hCU
    · exact (disjoint_left.mp hUV (hAU hzA) (hCV hzC)).elim
  by_contra hnot
  obtain ⟨w, hwC, hwF⟩ := hF
  have hwB : w ∈ B := mem_iUnion.mpr ⟨F, mem_iUnion.mpr ⟨hnot, hwF⟩⟩
  exact disjoint_left.mp hUV (hCU hwC) (hBV hwB)

/-- Helper toward Lemma 5.6: a face meeting a component of the complement
of a drawn slit lies entirely in that component. The slit may include
missing geometric edges; only containment in the actual drawing is used. -/
theorem m0Geodesic_face_subset_slit_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (K : Set ℂ)
    (hK : K ⊆ (WholePlanePastGlueDrawing.glueDrawing W h hp H).image)
    (z : ℂ) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : (connectedComponentIn Kᶜ z ∩ F.val).Nonempty) :
    F.val ⊆ connectedComponentIn Kᶜ z := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨x, hxC, hxF⟩ := hF
  obtain ⟨a, _, hFa⟩ := F.property
  have hFc : IsPreconnected F.val := by
    rw [hFa]
    exact isPreconnected_connectedComponentIn
  have hsub : F.val ⊆ Kᶜ := fun y hy hyK => P.face_subset_compl F hy (hK hyK)
  rw [connectedComponentIn_eq hxC]
  exact hFc.subset_connectedComponentIn hxF hsub

/-- Helper toward Lemma 5.6: a crossing inside an open slit component
has both of its bordering faces retained in that same component. -/
theorem m0GeodesicFaceChainStep_faces_subset_slit_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (K : Set ℂ) (hKc : IsClosed K)
    (hK : K ⊆ (WholePlanePastGlueDrawing.glueDrawing W h hp H).image)
    (z : ℂ) {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp (connectedComponentIn Kᶜ z) F G) :
    F.val ⊆ connectedComponentIn Kᶜ z ∧ G.val ⊆ connectedComponentIn Kᶜ z := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨d, hdF, hdG, q, hqd, hqC⟩ := hFG
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hKc.isOpen_compl.connectedComponentIn.mem_nhds hqC)
  have hside (A : P.Face) (hqA : q ∈ closure A.val) :
      A.val ⊆ connectedComponentIn Kᶜ z := by
    obtain ⟨y, hyA, hyq⟩ := Metric.mem_closure_iff.mp hqA r hr
    apply m0Geodesic_face_subset_slit_component hp K hK z A
    exact ⟨y, hball (by rwa [mem_ball, dist_comm]), hyA⟩
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  refine ⟨hside F (P.dartBorders_arc_subset_closure hv d F hdF hqd.1), ?_⟩
  apply hside G
  apply P.dartBorders_arc_subset_closure hv (wholePlaneDartFlip W d) G hdG
  rw [P.arc_flip, Polyline.image_reverse_transfer]
  exact hqd.1

/-- Helper toward Lemma 5.6: the clopen construction gives a chain entirely
of retained faces of an actual slit component. Connectedness and local drawing
structure are discharged here from the geometric component construction. -/
theorem m0GeodesicFaceChain_reaches_in_slit_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (K : Set ℂ) (hKc : IsClosed K)
    (hK : K ⊆ (WholePlanePastGlueDrawing.glueDrawing W h hp H).image)
    (z : ℂ) (F0 F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF0 : (connectedComponentIn Kᶜ z ∩ F0.val).Nonempty)
    (hF : (connectedComponentIn Kᶜ z ∩ F.val).Nonempty) :
    Relation.ReflTransGen
      (fun A B => m0GeodesicFaceChainStep hp (connectedComponentIn Kᶜ z) A B ∧
        A.val ⊆ connectedComponentIn Kᶜ z ∧ B.val ⊆ connectedComponentIn Kᶜ z)
      F0 F := by
  have hchain := m0GeodesicFaceChain_reaches_of_isOpen_isPreconnected hp
    (connectedComponentIn Kᶜ z) hKc.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn F0 F hF0 hF
  apply Relation.ReflTransGen.mono (p := fun A B =>
    m0GeodesicFaceChainStep hp (connectedComponentIn Kᶜ z) A B ∧
      A.val ⊆ connectedComponentIn Kᶜ z ∧ B.val ⊆ connectedComponentIn Kᶜ z)
    (fun A B hAB =>
      ⟨hAB, m0GeodesicFaceChainStep_faces_subset_slit_component hp K hKc hK z hAB⟩)
    F0 F hchain

/-- Helper toward Lemma 5.6: the compactness route has only finitely many
geometric darts to consider along a continuous path. This includes repeated
visits and polyline bends, without asserting transversality of the path. -/
theorem m0Geodesic_path_meets_finitely_many_darts
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (γ : C(unitInterval, ℂ)) :
    {d : WholePlaneDart W |
      (Set.range γ ∩
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).image).Nonempty}.Finite := by
  exact (WholePlanePastGlueDrawing.glueDrawing W h hp H).locally_finite
    (Set.range γ) (isCompact_range γ.continuous).isBounded

/-- Helper toward Lemma 5.6: only finitely many faces meet a bounded open
disk. The finite induction route therefore has a finite geometric carrier;
this does not identify that carrier with the paper's finite slice. -/
theorem m0Geodesic_faces_meeting_ball_finite
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (q : ℂ) (r : ℝ) (hr : 0 < r) :
    {F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face |
      (ball q r ∩ F.val).Nonempty}.Finite := by
  classical
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨z, hzoff, hzball⟩ :=
    (m0Geodesic_drawing_compl_dense (H := H) (h := h) hp).exists_mem_open
      isOpen_ball ⟨q, mem_ball_self hr⟩
  obtain ⟨F0, hzF0⟩ := (P.faces_cover_compl z).mpr hzoff
  let E : Set (WholePlaneDart W) := {d | (ball q r ∩ (P.arc d).image).Nonempty}
  have hE : E.Finite := P.locally_finite (ball q r) isBounded_ball
  let target : WholePlaneDart W → P.Face := fun d =>
    WholePlaneGlueFaceCorrespondenceFull.dartFace W h hp H (wholePlaneDartFlip W d)
  apply ((finite_singleton F0).union (hE.image target)).subset
  intro F hF
  have hchain := m0GeodesicFaceChain_reaches_of_isOpen_isPreconnected hp
    (ball q r) isOpen_ball (convex_ball q r).isPreconnected F0 F
    ⟨z, hzball, hzF0⟩ hF
  rcases hchain.cases_tail with heq | ⟨G, _, hGF⟩
  · exact Or.inl heq
  · obtain ⟨d, _, hdF, w, hwd, hwball⟩ := hGF
    exact Or.inr ⟨d, ⟨w, hwball, hwd.1⟩,
      (WholePlaneGlueFaceCorrespondenceFull.dartFace_eq_iff W h hp H
        (wholePlaneDartFlip W d) F).mpr hdF⟩

/-- Helper toward Lemma 5.6: any collection of geometric edges of the
glued drawing has closed union, by local finiteness of compact arc images.
This applies to the union of the two rays and the geometric exterior boundary. -/
theorem m0Geodesic_arc_union_isClosed
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (S : Set (WholePlaneDart W)) :
    IsClosed (⋃ d ∈ S,
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).image) := by
  classical
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let B : WholePlaneDart W → Set ℂ := fun d => if d ∈ S then (P.arc d).image else ∅
  have hlocal : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have hsub (d : WholePlaneDart W) : B d ⊆ (P.arc d).image := by
    dsimp only [B]
    split_ifs
    · exact Subset.rfl
    · exact empty_subset _
  have hclosed : IsClosed (⋃ d, B d) := by
    apply (hlocal.subset hsub).isClosed_iUnion
    intro d
    dsimp only [B]
    split_ifs
    · exact (P.arc d).isCompact_image.isClosed
    · exact isClosed_empty
  have heq : (⋃ d, B d) = ⋃ d ∈ S, (P.arc d).image := by
    ext z
    simp only [B, mem_iUnion, mem_ite_empty_right, exists_prop]
  exact heq ▸ hclosed

/-- Helper toward Lemma 5.6: the strict interior of the future-map ambient
region is open and preconnected. A vertical translation of a half-plane gives
the geometric proof without a face-connectivity premise. -/
theorem m0Geodesic_strict_ambient_isOpen_isPreconnected :
    IsOpen {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} ∧
    IsPreconnected {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} := by
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  have hf : Continuous f := seamFun_continuous (shiftedStream W 0) h (H.1 0)
  refine ⟨isOpen_lt (hf.comp Complex.continuous_re) Complex.continuous_im, ?_⟩
  let φ : ℝ × ℝ → ℂ := fun p => ⟨p.1, f p.1 + p.2⟩
  have hφ : Continuous φ := by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk ((hf.comp continuous_fst).add continuous_snd))
  have heq : φ '' (univ ×ˢ Ioi (0 : ℝ)) = {z : ℂ | f z.re < z.im} := by
    ext z
    constructor
    · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
      exact lt_add_of_pos_right _ ht
    · intro hz
      refine ⟨(z.re, z.im - f z.re), ⟨mem_univ _, sub_pos.mpr hz⟩, ?_⟩
      apply Complex.ext
      · rfl
      · exact add_sub_cancel _ _
  rw [← heq]
  exact (isPreconnected_univ.prod isPreconnected_Ioi).image φ hφ.continuousOn

/-- Helper toward Lemma 5.6: a face retained in the closed future-map
region actually lies strictly above the cut. This excludes seam contacts
from face interiors while retaining geometric boundary edges in the map. -/
theorem m0Geodesic_retained_face_subset_strict_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    F.val ⊆ {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} := by
  rcases WholePlaneM0Drawing.face_side W h hp H F with hupper | hlower
  · exact hupper
  · obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    have hu : seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im := hFR hzF
    have hl : z.im < seamFun (shiftedStream W 0) h (H.1 0) z.re := hlower hzF
    exact False.elim (not_lt_of_ge hu hl)

/-- Helper toward Lemma 5.6: all retained future-map faces are joined by
finite geometric dual chains crossing strictly above the cut. This supplies
an ambient chain for the first-crossing approach to locating ray seeds;
it does not assert that the chain stays on one side of either geodesic. -/
theorem m0Geodesic_retained_faces_ambient_faceChain
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F0 F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF0R : F0.val ⊆ m0GeodesicAmbientRegion W H h)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    Relation.ReflTransGen
      (m0GeodesicFaceChainStep hp
        {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im}) F0 F := by
  have hupper := m0Geodesic_strict_ambient_isOpen_isPreconnected (H := H) (h := h)
  apply m0GeodesicFaceChain_reaches_of_isOpen_isPreconnected hp _ hupper.1 hupper.2 F0 F
  · obtain ⟨z, hz, hF0⟩ := F0.property
    have hzF0 : z ∈ F0.val := hF0 ▸ mem_connectedComponentIn hz
    exact ⟨z, m0Geodesic_retained_face_subset_strict_ambient hp F0 hF0R hzF0, hzF0⟩
  · obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    exact ⟨z, m0Geodesic_retained_face_subset_strict_ambient hp F hFR hzF, hzF⟩

/-- Helper toward Lemma 5.6: crossing strictly above the cut retains both
bordering faces in the future map. A lower face cannot have a strictly upper
point in its closure, by continuity of the seam height. -/
theorem m0GeodesicFaceChainStep_strict_ambient_retained
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G) :
    F.val ⊆ m0GeodesicAmbientRegion W H h ∧
      G.val ⊆ m0GeodesicAmbientRegion W H h := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨d, hdF, hdG, q, hqd, hqC⟩ := hFG
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  have hside (A : P.Face) (hqA : q ∈ closure A.val) :
      A.val ⊆ m0GeodesicAmbientRegion W H h := by
    rcases WholePlaneM0Drawing.face_side W h hp H A with hupper | hlower
    · intro z hz
      have hu : seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im := hupper hz
      exact hu.le
    · have hcl : closure A.val ⊆
          {z : ℂ | z.im ≤ seamFun (shiftedStream W 0) h (H.1 0) z.re} := by
        apply closure_minimal
        · intro z hz
          have hl : z.im < seamFun (shiftedStream W 0) h (H.1 0) z.re := hlower hz
          exact hl.le
        · exact isClosed_le Complex.continuous_im
            ((seamFun_continuous (shiftedStream W 0) h (H.1 0)).comp Complex.continuous_re)
      have hl : q.im ≤ seamFun (shiftedStream W 0) h (H.1 0) q.re := hcl hqA
      have hu : seamFun (shiftedStream W 0) h (H.1 0) q.re < q.im := hqC
      exact False.elim (not_lt_of_ge hl hu)
  refine ⟨hside F (P.dartBorders_arc_subset_closure hv d F hdF hqd.1), ?_⟩
  apply hside G
  apply P.dartBorders_arc_subset_closure hv (wholePlaneDartFlip W d) G hdG
  rw [P.arc_flip, Polyline.image_reverse_transfer]
  exact hqd.1

/-- Helper toward Lemma 5.6: each ambient-chain crossing has a literal
run-zero dart representative. Thus the clopen proof does not introduce past
darts which would be absent from the intrinsic future-side cell carrier. -/
theorem m0GeodesicFaceChainStep_strict_ambient_runZero
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G) :
    ∃ e : ℕ × Bool,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 e) F ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e.1, !e.2)) G ∧
      (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 e)).interior ∩
          {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im}).Nonempty := by
  let P := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hFR := (m0GeodesicFaceChainStep_strict_ambient_retained hp hFG).1
  obtain ⟨d, hdF, hdG, hcross⟩ := hFG
  have hclosed : IsClosed (m0GeodesicAmbientRegion W H h) :=
    isClosed_le ((seamFun_continuous (shiftedStream W 0) h (H.1 0)).comp
      Complex.continuous_re) Complex.continuous_im
  have harc : (P.arc d).image ⊆ m0GeodesicAmbientRegion W H h :=
    (P.dartBorders_arc_subset_closure (uibhbot_faceOrbit_dartVertex_surjective W H)
      d F hdF).trans (closure_minimal hFR hclosed)
  obtain ⟨e, he⟩ := (WholePlaneM0Drawing.m0_dart_iff W h hp H d).mp harc
  subst d
  exact ⟨e, hdF, hdG, hcross⟩

section RaySeeds

variable {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
  (wholePlaneEdgeι W 0
    (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: an ambient dual step from a right face to
a left face necessarily crosses a reverse dart of the actual geodesic.
This constructs the geometric seed at a first crossing. -/
theorem m0GeodesicFaceChain_right_left_crossing
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right)
    (hGL : G.val ⊆ m0GeodesicSideOpenRegion hp Q .left) :
    ∃ n : ℕ, (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (Q.codePath.edge n, true)) F := by
  have hret := m0GeodesicFaceChainStep_strict_ambient_retained hp hFG
  obtain ⟨e, heF, heG, _⟩ := m0GeodesicFaceChainStep_strict_ambient_runZero hp hFG
  have he : e.1 ∈ m0GeodesicEdges Q := by
    by_contra hoff
    have heR := (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
      hoff e.2 F hret.1 heF .right).mpr hFR
    have hGR := (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
      hoff (!e.2) G hret.2 heG .right).mp heR
    obtain ⟨z, hz, hG⟩ := G.property
    have hzG : z ∈ G.val := hG ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q) (hGL hzG) (hGR hzG)
  obtain ⟨n, hn⟩ := he
  have hbit : e.2 = true := by
    cases hb : e.2 with
    | false =>
      have heq : e = (Q.codePath.edge n, false) := Prod.ext hn.symm hb
      have hFL := boundaryGluing_forward_seam_face_left W h k longest hp Q n F hret.1
        (by simpa only [heq, m0GeodesicSeam] using heF)
      obtain ⟨z, hz, hF⟩ := F.property
      have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
      exact False.elim (disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        (hFL hzF) (hFR hzF))
    | true => rfl
  exact ⟨n, (Prod.ext hn.symm hbit : e = (Q.codePath.edge n, true)) ▸ heF⟩

/-- Helper toward Lemma 5.6: every retained right face has a finite
geometric face chain to a reverse-ray seed, with every face in the chain
retained on the right. Seed contact follows by first crossing of an ambient
chain to the forward face; it is not an exhaustion premise. -/
theorem m0GeodesicFaceChain_right_face_reaches_ray
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    ∃ (n : ℕ) (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, true)) A ∧
      A.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
      Relation.ReflTransGen
        (fun X Y => m0GeodesicFaceChainStep hp
          {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} X Y ∧
          X.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
          Y.val ⊆ m0GeodesicSideOpenRegion hp Q .right) F A := by
  obtain ⟨G, hGR, hbG⟩ := boundaryGluing_retained_borderingFace_exists W h hp
    (Q.codePath.edge 0)
  have hGL := boundaryGluing_forward_seam_face_left W h k longest hp Q 0 G hGR
    (by simpa only [m0GeodesicSeam] using hbG)
  have hchain := m0Geodesic_retained_faces_ambient_faceChain hp F G
    (fun z hz => (hFR hz).1) hGR
  revert hFR
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hGR'
    obtain ⟨z, hz, hG⟩ := G.property
    have hzG : z ∈ G.val := hG ▸ mem_connectedComponentIn hz
    exact False.elim (disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
      (hGL hzG) (hGR' hzG))
  | @head A B hAB _ ih =>
    intro hAR
    have hBR := (m0GeodesicFaceChainStep_strict_ambient_retained hp hAB).2
    obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp Q B hBR
    cases s with
    | left =>
      obtain ⟨n, hn⟩ := m0GeodesicFaceChain_right_left_crossing hp Q hAB hAR hs
      exact ⟨n, A, hn, hAR, .refl⟩
    | right =>
      obtain ⟨n, D, hn, hDR, hBD⟩ := ih hs
      exact ⟨n, D, hn, hDR, hBD.head ⟨hAB, hAR, hs⟩⟩

/-- Helper toward Lemma 5.6: two right faces joined by an ambient step
cross a literal run-zero edge off the geodesic. Thus the right-face chain
does not use a forbidden crossing of the slit itself. -/
theorem m0GeodesicFaceChainStep_right_off_ray
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right)
    (hGR : G.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    ∃ e : ℕ × Bool, e.1 ∉ m0GeodesicEdges Q ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 e) F ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e.1, !e.2)) G := by
  have hret := m0GeodesicFaceChainStep_strict_ambient_retained hp hFG
  obtain ⟨e, heF, heG, _⟩ := m0GeodesicFaceChainStep_strict_ambient_runZero hp hFG
  refine ⟨e, ?_, heF, heG⟩
  rintro ⟨n, hn⟩
  have hno (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (hAR : A.val ⊆ m0GeodesicSideOpenRegion hp Q .right)
      (hAM : A.val ⊆ m0GeodesicAmbientRegion W H h)
      (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, false)) A) : False := by
    have hAL := boundaryGluing_forward_seam_face_left W h k longest hp Q n A hAM
      (by simpa only [m0GeodesicSeam] using hb)
    obtain ⟨z, hz, hA⟩ := A.property
    have hzA : z ∈ A.val := hA ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q) (hAL hzA) (hAR hzA)
  cases hb : e.2 with
  | false =>
    exact hno F hFR hret.1
      ((Prod.ext hn.symm hb : e = (Q.codePath.edge n, false)) ▸ heF)
  | true =>
    apply hno G hGR hret.2
    simpa only [← hn, hb, Bool.not_true] using heG

/-- Helper toward Lemma 5.6: the complete geometric right-face exhaustion
uses only retained right faces and off-ray run-zero edge crossings, and ends
at a reverse-ray seed. Transfer to intrinsic cells of the preceding right
side is a separate obligation. -/
theorem m0GeodesicFaceChain_right_face_reaches_ray_off_ray
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    ∃ (n : ℕ) (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, true)) A ∧
      A.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
      Relation.ReflTransGen
        (fun X Y => ∃ e : ℕ × Bool, e.1 ∉ m0GeodesicEdges Q ∧
          X.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
          Y.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
          (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
            (wholePlaneDartι W 0 e) X ∧
          (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
            (wholePlaneDartι W 0 (e.1, !e.2)) Y) F A := by
  obtain ⟨n, A, hb, hAR, hchain⟩ := m0GeodesicFaceChain_right_face_reaches_ray hp Q F hFR
  refine ⟨n, A, hb, hAR, ?_⟩
  apply Relation.ReflTransGen.mono (r := fun X Y => m0GeodesicFaceChainStep hp
    {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} X Y ∧
      X.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
      Y.val ⊆ m0GeodesicSideOpenRegion hp Q .right) ?_ F A hchain
  intro X Y hXY
  obtain ⟨e, he, heX, heY⟩ := m0GeodesicFaceChainStep_right_off_ray hp Q
    hXY.1 hXY.2.1 hXY.2.2
  exact ⟨e, he, hXY.2.1, hXY.2.2, heX, heY⟩

end RaySeeds

end DirectedDistances.PaperProofs.Section5











































































































