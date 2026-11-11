/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization18

/-! # A single ambient comparison for the actual finite centered window -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

/-- Helper toward Proposition 3.9: one orientation-preserving ambient
homeomorphism simultaneously carries all positions and ordered dart arcs
of an agreeing window in an arbitrary later finite drawing into an arbitrary
whole-plane drawing. No recurrence or geometric comparison premise is added. -/
theorem uibotFiniteWindow_final_wholePlane_geometry
    (w : ℕ → Fin 3) (s m t : ℕ) (hst : s + m ≤ t)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (hcode : ∀ i < m, w (s + i) = shiftedStream W N i)
    (P : StageDrawing w t) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w t).IsOuter d) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ (v : Fin (kmswStage w t).nextVertex) (x : ℕ),
        x < (kmswStage (shiftedStream W N) m).nextVertex →
        v.val = kmswWindowVertexMapInf w s x →
        h (P.pos v) = G.pos (wholePlaneVertexι W N x)) ∧
      ∀ (d : StageDart (kmswStage w t).nextEdge)
        (a : StageDart (kmswStage (shiftedStream W N) m).nextEdge),
        d.1.val = kmswWindowEdgeMapInf w s a.1.val → d.2 = a.2 →
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ z, h ((P.arc d).toPath z) =
            (G.arc (wholePlaneDartι W N (a.1.val, a.2))).toPath (φ z) := by
  let u := shiftedStream W N
  let vcode := fun i => w (s + i)
  let C := familyQ vcode (monotone_family_all vcode) m
  let D := familyQ u (monotone_family_all u) m
  have hs : kmswStage vcode m = kmswStage u m := kmswStage_congr hcode
  obtain ⟨a, hao, hap, haa⟩ :=
    uibotFiniteWindow_final_ambient_canonical w s m t hst P U hU hborder
  obtain ⟨V, hV, _, hbV⟩ := uibotCanonicalStage_exterior u m
  obtain ⟨b, hbo, hbp, hba⟩ :=
    uibotWholePlaneStageDrawing_ambient_homeomorph W H G N m D V hV hbV
  refine ⟨a.trans b, hao.trans hbo, ?_, ?_⟩
  · intro v x hx hv
    have hx0 : x < (kmswStage vcode m).nextVertex := by rw [hs]; exact hx
    let x0 : Fin (kmswStage vcode m).nextVertex := ⟨x, hx0⟩
    have hxmap := kmswWindowVertexMapInf_eq_stage w s m x hx0
    have hv' : v = ⟨kmswWindowPatchVertexMap w s m x,
        ((kmswWindowPatchVertexMap_rel w s m).vertex_bound x hx0).trans_le
          (CutConverse.nextVertex_mono w hst)⟩ := Fin.ext (hv.trans hxmap)
    change b (a (P.pos v)) = _
    rw [hv', hap x0]
    have hp : C.pos x0 = D.pos ⟨x, hx⟩ := uibotLayoutPos_eq_of_prefix vcode u m hcode x
    rw [hp]
    exact hbp ⟨x, hx⟩
  · intro d e he hb
    have he0 : e.1.val < (kmswStage vcode m).nextEdge := by rw [hs]; exact e.1.isLt
    let e0 : StageDart (kmswStage vcode m).nextEdge := (⟨e.1.val, he0⟩, e.2)
    let f := kmswWindowDartMap w s m e0
    have hd : d = (f.1.castLE (kmswStage_nextEdge_mono w hst), e.2) := by
      apply Prod.ext
      · apply Fin.ext
        exact he.trans (kmswWindowEdgeMapInf_eq_stage w s m e.1.val he0)
      · exact hb
    obtain ⟨φ, hφ, hpφ⟩ := haa e0
    obtain ⟨ψ, hψ, hpψ⟩ := hba e
    refine ⟨φ.trans ψ, hψ.comp hφ, ?_⟩
    intro z
    change b (a ((P.arc d).toPath z)) = _
    rw [hd, hpφ]
    have hp : C.arc e0 = D.arc e := by
      change (if e.2 then (layoutArc vcode m e.1.val).reverse else layoutArc vcode m e.1.val) =
        (if e.2 then (layoutArc u m e.1.val).reverse else layoutArc u m e.1.val)
      rw [uibotLayoutArc_eq_of_prefix vcode u m hcode]
    rw [hp]
    exact hpψ (φ z)

/-- Helper toward Proposition 3.9: the successful centered observation
already gives one ambient comparison for the entire captured window in the
final finite drawing, with the exact infinite KMSW labels used by DC. -/
theorem uibotFiniteRootWindow_ambient_geometry {n N : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val)) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ (v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex) (x : ℕ),
        x < (kmswStage (shiftedStream W N) (2 * N)).nextVertex →
        v.val = kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N) x →
        h (P.pos v) = G.pos (wholePlaneVertexι W N x)) ∧
      ∀ (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge)
        (a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge),
        d.1.val = kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1.val →
        d.2 = a.2 →
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ z, h ((P.arc d).toPath z) =
            (G.arc (wholePlaneDartι W N (a.1.val, a.2))).toPath (φ z) := by
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hst : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  exact uibotFiniteWindow_final_wholePlane_geometry (finiteCodeExtend w)
    (j.val - N) (2 * N) (n - 1) hst W H G N hc P U hU hborder

private theorem simpleArc_parameter (γ δ : unitInterval → ℂ)
    (hγc : Continuous γ) (hδc : Continuous δ)
    (hγi : Function.Injective γ) (hδi : Function.Injective δ)
    (hrange : Set.range γ = Set.range δ) (b : Bool)
    (h0 : γ 0 = δ (if b then 1 else 0))
    (h1 : γ 1 = δ (if b then 0 else 1)) :
    ∃ φ : unitInterval ≃ₜ unitInterval,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, γ t = δ (φ t) := by
  let eγ : unitInterval ≃ₜ Set.range γ := (hγc.isClosedEmbedding hγi).isEmbedding.toHomeomorph
  let eδ : unitInterval ≃ₜ Set.range δ := (hδc.isClosedEmbedding hδi).isEmbedding.toHomeomorph
  let φ : unitInterval ≃ₜ unitInterval := (eγ.trans (Homeomorph.setCongr hrange)).trans eδ.symm
  have hmatch (t : unitInterval) : δ (φ t) = γ t :=
    congrArg Subtype.val (eδ.apply_symm_apply ((Homeomorph.setCongr hrange) (eγ t)))
  have hzero : φ 0 = if b then 1 else 0 := hδi ((hmatch 0).trans h0)
  have hone : φ 1 = if b then 0 else 1 := hδi ((hmatch 1).trans h1)
  refine ⟨φ, ?_, ?_, fun t => (hmatch t).symm⟩
  · intro hb
    apply φ.continuous.strictMono_of_inj_boundedOrder _ φ.injective
    change φ 0 ≤ φ 1
    rw [hzero, hone, hb]
    exact zero_le_one
  · intro hb
    apply φ.continuous.strictAnti_of_inj_boundedOrder _ φ.injective
    change φ 1 ≤ φ 0
    rw [hzero, hone, hb]
    exact zero_le_one

private theorem dart_flip_parameter
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (d : WholePlaneDart W) (b : Bool) :
    ∃ φ : unitInterval ≃ₜ unitInterval,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, (G.arc d).toPath t =
        (G.arc (if b then wholePlaneDartFlip W d else d)).toPath (φ t) := by
  let e := if b then wholePlaneDartFlip W d else d
  apply simpleArc_parameter (G.arc d).toPath (G.arc e).toPath
    (G.arc d).toPath.continuous (G.arc e).toPath.continuous
    ((G.arc d).toPath_injective (G.arc_length d) (G.arc_simple d))
    ((G.arc e).toPath_injective (G.arc_length e) (G.arc_simple e))
  · rw [Polyline.range_toPath, Polyline.range_toPath]
    cases b
    · rfl
    · exact (G.arc_image_flip d).symm
  · cases b
    · rfl
    · simp only [e, ite_true, Path.source, Path.target, G.arc_flip, Polyline.finish_reverse]
  · cases b
    · rfl
    · simp only [e, ite_true, Path.source, Path.target, G.arc_flip, Polyline.start_reverse]

private theorem frontier_eq_border_arcs_of_finite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hc : IsClosed K := hfin.isClosed_biUnion fun d _ =>
    (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hq
    by_contra hn
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds hn)
    have hqi := (P.face_open_frontier_subset_image hv F).2 hq
    have ha : ∃ d, q ∈ (P.arc d).image := by
      rcases hqi with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hv v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := ha
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases he : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hxf, hxb, hx⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hv F q d hi he (frontier_subset_closure hq) hs
      obtain ⟨e, hxe, heF⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex
        hv F hxf hx
      exact hsafe hxb (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqo := mem_openSegment_of_ne_left_right
        (fun h => he (Or.inl h.symm)) (fun h => he (Or.inr h.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hv d F hi hqo).mp
          (frontier_subset_closure hq) with hb | hb
      · exact hn (mem_iUnion₂.mpr ⟨d, hb, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hn
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hb, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · rintro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hv d F hd hqd

private theorem flip_storage (W : ℤ → Fin 3) (e : WholePlaneEdge W) (b c : Bool) :
    (e, c) = if Bool.xor b c then wholePlaneDartFlip W (e, b) else (e, b) := by
  cases b <;> cases c <;> rfl

private theorem interval_parameter_endpoints (φ : unitInterval ≃ₜ unitInterval)
    (b : Bool) (hm : b = false → StrictMono φ) (ha : b = true → StrictAnti φ) :
    φ 0 = (if b then 1 else 0) ∧ φ 1 = (if b then 0 else 1) := by
  cases b
  · constructor
    · obtain ⟨x, hx⟩ := φ.surjective 0
      apply le_antisymm _ bot_le
      calc
        φ 0 ≤ φ x := (hm rfl).monotone bot_le
        _ = 0 := hx
    · obtain ⟨x, hx⟩ := φ.surjective 1
      apply le_antisymm le_top
      calc
        1 = φ x := hx.symm
        _ ≤ φ 1 := (hm rfl).monotone le_top
  · constructor
    · obtain ⟨x, hx⟩ := φ.surjective 1
      apply le_antisymm le_top
      calc
        1 = φ x := hx.symm
        _ ≤ φ 0 := (ha rfl).antitone bot_le
    · obtain ⟨x, hx⟩ := φ.surjective 0
      apply le_antisymm _ bot_le
      calc
        φ 1 ≤ φ x := (ha rfl).antitone le_top
        _ = 0 := hx

private theorem open_eq_of_subset_frontier_disjoint {F S : Set ℂ}
    (ho : IsOpen F) (hn : F.Nonempty) (hc : IsPreconnected S)
    (hs : F ⊆ S) (hd : Disjoint (frontier F) S) : F = S := by
  apply Subset.antisymm hs
  apply hc.subset_of_closure_inter_subset ho
  · obtain ⟨x, hx⟩ := hn
    exact ⟨x, hs hx, hx⟩
  · rintro x ⟨hx, hxs⟩
    by_contra hnF
    exact Set.disjoint_left.mp hd
      (by rw [frontier, ho.interior_eq]; exact ⟨hx, hnF⟩) hxs

private theorem bounded_open_eq_of_frontier {S T : Set ℂ}
    (hoS : IsOpen S) (hcS : IsConnected S)
    (hoT : IsOpen T) (hcT : IsConnected T) (hbT : Bornology.IsBounded T)
    (hcE : IsPreconnected (closure S)ᶜ) (hbE : ¬ Bornology.IsBounded (closure S)ᶜ)
    (hf : frontier S = frontier T) : S = T := by
  have hd : Disjoint S (closure S)ᶜ := Set.disjoint_left.mpr
    (fun _ hx hy => hy (subset_closure hx))
  have hs : T ⊆ S ∪ (closure S)ᶜ := by
    intro x hx
    by_cases hxs : x ∈ S
    · exact Or.inl hxs
    · right
      intro hxc
      have hxf : x ∈ frontier S := by
        rw [frontier, hoS.interior_eq]; exact ⟨hxc, hxs⟩
      rw [hf, frontier, hoT.interior_eq] at hxf
      exact hxf.2 hx
  rcases hcT.isPreconnected.subset_or_subset hoS isClosed_closure.isOpen_compl hd hs with hin | hout
  · symm
    apply open_eq_of_subset_frontier_disjoint hoT hcT.nonempty hcS.isPreconnected hin
    rw [← hf, frontier, hoS.interior_eq]
    exact Set.disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  · have he := open_eq_of_subset_frontier_disjoint hoT hcT.nonempty hcE hout
      (Set.disjoint_left.mpr (fun _ hx hy => hy (frontier_subset_closure (hf.symm ▸ hx))))
    exact False.elim (hbE (he ▸ hbT))

private theorem cap_image_eq_of_frontier (C : DirectedDistances.KMSW.GraphCap)
    (g : ℂ ≃ₜ ℂ) (T : Set ℂ) (hoT : IsOpen T) (hcT : IsConnected T)
    (hbT : Bornology.IsBounded T) (hf : frontier (g '' C.region) = frontier T) :
    g '' C.region = T := by
  have hle : ∀ x ∈ Icc C.a C.b, C.low x ≤ C.high x := by
    intro x hx
    by_cases hxa : x = C.a
    · subst x; exact C.left_join.le
    by_cases hxb : x = C.b
    · subst x; exact C.right_join.le
    exact (C.separated x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩).le
  have hcl : closure C.region = closedGraphRegion C.a C.b C.low C.high :=
    closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous C.high_continuous
      C.separated C.left_join C.right_join
  have hext : (closure (g '' C.region))ᶜ = g '' (closure C.region)ᶜ := by
    rw [← g.image_closure, g.image_compl]
  apply bounded_open_eq_of_frontier
    (g.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous))
    ((isPathConnected_graphRegion C.ab C.low_continuous C.high_continuous C.separated).isConnected.image
      g g.continuous.continuousOn) hoT hcT hbT
  · change IsPreconnected (closure (g '' C.region))ᶜ
    rw [hext, hcl]
    exact (isPathConnected_compl_closedGraphRegion C.ab.le C.low_continuous
      C.high_continuous hle).isConnected.isPreconnected.image g g.continuous.continuousOn
  · change ¬ Bornology.IsBounded (closure (g '' C.region))ᶜ
    rw [hext, hcl]
    intro hb
    have hback := (hb.isCompact_closure.image g.symm.continuous).isBounded.subset
      (Set.image_mono (subset_closure : g '' (closedGraphRegion C.a C.b C.low C.high)ᶜ ⊆ _))
    have hb0 : Bornology.IsBounded (closedGraphRegion C.a C.b C.low C.high)ᶜ := by
      simpa only [Set.image_image, g.symm_apply_apply, Set.image_id'] using hback
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb0
    obtain ⟨z, hz, hRz⟩ := exists_norm_gt_compl_closedGraphRegion
      C.low_continuous C.high_continuous hle R
    exact (not_le_of_gt hRz) (hR z hz)
  · exact hf

/-- Helper toward Proposition 3.9: the single ambient window comparison
realizes all ball vertex, edge and retained-face equivalences, with the
monotone or antitone parameters required by the actual stored edge flips.
Bounded original face interiors are determined by their transported frontiers. -/
theorem uibotFiniteRootWindow_ambient_ballGeometry {n N r : ℕ} (hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let M := uibotFiniteStageExteriorMap P U hU hborder
    let rho := uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)
    let M' := uibotWholePlaneGeometricMap W H G hp
    let rho' := uibotWholePlaneGeometricRoot W H G
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      ∃ (V : {v // v ∈ d39GeomBallVertices M rho r} ≃
          {v // v ∈ d39GeomBallVertices M' rho' r})
        (E : {e // e ∈ d39GeomBallEdges M rho r} ≃
          {e // e ∈ d39GeomBallEdges M' rho' r}),
        (∀ v, h (M.pos v.val) = M'.pos (V v).val) ∧
        (∀ e, ∃ φ : unitInterval ≃ₜ unitInterval,
          (Bool.xor e.val.out.2 (E e).val.out.2 = false → StrictMono φ) ∧
          (Bool.xor e.val.out.2 (E e).val.out.2 = true → StrictAnti φ) ∧
          ∀ z, h (M.arc e.val z) = M'.arc (E e).val (φ z)) ∧
        (∀ e, (V ⟨M.src e.val, e.property.1⟩).val =
          if Bool.xor e.val.out.2 (E e).val.out.2 then M'.tgt (E e).val
          else M'.src (E e).val) ∧
        (∀ e, (V ⟨M.tgt e.val, e.property.2⟩).val =
          if Bool.xor e.val.out.2 (E e).val.out.2 then M'.src (E e).val
          else M'.tgt (E e).val) ∧
        (∀ e, M'.missing (E e).val ↔ M.missing e.val) ∧
        (∀ e (he : ¬ M.missing e.val),
          M'.forward ⟨(E e).val, uibotWholePlaneGeometricMap_noMissing W H G hp _⟩ =
            Bool.xor (M.forward ⟨e.val, he⟩)
              (Bool.xor e.val.out.2 (E e).val.out.2)) ∧
        (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val = rho'.1 ∧
        rho'.2 = Bool.xor rho.2
          (Bool.xor rho.1.out.2 (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val.out.2) ∧
        ∃ F : {F // F ∈ d39GeomRetainedFaces M rho r} ≃
            {F // F ∈ d39GeomRetainedFaces M' rho' r},
          ∀ K, h '' K.val.val = (F K).val.val := by
  classical
  dsimp only
  obtain ⟨h, ho, hpos, harc⟩ :=
    uibotFiniteRootWindow_ambient_geometry w j W H G P U hU hborder hwindow
  obtain ⟨V, hV⟩ := uibotFiniteRootWindow_exteriorVertexEquiv
    w j W H G hp P U hU hborder hwindow hcap
  obtain ⟨E, hE, hmiss, horient, hroot, hbool⟩ :=
    uibotFiniteRootWindow_exteriorGeometricEdgeData hr
      w j W H G hp P U hU hborder hwindow hcap
  obtain ⟨_, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hs := kmswStage_congr hc
  let M := uibotFiniteStageExteriorMap P U hU hborder
  let rho := uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)
  let M' := uibotWholePlaneGeometricMap W H G hp
  have hvmap : ∀ v, h (M.pos v.val) = M'.pos (V v).val := by
    intro v
    obtain ⟨x, hx, hv⟩ := (uibotFiniteRootWindow_exteriorBallVertices_iff
      w j (shiftedStream W N) P U hU hborder hwindow hcap v.val).mp v.property
    have hxl := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hxl' : x < (kmswStage (fun i => finiteCodeExtend w (j.val - N + i)) (2 * N)).nextVertex := by
      rw [hs]; exact hxl
    change h (P.pos v.val) = G.pos (V v).val
    rw [hV x hx v hv.symm]
    exact hpos v.val x hxl (hv.symm.trans
      (kmswWindowVertexMapInf_eq_stage (finiteCodeExtend w) (j.val - N) (2 * N) x hxl').symm)
  have hamap : ∀ e, ∃ φ : unitInterval ≃ₜ unitInterval,
      (Bool.xor e.val.out.2 (E e).val.out.2 = false → StrictMono φ) ∧
      (Bool.xor e.val.out.2 (E e).val.out.2 = true → StrictAnti φ) ∧
      ∀ z, h (M.arc e.val z) = M'.arc (E e).val (φ z) := by
    intro e
    have he := (uibotFiniteStageExteriorBallEdge_iff P U hU hborder j.val
      (by have := j.isLt; omega) r e.val).mp e.property
    obtain ⟨a, _, hae⟩ := (uibotFiniteRootWindow_rootBallEdges_bijOn
      w j (shiftedStream W N) hwindow hcap).surjOn ⟨e.val.out.1.isLt, he⟩
    have hal : a.val < (kmswStage (shiftedStream W N) (2 * N)).nextEdge := by
      rw [← hs]; exact a.isLt
    have hid : e.val.out.1.val = kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.val :=
      hae.symm.trans (kmswWindowEdgeMapInf_eq_stage
        (finiteCodeExtend w) (j.val - N) (2 * N) a.val a.isLt).symm
    let d : WholePlaneDart W := wholePlaneDartι W N (a.val, e.val.out.2)
    let flip := Bool.xor e.val.out.2 (E e).val.out.2
    have hout : (E e).val.out = if flip then wholePlaneDartFlip W d else d := by
      have heq : (E e).val.out = (wholePlaneEdgeι W N a.val, (E e).val.out.2) :=
        Prod.ext (hE e a.val hid) rfl
      exact heq.trans
        (flip_storage W (wholePlaneEdgeι W N a.val) e.val.out.2 (E e).val.out.2)
    obtain ⟨φ, hφ, hpφ⟩ := harc e.val.out (⟨a.val, hal⟩, e.val.out.2) hid rfl
    obtain ⟨ψ, hψm, hψa, hpψ⟩ := dart_flip_parameter W H G d flip
    refine ⟨φ.trans ψ, fun hb => (hψm hb).comp hφ,
      fun hb => (hψa hb).comp_strictMono hφ, ?_⟩
    intro z
    change h ((P.arc e.val.out).toPath z) = (G.arc (E e).val.out).toPath (ψ (φ z))
    rw [hout]
    exact (hpφ z).trans (hpψ (φ z))

  have hfaces : ∃ F : {F // F ∈ d39GeomRetainedFaces M rho r} ≃
        {F // F ∈ d39GeomRetainedFaces M' (uibotWholePlaneGeometricRoot W H G) r},
      ∀ K, h '' K.val.val = (F K).val.val := by
    obtain ⟨F, hF⟩ := uibotFiniteRootWindow_retainedFaces_wholePlaneEquiv
      w j W H G hp P U hU hborder hwindow hcap
    refine ⟨F, ?_⟩
    intro K
    obtain ⟨q, hq, hlabel, hfin, hwhole⟩ := hF K
    have hfront : h '' frontier K.val.val = frontier (F K).val.val := by
      have hbound : {d | G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv (F K).val)}.Finite := by
        apply Set.Finite.subset ((stageTriangleDartList (shiftedStream W N) q).finite_toSet.image
          (wholePlaneDartι W N))
        intro d hd
        obtain ⟨a, ha, he⟩ := (hwhole d).mp hd
        exact ⟨a, ha, he⟩
      have hFP := frontier_eq_border_arcs_of_finite P
        (kmswStageDrawing_vertex_surjective _ _) (P.toPlaneGraphDrawingFaceEquiv K.val)
        (Set.toFinite _)
      have hFG := frontier_eq_border_arcs_of_finite G
        (uibhbot_faceOrbit_dartVertex_surjective W H)
        (G.toPlaneGraphDrawingFaceEquiv (F K).val) hbound
      change frontier K.val.val = _ at hFP
      change frontier (F K).val.val = _ at hFG
      rw [hFP, hFG]
      have hpath (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge)
          (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList (shiftedStream W N) q)
          (he : (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2)) :
          h '' (P.arc d).image = (G.arc (wholePlaneDartι W N a)).image := by
        have hal := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
        obtain ⟨φ, _, hm⟩ := harc d (⟨a.1, hal⟩, a.2)
          (congrArg Prod.fst he).symm (congrArg Prod.snd he).symm
        rw [← Polyline.range_toPath, ← Polyline.range_toPath]
        ext z
        constructor
        · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
          exact ⟨φ t, (hm t).symm⟩
        · rintro ⟨t, rfl⟩
          refine ⟨(P.arc d).toPath (φ.symm t), ⟨φ.symm t, rfl⟩, ?_⟩
          exact (hm (φ.symm t)).trans (congrArg (fun z => (G.arc (wholePlaneDartι W N a)).toPath z)
            (φ.apply_symm_apply t))
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp hx
        obtain ⟨a, ha, he⟩ := (hfin d).mp hd
        exact mem_iUnion₂.mpr ⟨wholePlaneDartι W N a,
          (hwhole _).mpr ⟨a, ha, rfl⟩,
          (hpath d a ha he) ▸ mem_image_of_mem h hx⟩
      · intro hz
        obtain ⟨d, hd, hz⟩ := mem_iUnion₂.mp hz
        obtain ⟨a, ha, he⟩ := (hwhole d).mp hd
        have hal := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
        obtain ⟨hvalid, _⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
        have hst : j.val - N + 2 * N ≤ n - 1 := by
          have := hvalid.1
          have := hvalid.2
          omega
        have halloc := (uibotWindowDart_endpoint_transport (finiteCodeExtend w)
          (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc a hal).1
        let d0 : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge :=
          (⟨kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, halloc⟩, a.2)
        have hz' : z ∈ h '' (P.arc d0).image := by
          rw [hpath d0 a ha rfl, he]
          exact hz
        obtain ⟨x, hx, hxe⟩ := hz'
        exact ⟨x, mem_iUnion₂.mpr ⟨d0, (hfin d0).mpr ⟨a, ha, rfl⟩, hx⟩, hxe⟩
    obtain ⟨g0, _, hcaps⟩ := uibotFiniteRootWindow_retainedFaces_canonicalCaps
      w j (shiftedStream W N) P U hU hborder hwindow hcap
    obtain ⟨i, hi⟩ := hcaps K.val K.property
    let C := (familyG (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)).cap i
    let g := g0.trans h
    have himg : g '' C.region = h '' K.val.val := by
      rw [hi, Set.image_image]
      rfl
    have hconn : IsConnected (F K).val.val := by
      obtain ⟨z, hz, he⟩ := (F K).val.property
      rw [he]
      exact isConnected_connectedComponentIn_iff.mpr hz
    have hopen : IsOpen (F K).val.val :=
      (G.face_open_frontier_subset_image (uibhbot_faceOrbit_dartVertex_surjective W H)
        (G.toPlaneGraphDrawingFaceEquiv (F K).val)).1
    obtain ⟨T, hT, hbT, _⟩ := uibotWholePlaneStageDrawing_triangleFace W H G N (2 * N) q hq
    have hbounded : Bornology.IsBounded (F K).val.val := by
      rw [hlabel, ← hT]
      exact hbT
    rw [← himg]
    apply cap_image_eq_of_frontier C g (F K).val.val hopen hconn hbounded
    rw [himg, ← h.image_frontier]
    exact hfront

  refine ⟨h, ho, V, E, hvmap, hamap, ?_, ?_, hmiss, horient, hroot, hbool, hfaces⟩
  · intro e
    obtain ⟨φ, hm, ha, he⟩ := hamap e
    have h0 := (interval_parameter_endpoints φ _ hm ha).1
    apply M'.pos_injective
    calc
      M'.pos (V ⟨M.src e.val, e.property.1⟩).val = h (M.pos (M.src e.val)) :=
        (hvmap _).symm
      _ = M'.pos (if Bool.xor e.val.out.2 (E e).val.out.2 then M'.tgt (E e).val
          else M'.src (E e).val) := by
        have he0 := he 0
        rw [h0] at he0
        cases hb : Bool.xor e.val.out.2 (E e).val.out.2 <;>
          simpa only [hb, Bool.false_eq_true, ite_false, ite_true, Path.source, Path.target] using he0
  · intro e
    obtain ⟨φ, hm, ha, he⟩ := hamap e
    have h1 := (interval_parameter_endpoints φ _ hm ha).2
    apply M'.pos_injective
    calc
      M'.pos (V ⟨M.tgt e.val, e.property.2⟩).val = h (M.pos (M.tgt e.val)) :=
        (hvmap _).symm
      _ = M'.pos (if Bool.xor e.val.out.2 (E e).val.out.2 then M'.src (E e).val
          else M'.tgt (E e).val) := by
        have he1 := he 1
        rw [h1] at he1
        cases hb : Bool.xor e.val.out.2 (E e).val.out.2 <;>
          simpa only [hb, Bool.false_eq_true, ite_false, ite_true, Path.source, Path.target] using he1

/-- Helper toward Proposition 3.9: the exact deterministic comparison DC,
with every original binder and every field of the geometric ball isomorphism.
One ambient homeomorphism realizes vertices, arcs and retained original faces. -/
theorem uibotDeterministicComparison_proved : UIBOTDeterministicComparison := by
  intro n N r hr w j W H G hp P U hU hborder hwindow hcap
  obtain ⟨h, ho, V, E, hpos, harcs, hsrc, htgt, hmiss, horient, hroot, hbool, F, hface⟩ :=
    uibotFiniteRootWindow_ambient_ballGeometry hr w j W H G hp P U hU hborder hwindow hcap
  choose φ hm ha harc using harcs
  exact ⟨{
    radius_pos := hr
    h := h
    orientationPreserving := ho
    vertexEquiv := V
    edgeEquiv := E
    faceEquiv := F
    edgeFlip := fun e => Bool.xor e.val.out.2 (E e).val.out.2
    pos_map := hpos
    edgeParam := φ
    edgeParam_mono := hm
    edgeParam_anti := ha
    arc_map := harc
    src_map := hsrc
    tgt_map := htgt
    missing_map := hmiss
    orientation_map := horient
    root_edge_map := hroot
    root_bool_map := hbool
    face_image_map := hface }⟩

end DirectedDistances.PaperProofs.Section3
end
