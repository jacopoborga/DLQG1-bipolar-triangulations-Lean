/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.WholePlaneRunSubmap
public import DirectedDistances.PaperProofs.SourceResults.FutureMapDefinition
public import DirectedDistances.KMSW.WholePlanePastGlueDrawing
public import DirectedDistances.KMSW.WholePlaneStartIso
public import DirectedDistances.PlanarMap.EdgeRestrictedDrawing
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer

































public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap



theorem futureMaps_vertex_range_mono (W : ℤ → Fin 3) :
    Monotone (fun N : ℕ => Set.range (wholePlaneVertexι W N)) := by
  intro N M hNM v hv
  obtain ⟨x, rfl⟩ := hv
  exact ⟨wholePlaneVertexTrans W N M hNM x,
    congrFun (wholePlaneVertexι_trans W N M hNM) x⟩



theorem futureMaps_edge_range_mono (W : ℤ → Fin 3) :
    Monotone (fun N : ℕ => Set.range (wholePlaneEdgeι W N)) := by
  intro N M hNM e he
  obtain ⟨x, rfl⟩ := he
  exact ⟨wholePlaneEdgeTrans W N M hNM x,
    congrFun (wholePlaneEdgeι_trans W N M hNM) x⟩



theorem futureMaps_dart_range_mono (W : ℤ → Fin 3) :
    Monotone (fun N : ℕ => Set.range (wholePlaneDartι W N)) := by
  intro N M hNM d hd
  obtain ⟨x, rfl⟩ := hd
  exact ⟨wholePlaneDartTrans W N M hNM x,
    congrFun (wholePlaneDartι_trans W N M hNM) x⟩



theorem futureMaps_iUnion_vertices (W : ℤ → Fin 3) :
    (⋃ N : ℕ, Set.range (wholePlaneVertexι W N)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨N, x, hx⟩ := wholePlaneVertex_has_run_rep W v
  exact Set.mem_iUnion.mpr ⟨N, x, hx⟩



theorem futureMaps_iUnion_edges (W : ℤ → Fin 3) :
    (⋃ N : ℕ, Set.range (wholePlaneEdgeι W N)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  obtain ⟨N, x, hx⟩ := wholePlaneEdge_has_run_rep W e
  exact Set.mem_iUnion.mpr ⟨N, x, hx⟩



theorem futureMaps_iUnion_darts (W : ℤ → Fin 3) :
    (⋃ N : ℕ, Set.range (wholePlaneDartι W N)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro d
  obtain ⟨N, x, hx⟩ := wholePlaneDart_has_run_rep W d
  exact Set.mem_iUnion.mpr ⟨N, x, hx⟩



theorem futureMaps_present_edges_mono (W : ℤ → Fin 3) :
    Monotone (fun N : ℕ =>
      wholePlaneEdgeι W N '' {e | EdgePresent (shiftedStream W N) e}) := by
  intro N M hNM e he
  obtain ⟨x, hx, rfl⟩ := he
  exact ⟨wholePlaneEdgeTrans W N M hNM x,
    wholePlaneRun_present_mono W N M hNM x hx,
    congrFun (wholePlaneEdgeι_trans W N M hNM) x⟩



theorem futureMaps_iUnion_present_edges (W : ℤ → Fin 3) :
    (⋃ N : ℕ, wholePlaneEdgeι W N '' {e | EdgePresent (shiftedStream W N) e}) =
      {e | wholePlaneEdgePresent W e} := by
  ext e
  constructor
  · intro he
    obtain ⟨N, x, hx, rfl⟩ := Set.mem_iUnion.mp he
    exact wholePlaneRun_present_colimit W N x hx
  · intro he
    obtain ⟨N, x, rfl⟩ := wholePlaneEdge_has_run_rep W e
    obtain ⟨M, hNM, hp⟩ := (wholePlaneEdgePresent_ι W N x).mp he
    refine Set.mem_iUnion.mpr ⟨M, wholePlaneEdgeTrans W N M hNM x, ?_,
      congrFun (wholePlaneEdgeι_trans W N M hNM) x⟩
    exact hp M le_rfl



theorem futureMaps_present_edge_capture (W : ℤ → Fin 3)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (e : WholePlaneEdge W) :
    ∃ N x, EdgePresent (shiftedStream W N) x ∧ wholePlaneEdgeι W N x = e := by
  have he : e ∈ ⋃ N : ℕ,
      wholePlaneEdgeι W N '' {x | EdgePresent (shiftedStream W N) x} := by
    rw [futureMaps_iUnion_present_edges]
    exact hp e
  exact Set.mem_iUnion.mp he



theorem futureMaps_finite_dart_capture (W : ℤ → Fin 3)
    (s : Finset (WholePlaneDart W)) :
    ∃ N : ℕ, ∀ d ∈ s, d ∈ Set.range (wholePlaneDartι W N) := by
  let instFutureMapsExhaustWholePlaneDartDecidableEq : DecidableEq (WholePlaneDart W) :=
    Classical.decEq _
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun d hd => (Finset.notMem_empty d hd).elim⟩
  | @insert d s hd ih =>
    obtain ⟨N, x, hx⟩ := wholePlaneDart_has_run_rep W d
    obtain ⟨M, hM⟩ := ih
    refine ⟨max N M, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact futureMaps_dart_range_mono W (Nat.le_max_left N M) ⟨x, hx⟩
    · exact futureMaps_dart_range_mono W (Nat.le_max_right N M) (hM a ha)



theorem futureMaps_drawing_overlap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (N M : ℕ) (hNM : N ≤ M) :
    (∀ v, G.pos (wholePlaneVertexι W M (wholePlaneVertexTrans W N M hNM v)) =
      G.pos (wholePlaneVertexι W N v)) ∧
    (∀ d, G.arc (wholePlaneDartι W M (wholePlaneDartTrans W N M hNM d)) =
      G.arc (wholePlaneDartι W N d)) := by
  exact ⟨fun v => congrArg G.pos (congrFun (wholePlaneVertexι_trans W N M hNM) v),
    fun d => congrArg G.arc (congrFun (wholePlaneDartι_trans W N M hNM) d)⟩



theorem futureMaps_iUnion_drawing_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    (⋃ N : ℕ, (Set.range (fun v => G.pos (wholePlaneVertexι W N v)) ∪
      {z | ∃ d, z ∈ (G.arc (wholePlaneDartι W N d)).image})) = G.image := by
  ext z
  constructor
  · intro hz
    obtain ⟨N, hz⟩ := Set.mem_iUnion.mp hz
    rcases hz with ⟨v, rfl⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨wholePlaneVertexι W N v, rfl⟩
    · exact Or.inr ⟨wholePlaneDartι W N d, hd⟩
  · intro hz
    rcases hz with ⟨v, rfl⟩ | ⟨d, hd⟩
    · obtain ⟨N, x, rfl⟩ := wholePlaneVertex_has_run_rep W v
      exact Set.mem_iUnion.mpr ⟨N, Or.inl ⟨x, rfl⟩⟩
    · obtain ⟨N, x, rfl⟩ := wholePlaneDart_has_run_rep W d
      exact Set.mem_iUnion.mpr ⟨N, Or.inr ⟨x, hd⟩⟩



theorem futureMaps_cut_edges (W : ℤ → Fin 3) (n : ℤ)
    (phi : WholePlaneStartIso W n)
    (Hn : WholePlaneRotationHypothesis (shiftWordInt W n))
    (h : BoundaryHitWitnesses (shiftedStream (shiftWordInt W n) 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWordInt W n)
      (wholePlaneEdgeι (shiftWordInt W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWordInt W n) 0)
          (boundaryHitTime (shiftedStream (shiftWordInt W n) 0) h (k - 1))))) :
    phi.edge '' (m0CutData (shiftWordInt W n) Hn h hLL).edges =
      Set.range (lemma38StartEdgeι W n) := by
  rw [M0CutData.edges_eq _ h hLL]
  ext e
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (phi.iota_edge a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨wholePlaneEdgeι (shiftWordInt W n) 0 a, ⟨a, rfl⟩, phi.iota_edge a⟩

private theorem futureMaps_dart_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneDartι W N) := by
  intro a b hab
  exact Prod.ext (wholePlaneEdgeι_injective W N (congrArg Prod.fst hab))
    (congrArg (fun d : WholePlaneDart W => d.2) hab)

private theorem futureMaps_three_cycle_orbit {D : Type*} (f : Equiv.Perm D)
    (a b c : D) (hc : FaceSucc3Cycle f a b c) (e : D) :
    f.SameCycle a e ↔ e = a ∨ e = b ∨ e = c := by
  have hmem (z : ℤ) : (f ^ z) a = a ∨ (f ^ z) a = b ∨ (f ^ z) a = c := by
    induction z using Int.induction_on with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      rcases ih with ha | hb | hd
      · exact Or.inr (Or.inl ((congrArg f ha).trans hc.1))
      · exact Or.inr (Or.inr ((congrArg f hb).trans hc.2.1))
      · exact Or.inl ((congrArg f hd).trans hc.2.2.1)
    | pred n ih =>
      rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      rcases ih with ha | hb | hd
      · exact Or.inr (Or.inr ((congrArg f.symm ha).trans
          ((f.symm_apply_eq).mpr hc.2.2.1.symm)))
      · exact Or.inl ((congrArg f.symm hb).trans ((f.symm_apply_eq).mpr hc.1.symm))
      · exact Or.inr (Or.inl ((congrArg f.symm hd).trans
          ((f.symm_apply_eq).mpr hc.2.1.symm)))
  constructor
  · rintro ⟨z, rfl⟩
    exact hmem z
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa only [zpow_one] using hc.1⟩
    · exact ⟨2, by simpa only [show (2 : ℤ) = 1 + 1 by omega,
        zpow_add, zpow_one, Equiv.Perm.mul_apply, hc.1] using hc.2.1⟩

private theorem futureMaps_triangle_cycle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    FaceSucc3Cycle (wholePlaneFaceSucc W H)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).1)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).2.1)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).2.2) := by
  let t := stageTriangleDartTriple (shiftedStream W N) j
  have hc := kmswInfFaceSucc_stageTriangle_cycle (shiftedStream W N) (H.1 N) j
  have hm : ∀ d, d ∈ [t.1, t.2.1, t.2.2] →
      wholePlaneFaceSucc W H (wholePlaneDartι W N d) =
        wholePlaneDartι W N (kmswInfFaceSucc (shiftedStream W N) (H.1 N) d) :=
    fun d hd => wholePlaneFaceSucc_run_of_triangle W H N d ⟨j, hd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hm t.1 (by simp only [List.mem_cons, true_or])).trans
      (congrArg (wholePlaneDartι W N) hc.1)
  · exact (hm t.2.1 (by simp only [List.mem_cons, true_or, or_true])).trans
      (congrArg (wholePlaneDartι W N) hc.2.1)
  · exact (hm t.2.2 (by simp only [List.mem_cons, true_or, or_true])).trans
      (congrArg (wholePlaneDartι W N) hc.2.2.1)
  · exact fun he => hc.2.2.2.1 (futureMaps_dart_injective W N he)
  · exact fun he => hc.2.2.2.2.1 (futureMaps_dart_injective W N he)
  · exact fun he => hc.2.2.2.2.2 (futureMaps_dart_injective W N he)



theorem futureMaps_triangle_orbit (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) (d : WholePlaneDart W) :
    (wholePlaneFaceSucc W H).SameCycle
        (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).1) d ↔
      d ∈ wholePlaneDartι W N ''
        {a | a ∈ stageTriangleDartList (shiftedStream W N) j} := by
  rw [futureMaps_three_cycle_orbit _ _ _ _ (futureMaps_triangle_cycle W H N j)]
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨a, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)




theorem futureMaps_dart_triangle_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hPast : BoundaryHitWitnesses (kmswPastCode W)) (D : WholePlaneDart W) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      D ∈ wholePlaneDartι W N ''
        {d | d ∈ stageTriangleDartList (shiftedStream W N) j} := by
  rcases wholePlaneFaceSucc_runZero_or_past W H
    (WholePlanePastGlueData.past_finiteIncidence W H) hPast h0 D with
    ⟨d, rfl, ⟨j, hd⟩, _⟩ | ⟨d, rfl, ⟨j, hd⟩, _⟩
  · exact ⟨0, j, d, hd, rfl⟩
  · let N := j.val + 1
    have hj : j.val < N := Nat.lt_succ_self _
    obtain ⟨k, _, hk⟩ := kmswRevDart_triangle_words (shiftedStream W N)
      (kmswPastCode W) N (kmswPastCode_rev W N) j hj
    refine ⟨N, k, reversalDartValMap (shiftedStream W N) (kmswPastCode W) N d,
      hk.mem_iff.mp (List.mem_map.mpr ⟨d, hd, rfl⟩), ?_⟩
    exact (kmswPastDart_eq_stage W N d
      (stageTriangleDartList_lt (kmswPastCode W) N j hj d hd)).symm




theorem futureMaps_glued_face_triangle_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hPast : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h0 hPast H).Face) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      {D | (WholePlanePastGlueDrawing.glueDrawing W h0 hPast H).dartBorders D F} =
        wholePlaneDartι W N ''
          {d | d ∈ stageTriangleDartList (shiftedStream W N) j} := by
  obtain ⟨D, hD⟩ := WholePlaneGlueFaceCorrespondenceFull.face_bordered W h0 hPast H F
  obtain ⟨N, j, hj⟩ := futureMaps_dart_triangle_capture W H h0 hPast D
  have hd := (futureMaps_triangle_orbit W H N j D).mpr hj
  refine ⟨N, j, Set.ext (fun E => ?_)⟩
  constructor
  · intro hE
    exact (futureMaps_triangle_orbit W H N j E).mp
      (hd.trans ((WholePlaneGlueFaceCorrespondenceFull.faceOrbit_iff_common_face
        W h0 hPast H D E).mpr ⟨F, hD, hE⟩))
  · intro hE
    obtain ⟨F', hD', hE'⟩ :=
      (WholePlaneGlueFaceCorrespondenceFull.faceOrbit_iff_common_face
        W h0 hPast H D E).mp
          (hd.symm.trans ((futureMaps_triangle_orbit W H N j E).mpr hE))
    have hFF := WholePlaneGlueSeamFaces.glueSeamFaces_dartBorders_unique
      W h0 hPast H D F' F hD' hD
    exact hFF ▸ hE'



theorem futureMaps_dart_range_flip (W : ℤ → Fin 3) (N : ℕ)
    (d : WholePlaneDart W) :
    d ∈ Set.range (wholePlaneDartι W N) ↔
      wholePlaneDartFlip W d ∈ Set.range (wholePlaneDartι W N) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(a.1, !a.2), rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨(a.1, !a.2),
      (congrArg (wholePlaneDartFlip W) ha).trans
        (wholePlaneDartFlip_involutive W d)⟩




@[expose] noncomputable def futureMapsRunDrawing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) (N : ℕ) :=
  restrictDrawing G (Set.range (wholePlaneDartι W N)) (futureMaps_dart_range_flip W N)



theorem futureMaps_run_drawing_image_mono (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    Monotone (fun N : ℕ => (futureMapsRunDrawing W H G N).image) := by
  intro N M hNM z hz
  change z ∈ (restrictDrawing G _ _).image at hz ⊢
  rw [restrictDrawing_image_eq G (Set.range (wholePlaneDartι W N))
    (futureMaps_dart_range_flip W N)] at hz
  rw [restrictDrawing_image_eq G (Set.range (wholePlaneDartι W M))
    (futureMaps_dart_range_flip W M)]
  rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
  · obtain ⟨d, hd, hbase⟩ := v.property
    exact Or.inl ⟨⟨v.val, d, futureMaps_dart_range_mono W hNM hd, hbase⟩, hv⟩
  · exact Or.inr ⟨⟨d.val, futureMaps_dart_range_mono W hNM d.property⟩, hd⟩



theorem futureMaps_iUnion_run_drawing_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    (⋃ N : ℕ, (futureMapsRunDrawing W H G N).image) = G.image := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun N => restrictDrawing_image_subset G _ _
  · intro z hz
    rw [G.image_eq_union_arcs (WholePlanePastGlueData.vertex_incident W)] at hz
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
    obtain ⟨N, a, ha⟩ := wholePlaneDart_has_run_rep W d
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    change z ∈ (restrictDrawing G _ _).image
    rw [restrictDrawing_image_eq G (Set.range (wholePlaneDartι W N))
      (futureMaps_dart_range_flip W N)]
    exact Or.inr ⟨⟨d, a, ha⟩, hd⟩





theorem futureMaps_bounded_face_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (F : G.Face) (hF : Bornology.IsBounded F.val) :
    ∃ (N : ℕ) (F' : (futureMapsRunDrawing W H G N).Face),
      F'.val = F.val ∧
      ∀ d : RestrictedDart (WholePlaneDart W) (Set.range (wholePlaneDartι W N)),
        (futureMapsRunDrawing W H G N).dartBorders d F' ↔ G.dartBorders d.val F := by
  let s : Set (WholePlaneDart W) := {d | (closure F.val ∩ (G.arc d).image).Nonempty}
  have hs : s.Finite := G.locally_finite (closure F.val) hF.closure
  obtain ⟨N, hN⟩ := futureMaps_finite_dart_capture W hs.toFinset
  have hXY : G.image ∩ closure F.val ⊆ (futureMapsRunDrawing W H G N).image := by
    intro z hz
    have hzG := hz.1
    rw [G.image_eq_union_arcs (WholePlanePastGlueData.vertex_incident W)] at hzG
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hzG
    have hdN : d ∈ Set.range (wholePlaneDartι W N) :=
      hN d (hs.mem_toFinset.mpr ⟨z, hz.2, hd⟩)
    change z ∈ (restrictDrawing G _ _).image
    rw [restrictDrawing_image_eq G (Set.range (wholePlaneDartι W N))
      (futureMaps_dart_range_flip W N)]
    exact Or.inr ⟨⟨d, hdN⟩, hd⟩
  have hYX : (futureMapsRunDrawing W H G N).image ∩ F.val ⊆ G.image :=
    fun _ hz => restrictDrawing_image_subset G _ _ hz.1
  obtain ⟨F', hval⟩ := G.face_of_agree (futureMapsRunDrawing W H G N)
    (WholePlanePastGlueData.vertex_incident W) hXY hYX F Set.Subset.rfl
  refine ⟨N, F', hval, fun d => ?_⟩
  exact G.dartBorders_congr (futureMapsRunDrawing W H G N) F F'
    (restrictDrawing_arc G _ _ d) hval





theorem futureMaps_glued_face_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hPast : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h0 hPast H).Face) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hPast H
    ∃ (N : ℕ) (F' : (futureMapsRunDrawing W H G N).Face),
      F'.val = F.val ∧
      ∀ d : RestrictedDart (WholePlaneDart W) (Set.range (wholePlaneDartι W N)),
        (futureMapsRunDrawing W H G N).dartBorders d F' ↔ G.dartBorders d.val F := by
  apply futureMaps_bounded_face_capture
  rw [isBounded_iff_forall_norm_le]
  have hb := WholePlanePastGlueDrawing.glueDrawing_face_bounded W h0 hPast H F
  change ¬ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖ at hb
  push Not at hb
  exact hb



theorem futureMaps_integer_vertices_antitone (W : ℤ → Fin 3) :
    Antitone (fun n : ℤ => Set.range (lemma38StartVertexι W n)) := by
  intro n m hnm v hv
  simp only [Set.mem_range] at hv ⊢
  by_cases hn : n ≤ 0
  · by_cases hm : m ≤ 0
    · have ha : m.natAbs ≤ n.natAbs := by
        have hn' := Int.ofNat_natAbs_of_nonpos hn
        have hm' := Int.ofNat_natAbs_of_nonpos hm
        omega
      simp only [lemma38StartVertexι, ite_eq_left hm] at hv
      simp only [lemma38StartVertexι, ite_eq_left hn]
      exact futureMaps_vertex_range_mono W ha hv
    · obtain ⟨a, ha⟩ := hv
      simp only [lemma38StartVertexι, ite_eq_right hm] at ha
      simp only [lemma38StartVertexι, ite_eq_left hn]
      exact futureMaps_vertex_range_mono W (Nat.zero_le n.natAbs) ⟨_, ha⟩
  · have hm : ¬ m ≤ 0 := by omega
    obtain ⟨a, ha⟩ := hv
    simp only [lemma38StartVertexι, ite_eq_right hm] at ha
    simp only [lemma38StartVertexι, ite_eq_right hn]
    refine ⟨kmswWindowVertexMapInf
      (fun i => shiftedStream W 0 (n.toNat + i)) (m.toNat - n.toNat) a, ?_⟩
    rw [kmswWindowVertexMapInf_comp,
      Nat.add_sub_of_le (Int.toNat_le_toNat hnm)]
    exact ha



theorem futureMaps_integer_edges_antitone (W : ℤ → Fin 3) :
    Antitone (fun n : ℤ => Set.range (lemma38StartEdgeι W n)) := by
  intro n m hnm e he
  simp only [Set.mem_range] at he ⊢
  by_cases hn : n ≤ 0
  · by_cases hm : m ≤ 0
    · have ha : m.natAbs ≤ n.natAbs := by
        have hn' := Int.ofNat_natAbs_of_nonpos hn
        have hm' := Int.ofNat_natAbs_of_nonpos hm
        omega
      simp only [lemma38StartEdgeι, ite_eq_left hm] at he
      simp only [lemma38StartEdgeι, ite_eq_left hn]
      exact futureMaps_edge_range_mono W ha he
    · obtain ⟨a, ha⟩ := he
      simp only [lemma38StartEdgeι, ite_eq_right hm] at ha
      simp only [lemma38StartEdgeι, ite_eq_left hn]
      exact futureMaps_edge_range_mono W (Nat.zero_le n.natAbs) ⟨_, ha⟩
  · have hm : ¬ m ≤ 0 := by omega
    obtain ⟨a, ha⟩ := he
    simp only [lemma38StartEdgeι, ite_eq_right hm] at ha
    simp only [lemma38StartEdgeι, ite_eq_right hn]
    refine ⟨kmswWindowEdgeMapInf
      (fun i => shiftedStream W 0 (n.toNat + i)) (m.toNat - n.toNat) a, ?_⟩
    rw [kmswWindowEdgeMapInf_comp,
      Nat.add_sub_of_le (Int.toNat_le_toNat hnm)]
    exact ha



theorem futureMaps_iUnion_integer_vertices (W : ℤ → Fin 3) :
    (⋃ n : ℤ, Set.range (lemma38StartVertexι W n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨N, a, ha⟩ := wholePlaneVertex_has_run_rep W v
  refine Set.mem_iUnion.mpr ⟨-(N : ℤ), a, ?_⟩
  simpa only [lemma38StartVertexι, neg_nonpos.mpr (Int.natCast_nonneg N),
    ite_true, Int.natAbs_neg, Int.natAbs_natCast] using ha



theorem futureMaps_iUnion_integer_edges (W : ℤ → Fin 3) :
    (⋃ n : ℤ, Set.range (lemma38StartEdgeι W n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  obtain ⟨N, a, ha⟩ := wholePlaneEdge_has_run_rep W e
  refine Set.mem_iUnion.mpr ⟨-(N : ℤ), a, ?_⟩
  simpa only [lemma38StartEdgeι, neg_nonpos.mpr (Int.natCast_nonneg N),
    ite_true, Int.natAbs_neg, Int.natAbs_natCast] using ha



theorem futureMaps_missing_of_missing_trans (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (e : ℕ)
    (hm : ¬ EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e)) :
    ¬ EdgePresent (shiftedStream W N) e :=
  fun hp => hm (wholePlaneRun_present_mono W N M hNM e hp)

section ShiftedCut

variable (W : ℤ → Fin 3) (n : ℤ) (phi : WholePlaneStartIso W n)
    (Hn : WholePlaneRotationHypothesis (shiftWordInt W n))
    (h : BoundaryHitWitnesses (shiftedStream (shiftWordInt W n) 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWordInt W n)
      (wholePlaneEdgeι (shiftWordInt W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWordInt W n) 0)
          (boundaryHitTime (shiftedStream (shiftWordInt W n) 0) h (k - 1)))))



theorem futureMaps_cut_vertices :
    phi.vertex '' m0CutLeftVertices (shiftWordInt W n) Hn
        (m0CutData (shiftWordInt W n) Hn h hLL).seam =
      Set.range (lemma38StartVertexι W n) := by
  change phi.vertex '' m0CutLeftVertices (shiftWordInt W n) Hn
    (m0CutSeamEdge (shiftWordInt W n) Hn) = _
  rw [m0Cut_leftVertices_eq_runZero (shiftWordInt W n) Hn h _
    (m0Cut_seamEdge_iff (shiftWordInt W n) Hn h hLL)]
  ext v
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (phi.iota_vertex a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨wholePlaneVertexι (shiftWordInt W n) 0 a, ⟨a, rfl⟩, phi.iota_vertex a⟩



theorem futureMaps_cut_darts :
    phi.dart '' (m0CutData (shiftWordInt W n) Hn h hLL).darts =
      {d : WholePlaneDart W | d.1 ∈ Set.range (lemma38StartEdgeι W n)} := by
  have he := futureMaps_cut_edges W n phi Hn h hLL
  ext d
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (phi.dart a).1 ∈ Set.range (lemma38StartEdgeι W n)
    rw [phi.dart_apply]
    exact he ▸ Set.mem_image_of_mem phi.edge ha
  · intro hd
    have hdi : d.1 ∈ phi.edge '' (m0CutData (shiftWordInt W n) Hn h hLL).edges :=
      he.symm ▸ hd
    obtain ⟨e, he, hed⟩ := hdi
    refine ⟨(e, d.2), he, ?_⟩
    exact (phi.dart_apply (e, d.2)).trans (Prod.ext hed rfl)




theorem futureMaps_cut_missing (e : ℕ) :
    (m0CutData (shiftWordInt W n) Hn h hLL).missing
        (phi.edge.symm (lemma38StartEdgeι W n e)) ↔
      ¬ EdgePresent (lemma38StartStream W n) e := by
  have hi : phi.edge.symm (lemma38StartEdgeι W n e) =
      wholePlaneEdgeι (shiftWordInt W n) 0 e := by
    rw [← phi.iota_edge e, Equiv.symm_apply_apply]
  rw [hi]
  have hs : shiftedStream (shiftWordInt W n) 0 = lemma38StartStream W n := by
    funext i
    simp only [shiftedStream, shiftWordInt, lemma38StartStream, Nat.cast_zero, sub_zero]
  rw [← hs]
  exact (m0CutData (shiftWordInt W n) Hn h hLL).missing_eq h hLL e

end ShiftedCut























































end DirectedDistances.PaperProofs.Section5
