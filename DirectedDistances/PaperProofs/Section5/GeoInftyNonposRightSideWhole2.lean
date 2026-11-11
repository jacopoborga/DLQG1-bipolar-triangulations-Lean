/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole






public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the creation branch is detected by the east endpoints. -/
theorem rMinusWhole_record_east_eq_iff (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
    omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge, hne, hne', ne_of_lt hv]

/-- Helper toward Lemma 5.5: the stored oriented word and the creation
word have the same darts, including the cyclic shift in existing-left steps. -/
theorem rMinusWhole_creation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  unfold triangleOrientedDarts
  rcases j.property with h0 | h1
  · rw [ite_eq_left ((rMinusWhole_record_east_eq_iff w j).mpr h0)]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
        h0, hp, or_comm, or_left_comm, or_assoc]
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right (fun he => h0 ((rMinusWhole_record_east_eq_iff w j).mp he))]
    simp only [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
      h0, ↓reduceIte]

/-- Helper toward Lemma 5.5: every creation triangle has an edge outside
any infinite present path. The old and new active edges share an endpoint,
whereas a directed path uses at most one incoming and one outgoing edge. -/
theorem rMinusWhole_triangle_off_path (w : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence w) {v : ℕ} (R : InfinitePresentPath w ⟨v⟩)
    (j : TriangleCreationTime w) :
    ∃ d ∈ stageTriangleDartList w j, d.1 ∉ Set.range R.edge := by
  classical
  have hW := infinitePresentPath_west_injective hf
    (fun n => ⟨_, (monotone_family_all w n).choose_spec⟩) R
  have hE : Function.Injective (fun i => edgeEast w (R.edge i)) := by
    intro a b hab
    change edgeEast w (R.edge a) = edgeEast w (R.edge b) at hab
    have he (i : ℕ) : edgeEast w (R.edge i) = edgeWest w (R.edge (i + 1)) :=
      (R.edge_incoming_at_succ w i).2.trans (R.edge_outgoing_at_initial w (i + 1)).2.symm
    rw [he, he] at hab
    have := hW hab
    omega
  let t := stageTriangleRecord w j
  have hne : t.1 ≠ t.2.1 := by
    have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
    rcases j.property with h0 | h1
    · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
        simpa only [t, stageTriangleRecord, h0, ↓reduceIte, hp] using ne_of_lt ha
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simpa only [t, stageTriangleRecord, h0, ↓reduceIte] using ne_of_lt ha
  have hold : (t.1, false) ∈ stageTriangleDartList w j := by
    apply (rMinusWhole_creation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> exact List.mem_cons_self
  have hnew : (t.2.1, true) ∈ stageTriangleDartList w j := by
    apply (rMinusWhole_creation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false, t, Prod.mk.injEq,
      and_true, true_or, or_true]
  by_contra hn
  have hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ Set.range R.edge := by
    intro d hd
    by_contra hnot
    exact hn ⟨d, hd, hnot⟩
  obtain ⟨a, ha⟩ := hall _ hold
  obtain ⟨b, hb⟩ := hall _ hnew
  apply hne
  have heq : a = b := by
    by_cases h0 : w j.val = 0
    · apply hE
      change edgeEast w (R.edge a) = edgeEast w (R.edge b)
      rw [ha, hb]
      exact (rMinusWhole_record_east_eq_iff w j).mpr h0
    · apply hW
      change edgeWest w (R.edge a) = edgeWest w (R.edge b)
      rw [ha, hb]
      have h1 : w j.val = 1 := j.property.resolve_left h0
      obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
      have hbounds := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
      rw [← (edge_endpoints_eq w hbounds.1).1, ← (edge_endpoints_eq w hbounds.2.1).1]
      have hact := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
      have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
        omega
      simp [stageTriangleRecord, h1, kmswStage, kmswStep,
        kmswCodeStep, kmswStepOfStep, State.addEdge, ne_of_lt hact, hne']
  exact ha.symm.trans (heq ▸ hb)

section GeometricFaces

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime w h k
local notation "F" => kmswStage w n
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ

/-- Helper toward Lemma 5.5: each run-zero creation triangle survives as
one glued face with all of its oriented bordering darts. -/
theorem rMinusWhole_creation_gluedFace (j : TriangleCreationTime w) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicAmbientRegion W H h ∧
      ∀ d ∈ stageTriangleDartList w j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) G := by
  let A := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  let G₀ := capFace w (H.1 0) j
  obtain ⟨G, hG, _⟩ := WholePlaneGlueFaceOrbits.glueFaceOrbits_runZero_dartBorders
    W h hp H (0, false) G₀ (capFace_isBounded_face w (H.1 0) j)
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    have hup := boundedFace_subset_upper w h (H.1 0) G₀
      (capFace_isBounded_face w (H.1 0) j) (hG ▸ hz)
    change seamFun w h (H.1 0) z.re < z.im at hup
    exact le_of_lt hup
  · intro d hd
    exact (PLDrawing.dartBorders_congr A _ G₀ G
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H d) hG).mpr
        ((cap_border_iff w (H.1 0) j d).mpr hd)

/-- Helper toward Lemma 5.5: a creation triangle whose geometric edges
are all on the right has its entire open face on the right. -/
theorem rMinusWhole_creation_retained (j : TriangleCreationTime w)
    (hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ (S).edges) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicSideOpenRegion hp P .right ∧
      ∀ d ∈ stageTriangleDartList w j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) G := by
  obtain ⟨G, hGR, hb⟩ := rMinusWhole_creation_gluedFace hp (H := H) j
  obtain ⟨d, hd, hoff⟩ := rMinusWhole_triangle_off_path w (H.1 0) P.codePath j
  exact ⟨G, (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hoff
    d.2 G hGR (hb d hd) .right).mp (hall d hd), hb⟩

/-- Helper toward Lemma 5.5: prefix triangle cycles contain exactly the
oriented darts of the stored triangle, in its run-zero endpoint convention. -/
theorem rMinusPrefixTriangleCycle_mem (t : ℕ × ℕ × ℕ) (ht : t ∈ (F).triangles)
    (d : ℕ × Bool) :
    let c := rMinusPrefixTriangleCycle F t
    d ∈ [c.1, c.2.1, c.2.2] ↔ d ∈ triangleOrientedDarts w t := by
  have hb := triBound_stage w n t ht
  simp only [rMinusPrefixTriangleCycle, triangleOrientedDarts,
    (edge_endpoints_eq w hb.1).2, (edge_endpoints_eq w hb.2.1).2]
  split <;> rfl

include hτ hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every stored prefix triangle is retained as
one actual geometric face on the right, including all missing-edge darts. -/
theorem rMinusWhole_prefix_triangle_retained (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (F).triangles) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicSideOpenRegion hp P .right ∧
      ∀ d ∈ triangleOrientedDarts w t,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) G := by
  rw [← stageTriangleTimes_records w n] at ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  obtain ⟨G, hG, hb⟩ := rMinusWhole_creation_retained hp P j (by
    intro d hd
    apply boundaryGluingPrefixEdges_subset_right W h k longest hp P
      hτ hqMode Tpath hfin hleft hk
    apply stage_face_dart_lt_nextEdge w n d
    apply List.mem_append.mpr
    exact Or.inr (List.mem_flatMap.mpr ⟨j, hj, hd⟩))
  exact ⟨G, hG, fun d hd => hb d ((rMinusWhole_creation_oriented_mem w j d).mp hd)⟩

include hτ hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a prefix face step maps to a retained
geometric face step and keeps its original infinite-map successor. -/
theorem rMinusWhole_prefix_faceNext (a b : StageDart (F).nextEdge)
    (hab : rMinusPrefixFaceNext F (a.1.val, a.2) (b.1.val, b.2)) :
    (S).faceNext (a.1.val, a.2) (b.1.val, b.2) := by
  refine ⟨?_, rMinusPrefixFaceNext_infFaceSucc w (H.1 0) n a b hab⟩
  obtain ⟨t, ht, hs⟩ := hab
  obtain ⟨G, hG, hb⟩ := rMinusWhole_prefix_triangle_retained
    hτ hp P hqMode Tpath hfin hleft hk t ht
  refine ⟨G, hb _ ((rMinusPrefixTriangleCycle_mem t ht _).mp ?_), hG⟩
  rcases hs with ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    simp only [ha, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

end GeometricFaces

/-- Helper toward Lemma 5.5: on a stored triangle, the finite successor
is a prefix face step with the same dart identities. -/
theorem rMinusWhole_prefix_step_of_mem (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (d.1.val, d.2) ∈ triangleOrientedDarts w t) :
    rMinusPrefixFaceNext (kmswStage w n) (d.1.val, d.2)
      (((kmswMap w n).faceSucc d).1.val, ((kmswMap w n).faceSucc d).2) := by
  let c := triangleDartCycle w n t ht
  have hc := triangleDartCycle_isFace w n t ht
  have hd' : d ∈ [c.1, c.2.1, c.2.2] := by
    rw [← triangleDartCycle_values w n t ht] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with hd | hd | hd
    · exact Or.inl (Prod.ext (Fin.ext (congrArg Prod.fst hd)) (congrArg (fun z : ℕ × Bool => z.2) hd))
    · exact Or.inr (Or.inl
        (Prod.ext (Fin.ext (congrArg Prod.fst hd)) (congrArg (fun z : ℕ × Bool => z.2) hd)))
    · exact Or.inr (Or.inr
        (Prod.ext (Fin.ext (congrArg Prod.fst hd)) (congrArg (fun z : ℕ × Bool => z.2) hd)))
  refine ⟨t, ht, ?_⟩
  rw [rMinusPrefixTriangleCycle_eq w n t ht]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
  rcases hd' with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, congrArg (fun z => (z.1.val, z.2)) hc.1⟩
  · exact Or.inr (Or.inl ⟨rfl, congrArg (fun z => (z.1.val, z.2)) hc.2.1⟩)
  · exact Or.inr (Or.inr ⟨rfl, congrArg (fun z => (z.1.val, z.2)) hc.2.2.1⟩)

/-- Helper toward Lemma 5.5: a hatted creation-face dart keeps its
successor when embedded in the future map, rather than using exterior rotation. -/
theorem rMinusWhole_hat_infFaceSucc (u : ℕ → Fin 3) (hh : HasFlowLineHits u)
    (hf : hatLimitFiniteIncidence u) (j : TriangleCreationTime (hatCodes u hh))
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList (hatCodes u hh) j) :
    kmswInfFaceSucc u hf (hatLimitEdgeMap u hh d.1, d.2) =
      (hatLimitEdgeMap u hh
        (kmswInfFaceSucc (hatCodes u hh) (hatCodes_inducedFiniteIncidence u hh hf) d).1,
        (kmswInfFaceSucc (hatCodes u hh) (hatCodes_inducedFiniteIncidence u hh hf) d).2) := by
  let z := hatCodes u hh
  let m := j.val + 1
  let t := stageTriangleRecord z j
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  have ht : t ∈ (kmswStage z m).triangles := by
    dsimp only [t, m]
    exact hi ▸ List.get_mem _ i
  have hdo : d ∈ triangleOrientedDarts z t :=
    (rMinusWhole_creation_oriented_mem z j d).mpr hd
  have hdlt : d.1 < (kmswStage z m).nextEdge := by
    apply stage_face_dart_lt_nextEdge z m d
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨j, (mem_stageTriangleTimes z m j).mpr (Nat.lt_succ_self _), hd⟩))
  let a : StageDart (kmswStage z m).nextEdge := (⟨d.1, hdlt⟩, d.2)
  let b := (kmswMap z m).faceSucc a
  have hs := rMinusWhole_prefix_step_of_mem z m t ht a hdo
  have hsrc := rMinusPrefixFaceNext_infFaceSucc z
    (hatCodes_inducedFiniteIncidence u hh hf) m a b hs
  have hmap : ∀ c : StageDart (kmswStage z m).nextEdge,
      ((hatDartMap u hh m c).1.val, (hatDartMap u hh m c).2) =
        (hatLimitEdgeMap u hh c.1.val, c.2) := by
    intro c
    change (hatAllEdgeMap u hh m c.1.val, c.2) = _
    rw [hatLimitEdgeMap_eq_stage u hh m c.1.val c.1.isLt]
  have hglobmem : ((hatDartMap u hh m a).1.val, (hatDartMap u hh m a).2) ∈
      triangleOrientedDarts u
        (hatAllEdgeMap u hh m t.1, hatAllEdgeMap u hh m t.2.1,
          hatAllEdgeMap u hh m t.2.2) := by
    rw [← hatAll_triangleOrientedDarts u hh m t ht]
    exact List.mem_map.mpr ⟨d, hdo, rfl⟩
  have hgs := rMinusWhole_prefix_step_of_mem u (quadrantRStageTime u hh m) _
    (hatAll_triSim u hh m t ht) (hatDartMap u hh m a) hglobmem
  have htyped : a ∈ [(triangleDartCycle z m t ht).1,
      (triangleDartCycle z m t ht).2.1, (triangleDartCycle z m t ht).2.2] := by
    rw [← triangleDartCycle_values z m t ht] at hdo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdo ⊢
    have hinj : Function.Injective
        (fun c : StageDart (kmswStage z m).nextEdge => (c.1.val, c.2)) := by
      intro c e he
      exact Prod.ext (Fin.ext (congrArg Prod.fst he))
        (congrArg (fun z : ℕ × Bool => z.2) he)
    exact hdo.imp (fun he => hinj he)
      (fun he => he.imp (fun he => hinj he) (fun he => hinj he))
  have hg := rMinusPrefixFaceNext_infFaceSucc u hf (quadrantRStageTime u hh m)
    (hatDartMap u hh m a) ((kmswMap u (quadrantRStageTime u hh m)).faceSucc
      (hatDartMap u hh m a)) hgs
  rw [hatDartMap_faceSucc u hh m t ht a htyped, hmap, hmap] at hg
  rw [hsrc]
  exact hg

/-- Helper toward Lemma 5.5: creation-face successors commute with the infinite window embedding. -/
theorem rMinusWhole_window_faceSucc_of_triangle (w : ℕ → Fin 3) (s : ℕ)
    (hu : KMSWFiniteIncidence (fun i => w (s + i))) (hw : KMSWFiniteIncidence w)
    (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (fun i => w (s + i)),
      d ∈ stageTriangleDartList (fun i => w (s + i)) j) :
    (kmswWindowEdgeMapInf w s
        (kmswInfFaceSucc (fun i => w (s + i)) hu d).1,
      (kmswInfFaceSucc (fun i => w (s + i)) hu d).2) =
      kmswInfFaceSucc w hw (kmswWindowEdgeMapInf w s d.1, d.2) := by
  let u := fun i => w (s + i)
  obtain ⟨j, hdj⟩ := hd
  obtain ⟨a, ha⟩ := kmswInfFaceSucc_eventually_eq_stage u hu d
  obtain ⟨b, hb⟩ := kmswInfFaceSucc_eventually_eq_stage w hw
    (kmswWindowEdgeMapInf w s d.1, d.2)
  let m := max (max a b) (j.val + 1)
  obtain ⟨hedge, hsrc⟩ := ha m (by dsimp only [m]; omega)
  obtain ⟨himage, htgt⟩ := hb (s + m) (by dsimp only [m]; omega)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hedge⟩, d.2)
  have hx : (x.1.val, x.2) ∈ stageTriangleDartsVal u m := by
    apply List.mem_flatMap.mpr
    exact ⟨j, (mem_stageTriangleTimes u m j).mpr (by dsimp only [m]; omega), hdj⟩
  have hface := kmswWindowDartMap_faceSucc w s m x hx
  have hmap : kmswWindowDartMap w s m x =
      (⟨kmswWindowEdgeMapInf w s d.1, himage⟩, d.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswWindowEdgeMapInf_eq_stage w s m d.1 hedge).symm
    · rfl
  rw [hsrc]
  have hout := kmswWindowEdgeMapInf_eq_stage w s m
    ((kmswMap u m).faceSucc x).1.val ((kmswMap u m).faceSucc x).1.isLt
  change (kmswWindowEdgeMapInf w s ((kmswMap u m).faceSucc x).1.val,
    ((kmswMap u m).faceSucc x).2) = _
  rw [hout]
  change ((kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).1.val,
    (kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).2) = _
  rw [← hface, hmap]
  exact htgt.symm

/-- Helper toward Lemma 5.5: a strict record attains the running minimum. -/
private theorem rMinusWhole_record_min (w : ℕ → Fin 3) (m : ℕ)
    (hm : ∀ j < m, R w m < R w j) : minR w m = R w m := by
  obtain ⟨j, hj, he⟩ := runningMin_attained (R w) m
  have hle := runningMin_le (R w) m m le_rfl
  change minR w m ≤ R w m at hle
  change minR w m = R w j at he
  by_cases hjm : j < m
  · have := hm j hjm
    omega
  · have : j = m := by omega
    simpa only [this] using he

/-- Helper toward Lemma 5.5: the record count determines the vertical level,
including the record at time zero. -/
private theorem rMinusWhole_record_count (w : ℕ → Fin 3) (m : ℕ)
    (hm : ∀ j < m, R w m < R w j) :
    (Nat.count (fun n => ∀ j < n, R w n < R w j) m : ℤ) = -R w m := by
  classical
  have hlen := kmswStage_LR_length w m
  have hc : (kmswStage w m).LR.length =
      Nat.count (fun n => ∀ j < n, R w n < R w j) (m + 1) := by
    rw [kmswStage_LR_eq, List.length_map, length_filter_range]
    apply natCount_congr
    intro n _
    exact decide_eq_true_iff
  rw [hc, Nat.count_succ, ite_eq_left hm, Nat.cast_add, Nat.cast_one,
    rMinusWhole_record_min w m hm] at hlen
  omega

/-- Helper toward Lemma 5.5: the selected right record has level minus its
zero-based index. -/
private theorem rMinusWhole_selected_record (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    let m := natSelect (fun n => ∀ j < n, R w n < R w j) i
    (∀ j < m, R w m < R w j) ∧ R w m = -(i : ℤ) := by
  classical
  obtain ⟨hm, hc⟩ := natSelect_spec (right_record_infinite w hR) i
  have hv := rMinusWhole_record_count w _ hm
  rw [hc] at hv
  exact ⟨hm, by omega⟩

/-- Helper toward Lemma 5.5: a record at level minus i is exactly record i,
as an edge ID, independently of its endpoints. -/
private theorem rMinusWhole_record_edge (w : ℕ → Fin 3) (m i : ℕ)
    (hm : ∀ j < m, R w m < R w j) (hv : R w m = -(i : ℤ)) :
    act w m = kmswRightBoundaryEdge w i := by
  classical
  have hc := rMinusWhole_record_count w m hm
  have hc' : Nat.count (fun n => ∀ j < n, R w n < R w j) m = i := by omega
  unfold kmswRightBoundaryEdge
  rw [← hc', natSelect_count hm]
/-- Helper toward Lemma 5.5: vertical coordinates add across a code shift. -/
private theorem rMinusWhole_R_shift_add (w : ℕ → Fin 3) (t n : ℕ) :
    R w (t + n) = R w t + R (fun j => w (t + j)) n := by
  induction n with
  | zero => simp only [R, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n ih =>
    have hg : R w (t + n + 1) = R w (t + n) +
        (lazyTwoDimensionalStep (w (t + n))).2 := Finset.sum_range_succ _ _
    have hs : R (fun j => w (t + j)) (n + 1) =
        R (fun j => w (t + j)) n +
          (lazyTwoDimensionalStep (w (t + n))).2 := Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega

section HattedFaces
variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime w h k
local notation "F" => kmswStage w n
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ

local notation "U" => boundaryGluingFutureStream W h k
local notation "z" => hatCodes U hτ

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: every retained hatted triangle maps to one
retained geometric triangle on the right, with all bordering darts preserved. -/
theorem rMinusWhole_hatted_triangle_retained (j : TriangleCreationTime z)
    (hall : ∀ d ∈ stageTriangleDartList z j, d.1 ∈ (Q).edges) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicSideOpenRegion hp P .right ∧
      ∀ d ∈ stageTriangleDartList z j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (EH d.1, d.2)) G := by
  have hc := boundaryGluing_decoded_stream W h k hτ
  let j' : TriangleCreationTime
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) :=
    ⟨j.val, by rw [hc]; exact j.property⟩
  let R := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri U hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨G, hGR, hborder⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin T
  have hb (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList z j) :
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (EH d.1, d.2)) G :=
    hborder d ((rMinusWhole_creation_oriented_mem z j d).mpr hd)
  obtain ⟨d, hd, hoff⟩ := rMinusWhole_triangle_off_path _
    (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩) R j'
  have hdz : d ∈ stageTriangleDartList z j := by
    simpa only [stageTriangleDartList, stageTriangleDartTriple, j', hc] using hd
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have hoff' : EH d.1 ∉ m0GeodesicEdges P := by
    rintro ⟨a, ha⟩
    apply hoff
    exact ⟨a, boundaryGluingHatEdgeMap_injective W h k hτ ((hid a).symm.trans ha)⟩
  have heR : EH d.1 ∈ (S).edges :=
    boundaryGluingRightHatEdges_subset_right W h k hτ longest hp P
      hqMode Tpath hfin hleft ⟨d.1, hall d hdz, rfl⟩
  exact ⟨G, (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hoff'
    d.2 G hGR (hb d hdz) .right).mp heR, hb⟩

/-- Helper toward Lemma 5.5: a hatted creation-face dart keeps its
successor under the composite hat-then-future gluing map. -/
theorem rMinusWhole_hatted_infFaceSucc (j : TriangleCreationTime z)
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList z j) :
    kmswInfFaceSucc w (H.1 0) (EH d.1, d.2) =
      (EH (kmswInfFaceSucc z (hatCodes_inducedFiniteIncidence U hτ hfin) d).1,
        (kmswInfFaceSucc z (hatCodes_inducedFiniteIncidence U hτ hfin) d).2) := by
  have hh := rMinusWhole_hat_infFaceSucc U hτ hfin j d hd
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri U hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  have hdo := (rMinusWhole_creation_oriented_mem z j d).mpr hd
  have hm : (hatLimitEdgeMap U hτ d.1, d.2) ∈
      triangleOrientedDarts U (hatLimitFaceEquiv U hτ T).val := by
    rw [← hatLimit_triangleOrientedDarts U hτ T]
    exact List.mem_map.mpr ⟨d, hdo, rfl⟩
  obtain ⟨m, ht⟩ := (hatLimitFaceEquiv U hτ T).property
  rw [← stageTriangleTimes_records U m] at ht
  obtain ⟨j₀, _, heq⟩ := List.mem_map.mp ht.1
  have hm' : (hatLimitEdgeMap U hτ d.1, d.2) ∈ stageTriangleDartList U j₀ :=
    (rMinusWhole_creation_oriented_mem U j₀ _).mp (heq ▸ hm)
  have hs := rMinusWhole_window_faceSucc_of_triangle w n hfin (H.1 0)
    (hatLimitEdgeMap U hτ d.1, d.2) ⟨j₀, hm'⟩
  change kmswInfFaceSucc (fun i => w (n + i)) hfin (hatLimitEdgeMap U hτ d.1, d.2) = _ at hh
  rw [hh] at hs
  change _ = (kmswInfFaceSucc w (H.1 0))
    (boundaryGluingEdgeMap W h k (hatLimitEdgeMap U hτ d.1), d.2) at hs
  exact hs.symm

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: a retained hatted face step maps to a
retained geometric face step with its actual successor unchanged. -/
theorem rMinusWhole_hatted_faceNext (d e : ℕ × Bool) (hde : (Q).faceNext d e) :
    (S).faceNext (EH d.1, d.2) (EH e.1, e.2) := by
  have hc := boundaryGluing_decoded_stream W h k hτ
  obtain ⟨⟨j, hd, hall⟩, he⟩ := hde
  let j' : TriangleCreationTime z := ⟨j.val, by rw [← hc]; exact j.property⟩
  have hl : stageTriangleDartList _ j = stageTriangleDartList z j' := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, j', hc]
  rw [hl] at hd hall
  obtain ⟨G, hG, hb⟩ := rMinusWhole_hatted_triangle_retained
    hτ hp P hqMode Tpath hfin hleft j' hall
  refine ⟨⟨G, hb d hd, hG⟩, ?_⟩
  have he' : kmswInfFaceSucc z (hatCodes_inducedFiniteIncidence U hτ hfin) d = e := by
    have hcongr : ∀ (a b : ℕ → Fin 3) (ha : KMSWFiniteIncidence a)
        (hb : KMSWFiniteIncidence b), a = b → kmswInfFaceSucc a ha = kmswInfFaceSucc b hb := by
      intro a b ha hb hab
      subst b
      rfl
    have heq := hcongr _ _
      (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩)
      (hatCodes_inducedFiniteIncidence U hτ hfin) hc
    exact (congrArg (fun f : Equiv.Perm (ℕ × Bool) => f d) heq).symm.trans he
  rw [rMinusWhole_hatted_infFaceSucc hτ (H := H) hfin j' d hd, he']

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every glued code face is an actual retained
geometric face, and the cell equivalence preserves its successor. -/
theorem rMinusGluedMarkedIso_faceNext_forward
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode))
    (huv : rMinusGluedFaceNext hτ hqMode u v) :
    geometricSideRelation S .faceNext
      (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
      (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  cases u with
  | inl u => exact False.elim huv
  | inr u =>
    cases v with
    | inl v => exact False.elim huv
    | inr v =>
      rcases huv with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · change (S).faceNext (a.1.val, a.2) (b.1.val, b.2)
        exact rMinusWhole_prefix_faceNext hτ hp P hqMode Tpath hfin hleft hk a b hab
      · change (S).faceNext (EH a.val.1, a.val.2) (EH b.val.1, b.val.2)
        exact rMinusWhole_hatted_faceNext hτ hp P hqMode Tpath hfin hleft
          a.val b.val hab

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a future edge on the nonpositive right side
already belongs to the hatted right block, even on the prefix interface. -/
theorem rMinusWhole_future_edge_capture (e : ℕ)
    (he : boundaryGluingEdgeMap W h k e ∈ (S).edges) :
    ∃ a, a ∈ (Q).edges ∧ hatLimitEdgeMap U hτ a = e := by
  have he' := he
  rw [(boundaryGluing_nonpos_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).2] at he'
  have hhat : boundaryGluingEdgeMap W h k e ∈
      boundaryGluingRightHatEdges W h k hτ (if longest then XDP.ldp else XDP.sdp) hqMode := by
    rcases he' with heP | heH
    · have hm : boundaryGluingEdgeMap W h k e ∈
          boundaryGluingPrefixEdges W h k ∩ Set.range (boundaryGluingEdgeMap W h k) :=
        ⟨heP, e, rfl⟩
      rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ] at hm
      have hUL : (F).UL = [(F).active] := by
        by_cases hk0 : k = 0
        · rw [hk0, boundaryHitTime_zero]
          rfl
        · exact (leftHit_UL_singleton_and_west_endpoint w h (by omega)).1
      rcases hm with hm | hm
      · change _ ∈ (F).UL.dropLast at hm
        rw [hUL] at hm
        exact False.elim (List.not_mem_nil hm)
      · exact boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ
          (if longest then XDP.ldp else XDP.sdp) hqMode hfin hm
    · exact heH
  obtain ⟨a, ha, hae⟩ := hhat
  exact ⟨a, ha, boundaryGluingEdgeMap_injective W h k hae⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: hatted edge retention is reflected as well
as preserved, including the finite-prefix attachment. -/
theorem rMinusWhole_hatted_edge_iff (e : ℕ) :
    EH e ∈ (S).edges ↔ e ∈ (Q).edges := by
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := rMinusWhole_future_edge_capture
      hτ hp P hqMode Tpath hfin hleft hk (hatLimitEdgeMap U hτ e) he
    exact hatLimitEdgeMap_injective U hτ hae ▸ ha
  · intro he
    exact boundaryGluingRightHatEdges_subset_right W h k hτ longest hp P
      hqMode Tpath hfin hleft ⟨e, he, rfl⟩

/-- Helper toward Lemma 5.5: the infinite window embedding preserves
each creation triangle's entire dart list up to cyclic order. -/
theorem rMinusWhole_window_triangle_rotated (j : TriangleCreationTime U) :
    List.IsRotated
      ((stageTriangleDartList U j).map (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)))
      (stageTriangleDartList w ⟨n + j.val, j.property⟩) := by
  have hr := kmswWindowPatchData_triangle_rotated w n (j.val + 1) j.val
    (Nat.lt_succ_self _) j.property
  have hm : (stageTriangleDartList U j).map
      (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)) =
      (stageTriangleDartList U j).map
        (fun d => ((kmswWindowPatchData w n (j.val + 1)).φ d.1, d.2)) := by
    apply List.map_congr_left
    intro d hd
    have hdlt : d.1 < (kmswStage U (j.val + 1)).nextEdge := by
      apply stage_face_dart_lt_nextEdge U (j.val + 1) d
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨j, (mem_stageTriangleTimes U (j.val + 1) j).mpr (Nat.lt_succ_self _), hd⟩))
    exact Prod.ext (kmswWindowEdgeMapInf_eq_stage w n (j.val + 1) d.1 hdlt) rfl
  rw [hm]
  exact hr

/-- Helper toward Lemma 5.5: every edge of a stored record occurs in
its oriented boundary word, irrespective of the creation branch. -/
theorem rMinusWhole_oriented_edge_exists (v : ℕ → Fin 3) (t : ℕ × ℕ × ℕ)
    (e : ℕ) (he : e ∈ [t.1, t.2.1, t.2.2]) :
    ∃ b : Bool, (e, b) ∈ triangleOrientedDarts v t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  unfold triangleOrientedDarts
  split
  · rcases he with rfl | rfl | rfl
    · exact ⟨false, List.mem_cons_self⟩
    · exact ⟨true, by simp only [List.mem_cons, true_or, or_true]⟩
    · exact ⟨false, by simp only [List.mem_cons, true_or, or_true]⟩
  · rcases he with rfl | rfl | rfl
    · exact ⟨false, List.mem_cons_self⟩
    · exact ⟨true, by simp only [List.mem_cons, true_or, or_true]⟩
    · exact ⟨true, by simp only [List.mem_cons, true_or, or_true]⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every retained run-zero triangle is either
a stored prefix triangle or an entire hatted right triangle. In particular,
there is no additional retained triangle straddling the attachment seam. -/
theorem rMinusWhole_retained_triangle_exhaustion (j : TriangleCreationTime w)
    (hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ (S).edges) :
    stageTriangleRecord w j ∈ (F).triangles ∨
      ∃ T : HatLocalTri U hτ,
        (∀ d ∈ triangleOrientedDarts z T.val, d.1 ∈ (Q).edges) ∧
        ∀ r : ℕ × Bool, r ∈ stageTriangleDartList w j ↔
          ∃ d ∈ triangleOrientedDarts z T.val, (EH d.1, d.2) = r := by
  by_cases hj : j.val < n
  · exact Or.inl (by
      rw [← stageTriangleTimes_records w n]
      exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes w n j).mpr hj, rfl⟩)
  · right
    let j' : TriangleCreationTime U := ⟨j.val - n, by
      change w (n + (j.val - n)) = 0 ∨ w (n + (j.val - n)) = 1
      have hn : n + (j.val - n) = j.val := by omega
      rw [hn]
      exact j.property⟩
    have hjj : (⟨n + j'.val, j'.property⟩ : TriangleCreationTime w) = j := by
      apply Subtype.ext
      dsimp only [j']
      omega
    have hrot := rMinusWhole_window_triangle_rotated (h := h) j'
    rw [hjj] at hrot
    have hr : HatTriangleReachable U (stageTriangleRecord U j') := by
      intro e he
      obtain ⟨b, hb⟩ := rMinusWhole_oriented_edge_exists U (stageTriangleRecord U j') e he
      have hb' := (rMinusWhole_creation_oriented_mem U j' (e, b)).mp hb
      have him : (boundaryGluingEdgeMap W h k e, b) ∈ stageTriangleDartList w j :=
        hrot.mem_iff.mp (List.mem_map.mpr ⟨(e, b), hb', rfl⟩)
      obtain ⟨a, _, hae⟩ := rMinusWhole_future_edge_capture
        hτ hp P hqMode Tpath hfin hleft hk e (hall _ him)
      exact (hatLimitEdgeMap_geometric_range_iff U hτ e).mp ⟨a, hae⟩
    obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index U j'
    let G : GlobalHatTri U := ⟨stageTriangleRecord U j', j'.val + 1,
      hi ▸ List.get_mem _ i, hr⟩
    obtain ⟨T, hT⟩ := hatLimitTriangle_surj U hτ G
    change (hatLimitFaceEquiv U hτ T).val = stageTriangleRecord U j' at hT
    have hm := hatLimit_triangleOrientedDarts U hτ T
    rw [hT] at hm
    have hmem (r : ℕ × Bool) : r ∈ stageTriangleDartList w j ↔
        ∃ d ∈ triangleOrientedDarts z T.val, (EH d.1, d.2) = r := by
      constructor
      · intro hr
        obtain ⟨a, ha, har⟩ := List.mem_map.mp (hrot.mem_iff.mpr hr)
        have hao := (rMinusWhole_creation_oriented_mem U j' a).mpr ha
        rw [← hm] at hao
        obtain ⟨d, hd, hda⟩ := List.mem_map.mp hao
        refine ⟨d, hd, ?_⟩
        have he : (hatLimitEdgeMap U hτ d.1, d.2) = a := hda
        exact (congrArg (fun a : ℕ × Bool => (boundaryGluingEdgeMap W h k a.1, a.2)) he).trans har
      · rintro ⟨d, hd, rfl⟩
        have ha : (hatLimitEdgeMap U hτ d.1, d.2) ∈ stageTriangleDartList U j' := by
          apply (rMinusWhole_creation_oriented_mem U j' _).mp
          rw [← hm]
          exact List.mem_map.mpr ⟨d, hd, rfl⟩
        exact hrot.mem_iff.mp (List.mem_map.mpr ⟨_, ha, rfl⟩)
    refine ⟨T, ?_, hmem⟩
    intro d hd
    apply (rMinusWhole_hatted_edge_iff hτ hp P hqMode Tpath hfin hleft hk d.1).mp
    exact hall _ ((hmem _).mpr ⟨d, hd, rfl⟩)

include hp P in
/-- Helper toward Lemma 5.5: every retained geometric face step has an
actual run-zero creation triangle, all of whose edges are on the right. -/
theorem rMinusWhole_faceNext_triangle (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j ∧
      ∀ a ∈ stageTriangleDartList w j, a.1 ∈ (S).edges := by
  obtain ⟨⟨G, hdG, hG⟩, _⟩ := hde
  let A := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  have hGR : G.val ⊆ m0GeodesicAmbientRegion W H h := fun a ha => (hG ha).1
  have hupper : G.val ⊆ {a : ℂ | seamFun w h (H.1 0) a.re < a.im} := by
    rcases WholePlaneM0Drawing.face_side W h hp H G with hu | hl
    · exact hu
    · obtain ⟨a, ha, hface⟩ := G.property
      have ham : a ∈ G.val := hface ▸ mem_connectedComponentIn ha
      have hle : seamFun w h (H.1 0) a.re ≤ a.im := hGR ham
      have hlt : a.im < seamFun w h (H.1 0) a.re := hl ham
      exact False.elim (not_lt_of_ge hle hlt)
  obtain ⟨G₀, hG₀, hval⟩ := (WholePlaneM0Drawing.m0_face_iff W h hp H G).mp hupper
  have hb (r : ℕ × Bool) : A.dartBorders r G₀ ↔
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 r) G :=
    (PLDrawing.dartBorders_congr A _ G₀ G
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H r) hval).symm
  obtain ⟨j, hlist, _, _⟩ := boundedFace_orbit_is_triangle w (H.1 0) h G₀ hG₀
  have hj (a : ℕ × Bool) : A.dartBorders a G₀ ↔ a ∈ stageTriangleDartList w j :=
    Set.ext_iff.mp hlist a
  refine ⟨j, (hj d).mp ((hb d).mpr hdG), ?_⟩
  intro a ha
  by_cases hs : a.1 ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P hs).2
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hs
      a.2 G hGR ((hb a).mp ((hj a).mpr ha)) .right).mpr hG

/-- Helper toward Lemma 5.5: every oriented dart of a stored triangle
is allocated in the same finite stage. -/
theorem rMinusWhole_oriented_dart_lt (v : ℕ → Fin 3) (m : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage v m).triangles)
    (d : ℕ × Bool) (hd : d ∈ triangleOrientedDarts v t) :
    d.1 < (kmswStage v m).nextEdge := by
  have hb := triBound_stage v m t ht
  unfold triangleOrientedDarts at hd
  split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  · rcases hd with rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  · rcases hd with rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.2
    · exact hb.2.1

/-- Helper toward Lemma 5.5: creation triangles are closed under the
actual infinite face successor, preserving the oriented dart list. -/
theorem rMinusWhole_triangle_succ_mem (v : ℕ → Fin 3) (hf : KMSWFiniteIncidence v)
    (j : TriangleCreationTime v) (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList v j) :
    kmswInfFaceSucc v hf d ∈ stageTriangleDartList v j := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle v hf j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl
  · exact Or.inr (Or.inl hc.1)
  · exact Or.inr (Or.inr hc.2.1)
  · exact Or.inl hc.2.2.1

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every retained geometric face step comes
from one complete prefix or hatted face under the glued cell equivalence. -/
theorem rMinusGluedMarkedIso_faceNext_reverse
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode))
    (huv : geometricSideRelation S .faceNext
      (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
      (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v)) :
    rMinusGluedFaceNext hτ hqMode u v := by
  let E := rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  cases u with
  | inl u => exact False.elim huv
  | inr u =>
    cases v with
    | inl v => exact False.elim huv
    | inr v =>
      change (S).faceNext (E u).val (E v).val at huv
      obtain ⟨j, hdj, hall⟩ := rMinusWhole_faceNext_triangle hp P _ _ huv
      rcases rMinusWhole_retained_triangle_exhaustion
        hτ hp P hqMode Tpath hfin hleft hk j hall with ht | ⟨T, hT, hm⟩
      · have hdo := (rMinusWhole_creation_oriented_mem w j _).mpr hdj
        let a : StageDart (F).nextEdge :=
          (⟨(E u).val.1, rMinusWhole_oriented_dart_lt w n _ ht _ hdo⟩, (E u).val.2)
        let b := (kmswMap w n).faceSucc a
        have hab := rMinusWhole_prefix_step_of_mem w n _ ht a hdo
        have hs := rMinusPrefixFaceNext_infFaceSucc w (H.1 0) n a b hab
        have ha : rMinusGluedPrefixDart hτ hqMode a = u := by
          apply E.injective
          apply Subtype.ext
          rfl
        have hb : rMinusGluedPrefixDart hτ hqMode b = v := by
          apply E.injective
          apply Subtype.ext
          exact hs.symm.trans huv.2
        exact Or.inl ⟨a, b, hab, ha, hb⟩
      · obtain ⟨d, hd, hdu⟩ := (hm _).mp hdj
        obtain ⟨m, htm⟩ := T.property
        rw [← stageTriangleTimes_records z m] at htm
        obtain ⟨j', _, hj'⟩ := List.mem_map.mp htm
        have hdj' : d ∈ stageTriangleDartList z j' :=
          (rMinusWhole_creation_oriented_mem z j' d).mp (hj' ▸ hd)
        let f := kmswInfFaceSucc z (hatCodes_inducedFiniteIncidence U hτ hfin)
        have hfd : f d ∈ stageTriangleDartList z j' :=
          rMinusWhole_triangle_succ_mem z _ j' d hdj'
        have hfdo : f d ∈ triangleOrientedDarts z T.val :=
          hj' ▸ (rMinusWhole_creation_oriented_mem z j' _).mpr hfd
        let a : {d : ℕ × Bool // d.1 ∈ (Q).edges} := ⟨d, hT d hd⟩
        let b : {d : ℕ × Bool // d.1 ∈ (Q).edges} := ⟨f d, hT (f d) hfdo⟩
        have hab : (Q).faceNext a.val b.val := by
          have hc := boundaryGluing_decoded_stream W h k hτ
          let j'' : TriangleCreationTime
              (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) :=
            ⟨j'.val, by rw [hc]; exact j'.property⟩
          have hl : stageTriangleDartList _ j'' = stageTriangleDartList z j' := by
            simp only [stageTriangleDartList, stageTriangleDartTriple, j'', hc]
          refine ⟨⟨j'', ?_, ?_⟩, ?_⟩
          · exact hl ▸ hdj'
          · intro r hr
            apply hT r
            rw [hl] at hr
            exact hj' ▸ (rMinusWhole_creation_oriented_mem z j' r).mpr hr
          · have hcongr : ∀ (c d : ℕ → Fin 3) (hc : KMSWFiniteIncidence c)
                (hd : KMSWFiniteIncidence d), c = d → kmswInfFaceSucc c hc = kmswInfFaceSucc d hd := by
              intro c d hc hd hcd
              subst d
              rfl
            exact congrArg (fun f : Equiv.Perm (ℕ × Bool) => f d)
              (hcongr _ _ _ _ hc)
        have ha : rMinusGluedHattedDart hτ hqMode a = u := by
          apply E.injective
          apply Subtype.ext
          exact hdu
        have hb : rMinusGluedHattedDart hτ hqMode b = v := by
          apply E.injective
          apply Subtype.ext
          have hs := rMinusWhole_hatted_infFaceSucc hτ (H := H) hfin j' d hdj'
          exact hs.symm.trans ((congrArg (kmswInfFaceSucc w (H.1 0)) hdu).trans huv.2)
        exact Or.inr ⟨a, b, hab, ha, hb⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the code-built retained-face relation agrees
in both directions with the actual right side, on every cell branch. -/
theorem rMinusGluedMarkedIso_faceNext_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedFaceNext hτ hqMode u v ↔
      geometricSideRelation S .faceNext
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) :=
  ⟨rMinusGluedMarkedIso_faceNext_forward hτ hp P hqMode Tpath hfin hleft hk u v,
    rMinusGluedMarkedIso_faceNext_reverse hτ hp P hqMode Tpath hfin hleft hk u v⟩

include hk in
/-- Helper toward Lemma 5.5: the stopped prefix has exactly minus its
nonpositive boundary index many missing lower-left edges. -/
theorem rMinusWhole_LL_length : ((F).LL.length : ℤ) = -k := by
  have hUL : (F).UL = [(F).active] := by
    by_cases hk0 : k = 0
    · rw [hk0, boundaryHitTime_zero]
      rfl
    · exact (leftHit_UL_singleton_and_west_endpoint w h (by omega)).1
  have hL : L w n = k := by
    by_cases hk0 : k = 0
    · simp only [hk0, boundaryHitTime_zero, L, Finset.range_zero, Finset.sum_empty]
    · exact boundaryHitTime_left_spec w h (by omega)
  have hul := kmswStage_UL_length w n
  have hll := kmswStage_LL_length w n
  rw [hUL] at hul
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.cast_one] at hul
  omega

include hk in
/-- Helper toward Lemma 5.5: the lower-left prefix word has exactly the
original exterior edge labels, in order from the root of the glued side. -/
theorem rMinusWhole_LL_get (i : ℕ) (hi : i < (F).LL.length) :
    (F).LL.get ⟨i, hi⟩ = boundaryOuterEdge w h (k + (i : ℤ)) := by
  have hlen := rMinusWhole_LL_length (h := h) hk
  let m := (F).LL.length - i
  have hm : 1 ≤ m := by dsimp only [m]; omega
  have hmb : m ≤ (F).LL.length := Nat.sub_le _ _
  have hmi : (m : ℤ) = -(k + (i : ℤ)) := by dsimp only [m]; omega
  have hki : k + (i : ℤ) ≤ -1 := by omega
  obtain ⟨_, _, he⟩ := kmswLL_reverse_get_first_hit w n m hm hmb
  have ht : boundaryHitTime w h (-(m : ℤ)) =
      Nat.find (kmswLL_level_hit w n m hm hmb) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (show -(m : ℤ) ≠ 0 by omega),
      dite_eq_right (show ¬ 0 < -(m : ℤ) by omega)]
  have hidx : (F).LL.length - 1 - (m - 1) = i := by dsimp only [m]; omega
  rw [List.get_reverse' _ _ (show (F).LL.length - 1 - (m - 1) < (F).LL.length by omega)] at he
  have he' : (F).LL.get ⟨i, hi⟩ = kmswLLCreatedEdge w (boundaryHitTime w h (-(m : ℤ))) := by
    simpa only [hidx, ht] using he
  rw [boundaryOuterEdge_of_negative w h hki]
  simpa only [hmi, neg_neg] using he'

/-- Helper toward Lemma 5.5: each allocated lower-right boundary entry
already equals its permanent right-record edge, before taking a limit. -/
theorem rMinusWhole_LR_get (v : ℕ → Fin 3) (hv : BoundaryHitWitnesses v)
    (m i : ℕ) (hi : i < (kmswStage v m).LR.length) :
    (kmswStage v m).LR.get ⟨i, hi⟩ = kmswRightBoundaryEdge v i := by
  have hR : ∀ a : ℤ, ∃ s, R v s ≤ a := by
    intro a
    obtain ⟨s, hs⟩ := hv.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨s, by have ha := le_max_left (-a) 1; omega⟩
  have hmono : ∀ t, m ≤ t → ∃ l, (kmswStage v t).LR = (kmswStage v m).LR ++ l := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨[], (List.append_nil _).symm⟩
    | succ t ht ih =>
      obtain ⟨l, hl⟩ := ih
      obtain ⟨r, hr⟩ := kmswStage_LR_succ_eq_append v t
      exact ⟨l ++ r, by rw [hr, hl, List.append_assoc]⟩
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually v hR i
  obtain ⟨l, hl⟩ := hmono (max m N) (le_max_left _ _)
  have he := hN (max m N) (le_max_right _ _)
  rw [hl, List.getElem?_append_left (by exact hi)] at he
  exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans he)

include hk in
/-- Helper toward Lemma 5.5: the finite lower boundary word is the
initial segment of the indexed exterior boundary of the glued right side. -/
theorem rMinusWhole_lower_get (i : ℕ) (hi : i < ((F).LL ++ (F).LR).length) :
    ((F).LL ++ (F).LR).get ⟨i, hi⟩ = boundaryOuterEdge w h (k + (i : ℤ)) := by
  have hlen := rMinusWhole_LL_length (h := h) hk
  by_cases hiL : i < (F).LL.length
  · simpa only [List.get_eq_getElem, List.getElem_append_left hiL] using
      rMinusWhole_LL_get (h := h) hk i hiL
  · have hiR : i - (F).LL.length < (F).LR.length := by
      rw [List.length_append] at hi
      omega
    have he := rMinusWhole_LR_get w h n (i - (F).LL.length) hiR
    have hnat : k + (i : ℤ) = ((i - (F).LL.length : ℕ) : ℤ) := by omega
    have hb : boundaryOuterEdge w h (k + (i : ℤ)) =
        kmswRightBoundaryEdge w (i - (F).LL.length) := by
      rw [hnat]
      by_cases hz : i - (F).LL.length = 0
      · rw [hz, Nat.cast_zero, boundaryOuterEdge_zero, kmswRightBoundaryEdge_zero]
      · rw [boundaryOuterEdge_of_positive w h (by omega), Int.toNat_natCast]
    rw [hb]
    simpa only [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt hiL)] using he

include hτ in
/-- Helper toward Lemma 5.5: past the attached upper frontier, hatted
boundary records map to the original positive exterior labels. -/
theorem rMinusWhole_future_boundary_tail (i : ℕ) (hi : (F).UR.length < i) :
    boundaryGluingEdgeMap W h k (kmswRightBoundaryEdge U i) =
      boundaryOuterEdge w h ((i : ℤ) - R w n) := by
  let m := natSelect (fun t => ∀ j < t, R U t < R U j) i
  have hR : ∀ a : ℤ, ∃ s, R U s ≤ a := by
    intro a
    obtain ⟨s, hs⟩ := (hatBoundaryHitWitnesses U hτ).rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨s, by have ha := le_max_left (-a) 1; omega⟩
  obtain ⟨hm, hv⟩ := rMinusWhole_selected_record U hR i
  have hshift (t : ℕ) : R w (n + t) = R w n + R U t :=
    rMinusWhole_R_shift_add w n t
  have hval : R w (n + m) = -((i : ℤ) - R w n) := by
    rw [hshift, hv]
    omega
  have hurlen := kmswStage_UR_length w n
  have hlow : R w (n + m) < minR w n := by omega
  have hrecord : ∀ j < n + m, R w (n + m) < R w j := by
    intro j hj
    by_cases hjt : j < n
    · have hb := runningMin_le (R w) n j hjt.le
      change minR w n ≤ R w j at hb
      exact hlow.trans_le hb
    · have hlocal := hm (j - n) (by omega)
      have hs := hshift (j - n)
      rw [Nat.add_sub_of_le (by omega : n ≤ j)] at hs
      have hs' := hshift m
      omega
  have hmin0 : minR w n ≤ 0 := by
    have hh := runningMin_le (R w) n 0 (Nat.zero_le _)
    change minR w n ≤ R w 0 at hh
    simpa only [R, Finset.range_zero, Finset.sum_empty] using hh
  have hpos : 1 ≤ (i : ℤ) - R w n := by omega
  have hcast : ((((i : ℤ) - R w n).toNat : ℕ) : ℤ) = (i : ℤ) - R w n :=
    Int.toNat_of_nonneg (by omega)
  have he := rMinusWhole_record_edge w (n + m) ((i : ℤ) - R w n).toNat
    hrecord (by rw [hcast]; exact hval)
  rw [boundaryOuterEdge_of_positive w h hpos]
  change kmswWindowEdgeMapInf w n (act U m) = _
  rw [kmswWindowEdgeMapInf_eq_stage w n m _ (act_lt_nextEdge U le_rfl)]
  exact (kmswWindowPatchData_rel w n m).active.trans he

include hk in
/-- Helper toward Lemma 5.5: the untouched hatted boundary tail starts
immediately after the finite lower boundary word, with no omitted endpoint. -/
theorem rMinusWhole_hatted_boundary_tail (i : ℕ)
    (hi : ((F).LL ++ (F).LR).length ≤ i) :
    let j := i - ((F).LL ++ (F).LR).length + ((F).active :: (F).UR).length
    (EH ((Q).boundary j).1, ((Q).boundary j).2) = (S).boundary i := by
  dsimp only
  let j := i - ((F).LL ++ (F).LR).length + ((F).active :: (F).UR).length
  have hj : (F).UR.length < j := by dsimp only [j]; simp only [List.length_cons]; omega
  have hll := rMinusWhole_LL_length (h := h) hk
  have hlr := kmswStage_LR_length w n
  have hur := kmswStage_UR_length w n
  have hjlabel : (j : ℤ) - R w n = k + (i : ℤ) := by
    dsimp only [j]
    simp only [List.length_append, List.length_cons] at hi ⊢
    omega
  have hb := boundaryGluing_nonneg_right_boundary_index hqMode j
  rw [hb, boundaryGluing_decoded_stream W h k hτ]
  change (boundaryGluingEdgeMap W h k
    (hatLimitEdgeMap U hτ (kmswRightBoundaryEdge z j)), false) = _
  rw [hattedSide_hatLimitEdgeMap_rightBoundaryEdge,
    rMinusWhole_future_boundary_tail hτ j hj, hjlabel]
  rfl

/-- Helper toward Lemma 5.5: the exterior boundary is read from the
finite lower word, followed by the hatted tail after the attached upper word.
This definition uses the two blocks and their gluing maps only. -/
@[expose] noncomputable def rMinusGluedBoundary (i : ℕ) :
    Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) → Prop
  | .inr d, _ =>
    (∃ a : StageDart (F).nextEdge,
      ((F).LL ++ (F).LR)[i]? = some a.1.val ∧ a.2 = false ∧
        rMinusGluedPrefixDart hτ hqMode a = d) ∨
    (((F).LL ++ (F).LR).length ≤ i ∧
      ∃ a : {d : ℕ × Bool // d.1 ∈ (Q).edges},
        (Q).boundary (i - ((F).LL ++ (F).LR).length + ((F).active :: (F).UR).length) = a.val ∧
          rMinusGluedHattedDart hτ hqMode a = d)
  | .inl _, _ => False

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every indexed exterior boundary tag is
preserved and reflected, including the join between prefix and hatted tail. -/
theorem rMinusGluedMarkedIso_boundary_iff (i : ℕ)
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedBoundary hτ hqMode i u v ↔
      geometricSideRelation S (.boundary i)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  let E := rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  cases u with
  | inl u => rfl
  | inr d =>
    change _ ↔ (S).boundary i = (E d).val
    constructor
    · rintro (⟨a, hai, ha, rfl⟩ | ⟨hi, a, ha, rfl⟩)
      · have hi := (List.getElem?_eq_some_iff.mp hai).1
        have hv := (List.getElem?_eq_some_iff.mp hai).2
        have hb := rMinusWhole_lower_get (h := h) hk i hi
        change (boundaryOuterEdge w h (k + (i : ℤ)), false) = (a.1.val, a.2)
        exact Prod.ext (hb.symm.trans hv) ha.symm
      · have hb := rMinusWhole_hatted_boundary_tail hτ hp P hqMode hk i hi
        dsimp only at hb
        rw [ha] at hb
        exact hb.symm
    · intro hd
      by_cases hi : i < ((F).LL ++ (F).LR).length
      · let e := ((F).LL ++ (F).LR).get ⟨i, hi⟩
        have he : e < (F).nextEdge := by
          apply (kmswStage_boundary_ids_lt_nextEdge w n).2
          have hm : e ∈ (F).LL ++ (F).LR := List.get_mem _ _
          simp only [List.mem_append] at hm ⊢
          tauto
        let a : StageDart (F).nextEdge := (⟨e, he⟩, false)
        refine Or.inl ⟨a, List.getElem?_eq_getElem hi, rfl, ?_⟩
        apply E.injective
        apply Subtype.ext
        have hb := rMinusWhole_lower_get (h := h) hk i hi
        change (e, false) = (E d).val
        exact (congrArg (fun e : ℕ => (e, false)) hb).trans hd
      · let j := i - ((F).LL ++ (F).LR).length + ((F).active :: (F).UR).length
        let a : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
          ⟨(Q).boundary j, rMinus_hatted_boundary_mem
            (if longest then XDP.ldp else XDP.sdp) ⟨boundaryFutureHattedPath k W, hqMode⟩ j⟩
        refine Or.inr ⟨Nat.le_of_not_gt hi, a, rfl, ?_⟩
        apply E.injective
        apply Subtype.ext
        exact (rMinusWhole_hatted_boundary_tail hτ hp P hqMode hk i
          (Nat.le_of_not_gt hi)).trans hd

/-- Helper toward Lemma 5.5: assemble the proved incidence, adjusted
code rotation, retained faces, exterior boundary and seam on the glued cells.
The relation is built from block data; it does not pull back a target relation. -/
@[expose] noncomputable def rMinusGluedWholeRelation :
    TruncationRelation →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) → Prop
  | .faceNext, u, v => rMinusGluedFaceNext hτ hqMode u v
  | .boundary i, u, v => rMinusGluedBoundary hτ hqMode i u v
  | .rotation, .inr d, .inr e =>
    Equiv.permCongr (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)
      (rMinusCodeInitialAdjustedRotation w n ⟨boundaryFutureHattedPath k W, hqMode⟩) d = e
  | .rotation, _, _ => False
  | t, u, v => rMinusGluedIncidenceRelation hτ hqMode t u v

/-- Helper toward Lemma 5.5: all marked relations agree on the complete
glued cell carrier. A code-only whole-side decoder remains a separate construction. -/
theorem rMinusGluedWholeRelation_iff (t : TruncationRelation)
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedWholeRelation hτ hp P hqMode Tpath hfin hleft hk t u v ↔
      geometricSideRelation S t
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  cases t with
  | vertex => exact rMinusGluedCellEquiv_vertex_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | root => exact rMinusGluedCellEquiv_root_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | incident => exact rMinusGluedCellEquiv_incident_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | opposite => exact rMinusGluedCellEquiv_opposite_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | oriented => exact rMinusGluedCellEquiv_oriented_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | rotation =>
    have hr := rMinusGluedCellEquiv_rotation_iff hτ hp P hqMode Tpath hfin hleft hk u v
    dsimp only at hr
    cases u <;> cases v <;> exact hr
  | faceNext => exact rMinusGluedMarkedIso_faceNext_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | target => exact rMinusGluedCellEquiv_target_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | boundary i => exact rMinusGluedMarkedIso_boundary_iff hτ hp P hqMode Tpath hfin hleft hk i u v
  | seam i => exact rMinusGluedCellEquiv_seam_iff hτ hp P hqMode Tpath hfin hleft hk i u v

end HattedFaces



















































end DirectedDistances.PaperProofs.Section5
