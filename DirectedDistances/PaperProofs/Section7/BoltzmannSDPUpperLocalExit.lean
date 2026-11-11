/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperExitMap
public import DirectedDistances.KMSW.StageUpperFutureTail
public import DirectedDistances.KMSW.StageTailPersistence
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperReversalClass
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperOuterCorner
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperReduction
import DirectedDistances.KMSW.Lemma79MarkTransport

public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open Quiver MeasureTheory ProbabilityTheory

attribute [local instance 1100] presentDartQuiver

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result. -/
private theorem localExit_cast_stage_arrow {w : ℕ → Fin 3} {n : ℕ}
    {a b b' : StagePresentVertex w n} (hb : b = b') (e : a ⟶ b) :
    (hb ▸ e).val = e.val := by
  cases hb
  rfl

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result. -/
private theorem localExit_cast_stage_arrow_source {w : ℕ → Fin 3} {n : ℕ}
    {a a' b : StagePresentVertex w n} (ha : a = a') (e : a ⟶ b) :
    (ha ▸ e).val = e.val := by
  cases ha
  rfl

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result. -/
private theorem localExit_minL_zero (w : ℕ → Fin 3) (hL : ∀ k, 0 ≤ L w k)
    (n : ℕ) : minL w n = 0 := by
  obtain ⟨j, _, he⟩ := runningMin_attained (L w) n
  have hle := runningMin_le (L w) n 0 (Nat.zero_le _)
  have hz : L w 0 = 0 := by simp only [L, Finset.range_zero, Finset.sum_empty]
  change minL w n = L w j at he
  change minL w n ≤ L w 0 at hle
  have hj := hL j
  omega

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
is a prefix of the new one, including the old sink, which becomes the new active tail. -/
private theorem boltzmannSdpUpper_down_UL_vertices (w : ℕ → Fin 3) (N : ℕ)
    (hc : w N = 2) (hUR : (kmswStage w N).UR = []) :
    ((kmswStage w (N + 1)).UL.map (kmswStage w (N + 1)).west) ++
        [(kmswStage w (N + 1)).east (kmswStage w (N + 1)).active] =
      (((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active]) ++
          [(kmswStage w N).nextVertex] := by
  have hUL : (kmswStage w (N + 1)).UL =
      (kmswStage w N).UL ++ [(kmswStage w N).nextEdge] := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR,
      State.addEdge]
  have hmap : ((kmswStage w N).UL.map (kmswStage w (N + 1)).west) =
      (kmswStage w N).UL.map (kmswStage w N).west := by
    apply List.map_congr_left
    intro e he
    have hb := (kmswStage_boundary_ids_lt_nextEdge w N).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl he)))
    exact (kmswStage_endpoints_stable w (Nat.le_succ N) hb).1
  have hwest : (kmswStage w (N + 1)).west (kmswStage w N).nextEdge =
      (kmswStage w N).east (kmswStage w N).active := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR,
      State.addEdge]
  rw [hUL, List.map_append, List.map_singleton, hmap, hwest]
  rw [(kmswStage_down_UR_nil_endpoints w N hc hUR).2]

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
the down step. Its old-list index still satisfies the cutoff, including the old sink. -/
private theorem boltzmannSdpUpper_oldTail_postHit_suffix (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N + 1 ≤ m) (hc : w N = 2) (hUR : (kmswStage w N).UR = [])
    (hL : ∀ k, 0 ≤ L w k)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex) (c : ℕ)
    (hcut : ∀ k, N + 1 ≤ k → k ≤ m → (c : ℤ) ≤ L w k) :
    ∃ i, c ≤ i ∧
      (((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active])[i]? =
          some ((kmswStage w m).west (kmswStage w m).active) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp
    (kmswStage_tail_mem_UL_vertex_list w (by omega) hOld hUR)
  have hget := (List.getElem?_eq_getElem hi).trans (congrArg some he)
  refine ⟨i, ?_, hget⟩
  apply kmswStage_old_tail_index_lower_bound w hNm
    ((localExit_minL_zero w hL m).trans (localExit_minL_zero w hL (N + 1)).symm)
      c i
  · intro k hNk hkm
    rw [localExit_minL_zero w hL (N + 1), sub_zero]
    exact hcut k hNk hkm
  · rw [boltzmannSdpUpper_down_UL_vertices w N hc hUR,
      List.getElem?_append_left hi]
    exact hget

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
has an exact hat index, including index zero; edge identities determine its raw time. -/
private theorem boltzmannSdpUpper_reachable_active_hatIndex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hv : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w m).west (kmswStage w m).active⟩) :
    ∃ j, quadrantRStageTime w h j = m := by
  obtain ⟨M, hM⟩ := quadrantRStageTime_unbounded w h m
  have hb := kmswStage_active_lt w m
  have hp := present_mono w hb (kmswStage_active_present w m) _ hM
  have hs := kmswStage_endpoints_stable w hM hb
  have hreach : (kmswStage w m).active ∈
      stageReachablePresentEdges w (quadrantRStageTime w h M) := by
    refine ⟨hp.1, hp.2, ?_, ?_⟩
    · rw [hs.1]
      exact hv
    · rw [hs.2]
      exact kmswStage_activeEast_reachable w m hv
  rw [← hatAllEdgeMap_image_eq_reachable w h M] at hreach
  obtain ⟨e, he, hep, hei⟩ := hreach
  obtain ⟨j, hjM, hje⟩ := kmswStage_present_eq_active (hatCodes w h) M e he hep
  have hjb := kmswStage_active_lt (hatCodes w h) j
  have hactive := (hatAll_sim w h j).incidenceSim.active
  have heq : (kmswStage w (quadrantRStageTime w h j)).active =
      (kmswStage w m).active := by
    rw [← hactive, hje, ← hatAllEdgeMap_eq_of_le w h j M e hjM (hje ▸ hjb)]
    exact hei
  exact ⟨j, CutConverse.act_injective w heq⟩

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
active tail is exactly the corresponding hat active tail, by incidence and injectivity. -/
private theorem boltzmannSdpUpper_oldVertex_active_tail (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {N j v : ℕ} (hNj : N ≤ j)
    (hv : v < (kmswStage (hatCodes w h) N).nextVertex)
    (heq : hatAllVertexMap w h N v =
      (kmswStage w (quadrantRStageTime w h j)).west
        (kmswStage w (quadrantRStageTime w h j)).active) :
    (kmswStage (hatCodes w h) j).west (kmswStage (hatCodes w h) j).active = v := by
  have hs := (hatAll_sim w h j).incidenceSim
  have hb := kmswStage_active_lt (hatCodes w h) j
  have hend := (kmswStage_endpoints_lt_nextVertex (hatCodes w h) j _ hb).1
  apply hs.vertex_injective _ _ hend
    (hv.trans_le (CutConverse.nextVertex_mono (hatCodes w h) hNj))
  calc
    _ = (kmswStage w (quadrantRStageTime w h j)).west
        (hatAllEdgeMap w h j (kmswStage (hatCodes w h) j).active) :=
      (hs.incidence _ hb).1.symm
    _ = _ := by rw [hs.active]
    _ = hatAllVertexMap w h N v := heq.symm
    _ = _ := (hatAllVertexMap_eq_of_le w h N j v hNj hv).symm

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
left-path vertex is its UL-list slot, with both endpoints included. -/
private theorem boltzmannSdpUpper_base_left_slot {ell r t : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) (j : Fin (ell + 1)) :
    (stageMapVertex (codeExtend c) (t - 1)
      ((kmswWalkClassBase ht c).leftPath.vertices.get
        ⟨j.val, by
          rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
          exact j.isLt⟩)).id =
      (stoppedLeftBoundaryVertices (codeExtend c) t).getD j.val 0 := by
  have he := kmswWalkClassRep_leftBoundaryVertex_getD_stage ht c j
  rw [kmswClass_leftBoundaryVertex_getD] at he
  rw [List.getD_eq_get _ _
    ⟨j.val, by rw [(kmswWalkClassBase ht c).leftPath.vertices_length]; exact j.isLt⟩]
      at he
  exact he

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
prefunctor lifts every outgoing arrow in the common stopped stage, preserving its ID. -/
private theorem boltzmannSdpUpper_baseHat_lift
    {D : Type*} [Fintype D] [DecidableEq D] {ell r t : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ell r) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) (I : BipolarBoundaryBaseIso B (kmswWalkClassBase ht c))
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hs : kmswStage (codeExtend c) (t - 1) = kmswStage (hatCodes w h) (t - 1))
    (a : MapVertex B.map) (b : StagePresentVertex (hatCodes w h) (t - 1))
    (e : (boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs).obj a ⟶ b) :
    ∃ z : MapVertex B.map, ∃ f : a ⟶ z,
      ∃ hz : (boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs).obj z = b,
        hz ▸ (boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs).map f = e := by
  classical
  let C := kmswWalkClassBase ht c
  let d : StageDart (kmswStage (codeExtend c) (t - 1)).nextEdge :=
    (⟨e.val, by rw [hs]; exact e.property.1⟩, false)
  let z := I.vertexEquiv.symm (dartHeadVertex C.map d)
  have htail : dartTailVertex C.map d = I.vertexEquiv a := by
    apply stageMapVertex_injective (codeExtend c) (t - 1)
    apply congrArg (StagePresentVertex.mk (w := codeExtend c) (n := t - 1))
    change (kmswStage (codeExtend c) (t - 1)).west e.val = _
    exact (congrArg (fun s : State => s.west e.val) hs).trans e.property.2.2.1
  have hp : ¬ C.map.missing d ∧ C.map.tail d := by
    have hpres : (kmswStage (codeExtend c) (t - 1)).present e.val = true := by
      rw [hs]
      exact e.property.2.1
    exact ⟨by change ¬ _ = false; rw [hpres]; decide, hpres, rfl⟩
  let dB := I.toEquiv.symm d
  have htailB : dartTailVertex B.map dB = a := by
    apply I.vertexEquiv.injective
    rw [I.vertexEquiv_dartTailVertex]
    change dartTailVertex C.map (I.toEquiv (I.toEquiv.symm d)) = _
    rw [Equiv.apply_symm_apply]
    exact htail
  have hheadB : dartHeadVertex B.map dB = z := by
    apply I.vertexEquiv.injective
    rw [I.vertexEquiv_dartHeadVertex]
    change dartHeadVertex C.map (I.toEquiv (I.toEquiv.symm d)) = _
    rw [Equiv.apply_symm_apply]
    exact (I.vertexEquiv.apply_symm_apply _).symm
  let f : a ⟶ z := ⟨dB, by
    rw [← I.toEquiv.apply_symm_apply d] at hp
    exact ⟨fun hm => hp.1 ((I.missing_iff dB).2 hm),
      (I.tail_iff dB).1 hp.2, htailB, hheadB⟩⟩
  have hz : (boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs).obj z = b := by
    apply congrArg (StagePresentVertex.mk (w := hatCodes w h) (n := t - 1))
    rw [I.vertexEquiv.apply_symm_apply]
    change (kmswStage (codeExtend c) (t - 1)).east e.val = b.id
    rw [hs]
    exact e.property.2.2.2
  refine ⟨z, f, hz, ?_⟩
  apply Subtype.ext
  rw [localExit_cast_stage_arrow]
  change (I.toEquiv (I.toEquiv.symm d)).1.val = e.val
  rw [Equiv.apply_symm_apply]

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
map is reachable from its source in the present-dart quiver. -/
private theorem boltzmannSdpUpper_source_reachable
    {D : Type*} [Fintype D] [DecidableEq D] {ell r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ell r) (a : MapVertex B.map) :
    Reachable B.source a := by
  obtain ⟨_, P, _⟩ := exists_simple_source_pathBase B a
  obtain ⟨Q, _, _⟩ := boltzmannSdpUpper_simple_exists_presentPath P
  exact ⟨Q⟩

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
minimum, so the actual mark bounds every first coordinate at or after the hit. -/
private theorem boltzmannSdpUpper_mark_postHit_bound (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (hp : ∀ k, 0 ≤ (p k).1) (k : ℕ)
    (hk : (conditionedSecondCoordinateFirstHit r p).toNat ≤ k) :
    ((stoppedMarked r hr p).2.val : ℤ) ≤ (p k).1 := by
  have hb : BddBelow (Set.range (fun j : ℕ =>
      (p ((conditionedSecondCoordinateFirstHit r p).toNat + j)).1)) :=
    ⟨0, by rintro z ⟨j, rfl⟩; exact hp _⟩
  have hi : postHitMinimum r p ≤ (p k).1 := by
    have hi : postHitMinimum r p ≤
        (p ((conditionedSecondCoordinateFirstHit r p).toNat +
          (k - (conditionedSecondCoordinateFirstHit r p).toNat))).1 :=
      ciInf_le hb _
    simpa only [Nat.add_sub_of_le hk] using hi
  have hnat := Int.toNat_le_toNat hi
  have hmark : (stoppedMarked r hr p).2.val ≤ (postHitMinimum r p).toNat :=
    Nat.min_le_left _ _
  have hpk := hp k
  omega

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
pathwise under the actual flow-line-hit witness, without a further almost-sure premise. -/
private theorem boltzmannSdpUpper_hat_L_nonneg (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) : 0 ≤ L (hatCodes w h) k := by
  have he : L (hatCodes w h) k = (integrateCodes (hatCodes w h) k).1 := by
    simp only [L, integrateCodes, Prod.fst_sum]
  rw [he, ← rCodeSequence_quadrantTrajectory_eq_hatCodes w h]
  exact integrateCodes_pitmanCode_fst_nonneg _ k

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
post-hit active tail lies in the marked upper arc. The cutoff starts at the hit stage. -/
private theorem boltzmannSdpUpper_postHit_tail_preimage {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (ht : 1 ≤ q.1.2.1)
    (c : KMSWWalkClass q.1.1 r q.1.2.1)
    (I : BipolarBoundaryBaseIso q.1.2.2.out.B (kmswWalkClassBase ht c))
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hs : kmswStage (codeExtend c) (q.1.2.1 - 1) =
      kmswStage (hatCodes w h) (q.1.2.1 - 1))
    (hc : hatCodes w h (q.1.2.1 - 1) = 2)
    (hUR : (kmswStage (hatCodes w h) (q.1.2.1 - 1)).UR = [])
    (hcut : ∀ k, q.1.2.1 ≤ k → (q.2.val : ℤ) ≤ L (hatCodes w h) k)
    (a : MapVertex q.1.2.2.out.B.map) (j : ℕ) (htj : q.1.2.1 ≤ j)
    (ha : hatAllVertexMap w h (q.1.2.1 - 1)
      (stageMapVertex (codeExtend c) (q.1.2.1 - 1) (I.vertexEquiv a)).id =
        (kmswStage w (quadrantRStageTime w h j)).west
          (kmswStage w (quadrantRStageTime w h j)).active) :
    a ∈ boltzmannSdpUpper_upperMarkedArc q := by
  let N := q.1.2.1 - 1
  let v := (stageMapVertex (codeExtend c) N (I.vertexEquiv a)).id
  have hv : v < (kmswStage (hatCodes w h) N).nextVertex := by
    have hb := (stageVertexEquiv (codeExtend c) N (I.vertexEquiv a)).isLt
    exact hb.trans_le (Nat.le_of_eq (congrArg State.nextVertex hs))
  have htail := boltzmannSdpUpper_oldVertex_active_tail w h (by omega) hv ha
  have hOld : (kmswStage (hatCodes w h) j).west
      (kmswStage (hatCodes w h) j).active < (kmswStage (hatCodes w h) N).nextVertex := by
    rw [htail]
    exact hv
  obtain ⟨i, hmark, hslot⟩ := boltzmannSdpUpper_oldTail_postHit_suffix
    (hatCodes w h) (by omega) hc hUR
    (boltzmannSdpUpper_hat_L_nonneg w h) hOld q.2.val
    (fun k hNk _ => hcut k (by omega))
  rw [htail] at hslot
  have hlen : (kmswStage (codeExtend c) N).UL.length = q.1.1 := by
    simpa only [kmswStageULDartRun, stageDarts, List.length_map,
      List.length_attach] using kmswWalkClassBase_leftDartRun_length ht c
  have hi : i < q.1.1 + 1 := by
    have hbound := List.getElem?_eq_some_iff.mp hslot
    have hlen' : (kmswStage (hatCodes w h) N).UL.length = q.1.1 := by
      rw [← hs]
      exact hlen
    have hh := hbound.1
    simp only [List.length_append, List.length_map, List.length_singleton] at hh
    change i < (kmswStage (hatCodes w h) N).UL.length + 1 at hh
    rwa [hlen'] at hh
  let ix : Fin (q.1.1 + 1) := ⟨i, hi⟩
  refine ⟨ix, hmark, ?_⟩
  apply I.vertexEquiv.injective
  apply stageMapVertex_injective (codeExtend c) N
  apply congrArg (StagePresentVertex.mk (w := codeExtend c) (n := N))
  change v = (stageMapVertex (codeExtend c) N
    (I.vertexEquiv (boltzmannSdpUpper_leftVertex q ix))).id
  rw [boltzmannSdpUpper_baseIso_leftVertex q ht c I ix,
    boltzmannSdpUpper_base_left_slot ht c ix]
  have hget : (stoppedLeftBoundaryVertices (hatCodes w h) q.1.2.1).getD i 0 = v := by
    change (stoppedLeftBoundaryVertices (hatCodes w h) q.1.2.1)[i]? = some v
      at hslot
    change _[i]?.getD 0 = v
    rw [hslot]
    rfl
  have hlists : stoppedLeftBoundaryVertices (codeExtend c) q.1.2.1 =
      stoppedLeftBoundaryVertices (hatCodes w h) q.1.2.1 := by
    simp only [stoppedLeftBoundaryVertices, act, hs]
  rw [hlists]
  exact hget.symm

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
satisfies lifting and the endpoint clause once the post-hit cutoff is identified. -/
private theorem boltzmannSdpUpper_localExit_at {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (ht : 1 ≤ q.1.2.1)
    (c : KMSWWalkClass q.1.1 r q.1.2.1)
    (I : BipolarBoundaryBaseIso q.1.2.2.out.B (kmswWalkClassBase ht c))
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (hs : kmswStage (codeExtend c) (q.1.2.1 - 1) =
      kmswStage (hatCodes w h) (q.1.2.1 - 1))
    (hc : hatCodes w h (q.1.2.1 - 1) = 2)
    (hUR : (kmswStage (hatCodes w h) (q.1.2.1 - 1)).UR = [])
    (hcut : ∀ k, q.1.2.1 ≤ k → (q.2.val : ℤ) ≤ L (hatCodes w h) k)
    (n : ℕ) (hn : quadrantRStageTime w h q.1.2.1 ≤ n) :
    ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map) (StagePresentVertex w n),
      F.obj q.1.2.2.out.B.source = ⟨0⟩ ∧
      (∀ a : MapVertex q.1.2.2.out.B.map,
        a ∉ boltzmannSdpUpper_upperMarkedArc q →
        ∀ b : StagePresentVertex w n, ∀ edge : F.obj a ⟶ b,
          ∃ z : MapVertex q.1.2.2.out.B.map, ∃ lifted : a ⟶ z,
            ∃ hz : F.obj z = b, hz ▸ F.map lifted = edge) ∧
      ∀ y : ℕ,
        (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
        boltzmannSdpUpper_endpointAboveMark q F ⟨y⟩ := by
  classical
  let N := q.1.2.1 - 1
  have hNn : quadrantRStageTime w h N ≤ n :=
    (quadrantRStageTime_mono w h (Nat.sub_le _ _)).trans hn
  let B := q.1.2.2.out.B
  let G := boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs
  let H := boltzmannSdpUpper_hatRawStagePrefunctor w h N n hNn
  let F := G.comp H
  have hbound (a : MapVertex B.map) :
      (G.obj a).id < (kmswStage (hatCodes w h) N).nextVertex := by
    exact (stageVertexEquiv (codeExtend c) N (I.vertexEquiv a)).isLt.trans_le
      (Nat.le_of_eq (congrArg State.nextVertex hs))
  have hobj (a : MapVertex B.map) : F.obj a =
      ⟨hatAllVertexMap w h N (G.obj a).id⟩ := by
    change (⟨boltzmannSdpUpper_hatRawVertex w h N (G.obj a).id⟩ :
      StagePresentVertex w n) = _
    rw [boltzmannSdpUpper_hatRawVertex, ite_eq_left (hbound a)]
  have hsource : F.obj B.source = ⟨0⟩ := by
    have hG : G.obj B.source = ⟨0⟩ := by
      change (⟨(stageMapVertex (codeExtend c) N (I.vertexEquiv B.source)).id⟩ :
        StagePresentVertex (hatCodes w h) N) = ⟨0⟩
      rw [I.vertexEquiv_source, boltzmannSdpUpper_stageBase_source ht c]
    change H.obj (G.obj B.source) = ⟨0⟩
    rw [hG]
    exact boltzmannSdpUpper_hatRawStagePrefunctor_root w h N n hNn
  have hreach (a : MapVertex B.map) :
      Reachable (⟨0⟩ : PresentVertex w) ⟨(F.obj a).id⟩ := by
    obtain ⟨P⟩ := boltzmannSdpUpper_source_reachable B a
    have hP : Reachable (F.obj B.source) (F.obj a) := ⟨F.mapPath P⟩
    rw [hsource] at hP
    exact stageToLimit_reachable w n hP
  have hfuture (a : MapVertex B.map) (m : ℕ)
      (hm : quadrantRStageTime w h q.1.2.1 ≤ m)
      (ha : (F.obj a).id = (kmswStage w m).west (kmswStage w m).active) :
      a ∈ boltzmannSdpUpper_upperMarkedArc q := by
    have hr := hreach a
    rw [ha] at hr
    obtain ⟨j, hj⟩ := boltzmannSdpUpper_reachable_active_hatIndex w h m hr
    have htj : q.1.2.1 ≤ j := (quadrantRStageTime_strictMono w h).le_iff_le.mp
      (by rw [hj]; exact hm)
    apply boltzmannSdpUpper_postHit_tail_preimage q ht c I w h hs hc hUR hcut a j htj
    have ho := congrArg StagePresentVertex.id (hobj a)
    change (F.obj a).id = hatAllVertexMap w h N (G.obj a).id at ho
    change hatAllVertexMap w h N (G.obj a).id = _
    rw [← ho, hj]
    exact ha
  refine ⟨F, hsource, ?_, ?_⟩
  · intro a ha b e
    obtain ⟨m, hmn, hme⟩ := kmswStage_present_eq_active w n e.val
      e.property.1 e.property.2.1
    have hmb := kmswStage_active_lt w m
    have hstable := kmswStage_endpoints_stable w hmn hmb
    have hatTail : (F.obj a).id = (kmswStage w m).west (kmswStage w m).active := by
      calc
        _ = (kmswStage w n).west e.val := e.property.2.2.1.symm
        _ = (kmswStage w n).west (kmswStage w m).active := by rw [hme]
        _ = _ := hstable.1
    have hr := hreach a
    rw [hatTail] at hr
    obtain ⟨j, hj⟩ := boltzmannSdpUpper_reachable_active_hatIndex w h m hr
    by_cases hlate : q.1.2.1 ≤ j
    · have htm := quadrantRStageTime_mono w h hlate
      rw [hj] at htm
      exact (ha (hfuture a m htm hatTail)).elim
    · have hjN : j ≤ N := by omega
      let d := (kmswStage (hatCodes w h) j).active
      have hdb := kmswStage_active_lt (hatCodes w h) j
      have hdp := present_mono (hatCodes w h) hdb
        (kmswStage_active_present (hatCodes w h) j) N hjN
      let u : StagePresentVertex (hatCodes w h) N :=
        ⟨(kmswStage (hatCodes w h) N).west d⟩
      let v : StagePresentVertex (hatCodes w h) N :=
        ⟨(kmswStage (hatCodes w h) N).east d⟩
      let eh : u ⟶ v := ⟨d, hdp.1, hdp.2, rfl, rfl⟩
      have hid : (H.map eh).val = e.val := by
        rw [boltzmannSdpUpper_hatRawStagePrefunctor_edge_id,
          hatAllEdgeMap_eq_of_le w h j N d hjN hdb]
        have hh := (hatAll_sim w h j).incidenceSim.active
        change hatAllEdgeMap w h j d =
          (kmswStage w (quadrantRStageTime w h j)).active at hh
        rw [hh, hj]
        exact hme
      have hu : u = G.obj a := by
        apply boltzmannSdpUpper_hatRawStagePrefunctor_obj_injective w h N n hNn
        apply congrArg (StagePresentVertex.mk (w := w) (n := n))
        change (H.obj u).id = (F.obj a).id
        exact (H.map eh).property.2.2.1.symm.trans
          ((congrArg (kmswStage w n).west hid).trans e.property.2.2.1)
      let eh' : G.obj a ⟶ v := hu ▸ eh
      have heh : eh'.val = d := localExit_cast_stage_arrow_source hu eh
      obtain ⟨z, f, hz, hf⟩ := boltzmannSdpUpper_baseHat_lift B ht c I w h hs a v eh'
      have hfval : (G.map f).val = d := by
        have hh := congrArg Subtype.val hf
        rw [localExit_cast_stage_arrow] at hh
        exact hh.trans heh
      have hfid : (F.map f).val = e.val := by
        change hatAllEdgeMap w h N (G.map f).val = e.val
        rw [hfval]
        exact hid
      have hzb : F.obj z = b := by
        apply congrArg (StagePresentVertex.mk (w := w) (n := n))
        exact (F.map f).property.2.2.2.symm.trans
          ((congrArg (kmswStage w n).east hfid).trans e.property.2.2.2)
      refine ⟨z, f, hzb, ?_⟩
      apply Subtype.ext
      rw [localExit_cast_stage_arrow]
      exact hfid
  · intro y hy a ha
    obtain ⟨m, hnm, hm⟩ := kmswStage_upper_vertex_future_tail w hb n y hy
    apply hfuture a m (hn.trans hnm)
    exact (congrArg StagePresentVertex.id ha).trans hm.symm

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
simultaneous probability-one event for every positive radius and every raw hit stage. -/
theorem boltzmannSdpUpper_localExitGeometry_holds :
    boltzmannSdpUpper_localExitGeometry := by
  classical
  unfold boltzmannSdpUpper_localExitGeometry
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits, iidCodes_ae_boundaryHitWitnesses]
    with ω h hb
  intro r hr n hhit
  let w := fun i => ω (i + 1)
  let q := stoppedMarked r hr (quadrantHatWalk ω)
  obtain ⟨_, _, _, ht, c, I, htime, _, hs, _⟩ :=
    boltzmannSdpUpper_exitMap ω r hr h hb n hhit
  change ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map) (StagePresentVertex w n), _
  have hthit : R (hatCodes w h) q.1.2.1 = -(r : ℤ) := by
    rw [htime, hattedRightVertexHitTime_eq_hattedRightHitTime w h hb r hr]
    exact hattedRightHitTime_spec w h r hr
  have hfirst : ∀ s < q.1.2.1, R (hatCodes w h) s ≠ -(r : ℤ) := by
    intro s hst
    have hlt : s < hattedRightHitTime w h r hr := by
      rwa [htime, hattedRightVertexHitTime_eq_hattedRightHitTime w h hb r hr] at hst
    exact Nat.find_min (hattedRightHit_exists w h r hr) hlt
  have hUR := stopped_UR_nil (hatCodes w h) r hr hthit hfirst
  have hprev := (hat_first_hit_prev_running_min (hatCodes w h) r hr hthit hfirst).1
  have hc : hatCodes w h (q.1.2.1 - 1) = 2 := by
    have hstep : R (hatCodes w h) (q.1.2.1 - 1 + 1) =
        R (hatCodes w h) (q.1.2.1 - 1) +
          (lazyTwoDimensionalStep (hatCodes w h (q.1.2.1 - 1))).2 :=
      Finset.sum_range_succ _ _
    have hidx : q.1.2.1 - 1 + 1 = q.1.2.1 := Nat.sub_add_cancel ht
    rw [hidx, hthit, hprev] at hstep
    have hdown : (lazyTwoDimensionalStep (hatCodes w h (q.1.2.1 - 1))).2 = -1 := by
      omega
    generalize hatCodes w h (q.1.2.1 - 1) = code at hdown ⊢
    fin_cases code
    · norm_num [lazyTwoDimensionalStep] at hdown
    · norm_num [lazyTwoDimensionalStep] at hdown
    · rfl
  have hp : quadrantHatWalk ω = integrateCodes (hatCodes w h) := by
    rw [quadrantHatWalk_eq_interval ω h]
    rfl
  have hpL (k : ℕ) : (quadrantHatWalk ω k).1 = L (hatCodes w h) k := by
    rw [hp]
    simp only [integrateCodes, L, Prod.fst_sum]
  have hpR (k : ℕ) : (quadrantHatWalk ω k).2 = R (hatCodes w h) k := by
    rw [hp]
    simp only [integrateCodes, R, Prod.snd_sum]
  have hphit : ∃ k, (quadrantHatWalk ω k).2 = -(r : ℤ) :=
    ⟨q.1.2.1, (hpR _).trans hthit⟩
  have hfind : Nat.find hphit = q.1.2.1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hphit ((hpR _).trans hthit)
    · by_contra hnot
      have hf := Nat.find_spec hphit
      rw [hpR] at hf
      exact hfirst _ (by omega) hf
  have hhitTime : (conditionedSecondCoordinateFirstHit r (quadrantHatWalk ω)).toNat =
      q.1.2.1 := by
    rw [conditionedSecondCoordinateFirstHit, dite_eq_left hphit]
    simpa only [ENat.toNat_natCast] using hfind
  have hcut (k : ℕ) (hk : q.1.2.1 ≤ k) : (q.2.val : ℤ) ≤ L (hatCodes w h) k := by
    have hm := boltzmannSdpUpper_mark_postHit_bound r hr (quadrantHatWalk ω)
      (fun k => by rw [hpL]; exact boltzmannSdpUpper_hat_L_nonneg w h k) k
      (by rw [hhitTime]; exact hk)
    rw [hpL] at hm
    exact hm
  have hn : quadrantRStageTime w h q.1.2.1 ≤ n := by
    obtain ⟨k, hkn, hk⟩ := hhit
    have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have hfindRaw : boundaryHitTime w hb (r : ℤ) =
        Nat.find (hb.rightHit (r : ℤ) hrZ) := by
      unfold boundaryHitTime
      simp only [dite_eq_right (by omega : (r : ℤ) ≠ 0),
        dite_eq_left (by omega : (0 : ℤ) < r)]
    have htimeRaw : quadrantRStageTime w h q.1.2.1 = boundaryHitTime w hb (r : ℤ) := by
      rw [htime]
      exact
        (DirectedDistances.PaperProofs.Section5.quadrantRStageTime_eq_sourceQuadrantS
          w h _).trans (sourceHitTime_eq_sourceHattedRightVertexHit w h hb r hr).symm
    rw [htimeRaw, hfindRaw]
    exact (Nat.find_min' (hb.rightHit (r : ℤ) hrZ) hk).trans hkn
  exact boltzmannSdpUpper_localExit_at q ht c I w h hb hs hc hUR hcut n hn

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
conclusion follows from the three proved geometric inputs and the existing reduction. -/
theorem boltzmann_sdp_upper_code :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
          ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))} := by
  exact boltzmann_sdp_upper_of_threeProps boltzmannSdpUpper_localExitGeometry_holds
    boltzmannSdpUpper_reversalClassGeometry_holds
    boltzmannSdpUpper_boundaryPathIntersection_proved

/-- Helper (code level) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
provider's exact target form; this makes no whole-paper completion claim. -/
theorem boltzmann_sdp_upper_code_providerTarget : boltzmannSdpUpperThreePropsProviderTarget :=
  boltzmann_sdp_upper_of_threeProps_matches_providerTarget.mp boltzmann_sdp_upper_code

end DirectedDistances.PaperProofs.Section7
