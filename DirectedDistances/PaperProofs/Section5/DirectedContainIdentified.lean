/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmost
public import DirectedDistances.KMSW.M0CutIdentificationAE
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.ShiftHatReach
public import DirectedDistances.KMSW.DirectedContainLaw1
public import DirectedDistances.KMSW.WindowModelHatCodes
public import DirectedDistances.KMSW.FutureMapHatLaw

/-! Supporting lemmas for paper labels `lem-directed-contain` (see CORRESPONDENCE.md). -/












public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk



private theorem present_endpoints_allocated (u : ℕ → Fin 3) {e : ℕ}
    (he : EdgePresent u e) :
    kmswVertexAllocated u ⟨edgeWest u e⟩ ∧
      kmswVertexAllocated u ⟨edgeEast u e⟩ := by
  obtain ⟨m, hm, _⟩ := he
  have hb := kmswStage_endpoints_lt_nextVertex u m e hm
  rw [(edge_endpoints_eq u hm).1, (edge_endpoints_eq u hm).2] at hb
  exact ⟨⟨m, hb.1⟩, ⟨m, hb.2⟩⟩





theorem boundary_infinitePath_lifts_to_shifted_limit
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h k)) :
    ∃ Q : InfinitePresentPath
        (fun i => w (boundaryHitTime w h k + i)) ⟨0⟩,
      ∀ n, shiftLimitEdge w (boundaryHitTime w h k)
        ⟨Q.edge n, (Q.edge_outgoing_at_initial _ n).1⟩ = P.edge n := by
  classical
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  have hlate (n : ℕ) : t ≤ actTime w (P.edge n)
      (P.edge_outgoing_at_initial w n).1 := by
    have hmem : P.edge n ∈ pathEdgeList (P.initial (n + 1)).2 := by
      rw [P.prefix_edges]
      exact List.mem_ofFn.mpr ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
    obtain ⟨m, htm, hm⟩ := boundary_path_future_edges w h k
      (P.initial (n + 1)).2 (P.edge n) hmem
    have ht := (actTime_eq_iff w (P.edge n)
      (P.edge_outgoing_at_initial w n).1 m).2 hm
    simpa [ht] using htm
  have hex (n : ℕ) : ∃ e : {e : ℕ // EdgePresent u e},
      shiftLimitEdge w t e = P.edge n :=
    (shiftLimitEdge_image_iff w t (P.edge n)
      (P.edge_outgoing_at_initial w n).1).2 (hlate n)
  choose e he using hex
  have halloc (n : ℕ) := present_endpoints_allocated u (e n).property
  have hinc (n : ℕ) := shiftLimitEdge_incidence w t (e n)
  have hroot : shiftLimitVertex w t (⟨0⟩ : PresentVertex u) =
      (boundaryPresentVertex w h k) := by
    rw [shiftLimitVertex_eq w t 0 ⟨0⟩ (by change 0 < 2; omega)]
    exact congrArg PresentVertex.mk (kmswShift_root_vertex_map w h k)
  have hstart : edgeWest u (e 0).val = 0 := by
    have hs : shiftLimitVertex w t ⟨edgeWest u (e 0).val⟩ =
        boundaryPresentVertex w h k := by
      apply congrArg PresentVertex.mk
      exact (hinc 0).1.symm.trans
        ((congrArg (edgeWest w) (he 0)).trans (P.first_edge_outgoing w).2)
    have hz := shiftLimitVertex_injective w t (halloc 0).1
      (show kmswVertexAllocated u ⟨0⟩ from ⟨0, by change 0 < 2; omega⟩)
      (hs.trans hroot.symm)
    exact congrArg PresentVertex.id hz
  have hchain (n : ℕ) : edgeEast u (e n).val = edgeWest u (e (n + 1)).val := by
    have hc : edgeEast w (P.edge n) = edgeWest w (P.edge (n + 1)) :=
      (P.edge_incoming_at_succ w n).2.trans
        (P.edge_outgoing_at_initial w (n + 1)).2.symm
    have hv : shiftLimitVertex w t ⟨edgeEast u (e n).val⟩ =
        shiftLimitVertex w t ⟨edgeWest u (e (n + 1)).val⟩ := by
      apply congrArg PresentVertex.mk
      exact (hinc n).2.symm.trans
        ((congrArg (edgeEast w) (he n)).trans
          (hc.trans ((congrArg (edgeWest w) (he (n + 1))).symm.trans
            (hinc (n + 1)).1)))
    exact congrArg PresentVertex.id
      (shiftLimitVertex_injective w t (halloc n).2 (halloc (n + 1)).1 hv)
  have hpref (n : ℕ) : ∃ q : Path (⟨0⟩ : PresentVertex u)
      ⟨edgeWest u (e n).val⟩,
      q.length = n ∧ pathEdgeList q = List.ofFn (fun i : Fin n => (e i.val).val) := by
    induction n with
    | zero =>
      rw [hstart]
      exact ⟨.nil, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨q, hlen, hedges⟩ := ih
      let f : (⟨edgeWest u (e n).val⟩ : PresentVertex u) ⟶
          ⟨edgeWest u (e (n + 1)).val⟩ :=
        ⟨(e n).val, (e n).property, rfl, hchain n⟩
      refine ⟨q.cons f, congrArg (· + 1) hlen, ?_⟩
      simp only [pathEdgeList, hedges, List.ofFn_succ', List.concat_eq_append,
        Fin.val_castSucc, Fin.val_last]
      rfl
  choose q hlen hedges using hpref
  let Q : InfinitePresentPath u ⟨0⟩ :=
    ⟨fun n => (e n).val, fun n => ⟨⟨edgeWest u (e n).val⟩, q n⟩, hlen, hedges⟩
  exact ⟨Q, he⟩

section Cut

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "w" => shiftedStream W 0
local notation "V" => wholePlaneVertexι W 0
local notation "E" => wholePlaneEdgeι W 0
local notation "D" => m0CutData W H h hLL



theorem m0Cut_finitePath_lift_edges (n : ℕ)
    (p : Fin (n + 1) → WholePlaneVertex W) (e : Fin n → WholePlaneEdge W)
    (a : ℕ) (h0 : p 0 = V a)
    (hcut : ∀ i, e i ∈ (D).edges)
    (hdir : ∀ i, (D).tail (e i, false))
    (hw : ∀ i, wholePlaneEdgeWest W (e i) = p i.castSucc)
    (he : ∀ i, wholePlaneEdgeEast W (e i) = p i.succ) :
    ∃ b, V b = p (Fin.last n) ∧
      ∃ q : Path (⟨a⟩ : PresentVertex w) ⟨b⟩,
        q.length = n ∧ (pathEdgeList q).map E = List.ofFn e := by
  induction n generalizing a with
  | zero =>
    exact ⟨a, h0.symm, .nil, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨c, hc, q, hlen, hedges⟩ := ih
      (fun i => p i.castSucc) (fun i => e i.castSucc) a h0
      (fun i => hcut i.castSucc) (fun i => hdir i.castSucc)
      (fun i => hw i.castSucc) (fun i => he i.castSucc)
    have hlast := hcut (Fin.last n)
    rw [(D).edges_eq h hLL] at hlast
    obtain ⟨f, hf⟩ := hlast
    have hpres : EdgePresent w f := by
      have hd := hdir (Fin.last n)
      rw [← hf] at hd
      exact ((m0Cut_tail_iff W H h hLL (f, false)).1 hd).2
    have hwest : edgeWest w f = c := by
      apply wholePlaneVertexι_injective W 0
      rw [← m0Cut_edgeWest, hf, hw]
      exact hc.symm
    let g : (⟨c⟩ : PresentVertex w) ⟶ ⟨edgeEast w f⟩ :=
      ⟨f, hpres, hwest, rfl⟩
    refine ⟨edgeEast w f, ?_, q.cons g, congrArg (· + 1) hlen, ?_⟩
    · rw [← m0Cut_edgeEast, hf, he]
      rfl
    · simp only [pathEdgeList, List.map_append, List.map_singleton, hedges,
        List.ofFn_succ', List.concat_eq_append]
      exact congrArg (List.ofFn (fun i : Fin n => e i.castSucc) ++ ·)
        (congrArg (fun x => [x]) hf)




theorem m0Cut_finitePath_lifts_to_shifted_stage (k : ℤ) (n : ℕ)
    (p : Fin (n + 1) → WholePlaneVertex W) (e : Fin n → WholePlaneEdge W)
    (h0 : p 0 = (D).x k)
    (hcut : ∀ i, e i ∈ (D).edges)
    (hdir : ∀ i, (D).tail (e i, false))
    (hw : ∀ i, wholePlaneEdgeWest W (e i) = p i.castSucc)
    (he : ∀ i, wholePlaneEdgeEast W (e i) = p i.succ) :
    ∃ m, ∃ z : StagePresentVertex (fun i => w (boundaryHitTime w h k + i)) m,
      ∃ q : Path (⟨0⟩ : StagePresentVertex
        (fun i => w (boundaryHitTime w h k + i)) m) z,
        V ((kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj ⟨0⟩).id =
          (D).x k ∧
        V ((kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj z).id =
          p (Fin.last n) ∧
        (pathEdgeList ((kmswShiftStageToLimit w
          (boundaryHitTime w h k) m).mapPath q)).map E = List.ofFn e ∧
        q.length = n := by
  obtain ⟨b, hb, r, hrlen, hredges⟩ := m0Cut_finitePath_lift_edges W H h hLL
    n p e (boundaryVertex w h k) (h0.trans ((D).x_eq h hLL k)) hcut hdir hw he
  obtain ⟨m, z, q, hroot, hend, hedge, hlen⟩ :=
    boundary_path_lifts_to_shifted_stage w h k r
  refine ⟨m, z, q, ?_, ?_, ?_, ?_⟩
  · rw [hroot]
    exact ((D).x_eq h hLL k).symm
  · rw [hend]
    exact hb
  · rw [hedge]
    exact hredges
  · rw [← kmswShiftStageToLimit_length w (boundaryHitTime w h k) m q, hlen, hrlen]





theorem m0Cut_infinitePath_lifts_to_shifted_limit (k : ℤ)
    (P : M0CutInfinitePath W H D ((D).x k)) :
    ∃ Q : InfinitePresentPath (fun i => w (boundaryHitTime w h k + i)) ⟨0⟩,
      ∀ n, E (shiftLimitEdge w (boundaryHitTime w h k)
        ⟨Q.edge n, (Q.edge_outgoing_at_initial _ n).1⟩) = P.edge n := by
  obtain ⟨R, hR, _⟩ := m0Cut_infinitePath_lift W H h hLL k P
  obtain ⟨Q, hQ⟩ := boundary_infinitePath_lifts_to_shifted_limit w h k R
  exact ⟨Q, fun n => (congrArg E (hQ n)).trans (hR n)⟩

end Cut



@[expose] noncomputable def boundaryCodeTime (k : ℤ) (ω : ℕ → Fin 3) : ℕ :=
  if k = 0 then 0 else if 0 < k then (codeSndFirstHit (-k) ω).toNat
    else (codeFstFirstHit k ω).toNat



@[expose] noncomputable def boundaryCodeShift (k : ℤ) (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  codeShift (boundaryCodeTime k ω) ω



theorem measurable_boundaryCodeShift (k : ℤ) : Measurable (boundaryCodeShift k) := by
  change Measurable (fun ω => codeShift (boundaryCodeTime k ω) ω)
  by_cases hk0 : k = 0
  · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_left hk0] using
      measurable_codeShift 0
  · by_cases hk : 0 < k
    · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_right hk0, ite_eq_left hk] using
        measurable_codeShift_toNat (codeSndFirstHit (-k))
          (measurableSet_codePast_codeSndFirstHit_eq (-k))
    · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_right hk0, ite_eq_right hk] using
        measurable_codeShift_toNat (codeFstFirstHit k)
          (measurableSet_codePast_codeFstFirstHit_eq k)



theorem boundaryCodeShift_law (k : ℤ) :
    iidCodeMeasure.map (boundaryCodeShift k) = iidCodeMeasure := by
  change iidCodeMeasure.map (fun ω => codeShift (boundaryCodeTime k ω) ω) = _
  by_cases hk0 : k = 0
  · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_left hk0] using map_codeShift 0
  · by_cases hk : 0 < k
    · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_right hk0, ite_eq_left hk] using
        map_codeShift_codeSndFirstHit (-k)
    · simpa only [boundaryCodeShift, boundaryCodeTime, ite_eq_right hk0, ite_eq_right hk] using
        map_codeShift_codeFstFirstHit k



theorem boundaryCodeTime_eq_boundaryHitTime (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) :
    boundaryCodeTime k ω = boundaryHitTime (fun i => ω (i + 1)) h k := by
  by_cases hk0 : k = 0
  · subst k
    simp only [boundaryCodeTime, ite_true, boundaryHitTime_zero]
  · by_cases hk : 0 < k
    · simp only [boundaryCodeTime, ite_eq_right hk0, ite_eq_left hk]
      rw [codeSndFirstHit_eq_boundaryHitTime ω h (by omega : 1 ≤ k)]
      rfl
    · simp only [boundaryCodeTime, ite_eq_right hk0, ite_eq_right hk]
      rw [codeFstFirstHit_eq_boundaryHitTime ω h (by omega : k ≤ -1)]
      rfl



@[expose] noncomputable def boundaryFutureCode (k : ℤ) (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  boundaryCodeShift k (shiftedCodePath W 0)



theorem measurable_boundaryFutureCode (k : ℤ) : Measurable (boundaryFutureCode k) :=
  (measurable_boundaryCodeShift k).comp (measurable_shiftedCodePath 0)



theorem boundaryFutureCode_law (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) = iidCodeMeasure := by
  change wholePlaneIIDCodeMeasure.map
    (boundaryCodeShift k ∘ (fun W => shiftedCodePath W 0)) = _
  rw [← Measure.map_map (measurable_boundaryCodeShift k) (measurable_shiftedCodePath 0),
    wholePlaneIIDCodeMeasure_map_shiftedPath, boundaryCodeShift_law]



theorem boundaryFutureCode_law_eq_zero (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
      wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) :=
  (boundaryFutureCode_law k).trans (boundaryFutureCode_law 0).symm



theorem shiftedCodePath_tail_eq (W : ℤ → Fin 3) :
    (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
  funext i
  simp [shiftedCodePath]



theorem boundaryFutureCode_tail (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :
    (fun i => boundaryFutureCode k W (i + 1)) =
      (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)) := by
  have hω : BoundaryHitWitnesses (fun i => shiftedCodePath W 0 (i + 1)) := by
    rw [shiftedCodePath_tail_eq]
    exact h
  have ht : boundaryCodeTime k (shiftedCodePath W 0) =
      boundaryHitTime (shiftedStream W 0) h k := by
    simpa only [shiftedCodePath_tail_eq] using
      boundaryCodeTime_eq_boundaryHitTime (shiftedCodePath W 0) hω k
  funext i
  simp only [boundaryFutureCode, boundaryCodeShift, codeShift,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
  rw [ht]
  simp [shiftedCodePath]





theorem boundaryFutureHatCode_law (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W => rCodeSequence (boundaryFutureCode k W)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
  change wholePlaneIIDCodeMeasure.map (rCodeSequence ∘ boundaryFutureCode k) = _
  rw [← Measure.map_map measurable_rCodeSequence (measurable_boundaryFutureCode k),
    boundaryFutureCode_law]
  exact map_rCodeSequence



theorem boundaryFutureHatCode_eq_hatCodes (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (hτ : HasFlowLineHits
      (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i))) :
    rCodeSequence (boundaryFutureCode k W) =
      hatCodes (fun i => shiftedStream W 0
        (boundaryHitTime (shiftedStream W 0) h k + i)) hτ := by
  rw [← rCodeSequence_quadrantTrajectory_eq_hatCodes _ hτ]
  apply rCodeSequence_eq_of_succ_eq
  intro i
  exact congrFun (boundaryFutureCode_tail W h k) i



theorem wholePlane_ae_hasFlowLineHits_all_future_times :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ t : ℕ,
      HasFlowLineHits (fun i => shiftedStream W 0 (t + i)) := by
  have hevent : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0),
      ∀ t : ℕ, HasFlowLineHits (fun i => ω (t + i + 1)) := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath]
    exact iidCodes_ae_hasFlowLineHits_all_future_times
  have h := (Measure.tendsto_ae_map (measurable_shiftedCodePath 0).aemeasurable).eventually
    hevent
  filter_upwards [h] with W hW
  intro t
  simpa [shiftedCodePath, Nat.add_assoc] using hW t




theorem hatLawCodes_ae_eq_rCodeSequence :
    hatLawCodes =ᵐ[iidCodeMeasure] rCodeSequence := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω hω
  simp only [hatLawCodes, dite_eq_left hω]
  rw [← rCodeSequence_quadrantTrajectory_eq_hatCodes _ hω]
  exact rCodeSequence_eq_of_succ_eq _ _ (fun _ => rfl)




theorem boundaryFuture_hatLawCodes_law (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
  have hm : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_hatLawCodes.1
  rw [← hm.map_map_of_aemeasurable (measurable_boundaryFutureCode k).aemeasurable,
    boundaryFutureCode_law, Measure.map_congr hatLawCodes_ae_eq_rCodeSequence]
  exact map_rCodeSequence




theorem boundaryFuture_hatLawCodes_eq_hatCodes (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (hτ : HasFlowLineHits
      (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i))) :
    hatLawCodes (boundaryFutureCode k W) =
      hatCodes (fun i => shiftedStream W 0
        (boundaryHitTime (shiftedStream W 0) h k + i)) hτ := by
  have hs : HasFlowLineHits (fun i => boundaryFutureCode k W (i + 1)) := by
    rw [boundaryFutureCode_tail W h k]
    exact hτ
  simp only [hatLawCodes, dite_eq_left hs]
  congr 1
  exact boundaryFutureCode_tail W h k






@[expose] def M0CutShiftContainment (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (k : ℤ) : Prop :=
  let w := shiftedStream W 0
  let V := wholePlaneVertexι W 0
  let E := wholePlaneEdgeι W 0
  let D := m0CutData W H h hLL
  (∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
    ∀ e : Fin n → WholePlaneEdge W,
    p 0 = D.x k →
    (∀ i, e i ∈ D.edges) → (∀ i, D.tail (e i, false)) →
    (∀ i, wholePlaneEdgeWest W (e i) = p i.castSucc) →
    (∀ i, wholePlaneEdgeEast W (e i) = p i.succ) →
    ∃ m, ∃ z : StagePresentVertex (fun i => w (boundaryHitTime w h k + i)) m,
      ∃ q : Path (⟨0⟩ : StagePresentVertex
        (fun i => w (boundaryHitTime w h k + i)) m) z,
        V ((kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj ⟨0⟩).id =
          D.x k ∧
        V ((kmswShiftStageToLimit w (boundaryHitTime w h k) m).obj z).id =
          p (Fin.last n) ∧
        (pathEdgeList ((kmswShiftStageToLimit w
          (boundaryHitTime w h k) m).mapPath q)).map E = List.ofFn e ∧
        q.length = n) ∧
  (∀ P : M0CutInfinitePath W H D (D.x k),
    ∃ Q : InfinitePresentPath (fun i => w (boundaryHitTime w h k + i)) ⟨0⟩,
      ∀ n, E (shiftLimitEdge w (boundaryHitTime w h k)
        ⟨Q.edge n, (Q.edge_outgoing_at_initial _ n).1⟩) = P.edge n)



theorem m0Cut_shiftContainment (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (k : ℤ) :
    M0CutShiftContainment W H h hLL k :=
  ⟨m0Cut_finitePath_lifts_to_shifted_stage W H h hLL k,
    m0Cut_infinitePath_lifts_to_shifted_limit W H h hLL k⟩




theorem m0Cut_shiftContainment_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∀ k : ℤ, M0CutShiftContainment W H h hLL k := by
  filter_upwards [m0Cut_identification_ae] with W hW
  obtain ⟨H, h, hLL, _⟩ := hW
  exact ⟨H, h, hLL, m0Cut_shiftContainment W H h hLL⟩










@[expose] def lemma52Statement : Prop :=
  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    ∃ H : WholePlaneRotationHypothesis W,
    ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
    ∀ k : ℤ,
      wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
        wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
      wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
        iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
      (fun i => boundaryFutureCode k W (i + 1)) =
        (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)) ∧
      (∃ hτ : HasFlowLineHits
          (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)),
        hatLawCodes (boundaryFutureCode k W) =
          hatCodes (fun i => shiftedStream W 0
            (boundaryHitTime (shiftedStream W 0) h k + i)) hτ) ∧
      M0CutShiftContainment W H h hLL k



theorem lemma52_code_and_path_statement : lemma52Statement := by
  unfold lemma52Statement
  filter_upwards [m0Cut_shiftContainment_ae,
    wholePlane_ae_hasFlowLineHits_all_future_times] with W hc hf
  obtain ⟨H, h, hLL, hc⟩ := hc
  refine ⟨H, h, hLL, fun k => ?_⟩
  exact ⟨boundaryFutureCode_law_eq_zero k, boundaryFuture_hatLawCodes_law k,
    boundaryFutureCode_tail W h k,
    ⟨hf (boundaryHitTime (shiftedStream W 0) h k),
      boundaryFuture_hatLawCodes_eq_hatCodes W h k
        (hf (boundaryHitTime (shiftedStream W 0) h k))⟩, hc k⟩

end DirectedDistances.PaperProofs.Section5
