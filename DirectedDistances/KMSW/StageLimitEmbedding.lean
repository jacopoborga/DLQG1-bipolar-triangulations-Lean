module

public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.KMSW.StageInfiniteOutgoingOrder
import DirectedDistances.KMSW.HatInducedExit












public section
namespace DirectedDistances.KMSW

open Quiver
open scoped Classical




@[expose] def stageLimitDart (w : ℕ → Fin 3) (n : ℕ) :
    StageDart (kmswStage w n).nextEdge ↪ ℕ × Bool where
  toFun d := (d.1.val, d.2)
  inj' := by
    intro d e h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (congrArg (fun z : ℕ × Bool => z.2) h)




@[expose] def stagePresentInclusion (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w m) where
  obj v := ⟨v.id⟩
  map {_ _} e :=
    ⟨e.val, (present_mono w e.property.1 e.property.2.1 m hnm).1,
      (present_mono w e.property.1 e.property.2.1 m hnm).2,
      ((kmswStage_endpoints_stable w hnm e.property.1).1).trans e.property.2.2.1,
      ((kmswStage_endpoints_stable w hnm e.property.1).2).trans e.property.2.2.2⟩




theorem kmswStage_limit_incidence (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).IsPlanar ∧
      (∀ e : Fin (kmswStage w n).nextEdge,
        (kmswStage w n).west e.val = edgeWest w e.val ∧
          (kmswStage w n).east e.val = edgeEast w e.val) ∧
      (∀ d : StageDart (kmswStage w n).nextEdge,
        stageLimitDart w n ((kmswMap w n).edgeInv d) =
          ((stageLimitDart w n d).1, !(stageLimitDart w n d).2)) ∧
      (∀ e : Fin (kmswStage w n).nextEdge,
        (kmswStage w n).present e.val = true →
        EdgePresent w e.val ∧ ∀ m, n ≤ m →
          e.val < (kmswStage w m).nextEdge ∧ (kmswStage w m).present e.val = true) := by
  refine ⟨kmswMap_isPlanar w n, fun e => edge_endpoints_eq w e.isLt,
    fun _ => rfl, ?_⟩
  intro e hp
  exact ⟨EdgePresent.of_stage_present e.isLt hp, present_mono w e.isLt hp⟩




theorem kmswEdgePresent_stage_limit (w : ℕ → Fin 3) (e : ℕ) :
    (EdgePresent w e ↔ ∃ N, ∀ n, N ≤ n →
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) ∧
      (∃ N, ∀ n, N ≤ n → e < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present e = decide (EdgePresent w e)) := by
  constructor
  · exact ⟨fun hp => hp.eventually_present, fun ⟨N, hN⟩ => ⟨N, hN N le_rfl⟩⟩
  · by_cases hp : EdgePresent w e
    · obtain ⟨N, hN⟩ := hp.eventually_present
      refine ⟨N, fun n hn => ?_⟩
      simpa only [hp, decide_true] using hN n hn
    · refine ⟨e, fun n hn => ⟨kmsw_nextEdge_unbounded w e n hn, ?_⟩⟩
      have hfalse : (kmswStage w n).present e = false := by
        cases heq : (kmswStage w n).present e with
        | false => rfl
        | true => exact (hp ⟨n, kmsw_nextEdge_unbounded w e n hn, heq⟩).elim
      simpa only [hp, decide_false] using hfalse




theorem kmswStage_limit_rotation (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) :
    kmswInfRot w hfin (stageLimitDart w n d) =
        stageLimitDart w n ((kmswMap w n).rot d) ∧
      (kmswInfRot w hfin).symm (stageLimitDart w n d) =
        stageLimitDart w n ((kmswMap w n).rot.symm d) :=
  ⟨kmswInfRot_eq_stage w hfin n d hc, kmswInfRot_symm_eq_stage w hfin n d hc⟩





theorem kmswStage_limit_firstReturn (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    (∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfin ^ k) (stageLimitDart w n d) =
        stageLimitDart w n ((kmswMap w n).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswStage w n).nextEdge ≤
          ((kmswInfRot w hfin ^ j) (stageLimitDart w n d)).1) ∧
    (∃ k : ℕ, 0 < k ∧
      ((kmswInfRot w hfin).symm ^ k) (stageLimitDart w n d) =
        stageLimitDart w n ((kmswMap w n).rot.symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswStage w n).nextEdge ≤
          (((kmswInfRot w hfin).symm ^ j) (stageLimitDart w n d)).1) :=
  ⟨kmswInfRot_firstReturn_stage w hfin n d,
    kmswInfRot_symm_firstReturn_stage w hfin n d⟩





theorem kmswStage_inclusion_compatible (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m) :
    Function.Injective (outerSucc_castDart (kmswStage_nextEdge_mono w hnm)) ∧
      (∀ d : StageDart (kmswStage w n).nextEdge,
        stageLimitDart w m (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d) =
            stageLimitDart w n d ∧
          stageEndpoint (kmswStage w m)
              (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d) =
            stageEndpoint (kmswStage w n) d ∧
          outerSucc_castDart (kmswStage_nextEdge_mono w hnm) ((kmswMap w n).edgeInv d) =
            (kmswMap w m).edgeInv
              (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d)) ∧
      (∀ d : StageDart (kmswStage w n).nextEdge, ∃ k : ℕ, 0 < k ∧
        (stageRot w m : _ → _)^[k]
            (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d) =
          outerSucc_castDart (kmswStage_nextEdge_mono w hnm) (stageRot w n d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (stageRot w m : _ → _)^[j]
              (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d) ∉
            Set.range (outerSucc_castDart (kmswStage_nextEdge_mono w hnm))) ∧
      (stagePresentInclusion w hnm).comp (stageToLimit w m) = stageToLimit w n ∧
      Function.Injective (stagePresentInclusion w hnm).obj ∧
      (∀ a b : StagePresentVertex w n,
        Function.Injective (fun e : a ⟶ b => (stagePresentInclusion w hnm).map e)) := by
  refine ⟨?_, ?_, hatExit_ambient_rotation_induced w n m hnm, rfl, ?_, ?_⟩
  · intro d e he
    apply (stageLimitDart w n).injective
    exact congrArg (stageLimitDart w m) he
  · intro d
    refine ⟨rfl, ?_, rfl⟩
    obtain ⟨hw, he⟩ := kmswStage_endpoints_stable w hnm d.1.isLt
    cases hb : d.2 <;>
      simp only [stageEndpoint, outerSucc_castDart, Fin.val_castLE, hb,
        Bool.false_eq_true, ↓reduceIte, hw, he]
  · intro a b he
    cases a
    cases b
    congr 1
    exact congrArg (fun v : StagePresentVertex w m => v.id) he
  · intro a b e f he
    apply Subtype.ext
    exact congrArg (fun g : (stagePresentInclusion w hnm).obj a ⟶
      (stagePresentInclusion w hnm).obj b => g.val) he

private theorem vertex_complete_later (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete w n v) : kmswVertexComplete w m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem vertex_complete_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) : ∃ N, kmswVertexComplete w N v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem finite_darts_complete (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (s : Set (ℕ × Bool)) (hs : s.Finite) :
    ∃ N, ∀ d ∈ s, kmswVertexComplete w N (edgeWest w d.1) ∧
      kmswVertexComplete w N (edgeEast w d.1) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, fun _ hd => hd.elim⟩
  | @insert d s _ _ ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨A, hA⟩ := vertex_complete_exists w hfin (edgeWest w d.1)
    obtain ⟨B, hB⟩ := vertex_complete_exists w hfin (edgeEast w d.1)
    refine ⟨max N (max A B), fun e he => ?_⟩
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ⟨vertex_complete_later w (le_trans (le_max_left _ _) (le_max_right _ _)) hA,
        vertex_complete_later w (le_trans (le_max_right _ _) (le_max_right _ _)) hB⟩
    · exact ⟨vertex_complete_later w (le_max_left _ _) (hN e he).1,
        vertex_complete_later w (le_max_left _ _) (hN e he).2⟩





theorem kmswLimit_finite_darts_complete (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (s : Set (ℕ × Bool)) (hs : s.Finite) :
    ∃ N, ∀ n, N ≤ n → ∀ d ∈ s,
      ∃ hd : d.1 < (kmswStage w n).nextEdge,
        kmswVertexComplete w n (edgeWest w d.1) ∧
        kmswVertexComplete w n (edgeEast w d.1) ∧
        kmswInfRot w hfin d =
          stageLimitDart w n ((kmswMap w n).rot (⟨d.1, hd⟩, d.2)) ∧
        kmswInfFaceSucc w hfin d =
          stageLimitDart w n ((kmswMap w n).faceSucc (⟨d.1, hd⟩, d.2)) := by
  obtain ⟨N, hN⟩ := finite_darts_complete w hfin s hs
  refine ⟨N, fun n hn d hd => ?_⟩
  have hw := vertex_complete_later w hn (hN d hd).1
  have he := vertex_complete_later w hn (hN d hd).2
  have hb : d.1 < (kmswStage w n).nextEdge := hw d.1 (Or.inl rfl)
  refine ⟨hb, hw, he, kmswInfRot_eq_stage w hfin n (⟨d.1, hb⟩, d.2) ?_,
    kmswInfFaceSucc_eq_stage w hfin n (⟨d.1, hb⟩, d.2) ?_⟩
  · obtain ⟨hwest, heast⟩ := edge_endpoints_eq w hb
    cases d.2 <;>
      simp only [stageEndpoint, Bool.false_eq_true, ↓reduceIte]
    · rw [hwest]
      exact hw
    · rw [heast]
      exact he
  · obtain ⟨hwest, heast⟩ := edge_endpoints_eq w hb
    cases d.2 <;>
      simp only [stageEndpoint, edgeFlip_apply, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
    · rw [heast]
      exact he
    · rw [hwest]
      exact hw

end DirectedDistances.KMSW
