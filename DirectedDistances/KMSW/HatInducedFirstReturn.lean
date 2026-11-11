module

public import DirectedDistances.KMSW.HatInducedFinal
public import DirectedDistances.KMSW.InfiniteRotation

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

private theorem limitEdge_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitEdgeMap w h) := by
  intro e f hef
  let m := max e f
  exact ((hatLimitExplicitInput w h).stage_sim m).edge_injective e f
    (kmsw_nextEdge_unbounded (hatCodes w h) e m (Nat.le_max_left e f))
    (kmsw_nextEdge_unbounded (hatCodes w h) f m (Nat.le_max_right e f)) hef






theorem hatCodes_inducedFiniteIncidence (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ∀ v, {e : ℕ | ∃ n, e < (kmswStage (hatCodes w h) n).nextEdge ∧
      ((kmswStage (hatCodes w h) n).west e = v ∨
        (kmswStage (hatCodes w h) n).east e = v)}.Finite := by
  intro v
  apply Set.Finite.of_injOn (f := hatLimitEdgeMap w h) ?_
    (fun _ _ _ _ hef => limitEdge_injective w h hef)
    (hfinW (hatLimitVertexMap w h v))
  rintro e ⟨n, he, hv⟩
  have D := (hatLimitExplicitInput w h).stage_sim n
  refine ⟨quadrantRStageTime w h n, D.edge_bound e he, ?_⟩
  rcases hv with hv | hv
  · exact Or.inl ((D.incidence e he).1.trans (congrArg _ hv))
  · exact Or.inr ((D.incidence e he).2.trans (congrArg _ hv))





theorem hatLimitDart_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (fun d : ℕ × Bool => (hatLimitEdgeMap w h d.1, d.2)) := by
  intro d e he
  have hb := congrArg (fun z : ℕ × Bool => z.2) he
  exact Prod.ext (limitEdge_injective w h (congrArg Prod.fst he)) hb

private def dartValue {k : ℕ} (d : StageDart k) : ℕ × Bool := (d.1.val, d.2)

private theorem dartValue_injective (k : ℕ) :
    Function.Injective (@dartValue k) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ he
  obtain ⟨hv, hb⟩ := Prod.mk.inj he
  exact Prod.ext (Fin.ext hv) hb

private def endpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem stageEndpoint_eq (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d = endpoint w (dartValue d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, endpoint, dartValue, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem hat_endpoint (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    endpoint w (hatLimitEdgeMap w h d.1, d.2) =
      hatLimitVertexMap w h (endpoint (hatCodes w h) d) := by
  have he := kmsw_edge_allocated_by_self (hatCodes w h) d.1
  have D := (hatLimitExplicitInput w h).stage_sim d.1
  have hW := edge_endpoints_eq w (D.edge_bound d.1 he)
  have hU := edge_endpoints_eq (hatCodes w h) he
  have hi := D.incidence d.1 he
  cases hb : d.2
  · simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte, ← hW.1, ← hU.1]
      using hi.1
  · simpa only [endpoint, hb, ↓reduceIte, ← hW.2, ← hU.2] using hi.2

private theorem endpoint_allocated (w : ℕ → Fin 3) (d : ℕ × Bool) :
    ∃ n, endpoint w d < (kmswStage w n).nextVertex := by
  refine ⟨d.1, ?_⟩
  have hb := kmswStage_endpoints_lt_nextVertex w d.1 d.1
    (kmsw_edge_allocated_by_self w d.1)
  cases hd : d.2
  · simpa only [endpoint, hd, Bool.false_eq_true, ↓reduceIte, edgeWest] using hb.1
  · simpa only [endpoint, hd, ↓reduceIte, edgeEast] using hb.2

private theorem hat_endpoint_reflect (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d e : ℕ × Bool)
    (he : endpoint w (hatLimitEdgeMap w h d.1, d.2) =
      endpoint w (hatLimitEdgeMap w h e.1, e.2)) :
    endpoint (hatCodes w h) d = endpoint (hatCodes w h) e := by
  rw [hat_endpoint, hat_endpoint] at he
  exact vertex_inj (hatLimitExplicitInput w h)
    (endpoint_allocated _ d) (endpoint_allocated _ e) he

private theorem complete_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) : ∃ n, kmswVertexComplete w n v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem complete_mono' (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete w n v) : kmswVertexComplete w m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem rot_endpoint' (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) (stageRot w n d) =
      stageEndpoint (kmswStage w n) d :=
  ((stageRot_sameCycle_iff_endpoint_eq w n d (stageRot w n d)).1 ⟨1, rfl⟩).symm

private theorem iterate_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w n) ((stageRot w n : _ → _)^[k] d) =
      stageEndpoint (kmswStage w n) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', rot_endpoint', ih]

private theorem inf_iterate_eq_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) (k : ℕ) :
    (kmswInfRot w hfin : _ → _)^[k] (dartValue d) =
      dartValue ((stageRot w n : _ → _)^[k] d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact kmswInfRot_eq_stage w hfin n _ (by rw [iterate_endpoint]; exact hc)






theorem hatInfRot_firstReturn (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    let I : (ℕ × Bool) → ℕ × Bool := fun e => (hatLimitEdgeMap w h e.1, e.2)
    ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfinW : _ → _)^[k] (I d) =
        I (kmswInfRot (hatCodes w h) (hatCodes_inducedFiniteIncidence w h hfinW) d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswInfRot w hfinW : _ → _)^[j] (I d) ∉ Set.range I := by
  let u := hatCodes w h
  let I : (ℕ × Bool) → ℕ × Bool := fun e => (hatLimitEdgeMap w h e.1, e.2)
  let hfinU := hatCodes_inducedFiniteIncidence w h hfinW
  obtain ⟨Ns, hNs⟩ := complete_exists u hfinU (endpoint u d)
  obtain ⟨Nw, hNw⟩ := complete_exists w hfinW (endpoint w (I d))
  obtain ⟨M, hM⟩ := quadrantRStageTime_unbounded w h Nw
  let m := max Ns (max M d.1)
  have hsm : Ns ≤ m := Nat.le_max_left _ _
  have hMm : M ≤ m := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdm : d.1 ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcs := complete_mono' u hsm hNs
  have hcw := complete_mono' w
    (hM.trans (quadrantRStageTime_mono w h hMm)) hNw
  have hd := kmsw_nextEdge_unbounded u d.1 m hdm
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := hatDartMap w h m x
  have hmap (z : StageDart (kmswStage u m).nextEdge) :
      dartValue (hatDartMap w h m z) = I (dartValue z) := by
    change (hatAllEdgeMap w h m z.1.val, z.2) = (hatLimitEdgeMap w h z.1.val, z.2)
    rw [hatLimitEdgeMap_eq_stage w h m z.1.val z.1.isLt]
  have hy : dartValue y = I d := hmap x
  have hcx : kmswVertexComplete u m (stageEndpoint (kmswStage u m) x) := by
    rw [stageEndpoint_eq]
    exact hcs
  have hcy : kmswVertexComplete w (quadrantRStageTime w h m)
      (stageEndpoint (kmswStage w (quadrantRStageTime w h m)) y) := by
    rw [stageEndpoint_eq, hy]
    exact hcw
  have hiter (j : ℕ) :
      (kmswInfRot w hfinW : _ → _)^[j] (I d) =
        dartValue ((stageRot w (quadrantRStageTime w h m) : _ → _)^[j] y) := by
    rw [← hy]
    exact inf_iterate_eq_stage w hfinW _ y hcy j
  obtain ⟨k, hk, hreturn, hgap⟩ := hatRotInduced_all w h m x
  change (stageRot w (quadrantRStageTime w h m) : _ → _)^[k] y =
    hatDartMap w h m (stageRot u m x) at hreturn
  refine ⟨k, hk, ?_, ?_⟩
  · calc
      (kmswInfRot w hfinW : _ → _)^[k] (I d) =
          dartValue ((stageRot w (quadrantRStageTime w h m) : _ → _)^[k] y) :=
        hiter k
      _ = dartValue (hatDartMap w h m (stageRot u m x)) := congrArg dartValue hreturn
      _ = I (dartValue (stageRot u m x)) := hmap _
      _ = I (kmswInfRot u hfinU d) :=
        congrArg I (kmswInfRot_eq_stage u hfinU m x hcx).symm
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    have hep : endpoint w (I e) = endpoint w (I d) := by
      calc
        endpoint w (I e) = endpoint w
            (dartValue ((stageRot w (quadrantRStageTime w h m) : _ → _)^[j] y)) :=
          congrArg (endpoint w) (he.trans (hiter j))
        _ = endpoint w (dartValue y) := by
          rw [← stageEndpoint_eq, ← stageEndpoint_eq, iterate_endpoint]
        _ = endpoint w (I d) := congrArg (endpoint w) hy
    have heLocal := hat_endpoint_reflect w h e d hep
    have heb : e.1 < (kmswStage u m).nextEdge := by
      apply hcs e.1
      cases hb : e.2
      · exact Or.inl (by
          simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using heLocal)
      · exact Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using heLocal)
    let z : StageDart (kmswStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, dartValue_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))

end DirectedDistances.KMSW
