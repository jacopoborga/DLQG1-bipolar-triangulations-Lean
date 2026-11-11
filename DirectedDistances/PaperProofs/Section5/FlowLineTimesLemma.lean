module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimesSource
public import DirectedDistances.KMSW.Beta0BoundarySuccessor
public import DirectedDistances.KMSW.PrimedRotInducedOriented
















































































public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open Quiver

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Joint source membership and coordinate minima, including the initial value -/
@[expose] def FlowLineTimesJointMinima (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Prop :=
  sourceFlowNR w h 0 = 0 ∧
    (∀ k, IsLeast
      {n | sourceFlowLeftCandidate w (sourceFlowNR w h k) n}
      (sourceFlowNL w h k)) ∧
    (∀ k, IsLeast
      {n | sourceFlowRightCandidate w (sourceFlowNL w h k) n}
      (sourceFlowNR w h (k + 1))) ∧
    (∀ k, IsLeast
      {n | sourceFlowNR w h k + 1 ≤ n ∧
        L w n = L w (sourceFlowNR w h k) - 1}
      (sourceFlowNL w h k)) ∧
    (∀ k, IsLeast
      {n | sourceFlowNL w h k + 1 ≤ n ∧
        R w n = R w (sourceFlowNL w h k) - 1}
      (sourceFlowNR w h (k + 1)))

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Item (i), preserving both allocation cases of the new present active edge -/
@[expose] def FlowLineTimesItemI (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    let r := sourceFlowNR w h (k - 1)
    let s := kmswStage w (r - 1)
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w r).west (act w r)⟩ ∧
      (L w r - L w (r - 1), R w r - R w (r - 1)) = (1, -1) ∧
      (kmswStage w r).triangles = s.triangles ∧
      ((s.UR = [] ∧
          (kmswStage w r).nextEdge = s.nextEdge + 1 ∧
          (kmswStage w r).nextVertex = s.nextVertex + 1 ∧
          act w r = s.nextEdge ∧
          (kmswStage w r).west (act w r) = s.east s.active ∧
          (kmswStage w r).east (act w r) = s.nextVertex ∧
          (kmswStage w r).present (act w r) = true) ∨
        ∃ e es, s.UR = e :: es ∧ s.present e = false ∧
          (kmswStage w r).nextEdge = s.nextEdge ∧
          act w r = e ∧
          (kmswStage w r).west e = s.east s.active ∧
          (kmswStage w r).east e = s.east e ∧
          (kmswStage w r).present e = true)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Item (ii) except actual primed-map face containment, for every source `k ≥ 1`,
with one shared triangle witness and the initial triangle convention first-case endpoints. The old
active edge belongs to the actual ordered β₀ stream -/
@[expose] def FlowLineTimesItemII (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      ∃ e,
        (kmswStage w t).triangles =
          s.triangles ++ [(act w (t - 1), act w t, e)] ∧
        act w t = s.nextEdge ∧
        (kmswStage w t).present (act w t) = true ∧
        ¬ Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).west (act w t)⟩ ∧
        sourceFlowMhatInterfaceEdge w t (act w (t - 1)) ∧
        ((k = 1 ∧ e = s.nextEdge + 1 ∧
            (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
            s.nextEdge ≤ e ∧ e < (kmswStage w t).nextEdge ∧
            (kmswStage w t).present e = false ∧
            ({(kmswStage w t).west e, (kmswStage w t).east e} : Set ℕ) =
              {(kmswStage w t).west (act w t), s.west (act w (t - 1))}) ∨
          (2 ≤ k ∧ e = act w (r - 1))) ∧
        ∃ j : ℕ, (kmswBeta0Stream w hfin hb j).1 = act w (t - 1)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The initial triangle convention first missing geometric edge remains in LL forever and never belongs -/
@[expose] def FlowLineTimesFirstMissingPersistence (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Prop :=
  let t := sourceFlowNL w h 0
  let s := kmswStage w (t - 1)
  let e := s.nextEdge + 1
  s.LL = [] ∧ (kmswStage w t).LL = [e] ∧
    (∀ n, t ≤ n → e ∈ (kmswStage w n).LL ∧
      (kmswStage w n).present e = false) ∧
    ¬ EdgePresent w e

/- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
bound an internal face of an oriented primed plane stage, whose image has
exactly the three corrected geometric edge IDs, with multiplicities retained.
This is not defined as mere global non-reachability. The independent
identification of the primed construction with the actual source submap is
also required before any paper-result claim; it is not proved here. -/
@[expose] def FlowLineTimesPrimedFaceContainment (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
    ∃ (m : ℕ) (hm : 1 ≤ m)
      (d₁ d₂ d₃ :
        StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge),
      FaceSucc3Cycle (primedRootedStage w h m hm).map.toCombinatorialMap.faceSucc
        d₁ d₂ d₃ ∧
      ¬ (primedRootedStage w h m hm).map.IsOuter d₁ ∧
      ({(primedDartMapOriented w h m d₁).1.val,
        (primedDartMapOriented w h m d₂).1.val,
        (primedDartMapOriented w h m d₃).1.val} : Multiset ℕ) =
        {act w (t - 1), act w t, e}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Combine the proved item (ii) geometry with actual β₀-stream membership, -/
theorem flow_line_times_lemma_item_ii (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    FlowLineTimesItemII w hfin hb h := by
  intro k hk
  obtain ⟨hstep, e, htri, hact, hpresent, hnot, hinter, hcases⟩ :=
    flow_line_times_source_item_ii_geometry w h k hk
  exact ⟨hstep, e, htri, hact, hpresent, hnot, hinter, hcases,
    flow_line_times_source_left_exit_mem_beta0 w hfin hb h k hk⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Joint unconditional local content on the providers' deterministic domains:
minima, all of (i), (ii) except primed-face containment, and initial triangle convention persistence -/
theorem flow_line_times_lemma_local (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    FlowLineTimesJointMinima w h ∧
      FlowLineTimesItemI w h ∧
      FlowLineTimesItemII w hfin hb h ∧
      FlowLineTimesFirstMissingPersistence w h := by
  exact ⟨flow_line_times_source_minima w h,
    flow_line_times_source_item_i w h,
    flow_line_times_lemma_item_ii w hfin hb h,
    flow_line_times_source_first_missing_persistent w h⟩

/- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Actual cut-completed primed-map identification is still required separately. -/
theorem flow_line_times_lemma_conditional (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w)
    (hprime : FlowLineTimesPrimedFaceContainment w h) :
    (FlowLineTimesJointMinima w h ∧
      FlowLineTimesItemI w h ∧
      FlowLineTimesItemII w hfin hb h ∧
      FlowLineTimesFirstMissingPersistence w h) ∧
      FlowLineTimesPrimedFaceContainment w h := by
  exact ⟨flow_line_times_lemma_local w hfin hb h, hprime⟩

end DirectedDistances.PaperProofs.Section5
