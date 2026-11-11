module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimesLemma
public import DirectedDistances.KMSW.InfiniteTriangulation
public import DirectedDistances.KMSW.LimitExternalFace
public import DirectedDistances.KMSW.StageBoundaryMap
import DirectedDistances.KMSW.CutVertexConverse

/-! # Formal limiting-successor triangles

Helpers toward Lemma 5.12 (`lem-flow-line-times`), with source semantics -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section5
open Quiver

/-- Vertices reachable from the root in the present directed graph
(lem-flow-line-times); not a paper result. -/
@[expose] def MhatVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩

/-- Geometric edge IDs whose two endpoints lie in the reachable submap
(lem-flow-line-times); not a paper result. -/
@[expose] def MhatGeometricEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  MhatVertex w (edgeWest w e) ∧ MhatVertex w (edgeEast w e)

/- Formal 3-cycle of the limit face successor with the specified edge-ID
multiset, an unreachable boundary vertex, and no eventually-outer dart.
Identification with faces of the source map `\widehat M'_{0,\infty}` is open -/
@[expose] def MhatPrimeTriangleFace (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (E : Multiset ℕ) : Prop :=
  ∃ d₁ d₂ d₃ : ℕ × Bool,
    FaceSucc3Cycle (kmswInfFaceSucc w hfin) d₁ d₂ d₃ ∧
    ({d₁.1, d₂.1, d₃.1} : Multiset ℕ) = E ∧
    ¬ (MhatVertex w (kmswDartEndpoint w d₁) ∧
      MhatVertex w (kmswDartEndpoint w d₂) ∧
      MhatVertex w (kmswDartEndpoint w d₃)) ∧
    ¬ limitExternalDart w d₁ ∧
      ¬ limitExternalDart w d₂ ∧ ¬ limitExternalDart w d₃

private theorem stageOuterWord_mem_of_isOuter (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (kmswStageDirectedMap w n).IsOuter d) : d ∈ stageOuterWord w n := by
  have hclass := kmswStage_outer_dart_exactly_one w n d hd
  rcases hclass with hUL | hUR | hLR | hLL
  · obtain ⟨hb, he⟩ := (kmswStageULDartsFinset_mem w n d).1 hUL.1
    exact (stageOuterWord_mem_iff w n d).2 (Or.inl ⟨hb, Or.inl he⟩)
  · obtain ⟨hb, he⟩ := (kmswStageURDartsFinset_mem w n d).1 hUR.1
    exact (stageOuterWord_mem_iff w n d).2 (Or.inl ⟨hb, Or.inr he⟩)
  · obtain ⟨hb, he⟩ := (kmswStageLRDartsFinset_mem w n d).1 hLR.1
    exact (stageOuterWord_mem_iff w n d).2 (Or.inr ⟨hb, Or.inl he⟩)
  · obtain ⟨hb, he⟩ := (kmswStageLLDartsFinset_mem w n d).1 hLL.1
    exact (stageOuterWord_mem_iff w n d).2 (Or.inr ⟨hb, Or.inr he⟩)

/-- Each dart of a recorded triangle is not an eventual external dart. Helper
toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem stageTriangleDart_not_limitExternal (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) : ¬ limitExternalDart w d := by
  intro hext
  obtain ⟨N, hN⟩ := hext
  let n := max N (j.val + 1)
  have hj : j.val < n := by dsimp [n]; omega
  obtain ⟨hbound, houter⟩ := hN n (le_max_left _ _)
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hbound⟩, d.2)
  have hmem : (x.1.val, x.2) ∈ stageTriangleDartList w j := by
    simpa [x] using hd
  have hnot := stageTriangleDart_not_outer w n j hj x hmem
  exact hnot (stageOuterWord_mem_of_isOuter w n x houter)

private theorem kmswInfFaceSucc_endpoint_eq_flip (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    kmswDartEndpoint w (kmswInfFaceSucc w hfin d) =
      if d.2 then edgeWest w d.1 else edgeEast w d.1 := by
  have h := (kmswInfRot_endpoint_eq w hfin
    ((kmswInfRot w hfin).symm (d.1, !d.2))).symm
  cases hb : d.2 <;>
    simpa [kmswInfFaceSucc, Equiv.Perm.mul_apply, kmswDartEndpoint, hb] using h

private theorem edgeWest_eq_faceCycleEndpoint (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d₁ d₂ d₃ : ℕ × Bool)
    (hcyc : FaceSucc3Cycle (kmswInfFaceSucc w hfin) d₁ d₂ d₃)
    (e : ℕ) (he : e = d₁.1 ∨ e = d₂.1 ∨ e = d₃.1) :
    edgeWest w e = kmswDartEndpoint w d₁ ∨
      edgeWest w e = kmswDartEndpoint w d₂ ∨
      edgeWest w e = kmswDartEndpoint w d₃ := by
  rcases he with he | he | he
  · subst e
    cases hb : d₁.2
    · exact Or.inl (by simp [kmswDartEndpoint, hb])
    · have hh := kmswInfFaceSucc_endpoint_eq_flip w hfin d₁
      rw [hb] at hh
      rw [hcyc.1] at hh
      exact Or.inr (Or.inl (by simpa [kmswDartEndpoint, hb] using hh.symm))
  · subst e
    cases hb : d₂.2
    · exact Or.inr (Or.inl (by simp [kmswDartEndpoint, hb]))
    · have hh := kmswInfFaceSucc_endpoint_eq_flip w hfin d₂
      rw [hb] at hh
      rw [hcyc.2.1] at hh
      exact Or.inr (Or.inr (by simpa [kmswDartEndpoint, hb] using hh.symm))
  · subst e
    cases hb : d₃.2
    · exact Or.inr (Or.inr (by simp [kmswDartEndpoint, hb]))
    · have hh := kmswInfFaceSucc_endpoint_eq_flip w hfin d₃
      rw [hb] at hh
      rw [hcyc.2.2.1] at hh
      exact Or.inl (by simpa [kmswDartEndpoint, hb] using hh.symm)

private theorem stageTriangleDartTriple_edges_eq_record (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    ({(stageTriangleDartTriple w j).1.1,
      (stageTriangleDartTriple w j).2.1.1,
      (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
      {(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
        (stageTriangleRecord w j).2.2} := by
  rcases j.property with h0 | h1
  · by_cases hl : (kmswStage w j.val).UL.dropLast.reverse = []
    · simp [stageTriangleDartTriple, stageTriangleRecord, h0, hl]
    · cases hl' : (kmswStage w j.val).UL.dropLast.reverse with
      | nil => exact (hl hl').elim
      | cons e es =>
        simp only [stageTriangleDartTriple, stageTriangleRecord, h0, hl', ↓reduceIte]
        simp only [Multiset.insert_eq_cons]
        rw [Multiset.cons_swap e (kmswStage w j.val).active
          {(kmswStage w j.val).nextEdge}]
        congr 1
        exact Multiset.pair_comm _ _
  · simp [stageTriangleDartTriple, stageTriangleRecord, h1]
    exact Multiset.pair_comm _ _

/- Produces the formal limiting-successor cycle predicate for each flow-line -/
theorem flowLineTimes_mhatPrimeFace (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    ∀ k, 1 ≤ k →
      let r := sourceFlowNR w h (k - 1)
      let t := sourceFlowNL w h (k - 1)
      let s := kmswStage w (t - 1)
      let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
      MhatPrimeTriangleFace w hfin
        {act w (t - 1), act w t, e} := by
  intro k hk
  let r := sourceFlowNR w h (k - 1)
  let t := sourceFlowNL w h (k - 1)
  let s := kmswStage w (t - 1)
  dsimp only [r, t, s]
  obtain ⟨_, e, htri, hact, _, hnot, _, hcases⟩ :=
    flow_line_times_source_item_ii_geometry w h k hk
  have he : e = if k = 1 then s.nextEdge + 1 else act w (r - 1) := by
    rcases hcases with ⟨hk1, he, _, _, _, _, _⟩ | ⟨hk2, he⟩
    · simpa [s, r, t, hk1] using he
    · have hkne : k ≠ 1 := by omega
      simpa [s, r, t, hkne] using he
  have htpos : 0 < t := by
    dsimp [t]
    rw [sourceFlowNL_eq_walkNL]
    have hspec := walkNL_spec w h (k - 1)
    omega
  have hjcode : w (t - 1) = 0 := by
    dsimp [t]
    rw [sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code w h (k - 1)
  let j : TriangleCreationTime w := ⟨t - 1, Or.inl hjcode⟩
  have hjtime : t - 1 + 1 = t := by omega
  have htriLocal : (kmswStage w t).triangles =
      (kmswStage w (t - 1)).triangles ++
        [(act w (t - 1), act w t, e)] := by simpa [r, t, s] using htri
  have htriStep : (kmswStep s (w (t - 1))).triangles =
      s.triangles ++ [(act w (t - 1), act w t, e)] := by
    rw [← hjtime] at htriLocal
    change (kmswStep s (w (t - 1))).triangles =
      s.triangles ++ [(act w (t - 1), act w (t - 1 + 1), e)] at htriLocal
    simpa [hjtime] using htriLocal
  have hrecord : stageTriangleRecord w j = (act w (t - 1), act w t, e) := by
    rcases hl : s.UL.dropLast.reverse with _ | ⟨a, as⟩
    · have hleft := htriStep
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hjcode, s, hl, act] at hleft
      simp [stageTriangleRecord, j, s, hjcode, hl, act]
      omega
    · have hleft := htriStep
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hjcode, s, hl, act] at hleft
      simp [stageTriangleRecord, j, s, hjcode, hl, act]
      omega
  let d := stageTriangleDartTriple w j
  have hcycle := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hids' :
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
      {act w (t - 1), act w t, if k = 1 then s.nextEdge + 1 else act w (r - 1)} := by
    rw [stageTriangleDartTriple_edges_eq_record w j, hrecord, he]
  have hids : ({d.1.1, d.2.1.1, d.2.2.1} : Multiset ℕ) =
      {act w (t - 1), act w t, if k = 1 then s.nextEdge + 1 else act w (r - 1)} := by
    simpa [d] using hids'
  have hwest : ¬ MhatVertex w (edgeWest w (act w t)) := by
    intro hr
    change ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w t).west (act w t)⟩ at hnot
    have hend := edge_endpoints_eq w (act_lt_nextEdge w (le_rfl : t ≤ t))
    change Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (act w t)⟩ at hr
    have hrStage : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ := by
      simpa only [hend.1] using hr
    exact hnot hrStage
  have hbad : ¬ (MhatVertex w (kmswDartEndpoint w d.1) ∧
      MhatVertex w (kmswDartEndpoint w d.2.1) ∧
      MhatVertex w (kmswDartEndpoint w d.2.2)) := by
    intro hall
    have hmem : act w t ∈ ({d.1.1, d.2.1.1, d.2.2.1} : Multiset ℕ) := by
      rw [hids]
      simp
    have hedge : act w t = d.1.1 ∨ act w t = d.2.1.1 ∨ act w t = d.2.2.1 := by
      simpa using hmem
    rcases edgeWest_eq_faceCycleEndpoint w hfin d.1 d.2.1 d.2.2 hcycle
      (act w t) hedge with heq | heq | heq
    · exact hwest (heq ▸ hall.1)
    · exact hwest (heq ▸ hall.2.1)
    · exact hwest (heq ▸ hall.2.2)
  refine ⟨d.1, d.2.1, d.2.2, hcycle, hids, hbad, ?_, ?_, ?_⟩
  · exact stageTriangleDart_not_limitExternal w j d.1 (by simp [stageTriangleDartList, d])
  · exact stageTriangleDart_not_limitExternal w j d.2.1
      (by simp [stageTriangleDartList, d])
  · exact stageTriangleDart_not_limitExternal w j d.2.2
      (by simp [stageTriangleDartList, d])

end DirectedDistances.KMSW
