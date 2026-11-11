module

public import DirectedDistances.KMSW.StageTriangleCapSideForced
public import DirectedDistances.KMSW.MhatPrimeFaceSource
public import DirectedDistances.PaperProofs.Section5.FlowLineTimesFullProvider

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open MeasureTheory

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Each flow-line triangle has its exact creation time and a stored-triangle index.
The first triangle uses the missing geometric edge specified by initial triangle convention. -/
theorem flowLineTimes_triangle_creation_record (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
    ∃ j : TriangleCreationTime w,
      j.val = t - 1 ∧ j.val + 1 = t ∧
      stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
      ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
        (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j := by
  let r := sourceFlowNR w h (k - 1)
  let t := sourceFlowNL w h (k - 1)
  let s := kmswStage w (t - 1)
  obtain ⟨_, e, htri, _, _, _, _, hcases⟩ :=
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
  have hjtime : j.val + 1 = t := by dsimp [j]; omega
  have hcreated : (kmswStage w (j.val + 1)).triangles =
      (kmswStage w j.val).triangles ++ [stageTriangleRecord w j] := by
    rw [← stageTriangleTimes_records w (j.val + 1), stageTriangleTimes,
      dite_eq_left j.property, List.map_append, stageTriangleTimes_records]
    simp only [List.map_cons, List.map_nil]
  have htriLocal : (kmswStage w (j.val + 1)).triangles =
      (kmswStage w j.val).triangles ++ [(act w (t - 1), act w t, e)] := by
    simpa only [hjtime] using htri
  have hrecord : stageTriangleRecord w j = (act w (t - 1), act w t, e) := by
    have hh := List.append_cancel_left (hcreated.symm.trans htriLocal)
    simpa only [List.cons.injEq, and_true] using hh
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  exact ⟨j, rfl, hjtime, by simpa only [he] using hrecord, i, hi⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The creation triangle bounds its ambient cap component. This bounded component
differs from every unbounded face, and from every face whose bordering darts
are classified by `limitExternalDart`. No cut-completed map is identified here. -/
theorem mhatPrimeTriangleFace_ambient_face (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ F : PlaneFaces P,
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
      (∀ d ∈ stageTriangleDartList w j, P.dartBorders d F.val) ∧
      (∀ U : P.Face, P.IsUnbounded U → F.val ≠ U) ∧
      (∀ U : P.Face, (∀ d, P.dartBorders d U ↔ limitExternalDart w d) →
        F.val ≠ U) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨F, hregion, hborders⟩ := stageTriangleDarts_border_creation_cap w hfin j i hi
  refine ⟨F, hregion, hborders, ?_, ?_⟩
  · intro U hU hFU
    obtain ⟨R, hR⟩ := F.property.exists_norm_le
    obtain ⟨z, hz, hnorm⟩ := hU R
    have hzF : z ∈ F.val.val := by rwa [hFU]
    exact (not_lt_of_ge (hR z hzF)) hnorm
  · intro U hclass hFU
    let d := (stageTriangleDartTriple w j).1
    have hd : d ∈ stageTriangleDartList w j := by simp [stageTriangleDartList, d]
    have hb : P.dartBorders d U := by rw [← hFU]; exact hborders d hd
    exact stageTriangleDart_not_limitExternal w j d hd ((hclass d).mp hb)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Each source flow-line triangle has a bounded ambient face with the exact edge
multiset and cap region. The unreachable-vertex predicate is retained, while
identification with the cut-completed map remains separate. -/
theorem flowLineTimes_mhatPrimeFace_ambient (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    ∀ k, 1 ≤ k →
      let r := sourceFlowNR w h (k - 1)
      let t := sourceFlowNL w h (k - 1)
      let s := kmswStage w (t - 1)
      let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
      let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
      MhatPrimeTriangleFace w hfin {act w (t - 1), act w t, e} ∧
      ∃ j : TriangleCreationTime w,
        j.val = t - 1 ∧ j.val + 1 = t ∧
        stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
        ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
          (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
          ∃ F : PlaneFaces P,
            F.val.val =
              ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
            (∀ d ∈ stageTriangleDartList w j, P.dartBorders d F.val) ∧
            FaceSucc3Cycle (kmswInfFaceSucc w hfin)
              (stageTriangleDartTriple w j).1
              (stageTriangleDartTriple w j).2.1
              (stageTriangleDartTriple w j).2.2 ∧
            ({(stageTriangleDartTriple w j).1.1,
              (stageTriangleDartTriple w j).2.1.1,
              (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
                {act w (t - 1), act w t, e} ∧
            (∀ U : P.Face, P.IsUnbounded U → F.val ≠ U) ∧
            (∀ U : P.Face, (∀ d, P.dartBorders d U ↔ limitExternalDart w d) →
              F.val ≠ U) := by
  intro k hk
  obtain ⟨j, hj, hjtime, hrecord, i, hi⟩ :=
    flowLineTimes_triangle_creation_record w h k hk
  obtain ⟨F, hregion, hborders, hunbounded, hclassified⟩ :=
    mhatPrimeTriangleFace_ambient_face w hfin j i hi
  refine ⟨flowLineTimes_mhatPrimeFace w hfin hb h k hk,
    j, hj, hjtime, hrecord, i, hi, F, hregion, hborders,
    kmswInfFaceSucc_stageTriangle_cycle w hfin j, ?_, hunbounded, hclassified⟩
  rw [stageTriangleDartTriple_edges_eq_record w j, hrecord]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The provider's simultaneous almost-sure event also carries the bounded ambient
faces. This does not assert the cut-completed prime-map face identification. -/
theorem flowLineTimes_ae_mhatPrimeFace_ambient :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hb : BoundaryHitWitnesses w,
      ∃ h : HasFlowLineHits w,
        FlowLineTimesJointMinima w h ∧
        FlowLineTimesItemI w h ∧
        FlowLineTimesItemII w hfin hb h ∧
        ∀ k, 1 ≤ k →
          let r := sourceFlowNR w h (k - 1)
          let t := sourceFlowNL w h (k - 1)
          let s := kmswStage w (t - 1)
          let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
          let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
          MhatPrimeTriangleFace w hfin {act w (t - 1), act w t, e} ∧
          ∃ j : TriangleCreationTime w,
            j.val = t - 1 ∧ j.val + 1 = t ∧
            stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
            ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
              (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
              ∃ F : PlaneFaces P,
                F.val.val =
                  ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
                (∀ d ∈ stageTriangleDartList w j, P.dartBorders d F.val) ∧
                FaceSucc3Cycle (kmswInfFaceSucc w hfin)
                  (stageTriangleDartTriple w j).1
                  (stageTriangleDartTriple w j).2.1
                  (stageTriangleDartTriple w j).2.2 ∧
                ({(stageTriangleDartTriple w j).1.1,
                  (stageTriangleDartTriple w j).2.1.1,
                  (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) =
                    {act w (t - 1), act w t, e} ∧
                (∀ U : P.Face, P.IsUnbounded U → F.val ≠ U) ∧
                (∀ U : P.Face, (∀ d, P.dartBorders d U ↔ limitExternalDart w d) →
                  F.val ≠ U) := by
  filter_upwards [lemma_5_12_provider] with ω hprovider
  obtain ⟨hfin, hb, h, hmin, hitemI, hitemII, _⟩ := hprovider
  exact ⟨hfin, hb, h, hmin, hitemI, hitemII,
    flowLineTimes_mhatPrimeFace_ambient (fun i => ω (i + 1)) hfin hb h⟩

end DirectedDistances.KMSW
