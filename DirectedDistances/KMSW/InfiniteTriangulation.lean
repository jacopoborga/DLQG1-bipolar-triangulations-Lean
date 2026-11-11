module

public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.LocalFinitenessUpperChain
public import DirectedDistances.KMSW.NoMissingEdgesAE
public import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.RandomWalk.ConditionedTransience

/-! # The infinite KMSW face decomposition

Under finite incidence, finite triangle faces persist in the limiting face
successor. Under the transient boundary assumptions, every other face dart is
on one of the two boundary chains. The almost-sure statement uses the Pitman -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

private theorem inf_complete_mono (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m)
    {u : ℕ} (h : kmswVertexComplete w n u) : kmswVertexComplete w m u := by
  intro e he
  exact (h e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem inf_complete_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (u : ℕ) : ∃ N, kmswVertexComplete w N u := by
  obtain ⟨B, hB⟩ := (hfin u).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hmem : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)} := by
    refine ⟨e, kmsw_edge_allocated_by_self w e, ?_⟩
    exact he
  exact (hB hmem).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem inf_edge_complete_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (e : ℕ) : ∃ N,
      kmswVertexComplete w N (edgeWest w e) ∧
      kmswVertexComplete w N (edgeEast w e) := by
  obtain ⟨Nw, hw⟩ := inf_complete_stage w hfin (edgeWest w e)
  obtain ⟨Ne, he⟩ := inf_complete_stage w hfin (edgeEast w e)
  exact ⟨max Nw Ne, inf_complete_mono w (le_max_left _ _) hw,
    inf_complete_mono w (le_max_right _ _) he⟩

private theorem inf_complete_flip_endpoint (w : ℕ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage w N).nextEdge)
    (hw : kmswVertexComplete w N (edgeWest w e))
    (hee : kmswVertexComplete w N (edgeEast w e))
    (x : StageDart (kmswStage w N).nextEdge)
    (hx : x.1.val = e) :
    kmswVertexComplete w N
      (stageEndpoint (kmswStage w N) (edgeFlip (kmswStage w N).nextEdge x)) := by
  have hid : x.1.val = e := hx
  have hend := edge_endpoints_eq w he
  cases hb : x.2
  · simpa [edgeFlip, stageEndpoint, hb, hid, hend.2] using hee
  · simpa [edgeFlip, stageEndpoint, hb, hid, hend.1] using hw

private theorem inf_stageDart_eq_of_val {k : ℕ} {x y : StageDart k}
    (h : (x.1.val, x.2) = (y.1.val, y.2)) : x = y := by
  have hfst : x.1.val = y.1.val := congrArg (fun p : ℕ × Bool => p.1) h
  have hsnd : x.2 = y.2 := congrArg (fun p : ℕ × Bool => p.2) h
  apply Prod.ext
  · exact Fin.ext hfst
  · exact hsnd

/-- Each recorded triangle remains a three-cycle of the limiting face -/
theorem kmswInfFaceSucc_stageTriangle_cycle (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    FaceSucc3Cycle (kmswInfFaceSucc w hfin)
      (stageTriangleDartTriple w j).1
      (stageTriangleDartTriple w j).2.1
      (stageTriangleDartTriple w j).2.2 := by
  let t := stageTriangleDartTriple w j
  obtain ⟨N1, h1w, h1e⟩ := inf_edge_complete_stage w hfin t.1.1
  obtain ⟨N2, h2w, h2e⟩ := inf_edge_complete_stage w hfin t.2.1.1
  obtain ⟨N3, h3w, h3e⟩ := inf_edge_complete_stage w hfin t.2.2.1
  let N := max (j.val + 1) (max N1 (max N2 N3))
  have hjN : j.val < N := by dsimp [N]; omega
  have hN1w := inf_complete_mono w (n := N1) (m := N) (by dsimp [N]; omega) h1w
  have hN1e := inf_complete_mono w (n := N1) (m := N) (by dsimp [N]; omega) h1e
  have hN2w := inf_complete_mono w (n := N2) (m := N) (by dsimp [N]; omega) h2w
  have hN2e := inf_complete_mono w (n := N2) (m := N) (by dsimp [N]; omega) h2e
  have hN3w := inf_complete_mono w (n := N3) (m := N) (by dsimp [N]; omega) h3w
  have hN3e := inf_complete_mono w (n := N3) (m := N) (by dsimp [N]; omega) h3e
  let x1 := stageTriangleDart₁ w N j hjN
  let x2 := stageTriangleDart₂ w N j hjN
  let x3 := stageTriangleDart₃ w N j hjN
  have hx1 : (x1.1.val, x1.2) = t.1 := by
    simp [x1, stageTriangleDart₁, stageTriangleDartAt, t]
  have hx2 : (x2.1.val, x2.2) = t.2.1 := by
    simp [x2, stageTriangleDart₂, stageTriangleDartAt, t]
  have hx3 : (x3.1.val, x3.2) = t.2.2 := by
    simp [x3, stageTriangleDart₃, stageTriangleDartAt, t]
  have he1 : t.1.1 < (kmswStage w N).nextEdge :=
    stageTriangleDartList_lt w N j hjN t.1 (by simp [stageTriangleDartList, t])
  have he2 : t.2.1.1 < (kmswStage w N).nextEdge :=
    stageTriangleDartList_lt w N j hjN t.2.1 (by simp [stageTriangleDartList, t])
  have he3 : t.2.2.1 < (kmswStage w N).nextEdge :=
    stageTriangleDartList_lt w N j hjN t.2.2 (by simp [stageTriangleDartList, t])
  have hc1 := inf_complete_flip_endpoint w N t.1.1 he1 hN1w hN1e x1
    (congrArg Prod.fst hx1)
  have hc2 := inf_complete_flip_endpoint w N t.2.1.1 he2 hN2w hN2e x2
    (congrArg Prod.fst hx2)
  have hc3 := inf_complete_flip_endpoint w N t.2.2.1 he3 hN3w hN3e x3
    (congrArg Prod.fst hx3)
  have hstage := stageTriangle_isFace w j N hjN
  rcases hstage with ⟨h12, h23, h31, hne12, hne23, hne31⟩
  have hinf1 := kmswInfFaceSucc_eq_stage w hfin N x1 hc1
  have hinf2 := kmswInfFaceSucc_eq_stage w hfin N x2 hc2
  have hinf3 := kmswInfFaceSucc_eq_stage w hfin N x3 hc3
  have h12val := congrArg (fun d : StageDart (kmswStage w N).nextEdge =>
    (d.1.val, d.2)) h12
  have h23val := congrArg (fun d : StageDart (kmswStage w N).nextEdge =>
    (d.1.val, d.2)) h23
  have h31val := congrArg (fun d : StageDart (kmswStage w N).nextEdge =>
    (d.1.val, d.2)) h31
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      kmswInfFaceSucc w hfin t.1 = kmswInfFaceSucc w hfin (x1.1.val, x1.2) :=
        congrArg (kmswInfFaceSucc w hfin) hx1.symm
      _ = (((kmswMap w N).faceSucc x1).1.val, ((kmswMap w N).faceSucc x1).2) := hinf1
      _ = (x2.1.val, x2.2) := h12val
      _ = t.2.1 := hx2
  · calc
      kmswInfFaceSucc w hfin t.2.1 = kmswInfFaceSucc w hfin (x2.1.val, x2.2) :=
        congrArg (kmswInfFaceSucc w hfin) hx2.symm
      _ = (((kmswMap w N).faceSucc x2).1.val, ((kmswMap w N).faceSucc x2).2) := hinf2
      _ = (x3.1.val, x3.2) := h23val
      _ = t.2.2 := hx3
  · calc
      kmswInfFaceSucc w hfin t.2.2 = kmswInfFaceSucc w hfin (x3.1.val, x3.2) :=
        congrArg (kmswInfFaceSucc w hfin) hx3.symm
      _ = (((kmswMap w N).faceSucc x3).1.val, ((kmswMap w N).faceSucc x3).2) := hinf3
      _ = (x1.1.val, x1.2) := h31val
      _ = t.1 := hx1
  · intro ht
    have hval : (x1.1.val, x1.2) = (x2.1.val, x2.2) := hx1.trans (ht.trans hx2.symm)
    exact hne12 (inf_stageDart_eq_of_val hval)
  · intro ht
    have hval : (x2.1.val, x2.2) = (x3.1.val, x3.2) := hx2.trans (ht.trans hx3.symm)
    exact hne23 (inf_stageDart_eq_of_val hval)
  · intro ht
    have hval : (x3.1.val, x3.2) = (x1.1.val, x1.2) := hx3.trans (ht.trans hx1.symm)
    exact hne31 (inf_stageDart_eq_of_val hval)

/-- A dart whose orientation is not on its corresponding infinite boundary
chain belongs to a recorded triangle. The finite stage is chosen after the
edge is present and after its relevant boundary record set has stabilized. -/
private theorem infDart_triangle_of_not_boundary (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool)
    (hboundary : (d.2 = false → ¬ IsLeftBoundaryEdge w d.1) ∧
      (d.2 = true → ¬ IsRightBoundaryEdge w d.1)) :
    ∃! j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  obtain ⟨N₀, hpresent⟩ :=
    eventually_present_of_nonneg_of_unbounded w hL0 hR d.1
  let S : Set ℕ := if d.2 then
    {n | d.1 ∈ (kmswStage w n).LR} else {n | d.1 ∈ (kmswStage w n).UL}
  have hSfin : S.Finite := by
    by_cases hb : d.2 = false
    · have hnot := hboundary.1 hb
      have hfin : {n | d.1 ∈ (kmswStage w n).UL}.Finite := by
        rcases ({n | d.1 ∈ (kmswStage w n).UL} : Set ℕ).finite_or_infinite with h | h
        · exact h
        · exact (hnot h).elim
      simpa [S, hb] using hfin
    · have ht : d.2 = true := by
        cases hbool : d.2 with
        | false => exact (hb hbool).elim
        | true => rfl
      have hnot := hboundary.2 ht
      have hfin : {n | d.1 ∈ (kmswStage w n).LR}.Finite := by
        rcases ({n | d.1 ∈ (kmswStage w n).LR} : Set ℕ).finite_or_infinite with h | h
        · exact h
        · exact (hnot h).elim
      simpa [S, ht] using hfin
  obtain ⟨B, hB⟩ := hSfin.bddAbove
  let n := max N₀ (B + 1)
  have hN₀ : N₀ ≤ n := le_max_left _ _
  have halloc : d.1 < (kmswStage w n).nextEdge := (hpresent n hN₀).1
  have hp : (kmswStage w n).present d.1 = true := (hpresent n hN₀).2
  have hLL := kmswStage_LL_eq_nil w hL0 n
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, halloc⟩, d.2)
  have hpart := stage_dart_partition w n x
  rcases hpart with hout | htri
  · have hout' := (stageOuterWord_mem_iff w n x).mp hout
    have houtVal :
        (d.2 = false ∧ (d.1 ∈ (kmswStage w n).UL ∨ d.1 ∈ (kmswStage w n).UR)) ∨
        (d.2 = true ∧ (d.1 ∈ (kmswStage w n).LR ∨ d.1 ∈ (kmswStage w n).LL)) := by
      simpa [x] using hout'
    rcases houtVal with ⟨hb, hside⟩ | ⟨hb, hside⟩
    · rcases hside with hUL | hUR
      · have hnUL : n ∈ {m | d.1 ∈ (kmswStage w m).UL} := hUL
        have hbound : n ≤ B := by
          have hs : n ∈ S := by simpa [S, hb] using hnUL
          exact hB hs
        dsimp [n] at hbound
        omega
      · have hmiss := ((kmswStage_status w n).1 d.1 halloc).2 (Or.inl hUR)
        simp [hp] at hmiss
    · rcases hside with hLR | hLL'
      · have hnLR : n ∈ {m | d.1 ∈ (kmswStage w m).LR} := hLR
        have hbound : n ≤ B := by
          have hs : n ∈ S := by simpa [S, hb] using hnLR
          exact hB hs
        dsimp [n] at hbound
        omega
      · rw [hLL] at hLL'
        simp at hLL'
  · obtain ⟨j, ⟨hjn, hdj⟩, _⟩ := htri
    refine ⟨j, ?_, ?_⟩
    · simpa [x] using hdj
    · intro k hkd
      by_contra hjk
      let m := max n (max (j.val + 1) (k.val + 1))
      have hjm : j.val < m := by dsimp [m]; omega
      have hkm : k.val < m := by dsimp [m]; omega
      have hdisj := stageTriangleDartLists_disjoint w m j k hjm hkm
        (fun hEq => hjk hEq.symm)
      have hdj' : d ∈ stageTriangleDartList w j := by simpa [x] using hdj
      exact List.disjoint_left.mp hdisj hdj' hkd

/-- Every geometric dart is either a left or right boundary dart, or belongs
to exactly one recorded triangle. Temporary outer-word darts are eliminated
by eventual presence and the stabilised boundary record sets (`def-uiqbot`, -/
theorem kmswInfDart_partition (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) :
    (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
      (∃ i, d = (kmswRightBoundaryEdge w i, true)) ∨
      ∃! j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  by_cases hb : d.2 = false
  · by_cases hleft : IsLeftBoundaryEdge w d.1
    · obtain ⟨i, hi⟩ := (isLeftBoundaryEdge_iff w htrans d.1).mp hleft
      have hEq : d = (kmswLeftBoundaryEdge w i, false) := by
        apply Prod.ext
        · exact hi
        · exact hb
      exact Or.inl ⟨i, hEq⟩
    · have htri := infDart_triangle_of_not_boundary w hR hL0 d
        ⟨(fun _ => hleft), (fun ht => by cases (hb.symm.trans ht))⟩
      exact Or.inr (Or.inr htri)
  · have hb' : d.2 = true := by
      cases hbool : d.2 with
      | false => exact (hb hbool).elim
      | true => rfl
    by_cases hright : IsRightBoundaryEdge w d.1
    · obtain ⟨i, hi⟩ := (isRightBoundaryEdge_iff w hR d.1).mp hright
      have hEq : d = (kmswRightBoundaryEdge w i, true) := by
        apply Prod.ext
        · exact hi
        · exact hb'
      exact Or.inr (Or.inl ⟨i, hEq⟩)
    · have htri := infDart_triangle_of_not_boundary w hR hL0 d
        ⟨(fun ht => by cases (hb'.symm.trans ht)), (fun _ => hright)⟩
      exact Or.inr (Or.inr htri)

/-- Every nonboundary dart belongs to a unique triangle whose three distinct
darts form its limiting face cycle. Thus each non-outer face has exactly -/
theorem kmswInfDart_nonOuterFace_cycle (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool)
    (hleft : ∀ i, d ≠ (kmswLeftBoundaryEdge w i, false))
    (hright : ∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) :
    ∃! j : TriangleCreationTime w,
      d ∈ stageTriangleDartList w j ∧
        FaceSucc3Cycle (kmswInfFaceSucc w hfin)
          (stageTriangleDartTriple w j).1
          (stageTriangleDartTriple w j).2.1
          (stageTriangleDartTriple w j).2.2 := by
  have hpart := kmswInfDart_partition w hfin htrans hR hL0 d
  rcases hpart with ⟨i, hi⟩ | ⟨i, hi⟩ | htri
  · exact (hleft i hi).elim
  · exact (hright i hi).elim
  · obtain ⟨j, hdj, huniq⟩ := htri
    refine ⟨j, ⟨hdj, kmswInfFaceSucc_stageTriangle_cycle w hfin j⟩, ?_⟩
    intro k hk
    exact huniq k hk.1

private theorem measurable_vectorPitman_infTriangulation :
    Measurable RandomWalk.vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp RandomWalk.measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add
      ((RandomWalk.measurable_globalLazyRunningMinimum n).comp hf))

private theorem pitmanCodes_ae_L_tendsto_atTop :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      Tendsto (L (RandomWalk.pitmanCode (fun i => ω (i + 1)))) atTop atTop := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 =>
      RandomWalk.vectorPitman (RandomWalk.codeWalk ω)) :=
    measurable_vectorPitman_infTriangulation.comp RandomWalk.measurable_codeWalk
  have hT := ae_of_ae_map hmeas.aemeasurable
    (by rw [RandomWalk.map_vectorPitman_codeWalk]
        exact RandomWalk.conditionedVectorPathLaw_tendsto_fst_atTop 0 0)
  filter_upwards [hT] with ω hω
  have heq : L (RandomWalk.pitmanCode (fun i => ω (i + 1))) =
      fun j => (RandomWalk.vectorPitman (RandomWalk.codeWalk ω) j).1 := by
    funext j
    rw [RandomWalk.kmsw_L_eq, RandomWalk.integrateCodes_pitmanCode]
    have hwalk : RandomWalk.codeWalk ω =
        RandomWalk.integrateCodes (fun i => ω (i + 1)) := by
      funext k
      exact RandomWalk.codeWalk_eq_integrateCodes ω k
    rw [← hwalk]
  rw [heq]
  exact hω

/-- Almost surely finite incidence, the two boundary chains, and triangularity
of every non-outer face hold simultaneously; every edge also becomes -/
theorem pitmanCodes_ae_infinite_face_structure :
    (∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∀ d : ℕ × Bool,
          (∀ i, d ≠ (kmswLeftBoundaryEdge w i, false)) →
          (∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) →
          ∃! j : TriangleCreationTime w,
            d ∈ stageTriangleDartList w j ∧
              FaceSucc3Cycle (kmswInfFaceSucc w hfin)
                (stageTriangleDartTriple w j).1
                (stageTriangleDartTriple w j).2.1
                (stageTriangleDartTriple w j).2.2) ∧
    (∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ e : ℕ, ∃ N, ∀ n, N ≤ n →
        e < (kmswStage (RandomWalk.pitmanCode (fun i => ω (i + 1))) n).nextEdge ∧
          (kmswStage (RandomWalk.pitmanCode (fun i => ω (i + 1))) n).present e = true) := by
  have hface : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∀ d : ℕ × Bool,
          (∀ i, d ≠ (kmswLeftBoundaryEdge w i, false)) →
          (∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) →
          ∃! j : TriangleCreationTime w,
            d ∈ stageTriangleDartList w j ∧
              FaceSucc3Cycle (kmswInfFaceSucc w hfin)
                (stageTriangleDartTriple w j).1
                (stageTriangleDartTriple w j).2.1
                (stageTriangleDartTriple w j).2.2 := by
    have hfinAE := pitmanCodes_ae_finite_incident_edges
    have hRAE := RandomWalk.pitmanCodes_ae_R_unbounded_below
    have hTAE := pitmanCodes_ae_L_tendsto_atTop
    filter_upwards [hfinAE, hRAE, hTAE] with ω hfin hR htrans
    let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
    have hfin' : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite := by
      intro v
      simpa [w] using hfin v
    have hR' : ∀ a : ℤ, ∃ n, R w n ≤ a := by
      intro a
      obtain ⟨n, hn⟩ := hR a
      exact ⟨n, by rw [RandomWalk.kmsw_R_eq]; exact hn⟩
    have hL0 : ∀ j, 0 ≤ L w j := by
      intro j
      rw [RandomWalk.kmsw_L_eq]
      exact RandomWalk.integrateCodes_pitmanCode_fst_nonneg
        (fun i => ω (i + 1)) j
    have htrans' : Tendsto (L w) atTop atTop := by simpa [w] using htrans
    refine ⟨hfin', ?_⟩
    intro d hleft hright
    exact kmswInfDart_nonOuterFace_cycle w hfin' htrans' hR' hL0 d hleft hright
  exact ⟨hface, pitmanCodes_ae_eventually_present⟩
end DirectedDistances.KMSW

