module

public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.LimitExternalFace
public import DirectedDistances.PlanarMap.GraphRegion
import DirectedDistances.KMSW.MonotoneLimitDrawing
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.PlanarMap.GraphRegionClosure
import DirectedDistances.KMSW.MonotoneStepCommon
import DirectedDistances.KMSW.MonotoneCapPersistence

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set Metric
open scoped Topology




@[expose] def monotoneStageRegion {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) : Set ℂ :=
  closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper




@[expose] def monotoneStageRegionUnion {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) : Set ℂ :=
  ⋃ n, monotoneStageRegion Q G n




@[expose] def monotoneLimitExterior {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) : Set ℂ :=
  (monotoneStageRegionUnion Q G)ᶜ




@[expose] def monotoneLayoutTraceUnion {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) : Set ℂ := ⋃ n, (Q n).image

/-- The union of the arcs on the persistent upper-left boundary rays.
Helper toward adjudication n308; not a paper result. See `remark-kmsw-infinite`, -/
@[expose] noncomputable def monotonePersistentULTrace (w : ℕ → Fin 3) : Set ℂ :=
  {z | ∃ i, z ∈ (layoutArc w (kmswLeftBoundaryEdge w i)
    (kmswLeftBoundaryEdge w i)).image}

/-- The union of the arcs on the persistent lower-right boundary rays.
Helper toward adjudication n308; not a paper result. See `remark-kmsw-infinite`, -/
@[expose] noncomputable def monotonePersistentLRTrace (w : ℕ → Fin 3) : Set ℂ :=
  {z | ∃ i, z ∈ (layoutArc w (kmswRightBoundaryEdge w i)
    (kmswRightBoundaryEdge w i)).image}

private theorem monotoneLayoutArc_stable {w : ℕ → Fin 3} {n m e : ℕ}
    (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

/-- On a bounded set, sufficiently late upper traces lie on persistent UL edges.
This local boundary lemma uses finite incidence and height control through the
locally finite limit drawing. Helper toward adjudication n308; not a paper result. -/
theorem monotoneStageUpperTrace_eventually_persistentUL {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℤ))
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    ∃ N, ∀ n, N ≤ n →
      graphOver (G n).xmin (G n).xmax (G n).upper ∩ K ⊆ monotonePersistentULTrace w := by
  classical
  let hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P) := fun n => ⟨Q n, ⟨G n⟩⟩
  let P := monotoneLimitDrawing w hfin hfam
  have hagree := monotoneLimitDrawing_agrees w hfin hfam Q
    (fun n v => (G n).pos_layout v) (fun n d => (G n).arc_layout d)
  have hlocal := P.locally_finite K hK
  let E : Set ℕ := Prod.fst ''
    {d | (K ∩ (P.arc d).image).Nonempty}
  have hE : E.Finite := hlocal.image Prod.fst
  have htime (e : ℕ) : ∃ N, ∀ n, N ≤ n →
      (e ∈ (kmswStage w n).UL ∨ e ∈ (kmswStage w n).UR) →
      IsLeftBoundaryEdge w e := by
    obtain ⟨NUR, hUR⟩ := kmswRun_UR_eventually_absent w hR e
    by_cases hleft : IsLeftBoundaryEdge w e
    · exact ⟨NUR, fun n _ _ => hleft⟩
    · have hfinite : {n | e ∈ (kmswStage w n).UL}.Finite := by
        simpa [IsLeftBoundaryEdge] using hleft
      obtain ⟨B, hB⟩ := hfinite.bddAbove
      refine ⟨max NUR (B + 1), fun n hn hUpper => ?_⟩
      rcases hUpper with hUL | hUR'
      · have hnB : B + 1 ≤ n := (le_max_right _ _).trans hn
        have hbound := hB hUL
        omega
      · exact False.elim (hUR n ((le_max_left _ _).trans hn) hUR')
  let T : ℕ → ℕ := fun e => Classical.choose (htime e)
  have hT (e : ℕ) : ∀ n, T e ≤ n →
      (e ∈ (kmswStage w n).UL ∨ e ∈ (kmswStage w n).UR) →
      IsLeftBoundaryEdge w e := Classical.choose_spec (htime e)
  obtain ⟨N, hN⟩ := (hE.image T).bddAbove
  refine ⟨N, fun n hn z hz => ?_⟩
  rcases hz with ⟨hzUpper, hzK⟩
  rw [(G n).upper_trace] at hzUpper
  obtain ⟨e, hzUpper⟩ := mem_iUnion.mp hzUpper
  obtain ⟨heUpper, hzTrace⟩ := mem_iUnion.mp hzUpper
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heUpper ⊢
      tauto)
  have heULorUR : e ∈ (kmswStage w n).UL ∨ e ∈ (kmswStage w n).UR :=
    List.mem_append.mp heUpper
  have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
    simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
  have hzStageArc : z ∈ (layoutArc w n e).image := by
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hzPArc : z ∈ (P.arc (e, false)).image := by
    rw [hagree.2 n (⟨⟨e, he⟩, false⟩), hd]
    exact hzStageArc
  have heE : e ∈ E := by
    change e ∈ Prod.fst '' {d | (K ∩ (P.arc d).image).Nonempty}
    exact Set.mem_image_of_mem Prod.fst
      (show (e, false) ∈ {d | (K ∩ (P.arc d).image).Nonempty} from
        ⟨z, ⟨hzK, hzPArc⟩⟩)
  have hleft := hT e n
    ((hN (Set.mem_image_of_mem T heE)).trans hn) heULorUR
  have hArcStable : layoutArc w n e = layoutArc w e e := by
    let m := max n e
    calc
      layoutArc w n e = layoutArc w m e :=
        (monotoneLayoutArc_stable (le_max_left n e) he).symm
      _ = layoutArc w e e :=
        monotoneLayoutArc_stable (le_max_right n e)
          (kmsw_edge_allocated_by_self w e)
  obtain ⟨i, heLeft⟩ := (isLeftBoundaryEdge_iff w htrans e).mp hleft
  rw [heLeft] at hArcStable
  have hzStageArc' : z ∈ (layoutArc w n (kmswLeftBoundaryEdge w i)).image := by
    simpa [heLeft] using hzStageArc
  exact ⟨i, by rw [← hArcStable]; exact hzStageArc'⟩

/-- Under nonnegative horizontal coordinates, every lower trace is on a persistent
lower-right boundary edge. The bounded set `K` (hypothesis `_hK`) is unused; the conclusion
holds for every `K` and `N = 0`, and the binder is kept for symmetry with the upper-trace
version. Helper toward adjudication n308; not a paper result. See -/
theorem monotoneStageLowerTrace_eventually_persistentLR {w : ℕ → Fin 3}
    (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (K : Set ℂ) (_hK : Bornology.IsBounded K) :
    ∃ N, ∀ n, N ≤ n →
      graphOver (G n).xmin (G n).xmax (G n).lower ∩ K ⊆
        monotonePersistentLRTrace w := by
  classical
  refine ⟨0, fun n _ z hz => ?_⟩
  rcases hz with ⟨hzLower, hzK⟩
  rw [(G n).lower_trace] at hzLower
  obtain ⟨e, hzLower⟩ := mem_iUnion.mp hzLower
  obtain ⟨heLower, hzTrace⟩ := mem_iUnion.mp hzLower
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heLower ⊢
      tauto)
  have hLL := kmswStage_LL_eq_nil w hL0 n
  have heLR : e ∈ (kmswStage w n).LR := by
    rw [hLL, List.nil_append] at heLower
    exact heLower
  have hstay (m : ℕ) (hnm : n ≤ m) : e ∈ (kmswStage w m).LR := by
    induction hnm with
    | refl => exact heLR
    | @step m hnm ih =>
      obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w m
      rw [ht]
      exact List.mem_append.mpr (Or.inl ih)
  have hInfinite : IsRightBoundaryEdge w e := by
    apply Set.Infinite.mono (s := Set.Ici n) ?_ (Set.Ici_infinite n)
    intro m hm
    exact hstay m (Set.mem_Ici.mp hm)
  obtain ⟨i, hi⟩ := (isRightBoundaryEdge_iff w hR e).mp hInfinite
  have hzArc : z ∈ (layoutArc w n e).image := by
    have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
      simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hArcStable : layoutArc w n e = layoutArc w e e := by
    let m := max n e
    calc
      layoutArc w n e = layoutArc w m e :=
        (monotoneLayoutArc_stable (le_max_left n e) he).symm
      _ = layoutArc w e e :=
        monotoneLayoutArc_stable (le_max_right n e)
          (kmsw_edge_allocated_by_self w e)
  rw [hi] at hzArc hArcStable
  rw [hArcStable] at hzArc
  exact ⟨i, hzArc⟩

/-- A point strictly above a persistent upper-left edge is outside every sufficiently
late stage region over the edge's horizontal range. Helper toward adjudication n308; -/
theorem monotoneStageRegion_excludes_above_persistentUL {w : ℕ → Fin 3}
    (htrans : Filter.Tendsto (L w) (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℤ))
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (i : ℕ) {q z : ℂ}
    (hq : q ∈ (layoutArc w (kmswLeftBoundaryEdge w i)
      (kmswLeftBoundaryEdge w i)).image)
    (hre : q.re = z.re) (him : q.im < z.im) :
    ∃ N, ∀ n, N ≤ n → z ∉ monotoneStageRegion Q G n := by
  obtain ⟨N, hN⟩ := kmswStage_UL_getElem?_eventually w htrans i
  refine ⟨N, fun n hn hzRegion => ?_⟩
  let e := kmswLeftBoundaryEdge w i
  have hget : (kmswStage w n).UL[i]? = some e := hN n hn
  have hidx := (List.getElem?_eq_some_iff.mp hget).1
  have heIn : e ∈ (kmswStage w n).UL := by
    rw [← (List.getElem?_eq_some_iff.mp hget).2]
    exact List.getElem_mem hidx
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heIn ⊢
      tauto)
  have hStable : layoutArc w n e = layoutArc w e e := by
    let m := max n e
    calc
      layoutArc w n e = layoutArc w m e :=
        (monotoneLayoutArc_stable (le_max_left n e) he).symm
      _ = layoutArc w e e :=
        monotoneLayoutArc_stable (le_max_right n e) (kmsw_edge_allocated_by_self w e)
  have hq' : q ∈ (layoutArc w n e).image := by
    have hqLayout : q ∈ (layoutArc w e e).image := by
      change q ∈ (layoutArc w e e).image at hq
      exact hq
    rw [← hStable] at hqLayout
    exact hqLayout
  have hUpper : (G n).upper q.re = q.im :=
    (G n).upper_eq_arc_height (List.mem_append.mpr (Or.inl heIn)) hq'
  have hRegion : z.im ≤ (G n).upper z.re := hzRegion.2.2.2
  have hEq : (G n).upper z.re = q.im := by rw [← hre, hUpper]
  rw [hEq] at hRegion
  exact (not_le_of_gt him) hRegion

/-- A point strictly below a persistent lower-right edge is outside every sufficiently
late stage region over the edge's horizontal range. Helper toward adjudication n308; -/
theorem monotoneStageRegion_excludes_below_persistentLR {w : ℕ → Fin 3}
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (i : ℕ) {q z : ℂ}
    (hq : q ∈ (layoutArc w (kmswRightBoundaryEdge w i)
      (kmswRightBoundaryEdge w i)).image)
    (hre : q.re = z.re) (him : z.im < q.im) :
    ∃ N, ∀ n, N ≤ n → z ∉ monotoneStageRegion Q G n := by
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually w hR i
  refine ⟨N, fun n hn hzRegion => ?_⟩
  let e := kmswRightBoundaryEdge w i
  have hget : (kmswStage w n).LR[i]? = some e := hN n hn
  have hidx := (List.getElem?_eq_some_iff.mp hget).1
  have heIn : e ∈ (kmswStage w n).LR := by
    rw [← (List.getElem?_eq_some_iff.mp hget).2]
    exact List.getElem_mem hidx
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heIn ⊢
      tauto)
  have hStable : layoutArc w n e = layoutArc w e e := by
    let m := max n e
    calc
      layoutArc w n e = layoutArc w m e :=
        (monotoneLayoutArc_stable (le_max_left n e) he).symm
      _ = layoutArc w e e :=
        monotoneLayoutArc_stable (le_max_right n e) (kmsw_edge_allocated_by_self w e)
  have hq' : q ∈ (layoutArc w n e).image := by
    have hqLayout : q ∈ (layoutArc w e e).image := by
      change q ∈ (layoutArc w e e).image at hq
      exact hq
    rw [← hStable] at hqLayout
    exact hqLayout
  have hLower : (G n).lower q.re = q.im :=
    (G n).lower_eq_arc_height (List.mem_append.mpr (Or.inr heIn)) hq'
  have hRegion : (G n).lower z.re ≤ z.im := hzRegion.2.2.1
  have hEq : (G n).lower z.re = q.im := by rw [← hre, hLower]
  rw [hEq] at hRegion
  exact (not_le_of_gt him) hRegion

private theorem kmswStageRank_nonneg_of_hL0 {w : ℕ → Fin 3}
    (hL0 : ∀ j, 0 ≤ L w j) :
    ∀ n v, 0 ≤ kmswStageRank w n v := by
  have hnoFresh (n : ℕ) (hc : w n = 0) :
      (kmswStage w n).UL.dropLast.reverse ≠ [] := by
    intro hfresh
    have hLL := kmswStage_LL_eq_nil w hL0 (n + 1)
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hfresh] at hLL
  intro n
  induction n with
  | zero =>
    intro v
    by_cases hv0 : v = 0
    · simp [kmswStageRank, hv0]
    · by_cases hv1 : v = 1
      · simp [kmswStageRank, hv1]
      · simp [kmswStageRank, hv1]
  | succ n ih =>
    intro v
    by_cases hv : v = (kmswStage w n).nextVertex
    · subst v
      by_cases hc0 : w n = 0
      · simp [kmswStageRank, hc0, hnoFresh n hc0]
        exact ih _
      · simp [kmswStageRank, hc0]
        by_cases hc1 : w n = 1
        · simp [hc1]
          have hwest := ih ((kmswStage w n).west (kmswStage w n).active)
          have heast := ih ((kmswStage w n).east (kmswStage w n).active)
          positivity
        · simp [hc1]
          by_cases hUR : (kmswStage w n).UR = []
          · simp [hUR]
            have heast := ih ((kmswStage w n).east (kmswStage w n).active)
            positivity
          · simp [hUR]
            exact ih _
    · simpa [kmswStageRank, hv] using ih v

private theorem kmswStage_zero_mem_LR (w : ℕ → Fin 3) (n : ℕ) :
    0 ∈ (kmswStage w n).LR := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left _ ih

private theorem monotoneLayoutRoot_pos (w : ℕ → Fin 3) (n : ℕ) :
    layoutPos w n 0 = 0 := by
  induction n with
  | zero =>
    apply Complex.ext <;> simp [layoutPos, kmswStageRank, layoutHeight]
  | succ n ih =>
    have hnext := CutConverse.nextVertex_mono w (Nat.zero_le n)
    have hroot : 0 < (kmswStage w n).nextVertex := by
      simp [kmswStage, kmswInit] at hnext
      omega
    rw [layoutPos_old_vertex w n 0 hroot, ih]

/-- Upper stage traces have nonnegative height. Helper toward adjudication n308; -/
theorem monotoneUpperTrace_nonneg {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {n : ℕ} {z : ℂ}
    (hz : z ∈ graphOver (G n).xmin (G n).xmax (G n).upper) : 0 ≤ z.im := by
  rw [(G n).upper_trace] at hz
  obtain ⟨e, hz⟩ := mem_iUnion.mp hz
  obtain ⟨heUpper, hzTrace⟩ := mem_iUnion.mp hz
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at heUpper ⊢
      tauto)
  have hzArc : z ∈ (layoutArc w n e).image := by
    have hd : (Q n).arc (⟨⟨e, he⟩, false⟩) = layoutArc w n e := by
      simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
    simpa [stageEdgeTrace, he, hd] using hzTrace
  have hheight := layoutArc_height_lower w n e he z hzArc
  have hw : 0 ≤ (layoutPos w n ((kmswStage w n).west e)).im := by
    simpa [layoutPos] using layoutHeight_nonneg w n ((kmswStage w n).west e)
  have heast : 0 ≤ (layoutPos w n ((kmswStage w n).east e)).im := by
    simpa [layoutPos] using layoutHeight_nonneg w n ((kmswStage w n).east e)
  exact (le_min hw heast).trans hheight

/-- Nonnegative horizontal walk coordinates keep every certified stage's west endpoint
at the root line. Helper toward adjudication n308; not a paper result. See `def-kmsw`, -/
theorem monotoneStageInvariant_xmin_eq_zero_of_hL0 {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (hL0 : ∀ j, 0 ≤ L w j)
    (G : MonotoneStageInvariant w n P) : G.xmin = 0 := by
  have hxnonneg : 0 ≤ G.xmin := by
    rw [G.xmin_eq_upper_start]
    change 0 ≤ (kmswStageRank w n
      ((kmswStage w n).west
        (((kmswStage w n).UL ++ (kmswStage w n).UR).head
          (kmswStage_boundary_nonempty w n).1)) : ℝ)
    exact_mod_cast kmswStageRank_nonneg_of_hL0 hL0 n
      ((kmswStage w n).west
        (((kmswStage w n).UL ++ (kmswStage w n).UR).head
          (kmswStage_boundary_nonempty w n).1))
  have h0LR := kmswStage_zero_mem_LR w n
  have he0 : 0 < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 0
    simp only [List.mem_append]
    tauto
  have hw0 : (kmswStage w n).west 0 = 0 := by
    have hstable := kmswStage_endpoints_stable w (Nat.zero_le n) (by
      simp [kmswStage, kmswInit] : 0 < (kmswStage w 0).nextEdge)
    simpa [kmswStage, kmswInit] using hstable.1
  have hroot : (layoutPos w n 0 : ℂ) ∈ (layoutArc w n 0).image := by
    have hstart : (layoutArc w n 0).start ∈ (layoutArc w n 0).image := Or.inl rfl
    rw [layoutArc_start w n 0 he0, hw0] at hstart
    simpa [monotoneLayoutRoot_pos] using hstart
  have htrace : (layoutPos w n 0 : ℂ) ∈ stageEdgeTrace P 0 := by
    simp [stageEdgeTrace, he0, G.arc_layout]
    exact hroot
  have hlow : 0 ∈ (kmswStage w n).LL ++ (kmswStage w n).LR := by
    rw [kmswStage_LL_eq_nil w hL0 n]
    exact List.mem_append.mpr (Or.inr h0LR)
  have hgraph : (layoutPos w n 0 : ℂ) ∈
      graphOver G.xmin G.xmax G.lower := by
    rw [G.lower_trace]
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨hlow, htrace⟩⟩
  have hxle : G.xmin ≤ 0 := by
    have hpos := monotoneLayoutRoot_pos w n
    have := hgraph.1
    simpa [hpos] using this
  exact le_antisymm hxle hxnonneg

private theorem kmswStageRank_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    kmswStageRank w (n + 1) v = kmswStageRank w n v := by
  have hne : v ≠ (kmswStage w n).nextVertex := by omega
  simp [kmswStageRank, hne]

private theorem kmswStage_LR_last_rank_transfer (w : ℕ → Fin 3) (n : ℕ)
    (hLR : (kmswStage w (n + 1)).LR = (kmswStage w n).LR)
    (hne : (kmswStage w n).LR ≠ [])
    (hrank : kmswStageRank w n
      ((kmswStage w n).east ((kmswStage w n).LR.getLast hne)) =
        ((kmswStage w n).LR.length : ℚ)) :
    ∃ hne' : (kmswStage w (n + 1)).LR ≠ [],
      kmswStageRank w (n + 1)
        ((kmswStage w (n + 1)).east ((kmswStage w (n + 1)).LR.getLast hne')) =
          ((kmswStage w (n + 1)).LR.length : ℚ) := by
  let e := (kmswStage w n).LR.getLast hne
  have hne' : (kmswStage w (n + 1)).LR ≠ [] := by rw [hLR]; exact hne
  have hlast : (kmswStage w (n + 1)).LR.getLast hne' = e := by
    simp [hLR, e]
  have heMem : e ∈ (kmswStage w n).LR := by
    exact List.getLast_mem hne
  have heAll : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
      (kmswStage w n).LL ++ (kmswStage w n).LR := by
    exact List.mem_append_right _ heMem
  have heBound : e < (kmswStage w n).nextEdge := by
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
  have hends := kmswStage_endpoints_stable w (Nat.le_succ n) heBound
  have hverts := kmswStage_endpoints_lt_nextVertex w n e heBound
  refine ⟨hne', ?_⟩
  calc
    kmswStageRank w (n + 1)
        ((kmswStage w (n + 1)).east ((kmswStage w (n + 1)).LR.getLast hne')) =
        kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) := by rw [hlast]
    _ = kmswStageRank w (n + 1) ((kmswStage w n).east e) := by rw [hends.2]
    _ = kmswStageRank w n ((kmswStage w n).east e) :=
      kmswStageRank_old_vertex w n _ hverts.2
    _ = ((kmswStage w n).LR.length : ℚ) := hrank
    _ = ((kmswStage w (n + 1)).LR.length : ℚ) := by rw [hLR]

private theorem kmswStage_LR_last_rank_eq_length (w : ℕ → Fin 3) (n : ℕ) :
    ∃ hLR : (kmswStage w n).LR ≠ [],
      kmswStageRank w n
        ((kmswStage w n).east ((kmswStage w n).LR.getLast hLR)) =
          ((kmswStage w n).LR.length : ℚ) := by
  induction n with
  | zero =>
      refine ⟨by simp [kmswStage, kmswInit], ?_⟩
      norm_num [kmswStage, kmswInit, kmswStageRank]
  | succ n ih =>
      obtain ⟨hne, hrank⟩ := ih
      have hI := kmswStage_boundary_chain_invariant w n
      have hURactive (hUR : (kmswStage w n).UR = []) :
          (kmswStage w n).east (kmswStage w n).active =
            (kmswStage w n).east ((kmswStage w n).LR.getLast hne) :=
        hI.2.2.2.2.2.2 hne hUR
      by_cases hleft : w n = 0
      · cases hstack : (kmswStage w n).UL.dropLast.reverse with
        | nil =>
          have hLR : (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
            simp [kmswStage, kmswStep, kmswCodeStep, hleft, hstack,
              kmswStepOfStep, State.addEdge]
          exact kmswStage_LR_last_rank_transfer w n hLR hne hrank
        | cons e es =>
          have hLR : (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
            simp [kmswStage, kmswStep, kmswCodeStep, hleft, hstack,
              kmswStepOfStep, State.addEdge]
          exact kmswStage_LR_last_rank_transfer w n hLR hne hrank
      · by_cases hup : w n = 1
        · have hLR : (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
            simp [kmswStage, kmswStep, kmswCodeStep, hup, kmswStepOfStep,
              State.addEdge]
          exact kmswStage_LR_last_rank_transfer w n hLR hne hrank
        · have hdown : w n = 2 := by
            apply Fin.ext
            have hv := (w n).isLt
            have hn0 : (w n).val ≠ 0 := fun h => hleft (Fin.ext h)
            have hn1 : (w n).val ≠ 1 := fun h => hup (Fin.ext h)
            omega
          cases hUR : (kmswStage w n).UR with
          | nil =>
            have hURnil : (kmswStage w n).UR = [] := hUR
            have hLR : (kmswStage w (n + 1)).LR =
                (kmswStage w n).LR ++ [(kmswStage w n).nextEdge] := by
              simp [kmswStage, kmswStep, kmswCodeStep, hdown, hURnil,
                kmswStepOfStep, State.addEdge]
            have hnewEast : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
                (kmswStage w n).nextVertex := by
              simp [kmswStage, kmswStep, kmswCodeStep, hdown, hURnil, kmswStepOfStep,
                State.addEdge]
            have hnewRank : kmswStageRank w (n + 1) (kmswStage w n).nextVertex =
                kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) + 1 := by
              simp [kmswStageRank, hdown, hURnil]
            have hnewne :
                (kmswStage w (n + 1)).LR ≠ [] := by rw [hLR]; simp
            have hnewlast :
                (kmswStage w (n + 1)).LR.getLast hnewne = (kmswStage w n).nextEdge := by
              simp only [hLR, List.getLast_append_singleton]
            refine ⟨hnewne, ?_⟩
            calc
              kmswStageRank w (n + 1)
                  ((kmswStage w (n + 1)).east
                    ((kmswStage w (n + 1)).LR.getLast hnewne)) =
                  kmswStageRank w (n + 1)
                    ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge) := by
                      rw [hnewlast]
              _ = kmswStageRank w (n + 1) (kmswStage w n).nextVertex := by
                    rw [hnewEast]
              _ = kmswStageRank w n
                    ((kmswStage w n).east (kmswStage w n).active) + 1 := hnewRank
              _ = kmswStageRank w n
                    ((kmswStage w n).east ((kmswStage w n).LR.getLast hne)) + 1 := by
                    rw [hURactive hUR]
              _ = ((kmswStage w n).LR.length : ℚ) + 1 := by rw [hrank]
              _ = ((kmswStage w (n + 1)).LR.length : ℚ) := by
                    rw [hLR]
                    simp
          | cons e es =>
            have hLR : (kmswStage w (n + 1)).LR = (kmswStage w n).LR := by
              simp [kmswStage, kmswStep, kmswCodeStep, hdown, hUR,
                kmswStepOfStep]
            exact kmswStage_LR_last_rank_transfer w n hLR hne hrank

/-- The horizontal extent of each certified stage is its lower-right edge count.
Helper toward adjudication n308; not a paper result. See `def-kmsw`, -/
private theorem monotoneStage_xmax_eq_LR_length {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (G n).xmax = ((kmswStage w n).LR.length : ℝ) := by
  obtain ⟨hne, hrank⟩ := kmswStage_LR_last_rank_eq_length w n
  let s := kmswStage w n
  let lower := s.LL ++ s.LR
  have hlowerne : lower ≠ [] := List.append_ne_nil_of_right_ne_nil _ hne
  have hupperne := (kmswStage_boundary_nonempty w n).1
  have hboundary := (kmswStage_boundary_endpoints w n).2
  have hboundary' : s.east ((s.UL ++ s.UR).getLast hupperne) =
      s.east (lower.getLast hlowerne) := by
    simpa only [s, lower] using hboundary
  have hlast : lower.getLast hlowerne = s.LR.getLast hne := by
    dsimp [lower]
    exact List.getLast_append_of_right_ne_nil _ _ hne
  rw [(G n).xmax_eq_upper_end]
  change (layoutPos w n (s.east ((s.UL ++ s.UR).getLast hupperne))).re = _
  rw [hboundary', hlast]
  change (kmswStageRank w n (s.east (s.LR.getLast hne)) : ℝ) = _
  exact_mod_cast hrank

/-- Under unbounded downward vertical motion, the certified stage widths diverge.
Helper toward adjudication n308; not a paper result. See `def-kmsw`, -/
theorem monotoneStage_xmax_unbounded {w : ℕ → Fin 3}
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    ∀ b : ℝ, ∃ N, ∀ n, N ≤ n → b ≤ (G n).xmax := by
  intro b
  obtain ⟨k, hk⟩ := exists_nat_gt b
  obtain ⟨N, hN⟩ := hR (-(k : ℤ))
  refine ⟨N, fun n hn => ?_⟩
  have hmin : minR w n ≤ -(k : ℤ) := by
    have h := runningMin_le (R w) n N hn
    change minR w n ≤ R w N at h
    exact h.trans (hN)
  have hlength : ((k : ℤ) + 1) ≤ ((kmswStage w n).LR.length : ℤ) := by
    rw [kmswStage_LR_length]
    omega
  have hlength' : (k : ℝ) + 1 ≤ ((kmswStage w n).LR.length : ℝ) := by
    exact_mod_cast hlength
  rw [monotoneStage_xmax_eq_LR_length Q G n]
  linarith

/-- On each bounded set, from some stage on, every point of the set is either in that
stage's region or in no stage region (boundary stabilization). Discharged in
`MonotoneExteriorExhaustion.lean` under `hfin`, `htrans`, `hR` and `hL0`.
Helper toward adjudication n308; not a paper result. -/
@[expose] def monotoneRegionBoundedExhaustion {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) : Prop :=
  ∀ K : Set ℂ, Bornology.IsBounded K →
    ∃ N, ∀ n, N ≤ n → ∀ z, z ∈ K →
      z ∈ monotoneStageRegion Q G n ∨ ∀ m, z ∉ monotoneStageRegion Q G m




theorem monotoneStageRegion_isClosed {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    IsClosed (monotoneStageRegion Q G n) := by
  exact isClosed_closedGraphRegion (G n).lower_continuous (G n).upper_continuous






theorem monotoneStageRegion_subset_of_le {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hnest : ∀ n, monotoneStageRegion Q G n ⊆ monotoneStageRegion Q G (n + 1))
    {m n : ℕ} (hmn : m ≤ n) : monotoneStageRegion Q G m ⊆ monotoneStageRegion Q G n := by
  induction hmn with
  | refl => exact subset_rfl
  | @step n hmn ih => exact ih.trans (hnest n)

/-- KMSW stage regions are nested at all earlier indices. Despite its name it uses no KMSW
hypotheses: nesting follows from the stage invariants alone. Helper toward adjudication n308; -/
theorem monotoneStageRegion_subset_of_le_fromKMSWHypotheses {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {m n : ℕ} (hmn : m ≤ n) :
    monotoneStageRegion Q G m ⊆ monotoneStageRegion Q G n := by
  change closedGraphRegion (G m).xmin (G m).xmax (G m).lower (G m).upper ⊆
    closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper
  exact monotone_region_mono_of_le w Q G hmn





theorem monotoneStageRegionUnion_inter_eq_stage {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hnest : ∀ n, monotoneStageRegion Q G n ⊆ monotoneStageRegion Q G (n + 1))
    (hbounded : monotoneRegionBoundedExhaustion Q G)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    ∃ N, monotoneStageRegionUnion Q G ∩ K = monotoneStageRegion Q G N ∩ K := by
  obtain ⟨N, hN⟩ := hbounded K hK
  refine ⟨N, ?_⟩
  ext z
  constructor
  · rintro ⟨hzUnion, hzK⟩
    obtain ⟨m, hzm⟩ := mem_iUnion.mp hzUnion
    by_cases hmn : m ≤ N
    · exact ⟨monotoneStageRegion_subset_of_le Q G hnest hmn hzm, hzK⟩
    · have hstable := hN N le_rfl z hzK
      rcases hstable with hzN | hnever
      · exact ⟨hzN, hzK⟩
      · exact (hnever m hzm).elim
  · rintro ⟨hzN, hzK⟩
    exact ⟨mem_iUnion.mpr ⟨N, hzN⟩, hzK⟩





theorem monotoneLimitExterior_isOpen_of_boundedExhaustion {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hbounded : monotoneRegionBoundedExhaustion Q G) :
    IsOpen (monotoneLimitExterior Q G) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hzOut : z ∉ monotoneStageRegionUnion Q G := hz
  obtain ⟨N, hN⟩ := hbounded (Metric.closedBall z 1) Metric.isBounded_closedBall
  have hzK : z ∈ Metric.closedBall z 1 := Metric.mem_closedBall_self (by norm_num)
  have hclass := hN N le_rfl z hzK
  have hzN : z ∉ monotoneStageRegion Q G N := by
    intro hzN
    exact hzOut (mem_iUnion.mpr ⟨N, hzN⟩)
  have hnever : ∀ m, z ∉ monotoneStageRegion Q G m := by
    rcases hclass with hzN' | hnever
    · exact (hzN hzN').elim
    · exact hnever
  have hneighborhood :
      Metric.ball z 1 ∩ (monotoneStageRegion Q G N)ᶜ ∈ 𝓝 z := by
    apply (Metric.isOpen_ball.inter (monotoneStageRegion_isClosed Q G N).isOpen_compl).mem_nhds
    exact ⟨Metric.mem_ball_self one_pos, hzN⟩
  apply Filter.mem_of_superset hneighborhood
  intro y hy
  change y ∉ monotoneStageRegionUnion Q G
  intro hyUnion
  obtain ⟨m, hym⟩ := mem_iUnion.mp hyUnion
  have hyK : y ∈ Metric.closedBall z 1 := Metric.ball_subset_closedBall hy.1
  have hyClass := hN N le_rfl y hyK
  rcases hyClass with hyN | hyNever
  · exact hy.2 hyN
  · exact hyNever m hym





theorem monotoneLimitExterior_disjoint_stageImage {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    Disjoint (monotoneLimitExterior Q G) (Q n).image := by
  rw [Set.disjoint_left]
  intro z hzE hzI
  apply hzE
  refine mem_iUnion.2 ⟨n, ?_⟩
  have hcover := (G n).toMonotoneStageCertificate.cover
  change z ∈ closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper
  rw [← hcover]
  exact Or.inl hzI

private theorem monotoneStageEdgeTrace_subset_image {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (e : ℕ) : stageEdgeTrace P e ⊆ P.image := by
  unfold stageEdgeTrace
  split
  · intro z hz
    exact Or.inr ⟨_, hz⟩
  · exact empty_subset _

private theorem monotoneStageCap_frontier_subset_image {w : ℕ → Fin 3} {n : ℕ}
    {Q : StageDrawing w n} (G : MonotoneStageInvariant w n Q)
    (i : Fin (kmswStage w n).triangles.length) :
    frontier (G.cap i).region ⊆ Q.image := by
  change frontier (graphRegion _ _ _ _) ⊆ _
  rw [frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
    (G.cap i).left_join (G.cap i).right_join]
  rw [G.toMonotoneStageCertificate.cap_lower_trace i,
    G.toMonotoneStageCertificate.cap_upper_trace i]
  rintro z (hz | hz)
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact monotoneStageEdgeTrace_subset_image e hz
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact monotoneStageEdgeTrace_subset_image e hz





theorem monotoneStageRegion_mem_capClosure_of_not_trace {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {z : ℂ}
    (hz : z ∈ monotoneStageRegionUnion Q G)
    (hout : z ∉ monotoneLayoutTraceUnion Q) :
    ∃ n i, z ∈ closure ((G n).cap i).region := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  have hcover := (G n).toMonotoneStageCertificate.cover
  change z ∈ closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper at hn
  rw [← hcover] at hn
  rcases hn with himage | hcaps
  · exact (hout (mem_iUnion.mpr ⟨n, himage⟩)).elim
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hcaps
    exact ⟨n, i, hi⟩




theorem monotoneStageRegion_frontier_subset_image {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    frontier (monotoneStageRegion Q G n) ⊆ (Q n).image := by
  intro z hz
  have hcover := (G n).toMonotoneStageCertificate.cover
  have hclosed := monotoneStageRegion_isClosed Q G n
  have hzR : z ∈ monotoneStageRegion Q G n := by
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hz
  change z ∈ closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper at hzR
  rw [← hcover] at hzR
  rcases hzR with hzImage | hzCaps
  · exact hzImage
  · obtain ⟨i, hzCapClosure⟩ := mem_iUnion.mp hzCaps
    by_cases hzCap : z ∈ ((G n).cap i).region
    · have hcapSub : ((G n).cap i).region ⊆ monotoneStageRegion Q G n := by
        intro y hy
        have hycl : y ∈ closure ((G n).cap i).region := subset_closure hy
        have hycover : y ∈ (Q n).image ∪
            ⋃ j, closure ((G n).cap j).region := Or.inr (mem_iUnion.mpr ⟨i, hycl⟩)
        change y ∈ closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper
        rw [← hcover]
        exact hycover
      have hopen : IsOpen ((G n).cap i).region :=
        isOpen_graphRegion ((G n).cap i).low_continuous
          ((G n).cap i).high_continuous
      have hint : z ∈ interior (monotoneStageRegion Q G n) :=
        interior_maximal hcapSub hopen hzCap
      exact False.elim ((Set.disjoint_left.mp disjoint_interior_frontier) hint hz)
    · have hopen : IsOpen ((G n).cap i).region :=
        isOpen_graphRegion ((G n).cap i).low_continuous
          ((G n).cap i).high_continuous
      have hzFront : z ∈ frontier ((G n).cap i).region := by
        rw [frontier, hopen.interior_eq]
        exact ⟨hzCapClosure, hzCap⟩
      exact monotoneStageCap_frontier_subset_image (G n) i hzFront





theorem monotoneStageRegionUnion_mem_cap_of_not_trace {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {z : ℂ}
    (hz : z ∈ monotoneStageRegionUnion Q G)
    (hout : z ∉ monotoneLayoutTraceUnion Q) :
    ∃ n i, z ∈ ((G n).cap i).region := by
  obtain ⟨n, i, hzCapClosure⟩ := monotoneStageRegion_mem_capClosure_of_not_trace
    Q G hz hout
  by_cases hzCap : z ∈ ((G n).cap i).region
  · exact ⟨n, i, hzCap⟩
  · have hopen : IsOpen ((G n).cap i).region :=
      isOpen_graphRegion ((G n).cap i).low_continuous ((G n).cap i).high_continuous
    have hzFront : z ∈ frontier ((G n).cap i).region := by
      rw [frontier, hopen.interior_eq]
      exact ⟨hzCapClosure, hzCap⟩
    have hzImage := monotoneStageCap_frontier_subset_image (G n) i hzFront
    exact (hout (mem_iUnion.mpr ⟨n, hzImage⟩)).elim





theorem monotoneLimitExterior_frontier_subset_trace {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hbounded : monotoneRegionBoundedExhaustion Q G) :
    frontier (monotoneLimitExterior Q G) ⊆ monotoneLayoutTraceUnion Q := by
  have hopen := monotoneLimitExterior_isOpen_of_boundedExhaustion Q G hbounded
  intro z hz
  rw [frontier, hopen.interior_eq] at hz
  have hzClosure := hz.1
  have hzNotExterior := hz.2
  have hzUnion : z ∈ monotoneStageRegionUnion Q G := by
    change z ∉ (monotoneStageRegionUnion Q G)ᶜ at hzNotExterior
    exact not_not.mp hzNotExterior
  obtain ⟨n, hzn⟩ := mem_iUnion.mp hzUnion
  have hnotInterior : z ∉ interior (monotoneStageRegion Q G n) := by
    intro hzInterior
    have hnonempty := (_root_.mem_closure_iff.mp hzClosure)
      (interior (monotoneStageRegion Q G n)) isOpen_interior hzInterior
    obtain ⟨y, hyInterior, hyExterior⟩ := hnonempty
    exact hyExterior (mem_iUnion.mpr ⟨n, interior_subset hyInterior⟩)
  have hzFront : z ∈ frontier (monotoneStageRegion Q G n) := by
    rw [(monotoneStageRegion_isClosed Q G n).frontier_eq]
    exact ⟨hzn, hnotInterior⟩
  exact mem_iUnion.mpr ⟨n, monotoneStageRegion_frontier_subset_image Q G n hzFront⟩






theorem monotoneLimitExterior_unbounded_of_xmin_zero {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hxmin : ∀ n, (G n).xmin = 0) (R : ℝ) :
    ∃ z ∈ monotoneLimitExterior Q G, R < ‖z‖ := by
  let x : ℝ := -(|R| + 1)
  refine ⟨(x : ℂ), ?_, ?_⟩
  · change (x : ℂ) ∉ ⋃ n, monotoneStageRegion Q G n
    intro hmem
    obtain ⟨n, hz⟩ := mem_iUnion.mp hmem
    have hx := hz.1
    rw [hxmin n] at hx
    have hxneg : x < 0 := by
      have hp : 0 < |R| + 1 := by positivity
      dsimp [x]
      linarith
    exact (not_le_of_gt hxneg) (by simpa using hx)
  · have hn : ‖(x : ℂ)‖ = |R| + 1 := by
      have hxnonpos : x ≤ 0 := by
        have hp : 0 ≤ |R| + 1 := by positivity
        dsimp [x]
        linarith
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hxnonpos]
      dsimp [x]
      ring
    calc
      R ≤ |R| := le_abs_self R
      _ < |R| + 1 := by linarith
      _ = ‖(x : ℂ)‖ := hn.symm





@[expose] def monotoneExteriorSectors (lower upper : ℝ → ℝ) (upperDomain : Set ℝ) :
    Set ℂ :=
  {z | z.re < 0} ∪ ({z | 0 ≤ z.re ∧ z.im < lower z.re} ∪
    {z | z.re ∈ upperDomain ∧ upper z.re < z.im})


private theorem monotoneExteriorSectors_join_base {lower upper : ℝ → ℝ}
    {upperDomain : Set ℝ} (hlower : Continuous lower) (hupper : Continuous upper)
    (hdom_nonneg : ∀ x ∈ upperDomain, 0 ≤ x)
    (hdom_down : ∀ x ∈ upperDomain, ∀ y ∈ Icc 0 x, y ∈ upperDomain)
    {z : ℂ} (hz : z ∈ monotoneExteriorSectors lower upper upperDomain) :
    JoinedIn (monotoneExteriorSectors lower upper upperDomain) z (-1 : ℂ) := by
  let S := monotoneExteriorSectors lower upper upperDomain
  have hz' : z ∈ {q : ℂ | q.re < 0} ∪
      ({q | 0 ≤ q.re ∧ q.im < lower q.re} ∪
        {q | q.re ∈ upperDomain ∧ upper q.re < q.im}) := by
    simpa only [monotoneExteriorSectors] using hz
  rcases hz' with hzWest | hzRest
  · apply JoinedIn.of_segment_subset
    intro q hq
    apply Or.inl
    exact (convex_halfSpace_re_lt 0).segment_subset hzWest (by simp) hq
  · rcases hzRest with hzLower | hzUpper
    · let x := z.re
      have hx : 0 ≤ x := by simpa [x] using hzLower.1
      have hf : ContinuousOn lower (Icc 0 x) := hlower.continuousOn
      obtain ⟨M, hM⟩ :=
        (isCompact_Icc.image_of_continuousOn hf).isBounded.subset_closedBall (0 : ℝ)
      let c := -(M + |z.im| + 1)
      let p : ℂ := ⟨x, c⟩
      let b : ℂ := ⟨-1, c⟩
      have hcM : c < -M := by
        have ha := abs_nonneg z.im
        dsimp [c]
        linarith
      have hcGraph : c < lower x := by
        have hzero : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
        have hm : |lower x| ≤ M := by
          have hball := hM ⟨x, hzero, rfl⟩
          simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hball
        exact lt_of_lt_of_le hcM (abs_le.mp hm).1
      have hvertical : JoinedIn S z p := by
        apply JoinedIn.of_segment_subset
        intro q hq
        have hqLe :=
          (convex_halfSpace_re_le x).segment_subset (by simp [x]) (by simp [p]) hq
        have hqGe :=
          (convex_halfSpace_re_ge x).segment_subset (by simp [x]) (by simp [p]) hq
        have hqRe : q.re = x := le_antisymm hqLe hqGe
        have hqNonneg : 0 ≤ q.re := hqRe ▸ hx
        have hzIm : z.im < lower x := by simpa [x] using hzLower.2
        have hpIm : p.im < lower x := by simpa [p] using hcGraph
        have hqIm :=
          (convex_halfSpace_im_lt (lower x)).segment_subset hzIm hpIm hq
        change q ∈ {q : ℂ | q.re < 0} ∪
          ({q | 0 ≤ q.re ∧ q.im < lower q.re} ∪
            {q | q.re ∈ upperDomain ∧ upper q.re < q.im})
        exact Or.inr (Or.inl ⟨hqNonneg, by simpa [hqRe] using hqIm⟩)
      have hhorizontal : JoinedIn S p b := by
        apply JoinedIn.of_segment_subset
        intro q hq
        have hpRe : p.re ≤ x := by simp [p]
        have hbRe : b.re ≤ x := by
          change -1 ≤ x
          linarith
        have hqRe := (convex_halfSpace_re_le x).segment_subset hpRe hbRe hq
        have hpImLe : p.im ≤ c := by simp [p]
        have hbImLe : b.im ≤ c := by simp [b]
        have hpImGe : c ≤ p.im := by simp [p]
        have hbImGe : c ≤ b.im := by simp [b]
        have hqImLe := (convex_halfSpace_im_le c).segment_subset hpImLe hbImLe hq
        have hqImGe := (convex_halfSpace_im_ge c).segment_subset hpImGe hbImGe hq
        have hqIm : q.im = c := le_antisymm hqImLe hqImGe
        by_cases hqWest : q.re < 0
        · change q ∈ {q : ℂ | q.re < 0} ∪ _
          exact Or.inl hqWest
        · have hqNonneg : 0 ≤ q.re := le_of_not_gt hqWest
          have hqi : q.re ∈ Icc 0 x := ⟨hqNonneg, hqRe⟩
          have hm : |lower q.re| ≤ M := by
            have hball := hM ⟨q.re, hqi, rfl⟩
            simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hball
          have hcGraph' : c < lower q.re := lt_of_lt_of_le hcM (abs_le.mp hm).1
          change q ∈ {q : ℂ | q.re < 0} ∪ _
          exact Or.inr (Or.inl ⟨hqNonneg, by rw [hqIm]; exact hcGraph'⟩)
      have hwest : JoinedIn S b (-1 : ℂ) := by
        apply JoinedIn.of_segment_subset
        intro q hq
        change q ∈ monotoneExteriorSectors lower upper upperDomain
        exact Or.inl ((convex_halfSpace_re_lt 0).segment_subset (by simp [b])
          (by simp) hq)
      exact hvertical.trans (hhorizontal.trans hwest)
    · let x := z.re
      have hx : 0 ≤ x := hdom_nonneg x hzUpper.1
      have hf : ContinuousOn upper (Icc 0 x) := hupper.continuousOn
      obtain ⟨M, hM⟩ :=
        (isCompact_Icc.image_of_continuousOn hf).isBounded.subset_closedBall (0 : ℝ)
      let c := M + |z.im| + 1
      let p : ℂ := ⟨x, c⟩
      let b : ℂ := ⟨-1, c⟩
      have hcM : M < c := by
        have ha := abs_nonneg z.im
        dsimp [c]
        linarith
      have hcGraph : upper x < c := by
        have hzero : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
        have hm : |upper x| ≤ M := by
          have hball := hM ⟨x, hzero, rfl⟩
          simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hball
        calc
          upper x ≤ |upper x| := le_abs_self _
          _ ≤ M := hm
          _ < c := hcM
      have hvertical : JoinedIn S z p := by
        apply JoinedIn.of_segment_subset
        intro q hq
        have hqLe :=
          (convex_halfSpace_re_le x).segment_subset (by simp [x]) (by simp [p]) hq
        have hqGe :=
          (convex_halfSpace_re_ge x).segment_subset (by simp [x]) (by simp [p]) hq
        have hqRe : q.re = x := le_antisymm hqLe hqGe
        have hqDomain : q.re ∈ upperDomain := by simpa [hqRe, x] using hzUpper.1
        have hzIm : upper x < z.im := by simpa [x] using hzUpper.2
        have hpIm : upper x < p.im := by simpa [p] using hcGraph
        have hqIm :=
          (convex_halfSpace_im_gt (upper x)).segment_subset hzIm hpIm hq
        change q ∈ {q : ℂ | q.re < 0} ∪
          ({q | 0 ≤ q.re ∧ q.im < lower q.re} ∪
            {q | q.re ∈ upperDomain ∧ upper q.re < q.im})
        exact Or.inr (Or.inr ⟨hqDomain, by simpa [hqRe] using hqIm⟩)
      have hhorizontal : JoinedIn S p b := by
        apply JoinedIn.of_segment_subset
        intro q hq
        have hpRe : p.re ≤ x := by simp [p]
        have hbRe : b.re ≤ x := by
          change -1 ≤ x
          linarith
        have hqRe := (convex_halfSpace_re_le x).segment_subset hpRe hbRe hq
        have hpImLe : p.im ≤ c := by simp [p]
        have hbImLe : b.im ≤ c := by simp [b]
        have hpImGe : c ≤ p.im := by simp [p]
        have hbImGe : c ≤ b.im := by simp [b]
        have hqImLe := (convex_halfSpace_im_le c).segment_subset hpImLe hbImLe hq
        have hqImGe := (convex_halfSpace_im_ge c).segment_subset hpImGe hbImGe hq
        have hqIm : q.im = c := le_antisymm hqImLe hqImGe
        by_cases hqWest : q.re < 0
        · change q ∈ {q : ℂ | q.re < 0} ∪ _
          exact Or.inl hqWest
        · have hqNonneg : 0 ≤ q.re := le_of_not_gt hqWest
          have hqi : q.re ∈ Icc 0 x := ⟨hqNonneg, hqRe⟩
          have hqDomain : q.re ∈ upperDomain := hdom_down x hzUpper.1 q.re hqi
          have hm : |upper q.re| ≤ M := by
            have hball := hM ⟨q.re, hqi, rfl⟩
            simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hball
          have hcGraph' : upper q.re < c := by
            calc
              upper q.re ≤ |upper q.re| := le_abs_self _
              _ ≤ M := hm
              _ < c := hcM
          change q ∈ {q : ℂ | q.re < 0} ∪ _
          exact Or.inr (Or.inr ⟨hqDomain, by rw [hqIm]; exact hcGraph'⟩)
      have hwest : JoinedIn S b (-1 : ℂ) := by
        apply JoinedIn.of_segment_subset
        intro q hq
        apply Or.inl
        exact (convex_halfSpace_re_lt 0).segment_subset (by simp [b]) (by simp) hq
      exact hvertical.trans (hhorizontal.trans hwest)





theorem monotoneExteriorSectors_isPathConnected {lower upper : ℝ → ℝ}
    {upperDomain : Set ℝ} (hlower : Continuous lower) (hupper : Continuous upper)
    (hdom_nonneg : ∀ x ∈ upperDomain, 0 ≤ x)
    (hdom_down : ∀ x ∈ upperDomain, ∀ y ∈ Icc 0 x, y ∈ upperDomain) :
    IsPathConnected (monotoneExteriorSectors lower upper upperDomain) := by
  apply isPathConnected_iff.mpr
  have hbase : (-1 : ℂ) ∈ monotoneExteriorSectors lower upper upperDomain := by
    simp [monotoneExteriorSectors]
  refine ⟨⟨-1, hbase⟩, ?_⟩
  intro x hx y hy
  exact (monotoneExteriorSectors_join_base hlower hupper hdom_nonneg hdom_down hx).trans
    (monotoneExteriorSectors_join_base hlower hupper hdom_nonneg hdom_down hy).symm

end DirectedDistances.KMSW
