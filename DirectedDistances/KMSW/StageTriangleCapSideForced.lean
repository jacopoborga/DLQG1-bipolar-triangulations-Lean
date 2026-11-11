module

public import DirectedDistances.KMSW.StageTriangleCapSideProof

import all DirectedDistances.KMSW.StageTriangleCapSide
import all DirectedDistances.KMSW.MonotoneStepAll
import all DirectedDistances.KMSW.MonotoneFamilyFaceData

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

private theorem cap_low_le_high (C : GraphCap) {x : ℝ} (hx : x ∈ Icc C.a C.b) :
    C.low x ≤ C.high x := by
  by_cases ha : x = C.a
  · subst x
    exact C.left_join.le
  by_cases hb : x = C.b
  · subst x
    exact C.right_join.le
  exact (C.separated x ⟨lt_of_le_of_ne hx.1 (Ne.symm ha),
    lt_of_le_of_ne hx.2 hb⟩).le

private theorem cap_lower_graph_subset (C C' : GraphCap)
    (h : graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high =
      graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high) :
    graphOver C.a C.b C.low ⊆ graphOver C'.a C'.b C'.low := by
  intro z hz
  have hz' : z ∈ graphOver C'.a C'.b C'.low ∪
      graphOver C'.a C'.b C'.high := by
    rw [← h]
    exact Or.inl hz
  rcases hz' with hz' | hz'
  · exact hz'
  · let q := graphParam C'.low z.re
    have hq : q ∈ graphOver C'.a C'.b C'.low := by
      simpa [q, graphParam, graphOver] using And.intro hz'.1 hz'.2.1
    have hq' : q ∈ graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high := by
      rw [h]
      exact Or.inl hq
    have hqim : q.im = C'.low z.re := by simp [q, graphParam]
    have hqre : q.re = z.re := by simp [q, graphParam]
    have hle : C.low z.re ≤ C'.low z.re := by
      rcases hq' with hq' | hq'
      · rw [← hqim, hq'.2.2, hqre]
      · rw [← hqim, hq'.2.2, hqre]
        exact cap_low_le_high C ⟨hz.1, hz.2.1⟩
    refine ⟨hz'.1, hz'.2.1, le_antisymm ?_ ?_⟩
    · rw [hz.2.2]
      exact hle
    · rw [hz'.2.2]
      exact cap_low_le_high C' ⟨hz'.1, hz'.2.1⟩

private theorem cap_upper_graph_subset (C C' : GraphCap)
    (h : graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high =
      graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high) :
    graphOver C.a C.b C.high ⊆ graphOver C'.a C'.b C'.high := by
  intro z hz
  have hz' : z ∈ graphOver C'.a C'.b C'.low ∪
      graphOver C'.a C'.b C'.high := by
    rw [← h]
    exact Or.inr hz
  rcases hz' with hz' | hz'
  · let q := graphParam C'.high z.re
    have hq : q ∈ graphOver C'.a C'.b C'.high := by
      simpa [q, graphParam, graphOver] using And.intro hz'.1 hz'.2.1
    have hq' : q ∈ graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high := by
      rw [h]
      exact Or.inr hq
    have hqim : q.im = C'.high z.re := by simp [q, graphParam]
    have hqre : q.re = z.re := by simp [q, graphParam]
    have hle : C'.high z.re ≤ C.high z.re := by
      rcases hq' with hq' | hq'
      · rw [← hqim, hq'.2.2, hqre]
        exact cap_low_le_high C ⟨hz.1, hz.2.1⟩
      · rw [← hqim, hq'.2.2, hqre]
    refine ⟨hz'.1, hz'.2.1, le_antisymm ?_ ?_⟩
    · rw [hz'.2.2]
      exact cap_low_le_high C' ⟨hz'.1, hz'.2.1⟩
    · rw [hz.2.2]
      exact hle
  · exact hz'

private theorem invariant_trace_eq {w : ℕ → Fin 3} {n : ℕ}
    {P P' : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (G' : MonotoneStageInvariant w n P') (e : ℕ) :
    stageEdgeTrace P e = stageEdgeTrace P' e := by
  unfold stageEdgeTrace
  split
  · congr 1
    rw [G.arc_layout, G'.arc_layout]
  · rfl

private theorem invariant_cap_boundary_eq {w : ℕ → Fin 3} {n : ℕ}
    {P P' : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (G' : MonotoneStageInvariant w n P')
    (i k : Fin (kmswStage w n).triangles.length)
    (ht : (kmswStage w n).triangles.get i = (kmswStage w n).triangles.get k) :
    graphOver (G.cap i).a (G.cap i).b (G.cap i).low ∪
        graphOver (G.cap i).a (G.cap i).b (G.cap i).high =
      graphOver (G'.cap k).a (G'.cap k).b (G'.cap k).low ∪
        graphOver (G'.cap k).a (G'.cap k).b (G'.cap k).high := by
  have hmem (H : MonotoneStageInvariant w n P)
      (j : Fin (kmswStage w n).triangles.length) (z : ℂ) :
      z ∈ graphOver (H.cap j).a (H.cap j).b (H.cap j).low ∪
          graphOver (H.cap j).a (H.cap j).b (H.cap j).high ↔
        ∃ e, e ∈ H.capLower j ++ H.capUpper j ∧ z ∈ stageEdgeTrace P e := by
    rw [H.cap_lower_trace, H.cap_upper_trace]
    simp only [mem_union, mem_iUnion, List.mem_append]
    aesop
  have htrace : ∀ e, stageEdgeTrace P' e = stageEdgeTrace P e :=
    fun e => (invariant_trace_eq G G' e).symm
  ext z
  rw [hmem G i z, G'.cap_lower_trace, G'.cap_upper_trace]
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro ⟨e, he, hz⟩
    have he' : e ∈ G'.capLower k ++ G'.capUpper k := by
      rw [G'.cap_edges, ← ht]
      exact (G.cap_edges i e).mp he
    rw [← htrace e] at hz
    rcases List.mem_append.mp he' with he' | he'
    · exact Or.inl ⟨e, he', hz⟩
    · exact Or.inr ⟨e, he', hz⟩
  · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
    · refine ⟨e, ?_, by rwa [htrace e] at hz⟩
      rw [G.cap_edges, ht]
      exact (G'.cap_edges k e).mp (List.mem_append.mpr (Or.inl he))
    · refine ⟨e, ?_, by rwa [htrace e] at hz⟩
      rw [G.cap_edges, ht]
      exact (G'.cap_edges k e).mp (List.mem_append.mpr (Or.inr he))

private theorem layout_trace_not_both (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) (C : GraphCap) :
    ¬ ((layoutArc w n e).image ⊆ graphOver C.a C.b C.low ∧
      (layoutArc w n e).image ⊆ graphOver C.a C.b C.high) := by
  rintro ⟨hl, hu⟩
  let a := (layoutPos w n ((kmswStage w n).west e)).re
  let b := (layoutPos w n ((kmswStage w n).east e)).re
  have hab : a < b := by
    change (kmswStageRank w n ((kmswStage w n).west e) : ℝ) <
      (kmswStageRank w n ((kmswStage w n).east e) : ℝ)
    exact_mod_cast kmswStageRank_strict w n e he
  obtain ⟨f, hf⟩ := layoutArc_image_graph w n e he
  have hpoint (x : ℝ) (hx : a ≤ x ∧ x ≤ b) :
      graphParam f x ∈ (layoutArc w n e).image := by
    rw [hf]
    simpa [graphParam] using hx
  have ha := hl (hpoint a ⟨le_rfl, hab.le⟩)
  have hb := hl (hpoint b ⟨hab.le, le_rfl⟩)
  have hm := hpoint ((a + b) / 2) ⟨by linarith, by linarith⟩
  have hml := hl hm
  have hmu := hu hm
  have ha' : C.a ≤ a := by simpa [graphParam] using ha.1
  have hb' : b ≤ C.b := by simpa [graphParam] using hb.2.1
  have hmid : (graphParam f ((a + b) / 2)).re ∈ Ioo C.a C.b := by
    simp only [graphParam, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      add_zero]
    constructor <;> linarith
  have hsep := C.separated _ hmid
  rw [← hml.2.2, ← hmu.2.2] at hsep
  exact (lt_irrefl _ hsep)

private theorem cap_side_transfer {w : ℕ → Fin 3} {n : ℕ}
    {P P' : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (G' : MonotoneStageInvariant w n P')
    (i k : Fin (kmswStage w n).triangles.length)
    (ht : (kmswStage w n).triangles.get i = (kmswStage w n).triangles.get k)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (e ∈ G.capLower i → e ∈ G'.capLower k) ∧
      (e ∈ G.capUpper i → e ∈ G'.capUpper k) := by
  have hboundary := invariant_cap_boundary_eq G G' i k ht
  have hlow := cap_lower_graph_subset (G.cap i) (G'.cap k) hboundary
  have hupp := cap_upper_graph_subset (G.cap i) (G'.cap k) hboundary
  have htrace : stageEdgeTrace P e = (layoutArc w n e).image := by
    simp only [stageEdgeTrace, dite_eq_left he, G.arc_layout, Bool.false_eq_true,
      ↓reduceIte]
  have htrace' : stageEdgeTrace P' e = (layoutArc w n e).image := by
    simp only [stageEdgeTrace, dite_eq_left he, G'.arc_layout, Bool.false_eq_true,
      ↓reduceIte]
  have hlower (H : MonotoneStageInvariant w n P') (hem : e ∈ H.capLower k) :
      stageEdgeTrace P' e ⊆ graphOver (H.cap k).a (H.cap k).b (H.cap k).low := by
    rw [H.cap_lower_trace]
    intro z hz
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hem, hz⟩⟩
  have hupper (H : MonotoneStageInvariant w n P') (hem : e ∈ H.capUpper k) :
      stageEdgeTrace P' e ⊆ graphOver (H.cap k).a (H.cap k).b (H.cap k).high := by
    rw [H.cap_upper_trace]
    intro z hz
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hem, hz⟩⟩
  constructor
  · intro hem
    have hunion : e ∈ G'.capLower k ++ G'.capUpper k := by
      rw [G'.cap_edges, ← ht]
      exact (G.cap_edges i e).mp (List.mem_append.mpr (Or.inl hem))
    rcases List.mem_append.mp hunion with hem' | hem'
    · exact hem'
    · exfalso
      apply layout_trace_not_both w n e he (G'.cap k)
      refine ⟨?_, ?_⟩
      · intro z hz
        apply hlow
        rw [G.cap_lower_trace]
        exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hem, by rwa [htrace]⟩⟩
      · simpa only [htrace'] using hupper G' hem'
  · intro hem
    have hunion : e ∈ G'.capLower k ++ G'.capUpper k := by
      rw [G'.cap_edges, ← ht]
      exact (G.cap_edges i e).mp (List.mem_append.mpr (Or.inr hem))
    rcases List.mem_append.mp hunion with hem' | hem'
    · exfalso
      apply layout_trace_not_both w n e he (G'.cap k)
      refine ⟨?_, ?_⟩
      · simpa only [htrace'] using hlower G' hem'
      · intro z hz
        apply hupp
        rw [G.cap_upper_trace]
        exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hem, by rwa [htrace]⟩⟩
    · exact hem'

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The side membership of each allocated cap edge is independent of the invariant -/
theorem MonotoneStageInvariant.cap_sides_mem_iff {w : ℕ → Fin 3} {n : ℕ}
    {P P' : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (G' : MonotoneStageInvariant w n P')
    (i k : Fin (kmswStage w n).triangles.length)
    (ht : (kmswStage w n).triangles.get i = (kmswStage w n).triangles.get k)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (e ∈ G.capLower i ↔ e ∈ G'.capLower k) ∧
      (e ∈ G.capUpper i ↔ e ∈ G'.capUpper k) := by
  have hf := cap_side_transfer G G' i k ht e he
  have hb := cap_side_transfer G' G k i ht.symm e he
  exact ⟨⟨hf.1, hb.1⟩, ⟨hf.2, hb.2⟩⟩

private theorem creation_triangles_append (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    (kmswStage w (j.val + 1)).triangles =
      (kmswStage w j.val).triangles ++ [stageTriangleRecord w j] := by
  rw [← stageTriangleTimes_records w (j.val + 1), stageTriangleTimes,
    dite_eq_left j.property, List.map_append, stageTriangleTimes_records]
  simp only [List.map_cons, List.map_nil]

private theorem creation_cap_sides_forced (w : ℕ → Fin 3) (j : TriangleCreationTime w)
    {P : StageDrawing w (j.val + 1)} (G : MonotoneStageInvariant w (j.val + 1) P)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    ∀ d ∈ stageTriangleDartList w j,
      (if d.2 then d.1 ∈ G.capUpper i else d.1 ∈ G.capLower i) := by
  have htris := creation_triangles_append w j
  let k : Fin (kmswStage w (j.val + 1)).triangles.length :=
    ⟨(kmswStage w j.val).triangles.length, by simp [htris]⟩
  have hk : ¬ k.val < (kmswStage w j.val).triangles.length := by
    exact Nat.lt_irrefl _
  have hki : (kmswStage w (j.val + 1)).triangles.get k = stageTriangleRecord w j := by
    simp only [List.get_eq_getElem, htris, k,
      List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
  let G₀ := familyG w (monotone_family_all w) j.val
  have transfer {P' : StageDrawing w (j.val + 1)}
      (G' : MonotoneStageInvariant w (j.val + 1) P')
      (hs : ∀ d ∈ stageTriangleDartList w j,
        if d.2 then d.1 ∈ G'.capUpper k else d.1 ∈ G'.capLower k) :
      ∀ d ∈ stageTriangleDartList w j,
        if d.2 then d.1 ∈ G.capUpper i else d.1 ∈ G.capLower i := by
    intro d hd
    have he := stageTriangleDartList_lt w (j.val + 1) j (by omega) d hd
    have hh := G'.cap_sides_mem_iff G k i (hki.trans hi.symm) d.1 he
    have hs' := hs d hd
    cases hb : d.2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs' ⊢
      exact hh.1.mp hs'
    · simp only [hb, ↓reduceIte] at hs' ⊢
      exact hh.2.mp hs'
  rcases j.property with hc | hc
  · cases hUL : (kmswStage w j.val).UL.dropLast.reverse with
    | nil =>
      let h := layoutGood_succ_lfr w j.val hc hUL G₀
      exact transfer (invariant_succ_lfr w j.val hc hUL G₀ h)
        (invariant_succ_lfr_new_cap_dart_sides w j hc hUL G₀ h k hk)
    | cons e es =>
      let h := layoutGood_succ_lex w j.val hc e es hUL G₀
      exact transfer (invariant_succ_lex w j.val hc e es hUL G₀ h)
        (invariant_succ_lex_new_cap_dart_sides w j hc e es hUL G₀ h k hk)
  · let h := layoutGood_succ_up w j.val hc G₀
    exact transfer (invariant_succ_up w j.val hc G₀ h)
      (invariant_succ_up_new_cap_dart_sides w j hc G₀ h k hk)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every monotone stage invariant has the creation dart side assignment forced by -/
theorem hasCreationCapDartSides_invariant (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    hasCreationCapDartSides w n G := by
  unfold hasCreationCapDartSides
  intro j hn
  subst n
  exact creation_cap_sides_forced w j G

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The chosen all-stage family has the forced creation dart sides. See -/
theorem hasCreationCapDartSides_familyG (w : ℕ → Fin 3) (n : ℕ) :
    hasCreationCapDartSides w n (familyG w (monotone_family_all w) n) :=
  hasCreationCapDartSides_invariant w n _

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every oriented creation dart borders its bounded limit cap face. See -/
theorem stageTriangleDarts_border_creation_cap (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    ∃ F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)),
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
        ∀ d ∈ stageTriangleDartList w j,
          (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders
            d F.val := by
  exact stageTriangleDarts_border_creation_cap_of_property w hfin j i hi
    (hasCreationCapDartSides_familyG w (j.val + 1))

end DirectedDistances.KMSW
