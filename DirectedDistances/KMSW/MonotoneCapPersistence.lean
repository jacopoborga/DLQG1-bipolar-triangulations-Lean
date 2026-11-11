module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.KMSW.MonotoneStageCertificate
public import DirectedDistances.KMSW.HatTriangleSim
public import DirectedDistances.PlanarMap.GraphRegion
public import DirectedDistances.PlanarMap.GraphRegionClosure

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem GraphCap.region_eq_of_boundary_eq (C C' : GraphCap)
    (h : graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high =
      graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high) :
    C.region = C'.region := by
  have hleft : C'.a ≤ C.a := by
    let z : ℂ := (C.a : ℂ) + (C.low C.a : ℂ) * Complex.I
    have hzre : z.re = C.a := by simp [z]
    have hz : z ∈ graphOver C.a C.b C.low := by
      simp [graphOver, z, C.ab.le]
    have hz' : z ∈ graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inl hz
    rcases hz' with hz' | hz'
    · calc
        C'.a ≤ z.re := hz'.1
        _ = C.a := hzre
    · calc
        C'.a ≤ z.re := hz'.1
        _ = C.a := hzre
  have hleft' : C.a ≤ C'.a := by
    let z : ℂ := (C'.a : ℂ) + (C'.low C'.a : ℂ) * Complex.I
    have hzre : z.re = C'.a := by simp [z]
    have hz : z ∈ graphOver C'.a C'.b C'.low := by
      simp [graphOver, z, C'.ab.le]
    have hz' : z ∈ graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high := by
      rw [h]
      exact Or.inl hz
    rcases hz' with hz' | hz'
    · calc
        C.a ≤ z.re := hz'.1
        _ = C'.a := hzre
    · calc
        C.a ≤ z.re := hz'.1
        _ = C'.a := hzre
  have hright : C.b ≤ C'.b := by
    let z : ℂ := (C.b : ℂ) + (C.low C.b : ℂ) * Complex.I
    have hzre : z.re = C.b := by simp [z]
    have hz : z ∈ graphOver C.a C.b C.low := by
      simp [graphOver, z, C.ab.le]
    have hz' : z ∈ graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inl hz
    rcases hz' with hz' | hz'
    · calc
        C.b = z.re := hzre.symm
        _ ≤ C'.b := hz'.2.1
    · calc
        C.b = z.re := hzre.symm
        _ ≤ C'.b := hz'.2.1
  have hright' : C'.b ≤ C.b := by
    let z : ℂ := (C'.b : ℂ) + (C'.low C'.b : ℂ) * Complex.I
    have hzre : z.re = C'.b := by simp [z]
    have hz : z ∈ graphOver C'.a C'.b C'.low := by
      simp [graphOver, z, C'.ab.le]
    have hz' : z ∈ graphOver C.a C.b C.low ∪ graphOver C.a C.b C.high := by
      rw [h]
      exact Or.inl hz
    rcases hz' with hz' | hz'
    · calc
        C'.b = z.re := hzre.symm
        _ ≤ C.b := hz'.2.1
    · calc
        C'.b = z.re := hzre.symm
        _ ≤ C.b := hz'.2.1
  have ha : C.a = C'.a := le_antisymm hleft' hleft
  have hb : C.b = C'.b := le_antisymm hright hright'
  have hlow : ∀ x ∈ Ioo C.a C.b, C.low x = C'.low x := by
    intro x hx
    let z : ℂ := (x : ℂ) + (C.low x : ℂ) * Complex.I
    have hzval : z.im = C.low x := by simp [z]
    have hzre : z.re = x := by simp [z]
    have hz : z ∈ graphOver C.a C.b C.low := by
      simp [graphOver, z, hx.1.le, hx.2.le]
    have hz' : z ∈ graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inl hz
    have hlowopts : C.low x = C'.low x ∨ C.low x = C'.high x := by
      rcases hz' with hz' | hz'
      · exact Or.inl (hzval.symm.trans (hz'.2.2.trans (congrArg C'.low hzre)))
      · exact Or.inr (hzval.symm.trans (hz'.2.2.trans (congrArg C'.high hzre)))
    let z' : ℂ := (x : ℂ) + (C.high x : ℂ) * Complex.I
    have hzval' : z'.im = C.high x := by simp [z']
    have hhigh_mem : z' ∈ graphOver C.a C.b C.high := by
      simp [graphOver, z', hx.1.le, hx.2.le]
    have hhigh_mem' : z' ∈
        graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inr hhigh_mem
    have hhighopts : C.high x = C'.low x ∨ C.high x = C'.high x := by
      rcases hhigh_mem' with hh | hh
      · exact Or.inl (hzval'.symm.trans (hh.2.2.trans (congrArg C'.low (by simp [z'] : z'.re = x))))
      · exact Or.inr (hzval'.symm.trans
          (hh.2.2.trans (congrArg C'.high (by simp [z'] : z'.re = x))))
    have hx' : x ∈ Ioo C'.a C'.b := by
      rw [← ha, ← hb]
      exact hx
    rcases hlowopts with hl | hl
    · rcases hhighopts with hh | hh
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact (lt_irrefl (C'.low x) hsep).elim
      · exact hl
    · rcases hhighopts with hh | hh
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact ((not_lt_of_ge hsep.le) (C'.separated x hx')).elim
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact (lt_irrefl (C'.high x) hsep).elim
  have hhigh : ∀ x ∈ Ioo C.a C.b, C.high x = C'.high x := by
    intro x hx
    let z : ℂ := (x : ℂ) + (C.high x : ℂ) * Complex.I
    have hzval : z.im = C.high x := by simp [z]
    have hzre : z.re = x := by simp [z]
    have hz : z ∈ graphOver C.a C.b C.high := by
      simp [graphOver, z, hx.1.le, hx.2.le]
    have hz' : z ∈ graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inr hz
    have hhighopts : C.high x = C'.low x ∨ C.high x = C'.high x := by
      rcases hz' with hz' | hz'
      · exact Or.inl (hzval.symm.trans (hz'.2.2.trans (congrArg C'.low hzre)))
      · exact Or.inr (hzval.symm.trans (hz'.2.2.trans (congrArg C'.high hzre)))
    let z' : ℂ := (x : ℂ) + (C.low x : ℂ) * Complex.I
    have hzval' : z'.im = C.low x := by simp [z']
    have hlow_mem : z' ∈ graphOver C.a C.b C.low := by
      simp [graphOver, z', hx.1.le, hx.2.le]
    have hlow_mem' : z' ∈
        graphOver C'.a C'.b C'.low ∪ graphOver C'.a C'.b C'.high := by
      rw [← h]
      exact Or.inl hlow_mem
    have hlowopts : C.low x = C'.low x ∨ C.low x = C'.high x := by
      rcases hlow_mem' with hl | hl
      · exact Or.inl (hzval'.symm.trans (hl.2.2.trans (congrArg C'.low (by simp [z'] : z'.re = x))))
      · exact Or.inr (hzval'.symm.trans
          (hl.2.2.trans (congrArg C'.high (by simp [z'] : z'.re = x))))
    have hx' : x ∈ Ioo C'.a C'.b := by
      rw [← ha, ← hb]
      exact hx
    rcases hlowopts with hl | hl
    · rcases hhighopts with hh | hh
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact (lt_irrefl (C'.low x) hsep).elim
      · exact hh
    · rcases hhighopts with hh | hh
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact ((not_lt_of_ge hsep.le) (C'.separated x hx')).elim
      · have hsep := C.separated x hx
        rw [hl, hh] at hsep
        exact (lt_irrefl (C'.high x) hsep).elim
  ext z
  change (C.a < z.re ∧ z.re < C.b ∧ C.low z.re < z.im ∧ z.im < C.high z.re) ↔
    (C'.a < z.re ∧ z.re < C'.b ∧ C'.low z.re < z.im ∧ z.im < C'.high z.re)
  constructor
  · rintro ⟨hax, hxb, hlo, hhi⟩
    have hax' : C'.a < z.re := by simpa only [ha] using hax
    have hxb' : z.re < C'.b := by simpa only [hb] using hxb
    have hx : z.re ∈ Ioo C.a C.b := ⟨hax, hxb⟩
    exact ⟨hax', hxb', by simpa only [(hlow z.re hx).symm] using hlo,
      by simpa only [(hhigh z.re hx).symm] using hhi⟩
  · rintro ⟨hax, hxb, hlo, hhi⟩
    have hax' : C.a < z.re := by simpa only [ha] using hax
    have hxb' : z.re < C.b := by simpa only [hb] using hxb
    have hx : z.re ∈ Ioo C.a C.b := ⟨hax', hxb'⟩
    exact ⟨hax', hxb', by simpa only [hlow z.re hx] using hlo,
      by simpa only [hhigh z.re hx] using hhi⟩

private theorem layoutArc_stable {w : ℕ → Fin 3} {n m e : ℕ}
    (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

private theorem stageEdgeTrace_eq_of_le {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {n m : ℕ}
    (hnm : n ≤ m) (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    stageEdgeTrace (Q m) e = stageEdgeTrace (Q n) e := by
  have hem : e < (kmswStage w m).nextEdge :=
    he.trans_le (kmswStage_nextEdge_mono w hnm)
  have hArcM : (Q m).arc (⟨⟨e, hem⟩, false⟩ : StageDart (kmswStage w m).nextEdge) =
      layoutArc w m e := by
    simpa using (G m).arc_layout (⟨⟨e, hem⟩, false⟩)
  have hArcN : (Q n).arc (⟨⟨e, he⟩, false⟩ : StageDart (kmswStage w n).nextEdge) =
      layoutArc w n e := by
    simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
  simp only [stageEdgeTrace, dite_eq_left hem, dite_eq_left he, hArcM, hArcN]
  rw [layoutArc_stable hnm he]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_cap_region_eq (w : ℕ → Fin 3) {n m : ℕ}
    {P : StageDrawing w n} {P' : StageDrawing w m}
    (G : MonotoneStageInvariant w n P) (G' : MonotoneStageInvariant w m P')
    (i : Fin (kmswStage w n).triangles.length)
    (j : Fin (kmswStage w m).triangles.length)
    (htri : (kmswStage w n).triangles.get i =
      (kmswStage w m).triangles.get j)
    (htrace : ∀ e, e ∈ [((kmswStage w n).triangles.get i).1,
      ((kmswStage w n).triangles.get i).2.1,
      ((kmswStage w n).triangles.get i).2.2] →
        stageEdgeTrace P e = stageEdgeTrace P' e) :
    (G.cap i).region = (G'.cap j).region := by
  have hmemLeft (z : ℂ) :
      z ∈ graphOver (G.cap i).a (G.cap i).b (G.cap i).low ∪
          graphOver (G.cap i).a (G.cap i).b (G.cap i).high ↔
        ∃ e, e ∈ G.capLower i ++ G.capUpper i ∧ z ∈ stageEdgeTrace P e := by
    rw [G.cap_lower_trace i, G.cap_upper_trace i]
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
      · exact ⟨e, List.mem_append.mpr (Or.inl he), hz⟩
      · exact ⟨e, List.mem_append.mpr (Or.inr he), hz⟩
    · rintro ⟨e, he, hz⟩
      rcases List.mem_append.mp he with he | he
      · exact Or.inl ⟨e, he, hz⟩
      · exact Or.inr ⟨e, he, hz⟩
  have hmemRight (z : ℂ) :
      z ∈ graphOver (G'.cap j).a (G'.cap j).b (G'.cap j).low ∪
          graphOver (G'.cap j).a (G'.cap j).b (G'.cap j).high ↔
        ∃ e, e ∈ G'.capLower j ++ G'.capUpper j ∧ z ∈ stageEdgeTrace P' e := by
    rw [G'.cap_lower_trace j, G'.cap_upper_trace j]
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
      · exact ⟨e, List.mem_append.mpr (Or.inl he), hz⟩
      · exact ⟨e, List.mem_append.mpr (Or.inr he), hz⟩
    · rintro ⟨e, he, hz⟩
      rcases List.mem_append.mp he with he | he
      · exact Or.inl ⟨e, he, hz⟩
      · exact Or.inr ⟨e, he, hz⟩
  have hedge : ∀ e, e ∈ G.capLower i ++ G.capUpper i ↔
      e ∈ G'.capLower j ++ G'.capUpper j := by
    intro e
    rw [G.cap_edges i e, G'.cap_edges j e, htri]
  have htriList :
      [((kmswStage w n).triangles.get i).1,
        ((kmswStage w n).triangles.get i).2.1,
        ((kmswStage w n).triangles.get i).2.2] =
      [((kmswStage w m).triangles.get j).1,
        ((kmswStage w m).triangles.get j).2.1,
        ((kmswStage w m).triangles.get j).2.2] := by
    exact congrArg (fun t : ℕ × ℕ × ℕ => [t.1, t.2.1, t.2.2]) htri
  have hboundary :
      graphOver (G.cap i).a (G.cap i).b (G.cap i).low ∪
          graphOver (G.cap i).a (G.cap i).b (G.cap i).high =
        graphOver (G'.cap j).a (G'.cap j).b (G'.cap j).low ∪
          graphOver (G'.cap j).a (G'.cap j).b (G'.cap j).high := by
    ext z
    rw [hmemLeft z, hmemRight z]
    constructor
    · rintro ⟨e, he, hz⟩
      refine ⟨e, (hedge e).mp he, ?_⟩
      have ht := (G.cap_edges i e).mp he
      have ht' : e ∈ [((kmswStage w n).triangles.get i).1,
          ((kmswStage w n).triangles.get i).2.1,
          ((kmswStage w n).triangles.get i).2.2] := by simpa using ht
      rw [htrace e ht'] at hz
      exact hz
    · rintro ⟨e, he, hz⟩
      refine ⟨e, (hedge e).mpr he, ?_⟩
      have ht' := (G'.cap_edges j e).mp he
      have ht : e ∈ [((kmswStage w n).triangles.get i).1,
          ((kmswStage w n).triangles.get i).2.1,
          ((kmswStage w n).triangles.get i).2.2] := by
        rw [htriList]
        simpa using ht'
      rw [htrace e ht]
      exact hz
  exact GraphCap.region_eq_of_boundary_eq (G.cap i) (G'.cap j) hboundary

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_cap_persistence (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    ∀ n (i : Fin (kmswStage w n).triangles.length) m, n ≤ m →
      ∃ j : Fin (kmswStage w m).triangles.length,
        ((G n).cap i).region = ((G m).cap j).region := by
  intro n i m hnm
  let t := (kmswStage w n).triangles.get i
  have hmem : t ∈ (kmswStage w n).triangles := by
    exact List.get_mem _ i
  have hmem' := triangles_sub_stage w hnm t hmem
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem'
  refine ⟨j, ?_⟩
  apply monotone_cap_region_eq w (G n) (G m) i j hj.symm
  intro e he
  have hb := triBound_stage w n t hmem
  have heBound : e < (kmswStage w n).nextEdge := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he
    · rw [he]
      exact hb.1
    · rw [he]
      exact hb.2.1
    · rw [he]
      exact hb.2.2
  exact (stageEdgeTrace_eq_of_le Q G hnm e heBound).symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_image_mono (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (Q n).image ⊆ (Q (n + 1)).image := by
  intro z hz
  change z ∈ Set.range (Q n).pos ∪ {z | ∃ d, z ∈ ((Q n).arc d).image} at hz
  change z ∈ Set.range (Q (n + 1)).pos ∪
    {z | ∃ d, z ∈ ((Q (n + 1)).arc d).image}
  rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
  · let v' := v.castLE (CutConverse.nextVertex_mono w (Nat.le_succ n))
    apply Or.inl
    refine ⟨v', ?_⟩
    calc
      (Q (n + 1)).pos v' = layoutPos w (n + 1) v'.val := (G (n + 1)).pos_layout v'
      _ = layoutPos w n v.val := by
        simpa [v'] using layoutPos_old_vertex w n v.val v.isLt
      _ = (Q n).pos v := (G n).pos_layout v |>.symm
      _ = z := hv
  · let d' : StageDart (kmswStage w (n + 1)).nextEdge :=
      (d.1.castLE (kmswStage_nextEdge_mono w (Nat.le_succ n)), d.2)
    apply Or.inr
    refine ⟨d', ?_⟩
    have harc : (Q n).arc d = (Q (n + 1)).arc d' := by
      rw [(G n).arc_layout d, (G (n + 1)).arc_layout d']
      cases d with
      | mk e b => simp [d', layoutArc_old w n e.val e.isLt]
    rw [← harc]
    exact hd

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_region_mono (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper ⊆
      closedGraphRegion (G (n + 1)).xmin (G (n + 1)).xmax
        (G (n + 1)).lower (G (n + 1)).upper := by
  intro z hz
  rw [← (G n).cover] at hz
  change z ∈ (Q n).image ∪
    ⋃ i, closure (((G n).cap i).region) at hz
  rw [← (G (n + 1)).cover]
  change z ∈ (Q (n + 1)).image ∪
    ⋃ j, closure (((G (n + 1)).cap j).region)
  rcases hz with hImage | hCaps
  · exact Or.inl (monotone_image_mono w Q G n hImage)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hCaps
    obtain ⟨j, hcap⟩ := monotone_cap_persistence w Q G n i (n + 1) (Nat.le_succ n)
    have hclosure : closure (((G n).cap i).region) =
        closure (((G (n + 1)).cap j).region) := congrArg closure hcap
    rw [hclosure] at hi
    exact Or.inr (mem_iUnion.mpr ⟨j, hi⟩)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_region_mono_of_le (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) {n m : ℕ} (hnm : n ≤ m) :
    closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper ⊆
      closedGraphRegion (G m).xmin (G m).xmax (G m).lower (G m).upper := by
  induction m, hnm using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact ih.trans (monotone_region_mono w Q G m)

end DirectedDistances.KMSW
