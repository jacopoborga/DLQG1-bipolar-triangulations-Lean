/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyCapBorder
public import DirectedDistances.KMSW.StageTriangleCapSideForced

/-! Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of the -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
A stage edge trace cannot lie on both sides of a cap, by strict horizontal rank and separation. -/
private theorem capOrient_layout_trace_not_both (w : ℕ → Fin 3) (n e : ℕ)
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

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
Overlapping wedges with the same initial data contradict disjoint target sets. -/
private theorem capOrient_wedgeIn_incompatible {p dir : ℂ} {S K : Set ℂ}
    (hS : WedgeIn p dir S) (hsub : S ⊆ K) (hK : WedgeIn p dir Kᶜ) : False := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hS
  obtain ⟨δ₂, hδ₂, h₂⟩ := hK
  let t := min δ₁ δ₂ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₁ : t < δ₁ := by
    have hmin := min_le_left δ₁ δ₂
    dsimp [t]
    linarith
  have ht₂ : t < δ₂ := by
    have hmin := min_le_right δ₁ δ₂
    dsimp [t]
    linarith
  exact h₂ t t ht ht₂ ht ht₂ (hsub (h₁ t t ht ht₁ ht ht₁))

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
A wedge remains in any larger target set. -/
private theorem capOrient_wedgeIn_mono {p dir : ℂ} {S T : Set ℂ}
    (hST : S ⊆ T) (hS : WedgeIn p dir S) : WedgeIn p dir T := by
  obtain ⟨δ, hδ, hw⟩ := hS
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htδ hε hεδ
  exact hST (hw t ε ht htδ hε hεδ)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
An edge cannot occur in both side lists of a stage cap. -/
private theorem capOrient_sides_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (G : MonotoneStageInvariant w n (familyQ w (monotone_family_all w) n))
    (i : Fin (kmswStage w n).triangles.length) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ¬ (e ∈ G.capLower i ∧ e ∈ G.capUpper i) := by
  intro hs
  have htrace : stageEdgeTrace (familyQ w (monotone_family_all w) n) e =
      (layoutArc w n e).image := by
    simp only [stageEdgeTrace, dite_eq_left he, G.arc_layout, Bool.false_eq_true,
      ↓reduceIte]
  have hl : (layoutArc w n e).image ⊆
      graphOver (G.cap i).a (G.cap i).b (G.cap i).low := by
    rw [← htrace, G.cap_lower_trace]
    intro z hz
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hs.1, hz⟩⟩
  have hu : (layoutArc w n e).image ⊆
      graphOver (G.cap i).a (G.cap i).b (G.cap i).high := by
    rw [← htrace, G.cap_upper_trace]
    intro z hz
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hs.2, hz⟩⟩
  exact capOrient_layout_trace_not_both w n e he (G.cap i) ⟨hl, hu⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
The creation transition records its triangle as the last triangle of the next stage. -/
private theorem capOrient_creation_triangles_append (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    (kmswStage w (j.val + 1)).triangles =
      (kmswStage w j.val).triangles ++ [stageTriangleRecord w j] := by
  rw [← stageTriangleTimes_records w (j.val + 1), stageTriangleTimes,
    dite_eq_left j.property, List.map_append, stageTriangleTimes_records]
  simp only [List.map_cons, List.map_nil]

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
The three creation darts have their update-prescribed lower or upper side memberships. -/
private theorem capOrient_creation_cap_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w)
    (G : MonotoneStageInvariant w (j.val + 1)
      (familyQ w (monotone_family_all w) (j.val + 1)))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    ∀ d ∈ stageTriangleDartList w j,
      (if d.2 then d.1 ∈ G.capUpper i else d.1 ∈ G.capLower i) := by
  have htris := capOrient_creation_triangles_append w j
  let k : Fin (kmswStage w (j.val + 1)).triangles.length :=
    ⟨(kmswStage w j.val).triangles.length, by simp [htris]⟩
  have hk : ¬ k.val < (kmswStage w j.val).triangles.length := Nat.lt_irrefl _
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

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
A dart bordering a creation cap has its edge in the cap side prescribed by its direction. -/
theorem cap_border_stage_side (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j)) :
    (if d.2 then
      d.1 ∈ (familyG w (monotone_family_all w) (j.val + 1)).capUpper
        (stageTriangleRecord_fin_index w j).choose
    else d.1 ∈ (familyG w (monotone_family_all w) (j.val + 1)).capLower
        (stageTriangleRecord_fin_index w j).choose) := by
  let n := j.val + 1
  let i := (stageTriangleRecord_fin_index w j).choose
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have htri : (kmswStage w n).triangles.get i = stageTriangleRecord w j :=
    (stageTriangleRecord_fin_index w j).choose_spec
  have hmem : stageTriangleRecord w j ∈ (kmswStage w n).triangles := by
    rw [← htri]
    exact List.get_mem _ i
  have hbound := triBound_stage w n (stageTriangleRecord w j) hmem
  have hedge := cap_border_edge_mem w hfin j d hd
  have hdBound : d.1 < (kmswStage w n).nextEdge := by
    rcases hedge with h | h | h
    · rw [h]
      exact hbound.1
    · rw [h]
      exact hbound.2.1
    · rw [h]
      exact hbound.2.2
  have hcapFace : (capFace w hfin j).val = ((G n).cap i).region := by
    simpa [G, n, i] using (capFace_spec w hfin j).1
  let dN : StageDart (kmswStage w n).nextEdge := (⟨d.1, hdBound⟩, d.2)
  have harc : P.arc d = (Q n).arc dN := by
    simpa [P, dN] using familyDrawing_arc w hfin (monotone_family_all w) n dN
  have hwP : WedgeIn (P.arc d).start (P.arc d).initialDirection
      (capFace w hfin j).val :=
    (dartBorders_iff_WedgeIn P d (capFace w hfin j)).mp hd
  have hw : WedgeIn ((Q n).arc dN).start ((Q n).arc dN).initialDirection
      ((G n).cap i).region := by
    rw [← harc, ← hcapFace]
    exact hwP
  have hcapSub : ((G n).cap i).region ⊆
      closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper := by
    intro z hz
    rw [← (G n).cover]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, subset_closure hz⟩)
  have hside : if d.2 then d.1 ∈ (G n).capUpper i else d.1 ∈ (G n).capLower i := by
    cases hb : d.2 with
    | false =>
      rcases (G n).cover_lower ⟨d.1, hdBound⟩ with hboundary | ⟨k, hside⟩
      · have hOutside := (G n).ext_upper_wedge d.1 hdBound hboundary
        have hOutside' : WedgeIn ((Q n).arc dN).start
            ((Q n).arc dN).initialDirection
            (closedGraphRegion (G n).xmin (G n).xmax
              (G n).lower (G n).upper)ᶜ := by
          simpa [Q, dN, hb] using hOutside
        have hsub : (closedGraphRegion (G n).xmin (G n).xmax
            (G n).lower (G n).upper)ᶜ ⊆ ((G n).cap i).regionᶜ := by
          intro z hz hzcap
          exact hz (hcapSub hzcap)
        exact (capOrient_wedgeIn_incompatible hw Set.Subset.rfl
          (capOrient_wedgeIn_mono hsub hOutside')).elim
      · by_cases hik : k = i
        · subst k
          simpa [hb] using hside
        · have hdisj : Disjoint ((G n).cap i).region ((G n).cap k).region :=
            (G n).cap_disjoint i k (Ne.symm hik)
          have hsub : ((G n).cap k).region ⊆ ((G n).cap i).regionᶜ := by
            intro z hzK hzI
            exact (Set.disjoint_left.mp hdisj hzI) hzK
          have hOutside := capOrient_wedgeIn_mono hsub
            ((G n).cap_lower_wedge k d.1 hdBound hside)
          have hOutside' : WedgeIn ((Q n).arc dN).start
              ((Q n).arc dN).initialDirection ((G n).cap i).regionᶜ := by
            simpa [Q, dN, hb] using hOutside
          exact (capOrient_wedgeIn_incompatible hw Set.Subset.rfl hOutside').elim
    | true =>
      rcases (G n).cover_upper ⟨d.1, hdBound⟩ with hboundary | ⟨k, hside⟩
      · have hOutside := (G n).ext_lower_wedge d.1 hdBound hboundary
        have hOutside' : WedgeIn ((Q n).arc dN).start
            ((Q n).arc dN).initialDirection
            (closedGraphRegion (G n).xmin (G n).xmax
              (G n).lower (G n).upper)ᶜ := by
          simpa [Q, dN, hb] using hOutside
        have hsub : (closedGraphRegion (G n).xmin (G n).xmax
            (G n).lower (G n).upper)ᶜ ⊆ ((G n).cap i).regionᶜ := by
          intro z hz hzcap
          exact hz (hcapSub hzcap)
        exact (capOrient_wedgeIn_incompatible hw Set.Subset.rfl
          (capOrient_wedgeIn_mono hsub hOutside')).elim
      · by_cases hik : k = i
        · subst k
          simpa [hb] using hside
        · have hdisj : Disjoint ((G n).cap i).region ((G n).cap k).region :=
            (G n).cap_disjoint i k (Ne.symm hik)
          have hsub : ((G n).cap k).region ⊆ ((G n).cap i).regionᶜ := by
            intro z hzK hzI
            exact (Set.disjoint_left.mp hdisj hzI) hzK
          have hOutside := capOrient_wedgeIn_mono hsub
            ((G n).cap_upper_wedge k d.1 hdBound hside)
          have hOutside' : WedgeIn ((Q n).arc dN).start
              ((Q n).arc dN).initialDirection ((G n).cap i).regionᶜ := by
            simpa [Q, dN, hb] using hOutside
          exact (capOrient_wedgeIn_incompatible hw Set.Subset.rfl hOutside').elim
  simpa [G, n, i] using hside

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
Every dart bordering a creation cap is one of its three oriented creation darts. -/
theorem cap_border_dart_mem (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j)) :
    d ∈ stageTriangleDartList w j := by
  have hside := cap_border_stage_side w hfin j d hd
  let i := (stageTriangleRecord_fin_index w j).choose
  let G := familyG w (monotone_family_all w) (j.val + 1)
  have hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j :=
    (stageTriangleRecord_fin_index w j).choose_spec
  have hforced := capOrient_creation_cap_sides w j G i hi
  have hedge := cap_border_edge_mem w hfin j d hd
  have hedge' : d.1 = (stageTriangleRecord w j).1 ∨
      d.1 = (stageTriangleRecord w j).2.1 ∨ d.1 = (stageTriangleRecord w j).2.2 := hedge
  have htriple : d.1 ∈
      ({(stageTriangleDartTriple w j).1.1,
        (stageTriangleDartTriple w j).2.1.1,
        (stageTriangleDartTriple w j).2.2.1} : Multiset ℕ) := by
    rw [stageTriangleDartTriple_edges_eq_record]
    simpa only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] using hedge'
  have hcand : ∃ c, c ∈ stageTriangleDartList w j ∧ c.1 = d.1 := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at htriple
    rcases htriple with h | h | h
    · exact ⟨(stageTriangleDartTriple w j).1, by simp [stageTriangleDartList], h.symm⟩
    · exact ⟨(stageTriangleDartTriple w j).2.1,
        by simp [stageTriangleDartList], h.symm⟩
    · exact ⟨(stageTriangleDartTriple w j).2.2,
        by simp [stageTriangleDartList], h.symm⟩
  obtain ⟨c, hc, hce⟩ := hcand
  have hcs := hforced c hc
  cases hbD : d.2 <;> cases hbC : c.2
  · have hEq : d = c := Prod.ext hce.symm (by simp [hbD, hbC])
    exact hEq ▸ hc
  · have hlow : d.1 ∈ G.capLower i := by simpa [hbD] using hside
    have hup : d.1 ∈ G.capUpper i := by simpa [hce, hbC] using hcs
    have hbound := triBound_stage w (j.val + 1) (stageTriangleRecord w j) (by
      rw [← hi]
      exact List.get_mem _ i)
    have hdBound : d.1 < (kmswStage w (j.val + 1)).nextEdge := by
      rcases hedge with h | h | h
      · rw [h]
        exact hbound.1
      · rw [h]
        exact hbound.2.1
      · rw [h]
        exact hbound.2.2
    exact (capOrient_sides_disjoint w (j.val + 1) G i d.1 hdBound
      ⟨hlow, hup⟩).elim
  · have hup : d.1 ∈ G.capUpper i := by simpa [hbD] using hside
    have hlow : d.1 ∈ G.capLower i := by simpa [hce, hbC] using hcs
    have hbound := triBound_stage w (j.val + 1) (stageTriangleRecord w j) (by
      rw [← hi]
      exact List.get_mem _ i)
    have hdBound : d.1 < (kmswStage w (j.val + 1)).nextEdge := by
      rcases hedge with h | h | h
      · rw [h]
        exact hbound.1
      · rw [h]
        exact hbound.2.1
      · rw [h]
        exact hbound.2.2
    exact (capOrient_sides_disjoint w (j.val + 1) G i d.1 hdBound
      ⟨hlow, hup⟩).elim
  · have hEq : d = c := Prod.ext hce.symm (by simp [hbD, hbC])
    exact hEq ▸ hc

end DirectedDistances.KMSW
