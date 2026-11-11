module

public import DirectedDistances.KMSW.StageTriangleBoundedFace

/-! # Cap sides at triangle creation

Helpers toward Lemma 5.12; not a paper result. The transition cap lists are -/

public section
namespace DirectedDistances.KMSW

/-- The up-step creation cycle has one west dart followed by two east darts.
Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem stageTriangleDartList_up_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 1) :
    stageTriangleDartList w j =
      [((kmswStage w j.val).active, false),
        ((kmswStage w j.val).nextEdge + 1, true),
        ((kmswStage w j.val).nextEdge, true)] := by
  simp only [stageTriangleDartList, stageTriangleDartTriple_up w j hc]

/-- The fresh-left creation cycle has west, east, west darts in that order.
Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem stageTriangleDartList_left_fresh_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0)
    (hl : (kmswStage w j.val).UL.dropLast.reverse = []) :
    stageTriangleDartList w j =
      [((kmswStage w j.val).active, false),
        ((kmswStage w j.val).nextEdge, true),
        ((kmswStage w j.val).nextEdge + 1, false)] := by
  simp only [stageTriangleDartList, stageTriangleDartTriple_left_fresh w j hc hl]

/-- The existing-left creation cycle has two west darts followed by one east
 dart. Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem stageTriangleDartList_left_existing_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0) (e : ℕ) (es : List ℕ)
    (hl : (kmswStage w j.val).UL.dropLast.reverse = e :: es) :
    stageTriangleDartList w j =
      [(e, false), ((kmswStage w j.val).active, false),
        ((kmswStage w j.val).nextEdge, true)] := by
  simp only [stageTriangleDartList,
    stageTriangleDartTriple_left_existing w j hc e es hl]

/-- The new up-step cap stores its old active edge on the lower side and the
 two new edges on the upper side. Helper toward Lemma 5.12; not a paper result. -/
theorem invariant_succ_up_new_cap_sides (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1))
    (i : Fin (kmswStage w (n + 1)).triangles.length)
    (hi : ¬ i.val < (kmswStage w n).triangles.length) :
    (invariant_succ_up w n hc G h).capLower i = [(kmswStage w n).active] ∧
      (invariant_succ_up w n hc G h).capUpper i =
        [(kmswStage w n).nextEdge, (kmswStage w n).nextEdge + 1] := by
  simp [invariant_succ_up, upCapLower, upCapUpper, hi]

/-- The fresh-left cap stores the new west boundary edges below and the new
 east edge above. Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem invariant_succ_lfr_new_cap_sides (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hUL : (kmswStage w n).UL.dropLast.reverse = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1))
    (i : Fin (kmswStage w (n + 1)).triangles.length)
    (hi : ¬ i.val < (kmswStage w n).triangles.length) :
    (invariant_succ_lfr w n hc hUL G h).capLower i =
        [(kmswStage w n).nextEdge + 1, (kmswStage w n).active] ∧
      (invariant_succ_lfr w n hc hUL G h).capUpper i =
        [(kmswStage w n).nextEdge] := by
  simp [invariant_succ_lfr, lfrCapLower, lfrCapUpper, hi]


/-- The three up-step darts lie on the sides prescribed by the new up cap.
Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem invariant_succ_up_new_cap_dart_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 1)
    {P : StageDrawing w j.val}
    (G : MonotoneStageInvariant w j.val P)
    (h : LayoutGood w (j.val + 1))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : ¬ i.val < (kmswStage w j.val).triangles.length) :
    ∀ d ∈ stageTriangleDartList w j,
      (if d.2 then d.1 ∈ (invariant_succ_up w j.val hc G h).capUpper i
        else d.1 ∈ (invariant_succ_up w j.val hc G h).capLower i) := by
  have hcap := invariant_succ_up_new_cap_sides w j.val hc G h i hi
  rw [stageTriangleDartList_up_sides w j hc]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd | hd
  · subst d
    simp [hcap.1]
  · subst d
    simp [hcap.2]
  · subst d
    simp [hcap.2]

/-- The three fresh-left darts lie on the sides prescribed by the new cap.
Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem invariant_succ_lfr_new_cap_dart_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0)
    (hUL : (kmswStage w j.val).UL.dropLast.reverse = [])
    {P : StageDrawing w j.val}
    (G : MonotoneStageInvariant w j.val P)
    (h : LayoutGood w (j.val + 1))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : ¬ i.val < (kmswStage w j.val).triangles.length) :
    ∀ d ∈ stageTriangleDartList w j,
      (if d.2 then d.1 ∈ (invariant_succ_lfr w j.val hc hUL G h).capUpper i
        else d.1 ∈ (invariant_succ_lfr w j.val hc hUL G h).capLower i) := by
  have hcap := invariant_succ_lfr_new_cap_sides w j.val hc hUL G h i hi
  rw [stageTriangleDartList_left_fresh_sides w j hc hUL]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd | hd
  · subst d
    simp [hcap.1]
  · subst d
    simp [hcap.2]
  · subst d
    simp [hcap.1]






def hasCreationCapDartSides (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) : Prop :=
  ∀ j : TriangleCreationTime w, j.val + 1 = n →
    ∀ i : Fin (kmswStage w n).triangles.length,
      (kmswStage w n).triangles.get i = stageTriangleRecord w j →
      ∀ d ∈ stageTriangleDartList w j,
        (if d.2 then d.1 ∈ G.capUpper i else d.1 ∈ G.capLower i)

/- Conditional all-darts border statement for the bounded limit face carried
`hasCreationCapDartSides`, which the invariant's public `cap_edges` field does
not provide. Helper toward Lemma 5.12; not a paper result. See `def-kmsw`, -/
theorem stageTriangleDarts_border_creation_cap_of_property (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w)
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j)
    (hside : hasCreationCapDartSides w (j.val + 1)
      (familyG w (monotone_family_all w) (j.val + 1))) :
    ∃ F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)),
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
        ∀ d ∈ stageTriangleDartList w j,
          (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders
            d F.val := by
  obtain ⟨F, hF⟩ := monotoneFamily_cap_planeFace w hfin (j.val + 1) i
  refine ⟨F, hF, ?_⟩
  intro d hd
  let Q := familyQ w (monotone_family_all w) (j.val + 1)
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hbound := stageTriangleDartList_lt w (j.val + 1) j (by omega) d hd
  let x : StageDart (kmswStage w (j.val + 1)).nextEdge :=
    (⟨d.1, hbound⟩, d.2)
  have hxArc : P.arc (x.1.val, x.2) = Q.arc x :=
    familyDrawing_arc w hfin (monotone_family_all w) (j.val + 1) x
  have hsides := hside j rfl i hi d hd
  cases hbool : d.2
  · have hmem : d.1 ∈
        (familyG w (monotone_family_all w) (j.val + 1)).capLower i := by
      simpa [hbool] using hsides
    have hdEq : d = (d.1, false) := by
      cases d with
      | mk e b => simp_all
    have hW := (familyG w (monotone_family_all w) (j.val + 1)).cap_lower_wedge
      i d.1 hbound hmem
    have hArc' : P.arc (d.1, false) =
        Q.arc ((⟨d.1, hbound⟩, false) : StageDart (kmswStage w (j.val + 1)).nextEdge) := by
      simpa [x, hbool] using hxArc
    rw [hdEq]
    apply (dartBorders_iff_WedgeIn P (d.1, false) F.val).2
    rw [hF, hArc']
    exact hW
  · have hmem : d.1 ∈
        (familyG w (monotone_family_all w) (j.val + 1)).capUpper i := by
      simpa [hbool] using hsides
    have hdEq : d = (d.1, true) := by
      cases d with
      | mk e b => simp_all
    have hW := (familyG w (monotone_family_all w) (j.val + 1)).cap_upper_wedge
      i d.1 hbound hmem
    have hArc' : P.arc (d.1, true) =
        Q.arc ((⟨d.1, hbound⟩, true) : StageDart (kmswStage w (j.val + 1)).nextEdge) := by
      simpa [x, hbool] using hxArc
    rw [hdEq]
    apply (dartBorders_iff_WedgeIn P (d.1, true) F.val).2
    rw [hF, hArc']
    exact hW

end DirectedDistances.KMSW
