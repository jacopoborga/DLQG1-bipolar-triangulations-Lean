module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
public import DirectedDistances.KMSW.StageRotation
import DirectedDistances.KMSW.MonotoneStepCommon

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

/-- The LEX step allocates exactly the chord edge. Helper toward the
plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswStage_lex_nextEdge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- The new LEX chord joins the west endpoint of the predecessor to the east
endpoint of the old active edge. Helper toward the plane-realization
obligation of adjudication n308; not a paper result. -/
theorem kmswStage_lex_chord_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge) =
        (kmswStage w n).west e ∧
      (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge) =
        (kmswStage w n).east (kmswStage w n).active := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

/-- The new LEX chord is the ramp roof between its allocated endpoints.
Helper toward the plane-realization obligation of adjudication n308; not a
paper result. -/
theorem layoutArc_succ_lex_chord_roof (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    layoutArc w (n + 1) ((kmswStage w n).nextEdge) =
      roofArc (layoutPos w (n + 1) ((kmswStage w n).west e))
        (layoutPos w (n + 1) ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) := by
  have hnew : (kmswStage w n).nextEdge ∈ freshEdges w n := by
    rw [freshEdges, kmswStage_lex_nextEdge w n hc e es hUL]
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hmiss : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc, hUL]
  have hep := kmswStage_lex_chord_endpoints w n hc e es hUL
  rw [layoutArc_fresh w n _ hnew, ite_eq_right hmiss, hep.1, hep.2]

/-- Old LEX darts keep their layout polylines. Helper toward the
plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutDart_succ_lex_old (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  change (if d.2 then (layoutArc w (n + 1) d.1.val).reverse
    else layoutArc w (n + 1) d.1.val) =
    if d.2 then (layoutArc w n d.1.val).reverse else layoutArc w n d.1.val
  rw [layoutArc_old w n d.1.val d.1.isLt]

/-- The old-old pairs satisfy the new interior-disjointness field. Helper
toward the plane-realization obligation of adjudication n308; not a paper
result. -/
theorem layoutGood_succ_lex_old_interior_disjoint (w : ℕ → Fin 3) (n : ℕ)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (d f : StageDart (kmswStage w n).nextEdge) (hne : f ≠ d)
    (hflip : f ≠ edgeFlip _ d) :
    Disjoint (layoutDart w (n + 1) (stageDartIncl w n d)).interior
      (layoutDart w (n + 1) (stageDartIncl w n f)).interior := by
  simpa only [layoutDart_succ_lex_old] using
    (layoutGood_of_invariant G).interior_disjoint d f hne hflip

/-- Old edges still avoid old vertices in the new layout. Helper toward the
plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutGood_succ_lex_old_interior_avoids_old_vertices
    (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P)
    (d : StageDart (kmswStage w n).nextEdge)
    (v : Fin (kmswStage w n).nextVertex) :
    layoutPos w (n + 1) (stageVertexIncl w n v).val ∉
      (layoutDart w (n + 1) (stageDartIncl w n d)).interior := by
  have hpos : layoutPos w (n + 1) (stageVertexIncl w n v).val =
      layoutPos w n v.val := by
    change layoutPos w (n + 1) v.val = layoutPos w n v.val
    exact layoutPos_old_vertex w n v.val v.isLt
  simpa only [layoutDart_succ_lex_old, hpos] using
    (layoutGood_of_invariant G).interior_avoids_vertices d v

private theorem lex_predecessor_mem_upper (w : ℕ → Fin 3) (n : ℕ)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
  have he : e ∈ (kmswStage w n).UL.dropLast.reverse := by
    rw [hUL]
    simp
  exact List.mem_append_left _
    (List.mem_of_mem_dropLast (List.mem_reverse.mp he))

private theorem lex_active_mem_upper (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).active ∈ (kmswStage w n).UL ++ (kmswStage w n).UR := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  rw [hxs]
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

private theorem lex_finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
  have hpos : 0 < p.points.length := by
    cases h : p.points with
    | nil => exact (p.nonempty h).elim
    | cons a as => simp
  by_cases hlen : p.points.length = 1
  · have hfin : p.finish = p.start := by
      rw [← Polyline.point_last_eq_finish, hlen]
      exact Polyline.point_zero_eq_start p
    exact Or.inl hfin
  · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
    unfold Polyline.segmentAt
    have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
    rw [hidx, Polyline.point_last_eq_finish]
    exact right_mem_segment ℝ _ _

private theorem lex_reverse_point (p : Polyline) (i : ℕ)
    (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.reverse.getD i p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_reverse i hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]

private theorem lex_reverse_segment (p : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold Polyline.segmentAt
  rw [lex_reverse_point p i (by omega), lex_reverse_point p (i + 1) hi]
  have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by
    omega
  have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by
    omega
  rw [h₁, h₂, segment_symm]

private theorem lex_reverse_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ lex_finish_mem_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    rw [lex_reverse_segment p i hi'] at hz
    exact Or.inr ⟨p.points.length - 2 - i, by omega, hz⟩

private theorem lex_reverse_image (p : Polyline) :
    p.reverse.image = p.image := by
  apply Set.Subset.antisymm (lex_reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using lex_reverse_image_subset p.reverse

private theorem lex_reverse_interior (p : Polyline) :
    p.reverse.interior = p.interior := by
  rw [Polyline.interior, lex_reverse_image, Polyline.start_reverse,
    Polyline.finish_reverse]
  rw [Set.pair_comm]
  rfl

private theorem lex_roof_data (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).west e)
    let b := layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active)
    a.re ∈ Icc G.xmin G.xmax ∧ b.re ∈ Icc G.xmin G.xmax ∧
      a.im = G.upper a.re ∧ b.im = G.upper b.re ∧
      ((n + 1 : ℝ) - a.im) / rampSlope w n +
        ((n + 1 : ℝ) - b.im) / rampSlope w n < b.re - a.re := by
  classical
  dsimp only
  let s := kmswStage w n
  have heUL : e ∈ s.UL ++ s.UR := by
    have he : e ∈ s.UL.dropLast.reverse := by rw [hUL]; simp
    exact List.mem_append_left _
      (List.mem_of_mem_dropLast (List.mem_reverse.mp he))
  have he : e < s.nextEdge := by
    exact (stageRotation_UL_bound w n) e
      (List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hUL]; simp)))
  have hactive : s.active ∈ s.UL ++ s.UR := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    have hxs' : s.UL = xs ++ [s.active] := by simpa [s] using hxs
    rw [hxs']
    exact List.mem_append_left _ (List.mem_append_right _ (by simp))
  have haEdge : (s.west e) < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n e he).1
  have hbEdge : (s.east s.active) < s.nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n s.active
      (act_lt_nextEdge w (le_refl n))).2
  let va : Fin s.nextVertex := ⟨s.west e, haEdge⟩
  let vb : Fin s.nextVertex := ⟨s.east s.active, hbEdge⟩
  have hia : layoutPos w n va.val ∈ P.image := by
    rw [← G.pos_layout va]
    exact Or.inl ⟨va, rfl⟩
  have hib : layoutPos w n vb.val ∈ P.image := by
    rw [← G.pos_layout vb]
    exact Or.inl ⟨vb, rfl⟩
  have hba := G.image_bounds hia
  have hbb := G.image_bounds hib
  have hza : layoutPos w n va.val ∈ (layoutArc w n e).image := by
    rw [← layoutArc_start w n e he]
    exact Or.inl rfl
  have hzb : layoutPos w n vb.val ∈ (layoutArc w n s.active).image := by
    rw [← layoutArc_finish w n s.active (act_lt_nextEdge w (le_refl n))]
    exact lex_finish_mem_image _
  have hya := G.upper_eq_arc_height heUL hza
  have hyb := G.upper_eq_arc_height hactive hzb
  have hfresh : s.nextEdge ∈ freshEdges w n := by
    rw [freshEdges, kmswStage_lex_nextEdge w n hc e es hUL]
    exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self _⟩
  have hfit := freshEdges_ramp_widths_lt w n s.nextEdge hfresh
  rcases kmswStage_lex_chord_endpoints w n hc e es hUL with ⟨hwest, heast⟩
  rw [hwest, heast] at hfit
  rw [layoutPos_old_vertex w n _ haEdge,
    layoutPos_old_vertex w n _ hbEdge] at hfit
  have hArange : (layoutPos w n (s.west e)).re ∈ Icc G.xmin G.xmax := by
    simpa only [va, Fin.val_mk] using ⟨hba.1, hba.2.1⟩
  have hBrange : (layoutPos w n (s.east s.active)).re ∈ Icc G.xmin G.xmax := by
    simpa only [vb, Fin.val_mk] using ⟨hbb.1, hbb.2.1⟩
  have hya' : (layoutPos w n (s.west e)).im =
      G.upper (layoutPos w n (s.west e)).re := by
    simpa only [va, Fin.val_mk] using hya.symm
  have hyb' : (layoutPos w n (s.east s.active)).im =
      G.upper (layoutPos w n (s.east s.active)).re := by
    simpa only [vb, Fin.val_mk] using hyb.symm
  exact ⟨hArange, hBrange, hya', hyb', hfit⟩

private theorem lex_old_dart_image_subset {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (d : StageDart (kmswStage w n).nextEdge) :
    (layoutDart w n d).image ⊆ P.image := by
  intro z hz
  apply Or.inr
  refine ⟨d, ?_⟩
  have hArc : P.arc d = layoutDart w n d := G.arc_layout d
  change z ∈ (layoutDart w n d).image at hz
  rw [← hArc] at hz
  exact hz

private theorem lex_old_dart_interior_subset {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (d : StageDart (kmswStage w n).nextEdge) :
    (layoutDart w n d).interior ⊆ P.image := by
  intro z hz
  exact lex_old_dart_image_subset G d hz.1

private theorem lex_fresh_edge (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).nextEdge ∈ freshEdges w n := by
  rw [freshEdges, kmswStage_lex_nextEdge w n hc e es hUL]
  exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self _⟩

private theorem lex_next_vertex (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUL,
    State.addEdge]

private theorem lex_chord_interior_disjoint_old_image
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    Disjoint (layoutArc w (n + 1) ((kmswStage w n).nextEdge)).interior
      P.image := by
  obtain ⟨ha, hb, hya, hyb, hfit⟩ := lex_roof_data w n hc e es hUL G
  have harc := layoutArc_succ_lex_chord_roof w n hc e es hUL
  have heDropped : e ∈ (kmswStage w n).UL.dropLast.reverse := by
    rw [hUL]
    simp
  have heUL : e ∈ (kmswStage w n).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp heDropped)
  have hebound : e < (kmswStage w n).nextEdge :=
    (stageRotation_UL_bound w n) e heUL
  have hvbound : (kmswStage w n).active < (kmswStage w n).nextEdge :=
    act_lt_nextEdge w (le_refl n)
  rw [layoutPos_old_vertex w n _
    ((kmswStage_endpoints_lt_nextVertex w n e hebound).1),
    layoutPos_old_vertex w n _
      ((kmswStage_endpoints_lt_nextVertex w n _ hvbound).2)] at harc
  rw [harc]
  apply G.roof_interior_disjoint_image ha hb hya hyb hfit

private theorem lex_chord_dart_interior_disjoint_old_dart
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val = (kmswStage w n).nextEdge)
    (d : StageDart (kmswStage w n).nextEdge) :
    Disjoint (layoutDart w (n + 1) x).interior
      (layoutDart w (n + 1) (stageDartIncl w n d)).interior := by
  have hInt : (layoutDart w (n + 1) x).interior =
      (layoutArc w (n + 1) ((kmswStage w n).nextEdge)).interior := by
    unfold layoutDart
    split
    · rw [hx]
      exact lex_reverse_interior _
    · rw [hx]
  have hOld : (layoutDart w (n + 1) (stageDartIncl w n d)).interior ⊆ P.image := by
    rw [layoutDart_succ_lex_old]
    exact lex_old_dart_interior_subset G d
  rw [hInt]
  apply Set.disjoint_left.mpr
  intro z hz hzOld
  exact (Set.disjoint_left.mp
    (lex_chord_interior_disjoint_old_image w n hc e es hUL G)) hz (hOld hzOld)

private theorem lex_chord_interior_avoids_old_vertex
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (v : Fin (kmswStage w n).nextVertex) :
    layoutPos w (n + 1) v.val ∉
      (layoutArc w (n + 1) ((kmswStage w n).nextEdge)).interior := by
  obtain ⟨ha, hb, hya, hyb, hfit⟩ := lex_roof_data w n hc e es hUL G
  have harc := layoutArc_succ_lex_chord_roof w n hc e es hUL
  have heDropped : e ∈ (kmswStage w n).UL.dropLast.reverse := by
    rw [hUL]
    simp
  have heUL : e ∈ (kmswStage w n).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp heDropped)
  have hebound : e < (kmswStage w n).nextEdge :=
    (stageRotation_UL_bound w n) e heUL
  have hvbound : (kmswStage w n).active < (kmswStage w n).nextEdge :=
    act_lt_nextEdge w (le_refl n)
  rw [layoutPos_old_vertex w n _
    ((kmswStage_endpoints_lt_nextVertex w n e hebound).1),
    layoutPos_old_vertex w n _
      ((kmswStage_endpoints_lt_nextVertex w n _ hvbound).2)] at harc
  rw [harc]
  simpa only [layoutPos_old_vertex w n v.val v.isLt] using
    G.old_vertex_not_mem_roof_interior ha hb hya hyb hfit v

private theorem lex_dartIncl_injective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Injective (stageDartIncl w n) := by
  intro d f h
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun x : StageDart (kmswStage w (n + 1)).nextEdge => x.1.val) h
  · exact congrArg
      (fun x : StageDart (kmswStage w (n + 1)).nextEdge => x.2) h

private theorem lex_old_star_eq_image (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    {f : StageDart (kmswStage w (n + 1)).nextEdge |
      f.1.val < (kmswStage w n).nextEdge ∧
        stageVertex w (n + 1) f =
          stageVertex w (n + 1) (stageDartIncl w n d)} =
      stageDartIncl w n '' {g | stageVertex w n g = stageVertex w n d} := by
  ext f
  constructor
  · rintro ⟨hf, hv⟩
    let g : StageDart (kmswStage w n).nextEdge := (⟨f.1.val, hf⟩, f.2)
    have hfg : stageDartIncl w n g = f := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    refine ⟨g, ?_, hfg⟩
    rw [← hfg, stageVertex_incl_eq, stageVertex_incl_eq] at hv
    exact Fin.ext (congrArg
      (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv)
  · rintro ⟨g, hv, rfl⟩
    exact ⟨g.1.isLt, by
      rw [stageVertex_incl_eq, stageVertex_incl_eq, hv]⟩

private theorem successor_insert_other {D : Type*} (S : Set D) (dir : D → ℂ)
    (f g p x : D) (hold : CcwSuccessor S dir f g)
    (hnew : CcwSuccessor (insert x S) dir p x) (hp : p ∈ S)
    (hf : f ≠ p) (hx : x ∉ S)
    (hargs : ∀ a ∈ insert x S, ∀ b ∈ insert x S, a ≠ b →
      Complex.arg (dir a) ≠ Complex.arg (dir b)) :
    CcwSuccessor (insert x S) dir f g := by
  apply ccwSuccessor_insert_preserve S dir f g x hold.1 hargs hold hx
  intro hbetween
  have hpx : p ≠ x := fun h => hx (h ▸ hp)
  have hfp := hargs f (mem_insert_of_mem x hold.2.1)
    p (mem_insert_of_mem x hp) hf
  have hxp := hargs x (mem_insert x S) p (mem_insert_of_mem x hp) hpx.symm
  have hmin : ccwTurn (dir f) (dir g) ≤ ccwTurn (dir f) (dir p) := by
    rcases hold.2.2.2 with ⟨_, hs⟩ | ⟨_, hm⟩
    · have hpf : p = f := by simpa only [hs, mem_singleton_iff] using hp
      exact False.elim (hf hpf.symm)
    · exact hm p hp hf.symm
  have hcomp := ccwTurn_comp_add (lt_of_lt_of_le hbetween hmin)
  have hrev := ccwTurn_add_reverse (dir f) (dir p) hfp
  have hrev' := ccwTurn_add_reverse (dir x) (dir p) hxp
  have hpos := ccwTurn_pos (dir f) (dir x)
  have hnewmin : ccwTurn (dir p) (dir x) ≤ ccwTurn (dir p) (dir f) := by
    rcases hnew.2.2.2 with ⟨heq, _⟩ | ⟨_, hm⟩
    · exact False.elim (hpx heq.symm)
    · exact hm f (mem_insert_of_mem x hold.2.1) hf
  linarith only [hcomp, hrev, hrev', hpos, hnewmin]

private theorem lex_darts_same_edge {k : ℕ} (d f : StageDart k)
    (h : d.1.val = f.1.val) : f = d ∨ f = edgeFlip k d := by
  have he : f.1 = d.1 := Fin.ext h.symm
  cases d with
  | mk de db =>
    cases f with
    | mk fe fb =>
      have : fe = de := he
      subst fe
      cases db <;> cases fb <;> simp [edgeFlip]

private theorem lex_succ_interior_disjoint
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d f : StageDart (kmswStage w (n + 1)).nextEdge,
      f ≠ d → f ≠ edgeFlip _ d →
      Disjoint (layoutDart w (n + 1) d).interior
        (layoutDart w (n + 1) f).interior := by
  let k := (kmswStage w n).nextEdge
  have hnext : (kmswStage w (n + 1)).nextEdge = k + 1 :=
    kmswStage_lex_nextEdge w n hc e es hUL
  intro d f hne hflip
  by_cases hd : d.1.val < k
  · let d₀ : StageDart k := (⟨d.1.val, hd⟩, d.2)
    have hdEq : stageDartIncl w n d₀ = d := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    by_cases hf : f.1.val < k
    · let f₀ : StageDart k := (⟨f.1.val, hf⟩, f.2)
      have hfEq : stageDartIncl w n f₀ = f := by
        apply Prod.ext
        · apply Fin.ext
          rfl
        · rfl
      have hne₀ : f₀ ≠ d₀ := by
        intro h
        apply hne
        calc
          f = stageDartIncl w n f₀ := hfEq.symm
          _ = stageDartIncl w n d₀ := congrArg (stageDartIncl w n) h
          _ = d := hdEq
      have hflip₀ : f₀ ≠ edgeFlip k d₀ := by
        intro h
        apply hflip
        calc
          f = stageDartIncl w n f₀ := hfEq.symm
          _ = stageDartIncl w n (edgeFlip k d₀) :=
            congrArg (stageDartIncl w n) h
          _ = edgeFlip _ (stageDartIncl w n d₀) := by
            cases d₀ with
            | mk de db => cases db <;> rfl
          _ = edgeFlip _ d := congrArg (edgeFlip _) hdEq
      rw [← hdEq, ← hfEq]
      exact layoutGood_succ_lex_old_interior_disjoint w n G d₀ f₀ hne₀ hflip₀
    · have hfEq : f.1.val = k := by omega
      exact (lex_chord_dart_interior_disjoint_old_dart
        w n hc e es hUL G f hfEq d₀).symm
  · have hdEq : d.1.val = k := by omega
    by_cases hf : f.1.val < k
    · let f₀ : StageDart k := (⟨f.1.val, hf⟩, f.2)
      have hfIncl : stageDartIncl w n f₀ = f := by
        apply Prod.ext
        · apply Fin.ext
          rfl
        · rfl
      exact lex_chord_dart_interior_disjoint_old_dart
        w n hc e es hUL G d hdEq f₀
    · have hfEq : f.1.val = k := by omega
      have hsame := lex_darts_same_edge d f (hdEq.trans hfEq.symm)
      rcases hsame with h | h
      · exact (hne h).elim
      · exact (hflip h).elim

private theorem lex_succ_interior_avoids_vertices
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      layoutPos w (n + 1) v.val ∉ (layoutDart w (n + 1) d).interior := by
  let k := (kmswStage w n).nextEdge
  have hnext : (kmswStage w (n + 1)).nextEdge = k + 1 :=
    kmswStage_lex_nextEdge w n hc e es hUL
  have hvertices := lex_next_vertex w n hc e es hUL
  intro d v
  have hvlt : v.val < (kmswStage w n).nextVertex := by
    simpa only [hvertices] using v.isLt
  let v₀ : Fin (kmswStage w n).nextVertex := ⟨v.val, hvlt⟩
  have hvEq : stageVertexIncl w n v₀ = v := by
    apply Fin.ext
    rfl
  by_cases hd : d.1.val < k
  · let d₀ : StageDart k := (⟨d.1.val, hd⟩, d.2)
    have hdEq : stageDartIncl w n d₀ = d := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    rw [← hvEq, ← hdEq]
    exact layoutGood_succ_lex_old_interior_avoids_old_vertices w n G d₀ v₀
  · have hdEq : d.1.val = k := by omega
    have hInt : (layoutDart w (n + 1) d).interior =
        (layoutArc w (n + 1) k).interior := by
      unfold layoutDart
      split
      · rw [hdEq]
        exact lex_reverse_interior _
      · rw [hdEq]
    rw [hInt]
    exact lex_chord_interior_avoids_old_vertex w n hc e es hUL G v₀

private theorem lex_chord_dart_direction_slope
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val = (kmswStage w n).nextEdge) :
    (if x.2 then (layoutDart w (n + 1) x).initialDirection.re < 0
      else 0 < (layoutDart w (n + 1) x).initialDirection.re) ∧
    (layoutDart w (n + 1) x).initialDirection.im /
      (layoutDart w (n + 1) x).initialDirection.re =
        if x.2 then -rampSlope w n else rampSlope w n := by
  have heDropped : e ∈ (kmswStage w n).UL.dropLast.reverse := by
    rw [hUL]
    simp
  have heUL : e ∈ (kmswStage w n).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp heDropped)
  have hebound : e < (kmswStage w n).nextEdge :=
    (stageRotation_UL_bound w n) e heUL
  have hvbound : (kmswStage w n).active < (kmswStage w n).nextEdge :=
    act_lt_nextEdge w (le_refl n)
  have haBound := (kmswStage_endpoints_lt_nextVertex w n e hebound).1
  have hbBound :=
    (kmswStage_endpoints_lt_nextVertex w n _ hvbound).2
  have hposA := layoutPos_old_vertex w n _ haBound
  have hposB := layoutPos_old_vertex w n _ hbBound
  have hArc : layoutArc w (n + 1) ((kmswStage w n).nextEdge) =
      roofArc (layoutPos w n ((kmswStage w n).west e))
        (layoutPos w n
          ((kmswStage w n).east (kmswStage w n).active))
        (n + 1) (rampSlope w n) := by
    simpa only [hposA, hposB] using
      layoutArc_succ_lex_chord_roof w n hc e es hUL
  have hA_lt : (layoutPos w n ((kmswStage w n).west e)).im < (n + 1 : ℝ) := by
    have hh := layoutHeight_le w n _ haBound
    change (layoutPos w n ((kmswStage w n).west e)).im ≤ n at hh
    exact lt_of_le_of_lt hh (by exact_mod_cast Nat.lt_succ_self n)
  have hB_lt :
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).im <
        (n + 1 : ℝ) := by
    have hh := layoutHeight_le w n _ hbBound
    change (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).im ≤ n at hh
    exact lt_of_le_of_lt hh (by exact_mod_cast Nat.lt_succ_self n)
  cases hb : x.2
  · have hdir : layoutDart w (n + 1) x = layoutArc w (n + 1) x.1.val := by
      simp [layoutDart, hb]
    rw [hdir, hx, hArc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨roofArc_initialDirection_re_pos (rampSlope_pos w n) hA_lt,
      roofArc_initialSlope (rampSlope_pos w n) hA_lt⟩
  · have hdir : layoutDart w (n + 1) x =
        (layoutArc w (n + 1) x.1.val).reverse := by simp [layoutDart, hb]
    rw [hdir, hx, hArc]
    simp only [↓reduceIte]
    exact ⟨(roofArc_reverse_initialDirection_geom
        (rampSlope_pos w n) hB_lt).1,
      roofArc_reverse_initialSlope (rampSlope_pos w n) hB_lt⟩

private theorem lex_succ_initial_arg_injective
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d f : StageDart (kmswStage w (n + 1)).nextEdge,
      stageVertex w (n + 1) d = stageVertex w (n + 1) f →
      Complex.arg (layoutDart w (n + 1) d).initialDirection =
        Complex.arg (layoutDart w (n + 1) f).initialDirection → d = f := by
  let k := (kmswStage w n).nextEdge
  have hnext : (kmswStage w (n + 1)).nextEdge = k + 1 := by
    simpa only [k] using kmswStage_lex_nextEdge w n hc e es hUL
  intro d f hv harg
  by_cases hd : d.1.val < k
  · let d₀ : StageDart k := (⟨d.1.val, hd⟩, d.2)
    have hdEq : stageDartIncl w n d₀ = d := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    by_cases hf : f.1.val < k
    · let f₀ : StageDart k := (⟨f.1.val, hf⟩, f.2)
      have hfEq : stageDartIncl w n f₀ = f := by
        apply Prod.ext
        · apply Fin.ext
          rfl
        · rfl
      have hv' := hv
      rw [← hdEq, ← hfEq, stageVertex_incl_eq w n d₀,
        stageVertex_incl_eq w n f₀] at hv'
      have hv₀ : stageVertex w n d₀ = stageVertex w n f₀ := by
        apply Fin.ext
        simpa only [stageVertexIncl, Fin.val_castLE] using
          congrArg (fun v : Fin (kmswStage w (n + 1)).nextVertex => v.val) hv'
      have harg' := harg
      rw [← hdEq, ← hfEq, layoutDart_succ_lex_old,
        layoutDart_succ_lex_old] at harg'
      have hEq₀ := (layoutGood_of_invariant G).initial_arg_injective d₀ f₀ hv₀ harg'
      calc
        d = stageDartIncl w n d₀ := hdEq.symm
        _ = stageDartIncl w n f₀ := congrArg (stageDartIncl w n) hEq₀
        _ = f := hfEq
    · have hfEq : f.1.val = k := by omega
      have hOldSlope := layoutDart_old_initial_slope_bounds w n d₀
      rw [layoutDart_succ_lex_old] at hOldSlope
      have htan := congrArg Real.tan harg
      rw [← hdEq] at htan
      simp only [Complex.tan_arg, layoutDart_succ_lex_old] at htan
      have hChord := lex_chord_dart_direction_slope w n hc e es hUL f hfEq
      cases hb : f.2
      · have hs := hChord.2
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs
        rw [hs] at htan
        exact False.elim ((ne_of_lt hOldSlope.2) htan)
      · have hs := hChord.2
        simp only [hb, ↓reduceIte] at hs
        rw [hs] at htan
        exact False.elim ((ne_of_lt hOldSlope.1) htan.symm)
  · have hdEq : d.1.val = k := by omega
    by_cases hf : f.1.val < k
    · let f₀ : StageDart k := (⟨f.1.val, hf⟩, f.2)
      have hfEq : stageDartIncl w n f₀ = f := by
        apply Prod.ext
        · apply Fin.ext
          rfl
        · rfl
      have hOldSlope := layoutDart_old_initial_slope_bounds w n f₀
      rw [layoutDart_succ_lex_old] at hOldSlope
      have htan := congrArg Real.tan harg
      rw [← hfEq] at htan
      simp only [Complex.tan_arg, layoutDart_succ_lex_old] at htan
      have hChord := lex_chord_dart_direction_slope w n hc e es hUL d hdEq
      cases hb : d.2
      · have hs := hChord.2
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs
        rw [hs] at htan
        exact False.elim ((ne_of_lt hOldSlope.2) htan.symm)
      · have hs := hChord.2
        simp only [hb, ↓reduceIte] at hs
        rw [hs] at htan
        exact False.elim ((ne_of_lt hOldSlope.1) htan)
    · have hfEq : f.1.val = k := by omega
      have hdSlope := lex_chord_dart_direction_slope w n hc e es hUL d hdEq
      have hfSlope := lex_chord_dart_direction_slope w n hc e es hUL f hfEq
      by_cases hbool : d.2 = f.2
      · have hFin : d.1 = f.1 := Fin.ext (hdEq.trans hfEq.symm)
        apply Prod.ext
        · exact hFin
        · exact hbool
      · have htan := congrArg Real.tan harg
        simp only [Complex.tan_arg] at htan
        cases hb : d.2 <;> cases hf' : f.2
        · exact (hbool (hb.trans hf'.symm)).elim
        · have hsD := hdSlope.2
          have hsF := hfSlope.2
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsD
          simp only [hf', ↓reduceIte] at hsF
          rw [hsD, hsF] at htan
          have hpos := rampSlope_pos w n
          linarith
        · have hsD := hdSlope.2
          have hsF := hfSlope.2
          simp only [hb, ↓reduceIte] at hsD
          simp only [hf', Bool.false_eq_true, ↓reduceIte] at hsF
          rw [hsD, hsF] at htan
          have hpos := rampSlope_pos w n
          linarith
        · exact (hbool (hb.trans hf'.symm)).elim

private theorem lex_stageRot_resize
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    StageRotation.resize (kmswStage_lex_nextEdge w n hc e es hUL)
      (stageRot w (n + 1)) =
    StageRotation.leftExisting (kmswStage w n).nextEdge (stageRot w n)
      ((⟨e, (stageRotation_UL_bound w n) e (List.mem_of_mem_dropLast
        (List.mem_reverse.mp (by rw [hUL]; simp)))⟩ :
          Fin (kmswStage w n).nextEdge), false)
      ((⟨(kmswStage w n).active, act_lt_nextEdge w (le_refl n)⟩ :
          Fin (kmswStage w n).nextEdge), true) := by
  have ha := act_lt_nextEdge w (le_refl n)
  have hu := stageRotation_UL_bound w n
  have hcCode : kmswCodeStep (w n) = .left := by
    rw [hc]
    rfl
  have htab := StageRotation.step_leftExisting (kmswStage w n) ha hu
    (stageRot w n) (w n) hcCode e es hUL
  rw [stageRot_succ]
  exact htab

private def lexFresh (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (b : Bool) : StageDart (kmswStage w (n + 1)).nextEdge :=
  (⟨(kmswStage w n).nextEdge, by
    rw [kmswStage_lex_nextEdge w n hc e es hUL]
    omega⟩, b)

private theorem unresize_eval {k l : ℕ} (h : k = l)
    (τ : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (ht : StageRotation.resize h τ = σ) (d : StageDart l) :
    τ (Fin.cast h.symm d.1, d.2) =
      (Fin.cast h.symm (σ d).1, (σ d).2) := by
  cases h
  exact congrArg (fun ρ => ρ d) ht

private theorem lex_rotation_old
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageRot w (n + 1) (stageDartIncl w n d) =
      if d = (⟨e, (stageRotation_UL_bound w n) e
          (List.mem_of_mem_dropLast
            (List.mem_reverse.mp (by rw [hUL]; simp)))⟩, false) then
        lexFresh w n hc e es hUL false
      else if stageRot w n d =
          (⟨(kmswStage w n).active, act_lt_nextEdge w (le_refl n)⟩, true) then
        lexFresh w n hc e es hUL true
      else stageDartIncl w n (stageRot w n d) := by
  let k := (kmswStage w n).nextEdge
  have ht := lex_stageRot_resize w n hc e es hUL
  have hh := unresize_eval _ _ _ ht (StageRotation.allocation k 1 (.inl d))
  rw [StageRotation.leftExisting_old] at hh
  split_ifs at hh ⊢ <;>
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lexFresh] using hh

private theorem lex_rotation_new
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    stageRot w (n + 1) (lexFresh w n hc e es hUL false) =
        (if stageRot w n
            ((⟨e, (stageRotation_UL_bound w n) e
              (List.mem_of_mem_dropLast
                (List.mem_reverse.mp (by rw [hUL]; simp)))⟩), false) =
                (⟨(kmswStage w n).active,
                  act_lt_nextEdge w (le_refl n)⟩, true) then
          lexFresh w n hc e es hUL true else
          stageDartIncl w n (stageRot w n
            ((⟨e, (stageRotation_UL_bound w n) e
              (List.mem_of_mem_dropLast
                (List.mem_reverse.mp (by rw [hUL]; simp)))⟩), false))) ∧
      stageRot w (n + 1) (lexFresh w n hc e es hUL true) =
        stageDartIncl w n
          (⟨(kmswStage w n).active, act_lt_nextEdge w (le_rfl)⟩, true) := by
  let k := (kmswStage w n).nextEdge
  have ht := lex_stageRot_resize w n hc e es hUL
  have hh0 := unresize_eval _ _ _ ht (StageRotation.allocation k 1 (.inr (0, false)))
  have hh1 := unresize_eval _ _ _ ht (StageRotation.allocation k 1 (.inr (0, true)))
  have htable := StageRotation.leftExisting_new k (stageRot w n)
    (⟨e, (stageRotation_UL_bound w n) e
      (List.mem_of_mem_dropLast
        (List.mem_reverse.mp (by rw [hUL]; simp)))⟩, false)
    (⟨(kmswStage w n).active, act_lt_nextEdge w (le_rfl)⟩, true)
  constructor
  · rw [htable.1] at hh0
    split_ifs at hh0 ⊢ <;>
      simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lexFresh] using hh0
  · rw [htable.2] at hh1
    simpa [StageRotation.allocation, stageDartIncl, Fin.castLE, lexFresh] using hh1

private theorem lex_dart_cases
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    (∃ d₀, d = stageDartIncl w n d₀) ∨
      d = lexFresh w n hc e es hUL false ∨
      d = lexFresh w n hc e es hUL true := by
  rcases d with ⟨i, b⟩
  by_cases hi : i.val < (kmswStage w n).nextEdge
  · exact Or.inl ⟨(⟨i.val, hi⟩, b), rfl⟩
  · have hcount := kmswStage_lex_nextEdge w n hc e es hUL
    have hb := i.isLt
    have heq : i.val = (kmswStage w n).nextEdge := by omega
    cases b
    · exact Or.inr (Or.inl (Prod.ext (Fin.ext (by
        simp only [lexFresh]
        exact heq)) rfl))
    · exact Or.inr (Or.inr (Prod.ext (Fin.ext (by
        simp only [lexFresh]
        exact heq)) rfl))

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. -/
theorem layoutGood_succ_lex_interior_disjoint
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d f : StageDart (kmswStage w (n + 1)).nextEdge,
      f ≠ d → f ≠ edgeFlip _ d →
      Disjoint (layoutDart w (n + 1) d).interior
        (layoutDart w (n + 1) f).interior :=
  lex_succ_interior_disjoint w n hc e es hUL G

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. -/
theorem layoutGood_succ_lex_interior_avoids_vertices
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      layoutPos w (n + 1) v.val ∉ (layoutDart w (n + 1) d).interior :=
  lex_succ_interior_avoids_vertices w n hc e es hUL G

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. -/
theorem layoutGood_succ_lex_initial_arg_injective
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d f : StageDart (kmswStage w (n + 1)).nextEdge,
      stageVertex w (n + 1) d = stageVertex w (n + 1) f →
      Complex.arg (layoutDart w (n + 1) d).initialDirection =
        Complex.arg (layoutDart w (n + 1) f).initialDirection → d = f :=
  lex_succ_initial_arg_injective w n hc e es hUL G

private theorem lex_insert_args_injective
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (v : Fin (kmswStage w n).nextVertex)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hslope : (layoutDart w (n + 1) x).initialDirection.im /
      (layoutDart w (n + 1) x).initialDirection.re = rampSlope w n ∨
      (layoutDart w (n + 1) x).initialDirection.im /
        (layoutDart w (n + 1) x).initialDirection.re = -rampSlope w n) :
    ∀ a ∈ insert x (stageDartIncl w n ''
        {d | stageVertex w n d = v}),
      ∀ b ∈ insert x (stageDartIncl w n ''
        {d | stageVertex w n d = v}),
        a ≠ b → Complex.arg (layoutDart w (n + 1) a).initialDirection ≠
          Complex.arg (layoutDart w (n + 1) b).initialDirection := by
  have hnew (d : StageDart (kmswStage w n).nextEdge) :
      Complex.arg (layoutDart w (n + 1) x).initialDirection ≠
        Complex.arg (layoutDart w (n + 1) (stageDartIncl w n d)).initialDirection := by
    intro harg
    have hs := congrArg Real.tan harg
    simp only [Complex.tan_arg, layoutDart_succ_lex_old] at hs
    have hbound := layoutDart_old_initial_slope_bounds w n d
    rw [layoutDart_succ_lex_old] at hbound
    rcases hslope with hplus | hminus
    · rw [hplus] at hs
      linarith only [hs, hbound.1, hbound.2]
    · rw [hminus] at hs
      linarith only [hs, hbound.1, hbound.2]
  rintro a (rfl | ⟨a, ha, rfl⟩) b (rfl | ⟨b, hb, rfl⟩) hne
  · exact (hne rfl).elim
  · exact hnew b
  · exact (hnew a).symm
  · intro harg
    have hv : stageVertex w (n + 1) (stageDartIncl w n a) =
        stageVertex w (n + 1) (stageDartIncl w n b) := by
      rw [stageVertex_incl_eq, stageVertex_incl_eq, ha, hb]
    have hab := layoutGood_succ_lex_initial_arg_injective w n hc e es hUL G
      (stageDartIncl w n a) (stageDartIncl w n b) hv
      (by simpa only [layoutDart_succ_lex_old] using harg)
    exact hne hab

private theorem lex_preserve_old {w : ℕ → Fin 3} {n : ℕ} (hc : w n = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (d p : StageDart (kmswStage w n).nextEdge)
    (x : StageDart (kmswStage w (n + 1)).nextEdge)
    (hx : x.1.val ∈ freshEdges w n)
    (hv : stageVertex w (n + 1) (stageDartIncl w n d) =
      stageVertex w (n + 1) (stageDartIncl w n p))
    (hne : d ≠ p)
    (hnew : CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n p)}
      (fun f => (layoutDart w (n + 1) f).initialDirection) (stageDartIncl w n p) x) :
    CcwSuccessor
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)}
      (fun f => (layoutDart w (n + 1) f).initialDirection)
      (stageDartIncl w n d) (stageDartIncl w n (stageRot w n d)) := by
  have hxd := hnew.2.2.1.trans hv.symm
  have hs := stageStar_eq_insert_old_star w n d x hx hxd
  rw [hs]
  apply successor_insert_other _ _ _ _ (stageDartIncl w n p) x
    (G.old_star_rotation_agreement d)
  · rw [← hs]
    simpa only [hv] using hnew
  · exact ⟨p.1.isLt, hv.symm⟩
  · intro he
    apply hne
    apply Prod.ext
    · exact Fin.ext (congrArg (fun f => f.1.val) he)
    · exact congrArg
        (fun f : StageDart (kmswStage w (n + 1)).nextEdge => f.2) he
  · intro he
    have hlo := he.1
    have hhi := (Finset.mem_Ico.mp hx).1
    omega
  · intro a ha b hb hab harg
    rw [← hs] at ha hb
    exact hab (layoutGood_succ_lex_initial_arg_injective w n hc e es hUL G a b
      (ha.trans hb.symm) harg)

private theorem lex_star_unaffected (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (d : StageDart (kmswStage w n).nextEdge)
    (ht : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (lexFresh w n hc e es hUL false))
    (hv : stageVertex w (n + 1) (stageDartIncl w n d) ≠
      stageVertex w (n + 1) (lexFresh w n hc e es hUL true)) :
    {f | stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} =
      {f : StageDart (kmswStage w (n + 1)).nextEdge |
        f.1.val < (kmswStage w n).nextEdge ∧
          stageVertex w (n + 1) f = stageVertex w (n + 1) (stageDartIncl w n d)} := by
  ext f
  constructor
  · intro hf
    refine ⟨?_, hf⟩
    rcases lex_dart_cases w n hc e es hUL f with ⟨g, rfl⟩ | rfl | rfl
    · exact g.1.isLt
    · exact False.elim (ht hf.symm)
    · exact False.elim (hv hf.symm)
  · exact fun hf => hf.2

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. Rotation agreement for the existing-predecessor left step of `def-kmsw`, -/
theorem layoutGood_succ_lex_rotation_agreement (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      CcwSuccessor
        {e | stageVertex w (n + 1) e = stageVertex w (n + 1) d}
        (fun e => (layoutDart w (n + 1) e).initialDirection)
        d (stageRot w (n + 1) d) := by
  have heUL : e ∈ (kmswStage w n).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hUL]; simp))
  let E : Fin (kmswStage w n).nextEdge := ⟨e, stageRotation_UL_bound w n e heUL⟩
  let act : Fin (kmswStage w n).nextEdge :=
    ⟨(kmswStage w n).active, act_lt_nextEdge w (le_rfl)⟩
  let a : StageDart (kmswStage w n).nextEdge := (E, false)
  let A : StageDart (kmswStage w n).nextEdge := (act, true)
  let p := (stageRot w n).symm A
  let x := lexFresh w n hc e es hUL false
  let y := lexFresh w n hc e es hUL true
  have he : E.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR :=
    lex_predecessor_mem_upper w n e es hUL
  have hact : act.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR :=
    lex_active_mem_upper w n
  have hx : x.1.val ∈ freshEdges w n := lex_fresh_edge w n hc e es hUL
  have hy : y.1.val ∈ freshEdges w n := lex_fresh_edge w n hc e es hUL
  have hends := kmswStage_lex_chord_endpoints w n hc e es hUL
  have hxv : stageVertex w (n + 1) x =
      stageVertex w (n + 1) (stageDartIncl w n a) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact hends.1
  have hyv : stageVertex w (n + 1) y =
      stageVertex w (n + 1) (stageDartIncl w n A) := by
    rw [stageVertex_incl_eq]
    apply Fin.ext
    exact hends.2
  have hne : stageVertex w n a ≠ stageVertex w n A := by
    intro hv
    have hh := congrArg Fin.val hv
    change (kmswStage w n).west e = (kmswStage w n).east (kmswStage w n).active at hh
    have hs := kmswStageRank_strict w (n + 1) (kmswStage w n).nextEdge
      (Finset.mem_Ico.mp hx).2
    rw [hends.1, hends.2, hh] at hs
    exact lt_irrefl _ hs
  have hrot : stageRot w n a ≠ A := by
    intro hh
    have hv := P.vert_rotation a
    rw [hh] at hv
    exact hne hv.symm
  have hp : stageRot w n p = A := (stageRot w n).apply_symm_apply A
  have hpv : stageVertex w n p = stageVertex w n A := by
    have hh := P.vert_rotation p
    rw [hp] at hh
    exact hh.symm
  have hE := G.east_roof_insertion_successors E he x hx rfl hxv
  have hW := G.west_roof_insertion_successors act hact y hy rfl (by
    rintro ⟨_, _, hh⟩
    change (kmswStage w n).nextEdge = (kmswStage w n).nextEdge + 1 at hh
    omega) hyv
  have hr := lex_rotation_new w n hc e es hUL
  change stageRot w (n + 1) x =
      (if stageRot w n a = A then y else stageDartIncl w n (stageRot w n a)) ∧
    stageRot w (n + 1) y = stageDartIncl w n A at hr
  rw [ite_eq_right hrot] at hr
  have hrold (d : StageDart (kmswStage w n).nextEdge) :
      stageRot w (n + 1) (stageDartIncl w n d) =
        if d = a then x else if stageRot w n d = A then y
          else stageDartIncl w n (stageRot w n d) := lex_rotation_old w n hc e es hUL d
  intro d
  rcases lex_dart_cases w n hc e es hUL d with ⟨d, rfl⟩ | rfl | rfl
  · rw [hrold]
    by_cases hda : d = a
    · subst d
      rw [ite_eq_left rfl]
      exact hE.1
    · rw [ite_eq_right hda]
      by_cases hdA : stageRot w n d = A
      · rw [ite_eq_left hdA]
        have hdp : d = p := (stageRot w n).injective (hdA.trans hp.symm)
        subst d
        have hv : stageVertex w (n + 1) (stageDartIncl w n p) =
            stageVertex w (n + 1) (stageDartIncl w n A) := by
          rw [stageVertex_incl_eq, stageVertex_incl_eq, hpv]
        simpa only [hv] using hW.1
      · rw [ite_eq_right hdA]
        by_cases hdu : stageVertex w (n + 1) (stageDartIncl w n d) =
            stageVertex w (n + 1) (stageDartIncl w n a)
        · exact lex_preserve_old hc e es hUL G d a x hx hdu hda hE.1
        · by_cases hdv : stageVertex w (n + 1) (stageDartIncl w n d) =
              stageVertex w (n + 1) (stageDartIncl w n A)
          · have hv : stageVertex w (n + 1) (stageDartIncl w n d) =
                stageVertex w (n + 1) (stageDartIncl w n p) := by
              rw [stageVertex_incl_eq, stageVertex_incl_eq, hpv]
              simpa only [stageVertex_incl_eq] using hdv
            have hdp : d ≠ p := fun hh => hdA (hh ▸ hp)
            have hW' : CcwSuccessor
                {f | stageVertex w (n + 1) f =
                  stageVertex w (n + 1) (stageDartIncl w n p)}
                (fun f => (layoutDart w (n + 1) f).initialDirection)
                (stageDartIncl w n p) y := by
              simpa only [stageVertex_incl_eq, hpv] using hW.1
            exact lex_preserve_old hc e es hUL G d p y hy hv hdp hW'
          · rw [lex_star_unaffected w n hc e es hUL d
              (fun hh => hdu (hh.trans hxv)) (fun hh => hdv (hh.trans hyv))]
            exact G.old_star_rotation_agreement d
  · rw [hr.1]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) x}
      (fun f => (layoutDart w (n + 1) f).initialDirection) x _
    rw [hxv]
    exact hE.2
  · rw [hr.2]
    change CcwSuccessor {f | stageVertex w (n + 1) f = stageVertex w (n + 1) y}
      (fun f => (layoutDart w (n + 1) f).initialDirection) y _
    rw [hyv]
    exact hW.2

/-- Helper toward the plane-realization obligation of adjudication n308;
not a paper result. The good layout for the existing-predecessor left step -/
theorem layoutGood_succ_lex (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w n).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    LayoutGood w (n + 1) where
  interior_disjoint := layoutGood_succ_lex_interior_disjoint w n hc e es hUL G
  interior_avoids_vertices := layoutGood_succ_lex_interior_avoids_vertices w n hc e es hUL G
  initial_arg_injective := layoutGood_succ_lex_initial_arg_injective w n hc e es hUL G
  rotation_agreement := layoutGood_succ_lex_rotation_agreement w n hc e es hUL G

end DirectedDistances.KMSW
