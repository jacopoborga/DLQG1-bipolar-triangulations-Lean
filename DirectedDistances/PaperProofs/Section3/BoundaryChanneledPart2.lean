/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPart1
public import DirectedDistances.PlanarMap.D39DrawingRepresentation2

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

private theorem boundaryChanneledCcwSuccessorEquiv_part2
    {D D' : Type*} {star : Set D} {star' : Set D'}
    {dir : D → ℂ} {dir' : D' → ℂ} {d r : D} {d' r' : D'}
    (e : D ≃ D') (hstar : ∀ x, e x ∈ star' ↔ x ∈ star)
    (hdir : ∀ x, dir' (e x) = dir x)
    (hd : d' = e d) (hr : r' = e r)
    (h : CcwSuccessor star dir d r) : CcwSuccessor star' dir' d' r' := by
  have hset : star' = e '' star := by
    ext y
    constructor
    · intro hy
      have hy' : e (e.symm y) ∈ star' := by simpa using hy
      exact ⟨e.symm y, (hstar _).mp hy', e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hstar x).mpr hx
  rcases h with ⟨hfinite, hdmem, hrmem, hcase⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hset]; exact hfinite.image e
  · rw [hset]; exact ⟨d, hdmem, hd.symm⟩
  · rw [hset]; exact ⟨r, hrmem, hr.symm⟩
  · rcases hcase with ⟨heq, hsingleton⟩ | ⟨hne, hmin⟩
    · left
      refine ⟨?_, ?_⟩
      · calc r' = e r := hr
            _ = e d := congrArg e heq
            _ = d' := hd.symm
      · ext y
        constructor
        · intro hy
          rw [hset] at hy
          rcases hy with ⟨x, hx, hxy⟩
          rw [hsingleton] at hx
          subst x
          exact hxy.symm.trans hd.symm
        · intro hy
          rw [hset]
          refine ⟨d, ?_, ?_⟩
          · rw [hsingleton]; rfl
          · have hy' : y = d' := by simpa using hy
            exact hd.symm.trans hy'.symm
    · right
      refine ⟨?_, ?_⟩
      · intro heq
        apply hne
        apply e.injective
        calc e r = r' := hr.symm
          _ = d' := heq
          _ = e d := hd
      · intro f hf hfd
        rw [hset] at hf
        rcases hf with ⟨x, hx, hxf⟩
        have hxd : x ≠ d := by
          intro hxd
          apply hfd
          calc f = e x := hxf.symm
            _ = e d := congrArg e hxd
            _ = d' := hd.symm
        have hs := hmin x hx hxd
        calc
          ccwTurn (dir' d') (dir' r') = ccwTurn (dir d) (dir r) := by
            rw [hd, hr, hdir d, hdir r]
          _ ≤ ccwTurn (dir d) (dir x) := hs
          _ = ccwTurn (dir' d') (dir' f) := by
            rw [hd, ← hxf, hdir d, hdir x]

/-- Helper toward Definition 3.2: the two nonempty sides have canonical
finite positions, upper-left followed by reversed lower-right. -/
@[expose] def boundaryChanneledPositionEquiv_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R) :
    InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation ≃ Fin (l + r) where
  toFun i := match i with
    | .upperLeft a => ⟨a.val, by omega⟩
    | .upperRight a => a.elim
    | .lowerRight a => ⟨l + a.val, by omega⟩
    | .lowerLeft a => a.elim
  invFun i := if h : i.val < l then .upperLeft ⟨i.val, h⟩
    else .lowerRight ⟨i.val - l, by omega⟩
  left_inv i := by
    cases i with
    | upperLeft a =>
      simp only [a.is_lt, dite_true]
      rfl
    | upperRight a => exact a.elim
    | lowerRight a =>
      simp only [show ¬ l + a.val < l by omega, dite_false, Nat.add_sub_cancel_left]
      rfl
    | lowerLeft a => exact a.elim
  right_inv i := by
    by_cases h : i.val < l
    · simp only [h, dite_true]
    · simp only [h, dite_false]
      apply Fin.ext
      change l + (i.val - l) = i.val
      omega

private theorem boundaryChanneled_indexed_outer_get_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (i : InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation) :
    let L := R.B.leftPath.darts ++
      R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv
    let p := boundaryChanneledPositionEquiv_part2 R G
    boundaryChanneledDartPairEquiv19 G (L[p i |>.val]'(by
      simp [L, R.B.leftPath.darts_length, R.B.rightPath.darts_length, (p i).is_lt])) =
      InfiniteBoundaryDartIndex.dart
        (boundaryChanneledPresentationWithJunctions R G).presentation i := by
  dsimp only
  cases i with
  | upperLeft a =>
    simp only [InfiniteBoundaryDartIndex.dart_eq]
    change boundaryChanneledDartPairEquiv19 G
      ((R.B.leftPath.darts ++
        R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv)[a.val]'(by simp only [List.length_append, List.length_map, List.length_reverse, R.B.leftPath.darts_length, R.B.rightPath.darts_length]; omega)) = _
    rw [List.getElem_append_left (by simpa only [R.B.leftPath.darts_length] using a.is_lt)]
    exact boundaryChanneledLeftDart_eq_encodedPath20 R G a
  | upperRight a => exact a.elim
  | lowerRight a =>
    simp only [InfiniteBoundaryDartIndex.dart_eq]
    change boundaryChanneledDartPairEquiv19 G
      ((R.B.leftPath.darts ++
        R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv)[l + a.val]'(by simp only [List.length_append, List.length_map, List.length_reverse, R.B.leftPath.darts_length, R.B.rightPath.darts_length]; omega)) = _
    rw [List.getElem_append_right (by rw [R.B.leftPath.darts_length]; omega)]
    simp only [R.B.leftPath.darts_length, Nat.add_sub_cancel_left, List.getElem_map]
    exact boundaryChanneledRightDart_eq_encodedReverse20 R G a
  | lowerLeft a => exact a.elim

/-- Helper toward Definition 3.2: source face succession advances exactly
one position in the supplied two-path outer cycle, including its closing step. -/
theorem boundaryChanneled_sourceCyclicOrder_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R) :
    let P := (boundaryChanneledPresentationWithJunctions R G).presentation
    let E := boundaryChanneledDartPairEquiv19 G
    let p := boundaryChanneledPositionEquiv_part2 R G
    ∀ i j : InfiniteBoundaryDartIndex P,
      R.B.map.toCombinatorialMap.faceSucc (E.symm (InfiniteBoundaryDartIndex.dart P i)) =
        E.symm (InfiniteBoundaryDartIndex.dart P j) ↔
      p j = boundaryCycleSucc4 (p i) := by
  dsimp only
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let E := boundaryChanneledDartPairEquiv19 G
  let p := boundaryChanneledPositionEquiv_part2 R G
  let L := R.B.leftPath.darts ++
    R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv
  have hlen : L.length = l + r := by
    simp only [L, List.length_append, List.length_map, List.length_reverse,
      R.B.leftPath.darts_length, R.B.rightPath.darts_length]
  have hnd : L.Nodup := by
    simpa only [L, List.append_nil] using
      R.B.outerSplit.2.1.perm.nodup_iff.mp R.B.outerWord.nodup
  have hget (i : InfiniteBoundaryDartIndex P) :
      E.symm (InfiniteBoundaryDartIndex.dart P i) =
        L[(p i).val]'(by rw [hlen]; exact (p i).is_lt) := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact (boundaryChanneled_indexed_outer_get_part2 R G i).symm
  intro i j
  have hi : (p i).val < L.length := by rw [hlen]; exact (p i).is_lt
  have himem : L[(p i).val]'hi ∈ R.B.outerWord.letters := by
    apply R.B.outerSplit.2.1.perm.mem_iff.mpr
    simpa only [L, List.append_nil] using List.getElem_mem hi
  have hsucc : R.B.map.toCombinatorialMap.faceSucc L[(p i).val] =
      L[((p i).val + 1) % L.length]'(Nat.mod_lt _ (by omega)) := by
    calc
      _ = R.B.outerWord.letters.formPerm L[(p i).val] :=
        R.B.outerSplit.1.2.2 _ himem
      _ = L.formPerm L[(p i).val] := by
        have hperm := List.formPerm_eq_of_isRotated R.B.outerWord.nodup R.B.outerSplit.2.1
        simpa only [L, List.append_nil] using congrArg (fun f : Equiv.Perm (Fin R.dartCount) => f L[(p i).val]) hperm
      _ = _ := List.formPerm_apply_getElem L hnd (p i).val hi
  rw [hget i, hget j, hsucc]
  constructor
  · intro h
    apply Fin.ext
    have heq := (List.Nodup.getElem_inj_iff hnd).mp h
    change (p j).val = ((p i).val + 1) % (l + r)
    simpa only [hlen] using heq.symm
  · intro h
    have hv := congrArg Fin.val h
    change (p j).val = ((p i).val + 1) % (l + r) at hv
    have hv' : (p j).val = ((p i).val + 1) % L.length := by simpa only [hlen] using hv
    simp only [hv']

/-- Helper toward Definition 3.2: the canonical positions provide the exact
finite cyclic side order for the encoded source face successor. -/
theorem boundaryChanneled_sourceFinitePositionOrder_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R) :
    let E := boundaryChanneledDartPairEquiv19 G
    FiniteBoundaryPositionOrder4
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => E (R.B.map.toCombinatorialMap.faceSucc (E.symm d))) := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let E := boundaryChanneledDartPairEquiv19 G
  let p := boundaryChanneledPositionEquiv_part2 R G
  have hpos : 0 < l + r := by have := R.B.left_length_pos; omega
  let cut : Fin (l + r) := ⟨0, hpos⟩
  have hoff (i : Fin (l + r)) : boundaryCycleOffset4 cut i = i.val := by
    simp only [boundaryCycleOffset4, cut, Nat.sub_zero, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.is_lt]
  refine ⟨l + r, p, ?_, Or.inr ⟨cut, ?_, ?_⟩⟩
  · intro i j
    rw [← Equiv.eq_symm_apply]
    exact boundaryChanneled_sourceCyclicOrder_part2 R G i j
  · intro a b hab
    obtain ⟨i, rfl⟩ := p.surjective a
    obtain ⟨j, rfl⟩ := p.surjective b
    rw [hoff, hoff] at hab
    simp only [Equiv.symm_apply_apply]
    cases i <;> cases j <;> rename_i i j
    all_goals try { first
      | (change Empty at i; cases i)
      | (change Empty at j; cases j) }
    all_goals simp only [sideTag]
    all_goals try omega
    case lowerRight.upperLeft =>
      change l + i.val ≤ j.val at hab
      have hj : j.val < l := j.is_lt
      omega
  · intro i j
    rw [hoff, hoff]
    cases i <;> cases j <;> rename_i a b
    all_goals try { first
      | (change Empty at a; cases a)
      | (change Empty at b; cases b) }
    all_goals simp [sideNext, sideTag, p,
      boundaryChanneledPositionEquiv_part2, boundaryChanneledPresentationWithJunctions]
    case upperLeft.upperLeft =>
      change (∃ h : a.val + 1 < l,
        InfiniteBoundaryDartIndex.upperLeft (P := P) ⟨a.val + 1, h⟩ =
          InfiniteBoundaryDartIndex.upperLeft b) ↔ b.val = a.val + 1
      constructor
      · rintro ⟨h, heq⟩
        injection heq with heq
        exact (congrArg Fin.val heq).symm
      · intro h
        exact ⟨by omega, congrArg InfiniteBoundaryDartIndex.upperLeft (Fin.ext h.symm)⟩
    case lowerRight.lowerRight =>
      change (∃ h : a.val + 1 < r,
        InfiniteBoundaryDartIndex.lowerRight (P := P) ⟨a.val + 1, h⟩ =
          InfiniteBoundaryDartIndex.lowerRight b) ↔ l + b.val = l + a.val + 1
      constructor
      · rintro ⟨h, heq⟩
        injection heq with heq
        have hv := congrArg Fin.val heq
        dsimp only at hv
        omega
      · intro h
        have hv : b.val = a.val + 1 := by omega
        exact ⟨by omega, congrArg InfiniteBoundaryDartIndex.lowerRight (Fin.ext hv.symm)⟩

private theorem boundaryChanneled_initialDirection_scale_part2
    (p q : Polyline) (hp : p.IsSimple) (hq : q.IsSimple)
    (hlp : 2 ≤ p.points.length) (hlq : 2 ≤ q.points.length)
    (hs : q.start = p.start) (him : q.image = p.image) :
    ∃ c : ℝ, 0 < c ∧ q.initialDirection = c • p.initialDirection := by
  classical
  let K : Set ℂ := ⋃ i : Fin (p.points.length - 1),
    if i.val = 0 then ∅ else p.segmentAt i.val
  have hclosed : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro i
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hnot : p.start ∉ K := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    by_cases hi0 : i.val = 0
    · simp only [ite_eq_left hi0, Set.mem_empty_iff_false] at hi
    · have hip : p.start ∈ p.segmentAt i.val := by simpa only [ite_eq_right hi0] using hi
      exact hi0 (p.segmentAt_index_eq_zero_of_start_mem hp hlp (by omega) hip)
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  let t := min (1 / 2 : ℝ) (r / (2 * (‖q.initialDirection‖ + 1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hmul : t * (2 * (‖q.initialDirection‖ + 1)) ≤ r :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hsmall : t * ‖q.initialDirection‖ < r := by
    nlinarith only [hmul, ht, norm_nonneg q.initialDirection]
  have hqn : q.initialDirection ≠ 0 := by
    intro hz
    exact hq.1 0 (by omega)
      (q.point_zero_eq_start.trans (sub_eq_zero.mp hz).symm)
  let z := q.start + t • q.initialDirection
  have hzq : z ∈ q.image := by
    refine Or.inr ⟨0, by omega, ?_⟩
    rw [Polyline.segmentAt, q.point_zero_eq_start, segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
  have hzball : z ∈ Metric.ball p.start r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖q.start + t • q.initialDirection - p.start‖ < r
    rw [hs, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact hsmall
  have hznot : z ≠ p.start := by
    intro heq
    have hh : t • q.initialDirection = 0 := by
      have : p.start + t • q.initialDirection = p.start := by simpa only [z, hs] using heq
      exact add_eq_left.mp this
    exact (smul_ne_zero ht.ne' hqn) hh
  have hzp : z ∈ p.image := him ▸ hzq
  rcases hzp with hzp | ⟨i, hi, hzi⟩
  · exact (hznot hzp).elim
  have hi0 : i = 0 := by
    by_contra hne
    apply hball hzball
    exact Set.mem_iUnion.mpr ⟨⟨i, by omega⟩, by simpa only [ite_eq_right hne] using hzi⟩
  subst i
  rw [Polyline.segmentAt, p.point_zero_eq_start, segment_eq_image'] at hzi
  obtain ⟨s, hs01, hsz⟩ := hzi
  have hdirs : s • p.initialDirection = t • q.initialDirection := by
    apply add_left_cancel (a := p.start)
    simpa only [z, hs, Polyline.initialDirection] using hsz
  have hspos : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs01.1
    rw [hs0, zero_smul] at hdirs
    exact (smul_ne_zero ht.ne' hqn) hdirs.symm
  refine ⟨s / t, div_pos hspos ht, ?_⟩
  calc
    q.initialDirection = (1 / t) • (t • q.initialDirection) := by
      rw [smul_smul, one_div_mul_cancel ht.ne', one_smul]
    _ = (1 / t) • (s • p.initialDirection) := by rw [hdirs]
    _ = (s / t) • p.initialDirection := by rw [smul_smul]; congr 1; ring

/-- Helper toward Definition 3.2: every compatible drawing preserves the
initial point and the oriented initial ray of each source dart. -/
theorem boundaryChanneled_drawsMap_initialRays_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hdraw : DrawsMap (boundaryChanneledPlaneMap R G) H) (d : Fin R.dartCount) :
    (H.arc (boundaryChanneledDartPairEquiv19 G d)).start = (G.arc d).start ∧
    ∃ c : ℝ, 0 < c ∧
      (H.arc (boundaryChanneledDartPairEquiv19 G d)).initialDirection =
        c • (G.arc d).initialDirection := by
  let e := boundaryChanneledDartPairEquiv19 G
  have hs : (H.arc (e d)).start = (G.arc d).start := by
    rw [H.arc_start, hdraw.1, boundaryChanneledDartPairEquiv19_initial, G.arc_start]
    rfl
  refine ⟨hs, ?_⟩
  apply boundaryChanneled_initialDirection_scale_part2 (G.arc d) (H.arc (e d))
    (G.arc_simple d) (H.arc_simple (e d)) (G.arc_length d) (H.arc_length (e d)) hs
  rw [← Polyline.range_toPath, hdraw.2]
  exact G.toPlaneGraphDrawing_arc_range d

private theorem boundaryChanneled_border_scale_part2
    (p q : Polyline) (F : Set ℂ) (hs : q.start = p.start)
    (c : ℝ) (hc : 0 < c) (hdir : q.initialDirection = c • p.initialDirection)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
      p.start + (t : ℂ) * (p.initialDirection + (ε : ℂ) * Complex.I * p.initialDirection) ∈ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
      q.start + (t : ℂ) * (q.initialDirection + (ε : ℂ) * Complex.I * q.initialDirection) ∈ F := by
  obtain ⟨δ, hδ, hh⟩ := h
  refine ⟨min δ (δ / c), lt_min hδ (div_pos hδ hc), ?_⟩
  intro t ε ht htδ hε hεδ
  have htc : t * c < δ := (lt_div_iff₀ hc).mp (htδ.trans_le (min_le_right _ _))
  have hh' := hh (t * c) ε (mul_pos ht hc) htc hε (hεδ.trans_le (min_le_left _ _))
  convert hh' using 1
  rw [hs, hdir, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Helper toward Definition 3.2: every drawing of this map has the same
external bordering darts as the supplied four-part presentation. -/
theorem boundaryChanneled_drawsMap_dartCoverage_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face)
    (hdraw : DrawsMap (boundaryChanneledPlaneMap R G) H) (hU : H.IsUnbounded U) :
    ∀ d, H.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation,
      InfiniteBoundaryDartIndex.dart
        (boundaryChanneledPresentationWithJunctions R G).presentation i = d := by
  let E := boundaryChanneledDartPairEquiv19 G
  have hval := boundaryChanneled_transport_unboundedFace_eq_marked R G hOuterUnbounded
    rot H hdraw U hU
  intro d
  obtain ⟨hs, c, hc, hdir⟩ := boundaryChanneled_drawsMap_initialRays_part2 R G rot H hdraw (E.symm d)
  have ht : H.dartBorders d U ↔ G.dartBorders (E.symm d)
      (boundaryChanneledMarkedOuterFace R G) := by
    have he : E (E.symm d) = d := E.apply_symm_apply d
    change (H.arc (E (E.symm d))).start = _ at hs
    change (H.arc (E (E.symm d))).initialDirection = _ at hdir
    rw [he] at hs hdir
    constructor
    · intro hd
      have hreverse : (G.arc (E.symm d)).initialDirection =
          (1 / c) • (H.arc d).initialDirection := by
        rw [hdir, smul_smul, one_div_mul_cancel hc.ne', one_smul]
      have hh := boundaryChanneled_border_scale_part2 (H.arc d) (G.arc (E.symm d))
        U.val hs.symm (1 / c) (one_div_pos.mpr hc) hreverse hd
      simpa only [PLDrawing.dartBorders, hval] using hh
    · intro hd
      have hh := boundaryChanneled_border_scale_part2 (G.arc (E.symm d)) (H.arc d)
        (boundaryChanneledMarkedOuterFace R G).val hs c hc hdir hd
      simpa only [PLDrawing.dartBorders, hval] using hh
  exact ht.trans ((boundaryChanneled_markedOuterFace_borders_iff_indexed20 R G d).trans
    (boundaryChanneledPresentation_indexRange_iff_leftRight16 R G d).symm)

/-- Helper toward Definition 3.2: equality of oriented edge traces forces
every compatible drawing to have the encoded source rotation. -/
theorem boundaryChanneled_drawsMap_rotation_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hdraw : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    ∀ d, rot (boundaryChanneledDartPairEquiv19 G d) =
      boundaryChanneledDartPairEquiv19 G (R.B.map.toCombinatorialMap.rot d) := by
  let E := boundaryChanneledDartPairEquiv19 G
  have hargs (d : Fin R.dartCount) :
      (H.arc (E d)).initialDirection.arg = (G.arc d).initialDirection.arg := by
    obtain ⟨_, c, hc, hdir⟩ := boundaryChanneled_drawsMap_initialRays_part2 R G rot H hdraw d
    rw [hdir, Complex.real_smul, Complex.arg_real_mul _ hc]
  intro d
  have hsource : CcwSuccessor {x | dartTailVertex R.B.map x = dartTailVertex R.B.map d}
      (fun x => (H.arc (E x)).initialDirection) d (R.B.map.toCombinatorialMap.rot d) := by
    obtain ⟨hfin, hd, hr, hcase⟩ := G.rotation_agreement d
    refine ⟨hfin, hd, hr, ?_⟩
    rcases hcase with hh | ⟨hne, hmin⟩
    · exact Or.inl hh
    · refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      simpa only [ccwTurn, hargs] using hmin f hf hfd
  have htransfer : CcwSuccessor
      {x | boundaryDartInitial (boundaryChanneledPlaneMap R G) x =
        boundaryDartInitial (boundaryChanneledPlaneMap R G) (E d)}
      (fun x => (H.arc x).initialDirection) (E d)
      (E (R.B.map.toCombinatorialMap.rot d)) := by
    apply boundaryChanneledCcwSuccessorEquiv_part2 E
      (fun x => ?_) (fun _ => rfl) rfl rfl hsource
    simp only [Set.mem_ofPred_eq, E, boundaryChanneledDartPairEquiv19_initial]
  apply d39CcwSuccessor_unique _ (H.rotation_agreement (E d)) htransfer
  intro x hx y hy harg
  exact H.initial_arg_injective x y (hx.trans hy.symm) harg

/-- Helper toward Definition 3.2: every compatible drawing satisfies the
exact finite cyclic-position clause of Package3, without a side-order premise. -/
theorem boundaryChanneled_drawsMap_finitePositionOrder_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hdraw : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    FiniteBoundaryPositionOrder4
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => rot.symm (d.1, !d.2)) := by
  let E := boundaryChanneledDartPairEquiv19 G
  have hrot := boundaryChanneled_drawsMap_rotation_part2 R G rot H hdraw
  have hs : (fun d : G.GeometricEdge × Bool => rot.symm (d.1, !d.2)) =
      fun d => E (R.B.map.toCombinatorialMap.faceSucc (E.symm d)) := by
    funext d
    apply rot.injective
    rw [rot.apply_symm_apply, hrot]
    change (d.1, !d.2) = E (R.B.map.toCombinatorialMap.rot
      (R.B.map.toCombinatorialMap.rot.symm (R.B.map.toCombinatorialMap.edgeInv (E.symm d))))
    rw [Equiv.apply_symm_apply, boundaryChanneledDartPairEquiv19_flip]
    simp only [E, Equiv.apply_symm_apply]
  rw [hs]
  exact boundaryChanneled_sourceFinitePositionOrder_part2 R G

/-- Helper toward Definition 3.2: all exact open binders of Package3 are
discharged for the boundary-channeled representation, including its universal
drawing clauses. The marked face's unboundedness remains geometric input. -/
theorem exists_boundaryChanneled_finite_bound_edges32_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    let M := boundaryChanneledPlaneMap R G
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : H.Face) (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R G ∧ DrawsMap M H ∧
        IsFiniteExternalFaceIntervalOrder7 M B H U S := by
  apply exists_boundaryChanneled_bound_edges32_of_open_clauses3 R G
  · obtain ⟨rot, H, hdraw, _⟩ := boundaryChanneled_transport_dart_orientation19 R G
    exact ⟨rot, H, hdraw⟩
  · exact boundaryChanneled_drawsMap_dartCoverage_part2 R G hOuterUnbounded
  · intro rot H U _ hU
    exact boundaryChanneled_geometricSuccessor_part1 R G rot H U hU
  · exact boundaryChanneledPresentation_boundaryOrder_part1 R G hOuterUnbounded
  · exact boundaryChanneledPresentation_ULOkInf22 R G hOuterUnbounded
  · exact boundaryChanneledPresentation_LROkInf22 R G hOuterUnbounded
  · exact boundaryChanneledPresentation_upperLeft_simple R G
  · exact boundaryChanneledPresentation_lowerRight_simple R G
  · exact boundaryChanneledPresentation_upperLeft_endpointLabels6 R G
  · exact boundaryChanneledPresentation_lowerRight_endpointLabels6 R G
  · exact boundaryChanneled_drawsMap_finitePositionOrder_part2 R G
  · exact boundaryChanneledPresentation_requiredJoinEndpointLabels7 R G

/-- Helper toward Definition 3.2: the finite boundary-channeled construction
supplies the full boundary package, with only marked-outer-face unboundedness
as its geometric premise. -/
theorem exists_boundaryChanneled_bound_edges32_part2
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    let M := boundaryChanneledPlaneMap R G
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : H.Face) (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R G ∧ DrawsMap M H ∧
        IsBoundEdges32 M B H U S := by
  classical
  have boundaryChanneledPart2FiniteDarts : Finite (G.GeometricEdge × Bool) :=
    Finite.of_equiv (Fin R.dartCount) (boundaryChanneledDartPairEquiv19 G)
  obtain ⟨B, rot, H, U, S, hB, hdraw, hfinite⟩ :=
    exists_boundaryChanneled_finite_bound_edges32_part2 R G hOuterUnbounded
  exact ⟨B, rot, H, U, S, hB, hdraw,
    (IsBoundEdges32.finite_iff (Set.toFinite _)).mpr hfinite⟩







end DirectedDistances.PaperProofs.Section3

end
