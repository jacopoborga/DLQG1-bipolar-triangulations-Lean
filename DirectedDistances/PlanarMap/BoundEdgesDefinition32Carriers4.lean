/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Carriers3




public section
noncomputable section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW MeasureTheory unitInterval
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

section M0Carrier

variable (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
local notation "M" => m0BoundaryMap32 w hfin h
local notation "G" => m0BoundaryDrawing32 w hfin h
local notation "Q" => BoundaryPresentationWithJunctions.presentation (m0BoundaryPresentation32 w hfin h)

/-- Helper toward Definition 3.2: the supplied dart index has the exact
integer label of its source boundary edge. -/
abbrev m0BoundaryLabel32 : InfiniteBoundaryDartIndex Q → ℤ
  | .upperLeft i => i.elim
  | .upperRight i => i.elim
  | .lowerRight i => i
  | .lowerLeft i => -(i : ℤ) - 1

/-- Helper toward Definition 3.2: every labelled supplied dart is the
existing hit-indexed external dart, including its traversal bit. -/
theorem m0BoundaryLabel32_dart (i : InfiniteBoundaryDartIndex Q) :
    InfiniteBoundaryDartIndex.dart Q i =
      futureMapBoundaryDart w h (m0BoundaryLabel32 w hfin h i) := by
  cases i with
  | upperLeft i => exact i.elim
  | upperRight i => exact i.elim
  | lowerRight i => rw [InfiniteBoundaryDartIndex.dart_eq]; rfl
  | lowerLeft i => rw [InfiniteBoundaryDartIndex.dart_eq]; rfl

/-- Helper toward Definition 3.2: the two supplied rays partition the
integer boundary labels without repetition or omissions. -/
theorem m0BoundaryLabel32_bijective : Function.Bijective (m0BoundaryLabel32 w hfin h) := by
  constructor
  · intro i j hij
    cases i with
    | upperLeft i => exact i.elim
    | upperRight i => exact i.elim
    | lowerRight i =>
      cases j with
      | upperLeft j => exact j.elim
      | upperRight j => exact j.elim
      | lowerRight j =>
        have he : i = j := by
          change (i : ℤ) = (j : ℤ) at hij
          exact_mod_cast hij
        exact congrArg _ he
      | lowerLeft j => change (i : ℤ) = -(j : ℤ) - 1 at hij; omega
    | lowerLeft i =>
      cases j with
      | upperLeft j => exact j.elim
      | upperRight j => exact j.elim
      | lowerRight j => change -(i : ℤ) - 1 = j at hij; omega
      | lowerLeft j =>
        change ℕ at i j
        have he : i = j := by
          change -(i : ℤ) - 1 = -(j : ℤ) - 1 at hij
          simpa only [sub_left_inj, neg_inj, Int.natCast_inj] using hij
        exact congrArg _ he
  · intro k
    by_cases hk : 0 ≤ k
    · exact ⟨.lowerRight k.toNat, Int.toNat_of_nonneg hk⟩
    · refine ⟨.lowerLeft (-k - 1).toNat, ?_⟩
      change -(((-k - 1).toNat : ℕ) : ℤ) - 1 = k
      rw [Int.toNat_of_nonneg (by omega)]
      omega

/-- Helper toward Definition 3.2: even after forgetting traversal bits,
each supplied geometric boundary edge occurs exactly once. -/
theorem m0BoundaryPresentation32_edge_injective :
    Function.Injective (fun i : InfiniteBoundaryDartIndex Q =>
      (InfiniteBoundaryDartIndex.dart Q i).1) := by
  intro i j hij
  dsimp only at hij
  erw [m0BoundaryLabel32_dart, m0BoundaryLabel32_dart] at hij
  exact (m0BoundaryLabel32_bijective w hfin h).1
    (m0BoundaryEdge32_injective w h hij)

/-- Helper toward Definition 3.2: the compatible drawing has one unbounded
face; its darts are precisely the supplied boundary darts, and its geometric
successor decreases the source's integer label. -/
theorem m0BoundaryDrawing32_geometry :
    ∃ U : (G).Face,
      (G).IsUnbounded U ∧ (∀ F : (G).Face, (G).IsUnbounded F → F = U) ∧
      (∀ d, (G).dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
      IsGeometricExternalFaceSucc G U (kmswInfFaceSucc w hfin) ∧
      (∀ d, (G).dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex Q,
        InfiniteBoundaryDartIndex.dart Q i = d) := by
  obtain ⟨U, hU, huniq, _, hborder, _, hsucc⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w hfin h
  refine ⟨U, hU, huniq, hborder, ⟨hU, ?_⟩, ?_⟩
  · intro d hd
    refine ⟨rfl, ?_⟩
    obtain ⟨k, rfl⟩ := (hborder d).mp hd
    exact (hborder _).mpr ⟨k - 1, hsucc k⟩
  · intro d
    change (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d U ↔ _
    rw [hborder]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨i, hi⟩ := (m0BoundaryLabel32_bijective w hfin h).2 k
      exact ⟨i, (m0BoundaryLabel32_dart w hfin h i).trans (congrArg _ hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, m0BoundaryLabel32_dart w hfin h i⟩

private theorem m0Drawing32_surjective : Function.Surjective (boundaryDartInitial M) := by
  rw [m0BoundaryMap32_initial]
  exact kmswLimitDartVertex_surjective w hfin

private theorem m0Drawing32_external_face_eq
    (U : (G).Face) (huniq : ∀ F : (G).Face, (G).IsUnbounded F → F = U)
    (F : (Drawing M).Face) (hF : (Drawing M).IsExternal F) : F.val = U.val := by
  obtain ⟨F', hF'⟩ := (m0BoundaryDrawing32_draws w hfin h).face_from_map F
  have hUn : (G).IsUnbounded F' := by
    intro R
    by_contra hn
    push Not at hn
    exact hF (isBounded_iff_forall_norm_le.mpr ⟨R, by simpa only [hF'] using hn⟩)
  exact hF'.symm.trans (congrArg Subtype.val (huniq F' hUn))

/-- Helper toward Definition 3.2: external frontier incidence agrees
exactly with one of the two dart sides of the same geometric edge. -/
theorem m0BoundaryMap32_frontier_iff
    (U : (G).Face) (hU : (G).IsUnbounded U)
    (huniq : ∀ F : (G).Face, (G).IsUnbounded F → F = U) (e : ℕ) :
    ExternalFrontierEdge M e ↔ (G).dartBorders (e, false) U ∨ (G).dartBorders (e, true) U := by
  rw [externalFrontierEdge_iff]
  constructor
  · rintro ⟨F, hF, harc⟩
    have hFU := m0Drawing32_external_face_eq w hfin h U huniq F hF
    let s : I := ⟨1 / 4, by norm_num⟩
    have hi : 0 + 1 < ((G).arc (e, true)).points.length := by
      have := (G).arc_length (e, true); omega
    have hq := Polyline.toPath_mem_openSegment_of_parameter
      ((G).arc (e, true)) hi s (by norm_num [s, Polyline.segmentParameterStart_zero])
      (by dsimp [s, Polyline.segmentParameterEnd]; split_ifs <;> norm_num)
    have hb := ((G).mem_closure_face_openSegment_iff_dartBorders
      (m0Drawing32_surjective w hfin h) (e, true) U hi hq).mp
    apply Or.symm
    apply hb
    apply frontier_subset_closure
    rw [← hFU]
    apply harc
    rw [← (m0BoundaryDrawing32_draws w hfin h).2 (e, true)]
    exact Set.mem_range_self s
  · intro hb
    obtain ⟨F, hFU, hF⟩ :=
      (m0BoundaryDrawing32_draws w hfin h).unbounded_face_to_external U hU
    refine ⟨F, hF, ?_⟩
    rw [hFU, ← (m0BoundaryDrawing32_draws w hfin h).2 (e, true), Polyline.range_toPath]
    rcases hb with hb | hb
    · have hs := (G).dartBorders_arc_subset_frontier
        (m0Drawing32_surjective w hfin h) (e, false) U hb
      have heq : ((G).arc (e, true)).image = ((G).arc (e, false)).image :=
        (G).arc_image_flip (e, false)
      rw [heq]
      exact hs
    · exact (G).dartBorders_arc_subset_frontier (m0Drawing32_surjective w hfin h) _ U hb

/-- Helper toward Definition 3.2: the supplied ordered boundary is exactly
the external frontier, with no repeated geometric edge occurrences. -/
theorem m0BoundaryPresentation32_boundaryOrder : IsBoundaryOrderOfInf M Q := by
  obtain ⟨U, hU, huniq, _, _, hcover⟩ := m0BoundaryDrawing32_geometry w hfin h
  rw [IsBoundaryOrderOfInf_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rw [m0BoundaryMap32_frontier_iff w hfin h U hU huniq e]
    constructor
    · rintro ⟨i, hi⟩
      have hb := (hcover _).mpr ⟨i, rfl⟩
      rcases hd : InfiniteBoundaryDartIndex.dart Q i with ⟨f, b⟩
      have he : f = e := (congrArg Prod.fst hd).symm.trans hi
      subst f
      rw [hd] at hb
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · rintro (hb | hb)
      · obtain ⟨i, hi⟩ := (hcover _).mp hb
        exact ⟨i, congrArg Prod.fst hi⟩
      · obtain ⟨i, hi⟩ := (hcover _).mp hb
        exact ⟨i, congrArg Prod.fst hi⟩
  · intro e i j k hi hj _
    exact Or.inl (m0BoundaryPresentation32_edge_injective w hfin h (hi.trans hj.symm))
  · intro e i j hij hi hj
    exact (hij (m0BoundaryPresentation32_edge_injective w hfin h (hi.trans hj.symm))).elim

/-- Helper toward Definition 3.2: the supplied missing lower-left darts
have the exact source missingness and consecutive geometric endpoint joins. -/
theorem m0BoundaryPresentation32_missing_side : LLOkInf Q := by
  rw [LLOkInf_iff]
  constructor
  · intro n
    exact (boundaryOuterEdge_endpoints w h (-(n : ℤ) - 1)).2.2.2 (by omega)
  · intro i j hij
    have hj : i + 1 = j := Option.some.inj hij
    subst j
    erw [(m0BoundaryMap32_boundary_endpoints w hfin h _).2,
      (m0BoundaryMap32_boundary_endpoints w hfin h _).1]
    congr 1
    push_cast
    omega

/-- Helper toward Definition 3.2: the present lower-right traversal has no
repeated vertices, including its final vertex x₀, and has no successor cycle. -/
theorem m0BoundaryPresentation32_lowerRight_simple : IsSimpleBoundarySide M (Q).lowerRight := by
  have hinit (n : ℕ) : boundaryDartInitial M ((Q).lowerRight.darts n) =
      boundaryVertex w h ((n : ℤ) + 1) :=
    (m0BoundaryMap32_boundary_endpoints w hfin h n).1
  have hterm (n : ℕ) : boundaryDartTerminal M ((Q).lowerRight.darts n) =
      boundaryVertex w h n := (m0BoundaryMap32_boundary_endpoints w hfin h n).2
  have hlast (n : ℕ) : (Q).lowerRight.next n = none ↔ n = 0 := by
    change (if n = 0 then none else some (n - 1)) = none ↔ n = 0
    by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte, Option.some_ne_none]
  constructor
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change ℕ at i j
        change boundaryDartInitial M ((Q).lowerRight.darts i) =
          boundaryDartInitial M ((Q).lowerRight.darts j) at hij
        erw [hinit, hinit] at hij
        have he := boundaryVertex_injective w h hij
        have heq : i = j := by
          simpa only [add_left_inj, Int.natCast_inj] using he
        exact congrArg Sum.inl heq
      | inr j =>
        change boundaryDartInitial M ((Q).lowerRight.darts i) =
          boundaryDartTerminal M ((Q).lowerRight.darts j.val) at hij
        erw [hinit, hterm, (hlast _).mp j.property] at hij
        have he := boundaryVertex_injective w h hij
        omega
    | inr i =>
      cases j with
      | inl j =>
        change boundaryDartTerminal M ((Q).lowerRight.darts i.val) =
          boundaryDartInitial M ((Q).lowerRight.darts j) at hij
        erw [hinit, hterm, (hlast _).mp i.property] at hij
        have he := boundaryVertex_injective w h hij
        omega
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext (((hlast _).mp i.property).trans
          ((hlast _).mp j.property).symm))
  · intro i hi
    have hstep : ∀ a b : ℕ, (Q).lowerRight.next a = some b → b < a := by
      intro a b hab
      change (if a = 0 then none else some (a - 1)) = some b at hab
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte] at hab
        cases hab
      · simp only [ha, ↓reduceIte, Option.some.injEq] at hab
        omega
    have hlt : ∀ {a b}, Relation.TransGen (fun a b => (Q).lowerRight.next a = some b) a b → b < a := by
      intro a b hab
      induction hab with
      | single hab => exact hstep _ _ hab
      | tail _ hbc ih => exact (hstep _ _ hbc).trans ih
    exact (Nat.lt_irrefl i) (hlt hi)

/-- Helper toward Definition 3.2: the present lower-right ray has its
external face on the right of its west-to-east orientation, with joined darts. -/
theorem m0BoundaryPresentation32_present_side : LROkInf Q := by
  obtain ⟨U, hU, _, hborder, _, _⟩ := m0BoundaryDrawing32_geometry w hfin h
  obtain ⟨F, hFU, hF⟩ := (m0BoundaryDrawing32_draws w hfin h).unbounded_face_to_external U hU
  rw [LROkInf_iff]
  constructor
  · intro n
    change ℕ at n
    have hp : ¬ (M).toPlaneMapWithMissing.missing (boundaryOuterEdge w h n) :=
      not_not.mpr ((boundaryOuterEdge_endpoints w h n).2.2.1 (by omega))
    refine ⟨hp, rfl, F, hF, ?_⟩
    have hb : (G).dartBorders (futureMapBoundaryDart w h n) U :=
      (hborder _).mpr ⟨n, rfl⟩
    have hl : ∀ s, LeftAtOn F.val ((Drawing M).arc (boundaryOuterEdge w h n)) s := by
      intro s
      rw [hFU]
      exact (leftAtOn_cast_iff U.val _
        ((m0BoundaryPL32 w hfin).arc_start (futureMapBoundaryDart w h n)).symm
        ((m0BoundaryPL32 w hfin).arc_finish (futureMapBoundaryDart w h n)).symm s).mpr
        ((G).dartBorders_toPath_leftAtOn (m0Drawing32_surjective w hfin h) _ U hb s)
    have hr := (forall_rightAtOn_symm_iff F.val
      ((Drawing M).arc (boundaryOuterEdge w h n))).mpr hl
    change ∀ s, RightAtOn F.val (orientedArc M ⟨boundaryOuterEdge w h n, hp⟩) s
    dsimp [orientedArc, m0BoundaryMap32, DirectedPlaneMapWithMissing.tail,
      DirectedPlaneMapWithMissing.head] at hr ⊢
    exact hr
  · intro i j hij
    change ℕ at i j
    change (if i = 0 then none else some (i - 1)) = some j at hij
    have hi : i ≠ 0 := by intro hi; simp only [hi, ↓reduceIte] at hij; cases hij
    have hj : i - 1 = j := by simpa only [hi, ↓reduceIte, Option.some.injEq] using hij
    change boundaryDartTerminal M (futureMapBoundaryDart w h i) =
      boundaryDartInitial M (futureMapBoundaryDart w h j)
    rw [(m0BoundaryMap32_boundary_endpoints w hfin h _).2,
      (m0BoundaryMap32_boundary_endpoints w hfin h _).1]
    congr 1
    omega

/-- Helper toward Definition 3.2: all four supplied sides have the correct
optional endpoint labels, without finite marks at their infinite ends. -/
theorem m0BoundaryPresentation32_endpointLabels :
    BoundarySideEndpointLabels M (Q).upperLeft ∧
    BoundarySideEndpointLabels M (Q).upperRight ∧
    BoundarySideEndpointLabels M (Q).lowerRight ∧
    BoundarySideEndpointLabels M (Q).lowerLeft := by
  have hempty : BoundarySideEndpointLabels M m0EmptySide32 := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro _ v z hv; cases hv
  refine ⟨hempty, hempty, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro v hv; cases hv
    · intro v hv
      have hv' : boundaryVertex w h 0 = v := Option.some.inj hv
      subst v
      constructor
      · intro _
        exact ⟨0, rfl, (m0BoundaryMap32_boundary_endpoints w hfin h 0).2⟩
      · intro i hi
        change ℕ at i
        have hz : i = 0 := by
          change (if i = 0 then none else some (i - 1)) = none at hi
          by_contra hn
          simp only [hn, ↓reduceIte, Option.some_ne_none] at hi
        subst i
        exact (m0BoundaryMap32_boundary_endpoints w hfin h 0).2
    · intro _ v z hv; cases hv
  · refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have hv' : boundaryVertex w h 0 = v := Option.some.inj hv
      subst v
      have hzero : boundaryDartInitial M ((Q).lowerLeft.darts 0) = boundaryVertex w h 0 := by
        change boundaryDartInitial M (futureMapBoundaryDart w h (-1)) = boundaryVertex w h 0
        simpa only [neg_add_cancel] using (m0BoundaryMap32_boundary_endpoints w hfin h (-1)).1
      constructor
      · intro _
        refine ⟨0, ?_, hzero⟩
        intro j hj
        change ℕ at j
        have he : j + 1 = 0 := Option.some.inj hj
        omega
      · intro i hi
        change ℕ at i
        have hz : i = 0 := by
          cases i with
          | zero => rfl
          | succ i => exact (hi i rfl).elim
        subst i
        exact hzero
    · intro v hv; cases hv
    · intro _ v z _ hz; cases hz

/-- Helper toward Definition 3.2: there are infinitely many external
geometric edges, so the supplied presentation uses the infinite branch. -/
theorem m0BoundaryMap32_infinite_boundary : ¬ (externalBoundaryDartSet4 M).Finite := by
  have hf := m0BoundaryPresentation32_boundaryOrder w hfin h
  rw [IsBoundaryOrderOfInf_iff] at hf
  intro hfinite
  apply (Set.infinite_of_injective_forall_mem
    (f := futureMapBoundaryDart w h) (futureMapBoundaryDart_injective w h) ?_) hfinite
  intro k
  change ExternalFrontierEdge M (boundaryOuterEdge w h k)
  apply (hf.1 _).mp
  obtain ⟨i, hi⟩ := (m0BoundaryLabel32_bijective w hfin h).2 k
  refine ⟨i, ?_⟩
  rw [m0BoundaryLabel32_dart, hi]
  rfl

/-- Helper toward Definition 3.2: boundary-successor equality is exactly
one decrease in the integer label, with no added recurrence premise. -/
theorem m0BoundaryPresentation32_successor_iff
    (i j : InfiniteBoundaryDartIndex Q) :
    kmswInfFaceSucc w hfin (InfiniteBoundaryDartIndex.dart Q i) =
        InfiniteBoundaryDartIndex.dart Q j ↔
      m0BoundaryLabel32 w hfin h j = m0BoundaryLabel32 w hfin h i - 1 := by
  rw [m0BoundaryLabel32_dart, m0BoundaryLabel32_dart,
    futureMapBoundaryDart_faceSucc w hfin h]
  exact ⟨fun he => (futureMapBoundaryDart_injective w h he).symm,
    fun he => congrArg _ he.symm⟩

/-- Helper toward Definition 3.2: every within-side successor follows the
geometric successor and joins the same two boundary endpoints. -/
theorem m0BoundaryPresentation32_withinSide :
    ∀ i j : InfiniteBoundaryDartIndex Q, sideNext Q i = some j →
      kmswInfFaceSucc w hfin (InfiniteBoundaryDartIndex.dart Q i) =
        InfiniteBoundaryDartIndex.dart Q j ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j) := by
  intro i j hij
  have hl : m0BoundaryLabel32 w hfin h j = m0BoundaryLabel32 w hfin h i - 1 := by
    cases i with
    | upperLeft i => exact i.elim
    | upperRight i => exact i.elim
    | lowerRight i =>
      change ℕ at i
      change (if i = 0 then none else some (i - 1)).map InfiniteBoundaryDartIndex.lowerRight = some j at hij
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte, Option.map_none] at hij; cases hij
      · simp only [hi, ↓reduceIte, Option.map_some, Option.some.injEq] at hij
        subst j
        change ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1
        omega
    | lowerLeft i =>
      change ℕ at i
      change some (InfiniteBoundaryDartIndex.lowerLeft (i + 1)) = some j at hij
      have hj := Option.some.inj hij
      subst j
      change -((i + 1 : ℕ) : ℤ) - 1 = -(i : ℤ) - 1 - 1
      omega
  refine ⟨(m0BoundaryPresentation32_successor_iff w hfin h i j).mpr hl, ?_⟩
  rw [m0BoundaryLabel32_dart, m0BoundaryLabel32_dart,
    (m0BoundaryMap32_boundary_endpoints w hfin h _).2,
    (m0BoundaryMap32_boundary_endpoints w hfin h _).1, hl]
  congr 1
  omega


private theorem m0Boundary32_successor_cases (i j : InfiniteBoundaryDartIndex Q)
    (hij : kmswInfFaceSucc w hfin (InfiniteBoundaryDartIndex.dart Q i) =
      InfiniteBoundaryDartIndex.dart Q j) :
    sideNext Q i = some j ∨
      (i = (InfiniteBoundaryDartIndex.lowerRight 0 : InfiniteBoundaryDartIndex Q) ∧
        j = (InfiniteBoundaryDartIndex.lowerLeft 0 : InfiniteBoundaryDartIndex Q)) := by
  have hl := (m0BoundaryPresentation32_successor_iff w hfin h i j).mp hij
  cases i with
  | upperLeft i => exact i.elim
  | upperRight i => exact i.elim
  | lowerRight i =>
    cases j with
    | upperLeft j => exact j.elim
    | upperRight j => exact j.elim
    | lowerRight j =>
      change ℕ at i j
      change (j : ℤ) = (i : ℤ) - 1 at hl
      have hi : i ≠ 0 := by omega
      have hj : i - 1 = j := by omega
      left
      simp only [sideNext, m0BoundaryPresentation32, m0LowerRightSide32,
        hi, ↓reduceIte, hj, Option.map_some]
    | lowerLeft j =>
      change ℕ at i j
      change -(j : ℤ) - 1 = (i : ℤ) - 1 at hl
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      exact Or.inr ⟨congrArg _ hi, congrArg _ hj⟩
  | lowerLeft i =>
    cases j with
    | upperLeft j => exact j.elim
    | upperRight j => exact j.elim
    | lowerRight j =>
      change ℕ at i j
      change (j : ℤ) = -(i : ℤ) - 1 - 1 at hl
      omega
    | lowerLeft j =>
      change ℕ at i j
      change -(j : ℤ) - 1 = -(i : ℤ) - 1 - 1 at hl
      have hj : i + 1 = j := by omega
      left
      simp only [sideNext, m0BoundaryPresentation32, m0LowerLeftSide32,
        hj, Option.map_some]

private theorem m0Boundary32_crossing :
    firstOnSide Q (.lowerLeft 0) ∧ nextNonemptySide Q 2 3 := by
  constructor
  · intro i hi
    cases i with
    | upperLeft i => exact i.elim
    | upperRight i => exact i.elim
    | lowerRight i =>
      change (if i = 0 then none else some (i - 1)).map
        InfiniteBoundaryDartIndex.lowerRight = some (.lowerLeft 0) at hi
      by_cases hz : i = 0 <;> simp only [hz, ↓reduceIte, Option.map_none,
        Option.map_some, Option.some.injEq] at hi <;> cases hi
    | lowerLeft i =>
      change ℕ at i
      have hi' : InfiniteBoundaryDartIndex.lowerLeft (i + 1) =
          (InfiniteBoundaryDartIndex.lowerLeft 0 : InfiniteBoundaryDartIndex Q) :=
        Option.some.inj hi
      have hzero : i + 1 = 0 := InfiniteBoundaryDartIndex.lowerLeft.inj hi'
      omega
  · refine ⟨⟨0⟩, by decide, ?_⟩
    intro k hk₁ hk₂
    change sideDistance 2 k < 1 at hk₂
    omega

/-- Helper toward Definition 3.2: the complete external successor order has
one finite transition, from the root lower-right dart to the first missing dart. -/
theorem m0BoundaryPresentation32_externalOrder
    (U : (G).Face) (hgeom : IsGeometricExternalFaceSucc G U (kmswInfFaceSucc w hfin))
    (hcover : ∀ d, (G).dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex Q,
      InfiniteBoundaryDartIndex.dart Q i = d) :
    IsExternalFaceIntervalOrder M Q G U (kmswInfFaceSucc w hfin) := by
  refine ⟨m0BoundaryPresentation32_boundaryOrder w hfin h, hcover, hgeom,
    m0BoundaryPresentation32_withinSide w hfin h, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := (m0BoundaryLabel32_bijective w hfin h).2
      (m0BoundaryLabel32 w hfin h i - 1)
    exact ⟨j, (m0BoundaryPresentation32_successor_iff w hfin h i j).mpr hj⟩
  · intro i j hij
    rcases m0Boundary32_successor_cases w hfin h i j hij with hn | ⟨rfl, rfl⟩
    · exact Or.inl hn
    · refine Or.inr ⟨rfl, (m0Boundary32_crossing w hfin h).1,
        (m0Boundary32_crossing w hfin h).2, ?_⟩
      rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
      change boundaryDartTerminal M (futureMapBoundaryDart w h 0) =
        boundaryDartInitial M (futureMapBoundaryDart w h (-1))
      rw [(m0BoundaryMap32_boundary_endpoints w hfin h 0).2,
        (m0BoundaryMap32_boundary_endpoints w hfin h (-1)).1]
      norm_num

/-- Helper toward Definition 3.2: the one finite side transition retains
both labels at x₀, and no empty side is skipped at that junction. -/
theorem m0BoundaryPresentation32_requiredLabels :
    RequiredBoundaryJoinEndpointLabels Q (kmswInfFaceSucc w hfin) := by
  intro i j hij hlast _
  rcases m0Boundary32_successor_cases w hfin h i j hij with hn | ⟨rfl, rfl⟩
  · rw [hlast] at hn; cases hn
  · dsimp only
    have he : boundaryDartTerminal M
        (InfiniteBoundaryDartIndex.dart Q (.lowerRight 0)) = boundaryVertex w h 0 := by
      rw [InfiniteBoundaryDartIndex.dart_eq]
      exact (m0BoundaryMap32_boundary_endpoints w hfin h 0).2
    rw [he]
    refine ⟨rfl, rfl, ?_⟩
    intro k hk₁ hk₂
    simp only [sideTag] at hk₁ hk₂
    change sideDistance 2 k < 1 at hk₂
    omega

private theorem m0Boundary32_joinLabels :
    BoundaryJoinEndpointLabels Q (kmswInfFaceSucc w hfin) := by
  intro i j hij hlast
  rcases m0Boundary32_successor_cases w hfin h i j hij with hn | ⟨rfl, rfl⟩
  · rw [hlast] at hn; cases hn
  · have he : boundaryDartTerminal M
        (InfiniteBoundaryDartIndex.dart Q (.lowerRight 0)) = boundaryVertex w h 0 := by
      rw [InfiniteBoundaryDartIndex.dart_eq]
      exact (m0BoundaryMap32_boundary_endpoints w hfin h 0).2
    dsimp only
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz; exact (Option.some.inj hz).symm
    · intro z hz; exact (Option.some.inj hz).symm
    · intro k hk₁ hk₂
      simp only [sideTag] at hk₁ hk₂
      change sideDistance 2 k < 1 at hk₂
      omega

private theorem m0Boundary32_tag (i : InfiniteBoundaryDartIndex Q) :
    sideTag Q i = if 0 ≤ m0BoundaryLabel32 w hfin h i then 2 else 3 := by
  cases i with
  | upperLeft i => exact i.elim
  | upperRight i => exact i.elim
  | lowerRight i => simp only [sideTag, m0BoundaryLabel32, Int.natCast_nonneg, ↓reduceIte]
  | lowerLeft i =>
    change (3 : Fin 4) = if 0 ≤ -(i : ℤ) - 1 then 2 else 3
    rw [ite_eq_right (by omega)]

/-- Helper toward Definition 3.2: negative source labels give a gapless
integer order, with the LR and LL sides as consecutive convex blocks. -/
theorem m0BoundaryPresentation32_positions : BoundaryPositionOrder3 Q := by
  refine ⟨fun i => -m0BoundaryLabel32 w hfin h i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (m0BoundaryLabel32_bijective w hfin h).1 (neg_injective hij)
  · intro i j htag
    constructor
    · intro hn
      have hs := (m0BoundaryPresentation32_withinSide w hfin h i j hn).1
      have hl := (m0BoundaryPresentation32_successor_iff w hfin h i j).mp hs
      dsimp only
      omega
    · intro hp
      dsimp only at hp
      have hl : m0BoundaryLabel32 w hfin h j = m0BoundaryLabel32 w hfin h i - 1 := by omega
      rcases m0Boundary32_successor_cases w hfin h i j
        ((m0BoundaryPresentation32_successor_iff w hfin h i j).mpr hl) with hn | ⟨rfl, rfl⟩
      · exact hn
      · cases htag
  · intro i j z _ _
    obtain ⟨k, hk⟩ := (m0BoundaryLabel32_bijective w hfin h).2 (-z)
    exact ⟨k, by dsimp only; rw [hk, neg_neg]⟩
  · intro i j k hij hjk hends
    dsimp only at hij hjk
    rw [m0Boundary32_tag, m0Boundary32_tag] at hends ⊢
    split_ifs at hends ⊢ <;> omega
  · intro i j k _ _ hij hjk hik
    have hi : sideTag Q i = 2 ∨ sideTag Q i = 3 := by rw [m0Boundary32_tag]; split_ifs <;> simp
    have hj : sideTag Q j = 2 ∨ sideTag Q j = 3 := by rw [m0Boundary32_tag]; split_ifs <;> simp
    have hk : sideTag Q k = 2 ∨ sideTag Q k = 3 := by rw [m0Boundary32_tag]; split_ifs <;> simp
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk <;>
      simp_all only [ne_eq, not_true_eq_false]

/-- Helper toward Definition 3.2: the full future-run map supplies its
limiting presentation, compatible PL drawing, and complete certificate. -/
theorem m0BoundaryPresentation32_certificate :
    ∃ U : (G).Face, IsBoundEdges32 M (m0BoundaryPresentation32 w hfin h) G U
      (kmswInfFaceSucc w hfin) := by
  obtain ⟨U, _, _, _, hgeom, hcover⟩ := m0BoundaryDrawing32_geometry w hfin h
  have hlabels := m0BoundaryPresentation32_endpointLabels w hfin h
  have hemptySimple : IsSimpleBoundarySide M m0EmptySide32 := by
    constructor
    · intro i
      cases i with
      | inl i => exact i.elim
      | inr i => exact i.val.elim
    · intro i; exact i.elim
  refine ⟨U, (IsBoundEdges32.infinite_iff (m0BoundaryMap32_infinite_boundary w hfin h)).mpr
    ⟨rfl, ?_, m0BoundaryPresentation32_positions w hfin h,
      m0BoundaryPresentation32_requiredLabels w hfin h⟩⟩
  exact ⟨m0BoundaryPresentation32_externalOrder w hfin h U hgeom hcover,
    ULOkInf_of_isEmpty Q, UROkInf_of_isEmpty Q,
    m0BoundaryPresentation32_present_side w hfin h,
    m0BoundaryPresentation32_missing_side w hfin h,
    hemptySimple, m0BoundaryPresentation32_lowerRight_simple w hfin h,
    hlabels.1, hlabels.2.1, hlabels.2.2.1, hlabels.2.2.2,
    m0Boundary32_joinLabels w hfin h⟩


end M0Carrier

universe uV uE uUL uUR uLR uLL

private theorem source_clauses_of_certificate_carriers4
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) :
    BoundEdges32SourceClauses M B G U S := by
  have horder : IsBoundaryOrderOfInf M B.presentation ∧
      IsGeometricExternalFaceSucc G U S := by
    by_cases hf : (externalBoundaryDartSet4 M).Finite
    · have hc := ((IsBoundEdges32.finite_iff hf).mp h).1
      exact ⟨hc.1, hc.2.2.2.1⟩
    · have hc := ((IsBoundEdges32.infinite_iff hf).mp h).2.1.1
      exact ⟨hc.1, hc.2.2.1⟩
  refine ⟨h, horder.1, horder.2, h.linear_positions_part2,
    bound_edges_provider_of_isBoundEdges32 M B G U S h, ?_,
    h.upperRight_geometric_integer_interval_part2,
    h.lowerLeft_geometric_integer_interval_part2, ?_, ?_⟩
  · intro e
    exact ⟨mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e,
      mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e⟩
  · intro J hJ
    have hf : (externalBoundaryDartSet4 M).Finite := by
      by_contra hi
      have hn := ((IsBoundEdges32.infinite_iff hi).mp h).1
      rw [hJ] at hn
      cases hn
    exact ⟨((IsBoundEdges32.finite_supplied_junctions_iff hf J hJ).mp h).2,
      h.upperRight_supplied_vertex_interval_part2 J hJ,
      h.lowerLeft_supplied_vertex_interval_part2 J hJ⟩
  · intro hb hn
    exact leftRightBoundaries32_of_bipolar_no_missing_edges hb hn h


/-- Helper toward Definition 3.2: every source clause follows for the full
future-run presentation, with local finiteness proved on its actual carrier. -/
theorem m0BoundaryPresentation32_source (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) :
    ∃ U : (m0BoundaryDrawing32 w hfin h).Face,
      BoundEdges32SourceClauses (m0BoundaryMap32 w hfin h)
        (m0BoundaryPresentation32 w hfin h) (m0BoundaryDrawing32 w hfin h)
        U (kmswInfFaceSucc w hfin) := by
  obtain ⟨U, h32⟩ := m0BoundaryPresentation32_certificate w hfin h
  exact ⟨U, source_clauses_of_certificate_carriers4 _ (m0BoundaryPresentation32 w hfin h)
    _ U (kmswInfFaceSucc w hfin) h32 (m0BoundaryMap32_locallyFinite w hfin h _)⟩

/-- Helper toward Definition 3.2: the exact M₀,∞ supplied-presentation
conclusion in raw edge and vertex coordinates, using the finite-stage
endpoint-storage convention. Every cut correspondence and all source clauses
share the same almost-sure witnesses; this predicate is never a premise. -/
@[expose] def M0CutSuppliedBoundEdges32Source : Prop :=
  ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
    ∃ (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
    let w := shiftedStream W 0
    let D := m0CutData W H h hLL
    let M := m0BoundaryMap32 w (H.1 0) h
    let B := m0BoundaryPresentation32 w (H.1 0) h
    let G := m0BoundaryDrawing32 w (H.1 0) h
    ∃ U : G.Face,
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      (∀ e, D.missing (wholePlaneEdgeι W 0 e) ↔ M.toPlaneMapWithMissing.missing e) ∧
      (∀ e : PresentEdge M,
        wholePlaneVertexι W 0 (M.tail e) = wholePlaneEdgeWest W (wholePlaneEdgeι W 0 e.val) ∧
        wholePlaneVertexι W 0 (M.head e) = wholePlaneEdgeEast W (wholePlaneEdgeι W 0 e.val)) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex w h k)) ∧
      M.IsAcyclic ∧ DrawsMap M G ∧ B.finiteJunctions? = none ∧
      (∀ e, e ∈ upperLeftBoundary32 B ↔ kmswBoundaryLimsup State.UL w e) ∧
      (∀ e, e ∈ upperRightBoundary32 B ↔ kmswBoundaryLimsup State.UR w e) ∧
      (∀ e, e ∈ lowerRightBoundary32 B ↔ kmswBoundaryLimsup State.LR w e) ∧
      (∀ e, e ∈ lowerLeftBoundary32 B ↔ kmswBoundaryLimsup State.LL w e) ∧
      BoundEdges32SourceClauses M B G U (kmswInfFaceSucc w (H.1 0))




theorem m0Cut_bound_edges32_source : M0CutSuppliedBoundEdges32Source := by
  filter_upwards [ae_m0BoundaryMap32_cut_correspondence] with W hW
  obtain ⟨H, h, hLL, he, hei, hvi, hm, hends, hx, hacyc, hdraw, _⟩ := hW
  obtain ⟨U, hsource⟩ := m0BoundaryPresentation32_source (shiftedStream W 0) (H.1 0) h
  have hlim := m0BoundaryPresentation32_limsup (shiftedStream W 0) (H.1 0) h
  exact ⟨H, h, hLL, U, he, hei, hvi, hm, hends, hx, hacyc, hdraw, rfl,
    hlim.1, hlim.2.1, hlim.2.2.1, hlim.2.2.2, hsource⟩

/-- Helper toward Definition 3.2: extend the existing joint source package
by the actual M₀,∞ carrier. No unrestricted stream carrier is included. -/
theorem bound_edges_definition32_source_with_m0Cut :
    UIQBOTBoundEdges32Source ∧ UIBHBOTBoundEdges32Source ∧
    KMSWStageBoundEdges32Source ∧ BoundaryChanneledBoundEdges32Source ∧
    M0CutSuppliedBoundEdges32Source :=
  ⟨bound_edges_definition32_source.1, bound_edges_definition32_source.2.1,
    bound_edges_definition32_source.2.2.1, bound_edges_definition32_source.2.2.2,
    m0Cut_bound_edges32_source⟩



























end DirectedDistances.PlanarMap
end
