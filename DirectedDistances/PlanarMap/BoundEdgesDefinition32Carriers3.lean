/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Carriers2
public import DirectedDistances.KMSW.RunInfDartPartition







public section
noncomputable section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW MeasureTheory
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

private theorem hit_left_unbounded32 (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, L w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨n, hn.le.trans (min_le_left _ _)⟩

private theorem hit_right_unbounded32 (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
  exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩

/-- Helper toward Definition 3.2: the existing monotone drawing of the full
one-sided run, before passing to its reachable hatted submap. -/
abbrev m0BoundaryPL32 (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) :=
  monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Definition 3.2: a plane drawing on the raw IDs, retaining
all geometric edges, with stored paths from their east to west endpoints. -/
@[expose] def m0BoundaryGraph32 (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) :
    PlaneGraphDrawing ℕ ℕ where
  src := edgeEast w
  tgt := edgeWest w
  pos := (m0BoundaryPL32 w hfin).pos
  pos_injective := (m0BoundaryPL32 w hfin).pos_injective
  arc e := ((m0BoundaryPL32 w hfin).arc (e, true)).toPath.cast
    ((m0BoundaryPL32 w hfin).arc_start (e, true)).symm
    ((m0BoundaryPL32 w hfin).arc_finish (e, true)).symm
  arc_injOn e := ((m0BoundaryPL32 w hfin).arc (e, true)).toPath_injOn
    ((m0BoundaryPL32 w hfin).arc_length _) ((m0BoundaryPL32 w hfin).arc_simple _)
  openArc_disjoint := by
    intro e f hef
    change Disjoint (((m0BoundaryPL32 w hfin).arc (e, true)).toPath '' openParams)
      (((m0BoundaryPL32 w hfin).arc (f, true)).toPath '' openParams)
    rw [Polyline.toPath_image_openParams _ ((m0BoundaryPL32 w hfin).arc_length _)
        ((m0BoundaryPL32 w hfin).arc_simple _),
      Polyline.toPath_image_openParams _ ((m0BoundaryPL32 w hfin).arc_length _)
        ((m0BoundaryPL32 w hfin).arc_simple _)]
    apply (m0BoundaryPL32 w hfin).interior_disjoint
    · intro heq
      exact hef (congrArg Prod.fst heq).symm
    · intro heq
      have hb := congrArg Prod.snd heq
      simp only [Bool.not_true, Bool.true_eq_false] at hb
  openArc_avoids := by
    intro e v
    change (m0BoundaryPL32 w hfin).pos v ∉
      ((m0BoundaryPL32 w hfin).arc (e, true)).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ ((m0BoundaryPL32 w hfin).arc_length _)
      ((m0BoundaryPL32 w hfin).arc_simple _)]
    exact (m0BoundaryPL32 w hfin).interior_avoids_vertices _ v

/-- Helper toward Definition 3.2: both darts retain the same raw edge trace. -/
theorem m0BoundaryGraph32_arc_range (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    Set.range ((m0BoundaryGraph32 w hfin).arc d.1) =
      ((m0BoundaryPL32 w hfin).arc d).image := by
  change Set.range ((m0BoundaryPL32 w hfin).arc (d.1, true)).toPath = _
  rw [Polyline.range_toPath]
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact (m0BoundaryPL32 w hfin).arc_image_flip (e, false)
  | true => rfl

/-- Helper toward Definition 3.2: the adapter preserves the full drawing
image, including missing edges and all vertex positions. -/
theorem m0BoundaryGraph32_image (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) :
    (m0BoundaryGraph32 w hfin).image = (m0BoundaryPL32 w hfin).image := by
  change (Set.range (m0BoundaryPL32 w hfin).pos ∪ ⋃ e,
    Set.range ((m0BoundaryGraph32 w hfin).arc e)) = _
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
      exact Or.inr ⟨(e, true), (m0BoundaryGraph32_arc_range w hfin (e, true)) ▸ he⟩
  · rintro (hz | ⟨d, hd⟩)
    · exact Or.inl hz
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨d.1, (m0BoundaryGraph32_arc_range w hfin d).symm ▸ hd⟩)

/-- Helper toward Definition 3.2: every missing raw edge lies on the
unbounded face of the full run drawing. -/
theorem m0BoundaryGraph32_missing_external
    (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ EdgePresent w e) :
    ∃ F : (m0BoundaryGraph32 w hfin).Face,
      (m0BoundaryGraph32 w hfin).IsExternal F ∧
        Set.range ((m0BoundaryGraph32 w hfin).arc e) ⊆ closure F.val := by
  obtain ⟨U, hU, _, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin h
  let F : (m0BoundaryGraph32 w hfin).Face :=
    ⟨U.val, by simpa only [m0BoundaryGraph32_image, m0BoundaryPL32] using U.property⟩
  refine ⟨F, ?_, ?_⟩
  · change ¬ Bornology.IsBounded U.val
    rw [isBounded_iff_forall_norm_le]
    rintro ⟨R, hR⟩
    obtain ⟨z, hz, hnorm⟩ := hU R
    exact (not_lt_of_ge (hR z hz)) hnorm
  · rw [m0BoundaryGraph32_arc_range w hfin (e, true)]
    exact (m0BoundaryPL32 w hfin).dartBorders_arc_subset_closure
      (kmswLimitDartVertex_surjective w hfin) (e, true) U
      ((hborder _).mpr (futureMap_missing_east_external w
        (hit_right_unbounded32 w h) e he))

/-- Helper toward Definition 3.2: the full future-run map with exactly the
source's missing edges, and west-to-east orientation only on present edges. -/
@[expose] def m0BoundaryMap32 (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) : DirectedPlaneMapWithMissing ℕ ℕ where
  toPlaneMapWithMissing :=
    { toPlaneGraphDrawing := m0BoundaryGraph32 w hfin
      missing := fun e => ¬ EdgePresent w e
      missing_on_external := m0BoundaryGraph32_missing_external w hfin h }
  forward := fun _ => false

/-- Helper toward Definition 3.2: the adapter's dart endpoints are precisely
the installed KMSW endpoints, in the existing east-dart convention. -/
theorem m0BoundaryMap32_initial (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) :
    boundaryDartInitial (m0BoundaryMap32 w hfin h) = kmswLimitDartVertex w := by
  funext d
  rcases d with ⟨e, b⟩
  cases b <;> simp only [boundaryDartInitial_eq, m0BoundaryMap32,
    m0BoundaryGraph32, kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte]

/-- Helper toward Definition 3.2: directed tails and heads remain the raw
west and east endpoints, despite the stored path convention. -/
theorem m0BoundaryMap32_endpoints (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) (e : PresentEdge (m0BoundaryMap32 w hfin h)) :
    (m0BoundaryMap32 w hfin h).tail e = edgeWest w e.val ∧
      (m0BoundaryMap32 w hfin h).head e = edgeEast w e.val := ⟨rfl, rfl⟩

/-- Helper toward Definition 3.2: the full future-run adapter is acyclic;
this is proved from present-edge acyclicity, not assumed in its carrier. -/
theorem m0BoundaryMap32_acyclic (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) : (m0BoundaryMap32 w hfin h).IsAcyclic := by
  classical
  let M := m0BoundaryMap32 w hfin h
  have hpath : ∀ {u v : ℕ}, Relation.TransGen M.step u v →
      ∃ p : Quiver.Path (PresentVertex.mk u : PresentVertex w) (PresentVertex.mk v),
        0 < p.length := by
    intro u v huv
    induction huv with
    | @single v huv =>
      obtain ⟨e, hu, hv⟩ := huv
      have hp : EdgePresent w e.val := not_not.mp e.property
      let a : (PresentVertex.mk u : PresentVertex w) ⟶ PresentVertex.mk v :=
        ⟨e.val, hp, hu, hv⟩
      exact ⟨a.toPath, Nat.zero_lt_one⟩
    | tail _ huv ih =>
      obtain ⟨p, _⟩ := ih
      obtain ⟨e, hu, hv⟩ := huv
      have hp : EdgePresent w e.val := not_not.mp e.property
      exact ⟨p.cons ⟨e.val, hp, hu, hv⟩, Nat.succ_pos _⟩
  intro v hv
  obtain ⟨p, hp⟩ := hpath hv
  rw [presentVertex_acyclic w _ p] at hp
  exact Nat.lt_irrefl 0 hp

/-- Helper toward Definition 3.2: the compatible PL drawing is the existing
run drawing with its endpoint type transported by the proved equality. -/
@[expose] def m0BoundaryDrawing32 (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) (kmswInfRot w hfin)
      (boundaryDartInitial (m0BoundaryMap32 w hfin h)) :=
  { flip_involutive := (m0BoundaryPL32 w hfin).flip_involutive
    flip_ne := (m0BoundaryPL32 w hfin).flip_ne
    vert_rotation := by
      simp only [m0BoundaryMap32_initial]
      exact (m0BoundaryPL32 w hfin).vert_rotation
    pos := (m0BoundaryPL32 w hfin).pos
    pos_injective := (m0BoundaryPL32 w hfin).pos_injective
    arc := (m0BoundaryPL32 w hfin).arc
    arc_simple := (m0BoundaryPL32 w hfin).arc_simple
    arc_length := (m0BoundaryPL32 w hfin).arc_length
    arc_start := by
      simp only [m0BoundaryMap32_initial]
      exact (m0BoundaryPL32 w hfin).arc_start
    arc_finish := by
      simp only [m0BoundaryMap32_initial]
      exact (m0BoundaryPL32 w hfin).arc_finish
    arc_flip := (m0BoundaryPL32 w hfin).arc_flip
    interior_disjoint := (m0BoundaryPL32 w hfin).interior_disjoint
    interior_avoids_vertices := (m0BoundaryPL32 w hfin).interior_avoids_vertices
    locally_finite := (m0BoundaryPL32 w hfin).locally_finite
    initial_nonzero := (m0BoundaryPL32 w hfin).initial_nonzero
    initial_arg_injective := by
      simp only [m0BoundaryMap32_initial]
      exact (m0BoundaryPL32 w hfin).initial_arg_injective
    rotation_agreement := by
      simp only [m0BoundaryMap32_initial]
      exact (m0BoundaryPL32 w hfin).rotation_agreement }

/-- Helper toward Definition 3.2: endpoint-type transport preserves every
vertex position and edge trace of the constructed map. -/
theorem m0BoundaryDrawing32_draws (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) :
    DrawsMap (m0BoundaryMap32 w hfin h) (m0BoundaryDrawing32 w hfin h) := by
  refine ⟨rfl, fun d => ?_⟩
  change Set.range ((m0BoundaryPL32 w hfin).arc d).toPath = _
  rw [Polyline.range_toPath]
  exact (m0BoundaryGraph32_arc_range w hfin d).symm

/-- Helper toward Definition 3.2: every compatible drawing of this adapter
has locally finite vertex image, by the proved incidence surjectivity. -/
theorem m0BoundaryMap32_locallyFinite (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) {rot : Equiv.Perm (ℕ × Bool)}
    (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (m0BoundaryMap32 w hfin h))) : LocallyFiniteVertexImage G := by
  apply locallyFiniteVertexImage_of_surjective G
  rw [m0BoundaryMap32_initial]
  exact kmswLimitDartVertex_surjective w hfin

/-- Helper toward Definition 3.2: the boundary edge IDs are injectively
indexed by the source's integer vertex labels. -/
theorem m0BoundaryEdge32_injective (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    Function.Injective (boundaryOuterEdge w h) := by
  intro i j hij
  apply boundaryVertex_injective w h
  exact ((boundaryOuterEdge_endpoints w h i).1.symm.trans
    (congrArg (edgeWest w) hij)).trans (boundaryOuterEdge_endpoints w h j).1

/-- Helper toward Definition 3.2: a supplied empty upper side, with no
invented finite endpoint at an infinite end. -/
abbrev m0EmptySide32 : InfiniteBoundarySide.{0, 0, 0} ℕ ℕ where
  Index := Empty
  darts := ⟨Empty.elim, fun i => i.elim⟩
  next := Empty.elim
  initialVertex? := none
  terminalVertex? := none

/-- Helper toward Definition 3.2: decreasing traversal along the present
lower-right ray; the root edge is its last dart. -/
abbrev m0LowerRightSide32 (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    InfiniteBoundarySide.{0, 0, 0} ℕ ℕ where
  Index := ℕ
  darts := ⟨fun n => futureMapBoundaryDart w h n, by
    intro i j hij
    have he := futureMapBoundaryDart_injective w h hij
    exact_mod_cast he⟩
  next n := if n = 0 then none else some (n - 1)
  initialVertex? := none
  terminalVertex? := some (boundaryVertex w h 0)

/-- Helper toward Definition 3.2: the consecutive missing lower-left ray,
traversed from x₀ toward decreasing negative boundary labels. -/
abbrev m0LowerLeftSide32 (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    InfiniteBoundarySide.{0, 0, 0} ℕ ℕ where
  Index := ℕ
  darts := ⟨fun n => futureMapBoundaryDart w h (-(n : ℤ) - 1), by
    intro i j hij
    have he := futureMapBoundaryDart_injective w h hij
    omega⟩
  next n := some (n + 1)
  initialVertex? := some (boundaryVertex w h 0)
  terminalVertex? := none

/-- Helper toward Definition 3.2: the supplied limiting presentation of the
full future run. It has exactly the two lower rays and their shared x₀ label. -/
abbrev m0BoundaryPresentation32 (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) :
    BoundaryPresentationWithJunctions.{0, 0, 0, 0, 0, 0} (m0BoundaryMap32 w hfin h) where
  presentation :=
    { upperLeft := m0EmptySide32
      upperRight := m0EmptySide32
      lowerRight := m0LowerRightSide32 w h
      lowerLeft := m0LowerLeftSide32 w h }
  finiteJunctions? := none

private theorem boundaryOuterEdge_nat32 (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    boundaryOuterEdge w h n = kmswRightBoundaryEdge w n := by
  cases n with
  | zero => rw [Int.natCast_zero, boundaryOuterEdge_zero, kmswRightBoundaryEdge_zero]
  | succ n =>
    rw [boundaryOuterEdge_of_positive w h (by omega), Int.toNat_natCast]

/-- Helper toward Definition 3.2: all four supplied edge sets equal the
source's limiting KMSW side sets. No left-transience assumption is imposed. -/
theorem m0BoundaryPresentation32_limsup (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) :
    let B := m0BoundaryPresentation32 w hfin h
    (∀ e, e ∈ upperLeftBoundary32 B ↔ kmswBoundaryLimsup State.UL w e) ∧
    (∀ e, e ∈ upperRightBoundary32 B ↔ kmswBoundaryLimsup State.UR w e) ∧
    (∀ e, e ∈ lowerRightBoundary32 B ↔ kmswBoundaryLimsup State.LR w e) ∧
    (∀ e, e ∈ lowerLeftBoundary32 B ↔ kmswBoundaryLimsup State.LL w e) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    constructor
    · rintro ⟨i, _⟩; exact i.elim
    · intro he
      obtain ⟨N, hN⟩ := kmswRun_UL_eventually_absent w (hit_left_unbounded32 w h) e
      obtain ⟨n, hn, he⟩ := (kmswBoundaryLimsup_iff_forall_exists_ge _ _ _).mp he N
      exact (hN n hn he).elim
  · intro e
    constructor
    · rintro ⟨i, _⟩; exact i.elim
    · intro he
      obtain ⟨N, hN⟩ := kmswRun_UR_eventually_absent w (hit_right_unbounded32 w h) e
      obtain ⟨n, hn, he⟩ := (kmswBoundaryLimsup_iff_forall_exists_ge _ _ _).mp he N
      exact (hN n hn he).elim
  · intro e
    change (∃ n : ℕ, boundaryOuterEdge w h n = e) ↔ IsRightBoundaryEdge w e
    rw [isRightBoundaryEdge_iff w (hit_right_unbounded32 w h)]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (boundaryOuterEdge_nat32 w h n).symm.trans hn |>.symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (boundaryOuterEdge_nat32 w h n).trans hn.symm⟩
  · intro e
    change (∃ n : ℕ, boundaryOuterEdge w h (-(n : ℤ) - 1) = e) ↔ _
    constructor
    · rintro ⟨n, rfl⟩
      have hp := (boundaryOuterEdge_endpoints w h (-(n : ℤ) - 1)).2.2.2 (by omega)
      obtain ⟨N, hN⟩ := (m0Cut_not_present_iff_eventually_LL w h _).mp hp
      apply (kmswBoundaryLimsup_iff_forall_exists_ge _ _ _).mpr
      intro m
      exact ⟨max m N, le_max_left _ _, hN _ (le_max_right _ _)⟩
    · intro he
      have hp : ¬ EdgePresent w e := by
        intro hp
        obtain ⟨N, hN⟩ := hp.eventually_present
        obtain ⟨n, hn, he⟩ := (kmswBoundaryLimsup_iff_forall_exists_ge _ _ _).mp he N
        have hf := kmswStage_LL_edge_missing w n e he
        have ht := (hN n hn).2
        rw [hf] at ht
        cases ht
      have hevent := (m0Cut_not_present_iff_eventually_LL w h e).mp hp
      have hrange : e ∈ Set.range (fun j : ℕ =>
          kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
        rw [← kmswRunEventuallyLL_eq_range w h]
        exact hevent
      obtain ⟨j, hj⟩ := hrange
      refine ⟨j, ?_⟩
      rw [boundaryOuterEdge_of_negative w h (by omega)]
      convert hj using 1
      congr 2
      omega

/-- Helper toward Definition 3.2: the two boundary sides use exactly the
source-labelled endpoints, including the junction at x₀. -/
theorem m0BoundaryMap32_boundary_endpoints (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryDartInitial (m0BoundaryMap32 w hfin h) (futureMapBoundaryDart w h k) =
      boundaryVertex w h (k + 1) ∧
    boundaryDartTerminal (m0BoundaryMap32 w hfin h) (futureMapBoundaryDart w h k) =
      boundaryVertex w h k := by
  refine ⟨?_, ?_⟩
  · rw [m0BoundaryMap32_initial]
    exact (futureMapBoundaryDart_endpoints w h k).1
  · rw [boundaryDartTerminal_eq]
    change edgeWest w (boundaryOuterEdge w h k) = _
    exact (boundaryOuterEdge_endpoints w h k).1

/-- Helper toward Definition 3.2: on one probability-one event, the map
adapter agrees with the actual M₀,∞ cut's missingness, endpoints, and labels.
The whole-plane embeddings retain all edge and vertex identities. -/
theorem ae_m0BoundaryMap32_cut_correspondence :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
      let D := m0CutData W H h hLL
      let M := m0BoundaryMap32 (shiftedStream W 0) (H.1 0) h
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      (∀ e, D.missing (wholePlaneEdgeι W 0 e) ↔ M.toPlaneMapWithMissing.missing e) ∧
      (∀ e : PresentEdge M,
        wholePlaneVertexι W 0 (M.tail e) = wholePlaneEdgeWest W (wholePlaneEdgeι W 0 e.val) ∧
        wholePlaneVertexι W 0 (M.head e) = wholePlaneEdgeEast W (wholePlaneEdgeι W 0 e.val)) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∧
      M.IsAcyclic ∧ DrawsMap M (m0BoundaryDrawing32 (shiftedStream W 0) (H.1 0) h) ∧
      LocallyFiniteVertexImage (m0BoundaryDrawing32 (shiftedStream W 0) (H.1 0) h) := by
  filter_upwards [ae_m0Cut_boundary_carrier_data_carriers2] with W hW
  obtain ⟨H, h, hLL, he, _, hei, hvi, hm, hx, _⟩ := hW
  refine ⟨H, h, hLL, he, hei, hvi, hm, ?_, hx,
    m0BoundaryMap32_acyclic _ _ _, m0BoundaryDrawing32_draws _ _ _,
    m0BoundaryMap32_locallyFinite _ _ _ _⟩
  intro e
  exact ⟨(wholePlaneEdgeWest_ι W 0 e.val).symm,
    (wholePlaneEdgeEast_ι W 0 e.val).symm⟩


end DirectedDistances.PlanarMap
end
