module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfArcSeed

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Exterior-boundary departures away from the seam are confined without a rotation-sector
assumption. The remaining seam-departure obligation is isolated, never assumed. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver Set
open scoped Classical Topology

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private noncomputable def launchPrepend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (e : u ⟶ v) (Q : InfinitePresentPath w v) : InfinitePresentPath w u where
  edge
    | 0 => e.val
    | n + 1 => Q.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(Q.initial n).1, e.toPath.comp (Q.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Path.length_comp, Path.length_toPath, Q.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, Q.prefix_edges, List.ofFn_succ]
      rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem launch_extendPath {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) (S : InfinitePresentPath w v) :
    ∃ Q : InfinitePresentPath w u, Set.range S.edge ⊆ Set.range Q.edge := by
  induction p with
  | nil => exact ⟨S, Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨Q, hQ⟩ := ih (launchPrepend e S)
    refine ⟨Q, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hQ ⟨i + 1, rfl⟩

section Drawing

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every source path trace lies in the union of the two geometric sides. -/
theorem thinMapPathTrace_subset_sideRegions (Q : InfinitePresentPath w ⟨0⟩) :
    pathTrace G (fun i => (Q.edge i, false)) ⊆
      thinMapSideRegion w hfin hL htrans hRneg P .left ∪
        thinMapSideRegion w hfin hL htrans hRneg P .right := by
  intro z hz
  have hl := seamTrace_subset_sideRegion w hfin hL htrans hRneg Q .left hz
  have hr := seamTrace_subset_sideRegion w hfin hL htrans hRneg Q .right hz
  by_cases hs : ∃ q ∈ pathTrace G (fun i => (P.edge i, false)),
      q.re = z.re ∧ q.im ≤ z.im
  · exact Or.inl ⟨hs, hl.2⟩
  · refine Or.inr ⟨hr.1, ?_⟩
    intro q hq hqre
    exact le_of_not_ge (fun h => hs ⟨q, hq, hqre, h⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A drawing vertex on the seam trace is one of its actual path vertices. -/
theorem thinMapVertex_mem_seamTrace_iff (v : ℕ) :
    (G).pos v ∈ pathTrace G (fun i => (P.edge i, false)) ↔
      ∃ i : ℕ, v = (P.initial i).1.id := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    have he : (G).pos v = ((G).arc (P.edge i, false)).start ∨
        (G).pos v = ((G).arc (P.edge i, false)).finish := by
      by_contra hn
      exact (G).interior_avoids_vertices (P.edge i, false) v ⟨hi, hn⟩
    rcases he with hs | hf
    · rw [(G).arc_start] at hs
      exact ⟨i, ((G).pos_injective hs).trans (P.edge_outgoing_at_initial w i).2⟩
    · rw [(G).arc_finish] at hf
      exact ⟨i + 1, ((G).pos_injective hf).trans (P.edge_incoming_at_succ w i).2⟩
  · rintro ⟨i, rfl⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hs := (G).arc_start (P.edge i, false)
    change ((G).arc (P.edge i, false)).start = (G).pos (edgeWest w (P.edge i)) at hs
    rw [(P.edge_outgoing_at_initial w i).2] at hs
    exact hs ▸ (Or.inl rfl)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The exterior boundary vertex has a genuine finite path from the source. -/
private theorem launch_boundary_reachable (a : ThinMapSide) (i : ℕ) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨thinMapBoundaryVertex w hfin hL htrans hRneg a i⟩ := by
  cases a with
  | left => exact ⟨thinMapLeftBoundaryPrefix w hfin hL htrans hRneg i⟩
  | right =>
    let B := kmswRightmostPath w hfin hL htrans hRneg 0
    have he : (B.initial i).1 =
        (⟨thinMapBoundaryVertex w hfin hL htrans hRneg .right i⟩ : PresentVertex w) := by
      apply congrArg (fun n => (⟨n⟩ : PresentVertex w))
      exact (B.edge_outgoing_at_initial w i).2.symm.trans
        ((ancestor_rightmostPath_edge_eq w hfin hL htrans hRneg i) ▸
          (ancestor_boundaryVertex_eq w hfin hL htrans hRneg .right i).symm)
    exact he ▸ ⟨(B.initial i).2⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem launch_seed_mem_union (e : ℕ) (hp : EdgePresent w e)
    (hsource : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩) :
    thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P .left ∪
      thinMapSideRegion w hfin hL htrans hRneg P .right := by
  obtain ⟨p⟩ := hsource
  let f : (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeEast w e⟩ := ⟨e, hp, rfl, rfl⟩
  let S := launchPrepend f (kmswRightmostPath w hfin hL htrans hRneg (edgeEast w e))
  obtain ⟨Q, hQ⟩ := launch_extendPath p S
  obtain ⟨j, hj⟩ := hQ (show e ∈ Set.range S.edge from ⟨0, rfl⟩)
  apply thinMapPathTrace_subset_sideRegions w hfin hL htrans hRneg P Q
  exact Set.mem_iUnion.mpr ⟨j, hj ▸ (thinMapArcSeed_mem_interior w hfin e).1⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every nonseam edge launched from a side vertex reachable from the source stays in
that side when its launch vertex is not on the seam. Boundary launches are included. -/
theorem thinMapArcSeed_mem_side_of_nonseam_launch (a : ThinMapSide) (e : ℕ)
    (hp : EdgePresent w e)
    (hsource : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩)
    (hv : edgeWest w e ∈ sideVertices w hfin hL htrans hRneg P a)
    (hseam : ∀ i : ℕ, edgeWest w e ≠ (P.initial i).1.id)
    (hoff : ∀ i : ℕ, e ≠ P.edge i) :
    thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P a := by
  have hunion := launch_seed_mem_union w hfin hL htrans hRneg P e hp hsource
  have hnot : (G).pos (edgeWest w e) ∉
      pathTrace G (fun i => (P.edge i, false)) := by
    intro h
    obtain ⟨i, hi⟩ := (thinMapVertex_mem_seamTrace_iff w hfin P _).mp h
    exact hseam i hi
  have hend (b : ThinMapSide)
      (hb : thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P b) :
      edgeWest w e ∈ sideVertices w hfin hL htrans hRneg P b :=
    (sideEdges_endpoints w hfin hL htrans hRneg P b
      ((thinMapArc_subset_sideRegion_iff_seed w hfin hL htrans hRneg P b e hoff).mpr
        hb)).1
  cases a with
  | left =>
    rcases hunion with hl | hr
    · exact hl
    · exact False.elim (hnot (by
        rw [← thinMapSideRegions_inter_eq_seamTrace w hfin hL htrans hRneg P]
        exact ⟨hv, hend .right hr⟩))
  | right =>
    rcases hunion with hl | hr
    · exact False.elim (hnot (by
        rw [← thinMapSideRegions_inter_eq_seamTrace w hfin hL htrans hRneg P]
        exact ⟨hend .left hl, hv⟩))
    · exact hr

end Drawing

section Half

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem launch_path_reachable
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    {u v : MapVertex M} {j : ℕ} (Q : SimpleDirectedDartPath M u v j) :
    Relation.ReflTransGen M.directedStep u v := by
  have hr (i : ℕ) (hi : i ≤ j) : Relation.ReflTransGen M.directedStep
      (Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩)
      (Q.vertices.get ⟨i, by rw [Q.vertices_length]; omega⟩) := by
    induction i with
    | zero => exact .refl
    | succ i ih =>
      have hs := Q.edge_step ⟨i, by rw [Q.darts_length]; omega⟩
      exact (ih (by omega)).tail ⟨Q.darts.get ⟨i, by rw [Q.darts_length]; omega⟩,
        hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
  simpa only [Q.start_vertex, Q.end_vertex] using hr j le_rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem launch_stage_head_id (e : Fin R.dartCount)
    (he : (I.toEquiv e).2 = false) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map e))).id =
      edgeEast w (I.toEquiv e).1.val := by
  rw [(cutMapIsoVertexEquiv_endpoints I e).2]
  change (stageMapVertex w t (dartTailVertex (kmswStageDirectedMap w t)
    ((kmswStageDirectedMap w t).edgeInv (I.toEquiv e)))).id = _
  rw [stageMapVertex_tail]
  change (if !(I.toEquiv e).2 then _ else _) = _
  rw [he]
  exact (edge_endpoints_eq w (I.toEquiv e).1.isLt).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A forward half dart cannot leave a seam vertex at or beyond the finite cut endpoint.
This includes exclusion of departure from the endpoint itself. -/
theorem ancestorPos_seamLaunch_index_lt
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (ht : (ancestorPosHalfRep R hR a).B.map.tail d)
    (i : ℕ) (hi : edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      (P.initial i).1.id) : i < m := by
  by_contra hn
  have hm : m ≤ i := Nat.le_of_not_gt hn
  let e := ancestorPosDartMap R hR a d
  have hor := (ancestorPos_ids_oriented w t R hR I a d).mp ht
  obtain ⟨N, Q, _⟩ := exists_simple_sink_pathBase R.B (dartHeadVertex R.B.map e)
  have hr := launch_path_reachable Q
  rw [cutMapIsoVertexEquiv_reachable_iff I, ancestorFinal_stage_reachable_iff] at hr
  have hr' := stageToLimit_reachable w t hr
  change Reachable
    (⟨(stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map e))).id⟩ :
      PresentVertex w)
    ⟨(stageMapVertex w t (cutMapIsoVertexEquiv I R.B.sink)).id⟩ at hr'
  rw [launch_stage_head_id w t R I e hor.2,
    ancestorPos_sink_id_of_prefix w t P R hR I hp] at hr'
  obtain ⟨q⟩ := hr'
  let f : (⟨edgeWest w (ancestorPosDartId w t R hR I a d).1⟩ : PresentVertex w) ⟶
      ⟨edgeEast w (ancestorPosDartId w t R hR I a d).1⟩ := ⟨_, hor.1, rfl, rfl⟩
  have q0 : Path
      (⟨edgeEast w (ancestorPosDartId w t R hR I a d).1⟩ : PresentVertex w)
      (P.initial m).1 := q
  have heq : (⟨edgeWest w (ancestorPosDartId w t R hR I a d).1⟩ : PresentVertex w) =
      (P.initial i).1 := congrArg PresentVertex.mk hi
  have hex : ∃ q' : Path (P.initial i).1 (P.initial m).1, 0 < q'.length := by
    rw [← heq]
    exact ⟨f.toPath.comp q0, by rw [Path.length_comp, Path.length_toPath]; omega⟩
  obtain ⟨q', hq'⟩ := hex
  obtain ⟨_, p, _, _, _, _⟩ := P.exists_shift_split m (i - m)
  have hs : m + (i - m) = i := Nat.add_sub_of_le hm
  rw [hs] at p
  have hz := presentVertex_acyclic w _ (p.comp q')
  rw [Path.length_comp] at hz
  omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Exterior-boundary launches away from the seam have their seed in the correct side.
No sector assumption or nonboundary-edge assumption is needed in this case. -/
theorem ancestorPos_boundaryLaunch_arcSeed
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (ht : (ancestorPosHalfRep R hR a).B.map.tail d)
    (hoff : ∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val)
    (hseam : ∀ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 ≠
      (P.initial i).1.id)
    (hb : ∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      thinMapBoundaryVertex w hfin hL htrans hRneg a i) :
    thinMapArcSeed w hfin (ancestorPosDartId w t R hR I a d).1 ∈
      thinMapSideRegion w hfin hL htrans hRneg P a := by
  obtain ⟨i, hi⟩ := hb
  have hbw : edgeWest w (thinMapBoundaryDart w hfin hL htrans hRneg a i).1 =
      thinMapBoundaryVertex w hfin hL htrans hRneg a i := by
    rw [ancestor_boundaryDart_eq]
    exact (ancestor_boundaryVertex_eq w hfin hL htrans hRneg a i).symm
  apply thinMapArcSeed_mem_side_of_nonseam_launch w hfin hL htrans hRneg P a _
    ((ancestorPos_ids_oriented w t R hR I a d).mp ht).1
  · rw [hi]
    exact launch_boundary_reachable w hfin hL htrans hRneg a i
  · rw [hi, ← hbw]
    exact (sideEdges_endpoints w hfin hL htrans hRneg P a
      (thinMapBoundaryDart_mem_sourceAncestorEdges w hfin hL htrans hRneg P a i).1).1
  · exact hseam
  · exact ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
of a source realization theorem. Exterior-boundary edges and prefix edges are excluded. -/
@[expose] noncomputable def AncestorPosHalfSeamLaunchArcSeeds (a : ThinMapSide) : Prop :=
  ∀ d : Fin (ancestorPosHalfRep R hR a).dartCount,
    (ancestorPosHalfRep R hR a).B.map.tail d →
    (∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) →
    (∀ i : ℕ, (ancestorPosDartId w t R hR I a d).1 ≠
      (thinMapBoundaryDart w hfin hL htrans hRneg a i).1) →
    (∃ i : Fin m, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      (P.initial i.val).1.id) →
    thinMapArcSeed w hfin (ancestorPosDartId w t R hR I a d).1 ∈
      thinMapSideRegion w hfin hL htrans hRneg P a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Removing the proved exterior-boundary-only case leaves precisely the seam launches.
This equivalence asserts neither of its two geometric obligations. -/
theorem ancestorPos_boundaryLaunch_iff_seamLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) :
    AncestorPosHalfBoundaryLaunchArcSeeds w hfin hL htrans hRneg P t R hR I a ↔
      AncestorPosHalfSeamLaunchArcSeeds w hfin hL htrans hRneg P t R hR I a := by
  constructor
  · intro h d ht hoff hb ⟨i, hi⟩
    exact h d ht hoff hb (Or.inl ⟨i.val, hi⟩)
  · intro h d ht hoff hb hstart
    by_cases hs : ∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
        (P.initial i).1.id
    · obtain ⟨i, hi⟩ := hs
      exact h d ht hoff hb
        ⟨⟨i, ancestorPos_seamLaunch_index_lt w P t R hR I hp a d ht i hi⟩, hi⟩
    · exact ancestorPos_boundaryLaunch_arcSeed w hfin hL htrans hRneg P t R hR I
        hp a d ht hoff (fun i hi => hs ⟨i, hi⟩) (hstart.resolve_left hs)

end Half

section Source

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining seam launches for the exact source witnesses. This proposition is -/
@[expose] noncomputable def SourceAncestorCutSeamLaunchArcSeeds : Prop :=
  ∀ (q : selectedCutCoherentDomain x T hT) (k : ℕ),
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let hfin := sourceAncestor_finite_incidence x T hT q
    let hL := sourceAncestor_left_nonneg x T hT q
    let htrans := sourceAncestor_left_transient x T hT q
    let hRneg := sourceAncestor_right_unbounded x T hT q
    let P := sourceAncestorPath x T hT q
    ∀ {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t)),
      (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) →
      ∀ a, AncestorPosHalfSeamLaunchArcSeeds
        w hfin hL htrans hRneg P t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The source obligation has only seam launches left after exterior-boundary confinement.
This is a reduction, not an unconditional source realization. -/
theorem sourceAncestorCut_boundaryLaunch_iff_seamLaunch :
    SourceAncestorCutBoundaryLaunchArcSeeds x T hT ↔
      SourceAncestorCutSeamLaunchArcSeeds x T hT := by
  constructor
  · intro h q k
    dsimp only
    intro ℓ r n m R hR I hp a
    exact (ancestorPos_boundaryLaunch_iff_seamLaunch
      _ _ _ _ _ _ _ R hR I hp a).mp (h q k R hR I hp a)
  · intro h q k
    dsimp only
    intro ℓ r n m R hR I hp a
    exact (ancestorPos_boundaryLaunch_iff_seamLaunch
      _ _ _ _ _ _ _ R hR I hp a).mpr (h q k R hR I hp a)

end Source

end DirectedDistances.PaperProofs.Section4
