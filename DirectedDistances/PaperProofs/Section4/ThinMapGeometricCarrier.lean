module

public import DirectedDistances.PaperProofs.Section4.ThinMapSideCarrier
public import DirectedDistances.KMSW.KMSWConstructedRealizationProof
public import DirectedDistances.KMSW.LeftmostRegionForward
public import DirectedDistances.PlanarMap.VariableRayStrip
import DirectedDistances.KMSW.ActiveTimeMonotone

/-! # Geometric carriers of the two thin sides

Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The drawing is the constructed monotone family drawing. Edge IDs include missing
geometric edges; directed arrows retain the separate `EdgePresent` predicate.
The left boundary is the persistent upper-left boundary, never an arbitrary ray witness. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter Quiver

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
@[expose] noncomputable def thinMapBoundaryDart (a : ThinMapSide) (i : ℕ) : ℕ × Bool :=
  match a with
  | .left => (kmswLeftBoundaryEdge w i, false)
  | .right => ((kmswRightmostPath w hfin hL htrans hR 0).edge i, false)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
@[expose] noncomputable def thinMapSideRegion (a : ThinMapSide) : Set ℂ :=
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let seam := pathTrace G (fun i => (P.edge i, false))
  match a with
  | .left => closedBetween
      (pathTrace G (thinMapBoundaryDart w hfin hL htrans hR .left)) seam
  | .right => closedBetween seam
      (pathTrace G (thinMapBoundaryDart w hfin hL htrans hR .right))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
@[expose] noncomputable def sideVertices (a : ThinMapSide) : Set ℕ :=
  {v | (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v ∈
    thinMapSideRegion w hfin hL htrans hR P a}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Presence is deliberately separate so that missing edges keep their geometric identity. -/
@[expose] noncomputable def sideEdges (a : ThinMapSide) : Set ℕ :=
  {e | ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).image ⊆
    thinMapSideRegion w hfin hL htrans hR P a}

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)
private theorem drawingFamily (w : ℕ → Fin 3) :
    ∀ n, ∃ Q : StageDrawing w n, Nonempty (MonotoneStageInvariant w n Q) :=
  fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
    ((monotone_family_all w) n).choose_spec⟩

local notation "F" => drawingFamily w

private theorem finish_mem_image (p : Polyline) (hp : 2 ≤ p.points.length) :
    p.finish ∈ p.image := by
  refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
  unfold Polyline.segmentAt
  have hi : p.points.length - 2 + 1 = p.points.length - 1 := by omega
  rw [hi, Polyline.point_last_eq_finish]
  exact right_mem_segment ℝ _ _

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem sideEdges_endpoints (a : ThinMapSide) {e : ℕ}
    (he : e ∈ sideEdges w hfin hL htrans hR P a) :
    edgeWest w e ∈ sideVertices w hfin hL htrans hR P a ∧
      edgeEast w e ∈ sideVertices w hfin hL htrans hR P a := by
  constructor
  · have hs := (G).arc_start (e, false)
    exact he (hs ▸ (show ((G).arc (e, false)).start ∈ ((G).arc (e, false)).image
      from Or.inl rfl))
  · have ht := (G).arc_finish (e, false)
    exact he (ht ▸ finish_mem_image ((G).arc (e, false)) ((G).arc_length (e, false)))

include htrans in
private theorem drawing_below_left_boundary {z q : ℂ} (hz : z ∈ (G).image)
    (hq : q ∈ pathTrace G (fun i => (kmswLeftBoundaryEdge w i, false)))
    (hre : q.re = z.re) : z.im ≤ q.im := by
  by_contra hn
  have hlt : q.im < z.im := lt_of_not_ge hn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
  have hi' : q ∈ (layoutArc w (kmswLeftBoundaryEdge w i)
      (kmswLeftBoundaryEdge w i)).image := by
    have ha := monotoneLimitDrawing_arc_layout w hfin F
      (kmswLeftBoundaryEdge w i) (kmswLeftBoundaryEdge w i)
      (kmsw_edge_allocated_by_self w _) false
    change q ∈ ((monotoneLimitDrawing w hfin F).arc
      (kmswLeftBoundaryEdge w i, false)).image at hi
    simpa only [ha, Bool.false_eq_true, ite_false] using hi
  obtain ⟨N, hN⟩ := monotoneStageRegion_excludes_above_persistentUL htrans
    (familyQ w (monotone_family_all w)) (familyG w (monotone_family_all w))
    i hi' hre hlt
  rw [monotoneFamilyDrawing_image] at hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  have hreg : z ∈ monotoneStageRegion (familyQ w (monotone_family_all w))
      (familyG w (monotone_family_all w)) n := by
    change z ∈ closedGraphRegion _ _ _ _
    rw [← (familyG w (monotone_family_all w) n).cover]
    exact Or.inl hn
  exact hN (max n N) (le_max_right _ _)
    (monotone_region_mono_of_le w _ _ (le_max_left n N) hreg)

private theorem shared_departures_self :
    GeodesicSharedDeparturesRightOf w hfin hL htrans hR 0 P P := by
  intro m n hmn
  have he : edgeWest w (P.edge m) = edgeWest w (P.edge n) := by
    rw [(P.edge_outgoing_at_initial w m).2, (P.edge_outgoing_at_initial w n).2, hmn]
  have hi := infinitePresentPath_west_injective hfin F P he
  subst n
  exact ⟨rfl, le_rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem seamTrace_subset_sideRegion (a : ThinMapSide) :
    pathTrace G (fun i => (P.edge i, false)) ⊆
      thinMapSideRegion w hfin hL htrans hR P a := by
  cases a with
  | left =>
    intro z hz
    refine ⟨⟨z, hz, rfl, le_rfl⟩, ?_⟩
    intro q hq hre
    have hzG : z ∈ (G).image := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Or.inr ⟨(P.edge i, false), hi⟩
    exact drawing_below_left_boundary w hfin htrans hzG hq hre
  | right =>
    exact trace_subset_closedBetween_of_inBetween w hfin hL htrans hR F 0 P _ P
      ⟨shared_departures_self w hfin hL htrans hR P,
        kmswRightmostPath_sharedDeparturesLeftOf w hfin hL htrans hR 0 P⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem seamEdge_mem_sideEdges (a : ThinMapSide) (i : ℕ) :
    P.edge i ∈ sideEdges w hfin hL htrans hR P a := by
  intro z hz
  exact seamTrace_subset_sideRegion w hfin hL htrans hR P a
    (Set.mem_iUnion.mpr ⟨i, hz⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem seamVertex_mem_sideVertices (a : ThinMapSide) (i : ℕ) :
    (P.initial i).1.id ∈ sideVertices w hfin hL htrans hR P a := by
  rw [← (P.edge_outgoing_at_initial w i).2]
  exact (sideEdges_endpoints w hfin hL htrans hR P a
    (seamEdge_mem_sideEdges w hfin hL htrans hR P a i)).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Truncation indexing: zero is the source, successor is the boundary edge's head. -/
@[expose] noncomputable def thinMapBoundaryVertex (a : ThinMapSide) : ℕ → ℕ
  | 0 => 0
  | i + 1 => edgeEast w (thinMapBoundaryDart w hfin hL htrans hR a i).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The ambient edge IDs and orientation are inherited without identifying parallel edges. -/
@[expose] noncomputable def sideDirectedStep (a : ThinMapSide) (u v : ℕ) : Prop :=
  ∃ e ∈ sideEdges w hfin hL htrans hR P a,
    EdgePresent w e ∧ edgeWest w e = u ∧ edgeEast w e = v

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Vertices reaching the indexed boundary vertex through the selected side. -/
@[expose] noncomputable def sourceAncestorVertices (a : ThinMapSide) (s : ℕ) : Set ℕ :=
  {v | v ∈ sideVertices w hfin hL htrans hR P a ∧
    Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a)
      v (thinMapBoundaryVertex w hfin hL htrans hR a s)}

private theorem side_reachable {a : ThinMapSide} {u v : ℕ}
    (h : Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a) u v) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨v⟩ := by
  induction h with
  | refl => exact ⟨.nil⟩
  | @tail b c h hbc ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨e, _, hp, hw, he⟩ := hbc
    exact ⟨p.cons ⟨e, hp, hw, he⟩⟩

private theorem path_start_eq_or_edge {u v : PresentVertex w} (p : Path u v) :
    u = v ∨ ∃ e ∈ pathEdgeList p, edgeWest w e = u.id := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons b c p e ih =>
    rcases ih with heq | ⟨f, hf, hw⟩
    · exact Or.inr ⟨e.val, List.mem_append_right _ (List.mem_singleton.mpr rfl),
        e.property.2.1.trans (congrArg PresentVertex.id heq.symm)⟩
    · exact Or.inr ⟨f, List.mem_append_left _ hf, hw⟩

include hfin in
private theorem ancestors_finite (b : ℕ) :
    {v : ℕ | Reachable (⟨v⟩ : PresentVertex w) ⟨b⟩}.Finite := by
  apply ((Set.finite_Iic (incomingActTimeMax w hfin b)).image
    (fun n => edgeWest w (act w n))).union (Set.finite_singleton b) |>.subset
  rintro v ⟨p⟩
  rcases path_start_eq_or_edge w p with heq | ⟨e, he, hw⟩
  · exact Or.inr (congrArg PresentVertex.id heq)
  · obtain ⟨hp, ht⟩ := path_actTime_le_incomingMax w hfin p e he
    exact Or.inl ⟨actTime w e hp, ht, by
      dsimp only
      rw [← actTime_spec w e hp]
      exact hw⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The proof uses increasing edge activation times and finite incoming incidence. -/
theorem sourceAncestorVertices_finite (a : ThinMapSide) (s : ℕ) :
    (sourceAncestorVertices w hfin hL htrans hR P a s).Finite := by
  apply (ancestors_finite w hfin (thinMapBoundaryVertex w hfin hL htrans hR a s)).subset
  intro v hv
  exact side_reachable w hfin hL htrans hR P hv.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The directed prefix of the canonical left boundary, retaining its edge IDs. -/
@[expose] noncomputable def thinMapLeftBoundaryPrefix : (n : ℕ) →
    Path (⟨0⟩ : PresentVertex w)
      ⟨thinMapBoundaryVertex w hfin hL htrans hR .left n⟩
  | 0 => .nil
  | n + 1 =>
    (thinMapLeftBoundaryPrefix n).cons
      ⟨kmswLeftBoundaryEdge w n,
        (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.2 n,
        by
          cases n with
          | zero =>
            exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.1
          | succ n =>
            exact ((kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 n).symm,
        rfl⟩

private theorem thinMapLeftBoundaryPrefix_length (n : ℕ) :
    (thinMapLeftBoundaryPrefix w hfin hL htrans hR n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [thinMapLeftBoundaryPrefix, Path.length_cons, ih]

private theorem thinMapLeftBoundaryPrefix_edges (n : ℕ) :
    pathEdgeList (thinMapLeftBoundaryPrefix w hfin hL htrans hR n) =
      List.ofFn (fun i : Fin n => kmswLeftBoundaryEdge w i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [thinMapLeftBoundaryPrefix, pathEdgeList]
    rw [ih, List.ofFn_succ_last]
    simp

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual persistent upper-left boundary as a present path from the source. -/
@[expose] noncomputable def thinMapLeftBoundaryPath : InfinitePresentPath w ⟨0⟩ where
  edge := kmswLeftBoundaryEdge w
  initial n := by
    exact ⟨⟨thinMapBoundaryVertex w hfin hL htrans hR .left n⟩,
      thinMapLeftBoundaryPrefix w hfin hL htrans hR n⟩
  prefix_length := by exact thinMapLeftBoundaryPrefix_length w hfin hL htrans hR
  prefix_edges := by exact thinMapLeftBoundaryPrefix_edges w hfin hL htrans hR

private theorem trace_eq_graph (Q : InfinitePresentPath w ⟨0⟩) :
    pathTrace G (fun i => (Q.edge i, false)) =
      {z | z.re ∈ rayDomain ((G).pos 0).re (infinitePresentPath_rightEnd hfin F Q) ∧
        z.im = infinitePresentPath_height hfin F Q z.re} := by
  have h := infinitePresentPath_trace_eq_graph hfin F Q
  have hs : ((monotoneLimitDrawing w hfin F).arc (Q.edge 0, false)).start =
      (G).pos 0 := by
    rw [(monotoneLimitDrawing w hfin F).arc_start]
    exact congrArg (G).pos Q.first_edge_outgoing.2
  rw [hs] at h
  exact h

private theorem leftBoundary_height_ge (x : ℝ)
    (hxP : x ∈ rayDomain ((G).pos 0).re (infinitePresentPath_rightEnd hfin F P))
    (hxB : x ∈ rayDomain ((G).pos 0).re
      (infinitePresentPath_rightEnd hfin F
        (thinMapLeftBoundaryPath w hfin hL htrans hR))) :
    infinitePresentPath_height hfin F P x ≤
      infinitePresentPath_height hfin F (thinMapLeftBoundaryPath w hfin hL htrans hR) x := by
  let B := thinMapLeftBoundaryPath w hfin hL htrans hR
  have eP := trace_eq_graph w hfin P
  have eB := trace_eq_graph w hfin B
  let z : ℂ := ⟨x, infinitePresentPath_height hfin F P x⟩
  let q : ℂ := ⟨x, infinitePresentPath_height hfin F B x⟩
  have hz : z ∈ pathTrace G (fun i => (P.edge i, false)) := by
    rw [eP]
    exact ⟨hxP, rfl⟩
  have hq : q ∈ pathTrace G (fun i => (kmswLeftBoundaryEdge w i, false)) := by
    change q ∈ pathTrace G (fun i => (B.edge i, false))
    rw [eB]
    exact ⟨hxB, rfl⟩
  have hzG : z ∈ (G).image := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Or.inr ⟨(P.edge i, false), hi⟩
  exact drawing_below_left_boundary w hfin htrans hzG hq rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical left boundary trace belongs to the left side. -/
theorem leftBoundaryTrace_subset_sideRegion :
    pathTrace G (thinMapBoundaryDart w hfin hL htrans hR .left) ⊆
      thinMapSideRegion w hfin hL htrans hR P .left := by
  let B := thinMapLeftBoundaryPath w hfin hL htrans hR
  have hend := infinitePresentPath_rightEnd_le_of_height_le w hfin F B P
    (fun x hxB hxP => leftBoundary_height_ge w hfin hL htrans hR P x hxP hxB)
  have eP := trace_eq_graph w hfin P
  have eB := trace_eq_graph w hfin B
  intro q hq
  have hqB : q ∈ pathTrace G (fun i => (B.edge i, false)) := hq
  obtain ⟨hxB, hqi⟩ := (Set.ext_iff.mp eB q).mp hqB
  have hxP : q.re ∈ rayDomain ((G).pos 0).re
      (infinitePresentPath_rightEnd hfin F P) := ⟨hxB.1, hxB.2.trans_le hend⟩
  refine ⟨⟨⟨q.re, infinitePresentPath_height hfin F P q.re⟩, ?_, rfl, ?_⟩, ?_⟩
  · rw [eP]
    exact ⟨hxP, rfl⟩
  · change infinitePresentPath_height hfin F P q.re ≤ q.im
    rw [hqi]
    exact leftBoundary_height_ge w hfin hL htrans hR P q.re hxP hxB
  · intro z hz hre
    have hqG : q ∈ (G).image := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
      exact Or.inr ⟨thinMapBoundaryDart w hfin hL htrans hR .left i, hi⟩
    exact drawing_below_left_boundary w hfin htrans hqG hz hre

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical rightmost boundary trace belongs to the right side. -/
theorem rightBoundaryTrace_subset_sideRegion :
    pathTrace G (thinMapBoundaryDart w hfin hL htrans hR .right) ⊆
      thinMapSideRegion w hfin hL htrans hR P .right := by
  let B := kmswRightmostPath w hfin hL htrans hR 0
  apply trace_subset_closedBetween_of_inBetween w hfin hL htrans hR F 0 P B B
  constructor
  · intro i j hs
    exact kmswRightmostPath_sharedDeparturesLeftOf w hfin hL htrans hR 0 P j i hs.symm
  · intro i j hs
    exact shared_departures_self w hfin hL htrans hR B j i hs.symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem source_mem_sideVertices (a : ThinMapSide) :
    0 ∈ sideVertices w hfin hL htrans hR P a := by
  have hw : edgeWest w (P.edge 0) = 0 := P.first_edge_outgoing.2
  rw [← hw]
  exact (sideEdges_endpoints w hfin hL htrans hR P a
    (seamEdge_mem_sideEdges w hfin hL htrans hR P a 0)).1

private theorem boundary_edge_mem (a : ThinMapSide) (i : ℕ) :
    (thinMapBoundaryDart w hfin hL htrans hR a i).1 ∈
      sideEdges w hfin hL htrans hR P a := by
  have hb : pathTrace G (thinMapBoundaryDart w hfin hL htrans hR a) ⊆
      thinMapSideRegion w hfin hL htrans hR P a := by
    cases a with
    | left => exact leftBoundaryTrace_subset_sideRegion w hfin hL htrans hR P
    | right => exact rightBoundaryTrace_subset_sideRegion w hfin hL htrans hR P
  have hd : (thinMapBoundaryDart w hfin hL htrans hR a i).2 = false := by
    cases a <;> rfl
  intro z hz
  apply hb
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  simpa only [← hd, Prod.mk.eta] using hz

private theorem boundary_edge_west (a : ThinMapSide) (i : ℕ) :
    edgeWest w (thinMapBoundaryDart w hfin hL htrans hR a i).1 =
      thinMapBoundaryVertex w hfin hL htrans hR a i := by
  cases a with
  | left =>
    cases i with
    | zero => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.1
    | succ i => exact ((kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 i).symm
  | right =>
    let B := kmswRightmostPath w hfin hL htrans hR 0
    cases i with
    | zero => exact B.first_edge_outgoing.2
    | succ i => exact (infinitePresentPath_edge_chain B i).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The source root is retained by every ancestor truncation, with no edge-root requirement. -/
theorem source_mem_sourceAncestorVertices (a : ThinMapSide) (s : ℕ) :
    0 ∈ sourceAncestorVertices w hfin hL htrans hR P a s := by
  refine ⟨source_mem_sideVertices w hfin hL htrans hR P a, ?_⟩
  induction s with
  | zero => exact .refl
  | succ s ih =>
    apply Relation.ReflTransGen.tail ih
    refine ⟨(thinMapBoundaryDart w hfin hL htrans hR a s).1,
      boundary_edge_mem w hfin hL htrans hR P a s, ?_,
      boundary_edge_west w hfin hL htrans hR a s, rfl⟩
    cases a with
    | left => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.2 s
    | right => exact ((kmswRightmostPath w hfin hL htrans hR 0).edge_outgoing s).1

end DirectedDistances.PaperProofs.Section4
