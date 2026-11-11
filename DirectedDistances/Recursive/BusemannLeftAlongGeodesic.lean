module

public import DirectedDistances.Recursive.BusemannLeftSideDecomposition
public import DirectedDistances.Recursive.BusemannRightSideLocalization
public import DirectedDistances.KMSW.HatLimitDartIdentification
public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
import DirectedDistances.KMSW.UIQBOTOrientation
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport
import DirectedDistances.PaperProofs.Section4.ThinMapSideConfinement








public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "RightDomain" =>
  selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "Q" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "SE" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a
local notation "SV" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
H-images of the actual hatted closed right side, with individual geometric edge IDs. -/
@[expose] noncomputable def closedRightEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) : Set ℕ :=
  hatLimitEdgeMap w h '' SE q .right

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The primed part, including edges entering beta vertices, glued to the hatted left side.
The complement is geometric: missing edges are retained without becoming arrows. -/
@[expose] noncomputable def closedLeftEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) : Set ℕ :=
  {e | ¬ MhatGeometricEdge w e} ∪ hatLimitEdgeMap w h '' SE q .left

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted seam's raw edge stream, before asserting raw first-divergence leftmostness. -/
@[expose] noncomputable def leftAlongSeamEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (i : ℕ) : ℕ :=
  hatLimitEdgeMap w h ((Q q).edge i)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Prepending a present arrow retains the exact arrow and the infinite tail. -/
private noncomputable def alongPrepend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (e : u ⟶ v) (S : InfinitePresentPath w v) : InfinitePresentPath w u where
  edge
    | 0 => e.val
    | n + 1 => S.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(S.initial n).1, e.toPath.comp (S.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Path.length_comp, Path.length_toPath, S.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, S.prefix_edges, List.ofFn_succ]
      rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A reachable prefix followed by an infinite path preserves every edge of that tail. -/
private theorem alongExtend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) (S : InfinitePresentPath w v) :
    ∃ T : InfinitePresentPath w u, Set.range S.edge ⊆ Set.range T.edge := by
  induction p with
  | nil => exact ⟨S, Set.Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨T, hT⟩ := ih (alongPrepend e S)
    refine ⟨T, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hT ⟨i + 1, rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every present edge in the coherent hatted carrier lies in one of the two closed sides. -/
private theorem alongSideEdgeCover (q : RightDomain) (e : ℕ)
    (he : EdgePresent (W q) e) : e ∈ SE q .left ∪ SE q .right := by
  classical
  by_cases hs : ∃ i, e = (Q q).edge i
  · obtain ⟨i, rfl⟩ := hs
    exact Or.inl (seamEdge_mem_sideEdges
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i)
  · have hoff := fun i hi => hs ⟨i, hi⟩
    obtain ⟨p⟩ := allocated_vertex_reachable_from_zero (W q) (HL q)
      (edgeWest (W q) e) (kmswVertexAllocated_all _ ⟨edgeWest (W q) e⟩)
    let a : (⟨edgeWest (W q) e⟩ : PresentVertex (W q)) ⟶
        ⟨edgeEast (W q) e⟩ := ⟨e, he, rfl, rfl⟩
    let S := alongPrepend a
      (kmswRightmostPath (W q) (HF q) (HL q) (HT q) (HR q) (edgeEast (W q) e))
    obtain ⟨T, hT⟩ := alongExtend p S
    obtain ⟨i, hi⟩ := hT (show e ∈ Set.range S.edge from ⟨0, rfl⟩)
    have hz := thinMapPathTrace_subset_sideRegions
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) T
      (Set.mem_iUnion.mpr ⟨i, hi ▸ (thinMapArcSeed_mem_interior (W q) (HF q) e).1⟩)
    rw [hi] at hz
    rcases hz with hl | hr
    · exact Or.inl ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left e hoff).mpr hl)
    · exact Or.inr ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right e hoff).mpr hr)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The closed raw sides cover every geometric edge, including missing boundary edges.
The code equality is carrier identification, not an additional geometric premise. -/
theorem closedEdges_cover (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    closedLeftEdges w h q ∪ closedRightEdges w h q = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro e
  by_cases he : MhatGeometricEdge w e
  · obtain ⟨a, rfl⟩ := (hatLimitEdgeMap_geometric_range_iff w h e).mpr he
    have ha : EdgePresent (W q) a := hw.symm ▸ hatCodes_edge_present w h a
    rcases alongSideEdgeCover q a ha with hl | hr
    · exact Or.inl (Or.inr ⟨a, hl, rfl⟩)
    · exact Or.inr ⟨a, hr, rfl⟩
  · exact Or.inl (Or.inl he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The intersection is exactly the raw image of the seam, preserving parallel-edge identity.
This edge identity does not yet identify the seam as the raw leftmost geodesic. -/
theorem closedEdges_inter (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) :
    closedLeftEdges w h q ∩ closedRightEdges w h q =
      Set.range (leftAlongSeamEdge w h q) := by
  ext e
  constructor
  · rintro ⟨hl, a, ha, rfl⟩
    have hm := (hatLimitEdgeMap_geometric_range_iff w h _).mp ⟨a, rfl⟩
    rcases hl with hn | ⟨b, hb, he⟩
    · exact (hn hm).elim
    · have hba := hatLimitEdgeMap_injective w h he
      subst b
      have hs : a ∈ Set.range (Q q).edge := by
        rw [← thinMapSideEdges_inter_eq_seamEdges
          (W q) (HF q) (HL q) (HT q) (HR q) (Q q)]
        exact ⟨hb, ha⟩
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Or.inr ⟨(Q q).edge i, seamEdge_mem_sideEdges
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i, rfl⟩,
      ⟨(Q q).edge i, seamEdge_mem_sideEdges
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right i, rfl⟩⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The actual hatted-to-raw incidence map, using the coherent stream identification. -/
@[expose] noncomputable def alongHatFunctor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    Prefunctor (PresentVertex (W q)) (PresentVertex w) where
  obj a := ⟨hatLimitVertexMap w h a.id⟩
  map {a b} e := by
    have he : EdgePresent (hatCodes w h) e.val := by
      rw [← hw]
      exact e.property.1
    have hi := hatLimit_edge_incidence (hatLimitExplicitInput w h) he
    rw [← hw] at hi
    exact ⟨hatLimitEdgeMap w h e.val, hi.1,
      hi.2.1.trans (congrArg (hatLimitVertexMap w h) e.property.2.1),
      hi.2.2.trans (congrArg (hatLimitVertexMap w h) e.property.2.2)⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The incidence map preserves every path length. -/
theorem alongMap_length (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h)
    {a b : PresentVertex (W q)} (p : Path a b) :
    ((alongHatFunctor w h q hw).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The incidence map preserves the ordered edge-ID list through H. -/
theorem alongMap_edges (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h)
    {a b : PresentVertex (W q)} (p : Path a b) :
    pathEdgeList ((alongHatFunctor w h q hw).mapPath p) =
      (pathEdgeList p).map (hatLimitEdgeMap w h) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, pathEdgeList, ih, List.map_append,
      List.map_singleton]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The mapped infinite path before transporting its root equality. -/
@[expose] noncomputable def alongMappedPath (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    InfinitePresentPath w ⟨hatLimitVertexMap w h 0⟩ where
  edge := leftAlongSeamEdge w h q
  initial n := ⟨(alongHatFunctor w h q hw).obj ((Q q).initial n).1,
    (alongHatFunctor w h q hw).mapPath ((Q q).initial n).2⟩
  prefix_length n := (alongMap_length w h q hw _).trans ((Q q).prefix_length n)
  prefix_edges n := by
    change pathEdgeList ((alongHatFunctor w h q hw).mapPath ((Q q).initial n).2) = _
    rw [alongMap_edges, (Q q).prefix_edges]
    simp only [List.map_ofFn, Function.comp_def]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Transport of the initial vertex does not change the edge stream. -/
private theorem alongRootTransport_edge {w : ℕ → Fin 3} {a b : PresentVertex w}
    (hab : a = b) (P : InfinitePresentPath w a) :
    (hab ▸ P).edge = P.edge := by
  subst b
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Transport of the initial vertex does not change any terminal prefix vertex. -/
private theorem alongRootTransport_vertex {w : ℕ → Fin 3} {a b : PresentVertex w}
    (hab : a = b) (P : InfinitePresentPath w a) (n : ℕ) :
    ((hab ▸ P).initial n).1 = (P.initial n).1 := by
  subst b
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw root-started image of the hatted canonical leftmost LDP path.
Raw first-divergence leftmostness is not included in this definition or presumed. -/
@[expose] noncomputable def leftAlongRawGeodesic (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h) :
    InfinitePresentPath w ⟨0⟩ :=
  (congrArg PresentVertex.mk (hatLimitExplicitInput w h).root) ▸
    alongMappedPath w h q hw

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw path has exactly the H-image edge stream, with no quotient of parallel edges. -/
theorem leftAlongRawGeodesic_edge (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    (leftAlongRawGeodesic w h q hw).edge = leftAlongSeamEdge w h q :=
  alongRootTransport_edge _ _

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every prefix endpoint is the H-image of the actual hatted prefix endpoint. -/
theorem leftAlongRawGeodesic_vertex (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) (n : ℕ) :
    ((leftAlongRawGeodesic w h q hw).initial n).1 =
      ⟨hatLimitVertexMap w h ((Q q).initial n).1.id⟩ :=
  alongRootTransport_vertex _ _ n

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The closed sides intersect exactly in the edges of the constructed raw infinite path. -/
theorem closedEdges_inter_rawGeodesic (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    closedLeftEdges w h q ∩ closedRightEdges w h q =
      Set.range (leftAlongRawGeodesic w h q hw).edge := by
  rw [leftAlongRawGeodesic_edge]
  exact closedEdges_inter w h q

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw image has longest prefixes: all raw competitors lift with the same length. -/
theorem leftAlongRawGeodesic_initial_isLongest (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h) (n : ℕ) :
    IsLongest ((leftAlongRawGeodesic w h q hw).initial n).2 := by
  have hQ : (Q q).HasLongestSegments :=
    kmswLeftmostLdpPath_hasLongestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 _
  intro p
  have hv := leftAlongRawGeodesic_vertex w h q hw n
  have hroot : hatLimitVertexMap w h 0 = 0 := (hatLimitExplicitInput w h).root
  have hlift : ∃ r : Path (⟨0⟩ : PresentVertex (W q)) ((Q q).initial n).1,
      r.length = p.length := by
    obtain ⟨p', hp'⟩ : ∃ p' : Path
        (⟨hatLimitVertexMap w h 0⟩ : PresentVertex w)
        ⟨hatLimitVertexMap w h ((Q q).initial n).1.id⟩,
        p'.length = p.length := by
      rw [hroot, ← hv]
      exact ⟨p, rfl⟩
    obtain ⟨r, hr⟩ := rightHat_path_lift w h ⟨0⟩ ⟨((Q q).initial n).1.id⟩ p'
    have hr' : ∃ r : Path (⟨0⟩ : PresentVertex (hatCodes w h))
        ⟨((Q q).initial n).1.id⟩, r.length = p.length := ⟨r, hr.trans hp'⟩
    rw [← hw] at hr'
    exact hr'
  obtain ⟨r, hr⟩ := hlift
  have hn := (Q q).initial_isLongest (W q) hQ n r
  rw [hr, (Q q).prefix_length] at hn
  rw [(leftAlongRawGeodesic w h q hw).prefix_length]
  exact hn

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every nonempty segment of the raw image is longest, with the literal source indexing. -/
theorem leftAlongRawGeodesic_hasLongestSegments (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h) :
    (leftAlongRawGeodesic w h q hw).HasLongestSegments := by
  let P := leftAlongRawGeodesic w h q hw
  intro a b ha hab
  obtain ⟨z, p, r, hpr, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, r, ?_, ?_, ?_⟩
  · have hlen := P.prefix_length b
    rw [hpr, Path.length_comp, hp] at hlen
    omega
  · rw [← P.prefix_edges b, hpr, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := leftAlongRawGeodesic_initial_isLongest w h q hw b
    change IsLongest (P.initial b).2 at hopt
    rw [hpr] at hopt
    exact hopt.of_comp_right

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The seam root distance is finite, attained, and equal to the index, including zero. -/
theorem leftAlongRawGeodesic_root_distance (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h) (t : ℕ) :
    presentLdp (⟨0⟩ : PresentVertex w)
        ((leftAlongRawGeodesic w h q hw).initial t).1 =
      ((t : ℕ∞) : WithBot ℕ∞) :=
  leftGeodesic_root_distance _ (leftAlongRawGeodesic_hasLongestSegments w h q hw) t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Nothing outside the induced hatted map belongs to the closed right edge carrier. -/
theorem closedRightEdges_subset_hat (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) : closedRightEdges w h q ⊆ {e | MhatGeometricEdge w e} := by
  rintro e ⟨a, _, rfl⟩
  exact (hatLimitEdgeMap_geometric_range_iff w h _).mp ⟨a, rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A path ending outside the hatted map uses only edges outside it. -/
private theorem alongOutsideEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y) (hy : y ∉ leftHatVertices w) :
    ∀ e ∈ pathEdgeList p, ¬ MhatGeometricEdge w e := by
  induction p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons z y p e ih =>
    have hz : z ∉ leftHatVertices w := by
      intro hz
      exact hy (leftHatVertices_closed hz e.toPath)
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih hz f hf
    · have heq : f = e.val := List.mem_singleton.mp hf
      subst f
      intro hgeom
      apply hy
      have hend := hgeom.2
      rw [e.property.2.2] at hend
      exact hend

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A genuine first-entry prefix uses only primed edges, including its final crossing arrow. -/
private theorem alongEntryEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y)
    (hp : ∀ u ∈ p.vertices, u ≠ y → u ∉ leftHatVertices w) :
    ∀ e ∈ pathEdgeList p, ¬ MhatGeometricEdge w e := by
  cases p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons z y p e =>
    have hzy : z ≠ y := by
      intro heq
      have hc : ∀ v : PresentVertex w, ∀ r : Path v v, r.length = 0 :=
        presentVertex_acyclic w
      subst y
      have hz := hc z e.toPath
      simp only [Path.length_toPath] at hz
      omega
    have hz : z ∉ leftHatVertices w := hp z
      ((Path.mem_vertices_cons p e).mpr (Or.inl p.end_mem_vertices)) hzy
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact alongOutsideEdges p hz f hf
    · have heq : f = e.val := List.mem_singleton.mp hf
      subst f
      intro hgeom
      apply hz
      have hstart := hgeom.1
      rw [e.property.2.1] at hstart
      exact hstart

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every first-entry split has a closed-left prefix and an entirely hatted suffix.
This proves confinement of the outside part without assuming a planar gluing bridge. -/
theorem leftAlong_firstEntry_closedLeft (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) {x y : PresentVertex w} (p : Path x y)
    (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    ∃ v ∈ leftHatEntryVertices w, ∃ a : Path x v, ∃ b : Path v y,
      p = a.comp b ∧ (∀ e ∈ pathEdgeList a, e ∈ closedLeftEdges w h q) ∧
      ∀ u ∈ b.vertices, u ∈ leftHatVertices w := by
  obtain ⟨v, hv, a, b, hp, ha, hb⟩ := leftHat_firstEntry_split p hx hy
  exact ⟨v, hv, a, b, hp, fun e he => Or.inl (alongEntryEdges a ha e he), hb⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost-sure concrete raw edge decomposition and a longest root-started seam image.
This does not assert raw leftmostness, side exchange, or the left Busemann formula. -/
theorem leftAlong_closedEdges_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (q : RightDomain)
        (hw : (W q) = hatCodes w h) (P : InfinitePresentPath w ⟨0⟩),
        q.1 = integrateCodes (hatLawCodes ω) ∧
        P = leftAlongRawGeodesic w h q hw ∧ P.HasLongestSegments ∧
        closedLeftEdges w h q ∪ closedRightEdges w h q = Set.univ ∧
        closedLeftEdges w h q ∩ closedRightEdges w h q = Set.range P.edge := by
  filter_upwards [rightHatThinBoundaryIdentification_proved] with ω hω
  obtain ⟨h, q, hq, hw, _⟩ := hω
  exact ⟨h, q, hw, leftAlongRawGeodesic _ h q hw, hq, rfl,
    leftAlongRawGeodesic_hasLongestSegments _ h q hw,
    closedEdges_cover _ h q hw, closedEdges_inter_rawGeodesic _ h q hw⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An edge launched away from the seam stays in its launch side. -/
private theorem alongNonseamEdge (q : RightDomain) (a : ThinMapSide)
    {u v : PresentVertex (W q)} (e : u ⟶ v) (hv : u.id ∈ SV q a)
    (hs : ∀ i, u ≠ ((Q q).initial i).1) : e.val ∈ SE q a := by
  have hu := allocated_vertex_reachable_from_zero (W q) (HL q) u.id
    (kmswVertexAllocated_all _ u)
  have hoff : ∀ i, e.val ≠ (Q q).edge i := by
    intro i hi
    apply hs i
    exact congrArg PresentVertex.mk
      (e.property.2.1.symm.trans (hi ▸ ((Q q).edge_outgoing_at_initial (W q) i).2))
  apply (thinMapArc_subset_sideRegion_iff_seed
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a e.val hoff).mpr
  apply thinMapArcSeed_mem_side_of_nonseam_launch
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a e.val e.property.1
  · exact e.property.2.1.symm ▸ hu
  · exact e.property.2.1.symm ▸ hv
  · intro i hi
    exact hs i (congrArg PresentVertex.mk (e.property.2.1.symm.trans hi))
  · exact hoff

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A hatted vertex in both closed sides is an actual seam vertex. -/
private theorem alongVertexInter (q : RightDomain) (v : PresentVertex (W q))
    (hl : v.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, v = ((Q q).initial i).1 := by
  have hv : (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q))).pos v.id ∈
      pathTrace (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q)))
        (fun i => ((Q q).edge i, false)) := by
    rw [← thinMapSideRegions_inter_eq_seamTrace
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q)]
    exact ⟨hl, hr⟩
  obtain ⟨i, hi⟩ := (thinMapVertex_mem_seamTrace_iff (W q) (HF q) (Q q) v.id).mp hv
  exact ⟨i, congrArg PresentVertex.mk hi⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A hatted right-to-left path visits the seam; this uses the constructed planar sides. -/
private theorem alongRightToLeftHitsSeam (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v)
    (hr : u.id ∈ SV q .right) (hl : v.id ∈ SV q .left) :
    ∃ i, ((Q q).initial i).1 ∈ p.vertices := by
  classical
  by_contra hn
  have hno : ∀ z ∈ p.vertices, ∀ i, z ≠ ((Q q).initial i).1 := by
    intro z hz i hi
    exact hn ⟨i, hi ▸ hz⟩
  have hend : v.id ∈ SV q .right := by
    clear hl hn
    induction p with
    | nil => exact hr
    | @cons y z p e ih =>
      have hpno : ∀ b ∈ p.vertices, ∀ i, b ≠ ((Q q).initial i).1 := by
        intro b hb
        exact hno b ((Path.mem_vertices_cons p e).mpr (Or.inl hb))
      have hy := ih hpno
      have ey := alongNonseamEdge q .right e hy
        (hno y ((Path.mem_vertices_cons p e).mpr (Or.inl p.end_mem_vertices)))
      exact e.property.2.2 ▸
        (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right ey).2
  obtain ⟨i, hi⟩ := alongVertexInter q v hl hend
  exact hno v p.end_mem_vertices i hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A seam segment dominates any competitor between its endpoints and lies in the left side. -/
private theorem alongLeftSeamSegment (q : RightDomain) (i j : ℕ)
    (p : Path ((Q q).initial i).1 ((Q q).initial j).1) :
    ∃ r : Path ((Q q).initial i).1 ((Q q).initial j).1,
      p.length ≤ r.length ∧ ∀ e ∈ pathEdgeList r, e ∈ SE q .left := by
  have hlong : (Q q).HasLongestSegments :=
    kmswLeftmostLdpPath_hasLongestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 _
  have hij : i ≤ j := by
    by_contra hn
    have hji : j ≤ i := by omega
    have H := (Q q).exists_shift_split j (i - j)
    rw [Nat.add_sub_of_le hji] at H
    obtain ⟨_, r, _, _, hlen, _⟩ := H
    have hz := presentVertex_acyclic (W q) _ (r.comp p)
    rw [Path.length_comp, hlen] at hz
    omega
  have H := (Q q).exists_shift_split i (j - i)
  rw [Nat.add_sub_of_le hij] at H
  obtain ⟨s, r, heq, _, _, hlist⟩ := H
  have hop := (Q q).initial_isLongest (W q) hlong j
  rw [heq] at hop
  refine ⟨r, hop.of_comp_right p, ?_⟩
  intro e he
  rw [hlist] at he
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
  exact hk ▸ seamEdge_mem_sideEdges
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left (i + k.val)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every hatted path between closed-left vertices has a closed-left competitor at least
as long. Right excursions are replaced with longest seam segments. -/
theorem leftAlongHat_path_dominance (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v)
    (hul : u.id ∈ SV q .left) (hvl : v.id ∈ SV q .left) :
    ∃ r : Path u v, p.length ≤ r.length ∧
      ∀ e ∈ pathEdgeList r, e ∈ SE q .left := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    by_cases hz : p.length = 0
    · obtain rfl := p.eq_of_length_zero hz
      obtain rfl := p.eq_nil_of_length_zero hz
      exact ⟨.nil, by omega, fun _ he => False.elim (List.not_mem_nil he)⟩
    · obtain ⟨b, e, t, hp, hlen⟩ := p.length_ne_zero_iff_eq_comp.mp hz
      by_cases he : e.val ∈ SE q .left
      · have hbl : b.id ∈ SV q .left := e.property.2.2 ▸
          (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left he).2
        obtain ⟨r, hrlen, hr⟩ := ih t.length (by omega) t hbl hvl rfl
        refine ⟨e.toPath.comp r, ?_, ?_⟩
        · rw [← hn, hp, Path.length_comp, Path.length_comp]
          exact Nat.add_le_add_left hrlen _
        · intro f hf
          rw [pathEdgeList_comp] at hf
          rcases List.mem_append.mp hf with hf | hf
          · have hfe : f = e.val := by
              change f ∈ ([] ++ [e.val]) at hf
              exact List.mem_singleton.mp hf
            exact hfe ▸ he
          · exact hr f hf
      · have hus : ∃ i, u = ((Q q).initial i).1 := by
          by_contra hs
          exact he (alongNonseamEdge q .left e hul (fun i hi => hs ⟨i, hi⟩))
        have her := (alongSideEdgeCover q e.val e.property.1).resolve_left he
        have hbr : b.id ∈ SV q .right := e.property.2.2 ▸
          (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right her).2
        obtain ⟨j, hj⟩ := alongRightToLeftHitsSeam q t hbr hvl
        obtain ⟨s, t', ht⟩ := t.exists_eq_comp_of_mem_vertices hj
        obtain ⟨i, hi⟩ := hus
        have hex : ∃ r : Path u ((Q q).initial j).1,
            (e.toPath.comp s).length ≤ r.length ∧
              ∀ f ∈ pathEdgeList r, f ∈ SE q .left := by
          subst u
          exact alongLeftSeamSegment q i j (e.toPath.comp s)
        obtain ⟨r, hrlen, hr⟩ := hex
        have hjl := seamVertex_mem_sideVertices
          (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left j
        have hsplit : p.length = 1 + s.length + t'.length := by
          rw [hp, ht, Path.length_comp, Path.length_comp, Path.length_toPath]
          omega
        obtain ⟨r', hr'len, hr'⟩ := ih t'.length (by omega) t' hjl hvl rfl
        refine ⟨r.comp r', ?_, ?_⟩
        · simp only [Path.length_comp, Path.length_toPath] at hrlen ⊢
          omega
        · intro f hf
          rw [pathEdgeList_comp] at hf
          exact (List.mem_append.mp hf).elim (hr f) (hr' f)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A hatted left-to-right path visits the seam. -/
private theorem alongLeftToRightHitsSeam (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v)
    (hl : u.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, ((Q q).initial i).1 ∈ p.vertices := by
  classical
  by_contra hn
  have hno : ∀ z ∈ p.vertices, ∀ i, z ≠ ((Q q).initial i).1 := by
    intro z hz i hi
    exact hn ⟨i, hi ▸ hz⟩
  have hend : v.id ∈ SV q .left := by
    clear hr hn
    induction p with
    | nil => exact hl
    | @cons y z p e ih =>
      have hpno : ∀ b ∈ p.vertices, ∀ i, b ≠ ((Q q).initial i).1 := by
        intro b hb
        exact hno b ((Path.mem_vertices_cons p e).mpr (Or.inl hb))
      have hy := ih hpno
      have ey := alongNonseamEdge q .left e hy
        (hno y ((Path.mem_vertices_cons p e).mpr (Or.inl p.end_mem_vertices)))
      exact e.property.2.2 ▸
        (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left ey).2
  obtain ⟨i, hi⟩ := alongVertexInter q v hend hr
  exact hno v p.end_mem_vertices i hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Seam vertices have unique indices, by acyclicity and exact segment lengths. -/
private theorem alongSeamVertex_injective (q : RightDomain) :
    Function.Injective (fun i => ((Q q).initial i).1) := by
  have hz {u v : PresentVertex (W q)} (p : Path u v) (huv : u = v) :
      p.length = 0 := by
    subst v
    exact presentVertex_acyclic (W q) _ p
  have hordered (i j : ℕ) (hij : i ≤ j)
      (heq : ((Q q).initial i).1 = ((Q q).initial j).1) : i = j := by
    have H := (Q q).exists_shift_split i (j - i)
    rw [Nat.add_sub_of_le hij] at H
    obtain ⟨_, r, _, _, hr, _⟩ := H
    have hr0 := hz r heq
    omega
  intro i j heq
  rcases le_total i j with hij | hji
  · exact hordered i j hij heq
  · exact (hordered j i hji heq.symm).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite path visiting the seam splits at its last seam vertex. -/
private theorem alongLastSeamSplit (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v)
    (hv : ∃ i, ((Q q).initial i).1 ∈ p.vertices) :
    ∃ i, ∃ a : Path u ((Q q).initial i).1,
      ∃ b : Path ((Q q).initial i).1 v,
      p = a.comp b ∧ ∀ j, ((Q q).initial j).1 ∈ b.vertices → j = i := by
  classical
  induction p with
  | nil =>
    obtain ⟨i, hi⟩ := hv
    have heq : ((Q q).initial i).1 = u := by
      simpa only [Path.vertices_nil, List.mem_singleton] using hi
    subst u
    refine ⟨i, .nil, .nil, rfl, ?_⟩
    intro j hj
    apply alongSeamVertex_injective q
    simpa only [Path.vertices_nil, List.mem_singleton] using hj
  | @cons z v p e ih =>
    by_cases hend : ∃ i, v = ((Q q).initial i).1
    · obtain ⟨i, rfl⟩ := hend
      refine ⟨i, p.cons e, .nil, (Path.comp_nil _).symm, ?_⟩
      intro j hj
      apply alongSeamVertex_injective q
      simpa only [Path.vertices_nil, List.mem_singleton] using hj
    · have hv' : ∃ i, ((Q q).initial i).1 ∈ p.vertices := by
        obtain ⟨i, hi⟩ := hv
        rcases (Path.mem_vertices_cons p e).mp hi with hi | hi
        · exact ⟨i, hi⟩
        · exact (hend ⟨i, hi.symm⟩).elim
      obtain ⟨i, a, b, hp, hb⟩ := ih hv'
      refine ⟨i, a, b.cons e, ?_, ?_⟩
      · rw [hp, Path.comp_cons]
      · intro j hj
        rcases (Path.mem_vertices_cons b e).mp hj with hj | hj
        · exact hb j hj
        · exact (hend ⟨j, hj.symm⟩).elim

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The full single-seam exchange inside the hatted carrier, without a separation premise.
The suffix has only its starting seam vertex; the seam segment joins the left prefix. -/
theorem leftAlongHat_geodesicExchange (q : RightDomain) :
    LeftClosedSideGeodesicExchange (W q) (Q q)
      {v | v.id ∈ SV q .left} {v | v.id ∈ SV q .right}
      (SE q .left) (SE q .right) := by
  intro u hu v hv p hp
  obtain ⟨i, hi⟩ := alongLeftToRightHitsSeam q p hu hv
  obtain ⟨a, b, hsplit⟩ := p.exists_eq_comp_of_mem_vertices hi
  have hil := seamVertex_mem_sideVertices
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i
  have hir := seamVertex_mem_sideVertices
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right i
  obtain ⟨aL, haLlen, haL⟩ := leftAlongHat_path_dominance q a hu hil
  obtain ⟨bR, hbRlen, hbR⟩ := rightSide_path_dominance q b
    (allocated_vertex_reachable_from_zero (W q) (HL q) _
      (kmswVertexAllocated_all _ _)) hir hv
  have hlen : (aL.comp bR).length = p.length := by
    have hle := hp (aL.comp bR)
    have hplen : p.length = a.length + b.length := by rw [hsplit, Path.length_comp]
    rw [Path.length_comp] at hle ⊢
    omega
  have hc : IsLongest (aL.comp bR) := hp.of_length_eq hlen
  obtain ⟨j, s, t, hbRsplit, ht⟩ := alongLastSeamSplit q bR
    ⟨i, bR.start_mem_vertices⟩
  have hc' : IsLongest ((aL.comp s).comp t) := by
    rw [Path.comp_assoc, ← hbRsplit]
    exact hc
  have hQ : (Q q).HasLongestSegments :=
    kmswLeftmostLdpPath_hasLongestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 _
  obtain ⟨r, _, _, hrEdges, hrlen, hrLongest⟩ :=
    leftGeodesic_replace_excursion (Q q) hQ i j aL s t hc'
  refine ⟨j, aL.comp r, t, ?_, hrLongest, ?_, ?_, ht⟩
  · have hbLen := congrArg Path.length hbRsplit
    simp only [Path.length_comp] at hlen hbLen ⊢
    omega
  · intro e he
    rw [pathEdgeList_comp] at he
    rcases List.mem_append.mp he with he | he
    · exact haL e he
    · rw [hrEdges] at he
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
      exact hk ▸ seamEdge_mem_sideEdges
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left (i + k.val)
  · intro e he
    apply hbR e
    rw [hbRsplit, pathEdgeList_comp]
    exact List.mem_append.mpr (Or.inr he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The concrete raw closed-right vertex set, on the same raw carrier as the edge sets. -/
@[expose] noncomputable def closedRightVertices (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) : Set (PresentVertex w) :=
  {v | ∃ a ∈ SV q .right, hatLimitVertexMap w h a = v.id}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The primed vertices glued to the H-images of the hatted closed left vertices. -/
@[expose] noncomputable def closedLeftVertices (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) : Set (PresentVertex w) :=
  {v | v ∉ leftHatVertices w} ∪
    {v | ∃ a ∈ SV q .left, hatLimitVertexMap w h a = v.id}




@[expose] def LeftAlongEntryLocalization (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) : Prop :=
  ∀ v ∈ leftHatEntryVertices w,
    ∃ a ∈ SV q .left, hatLimitVertexMap w h a = v.id




@[expose] def LeftAlongRawGeodesicExchange (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h) : Prop :=
  LeftClosedSideGeodesicExchange w (leftAlongRawGeodesic w h q hw)
    (closedLeftVertices w h q) (closedRightVertices w h q)
    (closedLeftEdges w h q) (closedRightEdges w h q)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Reachability step toward the left profile, proved below: each negative boundary vertex
reaches every sufficiently late seam vertex. No coalescence premise is introduced.
This proposition is never assumed by any theorem in this file. -/
@[expose] def LeftAlongNegativeBoundaryReachability (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (q : RightDomain)
    (hw : (W q) = hatCodes (fun i => ω (i + 1)) h) : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∀ᶠ t in atTop,
    Reachable (⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ :
      PresentVertex (fun i => ω (i + 1)))
      ((leftAlongRawGeodesic _ h q hw).initial t).1





@[expose] def LeftAlongBusemannFormulaAE : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h),
      q.1 = integrateCodes (hatLawCodes ω) ∧
      LeftBusemannAlongGeodesic ω (leftAlongRawGeodesic w h q hw) (closedLeftEdges w h q)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Any allocated raw vertex reaches a tail of the nonnegative boundary through present edges. -/
private theorem alongReachesBoundaryTail (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (v : PresentVertex w) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w hb l) := by
  obtain ⟨n, hn⟩ := kmswVertexAllocated_all w v
  obtain ⟨k, hkrec, hnk⟩ := (right_record_infinite w hb.R_unbounded_below).exists_gt n
  have hkpos : 0 < k := by omega
  have hrec : ∀ i < k, R w k < R w i := hkrec
  have hneg : R w k < 0 := by
    have hh := hrec 0 hkpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w k
  have hbpos : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w hb b = k := by
    have hle : boundaryHitTime w hb b ≤ k := by
      rw [boundaryHitTime_right_eq_find w hb hbpos]
      exact Nat.find_min' (hb.rightHit b hbpos) (by dsimp [b]; omega)
    have hge : k ≤ boundaryHitTime w hb b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w hb b) (by omega)
      have hh' := boundaryHitTime_right_spec w hb hbpos
      rw [hh'] at hh
      have hRb : R w k = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w k = boundaryPresentVertex w hb b := by
    apply congrArg PresentVertex.mk
    have he := edge_endpoints_eq w (act_lt_nextEdge w (le_refl k))
    rw [boundaryVertex_eq_edgeWest_hit w hb b, htime]
    exact he.1
  have hvk : v.id < (kmswStage w (k - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ k - 1))
  have hr : Reachable v (boundaryPresentVertex w hb b) := by
    have hh := allocated_vertex_reaches_strict_record w k
      (fun i hi => by have := hrec i hi; omega) hkpos v.id hvk
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w hb (by omega) (by omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw vertex reaches some seam vertex, using the coherent hatted cut vertices.
No coalescence or side confinement is assumed; the path may visit either side. -/
theorem leftAlongRawGeodesic_reachable_some (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h)
    (x : PresentVertex w) :
    ∃ i, Reachable x ((leftAlongRawGeodesic w h q hw).initial i).1 := by
  let hb := hatBoundaryHitWitnesses w h
  obtain ⟨B, hB⟩ := alongReachesBoundaryTail w hb x
  obtain ⟨b, _, _, hbmap, _⟩ := rightHatBoundaryIdentification_proved w h hb
  let a : PresentVertex (W q) := ⟨(b B).id⟩
  have hcuts : {v : ℕ | mapCutVertex (W q) (HF q) v}.Infinite := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hcuts, _⟩ := selectedCutCoherentDomain_spec
      XDP.ldp renewalTime renewalTime_positiveSuccessTime q
    exact hcuts
  obtain ⟨i, p⟩ := vertex_reachable_seam_of_infinite_cutVertices
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) hcuts a.id
  obtain ⟨p⟩ := p
  have hm : Reachable (⟨hatLimitVertexMap w h (b B).id⟩ : PresentVertex w)
      ((leftAlongRawGeodesic w h q hw).initial i).1 := by
    rw [leftAlongRawGeodesic_vertex]
    exact ⟨(alongHatFunctor w h q hw).mapPath p⟩
  have hbv : (⟨hatLimitVertexMap w h (b B).id⟩ : PresentVertex w) =
      boundaryPresentVertex w hb (B : ℤ) := congrArg PresentVertex.mk (hbmap B)
  rw [hbv] at hm
  exact ⟨i, (hB (B : ℤ) le_rfl).trans hm⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw vertex reaches all sufficiently late seam vertices, with no extra premise. -/
theorem leftAlongRawGeodesic_eventually_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h)
    (x : PresentVertex w) :
    ∀ᶠ t in atTop, Reachable x ((leftAlongRawGeodesic w h q hw).initial t).1 := by
  obtain ⟨i, hi⟩ := leftAlongRawGeodesic_reachable_some w h q hw x
  refine eventually_atTop.mpr ⟨i, fun t ht => hi.trans ?_⟩
  have H := (leftAlongRawGeodesic w h q hw).exists_shift_split i (t - i)
  rw [Nat.add_sub_of_le ht] at H
  obtain ⟨_, r, _, _, _, _⟩ := H
  exact r.reachable

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Negative-boundary reachability is proved, simultaneously for every boundary index.
This is weaker than coalescence of the canonical raw leftmost geodesics. -/
theorem leftAlongNegativeBoundaryReachability_proved (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (q : RightDomain)
    (hw : (W q) = hatCodes (fun i => ω (i + 1)) h) :
    LeftAlongNegativeBoundaryReachability ω h q hw := by
  intro j _hj
  exact leftAlongRawGeodesic_eventually_reachable _ h q hw
    ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩

end DirectedDistances.Recursive
