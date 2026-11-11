module

public import DirectedDistances.PaperProofs.Section4.ThinMapExhaustion
import DirectedDistances.KMSW.InfiniteGeodesicAnyStart
import DirectedDistances.KMSW.AllocatedVertices
import DirectedDistances.KMSW.InfinitePresentPathCutVisit

/- # Interior confinement and geometric side exhaustion

Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

starting off both boundary rays cannot leave the closed side. This is a local
non-crossing assertion about the constructed drawing, not a reachability assumption.
The conditional results below do not discharge this input or Proposition 4.7.
Infinite cut vertices, supplied by the coherent domain, suffice for all other steps. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter Quiver

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining local planar non-crossing obligation: a present edge starting in the
side, away from the seam and exterior boundary vertices, has its entire realized
arc in that side. This proposition is isolated, not asserted to hold. -/
@[expose] noncomputable def ThinMapInteriorArcConfinement (a : ThinMapSide) : Prop :=
  ∀ e : ℕ, EdgePresent w e →
    edgeWest w e ∈ sideVertices w hfin hL htrans hR P a →
    (∀ i : ℕ, edgeWest w e ≠ (P.initial i).1.id) →
    (∀ s : ℕ, edgeWest w e ≠ thinMapBoundaryVertex w hfin hL htrans hR a s) →
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc (e, false)).image ⊆
      thinMapSideRegion w hfin hL htrans hR P a

include hL htrans hR in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every vertex reaches a seam vertex through present edges in the whole graph.
This asserts no side confinement. Infinite cut vertices give arbitrarily late records. -/
theorem vertex_reachable_seam_of_infinite_cutVertices
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (v : ℕ) :
    ∃ i, Reachable (⟨v⟩ : PresentVertex w) (P.initial i).1 := by
  classical
  have halloc := kmsw_vertex_allocated_of_finite_incidence w hfin v
  obtain ⟨N, hN⟩ := allocated_eventually_before_records w hR ⟨v⟩ halloc
  let early : Finset ℕ := (Finset.range N).image (activeInitial w)
  obtain ⟨c, hc, hcearly⟩ := hcuts.exists_notMem_finset early
  obtain ⟨n, hcn, _, hA, hB, _⟩ :=
    mapCutVertex_firstVisit_records w hfin htrans hR hL hc
  have hNn : N ≤ n := by
    by_contra hn
    apply hcearly
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), hcn.symm⟩
  have hr := allocated_reachable_record w n hR hA hB ⟨v⟩ halloc
    (Or.inl (hN n hNn hA))
  obtain ⟨i, hi | hi⟩ :=
    InfinitePresentPath.visits_mapCutVertex w hfin htrans hR hL hc P
  · refine ⟨i, ?_⟩
    have heq : recordVertex w n = (P.initial i).1 := by
      apply congrArg (fun k : ℕ => (⟨k⟩ : PresentVertex w))
      change (kmswStage w n).west (act w n) = (P.initial i).1.id
      rw [← CutConverse.activeInitial_eq, ← hcn]
      exact hi.symm.trans (P.edge_outgoing_at_initial w i).2
    exact heq ▸ hr
  · refine ⟨i + 1, ?_⟩
    have heq : recordVertex w n = (P.initial (i + 1)).1 := by
      apply congrArg (fun k : ℕ => (⟨k⟩ : PresentVertex w))
      change (kmswStage w n).west (act w n) = (P.initial (i + 1)).1.id
      rw [← CutConverse.activeInitial_eq, ← hcn]
      exact hi.symm.trans (P.edge_incoming_at_succ w i).2
    exact heq ▸ hr

private theorem path_side_prefix (a : ThinMapSide)
    (hplanar : ThinMapInteriorArcConfinement w hfin hL htrans hR P a)
    {u z : PresentVertex w} (p : Path u z)
    (hu : u.id ∈ sideVertices w hfin hL htrans hR P a) :
    (∃ s, Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a)
      u.id (thinMapBoundaryVertex w hfin hL htrans hR a s)) ∨
    (∃ i, Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a)
      u.id (P.initial i).1.id) ∨
    (z.id ∈ sideVertices w hfin hL htrans hR P a ∧
      Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a) u.id z.id) := by
  classical
  induction p with
  | nil => exact Or.inr (Or.inr ⟨hu, .refl⟩)
  | @cons y z p e ih =>
    rcases ih with hb | hs | ⟨hy, hp⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hs)
    · by_cases hb : ∃ s, y.id = thinMapBoundaryVertex w hfin hL htrans hR a s
      · obtain ⟨s, hs⟩ := hb
        exact Or.inl ⟨s, hs ▸ hp⟩
      · by_cases hs : ∃ i, y.id = (P.initial i).1.id
        · obtain ⟨i, hi⟩ := hs
          exact Or.inr (Or.inl ⟨i, hi ▸ hp⟩)
        · have he : e.val ∈ sideEdges w hfin hL htrans hR P a := by
            apply hplanar e.val e.property.1
            · exact e.property.2.1.symm ▸ hy
            · intro i hi
              exact hs ⟨i, e.property.2.1.symm.trans hi⟩
            · intro s hi
              exact hb ⟨s, e.property.2.1.symm.trans hi⟩
          have hz := (sideEdges_endpoints w hfin hL htrans hR P a he).2
          refine Or.inr (Or.inr ⟨e.property.2.2 ▸ hz, ?_⟩)
          exact hp.tail ⟨e.val, he, e.property⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Conditional directed confinement, with the local planar obligation displayed explicitly.
A whole-graph path stops at its first seam or exterior-boundary vertex; the seam then
reaches a common cut vertex inside the side. -/
theorem sideVertex_reaches_boundary_of_interiorArcConfinement
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide)
    (hplanar : ThinMapInteriorArcConfinement w hfin hL htrans hR P a)
    (v : ℕ) (hv : v ∈ sideVertices w hfin hL htrans hR P a) :
    ∃ s, Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a)
      v (thinMapBoundaryVertex w hfin hL htrans hR a s) := by
  obtain ⟨i, p⟩ := vertex_reachable_seam_of_infinite_cutVertices
    w hfin hL htrans hR P hcuts v
  obtain ⟨p⟩ := p
  rcases path_side_prefix w hfin hL htrans hR P a hplanar p hv with
    hb | ⟨j, hj⟩ | ⟨_, hi⟩
  · exact hb
  · obtain ⟨s, hs⟩ := seamVertex_mem_sourceAncestorVertices_some
      w hfin hL htrans hR P hcuts a j
    exact ⟨s, hj.trans hs.2⟩
  · obtain ⟨s, hs⟩ := seamVertex_mem_sourceAncestorVertices_some
      w hfin hL htrans hR P hcuts a i
    exact ⟨s, hi.trans hs.2⟩

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Conditional exhaustion of every geometric side vertex by ancestor truncations. -/
theorem sideVertex_mem_sourceAncestorVertices_some_of_interiorArcConfinement
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide)
    (hplanar : ThinMapInteriorArcConfinement w hfin hL htrans hR P a)
    (v : ℕ) (hv : v ∈ sideVertices w hfin hL htrans hR P a) :
    ∃ s, v ∈ sourceAncestorVertices w hfin hL htrans hR P a s := by
  obtain ⟨s, hs⟩ := sideVertex_reaches_boundary_of_interiorArcConfinement
    w hfin hL htrans hR P hcuts a hplanar v hv
  exact ⟨s, hv, hs⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Conditional exhaustion of every geometric side edge, including missing edges.
Monotonicity puts both endpoints at one common truncation level. -/
theorem sideEdge_mem_sourceAncestorEdges_some_of_interiorArcConfinement
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide)
    (hplanar : ThinMapInteriorArcConfinement w hfin hL htrans hR P a)
    (e : ℕ) (he : e ∈ sideEdges w hfin hL htrans hR P a) :
    ∃ s, e ∈ sourceAncestorEdges w hfin hL htrans hR P a s := by
  obtain ⟨hw, ht⟩ := sideEdges_endpoints w hfin hL htrans hR P a he
  obtain ⟨s, hs⟩ := sideVertex_mem_sourceAncestorVertices_some_of_interiorArcConfinement
    w hfin hL htrans hR P hcuts a hplanar (edgeWest w e) hw
  obtain ⟨t, ht⟩ := sideVertex_mem_sourceAncestorVertices_some_of_interiorArcConfinement
    w hfin hL htrans hR P hcuts a hplanar (edgeEast w e) ht
  exact ⟨max s t, he,
    sourceAncestorVertices_mono w hfin hL htrans hR P a (le_max_left s t) hs,
    sourceAncestorVertices_mono w hfin hL htrans hR P a (le_max_right s t) ht⟩

end DirectedDistances.PaperProofs.Section4
