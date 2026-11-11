module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfArcConfinement
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The remaining geometric obligation concerns only forward half darts departing
from a seam or exterior-boundary vertex. Directed reachability from the half's
source propagates confinement through all other vertices. The local departure
obligation is isolated below and is not asserted to hold. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver Set
open DirectedDistances.Paper.Section4
open scoped Classical Topology

section Half

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The prefix equation fixes the permanent source ID of each half. -/
theorem ancestorPos_source_id_of_prefix
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) :
    ancestorPosVertexId w t R hR I a (ancestorPosHalfRep R hR a).B.source = 0 := by
  let Q := selectedGeodesicOfLen R.B x hR
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    have hi : (⟨0, by rw [Q.vertices_length]; omega⟩ : Fin Q.vertices.length) =
        ⟨m, by rw [Q.vertices_length]; omega⟩ := Fin.ext hz.symm
    exact bipolar_source_ne_sink R.B
      (Q.start_vertex.symm.trans ((congrArg Q.vertices.get hi).trans Q.end_vertex))
  let j : Fin Q.darts.length := ⟨0, by rw [Q.darts_length]; exact hm⟩
  let d := Q.darts.get j
  have hd : Q.darts[0]? = some d := List.getElem?_eq_getElem j.isLt
  have hh := congrArg (fun ds => ds[0]?) hp
  rw [List.getElem?_map, List.getElem?_map, hd, Option.map_some, Option.map_some,
    List.getElem?_ofFn, dite_eq_left hm] at hh
  have hid : (I.toEquiv d).1.val = P.edge 0 := Option.some.inj hh
  have hs : dartTailVertex R.B.map d = R.B.source :=
    (Q.edge_step j).2.2.1.symm.trans Q.start_vertex
  change (stageMapVertex w t
    (cutMapIsoVertexEquiv I (ancestorPosVertexMap R hR a _))).id = 0
  rw [ancestorPos_source_map, ← hs, (cutMapIsoVertexEquiv_endpoints I d).1,
    stageMapVertex_tail]
  have hf := directedPath_stageIso_darts_forward I Q d (List.get_mem _ _)
  change (if (I.toEquiv d).2 then _ else _) = 0
  rw [hf]
  exact (edge_endpoints_eq w (I.toEquiv d).1.isLt).1.trans
    (hid ▸ P.first_edge_outgoing.2)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The off-prefix, nonboundary seed avoids the complete frontier of its side. -/
theorem ancestorPos_arcSeed_not_mem_frontier
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hoff : ∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val)
    (hb : ∀ i : ℕ, (ancestorPosDartId w t R hR I a d).1 ≠
      (thinMapBoundaryDart w hfin hL htrans hRneg a i).1) :
    thinMapArcSeed w hfin (ancestorPosDartId w t R hR I a d).1 ∉
      frontier (thinMapSideRegion w hfin hL htrans hRneg P a) := by
  intro hz
  have hi := thinMapArcSeed_mem_interior w hfin (ancestorPosDartId w t R hR I a d).1
  rcases thinMapSideRegion_frontier_subset_traces w hfin hL htrans hRneg P a hz
    with hs | hboundary
  · exact Set.disjoint_left.mp
      (ancestorPos_offPrefix_interior_disjoint_seamTrace
        w t R hR I a hfin P hp d hoff) hi hs
  · have hdart : thinMapBoundaryDart w hfin hL htrans hRneg a =
        (fun i => ((thinMapBoundaryDart w hfin hL htrans hRneg a i).1, false)) := by
      funext i
      cases a <;> rfl
    rw [hdart] at hboundary
    exact Set.disjoint_left.mp (thinMapArc_interior_disjoint_trace w hfin _ _ hb)
      hi hboundary

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Only forward darts departing from a separator vertex remain to be identified.
The edge itself is neither a prefix edge nor an exterior-boundary edge.
This local obligation is isolated and is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfBoundaryLaunchArcSeeds
    (a : ThinMapSide) : Prop :=
  ∀ d : Fin (ancestorPosHalfRep R hR a).dartCount,
    (ancestorPosHalfRep R hR a).B.map.tail d →
    (∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) →
    (∀ i : ℕ, (ancestorPosDartId w t R hR I a d).1 ≠
      (thinMapBoundaryDart w hfin hL htrans hRneg a i).1) →
    ((∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      (P.initial i).1.id) ∨
      ∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
        thinMapBoundaryVertex w hfin hL htrans hRneg a i) →
    thinMapArcSeed w hfin (ancestorPosDartId w t R hR I a d).1 ∈
      thinMapSideRegion w hfin hL htrans hRneg P a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A forward half edge starting in the side stays in the side, conditional only
on the separator-vertex departure obligation. -/
theorem ancestorPos_forward_arc_subset_of_boundaryLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide)
    (hlaunch : AncestorPosHalfBoundaryLaunchArcSeeds
      w hfin hL htrans hRneg P t R hR I a)
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (ht : (ancestorPosHalfRep R hR a).B.map.tail d)
    (hv : edgeWest w (ancestorPosDartId w t R hR I a d).1 ∈
      sideVertices w hfin hL htrans hRneg P a) :
    (ancestorPosDartId w t R hR I a d).1 ∈
      sideEdges w hfin hL htrans hRneg P a := by
  by_cases hs : ∃ i : Fin m, (ancestorPosDartId w t R hR I a d).1 = P.edge i.val
  · obtain ⟨i, hi⟩ := hs
    rw [hi]
    exact seamEdge_mem_sideEdges w hfin hL htrans hRneg P a i.val
  · have hoff := fun i hi => hs ⟨i, hi⟩
    by_cases hb : ∃ i : ℕ, (ancestorPosDartId w t R hR I a d).1 =
        (thinMapBoundaryDart w hfin hL htrans hRneg a i).1
    · obtain ⟨i, hi⟩ := hb
      rw [hi]
      exact (thinMapBoundaryDart_mem_sourceAncestorEdges
        w hfin hL htrans hRneg P a i).1
    · have hboundary := fun i hi => hb ⟨i, hi⟩
      by_cases hstart :
          (∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
            (P.initial i).1.id) ∨
          ∃ i : ℕ, edgeWest w (ancestorPosDartId w t R hR I a d).1 =
            thinMapBoundaryVertex w hfin hL htrans hRneg a i
      · exact (thinMapArc_subset_sideRegion_iff_seed w hfin hL htrans hRneg P a _
          (ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff)).mpr
            (hlaunch d ht hoff hboundary hstart)
      · exact thinMapInteriorArcConfinement w hfin hL htrans hRneg P a _
          (ancestorPos_ids_oriented w t R hR I a d |>.mp ht).1 hv
          (fun i hi => hstart (Or.inl ⟨i, hi⟩))
          (fun i hi => hstart (Or.inr ⟨i, hi⟩))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A finite directed dart path gives directed reachability of its endpoints. -/
private theorem arcSeed_path_reachable
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

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Source reachability propagates side membership through every half vertex.
Only departures at separator vertices use the isolated local obligation. -/
theorem ancestorPos_vertex_mem_side_of_boundaryLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide)
    (hlaunch : AncestorPosHalfBoundaryLaunchArcSeeds
      w hfin hL htrans hRneg P t R hR I a)
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map) :
    ancestorPosVertexId w t R hR I a v ∈
      sideVertices w hfin hL htrans hRneg P a := by
  let B := (ancestorPosHalfRep R hR a).B
  let F := ancestorPosVertexId w t R hR I a
  obtain ⟨j, Q, _⟩ := exists_simple_source_pathBase B v
  have hreach := arcSeed_path_reachable Q
  clear Q
  have hroot : F B.source ∈ sideVertices w hfin hL htrans hRneg P a := by
    change ancestorPosVertexId w t R hR I a
      (ancestorPosHalfRep R hR a).B.source ∈ _
    rw [ancestorPos_source_id_of_prefix w P t R hR I hp a]
    exact source_mem_sideVertices w hfin hL htrans hRneg P a
  induction hreach with
  | refl => exact hroot
  | @tail b c _ hbc ih =>
    obtain ⟨d, _, ht, hb, hc⟩ := hbc
    have hor := (ancestorPos_ids_oriented w t R hR I a d).mp ht
    have he := ancestorPos_ids_endpoints w t R hR I a d
    simp only [hor.2, Bool.false_eq_true, ite_false] at he
    have hv : edgeWest w (ancestorPosDartId w t R hR I a d).1 ∈
        sideVertices w hfin hL htrans hRneg P a := by
      rw [he.1.symm.trans (congrArg F hb)]
      exact ih
    have hedge := ancestorPos_forward_arc_subset_of_boundaryLaunch
      w hfin hL htrans hRneg P t R hR I hp a hlaunch d ht hv
    have hv' := (sideEdges_endpoints w hfin hL htrans hRneg P a hedge).2
    change F c ∈ _
    exact (he.2.symm.trans (congrArg F hc)) ▸ hv'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The separator-vertex departure obligation confines every half edge, including
the edge represented by a reversed dart. No geometric half identification is assumed. -/
theorem ancestorPos_arc_subset_of_boundaryLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide)
    (hlaunch : AncestorPosHalfBoundaryLaunchArcSeeds
      w hfin hL htrans hRneg P t R hR I a)
    (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    (ancestorPosDartId w t R hR I a d).1 ∈
      sideEdges w hfin hL htrans hRneg P a := by
  let B := (ancestorPosHalfRep R hR a).B
  have hforward (c : Fin (ancestorPosHalfRep R hR a).dartCount) (ht : B.map.tail c) :
      (ancestorPosDartId w t R hR I a c).1 ∈
        sideEdges w hfin hL htrans hRneg P a := by
    apply ancestorPos_forward_arc_subset_of_boundaryLaunch
      w hfin hL htrans hRneg P t R hR I hp a hlaunch c ht
    have he := (ancestorPos_ids_endpoints w t R hR I a c).1
    simp only [(ancestorPos_ids_oriented w t R hR I a c |>.mp ht).2,
      Bool.false_eq_true, ite_false] at he
    rw [← he]
    exact ancestorPos_vertex_mem_side_of_boundaryLaunch
      w hfin hL htrans hRneg P t R hR I hp a hlaunch _
  by_cases ht : B.map.tail d
  · exact hforward d ht
  · have hflip : B.map.tail (B.map.edgeInv d) := by
      by_contra hn
      exact ht ((B.map.tail_iff d (B.noMissingDarts d)).mpr hn)
    have hh := hforward (B.map.edgeInv d) hflip
    exact (congrArg Prod.fst (ancestorPos_ids_opposite w t R hR I a d)) ▸ hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All off-prefix arc seeds follow from the local separator-vertex obligation. -/
theorem ancestorPos_arcSeeds_of_boundaryLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide)
    (hlaunch : AncestorPosHalfBoundaryLaunchArcSeeds
      w hfin hL htrans hRneg P t R hR I a) :
    AncestorPosHalfOffPrefixArcSeedIdentification
      w hfin hL htrans hRneg P t R hR I a := by
  intro d _ _
  exact ancestorPos_arc_subset_of_boundaryLaunch
    w hfin hL htrans hRneg P t R hR I hp a hlaunch d
      (thinMapArcSeed_mem_interior w hfin _).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The local separator-vertex obligation is equivalent to the full seed obligation;
the reverse direction is merely restriction to forward separator departures. -/
theorem ancestorPos_arcSeeds_iff_boundaryLaunch
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) :
    AncestorPosHalfOffPrefixArcSeedIdentification
        w hfin hL htrans hRneg P t R hR I a ↔
      AncestorPosHalfBoundaryLaunchArcSeeds w hfin hL htrans hRneg P t R hR I a := by
  constructor
  · intro h d _ hoff hb _
    exact h d hoff hb
  · exact ancestorPos_arcSeeds_of_boundaryLaunch
      w hfin hL htrans hRneg P t R hR I hp a

end Half

section Source

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining local departures, specialized to represented selected prefixes. -/
@[expose] noncomputable def SourceAncestorCutBoundaryLaunchArcSeeds : Prop :=
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
      ∀ a, AncestorPosHalfBoundaryLaunchArcSeeds
        w hfin hL htrans hRneg P t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The source seed obligation is equivalent to its separator-departure restriction.
This equivalence does not prove either geometric obligation. -/
theorem sourceAncestorCut_arcSeeds_iff_boundaryLaunch :
    SourceAncestorCutPositiveArcSeeds x T hT ↔
      SourceAncestorCutBoundaryLaunchArcSeeds x T hT := by
  constructor
  · intro h q k
    dsimp only
    intro ℓ r n m R hR I hp a
    exact (ancestorPos_arcSeeds_iff_boundaryLaunch
      _ _ _ _ _ _ _ R hR I hp a).mp (h q k R hR I hp a)
  · intro h q k
    dsimp only
    intro ℓ r n m R hR I hp a
    exact (ancestorPos_arcSeeds_iff_boundaryLaunch
      _ _ _ _ _ _ _ R hR I hp a).mpr (h q k R hR I hp a)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Conditional seed identification for both halves at every selected prefix. -/
theorem sourceAncestorCutPositiveArcSeeds_of_boundaryLaunch
    (h : SourceAncestorCutBoundaryLaunchArcSeeds x T hT) :
    SourceAncestorCutPositiveArcSeeds x T hT :=
  (sourceAncestorCut_arcSeeds_iff_boundaryLaunch x T hT).mpr h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All source side-range assembly follows from the local separator departures. -/
theorem sourceAncestorCutPositiveSideRangeIdentification_of_boundaryLaunch
    (h : SourceAncestorCutBoundaryLaunchArcSeeds x T hT) :
    SourceAncestorCutPositiveSideRangeIdentification x T hT :=
  sourceAncestorCutPositiveSideRangeIdentification_of_arcSeeds x T hT
    (sourceAncestorCutPositiveArcSeeds_of_boundaryLaunch x T hT h)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Realization is conditional solely on the displayed local departure obligation.
This is not an unconditional realization or a proof of Proposition 4.7. -/
theorem sourceAncestorCutRealization_of_boundaryLaunch
    (h : SourceAncestorCutBoundaryLaunchArcSeeds x T hT) :
    SourceAncestorCutRealization x T hT :=
  sourceAncestorCutRealization_of_arcSeeds x T hT
    (sourceAncestorCutPositiveArcSeeds_of_boundaryLaunch x T hT h)

end Source

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical renewal specialization retains exactly the local geometric obligation.
No unconditional source realization is asserted. -/
theorem sourceAncestorCutRealization_renewal_of_boundaryLaunch (x : XDP)
    (h : SourceAncestorCutBoundaryLaunchArcSeeds x renewalTime
      renewalTime_positiveSuccessTime) :
    SourceAncestorCutRealization x renewalTime renewalTime_positiveSuccessTime :=
  sourceAncestorCutRealization_of_boundaryLaunch x renewalTime
    renewalTime_positiveSuccessTime h

end DirectedDistances.PaperProofs.Section4
