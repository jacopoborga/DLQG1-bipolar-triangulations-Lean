module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import DirectedDistances.PlanarMap.GeneralBipolarBoundary
public import DirectedDistances.PlanarMap.BipolarBoundaryData
public import DirectedDistances.PlanarMap.PlanarPathCutOneSided
public import DirectedDistances.PlanarMap.PlanarPathCutAncestorReroute
public import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility

/-! Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.

Right-half analogue of the seam-rerouting argument for the converse
`cutRRep_ancestors_map_iff` (the converse of `cutRRep_ancestors_map`).  It reuses the
abstract rerouting lemmas of `PlanarPathCutAncestorReroute`. -/

public section

namespace DirectedDistances.PlanarMap

open Relation

section RightHalf

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Every dart based at the image of an off-path right-half vertex is a strictly right dart. -/
theorem pathCutRightHalf_offPath_tail_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v : MapVertex (pathCutRightHalfDirectedMap B P))
    (hv : pathCutRightHalfVertexMap B P v ∉ P.vertices)
    {d : D} (hdTail : dartTailVertex B.map d = pathCutRightHalfVertexMap B P v) :
    d ∈ pathCutRightDarts B P := by
  obtain ⟨e, he⟩ := Quotient.exists_rep v
  change dartTailVertex (pathCutRightHalfDirectedMap B P) e = v at he
  have heTail : dartTailVertex B.map e.1 = pathCutRightHalfVertexMap B P v := by
    calc
      dartTailVertex B.map e.1 = pathCutRightHalfVertexMap B P
          (dartTailVertex (pathCutRightHalfDirectedMap B P) e) :=
        (pathCutRightHalfVertexMap_dartTailVertex B P e).symm
      _ = pathCutRightHalfVertexMap B P v := congrArg _ he
  have heNotSeam : e.1 ∉ pathCutSeamDarts B P := by
    intro hseam
    have hvertex := pathCutSeamDarts_tailVertex_mem B P hseam
    exact hv (by simpa only [heTail] using hvertex)
  have heRight : e.1 ∈ pathCutRightDarts B P := by
    have heHalf := e.2
    change e.1 ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P at heHalf
    rcases heHalf with hright | hseam
    · exact hright
    · exact (heNotSeam hseam).elim
  rcases pathCut_vertex_darts_one_sided B P hv with hleftAll | hrightAll
  · have hleftE := hleftAll e.1 heTail
    have hdisjoint := Set.disjoint_left.mp (pathCut_offSeam_disjoint B P)
    exact (hdisjoint ⟨hleftE, heNotSeam⟩ ⟨heRight, heNotSeam⟩).elim
  · exact hrightAll d hdTail

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
A base step from the image of the right half to a vertex outside the image starts on the
cut path. -/
theorem pathCutRightHalf_leave_mem_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u w : MapVertex B.map} (h : B.map.directedStep u w)
    (hu : u ∈ Set.range (pathCutRightHalfVertexMap B P))
    (hw : w ∉ Set.range (pathCutRightHalfVertexMap B P)) : u ∈ P.vertices := by
  by_contra hup
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨d, _, _, hsource, htarget⟩ := h
  have hdRight := pathCutRightHalf_offPath_tail_mem B P v hup hsource
  let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, Or.inl hdRight⟩
  exact hw ⟨dartHeadVertex (pathCutRightHalfDirectedMap B P) dH,
    (pathCutRightHalfVertexMap_dartHeadVertex B P dH).trans htarget⟩

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
A base step from a vertex outside the image of the right half into the image ends on the
cut path. -/
theorem pathCutRightHalf_enter_mem_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u w : MapVertex B.map} (h : B.map.directedStep u w)
    (hu : u ∉ Set.range (pathCutRightHalfVertexMap B P))
    (hw : w ∈ Set.range (pathCutRightHalfVertexMap B P)) : w ∈ P.vertices := by
  by_contra hwp
  obtain ⟨v, rfl⟩ := hw
  obtain ⟨d, _, _, hsource, htarget⟩ := h
  have hrevTail : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
      pathCutRightHalfVertexMap B P v := by
    simpa only [dartTailVertex, dartHeadVertex] using htarget
  have hrevRight := pathCutRightHalf_offPath_tail_mem B P v hwp hrevTail
  have hdRight : d ∈ pathCutRightHalfDarts B P := by
    have h' := pathCutRightHalf_edgeInv_mem B P
      (Or.inl hrevRight : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P)
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h'
  exact hu ⟨dartTailVertex (pathCutRightHalfDirectedMap B P) ⟨d, hdRight⟩,
    (pathCutRightHalfVertexMap_dartTailVertex B P ⟨d, hdRight⟩).trans hsource⟩

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Every vertex of the cut path lies in the image of the right half. -/
theorem pathCutRightHalf_pathVertex_mem_range
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {v : MapVertex B.map} (hv : v ∈ P.vertices) :
    v ∈ Set.range (pathCutRightHalfVertexMap B P) := by
  by_cases hs : v = B.sink
  · exact ⟨pathCutRightHalfSink B P, (pathCutRightHalfSink_map B P).trans hs.symm⟩
  · obtain ⟨d, _, hdTail, _, _, hdRight, _⟩ :=
      pathCut_vertex_outgoingDart_in_both_closed_halves B P hv hs
    exact ⟨dartTailVertex (pathCutRightHalfDirectedMap B P) ⟨d, hdRight⟩,
      (pathCutRightHalfVertexMap_dartTailVertex B P ⟨d, hdRight⟩).trans hdTail⟩

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
The cut path, indexed by `g i = P.vertices.getD i B.source`, is a directed chain of base
steps inside the image of the right half. -/
theorem pathCutRightHalf_seam_chain
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    ∀ i < n, B.map.directedStep (P.vertices.getD i B.source)
        (P.vertices.getD (i + 1) B.source) ∧
      P.vertices.getD i B.source ∈ Set.range (pathCutRightHalfVertexMap B P) ∧
      P.vertices.getD (i + 1) B.source ∈ Set.range (pathCutRightHalfVertexMap B P) := by
  intro i hi
  have hlen : i < P.darts.length := by rw [P.darts_length]; exact hi
  obtain ⟨hm, ht, h1, h2⟩ := P.edge_step ⟨i, hlen⟩
  have hg : ∀ k (hk : k < P.vertices.length),
      P.vertices.getD k B.source = P.vertices.get ⟨k, hk⟩ := by
    intro k hk
    simp [List.getD_eq_getElem?_getD, hk]
  have hv0 : i < P.vertices.length := by rw [P.vertices_length]; omega
  have hv1 : i + 1 < P.vertices.length := by rw [P.vertices_length]; omega
  rw [hg i hv0, hg (i + 1) hv1]
  exact ⟨⟨P.darts.get ⟨i, hlen⟩, hm, ht, h1.symm, h2.symm⟩,
    pathCutRightHalf_pathVertex_mem_range B P (List.get_mem _ _),
    pathCutRightHalf_pathVertex_mem_range B P (List.get_mem _ _)⟩

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
A base step between images of right-half vertices lifts to a directed path in the half. -/
theorem pathCutRightHalf_reach_of_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {a b : MapVertex (pathCutRightHalfDirectedMap B P)}
    (h : B.map.directedStep (pathCutRightHalfVertexMap B P a)
      (pathCutRightHalfVertexMap B P b)) :
    ReflTransGen (pathCutRightHalfDirectedMap B P).directedStep a b := by
  have lift : ∀ {d : D}, d ∈ pathCutRightHalfDarts B P → B.map.tail d →
      dartTailVertex B.map d = pathCutRightHalfVertexMap B P a →
      dartHeadVertex B.map d = pathCutRightHalfVertexMap B P b →
      ReflTransGen (pathCutRightHalfDirectedMap B P).directedStep a b := by
    intro d hd htail hs ht
    let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, hd⟩
    have h1 : pathCutRightHalfVertexMap B P
        (dartTailVertex (pathCutRightHalfDirectedMap B P) dH) =
          pathCutRightHalfVertexMap B P a := by
      rw [pathCutRightHalfVertexMap_dartTailVertex]; exact hs
    have h2 : pathCutRightHalfVertexMap B P
        (dartHeadVertex (pathCutRightHalfDirectedMap B P) dH) =
          pathCutRightHalfVertexMap B P b := by
      rw [pathCutRightHalfVertexMap_dartHeadVertex]; exact ht
    exact ReflTransGen.single ⟨dH, not_false,
      (pathCutRightHalf_embedding_fields B P).2.2.1 dH |>.mpr htail,
      pathCutRightHalfVertexMap_injective B P h1, pathCutRightHalfVertexMap_injective B P h2⟩
  obtain ⟨d, hmiss, htail, hs, ht⟩ := h
  by_cases ha : pathCutRightHalfVertexMap B P a ∈ P.vertices
  · by_cases hb : pathCutRightHalfVertexMap B P b ∈ P.vertices
    · -- both endpoints on the path: follow the path itself
      obtain ⟨i, hi, hgi⟩ := pathCut_pathVertex_index B P ha
      obtain ⟨j, hj, hgj⟩ := pathCut_pathVertex_index B P hb
      have hchain := pathCutRightHalf_seam_chain B P
      have hbase : ∀ j i, j ≤ i → i ≤ n → ReflTransGen B.map.directedStep
          (P.vertices.getD j B.source) (P.vertices.getD i B.source) := by
        intro j i
        induction i with
        | zero =>
          intro hji _
          obtain rfl : j = 0 := by omega
          exact ReflTransGen.refl
        | succ i ih =>
          intro hji hin
          by_cases hje : j = i + 1
          · rw [hje]
          · exact (ih (by omega) (by omega)).tail (hchain i (by omega)).1
      have hstep : B.map.directedStep (P.vertices.getD i B.source)
          (P.vertices.getD j B.source) := by
        rw [hgi, hgj]; exact ⟨d, hmiss, htail, hs, ht⟩
      have hij : i < j := by
        by_contra hcon
        have hrev := hbase j i (by omega) hi
        have : TransGen B.map.directedStep (P.vertices.getD i B.source)
            (P.vertices.getD i B.source) :=
          TransGen.head' hstep hrev
        exact directedStep_not_transGen_self B _ this
      have key : ∀ k, k ≤ j → i ≤ k → ∀ x : MapVertex (pathCutRightHalfDirectedMap B P),
          pathCutRightHalfVertexMap B P x = P.vertices.getD k B.source →
          ReflTransGen (pathCutRightHalfDirectedMap B P).directedStep a x := by
        intro k
        induction k with
        | zero =>
          intro _ hik x hx
          obtain rfl : i = 0 := by omega
          have : x = a := pathCutRightHalfVertexMap_injective B P (hx.trans hgi)
          rw [this]
        | succ k ih =>
          intro hkj hik x hx
          by_cases hie : i = k + 1
          · have : x = a := pathCutRightHalfVertexMap_injective B P
              (hx.trans (by rw [← hie]; exact hgi))
            rw [this]
          · obtain ⟨hst, hkS, _⟩ := hchain k (by omega)
            obtain ⟨y, hy⟩ := hkS
            refine (ih (by omega) (by omega) y hy).trans ?_
            have hlen : k < P.darts.length := by rw [P.darts_length]; omega
            obtain ⟨hm, hdt, h1, h2⟩ := P.edge_step ⟨k, hlen⟩
            have hg : ∀ m (hm : m < P.vertices.length),
                P.vertices.getD m B.source = P.vertices.get ⟨m, hm⟩ := by
              intro m hm; simp [List.getD_eq_getElem?_getD, hm]
            have hv0 : k < P.vertices.length := by rw [P.vertices_length]; omega
            have hv1 : k + 1 < P.vertices.length := by rw [P.vertices_length]; omega
            have hdh := pathCutRightHalf_path_mem B P
              (List.get_mem P.darts ⟨k, hlen⟩)
            let dH : {d : D // d ∈ pathCutRightHalfDarts B P} :=
              ⟨P.darts.get ⟨k, hlen⟩, hdh⟩
            have e1 : pathCutRightHalfVertexMap B P
                (dartTailVertex (pathCutRightHalfDirectedMap B P) dH) =
                  pathCutRightHalfVertexMap B P y := by
              rw [pathCutRightHalfVertexMap_dartTailVertex, hy, hg k hv0]
              exact h1.symm
            have e2 : pathCutRightHalfVertexMap B P
                (dartHeadVertex (pathCutRightHalfDirectedMap B P) dH) =
                  pathCutRightHalfVertexMap B P x := by
              rw [pathCutRightHalfVertexMap_dartHeadVertex, hx, hg (k + 1) hv1]
              exact h2.symm
            exact ReflTransGen.single ⟨dH, not_false,
              (pathCutRightHalf_embedding_fields B P).2.2.1 dH |>.mpr hdt,
              pathCutRightHalfVertexMap_injective B P e1,
              pathCutRightHalfVertexMap_injective B P e2⟩
      exact key j le_rfl hij.le b hgj.symm
    · -- head off the path: the reversed dart is a right dart
      have hrevTail : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
          pathCutRightHalfVertexMap B P b := by
        simpa only [dartTailVertex, dartHeadVertex] using ht
      have hrevRight := pathCutRightHalf_offPath_tail_mem B P b hb hrevTail
      have hdRight : d ∈ pathCutRightHalfDarts B P := by
        have h' := pathCutRightHalf_edgeInv_mem B P
          (Or.inl hrevRight : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P)
        simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h'
      exact lift hdRight htail hs ht
  · exact lift (Or.inl (pathCutRightHalf_offPath_tail_mem B P a ha hs)) htail hs ht

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Ambient directed reachability between images of right-half vertices is exactly directed
reachability inside the right half. -/
theorem pathCutRightHalf_reach_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v t : MapVertex (pathCutRightHalfDirectedMap B P)) :
    ReflTransGen (pathCutRightHalfDirectedMap B P).directedStep v t ↔
      ReflTransGen B.map.directedStep (pathCutRightHalfVertexMap B P v)
        (pathCutRightHalfVertexMap B P t) := by
  constructor
  · intro hi
    apply ReflTransGen.lift (pathCutRightHalfVertexMap B P) _ _ _ hi
    intro u z h
    obtain ⟨d, _, ht, hu, hz⟩ := h
    refine ⟨d.1, B.noMissingDarts _,
      ((pathCutRightHalf_embedding_fields B P).2.2.1 d).mp ht, ?_, ?_⟩
    · exact (pathCutRightHalfVertexMap_dartTailVertex B P d).symm.trans
        (congrArg (pathCutRightHalfVertexMap B P) hu)
    · exact (pathCutRightHalfVertexMap_dartHeadVertex B P d).symm.trans
        (congrArg (pathCutRightHalfVertexMap B P) hz)
  · intro h
    have hre := (reach_in_of_reach_seam B.map.directedStep
      (Set.range (pathCutRightHalfVertexMap B P)) (fun i => P.vertices.getD i B.source) n
      (directedStep_not_transGen_self B) (pathCutRightHalf_seam_chain B P)
      (fun u w hs hu hw => pathCut_pathVertex_index B P
        (pathCutRightHalf_leave_mem_path B P hs hu hw))
      (fun u w hs hu hw => pathCut_pathVertex_index B P
        (pathCutRightHalf_enter_mem_path B P hs hu hw))
      ⟨t, rfl⟩ h).1 ⟨v, rfl⟩
    have key : ∀ x y, ReflTransGen (fun a b => B.map.directedStep a b ∧
        a ∈ Set.range (pathCutRightHalfVertexMap B P) ∧
        b ∈ Set.range (pathCutRightHalfVertexMap B P)) x y →
        ∀ x' y', pathCutRightHalfVertexMap B P x' = x →
        pathCutRightHalfVertexMap B P y' = y →
        ReflTransGen (pathCutRightHalfDirectedMap B P).directedStep x' y' := by
      intro x y hxy
      induction hxy with
      | refl =>
        intro x' y' hx hy
        have : x' = y' := pathCutRightHalfVertexMap_injective B P (hx.trans hy.symm)
        rw [this]
      | tail _ hst ih =>
        intro x' y' hx hy
        obtain ⟨hs, ⟨w', hw'⟩, _⟩ := hst
        refine (ih x' w' hx hw').trans (pathCutRightHalf_reach_of_step B P ?_)
        rw [hw', hy]
        exact hs
    exact key _ _ hre v t rfl rfl

end RightHalf

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Ancestor reachability of the relabelled right cut is exactly ancestor reachability of
its image in the original representative. -/
theorem cutRRep_ancestors_map_iff {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (z v : MapVertex (cutRRep R hR).2.B.map) :
    z ∈ ancestors (presentation (cutRRep R hR).2 .right v) ↔
      cutRRepVertexMap R hR z ∈
        ancestors (presentation R .right (cutRRepVertexMap R hR v)) := by
  refine ⟨cutRRep_ancestors_map R hR z v, fun h => ?_⟩
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have h1 : Relation.ReflTransGen R.B.map.directedStep
      (pathCutRightHalfVertexMap R.B P (I.vertexEquiv z))
      (pathCutRightHalfVertexMap R.B P (I.vertexEquiv v)) := h
  have h2 := (pathCutRightHalf_reach_iff R.B P _ _).mpr h1
  exact baseIso_reach_reflect I h2

end DirectedDistances.PaperProofs.Section4
