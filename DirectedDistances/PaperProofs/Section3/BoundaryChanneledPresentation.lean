/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled
public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationTransport2
public import DirectedDistances.PlanarMap.FiniteBoundaryPresentationTransport3
public import DirectedDistances.Paper.Section3.BoundaryChanneled
public import DirectedDistances.PaperProofs.SourceResults.BoundaryChanneledDefinition

/-! # Finite boundary-channeled presentations

finite carrier supplies simple source-to-sink left and right paths and an
outer-face word. This file records the presentation induced by a PL drawing
whose dart, flip, rotation, and vertex carriers are those of that finite map.
It does not identify the PL external face with the combinatorial outer face. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

universe u

/-- Helper toward Definition 3.2: the dart-labelled PL realization of a
finite KMSW boundary representative, with its prescribed flip, rotation, and
rotation-class vertex maps. -/
abbrev BoundaryChanneledPLDrawing {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) :=
  PLDrawing (Fin R.dartCount) (MapVertex R.B.map)
    R.B.map.toCombinatorialMap.edgeInv R.B.map.toCombinatorialMap.rot
    (dartTailVertex R.B.map)

/-- Helper toward Definition 3.2: turn a compatible dart drawing of a
finite boundary representative into its directed plane-map carrier. Every
geometric edge is present, and the stored dart representative selects the
orientation supplied by the finite map. -/
@[expose] def boundaryChanneledPlaneMap {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    DirectedPlaneMapWithMissing (MapVertex R.B.map) G.GeometricEdge where
  toPlaneMapWithMissing :=
    { toPlaneGraphDrawing := G.toPlaneGraphDrawing
      missing := fun _ => False
      missing_on_external := by
        intro e he
        exact False.elim he }
  forward := fun e => by
    classical
    exact decide (R.B.map.tail e.1.out)

/-- Helper toward Definition 3.2: every geometric edge in the constructed
finite boundary-channeled plane map is non-missing. -/
theorem boundaryChanneledPlaneMap_noMissing {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (e : G.GeometricEdge) :
    ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing e := by
  simp [boundaryChanneledPlaneMap]

/-- Helper toward Definition 3.2: a finite path index selects its dart using
the path's stored length equality. -/
@[expose] def boundaryPathDart {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k)
    (i : Fin k) : D :=
  P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.is_lt⟩

/-- Helper toward Definition 3.2: darts on a simple directed path are
pairwise distinct, since equal darts have equal initial vertices. -/
theorem boundaryPathDartsNodup {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hi := P.edge_step i
  have hj := P.edge_step j
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hjLt : j.val < k := by simpa [P.darts_length] using j.isLt
  have hv : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
      P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := by
    calc
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex M (P.darts.get i) := hi.2.2.1
      _ = dartTailVertex M (P.darts.get j) := congrArg (dartTailVertex M) hij
      _ = P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := hj.2.2.1.symm
  have hidx : (⟨i.val, by rw [P.vertices_length]; omega⟩ : Fin P.vertices.length) =
      ⟨j.val, by rw [P.vertices_length]; omega⟩ :=
    P.vertices_nodup.get_inj_iff.mp hv
  have hval : i.val = j.val := congrArg (fun x : Fin P.vertices.length => x.val) hidx
  exact Fin.ext hval

/-- Helper toward Definition 3.2: encode a left-boundary path dart by its
geometric edge and the traversal bit agreeing with its directed orientation. -/
@[expose] def boundaryChanneledLeftDart {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin ℓ) :
    G.GeometricEdge × Bool := by
  let M := boundaryChanneledPlaneMap R G
  let e : G.GeometricEdge := Quotient.mk G.edgeSetoid
    (boundaryPathDart R.B.leftPath i)
  exact (e, M.forward ⟨e, by simp [M, boundaryChanneledPlaneMap]⟩)

/-- Helper toward Definition 3.2: the UL encoded dart starts at the initial
vertex of the corresponding directed boundary path edge. -/
theorem boundaryChanneledLeftDart_initial {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin ℓ) :
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G i) =
        dartTailVertex R.B.map (boundaryPathDart R.B.leftPath i) := by
  let d := boundaryPathDart R.B.leftPath i
  let e : G.GeometricEdge := Quotient.mk G.edgeSetoid d
  have htail := (R.B.leftPath.edge_step
    ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.1
  have htail' : R.B.map.tail d := by
    simpa [d, boundaryPathDart] using htail
  rcases G.geometricEdge_out_mk d with hout | hout
  · rw [boundaryDartInitial_eq]
    simp [boundaryChanneledLeftDart, boundaryChanneledPlaneMap,
      PLDrawing.toPlaneGraphDrawing, d, e, hout, htail']
  · have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail
    rw [boundaryDartInitial_eq]
    simp [boundaryChanneledLeftDart, boundaryChanneledPlaneMap, d, e,
      PLDrawing.toPlaneGraphDrawing, hout, htail', hnot,
      R.B.map.toCombinatorialMap.edgeInv_invol]

/-- Helper toward Definition 3.2: the UL encoded dart ends at the terminal
vertex of the corresponding directed boundary path edge. -/
theorem boundaryChanneledLeftDart_terminal {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin ℓ) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G i) =
        dartHeadVertex R.B.map (boundaryPathDart R.B.leftPath i) := by
  let d := boundaryPathDart R.B.leftPath i
  have htail := (R.B.leftPath.edge_step
    ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.1
  have htail' : R.B.map.tail d := by simpa [d, boundaryPathDart] using htail
  rcases G.geometricEdge_out_mk d with hout | hout
  · rw [boundaryDartTerminal_eq]
    simp [boundaryChanneledLeftDart, boundaryChanneledPlaneMap,
      PLDrawing.toPlaneGraphDrawing, d, hout, htail']
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) =
      dartHeadVertex R.B.map d
    rfl
  · have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail'
    rw [boundaryDartTerminal_eq]
    simp [boundaryChanneledLeftDart, boundaryChanneledPlaneMap, d,
      PLDrawing.toPlaneGraphDrawing, hout, hnot,
      R.B.map.toCombinatorialMap.edgeInv_invol]
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) =
      dartHeadVertex R.B.map d
    rfl

/-- Helper toward Definition 3.2: encode a right-boundary path dart in
external-face traversal order, opposite its directed orientation. -/
@[expose] def boundaryChanneledRightDart {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin r) :
    G.GeometricEdge × Bool := by
  let M := boundaryChanneledPlaneMap R G
  let e : G.GeometricEdge := Quotient.mk G.edgeSetoid
    (R.B.rightPath.darts.reverse.get ⟨i.val, by
      rw [List.length_reverse, R.B.rightPath.darts_length]
      exact i.is_lt⟩)
  exact (e, !(M.forward ⟨e, by simp [M, boundaryChanneledPlaneMap]⟩))

/-- Helper toward Definition 3.2: an empty boundary side has its marked
zero-edge endpoint as both optional endpoint labels. -/
@[expose] def emptyBoundarySide {V E : Type*} (v : V) :
    InfiniteBoundarySide V E :=
  { Index := Empty
    darts := ⟨Empty.elim, by intro i j h; exact Empty.elim i⟩
    next := Empty.elim
    initialVertex? := some v
    terminalVertex? := some v }

/-- Helper toward Definition 3.2: an empty zero-edge side with matching
endpoint marks satisfies the side endpoint-label clauses. -/
theorem emptyBoundarySide_endpointLabels {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (v : V) :
    BoundarySideEndpointLabels M (emptyBoundarySide (E := E) v) := by
  simp [BoundarySideEndpointLabels, emptyBoundarySide]





@[expose] def boundaryChanneledPresentationWithJunctions {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    BoundaryPresentationWithJunctions (boundaryChanneledPlaneMap R G) := by
  let M := boundaryChanneledPlaneMap R G
  refine ⟨{
    upperLeft := {
      Index := Fin ℓ
      darts := ⟨boundaryChanneledLeftDart R G, ?_⟩
      next := fun i => if h : i.val + 1 < ℓ then some ⟨i.val + 1, h⟩ else none
      initialVertex? := some R.B.source
      terminalVertex? := some R.B.sink }
    upperRight := emptyBoundarySide R.B.sink
    lowerRight := {
      Index := Fin r
      darts := ⟨boundaryChanneledRightDart R G, ?_⟩
      next := fun i => if h : i.val + 1 < r then some ⟨i.val + 1, h⟩ else none
      initialVertex? := some R.B.sink
      terminalVertex? := some R.B.source }
    lowerLeft := emptyBoundarySide R.B.source },
    some ⟨R.B.source, R.B.sink, R.B.sink, R.B.source⟩⟩
  · intro i j hij
    have he := congrArg Prod.fst hij
    dsimp [boundaryChanneledLeftDart] at he
    apply Fin.ext
    have hq := Quotient.exact he
    rcases hq with h | h
    · dsimp [boundaryPathDart] at h
      have hidx := (boundaryPathDartsNodup R.B.leftPath).get_inj_iff.mp h
      exact congrArg (fun x : Fin R.B.leftPath.darts.length => x.val) hidx
    · have htaili := (R.B.leftPath.edge_step
        ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.1
      have htailj := (R.B.leftPath.edge_step
        ⟨j.val, by rw [R.B.leftPath.darts_length]; exact j.is_lt⟩).2.1
      have hnot := (R.B.map.tail_iff (boundaryPathDart R.B.leftPath j)
        (R.B.noMissingDarts _)).mp htailj
      exact (hnot (h ▸ htaili)).elim
  · intro i j hij
    have he := congrArg Prod.fst hij
    dsimp [boundaryChanneledRightDart] at he
    apply Fin.ext
    have hq := Quotient.exact he
    have hnd : R.B.rightPath.darts.reverse.Nodup :=
      List.nodup_reverse.mpr (boundaryPathDartsNodup R.B.rightPath)
    rcases hq with h | h
    · have hget : R.B.rightPath.darts.reverse.get
        ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.is_lt⟩ =
        R.B.rightPath.darts.reverse.get
        ⟨j.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact j.is_lt⟩ := h
      have hidx := hnd.get_inj_iff.mp hget
      exact congrArg (fun x : Fin R.B.rightPath.darts.reverse.length => x.val) hidx
    · have hmemi : R.B.rightPath.darts.reverse.get
        ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.is_lt⟩ ∈
        R.B.rightPath.darts.reverse := List.get_mem _ _
      have hmemj : R.B.rightPath.darts.reverse.get
        ⟨j.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact j.is_lt⟩ ∈
        R.B.rightPath.darts.reverse := List.get_mem _ _
      let di := R.B.rightPath.darts.reverse.get
        ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.is_lt⟩
      let dj := R.B.rightPath.darts.reverse.get
        ⟨j.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact j.is_lt⟩
      have hmemi' : di ∈ R.B.rightPath.darts := by
        exact List.mem_reverse.mp (by simpa [di] using hmemi)
      have hmemj' : dj ∈ R.B.rightPath.darts := by
        exact List.mem_reverse.mp (by simpa [dj] using hmemj)
      have htaili : R.B.map.tail di := by
        rcases List.mem_iff_get.mp hmemi' with ⟨k, hk⟩
        exact hk ▸ (R.B.rightPath.edge_step k).2.1
      have htailj : R.B.map.tail dj := by
        rcases List.mem_iff_get.mp hmemj' with ⟨k, hk⟩
        exact hk ▸ (R.B.rightPath.edge_step k).2.1
      have hnot := (R.B.map.tail_iff dj (R.B.noMissingDarts _)).mp htailj
      have hdi : di = R.B.map.toCombinatorialMap.edgeInv dj := by
        simpa [di, dj] using h
      have htailFlip : R.B.map.tail (R.B.map.toCombinatorialMap.edgeInv dj) := by
        rw [← hdi]
        exact htaili
      exact (hnot htailFlip).elim

/-- Helper toward Definition 3.2: the constructed presentation's eight
endpoint labels agree with its retained source/sink junctions. -/
theorem boundaryChanneledPresentation_junctionLabels {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    FiniteBoundaryJunctionLabels6
      (boundaryChanneledPresentationWithJunctions R G).presentation
      ⟨R.B.source, R.B.sink, R.B.sink, R.B.source⟩ := by
  simp [FiniteBoundaryJunctionLabels6, boundaryChanneledPresentationWithJunctions,
    emptyBoundarySide]

/-- Helper toward Definition 3.2: the supplied-junction clause of the finite
v7 predicate holds for the constructed presentation. -/
theorem boundaryChanneledPresentation_suppliedJunctionLabels {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    SuppliedFiniteJunctionLabels6 (boundaryChanneledPresentationWithJunctions R G) := by
  simp [SuppliedFiniteJunctionLabels6, FiniteBoundaryJunctionLabels6,
    boundaryChanneledPresentationWithJunctions, emptyBoundarySide]

/-- Helper toward Definition 3.2: the two missing runs of a finite
boundary-channeled triangulation are empty and satisfy their missingness
clauses. -/
theorem boundaryChanneledPresentation_missingRuns {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    UROkInf (boundaryChanneledPresentationWithJunctions R G).presentation ∧
      LLOkInf (boundaryChanneledPresentationWithJunctions R G).presentation := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hur : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    exact inferInstance
  have hll : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    exact inferInstance
  exact ⟨UROkInf_of_isEmpty P, LLOkInf_of_isEmpty P⟩

/-- Helper toward Definition 3.2: the empty UR and LL sides in the finite
boundary-channeled presentation satisfy their endpoint-label clauses. -/
theorem boundaryChanneledPresentation_emptySideEndpointLabels {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.upperRight ∧
      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.lowerLeft := by
  constructor <;>
    simpa [boundaryChanneledPresentationWithJunctions, emptyBoundarySide] using
      emptyBoundarySide_endpointLabels (boundaryChanneledPlaneMap R G) _
































end DirectedDistances.PaperProofs.Section3

end
end
