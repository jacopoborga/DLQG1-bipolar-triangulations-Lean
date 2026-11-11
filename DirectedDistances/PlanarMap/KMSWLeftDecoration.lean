/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWMapChanneled
public import DirectedDistances.PlanarMap.BdyReverseSizedSlices

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Boundary edge-orbit count on the `(ℓ,1)` base carrier, using the strong
carrier's boundary-edge injection. Its image is precisely the edge orbits
containing left- or right-path darts. Helper toward `lem-kmsw-left` -/
noncomputable def leftEndpointBoundaryEdgeCountBase {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) : ℕ := by
  classical
  exact Fintype.card {e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
    e ∈ Set.range (boundaryEdgeInjection (toStrongLeftEndpoint B hℓ))}

/-- The left and right boundary paths account for exactly `ℓ + 1` edge
orbits on this endpoint carrier. The right path has one edge, and its orbit
is disjoint from the `ℓ` distinct left-path edge orbits. Helper toward
not adopted; not the paper result. -/
theorem leftEndpointBoundaryEdgeCountBase_eq {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) :
    leftEndpointBoundaryEdgeCountBase B hℓ = ℓ + 1 := by
  classical
  unfold leftEndpointBoundaryEdgeCountBase
  let C := toStrongLeftEndpoint B hℓ
  have hinj := boundaryEdgeInjection_injective C
  calc
    Fintype.card {e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      e ∈ Set.range (boundaryEdgeInjection C)} =
        Fintype.card (Fin C.leftPath.darts.length ⊕ Fin C.rightPath.darts.length) :=
      Fintype.card_congr (Equiv.ofInjective (boundaryEdgeInjection C) hinj).symm
    _ = ℓ + 1 := by simp [C.leftPath.darts_length, C.rightPath.darts_length]

/-- The non-boundary edge count on the `(ℓ,1)` base carrier, defined by the
existing `innerEdgeCount` on its strong endpoint carrier. Helper toward -/
@[expose] noncomputable def leftEndpointNonBoundaryEdgeCountBase {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) : ℕ :=
  innerEdgeCount (toStrongLeftEndpoint B hℓ)

/-- On this base carrier, the non-boundary edge count is total edge count
minus the `ℓ + 1` boundary edge orbits. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem leftEndpointNonBoundaryEdgeCountBase_eq {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (hℓ : 2 ≤ ℓ) :
    leftEndpointNonBoundaryEdgeCountBase B hℓ =
      B.map.toCombinatorialMap.numEdges - (ℓ + 1) := by
  rfl

namespace KMSWMapRep

variable {ℓ n : ℕ}

/-- Number of non-boundary edge orbits of a representative of boundary
lengths `(ℓ,1)`, via the strong endpoint carrier. Helper toward -/
@[expose] noncomputable def leftEndpointNonBoundaryEdgeCount
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ) : ℕ :=
  leftEndpointNonBoundaryEdgeCountBase R.B hℓ

/-- For a representative with `n + ℓ` total edges and `n ≥ 1`, there are
exactly `n - 1` non-boundary edges. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem leftEndpointNonBoundaryEdgeCount_eq {n ℓ : ℕ}
    (R : KMSWMapRep ℓ 1 (n + ℓ)) (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) :
    R.leftEndpointNonBoundaryEdgeCount hℓ = n - 1 := by
  rw [leftEndpointNonBoundaryEdgeCount, leftEndpointNonBoundaryEdgeCountBase_eq,
    R.edges]
  omega

/-- The non-boundary count is invariant under isomorphisms of representatives. -/
theorem leftEndpointNonBoundaryEdgeCount_eq_of_iso {n ℓ : ℕ}
    (R R' : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.leftEndpointNonBoundaryEdgeCount hℓ =
      R'.leftEndpointNonBoundaryEdgeCount hℓ := by
  rw [leftEndpointNonBoundaryEdgeCount, leftEndpointNonBoundaryEdgeCount,
    leftEndpointNonBoundaryEdgeCountBase_eq,
    leftEndpointNonBoundaryEdgeCountBase_eq, I.numEdges_eq]

end KMSWMapRep

namespace KMSWMapIsoClass

/-- The representative-independent non-boundary edge count on an
isomorphism class of `(ℓ,1)` maps. It is the quotient lift of the count on
representatives, whose isomorphism invariance is proved above. Helper toward
not adopted; not the paper result. -/
@[expose] noncomputable def leftEndpointNonBoundaryEdgeCount {ℓ n : ℕ}
    (q : KMSWMapIsoClass ℓ 1 n) (hℓ : 2 ≤ ℓ) : ℕ :=
  Quotient.lift (fun R : KMSWMapRep ℓ 1 n =>
    R.leftEndpointNonBoundaryEdgeCount hℓ)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact KMSWMapRep.leftEndpointNonBoundaryEdgeCount_eq_of_iso R R' hℓ I) q

/-- The class-level count agrees with each representative. Helper toward
not adopted; not the paper result. -/
@[simp] theorem leftEndpointNonBoundaryEdgeCount_mk {ℓ n : ℕ}
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ) :
    leftEndpointNonBoundaryEdgeCount (KMSWMapIsoClass.mk R) hℓ =
      R.leftEndpointNonBoundaryEdgeCount hℓ := rfl

/-- For `n ≥ 1`, every class indexed by `n + ℓ` total edges has `n - 1`
non-boundary edges. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem leftEndpointNonBoundaryEdgeCount_eq {n ℓ : ℕ}
    (q : KMSWMapIsoClass ℓ 1 (n + ℓ)) (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) :
    leftEndpointNonBoundaryEdgeCount q hℓ = n - 1 := by
  induction q using KMSWMapIsoClass.ind with
  | h R =>
    rw [leftEndpointNonBoundaryEdgeCount_mk]
    exact KMSWMapRep.leftEndpointNonBoundaryEdgeCount_eq R hℓ hn

end KMSWMapIsoClass

/-- On a simple directed path, a dart has terminal vertex equal to the
endpoint exactly when it is the final dart. Supporting helper toward
not adopted; not the paper result. -/
private theorem leftPath_head_eq_sink_iff {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (i : Fin B.leftPath.darts.length) :
    dartHeadVertex B.map (B.leftPath.darts.get i) = B.sink ↔
      i.val + 1 = B.leftPath.darts.length := by
  have hlen : B.leftPath.vertices.length = B.leftPath.darts.length + 1 := by
    rw [B.leftPath.vertices_length, B.leftPath.darts_length]
  let j : Fin B.leftPath.vertices.length :=
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  let k : Fin B.leftPath.vertices.length :=
    ⟨B.leftPath.darts.length, by omega⟩
  have hstep := B.leftPath.edge_step i
  have hhead : B.leftPath.vertices.get j =
      dartHeadVertex B.map (B.leftPath.darts.get i) := by
    simpa [j] using hstep.2.2.2
  have hlast : B.leftPath.vertices.get k = B.sink := by
    simpa [k, B.leftPath.vertices_length, B.leftPath.darts_length] using
      B.leftPath.end_vertex
  constructor
  · intro h
    have hget : B.leftPath.vertices.get j = B.leftPath.vertices.get k := by
      rw [hhead, h, hlast]
    have hji := B.leftPath.vertices_nodup.get_inj_iff.mp hget
    have hv : i.val + 1 = B.leftPath.darts.length := by
      simpa [j, k] using congrArg Fin.val hji
    exact hv
  · intro h
    have hji : j = k := Fin.ext (by simpa [j, k] using h)
    rw [← hhead, hji, hlast]

/-- Canonical declared-missing decoration on the left boundary path: its
first `ℓ - 1` darts, represented by precisely the path indices before the
final one. The path lemma below identifies this with all left-boundary darts
whose terminal vertex is not the sink. The map itself continues to carry all
its geometric boundary edges. This transported representative set is the
simpler faithful class decoration. Helper toward `lem-kmsw-left` -/
@[expose] def leftMissingDarts {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) : Set D :=
  {d | ∃ i : Fin B.leftPath.darts.length,
    i.val + 1 < B.leftPath.darts.length ∧ d = B.leftPath.darts.get i}

/-- The declared-missing set is exactly the left-boundary darts whose
terminal vertex is not the sink, and consists of every dart except the final
left-path dart. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem mem_leftMissingDarts_iff {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (d : D) :
    d ∈ leftMissingDarts B ↔
      d ∈ B.leftPath.darts ∧ dartHeadVertex B.map d ≠ B.sink := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨List.get_mem _ _, ?_⟩
    intro h
    have hfinal := (leftPath_head_eq_sink_iff B i).mp h
    omega
  · rintro ⟨hd, hhead⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hd
    have hi : i.val + 1 < B.leftPath.darts.length := by
      have hnot : i.val + 1 ≠ B.leftPath.darts.length := by
        intro hfinal
        apply hhead
        have hfinalHead : dartHeadVertex B.map (B.leftPath.darts.get i) = B.sink :=
          (leftPath_head_eq_sink_iff B i).mpr hfinal
        rw [← hget]
        exact hfinalHead
      omega
    exact ⟨i, hi, hget.symm⟩

/-- The canonical declared-missing set transports as a set of dart identities
under every base-carrier isomorphism. Thus the decoration is well defined on
isomorphism classes by transport of its dart set. Helper toward
not adopted; not the paper result. -/
theorem BipolarBoundaryBaseIso.image_leftMissingDarts {ℓ : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ 1}
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ 1}
    (I : BipolarBoundaryBaseIso B B') :
    I.toEquiv '' leftMissingDarts B = leftMissingDarts B' := by
  ext d'
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hchar := (mem_leftMissingDarts_iff B d).mp hd
    apply (mem_leftMissingDarts_iff B' (I.toEquiv d)).mpr
    refine ⟨?_, ?_⟩
    · rw [← I.leftDarts]
      exact List.mem_map.mpr ⟨d, hchar.1, rfl⟩
    · intro h
      apply hchar.2
      apply I.vertexEquiv.injective
      calc
        I.vertexEquiv (dartHeadVertex B.map d) =
            dartHeadVertex B'.map (I.toEquiv d) := I.vertexEquiv_dartHeadVertex d
        _ = B'.sink := h
        _ = I.vertexEquiv B.sink := I.vertexEquiv_sink.symm
  · intro hd'
    have hchar' := (mem_leftMissingDarts_iff B' d').mp hd'
    have hmap : d' ∈ B.leftPath.darts.map I.toEquiv := by
      rw [I.leftDarts]
      exact hchar'.1
    obtain ⟨d, hdm, hdeq⟩ := List.mem_map.mp hmap
    have hsymm : I.toEquiv.symm d' = d := by
      calc
        I.toEquiv.symm d' = I.toEquiv.symm (I.toEquiv d) :=
            congrArg I.toEquiv.symm hdeq.symm
        _ = d := Equiv.symm_apply_apply I.toEquiv d
    have hmem : I.toEquiv.symm d' ∈ B.leftPath.darts := by
      simpa [hsymm] using hdm
    have hhead : dartHeadVertex B.map (I.toEquiv.symm d') ≠ B.sink := by
      intro h
      apply hchar'.2
      have hv := I.vertexEquiv_dartHeadVertex (I.toEquiv.symm d')
      calc
        dartHeadVertex B'.map d' =
            dartHeadVertex B'.map (I.toEquiv (I.toEquiv.symm d')) :=
          congrArg (dartHeadVertex B'.map) (I.toEquiv.apply_symm_apply d').symm
        _ = I.vertexEquiv (dartHeadVertex B.map (I.toEquiv.symm d')) := hv.symm
        _ = I.vertexEquiv B.sink := congrArg I.vertexEquiv h
        _ = B'.sink := I.vertexEquiv_sink
    have hleft := (mem_leftMissingDarts_iff B (I.toEquiv.symm d')).mpr
      ⟨hmem, hhead⟩
    exact ⟨I.toEquiv.symm d', hleft, I.toEquiv.apply_symm_apply d'⟩

/-- A representative carries its canonical left-boundary missing set as an
explicit decoration. Helper toward `lem-kmsw-left`
not the paper result. -/
def KMSWMapRep.IsDeclaredLeftMissingSet {ℓ n : ℕ}
    (R : KMSWMapRep ℓ 1 n) (S : Set (Fin R.dartCount)) : Prop :=
  S = leftMissingDarts R.B

/-- The representative decoration relation is stable under base-map
isomorphism when the dart set is transported along the isomorphism. This
equivariance is the class-level well-definedness of the decoration. Helper -/
theorem KMSWMapRep.isDeclaredLeftMissingSet_iff_of_iso {ℓ n : ℕ}
    (R R' : KMSWMapRep ℓ 1 n)
    (I : BipolarBoundaryBaseIso R.B R'.B)
    (S : Set (Fin R.dartCount)) (S' : Set (Fin R'.dartCount))
    (hS : I.toEquiv '' S = S') :
    R.IsDeclaredLeftMissingSet S ↔ R'.IsDeclaredLeftMissingSet S' := by
  change S = leftMissingDarts R.B ↔ S' = leftMissingDarts R'.B
  constructor
  · intro h
    calc
      S' = I.toEquiv '' S := hS.symm
      _ = I.toEquiv '' leftMissingDarts R.B := congrArg (fun T => I.toEquiv '' T) h
      _ = leftMissingDarts R'.B := I.image_leftMissingDarts
  · intro h'
    apply I.toEquiv.injective.image_injective
    calc
      I.toEquiv '' S = S' := hS
      _ = leftMissingDarts R'.B := h'
      _ = I.toEquiv '' leftMissingDarts R.B := I.image_leftMissingDarts.symm

namespace KMSWMapIsoClass

/-- A representative's declared-missing dart set as decoration data for its
isomorphism class. The representative is retained as an index because dart
identities are transported by the class isomorphism, rather than compared as
literal labels. Helper toward `lem-kmsw-left`
not the paper result. -/
def IsDeclaredLeftMissingSet {ℓ n : ℕ}
    (q : KMSWMapIsoClass ℓ 1 n) (R : KMSWMapRep ℓ 1 n)
    (S : Set (Fin R.dartCount)) : Prop :=
  q = KMSWMapIsoClass.mk R ∧ R.IsDeclaredLeftMissingSet S

/-- The decorated-representative relation descends to isomorphism classes:
transporting the dart set along an isomorphism preserves the class
decoration. Helper toward `lem-kmsw-left`
not the paper result. -/
theorem isDeclaredLeftMissingSet_iff_of_iso {ℓ n : ℕ}
    (q : KMSWMapIsoClass ℓ 1 n) (R R' : KMSWMapRep ℓ 1 n)
    (I : BipolarBoundaryBaseIso R.B R'.B)
    (hR : q = KMSWMapIsoClass.mk R)
    (S : Set (Fin R.dartCount)) (S' : Set (Fin R'.dartCount))
    (hS : I.toEquiv '' S = S') :
    IsDeclaredLeftMissingSet q R S ↔ IsDeclaredLeftMissingSet q R' S' := by
  have hclasses : KMSWMapIsoClass.mk R = KMSWMapIsoClass.mk R' :=
    (KMSWMapIsoClass.mk_eq_mk_iff R R').2 ⟨I⟩
  have hR' : q = KMSWMapIsoClass.mk R' := hR.trans hclasses
  change (q = KMSWMapIsoClass.mk R ∧ R.IsDeclaredLeftMissingSet S) ↔
    (q = KMSWMapIsoClass.mk R' ∧ R'.IsDeclaredLeftMissingSet S')
  constructor
  · rintro ⟨_, hdec⟩
    exact ⟨hR', (KMSWMapRep.isDeclaredLeftMissingSet_iff_of_iso
      R R' I S S' hS).mp hdec⟩
  · rintro ⟨_, hdec⟩
    exact ⟨hR, (KMSWMapRep.isDeclaredLeftMissingSet_iff_of_iso
      R R' I S S' hS).mpr hdec⟩

end KMSWMapIsoClass

end DirectedDistances.PlanarMap
