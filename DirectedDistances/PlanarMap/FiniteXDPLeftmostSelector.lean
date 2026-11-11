/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPSelectorPath
public import DirectedDistances.PlanarMap.FiniteXDPLeftmost

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/- This file defines the first XDP-geodesic dart in a finite rotation scan.  The
`FiniteXDPLeftmost`.  Identifying this scan with the paper's geometric
left-to-right order requires the outgoing-interval property, which is not a
field or theorem of `BipolarTriangulationWithBoundaryBase`. -/

/-- One full finite scan of the rotation cycle, in the left-to-right scan
direction.  The anchor is included first (`lem-lr-ind`, -/
@[expose] noncomputable def finiteRotationScan
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (corner : D) : List D :=
  List.ofFn fun i : Fin (orderOf B.map.toCombinatorialMap.rot.symm) =>
    (B.map.toCombinatorialMap.rot.symm ^ i.val) corner

/-- A dart occurs in the finite scan exactly when it is incident at the
anchor's rotation-cycle vertex (`lem-lr-ind`, -/
theorem mem_finiteRotationScan_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (corner d : D) :
    d ∈ finiteRotationScan B corner ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot corner d := by
  classical
  let σ := B.map.toCombinatorialMap.rot.symm
  change d ∈ List.ofFn
      (fun i : Fin (orderOf σ) => (σ ^ i.val) corner) ↔
    Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot corner d
  rw [List.mem_ofFn']
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    have hσ : Equiv.Perm.SameCycle σ corner d := ⟨i.val, by simpa using hi⟩
    exact Equiv.Perm.sameCycle_inv.mp hσ
  · intro h
    have hinv : Equiv.Perm.SameCycle σ corner d := by
      exact Equiv.Perm.sameCycle_inv.mpr h
    obtain ⟨i, hi, hpow⟩ := hinv.exists_pow_eq'
    exact ⟨⟨i, by simpa [σ] using hi⟩, by simpa [σ] using hpow⟩

/-- The outgoing darts at the anchor vertex, listed in the order induced by
the finite `rot.symm` scan (`lem-lr-ind`, -/
@[expose] noncomputable def finiteOutgoingRotationOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (corner : D) : List D := by
  classical
  exact (finiteRotationScan B corner).filter fun d =>
    dartTailVertex B.map d = dartTailVertex B.map corner ∧ B.map.tail d

/-- Membership in the filtered rotation scan is exactly incidence at the -/
theorem mem_finiteOutgoingRotationOrder_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (corner d : D) :
    d ∈ finiteOutgoingRotationOrder B corner ↔
      dartTailVertex B.map d = dartTailVertex B.map corner ∧ B.map.tail d := by
  classical
  simp only [finiteOutgoingRotationOrder, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨(mem_finiteRotationScan_iff B corner d).2 ?_, h⟩
    exact (Quotient.exact h.1).symm

/-- A selected non-source vertex has an incoming oriented dart -/
theorem exists_incomingDartAt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.source) :
    ∃ d, ¬ B.map.missing d ∧ B.map.tail d ∧
      dartHeadVertex B.map d = v := by
  have hstep : ∃ u, B.map.directedStep u v := by
    by_contra h
    exact hvs (B.source_unique v h)
  obtain ⟨u, d, hm, ht, htail, hhead⟩ := hstep
  exact ⟨d, hm, ht, hhead⟩

/-- The rotation corner used by the finite selector: the first left-boundary
dart at the source, and the reverse dart of a chosen incoming edge elsewhere -/
@[expose] noncomputable def finiteXDPLeftmostCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) : D := by
  classical
  exact if hs : v = B.source then
    B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
  else
    B.map.toCombinatorialMap.edgeInv (Classical.choose (exists_incomingDartAt B v hs))

private theorem leftPath_firstDart_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    dartTailVertex B.map
      (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) = B.source := by
  have hdpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact Nat.zero_lt_of_lt B.left_length_pos
  let i : Fin B.leftPath.darts.length := ⟨0, hdpos⟩
  have hs := B.leftPath.edge_step i
  have hvpos : 0 < B.leftPath.vertices.length := by
    rw [B.leftPath.vertices_length]
    exact Nat.zero_lt_succ _
  let j : Fin B.leftPath.vertices.length := ⟨0, hvpos⟩
  have hstart : B.leftPath.vertices.get j = B.source := by
    simpa [j] using B.leftPath.start_vertex
  calc
    dartTailVertex B.map
        (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
        B.leftPath.vertices.get j := by
      simpa [SimpleDirectedDartPath.firstDart, i, j] using hs.2.2.1.symm
    _ = B.source := hstart

/-- The corner scan at the source starts at the first left-boundary dart -/
theorem finiteXDPLeftmostCorner_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    finiteXDPLeftmostCorner B B.source =
      B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  classical
  simp [finiteXDPLeftmostCorner]

/-- Every dart based at the source is oriented out of the source.  This uses
the no-incoming source clause and the base carrier's no-missing-darts clause -/
theorem tail_of_dartTailVertex_eq_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : dartTailVertex B.map d = B.source) : B.map.tail d := by
  classical
  by_contra htail
  have htailInv : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
    exact (B.map.tail_iff (B.map.toCombinatorialMap.edgeInv d)
      (B.noMissingDarts _)).2 (by
        simpa only [B.map.toCombinatorialMap.edgeInv_invol] using htail)
  have hhead : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
      B.source := by
    calc
      dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
          dartTailVertex B.map d := by
        simp [dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol]
      _ = B.source := hd
  apply B.isSource
  exact ⟨dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d),
    B.map.toCombinatorialMap.edgeInv d, B.noMissingDarts _, htailInv,
    rfl, hhead⟩

/-- At the source, every dart in the rotation cycle is outgoing.  Thus the
finite outgoing scan is the entire cyclic rotation starting at the first
left-boundary dart (`lem-lr-ind`, -/
theorem finiteOutgoingRotationOrder_eq_scan_at_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    finiteOutgoingRotationOrder B (finiteXDPLeftmostCorner B B.source) =
      finiteRotationScan B (finiteXDPLeftmostCorner B B.source) := by
  classical
  rw [finiteOutgoingRotationOrder, finiteXDPLeftmostCorner_source]
  apply List.filter_eq_self.mpr
  intro d hd
  have hcycle := (mem_finiteRotationScan_iff B _ d).mp hd
  have hcorner := leftPath_firstDart_tail B
  have hquot : dartTailVertex B.map
      (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
      dartTailVertex B.map d := Quotient.sound hcycle
  have hvertex : dartTailVertex B.map d = B.source := hquot.symm.trans hcorner
  have htail := tail_of_dartTailVertex_eq_source B d hvertex
  simpa only [decide_eq_true_eq] using
    (show dartTailVertex B.map d =
        dartTailVertex B.map (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) ∧
      B.map.tail d from ⟨hvertex.trans hcorner.symm, htail⟩)

/-- With exactly one incoming dart at `v`, every dart at `v` is outgoing
except the reverse dart of that incoming edge.  Hence the outgoing darts are
one cyclic interval in the rotation order (`lem-lr-ind`, -/
theorem singleIncoming_rotationPattern
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (incoming : D)
    (hin : B.map.tail incoming ∧ dartHeadVertex B.map incoming = v)
    (hunique : ∀ d, B.map.tail d → dartHeadVertex B.map d = v → d = incoming) :
    B.map.tail incoming ∧ dartHeadVertex B.map incoming = v ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv incoming) ∧
      ∀ d, dartTailVertex B.map d = v →
        B.map.tail d ∨
          d = B.map.toCombinatorialMap.edgeInv incoming := by
  refine ⟨hin.1, hin.2, ?_, ?_⟩
  · exact (B.map.tail_iff incoming (B.noMissingDarts incoming)).mp hin.1
  · intro d hdv
    by_cases htail : B.map.tail d
    · exact Or.inl htail
    · right
      have htailInv : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
        exact (B.map.tail_iff (B.map.toCombinatorialMap.edgeInv d)
          (B.noMissingDarts (B.map.toCombinatorialMap.edgeInv d))).2 (by
            simpa only [B.map.toCombinatorialMap.edgeInv_invol] using htail)
      have hhead : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d) = v := by
        calc
          dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
              dartTailVertex B.map d := by
            simp [dartHeadVertex, dartTailVertex,
              B.map.toCombinatorialMap.edgeInv_invol]
          _ = v := hdv
      have heq := hunique (B.map.toCombinatorialMap.edgeInv d) htailInv hhead
      calc
        d = B.map.toCombinatorialMap.edgeInv
            (B.map.toCombinatorialMap.edgeInv d) :=
              (B.map.toCombinatorialMap.edgeInv_invol d).symm
        _ = B.map.toCombinatorialMap.edgeInv incoming := congrArg _ heq

 
theorem dartTailVertex_finiteXDPLeftmostCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :
    dartTailVertex B.map (finiteXDPLeftmostCorner B v) = v := by
  classical
  dsimp [finiteXDPLeftmostCorner]
  split_ifs with hs
  · rw [leftPath_firstDart_tail]
    exact hs.symm
  · have hhead := (Classical.choose_spec (exists_incomingDartAt B v hs)).2.2
    calc
      dartTailVertex B.map
          (B.map.toCombinatorialMap.edgeInv
            (Classical.choose (exists_incomingDartAt B v hs))) =
          dartHeadVertex B.map
            (Classical.choose (exists_incomingDartAt B v hs)) := rfl
      _ = v := hhead

/-- The finite outgoing rotation-order list restricted to XDP-geodesic darts -/
@[expose] noncomputable def finiteXDPGeodesicDartOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) : List D := by
  classical
  exact (finiteOutgoingRotationOrder B (finiteXDPLeftmostCorner B v)).filter
    fun d => IsXDPGeodesicDart B x d

/-- The first XDP-geodesic dart in the finite outgoing rotation order at
`v`, with the selected rotation corner as origin.  If no such dart occurs,
the corner is returned as junk (`lem-lr-ind`, -/
@[expose] noncomputable def leftmostSel
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) : D := by
  classical
  let candidates := finiteXDPGeodesicDartOrder B x v
  exact match candidates with
    | [] => finiteXDPLeftmostCorner B v
    | d :: _ => d

/-- At a non-sink vertex on an XDP geodesic, `leftmostSel` is the first
geodesic dart in its finite outgoing rotation scan (`lem-lr-ind`, -/
theorem leftmostSel_spec
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink) :
    dartTailVertex B.map (leftmostSel B x v) = v ∧
      IsXDPGeodesicDart B x (leftmostSel B x v) := by
  classical
  obtain ⟨d, htail, hgeo⟩ := exists_outgoingXDPGeodesicDart_of_geodesic_vertex
    B x hv hvs
  let corner := finiteXDPLeftmostCorner B v
  have hcorner : dartTailVertex B.map corner = v :=
    dartTailVertex_finiteXDPLeftmostCorner B v
  have htailOrientation := (IsXDPGeodesicDart.present_tail B x d hgeo).2
  have horder : d ∈ finiteOutgoingRotationOrder B corner :=
    (mem_finiteOutgoingRotationOrder_iff B corner d).2
      ⟨htail.trans hcorner.symm, htailOrientation⟩
  let candidates := finiteXDPGeodesicDartOrder B x v
  have hmem : d ∈ candidates := by
    simp only [candidates, finiteXDPGeodesicDartOrder, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨horder, hgeo⟩
  have hne : candidates ≠ [] := List.ne_nil_of_mem hmem
  have hselected : leftmostSel B x v ∈ candidates := by
    unfold leftmostSel
    dsimp [candidates, corner]
    cases hc : finiteXDPGeodesicDartOrder B x v with
    | nil => exact (hne hc).elim
    | cons e es => simp
  have hselected' : leftmostSel B x v ∈ finiteOutgoingRotationOrder B corner ∧
      IsXDPGeodesicDart B x (leftmostSel B x v) := by
    simpa only [candidates, finiteXDPGeodesicDartOrder, List.mem_filter,
      decide_eq_true_eq] using hselected
  have htailSelected :=
    (mem_finiteOutgoingRotationOrder_iff B corner _).mp hselected'.1
  exact ⟨htailSelected.1.trans hcorner, hselected'.2⟩

/-- At every non-sink geodesic vertex, `leftmostSel` is the first entry among
all outgoing XDP-geodesic darts in the selected finite rotation scan.  Thus
at a first divergence its dart is first in this scan order -/
theorem leftmostSel_first_in_rotationOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink) :
    ∃ rest : List D,
      leftmostSel B x v :: rest = finiteXDPGeodesicDartOrder B x v ∧
      ∀ d, dartTailVertex B.map d = v → IsXDPGeodesicDart B x d →
        d = leftmostSel B x v ∨ d ∈ rest := by
  classical
  let corner := finiteXDPLeftmostCorner B v
  let candidates := finiteXDPGeodesicDartOrder B x v
  have hspec := leftmostSel_spec B x v hv hvs
  have hcorner : dartTailVertex B.map corner = v :=
    dartTailVertex_finiteXDPLeftmostCorner B v
  have hselMem : leftmostSel B x v ∈ candidates := by
    simp only [candidates, finiteXDPGeodesicDartOrder, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨(mem_finiteOutgoingRotationOrder_iff B corner _).2
      ⟨hspec.1.trans hcorner.symm,
        (IsXDPGeodesicDart.present_tail B x _ hspec.2).2⟩, hspec.2⟩
  have hne : candidates ≠ [] := List.ne_nil_of_mem hselMem
  obtain ⟨rest, hcons⟩ :
      ∃ rest : List D, leftmostSel B x v :: rest = candidates := by
    unfold leftmostSel
    dsimp [candidates, corner]
    cases hc : finiteXDPGeodesicDartOrder B x v with
    | nil => exact (hne hc).elim
    | cons d ds => exact ⟨ds, rfl⟩
  refine ⟨rest, ?_, ?_⟩
  · simpa [candidates] using hcons
  · intro d htail hgeo
    have hmem : d ∈ candidates := by
      simp only [candidates, finiteXDPGeodesicDartOrder, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨(mem_finiteOutgoingRotationOrder_iff B corner d).2
        ⟨htail.trans hcorner.symm,
          (IsXDPGeodesicDart.present_tail B x d hgeo).2⟩, hgeo⟩
    rw [← hcons] at hmem
    exact List.mem_cons.mp hmem

/-- The finite leftmost selector determines an XDP-geodesic path.  Its
geodesicity follows from `exists_selector_XDPGeodesic_path`; geometric
leftmostness still requires identifying the rotation scans with the paper's
343–368`). -/
theorem exists_leftmostSel_XDPGeodesic_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
      IsXDPGeodesicBase B x P ∧
        ∀ i : Fin (xdpLengthBase B x),
          P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ =
            leftmostSel B x (selectorVertex B (leftmostSel B x) i.val) := by
  apply exists_selector_XDPGeodesic_path B x (leftmostSel B x)
  intro v hv hvs
  exact leftmostSel_spec B x v hv hvs

end DirectedDistances.PlanarMap
