/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarBoundary
import DirectedDistances.PlanarMap.OuterBoundaryRuns

/-! # Intrinsic boundary data for finite bipolar maps

the general combinatorial carrier determines its boundary lengths, ordered
boundary paths, source and sink. No disjointness between the paths is used.
The outer face here is the marked combinatorial face of the input carrier. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r ℓ' r' : ℕ}

namespace BipolarMapWithBoundaryBase



theorem ulDarts_nonempty (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.map.ulDarts.Nonempty := by
  have hpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact B.left_length_pos
  exact ⟨B.leftPath.darts[0],
    (B.outerSplit.2.2.1 _).mp (List.getElem_mem hpos)⟩



theorem lrDarts_nonempty (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.map.lrDarts.Nonempty := by
  let xs := B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hpos : 0 < xs.length := by
    simp only [xs, List.length_map, List.length_reverse, B.rightPath.darts_length]
    exact B.right_length_pos
  exact ⟨xs[0], (B.outerSplit.2.2.2.1 _).mp (List.getElem_mem hpos)⟩



theorem boundary_darts_eq_of_map_eq
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (B' : BipolarMapWithBoundaryBase D ℓ' r') (h : B.map = B'.map) :
    B.leftPath.darts = B'.leftPath.darts ∧
      B.rightPath.darts = B'.rightPath.darts := by
  have hsplit : FourArcsWitness B'.map B.outerWord B.leftPath.darts []
      (B.rightPath.darts.reverse.map B'.map.toCombinatorialMap.edgeInv) [] := by
    simpa only [h] using B.outerSplit
  have heq := fourArcsWitness_unique_blocks B'.map B.outerWord B'.outerWord
    B.leftPath.darts []
    (B.rightPath.darts.reverse.map B'.map.toCombinatorialMap.edgeInv) []
    B'.leftPath.darts []
    (B'.rightPath.darts.reverse.map B'.map.toCombinatorialMap.edgeInv) []
    B'.ulDarts_nonempty B'.lrDarts_nonempty hsplit B'.outerSplit
  refine ⟨heq.2.2.1, ?_⟩
  apply List.reverse_injective
  exact (List.map_injective_iff.mpr
    B'.map.toCombinatorialMap.edgeInv.injective) heq.2.2.2



theorem boundary_lengths_eq_of_map_eq
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (B' : BipolarMapWithBoundaryBase D ℓ' r') (h : B.map = B'.map) :
    ℓ = ℓ' ∧ r = r' := by
  obtain ⟨hleft, hright⟩ := B.boundary_darts_eq_of_map_eq B' h
  constructor
  · simpa only [B.leftPath.darts_length, B'.leftPath.darts_length] using
      congrArg List.length hleft
  · simpa only [B.rightPath.darts_length, B'.rightPath.darts_length] using
      congrArg List.length hright

private theorem isSource_cast {M N : DirectedMapWithMissing D} (h : M = N)
    (s : MapVertex M) (hs : ¬ ∃ u, M.directedStep u s) :
    ¬ ∃ u, N.directedStep u (cast (congrArg MapVertex h) s) := by
  subst N
  exact hs

private theorem isSink_cast {M N : DirectedMapWithMissing D} (h : M = N)
    (t : MapVertex M) (ht : ¬ ∃ w, M.directedStep t w) :
    ¬ ∃ w, N.directedStep (cast (congrArg MapVertex h) t) w := by
  subst N
  exact ht



theorem source_eq_of_map_eq
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (B' : BipolarMapWithBoundaryBase D ℓ' r') (h : B.map = B'.map) :
    cast (congrArg MapVertex h) B.source = B'.source := by
  exact B'.source_unique _ (isSource_cast h B.source B.isSource)



theorem sink_eq_of_map_eq
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (B' : BipolarMapWithBoundaryBase D ℓ' r') (h : B.map = B'.map) :
    cast (congrArg MapVertex h) B.sink = B'.sink := by
  exact B'.sink_unique _ (isSink_cast h B.sink B.isSink)

omit [Fintype D] in


private theorem card_eq_length_of_enumeratesSet (xs : List D) (s : Set D)
    (hnodup : xs.Nodup) (henum : EnumeratesSet xs s) :
    Nat.card {d : D // d ∈ s} = xs.length := by
  calc
    Nat.card {d : D // d ∈ s} = xs.toFinset.card :=
      Nat.subtype_card _ (fun d => List.mem_toFinset.trans (henum d))
    _ = xs.length := List.toFinset_card_of_nodup hnodup



theorem left_length_eq_card_ulDarts (B : BipolarMapWithBoundaryBase D ℓ r) :
    ℓ = Nat.card {d : D // d ∈ B.map.ulDarts} := by
  have hnodup : (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).Nodup := by
    simpa only [List.append_nil] using
      B.outerSplit.2.1.nodup_iff.mp B.outerWord.nodup
  calc
    ℓ = B.leftPath.darts.length := B.leftPath.darts_length.symm
    _ = Nat.card {d : D // d ∈ B.map.ulDarts} :=
      (card_eq_length_of_enumeratesSet _ _ hnodup.of_append_left
        B.outerSplit.2.2.1).symm



theorem right_length_eq_card_lrDarts (B : BipolarMapWithBoundaryBase D ℓ r) :
    r = Nat.card {d : D // d ∈ B.map.lrDarts} := by
  have hnodup : (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).Nodup := by
    simpa only [List.append_nil] using
      B.outerSplit.2.1.nodup_iff.mp B.outerWord.nodup
  have hcard := card_eq_length_of_enumeratesSet _ _ hnodup.of_append_right
    B.outerSplit.2.2.2.1
  simpa only [List.length_map, List.length_reverse, B.rightPath.darts_length]
    using hcard.symm



theorem outerFace_dartCount_eq_boundaryLengths
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.IsOuter d} = ℓ + r := by
  have hcard := card_eq_length_of_enumeratesSet B.outerWord.letters
    {d : D | B.map.IsOuter d} B.outerWord.nodup
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1)
  have hlen : B.outerWord.letters.length = ℓ + r := by
    simpa only [List.length_append, List.length_nil, List.length_map,
      List.length_reverse, Nat.add_zero, B.leftPath.darts_length,
      B.rightPath.darts_length] using B.outerSplit.2.1.perm.length_eq
  exact hcard.trans hlen

end BipolarMapWithBoundaryBase

/-- the boundary lengths are intrinsic to the underlying directed map. -/
theorem boundary_lengths_eq_of_isBipolarMapWithBoundary
    (M : DirectedMapWithMissing D)
    (h : IsBipolarMapWithBoundary M ℓ r)
    (h' : IsBipolarMapWithBoundary M ℓ' r') :
    ℓ = ℓ' ∧ r = r' := by
  obtain ⟨B, hBM⟩ := h
  obtain ⟨B', hB'M⟩ := h'
  exact B.boundary_lengths_eq_of_map_eq B' (hBM.trans hB'M.symm)

/-- the first left-boundary dart is on the outer face and leaves the source. -/
theorem left_firstDart_isOuter_tail_eq_source
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    let d := B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
    B.map.IsOuter d ∧ dartTailVertex B.map d = B.source := by
  dsimp
  let d := B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
  have hpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact Nat.zero_lt_of_lt B.left_length_pos
  have hdmem : d ∈ B.leftPath.darts := by
    dsimp [d, SimpleDirectedDartPath.firstDart]
    exact List.getElem_mem _
  have hUL : d ∈ B.map.ulDarts := (B.outerSplit.2.2.1 d).mp hdmem
  have htail : dartTailVertex B.map d = B.source := by
    let i : Fin B.leftPath.darts.length := ⟨0, hpos⟩
    let j : Fin B.leftPath.vertices.length := ⟨0, by
      rw [B.leftPath.vertices_length]
      omega⟩
    have hs := B.leftPath.edge_step i
    have hstart : B.leftPath.vertices.get j = B.source := by
      simpa [j] using B.leftPath.start_vertex
    calc
      dartTailVertex B.map d = B.leftPath.vertices.get j := by
        simpa [d, SimpleDirectedDartPath.firstDart, i, j] using hs.2.2.1.symm
      _ = B.source := hstart
  exact ⟨hUL.2.2, htail⟩

/-- the last right-boundary dart ends at the sink, and its inverse lies on the
outer face. -/
theorem right_lastDart_head_eq_sink_edgeInv_isOuter
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    let d := B.rightPath.darts[r - 1]'(by
      rw [B.rightPath.darts_length]
      have hr := B.right_length_pos
      omega)
    dartHeadVertex B.map d = B.sink ∧
      B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d) := by
  dsimp
  let d := B.rightPath.darts[r - 1]'(by
    rw [B.rightPath.darts_length]
    have hr := B.right_length_pos
    omega)
  have hidx : r - 1 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    have hr := B.right_length_pos
    omega
  have hdmem : d ∈ B.rightPath.darts := List.getElem_mem _
  have hhead : dartHeadVertex B.map d = B.sink := by
    let i : Fin B.rightPath.darts.length := ⟨r - 1, hidx⟩
    let j : Fin B.rightPath.vertices.length := ⟨r, by
      rw [B.rightPath.vertices_length]
      omega⟩
    have hs := B.rightPath.edge_step i
    have hi : i.val < r := by
      change r - 1 < r
      have hr := B.right_length_pos
      omega
    have hstepBound : i.val + 1 < B.rightPath.vertices.length := by
      rw [B.rightPath.vertices_length]
      omega
    have hstep : B.rightPath.vertices.get
        ⟨i.val + 1, hstepBound⟩ = dartHeadVertex B.map d := by
      simpa [d, i, List.get_eq_getElem] using hs.2.2.2
    have hend : B.rightPath.vertices.get j = B.sink := by
      simpa [j] using B.rightPath.end_vertex
    have hfin : (⟨i.val + 1, hstepBound⟩ : Fin B.rightPath.vertices.length) = j := by
      apply Fin.ext
      change r - 1 + 1 = r
      omega
    calc
      dartHeadVertex B.map d = B.rightPath.vertices.get j := by
        rw [← hstep, hfin]
      _ = B.sink := hend
  have hinvMem : B.map.toCombinatorialMap.edgeInv d ∈
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv := by
    apply List.mem_map.mpr
    exact ⟨d, List.mem_reverse.mpr hdmem, rfl⟩
  have hlr : B.map.toCombinatorialMap.edgeInv d ∈ B.map.lrDarts :=
    (B.outerSplit.2.2.2.1 _).mp hinvMem
  exact ⟨hhead, hlr.2.2⟩

/-- both poles are tails of darts on the outer face. -/
theorem source_and_sink_are_tails_of_outer_darts
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    (∃ d, B.map.IsOuter d ∧ dartTailVertex B.map d = B.source) ∧
    (∃ d, B.map.IsOuter d ∧ dartTailVertex B.map d = B.sink) := by
  let dL := B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
  have hL : B.map.IsOuter dL ∧ dartTailVertex B.map dL = B.source := by
    simpa only [dL] using left_firstDart_isOuter_tail_eq_source B
  let dR := B.rightPath.darts[r - 1]'(by
    rw [B.rightPath.darts_length]
    have hr := B.right_length_pos
    omega)
  have hR : dartHeadVertex B.map dR = B.sink ∧
      B.map.IsOuter (B.map.toCombinatorialMap.edgeInv dR) := by
    simpa only [dR] using right_lastDart_head_eq_sink_edgeInv_isOuter B
  refine ⟨⟨dL, hL.1, hL.2⟩, ?_⟩
  refine ⟨B.map.toCombinatorialMap.edgeInv dR, hR.2, ?_⟩
  simpa [dartTailVertex, dartHeadVertex,
    B.map.toCombinatorialMap.edgeInv_invol] using hR.1

end DirectedDistances.PlanarMap
