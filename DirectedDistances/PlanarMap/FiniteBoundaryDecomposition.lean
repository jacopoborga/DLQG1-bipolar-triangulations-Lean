/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarBoundary
public import DirectedDistances.PlanarMap.OuterFaceIncidence
public import DirectedDistances.PlanarMap.FiniteBipolarBoundaryWellDefined

/-! # Finite boundary decompositions with marked junctions

A directed path lists tail darts, whereas `lrDarts` contains non-tail darts.
The lower-right outer-face block therefore uses reversed opposite darts.
Missing runs are walks of geometric darts, without any orientation condition.
An empty run identifies its endpoint junctions; an empty present path is the
zero-edge simple path at its supplied junction. Both present-path labels are
retained even when both paths are empty, without requiring distinctness.

This is the finite marked combinatorial-face case only. No geometric external
face correspondence or infinite/boundaryless boundary definition is claimed. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}

namespace SimpleDirectedDartPath

/-- directed path cannot enumerate the intrinsic non-tail lower-right dart set
unless its length is zero. This is the obstruction to using its directed
dart list itself as the lower-right outer-face block. -/
theorem length_eq_zero_of_enumerates_lrDarts
    (P : SimpleDirectedDartPath M s t n)
    (h : EnumeratesSet P.darts M.lrDarts) : n = 0 := by
  by_contra hn
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  let i : Fin P.darts.length := ⟨0, by rw [P.darts_length]; exact hpos⟩
  have htail : M.tail (P.darts.get i) := (P.edge_step i).2.1
  have hlr : P.darts.get i ∈ M.lrDarts :=
    (h _).mp (List.get_mem P.darts i)
  exact hlr.2.1 htail

end SimpleDirectedDartPath

namespace BipolarMapWithBoundaryBase




theorem rightPath_not_enumerates_lrDarts {ℓ r : ℕ}
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    ¬ EnumeratesSet B.rightPath.darts B.map.lrDarts := by
  intro h
  have hr := B.rightPath.length_eq_zero_of_enumerates_lrDarts h
  have hpos := B.right_length_pos
  omega

end BipolarMapWithBoundaryBase

/-- an endpoint-labelled walk of geometric darts. No dart orientation is required.
In particular, the empty walk has equal endpoints. -/
@[expose] def IsBoundaryDartWalk (M : DirectedMapWithMissing D)
    (xs : List D) (s t : MapVertex M) : Prop :=
  match xs with
  | [] => s = t
  | d :: ds => s = dartTailVertex M d ∧
      IsBoundaryDartWalk M ds (dartHeadVertex M d) t

/-- the empty missing run is precisely the walk at a single supplied junction. -/
@[simp] theorem isBoundaryDartWalk_nil_iff (M : DirectedMapWithMissing D)
    (s t : MapVertex M) : IsBoundaryDartWalk M [] s t ↔ s = t := Iff.rfl

/-- the endpoint conditions for a missing run. An empty run identifies its two
supplied junctions; a nonempty run starts at its first dart's tail and ends
at its last dart's head. These are geometric endpoints, not orientations. -/
@[expose] def BoundaryRunEndpoints (M : DirectedMapWithMissing D)
    (xs : List D) (s t : MapVertex M) : Prop :=
  match xs with
  | [] => s = t
  | d :: ds => s = dartTailVertex M d ∧
      dartHeadVertex M ((d :: ds).getLast (by simp)) = t

/-- a geometric walk consists exactly of its endpoint incidences and its
consecutive dart incidences, including the empty-run case. -/
theorem isBoundaryDartWalk_iff_endpoints_and_isChain
    (M : DirectedMapWithMissing D) (xs : List D) (s t : MapVertex M) :
    IsBoundaryDartWalk M xs s t ↔ BoundaryRunEndpoints M xs s t ∧
      xs.IsChain (fun d e => dartHeadVertex M d = dartTailVertex M e) := by
  induction xs generalizing s with
  | nil => simp [IsBoundaryDartWalk, BoundaryRunEndpoints]
  | cons d ds ih =>
    cases ds with
    | nil => simp [IsBoundaryDartWalk, BoundaryRunEndpoints]
    | cons e es =>
      rw [IsBoundaryDartWalk, ih]
      simp only [BoundaryRunEndpoints, List.getLast_cons_cons, List.isChain_cons_cons]
      constructor
      · rintro ⟨hs, ⟨hm, ht⟩, hc⟩
        exact ⟨⟨hs, ht⟩, hm, hc⟩
      · rintro ⟨⟨hs, ht⟩, hm, hc⟩
        exact ⟨hs, ⟨hm, ht⟩, hc⟩

/-- any contiguous block of an exact outer cycle has consecutive geometric dart
incidences, even if the boundary revisits vertices or the block is empty. -/
theorem isOuterCycle_block_isChain (M : DirectedMapWithMissing D)
    (W : NonemptyWord D) (hW : IsOuterCycle M W) (pre xs post : List D)
    (hblock : W.letters ~r (pre ++ xs ++ post)) :
    xs.IsChain (fun d e => dartHeadVertex M d = dartTailVertex M e) := by
  obtain ⟨n, hn⟩ := hblock
  have hr : W.letters.rotate (n + pre.length) = xs ++ (post ++ pre) := by
    rw [← List.rotate_rotate, hn, List.append_assoc, List.rotate_append_length_eq,
      List.append_assoc]
  have hlen : xs.length ≤ W.letters.length := by
    have h := congrArg List.length hr
    simp only [List.length_rotate, List.length_append] at h
    omega
  apply List.isChain_iff_getElem.mpr
  intro i hi
  exact outerCycle_rotate_take_consecutive_incident M W hW
    (n + pre.length) xs.length xs (by rw [hr, List.take_left]) hlen i hi

/-- a finite four-part boundary with four retained junction labels. UL and LR
are simple directed paths, possibly of length zero; UR and LL are consecutive
missing geometric-dart walks in outer-face order. The LR outer block is the
reversed opposite-dart list of its directed path. The outer boundary need
not be a simple vertex cycle. -/
structure FiniteBoundaryDecomposition (M : DirectedMapWithMissing D) where
  outerWord : NonemptyWord D
  outerCycle : IsOuterCycle M outerWord
  ulInitial : MapVertex M
  ulTerminal : MapVertex M
  lrInitial : MapVertex M
  lrTerminal : MapVertex M
  ulLength : ℕ
  lrLength : ℕ
  ul : SimpleDirectedDartPath M ulInitial ulTerminal ulLength
  lr : SimpleDirectedDartPath M lrInitial lrTerminal lrLength
  ur : List D
  ll : List D
  outer_order : outerWord.letters ~r
    (ul.darts ++ ur ++ (lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ ll)
  ul_enumerates : EnumeratesSet ul.darts M.ulDarts
  lr_enumerates : EnumeratesSet
    (lr.darts.reverse.map M.toCombinatorialMap.edgeInv) M.lrDarts
  ur_missing : MissingRun M ur
  ll_missing : MissingRun M ll
  ur_walk : IsBoundaryDartWalk M ur ulTerminal lrTerminal
  ll_walk : IsBoundaryDartWalk M ll lrInitial ulInitial

namespace SimpleDirectedDartPath

/-- the zero-edge simple directed path at a supplied finite junction. -/
@[expose] def nil (M : DirectedMapWithMissing D) (v : MapVertex M) :
    SimpleDirectedDartPath M v v 0 where
  darts := []
  vertices := [v]
  darts_length := rfl
  vertices_length := rfl
  vertices_nodup := by simp
  start_vertex := rfl
  end_vertex := rfl
  edge_step := fun i => Fin.elim0 i

/-- an empty directed path has its initial and terminal junction at the same
vertex, as required by the finite empty-boundary ruling. -/
theorem endpoints_eq_of_darts_eq_nil (P : SimpleDirectedDartPath M s t n)
    (h : P.darts = []) : s = t := by
  have hn : n = 0 := by simpa only [h, List.length_nil] using P.darts_length.symm
  subst n
  exact P.start_vertex.symm.trans P.end_vertex

end SimpleDirectedDartPath

namespace FiniteBoundaryDecomposition

variable (C : FiniteBoundaryDecomposition M)

/-- forgetting the junction labels yields the corrected four-block witness. -/
theorem fourArcsWitness :
    FourArcsWitness M C.outerWord C.ul.darts C.ur
      (C.lr.darts.reverse.map M.toCombinatorialMap.edgeInv) C.ll :=
  ⟨C.outerCycle, C.outer_order, C.ul_enumerates, C.lr_enumerates,
    C.ur_missing, C.ll_missing⟩

/-- an empty UL retains its supplied single junction. -/
theorem ul_endpoints_eq_of_empty (h : C.ul.darts = []) :
    C.ulInitial = C.ulTerminal := C.ul.endpoints_eq_of_darts_eq_nil h

/-- an empty LR retains its supplied single junction. No inequality with the
UL junction is asserted. -/
theorem lr_endpoints_eq_of_empty (h : C.lr.darts = []) :
    C.lrInitial = C.lrTerminal := C.lr.endpoints_eq_of_darts_eq_nil h

/-- the endpoints of an empty UR run are the supplied terminal junctions. -/
theorem terminal_eq_of_ur_eq_nil (h : C.ur = []) :
    C.ulTerminal = C.lrTerminal := by
  simpa only [h, isBoundaryDartWalk_nil_iff] using C.ur_walk

/-- the endpoints of an empty LL run are the supplied initial junctions. -/
theorem initial_eq_of_ll_eq_nil (h : C.ll = []) :
    C.lrInitial = C.ulInitial := by
  simpa only [h, isBoundaryDartWalk_nil_iff] using C.ll_walk

end FiniteBoundaryDecomposition

/-- existence is equivalent to a marked four-block witness with the source's
two simple present paths and the missing runs' endpoint incidences. Their
internal consecutive incidences follow from the outer cycle. Simplicity
is required of the present paths only, not of the whole outer boundary.
Empty paths and runs use their supplied junctions without distinctness. -/
theorem nonempty_finiteBoundaryDecomposition_iff (M : DirectedMapWithMissing D) :
    Nonempty (FiniteBoundaryDecomposition M) ↔
      ∃ (W : NonemptyWord D) (ulInitial ulTerminal lrInitial lrTerminal : MapVertex M)
        (a b : ℕ) (ul : SimpleDirectedDartPath M ulInitial ulTerminal a)
        (lr : SimpleDirectedDartPath M lrInitial lrTerminal b) (ur ll : List D),
        FourArcsWitness M W ul.darts ur
          (lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ll ∧
        BoundaryRunEndpoints M ur ulTerminal lrTerminal ∧
        BoundaryRunEndpoints M ll lrInitial ulInitial := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.outerWord, C.ulInitial, C.ulTerminal, C.lrInitial, C.lrTerminal,
      C.ulLength, C.lrLength, C.ul, C.lr, C.ur, C.ll,
      C.fourArcsWitness,
      ((isBoundaryDartWalk_iff_endpoints_and_isChain M _ _ _).mp C.ur_walk).1,
      ((isBoundaryDartWalk_iff_endpoints_and_isChain M _ _ _).mp C.ll_walk).1⟩
  · rintro ⟨W, ui, ut, li, lt, a, b, ul, lr, ur, ll, h, hur, hll⟩
    have hUR := isOuterCycle_block_isChain M W h.1 ul.darts ur
      ((lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ ll)
      (by simpa only [List.append_assoc] using h.2.1)
    have hLL := isOuterCycle_block_isChain M W h.1
      (ul.darts ++ ur ++ (lr.darts.reverse.map M.toCombinatorialMap.edgeInv)) ll []
      (by simpa only [List.append_nil] using h.2.1)
    exact ⟨{
      outerWord := W
      outerCycle := h.1
      ulInitial := ui
      ulTerminal := ut
      lrInitial := li
      lrTerminal := lt
      ulLength := a
      lrLength := b
      ul := ul
      lr := lr
      ur := ur
      ll := ll
      outer_order := h.2.1
      ul_enumerates := h.2.2.1
      lr_enumerates := h.2.2.2.1
      ur_missing := h.2.2.2.2.1
      ll_missing := h.2.2.2.2.2
      ur_walk := (isBoundaryDartWalk_iff_endpoints_and_isChain M _ _ _).mpr ⟨hur, hUR⟩
      ll_walk := (isBoundaryDartWalk_iff_endpoints_and_isChain M _ _ _).mpr ⟨hll, hLL⟩ }⟩

namespace FiniteBoundaryDecomposition

/-- the dart lists are unique for fixed cuts in a common outer word. The first
cut is `k`; the next three cuts are determined by the common UL, UR and LR
lengths. Thus this applies in particular when the junction labels are also
fixed. It does not assert uniqueness from vertex labels alone and does not
assume that the outer boundary is a simple vertex cycle. -/
theorem blocks_eq_of_same_cuts (C C' : FiniteBoundaryDecomposition M)
    (hW : C.outerWord.letters = C'.outerWord.letters) (k : ℕ)
    (hcut : C.outerWord.letters.rotate k =
      C.ul.darts ++ C.ur ++ (C.lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ C.ll)
    (hcut' : C'.outerWord.letters.rotate k =
      C'.ul.darts ++ C'.ur ++
        (C'.lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ C'.ll)
    (hul : C.ulLength = C'.ulLength)
    (hur : C.ur.length = C'.ur.length)
    (hlr : C.lrLength = C'.lrLength) :
    C.ul.darts = C'.ul.darts ∧ C.lr.darts = C'.lr.darts ∧
      C.ur = C'.ur ∧ C.ll = C'.ll := by
  have h : C.ul.darts ++ C.ur ++
        (C.lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ C.ll =
      C'.ul.darts ++ C'.ur ++
        (C'.lr.darts.reverse.map M.toCombinatorialMap.edgeInv) ++ C'.ll := by
    rw [← hcut, hW, hcut']
  simp only [List.append_assoc] at h
  obtain ⟨hUL, htail⟩ := List.append_inj h (by
    rw [C.ul.darts_length, C'.ul.darts_length, hul])
  obtain ⟨hUR, htail'⟩ := List.append_inj htail hur
  obtain ⟨hLR, hLL⟩ := List.append_inj htail' (by
    simp only [List.length_map, List.length_reverse,
      C.lr.darts_length, C'.lr.darts_length, hlr])
  have hLR' : C.lr.darts = C'.lr.darts := by
    apply List.reverse_injective
    exact (List.map_injective_iff.mpr M.toCombinatorialMap.edgeInv.injective) hLR
  exact ⟨hUL, hLR', hUR, hLL⟩

end FiniteBoundaryDecomposition

namespace BipolarMapWithBoundaryBase

/-- the no-missing bipolar specialization retains the supplied left and right
paths, with source and sink as their initial and terminal junctions. -/
@[expose] def toFiniteBoundaryDecomposition {ℓ r : ℕ}
    (B : BipolarMapWithBoundaryBase D ℓ r) : FiniteBoundaryDecomposition B.map :=
  { outerWord := B.outerWord
    outerCycle := B.outerSplit.1
    ulInitial := B.source
    ulTerminal := B.sink
    lrInitial := B.source
    lrTerminal := B.sink
    ulLength := ℓ
    lrLength := r
    ul := B.leftPath
    lr := B.rightPath
    ur := []
    ll := []
    outer_order := B.outerSplit.2.1
    ul_enumerates := B.outerSplit.2.2.1
    lr_enumerates := B.outerSplit.2.2.2.1
    ur_missing := B.outerSplit.2.2.2.2.1
    ll_missing := B.outerSplit.2.2.2.2.2
    ur_walk := rfl
    ll_walk := rfl }

/-- a no-missing bipolar map admits a decomposition with the exact supplied
boundary paths, empty missing runs, and all four specified pole junctions.
No hypothesis beyond the bipolar carrier is required. -/
theorem exists_finiteBoundaryDecomposition {ℓ r : ℕ}
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    ∃ C : FiniteBoundaryDecomposition B.map,
      C.ur = [] ∧ C.ll = [] ∧
      C.ul.darts = B.leftPath.darts ∧ C.lr.darts = B.rightPath.darts ∧
      C.ulInitial = B.source ∧ C.lrInitial = B.source ∧
      C.ulTerminal = B.sink ∧ C.lrTerminal = B.sink :=
  ⟨B.toFiniteBoundaryDecomposition, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BipolarMapWithBoundaryBase

end DirectedDistances.PlanarMap
