/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.Basic
public import Init.Omega

/-! # Graph-level boundary prefix reversal

This is the graph-level core of Lemma `lem-bdy-reverse`
left-edge hypothesis records the graph-level shadow of the left boundary.
Planar boundary preservation and the bijection on map classes are not proved
here; this is a helper result only, not counted as the paper lemma. The
left-edge hypothesis H4 (`hleft` in `boundaryFlip_bipolar`) must be PRODUCED
from the planar carrier, by
`BipolarTriangulationWithBoundary.firstLeftEdge_leavesSource_and_differs_from_firstRight`,
and not assumed in a paper root.

Vertices and edges are separate types, and edges are identified by their
elements of `E`, so parallel edges are retained.  `Acyclic` is expressed by
a natural-valued topological ranking of the vertices; no finiteness of `V`
is assumed, and the equivalence with the absence of directed cycles is not
proved here. `Bipolar` does not include acyclicity, so consumers conjoin
`boundaryFlip_acyclic`. The `[Fintype E]` instances are unused. -/

public section
namespace DirectedDistances.DirectedPath
open Classical

/- A directed multigraph orientation, with edge identity kept in `E`. -/
@[ext] structure Orientation (V E : Type*) where
  src : E → V
  tgt : E → V

@[expose] def HasIncoming {V E : Type*} (O : Orientation V E) (v : V) : Prop :=
  ∃ e, O.tgt e = v

@[expose] def HasOutgoing {V E : Type*} (O : Orientation V E) (v : V) : Prop :=
  ∃ e, O.src e = v

/- A bounded topological numbering; boundedness is automatic for a finite
vertex type and is useful when constructing the numbering after the flip. -/
@[expose] def Acyclic {V E : Type*} (O : Orientation V E) : Prop :=
  ∃ cap : ℕ, ∃ rank : V → ℕ,
    (∀ v, rank v ≤ cap) ∧ (∀ e, rank (O.src e) < rank (O.tgt e))

/- A simple right-boundary path `vertex 0, ..., vertex r`, with edge `edge i`
joining vertices `i` and `i+1`. The functions are total for convenient
indexing; path facts are asserted on the specified finite range. -/
structure BoundaryPath {V E : Type*} (O : Orientation V E) (r : ℕ) where
  vertex : ℕ → V
  edge : ℕ → E
  vertex_injective : ∀ i j, i ≤ r → j ≤ r → vertex i = vertex j → i = j
  edge_injective : ∀ i j, i < r → j < r → edge i = edge j → i = j
  edge_src : ∀ i, i < r → O.src (edge i) = vertex i
  edge_tgt : ∀ i, i < r → O.tgt (edge i) = vertex (i + 1)

/- H2: `source` is the unique vertex with no incoming edge, `sink` is the
unique vertex with no outgoing edge. These clauses also give every other
vertex both an incoming and an outgoing edge. -/
@[expose] def Bipolar {V E : Type*} (O : Orientation V E) (source sink : V) : Prop :=
  (¬ HasIncoming O source) ∧
  (∀ v, v ≠ source → HasIncoming O v) ∧
  (¬ HasOutgoing O sink) ∧
  (∀ v, v ≠ sink → HasOutgoing O v)

/- H3: the source has no incoming edge, and each interior right-boundary
vertex has no incoming edge except its preceding boundary edge. -/
@[expose] def BoundaryChanneled {V E : Type*} {r : ℕ}
    (O : Orientation V E) (p : BoundaryPath O r) : Prop :=
  (∀ e, O.tgt e ≠ p.vertex 0) ∧
  (∀ i, 0 < i → i < r → ∀ e, O.tgt e = p.vertex i → e = p.edge (i - 1))

@[expose] def IsFlipped {E : Type*} (edge : ℕ → E) (k : ℕ) (e : E) : Prop :=
  ∃ i, i < k ∧ edge i = e

@[expose] def IsPrefixVertex {V : Type*} (vertex : ℕ → V) (k : ℕ) (v : V) : Prop :=
  ∃ i, i ≤ k ∧ vertex i = v

@[expose] noncomputable def flipEdges {V E : Type*} (O : Orientation V E)
    (edge : ℕ → E) (k : ℕ) : Orientation V E := by
  classical
  exact {
    src := fun e => if IsFlipped edge k e then O.tgt e else O.src e
    tgt := fun e => if IsFlipped edge k e then O.src e else O.tgt e
  }

@[expose] noncomputable def flipPrefix {V E : Type*} (O : Orientation V E)
    {r : ℕ} (p : BoundaryPath O r) (k : ℕ) : Orientation V E := by
  classical
  exact flipEdges O p.edge k

private theorem flipped_src_tgt {V E : Type*} {O : Orientation V E} {r k : ℕ}
    (p : BoundaryPath O r) (hk : k < r) {e : E} (h : IsFlipped p.edge k e) :
    ∃ i, i < k ∧ (flipPrefix O p k).src e = p.vertex (i + 1) ∧
      (flipPrefix O p k).tgt e = p.vertex i := by
  rcases h with ⟨i, hik, rfl⟩
  have hir : i < r := by omega
  have hflip : IsFlipped p.edge k (p.edge i) := ⟨i, hik, rfl⟩
  refine ⟨i, hik, ?_, ?_⟩
  · change (if IsFlipped p.edge k (p.edge i) then O.tgt (p.edge i) else O.src (p.edge i)) = _
    rw [ite_eq_left hflip]
    exact p.edge_tgt i hir
  · change (if IsFlipped p.edge k (p.edge i) then O.src (p.edge i) else O.tgt (p.edge i)) = _
    rw [ite_eq_left hflip]
    exact p.edge_src i hir

private theorem not_flipped_src_tgt {V E : Type*} {O : Orientation V E} {r k : ℕ}
    (p : BoundaryPath O r) {e : E} (h : ¬ IsFlipped p.edge k e) :
    (flipPrefix O p k).src e = O.src e ∧ (flipPrefix O p k).tgt e = O.tgt e := by
  simp [flipPrefix, flipEdges, h]

/- The prefix can have an incoming edge only from outside the prefix if the
original boundary-channel condition fails. -/
private theorem no_edge_external_to_prefix {V E : Type*} {O : Orientation V E}
    {r k : ℕ} (p : BoundaryPath O r) (hk : k < r)
    (hchan : BoundaryChanneled O p) {e : E}
    (hs : ¬ IsPrefixVertex p.vertex k ((flipPrefix O p k).src e))
    (ht : IsPrefixVertex p.vertex k ((flipPrefix O p k).tgt e)) : False := by
  by_cases hf : IsFlipped p.edge k e
  · obtain ⟨i, hik, hsrc, _⟩ := flipped_src_tgt p hk hf
    apply hs
    exact ⟨i + 1, by omega, hsrc.symm⟩
  · obtain ⟨j, hjk, hj⟩ := ht
    have hsrcTgt := not_flipped_src_tgt p hf
    have htarget : O.tgt e = p.vertex j := hsrcTgt.2.symm.trans hj.symm
    by_cases hj0 : j = 0
    · subst j
      exact hchan.1 e htarget
    · have hjr : j < r := by omega
      have he := hchan.2 j (by omega) hjr e htarget
      subst e
      have hsrcEq : (flipPrefix O p k).src (p.edge (j - 1)) = p.vertex (j - 1) := by
        exact hsrcTgt.1.trans (p.edge_src (j - 1) (by omega))
      apply hs
      exact ⟨j - 1, by omega, hsrcEq.symm⟩

private theorem prefix_edge_is_flipped {V E : Type*} {O : Orientation V E}
    {r k : ℕ} (p : BoundaryPath O r) (hk : k < r)
    (hchan : BoundaryChanneled O p) {e : E}
    (ht : IsPrefixVertex p.vertex k ((flipPrefix O p k).tgt e)) : IsFlipped p.edge k e := by
  by_contra hf
  obtain ⟨j, hjk, hj⟩ := ht
  have hsame := not_flipped_src_tgt p hf
  have htarget : O.tgt e = p.vertex j := hsame.2.symm.trans hj.symm
  by_cases hj0 : j = 0
  · subst j
    exact hchan.1 e htarget
  · have hjr : j < r := by omega
    have he := hchan.2 j (by omega) hjr e htarget
    subst e
    apply hf
    exact ⟨j - 1, by omega, rfl⟩

/- T1: acyclicity is preserved by reversing a right-boundary prefix. -/
/-- The prefix reversal in Lemma `lem-bdy-reverse` preserves acyclicity at the -/
theorem boundaryFlip_acyclic {V E : Type*} [Fintype E] {r k : ℕ}
    (O : Orientation V E) (p : BoundaryPath O r)
    (hacyc : Acyclic O) (hchan : BoundaryChanneled O p)
    (hk0 : 1 ≤ k) (hkr : k ≤ r - 1) :
    Acyclic (flipPrefix O p k) := by
  rcases hacyc with ⟨cap, rank, hbound, hrank⟩
  have hk : k < r := by omega
  let rank' : V → ℕ := fun v =>
    if IsPrefixVertex p.vertex k v then cap - rank v else cap + 1 + rank v
  refine ⟨2 * cap + 1, rank', ?_, ?_⟩
  · intro v
    by_cases hp : IsPrefixVertex p.vertex k v
    · simp [rank', hp]
      omega
    · simp [rank', hp]
      have hb := hbound v
      omega
  · intro e
    by_cases hs : IsPrefixVertex p.vertex k ((flipPrefix O p k).src e)
    · by_cases ht : IsPrefixVertex p.vertex k ((flipPrefix O p k).tgt e)
      · have hf := prefix_edge_is_flipped p hk hchan (e := e) ht
        obtain ⟨i, hik, hsrc, htgt⟩ := flipped_src_tgt p hk hf
        have hi : i < r := by omega
        have hold := hrank (p.edge i)
        rw [p.edge_src i hi, p.edge_tgt i hi] at hold
        have hps : IsPrefixVertex p.vertex k (p.vertex (i + 1)) := by
          rw [← hsrc]
          exact hs
        have hpt : IsPrefixVertex p.vertex k (p.vertex i) := by
          rw [← htgt]
          exact ht
        rw [hsrc, htgt]
        simp [rank', hps, hpt]
        have hb := hbound (p.vertex (i + 1))
        have hb' := hbound (p.vertex i)
        omega
      · simp [rank', hs, ht]
        have hb := hbound ((flipPrefix O p k).src e)
        omega
    · by_cases ht : IsPrefixVertex p.vertex k ((flipPrefix O p k).tgt e)
      · exact False.elim (no_edge_external_to_prefix p hk hchan hs ht)
      · have hf : ¬ IsFlipped p.edge k e := by
          intro hflip
          obtain ⟨i, hik, hsrc, _⟩ := flipped_src_tgt p hk hflip
          apply hs
          exact ⟨i + 1, by omega, hsrc.symm⟩
        have he := not_flipped_src_tgt p hf
        simp [rank', hs, ht]
        rw [he.1, he.2]
        exact hrank e

/- T2: the left-boundary shadow keeps x_0 from becoming a sink. -/
/-- If `O` is bipolar from `x_0` to `x_r` (`hbip`), boundary-channeled
(`hchan`), and has an outgoing edge at `x_0` other than the first right
boundary edge (`hleft`, H4), then the flipped orientation is bipolar with
source `x_k` and sink `x_r`. In particular it has no incoming edge at `x_k`,
the unique sink is `x_r`, and all other vertices have both an incoming and an
outgoing edge. The edge in H4 is the graph-level shadow of the left boundary;
it must be produced from the planar carrier
(`BipolarTriangulationWithBoundary.firstLeftEdge_leavesSource_and_differs_from_firstRight`),
not assumed in a paper root. Helper; not counted in the paper inventory. -/
theorem boundaryFlip_bipolar {V E : Type*} [Fintype E] {r k : ℕ}
    (O : Orientation V E) (p : BoundaryPath O r)
    (hbip : Bipolar O (p.vertex 0) (p.vertex r))
    (hchan : BoundaryChanneled O p)
    (hleft : ∃ e, e ≠ p.edge 0 ∧ O.src e = p.vertex 0)
    (hk0 : 1 ≤ k) (hkr : k ≤ r - 1) :
    Bipolar (flipPrefix O p k) (p.vertex k) (p.vertex r) := by
  have hk : k < r := by omega
  rcases hbip with ⟨hsourceIn, hsourceUnique, hsinkOut, hsinkUnique⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hin
    rcases hin with ⟨e, he⟩
    by_cases hf : IsFlipped p.edge k e
    · obtain ⟨i, hik, _, htgt⟩ := flipped_src_tgt p hk hf
      have heq : p.vertex i = p.vertex k := htgt.symm.trans he
      have : i = k := p.vertex_injective i k (by omega) (by omega) heq
      omega
    · have heq : O.tgt e = p.vertex k := by
        simpa [flipPrefix, flipEdges, hf] using he
      have he' := hchan.2 k (by omega) hk e heq
      subst e
      have hflip : IsFlipped p.edge k (p.edge (k - 1)) := ⟨k - 1, by omega, rfl⟩
      exact hf hflip
  · intro v hv
    by_cases hp : IsPrefixVertex p.vertex k v
    · obtain ⟨i, hik, hi⟩ := hp
      have hik' : i ≠ k := by
        intro heq
        subst i
        exact hv hi.symm
      have hil : i < k := by omega
      refine ⟨p.edge i, ?_⟩
      have hflip : IsFlipped p.edge k (p.edge i) := ⟨i, hil, rfl⟩
      simp [flipPrefix, flipEdges, hflip, p.edge_src i (by omega), hi]
    · rcases hsourceUnique v (by
        intro hv0
        apply hp
        exact ⟨0, by omega, hv0.symm⟩) with ⟨e, he⟩
      have hf : ¬ IsFlipped p.edge k e := by
        intro hflip
        obtain ⟨i, hik, hsrc, _⟩ := flipped_src_tgt p hk hflip
        have hsrcOld : (flipPrefix O p k).src e = O.tgt e := by
          simp [flipPrefix, flipEdges, hflip]
        apply hp
        exact ⟨i + 1, by omega, hsrc.symm.trans (hsrcOld.trans he)⟩
      refine ⟨e, ?_⟩
      simpa [flipPrefix, flipEdges, hf] using he
  · intro hout
    rcases hout with ⟨e, he⟩
    by_cases hf : IsFlipped p.edge k e
    · obtain ⟨i, hik, hsrc, _⟩ := flipped_src_tgt p hk hf
      have heq : p.vertex (i + 1) = p.vertex r := hsrc.symm.trans he
      have : i + 1 = r := p.vertex_injective (i + 1) r (by omega) (by omega) heq
      omega
    · have heq : O.src e = p.vertex r := by
        simpa [flipPrefix, flipEdges, hf] using he
      exact hsinkOut ⟨e, heq⟩
  · intro v hv
    by_cases hp : IsPrefixVertex p.vertex k v
    · obtain ⟨i, hik, hi⟩ := hp
      by_cases hi0 : i = 0
      · subst i
        rcases hleft with ⟨e, heNe, hesrc⟩
        have hf : ¬ IsFlipped p.edge k e := by
          intro hflip
          obtain ⟨j, hjk, hje⟩ := hflip
          have hsrcEq : p.vertex j = p.vertex 0 := by
            calc
              p.vertex j = O.src (p.edge j) := (p.edge_src j (by omega)).symm
              _ = O.src e := congrArg O.src hje
              _ = p.vertex 0 := hesrc
          have : j = 0 := p.vertex_injective j 0 (by omega) (by omega) hsrcEq
          subst j
          exact heNe hje.symm
        refine ⟨e, ?_⟩
        simpa [flipPrefix, flipEdges, hf] using hesrc.trans hi
      · have hil : i - 1 < k := by omega
        refine ⟨p.edge (i - 1), ?_⟩
        have hflip : IsFlipped p.edge k (p.edge (i - 1)) := ⟨i - 1, hil, rfl⟩
        simp [flipPrefix, flipEdges, hflip, p.edge_tgt (i - 1) (by omega)]
        have hidx : i - 1 + 1 = i := by omega
        rw [hidx]
        exact hi
    · rcases hsinkUnique v hv with ⟨e, he⟩
      have hf : ¬ IsFlipped p.edge k e := by
        intro hflip
        obtain ⟨i, hik, _, htgt⟩ := flipped_src_tgt p hk hflip
        apply hp
        have htgtOld : (flipPrefix O p k).tgt e = O.src e := by
          simp [flipPrefix, flipEdges, hflip]
        exact ⟨i, by omega, htgt.symm.trans (htgtOld.trans he)⟩
      refine ⟨e, ?_⟩
      simpa [flipPrefix, flipEdges, hf] using he

/- T3: applying the same orientation reversal twice restores the orientation. -/
/-- Reversing the same edge prefix twice is the identity orientation. -/
theorem flipPrefix_involutive {V E : Type*} [Fintype E] (O : Orientation V E)
    (edge : ℕ → E) (k : ℕ) :
    flipEdges (flipEdges O edge k) edge k = O := by
  ext e <;> by_cases h : IsFlipped edge k e <;> simp [flipEdges, h]

/- A concrete instance showing that H4 cannot be omitted from T2. -/
inductive CounterVertex where
  | x0 | x1 | x2
  deriving DecidableEq

instance : Fintype CounterVertex :=
  Fintype.ofList [.x0, .x1, .x2] (by intro v; cases v <;> simp)

inductive CounterEdge where
  | b0 | b1
  deriving DecidableEq

instance : Fintype CounterEdge :=
  Fintype.ofList [.b0, .b1] (by intro e; cases e <;> simp)

@[expose] def counterOrientation : Orientation CounterVertex CounterEdge where
  src
    | .b0 => .x0
    | .b1 => .x1
  tgt
    | .b0 => .x1
    | .b1 => .x2

@[expose] def counterPath : BoundaryPath counterOrientation 2 where
  vertex i := if i = 0 then .x0 else if i = 1 then .x1 else .x2
  edge i := if i = 0 then .b0 else .b1
  vertex_injective := by
    intro i j hi hj heq
    interval_cases i <;> interval_cases j <;> simp_all
  edge_injective := by
    intro i j hi hj heq
    interval_cases i <;> interval_cases j <;> simp_all
  edge_src := by
    intro i hi
    interval_cases i <;> rfl
  edge_tgt := by
    intro i hi
    interval_cases i <;> rfl

private theorem counterAcyclic : Acyclic counterOrientation := by
  refine ⟨2, (fun v => match v with | .x0 => 0 | .x1 => 1 | .x2 => 2), ?_, ?_⟩
  · intro v
    cases v <;> norm_num
  · intro e
    cases e <;> norm_num [counterOrientation]

private theorem counterBipolar :
    Bipolar counterOrientation .x0 .x2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨e, he⟩
    cases e <;> simp [counterOrientation] at he
  · intro v hv
    cases v
    · exact (hv rfl).elim
    · exact ⟨.b0, by simp [counterOrientation]⟩
    · exact ⟨.b1, by simp [counterOrientation]⟩
  · rintro ⟨e, he⟩
    cases e <;> simp [counterOrientation] at he
  · intro v hv
    cases v
    · exact ⟨.b0, by simp [counterOrientation]⟩
    · exact ⟨.b1, by simp [counterOrientation]⟩
    · exact (hv rfl).elim

private theorem counterBoundaryChanneled :
    BoundaryChanneled counterOrientation counterPath := by
  constructor
  · intro e
    cases e <;> simp [counterOrientation, counterPath]
  · intro i hi0 hir e he
    have hi : i = 1 := by omega
    subst i
    cases e <;> simp [counterOrientation, counterPath] at he ⊢

/- The statement packages H1--H3 and the failure of the outgoing-edge clause
in T2, for the three-vertex path with no left-boundary edge. -/
/-- H4 (`hleft` of `boundaryFlip_bipolar`) is necessary: this three-vertex
directed path is acyclic, bipolar and boundary-channeled, but after flipping
its first right-boundary edge `x₀` has no outgoing edge. Helper; not counted
in the paper inventory. -/
theorem counterexample_without_H4 :
    Acyclic counterOrientation ∧
    Bipolar counterOrientation .x0 .x2 ∧
    BoundaryChanneled counterOrientation counterPath ∧
    (¬ ∃ e, e ≠ counterPath.edge 0 ∧
      counterOrientation.src e = counterPath.vertex 0) ∧
    ¬ HasOutgoing (flipPrefix counterOrientation counterPath 1) .x0 := by
  refine ⟨counterAcyclic, counterBipolar, counterBoundaryChanneled, ?_, ?_⟩
  · rintro ⟨e, hne, hsrc⟩
    cases e <;> simp [counterPath, counterOrientation] at hne hsrc
  · rintro ⟨e, he⟩
    cases e <;> simp [flipPrefix, flipEdges, IsFlipped, counterPath, counterOrientation] at he

end DirectedDistances.DirectedPath
