/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder3





































public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: the map-determined external geometric
boundary darts, with both traversal bits retained. -/
@[expose] def externalBoundaryDartSet4 (M : DirectedPlaneMapWithMissing V E) :
    Set (E × Bool) := {d | ExternalFrontierEdge M d.1}

/-- Helper toward Definition 3.2: counting both traversal bits does not
change whether the map's external boundary is finite. -/
theorem externalBoundaryDartSet4_finite_iff
    (M : DirectedPlaneMapWithMissing V E) :
    (externalBoundaryDartSet4 M).Finite ↔
      Set.Finite {e : E | ExternalFrontierEdge M e} := by
  constructor
  · intro h
    apply (h.image Prod.fst).subset
    intro e he
    exact ⟨(e, false), he, rfl⟩
  · intro h
    apply ((h.image (fun e => (e, false))).union
      (h.image (fun e => (e, true)))).subset
    rintro ⟨e, b⟩ he
    cases b with
    | false => exact Or.inl ⟨e, he, rfl⟩
    | true => exact Or.inr ⟨e, he, rfl⟩

/-- Helper toward Definition 3.2: successor modulo the length of a finite
cycle; the empty cycle needs no successor value. -/
@[expose] def boundaryCycleSucc4 {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.is_lt)⟩

/-- Helper toward Definition 3.2: position measured forward from a cyclic cut. -/
@[expose] def boundaryCycleOffset4 {n : ℕ} (cut i : Fin n) : ℕ :=
  (i.val + n - cut.val) % n

/-- Helper toward Definition 3.2: the linear successor stops at the last
position of a side, while the geometric cyclic successor still wraps. -/
@[expose] def boundaryLinearNext4 {n : ℕ} (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

/-- Helper toward Definition 3.2: at this cut the four side tags are
nondecreasing; each side is one interval and empty sides are allowed. -/
@[expose] def IsCyclicSideWordAt4 {n : ℕ} (tag : Fin n → Fin 4)
    (cut : Fin n) : Prop :=
  ∀ i j, boundaryCycleOffset4 cut i ≤ boundaryCycleOffset4 cut j →
    (tag i).val ≤ (tag j).val

/-- Helper toward Definition 3.2: a finite cyclic word consists of four
cyclic intervals in UL–UR–LR–LL order. A sole side may cover the whole cycle. -/
@[expose] def IsCyclicSideWord4 {n : ℕ} (tag : Fin n → Fin 4) : Prop :=
  n = 0 ∨ ∃ cut, IsCyclicSideWordAt4 tag cut

/-- Helper toward Definition 3.2: finite cyclic positions enumerate all
listed darts exactly once. The geometric successor wraps; within-side steps
advance in the linear block order and stop at its endpoint, even for a sole
nonempty side. The same cut controls block order and supplied side steps. -/
@[expose] def FiniteBoundaryPositionOrder4
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (S : E × Bool → E × Bool) : Prop :=
  ∃ n : ℕ, ∃ position : InfiniteBoundaryDartIndex P ≃ Fin n,
    (∀ i j, S (InfiniteBoundaryDartIndex.dart P i) =
        InfiniteBoundaryDartIndex.dart P j ↔
      position j = boundaryCycleSucc4 (position i)) ∧
    (n = 0 ∨ ∃ cut : Fin n,
      IsCyclicSideWordAt4 (fun p => sideTag P (position.symm p)) cut ∧
      ∀ i j, sideNext P i = some j ↔
        sideTag P i = sideTag P j ∧
        boundaryCycleOffset4 cut (position j) =
          boundaryCycleOffset4 cut (position i) + 1)

/-- Helper toward Definition 3.2: at a finite closing junction a side may
be its own next nonempty side, in which case all other three sides are empty
zero-edge paths at this same junction. -/
@[expose] def RequiredFiniteBoundaryJoinEndpointLabels4
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (S : E × Bool → E × Bool) : Prop :=
  ∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    sideNext P i = none →
    let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)
    sideTerminalVertex? P (sideTag P i) = some v ∧
      sideInitialVertex? P (sideTag P j) = some v ∧
      ∀ k : Fin 4,
        0 < sideDistance (sideTag P i) k →
        sideDistance (sideTag P i) k <
          (if sideTag P i = sideTag P j then 4
            else sideDistance (sideTag P i) (sideTag P j)) →
        sideInitialVertex? P k = some v ∧ sideTerminalVertex? P k = some v

/-- Helper toward Definition 3.2: the exact retained labels when both
present paths are empty at supplied finite junctions. UL is the zero-edge
path at `a`, LR the zero-edge path at `b`; no inequality between them is
required. LR is listed in reverse directed traversal, so UR joins UL's
terminal to LR's listed initial, and LL joins LR's listed terminal to UL's
initial. Empty missing sides additionally force their own endpoints equal
through the separately retained endpoint-validity clauses. -/
@[expose] def EmptyFiniteBoundaryLabels4
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  ∃ a b : V,
    P.upperLeft.initialVertex? = some a ∧
    P.upperLeft.terminalVertex? = some a ∧
    P.lowerRight.initialVertex? = some b ∧
    P.lowerRight.terminalVertex? = some b ∧
    P.upperRight.initialVertex? = some a ∧
    P.upperRight.terminalVertex? = some b ∧
    P.lowerLeft.initialVertex? = some b ∧
    P.lowerLeft.terminalVertex? = some a





@[expose] def RequiredEmptyFiniteBoundaryLabels4
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) : Prop :=
  IsEmpty (InfiniteBoundaryDartIndex P) →
    (∃ v : V, G.pos v ∈ frontier U.val) → EmptyFiniteBoundaryLabels4 P

/-- Helper toward Definition 3.2: finite geometric coverage and side
conditions, without the v1 different-side transition rule that excludes a
sole block. All geometric successor steps join vertices, including closure. -/
@[expose] def IsFiniteExternalFaceIntervalOrder4
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsBoundaryOrderOfInf M P ∧
  (∀ d, G.dartBorders d U ↔
    ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d) ∧
  Function.Injective (InfiniteBoundaryDartIndex.dart P) ∧
  IsGeometricExternalFaceSucc G U S ∧
  ULOkInf P ∧ UROkInf P ∧ LROkInf P ∧ LLOkInf P ∧
  IsSimpleBoundarySide M P.upperLeft ∧ IsSimpleBoundarySide M P.lowerRight ∧
  BoundarySideEndpointLabels M P.upperLeft ∧
  BoundarySideEndpointLabels M P.upperRight ∧
  BoundarySideEndpointLabels M P.lowerRight ∧
  BoundarySideEndpointLabels M P.lowerLeft ∧
  FiniteBoundaryPositionOrder4 P S ∧
  (∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
      boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)) ∧
  RequiredFiniteBoundaryJoinEndpointLabels4 P S ∧
  RequiredEmptyFiniteBoundaryLabels4 P G U

/-- Helper toward Definition 3.2: the finite/infinite alternative is fixed
by finiteness of the map's external boundary darts, rather than a free flag.
The infinite branch retains precisely v3's requirements. -/
@[expose] def IsExternalFaceIntervalOrder4
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  ((externalBoundaryDartSet4 M).Finite ∧
    IsFiniteExternalFaceIntervalOrder4 M P G U S) ∨
  (¬ (externalBoundaryDartSet4 M).Finite ∧
    IsExternalFaceIntervalOrder3 M P G U S)

namespace IsFiniteExternalFaceIntervalOrder4

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}



theorem empty_boundary_labels
    (h : IsFiniteExternalFaceIntervalOrder4 M P G U S)
    [IsEmpty (InfiniteBoundaryDartIndex P)]
    (hv : ∃ v : V, G.pos v ∈ frontier U.val) :
    EmptyFiniteBoundaryLabels4 P := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlabels⟩
  exact hlabels inferInstance hv

end IsFiniteExternalFaceIntervalOrder4

namespace IsExternalFaceIntervalOrder4

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: both branches retain map boundary
coverage and exact exterior-facing dart coverage. -/
theorem boundary_coverage (h : IsExternalFaceIntervalOrder4 M P G U S) :
    IsBoundaryOrderOfInf M P ∧
      (∀ d, G.dartBorders d U ↔
        ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d) := by
  rcases h with ⟨_, hf⟩ | ⟨_, hi⟩
  · exact ⟨hf.1, hf.2.1⟩
  · exact ⟨hi.1.1.1, hi.1.1.2.1⟩

/-- Helper toward Definition 3.2: on data satisfying v4, the map-determined
branch agrees with finiteness of the actual exterior-facing dart set in the
supplied drawing. This only uses the retained coverage clauses. -/
theorem finite_iff_exterior_darts_finite
    (h : IsExternalFaceIntervalOrder4 M P G U S) :
    (externalBoundaryDartSet4 M).Finite ↔
      Set.Finite {d : E × Bool | G.dartBorders d U} := by
  rcases h.boundary_coverage with ⟨hmap, hcover⟩
  have hedge := (IsBoundaryOrderOfInf_iff P).mp hmap
  constructor
  · intro hfinite
    apply hfinite.subset
    intro d hd
    rcases (hcover d).mp hd with ⟨i, hi⟩
    exact (hedge.1 d.1).mp ⟨i, congrArg Prod.fst hi⟩
  · intro hfinite
    apply (externalBoundaryDartSet4_finite_iff M).mpr
    apply (hfinite.image Prod.fst).subset
    intro e he
    rcases (hedge.1 e).mpr he with ⟨i, hi⟩
    exact ⟨InfiniteBoundaryDartIndex.dart P i,
      (hcover _).mpr ⟨i, rfl⟩, hi⟩

/-- Helper toward Definition 3.2: on an infinite external boundary, v4
projects to all of v3 without changing any of its clauses. -/
theorem toIsExternalFaceIntervalOrder3
    (h : IsExternalFaceIntervalOrder4 M P G U S)
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder3 M P G U S := by
  rcases h with ⟨hfinite, _⟩ | ⟨_, h3⟩
  · exact (hinfinite hfinite).elim
  · exact h3

/-- Helper toward Definition 3.2: on a finite external boundary, v4
projects to the finite cyclic clauses. -/
theorem toIsFiniteExternalFaceIntervalOrder4
    (h : IsExternalFaceIntervalOrder4 M P G U S)
    (hfinite : (externalBoundaryDartSet4 M).Finite) :
    IsFiniteExternalFaceIntervalOrder4 M P G U S := by
  rcases h with ⟨_, h4⟩ | ⟨hinfinite, _⟩
  · exact h4
  · exact (hinfinite hfinite).elim

/-- Helper toward Definition 3.2: the infinite branch is precisely v3. -/
theorem infinite_iff (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder4 M P G U S ↔
      IsExternalFaceIntervalOrder3 M P G U S := by
  exact ⟨fun h => h.toIsExternalFaceIntervalOrder3 hinfinite,
    fun h => Or.inr ⟨hinfinite, h⟩⟩

/-- Helper toward Definition 3.2: the finite branch is precisely the
finite cyclic predicate, with no freely chosen case flag. -/
theorem finite_iff (hfinite : (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder4 M P G U S ↔
      IsFiniteExternalFaceIntervalOrder4 M P G U S := by
  exact ⟨fun h => h.toIsFiniteExternalFaceIntervalOrder4 hfinite,
    fun h => Or.inl ⟨hfinite, h⟩⟩

end IsExternalFaceIntervalOrder4

/-- Helper toward Definition 3.2: a finite cycle consisting solely of UL
has the required cyclic interval order, for every length including zero. -/
theorem isCyclicSideWord4_sole_ul (n : ℕ) :
    IsCyclicSideWord4 (fun _ : Fin n => (0 : Fin 4)) := by
  by_cases hn : n = 0
  · exact Or.inl hn
  · refine Or.inr ⟨⟨0, Nat.pos_of_ne_zero hn⟩, ?_⟩
    intro i j _
    exact Nat.le_refl 0

/-- Helper toward Definition 3.2: the last position of every nonempty
finite cycle wraps to zero, also when UL occupies the whole cycle. -/
theorem boundaryCycleSucc4_last (n : ℕ) :
    boundaryCycleSucc4 (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) =
      (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) := by
  apply Fin.ext
  exact Nat.mod_self (n + 1)

/-- Helper toward Definition 3.2: at cut zero, cyclic offsets recover
the usual positions. -/
theorem boundaryCycleOffset4_zero {n : ℕ} (hn : 0 < n) (i : Fin n) :
    boundaryCycleOffset4 (⟨0, hn⟩ : Fin n) i = i.val := by
  simp only [boundaryCycleOffset4, Nat.sub_zero, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.is_lt]

/-- Helper toward Definition 3.2: a linear successor exists exactly at
consecutive positions, excluding the closing geometric step. -/
theorem boundaryLinearNext4_eq_some_iff {n : ℕ} (i j : Fin n) :
    boundaryLinearNext4 i = some j ↔ j.val = i.val + 1 := by
  unfold boundaryLinearNext4
  split_ifs with h
  · constructor
    · intro heq
      exact (congrArg Fin.val (Option.some.inj heq)).symm
    · intro heq
      exact congrArg some (Fin.ext heq.symm)
  · constructor
    · intro heq
      cases heq
    · intro heq
      have hj := j.is_lt
      omega

/-- Helper toward Definition 3.2: a sole UL block fills a nonempty finite
cycle, with precisely the required linear within-side steps, and with a
geometric closing step from the last position to zero. These are the tag,
step and wrap clauses, without asserting side simplicity or a map instance. -/
theorem sole_ul_finite_cyclic_clauses4 (n : ℕ) :
    IsCyclicSideWordAt4 (fun _ : Fin (n + 1) => (0 : Fin 4))
      ⟨0, Nat.zero_lt_succ n⟩ ∧
    (∀ i j : Fin (n + 1), boundaryLinearNext4 i = some j ↔
      (0 : Fin 4) = 0 ∧
        boundaryCycleOffset4 ⟨0, Nat.zero_lt_succ n⟩ j =
          boundaryCycleOffset4 ⟨0, Nat.zero_lt_succ n⟩ i + 1) ∧
    boundaryCycleSucc4 (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) =
      (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) := by
  refine ⟨?_, ?_, boundaryCycleSucc4_last n⟩
  · intro i j _
    exact Nat.le_refl 0
  · intro i j
    rw [boundaryCycleOffset4_zero, boundaryCycleOffset4_zero,
      boundaryLinearNext4_eq_some_iff]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

/-- Helper toward Definition 3.2: once a cyclic cut has linearized the
blocks, a side cannot recur after a different side. Repetition across the
coordinate-zero cut alone is allowed; it can be the same wrapping block. -/
theorem IsCyclicSideWordAt4.no_side_recurrence
    {n : ℕ} {tag : Fin n → Fin 4} {cut : Fin n}
    (h : IsCyclicSideWordAt4 tag cut) {i j k : Fin n}
    (hij : boundaryCycleOffset4 cut i ≤ boundaryCycleOffset4 cut j)
    (hjk : boundaryCycleOffset4 cut j ≤ boundaryCycleOffset4 cut k)
    (hends : tag i = tag k) (hmiddle : tag i ≠ tag j) : False := by
  have hle := h i j hij
  have hge := h j k hjk
  rw [← hends] at hge
  exact hmiddle (Fin.ext (Nat.le_antisymm hle hge))

/-- Helper toward Definition 3.2: the concrete cyclic word UL–UR–UL–UR
is rejected at every cut, so cyclic rotation cannot hide side recurrence. -/
theorem not_isCyclicSideWord4_alternating :
    ¬ IsCyclicSideWord4 (fun i : Fin 4 =>
      if i.val % 2 = 0 then (0 : Fin 4) else 1) := by
  unfold IsCyclicSideWord4 IsCyclicSideWordAt4 boundaryCycleOffset4
  decide

end DirectedDistances.PlanarMap
