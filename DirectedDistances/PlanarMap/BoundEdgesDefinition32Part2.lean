/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals6

/-! Finite cyclic positions and infinite integer positions both give genuine
integer intervals for the supplied missing runs. Optional endpoint labels
are retained; no finite endpoint is postulated for an unbounded run. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

private theorem offset_formula_part2 {n : ℕ} (c i : Fin n) :
    boundaryCycleOffset4 c i =
      if i.val < c.val then i.val + n - c.val else i.val - c.val := by
  by_cases hi : i.val < c.val
  · rw [ite_eq_left hi, boundaryCycleOffset4, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right hi, boundaryCycleOffset4]
    have heq : i.val + n - c.val = i.val - c.val + n := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]

private theorem offset_injective_part2 {n : ℕ} (c : Fin n) :
    Function.Injective (boundaryCycleOffset4 c) := by
  intro i j hij
  apply Fin.ext
  rw [offset_formula_part2, offset_formula_part2] at hij
  split at hij <;> split at hij <;> omega

private theorem offset_surjective_part2 {n : ℕ} (c : Fin n)
    (z : ℕ) (hz : z < n) : ∃ i : Fin n, boundaryCycleOffset4 c i = z := by
  by_cases hzc : z + c.val < n
  · refine ⟨⟨z + c.val, hzc⟩, ?_⟩
    rw [offset_formula_part2]
    split <;> dsimp only at * <;> omega
  · refine ⟨⟨z + c.val - n, by omega⟩, ?_⟩
    rw [offset_formula_part2]
    split <;> dsimp only at * <;> omega

private theorem offset_next_part2 {n : ℕ} (c i j : Fin n)
    (h : boundaryCycleOffset4 c j = boundaryCycleOffset4 c i + 1) :
    j = boundaryCycleSucc4 i := by
  apply Fin.ext
  change j.val = (i.val + 1) % n
  rw [offset_formula_part2, offset_formula_part2] at h
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    split at h <;> split at h <;> omega
  · have hi' : i.val + 1 = n := by omega
    rw [hi', Nat.mod_self]
    split at h <;> split at h <;> omega

/-- Helper toward Definition 3.2: every v7 presentation admits injective,
gapless integer coordinates with convex side blocks. Supplied successors
are exactly adjacent coordinates within a block. This includes the finite
cyclic branch, linearized at its already supplied cut. -/
theorem IsBoundEdges32.linear_positions_part2
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) :
    ∃ p : InfiniteBoundaryDartIndex B.presentation → ℤ,
      Function.Injective p ∧
      (∀ i j, sideTag B.presentation i = sideTag B.presentation j →
        (sideNext B.presentation i = some j ↔ p j = p i + 1)) ∧
      (∀ i j z, p i ≤ z → z ≤ p j → ∃ k, p k = z) ∧
      (∀ i j k, p i ≤ p j → p j ≤ p k →
        sideTag B.presentation i = sideTag B.presentation k →
          sideTag B.presentation j = sideTag B.presentation i) ∧
      (∀ i j, sideNext B.presentation i = some j →
        S (InfiniteBoundaryDartIndex.dart B.presentation i) =
          InfiniteBoundaryDartIndex.dart B.presentation j ∧
        boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation i) =
          boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation j)) := by
  by_cases hf : (externalBoundaryDartSet4 M).Finite
  · rcases (IsBoundEdges32.finite_iff hf).mp h with ⟨hc, _⟩
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpos, hjoin, _⟩
    rcases hpos with ⟨n, pos, hsucc, hn | ⟨cut, hword, hnext⟩⟩
    · subst n
      exact ⟨fun i => Fin.elim0 (pos i),
        fun i => Fin.elim0 (pos i), fun i => Fin.elim0 (pos i),
        fun i => Fin.elim0 (pos i), fun i => Fin.elim0 (pos i),
        fun i => Fin.elim0 (pos i)⟩
    · let rank := fun i => boundaryCycleOffset4 cut (pos i)
      have hbound : ∀ i, rank i < n := fun i =>
        Nat.mod_lt _ (Nat.zero_lt_of_lt cut.is_lt)
      refine ⟨fun i => (rank i : ℤ), ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        change (rank i : ℤ) = (rank j : ℤ) at hij
        exact pos.injective (offset_injective_part2 cut (Int.ofNat_inj.mp hij))
      · intro i j htag
        rw [hnext i j, and_iff_right htag]
        change rank j = rank i + 1 ↔ (rank j : ℤ) = (rank i : ℤ) + 1
        omega
      · intro i j z hiz hzj
        change (rank i : ℤ) ≤ z at hiz
        change z ≤ (rank j : ℤ) at hzj
        have hz0 : 0 ≤ z := (Int.natCast_nonneg (rank i)).trans hiz
        have hzlt : z.toNat < n := by
          have hj := hbound j
          omega
        obtain ⟨k, hk⟩ := offset_surjective_part2 cut z.toNat hzlt
        refine ⟨pos.symm k, ?_⟩
        dsimp [rank]
        rw [pos.apply_symm_apply, hk, Int.toNat_of_nonneg hz0]
      · intro i j k hij hjk htag
        change (rank i : ℤ) ≤ (rank j : ℤ) at hij
        change (rank j : ℤ) ≤ (rank k : ℤ) at hjk
        have hij' : rank i ≤ rank j := by exact_mod_cast hij
        have hjk' : rank j ≤ rank k := by exact_mod_cast hjk
        have h₁ := hword (pos i) (pos j) hij'
        have h₂ := hword (pos j) (pos k) hjk'
        simp only [pos.symm_apply_apply] at h₁ h₂
        rw [← htag] at h₂
        exact Fin.ext (by omega)
      · intro i j hstep
        have hoff := ((hnext i j).mp hstep).2
        have hS := (hsucc i j).mpr (offset_next_part2 cut (pos i) (pos j) hoff)
        exact ⟨hS, hjoin i j hS⟩
  · have h3 := ((IsBoundEdges32.infinite_iff hf).mp h).2
    obtain ⟨p, hp, hn, hg, hb, _⟩ := h3.positionOrder
    exact ⟨p, hp, hn, hg, hb, fun i j hij => h.infinite_within_side_step hf hij⟩


private theorem integer_interval_endpoints_part2
    {I : Type*} (p : I ↪ ℤ) (next : I → Option I)
    (hc : Set.OrdConnected (Set.range p))
    (hn : ∀ i j, next i = some j ↔ p j = p i + 1) :
    (∀ i, (∀ j, next j ≠ some i) ↔ ∀ j, p i ≤ p j) ∧
    (∀ i, next i = none ↔ ∀ j, p j ≤ p i) := by
  constructor
  · intro i
    constructor
    · intro hfirst j
      by_contra hij
      have hlt : p j ≤ p i - 1 := by omega
      obtain ⟨k, hk⟩ := hc.out (Set.mem_range_self j) (Set.mem_range_self i)
        ⟨hlt, (by omega : p i - 1 ≤ p i)⟩
      exact hfirst k ((hn k i).mpr (by omega))
    · intro hmin j hj
      have hstep := (hn j i).mp hj
      have hle := hmin j
      omega
  · intro i
    constructor
    · intro hlast j
      by_contra hij
      have hlt : p i + 1 ≤ p j := by omega
      obtain ⟨k, hk⟩ := hc.out (Set.mem_range_self i) (Set.mem_range_self j)
        ⟨(by omega : p i ≤ p i + 1), hlt⟩
      have hstep := (hn i k).mpr hk
      rw [hlast] at hstep
      cases hstep
    · intro hmax
      cases hi : next i with
      | none => rfl
      | some j =>
        have hstep := (hn i j).mp hi
        have hle := hmax j
        omega

/-- Helper toward Definition 3.2: the upperRight missing run is a genuine
integer interval of external-face darts, with exact geometric successor joins.
First and last indices are precisely coordinate extrema; the retained labels
are their geometric vertices. Empty and unbounded intervals are allowed. -/
theorem IsBoundEdges32.upperRight_geometric_integer_interval_part2
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) :
    ∃ p : B.presentation.upperRight.Index ↪ ℤ,
      Set.OrdConnected (Set.range p) ∧
      (∀ i j, B.presentation.upperRight.next i = some j ↔ p j = p i + 1) ∧
      (∀ i, G.dartBorders (B.presentation.upperRight.darts i) U ∧
        M.toPlaneMapWithMissing.missing (B.presentation.upperRight.darts i).1) ∧
      (∀ i j, p j = p i + 1 →
        S (B.presentation.upperRight.darts i) = B.presentation.upperRight.darts j ∧
        boundaryDartTerminal M (B.presentation.upperRight.darts i) =
          boundaryDartInitial M (B.presentation.upperRight.darts j)) ∧
      (∀ i, (∀ j, B.presentation.upperRight.next j ≠ some i) ↔ ∀ j, p i ≤ p j) ∧
      (∀ i, B.presentation.upperRight.next i = none ↔ ∀ j, p j ≤ p i) ∧
      BoundarySideEndpointLabels M B.presentation.upperRight := by
  obtain ⟨pos, hinj, hnext, hgap, hblock, hgeom⟩ := h.linear_positions_part2
  let p : B.presentation.upperRight.Index ↪ ℤ :=
    ⟨fun i => pos (.upperRight i), fun i j hij =>
      InfiniteBoundaryDartIndex.upperRight.inj (hinj hij)⟩
  have hc : Set.OrdConnected (Set.range p) := by
    constructor
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ z ⟨hiz, hzj⟩
    change pos (.upperRight i) ≤ z at hiz
    change z ≤ pos (.upperRight j) at hzj
    obtain ⟨k, hk⟩ := hgap (.upperRight i) (.upperRight j) z hiz hzj
    have htag := hblock (.upperRight i) k (.upperRight j)
      (by simpa only [hk] using hiz) (by simpa only [hk] using hzj) rfl
    cases k with
    | upperLeft k => norm_num [sideTag] at htag
    | upperRight k => exact ⟨k, hk⟩
    | lowerRight k => norm_num [sideTag] at htag
    | lowerLeft k => norm_num [sideTag] at htag
  have hn : ∀ i j, B.presentation.upperRight.next i = some j ↔ p j = p i + 1 := by
    intro i j
    change B.presentation.upperRight.next i = some j ↔
      pos (.upperRight j) = pos (.upperRight i) + 1
    have hh := hnext (.upperRight i) (.upperRight j) rfl
    simpa only [sideNext, Option.map_eq_some_iff,
      InfiniteBoundaryDartIndex.upperRight.injEq, exists_eq_right] using hh
  obtain ⟨hfirst, hlast⟩ := integer_interval_endpoints_part2 p _ hc hn
  refine ⟨p, hc, hn, ?_, ?_, hfirst, hlast, (h.endpoint_labels).2.1⟩
  · intro i
    exact ⟨(h.presentation_facts.1 _).mpr ⟨.upperRight i,
      InfiniteBoundaryDartIndex.dart_eq _ _⟩, upperRightBoundary32_missing h ⟨i, rfl⟩⟩
  · intro i j hij
    have hh := hgeom (.upperRight i) (.upperRight j) (by
      simp only [sideNext, (hn i j).mpr hij, Option.map_some])
    simpa only [InfiniteBoundaryDartIndex.dart_eq] using hh

/-- Helper toward Definition 3.2: the lowerLeft missing run is a genuine
integer interval of external-face darts, with exact geometric successor joins.
First and last indices are precisely coordinate extrema; the retained labels
are their geometric vertices. Empty and unbounded intervals are allowed. -/
theorem IsBoundEdges32.lowerLeft_geometric_integer_interval_part2
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) :
    ∃ p : B.presentation.lowerLeft.Index ↪ ℤ,
      Set.OrdConnected (Set.range p) ∧
      (∀ i j, B.presentation.lowerLeft.next i = some j ↔ p j = p i + 1) ∧
      (∀ i, G.dartBorders (B.presentation.lowerLeft.darts i) U ∧
        M.toPlaneMapWithMissing.missing (B.presentation.lowerLeft.darts i).1) ∧
      (∀ i j, p j = p i + 1 →
        S (B.presentation.lowerLeft.darts i) = B.presentation.lowerLeft.darts j ∧
        boundaryDartTerminal M (B.presentation.lowerLeft.darts i) =
          boundaryDartInitial M (B.presentation.lowerLeft.darts j)) ∧
      (∀ i, (∀ j, B.presentation.lowerLeft.next j ≠ some i) ↔ ∀ j, p i ≤ p j) ∧
      (∀ i, B.presentation.lowerLeft.next i = none ↔ ∀ j, p j ≤ p i) ∧
      BoundarySideEndpointLabels M B.presentation.lowerLeft := by
  obtain ⟨pos, hinj, hnext, hgap, hblock, hgeom⟩ := h.linear_positions_part2
  let p : B.presentation.lowerLeft.Index ↪ ℤ :=
    ⟨fun i => pos (.lowerLeft i), fun i j hij =>
      InfiniteBoundaryDartIndex.lowerLeft.inj (hinj hij)⟩
  have hc : Set.OrdConnected (Set.range p) := by
    constructor
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ z ⟨hiz, hzj⟩
    change pos (.lowerLeft i) ≤ z at hiz
    change z ≤ pos (.lowerLeft j) at hzj
    obtain ⟨k, hk⟩ := hgap (.lowerLeft i) (.lowerLeft j) z hiz hzj
    have htag := hblock (.lowerLeft i) k (.lowerLeft j)
      (by simpa only [hk] using hiz) (by simpa only [hk] using hzj) rfl
    cases k with
    | upperLeft k => norm_num [sideTag] at htag
    | upperRight k => norm_num [sideTag] at htag
    | lowerRight k => norm_num [sideTag] at htag
    | lowerLeft k => exact ⟨k, hk⟩
  have hn : ∀ i j, B.presentation.lowerLeft.next i = some j ↔ p j = p i + 1 := by
    intro i j
    change B.presentation.lowerLeft.next i = some j ↔
      pos (.lowerLeft j) = pos (.lowerLeft i) + 1
    have hh := hnext (.lowerLeft i) (.lowerLeft j) rfl
    simpa only [sideNext, Option.map_eq_some_iff,
      InfiniteBoundaryDartIndex.lowerLeft.injEq, exists_eq_right] using hh
  obtain ⟨hfirst, hlast⟩ := integer_interval_endpoints_part2 p _ hc hn
  refine ⟨p, hc, hn, ?_, ?_, hfirst, hlast, (h.endpoint_labels).2.2.2⟩
  · intro i
    exact ⟨(h.presentation_facts.1 _).mpr ⟨.lowerLeft i,
      InfiniteBoundaryDartIndex.dart_eq _ _⟩, lowerLeftBoundary32_missing h ⟨i, rfl⟩⟩
  · intro i j hij
    have hh := hgeom (.lowerLeft i) (.lowerLeft j) (by
      simp only [sideNext, (hn i j).mpr hij, Option.map_some])
    simpa only [InfiniteBoundaryDartIndex.dart_eq] using hh


private theorem marked_integer_interval_part2
    {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}
    (Q : InfiniteBoundarySide V E) (p : Q.Index ↪ ℤ)
    (hc : Set.OrdConnected (Set.range p))
    (hfirst : ∀ i, (∀ j, Q.next j ≠ some i) ↔ ∀ j, p i ≤ p j)
    (hlast : ∀ i, Q.next i = none ↔ ∀ j, p j ≤ p i)
    (hlabels : BoundarySideEndpointLabels M Q)
    (a b : V) (ha : Q.initialVertex? = some a) (hb : Q.terminalVertex? = some b) :
    (Nonempty Q.Index → ∃ i j : Q.Index,
      Set.range p = Set.Icc (p i) (p j) ∧
      boundaryDartInitial M (Q.darts i) = a ∧
      boundaryDartTerminal M (Q.darts j) = b) ∧
    (IsEmpty Q.Index → a = b) := by
  constructor
  · intro hne
    obtain ⟨i, hi, hia⟩ := (hlabels.1 a ha).1 hne
    obtain ⟨j, hj, hjb⟩ := (hlabels.2.1 b hb).1 hne
    have hmin := (hfirst i).mp hi
    have hmax := (hlast j).mp hj
    refine ⟨i, j, ?_, hia, hjb⟩
    apply Set.Subset.antisymm
    · rintro z ⟨k, rfl⟩
      exact ⟨hmin k, hmax k⟩
    · exact hc.out (Set.mem_range_self i) (Set.mem_range_self j)
  · intro hempty
    exact hlabels.2.2 hempty a b ha hb

/-- Helper toward Definition 3.2: with supplied finite junctions the
upperRight run is exactly a closed integer interval of geometric darts between
its specified vertices. An empty run identifies those vertices, retaining
their labels. The lower-right path is read in reverse traversal order. -/
theorem IsBoundEdges32.upperRight_supplied_vertex_interval_part2
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S)
    (J : FiniteBoundaryJunctions V) (hJ : B.finiteJunctions? = some J) :
    ∃ p : B.presentation.upperRight.Index ↪ ℤ,
      Set.OrdConnected (Set.range p) ∧
      (∀ i, G.dartBorders (B.presentation.upperRight.darts i) U ∧
        M.toPlaneMapWithMissing.missing (B.presentation.upperRight.darts i).1) ∧
      (∀ i j, p j = p i + 1 →
        S (B.presentation.upperRight.darts i) = B.presentation.upperRight.darts j ∧
        boundaryDartTerminal M (B.presentation.upperRight.darts i) =
          boundaryDartInitial M (B.presentation.upperRight.darts j)) ∧
      (Nonempty B.presentation.upperRight.Index →
        ∃ i j : B.presentation.upperRight.Index,
          Set.range p = Set.Icc (p i) (p j) ∧
          boundaryDartInitial M (B.presentation.upperRight.darts i) = J.upperLeftUpperRight ∧
          boundaryDartTerminal M (B.presentation.upperRight.darts j) = J.upperRightLowerRight) ∧
      (IsEmpty B.presentation.upperRight.Index → J.upperLeftUpperRight = J.upperRightLowerRight) := by
  have hf : (externalBoundaryDartSet4 M).Finite := by
    by_contra hi
    have hn := ((IsBoundEdges32.infinite_iff hi).mp h).1
    rw [hJ] at hn
    cases hn
  have hj := ((IsBoundEdges32.finite_supplied_junctions_iff hf J hJ).mp h).2
  rcases hj with ⟨_, _, hurI, hurT, _, _, hllI, hllT⟩
  obtain ⟨p, hc, _, hb, hg, hfirst, hlast, hl⟩ :=
    h.upperRight_geometric_integer_interval_part2
  have hm := marked_integer_interval_part2 B.presentation.upperRight p hc hfirst hlast hl
    J.upperLeftUpperRight J.upperRightLowerRight hurI hurT
  exact ⟨p, hc, hb, hg, hm.1, hm.2⟩

/-- Helper toward Definition 3.2: with supplied finite junctions the
lowerLeft run is exactly a closed integer interval of geometric darts between
its specified vertices. An empty run identifies those vertices, retaining
their labels. The lower-right path is read in reverse traversal order. -/
theorem IsBoundEdges32.lowerLeft_supplied_vertex_interval_part2
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S)
    (J : FiniteBoundaryJunctions V) (hJ : B.finiteJunctions? = some J) :
    ∃ p : B.presentation.lowerLeft.Index ↪ ℤ,
      Set.OrdConnected (Set.range p) ∧
      (∀ i, G.dartBorders (B.presentation.lowerLeft.darts i) U ∧
        M.toPlaneMapWithMissing.missing (B.presentation.lowerLeft.darts i).1) ∧
      (∀ i j, p j = p i + 1 →
        S (B.presentation.lowerLeft.darts i) = B.presentation.lowerLeft.darts j ∧
        boundaryDartTerminal M (B.presentation.lowerLeft.darts i) =
          boundaryDartInitial M (B.presentation.lowerLeft.darts j)) ∧
      (Nonempty B.presentation.lowerLeft.Index →
        ∃ i j : B.presentation.lowerLeft.Index,
          Set.range p = Set.Icc (p i) (p j) ∧
          boundaryDartInitial M (B.presentation.lowerLeft.darts i) = J.lowerRightLowerLeft ∧
          boundaryDartTerminal M (B.presentation.lowerLeft.darts j) = J.lowerLeftUpperLeft) ∧
      (IsEmpty B.presentation.lowerLeft.Index → J.lowerRightLowerLeft = J.lowerLeftUpperLeft) := by
  have hf : (externalBoundaryDartSet4 M).Finite := by
    by_contra hi
    have hn := ((IsBoundEdges32.infinite_iff hi).mp h).1
    rw [hJ] at hn
    cases hn
  have hj := ((IsBoundEdges32.finite_supplied_junctions_iff hf J hJ).mp h).2
  rcases hj with ⟨_, _, hurI, hurT, _, _, hllI, hllT⟩
  obtain ⟨p, hc, _, hb, hg, hfirst, hlast, hl⟩ :=
    h.lowerLeft_geometric_integer_interval_part2
  have hm := marked_integer_interval_part2 B.presentation.lowerLeft p hc hfirst hlast hl
    J.lowerRightLowerLeft J.lowerLeftUpperLeft hllI hllT
  exact ⟨p, hc, hb, hg, hm.1, hm.2⟩

end DirectedDistances.PlanarMap


































































