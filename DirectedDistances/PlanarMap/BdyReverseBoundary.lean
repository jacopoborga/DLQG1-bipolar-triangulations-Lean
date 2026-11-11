/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData
public import DirectedDistances.PlanarMap.EdgeOrientationFlip















public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

open BipolarTriangulationWithBoundary

/-- The darts of the first `k` right-boundary edges, in their original
source-to-sink order (`lem-bdy-reverse`,
inventory. -/
@[expose] def rightBoundaryPrefixDarts
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) : List D :=
  B.rightPath.darts.take k

/-- Select both darts of each edge in the first `k` right-boundary edges.
Including both representatives makes this a set of whole edge orbits. -/
@[expose] def rightPrefixFlipDarts
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) : Set D :=
  {d | d ∈ rightBoundaryPrefixDarts B k ∨
    B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k}

/-- The right-prefix dart set is closed under the edge involution and
contains no missing darts. -/
theorem rightPrefixFlip_condition
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) :
    (∀ d, d ∈ rightPrefixFlipDarts B k →
      B.map.toCombinatorialMap.edgeInv d ∈ rightPrefixFlipDarts B k) ∧
    (∀ d, d ∈ rightPrefixFlipDarts B k → ¬ B.map.missing d) := by
  constructor
  · intro d hd
    change d ∈ rightBoundaryPrefixDarts B k ∨
      B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k at hd
    change B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k ∨
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.edgeInv d) ∈
        rightBoundaryPrefixDarts B k
    rcases hd with hd | hd
    · exact Or.inr (by simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hd)
    · exact Or.inl hd
  · intro d hd
    exact B.noMissingDarts d

/-- Reverse the first `k` right-boundary edges, where `k` is in the range
not counted in the paper inventory. -/
@[expose] noncomputable def flipRightPrefix
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (_hk : 1 ≤ k) (_hkr : k < r) : DirectedMapWithMissing D :=
  flipOrientation B.map (rightPrefixFlipDarts B k) (rightPrefixFlip_condition B k)

/-- The right-prefix flip leaves the combinatorial map unchanged. -/
theorem flipRightPrefix_toCombinatorialMap
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    (flipRightPrefix B k hk hkr).toCombinatorialMap = B.map.toCombinatorialMap := by
  exact flipOrientation_toCombinatorialMap B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k)

/-- The right-prefix flip leaves the missing-dart set unchanged. -/
theorem flipRightPrefix_missing
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    (flipRightPrefix B k hk hkr).missing = B.map.missing := by
  exact flipOrientation_missing B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k)

/-- On a selected prefix edge, the flipped tail is the old tail of the
opposite dart. -/
theorem flipRightPrefix_tail_of_mem
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (d : D)
    (hd : d ∈ rightPrefixFlipDarts B k) :
    (flipRightPrefix B k hk hkr).tail d ↔
      B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  exact flipOrientation_tail_of_mem B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k) d hd

/-- Outside the selected prefix edge orbits, the orientation is unchanged. -/
theorem flipRightPrefix_tail_of_not_mem
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (d : D)
    (hd : d ∉ rightPrefixFlipDarts B k) :
    (flipRightPrefix B k hk hkr).tail d ↔ B.map.tail d := by
  exact flipOrientation_tail_of_not_mem B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k) d hd

/-- Combinatorial planarity is inherited by the right-prefix flip. -/
theorem flipRightPrefix_planar
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    (flipRightPrefix B k hk hkr).toCombinatorialMap.IsPlanar := by
  exact (flipOrientation_isPlanar_iff B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k)).2 B.planar

/-- The outer-face cyclic word remains an exact outer cycle after the flip. -/
theorem flipRightPrefix_outerCycle
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    IsOuterCycle (flipRightPrefix B k hk hkr) B.outerWord := by
  exact (flipOrientation_isOuterCycle_iff B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k) B.outerWord).2 B.outerSplit.1

/-- Every inner face remains a triangle after the right-prefix flip. -/
theorem flipRightPrefix_innerFacesDegreeThree
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    ∀ d, ¬ (flipRightPrefix B k hk hkr).IsOuter d →
      (flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc
          ((flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc
            ((flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc d)) = d ∧
        (flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc d ≠ d ∧
        (flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc
          ((flipRightPrefix B k hk hkr).toCombinatorialMap.faceSucc d) ≠ d := by
  intro d hd
  have hd' : ¬ B.map.IsOuter d := by
    intro ho
    exact hd ((flipOrientation_isOuter_iff B.map (rightPrefixFlipDarts B k)
      (rightPrefixFlip_condition B k) d).mp ho)
  have h := B.innerFacesDegreeThree d hd'
  simpa only [flipRightPrefix, flipOrientation_faceSucc,
    flipOrientation_isOuter_iff] using h

/-- The vertex `x_i` on the right boundary, represented in the unchanged
rotation quotient. -/
@[expose] def rightBoundaryVertexAt
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (i : ℕ)
    (hi : i ≤ r) :
    MapVertex B.map :=
  B.rightPath.vertices.get ⟨i, by rw [B.rightPath.vertices_length]; omega⟩

/-- The exact path and outer-word data still to be constructed for the
planar-boundary part of Lemma `lem-bdy-reverse`. The paths have the source
`x_k`, end at the old sink, lengths `ℓ+k` and `r-k`, retain internal vertex
and edge disjointness, and split the unchanged outer word into the new left
arc and reversed-opposite-dart right arc. `FourArcsWitness` compares the
word up to rotation, so reusing `B.outerWord` is consistent. No acyclicity or
source/sink uniqueness field is included here. Helper; not counted in the
paper inventory. -/
structure RightPrefixBoundaryPathsData
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) where
  leftPath : SimpleDirectedDartPath (flipRightPrefix B k hk hkr)
    (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) B.sink (ℓ + k)
  leftPath_darts : leftPath.darts =
    (rightBoundaryPrefixDarts B k).reverse.map
      B.map.toCombinatorialMap.edgeInv ++ B.leftPath.darts
  leftPath_vertices : leftPath.vertices =
    (B.rightPath.vertices.take (k + 1)).reverse ++ B.leftPath.vertices.drop 1
  rightPath : SimpleDirectedDartPath (flipRightPrefix B k hk hkr)
    (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) B.sink (r - k)
  rightPath_darts : rightPath.darts = B.rightPath.darts.drop k
  rightPath_vertices : rightPath.vertices = B.rightPath.vertices.drop k
  paths_internally_vertex_disjoint : ∀ v,
    v ∈ leftPath.vertices → v ∈ rightPath.vertices →
      v = rightBoundaryVertexAt B k (Nat.le_of_lt hkr) ∨ v = B.sink
  paths_edge_disjoint : ∀ d, d ∈ leftPath.darts → ∀ e, e ∈ rightPath.darts →
    ¬ Equiv.Perm.SameCycle (flipRightPrefix B k hk hkr).toCombinatorialMap.edgeInv d e
  outerSplit : FourArcsWitness (flipRightPrefix B k hk hkr) B.outerWord
    leftPath.darts []
    (rightPath.darts.reverse.map
      (flipRightPrefix B k hk hkr).toCombinatorialMap.edgeInv) []

/- endpoints, lengths, disjointness clauses, and outer-word split. Helper; not
counted in the paper inventory. -/
@[expose] def rightPrefixBoundaryPathsGoal
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) : Prop :=
  Nonempty (RightPrefixBoundaryPathsData B k hk hkr)

/-- Add the graph-level conclusions to already constructed planar boundary
data. The acyclicity, new source/source uniqueness, and retained sink/sink
uniqueness are explicit inputs, as supplied by the separate graph-level
boundary-flip argument (`lem-bdy-reverse`,
inventory. -/
@[expose] noncomputable def RightPrefixBoundaryPathsData.toBipolarTriangulationWithBoundary
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r)
    (P : RightPrefixBoundaryPathsData B k hk hkr)
    (hacyclic : (flipRightPrefix B k hk hkr).IsAcyclic)
    (hisSource : ¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep
      u (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)))
    (hsource_unique : ∀ v,
      (¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep u v) →
        v = rightBoundaryVertexAt B k (Nat.le_of_lt hkr))
    (hisSink : ¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep B.sink w)
    (hsink_unique : ∀ v,
      (¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep v w) → v = B.sink) :
    BipolarTriangulationWithBoundary D (ℓ + k) (r - k) := by
  refine
    { map := flipRightPrefix B k hk hkr
      noMissingDarts := ?_
      planar := flipRightPrefix_planar B k hk hkr
      innerFacesDegreeThree := flipRightPrefix_innerFacesDegreeThree B k hk hkr
      acyclic := hacyclic
      source := rightBoundaryVertexAt B k (Nat.le_of_lt hkr)
      sink := B.sink
      isSource := hisSource
      source_unique := hsource_unique
      isSink := hisSink
      sink_unique := hsink_unique
      left_length_pos := by omega
      right_length_pos := by omega
      outerWord := B.outerWord
      leftPath := P.leftPath
      rightPath := P.rightPath
      paths_internally_vertex_disjoint := P.paths_internally_vertex_disjoint
      paths_edge_disjoint := P.paths_edge_disjoint
      outerSplit := P.outerSplit }
  intro d
  rw [flipRightPrefix_missing]
  exact B.noMissingDarts d

section ToBipolarProjections

variable {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
  (hk : 1 ≤ k) (hkr : k < r) (P : RightPrefixBoundaryPathsData B k hk hkr)
  (hacyclic : (flipRightPrefix B k hk hkr).IsAcyclic)
  (hisSource : ¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep
    u (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)))
  (hsource_unique : ∀ v,
    (¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep u v) →
      v = rightBoundaryVertexAt B k (Nat.le_of_lt hkr))
  (hisSink : ¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep B.sink w)
  (hsink_unique : ∀ v,
    (¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep v w) → v = B.sink)

/-- The constructed map is the right-prefix flip. Helper; not counted in the
paper inventory. -/
@[simp] theorem toBipolarTriangulationWithBoundary_map :
    (P.toBipolarTriangulationWithBoundary B k hk hkr hacyclic hisSource
      hsource_unique hisSink hsink_unique).map = flipRightPrefix B k hk hkr := rfl

/-- The constructed source is `x_k`. Helper; not counted in the paper
inventory. -/
@[simp] theorem toBipolarTriangulationWithBoundary_source :
    (P.toBipolarTriangulationWithBoundary B k hk hkr hacyclic hisSource
      hsource_unique hisSink hsink_unique).source =
      rightBoundaryVertexAt B k (Nat.le_of_lt hkr) := rfl

/-- The constructed sink is the old sink. Helper; not counted in the paper
inventory. -/
@[simp] theorem toBipolarTriangulationWithBoundary_sink :
    (P.toBipolarTriangulationWithBoundary B k hk hkr hacyclic hisSource
      hsource_unique hisSink hsink_unique).sink = B.sink := rfl

/-- The constructed left boundary path is the data's left path. Helper; not
counted in the paper inventory. -/
@[simp] theorem toBipolarTriangulationWithBoundary_leftPath :
    (P.toBipolarTriangulationWithBoundary B k hk hkr hacyclic hisSource
      hsource_unique hisSink hsink_unique).leftPath = P.leftPath := rfl

/-- The constructed right boundary path is the data's right path. Helper; not
counted in the paper inventory. -/
@[simp] theorem toBipolarTriangulationWithBoundary_rightPath :
    (P.toBipolarTriangulationWithBoundary B k hk hkr hacyclic hisSource
      hsource_unique hisSink hsink_unique).rightPath = P.rightPath := rfl

end ToBipolarProjections

/-- Boundary channeling after the flip reduces to the selected prefix being
recognized as old boundary edges. For an unselected dart the old channeling
condition applies directly; for a selected dart this theorem records the
remaining edge-orbit membership obligation. -/
theorem flipRightPrefix_channeling_or_selected
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ∀ d, ¬ (flipRightPrefix B k hk hkr).missing d →
      (flipRightPrefix B k hk hkr).tail d →
      dartHeadVertex (flipRightPrefix B k hk hkr) d ∈ B.boundaryVertices →
      dartHeadVertex (flipRightPrefix B k hk hkr) d ≠ B.sink →
      B.boundaryEdge d ∨ d ∈ rightPrefixFlipDarts B k := by
  intro d hmiss htail hv hvs
  by_cases hd : d ∈ rightPrefixFlipDarts B k
  · exact Or.inr hd
  · apply Or.inl
    apply hbc d
    · simpa only [flipRightPrefix_missing] using hmiss
    · exact (flipOrientation_tail_of_not_mem B.map (rightPrefixFlipDarts B k)
        (rightPrefixFlip_condition B k) d hd).mp htail
    · exact hv
    · exact hvs

/-- Every unselected edge entering an old boundary vertex other than the
sink retains the old boundary-channel conclusion. -/
theorem flipRightPrefix_unselected_incoming_is_boundary
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled)
    (d : D) (hd : d ∉ rightPrefixFlipDarts B k)
    (hmiss : ¬ (flipRightPrefix B k hk hkr).missing d)
    (htail : (flipRightPrefix B k hk hkr).tail d)
    (hv : dartHeadVertex (flipRightPrefix B k hk hkr) d ∈ B.boundaryVertices)
    (hvs : dartHeadVertex (flipRightPrefix B k hk hkr) d ≠ B.sink) :
    B.boundaryEdge d := by
  apply hbc d
  · simpa only [flipRightPrefix_missing] using hmiss
  · exact (flipRightPrefix_tail_of_not_mem B k hk hkr d hd).mp htail
  · exact hv
  · exact hvs

/-- Boundary channeling transfers through the right-prefix flip: every
present edge of the flipped map entering an old boundary vertex other than
the sink is an old boundary edge. Selected darts are boundary edges because
they, or their opposite darts, lie on the right path (`lem-bdy-reverse`,
inventory. -/
theorem flipRightPrefix_incoming_is_boundary
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ∀ d, ¬ (flipRightPrefix B k hk hkr).missing d →
      (flipRightPrefix B k hk hkr).tail d →
      dartHeadVertex (flipRightPrefix B k hk hkr) d ∈ B.boundaryVertices →
      dartHeadVertex (flipRightPrefix B k hk hkr) d ≠ B.sink →
      B.boundaryEdge d := by
  intro d hmiss htail hv hvs
  rcases flipRightPrefix_channeling_or_selected B k hk hkr hbc d hmiss htail hv hvs
    with h | h
  · exact h
  · simp only [rightPrefixFlipDarts, Set.mem_ofPred_eq] at h
    unfold BipolarTriangulationWithBoundary.boundaryEdge IsBoundaryEdge
    rcases h with h | h
    · unfold rightBoundaryPrefixDarts at h
      exact ⟨d, List.mem_append_right _ (List.mem_of_mem_take h),
        Equiv.Perm.SameCycle.refl _ _⟩
    · unfold rightBoundaryPrefixDarts at h
      exact ⟨B.map.toCombinatorialMap.edgeInv d,
        List.mem_append_right _ (List.mem_of_mem_take h),
        Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)⟩

end DirectedDistances.PlanarMap
