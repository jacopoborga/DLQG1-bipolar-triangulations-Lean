/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarCanonicalTrees
public import DirectedDistances.PlanarMap.BipolarPeanoContour
public import DirectedDistances.PlanarMap.KMSWMapIsoClass

/-! # Inverse KMSW walk coordinates

Helpers toward the inverse direction of `thm-kmsw`; not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The zero-based position `j` records the source definition's dart
`λ_{j+1}`: the first coordinate is the upper-left height of its initial
vertex, and the second is the lower-right height of its terminal vertex
Helper toward the inverse direction of `thm-kmsw`; not the paper result. -/
@[expose] noncomputable def bipolarInverseWalk
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Fin B.map.toCombinatorialMap.numEdges → ℤ × ℤ :=
  fun j =>
    ( (canonicalULHeight B (dartTailVertex B.map (peanoEdge B j)) : ℤ)
    , (canonicalLRHeight B (dartHeadVertex B.map (peanoEdge B j)) : ℤ) -
        ((r - 1 : ℕ) : ℤ) )

/-- The inverse walk starts at the origin, using the first right-boundary dart
inverse direction of `thm-kmsw`; not the paper result. -/
theorem bipolarInverseWalk_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    bipolarInverseWalk B ⟨0, contour_numEdges_pos B⟩ = (0, 0) := by
  have hr : 1 ≤ r := B.right_length_pos
  have hi : (0 : ℕ) < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    exact Nat.zero_lt_of_lt B.right_length_pos
  let i : Fin B.rightPath.darts.length := ⟨0, hi⟩
  have hstep := B.rightPath.edge_step i
  have htail : dartTailVertex B.map
      (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)) = B.source := by
    simpa only [SimpleDirectedDartPath.firstDart] using
      hstep.2.2.1.symm.trans B.rightPath.start_vertex
  have hhead : dartHeadVertex B.map
      (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)) =
        B.rightPath.vertices.get
          ⟨1, by rw [B.rightPath.vertices_length]; omega⟩ := by
    simpa only [SimpleDirectedDartPath.firstDart] using hstep.2.2.2.symm
  have hUL : canonicalULHeight B B.source = 0 := by
    simpa only [B.leftPath.start_vertex] using
      canonicalULHeight_leftPath B 0 (by omega)
  have hLR : canonicalLRHeight B
      (B.rightPath.vertices.get
        ⟨1, by rw [B.rightPath.vertices_length]; omega⟩) = r - 1 :=
    canonicalLRHeight_rightPath B 1 (by omega)
  rw [bipolarInverseWalk, peanoEdge_zero, htail, hhead, hUL, hLR]
  simp

/-- The final inverse-walk position is `(ℓ - 1, -r + 1)`, using the last
185–202`). Helper toward the inverse direction of `thm-kmsw`; not the paper
result. -/
theorem bipolarInverseWalk_last
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    bipolarInverseWalk B
      ⟨B.map.toCombinatorialMap.numEdges - 1, by
        have := contour_numEdges_pos B
        omega⟩ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := by
  have hℓ : 1 ≤ ℓ := B.left_length_pos
  have hr : 1 ≤ r := B.right_length_pos
  have htail : dartTailVertex B.map
      (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) =
        B.leftPath.vertices.get
          ⟨ℓ - 1, by rw [B.leftPath.vertices_length]; omega⟩ := by
    have hstep := B.leftPath.edge_step
      ⟨ℓ - 1, by rw [B.leftPath.darts_length]; omega⟩
    simpa only [pathLastDart] using hstep.2.2.1.symm
  have hhead : dartHeadVertex B.map
      (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) = B.sink :=
    pathLastDart_head_eq_end B.leftPath
      (Nat.zero_lt_of_lt B.left_length_pos)
  have hUL : canonicalULHeight B
      (B.leftPath.vertices.get
        ⟨ℓ - 1, by rw [B.leftPath.vertices_length]; omega⟩) = ℓ - 1 := by
    exact canonicalULHeight_leftPath B (ℓ - 1) (by omega)
  have hLR : canonicalLRHeight B B.sink = 0 := by
    calc
      canonicalLRHeight B B.sink = canonicalLRHeight B
          (B.rightPath.vertices.get
            ⟨r, by rw [B.rightPath.vertices_length]; omega⟩) := by
        rw [B.rightPath.end_vertex]
      _ = r - r := canonicalLRHeight_rightPath B r le_rfl
      _ = 0 := Nat.sub_self r
  rw [bipolarInverseWalk, peanoEdge_last, htail, hhead, hUL, hLR]
  have hℓcast : ((ℓ - 1 : ℕ) : ℤ) + 1 = (ℓ : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hℓ
  have hrcast : ((r - 1 : ℕ) : ℤ) + 1 = (r : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hr
  apply Prod.ext
  · omega
  · omega

/-- Every inverse-walk position lies in the cone
185–202`). Helper toward the inverse direction of `thm-kmsw`; not the paper
result. -/
theorem bipolarInverseWalk_cone
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    0 ≤ (bipolarInverseWalk B j).1 ∧
      -(r : ℤ) + 1 ≤ (bipolarInverseWalk B j).2 := by
  have hr : 1 ≤ r := B.right_length_pos
  have hrcast : ((r - 1 : ℕ) : ℤ) + 1 = (r : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hr
  rw [bipolarInverseWalk]
  constructor
  · exact Int.natCast_nonneg _
  · have hheight : 0 ≤
        (canonicalLRHeight B (dartHeadVertex B.map (peanoEdge B j)) : ℤ) :=
      Int.natCast_nonneg _
    omega

private theorem boundaryPath_length_le_numEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {k : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink k) :
    k ≤ B.map.toCombinatorialMap.numEdges := by
  classical
  let f : Fin k → {d : D // B.map.tail d} := fun i =>
    ⟨P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩,
      (P.edge_step ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩).2.1⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hd : P.darts.get
        ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ =
      P.darts.get ⟨j.val, by rw [P.darts_length]; exact j.isLt⟩ :=
      congrArg Subtype.val hij
    have hi := P.edge_step ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
    have hj := P.edge_step ⟨j.val, by rw [P.darts_length]; exact j.isLt⟩
    have hvertices :
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex B.map
              (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩) :=
          hi.2.2.1
        _ = dartTailVertex B.map
              (P.darts.get ⟨j.val, by rw [P.darts_length]; exact j.isLt⟩) :=
          congrArg (dartTailVertex B.map) hd
        _ = P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ :=
          hj.2.2.1.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hvertices
    have hval : i.val = j.val := by
      have h := congrArg (fun q : Fin P.vertices.length => q.val) hidx
      exact h
    exact Fin.ext hval
  have hset : (firstVisitOrder B).toFinset =
      Finset.univ.filter (fun d => B.map.tail d) := by
    ext d
    simp only [List.mem_toFinset, mem_firstVisitOrder_iff,
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard : Fintype.card {d : D // B.map.tail d} =
      B.map.toCombinatorialMap.numEdges := by
    calc
      Fintype.card {d : D // B.map.tail d} =
          (Finset.univ.filter (fun d => B.map.tail d)).card := by
        rw [Fintype.card_subtype]
      _ = (firstVisitOrder B).toFinset.card := by rw [← hset]
      _ = (firstVisitOrder B).length :=
        List.toFinset_card_of_nodup (firstVisitOrder_nodup B)
      _ = B.map.toCombinatorialMap.numEdges := firstVisitOrder_length B
  have hle : k ≤ Fintype.card {d : D // B.map.tail d} := by
    simpa using Fintype.card_le_of_injective f hf
  exact hle.trans_eq hcard

/-- If the base map has one edge, both positive boundary path lengths are
one, including the shared-boundary single-edge case (`thm-kmsw`,
`thm-kmsw`; not the paper result. -/
theorem bipolarInverseWalk_oneEdge_boundaryLengths
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (h : B.map.toCombinatorialMap.numEdges = 1) : ℓ = 1 ∧ r = 1 := by
  have hℓpos := B.left_length_pos
  have hrpos := B.right_length_pos
  have hleft := boundaryPath_length_le_numEdges B B.leftPath
  have hright := boundaryPath_length_le_numEdges B B.rightPath
  omega

/-- A representative's underlying map has exactly its declared `n` edges.
Helper toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem kmswRep_numEdges (R : KMSWMapRep ℓ r n) :
    R.B.map.toCombinatorialMap.numEdges = n :=
  R.edges

/-- The dart carrier of a representative has twice its declared edge count.
Helper toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem kmswRep_dartCount (R : KMSWMapRep ℓ r n) :
    R.dartCount = 2 * n :=
  R.dartCount_eq_two_mul

/-- The inverse walk on a representative, reindexed from its map's `n` edges
using the representative's edge-count equality. Helper toward the inverse
direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def kmswRepInverseWalk
    (R : KMSWMapRep ℓ r n) : Fin n → ℤ × ℤ :=
  fun j => bipolarInverseWalk R.B (Fin.cast R.edges.symm j)

/-- The representative inverse walk starts at the origin. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
theorem kmswRepInverseWalk_zero (R : KMSWMapRep ℓ r n) :
    kmswRepInverseWalk R
      ⟨0, by
        have h := contour_numEdges_pos R.B
        rw [R.edges] at h
        exact h⟩ = (0, 0) := by
  have hidx : Fin.cast R.edges.symm
      ⟨0, by
        have h := contour_numEdges_pos R.B
        rw [R.edges] at h
        exact h⟩ = ⟨0, contour_numEdges_pos R.B⟩ := Fin.ext rfl
  change bipolarInverseWalk R.B
    (Fin.cast R.edges.symm ⟨0, by
      have h := contour_numEdges_pos R.B
      rw [R.edges] at h
      exact h⟩) = (0, 0)
  rw [hidx]
  exact bipolarInverseWalk_zero R.B

/-- The final representative inverse-walk position has the theorem's stated
endpoint. Helper toward the inverse direction of `thm-kmsw`; not the paper -/
theorem kmswRepInverseWalk_last (R : KMSWMapRep ℓ r n) :
    kmswRepInverseWalk R
      ⟨n - 1, by
        have h := contour_numEdges_pos R.B
        rw [R.edges] at h
        omega⟩ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := by
  have he := R.edges
  have hidx : Fin.cast R.edges.symm
      ⟨n - 1, by
        have h := contour_numEdges_pos R.B
        rw [R.edges] at h
        omega⟩ =
      ⟨R.B.map.toCombinatorialMap.numEdges - 1, by
        have h := contour_numEdges_pos R.B
        omega⟩ := by
    apply Fin.ext
    change n - 1 = R.B.map.toCombinatorialMap.numEdges - 1
    omega
  change bipolarInverseWalk R.B
    (Fin.cast R.edges.symm ⟨n - 1, by
      have h := contour_numEdges_pos R.B
      rw [R.edges] at h
      omega⟩) = ((ℓ : ℤ) - 1, -(r : ℤ) + 1)
  rw [hidx]
  exact bipolarInverseWalk_last R.B

/-- Every representative inverse-walk position lies in the same cone.
Helper toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem kmswRepInverseWalk_cone (R : KMSWMapRep ℓ r n) (j : Fin n) :
    0 ≤ (kmswRepInverseWalk R j).1 ∧
      -(r : ℤ) + 1 ≤ (kmswRepInverseWalk R j).2 := by
  simpa only [kmswRepInverseWalk] using
    bipolarInverseWalk_cone R.B (Fin.cast R.edges.symm j)

end DirectedDistances.PlanarMap
