/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseBoundary

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

open BipolarTriangulationWithBoundary

/-- Darts on a simple directed path are pairwise distinct, since equal darts
would have equal initial vertices (`lem-bdy-reverse`,
inventory. -/
private theorem simplePath_darts_nodup {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hi := P.edge_step i
  have hj := P.edge_step j
  have hiLt : i.val < n := by simpa [P.darts_length] using i.isLt
  have hjLt : j.val < n := by simpa [P.darts_length] using j.isLt
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
  have hval : i.val = j.val := by
    exact congrArg (fun q : Fin P.vertices.length => q.val) hidx
  exact Fin.ext hval

/-- Every dart on the old right path is a tail dart. -/
private theorem rightPath_mem_tail {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (d : D)
    (hd : d ∈ B.rightPath.darts) : B.map.tail d := by
  rcases List.mem_iff_get.mp hd with ⟨i, hi⟩
  exact hi ▸ (B.rightPath.edge_step i).2.1

private theorem flipOrientation_dartHeadVertex (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (d : D) :
    dartHeadVertex (flipOrientation M S hS) d = dartHeadVertex M d := rfl

/-- A dart in the suffix of the right path is outside the flipped prefix
Helper; not counted in the paper inventory. -/
private theorem rightSuffix_dart_not_selected {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (_hk : k < r)
    (i : Fin (B.rightPath.darts.drop k).length) :
    (B.rightPath.darts.drop k).get i ∉ rightPrefixFlipDarts B k := by
  let d := (B.rightPath.darts.drop k).get i
  have hdrop : d ∈ B.rightPath.darts.drop k := List.get_mem _ _
  intro hs
  change d ∈ rightBoundaryPrefixDarts B k ∨
    B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k at hs
  rcases hs with hpre | hinv
  · have hnd := simplePath_darts_nodup B.rightPath
    have hdj := List.disjoint_take_drop hnd (Nat.le_refl k)
    exact hdj hpre hdrop
  · have htail : B.map.tail d :=
      rightPath_mem_tail B d (List.mem_of_mem_drop hdrop)
    have hinvTail : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      apply rightPath_mem_tail B
      exact List.mem_of_mem_take hinv
    have hnot := (B.map.tail_iff d (B.noMissingDarts d)).mp htail
    exact hnot hinvTail

/-- Every dart in the right-path suffix remains a present tail dart after
the prefix flip (`lem-bdy-reverse`,
inventory. -/
theorem rightSuffix_dart_present_tail {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r)
    (i : Fin (B.rightPath.darts.drop k).length) :
    ¬ (flipRightPrefix B k hk hkr).missing
        ((B.rightPath.darts.drop k).get i) ∧
      (flipRightPrefix B k hk hkr).tail
        ((B.rightPath.darts.drop k).get i) := by
  constructor
  · rw [flipRightPrefix_missing]
    exact B.noMissingDarts _
  · rw [flipRightPrefix_tail_of_not_mem B k hk hkr _
      (rightSuffix_dart_not_selected B k hkr i)]
    exact rightPath_mem_tail B _ (List.mem_of_mem_drop (List.get_mem _ _))

/-- The proposed left dart list has the required length (`lem-bdy-reverse`,
inventory. -/
private theorem rightPrefix_leftDarts_length {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (hkr : k < r) :
    ((B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv ++
      B.leftPath.darts).length = ℓ + k := by
  simp [List.length_take, B.rightPath.darts_length, B.leftPath.darts_length,
    Nat.min_eq_left (Nat.le_of_lt hkr)]
  omega

/-- The proposed left vertex list has the required length (`lem-bdy-reverse`,
inventory. -/
private theorem rightPrefix_leftVertices_length {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (hkr : k < r) :
    ((B.rightPath.vertices.take (k + 1)).reverse ++
      B.leftPath.vertices.drop 1).length = ℓ + k + 1 := by
  simp [List.length_take, B.rightPath.vertices_length,
    B.leftPath.vertices_length,
    Nat.min_eq_left (Nat.succ_le_succ (Nat.le_of_lt hkr))]
  omega

/-- The directed suffix of the right boundary remains a simple path after
the selected prefix is reversed (`lem-bdy-reverse`,
inventory. -/
def rightPrefix_suffixPath {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    SimpleDirectedDartPath (flipRightPrefix B k hk hkr)
      (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) B.sink (r - k) := by
  unfold flipRightPrefix flipOrientation
  let R := B.rightPath
  refine
    { darts := R.darts.drop k
      vertices := R.vertices.drop k
      darts_length := ?_
      vertices_length := ?_
      vertices_nodup := ?_
      start_vertex := ?_
      end_vertex := ?_
      edge_step := ?_ }
  · rw [List.length_drop, R.darts_length]
  · rw [List.length_drop, R.vertices_length]
    omega
  · exact B.rightPath.vertices_nodup.sublist
      (List.drop_sublist k B.rightPath.vertices)
  · simp [R, rightBoundaryVertexAt, List.get_eq_getElem, List.getElem_drop]
  · have hkr' : k ≤ r := Nat.le_of_lt hkr
    simpa [R, List.get_eq_getElem, List.getElem_drop,
      Nat.add_sub_of_le hkr'] using R.end_vertex
  · intro i
    have hi : i.val < r - k := by
      simpa [List.length_drop, R.darts_length] using i.isLt
    let j : Fin R.darts.length := ⟨k + i.val, by
      rw [R.darts_length]
      omega⟩
    have hgetD : (R.darts.drop k).get i = R.darts.get j := by
      simp [j, List.get_eq_getElem]
    have hstep := R.edge_step j
    have hselected := rightSuffix_dart_not_selected B k hkr i
    have htail : (flipRightPrefix B k hk hkr).tail ((R.darts.drop k).get i) := by
      rw [flipRightPrefix_tail_of_not_mem B k hk hkr _ hselected]
      rw [hgetD]
      exact hstep.2.1
    have hmiss : ¬ (flipRightPrefix B k hk hkr).missing ((R.darts.drop k).get i) := by
      rw [flipRightPrefix_missing]
      exact B.noMissingDarts _
    have hnext : k + (i.val + 1) < R.vertices.length := by
      rw [R.vertices_length]
      omega
    refine ⟨hmiss, htail, ?_, ?_⟩
    · simpa [j, List.get_eq_getElem, List.getElem_drop, dartTailVertex] using
        hstep.2.2.1
    · simp only [List.get_eq_getElem, List.getElem_drop]
      change R.vertices[k + (i.val + 1)] =
        dartHeadVertex (flipOrientation B.map (rightPrefixFlipDarts B k)
          (rightPrefixFlip_condition B k)) (R.darts.get j)
      rw [flipOrientation_dartHeadVertex]
      simpa [j, Nat.add_assoc] using hstep.2.2.2

/-- Reversal preserves the vertex carrier definitionally (`lem-bdy-reverse`, -/
theorem rightPrefix_mapVertex_eq {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    MapVertex (flipRightPrefix B k hk hkr) = MapVertex B.map := rfl

/-- The new left vertex list is simple (`lem-bdy-reverse`, -/
private theorem rightPrefix_leftVertices_nodup {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (hkr : k < r) :
    ((B.rightPath.vertices.take (k + 1)).reverse ++
      B.leftPath.vertices.drop 1).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr B.rightPath.vertices_nodup.take,
    B.leftPath.vertices_nodup.drop, ?_⟩
  intro v hvR hvL
  have hvR' : v ∈ B.rightPath.vertices.take (k + 1) := List.mem_reverse.mp hvR
  have hvL' : v ∈ B.leftPath.vertices := List.mem_of_mem_drop hvL
  rcases B.paths_internally_vertex_disjoint v hvL'
    (List.mem_of_mem_take hvR') with hs | ht
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvL
    have hi' : 1 + i.val < B.leftPath.vertices.length := by
      have := i.isLt
      simp only [List.length_drop] at this
      omega
    have heq : B.leftPath.vertices[1 + i.val] = B.leftPath.vertices[0] := by
      calc
        _ = v := by simpa only [List.get_eq_getElem, List.getElem_drop] using hi
        _ = B.source := hs
        _ = _ := B.leftPath.start_vertex.symm
    have := B.leftPath.vertices_nodup.getElem_inj.mp heq
    omega
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvR'
    have hi' : i.val < k + 1 := by
      have := i.isLt
      simp only [List.length_take] at this
      omega
    have heq : B.rightPath.vertices[i.val] = B.rightPath.vertices[r]'(by
        rw [B.rightPath.vertices_length]; omega) := by
      calc
        _ = v := by simpa only [List.get_eq_getElem, List.getElem_take] using hi
        _ = B.sink := ht
        _ = _ := B.rightPath.end_vertex.symm
    have := B.rightPath.vertices_nodup.getElem_inj.mp heq
    omega

/-- Old left darts retain their orientation (`lem-bdy-reverse`, -/
private theorem rightPrefix_leftDart_not_selected {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (d : D) (hd : d ∈ B.leftPath.darts) :
    d ∉ rightPrefixFlipDarts B k := by
  intro hs
  change d ∈ B.rightPath.darts.take k ∨
    B.map.toCombinatorialMap.edgeInv d ∈ B.rightPath.darts.take k at hs
  rcases hs with hs | hs
  · exact B.paths_edge_disjoint d hd d (List.mem_of_mem_take hs)
      (Equiv.Perm.SameCycle.refl _ _)
  · exact B.paths_edge_disjoint d hd _ (List.mem_of_mem_take hs)
      (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- Prefix indices in the new left vertex list run backwards on the old
Helper; not counted. -/
private theorem rightPrefix_leftVertices_get_prefix {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (hkr : k < r)
    (i : ℕ) (hi : i ≤ k) :
    (((B.rightPath.vertices.take (k + 1)).reverse ++
      B.leftPath.vertices.drop 1)[i]'(by
        rw [rightPrefix_leftVertices_length B k hkr]; omega)) =
      B.rightPath.vertices[k - i]'(by rw [B.rightPath.vertices_length]; omega) := by
  have hlen : (B.rightPath.vertices.take (k + 1)).length = k + 1 := by
    rw [List.length_take, B.rightPath.vertices_length, Nat.min_eq_left (by omega)]
  rw [List.getElem_append_left (by rw [List.length_reverse, hlen]; omega),
    List.getElem_reverse, List.getElem_take]
  congr 1
  omega

/-- Suffix indices in the new left vertex list run on the old left boundary -/
private theorem rightPrefix_leftVertices_get_suffix {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) (hkr : k < r)
    (i : ℕ) (hi : k ≤ i) (hi' : i ≤ ℓ + k) :
    (((B.rightPath.vertices.take (k + 1)).reverse ++
      B.leftPath.vertices.drop 1)[i]'(by
        rw [rightPrefix_leftVertices_length B k hkr]; omega)) =
      B.leftPath.vertices[i - k]'(by rw [B.leftPath.vertices_length]; omega) := by
  by_cases heq : i = k
  · subst i
    rw [rightPrefix_leftVertices_get_prefix B k hkr k (by omega)]
    simpa only [Nat.sub_self, List.get_eq_getElem] using
      B.rightPath.start_vertex.trans B.leftPath.start_vertex.symm
  · have hlen : (B.rightPath.vertices.take (k + 1)).length = k + 1 := by
      rw [List.length_take, B.rightPath.vertices_length, Nat.min_eq_left (by omega)]
    rw [List.getElem_append_right (by rw [List.length_reverse, hlen]; omega),
      List.getElem_drop]
    congr 1
    rw [List.length_reverse, hlen]
    omega

/-- Reversing the right prefix and following the old left boundary gives
the new simple left path (`lem-bdy-reverse`,
carrier; not counted in the paper inventory. -/
noncomputable def rightPrefix_leftPath {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    SimpleDirectedDartPath (flipRightPrefix B k hk hkr)
      (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) B.sink (ℓ + k) := by
  unfold flipRightPrefix flipOrientation
  refine
    { darts := (B.rightPath.darts.take k).reverse.map
        B.map.toCombinatorialMap.edgeInv ++ B.leftPath.darts
      vertices := (B.rightPath.vertices.take (k + 1)).reverse ++
        B.leftPath.vertices.drop 1
      darts_length := rightPrefix_leftDarts_length B k hkr
      vertices_length := rightPrefix_leftVertices_length B k hkr
      vertices_nodup := rightPrefix_leftVertices_nodup B k hkr
      start_vertex := ?_
      end_vertex := ?_
      edge_step := ?_ }
  · simpa only [List.get_eq_getElem, Nat.sub_zero, rightBoundaryVertexAt] using
      rightPrefix_leftVertices_get_prefix B k hkr 0 (by omega)
  · rw [List.get_eq_getElem,
      rightPrefix_leftVertices_get_suffix B k hkr (ℓ + k) (by omega) (by omega)]
    simpa only [Nat.add_sub_cancel_right, List.get_eq_getElem] using B.leftPath.end_vertex
  · intro i
    have hi : i.val < ℓ + k := by
      simpa only [rightPrefix_leftDarts_length B k hkr] using i.isLt
    have hlen : ((B.rightPath.darts.take k).reverse.map
        B.map.toCombinatorialMap.edgeInv).length = k := by
      simp only [List.length_map, List.length_reverse, List.length_take,
        B.rightPath.darts_length, Nat.min_eq_left (Nat.le_of_lt hkr)]
    by_cases hp : i.val < k
    · let j : Fin B.rightPath.darts.length := ⟨k - 1 - i.val, by
        rw [B.rightPath.darts_length]; omega⟩
      have hjmem : B.rightPath.darts.get j ∈ B.rightPath.darts.take k := by
        apply List.mem_iff_get.mpr
        refine ⟨⟨j.val, by dsimp [j]; rw [List.length_take, B.rightPath.darts_length]; omega⟩, ?_⟩
        simp [List.get_eq_getElem, j]
      have hd : ((B.rightPath.darts.take k).reverse.map
          B.map.toCombinatorialMap.edgeInv ++ B.leftPath.darts).get i =
          B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := by
        simp only [List.get_eq_getElem, List.getElem_append_left (by omega : i.val <
          ((B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv).length),
          List.getElem_map, List.getElem_reverse, List.getElem_take]
        simp only [List.length_take, B.rightPath.darts_length,
          Nat.min_eq_left (Nat.le_of_lt hkr)]
        rfl
      have hs : B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) ∈
          rightPrefixFlipDarts B k := by
        change _ ∈ B.rightPath.darts.take k ∨ _ ∈ B.rightPath.darts.take k
        exact Or.inr (by simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hjmem)
      have ht := B.rightPath.edge_step j
      have htail : (flipRightPrefix B k hk hkr).tail
          (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j)) := by
        rw [flipRightPrefix_tail_of_mem B k hk hkr _ hs,
          B.map.toCombinatorialMap.edgeInv_invol]
        exact ht.2.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · change ¬ (flipRightPrefix B k hk hkr).missing _
        rw [hd, flipRightPrefix_missing]
        exact B.noMissingDarts _
      · change (flipRightPrefix B k hk hkr).tail _
        rw [hd]
        exact htail
      · rw [List.get_eq_getElem,
          rightPrefix_leftVertices_get_prefix B k hkr i.val (by omega), hd]
        change B.rightPath.vertices[k - i.val]'(by rw [B.rightPath.vertices_length]; omega) =
          dartHeadVertex B.map (B.rightPath.darts.get j)
        have he : k - i.val = j.val + 1 := by dsimp [j]; omega
        simpa only [List.get_eq_getElem, he, dartHeadVertex] using ht.2.2.2
      · rw [List.get_eq_getElem,
          rightPrefix_leftVertices_get_prefix B k hkr (i.val + 1) (by omega), hd]
        change B.rightPath.vertices[k - (i.val + 1)]'(by rw [B.rightPath.vertices_length]; omega) =
          dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j))
        simp only [dartHeadVertex, B.map.toCombinatorialMap.edgeInv_invol]
        have he : k - (i.val + 1) = j.val := by dsimp [j]; omega
        simpa only [List.get_eq_getElem, he, dartTailVertex] using ht.2.2.1
    · let j : Fin B.leftPath.darts.length := ⟨i.val - k, by
        rw [B.leftPath.darts_length]; omega⟩
      have hd : ((B.rightPath.darts.take k).reverse.map
          B.map.toCombinatorialMap.edgeInv ++ B.leftPath.darts).get i =
          B.leftPath.darts.get j := by
        simp only [List.get_eq_getElem, List.getElem_append_right (by omega :
          ((B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv).length ≤ i.val),
          hlen]
        rfl
      have ht := B.leftPath.edge_step j
      have htail : (flipRightPrefix B k hk hkr).tail (B.leftPath.darts.get j) := by
        rw [flipRightPrefix_tail_of_not_mem B k hk hkr _
          (rightPrefix_leftDart_not_selected B k _ (List.get_mem _ _))]
        exact ht.2.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · change ¬ (flipRightPrefix B k hk hkr).missing _
        rw [hd, flipRightPrefix_missing]
        exact B.noMissingDarts _
      · change (flipRightPrefix B k hk hkr).tail _
        rw [hd]
        exact htail
      · rw [List.get_eq_getElem,
          rightPrefix_leftVertices_get_suffix B k hkr i.val (by omega) (by omega), hd]
        exact ht.2.2.1
      · rw [List.get_eq_getElem,
          rightPrefix_leftVertices_get_suffix B k hkr (i.val + 1) (by omega) (by omega), hd]
        have he : i.val + 1 - k = j.val + 1 := by dsimp [j]; omega
        simpa only [List.get_eq_getElem, he, dartHeadVertex] using ht.2.2.2

/-- The constructed left path has the prescribed dart list -/
theorem rightPrefix_leftPath_darts {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    (rightPrefix_leftPath B k hk hkr).darts =
      (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv ++
        B.leftPath.darts := by
  unfold rightPrefix_leftPath
  rfl

/-- The constructed left path has the prescribed vertex list -/
theorem rightPrefix_leftPath_vertices {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    (rightPrefix_leftPath B k hk hkr).vertices =
      (B.rightPath.vertices.take (k + 1)).reverse ++ B.leftPath.vertices.drop 1 := by
  unfold rightPrefix_leftPath
  rfl

/-- The two new paths share only their endpoints (`lem-bdy-reverse`, -/
theorem rightPrefix_paths_internally_vertex_disjoint {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    ∀ v, v ∈ (rightPrefix_leftPath B k hk hkr).vertices →
      v ∈ (rightPrefix_suffixPath B k hk hkr).vertices →
      v = rightBoundaryVertexAt B k (Nat.le_of_lt hkr) ∨ v = B.sink := by
  unfold flipRightPrefix flipOrientation
  intro v hvL hvR
  rw [rightPrefix_leftPath_vertices] at hvL
  unfold rightPrefix_suffixPath at hvR
  change v ∈ B.rightPath.vertices.drop k at hvR
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hvR
  have hjlt : k + j.val < B.rightPath.vertices.length := by
    have := j.isLt
    simp only [List.length_drop] at this
    omega
  have hjget : B.rightPath.vertices[k + j.val] = v := by
    simpa only [List.get_eq_getElem, List.getElem_drop] using hj
  rcases List.mem_append.mp hvL with hpre | hleft
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_reverse.mp hpre)
    have hilt : i.val < k + 1 := by
      have := i.isLt
      simp only [List.length_take] at this
      omega
    have higet : B.rightPath.vertices[i.val]'(by
        rw [B.rightPath.vertices_length]; omega) = v := by
      simpa only [List.get_eq_getElem, List.getElem_take] using hi
    have heq := B.rightPath.vertices_nodup.getElem_inj.mp (higet.trans hjget.symm)
    have hjzero : j.val = 0 := by omega
    apply Or.inl
    rw [← hjget]
    simp only [hjzero, Nat.add_zero, rightBoundaryVertexAt, List.get_eq_getElem]
  · rcases B.paths_internally_vertex_disjoint v (List.mem_of_mem_drop hleft)
      (List.mem_of_mem_drop hvR) with hs | ht
    · have heq : B.rightPath.vertices[k + j.val] = B.rightPath.vertices[0]'(by
          rw [B.rightPath.vertices_length]; omega) :=
        hjget.trans (hs.trans B.rightPath.start_vertex.symm)
      have := B.rightPath.vertices_nodup.getElem_inj.mp heq
      omega
    · exact Or.inr ht

/-- The two new paths use disjoint edge orbits (`lem-bdy-reverse`, -/
theorem rightPrefix_paths_edge_disjoint {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    ∀ d, d ∈ (rightPrefix_leftPath B k hk hkr).darts →
      ∀ e, e ∈ (rightPrefix_suffixPath B k hk hkr).darts →
      ¬ Equiv.Perm.SameCycle (flipRightPrefix B k hk hkr).toCombinatorialMap.edgeInv d e := by
  intro d hd e he hc
  rw [rightPrefix_leftPath_darts] at hd
  unfold rightPrefix_suffixPath at he
  change e ∈ B.rightPath.darts.drop k at he
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e at hc
  rcases List.mem_append.mp hd with hp | hl
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    have ha := List.mem_reverse.mp ha
    have hc' := Equiv.Perm.sameCycle_apply_left.mp hc
    rcases (B.map.toCombinatorialMap.edgeInv_sameCycle_iff a e).mp hc' with h | h
    · subst e
      exact List.disjoint_take_drop (simplePath_darts_nodup B.rightPath)
        (Nat.le_refl k) ha he
    · have hta := rightPath_mem_tail B a (List.mem_of_mem_take ha)
      have hte := rightPath_mem_tail B e (List.mem_of_mem_drop he)
      exact ((B.map.tail_iff a (B.noMissingDarts a)).mp hta) (h ▸ hte)
  · exact B.paths_edge_disjoint d hl e (List.mem_of_mem_drop he) hc

/-- Old right tail darts are not in the outer-face word: otherwise they
would also be left darts (`lem-bdy-reverse`, -/
private theorem rightPath_dart_not_outer {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (d : D)
    (hd : d ∈ B.rightPath.darts) : ¬ B.map.IsOuter d := by
  intro ho
  have hul : d ∈ B.map.ulDarts := ⟨B.noMissingDarts d, rightPath_mem_tail B d hd, ho⟩
  have hl := (B.outerSplit.2.2.1 d).mpr hul
  exact B.paths_edge_disjoint d hl d hd (Equiv.Perm.SameCycle.refl _ _)

/-- The new left darts enumerate exactly the flipped upper-left outer -/
private theorem rightPrefix_leftPath_enumerates {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    EnumeratesSet (rightPrefix_leftPath B k hk hkr).darts
      (flipRightPrefix B k hk hkr).ulDarts := by
  intro d
  rw [rightPrefix_leftPath_darts]
  constructor
  · intro hd
    rcases List.mem_append.mp hd with hp | hl
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      have ha := List.mem_reverse.mp ha
      have hR : a ∈ B.rightPath.darts := List.mem_of_mem_take ha
      have ho : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv a) := by
        have hm : B.map.toCombinatorialMap.edgeInv a ∈
            B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
          List.mem_map.mpr ⟨a, List.mem_reverse.mpr hR, rfl⟩
        exact ((B.outerSplit.2.2.2.1 _).mp hm).2.2
      refine ⟨?_, ?_, ho⟩
      · rw [flipRightPrefix_missing]
        exact B.noMissingDarts _
      · have hs : B.map.toCombinatorialMap.edgeInv a ∈ rightPrefixFlipDarts B k := by
          change _ ∈ B.rightPath.darts.take k ∨ _ ∈ B.rightPath.darts.take k
          exact Or.inr (by simpa only [B.map.toCombinatorialMap.edgeInv_invol] using ha)
        rw [flipRightPrefix_tail_of_mem B k hk hkr _ hs,
          B.map.toCombinatorialMap.edgeInv_invol]
        exact rightPath_mem_tail B a hR
    · have hul := (B.outerSplit.2.2.1 d).mp hl
      refine ⟨?_, ?_, hul.2.2⟩
      · rw [flipRightPrefix_missing]
        exact B.noMissingDarts _
      · rw [flipRightPrefix_tail_of_not_mem B k hk hkr _
          (rightPrefix_leftDart_not_selected B k d hl)]
        exact hul.2.1
  · intro hd
    have ho : B.map.IsOuter d := hd.2.2
    by_cases hs : d ∈ rightPrefixFlipDarts B k
    · change d ∈ B.rightPath.darts.take k ∨
        B.map.toCombinatorialMap.edgeInv d ∈ B.rightPath.darts.take k at hs
      rcases hs with hs | hs
      · exact False.elim (rightPath_dart_not_outer B d (List.mem_of_mem_take hs) ho)
      · apply List.mem_append_left
        apply List.mem_map.mpr
        exact ⟨B.map.toCombinatorialMap.edgeInv d, List.mem_reverse.mpr hs,
          B.map.toCombinatorialMap.edgeInv_invol d⟩
    · apply List.mem_append_right
      apply (B.outerSplit.2.2.1 d).mpr
      refine ⟨B.noMissingDarts d, ?_, ho⟩
      exact (flipRightPrefix_tail_of_not_mem B k hk hkr d hs).mp hd.2.1

/-- The reversed opposite suffix darts enumerate the flipped lower-right
Helper; not counted. -/
private theorem rightPrefix_suffixPath_enumerates {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    EnumeratesSet ((B.rightPath.darts.drop k).reverse.map
      B.map.toCombinatorialMap.edgeInv) (flipRightPrefix B k hk hkr).lrDarts := by
  intro d
  constructor
  · intro hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    have ha := List.mem_reverse.mp ha
    have hR := List.mem_of_mem_drop ha
    have hold := (B.outerSplit.2.2.2.1 _).mp
      (List.mem_map.mpr ⟨a, List.mem_reverse.mpr hR, rfl⟩)
    have hns : a ∉ rightPrefixFlipDarts B k := by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
      exact hi ▸ rightSuffix_dart_not_selected B k hkr i
    have hnsi : B.map.toCombinatorialMap.edgeInv a ∉ rightPrefixFlipDarts B k := by
      intro hs
      apply hns
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
        (rightPrefixFlip_condition B k).1 _ hs
    refine ⟨?_, ?_, hold.2.2⟩
    · rw [flipRightPrefix_missing]
      exact B.noMissingDarts _
    · intro ht
      exact hold.2.1 ((flipRightPrefix_tail_of_not_mem B k hk hkr _ hnsi).mp ht)
  · intro hd
    have ho : B.map.IsOuter d := hd.2.2
    have hns : d ∉ rightPrefixFlipDarts B k := by
      intro hs
      change d ∈ B.rightPath.darts.take k ∨
        B.map.toCombinatorialMap.edgeInv d ∈ B.rightPath.darts.take k at hs
      rcases hs with hs | hs
      · exact rightPath_dart_not_outer B d (List.mem_of_mem_take hs) ho
      · apply hd.2.1
        apply (flipRightPrefix_tail_of_mem B k hk hkr d (Or.inr hs)).mpr
        exact rightPath_mem_tail B _ (List.mem_of_mem_take hs)
    have hnot : ¬ B.map.tail d := by
      intro ht
      exact hd.2.1 ((flipRightPrefix_tail_of_not_mem B k hk hkr d hns).mpr ht)
    have hold : d ∈ B.map.lrDarts := ⟨B.noMissingDarts d, hnot, ho⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((B.outerSplit.2.2.2.1 d).mpr hold)
    have ha := List.mem_reverse.mp ha
    have hasplit : a ∈ B.rightPath.darts.take k ∨ a ∈ B.rightPath.darts.drop k := by
      rw [← List.mem_append, List.take_append_drop]
      exact ha
    rcases hasplit with hp | hs
    · apply False.elim
      apply hns
      change _ ∈ B.rightPath.darts.take k ∨ _ ∈ B.rightPath.darts.take k
      exact Or.inr (by simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hp)
    · exact List.mem_map.mpr ⟨a, List.mem_reverse.mpr hs, rfl⟩

/-- The unchanged outer word splits into the constructed boundary arcs
existing restricted carrier; not counted in the paper inventory. -/
theorem rightPrefix_outerSplit {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    FourArcsWitness (flipRightPrefix B k hk hkr) B.outerWord
      (rightPrefix_leftPath B k hk hkr).darts []
      ((rightPrefix_suffixPath B k hk hkr).darts.reverse.map
        (flipRightPrefix B k hk hkr).toCombinatorialMap.edgeInv) [] := by
  have hD : (rightPrefix_suffixPath B k hk hkr).darts = B.rightPath.darts.drop k := by
    unfold rightPrefix_suffixPath
    rfl
  have hsplit : B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv =
      (B.rightPath.darts.drop k).reverse.map B.map.toCombinatorialMap.edgeInv ++
        (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv := by
    calc
      _ = (B.rightPath.darts.take k ++ B.rightPath.darts.drop k).reverse.map
          B.map.toCombinatorialMap.edgeInv := by rw [List.take_append_drop]
      _ = _ := by rw [List.reverse_append, List.map_append]
  have hrot : B.outerWord.letters ~r
      (B.leftPath.darts ++ (B.rightPath.darts.drop k).reverse.map
        B.map.toCombinatorialMap.edgeInv) ++
          (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv := by
    simpa only [List.append_nil, hsplit, List.append_assoc] using B.outerSplit.2.1
  refine ⟨flipRightPrefix_outerCycle B k hk hkr, ?_,
    rightPrefix_leftPath_enumerates B k hk hkr, ?_, ?_, ?_⟩
  · rw [rightPrefix_leftPath_darts, hD]
    change B.outerWord.letters ~r
      (((B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv ++
        B.leftPath.darts) ++ [] ++
        (B.rightPath.darts.drop k).reverse.map B.map.toCombinatorialMap.edgeInv ++ [])
    simpa only [List.append_nil, List.append_assoc] using
      hrot.trans List.isRotated_append
  · change EnumeratesSet ((rightPrefix_suffixPath B k hk hkr).darts.reverse.map
      B.map.toCombinatorialMap.edgeInv) (flipRightPrefix B k hk hkr).lrDarts
    rw [hD]
    exact rightPrefix_suffixPath_enumerates B k hk hkr
  · intro d hd
    cases hd
  · intro d hd
    cases hd

/-- The right-prefix reversal has the required boundary paths, disjointness
and outer-word split (`lem-bdy-reverse`,
simple-boundary carrier, not a resolution of the unrestricted printed
claim or source issue simple-boundary restriction, and is not counted in the paper inventory. -/
theorem rightPrefixBoundaryPaths_exists {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    rightPrefixBoundaryPathsGoal B k hk hkr := by
  unfold rightPrefixBoundaryPathsGoal
  refine ⟨{
    leftPath := rightPrefix_leftPath B k hk hkr
    leftPath_darts := ?_
    leftPath_vertices := rightPrefix_leftPath_vertices B k hk hkr
    rightPath := rightPrefix_suffixPath B k hk hkr
    rightPath_darts := ?_
    rightPath_vertices := ?_
    paths_internally_vertex_disjoint := rightPrefix_paths_internally_vertex_disjoint B k hk hkr
    paths_edge_disjoint := rightPrefix_paths_edge_disjoint B k hk hkr
    outerSplit := rightPrefix_outerSplit B k hk hkr }⟩
  · simpa only [rightBoundaryPrefixDarts] using rightPrefix_leftPath_darts B k hk hkr
  · unfold rightPrefix_suffixPath
    rfl
  · unfold rightPrefix_suffixPath
    rfl

end DirectedDistances.PlanarMap
