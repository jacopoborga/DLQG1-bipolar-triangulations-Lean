/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

/-! # Right half of a planar path cut

paper result. This file records inherited dart and orientation facts for the
right half cut. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- For any edge-closed dart subset, the cycles of its induced first-return
rotation are exactly the original rotation cycles restricted to that subset.
paper result. -/
theorem closedHalf_vertex_sameCycle_iff_base
    (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    (hpresent : ∀ d : D, d ∈ S → ¬ B.missing d)
    (hne : ∃ d : D, d ∈ S)
    {a b : {d : D // d ∈ S}} :
    Equiv.Perm.SameCycle
        (closedHalfDirectedMap B S hclosed hpresent hne).rot a b ↔
      Equiv.Perm.SameCycle B.toCombinatorialMap.rot a.1 b.1 := by
  let σ := B.toCombinatorialMap.rot
  let ρ := firstReturnPerm σ S
  let H := closedHalfDirectedMap B S hclosed hpresent hne
  have hstepBase (x : {d : D // d ∈ S}) :
      Equiv.Perm.SameCycle B.toCombinatorialMap.rot x.1 (H.rot x).1 := by
    obtain ⟨k, hk, hrot, _⟩ :=
      (closedHalfEmbeddingFields B S hclosed hpresent hne).2.2.2 x
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast, ← perm_iterate_eq_pow]
    exact hrot
  have hiter (k : ℕ) (x : {d : D // d ∈ S}) :
      Equiv.Perm.SameCycle B.toCombinatorialMap.rot x.1
        ((H.rot : _ → _)^[k] x).1 := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (hstepBase ((H.rot : _ → _)^[k] x))
  have hstrong : ∀ k : ℕ, ∀ x y : {d : D // d ∈ S},
      (σ : D → D)^[k] x.1 = y.1 → Equiv.Perm.SameCycle ρ x y := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro x y hxy
        by_cases hk : k = 0
        · subst k
          have hval : x.1 = y.1 := by simpa using hxy
          have hsub : x = y := Subtype.ext hval
          simpa [hsub] using (Equiv.Perm.SameCycle.refl ρ x)
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          have hret : (σ : D → D)^[k] x.1 ∈ S := by
            rw [hxy]
            exact y.2
          let t := firstReturnTime σ S x
          have htpos := (firstReturnTime_spec σ S x).1
          have htle := firstReturnTime_min σ S x hkpos hret
          by_cases htk : t = k
          · have hreturn : (firstReturn σ S x).1 = y.1 := by
              calc
                (firstReturn σ S x).1 = (σ : D → D)^[t] x.1 :=
                  (firstReturn_characterization σ S x).1.symm
                _ = (σ : D → D)^[k] x.1 := by rw [htk]
                _ = y.1 := hxy
            have hcycle : ρ x = y := Subtype.ext hreturn
            refine ⟨(1 : ℤ), ?_⟩
            simp [hcycle]
          · have htk' : t < k := Nat.lt_of_le_of_ne htle htk
            let z := firstReturn σ S x
            have hnext : (σ : D → D)^[k - t] z.1 = y.1 := by
              calc
                (σ : D → D)^[k - t] z.1 =
                    (σ : D → D)^[k - t] ((σ : D → D)^[t] x.1) := by
                      exact congrArg (fun q : D => (σ : D → D)^[k - t] q)
                        (firstReturn_characterization σ S x).1.symm
                _ = (σ : D → D)^[(k - t) + t] x.1 :=
                      (Function.iterate_add_apply (σ : D → D) (k - t) t x.1).symm
                _ = (σ : D → D)^[k] x.1 := by
                      congr 1
                      omega
                _ = y.1 := hxy
            have hrecursive := ih (k - t) (by omega) z y hnext
            have hstep : Equiv.Perm.SameCycle ρ x z := by
              refine ⟨(1 : ℤ), ?_⟩
              simp only [zpow_one]
              rfl
            exact hstep.trans hrecursive
  constructor
  · intro hab
    obtain ⟨k, _hk, hpow⟩ := hab.exists_pow_eq'
    have hiterEq : (H.rot ^ k) a = b := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hval : ((H.rot : _ → _)^[k] a).1 = b.1 := congrArg Subtype.val hiterEq
    have hlast : Equiv.Perm.SameCycle B.toCombinatorialMap.rot
        ((H.rot : _ → _)^[k] a).1 b.1 := by rw [hval]
    exact (hiter k a).trans hlast
  · intro hab
    obtain ⟨k, _hk, hpow⟩ := hab.exists_pow_eq'
    have hiterEq : (σ : D → D)^[k] a.1 = b.1 := by
      simpa only [perm_iterate_eq_pow] using hpow
    change Equiv.Perm.SameCycle ρ a b
    exact hstrong k a b hiterEq

/-- A cycle of the right-half first-return rotation maps to a cycle of the
original rotation. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_vertex_sameCycle_to_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {a b : {d : D // d ∈ pathCutRightHalfDarts B P}}
    (hab : Equiv.Perm.SameCycle (pathCutRightHalfDirectedMap B P).rot a b) :
    Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot a.1 b.1 := by
  exact (closedHalf_vertex_sameCycle_iff_base B.map
    (pathCutRightHalfDarts B P)
    (fun d hd => pathCutRightHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d)
    (pathCutRightHalfDarts_nonempty B P)).mp (by
      simpa only [pathCutRightHalfDirectedMap] using hab)

/-- The first-return rotation has exactly the original rotation cycles
restricted to the right-half dart subset. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_vertex_sameCycle_iff_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {a b : {d : D // d ∈ pathCutRightHalfDarts B P}} :
    Equiv.Perm.SameCycle (pathCutRightHalfDirectedMap B P).rot a b ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot a.1 b.1 := by
  exact closedHalf_vertex_sameCycle_iff_base B.map
    (pathCutRightHalfDarts B P)
    (fun d hd => pathCutRightHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d)
    (pathCutRightHalfDarts_nonempty B P)

/-- The vertex map induced by inclusion of the right half into the original
the paper result. -/
@[expose] noncomputable def pathCutRightHalfVertexMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    MapVertex (pathCutRightHalfDirectedMap B P) → MapVertex B.map :=
  Quotient.map Subtype.val (by
    intro a b hab
    exact pathCutRightHalf_vertex_sameCycle_to_base B P hab)

/-- Every dart of the original right boundary path lies in the right closed
half of the cut. The right boundary arc is seeded with reversed opposite
darts; edge closure then includes the original boundary darts. Helper toward -/
theorem pathCutRightHalf_rightPath_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ B.rightPath.darts) :
    d ∈ pathCutRightHalfDarts B P := by
  have hrev : B.map.toCombinatorialMap.edgeInv d ∈
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv := by
    apply List.mem_map.mpr
    refine ⟨d, List.mem_reverse.mpr hd, rfl⟩
  have houter : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightOuterArc B :=
    (mem_pathCutRightOuterArc_iff B (B.map.toCombinatorialMap.edgeInv d)).2 hrev
  have hright : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightDarts B P :=
    ⟨B.map.toCombinatorialMap.edgeInv d, Or.inl houter,
      Relation.ReflTransGen.refl⟩
  have hhalf : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P :=
    Or.inl hright
  have hclosed := pathCutRightHalf_edgeInv_mem B P hhalf
  simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hclosed

/-- Every dart of the cut path lies in the right closed half of the cut by
its seam membership. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_path_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) :
    d ∈ pathCutRightHalfDarts B P := by
  change d ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P
  exact Or.inr (Or.inl hd)

/-- The right-half vertex map sends each dart tail to the original dart tail.
paper result. -/
theorem pathCutRightHalfVertexMap_dartTailVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    pathCutRightHalfVertexMap B P (dartTailVertex
      (pathCutRightHalfDirectedMap B P) d) = dartTailVertex B.map d.1 := by
  rfl

/-- The right-half vertex map sends each dart head to the original dart head.
paper result. -/
theorem pathCutRightHalfVertexMap_dartHeadVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    pathCutRightHalfVertexMap B P (dartHeadVertex
      (pathCutRightHalfDirectedMap B P) d) = dartHeadVertex B.map d.1 := by
  change Quotient.mk _ ((pathCutRightHalfDirectedMap B P).toCombinatorialMap.edgeInv d).1 =
    Quotient.mk _ (B.map.toCombinatorialMap.edgeInv d.1)
  rw [(pathCutRightHalf_embedding_fields B P).2.1 d]

/-- The right-half vertex map is injective. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfVertexMap_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    Function.Injective (pathCutRightHalfVertexMap B P) := by
  intro v w hvw
  revert hvw
  refine Quotient.inductionOn₂ v w ?_
  intro a b hab
  change Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.rot) a.1 =
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.rot) b.1 at hab
  apply Quotient.sound
  exact (pathCutRightHalf_vertex_sameCycle_iff_base B P).2 (Quotient.exact hab)

/-- The half vertex at a path index, represented by the outgoing dart tail
except at the final index, where it is the last dart head. Helper toward -/
@[expose] noncomputable def pathCutRightHalfPathVertexAt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutRightHalfDarts B P)
    (hk : 0 < k) (i : Fin (k + 1)) :
    MapVertex (pathCutRightHalfDirectedMap B P) :=
  if hi : i.val < k then
    dartTailVertex (pathCutRightHalfDirectedMap B P)
      ⟨Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact hi⟩,
        hmem _ (List.get_mem _ _)⟩
  else
    dartHeadVertex (pathCutRightHalfDirectedMap B P)
      ⟨Q.darts.get ⟨k - 1, by rw [Q.darts_length]; omega⟩,
        hmem _ (List.get_mem _ _)⟩

/-- The indexed right-half vertex maps to the corresponding vertex of the
original path. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfPathVertexAt_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutRightHalfDarts B P)
    (hk : 0 < k) (i : Fin (k + 1)) :
    pathCutRightHalfVertexMap B P (pathCutRightHalfPathVertexAt B P Q hmem hk i) =
      Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; exact i.isLt⟩ := by
  by_cases hi : i.val < k
  · have hstep := Q.edge_step ⟨i.val, by rw [Q.darts_length]; exact hi⟩
    rw [pathCutRightHalfPathVertexAt, dite_eq_left hi]
    rw [pathCutRightHalfVertexMap_dartTailVertex]
    exact hstep.2.2.1.symm
  · have hi' : i.val = k := by omega
    have hiFin : i = ⟨k, by omega⟩ := Fin.ext hi'
    rw [hiFin]
    have hstep := Q.edge_step ⟨k - 1, by rw [Q.darts_length]; omega⟩
    rw [pathCutRightHalfPathVertexAt, dite_eq_right (show ¬ k < k by omega)]
    change pathCutRightHalfVertexMap B P (dartHeadVertex
      (pathCutRightHalfDirectedMap B P)
        ⟨Q.darts.get ⟨k - 1, by rw [Q.darts_length]; omega⟩,
          hmem _ (List.get_mem _ _)⟩) = _
    rw [pathCutRightHalfVertexMap_dartHeadVertex]
    simpa only [Nat.sub_add_cancel hk] using hstep.2.2.2.symm

/-- Lift a positive-length path with right-half darts to a simple directed
path in the half map. Helper toward `lem-lr-ind` -/
noncomputable def pathCutRightHalf_liftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hk : 0 < k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutRightHalfDarts B P) :
    SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfPathVertexAt B P Q hmem hk ⟨0, by omega⟩)
      (pathCutRightHalfPathVertexAt B P Q hmem hk ⟨k, by omega⟩) k := by
  let E : Fin k → {d : D // d ∈ pathCutRightHalfDarts B P} := fun i =>
    ⟨Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩,
      hmem _ (List.get_mem _ _)⟩
  let V : Fin (k + 1) → MapVertex (pathCutRightHalfDirectedMap B P) :=
    fun i => pathCutRightHalfPathVertexAt B P Q hmem hk i
  refine {
    darts := List.ofFn E
    vertices := List.ofFn V
    darts_length := by simp
    vertices_length := by simp
    vertices_nodup := ?_
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_ }
  · apply List.nodup_ofFn.mpr
    intro i j hij
    have hbase : Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ =
        Q.vertices.get ⟨j.val, by rw [Q.vertices_length]; omega⟩ := by
      calc
        Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ =
            pathCutRightHalfVertexMap B P (V i) :=
          (pathCutRightHalfPathVertexAt_map B P Q hmem hk i).symm
        _ = pathCutRightHalfVertexMap B P (V j) := congrArg _ hij
        _ = Q.vertices.get ⟨j.val, by rw [Q.vertices_length]; omega⟩ :=
          pathCutRightHalfPathVertexAt_map B P Q hmem hk j
    have hindex := Q.vertices_nodup.get_inj_iff.mp hbase
    have hval : i.val = j.val := by
      simpa only [Fin.val_mk] using
        congrArg (fun a : Fin Q.vertices.length => a.val) hindex
    exact Fin.ext hval
  · rw [List.get_ofFn]
    rfl
  · rw [List.get_ofFn]
    rfl
  · intro i
    have hi : i.val < k := by simpa using i.isLt
    let j : Fin k := ⟨i.val, hi⟩
    let jQ : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact hi⟩
    let vi : Fin (k + 1) := ⟨i.val, by omega⟩
    let vi' : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    have hstep := Q.edge_step jQ
    have hdart : (List.ofFn E).get i = E j := by
      rw [List.get_ofFn]
      rfl
    have hgetVi : (List.ofFn V).get ⟨i.val, by simp; omega⟩ = V vi := by
      rw [List.get_ofFn]
      rfl
    have hgetVi' : (List.ofFn V).get ⟨i.val + 1, by simp; omega⟩ = V vi' := by
      rw [List.get_ofFn]
      rfl
    rw [hdart]
    refine ⟨by simp [pathCutRightHalfDirectedMap, closedHalfDirectedMap], ?_, ?_, ?_⟩
    · exact ((pathCutRightHalf_embedding_fields B P).2.2.1 (E j)).2 hstep.2.1
    · apply pathCutRightHalfVertexMap_injective B P
      calc
        pathCutRightHalfVertexMap B P ((List.ofFn V).get ⟨i.val, by simp; omega⟩) =
            Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ := by
              rw [hgetVi]
              exact pathCutRightHalfPathVertexAt_map B P Q hmem hk vi
        _ = dartTailVertex B.map (Q.darts.get jQ) := hstep.2.2.1
        _ = pathCutRightHalfVertexMap B P
            (dartTailVertex (pathCutRightHalfDirectedMap B P) (E j)) :=
              (pathCutRightHalfVertexMap_dartTailVertex B P (E j)).symm
    · apply pathCutRightHalfVertexMap_injective B P
      calc
        pathCutRightHalfVertexMap B P ((List.ofFn V).get ⟨i.val + 1, by simp; omega⟩) =
            Q.vertices.get ⟨i.val + 1, by rw [Q.vertices_length]; omega⟩ := by
              rw [hgetVi']
              exact pathCutRightHalfPathVertexAt_map B P Q hmem hk vi'
        _ = dartHeadVertex B.map (Q.darts.get jQ) := hstep.2.2.2
        _ = pathCutRightHalfVertexMap B P
            (dartHeadVertex (pathCutRightHalfDirectedMap B P) (E j)) :=
              (pathCutRightHalfVertexMap_dartHeadVertex B P (E j)).symm

/-- The lifted right-half path has exactly the original dart list after
forgetting its half-membership proofs. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_liftPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hk : 0 < k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutRightHalfDarts B P) :
    (pathCutRightHalf_liftPath B P Q hk hmem).darts.unattach = Q.darts := by
  classical
  simp only [pathCutRightHalf_liftPath, List.unattach, List.map_ofFn]
  apply List.ext_get
  · simp [Q.darts_length]
  · intro i h₁ h₂
    simp

/-- The right-half vertex representing the original source, using the first
dart of the right boundary path. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutRightHalfSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    MapVertex (pathCutRightHalfDirectedMap B P) :=
  pathCutRightHalfPathVertexAt B P B.rightPath
    (fun d hd => pathCutRightHalf_rightPath_mem B P hd)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos)
    ⟨0, by omega⟩

/-- The right-half vertex representing the original sink, using the last dart
of the right boundary path. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutRightHalfSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    MapVertex (pathCutRightHalfDirectedMap B P) :=
  pathCutRightHalfPathVertexAt B P B.rightPath
    (fun d hd => pathCutRightHalf_rightPath_mem B P hd)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos)
    ⟨r, by omega⟩

/-- The right-half source maps to the original source. Helper toward -/
theorem pathCutRightHalfSource_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    pathCutRightHalfVertexMap B P (pathCutRightHalfSource B P) = B.source := by
  rw [pathCutRightHalfSource, pathCutRightHalfPathVertexAt_map]
  exact B.rightPath.start_vertex

/-- The right-half sink maps to the original sink. Helper toward -/
theorem pathCutRightHalfSink_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    pathCutRightHalfVertexMap B P (pathCutRightHalfSink B P) = B.sink := by
  rw [pathCutRightHalfSink, pathCutRightHalfPathVertexAt_map]
  exact B.rightPath.end_vertex

/-- The original source and sink are distinct, witnessed by the positive
right boundary path. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_baseSource_ne_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : B.source ≠ B.sink := by
  intro hst
  let i : Fin B.rightPath.vertices.length :=
    ⟨0, by rw [B.rightPath.vertices_length]; omega⟩
  let j : Fin B.rightPath.vertices.length :=
    ⟨r, by rw [B.rightPath.vertices_length]; omega⟩
  have hvertices : B.rightPath.vertices.get i = B.rightPath.vertices.get j := by
    calc
      B.rightPath.vertices.get i = B.source := B.rightPath.start_vertex
      _ = B.sink := hst
      _ = B.rightPath.vertices.get j := B.rightPath.end_vertex.symm
  have hindex := B.rightPath.vertices_nodup.get_inj_iff.mp hvertices
  have hval := congrArg Fin.val hindex
  dsimp [i, j] at hval
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos
  omega

/-- The positive-length cut path has positive length, since its endpoints
are distinct. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_path_length_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  exact (pathCutRightHalf_baseSource_ne_sink B) (P.start_vertex.symm.trans P.end_vertex)

/-- The right boundary path lifted to the right half map. Helper toward -/
noncomputable def rightPathHalf
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) r := by
  exact pathCutRightHalf_liftPath B P B.rightPath
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos)
    (fun d hd => pathCutRightHalf_rightPath_mem B P hd)

/-- The cut path lifted to the right half map with the same half-map endpoints
as the right boundary path. Helper toward `lem-lr-ind` -/
noncomputable def cutPathRightHalf
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) n := by
  have hsource : pathCutRightHalfPathVertexAt B P P
      (fun d hd => pathCutRightHalf_path_mem B P hd)
      (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩ =
        pathCutRightHalfSource B P := by
    apply pathCutRightHalfVertexMap_injective B P
    rw [pathCutRightHalfPathVertexAt_map, pathCutRightHalfSource_map]
    exact P.start_vertex
  have hsink : pathCutRightHalfPathVertexAt B P P
      (fun d hd => pathCutRightHalf_path_mem B P hd)
      (pathCutRightHalf_path_length_pos B P) ⟨n, by omega⟩ =
        pathCutRightHalfSink B P := by
    apply pathCutRightHalfVertexMap_injective B P
    rw [pathCutRightHalfPathVertexAt_map, pathCutRightHalfSink_map]
    exact P.end_vertex
  rw [← hsource, ← hsink]
  exact pathCutRightHalf_liftPath B P P (pathCutRightHalf_path_length_pos B P)
    (fun d hd => pathCutRightHalf_path_mem B P hd)

/-- The right boundary path keeps its dart list under the half-map lift.
paper result. -/
theorem rightPathHalf_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (rightPathHalf B P).darts.unattach = B.rightPath.darts := by
  exact pathCutRightHalf_liftPath_darts B P B.rightPath
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos)
    (fun d hd => pathCutRightHalf_rightPath_mem B P hd)

/-- A directed step in the right half induces the corresponding directed
step in the original map. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_directedStep_to_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {v w : MapVertex (pathCutRightHalfDirectedMap B P)}
    (h : (pathCutRightHalfDirectedMap B P).directedStep v w) :
    B.map.directedStep (pathCutRightHalfVertexMap B P v)
      (pathCutRightHalfVertexMap B P w) := by
  rcases h with ⟨d, _hmissing, htail, hv, hw⟩
  have he := pathCutRightHalf_embedding_fields B P
  refine ⟨d.1, B.noMissingDarts d.1, (he.2.2.1 d).mp htail, ?_, ?_⟩
  · simpa [pathCutRightHalfVertexMap] using
      congrArg (pathCutRightHalfVertexMap B P) hv
  · have hflip := he.2.1 d
    change Quotient.mk _ (B.map.toCombinatorialMap.edgeInv d.1) = _
    simpa [pathCutRightHalfVertexMap, hflip] using
      congrArg (pathCutRightHalfVertexMap B P) hw

/-- A directed cycle in the right half would induce one in the original map;
therefore the half orientation is acyclic. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_acyclic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfDirectedMap B P).IsAcyclic := by
  intro v hcycle
  have mapTrans {a b : MapVertex (pathCutRightHalfDirectedMap B P)}
      (h : Relation.TransGen (pathCutRightHalfDirectedMap B P).directedStep a b) :
      Relation.TransGen B.map.directedStep
        (pathCutRightHalfVertexMap B P a) (pathCutRightHalfVertexMap B P b) := by
    induction h with
    | single h =>
        exact Relation.TransGen.single (pathCutRightHalf_directedStep_to_base B P h)
    | tail hab hbc ih =>
        exact Relation.TransGen.tail ih (pathCutRightHalf_directedStep_to_base B P hbc)
  exact B.acyclic (pathCutRightHalfVertexMap B P v) (mapTrans hcycle)

end DirectedDistances.PlanarMap

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem pathDarts_mpr_source
    {M : DirectedMapWithMissing D} {s s' t : MapVertex M} {k : ℕ}
    (h : s = s') (Q : SimpleDirectedDartPath M s' t k) :
    (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath M x t k) h) Q).darts =
      Q.darts := by
  cases h
  rfl

private theorem pathDarts_mpr_sink
    {M : DirectedMapWithMissing D} {s t t' : MapVertex M} {k : ℕ}
    (h : t = t') (Q : SimpleDirectedDartPath M s t' k) :
    (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath M s x k) h) Q).darts =
      Q.darts := by
  cases h
  rfl

/-- The lifted cut path has exactly the original dart list after forgetting
its half-membership proofs. Helper toward `lem-lr-ind` -/
theorem cutPathRightHalf_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (cutPathRightHalf B P).darts.unattach = P.darts := by
  have hsource : pathCutRightHalfPathVertexAt B P P
      (fun d hd => pathCutRightHalf_path_mem B P hd)
      (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩ =
        pathCutRightHalfSource B P := by
    apply pathCutRightHalfVertexMap_injective B P
    rw [pathCutRightHalfPathVertexAt_map, pathCutRightHalfSource_map]
    exact P.start_vertex
  have hsink : pathCutRightHalfPathVertexAt B P P
      (fun d hd => pathCutRightHalf_path_mem B P hd)
      (pathCutRightHalf_path_length_pos B P) ⟨n, by omega⟩ =
        pathCutRightHalfSink B P := by
    apply pathCutRightHalfVertexMap_injective B P
    rw [pathCutRightHalfPathVertexAt_map, pathCutRightHalfSink_map]
    exact P.end_vertex
  have hcut : cutPathRightHalf B P =
      Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutRightHalfDirectedMap B P) x (pathCutRightHalfSink B P) n)
        hsource.symm)
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutRightHalfDirectedMap B P)
            (pathCutRightHalfPathVertexAt B P P
              (fun d hd => pathCutRightHalf_path_mem B P hd)
              (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm)
          (pathCutRightHalf_liftPath B P P
            (pathCutRightHalf_path_length_pos B P)
            (fun d hd => pathCutRightHalf_path_mem B P hd))) := by
    rfl
  let Q := pathCutRightHalf_liftPath B P P
    (pathCutRightHalf_path_length_pos B P)
    (fun d hd => pathCutRightHalf_path_mem B P hd)
  have hinner :
      (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutRightHalfDirectedMap B P)
          (pathCutRightHalfPathVertexAt B P P
            (fun d hd => pathCutRightHalf_path_mem B P hd)
            (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
        hsink.symm) Q).darts = Q.darts := by
    exact pathDarts_mpr_sink hsink.symm Q
  have houter :
      (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutRightHalfDirectedMap B P) x (pathCutRightHalfSink B P) n)
        hsource.symm)
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutRightHalfDirectedMap B P)
            (pathCutRightHalfPathVertexAt B P P
              (fun d hd => pathCutRightHalf_path_mem B P hd)
              (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm) Q)).darts =
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutRightHalfDirectedMap B P)
            (pathCutRightHalfPathVertexAt B P P
              (fun d hd => pathCutRightHalf_path_mem B P hd)
              (pathCutRightHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm) Q).darts := by
    exact pathDarts_mpr_source hsource.symm _
  rw [hcut, houter, hinner]
  exact pathCutRightHalf_liftPath_darts B P P
    (pathCutRightHalf_path_length_pos B P)
    (fun d hd => pathCutRightHalf_path_mem B P hd)

end DirectedDistances.PlanarMap
