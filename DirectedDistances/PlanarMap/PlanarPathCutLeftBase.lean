/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

/-! # Left half of a planar path cut

paper result. This file records inherited dart and orientation facts for the
left half cut. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- A cycle of the induced first-return rotation maps to a cycle of the
original rotation. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_vertex_sameCycle_to_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {a b : {d : D // d ∈ pathCutLeftHalfDarts B P}}
    (hab : Equiv.Perm.SameCycle (pathCutLeftHalfDirectedMap B P).rot a b) :
    Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot a.1 b.1 := by
  let H := pathCutLeftHalfDirectedMap B P
  have hstep (x : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot x.1 (H.rot x).1 := by
    obtain ⟨k, hk, hrot, _⟩ := (pathCutLeftHalf_embedding_fields B P).2.2.2 x
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast, ← perm_iterate_eq_pow]
    exact hrot
  have hiter (k : ℕ) (x : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot x.1
        ((H.rot : _ → _)^[k] x).1 := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (hstep ((H.rot : _ → _)^[k] x))
  obtain ⟨k, _hk, hpow⟩ := hab.exists_pow_eq'
  have hiter_eq : (H.rot ^ k) a = b := by
    simpa only [perm_iterate_eq_pow] using hpow
  have hval : ((H.rot : _ → _)^[k] a).1 = b.1 := congrArg Subtype.val hiter_eq
  have hlast : Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
      ((H.rot : _ → _)^[k] a).1 b.1 := by
    rw [hval]
  exact (hiter k a).trans hlast

/-- The first-return rotation has exactly the original rotation cycles
restricted to the chosen dart subset. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_vertex_sameCycle_iff_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {a b : {d : D // d ∈ pathCutLeftHalfDarts B P}} :
    Equiv.Perm.SameCycle (pathCutLeftHalfDirectedMap B P).rot a b ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot a.1 b.1 := by
  constructor
  · exact pathCutLeftHalf_vertex_sameCycle_to_base B P
  · intro hab
    let σ := B.map.toCombinatorialMap.rot
    let H := pathCutLeftHalfDirectedMap B P
    let ρ := firstReturnPerm σ (pathCutLeftHalfDarts B P)
    have hstep (x : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
        Equiv.Perm.SameCycle ρ x (firstReturn σ (pathCutLeftHalfDarts B P) x) := by
      refine ⟨(1 : ℤ), ?_⟩
      simp only [zpow_one]
      rfl
    have hstrong : ∀ k : ℕ, ∀ x y : {d : D // d ∈ pathCutLeftHalfDarts B P},
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
              have hret : (σ : D → D)^[k] x.1 ∈ pathCutLeftHalfDarts B P := by
                rw [hxy]
                exact y.2
              let t := firstReturnTime σ (pathCutLeftHalfDarts B P) x
              have htpos := (firstReturnTime_spec σ (pathCutLeftHalfDarts B P) x).1
              have htle : t ≤ k := firstReturnTime_min σ
                (pathCutLeftHalfDarts B P) x hkpos hret
              by_cases htk : t = k
              · have hreturn : (firstReturn σ (pathCutLeftHalfDarts B P) x).1 = y.1 := by
                  calc
                    (firstReturn σ (pathCutLeftHalfDarts B P) x).1 =
                        (σ : D → D)^[t] x.1 :=
                          (firstReturn_characterization σ
                            (pathCutLeftHalfDarts B P) x).1.symm
                    _ = (σ : D → D)^[k] x.1 := by rw [htk]
                    _ = y.1 := hxy
                have hcycle : ρ x = y := Subtype.ext hreturn
                refine ⟨(1 : ℤ), ?_⟩
                simp [hcycle]
              · have htk' : t < k := Nat.lt_of_le_of_ne htle htk
                let z := firstReturn σ (pathCutLeftHalfDarts B P) x
                have hnext : (σ : D → D)^[k - t] z.1 = y.1 := by
                  calc
                    (σ : D → D)^[k - t] z.1 =
                        (σ : D → D)^[k - t]
                          ((σ : D → D)^[t] x.1) := by
                            exact congrArg (fun q : D => (σ : D → D)^[k - t] q)
                              (firstReturn_characterization σ
                                (pathCutLeftHalfDarts B P) x).1.symm
                    _ = (σ : D → D)^[(k - t) + t] x.1 :=
                          (Function.iterate_add_apply (σ : D → D) (k - t) t x.1).symm
                    _ = (σ : D → D)^[k] x.1 := by
                          congr 1
                          omega
                    _ = y.1 := hxy
                have hrecursive := ih (k - t) (by omega) z y hnext
                exact hstep x |>.trans hrecursive
    obtain ⟨k, _hk, hpow⟩ := hab.exists_pow_eq'
    have hiterEq : (σ : D → D)^[k] a.1 = b.1 := by
      simpa only [perm_iterate_eq_pow] using hpow
    change Equiv.Perm.SameCycle ρ a b
    exact hstrong k a b hiterEq

/-- The vertex map induced by the half inclusion, from half-map rotation
cycles to original-map rotation cycles. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutLeftHalfVertexMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    MapVertex (pathCutLeftHalfDirectedMap B P) → MapVertex B.map :=
  Quotient.map Subtype.val (by
    intro a b hab
    exact pathCutLeftHalf_vertex_sameCycle_to_base B P hab)

/-- The half-vertex map sends a dart tail to the original dart tail. Helper
result. -/
theorem pathCutLeftHalfVertexMap_dartTailVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    pathCutLeftHalfVertexMap B P (dartTailVertex
      (pathCutLeftHalfDirectedMap B P) d) = dartTailVertex B.map d.1 := by
  rfl

/-- The half-vertex map sends a dart head to the original dart head. Helper
result. -/
theorem pathCutLeftHalfVertexMap_dartHeadVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    pathCutLeftHalfVertexMap B P (dartHeadVertex
      (pathCutLeftHalfDirectedMap B P) d) = dartHeadVertex B.map d.1 := by
  change Quotient.mk _ ((pathCutLeftHalfDirectedMap B P).toCombinatorialMap.edgeInv d).1 =
    Quotient.mk _ (B.map.toCombinatorialMap.edgeInv d.1)
  rw [(pathCutLeftHalf_embedding_fields B P).2.1 d]

/-- The half-vertex map is injective. Every half-map vertex is represented by
a half dart, so the cycle correspondence gives injectivity on the full vertex
not the paper result. -/
theorem pathCutLeftHalfVertexMap_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    Function.Injective (pathCutLeftHalfVertexMap B P) := by
  intro v w hvw
  revert hvw
  refine Quotient.inductionOn₂ v w ?_
  intro a b hab
  change Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.rot) a.1 =
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.rot) b.1 at hab
  apply Quotient.sound
  exact (pathCutLeftHalf_vertex_sameCycle_iff_base B P).2 (Quotient.exact hab)

/-- Every dart of the original left boundary path is in the left half of the
the paper result. -/
theorem pathCutLeftHalf_leftPath_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ B.leftPath.darts) : d ∈ pathCutLeftHalfDarts B P := by
  apply Or.inl
  exact ⟨d, Or.inl ((mem_pathCutLeftOuterArc_iff B d).2 hd),
    Relation.ReflTransGen.refl⟩

/-- Every dart of the cut path is in the left half of the cut. Helper toward -/
theorem pathCutLeftHalf_path_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : d ∈ pathCutLeftHalfDarts B P := by
  apply Or.inl
  exact ⟨d, Or.inr hd, Relation.ReflTransGen.refl⟩

/-- The half vertex corresponding to a vertex index along a path whose darts
belong to the left half. Interior indices use the outgoing dart; the final
index uses the head of the last dart. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutLeftHalfPathVertexAt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutLeftHalfDarts B P)
    (hk : 0 < k) (i : Fin (k + 1)) :
    MapVertex (pathCutLeftHalfDirectedMap B P) :=
  if hi : i.val < k then
    dartTailVertex (pathCutLeftHalfDirectedMap B P)
      ⟨Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact hi⟩,
        hmem _ (List.get_mem _ _)⟩
  else
    dartHeadVertex (pathCutLeftHalfDirectedMap B P)
      ⟨Q.darts.get ⟨k - 1, by rw [Q.darts_length]; omega⟩,
        hmem _ (List.get_mem _ _)⟩

/-- The indexed half vertex maps to the corresponding vertex of the base
not the paper result. -/
theorem pathCutLeftHalfPathVertexAt_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutLeftHalfDarts B P)
    (hk : 0 < k) (i : Fin (k + 1)) :
    pathCutLeftHalfVertexMap B P (pathCutLeftHalfPathVertexAt B P Q hmem hk i) =
      Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; exact i.isLt⟩ := by
  by_cases hi : i.val < k
  · have hstep := Q.edge_step ⟨i.val, by rw [Q.darts_length]; exact hi⟩
    rw [pathCutLeftHalfPathVertexAt, dite_eq_left hi]
    rw [pathCutLeftHalfVertexMap_dartTailVertex]
    exact hstep.2.2.1.symm
  · have hi' : i.val = k := by omega
    have hiFin : i = ⟨k, by omega⟩ := Fin.ext hi'
    rw [hiFin]
    have hstep := Q.edge_step ⟨k - 1, by rw [Q.darts_length]; omega⟩
    rw [pathCutLeftHalfPathVertexAt, dite_eq_right (show ¬ k < k by omega)]
    change pathCutLeftHalfVertexMap B P (dartHeadVertex
      (pathCutLeftHalfDirectedMap B P)
        ⟨Q.darts.get ⟨k - 1, by rw [Q.darts_length]; omega⟩,
          hmem _ (List.get_mem _ _)⟩) = _
    rw [pathCutLeftHalfVertexMap_dartHeadVertex]
    simpa only [Nat.sub_add_cancel hk] using hstep.2.2.2.symm

/-- Lift a positive-length source-to-sink path whose darts belong to the left
half to a simple directed path in the half map. Helper toward `lem-lr-ind` -/
noncomputable def pathCutLeftHalf_liftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hk : 0 < k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutLeftHalfDarts B P) :
    SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfPathVertexAt B P Q hmem hk ⟨0, by omega⟩)
      (pathCutLeftHalfPathVertexAt B P Q hmem hk ⟨k, by omega⟩) k := by
  let E : Fin k → {d : D // d ∈ pathCutLeftHalfDarts B P} := fun i =>
    ⟨Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩,
      hmem _ (List.get_mem _ _)⟩
  let V : Fin (k + 1) → MapVertex (pathCutLeftHalfDirectedMap B P) :=
    fun i => pathCutLeftHalfPathVertexAt B P Q hmem hk i
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
            pathCutLeftHalfVertexMap B P (V i) :=
          (pathCutLeftHalfPathVertexAt_map B P Q hmem hk i).symm
        _ = pathCutLeftHalfVertexMap B P (V j) := congrArg _ hij
        _ = Q.vertices.get ⟨j.val, by rw [Q.vertices_length]; omega⟩ :=
          pathCutLeftHalfPathVertexAt_map B P Q hmem hk j
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
    refine ⟨by simp [pathCutLeftHalfDirectedMap, closedHalfDirectedMap], ?_, ?_, ?_⟩
    · exact ((pathCutLeftHalf_embedding_fields B P).2.2.1 (E j)).2 hstep.2.1
    · apply pathCutLeftHalfVertexMap_injective B P
      calc
        pathCutLeftHalfVertexMap B P ((List.ofFn V).get ⟨i.val, by simp; omega⟩) =
            Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ := by
              rw [hgetVi]
              exact pathCutLeftHalfPathVertexAt_map B P Q hmem hk vi
        _ = dartTailVertex B.map (Q.darts.get jQ) := hstep.2.2.1
        _ = pathCutLeftHalfVertexMap B P
            (dartTailVertex (pathCutLeftHalfDirectedMap B P) (E j)) :=
              (pathCutLeftHalfVertexMap_dartTailVertex B P (E j)).symm
    · apply pathCutLeftHalfVertexMap_injective B P
      calc
        pathCutLeftHalfVertexMap B P ((List.ofFn V).get ⟨i.val + 1, by simp; omega⟩) =
            Q.vertices.get ⟨i.val + 1, by rw [Q.vertices_length]; omega⟩ := by
              rw [hgetVi']
              exact pathCutLeftHalfPathVertexAt_map B P Q hmem hk vi'
        _ = dartHeadVertex B.map (Q.darts.get jQ) := hstep.2.2.2
        _ = pathCutLeftHalfVertexMap B P
            (dartHeadVertex (pathCutLeftHalfDirectedMap B P) (E j)) :=
              (pathCutLeftHalfVertexMap_dartHeadVertex B P (E j)).symm

/-- The half-map vertex at the start of the left boundary path, represented
by its first dart tail. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutLeftHalfSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    MapVertex (pathCutLeftHalfDirectedMap B P) :=
  pathCutLeftHalfPathVertexAt B P B.leftPath
    (fun d hd => pathCutLeftHalf_leftPath_mem B P hd)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos)
    ⟨0, by omega⟩

/-- The half-map vertex at the end of the left boundary path, represented by
the head of its last dart. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutLeftHalfSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    MapVertex (pathCutLeftHalfDirectedMap B P) :=
  pathCutLeftHalfPathVertexAt B P B.leftPath
    (fun d hd => pathCutLeftHalf_leftPath_mem B P hd)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos)
    ⟨ℓ, by omega⟩

/-- The half source maps to the original source. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfSource_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    pathCutLeftHalfVertexMap B P (pathCutLeftHalfSource B P) = B.source := by
  rw [pathCutLeftHalfSource, pathCutLeftHalfPathVertexAt_map]
  exact B.leftPath.start_vertex

/-- The half sink maps to the original sink. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfSink_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    pathCutLeftHalfVertexMap B P (pathCutLeftHalfSink B P) = B.sink := by
  rw [pathCutLeftHalfSink, pathCutLeftHalfPathVertexAt_map]
  exact B.leftPath.end_vertex

/-- The source and sink of the base carrier are distinct, as witnessed by
the positive-length simple left boundary path. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_baseSource_ne_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : B.source ≠ B.sink := by
  intro hst
  let i : Fin B.leftPath.vertices.length := ⟨0, by rw [B.leftPath.vertices_length]; omega⟩
  let j : Fin B.leftPath.vertices.length := ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩
  have hvertices : B.leftPath.vertices.get i = B.leftPath.vertices.get j := by
    calc
      B.leftPath.vertices.get i = B.source := B.leftPath.start_vertex
      _ = B.sink := hst
      _ = B.leftPath.vertices.get j := B.leftPath.end_vertex.symm
  have hindex := B.leftPath.vertices_nodup.get_inj_iff.mp hvertices
  have hval := congrArg Fin.val hindex
  dsimp [i, j] at hval
  have hℓ : 0 < ℓ := lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos
  omega

/-- The positive-length source-to-sink path `P` has positive length. Helper
result. -/
theorem pathCutLeftHalf_path_length_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  exact (pathCutLeftHalf_baseSource_ne_sink B) (P.start_vertex.symm.trans P.end_vertex)

/-- The left boundary path lifts to a simple directed path in the half map.
paper result. -/
noncomputable def leftPathHalf
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) ℓ := by
  exact pathCutLeftHalf_liftPath B P B.leftPath
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos)
    (fun d hd => pathCutLeftHalf_leftPath_mem B P hd)

/-- The cut path lifts to a simple directed path in the half map with the same
source and sink as the left boundary path. Helper toward `lem-lr-ind` -/
noncomputable def cutPathHalf
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) n := by
  have hsource : pathCutLeftHalfPathVertexAt B P P
      (fun d hd => pathCutLeftHalf_path_mem B P hd)
      (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩ =
        pathCutLeftHalfSource B P := by
    apply pathCutLeftHalfVertexMap_injective B P
    rw [pathCutLeftHalfPathVertexAt_map, pathCutLeftHalfSource_map]
    exact P.start_vertex
  have hsink : pathCutLeftHalfPathVertexAt B P P
      (fun d hd => pathCutLeftHalf_path_mem B P hd)
      (pathCutLeftHalf_path_length_pos B P) ⟨n, by omega⟩ =
        pathCutLeftHalfSink B P := by
    apply pathCutLeftHalfVertexMap_injective B P
    rw [pathCutLeftHalfPathVertexAt_map, pathCutLeftHalfSink_map]
    exact P.end_vertex
  rw [← hsource, ← hsink]
  exact pathCutLeftHalf_liftPath B P P (pathCutLeftHalf_path_length_pos B P)
    (fun d hd => pathCutLeftHalf_path_mem B P hd)

/-- The lifted left-half path has exactly the original dart list after
forgetting its half-membership proofs. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_liftPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink k)
    (hk : 0 < k)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ pathCutLeftHalfDarts B P) :
    (pathCutLeftHalf_liftPath B P Q hk hmem).darts.unattach = Q.darts := by
  classical
  simp only [pathCutLeftHalf_liftPath, List.unattach, List.map_ofFn]
  apply List.ext_get
  · simp [Q.darts_length]
  · intro i h₁ h₂
    simp

/-- The left boundary path keeps its dart list under the half-map lift.
paper result. -/
theorem leftPathHalf_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (leftPathHalf B P).darts.unattach = B.leftPath.darts := by
  exact pathCutLeftHalf_liftPath_darts B P B.leftPath
    (Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos)
    (fun d hd => pathCutLeftHalf_leftPath_mem B P hd)

/-- A directed step in the left half induces the corresponding directed step
in the original map. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_directedStep_to_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {v w : MapVertex (pathCutLeftHalfDirectedMap B P)}
    (h : (pathCutLeftHalfDirectedMap B P).directedStep v w) :
    B.map.directedStep (pathCutLeftHalfVertexMap B P v)
      (pathCutLeftHalfVertexMap B P w) := by
  rcases h with ⟨d, _hmissing, htail, hv, hw⟩
  have he := pathCutLeftHalf_embedding_fields B P
  refine ⟨d.1, B.noMissingDarts d.1, (he.2.2.1 d).mp htail, ?_, ?_⟩
  · simpa [pathCutLeftHalfVertexMap] using
      congrArg (pathCutLeftHalfVertexMap B P) hv
  · have hflip := he.2.1 d
    change Quotient.mk _ (B.map.toCombinatorialMap.edgeInv d.1) = _
    simpa [pathCutLeftHalfVertexMap, hflip] using
      congrArg (pathCutLeftHalfVertexMap B P) hw

/-- The half source has no incoming half-map dart. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfSource_isSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ¬ ∃ u, (pathCutLeftHalfDirectedMap B P).directedStep u
      (pathCutLeftHalfSource B P) := by
  rintro ⟨u, hu⟩
  have hbase := pathCutLeftHalf_directedStep_to_base B P hu
  rw [pathCutLeftHalfSource_map] at hbase
  exact B.isSource ⟨pathCutLeftHalfVertexMap B P u, hbase⟩

/-- The half sink has no outgoing half-map dart. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfSink_isSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ¬ ∃ w, (pathCutLeftHalfDirectedMap B P).directedStep
      (pathCutLeftHalfSink B P) w := by
  rintro ⟨w, hw⟩
  have hbase := pathCutLeftHalf_directedStep_to_base B P hw
  rw [pathCutLeftHalfSink_map] at hbase
  exact B.isSink ⟨pathCutLeftHalfVertexMap B P w, hbase⟩

/-- A directed cycle in the left half would induce one in the original map;
therefore the half orientation is acyclic. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_acyclic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfDirectedMap B P).IsAcyclic := by
  intro v hcycle
  have mapTrans {a b : MapVertex (pathCutLeftHalfDirectedMap B P)}
      (h : Relation.TransGen (pathCutLeftHalfDirectedMap B P).directedStep a b) :
      Relation.TransGen B.map.directedStep
        (pathCutLeftHalfVertexMap B P a) (pathCutLeftHalfVertexMap B P b) := by
    induction h with
    | single h =>
        exact Relation.TransGen.single (pathCutLeftHalf_directedStep_to_base B P h)
    | tail hab hbc ih =>
        exact Relation.TransGen.tail ih (pathCutLeftHalf_directedStep_to_base B P hbc)
  exact B.acyclic (pathCutLeftHalfVertexMap B P v) (mapTrans hcycle)

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
theorem cutPathHalf_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (cutPathHalf B P).darts.unattach = P.darts := by
  have hsource : pathCutLeftHalfPathVertexAt B P P
      (fun d hd => pathCutLeftHalf_path_mem B P hd)
      (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩ =
        pathCutLeftHalfSource B P := by
    apply pathCutLeftHalfVertexMap_injective B P
    rw [pathCutLeftHalfPathVertexAt_map, pathCutLeftHalfSource_map]
    exact P.start_vertex
  have hsink : pathCutLeftHalfPathVertexAt B P P
      (fun d hd => pathCutLeftHalf_path_mem B P hd)
      (pathCutLeftHalf_path_length_pos B P) ⟨n, by omega⟩ =
        pathCutLeftHalfSink B P := by
    apply pathCutLeftHalfVertexMap_injective B P
    rw [pathCutLeftHalfPathVertexAt_map, pathCutLeftHalfSink_map]
    exact P.end_vertex
  have hcut : cutPathHalf B P =
      Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutLeftHalfDirectedMap B P) x (pathCutLeftHalfSink B P) n)
        hsource.symm)
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutLeftHalfDirectedMap B P)
            (pathCutLeftHalfPathVertexAt B P P
              (fun d hd => pathCutLeftHalf_path_mem B P hd)
              (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm)
          (pathCutLeftHalf_liftPath B P P
            (pathCutLeftHalf_path_length_pos B P)
            (fun d hd => pathCutLeftHalf_path_mem B P hd))) := by
    rfl
  let Q := pathCutLeftHalf_liftPath B P P
    (pathCutLeftHalf_path_length_pos B P)
    (fun d hd => pathCutLeftHalf_path_mem B P hd)
  have hinner :
      (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutLeftHalfDirectedMap B P)
          (pathCutLeftHalfPathVertexAt B P P
            (fun d hd => pathCutLeftHalf_path_mem B P hd)
            (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
        hsink.symm) Q).darts = Q.darts := by
    exact pathDarts_mpr_sink hsink.symm Q
  have houter :
      (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
          (pathCutLeftHalfDirectedMap B P) x (pathCutLeftHalfSink B P) n)
        hsource.symm)
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutLeftHalfDirectedMap B P)
            (pathCutLeftHalfPathVertexAt B P P
              (fun d hd => pathCutLeftHalf_path_mem B P hd)
              (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm) Q)).darts =
        (Eq.mpr (congrArg (fun x => SimpleDirectedDartPath
            (pathCutLeftHalfDirectedMap B P)
            (pathCutLeftHalfPathVertexAt B P P
              (fun d hd => pathCutLeftHalf_path_mem B P hd)
              (pathCutLeftHalf_path_length_pos B P) ⟨0, by omega⟩) x n)
          hsink.symm) Q).darts := by
    exact pathDarts_mpr_source hsource.symm _
  rw [hcut, houter, hinner]
  exact pathCutLeftHalf_liftPath_darts B P P
    (pathCutLeftHalf_path_length_pos B P)
    (fun d hd => pathCutLeftHalf_path_mem B P hd)

end DirectedDistances.PlanarMap
