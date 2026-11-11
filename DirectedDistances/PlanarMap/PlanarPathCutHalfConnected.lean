/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation
public import DirectedDistances.PlanarMap.PlanarPathCutHalves

/-! # Connectivity of the path-cut half maps

paper result. -/

public section
namespace DirectedDistances.PlanarMap

private theorem perm_step_sameCycle {α : Type*} (p : Equiv.Perm α) (x : α) :
    p.SameCycle x (p x) := by
  refine ⟨1, ?_⟩
  simp

private theorem firstReturnPerm_sameCycle_of_sameCycle {α : Type*}
    [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x y : S)
    (hxy : σ.SameCycle x.1 y.1) :
    (firstReturnPerm σ S).SameCycle x y := by
  rcases hxy.exists_nat_pow_eq with ⟨m, hm⟩
  have hm' : (σ : α → α)^[m] x.1 = y.1 := by
    rw [perm_iterate_eq_pow]
    exact hm
  have aux : ∀ m (x y : S), (σ : α → α)^[m] x.1 = y.1 →
      (firstReturnPerm σ S).SameCycle x y := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro x y hxy
        by_cases hm0 : m = 0
        · subst m
          simp only [Function.iterate_zero, id_eq] at hxy
          have hxy' : x = y := Subtype.ext hxy
          subst y
          exact Equiv.Perm.SameCycle.rfl
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          let τ := firstReturnTime σ S x
          have hret : (σ : α → α)^[m] x.1 ∈ S := hxy ▸ y.2
          have hτle : τ ≤ m := firstReturnTime_min σ S x hmpos hret
          have hτpos : 0 < τ := (firstReturnTime_spec σ S x).1
          let z := firstReturnPerm σ S x
          have hz : z.1 = (σ : α → α)^[τ] x.1 := by
            exact (firstReturn_characterization σ S x).1.symm
          by_cases hτm : τ = m
          · have hzy : z = y := by
              apply Subtype.ext
              rw [hz, hτm, hxy]
            rw [← hzy]
            exact perm_step_sameCycle (firstReturnPerm σ S) x
          · have hτlt : τ < m := Nat.lt_of_le_of_ne hτle hτm
            let rem := m - τ
            have hrem_lt : rem < m := by dsimp [rem]; omega
            have htail : (σ : α → α)^[rem] z.1 = y.1 := by
              calc
                (σ : α → α)^[rem] z.1 = (σ ^ rem) z.1 := by
                  rw [← perm_iterate_eq_pow]
                _ = (σ ^ rem) ((σ ^ τ) x.1) := by
                  rw [hz, perm_iterate_eq_pow]
                _ = ((σ ^ rem) * (σ ^ τ)) x.1 := by
                  simp only [Equiv.Perm.mul_apply]
                _ = (σ ^ (rem + τ)) x.1 := by
                  rw [← pow_add]
                _ = (σ ^ m) x.1 := by
                  congr 2
                  dsimp [rem]
                  omega
                _ = (σ : α → α)^[m] x.1 := by
                  rw [perm_iterate_eq_pow]
                _ = y.1 := hxy
            exact (perm_step_sameCycle (firstReturnPerm σ S) x).trans
              (ih rem hrem_lt z y htail)
  exact aux m x y hm'

private def mapConnectivityStep {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (x y : D) : Prop :=
  y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x

private theorem sameCycle_reachable {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) {x y : D}
    (hxy : M.rot.SameCycle x y) :
    Relation.ReflTransGen (mapConnectivityStep M) x y := by
  rcases hxy.exists_nat_pow_eq with ⟨k, hk⟩
  have hk' : (M.rot : D → D)^[k] x = y := by
    rw [perm_iterate_eq_pow]
    exact hk
  have aux : ∀ k x y, (M.rot : D → D)^[k] x = y →
      Relation.ReflTransGen (mapConnectivityStep M) x y := by
    intro k
    induction k with
    | zero =>
        intro x y h
        simp only [Function.iterate_zero, id_eq] at h
        subst y
        exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro x y h
        rw [Function.iterate_succ_apply] at h
        have hstep : mapConnectivityStep M x (M.rot x) := Or.inl rfl
        exact (Relation.ReflTransGen.single hstep).trans (ih _ _ h)
  exact aux k x y hk'

private theorem closedHalf_rot_reachable {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    {x y : {d : D // d ∈ S}}
    (hxy : B.toCombinatorialMap.rot.SameCycle x.1 y.1) :
    Relation.ReflTransGen
      (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed)) x y := by
  have hhalf :
      (closedHalfCombinatorialMap B S hclosed).rot.SameCycle x y := by
    change (firstReturnPerm B.toCombinatorialMap.rot S).SameCycle x y
    exact firstReturnPerm_sameCycle_of_sameCycle B.toCombinatorialMap.rot S x y hxy
  exact sameCycle_reachable (closedHalfCombinatorialMap B S hclosed) hhalf

private theorem path_darts_adjacent_sameCycle {D : Type*} [Fintype D]
    [DecidableEq D] {M : DirectedMapWithMissing D} {s t : MapVertex M}
    {k : ℕ} (P : SimpleDirectedDartPath M s t k)
    (i : Fin (P.darts.length - 1)) :
    M.toCombinatorialMap.rot.SameCycle
      (M.toCombinatorialMap.edgeInv
        (P.darts.get ⟨i.val, by omega⟩))
      (P.darts.get ⟨i.val + 1, by omega⟩) := by
  let i₀ : Fin P.darts.length := ⟨i.val, by omega⟩
  let i₁ : Fin P.darts.length := ⟨i.val + 1, by omega⟩
  have h₀ := P.edge_step i₀
  have h₁ := P.edge_step i₁
  let v : Fin P.vertices.length := ⟨i.val + 1, by
    rw [P.vertices_length]
    have hdlen := P.darts_length
    omega⟩
  have hhead : P.vertices.get v = dartHeadVertex M (P.darts.get i₀) := by
    simpa [v, i₀] using h₀.2.2.2
  have htail : P.vertices.get v = dartTailVertex M (P.darts.get i₁) := by
    simpa [v, i₁] using h₁.2.2.1
  have hv : dartHeadVertex M (P.darts.get i₀) = dartTailVertex M (P.darts.get i₁) := by
    calc
      dartHeadVertex M (P.darts.get i₀) = P.vertices.get v := hhead.symm
      _ = dartTailVertex M (P.darts.get i₁) := htail
  change Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
      (M.toCombinatorialMap.edgeInv (P.darts.get i₀)) =
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
      (P.darts.get i₁) at hv
  exact Quotient.exact hv

private theorem path_darts_isChain {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) :
    P.darts.IsChain (fun d e =>
      M.toCombinatorialMap.rot.SameCycle (M.toCombinatorialMap.edgeInv d) e) := by
  rw [List.isChain_iff_forall₂]
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro i hi₁ hi₂
    have hiAdd : i + 1 < P.darts.length := by
      simp only [List.length_dropLast] at hi₁
      omega
    have hleft :
        P.darts.dropLast.get ⟨i, hi₁⟩ = P.darts.get ⟨i, by omega⟩ := by
      change P.darts.dropLast[i] = P.darts[i]
      exact List.getElem_dropLast hi₁
    have hright :
        P.darts.tail.get ⟨i, hi₂⟩ = P.darts.get ⟨i + 1, hiAdd⟩ :=
      List.get_tail P.darts i hi₂
    rw [hleft, hright]
    exact path_darts_adjacent_sameCycle P ⟨i, by omega⟩

private theorem closedHalf_edgeInv_apply {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    (x : {d : D // d ∈ S}) :
    (closedHalfCombinatorialMap B S hclosed).edgeInv x =
      ⟨B.toCombinatorialMap.edgeInv x.1, hclosed x.1 x.2⟩ := by
  change restrictedPerm B.toCombinatorialMap.edgeInv S hclosed x = _
  exact restrictedPerm_apply B.toCombinatorialMap.edgeInv S hclosed x

private theorem halfAdjacent_connected {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    {d e : D} (hd : d ∈ S) (he : e ∈ S)
    (hrot : B.toCombinatorialMap.rot.SameCycle
      (B.toCombinatorialMap.edgeInv d) e) :
    Relation.ReflTransGen
      (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed))
      ⟨d, hd⟩ ⟨e, he⟩ := by
  let H := closedHalfCombinatorialMap B S hclosed
  let u : {d : D // d ∈ S} :=
    ⟨B.toCombinatorialMap.edgeInv d, hclosed d hd⟩
  have hedge : mapConnectivityStep H ⟨d, hd⟩ u := by
    right
    right
    left
    exact (closedHalf_edgeInv_apply B S hclosed ⟨d, hd⟩).symm
  have hrot' : Relation.ReflTransGen (mapConnectivityStep H) u ⟨e, he⟩ :=
    closedHalf_rot_reachable B S hclosed hrot
  exact (Relation.ReflTransGen.single hedge).trans hrot'

private theorem halfFaceSucc_connected {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    {d : D} (hd : d ∈ S)
    (hnext : B.toCombinatorialMap.faceSucc d ∈ S) :
    Relation.ReflTransGen
      (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed))
      ⟨d, hd⟩ ⟨B.toCombinatorialMap.faceSucc d, hnext⟩ := by
  let H := closedHalfCombinatorialMap B S hclosed
  let u : {d : D // d ∈ S} :=
    ⟨B.toCombinatorialMap.edgeInv d, hclosed d hd⟩
  have hedge : mapConnectivityStep H ⟨d, hd⟩ u := by
    right
    right
    left
    exact (closedHalf_edgeInv_apply B S hclosed ⟨d, hd⟩).symm
  have hrot : B.toCombinatorialMap.rot.SameCycle
      (B.toCombinatorialMap.edgeInv d) (B.toCombinatorialMap.faceSucc d) := by
    refine ⟨-1, ?_⟩
    simp [CombinatorialMap.faceSucc]
  have hrot' : Relation.ReflTransGen (mapConnectivityStep H) u
      ⟨B.toCombinatorialMap.faceSucc d, hnext⟩ :=
    closedHalf_rot_reachable B S hclosed hrot
  exact (Relation.ReflTransGen.single hedge).trans hrot'

private theorem closedHalf_edgeInv_connected {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    (x : {d : D // d ∈ S}) :
    Relation.ReflTransGen
      (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed))
      x ((closedHalfCombinatorialMap B S hclosed).edgeInv x) := by
  have hstep : mapConnectivityStep (closedHalfCombinatorialMap B S hclosed)
      x ((closedHalfCombinatorialMap B S hclosed).edgeInv x) := by
    right
    right
    left
    rfl
  exact Relation.ReflTransGen.single hstep

private theorem mapConnectivityStep_symm {D : Type*} [Fintype D]
    [DecidableEq D] (M : CombinatorialMap D) {x y : D}
    (h : mapConnectivityStep M x y) : mapConnectivityStep M y x := by
  rcases h with h | h | h | h
  · subst y
    right
    left
    simp
  · subst y
    left
    simp
  · subst y
    right
    right
    right
    simp
  · subst y
    right
    right
    left
    simp

private theorem mapConnected_symm {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) {x y : D}
    (h : Relation.ReflTransGen (mapConnectivityStep M) x y) :
    Relation.ReflTransGen (mapConnectivityStep M) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hstep ih =>
      exact (Relation.ReflTransGen.single (mapConnectivityStep_symm M hstep)).trans ih

private theorem pathCutLeftStep_connected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {x y : D} (hx : x ∈ pathCutLeftDarts B P)
    (hy : y ∈ pathCutLeftDarts B P)
    (hstep : pathCutLeftStep B P x y) :
    Relation.ReflTransGen (mapConnectivityStep (pathCutLeftHalfMap B P))
      ⟨x, Or.inl hx⟩ ⟨y, Or.inl hy⟩ := by
  let S := pathCutLeftHalfDarts B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutLeftHalf_edgeInv_mem B P hd
  rcases hstep with ⟨hEq, _⟩ | ⟨hEq, _⟩
  · subst y
    exact halfFaceSucc_connected B.map S hclosed (Or.inl hx) (Or.inl hy)
  · subst y
    have hedge : mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed)
        ⟨x, Or.inl hx⟩
        ⟨B.map.toCombinatorialMap.edgeInv x, hclosed x (Or.inl hx)⟩ := by
      right
      right
      left
      exact (closedHalf_edgeInv_apply B.map S hclosed ⟨x, Or.inl hx⟩).symm
    exact Relation.ReflTransGen.single hedge

private theorem pathCutRightStep_connected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {x y : D} (hx : x ∈ pathCutRightDarts B P)
    (hy : y ∈ pathCutRightDarts B P)
    (hstep : pathCutRightStep B P x y) :
    Relation.ReflTransGen (mapConnectivityStep (pathCutRightHalfMap B P))
      ⟨x, Or.inl hx⟩ ⟨y, Or.inl hy⟩ := by
  let S := pathCutRightHalfDarts B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutRightHalf_edgeInv_mem B P hd
  rcases hstep with ⟨hEq, _⟩ | ⟨hEq, _⟩
  · subst y
    exact halfFaceSucc_connected B.map S hclosed (Or.inl hx) (Or.inl hy)
  · subst y
    have hedge : mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed)
        ⟨x, Or.inl hx⟩
        ⟨B.map.toCombinatorialMap.edgeInv x, hclosed x (Or.inl hx)⟩ := by
      right
      right
      left
      exact (closedHalf_edgeInv_apply B.map S hclosed ⟨x, Or.inl hx⟩).symm
    exact Relation.ReflTransGen.single hedge

private theorem chain_head_related {α : Type*} {R : α → α → Prop}
    [IsTrans α R] [Std.Refl R] {l : List α} (hl : l.IsChain R)
    {x : α} (hx : x ∈ l) : R (l.head (List.ne_nil_of_mem hx)) x := by
  cases l with
  | nil => simp at hx
  | cons a as =>
      have hxa : x = a ∨ x ∈ as := by simpa using hx
      rcases hxa with hxa | hxa
      · subst x
        exact refl a
      · simpa using hl.rel_cons hxa

private instance reflTransGen_isTrans {α : Type*} {r : α → α → Prop} :
    IsTrans α (Relation.ReflTransGen r) :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

private instance reflTransGen_isRefl {α : Type*} {r : α → α → Prop} :
    Std.Refl (Relation.ReflTransGen r) :=
  ⟨fun _ => Relation.ReflTransGen.refl⟩

private theorem path_first_darts_sameCycle {D : Type*} [Fintype D]
    [DecidableEq D] {M : DirectedMapWithMissing D} {s t₁ t₂ : MapVertex M}
    {k₁ k₂ : ℕ} (P : SimpleDirectedDartPath M s t₁ k₁)
    (Q : SimpleDirectedDartPath M s t₂ k₂)
    (hP : 0 < P.darts.length) (hQ : 0 < Q.darts.length) :
    M.toCombinatorialMap.rot.SameCycle
      (P.darts.head (List.length_pos_iff.mp hP))
      (Q.darts.head (List.length_pos_iff.mp hQ)) := by
  let iP : Fin P.darts.length := ⟨0, hP⟩
  let iQ : Fin Q.darts.length := ⟨0, hQ⟩
  have hPtail := P.edge_step iP
  have hQtail := Q.edge_step iQ
  have hv : dartTailVertex M (P.darts.get iP) = dartTailVertex M (Q.darts.get iQ) := by
    calc
      dartTailVertex M (P.darts.get iP) = P.vertices.get ⟨0, by
          rw [P.vertices_length]
          omega⟩ := hPtail.2.2.1.symm
      _ = s := P.start_vertex
      _ = Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ := Q.start_vertex.symm
      _ = dartTailVertex M (Q.darts.get iQ) := hQtail.2.2.1
  change Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
      (P.darts.get iP) =
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
      (Q.darts.get iQ) at hv
  have hPhead : P.darts.head (List.length_pos_iff.mp hP) = P.darts.get iP := by
    simpa [iP] using List.head_eq_getElem_zero (List.length_pos_iff.mp hP)
  have hQhead : Q.darts.head (List.length_pos_iff.mp hQ) = Q.darts.get iQ := by
    simpa [iQ] using List.head_eq_getElem_zero (List.length_pos_iff.mp hQ)
  have hsc : M.toCombinatorialMap.rot.SameCycle
      (P.darts.get iP) (Q.darts.get iQ) := Quotient.exact hv
  simpa only [hPhead, hQhead] using hsc

private theorem pathDart_connected_from_first {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.toCombinatorialMap.edgeInv d ∈ S)
    {s t : MapVertex B} {k : ℕ} (P : SimpleDirectedDartPath B s t k)
    (hmem : ∀ d, d ∈ P.darts → d ∈ S)
    (hne : P.darts ≠ []) {d : D} (hd : d ∈ P.darts) :
    Relation.ReflTransGen
      (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed))
      ⟨P.darts.head hne, hmem _ (List.head_mem hne)⟩
      ⟨d, hmem d hd⟩ := by
  classical
  have hlen : 0 < P.darts.length := List.length_pos_iff.mpr hne
  let first : D := P.darts.get ⟨0, hlen⟩
  have hfirst : first ∈ P.darts := List.get_mem _ _
  let base : {d : D // d ∈ S} := ⟨first, hmem first hfirst⟩
  let lift : D → {d : D // d ∈ S} := fun x =>
    if hx : x ∈ P.darts then ⟨x, hmem x hx⟩ else base
  have lift_of_mem {x : D} (hx : x ∈ P.darts) : lift x = ⟨x, hmem x hx⟩ := by
    simp [lift, hx]
  let conn : {d : D // d ∈ S} → {d : D // d ∈ S} → Prop :=
    Relation.ReflTransGen (mapConnectivityStep (closedHalfCombinatorialMap B S hclosed))
  have hchain : P.darts.IsChain (fun x y => conn (lift x) (lift y)) :=
    (path_darts_isChain P).imp_of_mem_imp (by
      intro x y hx hy hxy
      rw [lift_of_mem hx, lift_of_mem hy]
      exact halfAdjacent_connected B S hclosed
        (hmem x hx) (hmem y hy) hxy)
  have hmapped : (P.darts.map lift).IsChain conn := by
    rw [List.isChain_map]
    exact hchain
  have hmemMap : lift d ∈ P.darts.map lift :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  have hconn := chain_head_related hmapped hmemMap
  have hfirstHead : P.darts.head hne = first := by
    simpa [first] using List.head_eq_getElem_zero hne
  have hliftFirst : lift first = base := by
    simpa [base] using lift_of_mem hfirst
  have hhead : (P.darts.map lift).head (by simpa using hne) = base := by
    calc
      (P.darts.map lift).head (by simpa using hne) = lift (P.darts.head hne) := by simp
      _ = lift first := by rw [hfirstHead]
      _ = base := hliftFirst
  rw [hhead] at hconn
  have hbase : base = ⟨P.darts.head hne, hmem _ (List.head_mem hne)⟩ := by
    apply Subtype.ext
    exact hfirstHead.symm
  rw [hbase, lift_of_mem hd] at hconn
  exact hconn

private theorem pathCutLeft_seed_connected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (hne : B.leftPath.darts ≠ []) {a : D}
    (ha : a ∈ pathCutLeftSeeds B P) :
    Relation.ReflTransGen (mapConnectivityStep (pathCutLeftHalfMap B P))
      ⟨B.leftPath.darts.head hne,
        Or.inl ⟨B.leftPath.darts.head hne,
          Or.inl ((mem_pathCutLeftOuterArc_iff B _).2 (List.head_mem hne)),
          Relation.ReflTransGen.refl⟩⟩
      ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩ := by
  classical
  let S := pathCutLeftHalfDarts B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutLeftHalf_edgeInv_mem B P hd
  have hLmem : ∀ d, d ∈ B.leftPath.darts → d ∈ S := by
    intro d hd
    apply Or.inl
    exact ⟨d, Or.inl ((mem_pathCutLeftOuterArc_iff B d).2 hd),
      Relation.ReflTransGen.refl⟩
  have hPmem : ∀ d, d ∈ P.darts → d ∈ S := by
    intro d hd
    exact Or.inr (show d ∈ pathCutSeamDarts B P from Or.inl hd)
  change a ∈ pathCutLeftOuterArc B ∨ a ∈ P.darts at ha
  rcases ha with houter | hpath
  · have hpath : a ∈ B.leftPath.darts := (mem_pathCutLeftOuterArc_iff B a).1 houter
    exact pathDart_connected_from_first B.map S hclosed B.leftPath hLmem hne hpath
  · have hPne : P.darts ≠ [] := List.ne_nil_of_mem hpath
    have hLpos : 0 < B.leftPath.darts.length := List.length_pos_iff.mpr hne
    have hPpos : 0 < P.darts.length := List.length_pos_iff.mpr hPne
    have hfirst : B.map.toCombinatorialMap.rot.SameCycle
        (B.leftPath.darts.head hne) (P.darts.head hPne) :=
      path_first_darts_sameCycle B.leftPath P hLpos hPpos
    have hbridge : Relation.ReflTransGen
        (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
        ⟨B.leftPath.darts.head hne, hLmem _ (List.head_mem hne)⟩
        ⟨P.darts.head hPne, hPmem _ (List.head_mem hPne)⟩ :=
      closedHalf_rot_reachable B.map S hclosed hfirst
    have htail : Relation.ReflTransGen
        (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
        ⟨P.darts.head hPne, hPmem _ (List.head_mem hPne)⟩
        ⟨a, hPmem a hpath⟩ :=
      pathDart_connected_from_first B.map S hclosed P hPmem hPne hpath
    exact hbridge.trans htail

private theorem pathCutRight_seed_connected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (hne : B.rightPath.darts ≠ []) {a : D}
    (ha : a ∈ pathCutRightSeeds B P) :
    Relation.ReflTransGen (mapConnectivityStep (pathCutRightHalfMap B P))
      ⟨B.rightPath.darts.head hne,
        (by
          have hinv := pathCutRightHalf_edgeInv_mem B P (Or.inl
            ⟨B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.head hne),
              Or.inl (by
                apply (mem_pathCutRightOuterArc_iff B _).2
                exact List.mem_map.mpr ⟨B.rightPath.darts.head hne,
                  List.mem_reverse.mpr (List.head_mem hne), rfl⟩),
              Relation.ReflTransGen.refl⟩)
          simpa [B.map.toCombinatorialMap.edgeInv_invol] using hinv)⟩
      ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩ := by
  classical
  let S := pathCutRightHalfDarts B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutRightHalf_edgeInv_mem B P hd
  have hRmem : ∀ d, d ∈ B.rightPath.darts → d ∈ S := by
    intro d hd
    have hinvArc : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightOuterArc B := by
      apply (mem_pathCutRightOuterArc_iff B _).2
      exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
    have hinvDarts : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightDarts B P :=
      ⟨B.map.toCombinatorialMap.edgeInv d, Or.inl hinvArc,
        Relation.ReflTransGen.refl⟩
    have hinvS : B.map.toCombinatorialMap.edgeInv d ∈ S := Or.inl hinvDarts
    have hdS := hclosed (B.map.toCombinatorialMap.edgeInv d) hinvS
    simpa [B.map.toCombinatorialMap.edgeInv_invol] using hdS
  have hPmem : ∀ d, d ∈ P.darts → d ∈ S := by
    intro d hd
    exact Or.inr (show d ∈ pathCutSeamDarts B P from Or.inl hd)
  have haSeeds : a ∈ pathCutRightSeeds B P := ha
  change a ∈ pathCutRightOuterArc B ∨
    ∃ p ∈ P.darts, a = B.map.toCombinatorialMap.edgeInv p at ha
  rcases ha with houter | ⟨p, hp, hEq⟩
  · have houterPath : a ∈
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
      (mem_pathCutRightOuterArc_iff B a).1 houter
    obtain ⟨q, hqrev, hqa⟩ := List.mem_map.mp houterPath
    have hq : q ∈ B.rightPath.darts := List.mem_reverse.mp hqrev
    have hqconn := pathDart_connected_from_first B.map S hclosed
      B.rightPath hRmem hne hq
    have hqflip := closedHalf_edgeInv_connected B.map S hclosed
      ⟨q, hRmem q hq⟩
    have haRightDarts : a ∈ pathCutRightDarts B P :=
      ⟨a, haSeeds, Relation.ReflTransGen.refl⟩
    have haS : a ∈ S := by
      change a ∈ pathCutRightHalfDarts B P
      exact Or.inl haRightDarts
    have hflipTarget : (closedHalfCombinatorialMap B.map S hclosed).edgeInv
        ⟨q, hRmem q hq⟩ = ⟨a, haS⟩ := by
      apply Subtype.ext
      exact hqa
    have hqflip' : Relation.ReflTransGen
        (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
        ⟨q, hRmem q hq⟩
        ⟨a, haS⟩ := by
      simpa only [hflipTarget] using hqflip
    exact hqconn.trans hqflip'
  · subst a
    have hPne : P.darts ≠ [] := List.ne_nil_of_mem hp
    have hRpos : 0 < B.rightPath.darts.length := List.length_pos_iff.mpr hne
    have hPpos : 0 < P.darts.length := List.length_pos_iff.mpr hPne
    have hfirst : B.map.toCombinatorialMap.rot.SameCycle
        (B.rightPath.darts.head hne) (P.darts.head hPne) :=
      path_first_darts_sameCycle B.rightPath P hRpos hPpos
    have hbridge : Relation.ReflTransGen
        (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
        ⟨B.rightPath.darts.head hne, hRmem _ (List.head_mem hne)⟩
        ⟨P.darts.head hPne, hPmem _ (List.head_mem hPne)⟩ :=
      closedHalf_rot_reachable B.map S hclosed hfirst
    have hpconn := pathDart_connected_from_first B.map S hclosed P hPmem hPne hp
    have hflip := closedHalf_edgeInv_connected B.map S hclosed ⟨p, hPmem p hp⟩
    have hflipTarget : (closedHalfCombinatorialMap B.map S hclosed).edgeInv
        ⟨p, hPmem p hp⟩ =
          ⟨B.map.toCombinatorialMap.edgeInv p,
            Or.inl ⟨B.map.toCombinatorialMap.edgeInv p,
              Or.inr ⟨p, hp, rfl⟩, Relation.ReflTransGen.refl⟩⟩ := by
      apply Subtype.ext
      rfl
    have hflip' : Relation.ReflTransGen
        (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
        ⟨p, hPmem p hp⟩
        ⟨B.map.toCombinatorialMap.edgeInv p,
          Or.inl ⟨B.map.toCombinatorialMap.edgeInv p,
            Or.inr ⟨p, hp, rfl⟩, Relation.ReflTransGen.refl⟩⟩ := by
      simpa only [hflipTarget] using hflip
    exact hbridge.trans (hpconn.trans hflip')

/-- The left path-cut half map is connected (helper toward `lem-lr-ind`, -/
theorem pathCutLeftHalfMap_isConnected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMap B P).IsConnected := by
  classical
  let S := pathCutLeftHalfDarts B P
  let H := pathCutLeftHalfMap B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutLeftHalf_edgeInv_mem B P hd
  have hLpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    have hL := B.left_length_pos
    omega
  have hLne : B.leftPath.darts ≠ [] := List.length_pos_iff.mp hLpos
  let anchor : {d : D // d ∈ S} :=
    ⟨B.leftPath.darts.head hLne,
      Or.inl ⟨B.leftPath.darts.head hLne,
        Or.inl ((mem_pathCutLeftOuterArc_iff B _).2 (List.head_mem hLne)),
        Relation.ReflTransGen.refl⟩⟩
  have hseedConn {a : D} (ha : a ∈ pathCutLeftSeeds B P) :
      Relation.ReflTransGen (mapConnectivityStep H) anchor
        ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩ := by
    simpa [anchor, H, S, hclosed] using pathCutLeft_seed_connected B P hLne ha
  have hleftConn {d : D} (hd : d ∈ pathCutLeftDarts B P) :
      Relation.ReflTransGen (mapConnectivityStep H) anchor ⟨d, Or.inl hd⟩ := by
    rcases hd with ⟨a, ha, hreach⟩
    have hseed := hseedConn ha
    have hreachConn : Relation.ReflTransGen
        (mapConnectivityStep H)
        ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩
        ⟨d, Or.inl ⟨a, ha, hreach⟩⟩ := by
      induction hreach with
      | refl => exact Relation.ReflTransGen.refl
      | tail hprev hstep ih =>
          exact ih.trans (pathCutLeftStep_connected B P
            ⟨a, ha, hprev⟩ ⟨a, ha, Relation.ReflTransGen.tail hprev hstep⟩ hstep)
    exact hseed.trans hreachConn
  intro x y
  have hxAnchor : Relation.ReflTransGen (mapConnectivityStep H) anchor x := by
    have hx : x.1 ∈ S := x.2
    change x.1 ∈ pathCutLeftDarts B P ∨ x.1 ∈ pathCutSeamDarts B P at hx
    rcases hx with hleft | hseam
    · exact hleftConn hleft
    · change x.1 ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv x.1 ∈ P.darts at hseam
      rcases hseam with hpath | hreverse
      · have h := hseedConn (Or.inr hpath)
        have htarget :
            (⟨x.1, Or.inr (show x.1 ∈ pathCutSeamDarts B P from Or.inl hpath)⟩ :
              {d : D // d ∈ S}) =
              ⟨x.1, Or.inl ⟨x.1, Or.inr hpath, Relation.ReflTransGen.refl⟩⟩ := by
          apply Subtype.ext
          rfl
        simpa only [htarget] using h
      · let p := B.map.toCombinatorialMap.edgeInv x.1
        have hp : p ∈ P.darts := hreverse
        have hpLeft : p ∈ pathCutLeftDarts B P :=
          ⟨p, Or.inr hp, Relation.ReflTransGen.refl⟩
        have hpS : p ∈ S := Or.inl hpLeft
        have hpConn := hseedConn (Or.inr hp)
        have hflip := closedHalf_edgeInv_connected B.map S hclosed ⟨p, hpS⟩
        have hflipTarget :
            (closedHalfCombinatorialMap B.map S hclosed).edgeInv ⟨p, hpS⟩ = x := by
          apply Subtype.ext
          dsimp [p]
          exact B.map.toCombinatorialMap.edgeInv_invol x.1
        have hflip' : Relation.ReflTransGen (mapConnectivityStep H)
            ⟨p, hpS⟩ x := by
          change Relation.ReflTransGen
            (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
            ⟨p, hpS⟩ x
          simpa only [hflipTarget] using hflip
        exact hpConn.trans hflip'
  have hyAnchor : Relation.ReflTransGen (mapConnectivityStep H) anchor y := by
    have hy : y.1 ∈ S := y.2
    change y.1 ∈ pathCutLeftDarts B P ∨ y.1 ∈ pathCutSeamDarts B P at hy
    rcases hy with hleft | hseam
    · exact hleftConn hleft
    · change y.1 ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv y.1 ∈ P.darts at hseam
      rcases hseam with hpath | hreverse
      · have h := hseedConn (Or.inr hpath)
        have htarget :
            (⟨y.1, Or.inr (show y.1 ∈ pathCutSeamDarts B P from Or.inl hpath)⟩ :
              {d : D // d ∈ S}) =
              ⟨y.1, Or.inl ⟨y.1, Or.inr hpath, Relation.ReflTransGen.refl⟩⟩ := by
          apply Subtype.ext
          rfl
        simpa only [htarget] using h
      · let p := B.map.toCombinatorialMap.edgeInv y.1
        have hp : p ∈ P.darts := hreverse
        have hpLeft : p ∈ pathCutLeftDarts B P :=
          ⟨p, Or.inr hp, Relation.ReflTransGen.refl⟩
        have hpS : p ∈ S := Or.inl hpLeft
        have hpConn := hseedConn (Or.inr hp)
        have hflip := closedHalf_edgeInv_connected B.map S hclosed ⟨p, hpS⟩
        have hflipTarget :
            (closedHalfCombinatorialMap B.map S hclosed).edgeInv ⟨p, hpS⟩ = y := by
          apply Subtype.ext
          dsimp [p]
          exact B.map.toCombinatorialMap.edgeInv_invol y.1
        have hflip' : Relation.ReflTransGen (mapConnectivityStep H)
            ⟨p, hpS⟩ y := by
          change Relation.ReflTransGen
            (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
            ⟨p, hpS⟩ y
          simpa only [hflipTarget] using hflip
        exact hpConn.trans hflip'
  change Relation.ReflTransGen (mapConnectivityStep H) x y
  exact (mapConnected_symm H hxAnchor).trans hyAnchor

/-- The right path-cut half map is connected (helper toward `lem-lr-ind`, -/
theorem pathCutRightHalfMap_isConnected {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMap B P).IsConnected := by
  classical
  let S := pathCutRightHalfDarts B P
  let H := pathCutRightHalfMap B P
  let hclosed : ∀ d : D, d ∈ S → B.map.toCombinatorialMap.edgeInv d ∈ S :=
    fun d hd => pathCutRightHalf_edgeInv_mem B P hd
  have hRpos : 0 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    have hR := B.right_length_pos
    omega
  have hRne : B.rightPath.darts ≠ [] := List.length_pos_iff.mp hRpos
  have hRmem : ∀ d, d ∈ B.rightPath.darts → d ∈ S := by
    intro d hd
    have hinvArc : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightOuterArc B := by
      apply (mem_pathCutRightOuterArc_iff B _).2
      exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
    have hinvDarts : B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightDarts B P :=
      ⟨B.map.toCombinatorialMap.edgeInv d,
        (show B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightSeeds B P from
          Or.inl hinvArc), Relation.ReflTransGen.refl⟩
    have hinvS : B.map.toCombinatorialMap.edgeInv d ∈ S := Or.inl hinvDarts
    have hdS := hclosed (B.map.toCombinatorialMap.edgeInv d) hinvS
    simpa [B.map.toCombinatorialMap.edgeInv_invol] using hdS
  let anchor : {d : D // d ∈ S} :=
    ⟨B.rightPath.darts.head hRne, hRmem _ (List.head_mem hRne)⟩
  have hseedConn {a : D} (ha : a ∈ pathCutRightSeeds B P) :
      Relation.ReflTransGen (mapConnectivityStep H) anchor
        ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩ := by
    simpa [anchor, H, S, hclosed, hRmem] using
      pathCutRight_seed_connected B P hRne ha
  have hrightConn {d : D} (hd : d ∈ pathCutRightDarts B P) :
      Relation.ReflTransGen (mapConnectivityStep H) anchor ⟨d, Or.inl hd⟩ := by
    rcases hd with ⟨a, ha, hreach⟩
    have hseed := hseedConn ha
    have hreachConn : Relation.ReflTransGen
        (mapConnectivityStep H)
        ⟨a, Or.inl ⟨a, ha, Relation.ReflTransGen.refl⟩⟩
        ⟨d, Or.inl ⟨a, ha, hreach⟩⟩ := by
      induction hreach with
      | refl => exact Relation.ReflTransGen.refl
      | tail hprev hstep ih =>
          exact ih.trans (pathCutRightStep_connected B P
            ⟨a, ha, hprev⟩ ⟨a, ha, Relation.ReflTransGen.tail hprev hstep⟩ hstep)
    exact hseed.trans hreachConn
  intro x y
  have hxAnchor : Relation.ReflTransGen (mapConnectivityStep H) anchor x := by
    have hx : x.1 ∈ S := x.2
    change x.1 ∈ pathCutRightDarts B P ∨ x.1 ∈ pathCutSeamDarts B P at hx
    rcases hx with hright | hseam
    · exact hrightConn hright
    · change x.1 ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv x.1 ∈ P.darts at hseam
      rcases hseam with hpath | hreverse
      · let q := B.map.toCombinatorialMap.edgeInv x.1
        have hqSeed : q ∈ pathCutRightSeeds B P :=
          Or.inr ⟨x.1, hpath, rfl⟩
        have hqDarts : q ∈ pathCutRightDarts B P :=
          ⟨q, hqSeed, Relation.ReflTransGen.refl⟩
        have hqS : q ∈ S := Or.inl hqDarts
        have hqConn := hseedConn hqSeed
        have hflip := closedHalf_edgeInv_connected B.map S hclosed ⟨q, hqS⟩
        have hflipTarget :
            (closedHalfCombinatorialMap B.map S hclosed).edgeInv ⟨q, hqS⟩ = x := by
          apply Subtype.ext
          dsimp [q]
          exact B.map.toCombinatorialMap.edgeInv_invol x.1
        have hflip' : Relation.ReflTransGen (mapConnectivityStep H) ⟨q, hqS⟩ x := by
          change Relation.ReflTransGen
            (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
            ⟨q, hqS⟩ x
          simpa only [hflipTarget] using hflip
        exact hqConn.trans hflip'
      · let p := B.map.toCombinatorialMap.edgeInv x.1
        have hp : p ∈ P.darts := hreverse
        have haSeed : x.1 ∈ pathCutRightSeeds B P :=
          Or.inr ⟨p, hp, by
            dsimp [p]
            exact (B.map.toCombinatorialMap.edgeInv_invol x.1).symm⟩
        have hconn := hseedConn haSeed
        have htarget :
            (⟨x.1, Or.inl ⟨x.1, haSeed, Relation.ReflTransGen.refl⟩⟩ :
              {d : D // d ∈ S}) = x := by
          apply Subtype.ext
          rfl
        simpa only [htarget] using hconn
  have hyAnchor : Relation.ReflTransGen (mapConnectivityStep H) anchor y := by
    have hy : y.1 ∈ S := y.2
    change y.1 ∈ pathCutRightDarts B P ∨ y.1 ∈ pathCutSeamDarts B P at hy
    rcases hy with hright | hseam
    · exact hrightConn hright
    · change y.1 ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv y.1 ∈ P.darts at hseam
      rcases hseam with hpath | hreverse
      · let q := B.map.toCombinatorialMap.edgeInv y.1
        have hqSeed : q ∈ pathCutRightSeeds B P :=
          Or.inr ⟨y.1, hpath, rfl⟩
        have hqDarts : q ∈ pathCutRightDarts B P :=
          ⟨q, hqSeed, Relation.ReflTransGen.refl⟩
        have hqS : q ∈ S := Or.inl hqDarts
        have hqConn := hseedConn hqSeed
        have hflip := closedHalf_edgeInv_connected B.map S hclosed ⟨q, hqS⟩
        have hflipTarget :
            (closedHalfCombinatorialMap B.map S hclosed).edgeInv ⟨q, hqS⟩ = y := by
          apply Subtype.ext
          dsimp [q]
          exact B.map.toCombinatorialMap.edgeInv_invol y.1
        have hflip' : Relation.ReflTransGen (mapConnectivityStep H) ⟨q, hqS⟩ y := by
          change Relation.ReflTransGen
            (mapConnectivityStep (closedHalfCombinatorialMap B.map S hclosed))
            ⟨q, hqS⟩ y
          simpa only [hflipTarget] using hflip
        exact hqConn.trans hflip'
      · let p := B.map.toCombinatorialMap.edgeInv y.1
        have hp : p ∈ P.darts := hreverse
        have haSeed : y.1 ∈ pathCutRightSeeds B P :=
          Or.inr ⟨p, hp, by
            dsimp [p]
            exact (B.map.toCombinatorialMap.edgeInv_invol y.1).symm⟩
        have hconn := hseedConn haSeed
        have htarget :
            (⟨y.1, Or.inl ⟨y.1, haSeed, Relation.ReflTransGen.refl⟩⟩ :
              {d : D // d ∈ S}) = y := by
          apply Subtype.ext
          rfl
        simpa only [htarget] using hconn
  change Relation.ReflTransGen (mapConnectivityStep H) x y
  exact (mapConnected_symm H hxAnchor).trans hyAnchor
