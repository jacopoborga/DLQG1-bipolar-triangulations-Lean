/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIso

import DirectedDistances.PlanarMap.BdyReverseRelabelCarrier
import Mathlib.Tactic.FinCases

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']

/-- Conjugate a dart permutation across a carrier equivalence. Helper toward -/
@[expose] def transportPerm (e : D ≃ D') (f : Equiv.Perm D) : Equiv.Perm D' :=
  e.symm.trans (f.trans e)

omit [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] in
@[simp] theorem transportPerm_apply (e : D ≃ D') (f : Equiv.Perm D) (d : D') :
    transportPerm e f d = e (f (e.symm d)) := by
  simp [transportPerm]

omit [DecidableEq D] [Fintype D'] [DecidableEq D'] in
private theorem sameCycle_map_equiv (e : D ≃ D') (f : Equiv.Perm D)
    (f' : Equiv.Perm D') (hcomm : ∀ x, e (f x) = f' (e x))
    {x y : D} (hxy : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle f' (e x) (e y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have hpow : ∀ (n : ℕ) (x : D), e ((f ^ n) x) = (f' ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (f x)).trans (congrArg (f' ^ n) (hcomm x))
  calc
    (f' ^ n) (e x) = e ((f ^ n) x) := (hpow n x).symm
    _ = e y := congrArg e hn

omit [DecidableEq D] [DecidableEq D'] in
/-- The equivalence transports the full permutation orbit relation in both
directions. Helper toward `thm-kmsw`, not the paper result -/
theorem sameCycle_transport_iff (e : D ≃ D') (f : Equiv.Perm D)
    (x y : D) :
    Equiv.Perm.SameCycle (transportPerm e f) (e x) (e y) ↔
      Equiv.Perm.SameCycle f x y := by
  constructor
  · intro h
    have hcomm : ∀ z, e.symm ((transportPerm e f) z) =
        f (e.symm z) := by intro z; simp [transportPerm_apply]
    simpa using sameCycle_map_equiv e.symm (transportPerm e f) f hcomm h
  · intro h
    exact sameCycle_map_equiv e f (transportPerm e f)
      (by intro z; simp [transportPerm_apply]) h

/-- Conjugate both permutations of a combinatorial map across a dart
equivalence. Helper toward `thm-kmsw`; not the paper result -/
@[expose] def CombinatorialMap.transport (e : D ≃ D') (M : CombinatorialMap D) :
    CombinatorialMap D' where
  edgeInv := transportPerm e M.edgeInv
  edgeInv_invol := by intro d; simp [transportPerm_apply, M.edgeInv_invol]
  edgeInv_ne := by
    intro d h
    apply M.edgeInv_ne (e.symm d)
    apply e.injective
    simpa [transportPerm_apply] using h
  rot := transportPerm e M.rot

@[simp] theorem CombinatorialMap.transport_edgeInv (e : D ≃ D')
    (M : CombinatorialMap D) :
    (M.transport e).edgeInv = transportPerm e M.edgeInv := rfl

@[simp] theorem CombinatorialMap.transport_rot (e : D ≃ D')
    (M : CombinatorialMap D) :
    (M.transport e).rot = transportPerm e M.rot := rfl

omit [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] in
private theorem transportPerm_inv (e : D ≃ D') (f : Equiv.Perm D) :
    (transportPerm e f)⁻¹ = transportPerm e f⁻¹ := by
  ext d
  simp [transportPerm]

omit [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] in
private theorem transportPerm_mul (e : D ≃ D') (f g : Equiv.Perm D) :
    transportPerm e (f * g) = transportPerm e f * transportPerm e g := by
  ext d
  simp [transportPerm, Equiv.trans_apply, Equiv.Perm.mul_apply]

private theorem CombinatorialMap.transport_faceSucc (e : D ≃ D')
    (M : CombinatorialMap D) :
    (M.transport e).faceSucc = transportPerm e M.faceSucc := by
  change (transportPerm e M.rot)⁻¹ * transportPerm e M.edgeInv = _
  rw [transportPerm_inv, ← transportPerm_mul]
  rfl

private theorem sameCycle_faceSucc_transport_iff (e : D ≃ D')
    (M : CombinatorialMap D) (x y : D) :
    Equiv.Perm.SameCycle (M.transport e).faceSucc (e x) (e y) ↔
      Equiv.Perm.SameCycle M.faceSucc x y := by
  rw [CombinatorialMap.transport_faceSucc]
  exact sameCycle_transport_iff e M.faceSucc x y

/-- Transport a directed map with missing edges along a dart equivalence.
The marked outer dart is carried by the equivalence, while the missing and
tail predicates are pulled back. Helper toward `thm-kmsw`, not the paper -/
@[expose] def DirectedMapWithMissing.transport (e : D ≃ D')
    (M : DirectedMapWithMissing D) : DirectedMapWithMissing D' where
  toCombinatorialMap := M.toCombinatorialMap.transport e
  missing := fun d => M.missing (e.symm d)
  missing_edgeInv := by
    intro d
    change M.missing (e.symm d) ↔
      M.missing (e.symm (transportPerm e M.edgeInv d))
    simp only [transportPerm_apply, Equiv.symm_apply_apply]
    exact M.missing_edgeInv (e.symm d)
  tail := fun d => M.tail (e.symm d)
  tail_iff := by
    intro d hd
    change M.tail (e.symm d) ↔
      ¬ M.tail (e.symm (transportPerm e M.edgeInv d))
    simp only [transportPerm_apply, Equiv.symm_apply_apply]
    exact M.tail_iff (e.symm d) hd
  tail_missing := by
    intro d hd
    exact M.tail_missing (e.symm d) hd
  outer := e M.outer
  missing_outer := by
    intro d hd
    have h := M.missing_outer (e.symm d) hd
    rcases h with h | h
    · left
      unfold CombinatorialMap.IsOuter
      rw [show d = e (e.symm d) by simp]
      exact (sameCycle_faceSucc_transport_iff e M.toCombinatorialMap
        M.outer (e.symm d)).2 h
    · right
      unfold CombinatorialMap.IsOuter
      rw [show (M.toCombinatorialMap.transport e).edgeInv d =
        e (M.edgeInv (e.symm d)) by
          simp [CombinatorialMap.transport_edgeInv, transportPerm_apply]]
      exact (sameCycle_faceSucc_transport_iff e M.toCombinatorialMap M.outer
        (M.edgeInv (e.symm d))).2 h

@[simp] theorem DirectedMapWithMissing.transport_combinatorialMap
    (e : D ≃ D') (M : DirectedMapWithMissing D) :
    (M.transport e).toCombinatorialMap = M.toCombinatorialMap.transport e := rfl

@[simp] theorem DirectedMapWithMissing.transport_missing
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D') :
    (M.transport e).missing d ↔ M.missing (e.symm d) := Iff.rfl

@[simp] theorem DirectedMapWithMissing.transport_tail
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D') :
    (M.transport e).tail d ↔ M.tail (e.symm d) := Iff.rfl

@[simp] theorem DirectedMapWithMissing.transport_outer
    (e : D ≃ D') (M : DirectedMapWithMissing D) :
    (M.transport e).outer = e M.outer := rfl

private theorem DirectedMapWithMissing.transport_isOuter_iff
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D') :
    (M.transport e).IsOuter d ↔ M.IsOuter (e.symm d) := by
  change Equiv.Perm.SameCycle (M.transport e).toCombinatorialMap.faceSucc
      (e M.outer) d ↔
    Equiv.Perm.SameCycle M.toCombinatorialMap.faceSucc M.outer (e.symm d)
  rw [show d = e (e.symm d) by simp]
  simpa using sameCycle_faceSucc_transport_iff e M.toCombinatorialMap M.outer
    (e.symm d)

/-- The dart equivalence induces an equivalence of rotation-cycle vertices
for transported directed maps. Helper toward `thm-kmsw`, not the paper result -/
@[expose] noncomputable def DirectedMapWithMissing.transportVertexEquiv
    (e : D ≃ D') (M : DirectedMapWithMissing D) :
    MapVertex M ≃ MapVertex (M.transport e) := by
  classical
  apply Quotient.congr e
  intro x y
  change Equiv.Perm.SameCycle M.rot x y ↔
    Equiv.Perm.SameCycle (transportPerm e M.rot) (e x) (e y)
  exact (sameCycle_transport_iff e M.rot x y).symm

@[simp] theorem DirectedMapWithMissing.transportVertexEquiv_dartTailVertex
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D) :
    M.transportVertexEquiv e (dartTailVertex M d) =
      dartTailVertex (M.transport e) (e d) := by
  change Quotient.congr e _ (Quotient.mk _ d) = Quotient.mk _ (e d)
  exact Quotient.congr_mk e _ d

@[simp] theorem DirectedMapWithMissing.transportVertexEquiv_dartHeadVertex
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D) :
    M.transportVertexEquiv e (dartHeadVertex M d) =
      dartHeadVertex (M.transport e) (e d) := by
  change M.transportVertexEquiv e (dartTailVertex M (M.edgeInv d)) =
    dartTailVertex (M.transport e) ((M.transport e).edgeInv (e d))
  rw [DirectedMapWithMissing.transportVertexEquiv_dartTailVertex]
  simp [CombinatorialMap.transport_edgeInv, transportPerm_apply]

private theorem directedStep_transport_iff (e : D ≃ D')
    (M : DirectedMapWithMissing D) (u v : MapVertex M) :
    (M.transport e).directedStep (M.transportVertexEquiv e u)
      (M.transportVertexEquiv e v) ↔ M.directedStep u v := by
  constructor
  · rintro ⟨d, hmiss, htail, hu, hv⟩
    let d₀ := e.symm d
    refine ⟨d₀, ?_, ?_, ?_, ?_⟩
    · simpa [d₀] using hmiss
    · simpa [d₀] using htail
    · apply (M.transportVertexEquiv e).injective
      calc
        M.transportVertexEquiv e (Quotient.mk _ d₀) = Quotient.mk _ (e d₀) :=
          Quotient.congr_mk e _ d₀
        _ = M.transportVertexEquiv e u := by simpa [d₀] using hu
    · apply (M.transportVertexEquiv e).injective
      calc
        M.transportVertexEquiv e (Quotient.mk _ (M.edgeInv d₀)) =
            Quotient.mk _ (e (M.edgeInv d₀)) := Quotient.congr_mk e _ _
        _ = M.transportVertexEquiv e v := by
          simpa [d₀, DirectedMapWithMissing.transport, CombinatorialMap.transport,
            transportPerm_apply] using hv
  · rintro ⟨d, hmiss, htail, hu, hv⟩
    refine ⟨e d, ?_, ?_, ?_, ?_⟩
    · simpa using hmiss
    · simpa using htail
    · change dartTailVertex (M.transport e) (e d) = M.transportVertexEquiv e u
      rw [← DirectedMapWithMissing.transportVertexEquiv_dartTailVertex]
      exact congrArg (M.transportVertexEquiv e) hu
    · change dartHeadVertex (M.transport e) (e d) = M.transportVertexEquiv e v
      rw [← DirectedMapWithMissing.transportVertexEquiv_dartHeadVertex]
      exact congrArg (M.transportVertexEquiv e) hv

/-- Acyclicity is preserved under dart and vertex transport. Helper toward -/
theorem DirectedMapWithMissing.transport_isAcyclic
    (e : D ≃ D') (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) :
    (M.transport e).IsAcyclic := by
  intro v hcycle
  let ve := M.transportVertexEquiv e
  have hcycle' : Relation.TransGen M.directedStep (ve.symm v) (ve.symm v) := by
    have hmap := hcycle.lift ve.symm (by
      intro x y hxy
      have hxy' := (directedStep_transport_iff e M (ve.symm x) (ve.symm y)).mp
        (by simpa [ve] using hxy)
      simpa [ve] using hxy')
    simpa [ve] using hmap
  exact hM (ve.symm v) hcycle'

private theorem CombinatorialMap.transport_faceSucc_apply (e : D ≃ D')
    (M : CombinatorialMap D) (d : D) :
    (M.transport e).faceSucc (e d) = e (M.faceSucc d) := by
  rw [CombinatorialMap.transport_faceSucc]
  simp [transportPerm_apply]

private theorem DirectedMapWithMissing.transport_ulDarts
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D') :
    d ∈ (M.transport e).ulDarts ↔ e.symm d ∈ M.ulDarts := by
  simp only [DirectedMapWithMissing.ulDarts, Set.mem_ofPred_eq,
    DirectedMapWithMissing.transport_missing, DirectedMapWithMissing.transport_tail]
  rw [DirectedMapWithMissing.transport_isOuter_iff]

private theorem DirectedMapWithMissing.transport_lrDarts
    (e : D ≃ D') (M : DirectedMapWithMissing D) (d : D') :
    d ∈ (M.transport e).lrDarts ↔ e.symm d ∈ M.lrDarts := by
  simp only [DirectedMapWithMissing.lrDarts, Set.mem_ofPred_eq,
    DirectedMapWithMissing.transport_missing, DirectedMapWithMissing.transport_tail]
  rw [DirectedMapWithMissing.transport_isOuter_iff]

/-- Transport a nonempty cyclic-word representative letter by letter. Helper -/
@[expose] def NonemptyWord.transport (e : D ≃ D') (W : NonemptyWord D) :
    NonemptyWord D' where
  letters := W.letters.map e
  nonempty := by
    intro h
    have hnil : W.letters = [] := by
      simpa using congrArg (List.map e.symm) h
    exact W.nonempty hnil
  nodup := W.nodup.map e.injective

omit [Fintype D] [Fintype D'] in
private theorem formPerm_map_equiv_apply (e : D ≃ D') (xs : List D)
    (hxs : xs.Nodup) (x : D) (hx : x ∈ xs) :
    (xs.map e).formPerm (e x) = e (xs.formPerm x) := by
  have hxs' : (xs.map e).Nodup := hxs.map e.injective
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (xs.map e).length := by simpa using hi
  have hmap : (xs.map e)[i]'himap = e xs[i] := by simp
  rw [← hmap, List.formPerm_apply_getElem _ hxs' i himap,
    List.formPerm_apply_getElem _ hxs i hi]
  simp

private theorem isOuterCycle_transport (e : D ≃ D')
    (M : DirectedMapWithMissing D) (W : NonemptyWord D)
    (hW : IsOuterCycle M W) :
    IsOuterCycle (M.transport e) (NonemptyWord.transport e W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    change d ∈ W.letters.map e at hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    have hOuter : M.IsOuter (e.symm (e d₀)) := by
      simpa using hW.1 d₀ hd₀
    exact (DirectedMapWithMissing.transport_isOuter_iff e M (e d₀)).2 hOuter
  · intro d hd
    have ho : M.IsOuter (e.symm d) :=
      (DirectedMapWithMissing.transport_isOuter_iff e M d).1 hd
    exact List.mem_map.mpr ⟨e.symm d, hW.2.1 _ ho, by simp⟩
  · intro d hd
    change d ∈ W.letters.map e at hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    calc
      (M.transport e).toCombinatorialMap.faceSucc (e d₀) =
          e (M.toCombinatorialMap.faceSucc d₀) :=
        CombinatorialMap.transport_faceSucc_apply e M.toCombinatorialMap d₀
      _ = e (W.letters.formPerm d₀) := congrArg e (hW.2.2 d₀ hd₀)
      _ = (W.letters.map e).formPerm (e d₀) :=
        (formPerm_map_equiv_apply e W.letters W.nodup d₀ hd₀).symm

private theorem fourArcsWitness_transport (e : D ≃ D')
    (M : DirectedMapWithMissing D) (W : NonemptyWord D)
    (ul ur lr ll : List D) (h : FourArcsWitness M W ul ur lr ll) :
    FourArcsWitness (M.transport e) (NonemptyWord.transport e W)
      (ul.map e) (ur.map e) (lr.map e) (ll.map e) := by
  refine ⟨isOuterCycle_transport e M W h.1, ?_, ?_, ?_, ?_, ?_⟩
  · change W.letters.map e ~r _
    simpa only [List.map_append] using h.2.1.map e
  · intro d
    simp only [List.mem_map]
    rw [DirectedMapWithMissing.transport_ulDarts]
    constructor
    · rintro ⟨d₀, hd₀, rfl⟩
      simpa using (h.2.2.1 d₀).mp hd₀
    · intro hd
      exact ⟨e.symm d, (h.2.2.1 (e.symm d)).mpr hd, by simp⟩
  · intro d
    simp only [List.mem_map]
    rw [DirectedMapWithMissing.transport_lrDarts]
    constructor
    · rintro ⟨d₀, hd₀, rfl⟩
      simpa using (h.2.2.2.1 d₀).mp hd₀
    · intro hd
      exact ⟨e.symm d, (h.2.2.2.1 (e.symm d)).mpr hd, by simp⟩
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    simpa using h.2.2.2.2.1 d₀ hd₀
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    simpa using h.2.2.2.2.2 d₀ hd₀

/-- Transport a simple directed dart path by mapping darts and its
rotation-cycle vertices. Helper toward `thm-kmsw`, not the paper result -/
@[expose] noncomputable def SimpleDirectedDartPath.transport
    (e : D ≃ D') {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    SimpleDirectedDartPath (M.transport e)
      (M.transportVertexEquiv e s) (M.transportVertexEquiv e t) n where
  darts := P.darts.map e
  vertices := P.vertices.map (M.transportVertexEquiv e)
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map (M.transportVertexEquiv e).injective
  start_vertex := by
    simpa using congrArg (M.transportVertexEquiv e) P.start_vertex
  end_vertex := by
    simpa using congrArg (M.transportVertexEquiv e) P.end_vertex
  edge_step := by
    intro i
    have hi : i.val < n := by simpa [P.darts_length] using i.isLt
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map e).get i = e (P.darts.get j) := by simp [j]
    have hgetV : (P.vertices.map (M.transportVertexEquiv e)).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          M.transportVertexEquiv e (P.vertices.get jv) := by simp [jv]
    have hgetV' : (P.vertices.map (M.transportVertexEquiv e)).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          M.transportVertexEquiv e (P.vertices.get jv') := by simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h.1
    · simpa using h.2.1
    · calc
        (P.vertices.map (M.transportVertexEquiv e)).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            M.transportVertexEquiv e (P.vertices.get jv) := hgetV
        _ = M.transportVertexEquiv e (dartTailVertex M (P.darts.get j)) :=
          congrArg _ h.2.2.1
        _ = dartTailVertex (M.transport e) (e (P.darts.get j)) :=
          DirectedMapWithMissing.transportVertexEquiv_dartTailVertex e M _
    · calc
        (P.vertices.map (M.transportVertexEquiv e)).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            M.transportVertexEquiv e (P.vertices.get jv') := hgetV'
        _ = M.transportVertexEquiv e (dartHeadVertex M (P.darts.get j)) :=
          congrArg _ h.2.2.2
        _ = dartHeadVertex (M.transport e) (e (P.darts.get j)) :=
          DirectedMapWithMissing.transportVertexEquiv_dartHeadVertex e M _

@[simp] theorem SimpleDirectedDartPath.transport_darts
    (e : D ≃ D') {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    (SimpleDirectedDartPath.transport e P).darts = P.darts.map e := rfl

@[simp] theorem SimpleDirectedDartPath.transport_vertices
    (e : D ≃ D') {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    (SimpleDirectedDartPath.transport e P).vertices =
      P.vertices.map (M.transportVertexEquiv e) := rfl

private theorem CombinatorialMap.transport_numVertices (e : D ≃ D')
    (M : CombinatorialMap D) : (M.transport e).numVertices = M.numVertices := by
  classical
  unfold CombinatorialMap.numVertices
  exact (Fintype.card_congr (by
    apply Quotient.congr e
    intro x y
    exact (sameCycle_transport_iff e M.rot x y).symm)).symm

private theorem CombinatorialMap.transport_numEdges (e : D ≃ D')
    (M : CombinatorialMap D) : (M.transport e).numEdges = M.numEdges := by
  classical
  unfold CombinatorialMap.numEdges
  exact (Fintype.card_congr (by
    apply Quotient.congr e
    intro x y
    exact (sameCycle_transport_iff e M.edgeInv x y).symm)).symm

private theorem CombinatorialMap.transport_numFaces (e : D ≃ D')
    (M : CombinatorialMap D) : (M.transport e).numFaces = M.numFaces := by
  classical
  unfold CombinatorialMap.numFaces
  exact (Fintype.card_congr (by
    apply Quotient.congr e
    intro x y
    exact (sameCycle_faceSucc_transport_iff e M x y).symm)).symm

/-- Planarity is preserved under dart transport. Helper toward `thm-kmsw`, -/
theorem CombinatorialMap.transport_isPlanar (e : D ≃ D')
    (M : CombinatorialMap D) (hM : M.IsPlanar) :
    (M.transport e).IsPlanar := by
  have hconn : (M.transport e).IsConnected := by
    intro d d'
    let R := fun x y : D =>
      y = M.rot x ∨ y = M.rot.symm x ∨ y = M.edgeInv x ∨ y = M.edgeInv.symm x
    let R' := fun x y : D' =>
      y = (M.transport e).rot x ∨ y = (M.transport e).rot.symm x ∨
        y = (M.transport e).edgeInv x ∨ y = (M.transport e).edgeInv.symm x
    have hstep : ∀ x y, R x y ↔ R' (e x) (e y) := by
      intro x y
      dsimp only [R, R']
      constructor
      · rintro (h | h | h | h)
        · left; simpa [CombinatorialMap.transport_rot, transportPerm_apply] using congrArg e h
        · right; left
          have hinv : (transportPerm e M.rot).symm (e x) = e (M.rot.symm x) := by
            simp [transportPerm]
          simpa [CombinatorialMap.transport_rot, hinv] using congrArg e h
        · right; right; left
          simpa [CombinatorialMap.transport_edgeInv, transportPerm_apply] using congrArg e h
        · right; right; right
          have hinv : (transportPerm e M.edgeInv).symm (e x) = e (M.edgeInv.symm x) := by
            simp [transportPerm]
          simpa [CombinatorialMap.transport_edgeInv, hinv] using congrArg e h
      · rintro (h | h | h | h)
        · left
          apply e.injective
          simpa [CombinatorialMap.transport_rot, transportPerm_apply] using h
        · right; left
          have hinv : (transportPerm e M.rot).symm (e x) = e (M.rot.symm x) := by
            simp [transportPerm]
          apply e.injective
          simpa [CombinatorialMap.transport_rot, hinv] using h
        · right; right; left
          apply e.injective
          simpa [CombinatorialMap.transport_edgeInv, transportPerm_apply] using h
        · right; right; right
          have hinv : (transportPerm e M.edgeInv).symm (e x) = e (M.edgeInv.symm x) := by
            simp [transportPerm]
          apply e.injective
          simpa [CombinatorialMap.transport_edgeInv, hinv] using h
    have hreach := hM.1 (e.symm d) (e.symm d')
    have hmap : ∀ {x y}, Relation.ReflTransGen R x y →
        Relation.ReflTransGen R' (e x) (e y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hprev hlast ih => exact Relation.ReflTransGen.tail ih ((hstep _ _).mp hlast)
    have hreach' := hmap hreach
    simpa [R', Equiv.apply_symm_apply] using hreach'
  refine ⟨hconn, ?_⟩
  simpa only [CombinatorialMap.eulerChar,
    CombinatorialMap.transport_numVertices e M,
    CombinatorialMap.transport_numEdges e M,
    CombinatorialMap.transport_numFaces e M] using hM.2


/-- Transport the entire general bipolar boundary carrier across a dart
equivalence. Helper toward `thm-kmsw`, not the paper result -/
@[expose] noncomputable def BipolarTriangulationWithBoundaryBase.transport
    {ℓ r : ℕ} (e : D ≃ D')
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    BipolarTriangulationWithBoundaryBase D' ℓ r where
  map := B.map.transport e
  noMissingDarts := by
    intro d
    simpa using B.noMissingDarts (e.symm d)
  planar := CombinatorialMap.transport_isPlanar e B.map.toCombinatorialMap B.planar
  innerFacesDegreeThree := by
    intro d hd
    have hd' : ¬ B.map.IsOuter (e.symm d) := by
      intro ho
      apply hd
      exact (DirectedMapWithMissing.transport_isOuter_iff e B.map d).2 ho
    rcases B.innerFacesDegreeThree (e.symm d) hd' with ⟨h3, h1, h2⟩
    have hface (x : D) :
        (B.map.transport e).toCombinatorialMap.faceSucc (e x) =
          e (B.map.toCombinatorialMap.faceSucc x) :=
      CombinatorialMap.transport_faceSucc_apply e B.map.toCombinatorialMap x
    refine ⟨?_, ?_, ?_⟩
    · calc
        (B.map.transport e).toCombinatorialMap.faceSucc
          ((B.map.transport e).toCombinatorialMap.faceSucc
            ((B.map.transport e).toCombinatorialMap.faceSucc d)) =
            e (B.map.toCombinatorialMap.faceSucc
              (B.map.toCombinatorialMap.faceSucc
                (B.map.toCombinatorialMap.faceSucc (e.symm d)))) := by
                  rw [← e.apply_symm_apply d]
                  simp only [hface, Equiv.symm_apply_apply]
        _ = d := by simpa only [Equiv.apply_symm_apply] using congrArg e h3
    · intro heq
      apply h1
      apply e.injective
      calc
        e (B.map.toCombinatorialMap.faceSucc (e.symm d)) =
            (B.map.transport e).toCombinatorialMap.faceSucc d := by
          calc
            e (B.map.toCombinatorialMap.faceSucc (e.symm d)) =
                (B.map.transport e).toCombinatorialMap.faceSucc (e (e.symm d)) :=
              (hface (e.symm d)).symm
            _ = (B.map.transport e).toCombinatorialMap.faceSucc d :=
              congrArg _ (e.apply_symm_apply d)
        _ = d := heq
        _ = e (e.symm d) := by simp
    · intro heq
      apply h2
      apply e.injective
      calc
        e (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc (e.symm d))) =
            (B.map.transport e).toCombinatorialMap.faceSucc
              ((B.map.transport e).toCombinatorialMap.faceSucc d) := by
                rw [← e.apply_symm_apply d]
                simp only [hface, Equiv.symm_apply_apply]
        _ = d := heq
        _ = e (e.symm d) := by simp
  acyclic := DirectedMapWithMissing.transport_isAcyclic e B.map B.acyclic
  source := B.map.transportVertexEquiv e B.source
  sink := B.map.transportVertexEquiv e B.sink
  isSource := by
    rintro ⟨v, hv⟩
    let ve := B.map.transportVertexEquiv e
    apply B.isSource
    refine ⟨ve.symm v, ?_⟩
    have hv' : (B.map.transport e).directedStep
        (ve (ve.symm v)) (ve B.source) := by simpa [ve] using hv
    exact (directedStep_transport_iff e B.map (ve.symm v) B.source).mp hv'
  source_unique := by
    intro v hv
    let ve := B.map.transportVertexEquiv e
    have hv' : ¬ ∃ u, B.map.directedStep u (ve.symm v) := by
      rintro ⟨u, hu⟩
      apply hv
      refine ⟨ve u, ?_⟩
      simpa [ve] using
        (directedStep_transport_iff e B.map u (ve.symm v)).mpr hu
    exact (Equiv.apply_symm_apply ve v).symm.trans
      (congrArg ve (B.source_unique _ hv'))
  isSink := by
    rintro ⟨v, hv⟩
    let ve := B.map.transportVertexEquiv e
    apply B.isSink
    refine ⟨ve.symm v, ?_⟩
    have hv' : (B.map.transport e).directedStep
        (ve B.sink) (ve (ve.symm v)) := by simpa [ve] using hv
    exact (directedStep_transport_iff e B.map B.sink (ve.symm v)).mp hv'
  sink_unique := by
    intro v hv
    let ve := B.map.transportVertexEquiv e
    have hv' : ¬ ∃ w, B.map.directedStep (ve.symm v) w := by
      rintro ⟨w, hw⟩
      apply hv
      refine ⟨ve w, ?_⟩
      simpa [ve] using
        (directedStep_transport_iff e B.map (ve.symm v) w).mpr hw
    exact (Equiv.apply_symm_apply ve v).symm.trans
      (congrArg ve (B.sink_unique _ hv'))
  left_length_pos := B.left_length_pos
  right_length_pos := B.right_length_pos
  outerWord := NonemptyWord.transport e B.outerWord
  leftPath := SimpleDirectedDartPath.transport e B.leftPath
  rightPath := SimpleDirectedDartPath.transport e B.rightPath
  outerSplit := by
    have hright :
        (B.rightPath.darts.map e).reverse.map
            (B.map.transport e).toCombinatorialMap.edgeInv =
          (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).map e := by
      simp [List.map_reverse, List.map_map, Function.comp_def,
        CombinatorialMap.transport_edgeInv, transportPerm_apply]
    rw [SimpleDirectedDartPath.transport_darts, SimpleDirectedDartPath.transport_darts]
    rw [hright]
    exact fourArcsWitness_transport e B.map B.outerWord B.leftPath.darts []
      (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv) [] B.outerSplit

/-- The canonical orientation-preserving isomorphism from a base carrier to
its transported carrier. Helper toward `thm-kmsw`, not the paper result -/
@[expose] def BipolarTriangulationWithBoundaryBase.transportIso
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (e : D ≃ D') :
    BipolarBoundaryBaseIso B (B.transport e) where
  toEquiv := e
  rot_comm := by intro d; simp [BipolarTriangulationWithBoundaryBase.transport,
    CombinatorialMap.transport_rot, transportPerm_apply]
  edgeInv_comm := by intro d; simp [BipolarTriangulationWithBoundaryBase.transport,
    CombinatorialMap.transport_edgeInv, transportPerm_apply]
  missing_iff := by intro d; simp [BipolarTriangulationWithBoundaryBase.transport,
    DirectedMapWithMissing.transport]
  tail_iff := by intro d; simp [BipolarTriangulationWithBoundaryBase.transport,
    DirectedMapWithMissing.transport]
  outer_iff := by
    intro d
    simpa [BipolarTriangulationWithBoundaryBase.transport,
      DirectedMapWithMissing.transport] using
      (DirectedMapWithMissing.transport_isOuter_iff e B.map (e d))
  source_map := by
    intro d
    let ve := B.map.transportVertexEquiv e
    change (dartTailVertex B.map d = B.source) ↔
      (dartTailVertex (B.map.transport e) (e d) = ve B.source)
    rw [← DirectedMapWithMissing.transportVertexEquiv_dartTailVertex]
    constructor
    · intro h
      exact congrArg ve h
    · intro h
      exact ve.injective h
  sink_map := by
    intro d
    let ve := B.map.transportVertexEquiv e
    change (dartTailVertex B.map d = B.sink) ↔
      (dartTailVertex (B.map.transport e) (e d) = ve B.sink)
    rw [← DirectedMapWithMissing.transportVertexEquiv_dartTailVertex]
    constructor
    · intro h
      exact congrArg ve h
    · intro h
      exact ve.injective h
  leftDarts := by
    simp [BipolarTriangulationWithBoundaryBase.transport,
      SimpleDirectedDartPath.transport_darts]
  rightDarts := by
    simp [BipolarTriangulationWithBoundaryBase.transport,
      SimpleDirectedDartPath.transport_darts]
end DirectedDistances.PlanarMap

namespace DirectedDistances.PlanarMap

/-- A finite dart-labelled representative of a bipolar triangulation with
boundary lengths `ℓ` and `r`, carrying `n` edges. This is only a helper toward -/
structure KMSWMapRep (ℓ r n : ℕ) where
  dartCount : ℕ
  B : BipolarTriangulationWithBoundaryBase (Fin dartCount) ℓ r
  edges : B.map.toCombinatorialMap.numEdges = n

namespace KMSWMapRep


/-- Isomorphism of base maps defines the representative equivalence relation
for the map classes used toward `thm-kmsw`; helper only, not the paper result -/
@[expose] def isoSetoid (ℓ r n : ℕ) : Setoid (KMSWMapRep ℓ r n) where
  r R R' := Nonempty (BipolarBoundaryBaseIso R.B R'.B)
  iseqv := by
    constructor
    · intro R
      exact ⟨BipolarBoundaryBaseIso.refl R.B⟩
    · intro R R' h
      exact h.elim fun I => ⟨I.symm⟩
    · intro R R' R'' h₁ h₂
      exact h₁.elim fun I => h₂.elim fun J => ⟨I.trans J⟩

end KMSWMapRep

/-- Isomorphism classes of the representatives used toward `thm-kmsw`; helper -/
@[expose] def KMSWMapIsoClass (ℓ r n : ℕ) :=
  Quotient (KMSWMapRep.isoSetoid ℓ r n)

namespace KMSWMapRep

/-- Every representative has exactly twice as many darts as edges, since the
base carrier has no missing darts and every edge is an edge-involution pair.
Helper toward `thm-kmsw`, not the paper result -/
theorem dartCount_eq_two_mul (R : KMSWMapRep ℓ r n) :
    R.dartCount = 2 * n := by
  have h := CombinatorialMap.two_mul_numEdges R.B.map.toCombinatorialMap
  rw [R.edges, Fintype.card_fin] at h
  omega

/-- The one-edge initial map is present in the general base carrier for
`ℓ = r = n = 1`; it is the representative excluded by the strong carrier.
Helper toward `thm-kmsw`, not the paper result -/
noncomputable def singleEdge : KMSWMapRep 1 1 1 := by
  classical
  let M := CombinatorialMap.singleEdgeDirected
  let s : MapVertex M := dartTailVertex M 0
  let t : MapVertex M := dartHeadVertex M 0
  have hst : s ≠ t := by
    intro h
    change Quotient.mk _ (0 : Fin 2) = Quotient.mk _ 1 at h
    have hs : (CombinatorialMap.singleEdge.rot).SameCycle 0 1 := Quotient.exact h
    have h01 : (0 : Fin 2) = 1 := Equiv.Perm.sameCycle_one.mp hs
    exact Fin.zero_ne_one h01
  have hstep (v w : MapVertex M) : M.directedStep v w ↔ v = s ∧ w = t := by
    constructor
    · rintro ⟨d, hm, ht, htail, hhead⟩
      fin_cases d
      · exact ⟨htail.symm, hhead.symm⟩
      · have hnt : ¬ M.tail (1 : Fin 2) := by
          simp [M, CombinatorialMap.singleEdgeDirected]
        exact (hnt ht).elim
    · rintro ⟨rfl, rfl⟩
      refine ⟨0, ?_, ?_, rfl, rfl⟩ <;>
        simp [M, CombinatorialMap.singleEdgeDirected,
          CombinatorialMap.singleEdge]
  let P : SimpleDirectedDartPath M s t 1 := {
    darts := [0]
    vertices := [s, t]
    darts_length := by simp
    vertices_length := by simp
    vertices_nodup := by simp [hst]
    start_vertex := by simp
    end_vertex := by simp
    edge_step := by
      intro i
      fin_cases i
      simp [M, s, t, CombinatorialMap.singleEdgeDirected, CombinatorialMap.singleEdge]
  }
  let W : NonemptyWord (Fin 2) := ⟨[0, 1], by simp, by simp⟩
  have ho0 : M.IsOuter (0 : Fin 2) := by
    change CombinatorialMap.singleEdge.faceSucc.SameCycle 0 0
    exact Equiv.Perm.SameCycle.rfl
  have ho1 : M.IsOuter (1 : Fin 2) := by
    change CombinatorialMap.singleEdge.faceSucc.SameCycle 0 1
    exact ⟨1, by simp [CombinatorialMap.singleEdge, CombinatorialMap.faceSucc]⟩
  have hul0 : (0 : Fin 2) ∈ M.ulDarts := by
    change ¬ M.missing 0 ∧ M.tail 0 ∧ M.IsOuter 0
    exact ⟨by simp [M, CombinatorialMap.singleEdgeDirected],
      by simp [M, CombinatorialMap.singleEdgeDirected], ho0⟩
  have hul1 : (1 : Fin 2) ∉ M.ulDarts := by
    change ¬ M.missing 1 ∧ M.tail 1 ∧ M.IsOuter 1 → False
    intro h
    have hnt : ¬ M.tail 1 := by simp [M, CombinatorialMap.singleEdgeDirected]
    exact hnt h.2.1
  have hlr0 : (0 : Fin 2) ∉ M.lrDarts := by
    change ¬ M.missing 0 ∧ ¬ M.tail 0 ∧ M.IsOuter 0 → False
    intro h
    exact h.2.1 (by simp [M, CombinatorialMap.singleEdgeDirected])
  have hlr1 : (1 : Fin 2) ∈ M.lrDarts := by
    change ¬ M.missing 1 ∧ ¬ M.tail 1 ∧ M.IsOuter 1
    exact ⟨by simp [M, CombinatorialMap.singleEdgeDirected],
      by simp [M, CombinatorialMap.singleEdgeDirected], ho1⟩
  have houter : IsOuterCycle M W := by
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      fin_cases d
      · exact ho0
      · exact ho1
    · intro d hd
      fin_cases d <;> simp [W]
    · intro d hd
      fin_cases d <;> simp [W, M, CombinatorialMap.singleEdgeDirected,
        CombinatorialMap.singleEdge, CombinatorialMap.faceSucc]
  have hsplit : FourArcsWitness M W [0] [] [1] [] := by
    refine ⟨houter, ?_, ?_, ?_, ?_, ?_⟩
    · change [0, 1] ~r [0, 1]
      exact List.IsRotated.refl _
    · intro d
      fin_cases d
      · simp [hul0]
      · simp [hul1]
    · intro d
      fin_cases d
      · simp [hlr0]
      · simp [hlr1]
    · simp [MissingRun]
    · simp [MissingRun]
  let B : BipolarTriangulationWithBoundaryBase (Fin 2) 1 1 := {
    map := M
    noMissingDarts := by intro d; simp [M, CombinatorialMap.singleEdgeDirected]
    planar := by
      change CombinatorialMap.singleEdge.IsPlanar
      exact CombinatorialMap.singleEdge_isPlanar
    innerFacesDegreeThree := by
      intro d hd
      have ho : M.IsOuter d := by
        fin_cases d <;> simp [ho0, ho1]
      exact (hd ho).elim
    acyclic := by
      intro v hcyc
      rcases Relation.TransGen.head'_iff.mp hcyc with ⟨w, hvw, hrest⟩
      rcases (hstep v w).mp hvw with ⟨rfl, rfl⟩
      rcases hrest.cases_head with hEq | ⟨z, htz, _⟩
      · exact hst hEq.symm
      · rcases (hstep t z).mp htz with ⟨hts, _⟩
        exact hst hts.symm
    source := s
    sink := t
    isSource := by
      intro h
      obtain ⟨u, huv⟩ := h
      exact hst ((hstep u s).mp huv).2
    source_unique := by
      intro v hv
      obtain ⟨d, hd⟩ := Quotient.exists_rep v
      have hvd : v = dartTailVertex M d := hd.symm
      subst v
      fin_cases d
      · rfl
      · have hIn : M.directedStep s (dartTailVertex M (1 : Fin 2)) := by
          have hhead : dartHeadVertex M (0 : Fin 2) = dartTailVertex M 1 := by
            simp [M, CombinatorialMap.singleEdgeDirected, CombinatorialMap.singleEdge,
              dartTailVertex, dartHeadVertex]
          change ∃ d, ¬ M.missing d ∧ M.tail d ∧
            dartTailVertex M d = s ∧ dartHeadVertex M d = dartTailVertex M 1
          exact ⟨0, by simp [M, CombinatorialMap.singleEdgeDirected],
            by simp [M, CombinatorialMap.singleEdgeDirected], rfl, hhead⟩
        have h1t : dartTailVertex M (1 : Fin 2) = t := by
          simp [t, M, CombinatorialMap.singleEdgeDirected,
            CombinatorialMap.singleEdge, dartTailVertex, dartHeadVertex]
        exact (hv ⟨s, hIn⟩).elim
    isSink := by
      intro h
      obtain ⟨w, htw⟩ := h
      exact hst ((hstep t w).mp htw).1.symm
    sink_unique := by
      intro v hv
      obtain ⟨d, hd⟩ := Quotient.exists_rep v
      have hvd : v = dartTailVertex M d := hd.symm
      subst v
      fin_cases d
      · have hStep : M.directedStep (dartTailVertex M 0) t := by
          change ∃ d, ¬ M.missing d ∧ M.tail d ∧
            dartTailVertex M d = dartTailVertex M 0 ∧ dartHeadVertex M d = t
          exact ⟨0, by simp [M, CombinatorialMap.singleEdgeDirected],
            by simp [M, CombinatorialMap.singleEdgeDirected], rfl, rfl⟩
        exact (hv ⟨t, hStep⟩).elim
      · rfl
    left_length_pos := by omega
    right_length_pos := by omega
    outerWord := W
    leftPath := P
    rightPath := P
    outerSplit := by
      change FourArcsWitness M W [0] [] [M.toCombinatorialMap.edgeInv 0] []
      have hflip : M.toCombinatorialMap.edgeInv 0 = 1 := by
        simp [M, CombinatorialMap.singleEdgeDirected, CombinatorialMap.singleEdge]
      rw [hflip]
      exact hsplit
  }
  exact ⟨2, B, by
    change CombinatorialMap.singleEdge.numEdges = 1
    exact CombinatorialMap.numEdges_singleEdge⟩

/-- Choose the canonical representative of a finite base carrier by relabelling
its darts onto `Fin (card D)`. Helper toward `thm-kmsw`, not the paper result -/
@[expose] noncomputable def ofBase {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hB : B.map.toCombinatorialMap.numEdges = n) : KMSWMapRep ℓ r n := by
  let e := Fintype.equivFin D
  refine ⟨Fintype.card D, B.transport e, ?_⟩
  exact (B.transportIso e).numEdges_eq.symm.trans hB

/-- Equality of the canonically labelled quotient representatives is exactly
base-carrier isomorphism. Helper toward `thm-kmsw`, not the paper result -/
theorem mk_ofBase_eq_iff {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hB : B.map.toCombinatorialMap.numEdges = n)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (hB' : B'.map.toCombinatorialMap.numEdges = n) :
    (Quotient.mk (KMSWMapRep.isoSetoid ℓ r n) (ofBase B hB) =
      Quotient.mk (KMSWMapRep.isoSetoid ℓ r n) (ofBase B' hB')) ↔
        Nonempty (BipolarBoundaryBaseIso B B') := by
  let e := Fintype.equivFin D
  let e' := Fintype.equivFin D'
  constructor
  · intro h
    rcases (Quotient.exact h) with ⟨I⟩
    let J := (B.transportIso e).trans I
    exact ⟨J.trans (B'.transportIso e').symm⟩
  · rintro ⟨I⟩
    let J := (B.transportIso e).symm.trans I
    exact Quotient.sound ⟨J.trans (B'.transportIso e')⟩

end KMSWMapRep

/-- Finite data retained by an isomorphism class of base carriers on a fixed
dart set. Predicates are recorded by their truth tables, and the boundary paths
by fixed-length dart functions. Helper toward `thm-kmsw`, not the paper result -/
structure KMSWMapIsoCode (ℓ r N : ℕ) where
  rot : Equiv.Perm (Fin N)
  edgeInv : Equiv.Perm (Fin N)
  missing : Fin N → Bool
  tail : Fin N → Bool
  outer : Fin N → Bool
  source : Fin N → Bool
  sink : Fin N → Bool
  left : Fin ℓ → Fin N
  right : Fin r → Fin N

/-- View a fixed-length path's dart list as a function on its length index.
Helper toward `thm-kmsw`, not the paper result -/
def KMSWMapIsoCode.pathDarts {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Fin k → D := fun i => P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩

/-- Encode a carrier's isomorphism-relevant finite data. Helper toward -/
@[expose] noncomputable def KMSWMapIsoCode.ofBase {ℓ r N : ℕ}
    (B : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r) :
    KMSWMapIsoCode ℓ r N := by
  classical
  exact {
    rot := B.map.toCombinatorialMap.rot
    edgeInv := B.map.toCombinatorialMap.edgeInv
    missing := fun d => decide (B.map.missing d)
    tail := fun d => decide (B.map.tail d)
    outer := fun d => decide (B.map.IsOuter d)
    source := fun d => decide (dartTailVertex B.map d = B.source)
    sink := fun d => decide (dartTailVertex B.map d = B.sink)
    left := KMSWMapIsoCode.pathDarts B.leftPath
    right := KMSWMapIsoCode.pathDarts B.rightPath }

private theorem iff_of_decide_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : decide p = decide q) : p ↔ q := by
  constructor
  · intro hp
    have hp' : decide p = true := decide_eq_true hp
    rw [h] at hp'
    exact of_decide_eq_true hp'
  · intro hq
    have hq' : decide q = true := decide_eq_true hq
    rw [← h] at hq'
    exact of_decide_eq_true hq'

private theorem list_eq_of_pathDarts_eq {D : Type*} [Fintype D] [DecidableEq D]
    {M M' : DirectedMapWithMissing D}
    {s t : MapVertex M} {s' t' : MapVertex M'} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (Q : SimpleDirectedDartPath M' s' t' k)
    (h : KMSWMapIsoCode.pathDarts P = KMSWMapIsoCode.pathDarts Q) :
    P.darts = Q.darts := by
  apply List.ext_get
  · rw [P.darts_length, Q.darts_length]
  · intro i hi hi'
    have hiK : i < k := by simpa [P.darts_length] using hi
    simpa [KMSWMapIsoCode.pathDarts] using congrFun h ⟨i, hiK⟩

/-- Equal finite codes yield a boundary isomorphism with the identity dart
map. Helper toward `thm-kmsw`, not the paper result -/
private theorem KMSWMapIsoCode.eq_implies_baseIso {ℓ r N : ℕ}
    {B B' : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r}
    (h : KMSWMapIsoCode.ofBase B = KMSWMapIsoCode.ofBase B') :
    Nonempty (BipolarBoundaryBaseIso B B') := by
  classical
  have hrot := congrArg KMSWMapIsoCode.rot h
  have hedge := congrArg KMSWMapIsoCode.edgeInv h
  have hmissing := congrArg KMSWMapIsoCode.missing h
  have htail := congrArg KMSWMapIsoCode.tail h
  have houter := congrArg KMSWMapIsoCode.outer h
  have hsource := congrArg KMSWMapIsoCode.source h
  have hsink := congrArg KMSWMapIsoCode.sink h
  have hleft := congrArg KMSWMapIsoCode.left h
  have hright := congrArg KMSWMapIsoCode.right h
  have hleftDarts : B.leftPath.darts = B'.leftPath.darts :=
    list_eq_of_pathDarts_eq B.leftPath B'.leftPath hleft
  have hrightDarts : B.rightPath.darts = B'.rightPath.darts :=
    list_eq_of_pathDarts_eq B.rightPath B'.rightPath hright
  refine ⟨{
    toEquiv := Equiv.refl (Fin N)
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    outer_iff := ?_
    source_map := ?_
    sink_map := ?_
    leftDarts := ?_
    rightDarts := ?_ }⟩
  · intro d
    exact congrArg (fun f : Equiv.Perm (Fin N) => f d) hrot
  · intro d
    exact congrArg (fun f : Equiv.Perm (Fin N) => f d) hedge
  · intro d
    exact (iff_of_decide_eq (congrFun hmissing d)).symm
  · intro d
    exact (iff_of_decide_eq (congrFun htail d)).symm
  · intro d
    exact (iff_of_decide_eq (congrFun houter d)).symm
  · intro d
    exact iff_of_decide_eq (congrFun hsource d)
  · intro d
    exact iff_of_decide_eq (congrFun hsink d)
  · simpa using hleftDarts
  · simpa using hrightDarts

private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  cases hp : decide p <;> cases hq : decide q <;>
    simp_all [decide_eq_true_eq]

private theorem KMSWMapIsoCode.ext_data {ℓ r N : ℕ}
    {c c' : KMSWMapIsoCode ℓ r N}
    (hrot : c.rot = c'.rot) (hedge : c.edgeInv = c'.edgeInv)
    (hmissing : c.missing = c'.missing) (htail : c.tail = c'.tail)
    (houter : c.outer = c'.outer) (hsource : c.source = c'.source)
    (hsink : c.sink = c'.sink) (hleft : c.left = c'.left)
    (hright : c.right = c'.right) : c = c' := by
  cases c
  cases c'
  simp_all

private theorem KMSWMapIsoCode.eq_of_baseIso_refl {ℓ r N : ℕ}
    {B B' : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (hI : I.toEquiv = Equiv.refl (Fin N)) :
    KMSWMapIsoCode.ofBase B = KMSWMapIsoCode.ofBase B' := by
  classical
  apply KMSWMapIsoCode.ext_data
  · exact Equiv.ext fun d => by
      simpa [KMSWMapIsoCode.ofBase, hI] using I.rot_comm d
  · exact Equiv.ext fun d => by
      simpa [KMSWMapIsoCode.ofBase, hI] using I.edgeInv_comm d
  · funext d
    simpa [KMSWMapIsoCode.ofBase, hI] using decide_eq_of_iff (I.missing_iff d).symm
  · funext d
    simpa [KMSWMapIsoCode.ofBase, hI] using decide_eq_of_iff (I.tail_iff d).symm
  · funext d
    simpa [KMSWMapIsoCode.ofBase, hI] using decide_eq_of_iff (I.outer_iff d).symm
  · funext d
    simpa [KMSWMapIsoCode.ofBase, hI] using decide_eq_of_iff (I.source_map d)
  · funext d
    simpa [KMSWMapIsoCode.ofBase, hI] using decide_eq_of_iff (I.sink_map d)
  · have hlist : B.leftPath.darts = B'.leftPath.darts := by
      simpa [hI] using I.leftDarts
    funext i
    simp [KMSWMapIsoCode.ofBase, KMSWMapIsoCode.pathDarts, hlist]
  · have hlist : B.rightPath.darts = B'.rightPath.darts := by
      simpa [hI] using I.rightDarts
    funext i
    simp [KMSWMapIsoCode.ofBase, KMSWMapIsoCode.pathDarts, hlist]

private theorem KMSWMapIsoCode.finite (ℓ r N : ℕ) :
    Finite (KMSWMapIsoCode ℓ r N) := by
  classical
  apply Finite.of_injective
    (fun c => (c.rot, c.edgeInv, c.missing, c.tail, c.outer, c.source,
      c.sink, c.left, c.right))
  intro c c' h
  cases c
  cases c'
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  rfl

/-- The finite orbit of all truth-table codes obtained by relabelling a base
carrier. Helper toward `thm-kmsw`, not the paper result -/
private noncomputable def KMSWMapIsoCode.orbit {ℓ r N : ℕ}
    (B : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r) :
    Finset (KMSWMapIsoCode ℓ r N) := by
  classical
  letI : Finite (KMSWMapIsoCode ℓ r N) := KMSWMapIsoCode.finite ℓ r N
  letI : Fintype (KMSWMapIsoCode ℓ r N) := Fintype.ofFinite _
  exact Finset.univ.filter fun c =>
    ∃ σ : Equiv.Perm (Fin N), KMSWMapIsoCode.ofBase (B.transport σ) = c

private theorem KMSWMapIsoCode.orbit_eq_of_baseIso {ℓ r N : ℕ}
    {B B' : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    KMSWMapIsoCode.orbit B = KMSWMapIsoCode.orbit B' := by
  classical
  apply Finset.ext
  intro c
  simp only [KMSWMapIsoCode.orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨σ, hσ⟩
    let τ : Equiv.Perm (Fin N) := I.toEquiv.symm.trans σ
    let J := (B.transportIso σ).symm.trans (I.trans (B'.transportIso τ))
    have hJ : J.toEquiv = Equiv.refl (Fin N) := by
      ext d
      simp [J, τ, BipolarBoundaryBaseIso.trans, BipolarBoundaryBaseIso.symm,
        BipolarTriangulationWithBoundaryBase.transportIso, Equiv.trans_apply]
    refine ⟨τ, ?_⟩
    exact (KMSWMapIsoCode.eq_of_baseIso_refl J hJ).symm.trans hσ
  · rintro ⟨τ, hτ⟩
    let σ : Equiv.Perm (Fin N) := I.toEquiv.trans τ
    let J := (B'.transportIso τ).symm.trans (I.symm.trans (B.transportIso σ))
    have hJ : J.toEquiv = Equiv.refl (Fin N) := by
      ext d
      simp [J, σ, BipolarBoundaryBaseIso.trans, BipolarBoundaryBaseIso.symm,
        BipolarTriangulationWithBoundaryBase.transportIso, Equiv.trans_apply]
    refine ⟨σ, ?_⟩
    exact (KMSWMapIsoCode.eq_of_baseIso_refl J hJ).symm.trans hτ

private theorem KMSWMapIsoCode.orbit_eq_iff_baseIso {ℓ r N : ℕ}
    {B B' : BipolarTriangulationWithBoundaryBase (Fin N) ℓ r} :
    KMSWMapIsoCode.orbit B = KMSWMapIsoCode.orbit B' ↔
      Nonempty (BipolarBoundaryBaseIso B B') := by
  classical
  constructor
  · intro h
    let hI := B.transportIso (Equiv.refl (Fin N))
    have hIeq : hI.toEquiv = Equiv.refl (Fin N) := rfl
    have hcode := KMSWMapIsoCode.eq_of_baseIso_refl hI hIeq
    have hc : KMSWMapIsoCode.ofBase B ∈ KMSWMapIsoCode.orbit B := by
      classical
      simp only [KMSWMapIsoCode.orbit, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Equiv.refl _, hcode.symm⟩
    have hc' : KMSWMapIsoCode.ofBase B ∈ KMSWMapIsoCode.orbit B' := by
      rw [← h]
      exact hc
    have hwit := (Finset.mem_filter.mp hc').2
    rcases hwit with ⟨τ, hτ⟩
    rcases KMSWMapIsoCode.eq_implies_baseIso hτ.symm with ⟨J⟩
    exact ⟨J.trans (B'.transportIso τ).symm⟩
  · rintro ⟨I⟩
    exact KMSWMapIsoCode.orbit_eq_of_baseIso I

private noncomputable def KMSWMapRep.fixedBase {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) :
    BipolarTriangulationWithBoundaryBase (Fin (2 * n)) ℓ r :=
  R.B.transport (finCongr R.dartCount_eq_two_mul)

private theorem KMSWMapRep.fixedBaseIso {ℓ r n : ℕ}
    {R R' : KMSWMapRep ℓ r n}
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (BipolarBoundaryBaseIso R.fixedBase R'.fixedBase) := by
  let e := finCongr R.dartCount_eq_two_mul
  let e' := finCongr R'.dartCount_eq_two_mul
  exact ⟨(R.B.transportIso e).symm.trans
    (I.trans (R'.B.transportIso e'))⟩

private noncomputable def KMSWMapIsoClass.orbitCode {ℓ r n : ℕ}
    (q : KMSWMapIsoClass ℓ r n) :
    Finset (KMSWMapIsoCode ℓ r (2 * n)) :=
  Quotient.lift
    (fun R : KMSWMapRep ℓ r n => KMSWMapIsoCode.orbit R.fixedBase)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact KMSWMapIsoCode.orbit_eq_of_baseIso
        (R.fixedBaseIso I).some)
    q

private theorem KMSWMapIsoClass.orbitCode_injective {ℓ r n : ℕ} :
    Function.Injective (@KMSWMapIsoClass.orbitCode ℓ r n) := by
  intro q q' h
  revert h
  refine Quotient.inductionOn₂ q q' ?_
  intro R R' h
  change KMSWMapIsoCode.orbit R.fixedBase =
    KMSWMapIsoCode.orbit R'.fixedBase at h
  have horbit := h
  have hI : Nonempty (BipolarBoundaryBaseIso R.fixedBase R'.fixedBase) :=
    KMSWMapIsoCode.orbit_eq_iff_baseIso.mp horbit
  rcases hI with ⟨I⟩
  let e := finCongr R.dartCount_eq_two_mul
  let e' := finCongr R'.dartCount_eq_two_mul
  have J : BipolarBoundaryBaseIso R.B R'.B :=
    (R.B.transportIso e).trans
      (I.trans (R'.B.transportIso e').symm)
  exact Quotient.sound ⟨J⟩

@[instance_reducible]
private noncomputable def KMSWMapIsoCode.fintypeFinset (ℓ r N : ℕ) :
    Fintype (Finset (KMSWMapIsoCode ℓ r N)) := by
  classical
  letI : Finite (KMSWMapIsoCode ℓ r N) := KMSWMapIsoCode.finite ℓ r N
  letI : Fintype (KMSWMapIsoCode ℓ r N) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun s c => decide (c ∈ s)) (by
    intro s t h
    ext c
    have hc := congrFun h c
    simpa using hc)

/-- There are finitely many isomorphism classes of the finite-map helpers at
fixed boundary lengths and edge count. This is only a helper toward -/
theorem KMSWMapIsoClass.finite (ℓ r n : ℕ) :
    Finite (KMSWMapIsoClass ℓ r n) := by
  classical
  exact @Finite.of_injective
    (KMSWMapIsoClass ℓ r n)
    (Finset (KMSWMapIsoCode ℓ r (2 * n)))
    (@Finite.of_fintype _ (KMSWMapIsoCode.fintypeFinset ℓ r (2 * n)))
    KMSWMapIsoClass.orbitCode
    KMSWMapIsoClass.orbitCode_injective

namespace KMSWMapIsoClass

/-- The class of a representative, as a helper toward `thm-kmsw`; not the -/
@[expose] def mk {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) :
    KMSWMapIsoClass ℓ r n :=
  Quotient.mk _ R

/-- Equality of helper classes is exactly base-map isomorphism; helper toward -/
theorem mk_eq_mk_iff {ℓ r n : ℕ} (R R' : KMSWMapRep ℓ r n) :
    mk R = mk R' ↔ Nonempty (BipolarBoundaryBaseIso R.B R'.B) := by
  constructor
  · exact Quotient.exact
  · rintro ⟨I⟩
    change Quotient.mk (KMSWMapRep.isoSetoid ℓ r n) R =
      Quotient.mk (KMSWMapRep.isoSetoid ℓ r n) R'
    exact Quotient.sound ⟨I⟩

/-- Proposition induction on a helper class, toward `thm-kmsw`; not the paper -/
theorem ind {ℓ r n : ℕ}
    {motive : KMSWMapIsoClass ℓ r n → Prop}
    (h : ∀ R, motive (mk R)) (q : KMSWMapIsoClass ℓ r n) : motive q :=
  Quotient.inductionOn q h

/-- Lift a representative function that is invariant under base-map
isomorphism to helper classes, toward `thm-kmsw`; not the paper result -/
@[expose] def lift {ℓ r n : ℕ} {α : Sort u}
    (f : KMSWMapRep ℓ r n → α)
    (hf : ∀ R R', Nonempty (BipolarBoundaryBaseIso R.B R'.B) → f R = f R') :
    KMSWMapIsoClass ℓ r n → α :=
  Quotient.lift f (by
    intro R R' h
    exact hf R R' h)

/-- The lift agrees with its representative function; helper toward -/
theorem lift_mk {ℓ r n : ℕ} {α : Sort u}
    (f : KMSWMapRep ℓ r n → α)
    (hf : ∀ R R', Nonempty (BipolarBoundaryBaseIso R.B R'.B) → f R = f R')
    (R : KMSWMapRep ℓ r n) :
    lift f hf (mk R) = f R := rfl

end KMSWMapIsoClass
end DirectedDistances.PlanarMap
