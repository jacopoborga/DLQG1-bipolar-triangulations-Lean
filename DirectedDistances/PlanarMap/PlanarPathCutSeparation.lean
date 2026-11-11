/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutData
public import DirectedDistances.PlanarMap.PlanarFaceCycleSpace
import DirectedDistances.PlanarMap.FiniteBipolarBlockConventions

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Planar separation for a path cut

Helper toward `lem-lr-ind`; this is not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem edgeOrbit_sum (M : CombinatorialMap D) (d : D)
    (g : D → ZMod 2) [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    (∑ x : D, if edgeClass M x = edgeClass M d then g x else 0) =
      g d + g (M.edgeInv d) := by
  classical
  have hfilter :
      Finset.univ.filter (fun x : D => edgeClass M x = edgeClass M d) =
        {d, M.edgeInv d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hrel : M.edgeInv.SameCycle d x := (Quotient.exact hx).symm
      rcases (CombinatorialMap.edgeInv_sameCycle_iff M d x).mp hrel with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · rfl
      · apply Quotient.sound
        exact ((CombinatorialMap.edgeInv_sameCycle_iff M d (M.edgeInv d)).mpr
          (Or.inr rfl)).symm
  have hne : d ≠ M.edgeInv d := Ne.symm (M.edgeInv_ne d)
  rw [← Finset.sum_filter, hfilter]
  simp [hne]

private theorem vertexBoundary_single_edge (M : CombinatorialMap D) (d : D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)] :
    vertexBoundary M (Pi.single (edgeClass M d) 1) =
      (fun v => if vertexClass M d = v then (1 : ZMod 2) else 0) +
        (fun v => if vertexClass M (M.edgeInv d) = v then 1 else 0) := by
  classical
  funext v
  unfold vertexBoundary
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  have hsum := edgeOrbit_sum M d
    (fun x => if vertexClass M x = v then (1 : ZMod 2) else 0)
  calc
    (∑ x : D, if vertexClass M x = v then
        if edgeClass M x = edgeClass M d then (1 : ZMod 2) else 0 else 0) =
      ∑ x : D, if edgeClass M x = edgeClass M d then
        if vertexClass M x = v then (1 : ZMod 2) else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hv : vertexClass M x = v <;>
            by_cases he : edgeClass M x = edgeClass M d <;> simp [hv, he]
    _ = (if vertexClass M d = v then 1 else 0) +
        (if vertexClass M (M.edgeInv d) = v then 1 else 0) := hsum
    _ = (if vertexClass M d = v then (1 : ZMod 2) else 0) +
        (if vertexClass M (M.edgeInv d) = v then 1 else 0) := rfl

private noncomputable def dartPathChain (M : CombinatorialMap D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] {k : ℕ}
    (edges : Fin k → D) : EdgeSpace M :=
  ∑ i : Fin k, Pi.single (edgeClass M (edges i)) 1

private theorem dartPathChain_succ (M : CombinatorialMap D) {k : ℕ}
    (edges : Fin (k + 1) → D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    dartPathChain M edges =
      Pi.single (edgeClass M (edges 0)) 1 +
        dartPathChain M (fun i => edges i.succ) := by
  classical
  simp [dartPathChain, Fin.sum_univ_succ]

private theorem indicator_eq_of_eq {α : Type*} [DecidableEq α]
    (a b x : α) (hab : a = b) :
    (if a = x then (1 : ZMod 2) else 0) =
      (if b = x then 1 else 0) := by
  cases hab
  rfl

private theorem vertexBoundary_dartPathChain (M : CombinatorialMap D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)] {k : ℕ}
    (edges : Fin k → D) (vertices : Fin (k + 1) → CombinatorialMap.VertexQuotient M)
    (hstep : ∀ i : Fin k,
      vertexClass M (edges i) = vertices i.castSucc ∧
      vertexClass M (M.edgeInv (edges i)) = vertices i.succ) :
    vertexBoundary M (dartPathChain M edges) =
      (fun v => (if vertices 0 = v then (1 : ZMod 2) else 0) +
        (if vertices (Fin.last k) = v then 1 else 0)) := by
  induction k with
  | zero =>
      funext v
      simp [dartPathChain, CharTwo.add_self_eq_zero]
  | succ k ih =>
      let edges' : Fin k → D := fun i => edges i.succ
      let vertices' : Fin (k + 1) → CombinatorialMap.VertexQuotient M :=
        fun i => vertices i.succ
      have hstep' : ∀ i : Fin k,
          vertexClass M (edges' i) = vertices' i.castSucc ∧
          vertexClass M (M.edgeInv (edges' i)) = vertices' i.succ := by
        intro i
        simpa [edges', vertices'] using hstep i.succ
      have hrec := ih edges' vertices' hstep'
      rw [dartPathChain_succ, LinearMap.map_add, vertexBoundary_single_edge,
        hrec]
      funext v
      simp only [Pi.add_apply]
      have hfirst := hstep 0
      have hcast : Fin.castSucc (0 : Fin (k + 1)) = (0 : Fin (k + 2)) := by
        ext
        rfl
      have hmiddle :
          (if vertices' 0 = v then (1 : ZMod 2) else 0) +
            (if vertices' 0 = v then 1 else 0) = 0 := by
        exact CharTwo.add_self_eq_zero _
      have hstart : vertexClass M (edges 0) = vertices 0 := by
        calc
          vertexClass M (edges 0) = vertices (Fin.castSucc 0) := hfirst.1
          _ = vertices 0 := congrArg vertices hcast
      have hhead : vertexClass M (M.edgeInv (edges 0)) = vertices' 0 := by
        simpa [vertices'] using hfirst.2
      have hfinish : vertices' (Fin.last k) = vertices (Fin.last (k + 1)) := by
        dsimp [vertices']
      have hstartVal :
          (if vertexClass M (edges 0) = v then (1 : ZMod 2) else 0) =
            (if vertices 0 = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hstart
      have hheadVal :
          (if vertexClass M (M.edgeInv (edges 0)) = v then (1 : ZMod 2) else 0) =
            (if vertices' 0 = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hhead
      have hfinishVal :
          (if vertices' (Fin.last k) = v then (1 : ZMod 2) else 0) =
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hfinish
      rw [hstartVal, hheadVal, hfinishVal]
      calc
        _ = (if vertices 0 = v then (1 : ZMod 2) else 0) +
            ((if vertices' 0 = v then 1 else 0) +
              (if vertices' 0 = v then 1 else 0)) +
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
              abel
        _ = (if vertices 0 = v then (1 : ZMod 2) else 0) +
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
              rw [hmiddle]
              simp

private def simplePathEdges {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Fin k → D := fun i => P.darts.get ⟨i.val, by
      rw [P.darts_length]
      exact i.isLt⟩

private def simplePathVertices {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Fin (k + 1) → MapVertex M := fun i => P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      omega⟩

private theorem simplePath_edgeClass_injective {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Function.Injective (fun i : Fin k =>
      edgeClass M.toCombinatorialMap (simplePathEdges P i)) := by
  intro i j hij
  let di := simplePathEdges P i
  let dj := simplePathEdges P j
  have hi : i.val < P.darts.length := by simp [P.darts_length]
  have hj : j.val < P.darts.length := by simp [P.darts_length]
  have hrel : M.toCombinatorialMap.edgeInv.SameCycle di dj := Quotient.exact hij
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap di dj).mp hrel with
    hsame | hinv
  · have hiStep := P.edge_step ⟨i.val, hi⟩
    have hjStep := P.edge_step ⟨j.val, hj⟩
    have hvertices :
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex M di := hiStep.2.2.1
        _ = dartTailVertex M dj := by rw [hsame]
        _ = P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ :=
          hjStep.2.2.1.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hvertices
    exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val) hidx)
  · have hiStep := P.edge_step ⟨i.val, hi⟩
    have hjStep := P.edge_step ⟨j.val, hj⟩
    have hnotTail := (M.tail_iff di hiStep.1).mp hiStep.2.1
    have hjTail : M.tail dj := hjStep.2.1
    rw [hinv] at hjTail
    exact (hnotTail hjTail).elim

private theorem simplePath_chain_step {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k)
    (i : Fin k) :
    vertexClass M.toCombinatorialMap (simplePathEdges P i) =
        simplePathVertices P i.castSucc ∧
      vertexClass M.toCombinatorialMap
          (M.toCombinatorialMap.edgeInv (simplePathEdges P i)) =
        simplePathVertices P i.succ := by
  have hi : i.val < P.darts.length := by
    simp [P.darts_length]
  have hstep := P.edge_step ⟨i.val, hi⟩
  constructor
  · calc
      vertexClass M.toCombinatorialMap (simplePathEdges P i) =
          dartTailVertex M (simplePathEdges P i) := rfl
      _ = P.vertices.get ⟨i.val, by
          have hk := P.darts_length
          rw [P.vertices_length]
          omega⟩ := hstep.2.2.1.symm
      _ = simplePathVertices P i.castSucc := by
        dsimp [simplePathVertices]
  · calc
      vertexClass M.toCombinatorialMap
          (M.toCombinatorialMap.edgeInv (simplePathEdges P i)) =
          dartHeadVertex M (simplePathEdges P i) := rfl
      _ = P.vertices.get ⟨i.val + 1, by
          have hk := P.darts_length
          rw [P.vertices_length]
          omega⟩ := hstep.2.2.2.symm
      _ = simplePathVertices P i.succ := by
        dsimp [simplePathVertices]

/- the paper result. A dart of a simple path based at its source is its first
dart. -/
private theorem simplePath_dart_eq_first_of_tail_source
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (hk : 0 < k) {d : D}
    (hd : d ∈ P.darts) (hsource : dartTailVertex M d = s) :
    d = P.darts.get ⟨0, by rw [P.darts_length]; exact hk⟩ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hstep := P.edge_step i
  have hvertex : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = s := by
    calc
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex M (P.darts.get i) := hstep.2.2.1
      _ = dartTailVertex M d := congrArg (dartTailVertex M) hi
      _ = s := hsource
  have hi0 : i.val = 0 := by
    by_contra hne
    have hget :
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
      calc
        _ = s := hvertex
        _ = _ := P.start_vertex.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hget
    have hval : i.val = 0 := by simpa using congrArg Fin.val hidx
    exact hne hval
  have hifin : i = ⟨0, by rw [P.darts_length]; exact hk⟩ := Fin.ext hi0
  rw [hifin] at hi
  exact hi.symm




private theorem simplePath_dart_eq_of_endpoint_eq
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {a b : D}
    (ha : a ∈ P.darts) (hb : b ∈ P.darts)
    (h : dartTailVertex M a = dartTailVertex M b ∨
      dartHeadVertex M a = dartHeadVertex M b) : a = b := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
  have hi := P.edge_step i
  have hj := P.edge_step j
  have hij : i.val = j.val := by
    rcases h with h | h
    · have he := hi.2.2.1.trans (h.trans hj.2.2.1.symm)
      have he' := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp he)
      exact he'
    · have he := hi.2.2.2.trans (h.trans hj.2.2.2.symm)
      have he' := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp he)
      dsimp at he'
      omega
  exact congrArg P.darts.get (Fin.ext hij)



private theorem simplePath_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (P.edge_step i).2.1

private theorem simplePath_vertexBoundary {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k)
    [DecidableEq (CombinatorialMap.EdgeQuotient M.toCombinatorialMap)]
    [DecidableEq (CombinatorialMap.VertexQuotient M.toCombinatorialMap)] :
    vertexBoundary M.toCombinatorialMap (dartPathChain M.toCombinatorialMap
      (simplePathEdges P)) =
      (fun v => (if s = v then (1 : ZMod 2) else 0) +
        (if t = v then 1 else 0)) := by
  classical
  have h := vertexBoundary_dartPathChain M.toCombinatorialMap
    (simplePathEdges P) (simplePathVertices P) (simplePath_chain_step P)
  have hstart : simplePathVertices P 0 = s := by
    simpa [simplePathVertices] using P.start_vertex
  have hfinish : simplePathVertices P (Fin.last k) = t := by
    simpa [simplePathVertices, P.vertices_length] using P.end_vertex
  funext v
  have hpoint := congrFun h v
  rw [indicator_eq_of_eq _ _ _ hstart, indicator_eq_of_eq _ _ _ hfinish] at hpoint
  exact hpoint

private theorem pathCut_cycleBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidableEq (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)]
    [DecidableEq (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap)] :
    vertexBoundary B.map.toCombinatorialMap
      (dartPathChain B.map.toCombinatorialMap (simplePathEdges P) +
        dartPathChain B.map.toCombinatorialMap (simplePathEdges B.leftPath)) = 0 := by
  classical
  rw [map_add, simplePath_vertexBoundary P, simplePath_vertexBoundary B.leftPath]
  ext v
  simp only [Pi.add_apply, Pi.zero_apply]
  let a : ZMod 2 := if B.source = v then 1 else 0
  let b : ZMod 2 := if B.sink = v then 1 else 0
  calc
    a + b + (a + b) = (a + a) + (b + b) := by abel
    _ = 0 := by rw [CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b]; simp

private theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective 2
    simp [hval]
  · right
    apply ZMod.val_injective 2
    rw [hval, ZMod.val_one_eq_one_mod]

/-- The mod-two edge chain of a simple directed dart path, with one coefficient
helper toward `lem-lr-ind`, not the paper result. -/
@[expose] noncomputable def pathCutPathChain
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) : EdgeSpace M.toCombinatorialMap := by
  classical
  exact ∑ i : Fin k, Pi.single
    (edgeClass M.toCombinatorialMap (P.darts.get ⟨i.val, by
      rw [P.darts_length]
      exact i.isLt⟩)) 1

private theorem pathCutPathChain_apply_eq_one_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    pathCutPathChain P (edgeClass M.toCombinatorialMap d) = 1 := by
  classical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  let j : Fin k := ⟨i.val, by simpa [P.darts_length] using i.isLt⟩
  have hdj : simplePathEdges P j = d := by
    dsimp [simplePathEdges, j]
    simpa using hi
  unfold pathCutPathChain
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_apply]
    have hval : edgeClass M.toCombinatorialMap d =
        edgeClass M.toCombinatorialMap (P.darts[j.val]) := by
      simpa [simplePathEdges, List.get_eq_getElem] using
        (congrArg (edgeClass M.toCombinatorialMap) hdj).symm
    simp [hval]
  · intro q hq hqj
    simp only [Pi.single_apply]
    have hneq :
        edgeClass M.toCombinatorialMap (simplePathEdges P q) ≠
          edgeClass M.toCombinatorialMap d := by
      intro heq
      have hclass :
          edgeClass M.toCombinatorialMap (simplePathEdges P q) =
            edgeClass M.toCombinatorialMap (simplePathEdges P j) := by
        rw [heq, hdj]
      exact hqj (simplePath_edgeClass_injective P hclass)
    have hneq' : edgeClass M.toCombinatorialMap d ≠
        edgeClass M.toCombinatorialMap
          (P.darts.get ⟨q.val, by rw [P.darts_length]; exact q.isLt⟩) := by
      simpa [simplePathEdges, List.get_eq_getElem] using hneq.symm
    simpa [List.get_eq_getElem] using hneq'
  · simp

/-- A dart outside the cut path and its reversal has zero coefficient in the
toward `lem-lr-ind`, not the paper result. -/
theorem pathCutPathChain_apply_eq_zero_of_not_seam
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hseam : d ∉ pathCutSeamDarts B P) :
    pathCutPathChain P (edgeClass B.map.toCombinatorialMap d) = 0 := by
  classical
  unfold pathCutPathChain
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  let e := P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
  have he_mem : e ∈ P.darts := by
    dsimp [e]
    exact List.get_mem _ _
  have hneq : edgeClass B.map.toCombinatorialMap e ≠
      edgeClass B.map.toCombinatorialMap d := by
    intro heq
    have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle d e :=
      (Quotient.exact heq).symm
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
      B.map.toCombinatorialMap d e).mp hrel with hedge | hedge
    · have hmem : d ∈ P.darts := by
        rw [← hedge]
        exact he_mem
      change ¬ (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) at hseam
      exact hseam (Or.inl hmem)
    · have hmem : B.map.toCombinatorialMap.edgeInv d ∈ P.darts := by
        rw [← hedge]
        exact he_mem
      change ¬ (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) at hseam
      exact hseam (Or.inr hmem)
  have hneq' : edgeClass B.map.toCombinatorialMap d ≠
      edgeClass B.map.toCombinatorialMap
        (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩) := hneq.symm
  simp only [Pi.single_apply]
  simpa [List.get_eq_getElem] using hneq'

private theorem pathCutLeftBoundaryChain_apply_eq_one
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ pathCutLeftOuterArc B) :
    pathCutPathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) = 1 := by
  apply pathCutPathChain_apply_eq_one_of_mem B.leftPath
  exact (mem_pathCutLeftOuterArc_iff B d).mp hd

private theorem pathCutLeftBoundaryChain_apply_eq_zero_of_both_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : ¬ B.map.IsOuter d)
    (hinv : ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d)) :
    pathCutPathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) = 0 := by
  apply pathCutPathChain_apply_eq_zero_of_not_seam B B.leftPath d
  intro hseam
  change d ∈ B.leftPath.darts ∨
      B.map.toCombinatorialMap.edgeInv d ∈ B.leftPath.darts at hseam
  rcases hseam with hleft | hleft
  · have houter : B.map.IsOuter d :=
      (isOuter_iff_mem_outerArcs B d).2
        (.inl ((mem_pathCutLeftOuterArc_iff B d).mpr hleft))
    exact hd houter
  · have houter : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d) :=
      (isOuter_iff_mem_outerArcs B (B.map.toCombinatorialMap.edgeInv d)).2
        (.inl ((mem_pathCutLeftOuterArc_iff B _).mpr hleft))
    exact hinv houter

private theorem pathCutFaceBoundary_coeff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath) (d : D) :
    S (faceClass B.map.toCombinatorialMap d) +
        S (faceClass B.map.toCombinatorialMap
          (B.map.toCombinatorialMap.edgeInv d)) =
      pathCutPathChain P (edgeClass B.map.toCombinatorialMap d) +
        pathCutPathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) := by
  have h := congrFun hS (edgeClass B.map.toCombinatorialMap d)
  simpa only [faceBoundary_apply, Pi.add_apply] using h

/- the paper result. A zero cut-chain coefficient preserves the normalized face
coefficient across one `rot.symm` step. -/
private theorem pathCutFaceBoundary_rotSymm_eq_of_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath) (d : D)
    (hzero : (pathCutPathChain P + pathCutPathChain B.leftPath)
      (edgeClass B.map.toCombinatorialMap d) = 0) :
    S (faceClass B.map.toCombinatorialMap
      (B.map.toCombinatorialMap.rot.symm d)) =
        S (faceClass B.map.toCombinatorialMap d) := by
  let M := B.map.toCombinatorialMap
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  have hsum : S (faceClass M d) + S (faceClass M (M.edgeInv d)) = 0 := by
    exact hcoeff.trans hzero
  have heq : S (faceClass M d) = S (faceClass M (M.edgeInv d)) :=
    CharTwo.add_eq_zero.mp hsum
  have hclass : faceClass M (M.rot.symm d) = faceClass M (M.edgeInv d) := by
    apply Quotient.sound
    change M.faceSucc.SameCycle (M.rot.symm d) (M.edgeInv d)
    have h : M.faceSucc.SameCycle (M.edgeInv d) (M.faceSucc (M.edgeInv d)) :=
      Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm
  calc
    S (faceClass M (M.rot.symm d)) = S (faceClass M (M.edgeInv d)) :=
      congrArg S hclass
    _ = S (faceClass M d) := heq.symm

/-- The sum of the chosen path chain and the left boundary chain is a planar
toward `lem-lr-ind`, not the paper result. -/
theorem pathCutPathChain_add_leftBoundary_is_faceBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃ S : FaceSpace B.map.toCombinatorialMap,
      faceBoundary B.map.toCombinatorialMap S =
        pathCutPathChain P + pathCutPathChain B.leftPath := by
  classical
  have hcycle := pathCut_cycleBoundary B P
  change vertexBoundary B.map.toCombinatorialMap
      (pathCutPathChain P + pathCutPathChain B.leftPath) = 0 at hcycle
  exact planar_cycle_eq_faceBoundary B.map.toCombinatorialMap B.planar
    (pathCutPathChain P + pathCutPathChain B.leftPath) hcycle

private theorem pathCutPathChain_add_leftBoundary_is_faceBoundary_normalized
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃ S : FaceSpace B.map.toCombinatorialMap,
      faceBoundary B.map.toCombinatorialMap S =
          pathCutPathChain P + pathCutPathChain B.leftPath ∧
        S (faceClass B.map.toCombinatorialMap B.map.outer) = 0 := by
  classical
  obtain ⟨S₀, hS₀⟩ := pathCutPathChain_add_leftBoundary_is_faceBoundary B P
  let outerFace := faceClass B.map.toCombinatorialMap B.map.outer
  let S : FaceSpace B.map.toCombinatorialMap :=
    if S₀ outerFace = 0 then S₀ else S₀ + 1
  have hzeroOrOne := zmodTwo_eq_zero_or_one (S₀ outerFace)
  refine ⟨S, ?_, ?_⟩
  · by_cases hzero : S₀ outerFace = 0
    · simpa [S, hzero] using hS₀
    · have hone : S₀ outerFace = 1 := by
        rcases hzeroOrOne with hz | ho
        · exact (hzero hz).elim
        · exact ho
      simp [S, hzero, map_add, faceBoundary_one, hS₀]
  · by_cases hzero : S₀ outerFace = 0
    · simp [S, outerFace, hzero]
    · have hone : S₀ outerFace = 1 := by
        rcases hzeroOrOne with hz | ho
        · exact (hzero hz).elim
        · exact ho
      simp [S, outerFace, hone]
      exact CharTwo.add_self_eq_zero 1

/- the paper result. The first interior path dart has left-face coefficient one. -/
private theorem pathCut_firstDart_faceCoeff_eq_one
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hn : 0 < n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (hinner : ¬ B.map.IsOuter
      (P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩)) :
    S (faceClass B.map.toCombinatorialMap
      (P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩)) = 1 := by
  classical
  let M := B.map.toCombinatorialMap
  let d := P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩
  change ¬ B.map.IsOuter d at hinner
  have hdMem : d ∈ P.darts := List.get_mem _ _
  have hdSource : dartTailVertex B.map d = B.source := by
    have hstep := P.edge_step ⟨0, by rw [P.darts_length]; exact hn⟩
    calc
      dartTailVertex B.map d = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
        hstep.2.2.1.symm
      _ = B.source := P.start_vertex
  let x := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  let p : Equiv.Perm D := M.rot.symm
  have hxEq : x = B.leftPath.darts.get
      ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩ := by
    simpa [x, SimpleDirectedDartPath.firstDart, List.get_eq_getElem] using
      leftmostOutgoing_source_eq_firstLeftDart B
  have hxMem : x ∈ B.leftPath.darts := by
    rw [hxEq]
    exact List.get_mem _ _
  have hxStep := B.leftPath.edge_step
    ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩
  have hxSource : dartTailVertex B.map x = B.source := by
    rw [hxEq]
    exact hxStep.2.2.1.symm.trans B.leftPath.start_vertex
  have hxTail : B.map.tail x := by rw [hxEq]; exact hxStep.2.1
  have hxLeft : x ∈ pathCutLeftOuterArc B :=
    (mem_pathCutLeftOuterArc_iff B x).2 hxMem
  have hxOuter : B.map.IsOuter x :=
    (isOuter_iff_mem_outerArcs B x).2 (.inl hxLeft)
  have hdx : d ≠ x := by
    intro h
    exact hinner (h.symm ▸ hxOuter)
  have hxFace : faceClass M x = faceClass M B.map.outer := by
    apply Quotient.sound
    change M.faceSucc.SameCycle x B.map.outer
    exact hxOuter.symm
  have hxNotP : x ∉ P.darts := by
    intro h
    have hfirst := simplePath_dart_eq_first_of_tail_source P hn h hxSource
    exact hdx hfirst.symm
  have hxInvNotP : M.edgeInv x ∉ P.darts := by
    have hnotTail := (B.map.tail_iff x (B.noMissingDarts x)).mp hxTail
    intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    have hstep := P.edge_step i
    have hinvTail : B.map.tail (M.edgeInv x) := by
      rw [← hi]
      exact hstep.2.1
    exact hnotTail hinvTail
  have hxSeam : x ∉ pathCutSeamDarts B P := by
    intro h
    change x ∈ P.darts ∨ M.edgeInv x ∈ P.darts at h
    rcases h with h | h
    · exact hxNotP h
    · exact hxInvNotP h
  have hPzeroX := pathCutPathChain_apply_eq_zero_of_not_seam B P x hxSeam
  have hLoneX := pathCutLeftBoundaryChain_apply_eq_one B hxLeft
  have hC_one : (pathCutPathChain P + pathCutPathChain B.leftPath)
      (edgeClass M x) = 1 := by
    change pathCutPathChain P (edgeClass M x) +
      pathCutPathChain B.leftPath (edgeClass M x) = 1
    rw [hPzeroX, hLoneX]
    simp
  have hcoeffX := pathCutFaceBoundary_coeff B P S hS x
  have hsumX : S (faceClass M x) + S (faceClass M (M.edgeInv x)) = 1 :=
    hcoeffX.trans hC_one
  have hinvX : S (faceClass M (M.edgeInv x)) = 1 := by
    rw [hxFace, houterFace] at hsumX
    simpa using hsumX
  have hfaceRotX : faceClass M (M.rot.symm x) = faceClass M (M.edgeInv x) := by
    apply Quotient.sound
    change M.faceSucc.SameCycle (M.rot.symm x) (M.edgeInv x)
    have h : M.faceSucc.SameCycle (M.edgeInv x) (M.faceSucc (M.edgeInv x)) :=
      Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm
  have hbase : S (faceClass M (p x)) = 1 := by
    calc
      S (faceClass M (p x)) = S (faceClass M (M.rot.symm x)) := rfl
      _ = S (faceClass M (M.edgeInv x)) := congrArg S hfaceRotX
      _ = 1 := hinvX
  rcases (pole_rotation_cycle_segments B).1 d hdSource with
    ⟨k, hk, hget, hprefix⟩
  have hQ : ∃ j, p^[j] x = d := by
    refine ⟨k, ?_⟩
    simpa [p, x] using hget
  let m := Nat.find hQ
  have hm : p^[m] x = d := Nat.find_spec hQ
  have hmle : m ≤ k := Nat.find_min' hQ (by simpa [p, x] using hget)
  have hmpos : 0 < m := by
    by_contra hnotpos
    have hm0 : m = 0 := by omega
    have hxd : x = d := by simpa [hm0] using hm
    exact hinner (hxd ▸ hxOuter)
  have hmin (j : ℕ) (hj : j < m) : p^[j] x ≠ d := Nat.find_min hQ hj
  have htailIter (j : ℕ) (hj : j ≤ m) : B.map.tail (p^[j] x) := by
    have hjk : j ≤ k := le_trans hj hmle
    simpa [p, x] using hprefix j hjk
  have hsourceIter : ∀ j : ℕ,
      dartTailVertex B.map (p^[j] x) = B.source := by
    intro j
    induction j with
    | zero => simpa using hxSource
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B B.source ⟨p^[j] x, ih⟩
  have hneqStart (j : ℕ) (hj : 0 < j) (hjm : j < m) :
      p^[j] x ≠ x := by
    intro heq
    have hsplit : m - j + j = m := Nat.sub_add_cancel (Nat.le_of_lt hjm)
    have hperiod : p^[m] x = p^[m - j] x := by
      calc
        p^[m] x = p^[m - j + j] x :=
          congrArg (fun a : ℕ => p^[a] x) hsplit.symm
        _ = p^[m - j] (p^[j] x) := Function.iterate_add_apply p (m - j) j x
        _ = p^[m - j] x := congrArg (fun y : D => p^[m - j] y) heq
    have hsmaller : p^[m - j] x = d := hperiod.symm.trans hm
    exact hmin (m - j) (by omega) hsmaller
  have hseq : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro hlow hup
        by_cases hj0 : j = 0
        · subst j
          simpa [Function.iterate_succ_apply'] using hbase
        · have hjlow : 1 ≤ j := by omega
          have hjup : j ≤ m := by omega
          have hprev := ih hjlow hjup
          have hjlt : j < m := by omega
          let q := p^[j] x
          have hqTail : B.map.tail q := by simpa [q] using htailIter j hjup
          have hqSource : dartTailVertex B.map q = B.source := by
            simpa [q] using hsourceIter j
          have hqNotP : q ∉ P.darts := by
            intro hq
            have hfirst := simplePath_dart_eq_first_of_tail_source P hn hq hqSource
            have hpred : p^[j] x = d := by simpa [q, d] using hfirst
            exact hmin j hjlt hpred
          have hqNotLeft : q ∉ B.leftPath.darts := by
            intro hq
            have hfirst := simplePath_dart_eq_first_of_tail_source B.leftPath
              (Nat.zero_lt_of_lt B.left_length_pos) hq hqSource
            have hqx : q = x := hfirst.trans hxEq.symm
            exact hneqStart j (by omega) hjlt hqx
          have hqNoInvTail := (B.map.tail_iff q (B.noMissingDarts q)).mp hqTail
          have hqInvNotP : M.edgeInv q ∉ P.darts := by
            intro hq
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
            have hstep := P.edge_step i
            have hinvTail : B.map.tail (M.edgeInv q) := by
              rw [← hi]
              exact hstep.2.1
            exact hqNoInvTail hinvTail
          have hqInvNotLeft : M.edgeInv q ∉ B.leftPath.darts := by
            intro hq
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
            have hstep := B.leftPath.edge_step i
            have hinvTail : B.map.tail (M.edgeInv q) := by
              rw [← hi]
              exact hstep.2.1
            exact hqNoInvTail hinvTail
          have hseamP : q ∉ pathCutSeamDarts B P := by
            intro h
            change q ∈ P.darts ∨ M.edgeInv q ∈ P.darts at h
            rcases h with h | h
            · exact hqNotP h
            · exact hqInvNotP h
          have hseamL : q ∉ pathCutSeamDarts B B.leftPath := by
            intro h
            change q ∈ B.leftPath.darts ∨ M.edgeInv q ∈ B.leftPath.darts at h
            rcases h with h | h
            · exact hqNotLeft h
            · exact hqInvNotLeft h
          have hPzero := pathCutPathChain_apply_eq_zero_of_not_seam B P q hseamP
          have hLzero := pathCutPathChain_apply_eq_zero_of_not_seam B B.leftPath q hseamL
          have hCzero : (pathCutPathChain P + pathCutPathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathCutPathChain P (edgeClass M q) +
              pathCutPathChain B.leftPath (edgeClass M q) = 0
            rw [hPzero, hLzero]
            simp
          have htrans := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hCzero
          calc
            S (faceClass M (p^[j + 1] x)) = S (faceClass M (p (p^[j] x))) := by
              rw [show j + 1 = Nat.succ j by omega, Function.iterate_succ_apply']
            _ = S (faceClass M q) := by simpa [q, p] using htrans
            _ = 1 := hprev
  have hfinal := hseq m (by omega) le_rfl
  have hresult : S (faceClass M d) = 1 := by
    simpa [hm] using hfinal
  exact hresult



private theorem simplePath_endpoints_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    dartTailVertex M d ∈ P.vertices ∧ dartHeadVertex M d ∈ P.vertices := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  have hi := P.edge_step i
  constructor
  · rw [← hi.2.2.1]
    exact List.get_mem _ _
  · rw [← hi.2.2.2]
    exact List.get_mem _ _




private theorem rotation_first_visit (p : Equiv.Perm D) (x y : D)
    (hcycle : p.SameCycle x y) :
    ∃ m : ℕ, p^[m] x = y ∧
      (∀ j < m, p^[j] x ≠ y) ∧
      (∀ j, 0 < j → j ≤ m → p^[j] x ≠ x) := by
  obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq'
  have hex : ∃ j : ℕ, p^[j] x = y :=
    ⟨k, by simpa [Equiv.Perm.iterate_eq_pow] using hk⟩
  let m := Nat.find hex
  have hm : p^[m] x = y := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j < m) : p^[j] x ≠ y := Nat.find_min hex hj
  refine ⟨m, hm, hmin, ?_⟩
  intro j hj hjm heq
  have hsplit : m - j + j = m := Nat.sub_add_cancel hjm
  have hperiod : p^[m] x = p^[m - j] x := by
    calc
      p^[m] x = p^[m - j + j] x := by rw [hsplit]
      _ = p^[m - j] (p^[j] x) := Function.iterate_add_apply p (m - j) j x
      _ = p^[m - j] x := by rw [heq]
  exact hmin (m - j) (by omega) (hperiod.symm.trans hm)




private theorem pathCutLeftBoundaryChain_zero_at_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {v : MapVertex B.map} (hv : v ∉ B.leftPath.vertices)
    {q : D} (hq : dartTailVertex B.map q = v) :
    pathCutPathChain B.leftPath (edgeClass B.map.toCombinatorialMap q) = 0 := by
  apply pathCutPathChain_apply_eq_zero_of_not_seam B B.leftPath q
  rintro (h | h)
  · exact hv (hq ▸ (simplePath_endpoints_mem B.leftPath h).1)
  · have hmem := (simplePath_endpoints_mem B.leftPath h).2
    have heq : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv q) = v := by
      simpa [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol] using hq
    exact hv (heq ▸ hmem)




private theorem pathCutPathChain_zero_of_outgoing_ne
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {k : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink k)
    {b q : D} (hb : b ∈ P.darts) (hq : B.map.tail q)
    (hv : dartTailVertex B.map q = dartTailVertex B.map b) (hne : q ≠ b) :
    pathCutPathChain P (edgeClass B.map.toCombinatorialMap q) = 0 := by
  apply pathCutPathChain_apply_eq_zero_of_not_seam B P q
  rintro (h | h)
  · exact hne (simplePath_dart_eq_of_endpoint_eq P h hb (.inl hv))
  · exact ((B.map.tail_iff q (B.noMissingDarts q)).mp hq)
      (simplePath_tail_of_mem P h)



private theorem rotation_iterate_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (x : D) (j : ℕ) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm^[j] x) =
      dartTailVertex B.map x := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact vertexRotationCycle_successor_mem B _ ⟨_, ih⟩




private theorem pathCutFaceCoeff_outgoing_of_not_leftBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∉ B.leftPath.vertices) {b : D} (hb : b ∈ P.darts)
    (hbv : dartTailVertex B.map b = v)
    (hbase : S (faceClass B.map.toCombinatorialMap
      (leftmostOutgoing B v ht)) = 1) :
    S (faceClass B.map.toCombinatorialMap b) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := leftmostOutgoing B v ht
  have hxv := (leftmostOutgoing_internal_characterization B v hs ht).1
  obtain ⟨_, _, _, hout, _⟩ := internal_outgoing_block_segment B v hs ht
  obtain ⟨k, _, hk, hprefix⟩ := hout b hbv (simplePath_tail_of_mem P hb)
  have hcycle : p.SameCycle x b := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hbv.symm)
  obtain ⟨m, hm, hmin, _⟩ := rotation_first_visit p x b hcycle
  have hmk : m ≤ k := by
    by_contra h
    exact hmin k (by omega) hk
  have hseq : ∀ j, j ≤ m → S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro _; exact hbase
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        let q := p^[j] x
        have hqv : dartTailVertex B.map q = v :=
          (rotation_iterate_vertex B x j).trans hxv
        have hqt : B.map.tail q := hprefix j (by omega)
        have hP := pathCutPathChain_zero_of_outgoing_ne B P hb hqt
          (hqv.trans hbv.symm) (hmin j hjm)
        have hL := pathCutLeftBoundaryChain_zero_at_vertex B hv hqv
        have hzero : (pathCutPathChain P + pathCutPathChain B.leftPath)
            (edgeClass M q) = 0 := by
          change pathCutPathChain P _ + pathCutPathChain B.leftPath _ = 0
          rw [hP, hL, zero_add]
        have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
        rw [Function.iterate_succ_apply']
        exact hstep.trans (ih (by omega))
  simpa [hm] using hseq m le_rfl




private theorem pathCutFaceCoeff_leftmostOutgoing_of_incoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∉ B.leftPath.vertices) {a : D} (ha : a ∈ P.darts)
    (hav : dartHeadVertex B.map a = v)
    (haS : S (faceClass B.map.toCombinatorialMap a) = 1) :
    S (faceClass B.map.toCombinatorialMap (leftmostOutgoing B v ht)) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := M.edgeInv a
  let y := leftmostIncoming B v hs
  have hxv : dartTailVertex B.map x = v := hav
  have hxt : ¬ B.map.tail x :=
    (B.map.tail_iff a (B.noMissingDarts a)).mp (simplePath_tail_of_mem P ha)
  have hy := leftmostIncoming_internal_characterization B v hs ht
  have hcycle : p.SameCycle x y := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hy.1.symm)
  obtain ⟨m, hm, hmin, hreturn⟩ := rotation_first_visit p x y hcycle
  have hvertex (j : ℕ) : dartTailVertex B.map (p^[j] x) = v :=
    (rotation_iterate_vertex B x j).trans hxv
  have hincoming : ∀ j, j ≤ m → ¬ B.map.tail (p^[j] x) := by
    intro j
    induction j with
    | zero => intro _; exact hxt
    | succ j ih =>
        intro hj htail
        have hprev := ih (show j ≤ m by omega)
        have hnext : B.map.tail (p (p^[j] x)) := by
          simpa only [Function.iterate_succ_apply'] using htail
        exact hmin j (by omega) (hy.2.2.2 _ (hvertex j) hprev hnext)
  have hbase : S (faceClass M (p x)) = 1 := by
    have hclass : faceClass M (p x) = faceClass M a := by
      apply Quotient.sound
      have h : M.faceSucc.SameCycle (M.faceSucc a) a :=
        (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
      exact h
    exact (congrArg S hclass).trans haS
  have hseq : ∀ j, 1 ≤ j → j ≤ m + 1 →
      S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro hlo hhi
        by_cases hj0 : j = 0
        · subst j
          simpa only [Nat.zero_add, Function.iterate_one] using hbase
        · let q := p^[j] x
          have hjm : j ≤ m := by omega
          have hqv : dartTailVertex B.map q = v := hvertex j
          have hqt : ¬ B.map.tail q := hincoming j hjm
          have hqne : q ≠ x := hreturn j (by omega) hjm
          have hP : pathCutPathChain P (edgeClass M q) = 0 := by
            apply pathCutPathChain_apply_eq_zero_of_not_seam B P q
            rintro (h | h)
            · exact hqt (simplePath_tail_of_mem P h)
            · have hhead : dartHeadVertex B.map (M.edgeInv q) =
                  dartHeadVertex B.map a := by
                change dartTailVertex B.map (M.edgeInv (M.edgeInv q)) =
                  dartHeadVertex B.map a
                rw [M.edgeInv_invol]
                exact hqv.trans hav.symm
              have heq := simplePath_dart_eq_of_endpoint_eq P h ha (.inr hhead)
              apply hqne
              change M.edgeInv q = a at heq
              have heq' := congrArg M.edgeInv heq
              rw [M.edgeInv_invol] at heq'
              exact heq'
          have hL := pathCutLeftBoundaryChain_zero_at_vertex B hv hqv
          have hzero : (pathCutPathChain P + pathCutPathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathCutPathChain P _ + pathCutPathChain B.leftPath _ = 0
            rw [hP, hL, zero_add]
          have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
          rw [Function.iterate_succ_apply']
          exact hstep.trans (ih (by omega) (by omega))
  have hfinal := hseq (m + 1) (by omega) le_rfl
  have hlast : p^[m + 1] x = leftmostOutgoing B v ht := by
    rw [Function.iterate_succ_apply', hm]
    exact leftmostIncoming_rot_symm_eq_leftmostOutgoing B v hs ht
  simpa only [hlast] using hfinal



private theorem simplePath_exists_outgoing_of_mem_vertex
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {v : MapVertex M}
    (hv : v ∈ P.vertices) (ht : v ≠ t) :
    ∃ d ∈ P.darts, dartTailVertex M d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hik : i.val ≤ k := by have := i.isLt; have := P.vertices_length; omega
  have hine : i.val ≠ k := by
    intro heq
    have hifin : i = ⟨k, by rw [P.vertices_length]; omega⟩ := Fin.ext heq
    rw [hifin, P.end_vertex] at hi
    exact ht hi.symm
  let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; omega⟩
  refine ⟨P.darts.get j, List.get_mem _ _, ?_⟩
  exact (P.edge_step j).2.2.1.symm.trans hi



private theorem pathCut_leftBoundary_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  let d := B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩
  have hdOuter : B.map.IsOuter d :=
    ((B.outerSplit.2.2.1 d).mp (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Equiv.Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  have hidx : d = xs[i]'(by rw [hlen]; omega) := by
    dsimp [d, xs]
    rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)]
  have hform := List.formPerm_apply_getElem xs hnodup i (by rw [hlen]; omega)
  have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt (by rw [hlen]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface, hidx, hform]
  simp only [hmod]
  dsimp [xs]
  rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; exact hi)]




private theorem pathCut_leftBoundary_eq_leftmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    {x : D} (hx : x ∈ B.leftPath.darts) (hxv : dartTailVertex B.map x = v) :
    x = leftmostOutgoing B v ht := by
  let M := B.map.toCombinatorialMap
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  have hil : i.val < ℓ := by simpa [B.leftPath.darts_length] using i.isLt
  have hipos : 0 < i.val := by
    by_contra h
    have hi0 : i.val = 0 := by omega
    have hstep := B.leftPath.edge_step i
    have hsource : dartTailVertex B.map x = B.source := by
      rw [← hi, ← hstep.2.2.1]
      simpa only [hi0] using B.leftPath.start_vertex
    exact hs (hxv.symm.trans hsource)
  let j : Fin B.leftPath.darts.length :=
    ⟨i.val - 1, by have := B.leftPath.darts_length; omega⟩
  let a := B.leftPath.darts.get j
  have hax : M.faceSucc a = x := by
    have h := pathCut_leftBoundary_faceSucc_get B (i.val - 1) (by omega)
    have hadd : i.val - 1 + 1 = i.val := by omega
    simpa only [hadd] using h.trans (by simpa only [hadd] using hi)
  have hrot : M.rot x = M.edgeInv a := by
    rw [← hax]
    change M.rot (M.rot.symm (M.edgeInv a)) = M.edgeInv a
    exact M.rot.apply_symm_apply _
  apply (leftmostOutgoing_internal_characterization B v hs ht).2.2.2 x hxv
    (simplePath_tail_of_mem B.leftPath hx)
  rw [hrot]
  exact (B.map.tail_iff a (B.noMissingDarts a)).mp
    (simplePath_tail_of_mem B.leftPath (List.get_mem _ j))




private theorem pathCutFaceCoeff_outgoing_of_leftBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∈ B.leftPath.vertices) {b : D} (hb : b ∈ P.darts)
    (hbv : dartTailVertex B.map b = v) (hbinner : ¬ B.map.IsOuter b) :
    S (faceClass B.map.toCombinatorialMap b) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := leftmostOutgoing B v ht
  obtain ⟨z, hz, hzv⟩ := simplePath_exists_outgoing_of_mem_vertex B.leftPath hv ht
  have hzx : z = x := pathCut_leftBoundary_eq_leftmostOutgoing B hs ht hz hzv
  have hx : x ∈ B.leftPath.darts := hzx ▸ hz
  have hxv : dartTailVertex B.map x = v := hzx ▸ hzv
  have hxt : B.map.tail x := simplePath_tail_of_mem B.leftPath hx
  have hxOuter : B.map.IsOuter x := ((B.outerSplit.2.2.1 x).mp hx).2.2
  have hxb : x ≠ b := by intro h; exact hbinner (h ▸ hxOuter)
  have hPzero := pathCutPathChain_zero_of_outgoing_ne B P hb hxt
    (hxv.trans hbv.symm) hxb
  have hLone := pathCutPathChain_apply_eq_one_of_mem B.leftPath hx
  have hxFace : faceClass M x = faceClass M B.map.outer :=
    Quotient.sound hxOuter.symm
  have hcoeff := pathCutFaceBoundary_coeff B P S hS x
  rw [hPzero, hLone, hxFace, houterFace, zero_add, zero_add] at hcoeff
  have hbase : S (faceClass M (p x)) = 1 := by
    have hclass : faceClass M (p x) = faceClass M (M.edgeInv x) := by
      apply Quotient.sound
      change M.faceSucc.SameCycle (M.rot.symm x) (M.edgeInv x)
      have h : M.faceSucc.SameCycle (M.faceSucc (M.edgeInv x)) (M.edgeInv x) :=
        (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
      simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h
    exact (congrArg S hclass).trans hcoeff
  obtain ⟨_, _, _, hout, _⟩ := internal_outgoing_block_segment B v hs ht
  obtain ⟨k, _, hk, hprefix⟩ := hout b hbv (simplePath_tail_of_mem P hb)
  have hcycle : p.SameCycle x b := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hbv.symm)
  obtain ⟨m, hm, hmin, hreturn⟩ := rotation_first_visit p x b hcycle
  have hmk : m ≤ k := by by_contra h; exact hmin k (by omega) hk
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    exact hxb (by simpa [hm0] using hm)
  have hseq : ∀ j, 1 ≤ j → j ≤ m → S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
        intro hlo hhi
        by_cases hj0 : j = 0
        · subst j
          simpa only [Nat.zero_add, Function.iterate_one] using hbase
        · let q := p^[j] x
          have hqv : dartTailVertex B.map q = v :=
            (rotation_iterate_vertex B x j).trans hxv
          have hqt : B.map.tail q := hprefix j (by omega)
          have hP := pathCutPathChain_zero_of_outgoing_ne B P hb hqt
            (hqv.trans hbv.symm) (hmin j (by omega))
          have hL := pathCutPathChain_zero_of_outgoing_ne B B.leftPath hx hqt
            (hqv.trans hxv.symm) (hreturn j (by omega) (by omega))
          have hzero : (pathCutPathChain P + pathCutPathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathCutPathChain P _ + pathCutPathChain B.leftPath _ = 0
            rw [hP, hL, zero_add]
          have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
          rw [Function.iterate_succ_apply']
          exact hstep.trans (ih (by omega) (by omega))
  simpa [hm] using hseq m hmpos le_rfl




private theorem pathCut_pathDart_faceCoeff_eq_one
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {d : D} (hd : d ∈ P.darts) (hinner : ¬ B.map.IsOuter d) :
    S (faceClass B.map.toCombinatorialMap d) = 1 := by
  have hAll : ∀ (i : ℕ) (hi : i < n),
      ¬ B.map.IsOuter (P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩) →
      S (faceClass B.map.toCombinatorialMap
        (P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩)) = 1 := by
    intro i
    induction i with
    | zero =>
        intro hi hin
        exact pathCut_firstDart_faceCoeff_eq_one B P hi S hS houterFace hin
    | succ j ih =>
        intro hi hin
        let ai : Fin P.darts.length := ⟨j, by rw [P.darts_length]; omega⟩
        let bi : Fin P.darts.length := ⟨j + 1, by rw [P.darts_length]; exact hi⟩
        let a := P.darts.get ai
        let b := P.darts.get bi
        let v := dartTailVertex B.map b
        have ha : a ∈ P.darts := List.get_mem _ _
        have hb : b ∈ P.darts := List.get_mem _ _
        have hbstep := P.edge_step bi
        have hastep := P.edge_step ai
        have hav : dartHeadVertex B.map a = v :=
          hastep.2.2.2.symm.trans hbstep.2.2.1
        have hs : v ≠ B.source := by
          intro heq
          have hget :
              P.vertices.get ⟨j + 1, by rw [P.vertices_length]; omega⟩ =
                P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
            hbstep.2.2.1.trans (heq.trans P.start_vertex.symm)
          have hidx := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp hget)
          dsimp at hidx
          omega
        have ht : v ≠ B.sink := by
          intro heq
          apply B.isSink
          exact ⟨dartHeadVertex B.map b, b, B.noMissingDarts b,
            hbstep.2.1, heq, rfl⟩
        by_cases hv : v ∈ B.leftPath.vertices
        · exact pathCutFaceCoeff_outgoing_of_leftBoundary B P S hS houterFace
            hs ht hv hb rfl hin
        · have hainner : ¬ B.map.IsOuter a := by
            intro hao
            rcases (isOuter_iff_mem_outerArcs B a).mp hao with hal | har
            · have hamem := (mem_pathCutLeftOuterArc_iff B a).mp hal
              exact hv (hav ▸ (simplePath_endpoints_mem B.leftPath hamem).2)
            · have harnot : ¬ B.map.tail a := har.2.1
              exact harnot hastep.2.1
          have haS : S (faceClass B.map.toCombinatorialMap a) = 1 :=
            ih (by omega) hainner
          have hbase := pathCutFaceCoeff_leftmostOutgoing_of_incoming
            B P S hS hs ht hv ha hav haS
          exact pathCutFaceCoeff_outgoing_of_not_leftBoundary
            B P S hS hs ht hv hb rfl hbase
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hin : i.val < n := by simpa only [P.darts_length] using i.isLt
  have h := hAll i.val hin (by simpa only [hi] using hinner)
  simpa only [hi] using h




private theorem pathCut_pathDart_reverseFaceCoeff_eq_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {d : D} (hd : d ∈ P.darts) :
    S (faceClass B.map.toCombinatorialMap
      (B.map.toCombinatorialMap.edgeInv d)) = 0 := by
  let M := B.map.toCombinatorialMap
  have htail := simplePath_tail_of_mem P hd
  have hP := pathCutPathChain_apply_eq_one_of_mem P hd
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  by_cases hout : B.map.IsOuter d
  · have hleft : d ∈ pathCutLeftOuterArc B := by
      rcases (isOuter_iff_mem_outerArcs B d).mp hout with h | h
      · exact h
      · exact (h.2.1 htail).elim
    have hL := pathCutLeftBoundaryChain_apply_eq_one B hleft
    have hclass : faceClass M d = faceClass M B.map.outer := Quotient.sound hout.symm
    rw [hP, hL, hclass, houterFace, zero_add, CharTwo.add_self_eq_zero] at hcoeff
    exact hcoeff
  · have hL : pathCutPathChain B.leftPath (edgeClass M d) = 0 := by
      apply pathCutPathChain_apply_eq_zero_of_not_seam B B.leftPath d
      rintro (h | h)
      · exact hout (((B.outerSplit.2.2.1 d).mp h).2.2)
      · exact ((B.map.tail_iff d (B.noMissingDarts d)).mp htail)
          (simplePath_tail_of_mem B.leftPath h)
    have hleft := pathCut_pathDart_faceCoeff_eq_one B P S hS houterFace hd hout
    rw [hP, hL, hleft, add_zero] at hcoeff
    exact add_left_cancel (hcoeff.trans (add_zero 1).symm)

private noncomputable def pathCutSideFromFace
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : FaceSpace B.map.toCombinatorialMap) (d : D) : Bool := by
  classical
  exact if d ∈ pathCutLeftOuterArc B then true
    else if d ∈ pathCutRightOuterArc B then false
    else decide (S (faceClass B.map.toCombinatorialMap d) = 1)

private theorem pathCutSideFromFace_faceSucc_of_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : FaceSpace B.map.toCombinatorialMap) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.faceSucc d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let f := M.faceSucc
  have hnextInner : ¬ B.map.IsOuter (f d) := by
    intro hnext
    have houter : f.SameCycle B.map.outer d := by
      change f.SameCycle B.map.outer (f d) at hnext
      exact Equiv.Perm.sameCycle_apply_right.mp hnext
    exact hinner houter
  have hdLeft : d ∉ pathCutLeftOuterArc B := by
    intro hd
    exact hinner ((isOuter_iff_mem_outerArcs B d).2 (Or.inl hd))
  have hdRight : d ∉ pathCutRightOuterArc B := by
    intro hd
    exact hinner ((isOuter_iff_mem_outerArcs B d).2 (Or.inr hd))
  have hnextLeft : f d ∉ pathCutLeftOuterArc B := by
    intro hd
    exact hnextInner ((isOuter_iff_mem_outerArcs B (f d)).2 (Or.inl hd))
  have hnextRight : f d ∉ pathCutRightOuterArc B := by
    intro hd
    exact hnextInner ((isOuter_iff_mem_outerArcs B (f d)).2 (Or.inr hd))
  have hface : faceClass M (f d) = faceClass M d := by
    apply Quotient.sound
    exact (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
  have hnextLeft' : B.map.toCombinatorialMap.faceSucc d ∉
      pathCutLeftOuterArc B := by simpa [f, M] using hnextLeft
  have hnextRight' : B.map.toCombinatorialMap.faceSucc d ∉
      pathCutRightOuterArc B := by simpa [f, M] using hnextRight
  unfold pathCutSideFromFace
  rw [ite_eq_right hnextLeft', ite_eq_right hnextRight',
    ite_eq_right hdLeft, ite_eq_right hdRight]
  rw [hface]

private theorem pathCutSideFromFace_edgeInv_of_outer
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (d : D) (hseam : d ∉ pathCutSeamDarts B P)
    (houter : B.map.IsOuter d) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.edgeInv d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let e := M.edgeInv d
  have hseamE : e ∉ pathCutSeamDarts B P := by
    intro h
    have h' : d ∈ pathCutSeamDarts B P := by
      have hiff := pathCutSeamDarts_edgeInv_iff B P e
      simpa [e, M, M.edgeInv_invol] using hiff.mpr h
    exact hseam h'
  have hPzero := pathCutPathChain_apply_eq_zero_of_not_seam B P d hseam
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  have hsum : S (faceClass M d) + S (faceClass M e) =
      pathCutPathChain B.leftPath (edgeClass M d) := by
    simpa [hPzero, e] using hcoeff
  have hfaceD : faceClass M d = faceClass M B.map.outer := by
    apply Quotient.sound
    change M.faceSucc.SameCycle B.map.outer d at houter
    exact houter.symm
  rcases (isOuter_iff_mem_outerArcs B d).mp houter with hdLeft | hdRight
  · have hdLeftData : ¬ B.map.missing d ∧ B.map.tail d ∧ B.map.IsOuter d := hdLeft
    have hnotTailE : ¬ B.map.tail e :=
      (B.map.tail_iff d (B.noMissingDarts d)).mp hdLeftData.2.1
    by_cases heOuter : B.map.IsOuter e
    · have heArc := (isOuter_iff_mem_outerArcs B e).mp heOuter
      have heRight : e ∈ pathCutRightOuterArc B := by
        rcases heArc with heLeft | heRight
        · have heLeftData : ¬ B.map.missing e ∧ B.map.tail e ∧ B.map.IsOuter e := heLeft
          exact (hnotTailE heLeftData.2.1).elim
        · exact heRight
      have hleftOne := pathCutLeftBoundaryChain_apply_eq_one B hdLeft
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : faceClass M e = faceClass M B.map.outer := by
        apply Quotient.sound
        change M.faceSucc.SameCycle B.map.outer e at heOuter
        exact heOuter.symm
      rw [hfaceE, houterFace] at hsum
      simp at hsum
    · have hleftOne := pathCutLeftBoundaryChain_apply_eq_one B hdLeft
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : S (faceClass M e) = 1 := by simpa [e, M] using hsum
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, heLeft, heRight, hdLeft, hfaceE, e, M]
  · have hdRightData : ¬ B.map.missing d ∧ ¬ B.map.tail d ∧ B.map.IsOuter d := hdRight
    have htailE : B.map.tail e := by
      by_contra hnot
      have htailD : B.map.tail d := (B.map.tail_iff d (B.noMissingDarts d)).mpr hnot
      exact hdRightData.2.1 htailD
    by_cases heOuter : B.map.IsOuter e
    · have heArc := (isOuter_iff_mem_outerArcs B e).mp heOuter
      have heLeft : e ∈ pathCutLeftOuterArc B := by
        rcases heArc with heLeft | heRight
        · exact heLeft
        · have heRightData :
              ¬ B.map.missing e ∧ ¬ B.map.tail e ∧ B.map.IsOuter e := heRight
          exact (heRightData.2.1 htailE).elim
      have hleftOneE := pathCutLeftBoundaryChain_apply_eq_one B heLeft
      have hleftOne :
          pathCutPathChain B.leftPath (edgeClass M d) = 1 := by
        have hclass : edgeClass M e = edgeClass M d := by
          apply Quotient.sound
          exact (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
        rw [← hclass]
        exact hleftOneE
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : faceClass M e = faceClass M B.map.outer := by
        apply Quotient.sound
        change M.faceSucc.SameCycle B.map.outer e at heOuter
        exact heOuter.symm
      rw [hfaceE, houterFace] at hsum
      simp at hsum
    · have hnotLeft : d ∉ pathCutLeftOuterArc B := by
        intro hleft
        exact (Set.disjoint_left.mp (pathCut_outerArcs_disjoint B)) hleft hdRight
      have hnotLeftSeam : d ∉ pathCutSeamDarts B B.leftPath := by
        intro h
        change d ∈ B.leftPath.darts ∨ M.edgeInv d ∈ B.leftPath.darts at h
        rcases h with h | h
        · exact hnotLeft ((mem_pathCutLeftOuterArc_iff B d).mpr h)
        · have heOuter' : B.map.IsOuter e :=
            (isOuter_iff_mem_outerArcs B e).2
              (.inl ((mem_pathCutLeftOuterArc_iff B e).mpr h))
          exact heOuter heOuter'
      have hleftZero :=
        pathCutPathChain_apply_eq_zero_of_not_seam B B.leftPath d hnotLeftSeam
      rw [hleftZero] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : S (faceClass M e) = 0 := by simpa [e, M] using hsum
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, hnotLeft, hdRight, heLeft, heRight,
        hfaceE, e, M]

private theorem pathCutSideFromFace_edgeInv_of_not_seam
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathCutPathChain P + pathCutPathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (d : D) (hseam : d ∉ pathCutSeamDarts B P) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.edgeInv d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let e := M.edgeInv d
  have hseamE : e ∉ pathCutSeamDarts B P := by
    intro h
    have h' : d ∈ pathCutSeamDarts B P := by
      have hiff := pathCutSeamDarts_edgeInv_iff B P e
      simpa [e, M, M.edgeInv_invol] using hiff.mpr h
    exact hseam h'
  by_cases hdOuter : B.map.IsOuter d
  · exact pathCutSideFromFace_edgeInv_of_outer B P S hS houterFace d hseam hdOuter
  · by_cases heOuter : B.map.IsOuter e
    · have h := pathCutSideFromFace_edgeInv_of_outer B P S hS houterFace e hseamE heOuter
      simpa [e, M, M.edgeInv_invol] using h.symm
    · have hPzero := pathCutPathChain_apply_eq_zero_of_not_seam B P d hseam
      have hleftZero :=
        pathCutLeftBoundaryChain_apply_eq_zero_of_both_inner B hdOuter heOuter
      have hcoeff := pathCutFaceBoundary_coeff B P S hS d
      have hsum :
          S (faceClass M d) + S (faceClass M e) = 0 := by
        rw [hPzero, hleftZero] at hcoeff
        simpa using hcoeff
      have hfaceEq : S (faceClass M d) = S (faceClass M e) :=
        CharTwo.add_eq_zero.mp hsum
      have hdLeft : d ∉ pathCutLeftOuterArc B := by
        intro hd
        exact hdOuter ((isOuter_iff_mem_outerArcs B d).2 (.inl hd))
      have hdRight : d ∉ pathCutRightOuterArc B := by
        intro hd
        exact hdOuter ((isOuter_iff_mem_outerArcs B d).2 (.inr hd))
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, hdLeft, hdRight, heLeft, heRight,
        hfaceEq, e, M]




theorem pathCut_exists_side_coloring
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃ side : D → Bool,
      (∀ d, d ∈ pathCutLeftSeeds B P → side d = true) ∧
      (∀ d, d ∈ pathCutRightSeeds B P → side d = false) ∧
      (∀ d, ¬ B.map.IsOuter d →
        side (B.map.toCombinatorialMap.faceSucc d) = side d) ∧
      (∀ d, d ∉ pathCutSeamDarts B P →
        side (B.map.toCombinatorialMap.edgeInv d) = side d) := by
  classical
  obtain ⟨S, hS, houter⟩ :=
    pathCutPathChain_add_leftBoundary_is_faceBoundary_normalized B P
  refine ⟨pathCutSideFromFace B S, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rcases hd with hleft | hpath
    · simp only [pathCutSideFromFace, ite_eq_left hleft]
    · by_cases hdOuter : B.map.IsOuter d
      · have hdLeft : d ∈ pathCutLeftOuterArc B := by
          rcases (isOuter_iff_mem_outerArcs B d).mp hdOuter with hl | hr
          · exact hl
          · exact (hr.2.1 (simplePath_tail_of_mem P hpath)).elim
        simp only [pathCutSideFromFace, ite_eq_left hdLeft]
      · have hdLeft : d ∉ pathCutLeftOuterArc B :=
          fun h => hdOuter ((isOuter_iff_mem_outerArcs B d).mpr (.inl h))
        have hdRight : d ∉ pathCutRightOuterArc B :=
          fun h => hdOuter ((isOuter_iff_mem_outerArcs B d).mpr (.inr h))
        have hface := pathCut_pathDart_faceCoeff_eq_one B P S hS houter hpath hdOuter
        simp only [pathCutSideFromFace, ite_eq_right hdLeft, ite_eq_right hdRight,
          hface, decide_true]
  · intro d hd
    rcases hd with hright | ⟨p, hp, rfl⟩
    · have hnotLeft : d ∉ pathCutLeftOuterArc B :=
        fun h => Set.disjoint_left.mp (pathCut_outerArcs_disjoint B) h hright
      simp only [pathCutSideFromFace, ite_eq_right hnotLeft, ite_eq_left hright]
    · have hnotLeft : B.map.toCombinatorialMap.edgeInv p ∉
          pathCutLeftOuterArc B := by
        intro h
        exact ((B.map.tail_iff p (B.noMissingDarts p)).mp
          (simplePath_tail_of_mem P hp)) h.2.1
      have hface := pathCut_pathDart_reverseFaceCoeff_eq_zero B P S hS houter hp
      by_cases hright : B.map.toCombinatorialMap.edgeInv p ∈ pathCutRightOuterArc B
      · simp only [pathCutSideFromFace, ite_eq_right hnotLeft, ite_eq_left hright]
      · simp only [pathCutSideFromFace, ite_eq_right hnotLeft, ite_eq_right hright, hface,
          zero_ne_one, decide_false]
  · exact pathCutSideFromFace_faceSucc_of_inner B S
  · exact pathCutSideFromFace_edgeInv_of_not_seam B P S hS houter





theorem pathCut_offSeam_disjoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Disjoint
      (pathCutLeftDarts B P \ pathCutSeamDarts B P)
      (pathCutRightDarts B P \ pathCutSeamDarts B P) := by
  obtain ⟨side, hleft, hright, hface, hedge⟩ := pathCut_exists_side_coloring B P
  have hleftClosure (d : D) (hd : d ∈ pathCutLeftDarts B P) : side d = true := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hleft a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hface b hinner).trans ih
        · exact hleft _ (.inl hnext)
        · exact (hedge b hseam).trans ih
  have hrightClosure (d : D) (hd : d ∈ pathCutRightDarts B P) : side d = false := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hright a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hface b hinner).trans ih
        · exact hright _ (.inl hnext)
        · exact (hedge b hseam).trans ih
  apply Set.disjoint_left.mpr
  intro d hdLeft hdRight
  have hl := hleftClosure d hdLeft.1
  have hr := hrightClosure d hdRight.1
  rw [hl] at hr
  cases hr

end DirectedDistances.PlanarMap
