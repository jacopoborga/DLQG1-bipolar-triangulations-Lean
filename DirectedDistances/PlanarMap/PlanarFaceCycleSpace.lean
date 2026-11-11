/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.Basic

/-! # Face boundaries and the cycle space

Planar helper toward `lem-lr-ind`; this file is not the paper result. The -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Edge coefficient functions over `ZMod 2` on the edge orbits of a map. -/
abbrev EdgeSpace (M : CombinatorialMap D) :=
  CombinatorialMap.EdgeQuotient M → ZMod 2

/-- Vertex coefficient functions over `ZMod 2` on the vertex orbits of a map. -/
abbrev VertexSpace (M : CombinatorialMap D) :=
  CombinatorialMap.VertexQuotient M → ZMod 2

/-- Face coefficient functions over `ZMod 2` on the face orbits of a map. -/
abbrev FaceSpace (M : CombinatorialMap D) :=
  CombinatorialMap.FaceQuotient M → ZMod 2

/-- A dart's edge orbit in the map. -/
@[expose] def edgeClass (M : CombinatorialMap D) (d : D) :
    CombinatorialMap.EdgeQuotient M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d

/-- A dart's vertex orbit in the map. -/
@[expose] def vertexClass (M : CombinatorialMap D) (d : D) :
    CombinatorialMap.VertexQuotient M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) d

/-- A dart's face orbit in the map. -/
@[expose] def faceClass (M : CombinatorialMap D) (d : D) :
    CombinatorialMap.FaceQuotient M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.faceSucc) d

/-- The mod-two vertex incidence boundary, counting both dart incidences of
each loop. -/
@[expose] noncomputable def vertexBoundary (M : CombinatorialMap D) :
    EdgeSpace M →ₗ[ZMod 2] VertexSpace M := by
  classical
  refine {
    toFun := fun c v => ∑ d : D,
      if vertexClass M d = v then c (edgeClass M d) else 0
    map_add' := ?_
    map_smul' := ?_ }
  · intro c c'
    ext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : vertexClass M d = v <;> simp [h]
  · intro a c
    ext v
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : vertexClass M d = v <;> simp [h]

/-- The face boundary map: each edge receives the sum of the coefficients of
its two incident face sides, so a face incident to both sides contributes
twice and hence zero over `ZMod 2`. -/
@[expose] noncomputable def faceBoundary (M : CombinatorialMap D) :
    FaceSpace M →ₗ[ZMod 2] EdgeSpace M := by
  classical
  refine {
    toFun := fun S e => Quotient.lift
      (fun d : D => S (faceClass M d) + S (faceClass M (M.edgeInv d)))
      (by
        intro d e h
        rcases (CombinatorialMap.edgeInv_sameCycle_iff M d e).mp h with hde | hde
        · subst e
          rfl
        · subst e
          simp [M.edgeInv_invol, add_comm])
      e
    map_add' := ?_
    map_smul' := ?_ }
  · intro S T
    funext e
    refine Quotient.inductionOn e ?_
    intro d
    dsimp
    abel
  · intro a S
    funext e
    refine Quotient.inductionOn e ?_
    intro d
    dsimp
    ring

/-- Evaluating a face boundary on an edge adds the coefficients of the two
incident face sides; the same face on both sides therefore contributes zero. -/
@[simp] theorem faceBoundary_apply (M : CombinatorialMap D)
    (S : FaceSpace M) (d : D) :
    faceBoundary M S (edgeClass M d) =
      S (faceClass M d) + S (faceClass M (M.edgeInv d)) := by
  simp [faceBoundary, edgeClass]

/-- The cycle space is the kernel of the mod-two vertex incidence boundary. -/
@[expose] noncomputable def cycleSpace (M : CombinatorialMap D) :
    Submodule (ZMod 2) (EdgeSpace M) :=
  LinearMap.ker (vertexBoundary M)

/-- Each face boundary has even incidence at every vertex, by cancellation of
the two sides at each corner. -/
theorem vertexBoundary_faceBoundary (M : CombinatorialMap D)
    (S : FaceSpace M) :
    vertexBoundary M (faceBoundary M S) = 0 := by
  classical
  ext v
  change (∑ d : D,
      if vertexClass M d = v then
        S (faceClass M d) + S (faceClass M (M.edgeInv d)) else 0) = 0
  let first : D → ZMod 2 := fun d =>
    if vertexClass M d = v then S (faceClass M d) else 0
  let second : D → ZMod 2 := fun d =>
    if vertexClass M d = v then S (faceClass M (M.edgeInv d)) else 0
  have hsplit :
      (∑ d : D, if vertexClass M d = v then
          S (faceClass M d) + S (faceClass M (M.edgeInv d)) else 0) =
        (∑ d : D, first d) + (∑ d : D, second d) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : vertexClass M d = v <;> simp [first, second, h]
  have hvertex (d : D) :
      vertexClass M (M.rot.symm d) = vertexClass M d := by
    apply Quotient.sound
    change M.rot.SameCycle (M.rot.symm d) d
    exact (Equiv.Perm.sameCycle_symm_apply_left).2 Equiv.Perm.SameCycle.rfl
  have hface (d : D) :
      faceClass M (M.rot.symm d) = faceClass M (M.edgeInv d) := by
    apply Quotient.sound
    change M.faceSucc.SameCycle (M.rot.symm d) (M.edgeInv d)
    have h : M.faceSucc.SameCycle (M.edgeInv d) (M.faceSucc (M.edgeInv d)) :=
      Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm
  have hsum : (∑ d : D, first d) = ∑ d : D, second d := by
    calc
      (∑ d : D, first d) = ∑ d : D, first (M.rot.symm d) :=
        (Equiv.sum_comp M.rot.symm first).symm
      _ = ∑ d : D, second d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [first, second, hvertex, hface]
  rw [hsplit, hsum]
  exact CharTwo.add_self_eq_zero _

/-- The image of the face boundary map lies in the cycle space. -/
theorem faceBoundary_range_le_cycleSpace (M : CombinatorialMap D) :
    LinearMap.range (faceBoundary M) ≤ cycleSpace M := by
  intro c hc
  rcases hc with ⟨S, rfl⟩
  exact LinearMap.mem_ker.mpr (vertexBoundary_faceBoundary M S)

/-- The all-ones face function has zero boundary over `ZMod 2`. -/
theorem faceBoundary_one (M : CombinatorialMap D) :
    faceBoundary M (1 : FaceSpace M) = 0 := by
  classical
  ext e
  refine Quotient.inductionOn e ?_
  intro d
  change faceBoundary M (1 : FaceSpace M) (edgeClass M d) = 0
  rw [faceBoundary_apply]
  exact CharTwo.add_self_eq_zero 1

/-- For a connected map, a face coefficient function has zero boundary exactly
when it is constant, with the two possible values in `ZMod 2`. -/
theorem faceBoundary_eq_zero_iff_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) (S : FaceSpace M) :
    faceBoundary M S = 0 ↔ S = 0 ∨ S = 1 := by
  classical
  constructor
  · intro hδ
    let f : D → ZMod 2 := fun d => S (faceClass M d)
    have hflip (d : D) : f d = f (M.edgeInv d) := by
      have hsum : f d + f (M.edgeInv d) = 0 := by
        simpa [f] using congrFun hδ (edgeClass M d)
      calc
        f d = f d + (f (M.edgeInv d) + f (M.edgeInv d)) := by
          rw [CharTwo.add_self_eq_zero]
          simp
        _ = (f d + f (M.edgeInv d)) + f (M.edgeInv d) := by abel
        _ = 0 + f (M.edgeInv d) := by rw [hsum]
        _ = f (M.edgeInv d) := by simp
    have hfaceClass (d : D) :
        faceClass M d = faceClass M (M.faceSucc d) := by
      apply Quotient.sound
      exact Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    have hface (d : D) : f d = f (M.faceSucc d) := by
      dsimp [f]
      rw [hfaceClass]
    have hrotSymm (d : D) : f d = f (M.rot.symm d) := by
      calc
        f d = f (M.edgeInv d) := hflip d
        _ = f (M.faceSucc (M.edgeInv d)) := hface (M.edgeInv d)
        _ = f (M.rot.symm d) := by
          simp [CombinatorialMap.faceSucc, M.edgeInv_invol]
    have hrot (d : D) : f d = f (M.rot d) := by
      simpa using (hrotSymm (M.rot d)).symm
    have hinv (d : D) : M.edgeInv.symm d = M.edgeInv d := by
      apply M.edgeInv.injective
      simp [M.edgeInv_invol]
    have hstep (x y : D)
        (hy : y = M.rot x ∨ y = M.rot.symm x ∨
          y = M.edgeInv x ∨ y = M.edgeInv.symm x) : f x = f y := by
      rcases hy with hy | hy | hy | hy
      · rw [hy]
        exact hrot x
      · rw [hy]
        exact hrotSymm x
      · rw [hy]
        exact hflip x
      · rw [hy, hinv]
        exact hflip x
    have hpath : ∀ {x y : D},
        Relation.ReflTransGen
          (fun x y : D => y = M.rot x ∨ y = M.rot.symm x ∨
            y = M.edgeInv x ∨ y = M.edgeInv.symm x) x y → f x = f y := by
      intro x y hxy
      induction hxy with
      | refl => rfl
      | tail hprev hlast ih => exact ih.trans (hstep _ _ hlast)
    by_cases hD : Nonempty D
    · let d₀ : D := Classical.choice hD
      have hconst (d : D) : f d = f d₀ := hpath (hM d d₀)
      have hSconst : S = fun _ => f d₀ := by
        funext q
        refine Quotient.inductionOn q ?_
        intro d
        exact hconst d
      have hvalue : f d₀ = 0 ∨ f d₀ = 1 := by
        have hv := ZMod.val_lt (f d₀)
        have hv' : (f d₀).val = 0 ∨ (f d₀).val = 1 := by omega
        rcases hv' with hz | ho
        · left
          apply ZMod.val_injective 2
          simp [hz]
        · right
          apply ZMod.val_injective 2
          rw [ho, ZMod.val_one_eq_one_mod]
      rcases hvalue with hzero | hone
      · left
        rw [hSconst, hzero]
        rfl
      · right
        rw [hSconst, hone]
        rfl
    · left
      ext q
      refine Quotient.inductionOn q ?_
      intro d
      exact (hD ⟨d⟩).elim
  · intro h
    rcases h with h | h
    · rw [h]
      simp
    · rw [h]
      exact faceBoundary_one M

/-- On a connected map, two face functions have the same boundary exactly
when they agree everywhere or differ by the all-ones function. -/
theorem faceBoundary_eq_iff (M : CombinatorialMap D)
    (hM : M.IsConnected) (S S' : FaceSpace M) :
    faceBoundary M S = faceBoundary M S' ↔
      S = S' ∨ S = S' + (1 : FaceSpace M) := by
  constructor
  · intro h
    have hzero : faceBoundary M (S + S') = 0 := by
      rw [map_add, h]
      ext e
      exact CharTwo.add_self_eq_zero _
    have hker := (faceBoundary_eq_zero_iff_connected M hM (S + S')).mp hzero
    rcases hker with hker | hker
    · left
      ext q
      exact CharTwo.add_eq_zero.mp (congrFun hker q)
    · right
      ext q
      have hq := congrFun hker q
      change S q + S' q = 1 at hq
      change S q = S' q + 1
      simpa [add_comm] using (CharTwo.add_eq_iff_eq_add.mp hq)
  · rintro (h | h)
    · rw [h]
    · rw [h, map_add, faceBoundary_one, add_zero]

/-- Coboundary on vertices: the coefficient of an edge is the sum of the
values at its two darts' vertex classes. This is a helper toward
`lem-lr-ind` (planar cut separation), not the paper result; see -/
@[expose] noncomputable def coboundary (M : CombinatorialMap D) :
    VertexSpace M →ₗ[ZMod 2] EdgeSpace M := by
  classical
  refine {
    toFun := fun f e => Quotient.lift
      (fun d : D => f (vertexClass M d) + f (vertexClass M (M.edgeInv d)))
      (by
        intro d e h
        rcases (CombinatorialMap.edgeInv_sameCycle_iff M d e).mp h with hde | hde
        · subst e
          rfl
        · subst e
          simp [M.edgeInv_invol, add_comm])
      e
    map_add' := ?_
    map_smul' := ?_ }
  · intro f g
    funext e
    refine Quotient.inductionOn e ?_
    intro d
    dsimp
    abel
  · intro a f
    funext e
    refine Quotient.inductionOn e ?_
    intro d
    dsimp
    ring

/-- The coboundary coefficient at an edge is the sum of its endpoint values;
loops contribute twice and hence zero. Helper toward `lem-lr-ind` (planar cut -/
@[simp] theorem coboundary_apply (M : CombinatorialMap D)
    (f : VertexSpace M) (d : D) :
    coboundary M f (edgeClass M d) =
      f (vertexClass M d) + f (vertexClass M (M.edgeInv d)) := by
  simp [coboundary, edgeClass]

/-- On a connected map, the coboundary kernel consists exactly of the two
constant vertex functions. Helper toward `lem-lr-ind` (planar cut separation), -/
theorem coboundary_eq_zero_iff_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) (f : VertexSpace M) :
    coboundary M f = 0 ↔ f = 0 ∨ f = 1 := by
  classical
  constructor
  · intro hδ
    let g : D → ZMod 2 := fun d => f (vertexClass M d)
    have hedge (d : D) : g d = g (M.edgeInv d) := by
      have hsum : g d + g (M.edgeInv d) = 0 := by
        simpa [g] using congrFun hδ (edgeClass M d)
      calc
        g d = g d + (g (M.edgeInv d) + g (M.edgeInv d)) := by
          rw [CharTwo.add_self_eq_zero]
          simp
        _ = (g d + g (M.edgeInv d)) + g (M.edgeInv d) := by abel
        _ = 0 + g (M.edgeInv d) := by rw [hsum]
        _ = g (M.edgeInv d) := by simp
    have hrotClass (d : D) :
        vertexClass M d = vertexClass M (M.rot d) := by
      apply Quotient.sound
      exact Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    have hrot (d : D) : g d = g (M.rot d) := by
      dsimp [g]
      rw [hrotClass]
    have hrotSymm (d : D) : g d = g (M.rot.symm d) := by
      simpa using (hrot (M.rot.symm d)).symm
    have hinv (d : D) : M.edgeInv.symm d = M.edgeInv d := by
      apply M.edgeInv.injective
      simp [M.edgeInv_invol]
    have hstep (x y : D)
        (hy : y = M.rot x ∨ y = M.rot.symm x ∨
          y = M.edgeInv x ∨ y = M.edgeInv.symm x) : g x = g y := by
      rcases hy with hy | hy | hy | hy
      · rw [hy]
        exact hrot x
      · rw [hy]
        exact hrotSymm x
      · rw [hy]
        exact hedge x
      · rw [hy, hinv]
        exact hedge x
    have hpath : ∀ {x y : D},
        Relation.ReflTransGen
          (fun x y : D => y = M.rot x ∨ y = M.rot.symm x ∨
            y = M.edgeInv x ∨ y = M.edgeInv.symm x) x y → g x = g y := by
      intro x y hxy
      induction hxy with
      | refl => rfl
      | tail hprev hlast ih => exact ih.trans (hstep _ _ hlast)
    by_cases hD : Nonempty D
    · let d₀ : D := Classical.choice hD
      have hconst (d : D) : g d = g d₀ := hpath (hM d d₀)
      have hfconst : f = fun _ => g d₀ := by
        funext q
        refine Quotient.inductionOn q ?_
        intro d
        exact hconst d
      have hvalue : g d₀ = 0 ∨ g d₀ = 1 := by
        have hv := ZMod.val_lt (g d₀)
        have hv' : (g d₀).val = 0 ∨ (g d₀).val = 1 := by omega
        rcases hv' with hz | ho
        · left
          apply ZMod.val_injective 2
          simp [hz]
        · right
          apply ZMod.val_injective 2
          rw [ho, ZMod.val_one_eq_one_mod]
      rcases hvalue with hzero | hone
      · left
        rw [hfconst, hzero]
        rfl
      · right
        rw [hfconst, hone]
        rfl
    · left
      ext q
      refine Quotient.inductionOn q ?_
      intro d
      exact (hD ⟨d⟩).elim
  · intro h
    rcases h with h | h
    · rw [h]
      simp
    · rw [h]
      ext e
      refine Quotient.inductionOn e ?_
      intro d
      change coboundary M (1 : VertexSpace M) (edgeClass M d) = 0
      rw [coboundary_apply]
      exact CharTwo.add_self_eq_zero 1

private theorem sum_edgeOrbit (M : CombinatorialMap D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] (d : D)
    (g : D → ZMod 2) :
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

private noncomputable def incidenceMatrix (M : CombinatorialMap D)
    [Fintype (CombinatorialMap.VertexQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)]
    [Fintype (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    Matrix (CombinatorialMap.VertexQuotient M)
      (CombinatorialMap.EdgeQuotient M) (ZMod 2) :=
  LinearMap.toMatrix' (vertexBoundary M)

private theorem incidenceMatrix_apply (M : CombinatorialMap D)
    [Fintype (CombinatorialMap.VertexQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)]
    [Fintype (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    (v : CombinatorialMap.VertexQuotient M)
    (e : CombinatorialMap.EdgeQuotient M) :
    incidenceMatrix M v e =
      ∑ d : D, if vertexClass M d = v ∧ edgeClass M d = e then (1 : ZMod 2) else 0 := by
  classical
  rw [incidenceMatrix, LinearMap.toMatrix'_apply]
  change vertexBoundary M (Pi.single e 1) v = _
  unfold vertexBoundary
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hv : vertexClass M d = v <;>
    by_cases he : edgeClass M d = e <;>
    simp [hv, he]

private theorem sum_incidence_entries (M : CombinatorialMap D)
    [Fintype (CombinatorialMap.VertexQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)]
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    (e : CombinatorialMap.EdgeQuotient M) (f : VertexSpace M) :
    (∑ v : CombinatorialMap.VertexQuotient M,
      (∑ d : D, if vertexClass M d = v ∧ edgeClass M d = e then (1 : ZMod 2) else 0)
        * f v) =
      ∑ d : D, if edgeClass M d = e then f (vertexClass M d) else 0 := by
  classical
  calc
    _ = ∑ v : CombinatorialMap.VertexQuotient M,
        ∑ d : D, if vertexClass M d = v ∧ edgeClass M d = e then f v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : vertexClass M d = v ∧ edgeClass M d = e <;> simp [h]
    _ = ∑ d : D, ∑ v : CombinatorialMap.VertexQuotient M,
        if vertexClass M d = v ∧ edgeClass M d = e then f v else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d : D, if edgeClass M d = e then f (vertexClass M d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases he : edgeClass M d = e
      · simp only [he, and_true]
        rw [Finset.sum_eq_single (vertexClass M d)]
        · simp
        · intro v hv hne
          simp [hne.symm]
        · simp
      · simp [he]

private theorem coboundary_eq_matrixTranspose (M : CombinatorialMap D)
    [Fintype (CombinatorialMap.VertexQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)]
    [Fintype (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    coboundary M = Matrix.toLin' (Matrix.transpose (incidenceMatrix M)) := by
  classical
  apply LinearMap.ext
  intro f
  funext e
  refine Quotient.inductionOn e ?_
  intro d
  change coboundary M f (edgeClass M d) =
    ∑ v : CombinatorialMap.VertexQuotient M,
      incidenceMatrix M v (edgeClass M d) * f v
  simp_rw [incidenceMatrix_apply]
  rw [sum_incidence_entries, sum_edgeOrbit]
  rw [coboundary_apply]

private theorem coboundary_ker_eq_span_one (M : CombinatorialMap D)
    (hM : M.IsConnected) :
    LinearMap.ker (coboundary M) = Submodule.span (ZMod 2) {1} := by
  classical
  ext f
  change coboundary M f = 0 ↔ f ∈ Submodule.span (ZMod 2) {1}
  rw [coboundary_eq_zero_iff_connected M hM f]
  constructor
  · rintro (hf | hf)
    · rw [hf]
      exact Submodule.zero_mem _
    · rw [hf]
      exact Submodule.mem_span_singleton_self 1
  · intro hf
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hf
    have haval : a.val = 0 ∨ a.val = 1 := by
      have hv := ZMod.val_lt a
      omega
    rcases haval with ha0 | ha1
    · left
      have ha' : a = 0 := by
        apply ZMod.val_injective 2
        simpa using ha0
      rw [← ha, ha']
      simp
    · right
      have ha' : a = 1 := by
        apply ZMod.val_injective 2
        rw [ZMod.val_one_eq_one_mod]
        omega
      rw [← ha, ha']
      simp

private theorem matrix_rank_eq_finrank_range_toLin'
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (ZMod 2)) :
    A.rank = Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' A)) := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin A
    (Pi.basisFun (ZMod 2) m) (Pi.basisFun (ZMod 2) n),
    Matrix.toLin_eq_toLin']

noncomputable section ZModTwoField

local instance : Field (ZMod 2) :=
  Field.ofIsUnitOrEqZero (by
    intro a
    have hval : a.val = 0 ∨ a.val = 1 := by
      have hlt := ZMod.val_lt a
      omega
    rcases hval with hzero | hone
    · right
      apply ZMod.val_injective 2
      simpa using hzero
    · left
      have ha : a = 1 := by
        apply ZMod.val_injective 2
        rw [ZMod.val_one_eq_one_mod]
        omega
      rw [ha]
      exact isUnit_one
  )

/-- The connected-map coboundary range has dimension one less than the number
of vertices. Helper toward `lem-lr-ind` (planar cut separation), not the paper -/
theorem coboundary_finrank_range_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) :
    Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) =
      M.numVertices - 1 := by
  classical
  have hnull := LinearMap.finrank_range_add_finrank_ker (coboundary M)
  rw [coboundary_ker_eq_span_one M hM] at hnull
  by_cases hV : Nonempty (CombinatorialMap.VertexQuotient M)
  · have hOne : (1 : VertexSpace M) ≠ 0 := by
      intro h
      obtain ⟨v⟩ := hV
      have hv := congrFun h v
      simp at hv
    rw [finrank_span_singleton hOne, Module.finrank_pi] at hnull
    have hresult : Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) =
        Fintype.card (CombinatorialMap.VertexQuotient M) - 1 := by omega
    simpa [CombinatorialMap.numVertices] using hresult
  ·
    have hOne : (1 : VertexSpace M) = 0 := by
      funext v
      exact (hV ⟨v⟩).elim
    have hspan :
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) ({(1 : VertexSpace M)} : Set (VertexSpace M))) = 0 := by
      have hbot :
          Submodule.span (ZMod 2) ({(1 : VertexSpace M)} : Set (VertexSpace M)) = ⊥ := by
        rw [hOne]
        simp
      rw [hbot]
      simp
    have hcard : Fintype.card (CombinatorialMap.VertexQuotient M) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun v => (hV ⟨v⟩).elim⟩
    rw [hspan, Module.finrank_pi, hcard] at hnull
    have hresult : Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) = 0 := by
      omega
    change Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) =
      Fintype.card (CombinatorialMap.VertexQuotient M) - 1
    rw [hcard]
    simpa using hresult

/-- For a connected map, the vertex incidence map has rank one less than the
number of vertices. Helper toward `lem-lr-ind` (planar cut separation), not the -/
theorem vertexBoundary_finrank_range_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) :
    Module.finrank (ZMod 2) (LinearMap.range (vertexBoundary M)) =
      M.numVertices - 1 := by
  classical
  have hVB : (incidenceMatrix M).rank =
      Module.finrank (ZMod 2) (LinearMap.range (vertexBoundary M)) := by
    have h := matrix_rank_eq_finrank_range_toLin' (incidenceMatrix M)
    change (incidenceMatrix M).rank =
      Module.finrank (ZMod 2) (LinearMap.range
        (Matrix.toLin' (LinearMap.toMatrix' (vertexBoundary M)))) at h
    rw [Matrix.toLin'_toMatrix'] at h
    exact h
  have hC : (Matrix.transpose (incidenceMatrix M)).rank =
      Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) := by
    have h := matrix_rank_eq_finrank_range_toLin'
      (Matrix.transpose (incidenceMatrix M))
    change (Matrix.transpose (incidenceMatrix M)).rank =
      Module.finrank (ZMod 2) (LinearMap.range
        (Matrix.toLin' (Matrix.transpose (incidenceMatrix M)))) at h
    rw [← coboundary_eq_matrixTranspose M] at h
    exact h
  have htranspose :
      (incidenceMatrix M).rank = (Matrix.transpose (incidenceMatrix M)).rank := by
    exact (Matrix.rank_transpose (incidenceMatrix M)).symm
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (vertexBoundary M)) =
      Module.finrank (ZMod 2) (LinearMap.range (coboundary M)) := by
    calc
      _ = (incidenceMatrix M).rank := hVB.symm
      _ = (Matrix.transpose (incidenceMatrix M)).rank := htranspose
      _ = _ := hC
  rw [hrank, coboundary_finrank_range_connected M hM]

/-- For a connected map with at least one dart, the cycle-space dimension is
`E + 1 - V`, written additively to avoid truncated natural subtraction. Helper
toward `lem-lr-ind` (planar cut separation), not the paper result -/
theorem cycleSpace_finrank_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) (hD : Nonempty D) :
    Module.finrank (ZMod 2) (cycleSpace M) + M.numVertices =
      M.numEdges + 1 := by
  classical
  obtain ⟨d⟩ := hD
  have hV : 0 < M.numVertices := by
    change 0 < Fintype.card (CombinatorialMap.VertexQuotient M)
    exact Fintype.card_pos_iff.mpr ⟨vertexClass M d⟩
  have hnull := LinearMap.finrank_range_add_finrank_ker (vertexBoundary M)
  rw [vertexBoundary_finrank_range_connected M hM, Module.finrank_pi] at hnull
  change M.numVertices - 1 + Module.finrank (ZMod 2) (cycleSpace M) =
    M.numEdges at hnull
  have hVsub : M.numVertices - 1 + 1 = M.numVertices :=
    Nat.sub_add_cancel (by omega)
  have hsum : Module.finrank (ZMod 2) (cycleSpace M) + M.numVertices =
      M.numEdges + 1 := by
    calc
      _ = Module.finrank (ZMod 2) (cycleSpace M) + (M.numVertices - 1 + 1) := by
        rw [hVsub]
      _ = (M.numVertices - 1 + Module.finrank (ZMod 2) (cycleSpace M)) + 1 := by omega
      _ = M.numEdges + 1 := by rw [hnull]
  exact hsum

private theorem faceBoundary_ker_eq_span_one (M : CombinatorialMap D)
    (hM : M.IsConnected) :
    LinearMap.ker (faceBoundary M) = Submodule.span (ZMod 2) {1} := by
  classical
  ext S
  change faceBoundary M S = 0 ↔ S ∈ Submodule.span (ZMod 2) {1}
  rw [faceBoundary_eq_zero_iff_connected M hM S]
  constructor
  · rintro (hS | hS)
    · rw [hS]
      exact Submodule.zero_mem _
    · rw [hS]
      exact Submodule.mem_span_singleton_self 1
  · intro hS
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hS
    have haval : a.val = 0 ∨ a.val = 1 := by
      have hlt := ZMod.val_lt a
      omega
    rcases haval with ha0 | ha1
    · left
      have ha' : a = 0 := by
        apply ZMod.val_injective 2
        simpa using ha0
      rw [← ha, ha']
      simp
    · right
      have ha' : a = 1 := by
        apply ZMod.val_injective 2
        rw [ZMod.val_one_eq_one_mod]
        omega
      rw [← ha, ha']
      simp

/-- The connected-map face-boundary range has dimension one less than the
number of faces. Helper toward `lem-lr-ind` (planar cut separation), not the -/
theorem faceBoundary_finrank_range_connected (M : CombinatorialMap D)
    (hM : M.IsConnected) :
    Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
      M.numFaces - 1 := by
  classical
  have hnull := LinearMap.finrank_range_add_finrank_ker (faceBoundary M)
  rw [faceBoundary_ker_eq_span_one M hM] at hnull
  by_cases hF : Nonempty (CombinatorialMap.FaceQuotient M)
  · have hOne : (1 : FaceSpace M) ≠ 0 := by
      intro h
      obtain ⟨f⟩ := hF
      have hf := congrFun h f
      simp at hf
    rw [finrank_span_singleton hOne, Module.finrank_pi] at hnull
    have hresult : Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
        Fintype.card (CombinatorialMap.FaceQuotient M) - 1 := by omega
    simpa [CombinatorialMap.numFaces] using hresult
  · have hOne : (1 : FaceSpace M) = 0 := by
      funext f
      exact (hF ⟨f⟩).elim
    have hspan :
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) ({(1 : FaceSpace M)} : Set (FaceSpace M))) = 0 := by
      have hbot :
          Submodule.span (ZMod 2) ({(1 : FaceSpace M)} : Set (FaceSpace M)) = ⊥ := by
        rw [hOne]
        simp
      rw [hbot]
      simp
    have hcard : Fintype.card (CombinatorialMap.FaceQuotient M) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun f => (hF ⟨f⟩).elim⟩
    rw [hspan, Module.finrank_pi, hcard] at hnull
    have hresult : Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) = 0 := by
      omega
    change Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
      Fintype.card (CombinatorialMap.FaceQuotient M) - 1
    rw [hcard]
    simpa using hresult

private theorem planar_nonempty_darts (M : CombinatorialMap D)
    (hM : M.IsPlanar) : Nonempty D := by
  classical
  by_contra hD
  have hEmptyD : IsEmpty D := not_nonempty_iff.mp hD
  have hVCard : Fintype.card (CombinatorialMap.VertexQuotient M) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun q => Quotient.inductionOn q
      (fun d => hEmptyD.elim d)⟩
  have hECard : Fintype.card (CombinatorialMap.EdgeQuotient M) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun q => Quotient.inductionOn q
      (fun d => hEmptyD.elim d)⟩
  have hFCard : Fintype.card (CombinatorialMap.FaceQuotient M) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun q => Quotient.inductionOn q
      (fun d => hEmptyD.elim d)⟩
  have hV : M.numVertices = 0 := by
    change Fintype.card (CombinatorialMap.VertexQuotient M) = 0
    exact hVCard
  have hE : M.numEdges = 0 := by
    change Fintype.card (CombinatorialMap.EdgeQuotient M) = 0
    exact hECard
  have hF : M.numFaces = 0 := by
    change Fintype.card (CombinatorialMap.FaceQuotient M) = 0
    exact hFCard
  have hEuler := hM.2
  rw [CombinatorialMap.eulerChar, hV, hE, hF] at hEuler
  norm_num at hEuler

private theorem planar_range_faceBoundary_eq_cycleSpace
    (M : CombinatorialMap D) (hM : M.IsPlanar) :
    LinearMap.range (faceBoundary M) = cycleSpace M := by
  classical
  have hD := planar_nonempty_darts M hM
  have hcycle := cycleSpace_finrank_connected M hM.1 hD
  have hface := faceBoundary_finrank_range_connected M hM.1
  have hEuler : (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2 := by
    simpa [CombinatorialMap.eulerChar] using hM.2
  have hdim :
      Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
        Module.finrank (ZMod 2) (cycleSpace M) := by
    omega
  exact Submodule.eq_of_le_of_finrank_eq
    (faceBoundary_range_le_cycleSpace M) hdim

/-- Every mod-two cycle in a planar combinatorial map is a sum of face
boundaries. This is a helper toward `lem-lr-ind` (planar cut separation), not -/
theorem planar_cycle_eq_faceBoundary (M : CombinatorialMap D)
    (hM : M.IsPlanar) (c : EdgeSpace M) (hc : vertexBoundary M c = 0) :
    ∃ S : FaceSpace M, faceBoundary M S = c := by
  have hrange := planar_range_faceBoundary_eq_cycleSpace M hM
  have hcCycle : c ∈ cycleSpace M := by
    change c ∈ LinearMap.ker (vertexBoundary M)
    exact LinearMap.mem_ker.mpr hc
  have hcRange : c ∈ LinearMap.range (faceBoundary M) := by
    rw [hrange]
    exact hcCycle
  rcases hcRange with ⟨S, hS⟩
  exact ⟨S, hS⟩

/-- For a planar map, two face functions with the same cycle boundary agree or
differ by the all-ones function. This is a helper toward `lem-lr-ind` (planar -/
theorem planar_faceBoundary_unique_up_to_complement
    (M : CombinatorialMap D) (hM : M.IsPlanar) (c : EdgeSpace M)
    (S S' : FaceSpace M) (hS : faceBoundary M S = c)
    (hS' : faceBoundary M S' = c) :
    S = S' ∨ S = S' + (1 : FaceSpace M) := by
  apply (faceBoundary_eq_iff M hM.1 S S').mp
  calc
    faceBoundary M S = c := hS
    _ = faceBoundary M S' := hS'.symm

end ZModTwoField

end DirectedDistances.PlanarMap
