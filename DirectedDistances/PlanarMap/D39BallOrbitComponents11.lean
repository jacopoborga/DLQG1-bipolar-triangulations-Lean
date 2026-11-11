/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents10

/-! # Removing a reversal pair from a loop-free drawing

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`, -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set

namespace CombinatorialMap
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.16: enumerate the finite vertex quotient. -/
local instance vertexQuotientFintype (M : CombinatorialMap D) :
    Fintype (VertexQuotient M) := Fintype.ofFinite _

/-- Helper toward Proposition 5.16: retain every rotation step and all
edge steps except the selected reversal pair. -/
@[expose] def pairAvoidingStep (M : CombinatorialMap D) (d₀ : D) (x y : D) : Prop :=
  M.rot x = y ∨ (x ≠ d₀ ∧ x ≠ M.edgeInv d₀ ∧ M.edgeInv x = y)

/-- Helper toward Proposition 5.16: rotation-equivalent darts remain
connected when only an edge pair is suppressed. -/
theorem eqvGen_pairAvoidingStep_of_sameCycle (M : CombinatorialMap D) (d₀ : D)
    {x y : D} (h : M.rot.SameCycle x y) :
    Relation.EqvGen (M.pairAvoidingStep d₀) x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))

/-- Helper toward Proposition 5.16: the two darts of an edge represent
the same edge coefficient. -/
theorem edgeClass_flip_eq (M : CombinatorialMap D) (d : D) :
    edgeClass M (M.edgeInv d) = edgeClass M d := by
  apply Quotient.sound
  exact ((M.edgeInv_sameCycle_iff d (M.edgeInv d)).mpr (Or.inr rfl)).symm

/-- Helper toward Proposition 5.16: summing a weighted vertex boundary
is the corresponding weighted sum over incident darts. -/
theorem sum_mul_vertexBoundary (M : CombinatorialMap D)
    (f : VertexSpace M) (c : EdgeSpace M) :
    (∑ v, f v * vertexBoundary M c v) =
      ∑ d : D, f (vertexClass M d) * c (edgeClass M d) := by
  classical
  simp only [vertexBoundary, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single (vertexClass M d)]
  · simp only [ite_true]
  · intro v hv hne
    exact ite_eq_right hne.symm
  · simp

/-- Helper toward Proposition 5.16: a nonzero coefficient of a mod-two
cycle gives an alternate connection between the endpoints of that edge.
The relation keeps the old vertex cycles and omits exactly this edge. -/
theorem eqvGen_pairAvoidingStep_flip_of_cycle (M : CombinatorialMap D)
    (c : EdgeSpace M) (hc : vertexBoundary M c = 0) (d₀ : D)
    (hne : c (edgeClass M d₀) ≠ 0) :
    Relation.EqvGen (M.pairAvoidingStep d₀) d₀ (M.edgeInv d₀) := by
  classical
  let R := Relation.EqvGen (M.pairAvoidingStep d₀)
  by_contra hnot
  change ¬ R d₀ (M.edgeInv d₀) at hnot
  have hrot {x y : D} (h : M.rot.SameCycle x y) : R x y :=
    M.eqvGen_pairAvoidingStep_of_sameCycle d₀ h
  let f : VertexSpace M := Quotient.lift
    (fun d => if R d₀ d then (1 : ZMod 2) else 0)
    (by
      intro x y h
      have hxy := hrot h
      have he : R d₀ x ↔ R d₀ y :=
        ⟨fun hx => hx.trans _ _ _ hxy, fun hy => hy.trans _ _ _ (hxy.symm _ _)⟩
      simp only [he])
  have hf (d : D) : f (vertexClass M d) = if R d₀ d then 1 else 0 := rfl
  let g : D → ZMod 2 := fun d => f (vertexClass M d) * c (edgeClass M d)
  have hgflip (d : D) (hd : d ≠ d₀ ∧ d ≠ M.edgeInv d₀) :
      g (M.edgeInv d) = g d := by
    have hr : R d (M.edgeInv d) := Relation.EqvGen.rel _ _ (Or.inr ⟨hd.1, hd.2, rfl⟩)
    have he : R d₀ (M.edgeInv d) ↔ R d₀ d :=
      ⟨fun h => h.trans _ _ _ (hr.symm _ _), fun h => h.trans _ _ _ hr⟩
    simp only [g, hf, M.edgeClass_flip_eq, he]
  let s := Finset.univ.erase d₀ |>.erase (M.edgeInv d₀)
  have hs (d : D) : d ∈ s ↔ d ≠ d₀ ∧ d ≠ M.edgeInv d₀ := by
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  have hflipmem (d : D) (hd : d ∈ s) : M.edgeInv d ∈ s := by
    rw [hs] at hd ⊢
    constructor
    · intro h
      exact hd.2 ((M.edgeInv_invol d).symm.trans (congrArg M.edgeInv h))
    · intro h
      exact hd.1 (M.edgeInv.injective h)
  have hsum : ∑ d ∈ s, g d = 0 := by
    apply Finset.sum_involution (fun d _ => M.edgeInv d)
    · intro d hd
      rw [hgflip d ((hs d).mp hd)]
      exact CharTwo.add_self_eq_zero _
    · intro d hd hn
      exact M.edgeInv_ne d
    · exact hflipmem
    · intro d hd
      exact M.edgeInv_invol d
  have hu : Finset.univ = insert d₀ (insert (M.edgeInv d₀) s) := by
    ext d
    simp only [Finset.mem_univ, Finset.mem_insert, hs, true_iff]
    by_cases h₁ : d = d₀
    · exact Or.inl h₁
    by_cases h₂ : d = M.edgeInv d₀
    · exact Or.inr (Or.inl h₂)
    exact Or.inr (Or.inr ⟨h₁, h₂⟩)
  have hz : ∑ d : D, g d = 0 := by
    rw [← M.sum_mul_vertexBoundary f c, hc]
    simp
  rw [hu, Finset.sum_insert (by
    simp only [Finset.mem_insert, hs, not_or]
    exact ⟨(M.edgeInv_ne d₀).symm, fun h => h.1 rfl⟩),
    Finset.sum_insert (by rw [hs]; exact fun h => h.2 rfl), hsum] at hz
  have hf₀ : R d₀ d₀ := Relation.EqvGen.refl _
  simp only [g, hf, ite_eq_left hf₀, ite_eq_right hnot, one_mul, zero_mul, add_zero] at hz
  exact hne hz

/-- Helper toward Proposition 5.16: replacing the suppressed edge step
by an alternate connection preserves connectedness on the old dart set. -/
theorem pairAvoidingStep_connected_of_alternate (M : CombinatorialMap D)
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e)
    (d₀ : D) (halt : Relation.EqvGen (M.pairAvoidingStep d₀) d₀ (M.edgeInv d₀)) :
    ∀ d e : D, Relation.EqvGen (M.pairAvoidingStep d₀) d e := by
  intro d e
  refine Relation.EqvGen.eqvGen_le
    (r' := Relation.EqvGen (M.pairAvoidingStep d₀)) ?_ d e (hconn d e)
  intro x y h
  rcases h with h | rfl
  · exact Relation.EqvGen.rel _ _ (Or.inl h)
  · by_cases hx : x = d₀
    · subst x; exact halt
    by_cases hx' : x = M.edgeInv d₀
    · subst x
      rw [M.edgeInv_invol]
      exact halt.symm _ _
    exact Relation.EqvGen.rel _ _ (Or.inr ⟨hx, hx', rfl⟩)

/-- Helper toward Proposition 5.16: if the edge-suppressed relation is
connected and a dart remains, every old vertex has a remaining dart. -/
theorem vertex_survives_of_pairAvoidingStep_connected (M : CombinatorialMap D)
    (d₀ : D)
    (hconn : ∀ d e : D, Relation.EqvGen (M.pairAvoidingStep d₀) d e)
    (ht : ∃ t : D, t ≠ d₀ ∧ t ≠ M.edgeInv d₀) :
    ∀ d : D, ∃ e : D, M.rot.SameCycle d e ∧ e ≠ d₀ ∧ e ≠ M.edgeInv d₀ := by
  classical
  intro d
  by_contra hnone
  have hnot (x : D) (hx : x ≠ d₀ ∧ x ≠ M.edgeInv d₀) : ¬ M.rot.SameCycle d x :=
    fun h => hnone ⟨x, h, hx⟩
  have hinv {x y : D} (h : Relation.EqvGen (M.pairAvoidingStep d₀) x y) :
      M.rot.SameCycle d x ↔ M.rot.SameCycle d y := by
    induction h with
    | rel x y h =>
      rcases h with h | ⟨hx, hx', rfl⟩
      · subst y
        exact Equiv.Perm.sameCycle_apply_right.symm
      · have hy : M.edgeInv x ≠ d₀ ∧ M.edgeInv x ≠ M.edgeInv d₀ := by
          constructor
          · intro h
            exact hx' ((M.edgeInv_invol x).symm.trans (congrArg M.edgeInv h))
          · exact fun h => hx (M.edgeInv.injective h)
        exact iff_of_false (hnot x ⟨hx, hx'⟩) (hnot _ hy)
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  obtain ⟨t, ht⟩ := ht
  exact hnot t ht ((hinv (hconn d t)).mp Equiv.Perm.SameCycle.rfl)

/-- Helper toward Proposition 5.16: the field structure used by the
already proved mod-two cycle-space dimension formula. -/
local instance cycleCoefficientField : Field (ZMod 2) :=
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
      exact isUnit_one)

/-- Helper toward Proposition 5.16: a connected map with at least as
many edges as vertices has a nonzero cycle coefficient on some edge. -/
theorem exists_nonzero_cycle_coefficient (M : CombinatorialMap D) [Nonempty D]
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e)
    (hcount : M.numVertices ≤ M.numEdges) :
    ∃ (c : EdgeSpace M) (d₀ : D), vertexBoundary M c = 0 ∧ c (edgeClass M d₀) ≠ 0 := by
  classical
  have hdim := cycleSpace_finrank_connected M (M.isConnected_of_eqvGen hconn) ‹Nonempty D›
  have hpos : 0 < Module.finrank (ZMod 2) (cycleSpace M) := by omega
  obtain ⟨c, hc⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hcv : (c : EdgeSpace M) ≠ 0 := by
    intro h
    exact hc (Subtype.ext h)
  have hex : ∃ q, c.val q ≠ 0 := by
    by_contra h
    apply hcv
    funext q
    exact not_not.mp (fun hn => h ⟨q, hn⟩)
  obtain ⟨q, hq⟩ := hex
  obtain ⟨d₀, rfl⟩ := Quotient.exists_rep q
  exact ⟨c, d₀, c.property, hq⟩

/-- Helper toward Proposition 5.16: choose a reversal pair whose removal
preserves connectivity on vertex cycles and leaves every vertex incident.
The four-dart bound excludes the isolated single-loop exception; no
planarity, Euler formula, or loop-freeness is needed for this selection. -/
theorem exists_connected_pairAvoidingStep (M : CombinatorialMap D)
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e)
    (hcount : M.numVertices ≤ M.numEdges) (hcard : 4 ≤ Fintype.card D) :
    ∃ d₀ : D,
      (∀ d e : D, Relation.EqvGen (M.pairAvoidingStep d₀) d e) ∧
      (∀ d : D, ∃ e : D, M.rot.SameCycle d e ∧ e ≠ d₀ ∧ e ≠ M.edgeInv d₀) := by
  classical
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨c, d₀, hc, hd₀⟩ := M.exists_nonzero_cycle_coefficient hconn hcount
  have hconn' := M.pairAvoidingStep_connected_of_alternate hconn d₀
    (M.eqvGen_pairAvoidingStep_flip_of_cycle c hc d₀ hd₀)
  refine ⟨d₀, hconn', M.vertex_survives_of_pairAvoidingStep_connected d₀ hconn' ?_⟩
  by_contra hnone
  have hsub : (Finset.univ : Finset D) ⊆ {d₀, M.edgeInv d₀} := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    exact hnone ⟨d, (not_or.mp h).1, (not_or.mp h).2⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({d₀, M.edgeInv d₀} : Finset D).card = 2 := by
    exact Finset.card_pair_eq_two_iff.mpr (M.edgeInv_ne d₀).symm
  rw [Finset.card_univ] at hle
  omega

end CombinatorialMap

/-- Helper toward Proposition 5.16: a finite permutation has a positive
return to every subset containing its starting point. -/
theorem finiteSubsetPositiveReturn {D : Type*} [Fintype D]
    (σ : Equiv.Perm D) (S : Set D) (x : S) :
    ∃ k : ℕ, 0 < k ∧ (σ : D → D)^[k] x.val ∈ S := by
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  rw [permIterateEqPow, pow_orderOf_eq_one]
  exact x.property

/-- Helper toward Proposition 5.16: every retained ambient iterate is
reached by an iterate of the subset first-return permutation. -/
theorem subsetFirstReturnPerm_reaches_iterate {D : Type*}
    (σ : Equiv.Perm D) (S : Set D)
    (hp : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ : D → D)^[k] x.val ∈ S)
    (hi : ∀ x : S, ∃ k : ℕ, 0 < k ∧ ((σ⁻¹ : Equiv.Perm D) : D → D)^[k] x.val ∈ S)
    (q : ℕ) (x : S) (hq : (σ ^ q) x.val ∈ S) :
    ∃ n : ℕ, ((subsetFirstReturnPerm σ S hp hi ^ n) x).val = (σ ^ q) x.val := by
  classical
  induction q using Nat.strong_induction_on generalizing x with
  | h q ih =>
    by_cases hzero : q = 0
    · subst q
      exact ⟨0, rfl⟩
    let k := subsetFirstReturnTime σ S hp x
    have hk := subsetFirstReturnTime_spec σ S hp x
    have hkq : k ≤ q := Nat.find_min' (hp x) ⟨by omega, by
      rw [permIterateEqPow]; exact hq⟩
    let R := subsetFirstReturnPerm σ S hp hi
    let y := R x
    have hy : y.val = (σ ^ k) x.val := by
      rw [subsetFirstReturnPerm_apply, permIterateEqPow]
    by_cases heq : k = q
    · refine ⟨1, ?_⟩
      simpa only [pow_one, ← heq] using hy
    have hr : q - k < q := by dsimp [k] at *; omega
    have hrem : (σ ^ (q - k)) y.val = (σ ^ q) x.val := by
      rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hkq]
    obtain ⟨n, hn⟩ := ih (q - k) hr y (hrem.symm ▸ hq)
    refine ⟨n + 1, ?_⟩
    calc
      ((R ^ (n + 1)) x).val = ((R ^ n) y).val := by
        rw [pow_succ, Equiv.Perm.mul_apply]
      _ = (σ ^ (q - k)) y.val := hn
      _ = (σ ^ q) x.val := hrem

/-- Helper toward Proposition 5.16: first-return rotation preserves
exactly the old rotation cycles intersected with the retained dart set. -/
theorem subsetFirstReturnPerm_sameCycle_iff {D : Type*} [Finite D]
    (σ : Equiv.Perm D) (S : Set D)
    (hp : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ : D → D)^[k] x.val ∈ S)
    (hi : ∀ x : S, ∃ k : ℕ, 0 < k ∧ ((σ⁻¹ : Equiv.Perm D) : D → D)^[k] x.val ∈ S)
    (x y : S) :
    (subsetFirstReturnPerm σ S hp hi).SameCycle x y ↔ σ.SameCycle x.val y.val := by
  let R := subsetFirstReturnPerm σ S hp hi
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (subsetFirstReturn_sameCycle σ S hp _)
  · intro h
    obtain ⟨q, hq⟩ := h.exists_nat_pow_eq
    obtain ⟨n, hn⟩ := subsetFirstReturnPerm_reaches_iterate σ S hp hi q x (hq.symm ▸ y.property)
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext (hn.trans hq)

namespace CombinatorialMap
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.16: darts retained after one reversal
pair is deleted. -/
@[expose] def pairComplement (M : CombinatorialMap D) (d₀ : D) : Set D :=
  {d | d ≠ d₀ ∧ d ≠ M.edgeInv d₀}

/-- Helper toward Proposition 5.16: the retained dart set is invariant
under reversal. -/
theorem mem_pairComplement_flip_iff (M : CombinatorialMap D) (d₀ d : D) :
    M.edgeInv d ∈ M.pairComplement d₀ ↔ d ∈ M.pairComplement d₀ := by
  change (M.edgeInv d ≠ d₀ ∧ M.edgeInv d ≠ M.edgeInv d₀) ↔
    (d ≠ d₀ ∧ d ≠ M.edgeInv d₀)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₂ (congrArg M.edgeInv h), fun h => h₁ (h ▸ M.edgeInv_invol d₀)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₂ ((M.edgeInv_invol d).symm.trans (congrArg M.edgeInv h)),
      fun h => h₁ (M.edgeInv.injective h)⟩

/-- Helper toward Proposition 5.16: the actual first-return rotation
on the complement of the selected reversal pair. -/
@[expose] def pairComplementRotation (M : CombinatorialMap D) (d₀ : D) :
    Equiv.Perm (M.pairComplement d₀) :=
  subsetFirstReturnPerm M.rot (M.pairComplement d₀)
    (finiteSubsetPositiveReturn _ _) (finiteSubsetPositiveReturn _ _)

/-- Helper toward Proposition 5.16: the retained rotation cycles are
precisely the old vertex cycles on retained darts. -/
theorem pairComplementRotation_sameCycle_iff (M : CombinatorialMap D) (d₀ : D)
    (x y : M.pairComplement d₀) :
    (M.pairComplementRotation d₀).SameCycle x y ↔ M.rot.SameCycle x.val y.val :=
  subsetFirstReturnPerm_sameCycle_iff _ _ _ _ _ _

/-- Helper toward Proposition 5.16: an ambient vertex cycle supplies
rotation steps in any relation containing the forward rotation steps. -/
theorem eqvGen_of_rotation_sameCycle {A : Type*} [Finite A]
    (σ : Equiv.Perm A) (r : A → A → Prop) (hr : ∀ a, r a (σ a))
    {x y : A} (h : σ.SameCycle x y) : Relation.EqvGen r x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans _ _ _ (Relation.EqvGen.rel _ _ (hr _))

/-- Helper toward Proposition 5.16: suppressing an edge on old vertex
cycles and then taking first returns gives a connected retained map. -/
theorem pairComplementRotation_connected (M : CombinatorialMap D) (d₀ : D)
    (hconn : ∀ d e : D, Relation.EqvGen (M.pairAvoidingStep d₀) d e)
    (hsurv : ∀ d : D, ∃ e : D, M.rot.SameCycle d e ∧ e ∈ M.pairComplement d₀) :
    ∀ d e : M.pairComplement d₀, Relation.EqvGen
      (fun x y => M.pairComplementRotation d₀ x = y ∨ M.edgeInv x.val = y.val) d e := by
  classical
  let r := fun x y : M.pairComplement d₀ =>
    M.pairComplementRotation d₀ x = y ∨ M.edgeInv x.val = y.val
  let pick : D → M.pairComplement d₀ := fun d =>
    ⟨(hsurv d).choose, (hsurv d).choose_spec.2⟩
  have hpick (d : D) : M.rot.SameCycle d (pick d).val := (hsurv d).choose_spec.1
  have hrot {x y : M.pairComplement d₀} (h : M.rot.SameCycle x.val y.val) :
      Relation.EqvGen r x y :=
    eqvGen_of_rotation_sameCycle _ r (fun _ => Or.inl rfl)
      ((M.pairComplementRotation_sameCycle_iff d₀ x y).mpr h)
  have hstep {x y : D} (h : M.pairAvoidingStep d₀ x y) :
      Relation.EqvGen r (pick x) (pick y) := by
    rcases h with h | ⟨hx, hx', rfl⟩
    · subst y
      exact hrot ((hpick x).symm.trans (Equiv.Perm.SameCycle.rfl.apply_right.trans (hpick _)))
    · let a : M.pairComplement d₀ := ⟨x, hx, hx'⟩
      let b : M.pairComplement d₀ :=
        ⟨M.edgeInv x, (M.mem_pairComplement_flip_iff d₀ x).mpr a.property⟩
      exact (hrot (hpick x).symm).trans _ _ _
        ((Relation.EqvGen.rel a b (Or.inr rfl)).trans _ _ _ (hrot (hpick _)))
  have hlift {x y : D} (h : Relation.EqvGen (M.pairAvoidingStep d₀) x y) :
      Relation.EqvGen r (pick x) (pick y) := by
    induction h with
    | rel x y h => exact hstep h
    | refl => exact Relation.EqvGen.refl _
    | symm x y h ih => exact ih.symm _ _
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans _ _ _ ihyz
  intro d e
  exact (hrot (hpick d.val)).trans _ _ _
    ((hlift (hconn d.val e.val)).trans _ _ _ (hrot (hpick e.val).symm))

/-- Helper toward Proposition 5.16: a removable reversal pair with its
first-return rotation, retained connectivity, and survival of every vertex. -/
theorem exists_connected_vertex_preserving_pair (M : CombinatorialMap D)
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e)
    (hcount : M.numVertices ≤ M.numEdges) (hcard : 4 ≤ Fintype.card D) :
    ∃ (d₀ : D) (rot' : Equiv.Perm {d : D // d ≠ d₀ ∧ d ≠ M.edgeInv d₀}),
      (∀ d : {d : D // d ≠ d₀ ∧ d ≠ M.edgeInv d₀},
        ∃ n : ℕ, 0 < n ∧ (M.rot ^ n) d.val = (rot' d).val ∧
          ∀ k : ℕ, 0 < k → k < n →
            (M.rot ^ k) d.val = d₀ ∨ (M.rot ^ k) d.val = M.edgeInv d₀) ∧
      (∀ d e : {d : D // d ≠ d₀ ∧ d ≠ M.edgeInv d₀}, Relation.EqvGen
        (fun x y => rot' x = y ∨ M.edgeInv x.val = y.val) d e) ∧
      (∀ d : D, ∃ e : D, M.rot.SameCycle d e ∧ e ≠ d₀ ∧ e ≠ M.edgeInv d₀) := by
  classical
  obtain ⟨d₀, hconn', hsurv⟩ := M.exists_connected_pairAvoidingStep hconn hcount hcard
  refine ⟨d₀, M.pairComplementRotation d₀, ?_,
    M.pairComplementRotation_connected d₀ hconn' hsurv, hsurv⟩
  intro d
  let hp := finiteSubsetPositiveReturn M.rot (M.pairComplement d₀)
  let n := subsetFirstReturnTime M.rot (M.pairComplement d₀) hp d
  have hn := subsetFirstReturnTime_spec M.rot (M.pairComplement d₀) hp d
  refine ⟨n, hn.1, ?_, ?_⟩
  · exact (congrFun (permIterateEqPow M.rot n) d.val).symm
  · intro k hk hkn
    have hnot := hn.2.2 k hk hkn
    rw [permIterateEqPow] at hnot
    exact not_and_or.mp hnot |>.imp not_not.mp not_not.mp

/-- Helper toward Proposition 5.16: enumerate the retained darts. -/
instance pairComplementFintype (M : CombinatorialMap D) (d₀ : D) :
    Fintype (M.pairComplement d₀) := by classical exact Subtype.fintype _

/-- Helper toward Proposition 5.16: delete exactly one reversal pair,
using the actual first-return rotation on the retained dart identities. -/
@[expose] def pairComplementMap (M : CombinatorialMap D) (d₀ : D) :
    CombinatorialMap (M.pairComplement d₀) where
  edgeInv :=
    { toFun := fun d => ⟨M.edgeInv d.val, (M.mem_pairComplement_flip_iff d₀ d.val).mpr d.property⟩
      invFun := fun d => ⟨M.edgeInv d.val, (M.mem_pairComplement_flip_iff d₀ d.val).mpr d.property⟩
      left_inv := fun d => Subtype.ext (M.edgeInv_invol d.val)
      right_inv := fun d => Subtype.ext (M.edgeInv_invol d.val) }
  edgeInv_invol := fun d => Subtype.ext (M.edgeInv_invol d.val)
  edgeInv_ne := fun d h => M.edgeInv_ne d.val (congrArg Subtype.val h)
  rot := M.pairComplementRotation d₀

end CombinatorialMap

namespace PLDrawing
variable {D V : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.16: restrict the arcs and first-return
rotation after deleting a pair, while retaining the entire vertex carrier.
Surjectivity is proved separately from survival of the vertex cycles. -/
@[expose] def pairComplementDrawing (M : CombinatorialMap D) (vert : D → V)
    (P : PLDrawing D V M.edgeInv M.rot vert) (d₀ : D) :
    PLDrawing (M.pairComplement d₀) V (M.pairComplementMap d₀).edgeInv
      (M.pairComplementMap d₀).rot (fun d => vert d.val) := by
  classical
  let S := M.pairComplement d₀
  let hs : ∀ d, d ∈ S ↔ M.edgeInv d ∈ S :=
    fun d => (M.mem_pairComplement_flip_iff d₀ d).symm
  let Q := restrictDrawing P S hs
  refine {
    flip_involutive := Q.flip_involutive
    flip_ne := Q.flip_ne
    vert_rotation := drawingFirstReturn_sameVertex P S
    pos := P.pos
    pos_injective := P.pos_injective
    arc := fun d => P.arc d.val
    arc_simple := fun d => P.arc_simple d.val
    arc_length := fun d => P.arc_length d.val
    arc_start := fun d => P.arc_start d.val
    arc_finish := fun d => P.arc_finish d.val
    arc_flip := fun d => P.arc_flip d.val
    interior_disjoint := Q.interior_disjoint
    interior_avoids_vertices := fun d v => P.interior_avoids_vertices d.val v
    locally_finite := fun _ _ => Set.toFinite _
    initial_nonzero := fun d => P.initial_nonzero d.val
    initial_arg_injective := ?_
    rotation_agreement := ?_ }
  · intro d e hv ha
    exact Subtype.ext (P.initial_arg_injective d.val e.val hv ha)
  · intro d
    have h := Q.rotation_agreement d
    change CcwSuccessor {e : S | restrictedVertex P S e = restrictedVertex P S d}
      (fun e => (P.arc e.val).initialDirection) d (drawingFirstReturnPerm P S d) at h
    simpa only [CcwSuccessor, restrictedVertex_eq_iff,
      CombinatorialMap.pairComplementMap, CombinatorialMap.pairComplementRotation,
      drawingFirstReturnPerm, S] using h

/-- Helper toward Proposition 5.16: a vertex-preserving pair deletion
keeps the incidence function surjective onto the original vertex carrier. -/
theorem pairComplement_incidence_surjective (M : CombinatorialMap D) (vert : D → V)
    (P : PLDrawing D V M.edgeInv M.rot vert) (hvert : Function.Surjective vert)
    (d₀ : D) (hsurv : ∀ d : D, ∃ e : D,
      M.rot.SameCycle d e ∧ e ≠ d₀ ∧ e ≠ M.edgeInv d₀) :
    Function.Surjective (fun d : M.pairComplement d₀ => vert d.val) := by
  intro v
  obtain ⟨d, rfl⟩ := hvert v
  obtain ⟨e, hde, he⟩ := hsurv d
  exact ⟨⟨e, he⟩, (P.vert_eq_of_rot_sameCycle d e hde).symm⟩

/-- Helper toward Proposition 5.16: a nonempty drawing with at least as
many edges as vertices has at least four darts. Distinct arc endpoints
give two distinct vertex cycles, so the single-loop exception cannot occur. -/
theorem four_le_card_of_numVertices_le_numEdges (M : CombinatorialMap D) (vert : D → V)
    (P : PLDrawing D V M.edgeInv M.rot vert) (d : D)
    (hcount : M.numVertices ≤ M.numEdges) : 4 ≤ Fintype.card D := by
  classical
  have hne : vertexClass M d ≠ vertexClass M (M.edgeInv d) := by
    intro h
    exact P.vert_ne_flip d
      (P.vert_eq_of_rot_sameCycle d (M.edgeInv d) (Quotient.exact h))
  have hV : 1 < M.numVertices := Fintype.one_lt_card_iff.mpr
    ⟨vertexClass M d, vertexClass M (M.edgeInv d), hne⟩
  have hE := M.two_mul_numEdges
  omega

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: package the retained dart identities
as a finite ball. Missing and tail flags are inherited; an original face
flag is retained only for a whole retained face cycle lying in the old flag. -/
@[expose] def pairDeletedBall (B : D39FiniteBall) (d₀ : B.D)
    (root : B.map.pairComplement d₀) : D39FiniteBall := by
  classical
  let M := B.map.pairComplementMap d₀
  exact {
    D := B.map.pairComplement d₀
    instFintypeD := B.map.pairComplementFintype d₀
    instDecidableEqD := inferInstance
    map := M
    missing := fun d => B.missing d.val
    tail := fun d => B.tail d.val
    rootDart := root
    original := {d | ∀ e, M.faceSucc.SameCycle d e → e.val ∈ B.original}
    original_closed := by
      intro d
      simp only [Set.mem_ofPred_eq, Equiv.Perm.sameCycle_apply_left] }

/-- Helper toward Proposition 5.16: a connected non-tree drawing admits
deletion of one pair, preserving the vertex carrier, connectivity, positions
and all retained arcs; the removed interior lies in a single retained face. -/
theorem exists_connected_edge_deletion
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (hcount : B.map.numVertices ≤ B.map.numEdges) (hcard : 4 ≤ Fintype.card B.D) :
    ∃ (B' : D39FiniteBall) (vert' : B'.D → V)
      (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
      (newDart : B.D) (ι : B'.D ↪ B.D),
      Function.Surjective vert' ∧
      (∀ d e : B'.D, Relation.EqvGen
        (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e) ∧
      (∀ d : B.D, d ∈ Set.range ι ↔ d ≠ newDart ∧ d ≠ B.map.edgeInv newDart) ∧
      (∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d)) ∧
      (∀ d : B'.D, vert (ι d) = vert' d) ∧
      (∀ v : V, P.pos v = P'.pos v) ∧
      (∀ d : B'.D, P.arc (ι d) = P'.arc d) ∧
      (∃ F : P'.Face, (P.arc newDart).interior ⊆ F.val) ∧
      B'.map.numEdges < B.map.numEdges := by
  classical
  obtain ⟨d₀, hconn₀, hsurv⟩ := B.map.exists_connected_pairAvoidingStep hconn hcount hcard
  obtain ⟨root, hroot, hrootS⟩ := hsurv B.rootDart
  let B' := B.pairDeletedBall d₀ ⟨root, hrootS⟩
  let vert' : B'.D → V := fun d => vert d.val
  let P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert' :=
    P.pairComplementDrawing B.map vert d₀
  let ι : B'.D ↪ B.D := ⟨Subtype.val, Subtype.val_injective⟩
  have himage (d : B.D) : d ∈ Set.range ι ↔ d ≠ d₀ ∧ d ≠ B.map.edgeInv d₀ := by
    exact ⟨fun ⟨e, he⟩ => he ▸ e.property, fun h => ⟨⟨d, h⟩, rfl⟩⟩
  have hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e := by
    intro d e
    have h := B.map.pairComplementRotation_connected d₀ hconn₀ hsurv d e
    apply Relation.EqvGen.mono ?_ _ _ h
    intro x y hxy
    exact hxy.imp id (fun he => Subtype.ext he)
  have hface := exists_face_arc_interior_subset_of_edge_insertion B' B vert' vert P' P
    d₀ ι himage (fun _ => rfl) (fun _ => rfl)
  have hE := numEdges_eq_add_one_of_edge_insertion B' B d₀ ι himage
  exact ⟨B', vert', P', d₀, ι,
    P.pairComplement_incidence_surjective B.map vert hvert d₀ hsurv,
    hconn', himage, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    hface, by omega⟩

/-- Helper toward Proposition 5.16: every connected finite drawing has
common-face orbit uniqueness and Euler characteristic two. Strong induction
deletes a nonbridge pair; the tree base and the geometric insertion step
are the proved joint statements of `D39BallOrbitComponents8`. -/
theorem common_face_orbit_unique_and_eulerChar_eq_two
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    (∀ d e : B.D, B.plDartFace vert P hvert d = B.plDartFace vert P hvert e →
      B.map.faceSucc.SameCycle d e) ∧ B.map.eulerChar = 2 := by
  classical
  have H : ∀ n : ℕ, ∀ (C : D39FiniteBall), Fintype.card C.D = n →
      ∀ (v : C.D → V) (Q : PLDrawing C.D V C.map.edgeInv C.map.rot v)
        (hv : Function.Surjective v)
        (hc : ∀ d e : C.D, Relation.EqvGen
          (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e),
      (∀ d e : C.D, C.plDartFace v Q hv d = C.plDartFace v Q hv e →
        C.map.faceSucc.SameCycle d e) ∧ C.map.eulerChar = 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C hCn v Q hv hc
      by_cases hcount : C.map.numVertices ≤ C.map.numEdges
      · have hcard := Q.four_le_card_of_numVertices_le_numEdges C.map v C.rootDart hcount
        obtain ⟨C', v', Q', newDart, ι, hv', hc', himage, hflip, hvertι, hpos,
          harcs, ⟨F, hinterior⟩, hE⟩ :=
          C.exists_connected_edge_deletion v Q hv hc hcount hcard
        have hsmall : Fintype.card C'.D < n := by
          have hD := C.map.two_mul_numEdges
          have hD' := C'.map.two_mul_numEdges
          omega
        exact common_face_orbit_unique_and_eulerChar_eq_two_of_nonbridge_edge_insertion
          C' C v' v Q' Q hv' hv hc' hc newDart ι himage hflip hvertι hpos harcs F hinterior
          (ih (Fintype.card C'.D) hsmall C' rfl v' Q' hv' hc')
      · have hdim := cycleSpace_finrank_connected C.map
          (C.map.isConnected_of_eqvGen hc) ⟨C.rootDart⟩
        have htree : C.map.numEdges = C.map.numVertices - 1 := by omega
        exact C.common_face_orbit_unique_and_eulerChar_eq_two_of_tree v Q hv hc htree
  exact H (Fintype.card B.D) B rfl vert P hvert hconn

end D39FiniteBall
end DirectedDistances.PlanarMap
end
