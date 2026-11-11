/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarBoundaryWellDefined
public import DirectedDistances.PlanarMap.FiniteBoundaryDecomposition
public import DirectedDistances.PlanarMap.OuterFaceIncidence
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Intrinsic outer decomposition for finite bipolar maps -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The intrinsic finite-map conditions in Definition 1.9, expressed through
the source and sink fields of the directed-map carrier. Helper toward -/
def HasIntrinsicBipolarBoundary (M : DirectedMapWithMissing D) (ℓ r : ℕ) : Prop :=
  M.toCombinatorialMap.IsPlanar ∧ M.IsAcyclic ∧ (∀ d, ¬ M.missing d) ∧
    ∃ s t : MapVertex M,
      (¬ ∃ u, M.directedStep u s) ∧
      (∀ v, (¬ ∃ u, M.directedStep u v) → v = s) ∧
      (¬ ∃ w, M.directedStep t w) ∧
      (∀ v, (¬ ∃ w, M.directedStep v w) → v = t) ∧
      (∃ d, M.IsOuter d ∧ dartTailVertex M d = s) ∧
      (∃ d, M.IsOuter d ∧ dartTailVertex M d = t) ∧
      s ≠ t ∧ ℓ = Nat.card {d // d ∈ M.ulDarts} ∧
        r = Nat.card {d // d ∈ M.lrDarts}

private theorem tail_at_source (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (s : MapVertex M)
    (isSource : ¬ ∃ u, M.directedStep u s) {d : D}
    (hd : dartTailVertex M d = s) : M.tail d := by
  classical
  by_contra hnot
  have hinv : M.tail (M.edgeInv d) := by
    by_contra hinv
    exact hnot ((M.tail_iff d (noMissing d)).mpr hinv)
  have hhead : dartHeadVertex M (M.edgeInv d) = dartTailVertex M d := by
    simp [dartHeadVertex, dartTailVertex, M.edgeInv_invol]
  exact isSource ⟨dartTailVertex M (M.edgeInv d), M.edgeInv d,
    noMissing _, hinv, rfl, hhead.trans hd⟩

private theorem not_tail_at_sink (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (t : MapVertex M)
    (isSink : ¬ ∃ w, M.directedStep t w) {d : D}
    (hd : dartTailVertex M d = t) : ¬ M.tail d := by
  intro htail
  exact isSink ⟨dartHeadVertex M d, d, noMissing d, htail, hd, rfl⟩

/-- If the two poles lie on the external face, its cyclic boundary has a
non-tail-to-tail switch at the source and a tail-to-non-tail switch at the
This establishes the two pole switches, before the global Euler count that
rules out any additional switch. -/
theorem outerFace_switches_at_poles
    (M : DirectedMapWithMissing D) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (_hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ a b, M.IsOuter a ∧ M.IsOuter b ∧
      M.tail a ≠ M.tail (M.toCombinatorialMap.faceSucc a) ∧
      M.tail b ≠ M.tail (M.toCombinatorialMap.faceSucc b) ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc b) = t ∧ a ≠ b := by
  obtain ⟨dS, hdSouter, hdSvertex⟩ := hs
  obtain ⟨dT, hdTouter, hdTvertex⟩ := ht
  let a := M.toCombinatorialMap.faceSucc.symm dS
  let b := M.toCombinatorialMap.faceSucc.symm dT
  have hfa : M.toCombinatorialMap.faceSucc a = dS := by
    simp [a]
  have hfb : M.toCombinatorialMap.faceSucc b = dT := by
    simp [b]
  have haOuter : M.IsOuter a := by
    change M.toCombinatorialMap.faceSucc.SameCycle M.outer a
    have hstep : M.toCombinatorialMap.faceSucc.SameCycle dS a :=
      ⟨-1, by simp [a]⟩
    exact hdSouter.trans hstep
  have hbOuter : M.IsOuter b := by
    change M.toCombinatorialMap.faceSucc.SameCycle M.outer b
    have hstep : M.toCombinatorialMap.faceSucc.SameCycle dT b :=
      ⟨-1, by simp [b]⟩
    exact hdTouter.trans hstep
  have htailS : M.tail dS := tail_at_source M noMissing s isSource hdSvertex
  have hheadA : dartHeadVertex M a = s := by
    rw [dartHeadVertex_eq_tailVertex_faceSucc]
    rw [hfa, hdSvertex]
  have hnotTailA : ¬ M.tail a := by
    intro htail
    exact isSource ⟨dartTailVertex M a, a, noMissing a, htail, rfl, hheadA⟩
  have hnotTailT : ¬ M.tail dT := not_tail_at_sink M noMissing t isSink hdTvertex
  have htailB : M.tail b := by
    by_contra hnot
    have hinv : M.tail (M.edgeInv b) := by
      by_contra hinv
      exact hnot ((M.tail_iff b (noMissing b)).mpr hinv)
    have hstart : dartTailVertex M (M.edgeInv b) = t := by
      have hinc := dartHeadVertex_eq_tailVertex_faceSucc M b
      rw [hfb] at hinc
      have hhead : dartHeadVertex M b = dartTailVertex M dT := hinc
      simpa [dartHeadVertex, dartTailVertex, M.edgeInv_invol] using hhead.trans hdTvertex
    exact isSink ⟨dartHeadVertex M (M.edgeInv b), M.edgeInv b,
      noMissing _, hinv, hstart, rfl⟩
  have hab : a ≠ b := by
    intro h
    have hEq : dS = dT := by rw [← hfa, h, hfb]
    exact hnotTailT (hEq ▸ htailS)
  refine ⟨a, b, haOuter, hbOuter, ?_, ?_, ?_, ?_, hab⟩
  · rw [hfa]
    exact fun h => hnotTailA (h.symm ▸ htailS)
  · rw [hfb]
    exact fun h => hnotTailT (h ▸ htailB)
  · simpa [hfa] using hdSvertex
  · simpa [hfb] using hdTvertex

/-- A dart index is an outer-face switch when its orientation differs from
that of its successor around the external face. Helper toward Definition 1.9 -/
@[expose] def IsOuterFaceSwitch (M : DirectedMapWithMissing D) (d : D) : Prop :=
  M.tail d ≠ M.tail (M.toCombinatorialMap.faceSucc d)

private def rotationSwitch (M : DirectedMapWithMissing D) (d : D) : Prop :=
  M.tail d ≠ M.tail (M.rot.symm d)

omit [DecidableEq D] in
private theorem exists_cycle_transition (p : Equiv.Perm D) (P : D → Prop)
    {x y : D} (hxy : p.SameCycle x y) (hx : P x) (hy : ¬ P y) :
    ∃ z, p.SameCycle x z ∧ P z ∧ ¬ P (p z) := by
  classical
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hsegment : ∀ n, ¬ P ((p ^ n) x) →
      ∃ k < n, P ((p ^ k) x) ∧ ¬ P ((p ^ (k + 1)) x) := by
    intro n
    induction n with
    | zero => intro h; exact (h hx).elim
    | succ n ih =>
        intro h
        by_cases hm : P ((p ^ n) x)
        · exact ⟨n, Nat.lt_succ_self n, hm, h⟩
        · obtain ⟨k, hk, h₁, h₂⟩ := ih hm
          exact ⟨k, by omega, h₁, h₂⟩
  obtain ⟨k, _, h₁, h₂⟩ := hsegment n (hn ▸ hy)
  refine ⟨(p ^ k) x, ?_, h₁, ?_⟩
  · exact ⟨(k : ℤ), by simp⟩
  · simpa only [pow_succ', Equiv.Perm.mul_apply] using h₂

private theorem cycle_transition_card_ge_two (p : Equiv.Perm D) (P : D → Prop)
    {x y : D} (hxy : p.SameCycle x y) (hx : P x) (hy : ¬ P y) :
    2 ≤ Nat.card {d : D // p.SameCycle x d ∧ P d ≠ P (p d)} := by
  classical
  obtain ⟨a, ha, hPa, hPpa⟩ := exists_cycle_transition p P hxy hx hy
  obtain ⟨b, hb, hPb, hPpb⟩ := exists_cycle_transition p (fun d => ¬ P d)
    hxy.symm hy (by simpa only [not_not] using hx)
  let a' : {d : D // p.SameCycle x d ∧ P d ≠ P (p d)} :=
    ⟨a, ha, fun h => hPpa (h ▸ hPa)⟩
  let b' : {d : D // p.SameCycle x d ∧ P d ≠ P (p d)} :=
    ⟨b, hxy.trans hb, fun h => hPpb (h ▸ hPb)⟩
  have hne : a' ≠ b' := by
    intro h
    have hab : a = b := congrArg Subtype.val h
    exact hPb (hab ▸ hPa)
  have hcard := Finset.card_le_card
    (Finset.subset_univ ({a', b'} : Finset {d : D //
      p.SameCycle x d ∧ P d ≠ P (p d)}))
  simpa only [Finset.card_pair hne, Finset.card_univ, Nat.card_eq_fintype_card]
    using hcard

omit [DecidableEq D] in
private theorem card_fibers {α : Type*} [Fintype α] [DecidableEq α]
    (f : D → α) (P : D → Prop) :
    Nat.card {d : D // P d} =
      ∑ a : α, Nat.card {d : D // f d = a ∧ P d} := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := Finset.univ.filter P) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have hleft : Nat.card {d : D // P d} = (Finset.univ.filter P).card :=
    Nat.subtype_card _ (by intro d; simp)
  rw [hleft, h]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.subtype_card (Finset.univ.filter (fun d => f d = a ∧ P d))
    (by intro d; simp)]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

private theorem face_forward (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (d : D) (h : M.tail d) :
    M.directedStep (dartTailVertex M d)
      (dartTailVertex M (M.toCombinatorialMap.faceSucc d)) := by
  refine ⟨d, noMissing d, h, rfl, ?_⟩
  exact dartHeadVertex_eq_tailVertex_faceSucc M d

private theorem face_backward (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (d : D) (h : ¬ M.tail d) :
    M.directedStep (dartTailVertex M (M.toCombinatorialMap.faceSucc d))
      (dartTailVertex M d) := by
  have hinv : M.tail (M.edgeInv d) := by
    by_contra hn
    exact h ((M.tail_iff d (noMissing d)).mpr hn)
  refine ⟨M.edgeInv d, noMissing _, hinv,
    dartHeadVertex_eq_tailVertex_faceSucc M d, ?_⟩
  simp only [dartTailVertex, M.edgeInv_invol]

private theorem face_has_both_orientations (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (acyclic : M.IsAcyclic) (d : D) :
    (∃ e, M.toCombinatorialMap.faceSucc.SameCycle d e ∧ M.tail e) ∧
    (∃ e, M.toCombinatorialMap.faceSucc.SameCycle d e ∧ ¬ M.tail e) := by
  classical
  let p := M.toCombinatorialMap.faceSucc
  have hreturn : (p ^ orderOf p) d = d := by rw [pow_orderOf_eq_one]; rfl
  have hcycle (n : ℕ) : p.SameCycle d ((p ^ n) d) := ⟨(n : ℤ), by simp⟩
  constructor
  · by_contra h
    have hn (n : ℕ) : ¬ M.tail ((p ^ n) d) := by
      intro ht
      exact h ⟨(p ^ n) d, hcycle n, ht⟩
    have hpath : ∀ n, Relation.TransGen M.directedStep
        (dartTailVertex M ((p ^ (n + 1)) d)) (dartTailVertex M d) := by
      intro n
      induction n with
      | zero => exact Relation.TransGen.single (face_backward M noMissing d (hn 0))
      | succ n ih =>
          have hs := face_backward M noMissing ((p ^ (n + 1)) d) (hn (n + 1))
          have hs' : M.directedStep
              (dartTailVertex M ((p ^ (n + 1 + 1)) d))
              (dartTailVertex M ((p ^ (n + 1)) d)) := by
            simpa only [pow_succ', Equiv.Perm.mul_apply] using hs
          exact Relation.TransGen.head hs' ih
    have hp := hpath (orderOf p - 1)
    rw [Nat.sub_add_cancel (orderOf_pos p), hreturn] at hp
    exact acyclic _ hp
  · by_contra h
    have hn (n : ℕ) : M.tail ((p ^ n) d) := by
      by_contra ht
      exact h ⟨(p ^ n) d, hcycle n, ht⟩
    have hpath : ∀ n, Relation.TransGen M.directedStep
        (dartTailVertex M d) (dartTailVertex M ((p ^ (n + 1)) d)) := by
      intro n
      induction n with
      | zero => exact Relation.TransGen.single (face_forward M noMissing d (hn 0))
      | succ n ih =>
          have hs := face_forward M noMissing ((p ^ (n + 1)) d) (hn (n + 1))
          have hs' : M.directedStep
              (dartTailVertex M ((p ^ (n + 1)) d))
              (dartTailVertex M ((p ^ (n + 1 + 1)) d)) := by
            simpa only [pow_succ', Equiv.Perm.mul_apply] using hs
          exact ih.tail hs'
    have hp := hpath (orderOf p - 1)
    rw [Nat.sub_add_cancel (orderOf_pos p), hreturn] at hp
    exact acyclic _ hp

private theorem face_transition_card_ge_two (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (acyclic : M.IsAcyclic)
    (q : CombinatorialMap.FaceQuotient M.toCombinatorialMap) :
    2 ≤ Nat.card {d : D //
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d = q ∧
        IsOuterFaceSwitch M d} := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  obtain ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ :=
    face_has_both_orientations M noMissing acyclic d
  have h := cycle_transition_card_ge_two M.toCombinatorialMap.faceSucc M.tail
    (ha.symm.trans hb) hPa hPb
  have he := Equiv.subtypeEquivRight
    (p := fun e => M.toCombinatorialMap.faceSucc.SameCycle a e ∧
      M.tail e ≠ M.tail (M.toCombinatorialMap.faceSucc e))
    (q := fun e =>
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) e =
        Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d ∧
        IsOuterFaceSwitch M e) (fun e => by
      constructor
      · rintro ⟨he, hP⟩
        exact ⟨Quotient.sound (ha.trans he).symm, hP⟩
      · rintro ⟨he, hP⟩
        exact ⟨ha.symm.trans (Quotient.exact he).symm, hP⟩)
  rwa [Nat.card_congr he] at h

private theorem source_and_sink_orientations
    (M : DirectedMapWithMissing D) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    {v : MapVertex M} (hs : v ≠ s) (ht : v ≠ t) :
    (∃ a, dartTailVertex M a = v ∧ M.tail a) ∧
    (∃ b, dartTailVertex M b = v ∧ ¬ M.tail b) := by
  classical
  have hout : ∃ w, M.directedStep v w := by
    by_contra h
    exact ht (sink_unique v h)
  have hin : ∃ w, M.directedStep w v := by
    by_contra h
    exact hs (source_unique v h)
  obtain ⟨w, a, _, ha, hav, _⟩ := hout
  obtain ⟨w', b, _, hb, _, hbv⟩ := hin
  exact ⟨⟨a, hav, ha⟩, ⟨M.edgeInv b, hbv,
    (M.tail_iff b (noMissing b)).mp hb⟩⟩

private theorem rotation_transition_card_ge_two (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    {v : MapVertex M} (hs : v ≠ s) (ht : v ≠ t) :
    2 ≤ Nat.card {d : D // dartTailVertex M d = v ∧ rotationSwitch M d} := by
  obtain ⟨⟨a, hav, ha⟩, ⟨b, hbv, hb⟩⟩ :=
    source_and_sink_orientations M noMissing source_unique sink_unique hs ht
  have hcycle : Equiv.Perm.SameCycle M.rot.symm a b :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hav.trans hbv.symm))
  have h := cycle_transition_card_ge_two M.rot.symm M.tail hcycle ha hb
  have he := Equiv.subtypeEquivRight
    (p := fun e => Equiv.Perm.SameCycle M.rot.symm a e ∧
      M.tail e ≠ M.tail (M.rot.symm e))
    (q := fun e => dartTailVertex M e = v ∧ rotationSwitch M e) (fun e => by
      constructor
      · rintro ⟨he, hP⟩
        exact ⟨(Quotient.sound (Equiv.Perm.sameCycle_inv.mp he).symm).trans hav, hP⟩
      · rintro ⟨he, hP⟩
        exact ⟨Equiv.Perm.sameCycle_inv.mpr
          (Quotient.exact (hav.trans he.symm)), hP⟩)
  rwa [Nat.card_congr he] at h

private theorem transition_partition (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) :
    Nat.card {d : D // IsOuterFaceSwitch M d} +
      Nat.card {d : D // rotationSwitch M d} = Fintype.card D := by
  classical
  let F : D → Prop := fun d => IsOuterFaceSwitch M d
  let V : D → Prop := fun d => rotationSwitch M d
  have hcorner (d : D) : V (M.edgeInv d) ↔ ¬ F d := by
    have hi := M.tail_iff d (noMissing d)
    dsimp [V, F, IsOuterFaceSwitch, rotationSwitch, CombinatorialMap.faceSucc]
    by_cases hd : M.tail d <;>
      by_cases he : M.tail (M.edgeInv d) <;>
      by_cases hf : M.tail (M.rot.symm (M.edgeInv d)) <;>
      simp_all
  let e : {d : D // V d} ≃ {d : D // ¬ F d} := {
    toFun := fun d => ⟨M.edgeInv d.1, (hcorner _).mp (by
      simpa only [M.edgeInv_invol] using d.2)⟩
    invFun := fun d => ⟨M.edgeInv d.1, (hcorner _).mpr d.2⟩
    left_inv := by intro d; apply Subtype.ext; exact M.edgeInv_invol d.1
    right_inv := by intro d; apply Subtype.ext; exact M.edgeInv_invol d.1 }
  change Nat.card {d : D // F d} + Nat.card {d : D // V d} = _
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl F]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le F)

private theorem face_switch_total_lower (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) (acyclic : M.IsAcyclic) :
    2 * M.toCombinatorialMap.numFaces ≤
      Nat.card {d : D // IsOuterFaceSwitch M d} := by
  classical
  rw [card_fibers (fun d => Quotient.mk
    (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d)
    (IsOuterFaceSwitch M)]
  calc
    2 * M.toCombinatorialMap.numFaces =
        ∑ _q : CombinatorialMap.FaceQuotient M.toCombinatorialMap, (2 : ℕ) := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
          exact Nat.mul_comm _ _
    _ ≤ _ := Finset.sum_le_sum
      (fun q _ => face_transition_card_ge_two M noMissing acyclic q)

private theorem rot_inv_vertex (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.rot.symm d) = dartTailVertex M d := by
  apply Quotient.sound
  exact ⟨1, by simp⟩

private theorem rotation_switch_total_lower (M : DirectedMapWithMissing D)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t) :
    2 * (M.toCombinatorialMap.numVertices - 2) ≤
      Nat.card {d : D // rotationSwitch M d} := by
  classical
  let f : MapVertex M → ℕ := fun w =>
    Nat.card {d : D // dartTailVertex M d = w ∧ rotationSwitch M d}
  let nonpoles : Finset (MapVertex M) :=
    (Finset.univ.erase s).erase t
  have hsZero : f s = 0 := by
    have hempty : IsEmpty {d : D // dartTailVertex M d = s ∧ rotationSwitch M d} :=
      ⟨fun d => d.2.2 (propext ⟨
        fun _ => tail_at_source M noMissing s isSource
          ((rot_inv_vertex M d.1).trans d.2.1),
        fun _ => tail_at_source M noMissing s isSource d.2.1⟩)⟩
    have hcard : Nat.card {d : D // dartTailVertex M d = s ∧ rotationSwitch M d} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
      exact hempty
    simp [f]
  have htZero : f t = 0 := by
    have hempty : IsEmpty {d : D // dartTailVertex M d = t ∧ rotationSwitch M d} :=
      ⟨fun d => d.2.2 (propext ⟨
        fun htail => (not_tail_at_sink M noMissing t isSink d.2.1 htail).elim,
        fun htail => (not_tail_at_sink M noMissing t isSink
          ((rot_inv_vertex M d.1).trans d.2.1) htail).elim⟩)⟩
    have hcard : Nat.card {d : D // dartTailVertex M d = t ∧ rotationSwitch M d} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
      exact hempty
    simp [f]
  have htmem : t ∈ Finset.univ.erase s :=
    Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩
  have hcard : nonpoles.card = M.toCombinatorialMap.numVertices - 2 := by
    have hcard' : nonpoles.card = Fintype.card (MapVertex M) - 2 := by
      rw [Finset.card_erase_of_mem htmem,
        Finset.card_erase_of_mem (Finset.mem_univ s)]
      simp only [Finset.card_univ]
      omega
    simpa [CombinatorialMap.numVertices, MapVertex] using hcard'
  have hge : ∀ w ∈ nonpoles, 2 ≤ f w := by
    intro w hw
    have hws : w ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    have hwt : w ≠ t := (Finset.mem_erase.mp hw).1
    exact rotation_transition_card_ge_two M noMissing
      source_unique sink_unique hws hwt
  have hsumCard : Nat.card {d : D // rotationSwitch M d} =
      ∑ w : MapVertex M, f w := by
    simpa [f] using card_fibers (dartTailVertex M) (rotationSwitch M)
  have hsumLower : 2 * nonpoles.card ≤ ∑ w ∈ nonpoles, f w := by
    calc
      2 * nonpoles.card = ∑ _w ∈ nonpoles, (2 : ℕ) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl)]
        exact Nat.mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum (fun w hw => hge w hw)
  calc
    2 * (M.toCombinatorialMap.numVertices - 2) = 2 * nonpoles.card := by rw [hcard]
    _ ≤ ∑ w ∈ nonpoles, f w := hsumLower
    _ ≤ ∑ w : MapVertex M, f w :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = Nat.card {d : D // rotationSwitch M d} := hsumCard.symm

private theorem outer_face_fiber_switch_card_eq_two
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar)
    (acyclic : M.IsAcyclic) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (q : CombinatorialMap.FaceQuotient M.toCombinatorialMap) :
    Nat.card {d : D //
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d = q ∧
        IsOuterFaceSwitch M d} = 2 := by
  classical
  let F : ℕ := M.toCombinatorialMap.numFaces
  let V : ℕ := M.toCombinatorialMap.numVertices
  let E : ℕ := M.toCombinatorialMap.numEdges
  have hpart := transition_partition M noMissing
  have hF := face_switch_total_lower M noMissing acyclic
  have hV := rotation_switch_total_lower M noMissing isSource source_unique
    isSink sink_unique hst
  have hEuler : (V : ℤ) - E + F = 2 := by
    simpa [V, E, F, CombinatorialMap.eulerChar] using planar.2
  have hEulerNat : V + F = E + 2 := by omega
  have hD : 2 * E = Fintype.card D := by
    simpa [E] using M.toCombinatorialMap.two_mul_numEdges
  have hVpos : 2 ≤ V := by
    have hpair : ({s, t} : Finset (MapVertex M)).card = 2 := by simp [hst]
    have hle : ({s, t} : Finset (MapVertex M)).card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    have hpos : 2 ≤ Fintype.card (MapVertex M) := by
      calc
        2 = ({s, t} : Finset (MapVertex M)).card := hpair.symm
        _ ≤ Finset.univ.card := hle
        _ = Fintype.card (MapVertex M) := Finset.card_univ.symm
    simpa [V, CombinatorialMap.numVertices] using hpos
  have hsum : 2 * F + 2 * (V - 2) = Fintype.card D := by
    rw [← hD]
    omega
  have hfaceTotal : Nat.card {d : D // IsOuterFaceSwitch M d} = 2 * F := by
    let A := Nat.card {d : D // IsOuterFaceSwitch M d}
    let B := Nat.card {d : D // rotationSwitch M d}
    let x := 2 * F
    let y := 2 * (V - 2)
    have hcards : A + B = x + y := by
      simpa [A, B, x, y] using
        (hpart.trans hsum.symm)
    have hF' : x ≤ A := by simpa [A, x] using hF
    have hV' : y ≤ B := by simpa [B, y] using hV
    have hupper : A + y ≤ x + y := by
      calc
        A + y ≤ A + B := Nat.add_le_add_left hV' A
        _ = x + y := hcards
    have hA : A = x := by omega
    simpa [A, x] using hA
  let faceFiber : CombinatorialMap.FaceQuotient M.toCombinatorialMap → ℕ :=
    fun x => Nat.card {d : D //
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d = x ∧
        IsOuterFaceSwitch M d}
  have htotal : ∑ x : CombinatorialMap.FaceQuotient M.toCombinatorialMap,
      faceFiber x = 2 * F := by
    calc
      _ = Nat.card {d : D // IsOuterFaceSwitch M d} :=
        (card_fibers (fun d => Quotient.mk
          (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d)
          (IsOuterFaceSwitch M)).symm
      _ = 2 * F := hfaceTotal
  have hlocal : ∀ x, 2 ≤ faceFiber x :=
    fun x => face_transition_card_ge_two M noMissing acyclic x
  by_contra hne
  have hnot : faceFiber q ≠ 2 := by simpa [faceFiber] using hne
  have hqge := hlocal q
  have hlarge : 3 ≤ faceFiber q := by omega
  let rest := Finset.univ.erase q
  have hrest : 2 * rest.card ≤ ∑ x ∈ rest, faceFiber x := by
    calc
      2 * rest.card = ∑ _x ∈ rest, (2 : ℕ) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl)]
        exact Nat.mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hlocal x)
  have hsplit : faceFiber q + ∑ x ∈ rest, faceFiber x =
      ∑ x : CombinatorialMap.FaceQuotient M.toCombinatorialMap, faceFiber x := by
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := q) faceFiber
      (Finset.mem_univ q)]
    exact add_comm _ _
  have hFpos : 0 < F := by
    have : 0 < Fintype.card (CombinatorialMap.FaceQuotient M.toCombinatorialMap) :=
      Fintype.card_pos_iff.mpr ⟨q⟩
    simpa [F, CombinatorialMap.numFaces] using this
  have hcardRest' : rest.card = Fintype.card
      (CombinatorialMap.FaceQuotient M.toCombinatorialMap) - 1 := by
    simp [rest]
  have hFpos' : 0 < Fintype.card
      (CombinatorialMap.FaceQuotient M.toCombinatorialMap) := by
    exact Fintype.card_pos_iff.mpr ⟨q⟩
  have hcardRest : rest.card + 1 = F := by
    have hcard := hcardRest'
    have hFone : 1 ≤ Fintype.card
        (CombinatorialMap.FaceQuotient M.toCombinatorialMap) := hFpos'
    change rest.card + 1 = Fintype.card
      (CombinatorialMap.FaceQuotient M.toCombinatorialMap)
    rw [hcard]
    omega
  have hsplit' : faceFiber q + ∑ x ∈ rest, faceFiber x =
      2 * (rest.card + 1) := by
    calc
      _ = 2 * F := by rw [hsplit, htotal]
      _ = 2 * (rest.card + 1) := by rw [← hcardRest]
  have hbig : 2 * rest.card + 3 ≤
      faceFiber q + ∑ x ∈ rest, faceFiber x := by omega
  rw [hsplit'] at hbig
  omega

private def outerFaceSwitchFiberEquiv (M : DirectedMapWithMissing D) :
    {d : D //
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d =
        Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) M.outer ∧
        IsOuterFaceSwitch M d} ≃
      {d : D // M.IsOuter d ∧ IsOuterFaceSwitch M d} where
  toFun d := by
    refine ⟨d.1, ?_, d.2.2⟩
    change M.toCombinatorialMap.faceSucc.SameCycle M.outer d.1
    exact (Quotient.exact d.2.1).symm
  invFun d := by
    refine ⟨d.1, ?_, d.2.2⟩
    apply Quotient.sound
    exact d.2.1.symm
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- The external face of a finite acyclic bipolar planar map has exactly two
orientation switches. Helper toward Definition 1.9 -/
theorem outerFace_switch_card_eq_two
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar)
    (acyclic : M.IsAcyclic) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t) :
    Nat.card {d : D // M.IsOuter d ∧ IsOuterFaceSwitch M d} = 2 := by
  let q : CombinatorialMap.FaceQuotient M.toCombinatorialMap :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) M.outer
  have h := outer_face_fiber_switch_card_eq_two M planar acyclic noMissing
    isSource source_unique isSink sink_unique hst q
  calc
    Nat.card {d : D // M.IsOuter d ∧ IsOuterFaceSwitch M d} =
        Nat.card {d : D //
          Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.faceSucc) d = q ∧
            IsOuterFaceSwitch M d} := Nat.card_congr (outerFaceSwitchFiberEquiv M).symm
    _ = 2 := by simpa [q] using h

/-- There is exactly one outer-face orientation switch at the source and one
at the sink, and there are no other switches on the external face. Helper -/
theorem outerFace_has_exactly_two_switches_at_poles
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar)
    (acyclic : M.IsAcyclic) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    (∃! a, M.IsOuter a ∧ IsOuterFaceSwitch M a ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s) ∧
    (∃! b, M.IsOuter b ∧ IsOuterFaceSwitch M b ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc b) = t) ∧
    (∀ d, M.IsOuter d → IsOuterFaceSwitch M d →
      dartTailVertex M (M.toCombinatorialMap.faceSucc d) = s ∨
        dartTailVertex M (M.toCombinatorialMap.faceSucc d) = t) := by
  classical
  obtain ⟨a, b, haOuter, hbOuter, haSwitch, hbSwitch, haVertex, hbVertex, hab⟩ :=
    outerFace_switches_at_poles M noMissing isSource isSink hst hs ht
  have hcard := outerFace_switch_card_eq_two M planar acyclic noMissing
    isSource source_unique isSink sink_unique hst
  let S : Finset D := Finset.univ.filter fun d =>
    M.IsOuter d ∧ IsOuterFaceSwitch M d
  have hScard : S.card = 2 := by
    have h' := hcard
    rw [Nat.subtype_card S (by intro d; simp [S])] at h'
    exact h'
  have haMem : a ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨haOuter, haSwitch⟩
  have hbMem : b ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hbOuter, hbSwitch⟩
  have hS : S = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact haMem
      · exact hbMem
    · rw [Finset.card_pair hab, hScard]
  have hsource : ∃! d, M.IsOuter d ∧ IsOuterFaceSwitch M d ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc d) = s := by
    refine ⟨a, ⟨haOuter, haSwitch, haVertex⟩, ?_⟩
    intro d hd
    have hdS : d ∈ S := by simp [S, hd.1, hd.2.1]
    rw [hS] at hdS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdS
    rcases hdS with hda | hdb
    · exact hda
    · subst d
      exact (hst (hd.2.2.symm.trans hbVertex)).elim
  have hsink : ∃! d, M.IsOuter d ∧ IsOuterFaceSwitch M d ∧
      dartTailVertex M (M.toCombinatorialMap.faceSucc d) = t := by
    refine ⟨b, ⟨hbOuter, hbSwitch, hbVertex⟩, ?_⟩
    intro d hd
    have hdS : d ∈ S := by simp [S, hd.1, hd.2.1]
    rw [hS] at hdS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdS
    rcases hdS with hda | hdb
    · subst d
      exact (hst (haVertex.symm.trans hd.2.2)).elim
    · exact hdb
  refine ⟨hsource, hsink, ?_⟩
  intro d hdOuter hdSwitch
  have hdS : d ∈ S := by simp [S, hdOuter, hdSwitch]
  rw [hS] at hdS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdS
  rcases hdS with rfl | rfl
  · exact Or.inl haVertex
  · exact Or.inr hbVertex

/-- Outer incidence of both poles supplies at least one dart in each of the
two directed outer boundary sets. Helper toward Definition 1.9 -/
theorem outer_pole_dart_cards_pos
    (M : DirectedMapWithMissing D) (noMissing : ∀ d, ¬ M.missing d)
    {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    1 ≤ Nat.card {d // d ∈ M.ulDarts} ∧
      1 ≤ Nat.card {d // d ∈ M.lrDarts} := by
  classical
  obtain ⟨dS, hdSouter, hdSvertex⟩ := hs
  obtain ⟨dT, hdTouter, hdTvertex⟩ := ht
  have hdStail : M.tail dS := tail_at_source M noMissing s isSource hdSvertex
  have hSmem : dS ∈ M.ulDarts := ⟨noMissing dS, hdStail, hdSouter⟩
  have hdTnotTail : ¬ M.tail dT := not_tail_at_sink M noMissing t isSink hdTvertex
  have hTmem : dT ∈ M.lrDarts := ⟨noMissing dT, hdTnotTail, hdTouter⟩
  have hSpos : 0 < Nat.card {d // d ∈ M.ulDarts} := by
    have hnonempty : Nonempty {d // d ∈ M.ulDarts} := ⟨⟨dS, hSmem⟩⟩
    have hcard : 0 < Fintype.card {d // d ∈ M.ulDarts} :=
      Fintype.card_pos_iff.mpr hnonempty
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hTpos : 0 < Nat.card {d // d ∈ M.lrDarts} := by
    have hnonempty : Nonempty {d // d ∈ M.lrDarts} := ⟨⟨dT, hTmem⟩⟩
    have hcard : 0 < Fintype.card {d // d ∈ M.lrDarts} :=
      Fintype.card_pos_iff.mpr hnonempty
    simpa only [Nat.card_eq_fintype_card] using hcard
  omega

/-- The intrinsic characterization forces both directed boundary lengths to
be positive, with the endpoint case supplied by the pole incidences. Helper -/
theorem HasIntrinsicBipolarBoundary.lengths_pos
    (M : DirectedMapWithMissing D) (h : HasIntrinsicBipolarBoundary M ℓ r) :
    1 ≤ ℓ ∧ 1 ≤ r := by
  obtain ⟨_, _, noMissing, s, t, isSource, _, isSink, _, hs, ht, _, hℓ, hr⟩ := h
  have hcards := outer_pole_dart_cards_pos M noMissing isSource isSink hs ht
  exact ⟨by omega, by omega⟩

namespace BipolarMapWithBoundaryBase

private theorem source_ne_sink (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.source ≠ B.sink := by
  intro hst
  have hpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact Nat.zero_lt_of_lt B.left_length_pos
  let i : Fin B.leftPath.darts.length := ⟨0, hpos⟩
  have hstep := B.leftPath.edge_step i
  have hstart : dartTailVertex B.map (B.leftPath.darts.get i) = B.source := by
    calc
      dartTailVertex B.map (B.leftPath.darts.get i) =
          B.leftPath.vertices.get ⟨0, by rw [B.leftPath.vertices_length]; omega⟩ :=
        hstep.2.2.1.symm
      _ = B.source := B.leftPath.start_vertex
  have hstart' : dartTailVertex B.map (B.leftPath.darts.get i) = B.sink :=
    hstart.trans hst
  apply B.isSink
  exact ⟨dartHeadVertex B.map (B.leftPath.darts.get i),
    B.leftPath.darts.get i, B.noMissingDarts _, hstep.2.1, hstart', rfl⟩

end BipolarMapWithBoundaryBase

/-- Every combinatorial bipolar map with boundary satisfies the intrinsic
conditions, including the exact cardinalities of its two outer dart sets. -/
theorem isBipolarMapWithBoundary_implies_intrinsic
    (M : DirectedMapWithMissing D) (h : IsBipolarMapWithBoundary M ℓ r) :
    HasIntrinsicBipolarBoundary M ℓ r := by
  obtain ⟨B, hBM⟩ := h
  cases hBM
  obtain ⟨hsourceOuter, hsinkOuter⟩ :=
    source_and_sink_are_tails_of_outer_darts B
  refine ⟨B.planar, B.acyclic, B.noMissingDarts, B.source, B.sink,
    B.isSource, B.source_unique, B.isSink, B.sink_unique,
    hsourceOuter, hsinkOuter, B.source_ne_sink,
    B.left_length_eq_card_ulDarts, B.right_length_eq_card_lrDarts⟩

/-- The distinguished external face has a nonempty exact cyclic word obtained
by iterating `faceSucc` from its marked dart. Helper toward Definition 1.9 -/
theorem exists_outer_face_word
    (M : DirectedMapWithMissing D) {s t : MapVertex M} (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ W : NonemptyWord D,
      W.letters = Equiv.Perm.toList M.toCombinatorialMap.faceSucc M.outer ∧
      IsOuterCycle M W := by
  classical
  obtain ⟨dS, hdSouter, hdSs⟩ := hs
  obtain ⟨dT, hdTouter, hdTt⟩ := ht
  have hdne : dS ≠ dT := by
    intro h
    subst dT
    exact hst (hdSs.symm.trans hdTt)
  let p := M.toCombinatorialMap.faceSucc
  have hfix : p M.outer ≠ M.outer := by
    intro hfix
    obtain ⟨ks, hks⟩ := hdSouter.exists_nat_pow_eq
    obtain ⟨kt, hkt⟩ := hdTouter.exists_nat_pow_eq
    have hpow (k : ℕ) : (p ^ k) M.outer = M.outer := by
      induction k with
      | zero => simp
      | succ k ih => simp [pow_succ', ih, hfix]
    rw [hpow ks] at hks
    rw [hpow kt] at hkt
    exact hdne (hks.symm.trans hkt)
  have hsupport : M.outer ∈ p.support := Equiv.Perm.mem_support.mpr hfix
  let W : NonemptyWord D := ⟨Equiv.Perm.toList p M.outer, by
    intro hnil
    have hlen : (Equiv.Perm.toList p M.outer).length = 0 := by simp [hnil]
    rw [Equiv.Perm.length_toList] at hlen
    have hpos := Equiv.Perm.length_toList_pos_of_mem_support p M.outer hsupport
    rw [Equiv.Perm.length_toList] at hpos
    omega,
    Equiv.Perm.nodup_toList p M.outer⟩
  refine ⟨W, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    change M.IsOuter d
    change d ∈ Equiv.Perm.toList p M.outer at hd
    exact (Equiv.Perm.mem_toList_iff.mp hd).1
  · intro d hd
    change p.SameCycle M.outer d at hd
    change d ∈ Equiv.Perm.toList p M.outer
    rw [Equiv.Perm.mem_toList_iff]
    exact ⟨hd, hsupport⟩
  · intro d hd
    change p d = (Equiv.Perm.toList p M.outer).formPerm d
    have hcycle := (Equiv.Perm.mem_toList_iff.mp hd).1
    calc
      p d = p.cycleOf M.outer d := hcycle.cycleOf_apply.symm
      _ = (Equiv.Perm.toList p M.outer).formPerm d := by
        rw [Equiv.Perm.formPerm_toList]

private theorem isOuterCycle_rotate (M : DirectedMapWithMissing D)
    (W : NonemptyWord D) (hW : IsOuterCycle M W) (k : ℕ) :
    IsOuterCycle M ⟨W.letters.rotate k, by
      intro hnil
      apply W.nonempty
      apply List.length_eq_zero_iff.mp
      have hlen : (W.letters.rotate k).length = 0 := by simp [hnil]
      simpa only [List.length_rotate] using hlen,
      by simpa using W.nodup⟩ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact hW.1 d (List.mem_rotate.mp hd)
  · intro d hd
    exact List.mem_rotate.mpr (hW.2.1 d hd)
  · intro d hd
    rw [List.formPerm_rotate W.letters W.nodup k]
    exact hW.2.2 d (List.mem_rotate.mp hd)

 /-- Classical Boolean indicator for a proposition-valued predicate, used to
split the finite outer word at its orientation change. Helper toward -/
noncomputable def propIndicator {α : Type*} (P : α → Prop) : α → Bool :=
  fun x => @decide (P x) (Classical.propDecidable (P x))

private theorem mem_takeWhile_true {α : Type*} (p : α → Bool) {xs : List α}
    {x : α} (hx : x ∈ xs.takeWhile p) : p x = true := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    cases hp : p a with
    | false => simp [List.takeWhile, hp] at hx
    | true =>
      simp only [List.takeWhile, hp, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp
      · exact ih hx

private theorem all_not_of_chain_head_not {α : Type*} {P : α → Prop}
    {xs : List α} (hchain : xs.IsChain (fun x y => P x ∨ ¬ P y))
    {a : α} (hhead : xs.head? = some a) (ha : ¬ P a) :
    ∀ x, x ∈ xs → ¬ P x := by
  revert a hhead ha
  induction xs with
  | nil => intro a hhead ha; simp at hhead
  | cons x xs ih =>
    intro a hhead ha
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst a
    cases xs with
    | nil =>
      intro y hy
      simp only [List.mem_singleton] at hy
      subst y
      exact ha
    | cons y ys =>
      have hc := List.isChain_cons_cons.mp hchain
      have hnotY : ¬ P y := hc.1.resolve_left ha
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ha
      · exact ih hc.2 rfl hnotY z (by simp [hz])

private theorem all_not_dropWhile_of_no_return {α : Type*} {P : α → Prop}
    {xs : List α} (hchain : xs.IsChain (fun x y => P x ∨ ¬ P y)) :
    ∀ x, x ∈ xs.dropWhile (propIndicator P) → ¬ P x := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro x hx
    by_cases ha : P a
    · have htail : xs.IsChain (fun x y => P x ∨ ¬ P y) := by
        cases xs with
        | nil => exact List.isChain_nil
        | cons b bs => exact (List.isChain_cons_cons.mp hchain).2
      have hpa : propIndicator P a = true := by simp [propIndicator, ha]
      simp only [List.dropWhile, hpa] at hx
      exact ih htail x hx
    · have hAll := all_not_of_chain_head_not hchain (by simp) ha
      have hpa : propIndicator P a = false := by simp [propIndicator, ha]
      simp only [List.dropWhile, hpa] at hx
      exact hAll x hx

/-- The outer word can be rotated to start at the outer dart leaving the
source. The rotation uses O1's unique source switch. Helper toward Definition -/
theorem exists_outer_face_word_starting_at_source
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar) (acyclic : M.IsAcyclic)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ W W' : NonemptyWord D, ∃ d,
      W.letters = Equiv.Perm.toList M.toCombinatorialMap.faceSucc M.outer ∧
      IsOuterCycle M W ∧ IsOuterCycle M W' ∧ W.letters ~r W'.letters ∧
      W'.letters.head? = some d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      (∃ a, M.IsOuter a ∧ IsOuterFaceSwitch M a ∧
        dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s ∧
        M.toCombinatorialMap.faceSucc a = d) := by
  classical
  let p := M.toCombinatorialMap.faceSucc
  obtain ⟨W, hWletters, hW⟩ := exists_outer_face_word M hst hs ht
  have hO1 := outerFace_has_exactly_two_switches_at_poles M planar acyclic noMissing
    isSource source_unique isSink sink_unique hst hs ht
  obtain ⟨⟨a, ⟨haOuter, haSwitch, haVertex⟩, _⟩, _, _⟩ := hO1
  let d := p a
  have hdOuter : M.IsOuter d := by
    change p.SameCycle M.outer d
    change p.SameCycle M.outer a at haOuter
    exact haOuter.trans ⟨1, by simp [d]⟩
  have hdVertex : dartTailVertex M d = s := by simpa [d, p] using haVertex
  have hdNotFixed : p d ≠ d := by
    intro hfixed
    have had : a = d := p.injective (by
      calc
        p a = d := rfl
        _ = p d := hfixed.symm)
    exact haSwitch (by simpa [d] using congrArg M.tail had)
  have hsupport : d ∈ p.support := Equiv.Perm.mem_support.mpr hdNotFixed
  have hcycle : p.SameCycle M.outer d := by
    change p.SameCycle M.outer a at haOuter
    change p.SameCycle M.outer d
    exact haOuter.trans ⟨1, by simp [d]⟩
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hrot : Equiv.Perm.toList p d =
      (Equiv.Perm.toList p M.outer).rotate k := by
    calc
      Equiv.Perm.toList p d = Equiv.Perm.toList p ((p ^ k) M.outer) := by rw [hk]
      _ = (Equiv.Perm.toList p M.outer).rotate k :=
        Equiv.Perm.toList_pow_apply_eq_rotate p M.outer k
  let W' : NonemptyWord D := ⟨W.letters.rotate k, by
    intro hnil
    apply W.nonempty
    apply List.length_eq_zero_iff.mp
    have hlen : (W.letters.rotate k).length = 0 := by simp [hnil]
    simpa only [List.length_rotate] using hlen,
    by simpa using W.nodup⟩
  have hW' : IsOuterCycle M W' := by
    simpa only [W', hWletters] using isOuterCycle_rotate M W hW k
  have hfirst : W'.letters.head? = some d := by
    change (W.letters.rotate k).head? = some d
    rw [hWletters, ← hrot]
    have hpos := Equiv.Perm.length_toList_pos_of_mem_support p d hsupport
    have hzero := Equiv.Perm.toList_getElem_zero p d hsupport
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    exact congrArg some hzero
  have htail : M.tail d := tail_at_source M noMissing s isSource hdVertex
  refine ⟨W, W', d, hWletters, hW, hW', ⟨k, rfl⟩, hfirst, htail, hdVertex,
    ⟨a, haOuter, haSwitch, haVertex, rfl⟩⟩

/-- O1 splits the source-started outer word into its maximal tail-oriented
initial block and its non-tail complementary block. The block sets enumerate
`ulDarts` and `lrDarts`, with the two junctions at the source and sink. -/
theorem outer_face_maximal_oriented_blocks
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar) (acyclic : M.IsAcyclic)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ W W' : NonemptyWord D, ∃ (d : D) (ul lr : List D),
      W.letters = Equiv.Perm.toList M.toCombinatorialMap.faceSucc M.outer ∧
      IsOuterCycle M W ∧ IsOuterCycle M W' ∧ W.letters ~r W'.letters ∧
      W'.letters.head? = some d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      (∃ a, M.IsOuter a ∧ IsOuterFaceSwitch M a ∧
        dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s ∧
        M.toCombinatorialMap.faceSucc a = d) ∧
      W'.letters = ul ++ lr ∧
      ul = W'.letters.takeWhile (propIndicator M.tail) ∧
      lr = W'.letters.dropWhile (propIndicator M.tail) ∧
      (∀ e, e ∈ ul → M.tail e) ∧ (∀ e, e ∈ lr → ¬ M.tail e) ∧
      EnumeratesSet ul M.ulDarts ∧ EnumeratesSet lr M.lrDarts ∧
      1 ≤ ul.length ∧ 1 ≤ lr.length := by
  classical
  obtain ⟨W, W', d, hWletters, hW, hW', hrotate, hfirst, htail, hdVertex,
      hsourceStep⟩ :=
    exists_outer_face_word_starting_at_source M planar acyclic noMissing
      isSource source_unique isSink sink_unique hst hs ht
  let p := M.toCombinatorialMap.faceSucc
  let xs := W'.letters
  let ul := xs.takeWhile (propIndicator M.tail)
  let lr := xs.dropWhile (propIndicator M.tail)
  obtain ⟨⟨a, ⟨_, _, _⟩, haUnique⟩, _, hswitchAll⟩ :=
    outerFace_has_exactly_two_switches_at_poles M planar acyclic noMissing
      isSource source_unique isSink sink_unique hst hs ht
  have hzero : xs[0]'(List.length_pos_iff.mpr W'.nonempty) = d := by
    have hh : xs.head? = some d := by simpa [xs] using hfirst
    rw [List.head?_eq_getElem?] at hh
    rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr W'.nonempty)] at hh
    exact Option.some.inj hh
  have hNoReturn : xs.IsChain (fun x y => M.tail x ∨ ¬ M.tail y) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    let x := xs[i]'(by omega)
    let y := xs[i + 1]'(by omega)
    by_contra hbad
    have hxnot : ¬ M.tail x := by
      intro hx
      exact hbad (Or.inl hx)
    have hytail : M.tail y := by
      by_contra hy
      exact hbad (Or.inr hy)
    have hstep : p x = y := by
      calc
        p x = xs.formPerm x := hW'.2.2 x (by dsimp [x]; exact List.getElem_mem _)
        _ = y := by
          dsimp [x, y]
          exact List.formPerm_apply_lt_getElem xs W'.nodup i hi
    have hswitch : IsOuterFaceSwitch M x := by
      change M.tail x ≠ M.tail (p x)
      rw [hstep]
      exact fun heq => hxnot (heq.symm ▸ hytail)
    have hxouter : M.IsOuter x := hW'.1 x (by dsimp [x]; exact List.getElem_mem _)
    have hyVertex : dartTailVertex M y = s := by
      rcases hswitchAll x hxouter hswitch with hs' | ht'
      · exact hstep ▸ hs'
      · have ht'' : dartTailVertex M y = t := hstep ▸ ht'
        exact (not_tail_at_sink M noMissing t isSink ht'' hytail).elim
    have hxa : x = a := haUnique x ⟨hxouter, hswitch, hstep ▸ hyVertex⟩
    have hyD : y = d := by
      calc
        y = p x := hstep.symm
        _ = p a := congrArg p hxa
        _ = d := by
          obtain ⟨aSource, haSourceOuter, haSourceSwitch, haSourceVertex,
            haSourceStep⟩ := hsourceStep
          have haaSource : aSource = a := haUnique aSource
            ⟨haSourceOuter, haSourceSwitch, haSourceVertex⟩
          rw [← haaSource]
          exact haSourceStep
    have hdup : xs[i + 1] = xs[0] := hyD.trans hzero.symm
    have hidx := W'.nodup.getElem_inj_iff.mp hdup
    omega
  have hpart : xs = ul ++ lr := by
    simpa [ul, lr] using
      (List.takeWhile_append_dropWhile (propIndicator M.tail) xs)
  have hulTail : ∀ e, e ∈ ul → M.tail e := by
    intro e he
    have hp := mem_takeWhile_true (propIndicator M.tail) he
    simpa [propIndicator] using hp
  have hlrNotTail : ∀ e, e ∈ lr → ¬ M.tail e :=
    all_not_dropWhile_of_no_return hNoReturn
  have hUlNonempty : ul ≠ [] := by
    intro hempty
    have hfirstEq : xs = d :: xs.tail := by
      cases hx : xs with
      | nil => simp [xs, hx] at hfirst
      | cons e es =>
        have heq : e = d := by
          have hh : some e = some d := by simpa [xs, hx] using hfirst
          exact Option.some.inj hh
        subst e
        simp [hx]
    have hfirst' : d ∈ ul := by
      dsimp [ul]
      rw [hfirstEq]
      simp [propIndicator, htail]
    have hemptyMem : d ∈ ([] : List D) := hempty ▸ hfirst'
    simpa using hemptyMem
  obtain ⟨dT, hdTouter, hdTvertex⟩ := ht
  have hTnotTail : ¬ M.tail dT := not_tail_at_sink M noMissing t isSink hdTvertex
  have hTmem : dT ∈ xs := by
    exact hW'.2.1 dT hdTouter
  have hTmemLr : dT ∈ lr := by
    have hTsplit := (List.mem_append.mp (hpart ▸ hTmem))
    rcases hTsplit with hUL | hLR
    · exact (hTnotTail (hulTail dT hUL)).elim
    · exact hLR
  have hLrNonempty : lr ≠ [] := by
    intro hnil
    have : dT ∈ ([] : List D) := hnil ▸ hTmemLr
    simpa using this
  have hEnumUl : EnumeratesSet ul M.ulDarts := by
    intro e
    constructor
    · intro he
      have hout : M.IsOuter e := by
        have hexs : e ∈ xs := by
          rw [hpart]
          exact List.mem_append.mpr (Or.inl he)
        exact hW'.1 e hexs
      exact ⟨noMissing e, hulTail e he, hout⟩
    · rintro ⟨hpresent, hed, heouter⟩
      have hexs : e ∈ xs := hW'.2.1 e heouter
      rcases List.mem_append.mp (hpart ▸ hexs) with heUL | heLR
      · exact heUL
      · exact (hlrNotTail e heLR hed).elim
  have hEnumLr : EnumeratesSet lr M.lrDarts := by
    intro e
    constructor
    · intro he
      have hout : M.IsOuter e := by
        have hexs : e ∈ xs := by
          rw [hpart]
          exact List.mem_append.mpr (Or.inr he)
        exact hW'.1 e hexs
      exact ⟨noMissing e, hlrNotTail e he, hout⟩
    · rintro ⟨hpresent, hed, heouter⟩
      have hexs : e ∈ xs := hW'.2.1 e heouter
      rcases List.mem_append.mp (hpart ▸ hexs) with heUL | heLR
      · exact (hed (hulTail e heUL)).elim
      · exact heLR
  have hleftpos : 1 ≤ ul.length := by
    exact Nat.succ_le_iff.mpr (List.length_pos_iff.mpr hUlNonempty)
  have hrightpos : 1 ≤ lr.length := by
    exact Nat.succ_le_iff.mpr (List.length_pos_iff.mpr hLrNonempty)
  refine ⟨W, W', d, ul, lr, hWletters, hW, hW', hrotate, hfirst, htail,
    hdVertex, hsourceStep, hpart, rfl, rfl, hulTail, hlrNotTail, hEnumUl, hEnumLr,
    hleftpos, hrightpos⟩

private theorem simplePath_reaches_vertex
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) {v : MapVertex M}
    (hv : v ∈ P.vertices) : Relation.ReflTransGen M.directedStep s v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hreach : ∀ k (hk : k ≤ n), Relation.ReflTransGen M.directedStep s
      (P.vertices.get ⟨k, by rw [P.vertices_length]; omega⟩) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [P.start_vertex] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen M.directedStep s s)
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hs := P.edge_step ⟨k, by rw [P.darts_length]; omega⟩
        have hstep : M.directedStep
            (P.vertices.get ⟨k, by rw [P.vertices_length]; omega⟩)
            (P.vertices.get ⟨k + 1, by rw [P.vertices_length]; omega⟩) := by
          exact ⟨P.darts.get ⟨k, by rw [P.darts_length]; omega⟩,
            hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
        exact hprev.trans (Relation.ReflTransGen.single hstep)
  have hiBound : i.val ≤ n := by
    have hlen := P.vertices_length
    omega
  simpa only [hi] using hreach i.val hiBound

private def prependSimplePath
    (M : DirectedMapWithMissing D) (acyclic : M.IsAcyclic)
    {u v t : MapVertex M} {n : ℕ} (d : D)
    (hd : ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = u ∧
      dartHeadVertex M d = v)
    (P : SimpleDirectedDartPath M v t n) : SimpleDirectedDartPath M u t (n + 1) := by
  have hnot : u ∉ P.vertices := by
    intro hu
    exact acyclic u (Relation.TransGen.head' ⟨d, hd⟩ (simplePath_reaches_vertex M P hu))
  refine {
    darts := d :: P.darts
    vertices := u :: P.vertices
    darts_length := by simp only [List.length_cons, P.darts_length]
    vertices_length := by simp only [List.length_cons, P.vertices_length]
    vertices_nodup := List.nodup_cons.mpr ⟨hnot, P.vertices_nodup⟩
    start_vertex := rfl
    end_vertex := by
      simpa only [List.get_eq_getElem, List.getElem_cons_succ] using P.end_vertex
    edge_step := ?_ }
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      Nat.zero_add, List.getElem_cons_succ]
    exact ⟨hd.1, hd.2.1, hd.2.2.1.symm, P.start_vertex.trans hd.2.2.2.symm⟩
  · simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
      using P.edge_step j

private theorem exists_simplePath_of_boundaryDartWalk
    (M : DirectedMapWithMissing D) (acyclic : M.IsAcyclic) :
    ∀ (xs : List D) (s t : MapVertex M),
      IsBoundaryDartWalk M xs s t →
      (∀ d, d ∈ xs → ¬ M.missing d ∧ M.tail d) →
      ∃ P : SimpleDirectedDartPath M s t xs.length, P.darts = xs := by
  intro xs
  induction xs with
  | nil =>
      intro s t hwalk _
      have hst : s = t := by simpa only [IsBoundaryDartWalk] using hwalk
      subst t
      exact ⟨SimpleDirectedDartPath.nil M s, rfl⟩
  | cons d ds ih =>
      intro s t hwalk hdir
      have hstart : s = dartTailVertex M d := hwalk.1
      have htail : IsBoundaryDartWalk M ds (dartHeadVertex M d) t := hwalk.2
      have hd := hdir d (by simp)
      have hdir' : ∀ e, e ∈ ds → ¬ M.missing e ∧ M.tail e := by
        intro e he
        exact hdir e (by simp [he])
      obtain ⟨P, hP⟩ := ih (dartHeadVertex M d) t htail hdir'
      let Q := prependSimplePath M acyclic d
        ⟨hd.1, hd.2, hstart.symm, rfl⟩ P
      refine ⟨Q, ?_⟩
      have hQ : Q.darts = d :: P.darts := rfl
      rw [hQ, hP]

private theorem formPerm_getLast_append_eq_head
    {α : Type*} [DecidableEq α] (xs ys : List α)
    (hnd : (xs ++ ys).Nodup) (hx : xs ≠ []) (hy : ys ≠ []) :
    (xs ++ ys).formPerm (xs.getLast hx) = ys.head hy := by
  have hlen : (xs ++ ys).length = xs.length + ys.length := List.length_append
  have hxpos : 0 < xs.length := List.length_pos_iff.mpr hx
  have hypos : 0 < ys.length := List.length_pos_iff.mpr hy
  have hi : xs.length - 1 < (xs ++ ys).length := by rw [hlen]; omega
  have hnext : (xs.length - 1 + 1) % (xs ++ ys).length = xs.length := by
    rw [Nat.sub_add_cancel hxpos, hlen]
    exact Nat.mod_eq_of_lt (by omega)
  have hleft : xs.getLast hx = (xs ++ ys)[xs.length - 1]'hi := by
    rw [List.getLast_eq_getElem hx]
    rw [List.getElem_append_left (by omega : xs.length - 1 < xs.length)]
  have hright : (xs ++ ys)[xs.length]'(by rw [hlen]; omega) = ys[0]'hypos := by
    rw [List.getElem_append_right (by omega : xs.length ≤ xs.length)]
    simp only [Nat.sub_self]
  calc
    (xs ++ ys).formPerm (xs.getLast hx) =
        (xs ++ ys).formPerm ((xs ++ ys)[xs.length - 1]'hi) := by rw [hleft]
    _ = (xs ++ ys)[(xs.length - 1 + 1) % (xs ++ ys).length]'
        (Nat.mod_lt _ (by rw [hlen]; omega)) :=
      List.formPerm_apply_getElem (xs ++ ys) hnd (xs.length - 1) hi
    _ = ys.head hy := by
      simpa only [List.head_eq_getElem, hnext] using hright

private theorem formPerm_getLast_eq_head
    {α : Type*} [DecidableEq α] (xs : List α) (hnd : xs.Nodup)
    (hxs : xs ≠ []) : xs.formPerm (xs.getLast hxs) = xs.head hxs := by
  rw [List.formPerm_apply_mem_eq_next hnd _ (List.getLast_mem hxs)]
  exact List.next_getLast_eq_head xs hxs hnd

private theorem dartTailVertex_edgeInv (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.edgeInv d) = dartHeadVertex M d := rfl

private theorem dartHeadVertex_edgeInv (M : DirectedMapWithMissing D) (d : D) :
    dartHeadVertex M (M.edgeInv d) = dartTailVertex M d := by
  simp [dartHeadVertex, dartTailVertex, M.edgeInv_invol]

private theorem head_reverse_map_eq_last
    {α β : Type*} (f : α → β) (xs : List α) (hxs : xs ≠ []) :
    (xs.reverse.map f).head? = some (f (xs.getLast hxs)) := by
  rw [List.head?_map, List.head?_reverse,
    List.getLast?_eq_getLast_of_ne_nil hxs]
  rfl

private theorem getLast_reverse_map_eq_head
    {α β : Type*} (f : α → β) (xs : List α) (hxs : xs ≠ []) :
    (xs.reverse.map f).getLast (by simp [hxs]) = f (xs.head hxs) := by
  have hrev : xs.reverse ≠ [] := by simpa using hxs
  have hmap : xs.reverse.map f ≠ [] := by simpa using hrev
  rw [List.getLast_map hmap]
  exact congrArg f (List.getLast_reverse hrev)

/-- The upper-left outer block is the simple directed path from the source
to the sink. Helper toward Definition 1.9 -/
theorem exists_simple_upper_left_boundary_path
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar) (acyclic : M.IsAcyclic)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ W W' : NonemptyWord D, ∃ (d : D) (ul lr : List D),
      W.letters = Equiv.Perm.toList M.toCombinatorialMap.faceSucc M.outer ∧
      IsOuterCycle M W ∧ IsOuterCycle M W' ∧ W.letters ~r W'.letters ∧
      W'.letters.head? = some d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      (∃ a, M.IsOuter a ∧ IsOuterFaceSwitch M a ∧
        dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s ∧
        M.toCombinatorialMap.faceSucc a = d) ∧
      W'.letters = ul ++ lr ∧
      ul = W'.letters.takeWhile (propIndicator M.tail) ∧
      lr = W'.letters.dropWhile (propIndicator M.tail) ∧
      (∀ e, e ∈ ul → M.tail e) ∧ (∀ e, e ∈ lr → ¬ M.tail e) ∧
      EnumeratesSet ul M.ulDarts ∧ EnumeratesSet lr M.lrDarts ∧
      1 ≤ ul.length ∧ 1 ≤ lr.length ∧
      (∃ P : SimpleDirectedDartPath M s t ul.length, P.darts = ul) := by
  classical
  obtain ⟨W, W', d, ul, lr, hWletters, hW, hW', hrotate, hfirst, htail,
    hdVertex, hsourceStep, hpart, hTake, hDrop, hulTail, hlrNotTail,
    hEnumUl, hEnumLr, hUlPos, hLrPos⟩ :=
      outer_face_maximal_oriented_blocks M planar acyclic noMissing
        isSource source_unique isSink sink_unique hst hs ht
  have hO1 := outerFace_has_exactly_two_switches_at_poles M planar acyclic
    noMissing isSource source_unique isSink sink_unique hst hs ht
  obtain ⟨_, _, hswitchAll⟩ := hO1
  have hu : ul ≠ [] := by
    intro h
    simp [h] at hUlPos
  have hl : lr ≠ [] := by
    intro h
    simp [h] at hLrPos
  have hUlChain : ul.IsChain (fun a b => dartHeadVertex M a = dartTailVertex M b) := by
    apply isOuterCycle_block_isChain M W' hW' [] ul lr
    refine ⟨0, ?_⟩
    simpa only [List.rotate_zero, List.nil_append] using hpart
  let x := ul.getLast hu
  let y := lr.head hl
  have hxmem : x ∈ W'.letters := by
    rw [hpart]
    exact List.mem_append.mpr (Or.inl (List.getLast_mem hu))
  have hform : W'.letters.formPerm x = y := by
    simpa only [hpart] using
      (formPerm_getLast_append_eq_head ul lr
        (by simpa only [hpart] using W'.nodup) hu hl)
  have hnext : M.toCombinatorialMap.faceSucc x = y := by
    calc
      M.toCombinatorialMap.faceSucc x = W'.letters.formPerm x := hW'.2.2 x hxmem
      _ = y := hform
  have hyVertex : dartTailVertex M y = t := by
    have hswitch : IsOuterFaceSwitch M x := by
      change M.tail x ≠ M.tail (M.toCombinatorialMap.faceSucc x)
      rw [hnext]
      exact fun heq => hlrNotTail y (List.head_mem hl) (heq ▸ hulTail x (List.getLast_mem hu))
    have houter : M.IsOuter x := hW'.1 x hxmem
    rcases hswitchAll x houter hswitch with hs' | ht'
    · have hvertexY : dartTailVertex M y = s := by rw [← hnext]; exact hs'
      have htailY := tail_at_source M noMissing s isSource hvertexY
      exact (hlrNotTail y (List.head_mem hl) htailY).elim
    · rw [← hnext]
      exact ht'
  have hinc : dartHeadVertex M x = dartTailVertex M y := by
    have h := isOuterCycle_next_dart_incident M W' hW' x hxmem
    calc
      dartHeadVertex M x = dartTailVertex M (W'.letters.formPerm x) := h
      _ = dartTailVertex M (M.toCombinatorialMap.faceSucc x) := by
        rw [← hW'.2.2 x hxmem]
      _ = dartTailVertex M y := by rw [hnext]
  have hUlEnd : dartHeadVertex M x = t := hinc.trans hyVertex
  have hEndpoints : BoundaryRunEndpoints M ul s t := by
    cases hul : ul with
    | nil => exact (hu hul).elim
    | cons e es =>
        have heq : e = d := by
          have hh : some e = some d := by simpa [hul, hpart] using hfirst
          exact Option.some.inj hh
        subst e
        simp only [BoundaryRunEndpoints]
        refine ⟨hdVertex.symm, ?_⟩
        simpa [x, hul] using hUlEnd
  have hWalk : IsBoundaryDartWalk M ul s t :=
    (isBoundaryDartWalk_iff_endpoints_and_isChain M ul s t).mpr
      ⟨hEndpoints, hUlChain⟩
  obtain ⟨P, hP⟩ := exists_simplePath_of_boundaryDartWalk M acyclic ul s t
    hWalk (fun e he => ⟨noMissing e, hulTail e he⟩)
  exact ⟨W, W', d, ul, lr, hWletters, hW, hW', hrotate, hfirst, htail,
    hdVertex, hsourceStep, hpart, hTake, hDrop, hulTail, hlrNotTail,
    hEnumUl, hEnumLr, hUlPos, hLrPos, ⟨P, hP⟩⟩

/-- The lower-right outer block, read in reverse with each dart reversed, is
the simple directed path from the source to the sink. Helper toward Definition -/
theorem exists_simple_lower_right_boundary_path
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar) (acyclic : M.IsAcyclic)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    ∃ W W' : NonemptyWord D, ∃ (d : D) (ul lr : List D),
      W.letters = Equiv.Perm.toList M.toCombinatorialMap.faceSucc M.outer ∧
      IsOuterCycle M W ∧ IsOuterCycle M W' ∧ W.letters ~r W'.letters ∧
      W'.letters.head? = some d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      (∃ a, M.IsOuter a ∧ IsOuterFaceSwitch M a ∧
        dartTailVertex M (M.toCombinatorialMap.faceSucc a) = s ∧
        M.toCombinatorialMap.faceSucc a = d) ∧
      W'.letters = ul ++ lr ∧
      ul = W'.letters.takeWhile (propIndicator M.tail) ∧
      lr = W'.letters.dropWhile (propIndicator M.tail) ∧
      (∀ e, e ∈ ul → M.tail e) ∧ (∀ e, e ∈ lr → ¬ M.tail e) ∧
      EnumeratesSet ul M.ulDarts ∧ EnumeratesSet lr M.lrDarts ∧
      1 ≤ ul.length ∧ 1 ≤ lr.length ∧
      (∃ P : SimpleDirectedDartPath M s t ul.length, P.darts = ul) ∧
      (∃ Q : SimpleDirectedDartPath M s t lr.length,
        Q.darts = lr.reverse.map M.toCombinatorialMap.edgeInv) := by
  classical
  obtain ⟨W, W', d, ul, lr, hWletters, hW, hW', hrotate, hfirst, htail,
    hdVertex, hsourceStep, hpart, hTake, hDrop, hulTail, hlrNotTail,
    hEnumUl, hEnumLr, hUlPos, hLrPos, hULPath⟩ :=
      exists_simple_upper_left_boundary_path M planar acyclic noMissing
        isSource source_unique isSink sink_unique hst hs ht
  obtain ⟨P, hPdarts⟩ := hULPath
  have hu : ul ≠ [] := by
    intro hempty
    simp [hempty] at hUlPos
  have hl : lr ≠ [] := by
    intro hempty
    simp [hempty] at hLrPos
  let x := ul.getLast hu
  let y := lr.head hl
  have hxmem : x ∈ W'.letters := by
    rw [hpart]
    exact List.mem_append.mpr (Or.inl (List.getLast_mem hu))
  have hform : W'.letters.formPerm x = y := by
    simpa only [hpart] using
      (formPerm_getLast_append_eq_head ul lr
        (by simpa only [hpart] using W'.nodup) hu hl)
  have hnext : M.toCombinatorialMap.faceSucc x = y := by
    calc
      M.toCombinatorialMap.faceSucc x = W'.letters.formPerm x := hW'.2.2 x hxmem
      _ = y := hform
  have hswitch : IsOuterFaceSwitch M x := by
    change M.tail x ≠ M.tail (M.toCombinatorialMap.faceSucc x)
    rw [hnext]
    exact fun heq => hlrNotTail y (List.head_mem hl)
      (heq ▸ hulTail x (List.getLast_mem hu))
  have houter : M.IsOuter x := hW'.1 x hxmem
  have hyVertex : dartTailVertex M y = t := by
    obtain ⟨⟨a, ⟨_, _, _⟩, haUnique⟩, _, hswitchAll⟩ :=
      outerFace_has_exactly_two_switches_at_poles M planar acyclic noMissing
        isSource source_unique isSink sink_unique hst hs ht
    rcases hswitchAll x houter hswitch with hs' | ht'
    · have hySource : dartTailVertex M y = s := by rw [← hnext]; exact hs'
      exact (hlrNotTail y (List.head_mem hl)
        (tail_at_source M noMissing s isSource hySource)).elim
    · rw [← hnext]
      exact ht'
  have hLrChain : lr.IsChain (fun a b => dartHeadVertex M a = dartTailVertex M b) := by
    apply isOuterCycle_block_isChain M W' hW' ul lr []
    refine ⟨0, ?_⟩
    simpa only [List.rotate_zero, List.nil_append, List.append_nil] using hpart
  have hReverseChain : lr.reverse.IsChain
      (fun a b => dartHeadVertex M b = dartTailVertex M a) := by
    exact (List.isChain_reverse).2 hLrChain
  have hQChain : (lr.reverse.map M.toCombinatorialMap.edgeInv).IsChain
      (fun a b => dartHeadVertex M a = dartTailVertex M b) := by
    apply (List.isChain_map M.toCombinatorialMap.edgeInv).2
    apply hReverseChain.imp
    intro a b hab
    rw [dartHeadVertex_edgeInv, dartTailVertex_edgeInv]
    exact hab.symm
  let z := lr.getLast hl
  have hWlast : W'.letters.getLast W'.nonempty = z := by
    simpa only [hpart, z] using
      (List.getLast_append_of_right_ne_nil ul lr hl)
  have hwrapForm : W'.letters.formPerm z = d := by
    have h := formPerm_getLast_eq_head W'.letters W'.nodup W'.nonempty
    rw [hWlast] at h
    have hh := hfirst
    rw [List.head?_eq_some_head W'.nonempty] at hh
    have hHead : W'.letters.head W'.nonempty = d := Option.some.inj hh
    rw [hHead] at h
    exact h
  have hzmem : z ∈ W'.letters := by
    rw [hpart]
    exact List.mem_append.mpr (Or.inr (List.getLast_mem hl))
  have hwrap : M.toCombinatorialMap.faceSucc z = d := by
    calc
      M.toCombinatorialMap.faceSucc z = W'.letters.formPerm z := hW'.2.2 z hzmem
      _ = d := hwrapForm
  have hheadZ : dartHeadVertex M z = s := by
    calc
      dartHeadVertex M z = dartTailVertex M (M.toCombinatorialMap.faceSucc z) :=
        dartHeadVertex_eq_tailVertex_faceSucc M z
      _ = dartTailVertex M d := by rw [hwrap]
      _ = s := hdVertex
  let q := lr.reverse.map M.toCombinatorialMap.edgeInv
  have hqnonempty : q ≠ [] := by simp [q, hl]
  have hqhead : q.head? = some (M.toCombinatorialMap.edgeInv z) := by
    simpa only [q, z] using
      (head_reverse_map_eq_last M.toCombinatorialMap.edgeInv lr hl)
  have hqlast : q.getLast hqnonempty = M.toCombinatorialMap.edgeInv y := by
    simpa only [q, y] using
      (getLast_reverse_map_eq_head M.toCombinatorialMap.edgeInv lr hl)
  have hQEndpoints : BoundaryRunEndpoints M q s t := by
    cases hq : q with
    | nil => exact (hqnonempty hq).elim
    | cons e es =>
        have he : e = M.toCombinatorialMap.edgeInv z := by
          simpa only [hq, List.head?_cons, Option.some.injEq] using hqhead
        have hqLast' : (e :: es).getLast (by simp) =
            M.toCombinatorialMap.edgeInv y := by
          simpa only [hq] using hqlast
        simp only [BoundaryRunEndpoints]
        constructor
        · rw [he, dartTailVertex_edgeInv]
          exact hheadZ.symm
        · rw [hqLast', dartHeadVertex_edgeInv]
          exact hyVertex
  have hQWalk : IsBoundaryDartWalk M q s t :=
    (isBoundaryDartWalk_iff_endpoints_and_isChain M q s t).mpr
      ⟨hQEndpoints, hQChain⟩
  obtain ⟨Q₀, hQ₀darts⟩ := exists_simplePath_of_boundaryDartWalk M acyclic q s t
    hQWalk (fun e he => by
      rcases List.mem_map.mp (show e ∈ lr.reverse.map M.toCombinatorialMap.edgeInv from he)
          with ⟨f, hf, hfe⟩
      have hflr : f ∈ lr := List.mem_reverse.mp hf
      refine ⟨noMissing e, ?_⟩
      rw [← hfe]
      by_contra hnot
      exact hlrNotTail f hflr ((M.tail_iff f (noMissing f)).mpr hnot))
  let Q : SimpleDirectedDartPath M s t lr.length := {
    darts := Q₀.darts
    vertices := Q₀.vertices
    darts_length := by simpa [q] using Q₀.darts_length
    vertices_length := by simpa [q] using Q₀.vertices_length
    vertices_nodup := Q₀.vertices_nodup
    start_vertex := Q₀.start_vertex
    end_vertex := by simpa [q] using Q₀.end_vertex
    edge_step := Q₀.edge_step }
  have hQdarts : Q.darts = lr.reverse.map M.toCombinatorialMap.edgeInv := by
    simpa only [Q, q] using hQ₀darts
  exact ⟨W, W', d, ul, lr, hWletters, hW, hW', hrotate, hfirst, htail,
    hdVertex, hsourceStep, hpart, hTake, hDrop, hulTail, hlrNotTail,
    hEnumUl, hEnumLr, hUlPos, hLrPos, ⟨P, hPdarts⟩, ⟨Q, hQdarts⟩⟩

/-- The two oriented outer blocks assemble the four-arc witness and the
finite bipolar-boundary carrier with lengths given by their dart-set
cardinalities. Helper toward Definition 1.9 -/
theorem exists_bipolarBoundary_of_intrinsic_data
    (M : DirectedMapWithMissing D)
    (planar : M.toCombinatorialMap.IsPlanar) (acyclic : M.IsAcyclic)
    (noMissing : ∀ d, ¬ M.missing d) {s t : MapVertex M}
    (isSource : ¬ ∃ u, M.directedStep u s)
    (source_unique : ∀ v, (¬ ∃ u, M.directedStep u v) → v = s)
    (isSink : ¬ ∃ w, M.directedStep t w)
    (sink_unique : ∀ v, (¬ ∃ w, M.directedStep v w) → v = t)
    (hst : s ≠ t)
    (hs : ∃ d, M.IsOuter d ∧ dartTailVertex M d = s)
    (ht : ∃ d, M.IsOuter d ∧ dartTailVertex M d = t) :
    IsBipolarMapWithBoundary M
      (Nat.card {d // d ∈ M.ulDarts}) (Nat.card {d // d ∈ M.lrDarts}) := by
  classical
  obtain ⟨W, W', d, ul, lr, _, _, hW', _, _, _, _, _, hpart, _, _, _, _,
    hEnumUl, hEnumLr, hUlPos, hLrPos, ⟨P, hPdarts⟩, ⟨Q, hQdarts⟩⟩ :=
      exists_simple_lower_right_boundary_path M planar acyclic noMissing
        isSource source_unique isSink sink_unique hst hs ht
  have hblocksNodup : (ul ++ lr).Nodup := by
    simpa only [← hpart] using W'.nodup
  have hulNodup : ul.Nodup := hblocksNodup.of_append_left
  have hlrNodup : lr.Nodup := hblocksNodup.of_append_right
  have hcardUl : Nat.card {e // e ∈ M.ulDarts} = ul.length := by
    calc
      Nat.card {e // e ∈ M.ulDarts} = ul.toFinset.card :=
        Nat.subtype_card _ (fun e => List.mem_toFinset.trans (hEnumUl e))
      _ = ul.length := List.toFinset_card_of_nodup hulNodup
  have hcardLr : Nat.card {e // e ∈ M.lrDarts} = lr.length := by
    calc
      Nat.card {e // e ∈ M.lrDarts} = lr.toFinset.card :=
        Nat.subtype_card _ (fun e => List.mem_toFinset.trans (hEnumLr e))
      _ = lr.length := List.toFinset_card_of_nodup hlrNodup
  have hrightBlock : Q.darts.reverse.map M.toCombinatorialMap.edgeInv = lr := by
    rw [hQdarts]
    simp [Function.comp_def, M.toCombinatorialMap.edgeInv_invol]
  have hFour : FourArcsWitness M W' ul [] lr [] := by
    refine ⟨hW', ?_, hEnumUl, hEnumLr, ?_, ?_⟩
    · exact ⟨0, by simpa only [List.rotate_zero, List.append_nil] using hpart⟩
    · intro e he
      simp at he
    · intro e he
      simp at he
  have hOuterSplit : FourArcsWitness M W' P.darts []
      (Q.darts.reverse.map M.toCombinatorialMap.edgeInv) [] := by
    simpa only [hPdarts, hrightBlock] using hFour
  let B : BipolarMapWithBoundaryBase D ul.length lr.length := {
    map := M
    noMissingDarts := noMissing
    planar := planar
    acyclic := acyclic
    source := s
    sink := t
    isSource := isSource
    source_unique := source_unique
    isSink := isSink
    sink_unique := sink_unique
    left_length_pos := hUlPos
    right_length_pos := hLrPos
    outerWord := W'
    leftPath := P
    rightPath := Q
    outerSplit := hOuterSplit }
  have hB : IsBipolarMapWithBoundary M ul.length lr.length := ⟨B, rfl⟩
  simpa only [hcardUl, hcardLr] using hB

/-- The intrinsic finite-map conditions of Definition 1.9 are equivalent to
the finite bipolar-boundary carrier. Helper toward Definition 1.9 -/
theorem isBipolarMapWithBoundary_iff_intrinsic
    (M : DirectedMapWithMissing D) (ℓ r : ℕ) :
    IsBipolarMapWithBoundary M ℓ r ↔ HasIntrinsicBipolarBoundary M ℓ r := by
  constructor
  · exact isBipolarMapWithBoundary_implies_intrinsic M
  · intro h
    obtain ⟨planar, acyclic, noMissing, s, t, isSource, source_unique,
      isSink, sink_unique, hs, ht, hst, hℓ, hr⟩ := h
    have hB := exists_bipolarBoundary_of_intrinsic_data M planar acyclic
      noMissing isSource source_unique isSink sink_unique hst hs ht
    simpa only [hℓ, hr] using hB

end DirectedDistances.PlanarMap
