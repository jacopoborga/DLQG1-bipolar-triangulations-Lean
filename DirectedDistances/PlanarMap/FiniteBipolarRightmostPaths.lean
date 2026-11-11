/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarBoundary
import DirectedDistances.PlanarMap.FiniteXDPGeodesicSplit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Rotation blocks in finite bipolar planar maps

The carrier has arbitrary face degrees and retains dart identities and shared
boundary subpaths. Rotation is counter-clockwise; the block statements below
are read clockwise, in `rot.symm` order. -/

public section
namespace DirectedDistances.PlanarMap
namespace BipolarMapWithBoundaryBase

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

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

private theorem face_tail_vertex (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.toCombinatorialMap.faceSucc d) = dartHeadVertex M d := by
  apply Quotient.sound
  exact ⟨1, by simp [CombinatorialMap.faceSucc]⟩

private theorem face_forward (B : BipolarMapWithBoundaryBase D ℓ r) (d : D)
    (h : B.map.tail d) :
    B.map.directedStep (dartTailVertex B.map d)
      (dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d)) := by
  exact ⟨d, B.noMissingDarts d, h, rfl, (face_tail_vertex B.map d).symm⟩

private theorem face_backward (B : BipolarMapWithBoundaryBase D ℓ r) (d : D)
    (h : ¬ B.map.tail d) :
    B.map.directedStep
      (dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d))
      (dartTailVertex B.map d) := by
  have hinv : B.map.tail (B.map.edgeInv d) := by
    by_contra hn
    exact h ((B.map.tail_iff d (B.noMissingDarts d)).mpr hn)
  refine ⟨B.map.edgeInv d, B.noMissingDarts _, hinv,
    (face_tail_vertex B.map d).symm, ?_⟩
  simp only [dartTailVertex, B.map.edgeInv_invol]

/-- Every face has darts in both boundary orientations, including the outer
face and faces incident to bridges. Helper toward Definition 3.13
and acyclicity are used; there is no triangular-face assumption. -/
theorem face_has_both_orientations (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    (∃ e, B.map.toCombinatorialMap.faceSucc.SameCycle d e ∧ B.map.tail e) ∧
    (∃ e, B.map.toCombinatorialMap.faceSucc.SameCycle d e ∧ ¬ B.map.tail e) := by
  classical
  let p := B.map.toCombinatorialMap.faceSucc
  have hreturn : (p ^ orderOf p) d = d := by rw [pow_orderOf_eq_one]; rfl
  have hcycle (n : ℕ) : p.SameCycle d ((p ^ n) d) := ⟨(n : ℤ), by simp⟩
  constructor
  · by_contra h
    have hn (n : ℕ) : ¬ B.map.tail ((p ^ n) d) := by
      intro ht
      exact h ⟨(p ^ n) d, hcycle n, ht⟩
    have hpath : ∀ n, Relation.TransGen B.map.directedStep
        (dartTailVertex B.map ((p ^ (n + 1)) d)) (dartTailVertex B.map d) := by
      intro n
      induction n with
      | zero => exact Relation.TransGen.single (face_backward B d (hn 0))
      | succ n ih =>
          have hs := face_backward B ((p ^ (n + 1)) d) (hn (n + 1))
          have hs' : B.map.directedStep
              (dartTailVertex B.map ((p ^ (n + 1 + 1)) d))
              (dartTailVertex B.map ((p ^ (n + 1)) d)) := by
            simpa only [pow_succ', Equiv.Perm.mul_apply] using hs
          exact Relation.TransGen.head hs' ih
    have hp := hpath (orderOf p - 1)
    rw [Nat.sub_add_cancel (orderOf_pos p), hreturn] at hp
    exact B.acyclic _ hp
  · by_contra h
    have hn (n : ℕ) : B.map.tail ((p ^ n) d) := by
      by_contra ht
      exact h ⟨(p ^ n) d, hcycle n, ht⟩
    have hpath : ∀ n, Relation.TransGen B.map.directedStep
        (dartTailVertex B.map d) (dartTailVertex B.map ((p ^ (n + 1)) d)) := by
      intro n
      induction n with
      | zero => exact Relation.TransGen.single (face_forward B d (hn 0))
      | succ n ih =>
          have hs := face_forward B ((p ^ (n + 1)) d) (hn (n + 1))
          have hs' : B.map.directedStep
              (dartTailVertex B.map ((p ^ (n + 1)) d))
              (dartTailVertex B.map ((p ^ (n + 1 + 1)) d)) := by
            simpa only [pow_succ', Equiv.Perm.mul_apply] using hs
          exact ih.tail hs'
    have hp := hpath (orderOf p - 1)
    rw [Nat.sub_add_cancel (orderOf_pos p), hreturn] at hp
    exact B.acyclic _ hp

private theorem source_tail (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : dartTailVertex B.map d = B.source) : B.map.tail d := by
  classical
  by_contra hn
  have ht : B.map.tail (B.map.edgeInv d) := by
    by_contra hi
    exact hn ((B.map.tail_iff d (B.noMissingDarts d)).mpr hi)
  apply B.isSource
  refine ⟨dartTailVertex B.map (B.map.edgeInv d), B.map.edgeInv d,
    B.noMissingDarts _, ht, rfl, ?_⟩
  simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using hd

private theorem sink_not_tail (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : dartTailVertex B.map d = B.sink) : ¬ B.map.tail d := by
  intro ht
  exact B.isSink ⟨dartHeadVertex B.map d, d, B.noMissingDarts _, ht, hd, rfl⟩

private theorem rot_inv_vertex (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.rot.symm d) = dartTailVertex M d := by
  apply Quotient.sound
  exact ⟨1, by simp⟩

private theorem source_ne_sink (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.source ≠ B.sink := by
  intro h
  have hi : 0 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    exact B.right_length_pos
  have hs := B.rightPath.edge_step ⟨0, hi⟩
  have hv : dartTailVertex B.map (B.rightPath.darts.get ⟨0, hi⟩) = B.source :=
    hs.2.2.1.symm.trans B.rightPath.start_vertex
  exact sink_not_tail B (hv.trans h) hs.2.1

private theorem nonpole_orientations (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    (∃ a, dartTailVertex B.map a = v ∧ B.map.tail a) ∧
    (∃ b, dartTailVertex B.map b = v ∧ ¬ B.map.tail b) := by
  classical
  have hout : ∃ w, B.map.directedStep v w := by
    by_contra h
    exact ht (B.sink_unique v h)
  have hin : ∃ w, B.map.directedStep w v := by
    by_contra h
    exact hs (B.source_unique v h)
  obtain ⟨w, a, _, ha, hav, _⟩ := hout
  obtain ⟨w', b, _, hb, _, hbv⟩ := hin
  exact ⟨⟨a, hav, ha⟩, ⟨B.map.edgeInv b, hbv,
    (B.map.tail_iff b (B.noMissingDarts b)).mp hb⟩⟩

private theorem face_transition_lower (B : BipolarMapWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    2 ≤ Nat.card {d : D //
      Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.faceSucc) d = q ∧
        B.map.tail d ≠ B.map.tail (B.map.faceSucc d)} := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  obtain ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ := B.face_has_both_orientations d
  have h := cycle_transition_card_ge_two B.map.faceSucc B.map.tail
    (ha.symm.trans hb) hPa hPb
  have he := Equiv.subtypeEquivRight (p := fun e =>
    B.map.faceSucc.SameCycle a e ∧ B.map.tail e ≠ B.map.tail (B.map.faceSucc e))
    (q := fun e =>
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.faceSucc) e =
      Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.faceSucc) d ∧
      B.map.tail e ≠ B.map.tail (B.map.faceSucc e)) (fun e => by
        constructor
        · rintro ⟨he, hP⟩
          exact ⟨Quotient.sound (ha.trans he).symm, hP⟩
        · rintro ⟨he, hP⟩
          exact ⟨ha.symm.trans (Quotient.exact he).symm, hP⟩)
  rwa [Nat.card_congr he] at h

private theorem rotation_transition_lower (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    2 ≤ Nat.card {d : D // dartTailVertex B.map d = v ∧
      B.map.tail d ≠ B.map.tail (B.map.rot.symm d)} := by
  obtain ⟨⟨a, hav, ha⟩, ⟨b, hbv, hb⟩⟩ := nonpole_orientations B v hs ht
  have hcycle : Equiv.Perm.SameCycle B.map.rot.symm a b :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hav.trans hbv.symm))
  have h := cycle_transition_card_ge_two B.map.rot.symm B.map.tail hcycle ha hb
  have he := Equiv.subtypeEquivRight (p := fun e =>
    Equiv.Perm.SameCycle B.map.rot.symm a e ∧ B.map.tail e ≠ B.map.tail (B.map.rot.symm e))
    (q := fun e => dartTailVertex B.map e = v ∧
      B.map.tail e ≠ B.map.tail (B.map.rot.symm e)) (fun e => by
        constructor
        · rintro ⟨he, hP⟩
          exact ⟨(Quotient.sound (Equiv.Perm.sameCycle_inv.mp he).symm).trans hav, hP⟩
        · rintro ⟨he, hP⟩
          exact ⟨Equiv.Perm.sameCycle_inv.mpr
            (Quotient.exact (hav.trans he.symm)), hP⟩)
  rwa [Nat.card_congr he] at h

private theorem transition_partition (B : BipolarMapWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.tail d ≠ B.map.tail (B.map.faceSucc d)} +
      Nat.card {d : D // B.map.tail d ≠ B.map.tail (B.map.rot.symm d)} =
        Fintype.card D := by
  classical
  let F : D → Prop := fun d => B.map.tail d ≠ B.map.tail (B.map.faceSucc d)
  let V : D → Prop := fun d => B.map.tail d ≠ B.map.tail (B.map.rot.symm d)
  have hcorner (d : D) : V (B.map.edgeInv d) ↔ ¬ F d := by
    have hi := B.map.tail_iff d (B.noMissingDarts d)
    dsimp [V, F, CombinatorialMap.faceSucc]
    by_cases hd : B.map.tail d <;>
      by_cases he : B.map.tail (B.map.edgeInv d) <;>
      by_cases hf : B.map.tail (B.map.rot.symm (B.map.edgeInv d)) <;>
      simp_all
  let e : {d : D // V d} ≃ {d : D // ¬ F d} := {
    toFun := fun d => ⟨B.map.edgeInv d.1, (hcorner _).mp (by
      simpa only [B.map.edgeInv_invol] using d.2)⟩
    invFun := fun d => ⟨B.map.edgeInv d.1, (hcorner _).mpr d.2⟩
    left_inv := by intro d; apply Subtype.ext; exact B.map.edgeInv_invol d.1
    right_inv := by intro d; apply Subtype.ext; exact B.map.edgeInv_invol d.1 }
  change Nat.card {d : D // F d} + Nat.card {d : D // V d} = _
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl F]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le F)

/-- At a non-pole vertex there are exactly two orientation changes in the
clockwise rotation. Helper toward Definition 3.13
faces and all vertices and uses Euler characteristic two; no face-degree
restriction or disjointness of boundary paths is used. -/
theorem rotation_transition_card_eq_two (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    Nat.card {d : D // dartTailVertex B.map d = v ∧
      B.map.tail d ≠ B.map.tail (B.map.rot.symm d)} = 2 := by
  classical
  let F : D → Prop := fun d => B.map.tail d ≠ B.map.tail (B.map.faceSucc d)
  let V : D → Prop := fun d => B.map.tail d ≠ B.map.tail (B.map.rot.symm d)
  let f : MapVertex B.map → ℕ := fun w =>
    Nat.card {d : D // dartTailVertex B.map d = w ∧ V d}
  let nonpoles : Finset (MapVertex B.map) :=
    (Finset.univ.erase B.source).erase B.sink
  have hF : 2 * B.map.numFaces ≤ Nat.card {d : D // F d} := by
    rw [card_fibers (fun d => Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.faceSucc) d) F]
    calc
      2 * B.map.numFaces = ∑ _q : CombinatorialMap.FaceQuotient
          B.map.toCombinatorialMap, (2 : ℕ) := by
            rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
            exact Nat.mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum (fun q _ => face_transition_lower B q)
  have htotal : Nat.card {d : D // V d} = ∑ w : MapVertex B.map, f w :=
    card_fibers (dartTailVertex B.map) V
  have hcount := transition_partition B
  have hE := B.map.toCombinatorialMap.two_mul_numEdges
  have hEuler : (B.map.numVertices : ℤ) - B.map.numEdges + B.map.numFaces = 2 :=
    B.planar.2
  have hupper : (∑ w : MapVertex B.map, f w) ≤ 2 * (B.map.numVertices - 2) := by
    change Nat.card {d : D // F d} + Nat.card {d : D // V d} = _ at hcount
    rw [htotal] at hcount
    omega
  have hst := source_ne_sink B
  have hcard : nonpoles.card = B.map.numVertices - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
      ⟨hst.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rfl
  have hge : ∀ w ∈ nonpoles, 2 ≤ f w := by
    intro w hw
    have hws := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    have hwt := (Finset.mem_erase.mp hw).1
    exact rotation_transition_lower B w hws hwt
  have hv : v ∈ nonpoles := by simp only [nonpoles, Finset.mem_erase,
    Finset.mem_univ, and_true]; exact ⟨ht, hs⟩
  have hlocal : 2 ≤ f v := hge v hv
  change f v = 2
  by_contra hne
  have hrest : 2 * (nonpoles.erase v).card ≤ ∑ w ∈ nonpoles.erase v, f w := by
    calc
      2 * (nonpoles.erase v).card = ∑ _w ∈ nonpoles.erase v, (2 : ℕ) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl)]
        exact Nat.mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum (fun w hw => hge w (Finset.mem_of_mem_erase hw))
  have hsum : f v + ∑ w ∈ nonpoles.erase v, f w = ∑ w ∈ nonpoles, f w := by
    rw [← Finset.sum_erase_add _ _ hv]
    exact add_comm _ _
  have hsub : (∑ w ∈ nonpoles, f w) ≤ ∑ w : MapVertex B.map, f w :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hc := Finset.card_erase_of_mem hv
  omega

/-- The outgoing and reverse-incoming darts form one block each in clockwise
(`rot.symm`) order. `leftIncoming` is the unique incoming-to-outgoing
transition and `rightOutgoing` is the unique outgoing-to-incoming transition;
all other darts stay in their block. Incoming edges are represented here by
their reverse darts based at `v`, so edge identities and parallel edges are
retained. Helper toward Definition 3.13 -/
theorem incoming_block (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ (leftIncoming rightOutgoing : D),
      dartTailVertex B.map leftIncoming = v ∧ ¬ B.map.tail leftIncoming ∧
      dartTailVertex B.map rightOutgoing = v ∧ B.map.tail rightOutgoing ∧
      B.map.tail (B.map.rot.symm leftIncoming) ∧
      ¬ B.map.tail (B.map.rot.symm rightOutgoing) ∧
      (∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        q ≠ leftIncoming → ¬ B.map.tail (B.map.rot.symm q)) ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        q ≠ rightOutgoing → B.map.tail (B.map.rot.symm q)) ∧
      (∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        B.map.tail (B.map.rot.symm q) → q = leftIncoming) ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ¬ B.map.tail (B.map.rot.symm q) → q = rightOutgoing) := by
  classical
  let p : Equiv.Perm D := B.map.rot.symm
  obtain ⟨⟨a, hav, ha⟩, ⟨b, hbv, hb⟩⟩ := nonpole_orientations B v hs ht
  have hcycle : p.SameCycle a b :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hav.trans hbv.symm))
  obtain ⟨ro, hroCycle, hro, hroNext⟩ :=
    exists_cycle_transition p B.map.tail hcycle ha hb
  obtain ⟨li, hliCycle, hli, hliNext⟩ :=
    exists_cycle_transition p (fun d => ¬ B.map.tail d) hcycle.symm hb
      (by simpa only [not_not] using ha)
  have hliNext' : B.map.tail (p li) := not_not.mp hliNext
  have hroV : dartTailVertex B.map ro = v :=
    (Quotient.sound (Equiv.Perm.sameCycle_inv.mp hroCycle).symm).trans hav
  have hliV : dartTailVertex B.map li = v :=
    (Quotient.sound (Equiv.Perm.sameCycle_inv.mp hliCycle).symm).trans hbv
  let transitions : Finset D := Finset.univ.filter fun q =>
    dartTailVertex B.map q = v ∧ B.map.tail q ≠ B.map.tail (p q)
  have hcard : transitions.card = 2 := by
    have hc := rotation_transition_card_eq_two B v hs ht
    rw [Nat.subtype_card transitions (by intro q; simp only [transitions,
      Finset.mem_filter, Finset.mem_univ, true_and]; rfl)] at hc
    exact hc
  have hliMem : li ∈ transitions := by
    simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hliV, fun h => hli (h.symm ▸ hliNext')⟩
  have hroMem : ro ∈ transitions := by
    simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hroV, fun h => hroNext (h ▸ hro)⟩
  have hne : li ≠ ro := fun h => hli (h ▸ hro)
  have hpair : transitions = {li, ro} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hliMem
      · exact hroMem
    · rw [Finset.card_pair hne, hcard]
  have hup (q : D) (hqv : dartTailVertex B.map q = v)
      (hq : ¬ B.map.tail q) (hnext : B.map.tail (p q)) : q = li := by
    have hm : q ∈ transitions := by
      simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqv, fun h => hq (h.symm ▸ hnext)⟩
    rw [hpair] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_right (fun h => hq (h ▸ hro))
  have hdown (q : D) (hqv : dartTailVertex B.map q = v)
      (hq : B.map.tail q) (hnext : ¬ B.map.tail (p q)) : q = ro := by
    have hm : q ∈ transitions := by
      simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqv, fun h => hnext (h ▸ hq)⟩
    rw [hpair] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_left (fun h => hli (h ▸ hq))
  refine ⟨li, ro, hliV, hli, hroV, hro, hliNext', hroNext, ?_, ?_, hup, hdown⟩
  · intro q hqv hq hqne hnext
    exact hqne (hup q hqv hq hnext)
  · intro q hqv hq hqne
    by_contra hnext
    exact hqne (hdown q hqv hq hnext)

/-- At the source the whole rotation cycle is outgoing and no dart enters
the source. Helper toward Definition 3.13 -/
theorem source_rotation_all_outgoing (B : BipolarMapWithBoundaryBase D ℓ r) :
    (∀ d, dartTailVertex B.map d = B.source → B.map.tail d) ∧
      ¬ ∃ d, B.map.tail d ∧ dartHeadVertex B.map d = B.source := by
  refine ⟨fun _ hd => source_tail B hd, ?_⟩
  rintro ⟨d, hd, hv⟩
  exact B.isSource ⟨dartTailVertex B.map d, d, B.noMissingDarts _, hd, rfl, hv⟩

/-- At the sink the whole rotation cycle consists of reverse-incoming darts
and no dart leaves the sink. Helper toward Definition 3.13 -/
theorem sink_rotation_all_incoming (B : BipolarMapWithBoundaryBase D ℓ r) :
    (∀ d, dartTailVertex B.map d = B.sink → ¬ B.map.tail d) ∧
      ¬ ∃ d, B.map.tail d ∧ dartTailVertex B.map d = B.sink := by
  refine ⟨fun _ hd => sink_not_tail B hd, ?_⟩
  rintro ⟨d, hd, hv⟩
  exact sink_not_tail B hv hd

private def outerBoundaryDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) : List D :=
  B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv

private theorem outerBoundaryDarts_nodup
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).Nodup := by
  simpa [outerBoundaryDarts] using
    B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup

private theorem outerBoundaryDarts_length
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).length = ℓ + r := by
  simp [outerBoundaryDarts, B.leftPath.darts_length,
    B.rightPath.darts_length]

private theorem outerBoundaryDarts_faceSucc_eq_formPerm
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d = (outerBoundaryDarts B).formPerm d := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hd
  calc
    B.map.toCombinatorialMap.faceSucc d = B.outerWord.letters.formPerm d :=
      B.outerSplit.1.2.2 d hword
    _ = (outerBoundaryDarts B).formPerm d := by
      simpa [outerBoundaryDarts] using congrArg (fun f : Equiv.Perm D => f d)
        (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)

private theorem outerBoundaryDarts_mem_isOuter
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ outerBoundaryDarts B) : B.map.IsOuter d := by
  have hword : d ∈ B.outerWord.letters := by
    exact (B.outerSplit.2.1.perm.mem_iff).mpr (by simpa [outerBoundaryDarts] using hd)
  exact (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mp hword

 
theorem outerFace_sourceCorner_eq_firstLeftDart
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos))) =
      B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  let xs := outerBoundaryDarts B
  let dR := B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)
  have hlen : xs.length = ℓ + r := outerBoundaryDarts_length B
  have hleft : 0 < ℓ := Nat.zero_lt_of_lt B.left_length_pos
  have hright : 0 < r := Nat.zero_lt_of_lt B.right_length_pos
  have hpos : 0 < ℓ + r := by omega
  have hne : xs ≠ [] := by
    intro h
    simp [h] at hlen
    omega
  have hlast : xs.getLast hne = B.map.toCombinatorialMap.edgeInv dR := by
    have hrightNonempty : B.rightPath.darts ≠ [] := by
      intro hn
      have h := congrArg List.length hn
      simp [B.rightPath.darts_length] at h
      omega
    have hhead : B.rightPath.darts.head hrightNonempty = dR := by
      dsimp [dR, SimpleDirectedDartPath.firstDart]
      rw [List.head_eq_getElem_zero hrightNonempty]
    dsimp [xs, outerBoundaryDarts]
    rw [List.getLast_append_of_right_ne_nil]
    · simpa [dR, SimpleDirectedDartPath.firstDart, List.get_eq_getElem] using
        congrArg B.map.toCombinatorialMap.edgeInv hhead
    · intro hnil
      have hlenR := congrArg List.length hnil
      simp [B.rightPath.darts_length] at hlenR
      omega
  have hlastMem : xs.getLast hne ∈ xs := List.getLast_mem hne
  have hlastOuter : B.map.IsOuter (xs.getLast hne) :=
    outerBoundaryDarts_mem_isOuter B hlastMem
  have hmod : (ℓ + r) % (ℓ + r) < xs.length := by
    rw [hlen]
    exact Nat.mod_lt _ hpos
  have hfirst : 0 < xs.length := by rw [hlen]; omega
  have hlastIndex : xs[ℓ + r - 1]'(by rw [hlen]; omega) = xs.getLast hne := by
    have hh : xs[xs.length - 1]'(by omega) = xs.getLast hne := by
      simpa only [List.get_eq_getElem] using
        List.get_length_sub_one (l := xs) (by omega)
    have hlen' : ℓ + r - 1 = xs.length - 1 := congrArg (fun n : ℕ => n - 1) hlen.symm
    simpa only [hlen'] using hh
  have hidxOuter : B.map.IsOuter (xs[ℓ + r - 1]'(by rw [hlen]; omega)) := by
    rw [hlastIndex]
    exact hlastOuter
  have hsucc : B.map.toCombinatorialMap.faceSucc
        (xs[ℓ + r - 1]'(by rw [hlen]; omega)) =
      xs[(ℓ + r) % (ℓ + r)]'hmod := by
    have hform := List.formPerm_apply_getElem xs (outerBoundaryDarts_nodup B)
      (ℓ + r - 1) (by rw [hlen]; omega)
    have hindex : ℓ + r - 1 + 1 = ℓ + r := by omega
    rw [outerBoundaryDarts_faceSucc_eq_formPerm B hidxOuter]
    calc
      (outerBoundaryDarts B).formPerm xs[ℓ + r - 1] = xs[0]'hfirst := by
        simpa only [hindex, hlen, Nat.mod_self] using hform
      _ = xs[(ℓ + r) % (ℓ + r)]'hmod := by simp
  have hcorner : B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.edgeInv dR) =
      xs[0]'(by simpa only [Nat.mod_self] using hmod) := by
    rw [hlastIndex, hlast] at hsucc
    simpa only [Nat.mod_self] using hsucc
  have hxs0 : xs[0]'hfirst = B.leftPath.firstDart
      (Nat.zero_lt_of_lt B.left_length_pos) := by
    have hleftIndex : 0 < B.leftPath.darts.length := by
      rw [B.leftPath.darts_length]
      exact hleft
    have hzero :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[0]'
            (by simp [B.leftPath.darts_length]; omega) =
          B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
      rw [List.getElem_append_left hleftIndex]
      simp [SimpleDirectedDartPath.firstDart, List.get_eq_getElem]
    simpa [xs, outerBoundaryDarts] using hzero
  rw [hxs0] at hcorner
  exact hcorner


/-- The marked outer-face corner cuts the all-incoming sink rotation between
the reverses of the last left-boundary and last right-boundary darts. Helper
coinciding boundary paths and one-edge maps. -/
theorem outerFace_sinkCorner_eq_lastRightDart
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.map.faceSucc (B.leftPath.darts.get
        ⟨ℓ - 1, by rw [B.leftPath.darts_length]; have := B.left_length_pos; omega⟩) =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨r - 1, by rw [B.rightPath.darts_length]; have := B.right_length_pos; omega⟩) := by
  let xs := outerBoundaryDarts B
  have hl := B.left_length_pos
  have hr := B.right_length_pos
  have hlen : xs.length = ℓ + r := outerBoundaryDarts_length B
  have hi : ℓ - 1 < xs.length := by rw [hlen]; omega
  have hj : ℓ < xs.length := by rw [hlen]; omega
  have hstep : B.map.faceSucc xs[ℓ - 1] = xs[ℓ] := by
    have hmem : xs[ℓ - 1] ∈ xs := List.getElem_mem hi
    rw [outerBoundaryDarts_faceSucc_eq_formPerm B
      (outerBoundaryDarts_mem_isOuter B hmem)]
    have hform := List.formPerm_apply_getElem xs (outerBoundaryDarts_nodup B)
      (ℓ - 1) hi
    simpa only [Nat.sub_add_cancel hl, Nat.mod_eq_of_lt hj] using hform
  have hleft : xs[ℓ - 1] = B.leftPath.darts.get
      ⟨ℓ - 1, by rw [B.leftPath.darts_length]; omega⟩ := by
    have hzero : (B.leftPath.darts ++
        B.rightPath.darts.reverse.map B.map.edgeInv)[ℓ - 1]'(by
          simp only [List.length_append, List.length_map, List.length_reverse,
            B.leftPath.darts_length, B.rightPath.darts_length]; omega) =
        B.leftPath.darts[ℓ - 1]'(by rw [B.leftPath.darts_length]; omega) :=
      List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)
    simpa only [xs, outerBoundaryDarts, List.get_eq_getElem] using hzero
  have hright : xs[ℓ] = B.map.edgeInv (B.rightPath.darts.get
      ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩) := by
    have hzero : (B.leftPath.darts ++
        B.rightPath.darts.reverse.map B.map.edgeInv)[ℓ]'(by
          simp only [List.length_append, List.length_map, List.length_reverse,
            B.leftPath.darts_length, B.rightPath.darts_length]; omega) =
        B.map.edgeInv (B.rightPath.darts[r - 1]'(by
          rw [B.rightPath.darts_length]; omega)) := by
      rw [List.getElem_append_right (by rw [B.leftPath.darts_length])]
      simp only [B.leftPath.darts_length, Nat.sub_self, List.getElem_map,
        List.getElem_reverse, B.rightPath.darts_length, Nat.sub_zero]
    simpa only [xs, outerBoundaryDarts, List.get_eq_getElem] using hzero
  simpa only [hleft, hright] using hstep

/-- The outgoing block has a unique right extreme. Helper toward Definition 3.13 -/
theorem exists_rightmost_outgoing (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃! d, dartTailVertex B.map d = v ∧ B.map.tail d ∧
      ¬ B.map.tail (B.map.rot.symm d) := by
  obtain ⟨li, ro, _, _, hv, ho, _, hn, _, _, _, hu⟩ := B.incoming_block v hs ht
  exact ⟨ro, ⟨hv, ho, hn⟩, fun q hq => hu q hq.1 hq.2.1 hq.2.2⟩

/-- Rightmost outgoing dart, in clockwise (`rot.symm`) order: the last
outgoing dart before the incoming block. At the source the outer corner
selects the first right-boundary dart. Helper toward Definition 3.13 -/
@[expose] noncomputable def out (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (ht : v ≠ B.sink) : D := by
  classical
  exact if hs : v = B.source then
    B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)
  else Classical.choose (exists_rightmost_outgoing B v hs ht)

/-- The incoming selector stores the reverse dart based at the vertex. It
is the first incoming dart after the rightmost outgoing dart in clockwise
order; the sink's outer corner selects the final right-boundary edge. -/
@[expose] noncomputable def inc (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (_hs : v ≠ B.source) : D := by
  classical
  exact if ht : v = B.sink then
    B.map.edgeInv (B.rightPath.darts.get
      ⟨r - 1, by rw [B.rightPath.darts_length]; have := B.right_length_pos; omega⟩)
  else B.map.rot.symm (B.out v ht)

/-- Incidence, orientation and the internal outgoing extreme. Helper toward -/
theorem out_spec (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (ht : v ≠ B.sink) :
    dartTailVertex B.map (B.out v ht) = v ∧ B.map.tail (B.out v ht) ∧
      (v ≠ B.source → ¬ B.map.tail (B.map.rot.symm (B.out v ht))) := by
  classical
  by_cases hs : v = B.source
  · subst v
    rw [out, dite_eq_left rfl]
    have h := B.rightPath.edge_step
      ⟨0, by rw [B.rightPath.darts_length]; exact B.right_length_pos⟩
    exact ⟨h.2.2.1.symm.trans B.rightPath.start_vertex, h.2.1,
      fun hn => (hn rfl).elim⟩
  · rw [out, dite_eq_right hs]
    have h := (Classical.choose_spec (exists_rightmost_outgoing B v hs ht)).1
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩

/-- The internal extreme uniquely specifies the outgoing dart. Helper toward -/
theorem out_eq_of_extreme (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : B.map.tail d)
    (hn : ¬ B.map.tail (B.map.rot.symm d)) : d = B.out v ht := by
  classical
  rw [out, dite_eq_right hs]
  exact (Classical.choose_spec (exists_rightmost_outgoing B v hs ht)).2
    d ⟨hv, hd, hn⟩

private theorem rot_vertex (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.rot d) = dartTailVertex M d := by
  have h := rot_inv_vertex M (M.rot d)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- Incidence, reverse orientation and the internal incoming extreme. Helper -/
theorem inc_spec (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) :
    dartTailVertex B.map (B.inc v hs) = v ∧ ¬ B.map.tail (B.inc v hs) ∧
      (v ≠ B.sink → B.map.tail (B.map.rot (B.inc v hs))) := by
  classical
  by_cases ht : v = B.sink
  · subst v
    rw [inc, dite_eq_left rfl]
    have h := B.rightPath.edge_step
      ⟨r - 1, by rw [B.rightPath.darts_length]; have := B.right_length_pos; omega⟩
    have he : r - 1 + 1 = r := Nat.sub_add_cancel B.right_length_pos
    have hv : dartHeadVertex B.map (B.rightPath.darts.get
        ⟨r - 1, by have := B.rightPath.darts_length; omega⟩) = B.sink := by
      rw [← h.2.2.2]
      simpa only [he] using B.rightPath.end_vertex
    exact ⟨hv, (B.map.tail_iff _ (B.noMissingDarts _)).mp h.2.1,
      fun hn => (hn rfl).elim⟩
  · rw [inc, dite_eq_right ht]
    have h := B.out_spec v ht
    exact ⟨(rot_inv_vertex B.map _).trans h.1, h.2.2 hs,
      fun _ => by simpa only [Equiv.apply_symm_apply] using h.2.1⟩

/-- The internal incoming extreme uniquely specifies the reverse dart. -/
theorem inc_eq_of_extreme (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : ¬ B.map.tail d)
    (hn : B.map.tail (B.map.rot d)) : d = B.inc v hs := by
  classical
  have he := B.out_eq_of_extreme v hs ht (B.map.rot d)
    ((rot_vertex B.map d).trans hv) hn (by simpa only [Equiv.symm_apply_apply] using hd)
  rw [inc, dite_eq_right ht]
  simpa only [Equiv.symm_apply_apply] using congrArg B.map.rot.symm he

/-- Every edge is selected by its tail's rightmost outgoing selector. Helper -/
@[expose] def Out (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) : Prop :=
  ∀ i : Fin P.darts.length,
    ∃ h : dartTailVertex B.map (P.darts.get i) ≠ B.sink,
      P.darts.get i = B.out _ h

/-- Every edge is selected by its head's rightmost incoming selector, stored
in reverse orientation. Helper toward Definition 3.13 -/
@[expose] def In (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) : Prop :=
  ∀ i : Fin P.darts.length,
    ∃ h : dartHeadVertex B.map (P.darts.get i) ≠ B.source,
      B.map.edgeInv (P.darts.get i) = B.inc _ h

private theorem path_vertex_ne_start
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : ℕ) (hi : 0 < i) (hin : i ≤ n) :
    P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ≠ s := by
  intro h
  have he := P.vertices_nodup.get_inj_iff.mp (h.trans P.start_vertex.symm)
  have := congrArg Fin.val he
  simp only at this
  omega

private theorem path_vertex_ne_end
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : ℕ) (hi : i < n) :
    P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ≠ t := by
  intro h
  have he := P.vertices_nodup.get_inj_iff.mp (h.trans P.end_vertex.symm)
  have := congrArg Fin.val he
  simp only at this
  omega

private theorem rightPath_face_successor
    (B : BipolarMapWithBoundaryBase D ℓ r) (i : ℕ) (hi : i + 1 < r) :
    B.map.faceSucc (B.map.edgeInv (B.rightPath.darts[i + 1]'(by
      rw [B.rightPath.darts_length]; exact hi))) =
      B.map.edgeInv (B.rightPath.darts[i]'(by have := B.rightPath.darts_length; omega)) := by
  let xs := outerBoundaryDarts B
  let k := ℓ + (r - 2 - i)
  have hlen : xs.length = ℓ + r := outerBoundaryDarts_length B
  have hk : k < xs.length := by dsimp [k]; omega
  have hk' : k + 1 < xs.length := by dsimp [k]; omega
  have hcurrent : xs[k] = B.map.edgeInv (B.rightPath.darts[i + 1]'(by
      rw [B.rightPath.darts_length]; omega)) := by
    change (B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.edgeInv)[k]'
      (by simpa only [xs, outerBoundaryDarts] using hk) = _
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [k]; omega)]
    simp only [List.getElem_map, List.getElem_reverse, B.leftPath.darts_length,
      B.rightPath.darts_length]
    congr 2
    dsimp [k]
    omega
  have hnext : xs[k + 1] = B.map.edgeInv (B.rightPath.darts[i]'(by
      rw [B.rightPath.darts_length]; omega)) := by
    change (B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.edgeInv)[k + 1]'
      (by simpa only [xs, outerBoundaryDarts] using hk') = _
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [k]; omega)]
    simp only [List.getElem_map, List.getElem_reverse, B.leftPath.darts_length,
      B.rightPath.darts_length]
    congr 2
    dsimp [k]
    omega
  have ho := outerBoundaryDarts_mem_isOuter B (List.getElem_mem hk)
  have h := List.formPerm_apply_getElem xs (outerBoundaryDarts_nodup B) k hk
  have hface : B.map.faceSucc xs[k] = xs[k + 1] := by
    rw [outerBoundaryDarts_faceSucc_eq_formPerm B ho]
    simpa only [Nat.mod_eq_of_lt hk'] using h
  simpa only [hcurrent, hnext] using hface

/-- The right boundary follows the outgoing selector, fixing the rightmost
convention also at the source. Helper toward Definition 3.13 -/
theorem out_rightPath (B : BipolarMapWithBoundaryBase D ℓ r) : B.Out B.rightPath := by
  classical
  intro i
  have hi : i.val < r := by simpa only [B.rightPath.darts_length] using i.isLt
  have h := B.rightPath.edge_step i
  have ht : dartTailVertex B.map (B.rightPath.darts.get i) ≠ B.sink := by
    rw [← h.2.2.1]
    exact path_vertex_ne_end B.rightPath i.val hi
  refine ⟨ht, ?_⟩
  by_cases hz : i.val = 0
  · have hv : dartTailVertex B.map (B.rightPath.darts.get i) = B.source := by
      rw [← h.2.2.1]
      simpa only [hz] using B.rightPath.start_vertex
    simp only [out, hv, ↓reduceDIte, SimpleDirectedDartPath.firstDart]
    congr 1
    exact Fin.ext hz
  · have hs : dartTailVertex B.map (B.rightPath.darts.get i) ≠ B.source := by
      rw [← h.2.2.1]
      exact path_vertex_ne_start B.rightPath i.val (by omega) (by omega)
    apply B.out_eq_of_extreme _ hs ht _ rfl h.2.1
    have hf := rightPath_face_successor B (i.val - 1) (by omega)
    have he : i.val - 1 + 1 = i.val := by omega
    simp only [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply, B.map.edgeInv_invol, he] at hf
    have hp := B.rightPath.edge_step
      ⟨i.val - 1, by have := B.rightPath.darts_length; omega⟩
    rw [show B.map.rot.symm (B.rightPath.darts.get i) =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨i.val - 1, by have := B.rightPath.darts_length; omega⟩) from hf]
    exact (B.map.tail_iff _ (B.noMissingDarts _)).mp hp.2.1

/-- The right boundary follows the incoming selector, fixing the rightmost
convention also at the sink. Helper toward Definition 3.13 -/
theorem in_rightPath (B : BipolarMapWithBoundaryBase D ℓ r) : B.In B.rightPath := by
  classical
  intro i
  have hi : i.val < r := by simpa only [B.rightPath.darts_length] using i.isLt
  have h := B.rightPath.edge_step i
  have hs : dartHeadVertex B.map (B.rightPath.darts.get i) ≠ B.source := by
    rw [← h.2.2.2]
    exact path_vertex_ne_start B.rightPath (i.val + 1) (by omega) (by omega)
  refine ⟨hs, ?_⟩
  by_cases hl : i.val + 1 = r
  · have hv : dartHeadVertex B.map (B.rightPath.darts.get i) = B.sink := by
      rw [← h.2.2.2]
      simpa only [hl] using B.rightPath.end_vertex
    simp only [inc, hv, ↓reduceDIte]
    congr 2
    apply Fin.ext
    change i.val = r - 1
    omega
  · have ht : dartHeadVertex B.map (B.rightPath.darts.get i) ≠ B.sink := by
      rw [← h.2.2.2]
      exact path_vertex_ne_end B.rightPath (i.val + 1) (by omega)
    apply B.inc_eq_of_extreme _ hs ht _ rfl
      ((B.map.tail_iff _ (B.noMissingDarts _)).mp h.2.1)
    have hf := rightPath_face_successor B i.val (by omega)
    simp only [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply, B.map.edgeInv_invol] at hf
    have he := congrArg B.map.rot hf
    change B.map.rot (B.map.rot.symm _) = _ at he
    rw [Equiv.apply_symm_apply] at he
    simp only [List.get_eq_getElem]
    rw [← he]
    exact (B.rightPath.edge_step
      ⟨i.val + 1, by have := B.rightPath.darts_length; omega⟩).2.1

private theorem path_reaches {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    Relation.ReflTransGen M.directedStep s t := by
  induction n generalizing s with
  | zero =>
      have hst : s = t := P.start_vertex.symm.trans P.end_vertex
      subst t
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      have h := P.edge_step ⟨0, by rw [P.darts_length]; omega⟩
      have he : M.directedStep s (P.vertices.get ⟨1, by rw [P.vertices_length]; omega⟩) :=
        ⟨_, h.1, h.2.1, h.2.2.1.symm.trans P.start_vertex, h.2.2.2.symm⟩
      have Q := P.suffix ⟨1, by omega⟩
      have hQ := ih (by simpa only [Nat.add_sub_cancel] using Q)
      exact hQ.head he

private theorem path_start_reaches {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n)
    {v : MapVertex M} (hv : v ∈ P.vertices) :
    Relation.ReflTransGen M.directedStep s v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hin : i.val < n + 1 := by have := i.isLt; have := P.vertices_length; omega
  have h := path_reaches (P.prefix ⟨i.val, hin⟩)
  simpa only [hi] using h

private theorem path_reaches_end {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n)
    {v : MapVertex M} (hv : v ∈ P.vertices) :
    Relation.ReflTransGen M.directedStep v t := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hin : i.val < n + 1 := by have := i.isLt; have := P.vertices_length; omega
  have h := path_reaches (P.suffix ⟨i.val, hin⟩)
  simpa only [hi] using h

private def emptyPath (M : DirectedMapWithMissing D) (v : MapVertex M) :
    SimpleDirectedDartPath M v v 0 where
  darts := []
  vertices := [v]
  darts_length := rfl
  vertices_length := rfl
  vertices_nodup := List.nodup_singleton v
  start_vertex := rfl
  end_vertex := rfl
  edge_step := by intro i; exact Fin.elim0 i

private def prependPath (M : DirectedMapWithMissing D) (ha : M.IsAcyclic)
    {u v t : MapVertex M} {n : ℕ} (d : D)
    (hd : ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = u ∧ dartHeadVertex M d = v)
    (P : SimpleDirectedDartPath M v t n) : SimpleDirectedDartPath M u t (n + 1) := by
  have hnot : u ∉ P.vertices := by
    intro hu
    exact ha u (Relation.TransGen.head' ⟨d, hd⟩ (path_start_reaches P hu))
  refine {
    darts := d :: P.darts
    vertices := u :: P.vertices
    darts_length := by simp only [List.length_cons, P.darts_length]
    vertices_length := by simp only [List.length_cons, P.vertices_length]
    vertices_nodup := List.nodup_cons.mpr ⟨hnot, P.vertices_nodup⟩
    start_vertex := rfl
    end_vertex := by simpa only [List.get_eq_getElem, List.getElem_cons_succ] using P.end_vertex
    edge_step := ?_ }
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      Nat.zero_add, List.getElem_cons_succ]
    exact ⟨hd.1, hd.2.1, hd.2.2.1.symm, P.start_vertex.trans hd.2.2.2.symm⟩
  · simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
      using P.edge_step j

private def appendPath (M : DirectedMapWithMissing D) (ha : M.IsAcyclic)
    {s u v : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s u n) (d : D)
    (hd : ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = u ∧ dartHeadVertex M d = v) :
    SimpleDirectedDartPath M s v (n + 1) := by
  have hnot : v ∉ P.vertices := by
    intro hv
    exact ha v (Relation.TransGen.tail' (path_reaches_end P hv) ⟨d, hd⟩)
  refine {
    darts := P.darts ++ [d]
    vertices := P.vertices ++ [v]
    darts_length := by simp only [List.length_append, List.length_singleton, P.darts_length]
    vertices_length := by simp only [List.length_append, List.length_singleton, P.vertices_length]
    vertices_nodup := by
      rw [List.nodup_append]
      refine ⟨P.vertices_nodup, List.nodup_singleton v, ?_⟩
      intro a ha b hb hab
      have hb' : b = v := List.mem_singleton.mp hb
      exact hnot ((hab.trans hb') ▸ ha)
    start_vertex := by
      change (P.vertices ++ [v])[0]'_ = s
      rw [List.getElem_append_left (by rw [P.vertices_length]; omega : 0 < P.vertices.length)]
      exact P.start_vertex
    end_vertex := by simp only [List.get_eq_getElem,
      List.getElem_append_right (by rw [P.vertices_length]), P.vertices_length,
      Nat.sub_self, List.getElem_singleton]
    edge_step := ?_ }
  intro i
  have hi : i.val < n + 1 := by have := i.isLt; simp only [List.length_append,
    List.length_singleton, P.darts_length] at this; exact this
  by_cases hin : i.val < n
  · have h := P.edge_step ⟨i.val, by have := P.darts_length; omega⟩
    simpa only [List.get_eq_getElem,
      List.getElem_append_left (by have := P.darts_length; omega : i.val < P.darts.length),
      List.getElem_append_left (by have := P.vertices_length; omega : i.val < P.vertices.length),
      List.getElem_append_left (by have := P.vertices_length; omega : i.val + 1 < P.vertices.length)] using h
  · have he : i.val = n := by omega
    have hlenD := P.darts_length
    simp only [List.get_eq_getElem, he,
      List.getElem_append_right (by omega : n ≥ P.darts.length),
      List.getElem_append_left (by rw [P.vertices_length]; omega : n < P.vertices.length),
      List.getElem_append_right (by rw [P.vertices_length] : n + 1 ≥ P.vertices.length),
      P.darts_length, P.vertices_length, Nat.sub_self, List.getElem_singleton]
    exact ⟨hd.1, hd.2.1, P.end_vertex.trans hd.2.2.1.symm, hd.2.2.2.symm⟩

private theorem reach_wellFounded (B : BipolarMapWithBoundaryBase D ℓ r)
    (backwards : Bool) : WellFounded (Relation.TransGen
      (fun a b : MapVertex B.map => if backwards then B.map.directedStep a b else B.map.directedStep b a)) := by
  let R := Relation.TransGen
    (fun a b : MapVertex B.map => if backwards then B.map.directedStep a b else B.map.directedStep b a)
  let ht : IsTrans (MapVertex B.map) R := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  let hi : Std.Irrefl R := ⟨by
    intro a h
    cases backwards with
    | false => exact B.acyclic a (Relation.transGen_swap.mp h)
    | true => exact B.acyclic a h⟩
  let hs : IsStrictOrder (MapVertex B.map) R := @IsStrictOrder.mk _ R hi ht
  exact Set.wellFoundedOn_univ.mp
    (@Set.Finite.wellFoundedOn (MapVertex B.map) R hs Set.univ Set.finite_univ)

private theorem out_of_mem (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n : ℕ} (P : SimpleDirectedDartPath B.map a b n)
    (hP : B.Out P) {d : D} (hd : d ∈ P.darts) :
    ∃ h : dartTailVertex B.map d ≠ B.sink, d = B.out _ h := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact hP i

private theorem in_of_mem (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n : ℕ} (P : SimpleDirectedDartPath B.map a b n)
    (hP : B.In P) {d : D} (hd : d ∈ P.darts) :
    ∃ h : dartHeadVertex B.map d ≠ B.source, B.map.edgeInv d = B.inc _ h := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact hP i

/-- Iterating the outgoing extreme terminates at the sink. Acyclicity
prevents a repeated vertex and finiteness makes reverse reachability well -/
theorem exists_out_path (B : BipolarMapWithBoundaryBase D ℓ r)
    (u : MapVertex B.map) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map u B.sink n, B.Out P := by
  classical
  induction u using (reach_wellFounded B false).induction with
  | h u ih =>
      by_cases hu : u = B.sink
      · subst u
        exact ⟨0, emptyPath B.map B.sink, fun i => Fin.elim0 i⟩
      · let d := B.out u hu
        have hd := B.out_spec u hu
        have hdu : dartTailVertex B.map d = u := hd.1
        have he : B.map.directedStep u (dartHeadVertex B.map d) :=
          ⟨d, B.noMissingDarts d, hd.2.1, hd.1, rfl⟩
        obtain ⟨n, Q, hQ⟩ := ih (dartHeadVertex B.map d) (Relation.TransGen.single he)
        let P := prependPath B.map B.acyclic d
          ⟨B.noMissingDarts d, hd.2.1, hd.1, rfl⟩ Q
        refine ⟨n + 1, P, ?_⟩
        have hsel : ∀ e ∈ P.darts,
            ∃ ht : dartTailVertex B.map e ≠ B.sink, e = B.out _ ht := by
          intro e he
          change e ∈ d :: Q.darts at he
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨by simpa only [hdu] using hu, ?_⟩
            exact congrArg (fun w : {w : MapVertex B.map // w ≠ B.sink} => B.out w.1 w.2)
              (show (⟨u, hu⟩ : {w : MapVertex B.map // w ≠ B.sink}) =
                ⟨dartTailVertex B.map d, by simpa only [hdu] using hu⟩ from
                  Subtype.ext hdu.symm)
          · exact out_of_mem B Q hQ he
        intro i
        exact hsel _ (List.get_mem _ _)

/-- Iterating the reverse incoming extreme terminates at the source. The
forward result has no repeated vertex. Helper toward Definition 3.13 -/
theorem exists_in_path (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source v n, B.In P := by
  classical
  induction v using (reach_wellFounded B true).induction with
  | h v ih =>
      by_cases hv : v = B.source
      · subst v
        exact ⟨0, emptyPath B.map B.source, fun i => Fin.elim0 i⟩
      · let d := B.map.edgeInv (B.inc v hv)
        have hi := B.inc_spec v hv
        have hd : B.map.tail d := by
          by_contra hn
          exact hi.2.1 ((B.map.tail_iff _ (B.noMissingDarts _)).mpr hn)
        have hhead : dartHeadVertex B.map d = v := by
          simpa only [d, dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using hi.1
        have he : B.map.directedStep (dartTailVertex B.map d) v :=
          ⟨d, B.noMissingDarts d, hd, rfl, hhead⟩
        obtain ⟨n, Q, hQ⟩ := ih (dartTailVertex B.map d) (Relation.TransGen.single he)
        let P := appendPath B.map B.acyclic Q d
          ⟨B.noMissingDarts d, hd, rfl, hhead⟩
        refine ⟨n + 1, P, ?_⟩
        have hsel : ∀ e ∈ P.darts,
            ∃ hs : dartHeadVertex B.map e ≠ B.source, B.map.edgeInv e = B.inc _ hs := by
          intro e he
          change e ∈ Q.darts ++ [d] at he
          rcases List.mem_append.mp he with he | he
          · exact in_of_mem B Q hQ he
          · have he' : e = d := List.mem_singleton.mp he
            subst e
            refine ⟨by simpa only [hhead] using hv, ?_⟩
            simp only [hhead, d, B.map.edgeInv_invol]
        intro i
        exact hsel _ (List.get_mem _ _)

/-- Both internal extremes at a non-pole vertex. Helper toward Definition -/
theorem internal_extremes (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ¬ B.map.tail (B.map.rot.symm (B.out v ht)) ∧
      B.map.tail (B.map.rot (B.inc v hs)) :=
  ⟨(B.out_spec v ht).2.2 hs, (B.inc_spec v hs).2.2 ht⟩

private theorem out_dart_eq (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b c e : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) (Q : SimpleDirectedDartPath B.map c e m)
    (hP : B.Out P) (hQ : B.Out Q) (i : Fin P.darts.length) (j : Fin Q.darts.length)
    (hv : dartTailVertex B.map (P.darts.get i) = dartTailVertex B.map (Q.darts.get j)) :
    P.darts.get i = Q.darts.get j := by
  obtain ⟨hi, he⟩ := hP i
  obtain ⟨hj, hf⟩ := hQ j
  have hx : B.out _ hi = B.out _ hj := by congr 1
  exact he.trans (hx.trans hf.symm)

private theorem in_dart_eq (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b c e : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) (Q : SimpleDirectedDartPath B.map c e m)
    (hP : B.In P) (hQ : B.In Q) (i : Fin P.darts.length) (j : Fin Q.darts.length)
    (hv : dartHeadVertex B.map (P.darts.get i) = dartHeadVertex B.map (Q.darts.get j)) :
    P.darts.get i = Q.darts.get j := by
  obtain ⟨hi, he⟩ := hP i
  obtain ⟨hj, hf⟩ := hQ j
  have hx : B.inc _ hi = B.inc _ hj := by congr 1
  exact B.map.edgeInv.injective (he.trans (hx.trans hf.symm))

/-- Two outgoing-selected paths with the same endpoints have identical dart -/
theorem out_path_darts_eq (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) (Q : SimpleDirectedDartPath B.map a b m)
    (hP : B.Out P) (hQ : B.Out Q) : Q.darts = P.darts := by
  have hv : ∀ i (hin : i ≤ n) (him : i ≤ m),
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ =
        Q.vertices.get ⟨i, by rw [Q.vertices_length]; omega⟩ := by
    intro i
    induction i with
    | zero => intro _ _; exact P.start_vertex.trans Q.start_vertex.symm
    | succ i ih =>
        intro hin him
        have hp := P.edge_step ⟨i, by rw [P.darts_length]; omega⟩
        have hq := Q.edge_step ⟨i, by rw [Q.darts_length]; omega⟩
        have hd := out_dart_eq B P Q hP hQ
          ⟨i, by rw [P.darts_length]; omega⟩ ⟨i, by rw [Q.darts_length]; omega⟩
          (hp.2.2.1.symm.trans ((ih (by omega) (by omega)).trans hq.2.2.1))
        exact hp.2.2.2.trans ((congrArg (dartHeadVertex B.map) hd).trans hq.2.2.2.symm)
  have hnm : n = m := by
    apply Nat.le_antisymm
    · by_contra h
      have hne := path_vertex_ne_end P m (by omega)
      exact hne ((hv m (by omega) (by omega)).trans Q.end_vertex)
    · by_contra h
      have hne := path_vertex_ne_end Q n (by omega)
      exact hne ((hv n (by omega) (by omega)).symm.trans P.end_vertex)
  subst m
  apply List.ext_getElem (by rw [Q.darts_length, P.darts_length])
  intro i hiQ hiP
  have hin : i < n := by have := P.darts_length; omega
  have hp := P.edge_step ⟨i, hiP⟩
  have hq := Q.edge_step ⟨i, hiQ⟩
  exact (out_dart_eq B P Q hP hQ ⟨i, hiP⟩ ⟨i, hiQ⟩
    (hp.2.2.1.symm.trans ((hv i (by omega) (by omega)).trans hq.2.2.1))).symm

/-- Two incoming-selected paths with the same endpoints have identical dart -/
theorem in_path_darts_eq (B : BipolarMapWithBoundaryBase D ℓ r)
    {a b : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map a b n) (Q : SimpleDirectedDartPath B.map a b m)
    (hP : B.In P) (hQ : B.In Q) : Q.darts = P.darts := by
  have hv : ∀ i (hin : i ≤ n) (him : i ≤ m),
      P.vertices.get ⟨n - i, by rw [P.vertices_length]; omega⟩ =
        Q.vertices.get ⟨m - i, by rw [Q.vertices_length]; omega⟩ := by
    intro i
    induction i with
    | zero => intro _ _; exact P.end_vertex.trans Q.end_vertex.symm
    | succ i ih =>
        intro hin him
        have hpi : n - (i + 1) < P.darts.length := by rw [P.darts_length]; omega
        have hqi : m - (i + 1) < Q.darts.length := by rw [Q.darts_length]; omega
        have hp := P.edge_step ⟨n - (i + 1), hpi⟩
        have hq := Q.edge_step ⟨m - (i + 1), hqi⟩
        have hprev := ih (by omega) (by omega)
        have hpn : n - (i + 1) + 1 = n - i := by omega
        have hqm : m - (i + 1) + 1 = m - i := by omega
        have hh : dartHeadVertex B.map (P.darts.get ⟨n - (i + 1), hpi⟩) =
            dartHeadVertex B.map (Q.darts.get ⟨m - (i + 1), hqi⟩) := by
          rw [← hp.2.2.2, ← hq.2.2.2]
          simpa only [hpn, hqm] using hprev
        have hd := in_dart_eq B P Q hP hQ _ _ hh
        exact hp.2.2.1.trans ((congrArg (dartTailVertex B.map) hd).trans hq.2.2.1.symm)
  have hnm : n = m := by
    apply Nat.le_antisymm
    · by_contra h
      have hne := path_vertex_ne_start P (n - m) (by omega) (by omega)
      have he := hv m (by omega) (by omega)
      simp only [Nat.sub_self] at he
      exact hne (he.trans Q.start_vertex)
    · by_contra h
      have hne := path_vertex_ne_start Q (m - n) (by omega) (by omega)
      have he := hv n (by omega) (by omega)
      simp only [Nat.sub_self] at he
      exact hne (he.symm.trans P.start_vertex)
  subst m
  apply List.ext_getElem (by rw [Q.darts_length, P.darts_length])
  intro i hiQ hiP
  have hin : i < n := by have := P.darts_length; omega
  have hp := P.edge_step ⟨i, hiP⟩
  have hq := Q.edge_step ⟨i, hiQ⟩
  have he := hv (n - (i + 1)) (by omega) (by omega)
  have hidx : n - (n - (i + 1)) = i + 1 := by omega
  have he' : P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩ =
      Q.vertices.get ⟨i + 1, by rw [Q.vertices_length]; omega⟩ := by
    simpa only [hidx] using he
  exact (in_dart_eq B P Q hP hQ ⟨i, hiP⟩ ⟨i, hiQ⟩
    (hp.2.2.2.symm.trans (he'.trans hq.2.2.2))).symm

/-- Existence and uniqueness of the rightmost directed path started at an
arbitrary vertex, including the empty path at the sink. Helper toward -/
theorem exists_unique_out_path (B : BipolarMapWithBoundaryBase D ℓ r)
    (u : MapVertex B.map) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map u B.sink n,
      B.Out P ∧ ∀ m (Q : SimpleDirectedDartPath B.map u B.sink m),
        B.Out Q → Q.darts = P.darts := by
  obtain ⟨n, P, hP⟩ := B.exists_out_path u
  exact ⟨n, P, hP, fun _ Q hQ => B.out_path_darts_eq P Q hP hQ⟩

/-- Existence and uniqueness of the rightmost directed path ending at an
arbitrary vertex, including the empty path at the source. Helper toward -/
theorem exists_unique_in_path (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source v n,
      B.In P ∧ ∀ m (Q : SimpleDirectedDartPath B.map B.source v m),
        B.In Q → Q.darts = P.darts := by
  obtain ⟨n, P, hP⟩ := B.exists_in_path v
  exact ⟨n, P, hP, fun _ Q hQ => B.in_path_darts_eq P Q hP hQ⟩

end BipolarMapWithBoundaryBase
end DirectedDistances.PlanarMap
