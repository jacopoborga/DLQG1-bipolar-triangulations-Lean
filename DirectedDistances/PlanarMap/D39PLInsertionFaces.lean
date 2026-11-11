/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLChordInsertion

/-! # Face walks after inserting a chord

Helpers toward Proposition 5.16. The corner after `a` belongs to the old
left-face orbit of `a`, equivalently of `edgeInv (rot a)`. The positive
new dart first visits `b`; the negative new dart first visits `a`. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace D39FiniteBall

variable (B : D39FiniteBall)

/-- Helper toward Proposition 5.16: the old face successor immediately
before the corner after `a` arrives at `a`. -/
@[simp] theorem faceSucc_edgeInv_rot (a : B.D) :
    B.map.faceSucc (B.map.edgeInv (B.map.rot a)) = a := by
  change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv (B.map.rot a))) = a
  rw [B.map.edgeInv_invol, Equiv.symm_apply_apply]

/-- Helper toward Proposition 5.16: both bordering darts of the corner
after `a` represent the same old left-face orbit. -/
theorem corner_sameCycle (a : B.D) :
    B.map.faceSucc.SameCycle (B.map.edgeInv (B.map.rot a)) a := by
  have h : B.map.faceSucc.SameCycle (B.map.edgeInv (B.map.rot a))
      (B.map.faceSucc (B.map.edgeInv (B.map.rot a))) :=
    Equiv.Perm.SameCycle.rfl.apply_right
  simpa only [B.faceSucc_edgeInv_rot a] using h

/-- Helper toward Proposition 5.16: the two cut locations of the old
face permutation are distinct. -/
theorem chord_face_cuts_ne (a b : B.D) (hab : a ≠ b) :
    B.map.edgeInv (B.map.rot a) ≠ B.map.edgeInv (B.map.rot b) :=
  fun h => hab (B.map.rot.injective (B.map.edgeInv.injective h))

/-- Helper toward Proposition 5.16: the full old-dart face-successor
formula, including the two cut locations. -/
theorem chordMap_faceSucc_inl (a b : B.D) (hab : a ≠ b) (x : B.D) :
    (B.chordMap a b hab).faceSucc (.inl x) =
      if B.map.edgeInv x = B.map.rot a then .inr true
      else if B.map.edgeInv x = B.map.rot b then .inr false
      else .inl (B.map.faceSucc x) := rfl

/-- Helper toward Proposition 5.16: the old dart before the first corner
now enters the positive new dart. -/
@[simp] theorem chordMap_faceSucc_cut_a (a b : B.D) (hab : a ≠ b) :
    (B.chordMap a b hab).faceSucc (.inl (B.map.edgeInv (B.map.rot a))) =
      .inr true := by
  rw [B.chordMap_faceSucc_inl]
  simp only [B.map.edgeInv_invol, ↓reduceIte]

/-- Helper toward Proposition 5.16: the old dart before the second corner
now enters the negative new dart. -/
@[simp] theorem chordMap_faceSucc_cut_b (a b : B.D) (hab : a ≠ b) :
    (B.chordMap a b hab).faceSucc (.inl (B.map.edgeInv (B.map.rot b))) =
      .inr false := by
  rw [B.chordMap_faceSucc_inl]
  simp only [B.map.edgeInv_invol, Equiv.apply_eq_iff_eq, Ne.symm hab,
    ↓reduceIte]

/-- Helper toward Proposition 5.16: the positive chord dart continues at
the second old corner. -/
@[simp] theorem chordMap_faceSucc_true (a b : B.D) (hab : a ≠ b) :
    (B.chordMap a b hab).faceSucc (.inr true) = .inl b := rfl

/-- Helper toward Proposition 5.16: the negative chord dart continues at
the first old corner. -/
@[simp] theorem chordMap_faceSucc_false (a b : B.D) (hab : a ≠ b) :
    (B.chordMap a b hab).faceSucc (.inr false) = .inl a := rfl

/-- Helper toward Proposition 5.16: away from the two cut darts, face
succession commutes with the old-dart inclusion. -/
theorem chordMap_faceSucc_other (a b : B.D) (hab : a ≠ b) (x : B.D)
    (ha : x ≠ B.map.edgeInv (B.map.rot a))
    (hb : x ≠ B.map.edgeInv (B.map.rot b)) :
    (B.chordMap a b hab).faceSucc (.inl x) = .inl (B.map.faceSucc x) := by
  have ha' : B.map.edgeInv x ≠ B.map.rot a := by
    intro h
    exact ha ((B.map.edgeInv_invol x).symm.trans (congrArg B.map.edgeInv h))
  have hb' : B.map.edgeInv x ≠ B.map.rot b := by
    intro h
    exact hb ((B.map.edgeInv_invol x).symm.trans (congrArg B.map.edgeInv h))
  rw [B.chordMap_faceSucc_inl]
  simp only [ha', hb', ↓reduceIte]

/-- Helper toward Proposition 5.16: the geometric corner after `a` lies
in the left face represented by either of its two bordering darts. -/
theorem initialSector_subset_plDartFace_edgeInv_rot {V : Type*} (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert) (a : B.D) :
    P.initialSector a S.radius ⊆
      (B.plDartFace vert P hvert (B.map.edgeInv (B.map.rot a))).val := by
  rw [B.plDartFace_eq_of_sameCycle vert P hvert _ _ (B.corner_sameCycle a)]
  exact B.initialSector_subset_plDartFace vert P hvert S a

/-- Helper toward Proposition 5.16: an old face step whose destination
is neither selected corner is unchanged by chord insertion. -/
theorem chordMap_faceSucc_of_next_ne (a b : B.D) (hab : a ≠ b) (x : B.D)
    (ha : B.map.faceSucc x ≠ a) (hb : B.map.faceSucc x ≠ b) :
    (B.chordMap a b hab).faceSucc (.inl x) = .inl (B.map.faceSucc x) := by
  apply B.chordMap_faceSucc_other
  · intro h
    exact ha (h ▸ B.faceSucc_edgeInv_rot a)
  · intro h
    exact hb (h ▸ B.faceSucc_edgeInv_rot b)

/-- Helper toward Proposition 5.16: before its first return to the other
corner, either new dart follows the corresponding explicit old face arc.
Here `i` is the walk distance from `b` to `a` for `t = true`, and from
`a` to `b` for `t = false`. -/
theorem chordMap_faceSucc_iterate_new (a b : B.D) (hab : a ≠ b) (t : Bool)
    (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b)
    (k : ℕ) (hk : k < i) :
    ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[k + 1]
      (.inr t) = .inl ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) := by
  induction k with
  | zero =>
    cases t <;> rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hs : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) ≠
        cond t b a := by
      intro h
      have heq : (B.map.faceSucc : B.D → B.D)^[k + 1] (cond t b a) =
          (B.map.faceSucc : B.D → B.D)^[0] (cond t b a) := by
        simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using h
      have hn := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by omega : k + 1 < Function.minimalPeriod B.map.faceSucc (cond t b a))
        (by omega : 0 < Function.minimalPeriod B.map.faceSucc (cond t b a))).mp heq
      omega
    have he : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) ≠
        cond t a b := by
      intro h
      have heq : (B.map.faceSucc : B.D → B.D)^[k + 1] (cond t b a) =
          (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) := by
        simpa only [Function.iterate_succ_apply', hwalk] using h
      have hn := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by omega : k + 1 < Function.minimalPeriod B.map.faceSucc (cond t b a)) hi).mp heq
      omega
    have hnext : (B.chordMap a b hab).faceSucc
        (.inl ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a))) =
        .inl (B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a))) := by
      cases t
      · exact B.chordMap_faceSucc_of_next_ne a b hab _ hs he
      · exact B.chordMap_faceSucc_of_next_ne a b hab _ he hs
    rw [hnext, Function.iterate_succ_apply']

/-- Helper toward Proposition 5.16: the first positive return of either
new face walk occurs after its old arc and one new dart. -/
theorem chordMap_faceSucc_return_new (a b : B.D) (hab : a ≠ b) (t : Bool)
    (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b) :
    ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[i + 1]
      (.inr t) = .inr t := by
  have hi0 : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    subst i
    cases t <;> simp_all
  have hpred : (B.map.faceSucc : B.D → B.D)^[i - 1] (cond t b a) =
      B.map.edgeInv (B.map.rot (cond t a b)) := by
    apply B.map.faceSucc.injective
    rw [B.faceSucc_edgeInv_rot]
    have heq : (i - 1).succ = i := by omega
    rw [← Function.iterate_succ_apply' (f := (B.map.faceSucc : B.D → B.D)), heq]
    exact hwalk
  rw [Function.iterate_succ_apply']
  have heq : i = (i - 1) + 1 := by omega
  rw [heq, B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk (i - 1) (by omega),
    hpred]
  cases t
  · exact B.chordMap_faceSucc_cut_b a b hab
  · exact B.chordMap_faceSucc_cut_a a b hab

/-- Helper toward Proposition 5.16: the minimal period of either new
face is exactly its old arc length plus one. -/
theorem chordMap_faceSucc_minimalPeriod_new (a b : B.D) (hab : a ≠ b) (t : Bool)
    (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr t) = i + 1 := by
  have hret : Function.IsPeriodicPt (B.chordMap a b hab).faceSucc (i + 1) (.inr t) :=
    B.chordMap_faceSucc_return_new a b hab t i hi hwalk
  have hpos := hret.minimalPeriod_pos (by omega : 0 < i + 1)
  apply le_antisymm (hret.minimalPeriod_le (by omega))
  by_contra h
  have hle : Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr t) ≤ i := by
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hki : k < i := by omega
  have hreturn := Function.iterate_minimalPeriod
    (f := ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool)))
    (x := (.inr t : B.D ⊕ Bool))
  rw [hk, B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk k hki] at hreturn
  cases hreturn

/-- Helper toward Proposition 5.16: the orbit of either new dart consists
exactly of that dart and the indicated old face arc, with explicit iterates. -/
theorem chordMap_faceSucc_sameCycle_new_iff (a b : B.D) (hab : a ≠ b) (t : Bool)
    (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b)
    (z : B.D ⊕ Bool) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inr t) z ↔
      z = .inr t ∨ ∃ k < i,
        z = .inl ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) := by
  let g := (B.chordMap a b hab).faceSucc
  have hret : Function.IsPeriodicPt g (i + 1) (.inr t) :=
    B.chordMap_faceSucc_return_new a b hab t i hi hwalk
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    have hiter : (g : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inr t) = z := by
      simpa only [Equiv.Perm.coe_pow] using hn
    have hmod := (hret.iterate_mod_apply n).trans hiter
    have hlt : n % (i + 1) < i + 1 := Nat.mod_lt _ (by omega)
    generalize hr : n % (i + 1) = r at hmod hlt
    cases r with
    | zero => exact Or.inl hmod.symm
    | succ k =>
      right
      refine ⟨k, by omega, ?_⟩
      exact hmod.symm.trans
        (B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk k (by omega))
  · rintro (hz | ⟨k, hk, hz⟩)
    · subst z
      exact Equiv.Perm.SameCycle.rfl
    · rw [hz, ← B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk k hk]
      have h : g.SameCycle (.inr t) ((g ^ (k + 1)) (.inr t)) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      simpa only [Equiv.Perm.coe_pow] using h

/-- Helper toward Proposition 5.16: the two new darts lie in distinct
face orbits whenever the selected corners are on the same old face. -/
theorem chordMap_new_not_sameCycle (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a) :
    ¬ (B.chordMap a b hab).faceSucc.SameCycle (.inr true) (.inr false) := by
  rw [B.chordMap_faceSucc_sameCycle_new_iff a b hab true i hi hwalk]
  rintro (h | ⟨k, _, h⟩) <;> cases h

/-- Helper toward Proposition 5.16: distinct corners on a common old face
have a strictly positive walk distance shorter than that face's period. -/
theorem chord_corner_distance_exists (a b : B.D) (hab : a ≠ b)
    (hface : B.map.faceSucc.SameCycle b a) :
    ∃ i : ℕ, 0 < i ∧ i < Function.minimalPeriod B.map.faceSucc b ∧
      (B.map.faceSucc : B.D → B.D)^[i] b = a := by
  obtain ⟨n, hn⟩ := hface.exists_nat_pow_eq
  have hiter : (B.map.faceSucc : B.D → B.D)^[n] b = a := by
    simpa only [Equiv.Perm.coe_pow] using hn
  have hp : 0 < Function.minimalPeriod B.map.faceSucc b :=
    Function.minimalPeriod_pos_of_mem_periodicPts (B.map.faceSucc.injective.mem_periodicPts b)
  refine ⟨n % Function.minimalPeriod B.map.faceSucc b, ?_, Nat.mod_lt _ hp, ?_⟩
  · by_contra h
    have hz : n % Function.minimalPeriod B.map.faceSucc b = 0 := by omega
    have hmod := (Function.iterate_mod_minimalPeriod_eq
      (f := (B.map.faceSucc : B.D → B.D)) (x := b) (n := n)).trans hiter
    rw [hz, Function.iterate_zero_apply] at hmod
    exact hab hmod.symm
  · exact Function.iterate_mod_minimalPeriod_eq.trans hiter

/-- Helper toward Proposition 5.16: the complementary old face arc has
length `period - i`, and both corner darts have that same old period. -/
theorem chord_corner_complement (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a) :
    Function.minimalPeriod B.map.faceSucc a = Function.minimalPeriod B.map.faceSucc b ∧
    Function.minimalPeriod B.map.faceSucc b - i < Function.minimalPeriod B.map.faceSucc a ∧
    (B.map.faceSucc : B.D → B.D)^[Function.minimalPeriod B.map.faceSucc b - i] a = b := by
  have hi0 : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    subst i
    exact hab hwalk.symm
  have hp : Function.minimalPeriod B.map.faceSucc a =
      Function.minimalPeriod B.map.faceSucc b := by
    rw [← hwalk]
    exact Function.minimalPeriod_apply_iterate (B.map.faceSucc.injective.mem_periodicPts b) i
  refine ⟨hp, by omega, ?_⟩
  rw [← hwalk, ← Function.iterate_add_apply, Nat.sub_add_cancel hi.le]
  exact Function.iterate_minimalPeriod

/-- Helper toward Proposition 5.16: the two split faces have the two
complementary old arc lengths, each augmented by its own new dart. -/
theorem chordMap_faceSucc_split_periods (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr true) = i + 1 ∧
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr false) =
      (Function.minimalPeriod B.map.faceSucc b - i) + 1 := by
  obtain ⟨_, hj, hcomp⟩ := B.chord_corner_complement a b hab i hi hwalk
  exact ⟨B.chordMap_faceSucc_minimalPeriod_new a b hab true i hi hwalk,
    B.chordMap_faceSucc_minimalPeriod_new a b hab false _ hj hcomp⟩

/-- Helper toward Proposition 5.16: every iterate in an old orbit avoiding
both selected corners is unchanged, with its dart identity retained. -/
theorem chordMap_faceSucc_iterate_unaffected (a b : B.D) (hab : a ≠ b) (x : B.D)
    (ha : ¬ B.map.faceSucc.SameCycle x a) (hb : ¬ B.map.faceSucc.SameCycle x b)
    (n : ℕ) :
    ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inl x) =
      .inl ((B.map.faceSucc : B.D → B.D)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hcycle : B.map.faceSucc.SameCycle x
        (B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[n] x)) := by
      have h : B.map.faceSucc.SameCycle x ((B.map.faceSucc ^ n) x) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      have h' : B.map.faceSucc.SameCycle x ((B.map.faceSucc : B.D → B.D)^[n] x) := by
        simpa only [Equiv.Perm.coe_pow] using h
      exact h'.apply_right
    rw [B.chordMap_faceSucc_of_next_ne a b hab _
      (fun h => ha (h ▸ hcycle)) (fun h => hb (h ▸ hcycle)),
      Function.iterate_succ_apply']

/-- Helper toward Proposition 5.16: an unaffected old face orbit is
exactly its image under the old-dart inclusion and contains no new dart. -/
theorem chordMap_faceSucc_sameCycle_unaffected_iff (a b : B.D) (hab : a ≠ b) (x : B.D)
    (ha : ¬ B.map.faceSucc.SameCycle x a) (hb : ¬ B.map.faceSucc.SameCycle x b)
    (z : B.D ⊕ Bool) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inl x) z ↔
      ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = .inl y := by
  let g := (B.chordMap a b hab).faceSucc
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    have hiter : (g : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inl x) = z := by
      simpa only [Equiv.Perm.coe_pow] using hn
    rw [B.chordMap_faceSucc_iterate_unaffected a b hab x ha hb n] at hiter
    refine ⟨(B.map.faceSucc : B.D → B.D)^[n] x, ?_, hiter.symm⟩
    have h : B.map.faceSucc.SameCycle x ((B.map.faceSucc ^ n) x) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow] using h
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hiter : (B.map.faceSucc : B.D → B.D)^[n] x = y := by
      simpa only [Equiv.Perm.coe_pow] using hn
    have h : g.SameCycle (.inl x) ((g ^ n) (.inl x)) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    dsimp only [g] at h
    simpa only [Equiv.Perm.coe_pow,
      B.chordMap_faceSucc_iterate_unaffected a b hab x ha hb n, hiter] using h

/-- Helper toward Proposition 5.16: explicit dart descriptions of both
new face orbits, using the two complementary old face walks. -/
theorem chordMap_faceSucc_split_orbits (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a) :
    (∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inr true) z ↔
        z = .inr true ∨ ∃ k < i, z = .inl ((B.map.faceSucc : B.D → B.D)^[k] b)) ∧
    (∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inr false) z ↔
        z = .inr false ∨ ∃ k < Function.minimalPeriod B.map.faceSucc b - i,
          z = .inl ((B.map.faceSucc : B.D → B.D)^[k] a)) := by
  obtain ⟨_, hj, hcomp⟩ := B.chord_corner_complement a b hab i hi hwalk
  exact ⟨B.chordMap_faceSucc_sameCycle_new_iff a b hab true i hi hwalk,
    B.chordMap_faceSucc_sameCycle_new_iff a b hab false _ hj hcomp⟩

/-- Helper toward Proposition 5.16: every dart of the old split face lies
on one of the two new faces; the displayed arcs omit no old dart. -/
theorem chordMap_old_split_face_covered (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a)
    (x : B.D) (hx : B.map.faceSucc.SameCycle b x) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inr true) (.inl x) ∨
    (B.chordMap a b hab).faceSucc.SameCycle (.inr false) (.inl x) := by
  obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
  have hiter : (B.map.faceSucc : B.D → B.D)^[n] b = x := by
    simpa only [Equiv.Perm.coe_pow] using hn
  let r := n % Function.minimalPeriod B.map.faceSucc b
  have hr : r < Function.minimalPeriod B.map.faceSucc b := Nat.mod_lt _ (by omega)
  have hrx : (B.map.faceSucc : B.D → B.D)^[r] b = x :=
    Function.iterate_mod_minimalPeriod_eq.trans hiter
  obtain ⟨htrue, hfalse⟩ := B.chordMap_faceSucc_split_orbits a b hab i hi hwalk
  by_cases hri : r < i
  · exact Or.inl ((htrue _).mpr (Or.inr ⟨r, hri, congrArg Sum.inl hrx.symm⟩))
  · right
    apply (hfalse _).mpr
    right
    refine ⟨r - i, by omega, ?_⟩
    have hsum : r - i + i = r := by omega
    have hcomp : (B.map.faceSucc : B.D → B.D)^[r - i] a = x := by
      rw [← hwalk, ← Function.iterate_add_apply, hsum]
      exact hrx
    exact congrArg Sum.inl hcomp.symm

/-- Helper toward Proposition 5.16: every augmented dart belongs to one
of the two new orbits or is an old dart outside the split old face. -/
theorem chordMap_face_orbits_exhaustive (a b : B.D) (hab : a ≠ b) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] b = a) (z : B.D ⊕ Bool) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inr true) z ∨
    (B.chordMap a b hab).faceSucc.SameCycle (.inr false) z ∨
    ∃ x : B.D, ¬ B.map.faceSucc.SameCycle b x ∧ z = .inl x := by
  cases z with
  | inl x =>
    by_cases hx : B.map.faceSucc.SameCycle b x
    · rcases B.chordMap_old_split_face_covered a b hab i hi hwalk x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
  | inr t =>
    cases t
    · exact Or.inr (Or.inl Equiv.Perm.SameCycle.rfl)
    · exact Or.inl Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16: the initial vertex at time zero of
either new face walk is the corresponding chord endpoint. -/
theorem chordMap_face_vertices_zero {V : Type*} (vert : B.D → V)
    (a b : B.D) (hab : a ≠ b) (t : Bool) :
    B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[0] (.inr t)) =
      vert (cond t a b) := by
  cases t <;> rfl

/-- Helper toward Proposition 5.16: after its initial endpoint, the initial
vertices along either new orbit are precisely those along its old sub-walk. -/
theorem chordMap_face_vertices_succ {V : Type*} (vert : B.D → V)
    (a b : B.D) (hab : a ≠ b) (t : Bool) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b)
    (k : ℕ) (hk : k < i) :
    B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[k + 1]
        (.inr t)) = vert ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) := by
  rw [B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk k hk]
  rfl

/-- Helper toward Proposition 5.16: the initial-vertex set of either new
face is exactly its old sub-walk's initial vertices and one chord endpoint. -/
theorem chordMap_face_vertices_image {V : Type*} (vert : B.D → V)
    (a b : B.D) (hab : a ≠ b) (t : Bool) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b) :
    B.chordVert vert a b '' {z | (B.chordMap a b hab).faceSucc.SameCycle (.inr t) z} =
      {vert (cond t a b)} ∪
        {v | ∃ k < i, v = vert ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a))} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases (B.chordMap_faceSucc_sameCycle_new_iff a b hab t i hi hwalk z).mp hz with
      hz | ⟨k, hk, hz⟩
    · subst z
      left
      cases t <;> rfl
    · subst z
      exact Or.inr ⟨k, hk, rfl⟩
  · rintro (hv | ⟨k, hk, hv⟩)
    · refine ⟨.inr t, Equiv.Perm.SameCycle.rfl, ?_⟩
      have hzero : B.chordVert vert a b (.inr t) = vert (cond t a b) := by
        cases t <;> rfl
      exact hzero.trans (show v = vert (cond t a b) from hv).symm
    · refine ⟨.inl ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)), ?_, hv.symm⟩
      exact (B.chordMap_faceSucc_sameCycle_new_iff a b hab t i hi hwalk _).mpr
        (Or.inr ⟨k, hk, rfl⟩)

/-- Helper toward Proposition 5.16: all old orbits other than the selected
common face persist exactly under the old-dart inclusion. -/
theorem chordMap_faceSucc_sameCycle_of_not_split (a b : B.D) (hab : a ≠ b)
    (hface : B.map.faceSucc.SameCycle b a) (x : B.D)
    (hx : ¬ B.map.faceSucc.SameCycle b x) (z : B.D ⊕ Bool) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inl x) z ↔
      ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = .inl y := by
  exact B.chordMap_faceSucc_sameCycle_unaffected_iff a b hab x
    (fun h => hx (hface.trans h.symm)) (fun h => hx h.symm) z

/-- Helper toward Proposition 5.16: the explicit formula for an arbitrary
iterate of either new dart repeats its finite sub-walk periodically. -/
theorem chordMap_faceSucc_iterate_new_mod (a b : B.D) (hab : a ≠ b) (t : Bool)
    (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b)
    (n : ℕ) :
    ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inr t) =
      if n % (i + 1) = 0 then .inr t else
        .inl ((B.map.faceSucc : B.D → B.D)^[n % (i + 1) - 1] (cond t b a)) := by
  have hret : Function.IsPeriodicPt (B.chordMap a b hab).faceSucc (i + 1) (.inr t) :=
    B.chordMap_faceSucc_return_new a b hab t i hi hwalk
  rw [← hret.iterate_mod_apply n]
  have hr : n % (i + 1) < i + 1 := Nat.mod_lt _ (by omega)
  by_cases hz : n % (i + 1) = 0
  · simp only [hz, ↓reduceIte, Function.iterate_zero_apply]
  · simp only [hz, ↓reduceIte]
    have heq : n % (i + 1) = (n % (i + 1) - 1) + 1 := by omega
    conv_lhs => rw [heq]
    exact B.chordMap_faceSucc_iterate_new a b hab t i hi hwalk _ (by omega)

/-- Helper toward Proposition 5.16: distinct initial vertices on either
new orbit amount exactly to distinct initial vertices on its old sub-walk
and exclusion of the additional endpoint from that sub-walk. -/
theorem chordMap_face_vertices_injOn_iff {V : Type*} (vert : B.D → V)
    (a b : B.D) (hab : a ≠ b) (t : Bool) (i : ℕ)
    (hi : i < Function.minimalPeriod B.map.faceSucc (cond t b a))
    (hwalk : (B.map.faceSucc : B.D → B.D)^[i] (cond t b a) = cond t a b) :
    Set.InjOn (fun n : ℕ => B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inr t)))
      (Set.Iio (i + 1)) ↔
    Set.InjOn (fun k : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)))
      (Set.Iio i) ∧
      ∀ k < i, vert ((B.map.faceSucc : B.D → B.D)^[k] (cond t b a)) ≠
        vert (cond t a b) := by
  simp only [Set.InjOn, Set.mem_Iio]
  constructor
  · intro hinj
    constructor
    · intro k hk l hl heq
      have h := hinj (by omega : k + 1 < i + 1)
        (by omega : l + 1 < i + 1)
        (by simpa only [B.chordMap_face_vertices_succ vert a b hab t i hi hwalk k hk,
          B.chordMap_face_vertices_succ vert a b hab t i hi hwalk l hl] using heq)
      omega
    · intro k hk heq
      have h := hinj (by omega : k + 1 < i + 1)
        (by omega : 0 < i + 1)
        (by simpa only [B.chordMap_face_vertices_succ vert a b hab t i hi hwalk k hk,
          B.chordMap_face_vertices_zero vert a b hab t] using heq)
      omega
  · rintro ⟨hinj, havoid⟩ n hn m hm heq
    cases n with
    | zero =>
      cases m with
      | zero => rfl
      | succ m =>
        have hm' : m < i := by omega
        rw [B.chordMap_face_vertices_zero vert a b hab t,
          B.chordMap_face_vertices_succ vert a b hab t i hi hwalk m hm'] at heq
        exact (havoid m hm' heq.symm).elim
    | succ n =>
      have hn' : n < i := by omega
      cases m with
      | zero =>
        rw [B.chordMap_face_vertices_succ vert a b hab t i hi hwalk n hn',
          B.chordMap_face_vertices_zero vert a b hab t] at heq
        exact (havoid n hn' heq).elim
      | succ m =>
        have hm' : m < i := by omega
        rw [B.chordMap_face_vertices_succ vert a b hab t i hi hwalk n hn',
          B.chordMap_face_vertices_succ vert a b hab t i hi hwalk m hm'] at heq
        exact congrArg Nat.succ (hinj hn' hm' heq)

end D39FiniteBall
end DirectedDistances.PlanarMap
