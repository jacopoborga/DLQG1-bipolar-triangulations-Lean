/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLCornerAccessArc
public import DirectedDistances.PlanarMap.D39PLInsertionFaces
public import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen3
public import DirectedDistances.PlanarMap.D39PLInsertionImageHomeomorph

/-! # One step in a face star subdivision

Helpers toward Proposition 5.16. These statements retain dart identities and
construct the two drawing extensions independently. They do not assert a plane
the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: the open connected set arc theorem
discharges the general premise of the corner access construction. -/
theorem star_simpleArcInOpen : SimpleArcInOpenStatement := by
  intro U hU hconn x y hx hy hxy
  exact exists_simple_polyline_in_open_connected hU hconn hx hy hxy

include P in
/-- Helper toward Proposition 5.16: successive face darts start at the
two endpoints of the intervening edge, even for a repeated boundary walk. -/
theorem star_vert_faceSucc (d : B.D) :
    vert (B.map.faceSucc d) = vert (B.map.edgeInv d) := by
  have h := P.vert_rotation (B.map.faceSucc d)
  change vert (B.map.rot (B.map.rot.symm (B.map.edgeInv d))) =
    vert (B.map.faceSucc d) at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

include P in
/-- Helper toward Proposition 5.16: the boundary vertices on either side
of a single edge are distinct; a face need not have a simple boundary. -/
theorem star_vert_ne_faceSucc (d : B.D) :
    vert d ≠ vert (B.map.faceSucc d) := by
  rw [B.star_vert_faceSucc vert P d]
  exact P.vert_ne_flip d

/-- Helper toward Proposition 5.16: two distinct vertex corners in one
face orbit admit chord extensions of both drawings, with all old positions
and labeled arcs unchanged. No correspondence between the chosen arcs is
required for the construction of these drawing extensions. -/
theorem exists_star_chord_drawings (hvert : Function.Surjective vert)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hface : B.map.faceSucc.SameCycle a b) :
    ∃ (Q : PLDrawing (B.insertChord a b (B.chord_corners_ne vert a b hvab)).D V
        (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.edgeInv
        (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.rot
        (B.chordVert vert a b))
      (Q' : PLDrawing (B.insertChord a b (B.chord_corners_ne vert a b hvab)).D V
        (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.edgeInv
        (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.rot
        (B.chordVert vert a b)),
      (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) := by
  obtain ⟨S, _⟩ := P.exists_D39PLSeparationData hvert
  obtain ⟨S', _⟩ := P'.exists_D39PLSeparationData hvert
  obtain ⟨g, hg, hs, hf, hdis, _, ha, hga, hb, hgb, harg_a, harg_b⟩ :=
    B.exists_chord_arc vert P hvert star_simpleArcInOpen S a b hvab
      (B.plDartFace_eq_of_sameCycle vert P hvert a b hface)
  obtain ⟨g', hg', hs', hf', hdis', _, ha', hga', hb', hgb', harg_a', harg_b'⟩ :=
    B.exists_chord_arc vert P' hvert star_simpleArcInOpen S' a b hvab
      (B.plDartFace_eq_of_sameCycle vert P' hvert a b hface)
  exact ⟨B.insertChordDrawing vert P a b hvab g hg hs hf hdis
      ha hga hb hgb harg_a harg_b,
    B.insertChordDrawing vert P' a b hvab g' hg' hs' hf' hdis'
      ha' hga' hb' hgb' harg_a' harg_b',
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

include P in
/-- Helper toward Proposition 5.16: cutting off a two-edge boundary arc
creates an orbit of period three with the centre and the two consecutive
boundary vertices. The centre exclusions are the star induction invariant;
the boundary vertices are distinct by the drawing's no-loop property. -/
theorem star_chord_triangle (a b : B.D) (hab : a ≠ b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre₀ : vert b ≠ vert a)
    (hcentre₁ : vert (B.map.faceSucc b) ≠ vert a) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr true) = 3 ∧
    B.chordVert vert a b (.inr true) = vert a ∧
    B.chordVert vert a b ((B.chordMap a b hab).faceSucc (.inr true)) = vert b ∧
    B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[2]
        (.inr true)) = vert (B.map.faceSucc b) ∧
    Set.InjOn (fun n : ℕ => B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
        (.inr true))) (Set.Iio 3) := by
  refine ⟨B.chordMap_faceSucc_minimalPeriod_new a b hab true 2 hi hwalk,
    rfl, rfl, ?_, ?_⟩
  · exact B.chordMap_face_vertices_succ vert a b hab true 2 hi hwalk 1 (by omega)
  · apply (B.chordMap_face_vertices_injOn_iff vert a b hab true 2 hi hwalk).mpr
    constructor
    · intro m hm n hn heq
      have hm' : m = 0 ∨ m = 1 := by simp only [Set.mem_Iio] at hm; omega
      have hn' : n = 0 ∨ n = 1 := by simp only [Set.mem_Iio] at hn; omega
      rcases hm' with rfl | rfl
      · rcases hn' with rfl | rfl
        · rfl
        · exact (B.star_vert_ne_faceSucc vert P b heq).elim
      · rcases hn' with rfl | rfl
        · exact (B.star_vert_ne_faceSucc vert P b heq.symm).elim
        · rfl
    · intro n hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · exact hcentre₀
      · exact hcentre₁

/-- Helper toward Proposition 5.16: the triangle cut from a face is
exactly the new positive dart and the two old boundary-walk darts. -/
theorem star_chord_triangle_orbit (a b : B.D) (hab : a ≠ b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a) (z : B.D ⊕ Bool) :
    (B.chordMap a b hab).faceSucc.SameCycle (.inr true) z ↔
      z = .inr true ∨ z = .inl b ∨ z = .inl (B.map.faceSucc b) := by
  rw [B.chordMap_faceSucc_sameCycle_new_iff a b hab true 2 hi hwalk z]
  constructor
  · rintro (hz | ⟨n, hn, hz⟩)
    · exact Or.inl hz
    · have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr hz)
  · rintro (hz | hz | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨0, by omega, hz⟩
    · exact Or.inr ⟨1, by omega, hz⟩

/-- Helper toward Proposition 5.16: the one-step orbit invariant for a
star chord. There is a triangle and one complementary residual orbit;
every other old orbit is its exact inclusion image, and these exhaust all
augmented darts. This statement keeps the full remaining boundary walk. -/
theorem star_chord_orbit_invariant (a b : B.D) (hab : a ≠ b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr false) =
      Function.minimalPeriod B.map.faceSucc b - 1 ∧
    (¬ (B.chordMap a b hab).faceSucc.SameCycle (.inr true) (.inr false)) ∧
    (∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inr false) z ↔
        z = .inr false ∨ ∃ n < Function.minimalPeriod B.map.faceSucc b - 2,
          z = .inl ((B.map.faceSucc : B.D → B.D)^[n] a)) ∧
    (∀ x : B.D, ¬ B.map.faceSucc.SameCycle b x → ∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inl x) z ↔
        ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = .inl y) ∧
    (∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inr true) z ∨
      (B.chordMap a b hab).faceSucc.SameCycle (.inr false) z ∨
      ∃ x : B.D, ¬ B.map.faceSucc.SameCycle b x ∧ z = .inl x) := by
  have hperiod := (B.chordMap_faceSucc_split_periods a b hab 2 hi hwalk).2
  have hface : B.map.faceSucc.SameCycle b a := by
    rw [← hwalk]
    have h : B.map.faceSucc.SameCycle b ((B.map.faceSucc ^ 2) b) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow] using h
  refine ⟨?_, B.chordMap_new_not_sameCycle a b hab 2 hi hwalk,
    (B.chordMap_faceSucc_split_orbits a b hab 2 hi hwalk).2,
    ?_, B.chordMap_face_orbits_exhaustive a b hab 2 hi hwalk⟩
  · omega
  · intro x hx z
    exact B.chordMap_faceSucc_sameCycle_of_not_split a b hab hface x hx z

/-- Helper toward Proposition 5.16: all periods and all initial-vertex
iterates on a previously completed face outside the split orbit persist.
In particular, a previously completed triangle stays a triangle. -/
theorem star_chord_preserves_unaffected (a b : B.D) (hab : a ≠ b)
    (hface : B.map.faceSucc.SameCycle b a) (x : B.D)
    (hx : ¬ B.map.faceSucc.SameCycle b x) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inl x) =
      Function.minimalPeriod B.map.faceSucc x ∧
    (∀ n : ℕ, B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
        (.inl x)) = vert ((B.map.faceSucc : B.D → B.D)^[n] x)) ∧
    (∀ k : ℕ, Set.InjOn (fun n : ℕ => B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
        (.inl x))) (Set.Iio k) ↔
      Set.InjOn (fun n : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[n] x))
        (Set.Iio k)) := by
  have ha : ¬ B.map.faceSucc.SameCycle x a := fun h => hx (hface.trans h.symm)
  have hb : ¬ B.map.faceSucc.SameCycle x b := fun h => hx h.symm
  have hi := B.chordMap_faceSucc_iterate_unaffected a b hab x ha hb
  have hv (n : ℕ) : B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
        (.inl x)) = vert ((B.map.faceSucc : B.D → B.D)^[n] x) := by
    rw [hi n]
    rfl
  refine ⟨?_, hv, ?_⟩
  · apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    change (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
      (.inl x) = .inl x) ↔ (B.map.faceSucc : B.D → B.D)^[n] x = x
    rw [hi n]
    exact Sum.inl.inj_iff
  · intro k
    simp only [Set.InjOn, hv]






theorem exists_star_chord_step (hvert : Function.Surjective vert)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre : vert (B.map.faceSucc b) ≠ vert a) :
    let hab := B.chord_corners_ne vert a b hvab
    let C := B.insertChord a b hab
    ∃ (Q Q' : PLDrawing C.D V C.map.edgeInv C.map.rot (B.chordVert vert a b)),
      (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
      Function.minimalPeriod C.map.faceSucc (.inr true) = 3 ∧
      Set.InjOn (fun n : ℕ => B.chordVert vert a b
        ((C.map.faceSucc : C.D → C.D)^[n] (.inr true))) (Set.Iio 3) ∧
      (∀ z : C.D, C.map.faceSucc.SameCycle (.inr true) z ↔
        z = .inr true ∨ z = .inl b ∨ z = .inl (B.map.faceSucc b)) ∧
      Function.minimalPeriod C.map.faceSucc (.inr false) =
        Function.minimalPeriod B.map.faceSucc b - 1 ∧
      (∀ x : B.D, ¬ B.map.faceSucc.SameCycle b x → ∀ z : C.D,
        C.map.faceSucc.SameCycle (.inl x) z ↔
          ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = .inl y) := by
  dsimp only
  have hab := B.chord_corners_ne vert a b hvab
  have hface : B.map.faceSucc.SameCycle b a := by
    rw [← hwalk]
    have h : B.map.faceSucc.SameCycle b ((B.map.faceSucc ^ 2) b) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow] using h
  obtain ⟨Q, Q', hpos, hpos', harc, harc'⟩ :=
    B.exists_star_chord_drawings vert P P' hvert a b hvab hface.symm
  obtain ⟨htri, _, _, _, hinj⟩ :=
    B.star_chord_triangle vert P a b hab hi hwalk (Ne.symm hvab) hcentre
  obtain ⟨hres, _, _, hunaff, _⟩ := B.star_chord_orbit_invariant a b hab hi hwalk
  exact ⟨Q, Q', hpos, hpos', harc, harc', htri, hinj,
    B.star_chord_triangle_orbit a b hab hi hwalk, hres, hunaff⟩

/-- Helper toward Proposition 5.16: the pendant modifies exactly the
old face step entering its attachment corner. -/
theorem star_pendant_faceSucc_inl (a x : B.D) :
    (B.pendantMap a).faceSucc (.inl x) =
      if B.map.edgeInv x = B.map.rot a then .inr true
      else .inl (B.map.faceSucc x) := rfl

/-- Helper toward Proposition 5.16: the centre dart of the pendant
continues at corner zero of the old boundary walk. -/
theorem star_pendant_faceSucc_false (a : B.D) :
    (B.pendantMap a).faceSucc (.inr false) = .inl a := rfl

/-- Helper toward Proposition 5.16: the pendant's outward dart turns
back at its new centre vertex. -/
theorem star_pendant_faceSucc_true (a : B.D) :
    (B.pendantMap a).faceSucc (.inr true) = .inr false := rfl

/-- Helper toward Proposition 5.16: until the old face closes, the
pendant centre walk traverses the original boundary in its original order. -/
theorem star_pendant_faceSucc_iterate (a : B.D) (n : ℕ)
    (hn : n < Function.minimalPeriod B.map.faceSucc a) :
    ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n + 1]
      (.inr false) = .inl ((B.map.faceSucc : B.D → B.D)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega), B.star_pendant_faceSucc_inl]
    have hnext : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[n] a) ≠ a := by
      intro heq
      have heq' : (B.map.faceSucc : B.D → B.D)^[n + 1] a =
          (B.map.faceSucc : B.D → B.D)^[0] a := by
        simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using heq
      have h := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hn
        (by omega : 0 < Function.minimalPeriod B.map.faceSucc a)).mp heq'
      omega
    have hcut : B.map.edgeInv ((B.map.faceSucc : B.D → B.D)^[n] a) ≠
        B.map.rot a := by
      intro h
      apply hnext
      change B.map.rot.symm (B.map.edgeInv _) = a
      rw [h, Equiv.symm_apply_apply]
    rw [ite_eq_right hcut, Function.iterate_succ_apply']

/-- Helper toward Proposition 5.16: a pendant adds exactly two darts
to its attachment face, including in the presence of repeated vertices. -/
theorem star_pendant_face_period (a : B.D) :
    Function.minimalPeriod (B.pendantMap a).faceSucc (.inr false) =
      Function.minimalPeriod B.map.faceSucc a + 2 := by
  let p := Function.minimalPeriod B.map.faceSucc a
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
    (B.map.faceSucc.injective.mem_periodicPts a)
  have hpred : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[p - 1] a) = a := by
    rw [← Function.iterate_succ_apply' (f := (B.map.faceSucc : B.D → B.D))]
    have h : (p - 1).succ = p := by omega
    rw [h]
    exact Function.iterate_minimalPeriod
  have hcut : B.map.edgeInv ((B.map.faceSucc : B.D → B.D)^[p - 1] a) =
      B.map.rot a := by
    exact (B.map.rot.apply_symm_apply _).symm.trans (congrArg B.map.rot hpred)
  have hlast : ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[p + 1]
      (.inr false) = .inr true := by
    rw [Function.iterate_succ_apply']
    have heq : p = (p - 1) + 1 := by omega
    rw [heq, B.star_pendant_faceSucc_iterate a (p - 1) (by omega)]
    rw [B.star_pendant_faceSucc_inl, ite_eq_left hcut]
  have hret : Function.IsPeriodicPt (B.pendantMap a).faceSucc (p + 2) (.inr false) := by
    change ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[(p + 1) + 1]
      (.inr false) = .inr false
    rw [Function.iterate_succ_apply', hlast, B.star_pendant_faceSucc_true]
  have hpnew := hret.minimalPeriod_pos (by omega : 0 < p + 2)
  apply le_antisymm (hret.minimalPeriod_le (by omega))
  by_contra h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpnew)
  have hnle : n ≤ p := by omega
  have hreturn := Function.iterate_minimalPeriod
    (f := ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool)))
    (x := (.inr false : B.D ⊕ Bool))
  rw [hn] at hreturn
  by_cases hnp : n < p
  · rw [B.star_pendant_faceSucc_iterate a n hnp] at hreturn
    cases hreturn
  · have heq : n = p := by omega
    subst n
    rw [hlast] at hreturn
    cases hreturn

/-- Helper toward Proposition 5.16: the initial pendant can be drawn in
both specified faces, with a genuinely new centre and unchanged old data. -/
theorem exists_star_pendant_drawings (hvert : Function.Surjective vert)
    (a : B.D) (c c' : ℂ)
    (hc : c ∈ (B.plDartFace vert P hvert a).val)
    (hc' : c' ∈ (B.plDartFace vert P' hvert a).val) :
    ∃ (Q Q' : PLDrawing (B.insertPendant a).D (Option V)
        (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot
        (B.pendantVert vert a)),
      (∀ v, Q.pos (some v) = P.pos v) ∧
      (∀ v, Q'.pos (some v) = P'.pos v) ∧
      Q.pos none = c ∧ Q'.pos none = c' ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) := by
  obtain ⟨S, _⟩ := P.exists_D39PLSeparationData hvert
  obtain ⟨S', _⟩ := P'.exists_D39PLSeparationData hvert
  obtain ⟨g, hg, hs, hf, hnot, hdis, _, hslot⟩ :=
    B.exists_pendant_arc vert P hvert star_simpleArcInOpen S a hc
  obtain ⟨g', hg', hs', hf', hnot', hdis', _, hslot'⟩ :=
    B.exists_pendant_arc vert P' hvert star_simpleArcInOpen S' a hc'
  exact ⟨B.insertPendantDrawing vert P a c hnot g hg hs hf hdis hslot,
    B.insertPendantDrawing vert P' a c' hnot' g' hg' hs' hf' hdis' hslot',
    fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- Helper toward Proposition 5.16: after a nonterminal star chord,
the negative new dart is the next centre corner; its next two face steps
visit the current and then the next boundary corners in walk order. -/
theorem star_chord_next_corners (a b : B.D) (hab : a ≠ b)
    (hp : 3 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a) :
    ((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[2]
      (.inr false) = .inl (B.map.faceSucc a) ∧
    B.chordVert vert a b (.inr false) = vert b ∧
    B.chordVert vert a b ((B.chordMap a b hab).faceSucc (.inr false)) = vert a := by
  have hthree : (B.map.faceSucc : B.D → B.D)^[3] b = B.map.faceSucc a := by
    rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply', hwalk]
  have hna : B.map.faceSucc a ≠ a := by
    intro h
    have heq : (B.map.faceSucc : B.D → B.D)^[3] b =
        (B.map.faceSucc : B.D → B.D)^[2] b := hthree.trans (h.trans hwalk.symm)
    have he := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hp
      (by omega : 2 < Function.minimalPeriod B.map.faceSucc b)).mp heq
    omega
  have hnb : B.map.faceSucc a ≠ b := by
    intro h
    have heq : (B.map.faceSucc : B.D → B.D)^[3] b =
        (B.map.faceSucc : B.D → B.D)^[0] b := hthree.trans h
    have he := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hp
      (by omega : 0 < Function.minimalPeriod B.map.faceSucc b)).mp heq
    omega
  refine ⟨?_, rfl, rfl⟩
  change (B.chordMap a b hab).faceSucc
    ((B.chordMap a b hab).faceSucc (.inr false)) = _
  rw [B.chordMap_faceSucc_false, B.chordMap_faceSucc_of_next_ne a b hab a hna hnb]

/-- Helper toward Proposition 5.16: the pendant does not change any
iterate in an old face orbit other than its attachment face. -/
theorem star_pendant_iterate_unaffected (a x : B.D)
    (hx : ¬ B.map.faceSucc.SameCycle a x) (n : ℕ) :
    ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n] (.inl x) =
      .inl ((B.map.faceSucc : B.D → B.D)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, B.star_pendant_faceSucc_inl]
    have hcycle : B.map.faceSucc.SameCycle x
        (B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[n] x)) := by
      have h : B.map.faceSucc.SameCycle x ((B.map.faceSucc ^ n) x) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      have h' : B.map.faceSucc.SameCycle x ((B.map.faceSucc : B.D → B.D)^[n] x) := by
        simpa only [Equiv.Perm.coe_pow] using h
      exact h'.apply_right
    have hcut : B.map.edgeInv ((B.map.faceSucc : B.D → B.D)^[n] x) ≠
        B.map.rot a := by
      intro h
      have hnext : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[n] x) = a := by
        change B.map.rot.symm (B.map.edgeInv _) = a
        rw [h, Equiv.symm_apply_apply]
      rw [hnext] at hcycle
      exact hx hcycle.symm
    rw [ite_eq_right hcut, Function.iterate_succ_apply']

/-- Helper toward Proposition 5.16: every old face other than the
attachment face survives the pendant as exactly its old-dart inclusion
image, with the same period. -/
theorem star_pendant_orbit_unaffected (a x : B.D)
    (hx : ¬ B.map.faceSucc.SameCycle a x) :
    (∀ z : B.D ⊕ Bool,
      (B.pendantMap a).faceSucc.SameCycle (.inl x) z ↔
        ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = .inl y) ∧
    Function.minimalPeriod (B.pendantMap a).faceSucc (.inl x) =
      Function.minimalPeriod B.map.faceSucc x := by
  constructor
  · intro z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
      have hi : ((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
          (.inl x) = z := by
        simpa only [Equiv.Perm.coe_pow] using hn
      rw [B.star_pendant_iterate_unaffected a x hx n] at hi
      refine ⟨(B.map.faceSucc : B.D → B.D)^[n] x, ?_, hi.symm⟩
      have h : B.map.faceSucc.SameCycle x ((B.map.faceSucc ^ n) x) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      simpa only [Equiv.Perm.coe_pow] using h
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
      have hi : (B.map.faceSucc : B.D → B.D)^[n] x = y := by
        simpa only [Equiv.Perm.coe_pow] using hn
      have h : (B.pendantMap a).faceSucc.SameCycle (.inl x)
          (((B.pendantMap a).faceSucc ^ n) (.inl x)) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      simpa only [Equiv.Perm.coe_pow, B.star_pendant_iterate_unaffected a x hx n,
        hi] using h
  · apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    change (((B.pendantMap a).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
      (.inl x) = .inl x) ↔ (B.map.faceSucc : B.D → B.D)^[n] x = x
    rw [B.star_pendant_iterate_unaffected a x hx n]
    exact Sum.inl.inj_iff

include P in
/-- Helper toward Proposition 5.16: the pendant base satisfies the
two-step star invariant at corner one of the original boundary walk. The
centre is new, and the two old boundary vertices differ without requiring
the entire boundary walk to be simple. -/
theorem star_pendant_first_chord_invariant (a : B.D)
    (hk : 2 ≤ Function.minimalPeriod B.map.faceSucc a) :
    let C := B.insertPendant a
    let v := B.pendantVert vert a
    Function.minimalPeriod C.map.faceSucc (.inr false) =
      Function.minimalPeriod B.map.faceSucc a + 2 ∧
    (C.map.faceSucc : C.D → C.D)^[2] (.inr false) = .inl (B.map.faceSucc a) ∧
    v (.inl (B.map.faceSucc a)) ≠ v (.inr false) ∧
    v (C.map.faceSucc (.inr false)) ≠ v (.inl (B.map.faceSucc a)) := by
  dsimp only
  refine ⟨B.star_pendant_face_period a,
    B.star_pendant_faceSucc_iterate a 1 (by omega), ?_, ?_⟩
  · intro h
    cases h
  · change some (vert a) ≠ some (vert (B.map.faceSucc a))
    exact fun h => B.star_vert_ne_faceSucc vert P a (Option.some.inj h)

include P in
/-- Helper toward Proposition 5.16: when a residual star face has four
darts, the final chord leaves a second triangle. Together with the
positive triangle this closes the last chord step. -/
theorem star_chord_terminal_triangle (a b : B.D) (hab : a ≠ b)
    (hp : Function.minimalPeriod B.map.faceSucc b = 4)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre₀ : vert a ≠ vert b)
    (hcentre₁ : vert (B.map.faceSucc a) ≠ vert b) :
    Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inr false) = 3 ∧
    Set.InjOn (fun n : ℕ => B.chordVert vert a b
      (((B.chordMap a b hab).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[n]
        (.inr false))) (Set.Iio 3) ∧
    (∀ z : B.D ⊕ Bool,
      (B.chordMap a b hab).faceSucc.SameCycle (.inr false) z ↔
        z = .inr false ∨ z = .inl a ∨ z = .inl (B.map.faceSucc a)) := by
  have hi : 2 < Function.minimalPeriod B.map.faceSucc b := by omega
  obtain ⟨hpa, hj, hcomp⟩ := B.chord_corner_complement a b hab 2 hi hwalk
  have hcomp' : (B.map.faceSucc : B.D → B.D)^[2] a = b := by
    simpa only [hp, Nat.reduceSub] using hcomp
  have hi' : 2 < Function.minimalPeriod B.map.faceSucc a := by omega
  refine ⟨B.chordMap_faceSucc_minimalPeriod_new a b hab false 2 hi' hcomp', ?_, ?_⟩
  · apply (B.chordMap_face_vertices_injOn_iff vert a b hab false 2 hi' hcomp').mpr
    constructor
    · intro m hm n hn heq
      have hm' : m = 0 ∨ m = 1 := by simp only [Set.mem_Iio] at hm; omega
      have hn' : n = 0 ∨ n = 1 := by simp only [Set.mem_Iio] at hn; omega
      rcases hm' with rfl | rfl
      · rcases hn' with rfl | rfl
        · rfl
        · exact (B.star_vert_ne_faceSucc vert P a heq).elim
      · rcases hn' with rfl | rfl
        · exact (B.star_vert_ne_faceSucc vert P a heq.symm).elim
        · rfl
    · intro n hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · exact hcentre₀
      · exact hcentre₁
  · intro z
    rw [B.chordMap_faceSucc_sameCycle_new_iff a b hab false 2 hi' hcomp' z]
    constructor
    · rintro (hz | ⟨n, hn, hz⟩)
      · exact Or.inl hz
      · have hn' : n = 0 ∨ n = 1 := by omega
        rcases hn' with rfl | rfl
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr hz)
    · rintro (hz | hz | hz)
      · exact Or.inl hz
      · exact Or.inr ⟨0, by omega, hz⟩
      · exact Or.inr ⟨1, by omega, hz⟩















































































end D39FiniteBall
end DirectedDistances.PlanarMap
end
