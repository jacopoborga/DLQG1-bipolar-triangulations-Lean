/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLStarFace

/-! # Existential stages of face star subdivision

Helpers toward Proposition 5.16. The witnesses of the iteration live inside a
proposition, so its induction does not recurse on dependent map carriers. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace D39FiniteBall

variable {V : Type*}

/-- Helper toward Proposition 5.16: the precise geometric and orbit invariant
of a partial star with `n` cut-off triangles. The residual walk retains dart
identities even when original boundary vertices repeat. -/
structure StarStageInvariant (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (k n : ℕ) (C : D39FiniteBall) (v : C.D → Option V)
    (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
    (r : C.D) (t : ℕ → C.D) : Prop where
  /-- Helper toward Proposition 5.16: every augmented vertex is incident. -/
  surjective : Function.Surjective v
  /-- Helper toward Proposition 5.16: one pendant and `n` chords add two darts each. -/
  card : Fintype.card C.D = Fintype.card B.D + 2 * (n + 1)
  /-- Helper toward Proposition 5.16: the ordered root dart persists. -/
  root : C.rootDart = ι B.rootDart
  /-- Helper toward Proposition 5.16: original edge reversals persist. -/
  edgeInv : ∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)
  /-- Helper toward Proposition 5.16: original initial vertices persist. -/
  vertex : ∀ x, v (ι x) = some (vert x)
  /-- Helper toward Proposition 5.16: missing-edge tags persist. -/
  missing : ∀ x, C.missing (ι x) ↔ B.missing x
  /-- Helper toward Proposition 5.16: tail tags persist. -/
  tail : ∀ x, C.tail (ι x) ↔ B.tail x
  /-- Helper toward Proposition 5.16: every new edge is an unmarked centre spoke. -/
  new_darts : ∀ z, z ∉ Set.range ι →
    ¬ C.missing z ∧ ¬ C.tail z ∧ (v z = none ∨ v (C.map.edgeInv z) = none)
  /-- Helper toward Proposition 5.16: old vertex positions persist in the first drawing. -/
  pos : ∀ x, Q.pos (some x) = P.pos x
  /-- Helper toward Proposition 5.16: old vertex positions persist in the second drawing. -/
  pos' : ∀ x, Q'.pos (some x) = P'.pos x
  /-- Helper toward Proposition 5.16: old polylines persist in the first drawing. -/
  arc : ∀ x, Q.arc (ι x) = P.arc x
  /-- Helper toward Proposition 5.16: old polylines persist in the second drawing. -/
  arc' : ∀ x, Q'.arc (ι x) = P'.arc x
  /-- Helper toward Proposition 5.16: each chord reduces the residual period by one. -/
  period : Function.minimalPeriod C.map.faceSucc r = k - n + 2
  /-- Helper toward Proposition 5.16: the residual representative starts at the new centre. -/
  centre : v r = none
  /-- Helper toward Proposition 5.16: the residual walk lists the unprocessed original corners. -/
  walk : ∀ j < k - n,
    (C.map.faceSucc : C.D → C.D)^[j + 1] r =
      ι ((B.map.faceSucc : B.D → B.D)^[n + j] d)
  /-- Helper toward Proposition 5.16: the final spoke returns to the first boundary vertex. -/
  last_vertex : v ((C.map.faceSucc : C.D → C.D)^[k - n + 1] r) = some (vert d)
  /-- Helper toward Proposition 5.16: every completed orbit is triangular. -/
  triangle_period : ∀ i < n, Function.minimalPeriod C.map.faceSucc (t i) = 3
  /-- Helper toward Proposition 5.16: the completed triangles have distinct initial vertices. -/
  triangle_inj : ∀ i < n, Set.InjOn
    (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] (t i))) (Set.Iio 3)
  /-- Helper toward Proposition 5.16: each triangle retains its two specified boundary corners. -/
  triangle_vertices : ∀ i < n,
    v (t i) = some (vert ((B.map.faceSucc : B.D → B.D)^[i + 1] d)) ∧
    v (C.map.faceSucc (t i)) = none ∧
    v ((C.map.faceSucc : C.D → C.D)^[2] (t i)) =
      some (vert ((B.map.faceSucc : B.D → B.D)^[i] d))
  /-- Helper toward Proposition 5.16: different completed triangles are different face orbits. -/
  triangle_distinct : ∀ i < n, ∀ j < n,
    C.map.faceSucc.SameCycle (t i) (t j) ↔ i = j
  /-- Helper toward Proposition 5.16: completed triangles are outside the residual orbit. -/
  triangle_residual : ∀ i < n, ¬ C.map.faceSucc.SameCycle r (t i)
  /-- Helper toward Proposition 5.16: all other original orbits are exact inclusion images. -/
  unaffected : ∀ x, ¬ B.map.faceSucc.SameCycle d x → ∀ z,
    C.map.faceSucc.SameCycle (ι x) z ↔
      ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y
  /-- Helper toward Proposition 5.16: completed, residual and unaffected orbits exhaust the map. -/
  exhaustive : ∀ z,
    (∃ i < n, C.map.faceSucc.SameCycle (t i) z) ∨
    C.map.faceSucc.SameCycle r z ∨
    ∃ x, ¬ B.map.faceSucc.SameCycle d x ∧ z = ι x

/-- Helper toward Proposition 5.16: existence of a partial star, with every
map, inclusion, drawing and orbit representative quantified inside `Prop`. -/
@[expose] def StarStage (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (k n : ℕ) : Prop :=
  ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
    (r : C.D) (t : ℕ → C.D),
    StarStageInvariant B vert P P' d k n C v ι Q Q' r t

/-- Helper toward Proposition 5.16: an old face dart lies on the pendant
residual orbit exactly when it lay on the attachment orbit. -/
theorem star_pendant_sameCycle_inl (B : D39FiniteBall) (a x : B.D) :
    (B.pendantMap a).faceSucc.SameCycle (.inr false) (.inl x) ↔
      B.map.faceSucc.SameCycle a x := by
  constructor
  · intro hx
    by_contra h
    have ho := (B.star_pendant_orbit_unaffected a x h).1 (.inr false)
    obtain ⟨y, _, hy⟩ := ho.mp hx.symm
    cases hy
  · intro hx
    obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
    have hn' : (B.map.faceSucc : B.D → B.D)^[n] a = x := by
      simpa only [Equiv.Perm.coe_pow] using hn
    have hp : 0 < Function.minimalPeriod B.map.faceSucc a :=
      Function.minimalPeriod_pos_of_mem_periodicPts
        (B.map.faceSucc.injective.mem_periodicPts a)
    have hm : n % Function.minimalPeriod B.map.faceSucc a <
        Function.minimalPeriod B.map.faceSucc a := Nat.mod_lt _ hp
    have hw := B.star_pendant_faceSucc_iterate a _ hm
    rw [Function.iterate_mod_minimalPeriod_eq, hn'] at hw
    have h : (B.pendantMap a).faceSucc.SameCycle (.inr false)
        (((B.pendantMap a).faceSucc ^
          (n % Function.minimalPeriod B.map.faceSucc a + 1)) (.inr false)) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow, hw] using h

/-- Helper toward Proposition 5.16: the pendant initializes the existential
star invariant without any simple-boundary assumption. -/
theorem starStage_zero (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D) (k : ℕ)
    (hperiod : Function.minimalPeriod B.map.faceSucc d = k) :
    B.StarStage vert P P' d k 0 := by
  classical
  obtain ⟨c, hc, hF⟩ := (B.plDartFace vert P hvert d).property
  obtain ⟨c', hc', hF'⟩ := (B.plDartFace vert P' hvert d).property
  have hcF : c ∈ (B.plDartFace vert P hvert d).val := by
    rw [hF]
    exact mem_connectedComponentIn hc
  have hcF' : c' ∈ (B.plDartFace vert P' hvert d).val := by
    rw [hF']
    exact mem_connectedComponentIn hc'
  obtain ⟨Q, Q', hpos, hpos', _, _, harc, harc'⟩ :=
    B.exists_star_pendant_drawings vert P P' hvert d c c' hcF hcF'
  let C := B.insertPendant d
  have hp : Function.minimalPeriod C.map.faceSucc (.inr false) = k + 2 := by
    exact (B.star_pendant_face_period d).trans (congrArg (· + 2) hperiod)
  have hlast : (C.map.faceSucc : C.D → C.D)^[k + 1] (.inr false) = .inr true := by
    apply C.map.faceSucc.injective
    change (B.pendantMap d).faceSucc
      (((B.pendantMap d).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[k + 1] (.inr false)) =
      .inr false
    rw [← Function.iterate_succ_apply' (f := ((B.pendantMap d).faceSucc :
      (B.D ⊕ Bool) → (B.D ⊕ Bool)))]
    change ((B.pendantMap d).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[k + 2]
      (.inr false) = .inr false
    rw [← hp]
    exact Function.iterate_minimalPeriod
  refine ⟨C, B.pendantVert vert d, ⟨Sum.inl, Sum.inl_injective⟩,
    Q, Q', .inr false, fun _ => .inr false, ?_⟩
  refine {
    surjective := B.pendantVert_surjective vert d hvert
    card := ?_
    root := rfl
    edgeInv := fun _ => rfl
    vertex := fun _ => rfl
    missing := fun _ => Iff.rfl
    tail := fun _ => Iff.rfl
    new_darts := ?_
    pos := hpos
    pos' := hpos'
    arc := harc
    arc' := harc'
    period := by simpa only [Nat.sub_zero] using hp
    centre := rfl
    walk := ?_
    last_vertex := ?_
    triangle_period := by intro i hi; omega
    triangle_inj := by intro i hi; omega
    triangle_vertices := by intro i hi; omega
    triangle_distinct := by intro i hi; omega
    triangle_residual := by intro i hi; omega
    unaffected := ?_
    exhaustive := ?_ }
  · change Fintype.card (B.D ⊕ Bool) = _
    simp only [Fintype.card_sum, Fintype.card_bool, Nat.zero_add, Nat.mul_one]
  · rintro (x | b) hz
    · exact (hz ⟨x, rfl⟩).elim
    · refine ⟨fun h => h, fun h => h, ?_⟩
      cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro j hj
    simp only [Nat.zero_add]
    change ((B.pendantMap d).faceSucc : (B.D ⊕ Bool) → (B.D ⊕ Bool))^[j + 1]
      (.inr false) = .inl ((B.map.faceSucc : B.D → B.D)^[j] d)
    exact B.star_pendant_faceSucc_iterate d j (by omega)
  · change B.pendantVert vert d
      ((C.map.faceSucc : C.D → C.D)^[k + 1] (.inr false)) = some (vert d)
    rw [hlast]
    rfl
  · intro x hx z
    exact (B.star_pendant_orbit_unaffected d x hx).1 z
  · rintro (x | b)
    · by_cases hx : B.map.faceSucc.SameCycle d x
      · exact Or.inr (Or.inl ((B.star_pendant_sameCycle_inl d x).mpr hx))
      · exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
    · right; left
      cases b
      · exact Equiv.Perm.SameCycle.rfl
      · have h : C.map.faceSucc.SameCycle (.inr true) (C.map.faceSucc (.inr true)) :=
          Equiv.Perm.SameCycle.rfl.apply_right
        exact h.symm

/-- Helper toward Proposition 5.16: an unaffected original orbit cannot
contain the new centre of a partial star. -/
theorem StarStageInvariant.not_residual_old
    {B : D39FiniteBall} {vert : B.D → V}
    {P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert}
    {d : B.D} {k n : ℕ} {C : D39FiniteBall} {v : C.D → Option V}
    {ι : B.D ↪ C.D} {Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v}
    {r : C.D} {t : ℕ → C.D}
    (h : StarStageInvariant B vert P P' d k n C v ι Q Q' r t)
    (x : B.D) (hx : ¬ B.map.faceSucc.SameCycle d x) :
    ¬ C.map.faceSucc.SameCycle r (ι x) := by
  intro hr
  obtain ⟨y, _, hy⟩ := (h.unaffected x hx r).mp hr.symm
  have hv := congrArg v hy
  rw [h.centre, h.vertex] at hv
  cases hv

/-- Helper toward Proposition 5.16: a chord cuts off the next completed
triangle and advances the existential stage by one. No homeomorphism
extension is assumed or asserted by this drawing-and-orbit induction. -/
theorem starStage_succ (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (k n : ℕ) (hn : n + 1 < k)
    (hs : B.StarStage vert P P' d k n) :
    B.StarStage vert P P' d k (n + 1) := by
  classical
  obtain ⟨C, v, ι, Q, Q', r, t, h⟩ := hs
  let a := (C.map.faceSucc : C.D → C.D)^[2] r
  have ha : a = ι ((B.map.faceSucc : B.D → B.D)^[n + 1] d) := h.walk 1 (by omega)
  have hva : v a = some (vert ((B.map.faceSucc : B.D → B.D)^[n + 1] d)) := by
    rw [ha, h.vertex]
  have hvab : v a ≠ v r := by rw [hva, h.centre]; exact fun he => by cases he
  let hab := C.chord_corners_ne v a r hvab
  have hi : 2 < Function.minimalPeriod C.map.faceSucc r := by rw [h.period]; omega
  have hw : (C.map.faceSucc : C.D → C.D)^[2] r = a := rfl
  have hc : v (C.map.faceSucc r) ≠ v a :=
    C.star_vert_ne_faceSucc v Q (C.map.faceSucc r)
  have hface : C.map.faceSucc.SameCycle r a := by
    have he : C.map.faceSucc.SameCycle r ((C.map.faceSucc ^ 2) r) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    exact he
  obtain ⟨R, R', hpos, hpos', harc, harc', htp, htinj, hto, hrp, huo⟩ :=
    C.exists_star_chord_step v Q Q' h.surjective a r hvab hi hw hc
  dsimp only [insertChord] at R R' htp htinj hto hrp huo
  change Function.minimalPeriod (C.chordMap a r hab).faceSucc (.inr true) = 3 at htp
  change Set.InjOn (fun j : ℕ => C.chordVert v a r
    (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j]
      (.inr true))) (Set.Iio 3) at htinj
  change Function.minimalPeriod (C.chordMap a r hab).faceSucc (.inr false) =
    Function.minimalPeriod C.map.faceSucc r - 1 at hrp
  change ∀ x : C.D, ¬ C.map.faceSucc.SameCycle r x → ∀ z : C.D ⊕ Bool,
    (C.chordMap a r hab).faceSucc.SameCycle (.inl x) z ↔
      ∃ y, C.map.faceSucc.SameCycle x y ∧ z = .inl y at huo
  obtain ⟨_, hsep, hro, _, hex⟩ := C.star_chord_orbit_invariant a r hab hi hw
  obtain ⟨hpa, hj, hcomp⟩ := C.chord_corner_complement a r hab 2 hi hw
  have hpersist (i : ℕ) (hi : i < n) :=
    C.star_chord_preserves_unaffected v a r hab hface (t i) (h.triangle_residual i hi)
  have hold (x : C.D) (hx : ¬ C.map.faceSucc.SameCycle r x) (y : C.D) :
      (C.chordMap a r hab).faceSucc.SameCycle (.inl x) (.inl y) ↔
        C.map.faceSucc.SameCycle x y := by
    rw [huo x hx]
    constructor
    · rintro ⟨z, hz, he⟩
      cases Sum.inl.inj he
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hnone (x : C.D) (hx : ¬ C.map.faceSucc.SameCycle r x) (b : Bool) :
      ¬ (C.chordMap a r hab).faceSucc.SameCycle (.inl x) (.inr b) := by
    intro he
    obtain ⟨y, _, hy⟩ := (huo x hx (.inr b)).mp he
    cases hy
  have hnewwalk (j : ℕ) (hj' : j < k - n) :
      ((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j + 1]
        (.inr false) = .inl ((C.map.faceSucc : C.D → C.D)^[j + 2] r) := by
    have he := C.chordMap_faceSucc_iterate_new a r hab false
      (Function.minimalPeriod C.map.faceSucc r - 2) hj hcomp j (by rw [h.period]; omega)
    change ((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j + 1]
      (.inr false) = Sum.inl ((C.map.faceSucc : C.D → C.D)^[j] a) at he
    rw [he]
    dsimp only [a]
    rw [← Function.iterate_add_apply]
  let A := C.insertChord a r hab
  let w := C.chordVert v a r
  let κ : B.D ↪ (C.D ⊕ Bool) := ⟨fun x => .inl (ι x), Sum.inl_injective.comp ι.injective⟩
  let s : ℕ → (C.D ⊕ Bool) := fun i => if i < n then .inl (t i) else .inr true
  refine ⟨A, w, κ, R, R', .inr false, s, ?_⟩
  refine {
    surjective := ?_
    card := ?_
    root := ?_
    edgeInv := ?_
    vertex := ?_
    missing := ?_
    tail := ?_
    new_darts := ?_
    pos := fun x => (hpos _).trans (h.pos x)
    pos' := fun x => (hpos' _).trans (h.pos' x)
    arc := fun x => (harc _).trans (h.arc x)
    arc' := fun x => (harc' _).trans (h.arc' x)
    period := ?_
    centre := h.centre
    walk := ?_
    last_vertex := ?_
    triangle_period := ?_
    triangle_inj := ?_
    triangle_vertices := ?_
    triangle_distinct := ?_
    triangle_residual := ?_
    unaffected := ?_
    exhaustive := ?_ }
  · intro x
    obtain ⟨y, hy⟩ := h.surjective x
    exact ⟨.inl y, hy⟩
  · change Fintype.card (C.D ⊕ Bool) = _
    rw [Fintype.card_sum, Fintype.card_bool, h.card]
    omega
  · exact congrArg Sum.inl h.root
  · intro x
    exact congrArg Sum.inl (h.edgeInv x)
  · exact h.vertex
  · exact h.missing
  · exact h.tail
  · rintro (x | b) hz
    · have hx : x ∉ Set.range ι := by
        rintro ⟨y, rfl⟩
        exact hz ⟨y, rfl⟩
      exact h.new_darts x hx
    · refine ⟨fun h => h, fun h => h, ?_⟩
      cases b
      · exact Or.inl h.centre
      · exact Or.inr h.centre
  · change Function.minimalPeriod (C.chordMap a r hab).faceSucc (.inr false) = _
    rw [hrp, h.period]
    omega
  · intro j hj'
    change ((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j + 1]
      (.inr false) = .inl (ι ((B.map.faceSucc : B.D → B.D)^[(n + 1) + j] d))
    rw [hnewwalk j (by omega)]
    have he := h.walk (j + 1) (by omega)
    have he' : n + (j + 1) = (n + 1) + j := by omega
    simpa only [he'] using congrArg Sum.inl he
  · change w (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) →
      (C.D ⊕ Bool))^[k - (n + 1) + 1] (.inr false)) = _
    rw [hnewwalk (k - (n + 1)) (by omega)]
    change v ((C.map.faceSucc : C.D → C.D)^[k - (n + 1) + 2] r) = _
    rw [show k - (n + 1) + 2 = k - n + 1 by omega]
    exact h.last_vertex
  · intro i hi'
    by_cases hi'': i < n
    · change Function.minimalPeriod (C.chordMap a r hab).faceSucc (s i) = 3
      simp only [s, ite_eq_left hi'']
      exact (hpersist i hi'').1.trans (h.triangle_period i hi'')
    · have he : i = n := by omega
      subst i
      change Function.minimalPeriod (C.chordMap a r hab).faceSucc (s n) = 3
      simpa only [s, ite_eq_right (Nat.lt_irrefl n)] using htp
  · intro i hi'
    by_cases hi'' : i < n
    · change Set.InjOn (fun j : ℕ => w
        (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j] (s i))) _
      simp only [s, ite_eq_left hi'']
      exact ((hpersist i hi'').2.2 3).mpr (h.triangle_inj i hi'')
    · have he : i = n := by omega
      subst i
      change Set.InjOn (fun j : ℕ => w
        (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[j] (s n))) _
      simpa only [s, ite_eq_right (Nat.lt_irrefl n)] using htinj
  · intro i hi'
    by_cases hi'' : i < n
    · have hh := h.triangle_vertices i hi''
      have hv := (hpersist i hi'').2.1
      change w (s i) = _ ∧ w ((C.chordMap a r hab).faceSucc (s i)) = _ ∧
        w (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[2] (s i)) = _
      simp only [s, ite_eq_left hi'']
      exact ⟨hh.1, (hv 1).trans hh.2.1, (hv 2).trans hh.2.2⟩
    · have he : i = n := by omega
      subst i
      change w (s n) = _ ∧ w ((C.chordMap a r hab).faceSucc (s n)) = _ ∧
        w (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) → (C.D ⊕ Bool))^[2] (s n)) = _
      simp only [s, ite_eq_right (Nat.lt_irrefl n)]
      refine ⟨hva, h.centre, ?_⟩
      have hv := (C.star_chord_triangle v Q a r hab hi hw (Ne.symm hvab) hc).2.2.2.1
      change w (((C.chordMap a r hab).faceSucc : (C.D ⊕ Bool) →
        (C.D ⊕ Bool))^[2] (.inr true)) = _ at hv
      rw [hv]
      have hw₀ := h.walk 0 (by omega)
      change C.map.faceSucc r = ι ((B.map.faceSucc : B.D → B.D)^[n + 0] d) at hw₀
      rw [hw₀, h.vertex, Nat.add_zero]
  · intro i hi' j hj'
    change (C.chordMap a r hab).faceSucc.SameCycle (s i) (s j) ↔ i = j
    by_cases hi'' : i < n <;> by_cases hj'' : j < n
    · simp only [s, ite_eq_left hi'', ite_eq_left hj'']
      exact (hold _ (h.triangle_residual i hi'') _).trans
        (h.triangle_distinct i hi'' j hj'')
    · have he : j = n := by omega
      subst j
      simp only [s, ite_eq_left hi'', ite_eq_right (Nat.lt_irrefl n)]
      exact iff_of_false (hnone _ (h.triangle_residual i hi'') true) (by omega)
    · have he : i = n := by omega
      subst i
      simp only [s, ite_eq_left hj'', ite_eq_right (Nat.lt_irrefl n)]
      exact iff_of_false (fun hc => hnone _ (h.triangle_residual j hj'') true hc.symm)
        (by omega)
    · have hei : i = n := by omega
      have hej : j = n := by omega
      subst i; subst j
      exact iff_of_true Equiv.Perm.SameCycle.rfl rfl
  · intro i hi'
    change ¬ (C.chordMap a r hab).faceSucc.SameCycle (.inr false) (s i)
    by_cases hi'' : i < n
    · simp only [s, ite_eq_left hi'']
      exact fun hc => hnone _ (h.triangle_residual i hi'') false hc.symm
    · have he : i = n := by omega
      subst i
      simp only [s, ite_eq_right (Nat.lt_irrefl n)]
      exact fun hc => hsep hc.symm
  · intro x hx z
    dsimp only [A, insertChord] at z
    change (C.chordMap a r hab).faceSucc.SameCycle (.inl (ι x)) z ↔
      ∃ y, B.map.faceSucc.SameCycle x y ∧ z = Sum.inl (ι y)
    rw [huo (ι x) (h.not_residual_old x hx)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (h.unaffected x hx y).mp hy
      exact ⟨u, hu, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ι y, (h.unaffected x hx (ι y)).mpr ⟨y, hy, rfl⟩, rfl⟩
  · intro z
    rcases hex z with hz | hz | ⟨x, hx, rfl⟩
    · left
      refine ⟨n, by omega, ?_⟩
      change (C.chordMap a r hab).faceSucc.SameCycle (s n) z
      simpa only [s, ite_eq_right (Nat.lt_irrefl n)] using hz
    · exact Or.inr (Or.inl hz)
    · rcases h.exhaustive x with ⟨i, hi', hz⟩ | hz | ⟨y, hy, rfl⟩
      · left
        refine ⟨i, by omega, ?_⟩
        change (C.chordMap a r hab).faceSucc.SameCycle (s i) (.inl x)
        simp only [s, ite_eq_left hi']
        exact (hold _ (h.triangle_residual i hi') _).mpr hz
      · exact (hx hz).elim
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)

/-- Helper toward Proposition 5.16: induction on a natural number, entirely
inside `Prop`, constructs every nonempty residual stage of the star. -/
theorem starStage_of_lt (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D) (k : ℕ)
    (hperiod : Function.minimalPeriod B.map.faceSucc d = k)
    (n : ℕ) (hn : n < k) : B.StarStage vert P P' d k n := by
  have hall : ∀ m, m < k → B.StarStage vert P P' d k m := by
    intro m
    induction m with
    | zero =>
      intro _
      exact B.starStage_zero vert P P' hvert d k hperiod
    | succ m ih =>
      intro hm
      exact B.starStage_succ vert P P' d k m hm (ih (by omega))
  exact hall n hn

/-- Helper toward Proposition 5.16: on a three-dart orbit, exclusion of the
first and third initial vertices supplements the drawing's no-loop property
to give three distinct initial vertices. -/
theorem star_three_vertices_inj (C : D39FiniteBall) (v : C.D → V)
    (Q : PLDrawing C.D V C.map.edgeInv C.map.rot v) (r : C.D)
    (h02 : v r ≠ v ((C.map.faceSucc : C.D → C.D)^[2] r)) :
    Set.InjOn (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] r)) (Set.Iio 3) := by
  have h01 := C.star_vert_ne_faceSucc v Q r
  have h12 := C.star_vert_ne_faceSucc v Q (C.map.faceSucc r)
  intro i hi j hj he
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [Set.mem_Iio] at hi; omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Set.mem_Iio] at hj; omega
  rcases hi' with rfl | rfl | rfl
  · rcases hj' with rfl | rfl | rfl
    · rfl
    · exact (h01 he).elim
    · exact (h02 he).elim
  · rcases hj' with rfl | rfl | rfl
    · exact (h01 he.symm).elim
    · rfl
    · exact (h12 he).elim
  · rcases hj' with rfl | rfl | rfl
    · exact (h02 he.symm).elim
    · exact (h12 he.symm).elim
    · rfl

/-- Helper toward Proposition 5.16: a face of period three has exactly
its first three iterates, with no simplicity assumption on their vertices. -/
theorem star_period_three_orbit (C : D39FiniteBall) (r z : C.D)
    (hp : Function.minimalPeriod C.map.faceSucc r = 3) :
    C.map.faceSucc.SameCycle r z ↔
      z = r ∨ z = C.map.faceSucc r ∨
        z = (C.map.faceSucc : C.D → C.D)^[2] r := by
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    have hn' : (C.map.faceSucc : C.D → C.D)^[n] r = z := by
      simpa only [Equiv.Perm.coe_pow] using hn
    have he := Function.iterate_mod_minimalPeriod_eq
      (f := (C.map.faceSucc : C.D → C.D)) (x := r) (n := n)
    rw [hp, hn'] at he
    have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · left; simpa only [hm, Function.iterate_zero_apply] using he.symm
    · right; left; simpa only [hm, Function.iterate_one] using he.symm
    · right; right; simpa only [hm] using he.symm
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · have h : C.map.faceSucc.SameCycle r ((C.map.faceSucc ^ 2) r) :=
        Equiv.Perm.SameCycle.rfl.pow_right
      exact h

/-- Helper toward Proposition 5.16: the vertex image of a triangular
orbit is precisely its three initial vertices. -/
theorem star_period_three_vertex_image (C : D39FiniteBall) (v : C.D → V)
    (r : C.D) (hp : Function.minimalPeriod C.map.faceSucc r = 3) :
    v '' {z | C.map.faceSucc.SameCycle r z} =
      {v r, v (C.map.faceSucc r), v ((C.map.faceSucc : C.D → C.D)^[2] r)} := by
  have ho : {z | C.map.faceSucc.SameCycle r z} =
      {r, C.map.faceSucc r, (C.map.faceSucc : C.D → C.D)^[2] r} := by
    ext z
    exact C.star_period_three_orbit r z hp
  rw [ho, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- Helper toward Proposition 5.16: the terminal residual stage is itself
a triangle, whose two old vertices close the original boundary walk. -/
theorem StarStageInvariant.terminal_triangle
    {B : D39FiniteBall} {vert : B.D → V}
    {P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert}
    {d : B.D} {k : ℕ} {C : D39FiniteBall} {v : C.D → Option V}
    {ι : B.D ↪ C.D} {Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v}
    {r : C.D} {t : ℕ → C.D}
    (h : StarStageInvariant B vert P P' d k (k - 1) C v ι Q Q' r t)
    (hk : 1 ≤ k) :
    Function.minimalPeriod C.map.faceSucc r = 3 ∧
    Set.InjOn (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] r)) (Set.Iio 3) ∧
    v '' {z | C.map.faceSucc.SameCycle r z} =
      {none, some (vert ((B.map.faceSucc : B.D → B.D)^[k - 1] d)), some (vert d)} := by
  have hp : Function.minimalPeriod C.map.faceSucc r = 3 := by
    rw [h.period]
    omega
  have hv₂ : v ((C.map.faceSucc : C.D → C.D)^[2] r) = some (vert d) := by
    have hh := h.last_vertex
    rwa [show k - (k - 1) + 1 = 2 by omega] at hh
  have hv₁ : v (C.map.faceSucc r) =
      some (vert ((B.map.faceSucc : B.D → B.D)^[k - 1] d)) := by
    have hh := h.walk 0 (by omega)
    change C.map.faceSucc r = ι ((B.map.faceSucc : B.D → B.D)^[(k - 1) + 0] d) at hh
    rw [hh, h.vertex, Nat.add_zero]
  refine ⟨hp, C.star_three_vertices_inj v Q r ?_, ?_⟩
  · rw [h.centre, hv₂]
    exact fun he => by cases he
  · rw [C.star_period_three_vertex_image v r hp, h.centre, hv₁, hv₂]

/-- Helper toward Proposition 5.16: a nonempty residual stage is connected
whenever the original map is connected. Angular successor order identifies
all darts at a geometric vertex, and the centre has a residual spoke. -/
theorem StarStageInvariant.connected
    {B : D39FiniteBall} {vert : B.D → V}
    {P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert}
    {d : B.D} {k n : ℕ} {C : D39FiniteBall} {v : C.D → Option V}
    {ι : B.D ↪ C.D} {Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v}
    {r : C.D} {t : ℕ → C.D}
    (h : StarStageInvariant B vert P P' d k n C v ι Q Q' r t)
    (hvert : Function.Surjective vert) (hn : n < k)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun u w => B.map.rot u = w ∨ B.map.edgeInv u = w) x y) :
    ∀ x y : C.D, Relation.EqvGen
      (fun u w => C.map.rot u = w ∨ C.map.edgeInv u = w) x y := by
  let R := fun u w : C.D => C.map.rot u = w ∨ C.map.edgeInv u = w
  have hvertex {x y : C.D} (he : v x = v y) : Relation.EqvGen R x y :=
    CombinatorialMap.eqvGen_of_rotation_sameCycle C.map.rot R (fun _ => Or.inl rfl)
      (Q.rot_sameCycle_of_vert_eq x y he)
  have hlift {x y : B.D} (he : Relation.EqvGen
      (fun u w => B.map.rot u = w ∨ B.map.edgeInv u = w) x y) :
      Relation.EqvGen R (ι x) (ι y) := by
    induction he with
    | rel x y he =>
      rcases he with he | he
      · apply hvertex
        rw [h.vertex, h.vertex, ← he, P.vert_rotation]
      · exact Relation.EqvGen.rel _ _ (Or.inr ((h.edgeInv x).trans (congrArg ι he)))
    | refl => exact Relation.EqvGen.refl _
    | symm x y he ih => exact ih.symm _ _
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans _ _ _ ihyz
  have hstep : Relation.EqvGen R r (C.map.faceSucc r) := by
    have he : Relation.EqvGen R r (C.map.edgeInv r) :=
      Relation.EqvGen.rel _ _ (Or.inr rfl)
    have hr : Relation.EqvGen R (C.map.faceSucc r) (C.map.edgeInv r) :=
      Relation.EqvGen.rel _ _ (Or.inl (C.map.rot.apply_symm_apply _))
    exact he.trans _ _ _ (hr.symm _ _)
  have hw := h.walk 0 (by omega)
  change C.map.faceSucc r = ι ((B.map.faceSucc : B.D → B.D)^[n + 0] d) at hw
  have hcentrepath : Relation.EqvGen R r (ι d) := by
    rw [hw] at hstep
    exact hstep.trans _ _ _ (hlift (hconn _ d))
  have hpath (z : C.D) : Relation.EqvGen R z (ι d) := by
    cases hz : v z with
    | none =>
      exact (hvertex (hz.trans h.centre.symm)).trans _ _ _ hcentrepath
    | some x =>
      obtain ⟨y, hy⟩ := hvert x
      have he : v z = v (ι y) := by rw [hz, h.vertex, hy]
      exact (hvertex he).trans _ _ _ (hlift (hconn y d))
  intro x y
  exact (hpath x).trans _ _ _ ((hpath y).symm _ _)

/-- Helper toward Proposition 5.16: the drawing and orbit part of SA1b.
There are exactly `k` distinct triangular orbits, labeled by the original
boundary corners, and every other original face orbit is retained exactly.
This does not assert extension of a prescribed image homeomorphism, which
is an additional clause of the full SA1b target. -/
theorem exists_star_drawings (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun u w => B.map.rot u = w ∨ B.map.edgeInv u = w) x y)
    (d : B.D) (k : ℕ) (hk : 2 ≤ k)
    (hperiod : Function.minimalPeriod B.map.faceSucc d = k) :
    ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
      (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
      (s : Fin k → C.D),
      Function.Surjective v ∧
      (∀ x y : C.D, Relation.EqvGen
        (fun u w => C.map.rot u = w ∨ C.map.edgeInv u = w) x y) ∧
      Fintype.card C.D = Fintype.card B.D + 2 * k ∧
      C.rootDart = ι B.rootDart ∧
      (∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
      (∀ x, v (ι x) = some (vert x)) ∧
      (∀ x, C.missing (ι x) ↔ B.missing x) ∧
      (∀ x, C.tail (ι x) ↔ B.tail x) ∧
      (∀ z, z ∉ Set.range ι →
        ¬ C.missing z ∧ ¬ C.tail z ∧ (v z = none ∨ v (C.map.edgeInv z) = none)) ∧
      (∀ x, Q.pos (some x) = P.pos x) ∧
      (∀ x, Q'.pos (some x) = P'.pos x) ∧
      (∀ x, Q.arc (ι x) = P.arc x) ∧
      (∀ x, Q'.arc (ι x) = P'.arc x) ∧
      P.image ⊆ Q.image ∧ P'.image ⊆ Q'.image ∧
      (∀ i : Fin k, Function.minimalPeriod C.map.faceSucc (s i) = 3) ∧
      (∀ i : Fin k, Set.InjOn
        (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] (s i))) (Set.Iio 3)) ∧
      (∀ i : Fin k, v '' {z | C.map.faceSucc.SameCycle (s i) z} =
        {none, some (vert ((B.map.faceSucc : B.D → B.D)^[i.val] d)),
          some (vert ((B.map.faceSucc : B.D → B.D)^[i.val + 1] d))}) ∧
      (∀ i j : Fin k, C.map.faceSucc.SameCycle (s i) (s j) ↔ i = j) ∧
      (∀ x, ¬ B.map.faceSucc.SameCycle d x → ∀ z,
        C.map.faceSucc.SameCycle (ι x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
      (∀ z, (∃ i : Fin k, C.map.faceSucc.SameCycle (s i) z) ∨
        ∃ x, ¬ B.map.faceSucc.SameCycle d x ∧ z = ι x) := by
  classical
  obtain ⟨C, v, ι, Q, Q', r, t, h⟩ :=
    B.starStage_of_lt vert P P' hvert d k hperiod (k - 1) (by omega)
  obtain ⟨hrp, hri, hrv⟩ := h.terminal_triangle (by omega)
  let s : Fin k → C.D := fun i => if i.val < k - 1 then t i.val else r
  have hret : (B.map.faceSucc : B.D → B.D)^[k] d = d := by
    rw [← hperiod]
    exact Function.iterate_minimalPeriod
  refine ⟨C, v, ι, Q, Q', s, h.surjective, h.connected hvert (by omega) hconn,
    ?_, h.root, h.edgeInv, h.vertex,
    h.missing, h.tail, h.new_darts, h.pos, h.pos', h.arc, h.arc', ?_, ?_,
    ?_, ?_, ?_, ?_, h.unaffected, ?_⟩
  · rw [h.card, show k - 1 + 1 = k by omega]
  · rintro z (⟨x, rfl⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨some x, h.pos x⟩
    · exact Or.inr ⟨ι x, h.arc x ▸ hx⟩
  · rintro z (⟨x, rfl⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨some x, h.pos' x⟩
    · exact Or.inr ⟨ι x, h.arc' x ▸ hx⟩
  · intro i
    dsimp only [s]
    split_ifs with hi
    · exact h.triangle_period i.val hi
    · exact hrp
  · intro i
    dsimp only [s]
    split_ifs with hi
    · exact h.triangle_inj i.val hi
    · exact hri
  · intro i
    dsimp only [s]
    split_ifs with hi
    · obtain ⟨hv₀, hv₁, hv₂⟩ := h.triangle_vertices i.val hi
      rw [C.star_period_three_vertex_image v (t i.val) (h.triangle_period i.val hi),
        hv₀, hv₁, hv₂]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (hz | hz | hz)
        · exact Or.inr (Or.inr hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
      · rintro (hz | hz | hz)
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr hz)
        · exact Or.inl hz
    · have he : i.val = k - 1 := by have := i.isLt; omega
      have he' : i.val + 1 = k := by have := i.isLt; omega
      rw [hrv, he', hret, he]
  · intro i j
    dsimp only [s]
    by_cases hi : i.val < k - 1 <;> by_cases hj : j.val < k - 1
    · simp only [ite_eq_left hi, ite_eq_left hj]
      exact (h.triangle_distinct i.val hi j.val hj).trans Fin.val_inj
    · simp only [ite_eq_left hi, ite_eq_right hj]
      exact iff_of_false (fun hc => h.triangle_residual i.val hi hc.symm)
        (by intro he; subst j; exact hj hi)
    · simp only [ite_eq_right hi, ite_eq_left hj]
      exact iff_of_false (h.triangle_residual j.val hj)
        (by intro he; subst j; exact hi hj)
    · simp only [ite_eq_right hi, ite_eq_right hj]
      have he : i = j := by apply Fin.ext; have := i.isLt; have := j.isLt; omega
      exact iff_of_true Equiv.Perm.SameCycle.rfl he
  · intro z
    rcases h.exhaustive z with ⟨i, hi, hz⟩ | hz | hz
    · left
      refine ⟨⟨i, by omega⟩, ?_⟩
      simpa only [s, ite_eq_left hi] using hz
    · left
      refine ⟨⟨k - 1, by omega⟩, ?_⟩
      simpa only [s, ite_eq_right (Nat.lt_irrefl (k - 1))] using hz
    · exact Or.inr hz

/-! ## Remaining full SA1b target

`exists_star_drawings` proves the connected drawing-and-orbit construction,
including every combinatorial, vertex, arc, cardinality and exhaustion clause
below. It is a strict subtarget, not an equivalent statement of SA1b: it does
not construct `fplus` extending the prescribed `f`. No hypothesis standing in
for that construction has been added.

The remaining statement, with full binders, is:

∀ {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (f : B.PLImageHomeomorph vert P P')
    (d : B.D) (k : ℕ) (hk : 2 ≤ k)
    (hperiod : Function.minimalPeriod B.map.faceSucc d = k),
  ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
    (t : Fin k → C.D)
    (himage : P.image ⊆ Q.image) (himage' : P'.image ⊆ Q'.image)
    (fplus : C.PLImageHomeomorph v Q Q'),
    Function.Surjective v ∧
    (∀ x y : C.D, Relation.EqvGen
      (fun u w => C.map.rot u = w ∨ C.map.edgeInv u = w) x y) ∧
    Fintype.card C.D = Fintype.card B.D + 2 * k ∧
    C.rootDart = ι B.rootDart ∧
    (∀ x : B.D, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
    (∀ x : B.D, v (ι x) = some (vert x)) ∧
    (∀ x : B.D, C.missing (ι x) ↔ B.missing x) ∧
    (∀ x : B.D, C.tail (ι x) ↔ B.tail x) ∧
    (∀ z : C.D, z ∉ Set.range ι →
      ¬ C.missing z ∧ ¬ C.tail z ∧
      (v z = none ∨ v (C.map.edgeInv z) = none)) ∧
    (∀ x : V, Q.pos (some x) = P.pos x) ∧
    (∀ x : V, Q'.pos (some x) = P'.pos x) ∧
    (∀ x : B.D, Q.arc (ι x) = P.arc x) ∧
    (∀ x : B.D, Q'.arc (ι x) = P'.arc x) ∧
    (∀ x : P.image,
      (fplus.toHomeomorph ⟨x.val, himage x.property⟩ : ℂ) =
        (f.toHomeomorph x : ℂ)) ∧
    (∀ i : Fin k, Function.minimalPeriod C.map.faceSucc (t i) = 3) ∧
    (∀ i : Fin k, Set.InjOn
      (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] (t i))) (Set.Iio 3)) ∧
    (∀ i : Fin k,
      v '' {z : C.D | C.map.faceSucc.SameCycle (t i) z} =
        {none, some (vert ((B.map.faceSucc : B.D → B.D)^[i.val] d)),
          some (vert ((B.map.faceSucc : B.D → B.D)^[i.val + 1] d))}) ∧
    (∀ i j : Fin k, C.map.faceSucc.SameCycle (t i) (t j) ↔ i = j) ∧
    (∀ x : B.D, ¬ B.map.faceSucc.SameCycle d x → ∀ z : C.D,
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y : B.D, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
    (∀ z : C.D, (∃ i : Fin k, C.map.faceSucc.SameCycle (t i) z) ∨
      ∃ x : B.D, ¬ B.map.faceSucc.SameCycle d x ∧ z = ι x)

Three approaches were investigated in this file's development:

1. Existential stage induction: implemented here, including the simultaneous
   invariant and terminal residual triangle. The imported drawing steps do
   not supply extensions of a prescribed image homeomorphism. The induction
   therefore proves all the other clauses but cannot add the `fplus` witness.
2. Plane-drawing uniqueness: the inspected declarations in
   `D39PLDrawingUniqueness.lean` require vertex-simple boundaries on every
   augmented orbit for plane extension. Original unaffected orbits may have
   repeated boundary vertices. Its arbitrary image-homeomorphism existence
   result also does not prescribe agreement with the given `f`.
3. Closed-cover gluing: inspected
   `exists_homeomorph_of_finite_closed_covers_of_overlap` and the proved
   `exists_insertChord_union_homeomorph` in
   `D39PLInsertionImageHomeomorph2.lean`. The latter proves gluing on a union
   for one chord, but its full drawing-image restriction target remains a
   comment, and there is no corresponding proved pendant extension in the
   inspected insertion modules. A complete implementation must prove the
   old/new arc and vertex restrictions, construct the pendant extension,
   and carry the prescribed map through the same induction, or glue all
   spokes after the construction. These are proof obligations, not new
   source assumptions or author decisions.

No claim of SA1b or Proposition 5.16 completion is made. -/

end D39FiniteBall
end DirectedDistances.PlanarMap
end
