/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39SourceTopology

import Mathlib.Order.KonigLemma

/-! # Metric separation for Definition 3.8

Helpers toward Definition 3.8 (`def-bs-topology`). -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open scoped ENNReal

/-- Helper toward Definition 3.8. A positive-radius faced-ball isomorphism
restricts to the preceding radius while retaining the ordered mark, plane
rotation, missing tags, orientations, and contained-face data. -/
noncomputable def d39BallIso_restrict_succ (M N : D39RootedMap) {r : ℕ}
    (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M (r + 1) (by omega))
      (d39FacedBall N (r + 1) (by omega))) :
    D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr) :=
  I.restrict M N hr (Nat.le_succ r)

/-- Helper toward Definition 3.8. Between two finite faced balls there are
only finitely many isomorphisms of all retained data. -/
theorem d39BallIso_finite {B C : D39FiniteBall} : Finite (D39BallIso B C) := by
  classical
  let f : D39BallIso B C → (B.D ≃ C.D) := D39BallIso.toEquiv
  have hf : Function.Injective f := by
    intro I J h
    cases I with
    | mk i hi₁ hi₂ hi₃ hi₄ hi₅ hi₆ =>
      cases J with
      | mk j hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ =>
        simp_all [f]
  exact Finite.of_injective f hf

/-- Helper toward Definition 3.8. The set of isomorphisms between two finite
faced balls is finite. -/
theorem d39BallIso_set_finite {B C : D39FiniteBall} :
    (Set.univ : Set (D39BallIso B C)).Finite := by
  letI : Finite (D39BallIso B C) := d39BallIso_finite
  exact Set.finite_univ

/-- Helper toward Definition 3.8. Ball isomorphisms are determined by their
underlying dart equivalence. -/
theorem d39BallIso_ext {B C : D39FiniteBall} {I J : D39BallIso B C}
    (h : I.toEquiv = J.toEquiv) : I = J := by
  cases I with
  | mk i hi₁ hi₂ hi₃ hi₄ hi₅ hi₆ =>
    cases J with
    | mk j hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ =>
      simp_all

/-- Helper toward Definition 3.8. If every positive-radius faced-ball class
agrees, there is a family of ball isomorphisms compatible under restriction.
The family is obtained from the finite inverse system of ball isomorphisms. -/
theorem d39BallIso_exists_coherent_family (M N : D39RootedMap)
    (hball : ∀ r : ℕ,
      d39BallClass M (r + 1) (Nat.succ_pos r) =
        d39BallClass N (r + 1) (Nat.succ_pos r)) :
    ∃ F : (i : ℕ) → D39BallIso
        (d39FacedBall M (i + 1) (Nat.succ_pos i))
        (d39FacedBall N (i + 1) (Nat.succ_pos i)),
      ∀ ⦃i j : ℕ⦄ (hij : i ≤ j),
        (F j).restrict M N (Nat.succ_pos i) (Nat.succ_le_succ hij) = F i := by
  let α : ℕ → Type := fun i => D39BallIso
    (d39FacedBall M (i + 1) (Nat.succ_pos i))
    (d39FacedBall N (i + 1) (Nat.succ_pos i))
  let π : {i j : ℕ} → (hij : i ≤ j) → α j → α i := fun {i j} hij I =>
    I.restrict M N (Nat.succ_pos i) (Nat.succ_le_succ hij)
  have hπ_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a := by
    intro i a
    apply d39BallIso_ext
    apply Equiv.ext
    intro d
    apply Subtype.ext
    change ((a.restrict M N (Nat.succ_pos i) (Nat.le_refl (i + 1))).toEquiv d).1 =
      (a.toEquiv d).1
    rw [D39BallIso.restrict_apply]
    rfl
  have hπ_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (a : α k),
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intro i j k hij hjk a
    apply d39BallIso_ext
    apply Equiv.ext
    intro d
    apply Subtype.ext
    change (((a.restrict M N (Nat.succ_pos j) (Nat.succ_le_succ hjk)).restrict
      M N (Nat.succ_pos i) (Nat.succ_le_succ hij)).toEquiv d).1 =
      ((a.restrict M N (Nat.succ_pos i)
        (Nat.succ_le_succ (hij.trans hjk))).toEquiv d).1
    calc
      (((a.restrict M N (Nat.succ_pos j) (Nat.succ_le_succ hjk)).restrict
        M N (Nat.succ_pos i) (Nat.succ_le_succ hij)).toEquiv d).1 =
          ((a.restrict M N (Nat.succ_pos j) (Nat.succ_le_succ hjk)).toEquiv
            ⟨d.1, d39BallDarts_mono M (Nat.succ_le_succ hij) d.2⟩).1 :=
        D39BallIso.restrict_apply M N (Nat.succ_pos i) (Nat.succ_le_succ hij)
          (a.restrict M N (Nat.succ_pos j) (Nat.succ_le_succ hjk)) d
      _ = (a.toEquiv ⟨d.1,
          d39BallDarts_mono M (Nat.succ_le_succ (hij.trans hjk)) d.2⟩).1 :=
        D39BallIso.restrict_apply M N (Nat.succ_pos j) (Nat.succ_le_succ hjk) a
          ⟨d.1, d39BallDarts_mono M (Nat.succ_le_succ hij) d.2⟩
      _ = ((a.restrict M N (Nat.succ_pos i)
          (Nat.succ_le_succ (hij.trans hjk))).toEquiv d).1 :=
        (D39BallIso.restrict_apply M N (Nat.succ_pos i)
          (Nat.succ_le_succ (hij.trans hjk)) a d).symm
  have hfinite : ∀ i, Finite (α i) := by
    intro i
    exact d39BallIso_finite
  have hnonempty : ∀ i, Nonempty (α i) := by
    intro i
    dsimp [α]
    exact (d39BallClass_eq_iff M N (i + 1) (Nat.succ_pos i)).1 (hball i)
  have hone_step_finite : ∀ i a, {b : α (i + 1) | π (Nat.le_add_right i 1) b = a}.Finite := by
    intro i a
    letI : Finite (α (i + 1)) := hfinite (i + 1)
    exact Set.finite_univ.subset (by intro b hb; exact Set.mem_univ b)
  obtain ⟨F, hF⟩ := exists_seq_forall_proj_of_forall_finite π hπ_refl hπ_trans
    hone_step_finite
  exact ⟨F, hF⟩

/-- Helper toward Definition 3.8. Turn a coherent family of finite-ball
isomorphisms into a function on all ambient darts, using ball exhaustion. -/
noncomputable def d39CoherentBallIsoMap (M N : D39RootedMap)
    (F : (i : ℕ) → D39BallIso
      (d39FacedBall M (i + 1) (Nat.succ_pos i))
      (d39FacedBall N (i + 1) (Nat.succ_pos i))) : M.core.D → N.core.D := by
  classical
  intro d
  let i := Classical.choose (d39BallDarts_exhaust M d)
  have hd : d ∈ d39BallDarts M i := Classical.choose_spec (d39BallDarts_exhaust M d)
  exact ((F i).toEquiv ⟨d, d39BallDarts_mono M (Nat.le_succ i) hd⟩).1

/-- Helper toward Definition 3.8. The globally selected dart image agrees
with the finite isomorphism at any level containing that dart. -/
theorem d39CoherentBallIsoMap_apply_of_mem (M N : D39RootedMap)
    (F : (i : ℕ) → D39BallIso
      (d39FacedBall M (i + 1) (Nat.succ_pos i))
      (d39FacedBall N (i + 1) (Nat.succ_pos i)))
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j),
      (F j).restrict M N (Nat.succ_pos i) (Nat.succ_le_succ hij) = F i)
    {i : ℕ} {d : M.core.D} (hd : d ∈ d39BallDarts M (i + 1)) :
    d39CoherentBallIsoMap M N F d = ((F i).toEquiv ⟨d, hd⟩).1 := by
  classical
  let i₀ := Classical.choose (d39BallDarts_exhaust M d)
  have h₀ : d ∈ d39BallDarts M i₀ :=
    Classical.choose_spec (d39BallDarts_exhaust M d)
  let k := max i₀ i
  have h₀k : i₀ ≤ k := le_max_left _ _
  have hik : i ≤ k := le_max_right _ _
  have h₀k_ball : d ∈ d39BallDarts M (i₀ + 1) :=
    d39BallDarts_mono M (Nat.le_succ i₀) h₀
  have hk_ball : d ∈ d39BallDarts M (k + 1) :=
    d39BallDarts_mono M (Nat.succ_le_succ h₀k) h₀k_ball
  have hi_ball : d ∈ d39BallDarts M (i + 1) := hd
  have h₀eq := hF h₀k
  have hieq := hF hik
  have h₀point := congrArg (fun J : D39BallIso
      (d39FacedBall M (i₀ + 1) (Nat.succ_pos i₀))
      (d39FacedBall N (i₀ + 1) (Nat.succ_pos i₀)) =>
        (J.toEquiv ⟨d, h₀k_ball⟩).1) h₀eq
  have hipoint := congrArg (fun J : D39BallIso
      (d39FacedBall M (i + 1) (Nat.succ_pos i))
      (d39FacedBall N (i + 1) (Nat.succ_pos i)) =>
        (J.toEquiv ⟨d, hi_ball⟩).1) hieq
  have h₀restrict := D39BallIso.restrict_apply M N (Nat.succ_pos i₀)
    (Nat.succ_le_succ h₀k) (F k) ⟨d, h₀k_ball⟩
  have hirestrict := D39BallIso.restrict_apply M N (Nat.succ_pos i)
    (Nat.succ_le_succ hik) (F k) ⟨d, hi_ball⟩
  have h₀point' : ((F k).toEquiv ⟨d, hk_ball⟩).1 =
      ((F i₀).toEquiv ⟨d, h₀k_ball⟩).1 := by
    calc
      ((F k).toEquiv ⟨d, hk_ball⟩).1 =
          ((F k).toEquiv ⟨d,
            d39BallDarts_mono M (Nat.succ_le_succ h₀k) h₀k_ball⟩).1 := rfl
      _ = ((F i₀).toEquiv ⟨d, h₀k_ball⟩).1 := h₀restrict.symm.trans h₀point
  have hipoint' : ((F k).toEquiv ⟨d, hk_ball⟩).1 =
      ((F i).toEquiv ⟨d, hi_ball⟩).1 := by
    calc
      ((F k).toEquiv ⟨d, hk_ball⟩).1 =
          ((F k).toEquiv ⟨d,
            d39BallDarts_mono M (Nat.succ_le_succ hik) hi_ball⟩).1 := rfl
      _ = ((F i).toEquiv ⟨d, hi_ball⟩).1 := hirestrict.symm.trans hipoint
  unfold d39CoherentBallIsoMap
  dsimp only
  rw [h₀point'.symm, hipoint']

/-- Helper toward Definition 3.8. If the next ambient rotation dart lies in
the ball, its finite-ball first-return rotation is that dart. -/
theorem d39BallMap_rot_of_mem (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    {d : M.core.D} (hd : d ∈ d39BallDarts M r)
    (hrot : M.core.rot d ∈ d39BallDarts M r) :
    ((d39BallMap M r).rot ⟨d, hd⟩).1 = M.core.rot d := by
  classical
  let S := d39BallDarts M r
  let hreturn : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  change (cyclicFirstReturn M.core.rot S hreturn ⟨d, hd⟩).1 = M.core.rot d
  have htime : cyclicFirstReturnTime M.core.rot S hreturn ⟨d, hd⟩ = 1 := by
    apply le_antisymm
    · exact Nat.find_min' (hreturn ⟨d, hd⟩)
        ⟨Nat.one_pos, by simpa [S, pow_one] using hrot⟩
    · exact (cyclicFirstReturnTime_spec M.core.rot S hreturn ⟨d, hd⟩).1
  rw [(firstReturn_spec M.core.rot S hreturn ⟨d, hd⟩).1, htime, pow_one]

/-- Helper toward Definition 3.8. The rotation stored in the faced-ball
record agrees with the ambient rotation whenever its next dart is retained. -/
theorem d39FacedBallMap_rot_of_mem (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    {d : M.core.D} (hd : d ∈ d39BallDarts M r)
    (hrot : M.core.rot d ∈ d39BallDarts M r) :
    (((d39FacedBall M r hr).map.rot ⟨d, hd⟩).1) = M.core.rot d := by
  classical
  let B := d39FacedBall M r hr
  letI : DecidableEq B.D := B.instDecidableEqD
  change ((d39BallMap M r).rot ⟨d, hd⟩).1 = M.core.rot d
  exact d39BallMap_rot_of_mem M r hd hrot

/-- Helper toward Definition 3.8. The edge reversal stored in the faced-ball
record agrees with ambient edge reversal. -/
theorem d39FacedBallMap_edgeInv (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) :
    (((d39FacedBall M r hr).map.edgeInv d).1) = M.core.edgeInv d.1 := by
  classical
  let B := d39FacedBall M r hr
  letI : DecidableEq B.D := B.instDecidableEqD
  change ((d39BallMap M r).edgeInv d).1 = M.core.edgeInv d.1
  exact d39BallMap_edgeInv M r d

/-- Helper toward Definition 3.8. The ambient dart function induced by a
coherent family of finite-ball isomorphisms is bijective. -/
theorem d39CoherentBallIsoMap_bijective (M N : D39RootedMap)
    (F : (i : ℕ) → D39BallIso
      (d39FacedBall M (i + 1) (Nat.succ_pos i))
      (d39FacedBall N (i + 1) (Nat.succ_pos i)))
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j),
      (F j).restrict M N (Nat.succ_pos i) (Nat.succ_le_succ hij) = F i) :
    Function.Bijective (d39CoherentBallIsoMap M N F) := by
  classical
  constructor
  · intro d e hde
    obtain ⟨rd, hrd⟩ := d39BallDarts_exhaust M d
    obtain ⟨re, hre⟩ := d39BallDarts_exhaust M e
    let i := max rd re
    have hdi : d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (by dsimp [i]; omega) hrd
    have hei : e ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (by dsimp [i]; omega) hre
    have hfd := d39CoherentBallIsoMap_apply_of_mem M N F hF hdi
    have hfe := d39CoherentBallIsoMap_apply_of_mem M N F hF hei
    have heq : (F i).toEquiv ⟨d, hdi⟩ = (F i).toEquiv ⟨e, hei⟩ := by
      apply Subtype.ext
      simpa [hfd, hfe] using hde
    have := (F i).toEquiv.injective heq
    exact congrArg Subtype.val this
  · intro y
    obtain ⟨r, hr⟩ := d39BallDarts_exhaust N y
    let i := r
    have hy : y ∈ d39BallDarts N (i + 1) :=
      d39BallDarts_mono N (by dsimp [i]; omega) hr
    let y' : (d39FacedBall N (i + 1) (Nat.succ_pos i)).D := ⟨y, hy⟩
    let x' := (F i).toEquiv.symm y'
    refine ⟨x'.1, ?_⟩
    have hx : x'.1 ∈ d39BallDarts M (i + 1) := x'.2
    rw [d39CoherentBallIsoMap_apply_of_mem M N F hF hx]
    exact congrArg Subtype.val ((F i).toEquiv.apply_symm_apply y')

/-- Helper toward Definition 3.8. A coherent family of rooted faced-ball
isomorphisms glues to a rooted whole-map isomorphism. -/
noncomputable def d39BallIso_glue (M N : D39RootedMap)
    (F : (i : ℕ) → D39BallIso
      (d39FacedBall M (i + 1) (Nat.succ_pos i))
      (d39FacedBall N (i + 1) (Nat.succ_pos i)))
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j),
      (F j).restrict M N (Nat.succ_pos i) (Nat.succ_le_succ hij) = F i) :
    D39RootedMapIso M N := by
  classical
  let f := d39CoherentBallIsoMap M N F
  let e : M.core.D ≃ N.core.D :=
    Equiv.ofBijective f (d39CoherentBallIsoMap_bijective M N F hF)
  refine {
    toEquiv := e
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    root_dart_comm := ?_ }
  · intro d
    change d39CoherentBallIsoMap M N F (M.core.rot d) =
      N.core.rot (d39CoherentBallIsoMap M N F d)
    obtain ⟨rd, hrd⟩ := d39BallDarts_exhaust M d
    obtain ⟨rr, hrr⟩ := d39BallDarts_exhaust M (M.core.rot d)
    obtain ⟨rn, hrn⟩ := d39BallDarts_exhaust N (f d)
    obtain ⟨rs, hrs⟩ := d39BallDarts_exhaust N (N.core.rot (f d))
    let i := max (max (max rd rr) rn) rs
    have hrd_i : rd ≤ i := by
      dsimp [i]
      calc
        rd ≤ max rd rr := le_max_left _ _
        _ ≤ max (max rd rr) rn := le_max_left _ _
        _ ≤ max (max (max rd rr) rn) rs := le_max_left _ _
    have hrr_i : rr ≤ i := by
      dsimp [i]
      calc
        rr ≤ max rd rr := le_max_right _ _
        _ ≤ max (max rd rr) rn := le_max_left _ _
        _ ≤ max (max (max rd rr) rn) rs := le_max_left _ _
    have hrn_i : rn ≤ i := by
      dsimp [i]
      calc
        rn ≤ max (max rd rr) rn := le_max_right _ _
        _ ≤ max (max (max rd rr) rn) rs := le_max_left _ _
    have hrs_i : rs ≤ i := by dsimp [i]; exact le_max_right _ _
    have hdi : d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (le_trans hrd_i (Nat.le_succ i)) hrd
    have hri : M.core.rot d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (le_trans hrr_i (Nat.le_succ i)) hrr
    have hyi : f d ∈ d39BallDarts N (i + 1) :=
      d39BallDarts_mono N (le_trans hrn_i (Nat.le_succ i)) hrn
    have hni : N.core.rot (f d) ∈ d39BallDarts N (i + 1) :=
      d39BallDarts_mono N (le_trans hrs_i (Nat.le_succ i)) hrs
    have hfd := d39CoherentBallIsoMap_apply_of_mem M N F hF hdi
    have hfr := d39CoherentBallIsoMap_apply_of_mem M N F hF hri
    have hrotM := d39FacedBallMap_rot_of_mem M (i + 1) (Nat.succ_pos i) hdi hri
    have hballComm := (F i).rot_comm ⟨d, hdi⟩
    have hni' : N.core.rot ((F i).toEquiv ⟨d, hdi⟩).1 ∈
        d39BallDarts N (i + 1) := by
      change N.core.rot (d39CoherentBallIsoMap M N F d) ∈
        d39BallDarts N (i + 1) at hni
      rw [hfd] at hni
      exact hni
    have hrotN := d39FacedBallMap_rot_of_mem N (i + 1) (Nat.succ_pos i)
      ((F i).toEquiv ⟨d, hdi⟩).2 hni'
    have hrotM_eq :
        ((d39FacedBall M (i + 1) (Nat.succ_pos i)).map.rot
          ⟨d, hdi⟩) = ⟨M.core.rot d, hri⟩ := by
      apply Subtype.ext
      exact hrotM
    have hrotN_eq :
        ((d39FacedBall N (i + 1) (Nat.succ_pos i)).map.rot
          ((F i).toEquiv ⟨d, hdi⟩)) =
          ⟨N.core.rot ((F i).toEquiv ⟨d, hdi⟩).1, hni'⟩ := by
      apply Subtype.ext
      exact hrotN
    have hcomm_val :
        ((F i).toEquiv ⟨M.core.rot d, hri⟩).1 =
          N.core.rot ((F i).toEquiv ⟨d, hdi⟩).1 := by
      calc
        ((F i).toEquiv ⟨M.core.rot d, hri⟩).1 =
            ((F i).toEquiv ((d39FacedBall M (i + 1) (Nat.succ_pos i)).map.rot
              ⟨d, hdi⟩)).1 := by rw [hrotM_eq]
        _ = ((d39FacedBall N (i + 1) (Nat.succ_pos i)).map.rot
            ((F i).toEquiv ⟨d, hdi⟩)).1 := congrArg Subtype.val hballComm
        _ = N.core.rot ((F i).toEquiv ⟨d, hdi⟩).1 :=
          congrArg Subtype.val hrotN_eq
    change f (M.core.rot d) = N.core.rot (f d)
    calc
      f (M.core.rot d) = ((F i).toEquiv ⟨M.core.rot d, hri⟩).1 := hfr
      _ = N.core.rot ((F i).toEquiv ⟨d, hdi⟩).1 := hcomm_val
      _ = N.core.rot (f d) := congrArg N.core.rot hfd.symm
  · intro d
    change d39CoherentBallIsoMap M N F (M.core.edgeInv d) =
      N.core.edgeInv (d39CoherentBallIsoMap M N F d)
    obtain ⟨rm, hm⟩ := d39BallDarts_exhaust M d
    obtain ⟨rn, hn⟩ := d39BallDarts_exhaust N (f d)
    let i := max rm rn
    have hrm_i : rm ≤ i := by dsimp [i]; exact le_max_left _ _
    have hrn_i : rn ≤ i := by dsimp [i]; exact le_max_right _ _
    have hdi : d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (le_trans hrm_i (Nat.le_succ i)) hm
    have hfi : f d ∈ d39BallDarts N (i + 1) :=
      d39BallDarts_mono N (le_trans hrn_i (Nat.le_succ i)) hn
    have hrevM : M.core.edgeInv d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_edgeInv_closed M (i + 1) d hdi
    have hrevN : N.core.edgeInv (f d) ∈ d39BallDarts N (i + 1) :=
      d39BallDarts_edgeInv_closed N (i + 1) (f d) hfi
    have hfd := d39CoherentBallIsoMap_apply_of_mem M N F hF hdi
    have hfrev := d39CoherentBallIsoMap_apply_of_mem M N F hF hrevM
    have hcomm := (F i).edgeInv_comm ⟨d, hdi⟩
    have hrevN' : N.core.edgeInv ((F i).toEquiv ⟨d, hdi⟩).1 ∈
        d39BallDarts N (i + 1) := by
      change N.core.edgeInv (d39CoherentBallIsoMap M N F d) ∈
        d39BallDarts N (i + 1) at hrevN
      rw [hfd] at hrevN
      exact hrevN
    have hrevM_eq :
        ((d39FacedBall M (i + 1) (Nat.succ_pos i)).map.edgeInv ⟨d, hdi⟩) =
          ⟨M.core.edgeInv d, hrevM⟩ := by
      apply Subtype.ext
      exact d39FacedBallMap_edgeInv M (i + 1) (Nat.succ_pos i) ⟨d, hdi⟩
    have hrevN_eq :
        ((d39FacedBall N (i + 1) (Nat.succ_pos i)).map.edgeInv
          ((F i).toEquiv ⟨d, hdi⟩)) =
          ⟨N.core.edgeInv ((F i).toEquiv ⟨d, hdi⟩).1, hrevN'⟩ := by
      apply Subtype.ext
      exact d39FacedBallMap_edgeInv N (i + 1) (Nat.succ_pos i)
        ((F i).toEquiv ⟨d, hdi⟩)
    have hcomm_ball :
        ((F i).toEquiv ⟨M.core.edgeInv d, hrevM⟩).1 =
          N.core.edgeInv ((F i).toEquiv ⟨d, hdi⟩).1 := by
      calc
        ((F i).toEquiv ⟨M.core.edgeInv d, hrevM⟩).1 =
            ((F i).toEquiv ((d39FacedBall M (i + 1) (Nat.succ_pos i)).map.edgeInv
              ⟨d, hdi⟩)).1 := by rw [hrevM_eq]
        _ = ((d39FacedBall N (i + 1) (Nat.succ_pos i)).map.edgeInv
            ((F i).toEquiv ⟨d, hdi⟩)).1 := congrArg Subtype.val hcomm
        _ = N.core.edgeInv ((F i).toEquiv ⟨d, hdi⟩).1 :=
          congrArg Subtype.val hrevN_eq
    change f (M.core.edgeInv d) = N.core.edgeInv (f d)
    calc
      f (M.core.edgeInv d) = ((F i).toEquiv ⟨M.core.edgeInv d, hrevM⟩).1 := hfrev
      _ = N.core.edgeInv ((F i).toEquiv ⟨d, hdi⟩).1 := hcomm_ball
      _ = N.core.edgeInv (f d) := congrArg N.core.edgeInv hfd.symm
  · intro d
    change N.core.missing (d39CoherentBallIsoMap M N F d) ↔ M.core.missing d
    obtain ⟨r, hr⟩ := d39BallDarts_exhaust M d
    let i := r
    have hdi : d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (by dsimp [i]; omega) hr
    have hfd := d39CoherentBallIsoMap_apply_of_mem M N F hF hdi
    have hmiss := (F i).missing_iff ⟨d, hdi⟩
    have hmiss' : N.core.missing ((F i).toEquiv ⟨d, hdi⟩).1 ↔
        M.core.missing d := by
      simpa [d39FacedBall, d39BallMissing] using hmiss
    rw [hfd]
    exact hmiss'
  · intro d hd
    change N.core.tail (d39CoherentBallIsoMap M N F d) ↔ M.core.tail d
    obtain ⟨r, hr⟩ := d39BallDarts_exhaust M d
    let i := r
    have hdi : d ∈ d39BallDarts M (i + 1) :=
      d39BallDarts_mono M (Nat.le_succ i) hr
    have hfd := d39CoherentBallIsoMap_apply_of_mem M N F hF hdi
    have htail := (F i).tail_iff ⟨d, hdi⟩
    have htail' : N.core.tail ((F i).toEquiv ⟨d, hdi⟩).1 ↔
        M.core.tail d := by
      simpa [d39FacedBall, d39BallTail] using htail
    rw [hfd]
    exact htail'
  · change d39CoherentBallIsoMap M N F M.rootMark.dart = N.rootMark.dart
    have hm : M.rootMark.dart ∈ d39BallDarts M (0 + 1) :=
      (d39BallDarts_root_mem M (Nat.succ_pos 0)).1
    have hn : N.rootMark.dart ∈ d39BallDarts N (0 + 1) :=
      (d39BallDarts_root_mem N (Nat.succ_pos 0)).1
    have hroot := d39CoherentBallIsoMap_apply_of_mem M N F hF hm
    rw [hroot]
    exact congrArg Subtype.val (F 0).root_comm

/-- Helper toward Definition 3.8. The descended class distance separates
rooted planar-map classes. -/
theorem d39PlanarRootedMapClassDistance_eq_zero_iff
    (M N : D39PlanarRootedMapClass) :
    d39PlanarRootedMapClassDistance M N = 0 ↔ M = N := by
  refine Quotient.inductionOn₂ M N ?_
  intro A B
  rw [d39PlanarRootedMapClassDistance_mk_mk]
  constructor
  · intro hzero
    have hball := (d39RootedBallSystem_distance_eq_zero_iff
      A.toD39RootedMap B.toD39RootedMap).1 hzero
    obtain ⟨F, hF⟩ := d39BallIso_exists_coherent_family
      A.toD39RootedMap B.toD39RootedMap hball
    exact Quotient.sound ⟨d39BallIso_glue
      A.toD39RootedMap B.toD39RootedMap F hF⟩
  · intro hclass
    obtain ⟨I⟩ := Quotient.exact hclass
    apply (d39RootedBallSystem_distance_eq_zero_iff
      A.toD39RootedMap B.toD39RootedMap).2
    intro r
    exact D39RootedMapIso.d39BallClass_eq I r

end DirectedDistances.PaperProofs.Section3
