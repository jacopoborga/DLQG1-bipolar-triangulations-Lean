module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallFramed
public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallCompat
public import DirectedDistances.PlanarMap.FramedBallCountable
import Mathlib.Basic.Countable.Basic

noncomputable section

public section
namespace DirectedDistances.PlanarMap

open Equiv CombinatorialMap

local instance (M : RootedLocallyFiniteMap) : DecidableEq M.D := Classical.decEq _

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A framed ball with a union of face cycles marking the retained original faces. -/
structure FacedFramedBall where
  toFramedBall : FramedBall
  original : Set toFramedBall.D
  original_closed : ∀ d, toFramedBall.map.faceSucc d ∈ original ↔ d ∈ original

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Preserve and reflect the original-face selection as well as the framed map. -/
structure FacedFramedBallIso (B C : FacedFramedBall) where
  toFramedBallIso : FramedBallIso B.toFramedBall C.toFramedBall
  original_iff : ∀ d, toFramedBallIso.mapIso.toEquiv d ∈ C.original ↔ d ∈ B.original

private theorem face_comm {B C : FramedBall} (I : FramedBallIso B C) (d : B.D) :
    I.mapIso.toEquiv (B.map.faceSucc d) = C.map.faceSucc (I.mapIso.toEquiv d) := by
  change I.mapIso.toEquiv (B.map.rot.symm (B.map.edgeInv d)) =
    C.map.rot.symm (C.map.edgeInv (I.mapIso.toEquiv d))
  apply C.map.rot.injective
  rw [← I.mapIso.rot_comm, B.map.rot.apply_symm_apply,
    C.map.rot.apply_symm_apply, I.mapIso.edgeInv_comm]

namespace FacedFramedBallIso

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def refl (B : FacedFramedBall) : FacedFramedBallIso B B where
  toFramedBallIso := FramedBallIso.refl B.toFramedBall
  original_iff := fun _ => Iff.rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def symm {B C : FacedFramedBall} (I : FacedFramedBallIso B C) :
    FacedFramedBallIso C B where
  toFramedBallIso := I.toFramedBallIso.symm
  original_iff := by
    intro d
    have h := I.original_iff (I.toFramedBallIso.mapIso.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def trans {B C E : FacedFramedBall}
    (I : FacedFramedBallIso B C) (J : FacedFramedBallIso C E) :
    FacedFramedBallIso B E where
  toFramedBallIso := I.toFramedBallIso.trans J.toFramedBallIso
  original_iff := fun d => (J.original_iff _).trans (I.original_iff d)

end FacedFramedBallIso

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def FacedFramedBall.setoid : Setoid FacedFramedBall where
  r B C := Nonempty (FacedFramedBallIso B C)
  iseqv := ⟨fun B => ⟨FacedFramedBallIso.refl B⟩,
    fun ⟨I⟩ => ⟨I.symm⟩, fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def FacedFramedBallClass := Quotient FacedFramedBall.setoid

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def FacedFramedBallClass.forget : FacedFramedBallClass → FramedBallClass :=
  Quotient.map FacedFramedBall.toFramedBall (fun _ _ ⟨I⟩ => ⟨I.toFramedBallIso⟩)

private def FaceSelections (B : FramedBall) :=
  {S : Set B.D // ∀ d, B.map.faceSucc d ∈ S ↔ d ∈ S}

private instance (B : FramedBall) : Countable (FaceSelections B) := by
  dsimp [FaceSelections]
  infer_instance

private noncomputable def facedCodeClass
    (a : Σ q : FramedBallClass, FaceSelections q.out) : FacedFramedBallClass :=
  Quotient.mk FacedFramedBall.setoid ⟨a.1.out, a.2.1, a.2.2⟩

private theorem facedCodeClass_surjective : Function.Surjective facedCodeClass := by
  intro q
  refine Quotient.inductionOn q ?_
  intro B
  let c : FramedBallClass := Quotient.mk FramedBall.setoid B.toFramedBall
  obtain ⟨I⟩ : Nonempty (FramedBallIso c.out B.toFramedBall) :=
    Quotient.exact c.out_eq
  let S : FaceSelections c.out := ⟨{d | I.mapIso.toEquiv d ∈ B.original}, by
    intro d
    change I.mapIso.toEquiv (c.out.map.faceSucc d) ∈ B.original ↔ _
    rw [face_comm I]
    exact B.original_closed _⟩
  refine ⟨⟨c, S⟩, Quotient.sound ⟨?_⟩⟩
  exact ⟨I, fun _ => Iff.rfl⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Finite selections over countably many framed classes give countably many faced classes. -/
instance instCountableFacedFramedBallClass : Countable FacedFramedBallClass :=
  by
    have : Countable FramedBallClass := instCountableFramedBallClass
    have : ∀ q : FramedBallClass, Countable (FaceSelections q.out) :=
      fun _ => inferInstance
    exact Function.Surjective.countable facedCodeClass_surjective

private theorem original_face_step (M : RootedLocallyFiniteMap) (r : ℕ)
    (d : M.D) :
    rootedLocallyFiniteBallContainsOriginalFace M r (M.rot.symm (M.edgeInv d)) ↔
      rootedLocallyFiniteBallContainsOriginalFace M r d := by
  unfold rootedLocallyFiniteBallContainsOriginalFace
  exact forall_congr' fun e =>
    imp_congr (Equiv.Perm.sameCycle_apply_left (f := M.rot.symm * M.edgeInv)) Iff.rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The actual ball selects exactly the ambient faces all of whose darts are retained. -/
@[expose, reducible] noncomputable def rootedLocallyFiniteFacedBall
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) : FacedFramedBall where
  toFramedBall := rootedLocallyFiniteFramedBall M r hr
  original := {d | rootedLocallyFiniteBallContainsOriginalFace
    M.toRootedLocallyFiniteMap r d.1}
  original_closed := by
    classical
    intro d
    change rootedLocallyFiniteBallContainsOriginalFace M.toRootedLocallyFiniteMap r
      (((rootedLocallyFiniteBallCombinatorialMap M.toRootedLocallyFiniteMap r).faceSucc
        d).1) ↔ _
    constructor
    · intro h
      have hback : rootedLocallyFiniteBallContainsOriginalFace
          M.toRootedLocallyFiniteMap r d.1 := by
        let p := (rootedLocallyFiniteBallCombinatorialMap
          M.toRootedLocallyFiniteMap r).faceSucc
        let x : {d : M.D // d ∈
            rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r} := d
        have hprop : ∀ n : ℕ, rootedLocallyFiniteBallContainsOriginalFace
            M.toRootedLocallyFiniteMap r ((p ^ (n + 1)) x).1 := by
          intro n
          induction n with
          | zero => exact h
          | succ n ih =>
            rw [pow_succ', Equiv.Perm.mul_apply]
            rw [rootedLocallyFiniteBall_faceSucc_of_contained
              M.toRootedLocallyFiniteMap r _ ih]
            exact (original_face_step M.toRootedLocallyFiniteMap r _).2 ih
        obtain ⟨n, hn, _, heq⟩ :=
          (Equiv.Perm.SameCycle.rfl (f := p) (x := x)).exists_pow_eq''
        cases n with
        | zero => omega
        | succ n =>
          have ht := hprop n
          rw [heq] at ht
          exact ht
      exact hback
    · intro h
      rw [rootedLocallyFiniteBall_faceSucc_of_contained M.toRootedLocallyFiniteMap r d h]
      exact (original_face_step M.toRootedLocallyFiniteMap r d.1).2 h


private theorem commuting_zpow {A C : Type*} (f : A → C)
    (p : Equiv.Perm A) (q : Equiv.Perm C)
    (h : ∀ x, f (p x) = q (f x)) (i : ℤ) (x : A) :
    f ((p ^ i) x) = (q ^ i) (f x) := by
  have hnat (n : ℕ) : ∀ x, f ((p ^ n) x) = (q ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, h, ih]
  have hinv (x : A) : f (p.symm x) = q.symm (f x) := by
    apply q.injective
    rw [← h, p.apply_symm_apply, q.apply_symm_apply]
  have hneg (n : ℕ) : ∀ x, f ((p.symm ^ n) x) = (q.symm ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  cases i with
  | ofNat n => exact hnat n x
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using hneg (n + 1) x

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A selected original face has exactly its ambient face cycle, with incidences. -/
theorem rootedLocallyFiniteFacedBall_original_cycle
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r)
    (d e : (rootedLocallyFiniteFramedBall M r hr).D)
    (hd : d ∈ (rootedLocallyFiniteFacedBall M r hr).original) :
    (rootedLocallyFiniteFramedBall M r hr).map.faceSucc.SameCycle d e ↔
      Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) d.1 e.1 := by
  classical
  let B := rootedLocallyFiniteFacedBall M r hr
  let p := B.toFramedBall.map.faceSucc.subtypePerm B.original_closed
  let x : {d : B.toFramedBall.D // d ∈ B.original} := ⟨d, hd⟩
  let f : {d : B.toFramedBall.D // d ∈ B.original} → M.D := fun z => z.1.1
  have hc (z) : f (p z) = (M.rot.symm * M.edgeInv) (f z) :=
    rootedLocallyFiniteBall_faceSucc_of_contained M.toRootedLocallyFiniteMap r z.1 z.2
  have hb (i : ℤ) : ((p ^ i) x).1 = (B.toFramedBall.map.faceSucc ^ i) d := by
    simp only [p, Equiv.Perm.subtypePerm_zpow, Equiv.Perm.subtypePerm_apply, x]
  have ha (i : ℤ) : ((p ^ i) x).1.1 = ((M.rot.symm * M.edgeInv) ^ i) d.1 :=
    commuting_zpow f p (M.rot.symm * M.edgeInv) hc i x
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← ha i, hb i, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [← hb i, ha i, hi]

private theorem original_radius_iff
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hs : 0 < s) (hrs : r ≤ s)
    (d : (rootedLocallyFiniteFramedBall M s hs).D) :
    rootedLocallyFiniteBallContainsOriginalFace M.toRootedLocallyFiniteMap r d.1 ↔
      d ∈ (rootedLocallyFiniteFacedBall M s hs).original ∧
        ∀ e, (rootedLocallyFiniteFramedBall M s hs).map.faceSucc.SameCycle d e →
          e.1 ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
  constructor
  · intro h
    have hlarge : d ∈ (rootedLocallyFiniteFacedBall M s hs).original :=
      fun e he => rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs
        (h e he)
    refine ⟨hlarge, fun e he => h e.1 ?_⟩
    exact (rootedLocallyFiniteFacedBall_original_cycle M s hs d e hlarge).1 he
  · rintro ⟨hlarge, hsmall⟩ e he
    let e' : (rootedLocallyFiniteFramedBall M s hs).D := ⟨e, hlarge e he⟩
    exact hsmall e'
      ((rootedLocallyFiniteFacedBall_original_cycle M s hs d e' hlarge).2 he)

private theorem nested_radius_mem_iff
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (d : (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)).D) :
    d.1 ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r ↔
      d ∈ framedBallRadiusDarts (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)) r :=
  by
    classical
    rw [rootedLocallyFiniteFramedBallRadiusExact_proved M hr hrs]
    change d.1 ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r ↔
      (⟨d.1, d.2⟩ : {e : M.D // e ∈
        rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap s}) ∈
          rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s
    simp only [rootedLocallyFiniteNestedBallDarts, firstReturnSubset,
      Finset.mem_filter, Finset.mem_univ, true_and]

private theorem original_iso_radius_iff
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFacedBall N s (hr.trans_le hrs)))
    (d : (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)).D) :
    rootedLocallyFiniteBallContainsOriginalFace N.toRootedLocallyFiniteMap r
        (I.toFramedBallIso.mapIso.toEquiv d).1 ↔
      rootedLocallyFiniteBallContainsOriginalFace M.toRootedLocallyFiniteMap r d.1 := by
  let J := I.toFramedBallIso
  have hcycle := framedBall_sameCycle_iff_of_equiv J.mapIso.toEquiv
    (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)).map.faceSucc
    (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs)).map.faceSucc
    (face_comm J)
  have hmem (e) : (J.mapIso.toEquiv e).1 ∈
      rootedLocallyFiniteBallDarts N.toRootedLocallyFiniteMap r ↔
      e.1 ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r :=
    (nested_radius_mem_iff N hr hrs _).trans
      ((framedBallRadiusDarts_mem_iso_iff J r e).trans
        (nested_radius_mem_iff M hr hrs e).symm)
  rw [original_radius_iff N (hr.trans_le hrs) hrs,
    original_radius_iff M (hr.trans_le hrs) hrs]
  constructor
  · rintro ⟨h, hall⟩
    refine ⟨(I.original_iff d).1 h, fun e he => (hmem e).1 ?_⟩
    exact hall (J.mapIso.toEquiv e) ((hcycle d e).1 he)
  · rintro ⟨h, hall⟩
    refine ⟨(I.original_iff d).2 h, ?_⟩
    intro e he
    obtain ⟨e, rfl⟩ := J.mapIso.toEquiv.surjective e
    exact (hmem e).2 (hall e ((hcycle d e).2 he))


/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Restriction preserves the retained original faces as well as all framed data. -/
@[expose] noncomputable def rootedLocallyFiniteFacedBallIso_restrict
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFacedBall N s (hr.trans_le hrs))) :
    FacedFramedBallIso (rootedLocallyFiniteFacedBall M r hr)
      (rootedLocallyFiniteFacedBall N r hr) where
  toFramedBallIso := rootedLocallyFiniteFramedBallIso_restrict M N hr hrs I.toFramedBallIso
  original_iff := by
    intro d
    change rootedLocallyFiniteBallContainsOriginalFace N.toRootedLocallyFiniteMap r
      ((rootedLocallyFiniteFramedBallIso_restrict M N hr hrs
        I.toFramedBallIso).mapIso.toEquiv d).1 ↔ _
    rw [rootedLocallyFiniteFramedBallIso_restrict_apply]
    exact original_iso_radius_iff M N hr hrs I
      ⟨d.1, rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs d.2⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] noncomputable def rootedLocallyFiniteFacedBallClass
    (r : ℕ) (M : RootedLocallyFinitePlanarMap) : FacedFramedBallClass :=
  Quotient.mk FacedFramedBall.setoid (rootedLocallyFiniteFacedBall M (r + 1) (by omega))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
@[expose] def rootedLocallyFiniteFacedBallRestrictionCompatible : Prop :=
  ∀ (r : ℕ) (M N : RootedLocallyFinitePlanarMap),
    rootedLocallyFiniteFacedBallClass (r + 1) M =
        rootedLocallyFiniteFacedBallClass (r + 1) N →
      rootedLocallyFiniteFacedBallClass r M = rootedLocallyFiniteFacedBallClass r N

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The faced compatibility obligation is proved without extra premises. -/
theorem rootedLocallyFiniteFacedBallRestrictionCompatible_proved :
    rootedLocallyFiniteFacedBallRestrictionCompatible := by
  intro r M N h
  obtain ⟨I⟩ := Quotient.exact h
  exact Quotient.sound ⟨rootedLocallyFiniteFacedBallIso_restrict M N
    (Nat.succ_pos r) (Nat.le_succ (r + 1)) I⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Forgetting the selection recovers the existing framed class at every radius. -/
theorem rootedLocallyFiniteFacedBallClass_forget (r : ℕ)
    (M : RootedLocallyFinitePlanarMap) :
    (rootedLocallyFiniteFacedBallClass r M).forget =
      rootedLocallyFiniteFramedBallClass r M := rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Forgetting a restricted isomorphism agrees with the existing restriction operation. -/
theorem rootedLocallyFiniteFacedBallIso_restrict_forget
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFacedBall N s (hr.trans_le hrs))) :
    (rootedLocallyFiniteFacedBallIso_restrict M N hr hrs I).toFramedBallIso =
      rootedLocallyFiniteFramedBallIso_restrict M N hr hrs I.toFramedBallIso := rfl

end DirectedDistances.PlanarMap
end
