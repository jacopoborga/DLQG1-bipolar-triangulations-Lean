module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorShifted
public import DirectedDistances.PlanarMap.CombinatorialMapEulerBound
public import DirectedDistances.PlanarMap.D39Ball

/-! Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.

Both geometric fields of the lower-carrier reflection are proved here. Finite
connected first-return restrictions preserve planarity by extension of mod-two
cycles, and finite ambient face paths give outer capture without planarity.

The remaining obligation is
`RootedLocallyFiniteMirrorShiftedClassDeterminacy mirrorRootedLocallyFinitePlanarMap`.
It is neither proved nor assumed here. In isomorphism form, an isomorphism of
source faced balls at radius `r + 2` must induce an isomorphism of reflected
faced balls at radius `r + 1`, including their retained original-face selections.
The same-radius restriction API does not perform this change of center.
No continuity, measurability, or paper symmetry theorem is asserted. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private noncomputable def mirrorCloseEdgeExtension
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) : EdgeSpace M := by
  classical
  let N := inducedCombinatorialMap M S hflip
  refine fun q => Quotient.lift
    (fun d => if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) ?_ q
  intro d e hde
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M d e).mp hde with h | h
  · subst e
    rfl
  · subst e
    by_cases hd : d ∈ S
    · rw [dite_eq_left hd, dite_eq_left (hflip d hd)]
      apply congrArg c
      apply Quotient.sound
      exact (CombinatorialMap.edgeInv_sameCycle_iff N _ _).mpr (Or.inr rfl)
    · have hf : M.edgeInv d ∉ S := by
        intro h
        have hh := hflip (M.edgeInv d) h
        exact hd (by simpa only [M.edgeInv_invol] using hh)
      rw [dite_eq_right hd, dite_eq_right hf]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorCloseEdgeExtension_apply
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) (d : D) :
    mirrorCloseEdgeExtension M S hflip c (edgeClass M d) =
      if hd : d ∈ S then
        c (edgeClass (inducedCombinatorialMap M S hflip) ⟨d, hd⟩) else 0 := by
  classical
  rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorCloseEdgeExtension_cycle
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip))
    (hc : vertexBoundary (inducedCombinatorialMap M S hflip) c = 0) :
    vertexBoundary M (mirrorCloseEdgeExtension M S hflip c) = 0 := by
  classical
  let N := inducedCombinatorialMap M S hflip
  ext v
  change (∑ d : D, if vertexClass M d = v then
    mirrorCloseEdgeExtension M S hflip c (edgeClass M d) else 0) = 0
  simp_rw [mirrorCloseEdgeExtension_apply]
  have hsum : (∑ d : D, if vertexClass M d = v then
      (if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) else 0) =
      ∑ d : S, if vertexClass M d.1 = v then c (edgeClass N d) else 0 := by
    calc
      _ = ∑ d : D, if hd : d ∈ S then
          (if vertexClass M d = v then c (edgeClass N ⟨d, hd⟩) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d ∈ S <;> by_cases hv : vertexClass M d = v <;> simp [hd, hv]
      _ = _ := by
        simpa only [Finset.univ_eq_attach] using
          (Finset.sum_attach_eq_sum_dite S (fun d : S =>
            if vertexClass M d.1 = v then c (edgeClass N d) else 0)).symm
  rw [hsum]
  by_cases hv : ∃ x : S, vertexClass M x.1 = v
  · obtain ⟨x, hx⟩ := hv
    have heq (d : S) : vertexClass M d.1 = v ↔ vertexClass N d = vertexClass N x := by
      rw [← hx]
      constructor
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mpr
          (Quotient.exact h)
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mp
          (Quotient.exact h)
    simp_rw [heq]
    exact congrFun hc (vertexClass N x)
  · apply Finset.sum_eq_zero
    intro d _
    exact ite_eq_right (fun hd => hv ⟨d, hd⟩)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorCloseFaceCorner (M : CombinatorialMap D) (A : FaceSpace M) (d : D) :
    A (faceClass M (M.edgeInv (M.rot d))) = A (faceClass M d) := by
  apply congrArg A
  apply Quotient.sound
  change M.faceSucc.SameCycle (M.edgeInv (M.rot d)) d
  have h : M.faceSucc.SameCycle (M.edgeInv (M.rot d))
      (M.faceSucc (M.edgeInv (M.rot d))) :=
    Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
  simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorCloseFaceRot
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (A : FaceSpace M)
    (hzero : ∀ d, d ∉ S → A (faceClass M d) = A (faceClass M (M.edgeInv d)))
    (z : S) :
    A (faceClass M z.1) =
      A (faceClass M (M.edgeInv ((inducedCombinatorialMap M S hflip).rot z).1)) := by
  let k := cyclicFirstReturnTime M.rot S (finitePermutationReturn M.rot S) z
  have hk := cyclicFirstReturnTime_spec M.rot S (finitePermutationReturn M.rot S) z
  have hskip : ∀ j : ℕ, j < k →
      A (faceClass M ((M.rot ^ j) z.1)) = A (faceClass M z.1) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hdel : (M.rot ^ (j + 1)) z.1 ∉ S := hk.2.2 (j + 1) (by omega) hj
      calc
        _ = A (faceClass M (M.edgeInv ((M.rot ^ (j + 1)) z.1))) := hzero _ hdel
        _ = A (faceClass M ((M.rot ^ j) z.1)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact mirrorCloseFaceCorner M A _
        _ = A (faceClass M z.1) := ih (by omega)
  have hreturn : ((inducedCombinatorialMap M S hflip).rot z).1 =
      (M.rot ^ k) z.1 := (firstReturn_spec M.rot S
        (finitePermutationReturn M.rot S) z).1
  have hlast : k - 1 + 1 = k := by have := hk.1; omega
  calc
    _ = A (faceClass M ((M.rot ^ (k - 1)) z.1)) := (hskip _ (by omega)).symm
    _ = A (faceClass M (M.edgeInv (M.rot ((M.rot ^ (k - 1)) z.1)))) :=
      (mirrorCloseFaceCorner M A _).symm
    _ = _ := by
      have hp : M.rot ((M.rot ^ (k - 1)) z.1) = (M.rot ^ k) z.1 := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hlast]
      rw [hreturn, hp]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Connected finite first-return restrictions of planar maps are planar. -/
private theorem mirrorClose_induced_isPlanar (M : CombinatorialMap D) (hM : M.IsPlanar)
    (S : Finset D) (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    [Nonempty S] (hN : (inducedCombinatorialMap M S hflip).IsConnected) :
    (inducedCombinatorialMap M S hflip).IsPlanar := by
  classical
  let N := inducedCombinatorialMap M S hflip
  refine ⟨hN, (eulerChar_eq_two_iff_range_faceBoundary_eq_cycleSpace N hN).2 ?_⟩
  apply le_antisymm (faceBoundary_range_le_cycleSpace N)
  intro c hc
  have hc' : vertexBoundary N c = 0 := hc
  obtain ⟨A, hA⟩ := planar_cycle_eq_faceBoundary M hM
    (mirrorCloseEdgeExtension M S hflip c)
    (mirrorCloseEdgeExtension_cycle M S hflip c hc')
  have hz (d : D) (hd : d ∉ S) :
      A (faceClass M d) = A (faceClass M (M.edgeInv d)) := by
    have h := congrFun hA (edgeClass M d)
    rw [faceBoundary_apply, mirrorCloseEdgeExtension_apply, dite_eq_right hd] at h
    have h' := congrArg (fun q => q + A (faceClass M (M.edgeInv d))) h
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using h'
  let f : S → ZMod 2 := fun d => A (faceClass M d.1)
  have hf (d : S) : f (N.faceSucc d) = f d := by
    have h := mirrorCloseFaceRot M S hflip A hz (N.faceSucc d)
    change A (faceClass M (N.faceSucc d).1) = A (faceClass M d.1)
    change A (faceClass M (N.faceSucc d).1) =
      A (faceClass M (M.edgeInv (N.rot (N.rot.symm (N.edgeInv d))).1)) at h
    simpa only [Equiv.apply_symm_apply, N, inducedCombinatorialMap,
      Equiv.Perm.subtypePerm_apply, M.edgeInv_invol] using h
  have hcycle (d e : S) (h : N.faceSucc.SameCycle d e) : f d = f e := by
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp (k : ℕ) : f ((N.faceSucc ^ k) d) = f d := by
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
    rw [← hn]
    exact (hp n).symm
  let B : FaceSpace N := Quotient.lift f hcycle
  refine ⟨B, ?_⟩
  apply funext
  intro q
  refine Quotient.inductionOn q ?_
  intro d
  have h := congrFun hA (edgeClass M d.1)
  rw [faceBoundary_apply, mirrorCloseEdgeExtension_apply, dite_eq_left d.2] at h
  change B (faceClass N d) + B (faceClass N (N.edgeInv d)) = c (edgeClass N d)
  exact h

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Reversing a periodic cyclic order reverses its first-return order. -/
private theorem mirrorClose_firstReturn_symm {α : Type} [DecidableEq α]
    (σ : Equiv.Perm α) (S : Finset α)
    (h : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hi : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ.symm ^ k) x.1 ∈ S) :
    cyclicFirstReturn σ.symm S hi = (cyclicFirstReturn σ S h).symm := by
  classical
  let R := cyclicFirstReturn σ S h
  have hleft (x : S) : cyclicFirstReturn σ.symm S hi (R x) = x := by
    let k := cyclicFirstReturnTime σ S h x
    let y := R x
    have hk := cyclicFirstReturnTime_spec σ S h x
    have hy : y.1 = (σ ^ k) x.1 := (firstReturn_spec σ S h x).1
    have hback (j : ℕ) (hj : j ≤ k) :
        (σ.symm ^ j) y.1 = (σ ^ (k - j)) x.1 := by
      apply (σ ^ j).injective
      calc
        (σ ^ j) ((σ.symm ^ j) y.1) = y.1 := by
          rw [show σ.symm = σ⁻¹ from rfl, inv_pow]
          exact (σ ^ j).apply_symm_apply _
        _ = (σ ^ k) x.1 := hy
        _ = (σ ^ j) ((σ ^ (k - j)) x.1) := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hj]
    have hb : (σ.symm ^ k) y.1 = x.1 := by
      simpa only [Nat.sub_self, pow_zero, Equiv.Perm.one_apply] using hback k le_rfl
    let l := cyclicFirstReturnTime σ.symm S hi y
    have hl := cyclicFirstReturnTime_spec σ.symm S hi y
    have hlk : l ≤ k := Nat.find_min' (hi y) ⟨hk.1, hb.symm ▸ x.2⟩
    have hkl : k ≤ l := by
      by_contra hbad
      have hlt : l < k := by omega
      have hret : (σ ^ (k - l)) x.1 ∈ S := (hback l hlk) ▸ hl.2.1
      exact hk.2.2 (k - l) (by omega) (by have := hl.1; omega) hret
    have heq : l = k := Nat.le_antisymm hlk hkl
    apply Subtype.ext
    rw [(firstReturn_spec σ.symm S hi y).1]
    change (σ.symm ^ l) y.1 = x.1
    rw [heq, hb]
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := R.surjective y
  exact (hleft x).trans (R.symm_apply_apply x).symm

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorClose_perm_symm_comm {A B : Type*} (e : A ≃ B)
    (p : Equiv.Perm A) (q : Equiv.Perm B)
    (h : ∀ x, e (p x) = q (e x)) (x : A) :
    e (p.symm x) = q.symm (e x) := by
  apply q.injective
  rw [← h, p.apply_symm_apply, q.apply_symm_apply]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorClose_connected_equiv {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (K : CombinatorialMap A) (L : CombinatorialMap B) (e : A ≃ B)
    (hrot : ∀ x, e (K.rot x) = L.rot (e x))
    (hedge : ∀ x, e (K.edgeInv x) = L.edgeInv (e x))
    (hconn : L.IsConnected) : K.IsConnected := by
  have hrotSymm := mirrorClose_perm_symm_comm e K.rot L.rot hrot
  have hedgeSymm := mirrorClose_perm_symm_comm e K.edgeInv L.edgeInv hedge
  have hstep {a b : B}
      (hab : b = L.rot a ∨ b = L.rot.symm a ∨
        b = L.edgeInv a ∨ b = L.edgeInv.symm a) :
      e.symm b = K.rot (e.symm a) ∨
        e.symm b = K.rot.symm (e.symm a) ∨
        e.symm b = K.edgeInv (e.symm a) ∨
        e.symm b = K.edgeInv.symm (e.symm a) := by
    rcases hab with h | h | h | h
    · left
      apply e.injective
      simpa only [e.apply_symm_apply, hrot] using h
    · right; left
      apply e.injective
      simpa only [e.apply_symm_apply, hrotSymm] using h
    · right; right; left
      apply e.injective
      simpa only [e.apply_symm_apply, hedge] using h
    · right; right; right
      apply e.injective
      simpa only [e.apply_symm_apply, hedgeSymm] using h
  intro x y
  have hxy := hconn (e x) (e y)
  have hmap : ∀ {a b : B},
      Relation.ReflTransGen
        (fun x y => y = L.rot x ∨ y = L.rot.symm x ∨
          y = L.edgeInv x ∨ y = L.edgeInv.symm x) a b →
      Relation.ReflTransGen
        (fun x y => y = K.rot x ∨ y = K.rot.symm x ∨
          y = K.edgeInv x ∨ y = K.edgeInv.symm x) (e.symm a) (e.symm b) := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hlast ih => exact ih.tail (hstep hlast)
  simpa only [e.symm_apply_apply] using hmap hxy

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Equality of finite combinatorial maps from their two permutations. -/
private theorem mirrorClose_map_eq {E : Type} [Fintype E] [DecidableEq E]
    (K L : CombinatorialMap E) (he : K.edgeInv = L.edgeInv) (hr : K.rot = L.rot) :
    K = L := by
  cases K
  cases L
  cases he
  cases hr
  rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Every positive-radius ball of the lower-carrier reflection is planar. -/
theorem rootedLocallyFiniteMirrorBallPlanarity_proved (M : RootedLocallyFinitePlanarMap) :
    RootedLocallyFiniteMirrorBallPlanarity M := by
  classical
  intro r hr
  let B := M.toRootedLocallyFiniteMap
  let A := mirrorRootedLocallyFiniteMap B
  let S := rootedLocallyFiniteBallDarts A r
  let T := rootedLocallyFiniteBallDarts B (r + 1)
  have hST : ∀ d, d ∈ S → d ∈ T := rootedMirrorBallDarts_shift B r
  let N := (rootedLocallyFiniteBallCombinatorialMap B (r + 1)).mirror
  let U := firstReturnSubset T S
  have hU : ∀ z, z ∈ U → N.edgeInv z ∈ U := by
    intro z hz
    have hz' : z.1 ∈ S := by simpa [U, firstReturnSubset] using hz
    have hf := rootedLocallyFiniteBallDarts_edgeInv_closed A r z.1 hz'
    simpa [U, firstReturnSubset, N, CombinatorialMap.mirror,
      rootedLocallyFiniteBallCombinatorialMap, Equiv.Perm.subtypePerm_apply] using hf
  let K := inducedCombinatorialMap N U hU
  let L := rootedLocallyFiniteBallCombinatorialMap A r
  let e : {z : T // z ∈ U} ≃ S := {
    toFun := fun z => ⟨z.1.1, by simpa [U, firstReturnSubset] using z.2⟩
    invFun := fun z => ⟨⟨z.1, hST z.1 z.2⟩, by simp [U, firstReturnSubset, z.2]⟩
    left_inv := by intro z; cases z with | mk z hz => cases z; rfl
    right_inv := by intro z; cases z; rfl }
  have hret (V : Finset A.D) : ∀ x : V,
      ∃ k : ℕ, 0 < k ∧ (A.rot ^ k) x.1 ∈ V := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn A x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hretB : ∀ x : T, ∃ k : ℕ, 0 < k ∧ (B.rot ^ k) x.1 ∈ T := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn B x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hNT : N.rot = cyclicFirstReturn A.rot T (hret T) := by
    exact (mirrorClose_firstReturn_symm B.rot T hretB (hret T)).symm
  have hrot (z : {z : T // z ∈ U}) : e (K.rot z) = L.rot (e z) := by
    apply Subtype.ext
    change ((cyclicFirstReturn N.rot U (finitePermutationReturn N.rot U) z).1).1 = _
    rw [hNT]
    exact firstReturn_nested' A.rot T S (hret T) hST
      (finitePermutationReturn (cyclicFirstReturn A.rot T (hret T)) U) (hret S) (e z)
  have hedge (z : {z : T // z ∈ U}) : e (K.edgeInv z) = L.edgeInv (e z) := by
    apply Subtype.ext
    rfl
  have hK : K.IsConnected := mirrorClose_connected_equiv K L e hrot hedge
    (rootedLocallyFiniteBallCombinatorialMap_connected A r hr)
  let : Nonempty U := ⟨e.symm
    ⟨A.rootDart, (rootedLocallyFiniteBallDarts_frame_mem A hr).1⟩⟩
  have hN : N.IsPlanar := (CombinatorialMap.isPlanar_mirror_iff _).2
    (M.ball_isPlanar (r + 1) (by omega))
  have hplanar : (K.transport e).IsPlanar :=
    CombinatorialMap.transport_isPlanar e K (mirrorClose_induced_isPlanar N hN U hU hK)
  have heq : K.transport e = L := by
    apply mirrorClose_map_eq
    · apply Equiv.ext
      intro d
      change e (K.edgeInv (e.symm d)) = L.edgeInv d
      rw [hedge, e.apply_symm_apply]
    · apply Equiv.ext
      intro d
      change e (K.rot (e.symm d)) = L.rot d
      rw [hrot, e.apply_symm_apply]
  change L.IsPlanar
  rw [← heq]
  exact hplanar

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Every finite set of darts is captured by a sufficiently large geometric ball. -/
private theorem mirrorClose_capture_finite (M : RootedLocallyFiniteMap) (r : ℕ)
    (S : Finset M.D) :
    ∃ R, r ≤ R ∧ ∀ d ∈ S, d ∈ rootedLocallyFiniteBallDarts M R := by
  obtain ⟨R, hrR, hR⟩ := d39BallDarts_capture_finite M.toD39RootedMap r S
  refine ⟨R, hrR, ?_⟩
  intro d hd
  rw [← d39BallDarts_toD39RootedMap]
  exact hR d hd

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Retained face steps survive in the finite ball. -/
private theorem mirrorClose_faceSucc_of_mem (M : RootedLocallyFiniteMap) (r : ℕ)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}]
    (d : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r})
    (hface : M.rot.symm (M.edgeInv d.1) ∈ rootedLocallyFiniteBallDarts M r) :
    ((rootedLocallyFiniteBallCombinatorialMap M r).faceSucc d).1 = M.rot.symm (M.edgeInv d.1) := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let N := rootedLocallyFiniteBallCombinatorialMap M r
  let y : S := ⟨M.rot.symm (M.edgeInv d.1), hface⟩
  have hret : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hnext : M.rot y.1 = M.edgeInv d.1 := M.rot.apply_symm_apply _
  have hy : M.rot y.1 ∈ S := hnext.symm ▸
    rootedLocallyFiniteBallDarts_edgeInv_closed M r d.1 d.2
  have hrot : N.rot y = N.edgeInv d := by
    apply Subtype.ext
    have hone : (cyclicFirstReturn M.rot S hret y).1 = M.rot y.1 := by
      have htime : cyclicFirstReturnTime M.rot S hret y = 1 := by
        apply le_antisymm
        · exact Nat.find_min' (hret y) ⟨Nat.one_pos, by simpa using hy⟩
        · exact (cyclicFirstReturnTime_spec M.rot S hret y).1
      rw [(firstReturn_spec M.rot S hret y).1, htime, pow_one]
    exact hone.trans hnext
  change (N.rot.symm (N.edgeInv d)).1 = _
  rw [← hrot, Equiv.symm_apply_apply]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A finite forward ambient face path survives in one sufficiently large ball. -/
private theorem mirrorClose_capture_face_path (M : RootedLocallyFiniteMap) (r : ℕ)
    (x : M.D) (n : ℕ) :
    ∃ R, r ≤ R ∧ ∃ hx : x ∈ rootedLocallyFiniteBallDarts M R,
      ∃ hy : ((M.rot.symm * M.edgeInv) ^ n) x ∈ rootedLocallyFiniteBallDarts M R,
        letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
          Classical.decEq _
        (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle ⟨x, hx⟩
          ⟨((M.rot.symm * M.edgeInv) ^ n) x, hy⟩ := by
  classical
  let f : Equiv.Perm M.D := M.rot.symm * M.edgeInv
  let S := (Finset.range (n + 1)).image fun i => (f ^ i) x
  obtain ⟨R, hrR, hR⟩ := mirrorClose_capture_finite M r S
  let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
    Classical.decEq _
  have hmem (i : ℕ) (hi : i ≤ n) : (f ^ i) x ∈ rootedLocallyFiniteBallDarts M R := by
    apply hR
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hx : x ∈ rootedLocallyFiniteBallDarts M R := by
    simpa using hmem 0 (Nat.zero_le n)
  refine ⟨R, hrR, hx, hmem n le_rfl, ?_⟩
  let B := rootedLocallyFiniteBallCombinatorialMap M R
  let z : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} := ⟨x, hx⟩
  have hpow : ∀ i, i ≤ n → ((B.faceSucc ^ i) z).1 = (f ^ i) x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
        intro hi
        have hv := ih (by omega)
        have hnxt : M.rot.symm (M.edgeInv ((B.faceSucc ^ i) z).1) ∈
            rootedLocallyFiniteBallDarts M R := by
          rw [hv]
          simpa only [f, pow_succ', Equiv.Perm.mul_apply] using hmem (i + 1) hi
        rw [pow_succ', Equiv.Perm.mul_apply]
        rw [mirrorClose_faceSucc_of_mem M R _ hnxt, hv]
        rw [pow_succ', Equiv.Perm.mul_apply]
        rfl
  refine ⟨(n : ℤ), ?_⟩
  apply Subtype.ext
  exact hpow n le_rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Two darts on one ambient face are captured on one finite ball face. -/
private theorem mirrorClose_capture_sameCycle (M : RootedLocallyFiniteMap) (r : ℕ)
    (x y : M.D) (h : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) x y) :
    ∃ R, r ≤ R ∧ ∃ hx : x ∈ rootedLocallyFiniteBallDarts M R,
      ∃ hy : y ∈ rootedLocallyFiniteBallDarts M R,
        letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
          Classical.decEq _
        (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  let f : Equiv.Perm M.D := M.rot.symm * M.edgeInv
  rcases h with ⟨i, hi⟩
  cases i with
  | ofNat n =>
      have heq : (f ^ n) x = y := by simpa using hi
      obtain ⟨R, hrR, hx, hn, hcycle⟩ := mirrorClose_capture_face_path M r x n
      let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
        Classical.decEq _
      refine ⟨R, hrR, hx, heq ▸ hn, ?_⟩
      change (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle
        ⟨x, hx⟩ ⟨(f ^ n) x, hn⟩ at hcycle
      simpa only [heq] using hcycle
  | negSucc n =>
      have heq : (f ^ (n + 1)) y = x := by
        rw [← hi, zpow_negSucc]
        exact (f ^ (n + 1)).apply_symm_apply _
      obtain ⟨R, hrR, hy, hn, hcycle⟩ := mirrorClose_capture_face_path M r y (n + 1)
      let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
        Classical.decEq _
      refine ⟨R, hrR, heq ▸ hn, hy, ?_⟩
      have hcycle' := hcycle.symm
      change (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle
        ⟨(f ^ (n + 1)) y, hn⟩ ⟨y, hy⟩ at hcycle'
      simpa only [heq] using hcycle'

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The reflected outer face is captured together with its selected frame incidence. -/
theorem rootedLocallyFiniteMirrorOuterCapture_proved (M : RootedLocallyFinitePlanarMap) :
    RootedLocallyFiniteMirrorOuterCapture M := by
  intro r _ d _ hd
  let A := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
  have hf := rootedLocallyFiniteOuterFrameDart_outer A
  obtain ⟨R, hrR, hfR, hdR, hcycle⟩ := mirrorClose_capture_sameCycle A r
    (rootedLocallyFiniteOuterFrameDart A) d (hf.symm.trans hd)
  exact ⟨R, hrR, hdR, hfR, hcycle⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The reflection on the planar carrier, with both geometric fields proved. -/
@[expose] def mirrorRootedLocallyFinitePlanarMap (M : RootedLocallyFinitePlanarMap) :
    RootedLocallyFinitePlanarMap where
  toRootedLocallyFiniteMap := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
  ball_isPlanar := rootedLocallyFiniteMirrorBallPlanarity_proved M
  outerFace_captured_in_larger_ball := rootedLocallyFiniteMirrorOuterCapture_proved M

end DirectedDistances.PlanarMap
