module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorClose
public import DirectedDistances.PlanarMap.FacedBallMirror
import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem

public section
namespace DirectedDistances.PlanarMap

open Equiv CombinatorialMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory TopologicalSpace

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Move the finite frame to its other endpoint before reflection, retaining all face data. -/
@[expose] def reverseFacedBallFrame (B : FacedFramedBall) : FacedFramedBall where
  toFramedBall := {
    D := B.toFramedBall.D
    map := B.toFramedBall.map
    rootDart := B.toFramedBall.map.edgeInv B.toFramedBall.frameEdgeDart
    frameEdgeDart := B.toFramedBall.map.edgeInv B.toFramedBall.frameEdgeDart
    frameEdge_missing := (B.toFramedBall.map.missing_edgeInv _).1
      B.toFramedBall.frameEdge_missing
    frameEdge_at_root := Equiv.Perm.SameCycle.rfl
    frameOtherDart := B.toFramedBall.frameOtherDart.map (fun _ => B.toFramedBall.frameEdgeDart)
    frameOtherDart_valid := by
      intro y hy
      cases ho : B.toFramedBall.frameOtherDart with
      | none => simp only [ho, Option.map_none, reduceCtorEq] at hy
      | some d =>
        have he : B.toFramedBall.frameEdgeDart = y := by
          simpa only [ho, Option.map_some, Option.some.injEq] using hy
        rw [B.toFramedBall.map.edgeInv_invol, ← he] }
  original := B.original
  original_closed := B.original_closed

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Reversing the ordered frame transports every faced isomorphism. -/
@[expose] def FacedFramedBallIso.reverseFrame {B C : FacedFramedBall}
    (I : FacedFramedBallIso B C) :
    FacedFramedBallIso (reverseFacedBallFrame B) (reverseFacedBallFrame C) := by
  let J := I.toFramedBallIso
  have hnone : B.toFramedBall.frameOtherDart = none ↔
      C.toFramedBall.frameOtherDart = none := by
    cases hb : B.toFramedBall.frameOtherDart <;>
      cases hc : C.toFramedBall.frameOtherDart
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · rcases J.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
      · simp only [hc, reduceCtorEq] at h
        exact h.2.elim
      · simp only [hb, Option.map_none, reduceCtorEq] at hx
    · rcases J.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
      · simp only [hb, Option.map_some, reduceCtorEq] at h
        exact h.1.elim
      · simp only [hc, reduceCtorEq] at hy
    · simp only [reduceCtorEq]
  refine {
    toFramedBallIso := {
      mapIso := J.mapIso
      root_vertex := ?_
      frameEdge_comm := ?_
      frameOther_comm := ?_ }
    original_iff := I.original_iff }
  · change C.toFramedBall.map.rot.SameCycle
      (J.mapIso.toEquiv (B.toFramedBall.map.edgeInv B.toFramedBall.frameEdgeDart))
      (C.toFramedBall.map.edgeInv C.toFramedBall.frameEdgeDart)
    rw [J.mapIso.edgeInv_comm, J.frameEdge_comm]
  · exact (J.mapIso.edgeInv_comm _).trans
      (congrArg C.toFramedBall.map.edgeInv J.frameEdge_comm)
  · cases hb : B.toFramedBall.frameOtherDart with
    | none =>
      have hc := hnone.mp hb
      left
      simp only [reverseFacedBallFrame, hb, hc, Option.map_none, and_self]
    | some d =>
      cases hc : C.toFramedBall.frameOtherDart with
      | none =>
        have hf := hnone.mpr hc
        simp only [hb, reduceCtorEq] at hf
      | some e =>
        right
        refine ⟨J.mapIso.toEquiv B.toFramedBall.frameEdgeDart,
          C.toFramedBall.frameEdgeDart, ?_, ?_, ?_⟩
        · simp only [reverseFacedBallFrame, hb, Option.map_some]
          rfl
        · simp only [reverseFacedBallFrame, hc, Option.map_some]
        · rw [J.frameEdge_comm]
          exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The reflected finite enclosing ball with the ordered frame at its new endpoint. -/
@[expose] noncomputable def mirrorContinuityEnclosingBall
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s) : FacedFramedBall :=
  mirrorFacedFramedBall (reverseFacedBallFrame (rootedLocallyFiniteFacedBall M s hs))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The enclosing reflected and rerooted balls inherit the supplied faced isomorphism. -/
@[expose] noncomputable def mirrorContinuityEnclosingIso
    (M N : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M s hs)
      (rootedLocallyFiniteFacedBall N s hs)) :
    FacedFramedBallIso (mirrorContinuityEnclosingBall M s hs)
      (mirrorContinuityEnclosingBall N s hs) := I.reverseFrame.mirror

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Vertices of the finite reflected enclosing ball map to ambient reflected vertices. -/
private noncomputable def mirrorContinuityVertexMap
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s) :
    VertexQuotient (mirrorContinuityEnclosingBall M s hs).toFramedBall.map.toCombinatorialMap →
      RootedLocallyFiniteVertex M.D M.rot.symm := by
  classical
  exact Quotient.map Subtype.val (fun x y h => Equiv.Perm.sameCycle_inv.mpr
    ((rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap s x y).1
      (Equiv.Perm.sameCycle_inv.mp h)))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Ambient reachability is monotone in the radius. -/
private theorem mirrorContinuityRadiusMono (A : RootedLocallyFiniteMap) {r s : ℕ}
    (hrs : r ≤ s) {v} (h : rootedLocallyFiniteWithinRadius A r v) :
    rootedLocallyFiniteWithinRadius A s v :=
  (mem_rootedLocallyFiniteRadiusVertices A s v).1
    (rootedLocallyFiniteRadiusVertices_mono A hrs
      ((mem_rootedLocallyFiniteRadiusVertices A r v).2 h))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A finite reflected path gives an ambient reflected path of the same length. -/
private theorem mirrorContinuityPathToAmbient
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s) {v w n}
    (h : framedBallGeometricPath (mirrorContinuityEnclosingBall M s hs).toFramedBall
      v n w) :
    rootedLocallyFiniteWithinRadius (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap)
      0 (mirrorContinuityVertexMap M s hs v) →
    rootedLocallyFiniteWithinRadius (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap)
      n (mirrorContinuityVertexMap M s hs w) := by
  intro hv
  induction h with
  | nil => exact hv
  | snoc hp he ih =>
    obtain ⟨d, hd, hd'⟩ := he
    exact .edge ih ⟨d.1, congrArg (mirrorContinuityVertexMap M s hs) hd,
      congrArg (mirrorContinuityVertexMap M s hs) hd'⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Every ambient reflected path of length n fits in the original radius n+1 ball. -/
private theorem mirrorContinuityAmbientToBall
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s) {n v}
    (h : rootedLocallyFiniteWithinRadius
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) n v)
    (hn : n + 1 ≤ s)
    (d : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D)
    (hd : rootedLocallyFiniteVertexClassOf
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) d.1 = v) :
    framedBallWithinRadius (mirrorContinuityEnclosingBall M s hs).toFramedBall n
      (vertexClass _ (mirrorContinuityEnclosingBall M s hs).toFramedBall.rootDart)
      (vertexClass _ d) := by
  classical
  let A := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
  let B := (mirrorContinuityEnclosingBall M s hs).toFramedBall
  have hcycle (x y : B.D) : B.map.rot.SameCycle x y ↔ A.rot.SameCycle x.1 y.1 :=
    Equiv.Perm.sameCycle_inv.trans
      ((rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap s x y).trans
        Equiv.Perm.sameCycle_inv.symm)
  induction h generalizing d with
  | root =>
    have hc : B.map.rot.SameCycle B.rootDart d :=
      (hcycle _ _).2 (Quotient.exact hd).symm
    have heq : vertexClass B.map.toCombinatorialMap B.rootDart =
        vertexClass B.map.toCombinatorialMap d := Quotient.sound hc
    exact ⟨0, Nat.le_refl _, heq ▸ framedBallGeometricPath.nil _⟩
  | @stay n v hp ih =>
    obtain ⟨k, hk, hpath⟩ := ih (by omega) d hd
    exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hpath⟩
  | @edge n v w hp he ih =>
    obtain ⟨e, hev, hew⟩ := he
    have hp' : rootedLocallyFiniteWithinRadius A n
        (rootedLocallyFiniteVertexClassOf A e) := by
      change rootedLocallyFiniteVertexClassOf A e = v at hev
      rw [hev]
      exact hp
    have heA : e ∈ rootedLocallyFiniteBallDarts A (n + 1) := by
      rw [mem_rootedLocallyFiniteBallDarts]
      exact ⟨(mem_rootedLocallyFiniteRadiusVertices A _ _).2
        (.stay hp'),
        (mem_rootedLocallyFiniteRadiusVertices A _ _).2
          (.edge hp ⟨e, hev, rfl⟩)⟩
    have heS : e ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap s :=
      rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hn
        (rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (n + 1) e heA)
    let e' : B.D := ⟨e, heS⟩
    obtain ⟨k, hk, hpath⟩ := ih (by omega) e' hev
    have hc : B.map.rot.SameCycle (B.map.edgeInv e') d :=
      (hcycle _ _).2 (Quotient.exact (hew.trans hd.symm))
    exact ⟨k + 1, Nat.succ_le_succ hk,
      .snoc hpath ⟨e', rfl, Quotient.sound hc⟩⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The rerooted enclosing reflected ball measures ambient reflected distance exactly
while n+1 does not exceed its original enclosing radius. -/
theorem mirrorContinuityEnclosingBall_withinRadius_iff
    (M : RootedLocallyFinitePlanarMap) {n s : ℕ} (hs : 0 < s) (hn : n + 1 ≤ s)
    (d : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D) :
    framedBallWithinRadius (mirrorContinuityEnclosingBall M s hs).toFramedBall n
      (vertexClass _ (mirrorContinuityEnclosingBall M s hs).toFramedBall.rootDart)
      (vertexClass _ d) ↔
    rootedLocallyFiniteWithinRadius
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) n
      (rootedLocallyFiniteVertexClassOf
        (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) d.1) := by
  constructor
  · rintro ⟨k, hk, hp⟩
    exact mirrorContinuityRadiusMono _ hk
      (mirrorContinuityPathToAmbient M s hs hp .root)
  · intro h
    exact mirrorContinuityAmbientToBall M s hs h hn d rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Intrinsic rerooted radius darts are exactly the ambient reflected radius darts. -/
theorem mirrorContinuityEnclosingBall_radius_mem_iff
    (M : RootedLocallyFinitePlanarMap) {n s : ℕ} (hs : 0 < s) (hn : n + 1 ≤ s)
    (d : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D) :
    d ∈ framedBallRadiusDarts (mirrorContinuityEnclosingBall M s hs).toFramedBall n ↔
      d.1 ∈ rootedLocallyFiniteBallDarts
        (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) n := by
  rw [framedBallRadiusDarts_mem_iff, mem_rootedLocallyFiniteBallDarts]
  exact (and_congr (mirrorContinuityEnclosingBall_withinRadius_iff M hs hn d)
    (mirrorContinuityEnclosingBall_withinRadius_iff M hs hn
      ((mirrorContinuityEnclosingBall M s hs).toFramedBall.map.edgeInv d))).trans
    (and_congr (mem_rootedLocallyFiniteRadiusVertices _ _ _).symm
      (mem_rootedLocallyFiniteRadiusVertices _ _ _).symm)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Reversing a periodic cyclic order reverses its first-return order. -/
private theorem mirrorContinuityFirstReturnSymm {α : Type} [DecidableEq α]
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


/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The intrinsic smaller dart set inside the reflected enclosing ball. -/
@[expose] noncomputable def mirrorContinuityRestrictionDarts
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    Finset (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall.D :=
  framedBallRadiusDarts (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r +
    1))).toFramedBall
    (r + 1)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The intrinsic smaller dart set is closed under the edge involution. -/
theorem mirrorContinuityRestrictionDarts_edgeInv
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    ∀ d, d ∈ mirrorContinuityRestrictionDarts M r →
      (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r +
        1))).toFramedBall.map.edgeInv d ∈
        mirrorContinuityRestrictionDarts M r :=
  fun _ hd => framedBallRadiusDarts_edgeInv_mem _ _ hd

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The finite first-return map on the intrinsic rerooted radius darts. -/
@[expose] noncomputable def mirrorContinuityRestrictionMap
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    CombinatorialMap {d // d ∈ mirrorContinuityRestrictionDarts M r} :=
  inducedCombinatorialMap
    (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r +
      1))).toFramedBall.map.toCombinatorialMap
    (mirrorContinuityRestrictionDarts M r) (mirrorContinuityRestrictionDarts_edgeInv M r)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Flattening identifies the intrinsic restricted darts with the actual mirrored ball darts. -/
@[expose] noncomputable def mirrorContinuityFlatten
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    {d // d ∈ mirrorContinuityRestrictionDarts M r} ≃
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D where
  toFun := fun d => ⟨d.1.1,
    (mirrorContinuityEnclosingBall_radius_mem_iff M (by omega) (by omega) d.1).1 d.2⟩
  invFun := fun d => ⟨⟨d.1,
    rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (r + 1) d.1 d.2⟩,
    (mirrorContinuityEnclosingBall_radius_mem_iff M (by omega) (by omega) _).2 d.2⟩
  left_inv := by intro d; rfl
  right_inv := by intro d; rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Flattening commutes with the actual reflected first-return rotation. -/
theorem mirrorContinuityFlatten_rot (M : RootedLocallyFinitePlanarMap) (r : ℕ)
    (d : {d // d ∈ mirrorContinuityRestrictionDarts M r}) :
    mirrorContinuityFlatten M r ((mirrorContinuityRestrictionMap M r).rot d) =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.rot (mirrorContinuityFlatten M r d) := by
  classical
  let A := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
  let T := rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap (r + 2)
  let S := rootedLocallyFiniteBallDarts A (r + 1)
  let B := (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall
  have hret (V : Finset A.D) : ∀ x : V,
      ∃ k : ℕ, 0 < k ∧ (A.rot ^ k) x.1 ∈ V := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn A x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hretM : ∀ x : T,
      ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ T := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn M.toRootedLocallyFiniteMap x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hBT : B.map.rot = cyclicFirstReturn A.rot T (hret T) :=
    (mirrorContinuityFirstReturnSymm M.rot T hretM (hret T)).symm
  have hU : mirrorContinuityRestrictionDarts M r = firstReturnSubset T S := by
    ext z
    change T at z
    exact (mirrorContinuityEnclosingBall_radius_mem_iff M (by omega) (by omega) z).trans
      (by
        change z.1 ∈ S ↔ z ∈ (Finset.univ : Finset T).filter (fun x => x.1 ∈ S)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  apply Subtype.ext
  change ((cyclicFirstReturn B.map.rot (mirrorContinuityRestrictionDarts M r)
    (finitePermutationReturn B.map.rot _) d).1).1 = _
  rw [hBT]
  have h := firstReturn_nested' A.rot T S (hret T)
    (rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (r + 1))
    (finitePermutationReturn (cyclicFirstReturn A.rot T (hret T)) (firstReturnSubset T S))
    (hret S) (mirrorContinuityFlatten M r d)
  change _ = (cyclicFirstReturn A.rot S (hret S) (mirrorContinuityFlatten M r d)).1
  have hcongr (U V : Finset T) (hUV : U = V) (z : U) :
      ((cyclicFirstReturn (cyclicFirstReturn A.rot T (hret T)) U
        (finitePermutationReturn _ U) z).1).1 =
      ((cyclicFirstReturn (cyclicFirstReturn A.rot T (hret T)) V
        (finitePermutationReturn _ V) ⟨z.1, hUV ▸ z.2⟩).1).1 := by
    subst V
    rfl
  exact (hcongr _ _ hU d).trans h

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Flattening preserves edge identity and reversal exactly. -/
theorem mirrorContinuityFlatten_edgeInv (M : RootedLocallyFinitePlanarMap) (r : ℕ)
    (d : {d // d ∈ mirrorContinuityRestrictionDarts M r}) :
    mirrorContinuityFlatten M r ((mirrorContinuityRestrictionMap M r).edgeInv d) =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.edgeInv (mirrorContinuityFlatten M r d) := by
  apply Subtype.ext
  rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The enclosing faced isomorphism restricts to a bijection of the rerooted radius darts. -/
@[expose] noncomputable def mirrorContinuityRestrictedEquiv
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1)))) :
    {d // d ∈ mirrorContinuityRestrictionDarts M r} ≃
      {d // d ∈ mirrorContinuityRestrictionDarts N r} :=
  (mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1))
    I).toFramedBallIso.mapIso.toEquiv.subtypeEquiv (fun d => (framedBallRadiusDarts_mem_iso_iff
      (mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1)) I).toFramedBallIso
      (r + 1) d).symm)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The restricted bijection commutes with first-return rotation. -/
theorem mirrorContinuityRestrictedEquiv_rot
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : {d // d ∈ mirrorContinuityRestrictionDarts M r}) :
    mirrorContinuityRestrictedEquiv M N r I ((mirrorContinuityRestrictionMap M r).rot d) =
      (mirrorContinuityRestrictionMap N r).rot (mirrorContinuityRestrictedEquiv M N r I d) := by
  apply Subtype.ext
  let J := (mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1)) I).toFramedBallIso
  exact DirectedDistances.PaperProofs.Section3.cyclicFirstReturn_map_of_equiv
    _ _ _ _ J.mapIso.toEquiv
    (fun e => (framedBallRadiusDarts_mem_iso_iff J (r + 1) e).symm)
    J.mapIso.rot_comm (finitePermutationReturn _ _) (finitePermutationReturn _ _) d

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The restricted bijection commutes with edge reversal. -/
theorem mirrorContinuityRestrictedEquiv_edgeInv
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : {d // d ∈ mirrorContinuityRestrictionDarts M r}) :
    mirrorContinuityRestrictedEquiv M N r I
        ((mirrorContinuityRestrictionMap M r).edgeInv d) =
      (mirrorContinuityRestrictionMap N r).edgeInv (mirrorContinuityRestrictedEquiv M N r I d) := by
  apply Subtype.ext
  exact (mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1))
    I).toFramedBallIso.mapIso.edgeInv_comm d.1

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The canonical dart transport between the actual smaller reflected balls. -/
@[expose] noncomputable def mirrorContinuityDartTransport
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1)))) :
    (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D ≃
    (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D :=
  (mirrorContinuityFlatten M r).symm.trans
    ((mirrorContinuityRestrictedEquiv M N r I).trans (mirrorContinuityFlatten N r))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The actual smaller dart transport preserves cyclic order. -/
theorem mirrorContinuityDartTransport_rot
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D) :
    mirrorContinuityDartTransport M N r I
        ((rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
          (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.rot d) =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.rot (mirrorContinuityDartTransport M N r I
          d) := by
  let x := (mirrorContinuityFlatten M r).symm d
  have hx : d = mirrorContinuityFlatten M r x := (Equiv.apply_symm_apply _ d).symm
  rw [hx, ← mirrorContinuityFlatten_rot]
  change mirrorContinuityFlatten N r
      (mirrorContinuityRestrictedEquiv M N r I ((mirrorContinuityRestrictionMap M r).rot x)) = _
  rw [mirrorContinuityRestrictedEquiv_rot, mirrorContinuityFlatten_rot]
  rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The actual smaller dart transport preserves edge reversal. -/
theorem mirrorContinuityDartTransport_edgeInv
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D) :
    mirrorContinuityDartTransport M N r I
        ((rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
          (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.edgeInv d) =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.edgeInv
          (mirrorContinuityDartTransport M N r I d) := by
  let x := (mirrorContinuityFlatten M r).symm d
  have hx : d = mirrorContinuityFlatten M r x := (Equiv.apply_symm_apply _ d).symm
  rw [hx, ← mirrorContinuityFlatten_edgeInv]
  change mirrorContinuityFlatten N r
      (mirrorContinuityRestrictedEquiv M N r I
        ((mirrorContinuityRestrictionMap M r).edgeInv x)) = _
  rw [mirrorContinuityRestrictedEquiv_edgeInv, mirrorContinuityFlatten_edgeInv]
  rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Reversing rotation conjugates inverse face cycles by the edge involution. -/
private theorem mirrorContinuityFaceCycle {D : Type} (p e : Equiv.Perm D)
    (he : ∀ d, e (e d) = d) (a b : D) :
    Equiv.Perm.SameCycle (p * e) a b ↔
      Equiv.Perm.SameCycle (p.symm * e) (e a) (e b) := by
  have hi : e⁻¹ = e := by
    ext d
    apply e.injective
    change e (e.symm d) = e (e d)
    rw [e.apply_symm_apply, he]
  have hf : p * e = e * (p.symm * e)⁻¹ * e⁻¹ := by
    rw [mul_inv_rev, hi, Equiv.Perm.inv_def, Equiv.symm_symm]
    have hh : e * e = 1 := by ext d; exact he d
    rw [← mul_assoc, hh, one_mul]
  rw [hf, Equiv.Perm.sameCycle_conj, hi]
  exact Equiv.Perm.sameCycle_inv

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The enclosing face selection is exactly ambient reflected face containment in -/
private theorem mirrorContinuityOriginal_iff
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s)
    (d : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D) :
    d ∈ (mirrorContinuityEnclosingBall M s hs).original ↔
      ∀ e, Equiv.Perm.SameCycle (M.rot * M.edgeInv) d.1 e →
        e ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap s := by
  change rootedLocallyFiniteBallContainsOriginalFace M.toRootedLocallyFiniteMap s
    (M.edgeInv d.1) ↔ _
  constructor
  · intro h e he
    have hm := h (M.edgeInv e)
      ((mirrorContinuityFaceCycle M.rot M.edgeInv M.edgeInv_invol d.1 e).1 he)
    have hf := rootedLocallyFiniteBallDarts_edgeInv_closed M.toRootedLocallyFiniteMap s
      (M.edgeInv e) hm
    simpa only [M.edgeInv_invol] using hf
  · intro h e he
    have hc : (M.rot * M.edgeInv).SameCycle d.1 (M.edgeInv e) :=
      (mirrorContinuityFaceCycle M.rot M.edgeInv M.edgeInv_invol d.1 (M.edgeInv e)).2
        (by simpa only [M.edgeInv_invol] using he)
    have hf := rootedLocallyFiniteBallDarts_edgeInv_closed M.toRootedLocallyFiniteMap s
      (M.edgeInv e) (h _ hc)
    simpa only [M.edgeInv_invol] using hf

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A selected enclosing reflected face has exactly its ambient reflected cycle. -/
private theorem mirrorContinuityOriginal_cycle
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s)
    (d e : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D)
    (hd : d ∈ (mirrorContinuityEnclosingBall M s hs).original) :
    (mirrorContinuityEnclosingBall M s hs).toFramedBall.map.faceSucc.SameCycle d e ↔
      (M.rot * M.edgeInv).SameCycle d.1 e.1 := by
  let B := (rootedLocallyFiniteFacedBall M s hs).toFramedBall
  change (B.map.rot * B.map.edgeInv).SameCycle d e ↔ _
  exact (mirrorContinuityFaceCycle B.map.rot B.map.edgeInv B.map.edgeInv_invol d e).trans
    ((rootedLocallyFiniteFacedBall_original_cycle M s hs
      (B.map.edgeInv d) (B.map.edgeInv e) hd).trans
      (mirrorContinuityFaceCycle M.rot M.edgeInv M.edgeInv_invol d.1 e.1).symm)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Original faces of the actual smaller mirror are selected enclosing faces whose
entire enclosing cycle stays in the intrinsic smaller radius. -/
private theorem mirrorContinuityOriginal_radius_iff
    (M : RootedLocallyFinitePlanarMap) (r : ℕ)
    (d : (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall.D) :
    rootedLocallyFiniteBallContainsOriginalFace
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) (r + 1) d.1 ↔
      d ∈ (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).original ∧
        ∀ e, (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r +
          1))).toFramedBall.map.faceSucc.SameCycle d e → e ∈ mirrorContinuityRestrictionDarts M r
          := by
  constructor
  · intro h
    have hd : d ∈ (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).original :=
      (mirrorContinuityOriginal_iff M _ _ d).2 (fun e he =>
        rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (r + 1) e (h e he))
    refine ⟨hd, fun e he => ?_⟩
    exact (mirrorContinuityEnclosingBall_radius_mem_iff M (by omega) (by omega) e).2
      (h e.1 ((mirrorContinuityOriginal_cycle M _ _ d e hd).1 he))
  · rintro ⟨hd, hall⟩ e he
    let e' : (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall.D :=
      ⟨e, (mirrorContinuityOriginal_iff M _ _ d).1 hd e he⟩
    exact (mirrorContinuityEnclosingBall_radius_mem_iff M (by omega) (by omega) e').1
      (hall e' ((mirrorContinuityOriginal_cycle M _ _ d e' hd).2 he))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A finite framed isomorphism commutes with face successors. -/
private theorem mirrorContinuityIso_face {B C : FramedBall} (J : FramedBallIso B C)
    (d : B.D) : J.mapIso.toEquiv (B.map.faceSucc d) = C.map.faceSucc (J.mapIso.toEquiv d) := by
  change J.mapIso.toEquiv (B.map.rot.symm (B.map.edgeInv d)) =
    C.map.rot.symm (C.map.edgeInv (J.mapIso.toEquiv d))
  apply C.map.rot.injective
  rw [← J.mapIso.rot_comm, B.map.rot.apply_symm_apply, C.map.rot.apply_symm_apply,
    J.mapIso.edgeInv_comm]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The canonical smaller reflected dart transport preserves original-face selection. -/
theorem mirrorContinuityDartTransport_original
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D) :
    mirrorContinuityDartTransport M N r I d ∈
        (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
          (r + 1) (Nat.zero_lt_succ r)).original ↔
      d ∈ (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r)).original := by
  let J := mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1)) I
  let x := (mirrorContinuityFlatten M r).symm d
  change rootedLocallyFiniteBallContainsOriginalFace
      (mirrorRootedLocallyFiniteMap N.toRootedLocallyFiniteMap) (r + 1)
      (J.toFramedBallIso.mapIso.toEquiv x.1).1 ↔
    rootedLocallyFiniteBallContainsOriginalFace
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap) (r + 1) x.1.1
  rw [mirrorContinuityOriginal_radius_iff, mirrorContinuityOriginal_radius_iff]
  have hcycle := framedBall_sameCycle_iff_of_equiv J.toFramedBallIso.mapIso.toEquiv
    _ _ (mirrorContinuityIso_face J.toFramedBallIso)
  have hmem (e) : J.toFramedBallIso.mapIso.toEquiv e ∈
      mirrorContinuityRestrictionDarts N r ↔ e ∈ mirrorContinuityRestrictionDarts M r :=
    framedBallRadiusDarts_mem_iso_iff J.toFramedBallIso (r + 1) e
  constructor
  · rintro ⟨ho, hall⟩
    exact ⟨(J.original_iff _).1 ho, fun e he =>
      (hmem e).1 (hall _ ((hcycle _ _).1 he))⟩
  · rintro ⟨ho, hall⟩
    refine ⟨(J.original_iff _).2 ho, ?_⟩
    intro e he
    obtain ⟨e, rfl⟩ := J.toFramedBallIso.mapIso.toEquiv.surjective e
    exact (hmem e).2 (hall e ((hcycle _ _).2 he))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The canonical dart transport preserves the reversed ordered frame incidence. -/
theorem mirrorContinuityDartTransport_frameEdge
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1)))) :
    mirrorContinuityDartTransport M N r I
        (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
          (r + 1) (Nat.zero_lt_succ r)).toFramedBall.frameEdgeDart =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.frameEdgeDart := by
  apply Subtype.ext
  have he := I.toFramedBallIso.mapIso.edgeInv_comm
    (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall.frameEdgeDart
  rw [I.toFramedBallIso.frameEdge_comm] at he
  exact congrArg (fun z : (rootedLocallyFiniteFacedBall N (r + 2)
    (Nat.zero_lt_succ (r + 1))).toFramedBall.D => z.1) he

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Outer-face transport for the constructed dart bijection; proved below. Source: -/
@[expose] def RootedLocallyFiniteMirrorOuterTransport : Prop :=
  ∀ (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1))))
    (d : (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.D),
    (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.IsOuter (mirrorContinuityDartTransport M N r
        I d) ↔
    (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
      (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.IsOuter d

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Framed isomorphisms preserve presence of the optional endpoint mark. -/
theorem mirrorContinuityOtherNone_iff {B C : FramedBall} (J : FramedBallIso B C) :
    B.frameOtherDart = none ↔ C.frameOtherDart = none := by
  cases hb : B.frameOtherDart <;> cases hc : C.frameOtherDart
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rcases J.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
    · simp only [hc, reduceCtorEq] at h
      exact h.2.elim
    · simp only [hb, Option.map_none, reduceCtorEq] at hx
  · rcases J.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
    · simp only [hb, Option.map_some, reduceCtorEq] at h
      exact h.1.elim
    · simp only [hc, reduceCtorEq] at hy
  · simp only [reduceCtorEq]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Closing outer-face transport suffices to obtain the complete smaller faced isomorphism. -/
@[expose] noncomputable def mirrorContinuityFacedIso_of_outerTransport
    (h : RootedLocallyFiniteMirrorOuterTransport)
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M (r + 2) (Nat.zero_lt_succ (r + 1)))
      (rootedLocallyFiniteFacedBall N (r + 2) (Nat.zero_lt_succ (r + 1)))) :
    FacedFramedBallIso
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r))
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
        (r + 1) (Nat.zero_lt_succ r)) := by
  let B := (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
    (r + 1) (Nat.zero_lt_succ r)).toFramedBall
  let C := (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
    (r + 1) (Nat.zero_lt_succ r)).toFramedBall
  let e := mirrorContinuityDartTransport M N r I
  have hf : e B.frameEdgeDart = C.frameEdgeDart :=
    mirrorContinuityDartTransport_frameEdge M N r I
  have hedge : ∀ d, e (B.map.edgeInv d) = C.map.edgeInv (e d) :=
    mirrorContinuityDartTransport_edgeInv M N r I
  have hm : B.frameOtherDart = M.frameOtherDart.map
      (fun _ => B.map.edgeInv B.frameEdgeDart) := by
    simp only [B, rootedLocallyFiniteFacedBall, rootedLocallyFiniteFramedBall,
      mirrorRootedLocallyFinitePlanarMap, mirrorRootedLocallyFiniteMap, Option.map_map,
      Function.comp_def]
    rfl
  have hn : C.frameOtherDart = N.frameOtherDart.map
      (fun _ => C.map.edgeInv C.frameEdgeDart) := by
    simp only [C, rootedLocallyFiniteFacedBall, rootedLocallyFiniteFramedBall,
      mirrorRootedLocallyFinitePlanarMap, mirrorRootedLocallyFiniteMap, Option.map_map,
      Function.comp_def]
    rfl
  have hnone : M.frameOtherDart = none ↔ N.frameOtherDart = none := by
    have hstatus := mirrorContinuityOtherNone_iff I.toFramedBallIso
    simpa only [rootedLocallyFiniteFacedBall, rootedLocallyFiniteFramedBall,
      Option.map_eq_none_iff] using hstatus
  refine {
    toFramedBallIso := {
      mapIso := {
        toEquiv := e
        rot_comm := mirrorContinuityDartTransport_rot M N r I
        edgeInv_comm := hedge
        missing_iff := ?_
        tail_iff := ?_
        outer_iff := h M N r I }
      root_vertex := ?_
      frameEdge_comm := hf
      frameOther_comm := ?_ }
    original_iff := mirrorContinuityDartTransport_original M N r I }
  · intro d
    exact I.toFramedBallIso.mapIso.missing_iff
      ⟨d.1, rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (r + 1) d.1 d.2⟩
  · intro d
    exact I.toFramedBallIso.mapIso.tail_iff
      ⟨d.1, rootedMirrorBallDarts_shift M.toRootedLocallyFiniteMap (r + 1) d.1 d.2⟩
  · change C.map.rot.SameCycle (e B.frameEdgeDart) C.frameEdgeDart
    rw [hf]
  · rw [hm, hn]
    cases ho : M.frameOtherDart with
    | none =>
      have hno := hnone.mp ho
      simp only [hno, Option.map_none, and_self, true_or]
    | some d =>
      cases hp : N.frameOtherDart with
      | none =>
        have hh := hnone.mpr hp
        simp only [ho, reduceCtorEq] at hh
      | some d' =>
        right
        refine ⟨e (B.map.edgeInv B.frameEdgeDart), C.map.edgeInv C.frameEdgeDart,
          rfl, rfl, ?_⟩
        rw [hedge, hf]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Ambient reflected outer-face darts belong to the enclosing reflected outer face. -/
private theorem mirrorContinuityOuter_survives
    (M : RootedLocallyFinitePlanarMap) (s : ℕ) (hs : 0 < s)
    (d : (mirrorContinuityEnclosingBall M s hs).toFramedBall.D)
    (hd : (M.rot * M.edgeInv).SameCycle (M.edgeInv M.outer) d.1) :
    (mirrorContinuityEnclosingBall M s hs).toFramedBall.map.IsOuter d := by
  change (rootedLocallyFiniteFacedBall M s hs).toFramedBall.D at d
  change (rootedLocallyFiniteFacedBall M s hs).toFramedBall.map.mirror.IsOuter d
  rw [DirectedMapWithMissing.mirror_isOuter_iff]
  apply rootedLocallyFiniteBall_outer_survives M s hs (M.edgeInv d.1)
    (rootedLocallyFiniteBallDarts_edgeInv_closed M.toRootedLocallyFiniteMap s d.1 d.2)
  have hc := (mirrorContinuityFaceCycle M.rot M.edgeInv M.edgeInv_invol
    (M.edgeInv M.outer) d.1).1 hd
  simpa only [M.edgeInv_invol] using hc

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Flattening transports the induced face successor. -/
private theorem mirrorContinuityFlatten_face (M : RootedLocallyFinitePlanarMap) (r : ℕ)
    (d : {d // d ∈ mirrorContinuityRestrictionDarts M r}) :
    mirrorContinuityFlatten M r ((mirrorContinuityRestrictionMap M r).faceSucc d) =
      (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
        (r + 1) (Nat.zero_lt_succ r)).toFramedBall.map.faceSucc
          (mirrorContinuityFlatten M r d) := by
  let K := mirrorContinuityRestrictionMap M r
  let B := (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
    (r + 1) (Nat.zero_lt_succ r)).toFramedBall
  let e := mirrorContinuityFlatten M r
  have hinv (x) : e (K.rot.symm x) = B.map.rot.symm (e x) := by
    apply B.map.rot.injective
    rw [← mirrorContinuityFlatten_rot, K.rot.apply_symm_apply, B.map.rot.apply_symm_apply]
  change e (K.rot.symm (K.edgeInv d)) = B.map.rot.symm (B.map.edgeInv (e d))
  rw [hinv, mirrorContinuityFlatten_edgeInv]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The outer-face transport obligation is discharged by connected planar restriction. -/
theorem rootedLocallyFiniteMirrorOuterTransport_proved :
    RootedLocallyFiniteMirrorOuterTransport := by
  classical
  intro M N r I
  let B := (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap M)
    (r + 1) (Nat.zero_lt_succ r)).toFramedBall
  let C := (rootedLocallyFiniteFacedBall (mirrorRootedLocallyFinitePlanarMap N)
    (r + 1) (Nat.zero_lt_succ r)).toFramedBall
  let BM := (mirrorContinuityEnclosingBall M (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall
  let BN := (mirrorContinuityEnclosingBall N (r + 2) (Nat.zero_lt_succ (r + 1))).toFramedBall
  let J := (mirrorContinuityEnclosingIso M N (r + 2) (Nat.zero_lt_succ (r + 1)) I).toFramedBallIso
  let e := mirrorContinuityDartTransport M N r I
  let x := (mirrorContinuityFlatten M r).symm B.map.outer
  let y := (mirrorContinuityFlatten N r).symm C.map.outer
  let z := mirrorContinuityRestrictedEquiv M N r I x
  have hx : BM.map.IsOuter x.1 := mirrorContinuityOuter_survives M _ _ x.1
    (rootedLocallyFiniteOuterFrameDart_outer
      (mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap))
  have hy : BN.map.IsOuter y.1 := mirrorContinuityOuter_survives N _ _ y.1
    (rootedLocallyFiniteOuterFrameDart_outer
      (mirrorRootedLocallyFiniteMap N.toRootedLocallyFiniteMap))
  have hz : BN.map.IsOuter z.1 := (J.mapIso.outer_iff x.1).2 hx
  have hplanar : BN.map.toCombinatorialMap.IsPlanar :=
    (CombinatorialMap.isPlanar_mirror_iff _).2
      (N.ball_isPlanar (r + 2) (Nat.zero_lt_succ (r + 1)))
  have hsmall := inducedCombinatorialMap_face_sameCycle_of_connected_planar
    BN.map.toCombinatorialMap hplanar (mirrorContinuityRestrictionDarts N r)
    (mirrorContinuityRestrictionDarts_edgeInv N r)
    (framedBallRadiusDarts_connected BN (r + 1) (Nat.zero_lt_succ r)) y z (hy.symm.trans hz)
  have hflat := framedBall_sameCycle_iff_of_equiv (mirrorContinuityFlatten N r)
    (mirrorContinuityRestrictionMap N r).faceSucc C.map.faceSucc
    (mirrorContinuityFlatten_face N r)
  have houter : C.map.faceSucc.SameCycle C.map.outer (e B.map.outer) := by
    have hh := (hflat y z).1 hsmall
    change C.map.faceSucc.SameCycle C.map.outer (mirrorContinuityFlatten N r z)
    simpa only [y, Equiv.apply_symm_apply] using hh
  have hface (d) : e (B.map.faceSucc d) = C.map.faceSucc (e d) := by
    change e (B.map.rot.symm (B.map.edgeInv d)) = C.map.rot.symm (C.map.edgeInv (e d))
    apply C.map.rot.injective
    rw [← mirrorContinuityDartTransport_rot, B.map.rot.apply_symm_apply,
      C.map.rot.apply_symm_apply, mirrorContinuityDartTransport_edgeInv]
  have hcycle := framedBall_sameCycle_iff_of_equiv e B.map.faceSucc C.map.faceSucc hface
  intro d
  exact ⟨fun hd => (hcycle B.map.outer d).2 (houter.symm.trans hd),
    fun hd => houter.trans ((hcycle B.map.outer d).1 hd)⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Equal enclosing faced classes determine equal smaller reflected faced classes. -/
theorem rootedLocallyFiniteMirrorShiftedClassDeterminacy_proved :
    RootedLocallyFiniteMirrorShiftedClassDeterminacy mirrorRootedLocallyFinitePlanarMap := by
  intro r M N h
  obtain ⟨I⟩ := Quotient.exact h
  exact Quotient.sound ⟨mirrorContinuityFacedIso_of_outerTransport
    rootedLocallyFiniteMirrorOuterTransport_proved M N r I⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The constructed reflection is continuous in the faced-ball helper topology. -/
theorem continuous_mirrorRootedLocallyFinitePlanarMap :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    Continuous mirrorRootedLocallyFinitePlanarMap := by
  obtain ⟨c, hc⟩ := (rootedMirrorShiftedCoordinateEquation_iff
    mirrorRootedLocallyFinitePlanarMap).2
      rootedLocallyFiniteMirrorShiftedClassDeterminacy_proved
  exact continuous_mirrorRootedLocallyFinitePlanarMap_of_shiftedCoordinateEquation _ c hc

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The constructed reflection is measurable for the helper topology's Borel space. -/
theorem measurable_mirrorRootedLocallyFinitePlanarMap :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
    Measurable mirrorRootedLocallyFinitePlanarMap := by
  obtain ⟨c, hc⟩ := (rootedMirrorShiftedCoordinateEquation_iff
    mirrorRootedLocallyFinitePlanarMap).2
      rootedLocallyFiniteMirrorShiftedClassDeterminacy_proved
  exact measurable_mirrorRootedLocallyFinitePlanarMap_of_shiftedCoordinateEquation _ c hc


end DirectedDistances.PlanarMap
