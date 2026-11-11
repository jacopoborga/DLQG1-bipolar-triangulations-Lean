module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallConnected
public import DirectedDistances.PlanarMap.FramedBallClassRestrict

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/

noncomputable section

public section
namespace DirectedDistances.PlanarMap

open Equiv

local instance (M : RootedLocallyFiniteMap) : DecidableEq M.D := Classical.decEq _

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result. -/
theorem rootedLocallyFiniteBallDarts_mono (M : RootedLocallyFiniteMap)
    {r s : ℕ} (hrs : r ≤ s) :
    rootedLocallyFiniteBallDarts M r ⊆ rootedLocallyFiniteBallDarts M s := by
  intro d hd
  rw [mem_rootedLocallyFiniteBallDarts] at hd ⊢
  exact ⟨rootedLocallyFiniteRadiusVertices_mono M hrs hd.1,
    rootedLocallyFiniteRadiusVertices_mono M hrs hd.2⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The smaller radius dart set inside the larger ball. Source: -/
@[expose] noncomputable def rootedLocallyFiniteNestedBallDarts
    (M : RootedLocallyFiniteMap) (r s : ℕ) :
    Finset {d : M.D // d ∈ rootedLocallyFiniteBallDarts M s} := by
  classical
  exact firstReturnSubset (rootedLocallyFiniteBallDarts M s)
    (rootedLocallyFiniteBallDarts M r)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Nested radius darts are closed under edge reversal. Source: -/
theorem rootedLocallyFiniteNestedBallDarts_edgeInv_closed
    (M : RootedLocallyFiniteMap) (r s : ℕ)
    :
    ∀ z, z ∈ rootedLocallyFiniteNestedBallDarts M r s →
      (rootedLocallyFiniteBallCombinatorialMap M s).edgeInv z ∈
        rootedLocallyFiniteNestedBallDarts M r s := by
  classical
  intro z hz
  have hz' : z.1 ∈ rootedLocallyFiniteBallDarts M r := by
    simpa [rootedLocallyFiniteNestedBallDarts, firstReturnSubset] using hz
  have h := rootedLocallyFiniteBallDarts_edgeInv_closed M r z.1 hz'
  simpa [rootedLocallyFiniteNestedBallDarts, firstReturnSubset,
    rootedLocallyFiniteBallCombinatorialMap, Equiv.Perm.subtypePerm_apply] using h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The nested first-return map, without connectivity as a premise. Source: -/
@[expose] noncomputable def rootedLocallyFiniteNestedBallCombinatorialMap
    (M : RootedLocallyFiniteMap) (r s : ℕ)
    :
    CombinatorialMap {z // z ∈ rootedLocallyFiniteNestedBallDarts M r s} :=
  inducedCombinatorialMap (rootedLocallyFiniteBallCombinatorialMap M s)
    (rootedLocallyFiniteNestedBallDarts M r s)
    (rootedLocallyFiniteNestedBallDarts_edgeInv_closed M r s)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Flatten the two subtype layers of nested radius darts. Source: -/
@[expose] noncomputable def rootedLocallyFiniteNestedBallEquiv
    (M : RootedLocallyFiniteMap) {r s : ℕ} (hrs : r ≤ s) :
    {z // z ∈ rootedLocallyFiniteNestedBallDarts M r s} ≃
      {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} := by
  classical
  exact {
    toFun := fun z => ⟨z.1.1, by
      simpa [rootedLocallyFiniteNestedBallDarts, firstReturnSubset] using z.2⟩
    invFun := fun z => ⟨⟨z.1, rootedLocallyFiniteBallDarts_mono M hrs z.2⟩,
      by simp [rootedLocallyFiniteNestedBallDarts, firstReturnSubset, z.2]⟩
    left_inv := by intro z; cases z with | mk z hz => cases z; rfl
    right_inv := by intro z; cases z; rfl }

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Nested first return is direct first return, including infinite ambient carriers. -/
theorem rootedLocallyFiniteNestedBallEquiv_rot
    (M : RootedLocallyFiniteMap) {r s : ℕ} (hrs : r ≤ s)
    (z : {z // z ∈ rootedLocallyFiniteNestedBallDarts M r s}) :
    rootedLocallyFiniteNestedBallEquiv M hrs
        ((rootedLocallyFiniteNestedBallCombinatorialMap M r s).rot z) =
      (rootedLocallyFiniteBallCombinatorialMap M r).rot
        (rootedLocallyFiniteNestedBallEquiv M hrs z) := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let T := rootedLocallyFiniteBallDarts M s
  have hret (V : Finset M.D) : ∀ x : V,
      ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ V := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have h := firstReturn_nested' M.rot T S (hret T)
    (fun d hd => rootedLocallyFiniteBallDarts_mono M hrs hd)
    (finitePermutationReturn (cyclicFirstReturn M.rot T (hret T))
      (firstReturnSubset T S)) (hret S)
    (rootedLocallyFiniteNestedBallEquiv M hrs z)
  apply Subtype.ext
  exact h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Nested restriction preserves edge identity. Source: -/
theorem rootedLocallyFiniteNestedBallEquiv_edgeInv
    (M : RootedLocallyFiniteMap) {r s : ℕ} (hrs : r ≤ s)
    (z : {z // z ∈ rootedLocallyFiniteNestedBallDarts M r s}) :
    rootedLocallyFiniteNestedBallEquiv M hrs
        ((rootedLocallyFiniteNestedBallCombinatorialMap M r s).edgeInv z) =
      (rootedLocallyFiniteBallCombinatorialMap M r).edgeInv
        (rootedLocallyFiniteNestedBallEquiv M hrs z) := by
  apply Subtype.ext
  rfl

private theorem perm_symm_comm {A B : Type*} (e : A ≃ B)
    (p : Equiv.Perm A) (q : Equiv.Perm B)
    (h : ∀ x, e (p x) = q (e x)) (x : A) :
    e (p.symm x) = q.symm (e x) := by
  apply q.injective
  rw [← h, p.apply_symm_apply, q.apply_symm_apply]

private theorem connected_equiv {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (K : CombinatorialMap A) (L : CombinatorialMap B) (e : A ≃ B)
    (hrot : ∀ x, e (K.rot x) = L.rot (e x))
    (hedge : ∀ x, e (K.edgeInv x) = L.edgeInv (e x))
    (hconn : L.IsConnected) : K.IsConnected := by
  have hrotSymm := perm_symm_comm e K.rot L.rot hrot
  have hedgeSymm := perm_symm_comm e K.edgeInv L.edgeInv hedge
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



theorem rootedLocallyFiniteNestedBallCombinatorialMap_connected
    (M : RootedLocallyFiniteMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    :
    (rootedLocallyFiniteNestedBallCombinatorialMap M r s).IsConnected := by
  exact connected_equiv _ _ (rootedLocallyFiniteNestedBallEquiv M hrs)
    (rootedLocallyFiniteNestedBallEquiv_rot M hrs)
    (rootedLocallyFiniteNestedBallEquiv_edgeInv M hrs)
    (rootedLocallyFiniteBallCombinatorialMap_connected M r hr)

private theorem sameCycle_comm {A B : Type*} [Finite A]
    (e : A ≃ B) (p : Equiv.Perm A) (q : Equiv.Perm B)
    (h : ∀ x, e (p x) = q (e x)) {x y : A} (hxy : p.SameCycle x y) :
    q.SameCycle (e x) (e y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hpow (n : ℕ) : ∀ x, e ((p ^ n) x) = (q ^ n) (e x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, h, ih]
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, ← hpow, hn]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Flattening nested darts preserves the face successor, with plane orientation. -/
theorem rootedLocallyFiniteNestedBallEquiv_faceSucc (M : RootedLocallyFiniteMap)
    {r s : ℕ} (hrs : r ≤ s)
    (z : {z // z ∈ rootedLocallyFiniteNestedBallDarts M r s}) :
    rootedLocallyFiniteNestedBallEquiv M hrs
        ((rootedLocallyFiniteNestedBallCombinatorialMap M r s).faceSucc z) =
      (rootedLocallyFiniteBallCombinatorialMap M r).faceSucc
        (rootedLocallyFiniteNestedBallEquiv M hrs z) := by
  let K := rootedLocallyFiniteNestedBallCombinatorialMap M r s
  let L := rootedLocallyFiniteBallCombinatorialMap M r
  let e := rootedLocallyFiniteNestedBallEquiv M hrs
  have hrot := rootedLocallyFiniteNestedBallEquiv_rot M hrs
  have hedge := rootedLocallyFiniteNestedBallEquiv_edgeInv M hrs
  change e (K.rot.symm (K.edgeInv z)) = L.rot.symm (L.edgeInv (e z))
  rw [perm_symm_comm e K.rot L.rot hrot, hedge]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Retained darts on a larger ball face remain on one smaller ball face. -/
theorem rootedLocallyFiniteBall_face_restriction
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (x y : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r})
    (hxy : (rootedLocallyFiniteBallCombinatorialMap M.toRootedLocallyFiniteMap s).faceSucc.SameCycle
        ⟨x.1, rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs x.2⟩
        ⟨y.1, rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs y.2⟩) :
    Equiv.Perm.SameCycle
      (rootedLocallyFiniteBallCombinatorialMap M.toRootedLocallyFiniteMap r).faceSucc
      x y := by
  let A := M.toRootedLocallyFiniteMap
  let N := rootedLocallyFiniteBallCombinatorialMap A s
  let U := rootedLocallyFiniteNestedBallDarts A r s
  let hU := rootedLocallyFiniteNestedBallDarts_edgeInv_closed A r s
  let K := rootedLocallyFiniteNestedBallCombinatorialMap A r s
  let L := rootedLocallyFiniteBallCombinatorialMap A r
  let e := rootedLocallyFiniteNestedBallEquiv A hrs
  have hK : K.IsConnected :=
    rootedLocallyFiniteNestedBallCombinatorialMap_connected A hr hrs
  have hplanar : N.IsPlanar := M.ball_isPlanar s (hr.trans_le hrs)
  have hcycle : K.faceSucc.SameCycle (e.symm x) (e.symm y) :=
    inducedCombinatorialMap_face_sameCycle_of_connected_planar
      N hplanar U hU hK (e.symm x) (e.symm y) hxy
  have h := sameCycle_comm e K.faceSucc L.faceSucc
    (rootedLocallyFiniteNestedBallEquiv_faceSucc A hrs) hcycle
  simpa only [e.apply_symm_apply] using h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The selected ambient outer-facing frame dart is retained at positive radius. -/
theorem rootedLocallyFiniteOuterFrameDart_mem (M : RootedLocallyFiniteMap)
    {r : ℕ} (hr : 0 < r) :
    rootedLocallyFiniteOuterFrameDart M ∈ rootedLocallyFiniteBallDarts M r := by
  classical
  have h := rootedLocallyFiniteBallDarts_frame_mem M hr
  unfold rootedLocallyFiniteOuterFrameDart
  split
  · exact h.2.1
  · exact h.2.2




theorem rootedLocallyFiniteBall_outer_survives
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r)
    (d : M.D) (hd : d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r)
    (ho : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer d) :
    CombinatorialMap.IsOuter
      (rootedLocallyFiniteBallCombinatorialMap M.toRootedLocallyFiniteMap r)
      ⟨rootedLocallyFiniteOuterFrameDart M.toRootedLocallyFiniteMap,
        rootedLocallyFiniteOuterFrameDart_mem M.toRootedLocallyFiniteMap hr⟩
      ⟨d, hd⟩ := by
  obtain ⟨R, hrR, hdR, hfR, hface⟩ :=
    M.outerFace_captured_in_larger_ball r hr d hd ho
  exact rootedLocallyFiniteBall_face_restriction M hr hrR _ _ hface

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The tagged directed carrier is the actual first-return ball, with its outer
face obtained by restriction rather than supplied as a construction parameter. -/
@[expose] noncomputable def rootedLocallyFiniteBallDirectedMap
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) :
    DirectedMapWithMissing
      {d : M.D // d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r} := by
  let A := M.toRootedLocallyFiniteMap
  refine {
    toCombinatorialMap := rootedLocallyFiniteBallCombinatorialMap A r
    missing := rootedLocallyFiniteBallMissing A r
    missing_edgeInv := fun d => M.missing_edgeInv d.1
    tail := rootedLocallyFiniteBallTail A r
    tail_iff := fun d => M.tail_iff d.1
    tail_missing := fun d => M.tail_missing d.1
    outer := ⟨rootedLocallyFiniteOuterFrameDart A, rootedLocallyFiniteOuterFrameDart_mem A hr⟩
    missing_outer := ?_ }
  intro d hd
  rcases M.missing_outer d.1 hd with h | h
  · exact Or.inl (rootedLocallyFiniteBall_outer_survives M r hr d.1 d.2 h)
  · exact Or.inr (rootedLocallyFiniteBall_outer_survives M r hr (M.edgeInv d.1)
      (rootedLocallyFiniteBallDarts_edgeInv_closed A r d.1 d.2) h)







@[expose] noncomputable def rootedLocallyFiniteFramedBall
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) : FramedBall := by
  let A := M.toRootedLocallyFiniteMap
  let hframe := rootedLocallyFiniteBallDarts_frame_mem A hr
  let other : {d : M.D // d ∈ rootedLocallyFiniteBallDarts A r} :=
    ⟨M.edgeInv M.frameEdgeDart, hframe.2.2⟩
  refine {
    D := {d : M.D // d ∈ rootedLocallyFiniteBallDarts A r}
    map := rootedLocallyFiniteBallDirectedMap M r hr
    rootDart := ⟨M.rootDart, hframe.1⟩
    frameEdgeDart := ⟨M.frameEdgeDart, hframe.2.1⟩
    frameEdge_missing := M.frameEdge_missing
    frameEdge_at_root :=
      (rootedLocallyFiniteBall_rot_sameCycle_iff A r _ _).2 M.frameEdge_at_root
    frameOtherDart := M.frameOtherDart.map (fun _ => other)
    frameOtherDart_valid := ?_ }
  intro y hy
  cases hm : M.frameOtherDart with
  | none => simp only [hm, Option.map_none, reduceCtorEq] at hy
  | some d =>
    have hy' : other = y := by simpa only [hm, Option.map_some, Option.some.injEq] using hy
    subst y
    exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Tags and orientation are inherited verbatim. Source: -/
theorem rootedLocallyFiniteFramedBall_tags
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r)
    (d : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r}) :
    (rootedLocallyFiniteFramedBall M r hr).map.missing d = M.missing d.1 ∧
      (rootedLocallyFiniteFramedBall M r hr).map.tail d = M.tail d.1 := by
  exact ⟨rfl, rfl⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A commuting dart equivalence preserves and reflects permutation cycles. -/
theorem framedBall_sameCycle_iff_of_equiv {A B : Type*} [Finite A] [Finite B]
    (e : A ≃ B) (p : Equiv.Perm A) (q : Equiv.Perm B)
    (h : ∀ x, e (p x) = q (e x)) (x y : A) :
    p.SameCycle x y ↔ q.SameCycle (e x) (e y) := by
  constructor
  · exact sameCycle_comm e p q h
  · intro hxy
    have hinv (z : B) : e.symm (q z) = p (e.symm z) := by
      apply e.injective
      rw [e.apply_symm_apply, h, e.apply_symm_apply]
    have hback := sameCycle_comm e.symm q p hinv hxy
    simpa only [e.symm_apply_apply] using hback

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The tagged nested first-return map with the inherited root-facing outer face. -/
@[expose] noncomputable def rootedLocallyFiniteNestedBallDirectedMap
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    DirectedMapWithMissing
      {z // z ∈ rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s} := by
  let A := M.toRootedLocallyFiniteMap
  let K := rootedLocallyFiniteNestedBallCombinatorialMap A r s
  let L := rootedLocallyFiniteBallDirectedMap M r hr
  let e := rootedLocallyFiniteNestedBallEquiv A hrs
  have hface := framedBall_sameCycle_iff_of_equiv e K.faceSucc L.faceSucc
    (rootedLocallyFiniteNestedBallEquiv_faceSucc A hrs)
  refine {
    toCombinatorialMap := K
    missing := fun z => M.missing z.1.1
    missing_edgeInv := fun z => M.missing_edgeInv z.1.1
    tail := fun z => M.tail z.1.1
    tail_iff := fun z => M.tail_iff z.1.1
    tail_missing := fun z => M.tail_missing z.1.1
    outer := e.symm L.outer
    missing_outer := ?_ }
  intro z hz
  rcases L.missing_outer (e z) hz with h | h
  · apply Or.inl
    apply (hface _ _).2
    change L.faceSucc.SameCycle L.outer (e z) at h
    simpa only [e.apply_symm_apply] using h
  · apply Or.inr
    apply (hface _ _).2
    rw [e.apply_symm_apply, rootedLocallyFiniteNestedBallEquiv_edgeInv]
    exact h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A second restriction on the ambient radius dart set, retaining every ordered
mark and the tags of the larger ball. Intrinsic radius identification is separate. -/
@[expose] noncomputable def rootedLocallyFiniteNestedFramedBall
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    FramedBall := by
  let A := M.toRootedLocallyFiniteMap
  let B := rootedLocallyFiniteFramedBall M r hr
  let N := rootedLocallyFiniteNestedBallDirectedMap M hr hrs
  let e : {z // z ∈ rootedLocallyFiniteNestedBallDarts A r s} ≃ B.D :=
    rootedLocallyFiniteNestedBallEquiv A hrs
  have hrot : ∀ z, e (N.rot z) = B.map.rot (e z) :=
    rootedLocallyFiniteNestedBallEquiv_rot A hrs
  have hedge : ∀ z, e (N.edgeInv z) = B.map.edgeInv (e z) :=
    rootedLocallyFiniteNestedBallEquiv_edgeInv A hrs
  have hvertex := framedBall_sameCycle_iff_of_equiv e N.rot B.map.rot hrot
  refine {
    D := {z // z ∈ rootedLocallyFiniteNestedBallDarts A r s}
    map := N
    rootDart := e.symm B.rootDart
    frameEdgeDart := e.symm B.frameEdgeDart
    frameEdge_missing := B.frameEdge_missing
    frameEdge_at_root := ?_
    frameOtherDart := B.frameOtherDart.map e.symm
    frameOtherDart_valid := ?_ }
  · apply (hvertex _ _).2
    simpa only [e.apply_symm_apply] using B.frameEdge_at_root
  · intro y hy
    cases hm : B.frameOtherDart with
    | none => simp only [hm, Option.map_none, reduceCtorEq] at hy
    | some d =>
      have hy' : e.symm d = y := by
        simpa only [hm, Option.map_some, Option.some.injEq] using hy
      subst y
      apply (hvertex _ _).2
      rw [hedge, e.apply_symm_apply, e.apply_symm_apply]
      exact B.frameOtherDart_valid d hm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Nested restriction is a framed-ball isomorphism: rotations, edge identities,
tags, orientations, face cycles, outer face and the ordered mark are preserved. -/
@[expose] noncomputable def rootedLocallyFiniteNestedFramedBallIso
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    FramedBallIso (rootedLocallyFiniteNestedFramedBall M hr hrs)
      (rootedLocallyFiniteFramedBall M r hr) := by
  let A := M.toRootedLocallyFiniteMap
  let B := rootedLocallyFiniteFramedBall M r hr
  let N := rootedLocallyFiniteNestedFramedBall M hr hrs
  let e : N.D ≃ B.D := rootedLocallyFiniteNestedBallEquiv A hrs
  have hrot : ∀ z, e (N.map.rot z) = B.map.rot (e z) :=
    rootedLocallyFiniteNestedBallEquiv_rot A hrs
  have hedge : ∀ z, e (N.map.edgeInv z) = B.map.edgeInv (e z) :=
    rootedLocallyFiniteNestedBallEquiv_edgeInv A hrs
  have hface := framedBall_sameCycle_iff_of_equiv e N.map.faceSucc B.map.faceSucc
    (rootedLocallyFiniteNestedBallEquiv_faceSucc A hrs)
  refine {
    mapIso := {
      toEquiv := e
      rot_comm := hrot
      edgeInv_comm := hedge
      missing_iff := fun _ => Iff.rfl
      tail_iff := fun _ => Iff.rfl
      outer_iff := ?_ }
    root_vertex := ?_
    frameEdge_comm := e.apply_symm_apply _
    frameOther_comm := ?_ }
  · intro z
    have h := hface N.map.outer z
    have houter : e N.map.outer = B.map.outer := e.apply_symm_apply _
    rw [houter] at h
    exact h.symm
  · change B.map.rot.SameCycle (e (e.symm B.rootDart)) B.rootDart
    rw [e.apply_symm_apply]
  · change ((B.frameOtherDart.map e.symm).map e = none ∧ B.frameOtherDart = none) ∨
      (∃ x y, (B.frameOtherDart.map e.symm).map e = some x ∧
        B.frameOtherDart = some y ∧ B.map.rot.SameCycle x y)
    cases hm : B.frameOtherDart with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some d =>
      right
      refine ⟨d, d, ?_, rfl, Equiv.Perm.SameCycle.rfl⟩
      exact congrArg some (e.apply_symm_apply d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The nested restriction has the same framed-ball class as the direct ball. -/
theorem rootedLocallyFiniteNestedFramedBall_class
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    Quotient.mk FramedBall.setoid (rootedLocallyFiniteNestedFramedBall M hr hrs) =
      Quotient.mk FramedBall.setoid (rootedLocallyFiniteFramedBall M r hr) :=
  Quotient.sound ⟨rootedLocallyFiniteNestedFramedBallIso M hr hrs⟩

private theorem firstReturn_next_mem {D : Type*} [DecidableEq D]
    (p : Equiv.Perm D) (S : Finset D)
    (hret : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (p ^ k) x.1 ∈ S)
    (x : S) (hx : p x.1 ∈ S) : (cyclicFirstReturn p S hret x).1 = p x.1 := by
  have ht : cyclicFirstReturnTime p S hret x = 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hret x) ⟨Nat.one_pos, by simpa only [pow_one] using hx⟩
    · exact (cyclicFirstReturnTime_spec p S hret x).1
  rw [(firstReturn_spec p S hret x).1, ht, pow_one]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A retained ambient face step survives with its precise incidence. -/
theorem rootedLocallyFiniteBall_faceSucc_of_mem
    (M : RootedLocallyFiniteMap) (r : ℕ)
    (d : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r})
    (hface : M.rot.symm (M.edgeInv d.1) ∈ rootedLocallyFiniteBallDarts M r) :
    ((rootedLocallyFiniteBallCombinatorialMap M r).faceSucc d).1 =
      M.rot.symm (M.edgeInv d.1) := by
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
    exact (firstReturn_next_mem M.rot S hret y hy).trans hnext
  change (N.rot.symm (N.edgeInv d)).1 = _
  rw [← hrot, Equiv.symm_apply_apply]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The ambient face through this dart is completely retained, rather than being a
new face of the induced combinatorial map. This is a predicate on the original
ambient face; `FramedBall` does not store this selection of face cycles. -/
@[expose] def rootedLocallyFiniteBallContainsOriginalFace
    (M : RootedLocallyFiniteMap) (r : ℕ) (d : M.D) : Prop :=
  ∀ e, Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) d e →
    e ∈ rootedLocallyFiniteBallDarts M r

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Completely retained original faces have unchanged face successors. -/
theorem rootedLocallyFiniteBall_faceSucc_of_contained
    (M : RootedLocallyFiniteMap) (r : ℕ)
    (d : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r})
    (hface : rootedLocallyFiniteBallContainsOriginalFace M r d.1) :
    ((rootedLocallyFiniteBallCombinatorialMap M r).faceSucc d).1 =
      M.rot.symm (M.edgeInv d.1) := by
  apply rootedLocallyFiniteBall_faceSucc_of_mem
  apply hface
  exact ⟨(1 : ℤ), by rw [zpow_one]; rfl⟩

/- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Exact remaining intrinsic-radius identification: radius measured in the larger
finite ball must recover the ambient smaller-radius dart set. This proposition -/
@[expose] def rootedLocallyFiniteFramedBallRadiusExact
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) : Prop :=
  framedBallRadiusDarts (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)) r =
    rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Actual positive-radius class map on the existing planar carrier; index `r` -/
@[expose] noncomputable def rootedLocallyFiniteFramedBallClass
    (r : ℕ) (M : RootedLocallyFinitePlanarMap) : FramedBallClass :=
  Quotient.mk FramedBall.setoid (rootedLocallyFiniteFramedBall M (r + 1) (by omega))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Exact remaining class restriction obligation, without assuming it as data.
The current `RootedFramedBallSystem.Object : Type` also cannot directly hold the
existing planar carrier, which lies in `Type 1`. No system instance is claimed. -/
@[expose] def rootedLocallyFiniteFramedBallRestrictionCompatible : Prop :=
  ∀ (r : ℕ) (M N : RootedLocallyFinitePlanarMap),
    rootedLocallyFiniteFramedBallClass (r + 1) M =
        rootedLocallyFiniteFramedBallClass (r + 1) N →
      rootedLocallyFiniteFramedBallClass r M = rootedLocallyFiniteFramedBallClass r N

end DirectedDistances.PlanarMap
end
end
