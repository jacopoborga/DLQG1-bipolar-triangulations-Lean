/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RootedMapQuotient
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem

/-! # Whole-map isomorphisms of positive-radius balls

Helper toward Definition 3.8 (`def-bs-topology`): rooted whole-map
isomorphisms preserve the induced all-geometric graph-distance balls, their
retained face data, and the Euler characteristic of each finite ball. -/

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8. A dart isomorphism commuting with rotations
maps vertex rotation cycles to vertex rotation cycles. -/
theorem rootedSameCycle_map {D E : Type*} (e : D ≃ E)
    (f : Equiv.Perm D) (g : Equiv.Perm E)
    (hcomm : ∀ d, e (f d) = g (e d)) {x y : D}
    (hxy : f.SameCycle x y) : g.SameCycle (e x) (e y) := by
  obtain ⟨n, hn⟩ := hxy
  have hcommSymm (d : D) : e (f.symm d) = g.symm (e d) := by
    simpa using (congrArg g.symm (hcomm (f.symm d))).symm
  have hpow : ∀ n : ℤ, ∀ d : D, e ((f ^ n) d) = (g ^ n) (e d) := by
    intro n
    induction n using Int.induction_on with
    | zero => intro d; simp
    | succ n ih =>
        intro d
        rw [show (n : ℤ) + 1 = 1 + n by omega,
          zpow_add, zpow_one, Equiv.Perm.mul_apply,
          zpow_add, zpow_one, Equiv.Perm.mul_apply]
        rw [hcomm, ih]
    | pred n ih =>
        intro d
        rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega,
          zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
          zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
        exact (hcommSymm ((f ^ (-(n : ℤ))) d)).trans
          (congrArg g.symm (ih d))
  refine ⟨n, ?_⟩
  calc
    (g ^ n) (e x) = e ((f ^ n) x) := (hpow n x).symm
    _ = e y := congrArg e hn

/-- Helper toward Definition 3.8. The whole-map isomorphism induces its map on
rotation-orbit vertices. -/
@[expose] noncomputable def D39RootedMapIso.vertexMap {M N : D39RootedMap}
    (I : D39RootedMapIso M N) :
    RootedLocallyFiniteVertex M.core.D M.core.rot →
      RootedLocallyFiniteVertex N.core.D N.core.rot :=
  Quotient.map I.toEquiv (fun _ _ h =>
    rootedSameCycle_map I.toEquiv M.core.rot N.core.rot I.rot_comm h)

/-- Helper toward Definition 3.8. The induced vertex map sends the class of a
dart to the class of its image. -/
theorem D39RootedMapIso.vertexMap_dart {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (d : M.core.D) :
    I.vertexMap (d39VertexClass M d) = d39VertexClass N (I.toEquiv d) := rfl

/-- Helper toward Definition 3.8. The induced vertex maps of an isomorphism and
its inverse cancel. -/
theorem D39RootedMapIso.vertexMap_symm_apply {M N : D39RootedMap}
    (I : D39RootedMapIso M N)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    I.symm.vertexMap (I.vertexMap v) = v := by
  refine Quotient.inductionOn v ?_
  intro d
  change Quotient.mk _ (I.toEquiv.symm (I.toEquiv d)) = Quotient.mk _ d
  rw [Equiv.symm_apply_apply]

/-- Helper toward Definition 3.8. The induced vertex maps of an isomorphism and
its inverse also cancel in the other order. -/
theorem D39RootedMapIso.vertexMap_apply_symm {M N : D39RootedMap}
    (I : D39RootedMapIso M N)
    (v : RootedLocallyFiniteVertex N.core.D N.core.rot) :
    I.vertexMap (I.symm.vertexMap v) = v := by
  refine Quotient.inductionOn v ?_
  intro d
  change Quotient.mk _ (I.toEquiv (I.toEquiv.symm d)) = Quotient.mk _ d
  rw [I.toEquiv.apply_symm_apply]

/-- Helper toward Definition 3.8. The whole-map isomorphism induces a
bijection on rotation-orbit vertices. -/
@[expose] noncomputable def D39RootedMapIso.vertexEquiv {M N : D39RootedMap}
    (I : D39RootedMapIso M N) :
    RootedLocallyFiniteVertex M.core.D M.core.rot ≃
      RootedLocallyFiniteVertex N.core.D N.core.rot where
  toFun := I.vertexMap
  invFun := I.symm.vertexMap
  left_inv := I.vertexMap_symm_apply
  right_inv := I.vertexMap_apply_symm

/-- Helper toward Definition 3.8. Reachability from the root is preserved by a
whole-map isomorphism. -/
theorem D39RootedMapIso.withinRadius_map {M N : D39RootedMap}
    (I : D39RootedMapIso M N) {r : ℕ}
    {v : RootedLocallyFiniteVertex M.core.D M.core.rot}
    (hv : D39WithinRadius M r v) :
    D39WithinRadius N r (I.vertexMap v) := by
  induction hv with
  | root =>
      have hroot : I.vertexMap (d39VertexClass M M.rootMark.dart) =
          d39VertexClass N N.rootMark.dart := by
        rw [D39RootedMapIso.vertexMap_dart, I.root_dart_comm]
      simpa only [hroot] using
        (D39WithinRadius.root : D39WithinRadius N 0
          (d39VertexClass N N.rootMark.dart))
  | stay _ ih => exact D39WithinRadius.stay ih
  | edge hv hstep ih =>
      change ∃ d, d39VertexClass M d = _ ∧
        d39VertexClass M (M.core.edgeInv d) = _ at hstep
      rcases hstep with ⟨d, hdv, hdw⟩
      apply D39WithinRadius.edge ih
      refine ⟨I.toEquiv d, ?_, ?_⟩
      · exact (I.vertexMap_dart d).symm |>.trans (congrArg I.vertexMap hdv)
      · exact
          (congrArg (d39VertexClass N) (I.edgeInv_comm d).symm).trans
            ((I.vertexMap_dart (M.core.edgeInv d)).symm.trans
              (congrArg I.vertexMap hdw))

/-- Helper toward Definition 3.8. A whole-map isomorphism sends the vertices
of a radius-r ball onto the vertices of the corresponding ball. -/
theorem D39RootedMapIso.vertexMap_ballVertices {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (r : ℕ)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    v ∈ d39BallVertices M r ↔ I.vertexMap v ∈ d39BallVertices N r := by
  rw [mem_d39BallVertices, mem_d39BallVertices]
  constructor
  · exact I.withinRadius_map
  · intro hv
    have hback := I.symm.withinRadius_map hv
    rw [I.vertexMap_symm_apply] at hback
    exact hback

/-- Helper toward Definition 3.8. The induced vertex map preserves the other
endpoint of every geometric dart. -/
theorem D39RootedMapIso.vertexMap_edgeInv_dart {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (d : M.core.D) :
    I.vertexMap (d39VertexClass M (M.core.edgeInv d)) =
      d39VertexClass N (N.core.edgeInv (I.toEquiv d)) := by
  rw [I.vertexMap_dart, I.edgeInv_comm]

/-- Helper toward Definition 3.8. The whole-map isomorphism carries the dart
set of each radius-r ball onto the corresponding dart set. -/
theorem D39RootedMapIso.ballDarts_iff {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (r : ℕ) (d : M.core.D) :
    d ∈ d39BallDarts M r ↔ I.toEquiv d ∈ d39BallDarts N r := by
  rw [mem_d39BallDarts, mem_d39BallDarts]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₂' := (I.vertexMap_ballVertices r
      (d39VertexClass M (M.core.edgeInv d))).mp h₂
    rw [I.vertexMap_edgeInv_dart] at h₂'
    exact ⟨(I.vertexMap_ballVertices r _).mp h₁, h₂'⟩
  · rintro ⟨h₁, h₂⟩
    have h₂' : I.vertexMap (d39VertexClass M (M.core.edgeInv d)) ∈
        d39BallVertices N r := by rw [I.vertexMap_edgeInv_dart]; exact h₂
    exact ⟨(I.vertexMap_ballVertices r _).mpr h₁,
      (I.vertexMap_ballVertices r _).mpr h₂'⟩

/-- Helper toward Definition 3.8. Restrict the dart bijection to the two
radius-r balls. -/
@[expose] noncomputable def D39RootedMapIso.ballDartEquiv
    {M N : D39RootedMap} (I : D39RootedMapIso M N) (r : ℕ) :
    {d : M.core.D // d ∈ d39BallDarts M r} ≃
      {d : N.core.D // d ∈ d39BallDarts N r} where
  toFun d := ⟨I.toEquiv d.1, (I.ballDarts_iff r d.1).mp d.2⟩
  invFun d := ⟨I.toEquiv.symm d.1, by
    have h := I.ballDarts_iff r (I.toEquiv.symm d.1)
    have hd : I.toEquiv (I.toEquiv.symm d.1) ∈ d39BallDarts N r := by
      rw [I.toEquiv.apply_symm_apply]
      exact d.2
    exact h.mpr hd⟩
  left_inv d := by apply Subtype.ext; exact I.toEquiv.symm_apply_apply d.1
  right_inv d := by apply Subtype.ext; exact I.toEquiv.apply_symm_apply d.1

/-- Helper toward Definition 3.8. A whole-map isomorphism commutes with the
ambient face successor. -/
theorem D39RootedMapIso.faceSucc_comm {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (d : M.core.D) :
    I.toEquiv (M.core.rot.symm (M.core.edgeInv d)) =
      N.core.rot.symm (N.core.edgeInv (I.toEquiv d)) := by
  have hrot_symm (x : M.core.D) :
      I.toEquiv (M.core.rot.symm x) = N.core.rot.symm (I.toEquiv x) := by
    apply N.core.rot.injective
    rw [← I.rot_comm, M.core.rot.apply_symm_apply,
      N.core.rot.apply_symm_apply]
  calc
    I.toEquiv (M.core.rot.symm (M.core.edgeInv d)) =
        N.core.rot.symm (I.toEquiv (M.core.edgeInv d)) := hrot_symm _
    _ = N.core.rot.symm (N.core.edgeInv (I.toEquiv d)) :=
      congrArg N.core.rot.symm (I.edgeInv_comm d)

/-- Helper toward Definition 3.8. Ambient face cycles are carried exactly by a
whole-map isomorphism. -/
theorem D39RootedMapIso.faceSameCycle_iff {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (x y : M.core.D) :
    Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) x y ↔
      Equiv.Perm.SameCycle (N.core.rot.symm * N.core.edgeInv)
        (I.toEquiv x) (I.toEquiv y) := by
  constructor
  · exact rootedSameCycle_map I.toEquiv (M.core.rot.symm * M.core.edgeInv)
      (N.core.rot.symm * N.core.edgeInv) I.faceSucc_comm
  · intro h
    have hback := rootedSameCycle_map I.toEquiv.symm
      (N.core.rot.symm * N.core.edgeInv) (M.core.rot.symm * M.core.edgeInv)
      (fun d => by
        have hs := I.faceSucc_comm (I.toEquiv.symm d)
        simpa using (congrArg I.toEquiv.symm hs).symm) h
    simpa using hback

/-- Helper toward Definition 3.8. The whole-map isomorphism induces a full
isomorphism between the positive-radius faced balls. -/
@[expose] noncomputable def D39RootedMapIso.ballIso
    {M N : D39RootedMap} (I : D39RootedMapIso M N)
    (r : ℕ) (hr : 0 < r) :
    D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr) := by
  classical
  let S := d39BallDarts M r
  let T := d39BallDarts N r
  have hperS : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hperT : ∀ y : T, ∃ k : ℕ, 0 < k ∧ (N.core.rot ^ k) y.1 ∈ T := by
    intro y
    obtain ⟨k, hk, heq⟩ := d39RotationReturn N y.1
    exact ⟨k, hk, by rw [heq]; exact y.2⟩
  refine {
    toEquiv := I.ballDartEquiv r
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    root_comm := ?_
    original_iff := ?_ }
  · intro d
    apply Subtype.ext
    change I.toEquiv
        (cyclicFirstReturn M.core.rot S hperS d).1 =
      (cyclicFirstReturn N.core.rot T hperT
        ⟨I.toEquiv d.1, (I.ballDarts_iff r d.1).mp d.2⟩).1
    exact DirectedDistances.PaperProofs.Section3.cyclicFirstReturn_map_of_equiv
      M.core.rot N.core.rot S T I.toEquiv (I.ballDarts_iff r) I.rot_comm
      hperS hperT d
  · intro d
    apply Subtype.ext
    change I.toEquiv (M.core.edgeInv d.1) = N.core.edgeInv (I.toEquiv d.1)
    exact I.edgeInv_comm d.1
  · intro d
    exact I.missing_iff d.1
  · intro d
    change N.core.tail (I.toEquiv d.1) ↔ M.core.tail d.1
    by_cases hm : M.core.missing d.1
    · have hn := (I.missing_iff d.1).mpr hm
      simp [M.core.tail_missing d.1 hm, N.core.tail_missing (I.toEquiv d.1) hn]
    · exact I.tail_iff d.1 hm
  · apply Subtype.ext
    exact I.root_dart_comm
  · intro d
    change d39BallContainsOriginalFace N r (I.toEquiv d.1) ↔
      d39BallContainsOriginalFace M r d.1
    constructor
    · intro h e he
      have he' : Equiv.Perm.SameCycle (N.core.rot.symm * N.core.edgeInv)
          (I.toEquiv d.1) (I.toEquiv e) := (I.faceSameCycle_iff d.1 e).mp he
      have hball := h (I.toEquiv e) he'
      exact (I.ballDarts_iff r e).mpr (by simpa using hball)
    · intro h e he
      let e0 := I.toEquiv.symm e
      have he' : Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv)
          d.1 e0 := by
        apply (I.faceSameCycle_iff d.1 e0).mpr
        simpa [e0] using he
      have hball := h e0 he'
      simpa [e0] using (I.ballDarts_iff r e0).mp hball

/-- Helper toward Definition 3.8. A permutation isomorphism induces an
equivalence of its cycle quotients. -/
@[expose] noncomputable def permCycleQuotientEquiv {A B : Type*}
    (e : A ≃ B) (f : Equiv.Perm A) (g : Equiv.Perm B)
    (hcomm : ∀ x, e (f x) = g (e x)) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ≃
      Quotient (Equiv.Perm.SameCycle.setoid g) := by
  classical
  let fwd : Quotient (Equiv.Perm.SameCycle.setoid f) →
      Quotient (Equiv.Perm.SameCycle.setoid g) :=
    Quotient.map e (by
      intro x y h
      exact rootedSameCycle_map e f g hcomm h)
  let back : Quotient (Equiv.Perm.SameCycle.setoid g) →
      Quotient (Equiv.Perm.SameCycle.setoid f) :=
    Quotient.map e.symm (by
      intro x y h
      apply rootedSameCycle_map e.symm g f (fun d => by
        have hc := hcomm (e.symm d)
        simpa using (congrArg e.symm hc).symm) h)
  exact
    { toFun := fwd
      invFun := back
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        simp [fwd, back]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        simp [fwd, back] }

/-- Helper toward Definition 3.8. Isomorphic finite balls have the same number
of rotation-cycle vertices. -/
theorem D39BallIso.numVertices_eq {B C : D39FiniteBall} (I : D39BallIso B C) :
    B.map.numVertices = C.map.numVertices := by
  classical
  unfold CombinatorialMap.numVertices CombinatorialMap.VertexQuotient
  exact Fintype.card_congr
    (permCycleQuotientEquiv I.toEquiv B.map.rot C.map.rot I.rot_comm)

/-- Helper toward Definition 3.8. Isomorphic finite balls have the same number
of edge-reversal orbits, including parallel edge identities. -/
theorem D39BallIso.numEdges_eq {B C : D39FiniteBall} (I : D39BallIso B C) :
    B.map.numEdges = C.map.numEdges := by
  classical
  unfold CombinatorialMap.numEdges CombinatorialMap.EdgeQuotient
  exact Fintype.card_congr
    (permCycleQuotientEquiv I.toEquiv B.map.edgeInv C.map.edgeInv I.edgeInv_comm)

/-- Helper toward Definition 3.8. Isomorphic finite balls have the same number
of face cycles. -/
theorem D39BallIso.numFaces_eq {B C : D39FiniteBall} (I : D39BallIso B C) :
    B.map.numFaces = C.map.numFaces := by
  classical
  unfold CombinatorialMap.numFaces CombinatorialMap.FaceQuotient
  exact Fintype.card_congr
    (permCycleQuotientEquiv I.toEquiv B.map.faceSucc C.map.faceSucc I.face_comm)

/-- Helper toward Definition 3.8. Euler characteristic is invariant under a
full finite-ball isomorphism. -/
theorem D39BallIso.eulerChar_eq {B C : D39FiniteBall} (I : D39BallIso B C) :
    B.map.eulerChar = C.map.eulerChar := by
  unfold CombinatorialMap.eulerChar
  rw [I.numVertices_eq, I.numEdges_eq, I.numFaces_eq]

/-- Helper toward Definition 3.8. The positive-radius genus-zero condition is
preserved by a rooted whole-map isomorphism. -/
theorem D39RootedMapIso.positiveBallGenusZero_iff
    {M N : D39RootedMap} (I : D39RootedMapIso M N)
    (r : ℕ) (hr : 0 < r) :
    D39BallGenusZero M r ↔ D39BallGenusZero N r := by
  classical
  have heuler := I.ballIso r hr |>.eulerChar_eq
  have heuler' : (d39BallMap M r).eulerChar = (d39BallMap N r).eulerChar := by
    exact heuler
  change (d39BallMap M r).eulerChar = 2 ↔
    (d39BallMap N r).eulerChar = 2
  rw [heuler']

/-- Helper toward Definition 3.8. The whole-map setoid relation on the planar
wrapper preserves every positive-radius genus-zero condition. -/
theorem D39PlanarRootedMap.setoid_preserves_positiveBallGenusZero
    {M N : D39PlanarRootedMap}
    (hMN : D39PlanarRootedMap.setoid.r M N)
    (r : ℕ) (hr : 0 < r) :
    D39BallGenusZero M.toD39RootedMap r ↔
      D39BallGenusZero N.toD39RootedMap r := by
  rcases hMN with ⟨I⟩
  exact I.positiveBallGenusZero_iff r hr

end DirectedDistances.PlanarMap
