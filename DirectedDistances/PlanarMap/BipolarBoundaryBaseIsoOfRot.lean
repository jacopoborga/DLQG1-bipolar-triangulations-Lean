/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIso
public import DirectedDistances.PlanarMap.BipolarCanonicalTrees
public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock




public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}

omit [DecidableEq D] [Fintype D'] [DecidableEq D'] in
private theorem sameCycle_map (e : D ≃ D') (f : Equiv.Perm D)
    (f' : Equiv.Perm D') (hcomm : ∀ x, e (f x) = f' (e x))
    {x y : D} (hxy : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle f' (e x) (e y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have hpow : ∀ (n : ℕ) (x : D), e ((f ^ n) x) = (f' ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (f x)).trans (congrArg (f' ^ n) (hcomm x))
  calc
    (f' ^ n) (e x) = e ((f ^ n) x) := (hpow n x).symm
    _ = e y := congrArg e hn

private theorem rot_symm_comm_of_rot
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d)) (d : D) :
    e (B.map.toCombinatorialMap.rot.symm d) =
      B'.map.toCombinatorialMap.rot.symm (e d) := by
  apply B'.map.toCombinatorialMap.rot.injective
  calc
    B'.map.toCombinatorialMap.rot (e (B.map.toCombinatorialMap.rot.symm d)) =
        e (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.rot.symm d)) :=
      (hrot _).symm
    _ = e d := by simp
    _ = B'.map.toCombinatorialMap.rot
        (B'.map.toCombinatorialMap.rot.symm (e d)) := by simp

/-- Rot and edge-involution preservation imply preservation of face succession.
not the paper result. -/
theorem bipolarFaceSucc_comm_of_rot_edgeInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d)) (d : D) :
    e (B.map.toCombinatorialMap.faceSucc d) =
      B'.map.toCombinatorialMap.faceSucc (e d) := by
  simp [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    rot_symm_comm_of_rot B B' e hrot, hinv]

/-- A dart equivalence commuting with face succession maps each face orbit to
a face orbit. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarFaceOrbit_map_of_rot_edgeInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    {d d' : D}
    (hface : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d d') :
    Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc (e d) (e d') :=
  sameCycle_map e B.map.toCombinatorialMap.faceSucc
    B'.map.toCombinatorialMap.faceSucc
    (bipolarFaceSucc_comm_of_rot_edgeInv B B' e hrot hinv) hface

/-- Face-orbit membership is reflected as well as preserved by the dart
equivalence. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarFaceOrbit_iff_of_rot_edgeInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    {d d' : D} :
    Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d d' ↔
      Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc (e d) (e d') := by
  constructor
  · exact bipolarFaceOrbit_map_of_rot_edgeInv B B' e hrot hinv
  · intro h
    have hcomm := bipolarFaceSucc_comm_of_rot_edgeInv B B' e hrot hinv
    have hback : ∀ x,
        e.symm (B'.map.toCombinatorialMap.faceSucc x) =
          B.map.toCombinatorialMap.faceSucc (e.symm x) := by
      intro x
      simpa using (congrArg e.symm (hcomm (e.symm x))).symm
    have h' := sameCycle_map e.symm B'.map.toCombinatorialMap.faceSucc
      B.map.toCombinatorialMap.faceSucc hback h
    simpa using h'

/-- A dart equivalence commuting with rotation induces an equivalence of
vertex orbits. Helper toward `thm-kmsw` (unrooted classes, -/
noncomputable def bipolarBaseVertexEquiv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d)) :
    MapVertex B.map ≃ MapVertex B'.map :=
  bipolarBoundaryVertexEquiv B B' e hrot

/-- The vertex equivalence carries the initial vertex of each dart to the
initial vertex of its image. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarBaseVertexEquiv_dartTailVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d)) (d : D) :
    bipolarBaseVertexEquiv B B' e hrot (dartTailVertex B.map d) =
      dartTailVertex B'.map (e d) := by
  simp [dartTailVertex, bipolarBaseVertexEquiv, bipolarBoundaryVertexEquiv]

/-- The vertex equivalence carries the terminal vertex of each dart to the
terminal vertex of its image. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarBaseVertexEquiv_dartHeadVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d)) (d : D) :
    bipolarBaseVertexEquiv B B' e hrot (dartHeadVertex B.map d) =
      dartHeadVertex B'.map (e d) := by
  simp [dartHeadVertex, bipolarBaseVertexEquiv,
    bipolarBoundaryVertexEquiv, hinv]

/-- With missing darts excluded on both base carriers, tail preservation
transports directed steps in both directions. Helper toward `thm-kmsw`
result. -/
theorem bipolarBaseDirectedStep_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d)
    {u v : MapVertex B.map} :
    B.map.directedStep u v ↔
      B'.map.directedStep (bipolarBaseVertexEquiv B B' e hrot u)
        (bipolarBaseVertexEquiv B B' e hrot v) := by
  constructor
  · rintro ⟨d, _, hd, hu, hv⟩
    refine ⟨e d, B'.noMissingDarts (e d), (htail d).mpr hd, ?_, ?_⟩
    · calc
        dartTailVertex B'.map (e d) =
            bipolarBaseVertexEquiv B B' e hrot (dartTailVertex B.map d) :=
          (bipolarBaseVertexEquiv_dartTailVertex B B' e hrot d).symm
        _ = bipolarBaseVertexEquiv B B' e hrot u :=
          congrArg (bipolarBaseVertexEquiv B B' e hrot) hu
    · calc
        dartHeadVertex B'.map (e d) =
            bipolarBaseVertexEquiv B B' e hrot (dartHeadVertex B.map d) :=
          (bipolarBaseVertexEquiv_dartHeadVertex B B' e hrot hinv d).symm
        _ = bipolarBaseVertexEquiv B B' e hrot v :=
          congrArg (bipolarBaseVertexEquiv B B' e hrot) hv
  · rintro ⟨d', _, hd', hu', hv'⟩
    refine ⟨e.symm d', B.noMissingDarts (e.symm d'), ?_, ?_, ?_⟩
    · exact (htail (e.symm d')).mp (by simpa using hd')
    · apply (bipolarBaseVertexEquiv B B' e hrot).injective
      calc
        bipolarBaseVertexEquiv B B' e hrot
            (dartTailVertex B.map (e.symm d')) = dartTailVertex B'.map d' := by
          simpa using bipolarBaseVertexEquiv_dartTailVertex B B' e hrot
            (e.symm d')
        _ = bipolarBaseVertexEquiv B B' e hrot u := hu'
    · apply (bipolarBaseVertexEquiv B B' e hrot).injective
      calc
        bipolarBaseVertexEquiv B B' e hrot
            (dartHeadVertex B.map (e.symm d')) = dartHeadVertex B'.map d' := by
          simpa using bipolarBaseVertexEquiv_dartHeadVertex B B' e hrot hinv
            (e.symm d')
        _ = bipolarBaseVertexEquiv B B' e hrot v := hv'

/-- Directed-step preservation sends the unique source to the unique
source. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarBaseVertexEquiv_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d) :
    bipolarBaseVertexEquiv B B' e hrot B.source = B'.source := by
  apply B'.source_unique
  intro h
  rcases h with ⟨u, hu⟩
  have hback : B.map.directedStep
      ((bipolarBaseVertexEquiv B B' e hrot).symm u) B.source := by
    apply (bipolarBaseDirectedStep_iff B B' e hrot hinv htail).mpr
    simpa using hu
  exact B.isSource ⟨_, hback⟩

/-- Directed-step preservation sends the unique sink to the unique sink.
Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarBaseVertexEquiv_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d) :
    bipolarBaseVertexEquiv B B' e hrot B.sink = B'.sink := by
  apply B'.sink_unique
  intro h
  rcases h with ⟨v, hv⟩
  have hback : B.map.directedStep B.sink
      ((bipolarBaseVertexEquiv B B' e hrot).symm v) := by
    apply (bipolarBaseDirectedStep_iff B B' e hrot hinv htail).mpr
    simpa using hv
  exact B.isSink ⟨_, hback⟩

/-- A matched outer dart suffices to preserve membership in the outer face
orbit for every dart. Helper toward `thm-kmsw` (unrooted classes, -/
theorem bipolarOuter_iff_of_matchedOuterDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    {d₀ : D} (hd₀ : B.map.IsOuter d₀)
    (hedge : B'.map.IsOuter (e d₀)) (d : D) :
    B'.map.IsOuter (e d) ↔ B.map.IsOuter d := by
  have hanchorMap : Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      (e B.map.outer) (e d₀) :=
    (bipolarFaceOrbit_iff_of_rot_edgeInv B B' e hrot hinv).mp hd₀
  have hanchor : Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      (e B.map.outer) B'.map.outer := by
    exact hanchorMap.trans hedge.symm
  constructor
  · intro hd
    apply (bipolarFaceOrbit_iff_of_rot_edgeInv B B' e hrot hinv).mpr
    change Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      B'.map.outer (e d) at hd
    exact hanchor.trans hd
  · intro hd
    change Equiv.Perm.SameCycle B'.map.toCombinatorialMap.faceSucc
      B'.map.outer (e d)
    exact hanchor.symm.trans
      ((bipolarFaceOrbit_iff_of_rot_edgeInv B B' e hrot hinv).mp hd)

private theorem simplePath_dart_eq_first_of_tail_source
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (hk : 0 < k) {d : D}
    (hd : d ∈ P.darts) (hsource : dartTailVertex M d = s) :
    d = P.darts.get ⟨0, by rw [P.darts_length]; exact hk⟩ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hstep := P.edge_step i
  have hvertex : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = s := by
    calc
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex M (P.darts.get i) := hstep.2.2.1
      _ = dartTailVertex M d := congrArg (dartTailVertex M) hi
      _ = s := hsource
  have hi0 : i.val = 0 := by
    by_contra hne
    have hget : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
        P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
      calc
        _ = s := hvertex
        _ = _ := P.start_vertex.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hget
    have hval : i.val = 0 := by simpa using congrArg Fin.val hidx
    exact hne hval
  have hifin : i = ⟨0, by rw [P.darts_length]; exact hk⟩ := Fin.ext hi0
  rw [hifin] at hi
  exact hi.symm

private theorem outer_tail_at_source_eq_firstLeft
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (houter : B.map.IsOuter d) (htail : B.map.tail d)
    (hsource : dartTailVertex B.map d = B.source) :
    d = B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr houter
  have hcanon : d ∈ canonicalOuterBoundaryDarts B := by
    simpa [canonicalOuterBoundaryDarts] using
      B.outerSplit.2.1.perm.mem_iff.mp hword
  rcases List.mem_append.mp hcanon with hleft | hright
  · exact simplePath_dart_eq_first_of_tail_source B.leftPath
      (Nat.zero_lt_of_lt B.left_length_pos) hleft hsource
  · obtain ⟨x, hx, hxd⟩ := List.mem_map.mp hright
    have hx' : x ∈ B.rightPath.darts := List.mem_reverse.mp hx
    have hxtail : B.map.tail x := by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx'
      rw [← hi]
      exact (B.rightPath.edge_step i).2.1
    have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv x) :=
      (B.map.tail_iff x (B.noMissingDarts x)).mp hxtail
    exact (hnot (hxd ▸ htail)).elim

/-- Once the first left dart is identified, face succession and the source
corner determine both ordered boundary paths. Helper toward `thm-kmsw`
result. -/
theorem bipolarBoundaryPaths_map_of_firstLeft
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (hfirst : e (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
      B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos)) :
    B.leftPath.darts.map e = B'.leftPath.darts ∧
      B.rightPath.darts.map e = B'.rightPath.darts := by
  have hleftIdx : ∀ i (hi : i < ℓ),
      e (B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; omega)) =
        B'.leftPath.darts[i]'(by rw [B'.leftPath.darts_length]; omega) := by
    intro i hi
    induction i with
    | zero =>
      simpa [SimpleDirectedDartPath.firstDart] using hfirst
    | succ i ih =>
      have hip : i < ℓ := by omega
      have hprev := ih hip
      have hs := outerFace_leftPath_successor B i (by omega)
      have hs' := outerFace_leftPath_successor B' i (by omega)
      calc
        e (B.leftPath.darts[i + 1]'(by rw [B.leftPath.darts_length]; omega)) =
            e (B.map.toCombinatorialMap.faceSucc
              (B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; omega))) :=
          congrArg e hs.symm
        _ = B'.map.toCombinatorialMap.faceSucc
            (e (B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; omega))) :=
          bipolarFaceSucc_comm_of_rot_edgeInv B B' e hrot hinv _
        _ = B'.map.toCombinatorialMap.faceSucc
            (B'.leftPath.darts[i]'(by rw [B'.leftPath.darts_length]; omega)) :=
          congrArg B'.map.toCombinatorialMap.faceSucc hprev
        _ = B'.leftPath.darts[i + 1]'(by rw [B'.leftPath.darts_length]; omega) := hs'
  have hleft : B.leftPath.darts.map e = B'.leftPath.darts := by
    apply List.ext_getElem
    · simp [B.leftPath.darts_length, B'.leftPath.darts_length]
    · intro i hi hi'
      have hiℓ : i < ℓ := by simpa [B.leftPath.darts_length] using hi
      simpa using hleftIdx i hiℓ
  have hfirstRight : e (B.rightPath.firstDart
      (Nat.zero_lt_of_lt B.right_length_pos)) =
        B'.rightPath.firstDart (Nat.zero_lt_of_lt B'.right_length_pos) := by
    have hcorner := outerFace_sourceCorner_eq_firstLeftDart B
    have hcorner' := outerFace_sourceCorner_eq_firstLeftDart B'
    have hrotFirst : B.map.toCombinatorialMap.rot
        (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
          B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
      have hs : B.map.toCombinatorialMap.rot.symm
          (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)) =
            B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
        simpa [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
          B.map.toCombinatorialMap.edgeInv_invol] using hcorner
      have h := congrArg B.map.toCombinatorialMap.rot hs
      simpa using h.symm
    have hrotFirst' : B'.map.toCombinatorialMap.rot
        (B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos)) =
          B'.rightPath.firstDart (Nat.zero_lt_of_lt B'.right_length_pos) := by
      have hs : B'.map.toCombinatorialMap.rot.symm
          (B'.rightPath.firstDart (Nat.zero_lt_of_lt B'.right_length_pos)) =
            B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos) := by
        simpa [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
          B'.map.toCombinatorialMap.edgeInv_invol] using hcorner'
      have h := congrArg B'.map.toCombinatorialMap.rot hs
      simpa using h.symm
    calc
      e (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)) =
          e (B.map.toCombinatorialMap.rot
            (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos))) :=
        congrArg e hrotFirst.symm
      _ = B'.map.toCombinatorialMap.rot
          (e (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos))) :=
        hrot _
      _ = B'.rightPath.firstDart (Nat.zero_lt_of_lt B'.right_length_pos) := by
        rw [hfirst, hrotFirst']
  have hrightIdx : ∀ i (hi : i < r),
      e (B.rightPath.darts[i]'(by rw [B.rightPath.darts_length]; omega)) =
        B'.rightPath.darts[i]'(by rw [B'.rightPath.darts_length]; omega) := by
    intro i hi
    induction i with
    | zero =>
      simpa [SimpleDirectedDartPath.firstDart] using hfirstRight
    | succ i ih =>
      have hip : i < r := by omega
      have hprev := ih hip
      have hs := outerFace_rightPath_successor B i (by omega)
      have hs' := outerFace_rightPath_successor B' i (by omega)
      have hinvNext : e (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega))) =
            B'.map.toCombinatorialMap.edgeInv
              (B'.rightPath.darts[i + 1]'(by rw [B'.rightPath.darts_length]; omega)) := by
        apply B'.map.toCombinatorialMap.faceSucc.injective
        calc
          B'.map.toCombinatorialMap.faceSucc
              (e (B.map.toCombinatorialMap.edgeInv
                (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega)))) =
              e (B.map.toCombinatorialMap.faceSucc
                (B.map.toCombinatorialMap.edgeInv
                  (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega)))) :=
            (bipolarFaceSucc_comm_of_rot_edgeInv B B' e hrot hinv _).symm
          _ = e (B.map.toCombinatorialMap.edgeInv
              (B.rightPath.darts[i]'(by rw [B.rightPath.darts_length]; omega))) :=
            congrArg e hs
          _ = B'.map.toCombinatorialMap.edgeInv
              (B'.rightPath.darts[i]'(by rw [B'.rightPath.darts_length]; omega)) := by
            rw [hinv, hprev]
          _ = B'.map.toCombinatorialMap.faceSucc
              (B'.map.toCombinatorialMap.edgeInv
                (B'.rightPath.darts[i + 1]'(by rw [B'.rightPath.darts_length]; omega))) :=
            hs'.symm
      apply B'.map.toCombinatorialMap.edgeInv.injective
      calc
        B'.map.toCombinatorialMap.edgeInv
            (e (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega))) =
            e (B.map.toCombinatorialMap.edgeInv
              (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega))) :=
          (hinv _).symm
        _ = B'.map.toCombinatorialMap.edgeInv
            (B'.rightPath.darts[i + 1]'(by rw [B'.rightPath.darts_length]; omega)) :=
          hinvNext
  have hright : B.rightPath.darts.map e = B'.rightPath.darts := by
    apply List.ext_getElem
    · simp [B.rightPath.darts_length, B'.rightPath.darts_length]
    · intro i hi hi'
      have hiℓ : i < r := by simpa [B.rightPath.darts_length] using hi
      simpa using hrightIdx i hiℓ
  exact ⟨hleft, hright⟩

private noncomputable def bipolarBoundaryBaseIsoOfMatchedOuterDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d)
    {d₀ : D} (hd₀ : B.map.IsOuter d₀)
    (hedge : B'.map.IsOuter (e d₀)) : BipolarBoundaryBaseIso B B' := by
  let V := bipolarBaseVertexEquiv B B' e hrot
  have houter := bipolarOuter_iff_of_matchedOuterDart B B' e hrot hinv hd₀ hedge
  have hsource := bipolarBaseVertexEquiv_source B B' e hrot hinv htail
  have hsink := bipolarBaseVertexEquiv_sink B B' e hrot hinv htail
  have hfirstInfo : B.map.tail
      (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) ∧
      dartTailVertex B.map
        (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) = B.source := by
    have h := B.leftPath.edge_step
      ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩
    constructor
    · simpa [SimpleDirectedDartPath.firstDart] using h.2.1
    · simpa [SimpleDirectedDartPath.firstDart] using
        h.2.2.1.symm.trans B.leftPath.start_vertex
  have hfirst : e (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
      B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos) := by
    apply outer_tail_at_source_eq_firstLeft B'
    · have hleftMem : B.leftPath.firstDart
          (Nat.zero_lt_of_lt B.left_length_pos) ∈ B.leftPath.darts := by
        unfold SimpleDirectedDartPath.firstDart
        exact List.get_mem _ _
      have hout := canonicalOuterBoundaryDarts_mem_isOuter B
        (by
          change B.leftPath.firstDart
              (Nat.zero_lt_of_lt B.left_length_pos) ∈ B.leftPath.darts ++ _
          exact List.mem_append.mpr (Or.inl hleftMem))
      exact (houter _).mpr hout
    · exact (htail _).mpr hfirstInfo.1
    · calc
        dartTailVertex B'.map
            (e (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos))) =
            V (dartTailVertex B.map
              (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos))) :=
          (bipolarBaseVertexEquiv_dartTailVertex B B' e hrot _).symm
        _ = V B.source := congrArg V hfirstInfo.2
        _ = B'.source := hsource
  have hpaths := bipolarBoundaryPaths_map_of_firstLeft B B' e hrot hinv hfirst
  exact
    { toEquiv := e
      rot_comm := hrot
      edgeInv_comm := hinv
      missing_iff := by
        intro d
        simp [B.noMissingDarts d, B'.noMissingDarts (e d)]
      tail_iff := htail
      outer_iff := fun d => houter d
      source_map := by
        intro d
        constructor
        · intro hd
          calc
            dartTailVertex B'.map (e d) = V (dartTailVertex B.map d) :=
              (bipolarBaseVertexEquiv_dartTailVertex B B' e hrot d).symm
            _ = V B.source := congrArg V hd
            _ = B'.source := hsource
        · intro hd
          apply V.injective
          calc
            V (dartTailVertex B.map d) = dartTailVertex B'.map (e d) :=
              bipolarBaseVertexEquiv_dartTailVertex B B' e hrot d
            _ = B'.source := hd
            _ = V B.source := hsource.symm
      sink_map := by
        intro d
        constructor
        · intro hd
          calc
            dartTailVertex B'.map (e d) = V (dartTailVertex B.map d) :=
              (bipolarBaseVertexEquiv_dartTailVertex B B' e hrot d).symm
            _ = V B.sink := congrArg V hd
            _ = B'.sink := hsink
        · intro hd
          apply V.injective
          calc
            V (dartTailVertex B.map d) = dartTailVertex B'.map (e d) :=
              bipolarBaseVertexEquiv_dartTailVertex B B' e hrot d
            _ = B'.sink := hd
            _ = V B.sink := hsink.symm
      leftDarts := hpaths.1
      rightDarts := hpaths.2 }

/-- Upgrade a dart equivalence preserving rot, edgeInv and tail, with one
matched outer dart, to the unrooted base-map isomorphism relation. Helper -/
noncomputable def bipolarBoundaryBaseIsoOfRot
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d)
    (houter : ∃ d₀, B.map.IsOuter d₀ ∧ B'.map.IsOuter (e d₀)) :
    BipolarBoundaryBaseIso B B' := by
  let d₀ := Classical.choose houter
  have hd₀ := Classical.choose_spec houter
  exact bipolarBoundaryBaseIsoOfMatchedOuterDart B B' e hrot hinv htail
    hd₀.1 hd₀.2

/-- The KMSW root condition, mapping the final left-boundary dart, supplies
the outer-face anchor needed for `bipolarBoundaryBaseIsoOfRot`. Helper toward -/
noncomputable def bipolarBoundaryBaseIsoOfRotOfLastLeft
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r)
    (e : D ≃ D')
    (hrot : ∀ d, e (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (e d))
    (hinv : ∀ d, e (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (e d))
    (htail : ∀ d, B'.map.tail (e d) ↔ B.map.tail d)
    (hroot : e (pathLastDart B.leftPath
      (Nat.zero_lt_of_lt B.left_length_pos)) =
      pathLastDart B'.leftPath (Nat.zero_lt_of_lt B'.left_length_pos)) :
    BipolarBoundaryBaseIso B B' := by
  have hleftOuter : B.map.IsOuter (pathLastDart B.leftPath
      (Nat.zero_lt_of_lt B.left_length_pos)) := by
    apply canonicalOuterBoundaryDarts_mem_isOuter B
    change pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) ∈
      B.leftPath.darts ++ _
    apply List.mem_append.mpr
    left
    unfold pathLastDart
    exact List.get_mem _ _
  have hrightOuter : B'.map.IsOuter (pathLastDart B'.leftPath
      (Nat.zero_lt_of_lt B'.left_length_pos)) := by
    apply canonicalOuterBoundaryDarts_mem_isOuter B'
    change pathLastDart B'.leftPath (Nat.zero_lt_of_lt B'.left_length_pos) ∈
      B'.leftPath.darts ++ _
    apply List.mem_append.mpr
    left
    unfold pathLastDart
    exact List.get_mem _ _
  apply bipolarBoundaryBaseIsoOfRot B B' e hrot hinv htail
  exact ⟨pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos),
    hleftOuter, hroot ▸ hrightOuter⟩




