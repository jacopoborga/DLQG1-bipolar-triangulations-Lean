/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointClassIso

/-! # Naturality of the restricted left endpoint reversal

restricted reversal carrier; S7-inverse direction; simple-boundary restriction not assumed; not the
paper result. -/

public section
namespace DirectedDistances.PlanarMap

private theorem list_getD_map_nat {α β : Type*} (f : α → β)
    (xs : List α) (n : ℕ) (d : α) :
    (xs.map f).getD n (f d) = f (xs.getD n d) := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih => cases n with
    | zero => rfl
    | succ n => exact ih n

private theorem list_getD_eq_get_nat {α : Type*} (xs : List α)
    (i : Fin xs.length) (d : α) : xs.getD i.val d = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i with
    | mk n hn =>
      cases n with
      | zero => rfl
      | succ n =>
        have hlen : n < xs.length := by simpa using hn
        let j : Fin xs.length := ⟨n, hlen⟩
        simpa [List.getD, j] using ih j

@[simp] private theorem mirrorVertexMap_mirrorVertexMap_nat
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (v : MapVertex M) :
    DirectedMapWithMissing.mirrorVertexMap M.mirror
      (DirectedMapWithMissing.mirrorVertexMap M v) = v := by
  rw [DirectedMapWithMissing.mirrorVertexMap_eq M.mirror,
    DirectedMapWithMissing.mirrorVertexMap_eq M]
  obtain ⟨d, hd⟩ := Quotient.exists_rep v
  have hv : v = dartTailVertex M d := by
    simpa [dartTailVertex] using hd.symm
  rw [hv]
  rw [DirectedMapWithMissing.mirror_dartTailVertex M d,
    DirectedMapWithMissing.mirror_dartTailVertex M.mirror d]
  cases M with
  | mk C missing hm tail ht htm outer ho => rfl

private theorem leftPrefixReversal_source_nat
    {D : Type*} [Fintype D] [DecidableEq D] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).source =
      B.leftPath.vertices.get ⟨k, by rw [B.leftPath.vertices_length]; omega⟩ := by
  change DirectedMapWithMissing.mirrorVertexMap B.mirror.map
    (rightPrefixReversal B.mirror k hk hka
      (B.mirror_isBoundaryChanneled hbc)).source = _
  rw [rightPrefixReversal_source (B := B.mirror) (k := k) hk hka
    (B.mirror_isBoundaryChanneled hbc)]
  simp [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.mirror,
    DirectedMapWithMissing.SimpleDirectedDartPath.mirror]
  rfl

private theorem leftPrefixReversal_sink_nat
    {D : Type*} [Fintype D] [DecidableEq D] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).sink = B.sink := by
  change DirectedMapWithMissing.mirrorVertexMap B.mirror.map
    (rightPrefixReversal B.mirror k hk hka
      (B.mirror_isBoundaryChanneled hbc)).sink = _
  rw [rightPrefixReversal_sink (B := B.mirror) (k := k) hk hka
    (B.mirror_isBoundaryChanneled hbc)]
  simp [BipolarTriangulationWithBoundary.mirror]
  rfl

/-- Restricted left-prefix reversal transports across a base-carrier
isomorphism with the same dart equivalence. Helper toward `lem-kmsw-left`
S7-inverse direction; simple-boundary restriction not assumed; not the paper result. -/
theorem leftPrefixReversal_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (B' : BipolarTriangulationWithBoundary D' a b)
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase)
    (hk : 1 ≤ k) (hka : k < a)
    (hbc : B.IsBoundaryChanneled) (hbc' : B'.IsBoundaryChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      (leftPrefixReversal B k hk hka hbc).toBase
      (leftPrefixReversal B' k hk hka hbc').toBase) := by
  let C := leftPrefixReversal B k hk hka hbc
  let C' := leftPrefixReversal B' k hk hka hbc'
  have hpath : I.transportPath B.toBase.leftPath = B'.toBase.leftPath := by
    apply SimpleDirectedDartPath.eq_of_darts_eq
    rw [BipolarBoundaryBaseIso.transportPath_darts, I.leftDarts]
  have hverts : B.toBase.leftPath.vertices.map I.vertexEquiv =
      B'.toBase.leftPath.vertices := by
    have hv := congrArg SimpleDirectedDartPath.vertices hpath
    simpa [BipolarBoundaryBaseIso.transportPath,
      BipolarTriangulationWithBoundary.toBase] using hv
  have hsource : I.vertexEquiv C.source = C'.source := by
    rw [leftPrefixReversal_source_nat, leftPrefixReversal_source_nat]
    have hv := congrArg (fun xs : List (MapVertex B'.toBase.map) =>
      xs.getD k (I.vertexEquiv B.toBase.source)) hverts
    have hget := list_getD_map_nat I.vertexEquiv B.toBase.leftPath.vertices k
      B.toBase.source
    rw [hget] at hv
    have hi : k < B.leftPath.vertices.length := by
      rw [B.leftPath.vertices_length]
      omega
    have hi' : k < B'.leftPath.vertices.length := by
      rw [B'.leftPath.vertices_length]
      omega
    have hgetLeft : B.toBase.leftPath.vertices.getD k B.toBase.source =
        B.toBase.leftPath.vertices.get ⟨k, hi⟩ :=
      list_getD_eq_get_nat _ ⟨k, hi⟩ B.toBase.source
    have hgetRight : B'.toBase.leftPath.vertices.getD k
        (I.vertexEquiv B.toBase.source) =
        B'.toBase.leftPath.vertices.get ⟨k, hi'⟩ :=
      list_getD_eq_get_nat _ ⟨k, hi'⟩ (I.vertexEquiv B.toBase.source)
    rw [hgetLeft, hgetRight] at hv
    simpa only [BipolarTriangulationWithBoundary.toBase] using hv
  have hsink : I.vertexEquiv C.sink = C'.sink := by
    rw [leftPrefixReversal_sink_nat, leftPrefixReversal_sink_nat]
    exact I.vertexEquiv_sink
  have hInv (d : D) : I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := by
    change I.toEquiv (B.toBase.map.toCombinatorialMap.edgeInv d) =
      B'.toBase.map.toCombinatorialMap.edgeInv (I.toEquiv d)
    exact I.edgeInv_comm d
  have hsel (d : D) : d ∈ rightPrefixFlipDarts B.mirror k ↔
      I.toEquiv d ∈ rightPrefixFlipDarts B'.mirror k := by
    have htake : B'.leftPath.darts.take k =
        (B.leftPath.darts.take k).map I.toEquiv := by
      change B'.toBase.leftPath.darts.take k =
        (B.toBase.leftPath.darts.take k).map I.toEquiv
      rw [← I.leftDarts, ← List.map_take]
    change (d ∈ B.leftPath.darts.take k ∨
      B.map.toCombinatorialMap.edgeInv d ∈ B.leftPath.darts.take k) ↔
      (I.toEquiv d ∈ B'.leftPath.darts.take k ∨
        B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) ∈
          B'.leftPath.darts.take k)
    rw [htake]
    constructor
    · rintro (hd | hd)
      · exact Or.inl (List.mem_map.mpr ⟨d, hd, rfl⟩)
      · exact Or.inr (List.mem_map.mpr
          ⟨B.map.toCombinatorialMap.edgeInv d, hd, hInv d⟩)
    · rintro (hd | hd)
      · rcases List.mem_map.mp hd with ⟨e, he, heq⟩
        exact Or.inl ((I.toEquiv.injective heq) ▸ he)
      · rcases List.mem_map.mp hd with ⟨e, he, heq⟩
        have hback : B.map.toCombinatorialMap.edgeInv d = e := by
          apply I.toEquiv.injective
          calc
            I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
                B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := hInv d
            _ = I.toEquiv e := heq.symm
        exact Or.inr (by simpa [hback] using he)
  have hmapC : C.map = flipOrientation B.map
      (rightPrefixFlipDarts B.mirror k)
      (rightPrefixFlip_condition B.mirror k) :=
    leftPrefixReversal_map B k hk hka hbc
  have hmapC' : C'.map = flipOrientation B'.map
      (rightPrefixFlipDarts B'.mirror k)
      (rightPrefixFlip_condition B'.mirror k) :=
    leftPrefixReversal_map B' k hk hka hbc'
  have hSB : (∀ d, d ∈ rightPrefixFlipDarts B.mirror k →
      B.map.toCombinatorialMap.edgeInv d ∈ rightPrefixFlipDarts B.mirror k) ∧
      (∀ d, d ∈ rightPrefixFlipDarts B.mirror k → ¬ B.map.missing d) := by
    simpa [BipolarTriangulationWithBoundary.mirror,
      DirectedMapWithMissing.mirror, CombinatorialMap.mirror] using
      rightPrefixFlip_condition B.mirror k
  have hSB' : (∀ d, d ∈ rightPrefixFlipDarts B'.mirror k →
      B'.map.toCombinatorialMap.edgeInv d ∈ rightPrefixFlipDarts B'.mirror k) ∧
      (∀ d, d ∈ rightPrefixFlipDarts B'.mirror k → ¬ B'.map.missing d) := by
    simpa [BipolarTriangulationWithBoundary.mirror,
      DirectedMapWithMissing.mirror, CombinatorialMap.mirror] using
      rightPrefixFlip_condition B'.mirror k
  refine ⟨{
    toEquiv := I.toEquiv
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    outer_iff := ?_
    source_map := ?_
    sink_map := ?_
    leftDarts := ?_
    rightDarts := ?_ }⟩
  · intro d
    change I.toEquiv (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (I.toEquiv d)
    exact I.rot_comm d
  · intro d
    change I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (I.toEquiv d)
    exact I.edgeInv_comm d
  · intro d
    change C'.map.missing (I.toEquiv d) ↔ C.map.missing d
    rw [hmapC', hmapC]
    rw [flipOrientation_missing B'.map _ hSB',
      flipOrientation_missing B.map _ hSB]
    exact I.missing_iff d
  · intro d
    change C'.map.tail (I.toEquiv d) ↔ C.map.tail d
    rw [hmapC', hmapC]
    by_cases hd : d ∈ rightPrefixFlipDarts B.mirror k
    · rw [flipOrientation_tail_of_mem B.map _ hSB d hd,
        flipOrientation_tail_of_mem B'.map _ hSB' (I.toEquiv d)
          ((hsel d).mp hd)]
      have hi := I.tail_iff (B.map.toCombinatorialMap.edgeInv d)
      rw [hInv] at hi
      simpa only [BipolarTriangulationWithBoundary.toBase] using hi
    · have hd' : I.toEquiv d ∉ rightPrefixFlipDarts B'.mirror k := by
        intro h
        exact hd ((hsel d).mpr h)
      rw [flipOrientation_tail_of_not_mem B.map _ hSB d hd,
        flipOrientation_tail_of_not_mem B'.map _ hSB' (I.toEquiv d) hd']
      exact I.tail_iff d
  · intro d
    change C'.map.IsOuter (I.toEquiv d) ↔ C.map.IsOuter d
    rw [hmapC', hmapC]
    rw [flipOrientation_isOuter_iff B'.map _ hSB' (I.toEquiv d),
      flipOrientation_isOuter_iff B.map _ hSB d]
    exact I.outer_iff d
  · intro d
    change (dartTailVertex B.toBase.map d = C.source) ↔
      (dartTailVertex B'.toBase.map (I.toEquiv d) = C'.source)
    constructor
    · intro hd
      have hh := congrArg I.vertexEquiv hd
      rw [I.vertexEquiv_dartTailVertex, hsource] at hh
      exact hh
    · intro hd
      apply I.vertexEquiv.injective
      rw [I.vertexEquiv_dartTailVertex, hsource, hd]
  · intro d
    change (dartTailVertex B.toBase.map d = C.sink) ↔
      (dartTailVertex B'.toBase.map (I.toEquiv d) = C'.sink)
    constructor
    · intro hd
      have hh := congrArg I.vertexEquiv hd
      rw [I.vertexEquiv_dartTailVertex, hsink] at hh
      exact hh
    · intro hd
      apply I.vertexEquiv.injective
      rw [I.vertexEquiv_dartTailVertex, hsink, hd]
  · change C.leftPath.darts.map I.toEquiv = C'.leftPath.darts
    exact leftPrefixReversal_leftPath_darts_map B B' I hk hka hbc hbc'
  · change C.rightPath.darts.map I.toEquiv = C'.rightPath.darts
    exact leftPrefixReversal_rightPath_darts_map B B' I hk hka hbc hbc'

private def toStrongLeftEndpoint_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ 1)
    (hℓ : 2 ≤ ℓ) (I : BipolarBoundaryBaseIso B B') :
    BipolarBoundaryBaseIso
      (toStrongLeftEndpoint B hℓ).toBase
      (toStrongLeftEndpoint B' hℓ).toBase where
  toEquiv := I.toEquiv
  rot_comm := by intro d; exact I.rot_comm d
  edgeInv_comm := by intro d; exact I.edgeInv_comm d
  missing_iff := by intro d; exact I.missing_iff d
  tail_iff := by intro d; exact I.tail_iff d
  outer_iff := by intro d; exact I.outer_iff d
  source_map := by intro d; exact I.source_map d
  sink_map := by intro d; exact I.sink_map d
  leftDarts := I.leftDarts
  rightDarts := I.rightDarts

private theorem boundaryMbcClassEquiv_baseIso_nat
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b c d : ℕ}
    (ha : a = c) (hb : b = d)
    (B : BoundaryMbcClass D a b) (B' : BoundaryMbcClass D' a b)
    (I : BipolarBoundaryBaseIso B.val.toBase B'.val.toBase) :
    Nonempty (BipolarBoundaryBaseIso
      (boundaryMbcClassEquiv (D := D) ha hb B).val.toBase
      (boundaryMbcClassEquiv (D := D') ha hb B').val.toBase) := by
  cases ha
  cases hb
  exact ⟨I⟩

/-- The representative-level restricted left endpoint reversal transports
under a KMSW base isomorphism. Helper toward `lem-kmsw-left`
S7-inverse direction; simple-boundary restriction not assumed; not the paper result. -/
theorem kmswLeftEndpointReverseRep_iso
    {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (R R' : KMSWMapRep ℓ 1 n)
    (hbc : R.IsBoundaryChanneled) (hbc' : R'.IsBoundaryChanneled)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswLeftEndpointReverseRep R hℓ hbc).B
      (kmswLeftEndpointReverseRep R' hℓ hbc').B) := by
  let C := toBoundaryMbcClassLeftEndpoint R.B hℓ hbc
  let C' := toBoundaryMbcClassLeftEndpoint R'.B hℓ hbc'
  have J := toStrongLeftEndpoint_baseIso R.B R'.B hℓ I
  have hk : 1 ≤ ℓ - 1 := by omega
  have hka : ℓ - 1 < ℓ := by omega
  have hleft : ℓ - (ℓ - 1) = 1 := by omega
  have hright : 1 + (ℓ - 1) = ℓ := by omega
  have hrev := leftPrefixReversal_baseIso C.val C'.val J hk hka
    C.property C'.property
  change Nonempty (BipolarBoundaryBaseIso
    (leftEndpointReversalEquiv (D := Fin R.dartCount) hℓ C).val.toBase
    (leftEndpointReversalEquiv (D := Fin R'.dartCount) hℓ C').val.toBase)
  rcases hrev with ⟨Irev⟩
  have Irev' : BipolarBoundaryBaseIso
      (leftPrefixReversalMbc (D := Fin R.dartCount) (a := ℓ) (b := 1)
        (ℓ - 1) hk hka C).val.toBase
      (leftPrefixReversalMbc (D := Fin R'.dartCount) (a := ℓ) (b := 1)
        (ℓ - 1) hk hka C').val.toBase := by
    simpa only [leftPrefixReversalMbc] using Irev
  have hcast := boundaryMbcClassEquiv_baseIso_nat
    (D := Fin R.dartCount) (D' := Fin R'.dartCount)
    (a := ℓ - (ℓ - 1)) (b := 1 + (ℓ - 1)) (c := 1) (d := ℓ)
    hleft hright
    (leftPrefixReversalMbc (D := Fin R.dartCount) (a := ℓ) (b := 1)
      (ℓ - 1) hk hka C)
    (leftPrefixReversalMbc (D := Fin R'.dartCount) (a := ℓ) (b := 1)
      (ℓ - 1) hk hka C') Irev'
  simpa only [leftEndpointReversalEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, C, C'] using hcast

private noncomputable def kmswLeftEndpointReverseClassOption
    {ℓ n : ℕ} (hℓ : 2 ≤ ℓ) :
    KMSWMapIsoClass ℓ 1 n → Option (KMSWMapIsoClass 1 ℓ n) := by
  classical
  exact KMSWMapIsoClass.lift
    (fun R : KMSWMapRep ℓ 1 n =>
      if hbc : R.IsBoundaryChanneled then
        some (KMSWMapIsoClass.mk (kmswLeftEndpointReverseRep R hℓ hbc))
      else none)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      have hiff := KMSWMapRep.isBoundaryChanneled_iff_of_iso R R' I
      by_cases hbc : R.IsBoundaryChanneled
      · have hbc' : R'.IsBoundaryChanneled := hiff.mp hbc
        have hrev := kmswLeftEndpointReverseRep_iso hℓ R R' hbc hbc' I
        have hclass := (KMSWMapIsoClass.mk_eq_mk_iff
          (kmswLeftEndpointReverseRep R hℓ hbc)
          (kmswLeftEndpointReverseRep R' hℓ hbc')).2 hrev
        simp only [dite_eq_left hbc, dite_eq_left hbc']
        exact congrArg some hclass
      · have hbc' : ¬ R'.IsBoundaryChanneled := by
          intro hh
          exact hbc (hiff.mpr hh)
        simp only [dite_eq_right hbc, dite_eq_right hbc'])

/-- The restricted left endpoint operation descends to isomorphism classes
of boundary-channeled representatives. Helper toward `lem-kmsw-left`
S7-inverse direction; simple-boundary restriction not assumed; not the paper result. -/
noncomputable def kmswLeftEndpointReverseClass
    {ℓ n : ℕ} (hℓ : 2 ≤ ℓ) :
    {q : KMSWMapIsoClass ℓ 1 n // q.IsBoundaryChanneled} →
      {q : KMSWMapIsoClass 1 ℓ n // q.IsBoundaryChanneledBase} := by
  classical
  intro q
  let repWitness := Quotient.exists_rep q.val
  let R := Classical.choose repWitness
  have hrep := Classical.choose_spec repWitness
  have hchanClass : (KMSWMapIsoClass.mk R).IsBoundaryChanneled :=
    (congrArg (fun x : KMSWMapIsoClass ℓ 1 n => x.IsBoundaryChanneled)
      hrep.symm).mp q.property
  have hbc : R.IsBoundaryChanneled :=
    (KMSWMapIsoClass.isBoundaryChanneled_mk R).mp hchanClass
  have hrawMk : kmswLeftEndpointReverseClassOption hℓ
      (KMSWMapIsoClass.mk R) =
      some (KMSWMapIsoClass.mk (kmswLeftEndpointReverseRep R hℓ hbc)) := by
    rw [kmswLeftEndpointReverseClassOption, KMSWMapIsoClass.lift_mk]
    simp only [dite_eq_left hbc]
  have hraw : kmswLeftEndpointReverseClassOption hℓ q.val =
      some (KMSWMapIsoClass.mk (kmswLeftEndpointReverseRep R hℓ hbc)) :=
    (congrArg (kmswLeftEndpointReverseClassOption hℓ) hrep.symm).trans hrawMk
  let hex : ∃ r, kmswLeftEndpointReverseClassOption hℓ q.val = some r :=
    ⟨KMSWMapIsoClass.mk (kmswLeftEndpointReverseRep R hℓ hbc), hraw⟩
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  have heq : r = KMSWMapIsoClass.mk
      (kmswLeftEndpointReverseRep R hℓ hbc) :=
    Option.some.inj (hr.symm.trans hraw)
  refine ⟨r, ?_⟩
  rw [heq, KMSWMapIsoClass.isBoundaryChanneledBase_mk]
  exact kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc

end DirectedDistances.PlanarMap
