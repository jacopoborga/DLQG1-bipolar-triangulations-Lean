/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointClass
public import DirectedDistances.PlanarMap.KMSWRightEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled

/-! # Reversing the right endpoint on the KMSW map class

paper result.

The reversal used here is the restricted endpoint case of `lem-bdy-reverse`
(`(1,ℓ)` to `(ℓ,1)`). That inverse direction is the S7-inverse item, which -/

public section
namespace DirectedDistances.PlanarMap

variable {ℓ n : ℕ}

/-- Apply the restricted right endpoint reversal to the general base carrier
of a boundary-channeled `(1,ℓ)` representative. Helper toward -/
@[expose] noncomputable def kmswRightEndpointReverseStrong
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    BipolarTriangulationWithBoundary (Fin R.dartCount) ℓ 1 :=
  (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
    (toBoundaryMbcClassRightEndpoint R.B hℓ hbc)).val

/-- Apply the restricted right endpoint reversal to a boundary-channeled
`(1,ℓ)` representative, retaining its dart type and total edge count. Helper -/
@[expose] noncomputable def kmswRightEndpointReverseRep
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    KMSWMapRep ℓ 1 n := by
  refine ⟨R.dartCount, (kmswRightEndpointReverseStrong R hℓ hbc).toBase, ?_⟩
  change (kmswRightEndpointReverseStrong R hℓ hbc).map.toCombinatorialMap.numEdges = n
  let C := toBoundaryMbcClassRightEndpoint R.B hℓ hbc
  have hk : 1 ≤ ℓ - 1 := by omega
  have hkl : ℓ - 1 < ℓ := by omega
  have hleft : 1 + (ℓ - 1) = ℓ := by omega
  have hright : ℓ - (ℓ - 1) = 1 := by omega
  have hcount := rightPrefixReversal_numEdges C.val (ℓ - 1) hk hkl C.property
  have hcast := boundaryMbcClassEquiv_numEdges hleft hright
    (rightPrefixReversalMbc (D := Fin R.dartCount) (ℓ := 1) (r := ℓ)
      (ℓ - 1) hk hkl C)
  have hcount' :
      (kmswRightEndpointReverseStrong R hℓ hbc).map.toCombinatorialMap.numEdges =
      R.B.map.toCombinatorialMap.numEdges := by
    change (boundaryMbcClassEquiv (D := Fin R.dartCount) hleft hright
      (rightPrefixReversalMbc (D := Fin R.dartCount) (ℓ := 1) (r := ℓ)
        (ℓ - 1) hk hkl C)).val.map.toCombinatorialMap.numEdges = _
    exact hcast.trans hcount
  exact hcount'.trans R.edges

/-- The reversed representative remains channeled on the general base
not the paper result. -/
theorem kmswRightEndpointReverseRep_isChanneled
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    (kmswRightEndpointReverseRep R hℓ hbc).IsChanneled := by
  change (kmswRightEndpointReverseStrong R hℓ hbc).toBase.IsBoundaryChanneledBase
  exact BipolarTriangulationWithBoundary.isBoundaryChanneledBase_toBase _
    (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
      (toBoundaryMbcClassRightEndpoint R.B hℓ hbc)).property

/-- Right reversal after left reversal returns a base-isomorphic channeled
`(ℓ,1)` representative. Helper toward `lem-kmsw-left` -/
theorem kmswRightEndpointReverseRep_left_roundTrip
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ) (hbc : R.IsBoundaryChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswRightEndpointReverseRep (kmswLeftEndpointReverseRep R hℓ hbc) hℓ
        (kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc)).B R.B) := by
  let C := toBoundaryMbcClassLeftEndpoint R.B hℓ hbc
  let L := kmswLeftEndpointReverseRep R hℓ hbc
  have hclass :
      toBoundaryMbcClassRightEndpoint L.B hℓ
        (kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc) =
      leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ C := by
    apply Subtype.ext
    change toStrongRightEndpoint
        ((leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ C).val.toBase) hℓ =
      (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ C).val
    let B := (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ C).val
    change toStrongRightEndpoint B.toBase hℓ = B
    cases B
    rfl
  have hback :
      rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
        (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ C) = C := by
    rw [← leftEndpointReversalEquiv_symm (D := Fin R.dartCount) (l := ℓ) hℓ]
    exact (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ).symm_apply_apply C
  have hround :
      rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
        (toBoundaryMbcClassRightEndpoint L.B hℓ
          (kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc)) = C :=
    (congrArg (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ)
      hclass).trans hback
  have hCbase : C.val.toBase = R.B := by
    dsimp [C, toBoundaryMbcClassLeftEndpoint, toStrongLeftEndpoint]
    simp
  have hbase :
      (kmswRightEndpointReverseRep (kmswLeftEndpointReverseRep R hℓ hbc) hℓ
        (kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc)).B = R.B := by
    change (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
      (toBoundaryMbcClassRightEndpoint L.B hℓ
        (kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc))).val.toBase = R.B
    rw [hround]
    exact hCbase
  rw [hbase]
  exact ⟨BipolarBoundaryBaseIso.refl R.B⟩

/-- Left reversal after right reversal returns a base-isomorphic channeled
`(1,ℓ)` representative. Helper toward `lem-kmsw-left` -/
theorem kmswLeftEndpointReverseRep_right_roundTrip
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswLeftEndpointReverseRep (kmswRightEndpointReverseRep R hℓ hbc) hℓ
        (by
          exact (KMSWMapRep.isChanneled_iff_isBoundaryChanneled
            (kmswRightEndpointReverseRep R hℓ hbc)).mp
            (kmswRightEndpointReverseRep_isChanneled R hℓ hbc))).B R.B) := by
  let C := toBoundaryMbcClassRightEndpoint R.B hℓ hbc
  let S := kmswRightEndpointReverseRep R hℓ hbc
  have hSbc : S.IsBoundaryChanneled := by
    exact (KMSWMapRep.isChanneled_iff_isBoundaryChanneled S).mp
      (kmswRightEndpointReverseRep_isChanneled R hℓ hbc)
  have hclass :
      toBoundaryMbcClassLeftEndpoint S.B hℓ hSbc =
        rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ C := by
    apply Subtype.ext
    change toStrongLeftEndpoint
        ((rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ C).val.toBase) hℓ =
      (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ C).val
    let B := (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ C).val
    change toStrongLeftEndpoint B.toBase hℓ = B
    cases B
    rfl
  have hback :
      leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ
        (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ C) = C := by
    exact leftEndpointReversalEquiv_comp_rightEndpointReversalEquiv
      (D := Fin R.dartCount) (l := ℓ) hℓ C
  have hround :
      leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ
        (toBoundaryMbcClassLeftEndpoint S.B hℓ hSbc) = C :=
    (congrArg (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ)
      hclass).trans hback
  have hCbase : C.val.toBase = R.B := by
    dsimp [C, toBoundaryMbcClassRightEndpoint, toStrongRightEndpoint]
    simp
  have hbase :
      (kmswLeftEndpointReverseRep S hℓ hSbc).B = R.B := by
    change (leftEndpointReversalEquiv (D := Fin R.dartCount) (l := ℓ) hℓ
      (toBoundaryMbcClassLeftEndpoint S.B hℓ hSbc)).val.toBase = R.B
    rw [hround]
    exact hCbase
  rw [hbase]
  exact ⟨BipolarBoundaryBaseIso.refl R.B⟩

private theorem list_getD_map {α β : Type*} (f : α → β)
    (xs : List α) (k : ℕ) (d : α) :
    (xs.map f).getD k (f d) = f (xs.getD k d) := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih => cases k with
    | zero => rfl
    | succ k => exact ih k

private theorem list_getD_eq_get {α : Type*} : ∀ (xs : List α)
    (i : Fin xs.length) (d : α), xs.getD i.val d = xs.get i := by
  intro xs
  induction xs with
  | nil => intro i; exact Fin.elim0 i
  | cons x xs ih =>
    intro i d
    cases i with
    | mk n hn =>
      cases n with
      | zero => rfl
      | succ n =>
        have hlen : n < xs.length := by simpa using hn
        let j : Fin xs.length := ⟨n, hlen⟩
        simpa [List.getD, j] using ih j d

private theorem rightPrefixReversal_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (B' : BipolarTriangulationWithBoundary D' a b)
    (I : BipolarBoundaryBaseIso B.toBase B'.toBase)
    (hk : 1 ≤ k) (hkb : k < b)
    (hbc : B.IsBoundaryChanneled) (hbc' : B'.IsBoundaryChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      (rightPrefixReversal B k hk hkb hbc).toBase
      (rightPrefixReversal B' k hk hkb hbc').toBase) := by
  let C := rightPrefixReversal B k hk hkb hbc
  let C' := rightPrefixReversal B' k hk hkb hbc'
  have hpath : I.transportPath B.toBase.rightPath = B'.toBase.rightPath := by
    apply SimpleDirectedDartPath.eq_of_darts_eq
    rw [BipolarBoundaryBaseIso.transportPath_darts, I.rightDarts]
  have hverts : B.toBase.rightPath.vertices.map I.vertexEquiv =
      B'.toBase.rightPath.vertices := by
    have hv := congrArg SimpleDirectedDartPath.vertices hpath
    simpa [BipolarBoundaryBaseIso.transportPath,
      BipolarTriangulationWithBoundary.toBase] using hv
  have hsource : I.vertexEquiv C.source = C'.source := by
    rw [rightPrefixReversal_source, rightPrefixReversal_source]
    have hv := congrArg (fun xs : List (MapVertex B'.toBase.map) =>
      xs.getD k (I.vertexEquiv B.toBase.source)) hverts
    have hget := list_getD_map I.vertexEquiv B.toBase.rightPath.vertices k
      B.toBase.source
    rw [hget] at hv
    have hi : k < B.rightPath.vertices.length := by
      rw [B.rightPath.vertices_length]
      omega
    have hi' : k < B'.rightPath.vertices.length := by
      rw [B'.rightPath.vertices_length]
      omega
    have hgetLeft : B.toBase.rightPath.vertices.getD k B.toBase.source =
        B.toBase.rightPath.vertices.get ⟨k, hi⟩ :=
      list_getD_eq_get _ ⟨k, hi⟩ B.toBase.source
    have hgetRight : B'.toBase.rightPath.vertices.getD k (I.vertexEquiv B.toBase.source) =
        B'.toBase.rightPath.vertices.get ⟨k, hi'⟩ :=
      list_getD_eq_get _ ⟨k, hi'⟩ (I.vertexEquiv B.toBase.source)
    rw [hgetLeft, hgetRight] at hv
    simpa [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.toBase] using hv
  have hsink : I.vertexEquiv C.sink = C'.sink := by
    rw [rightPrefixReversal_sink, rightPrefixReversal_sink]
    exact I.vertexEquiv_sink
  have hInv (d : D) : I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := by
    change I.toEquiv (B.toBase.map.toCombinatorialMap.edgeInv d) =
      B'.toBase.map.toCombinatorialMap.edgeInv (I.toEquiv d)
    exact I.edgeInv_comm d
  have hsel (d : D) : d ∈ rightPrefixFlipDarts B k ↔
      I.toEquiv d ∈ rightPrefixFlipDarts B' k := by
    have htake : B'.rightPath.darts.take k =
        (B.rightPath.darts.take k).map I.toEquiv := by
      change B'.toBase.rightPath.darts.take k =
        (B.toBase.rightPath.darts.take k).map I.toEquiv
      rw [← I.rightDarts, ← List.map_take]
    simp only [rightPrefixFlipDarts, rightBoundaryPrefixDarts,
      Set.mem_ofPred_eq]
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
      (rightPrefixFlipDarts B k) (rightPrefixFlip_condition B k) :=
    rightPrefixReversal_map B k hk hkb hbc
  have hmapC' : C'.map = flipOrientation B'.map
      (rightPrefixFlipDarts B' k) (rightPrefixFlip_condition B' k) :=
    rightPrefixReversal_map B' k hk hkb hbc'
  have hcombC : C.map.toCombinatorialMap = B.map.toCombinatorialMap := by
    rw [hmapC, flipOrientation_toCombinatorialMap]
  have hcombC' : C'.map.toCombinatorialMap = B'.map.toCombinatorialMap := by
    rw [hmapC', flipOrientation_toCombinatorialMap]
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
    rw [hmapC', hmapC, flipOrientation_missing, flipOrientation_missing]
    exact I.missing_iff d
  · intro d
    change C'.map.tail (I.toEquiv d) ↔ C.map.tail d
    rw [hmapC', hmapC]
    by_cases hd : d ∈ rightPrefixFlipDarts B k
    · rw [flipOrientation_tail_of_mem B.map _ (rightPrefixFlip_condition B k) d hd,
        flipOrientation_tail_of_mem B'.map _ (rightPrefixFlip_condition B' k)
          (I.toEquiv d) ((hsel d).mp hd)]
      have hi := I.tail_iff (B.map.toCombinatorialMap.edgeInv d)
      have hInv : I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
          B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := by
        change I.toEquiv (B.toBase.map.toCombinatorialMap.edgeInv d) =
          B'.toBase.map.toCombinatorialMap.edgeInv (I.toEquiv d)
        exact I.edgeInv_comm d
      rw [hInv] at hi
      simpa [BipolarTriangulationWithBoundary.toBase] using hi
    · have hd' : I.toEquiv d ∉ rightPrefixFlipDarts B' k := by
        intro h
        exact hd ((hsel d).mpr h)
      rw [flipOrientation_tail_of_not_mem B.map _
          (rightPrefixFlip_condition B k) d hd,
        flipOrientation_tail_of_not_mem B'.map _
          (rightPrefixFlip_condition B' k) (I.toEquiv d) hd']
      exact I.tail_iff d
  · intro d
    change C'.map.IsOuter (I.toEquiv d) ↔ C.map.IsOuter d
    rw [hmapC', hmapC, flipOrientation_isOuter_iff, flipOrientation_isOuter_iff]
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
    rw [rightPrefixReversal_leftPath_darts, rightPrefixReversal_leftPath_darts]
    have hleftDarts : B.leftPath.darts.map I.toEquiv = B'.leftPath.darts := by
      change B.toBase.leftPath.darts.map I.toEquiv = B'.toBase.leftPath.darts
      exact I.leftDarts
    have hrightDarts : B.rightPath.darts.map I.toEquiv = B'.rightPath.darts := by
      change B.toBase.rightPath.darts.map I.toEquiv = B'.toBase.rightPath.darts
      exact I.rightDarts
    have htake : (B.rightPath.darts.take k).map I.toEquiv =
        B'.rightPath.darts.take k := by
      rw [List.map_take, hrightDarts]
    have hflipPrefix :
        ((B.rightPath.darts.take k).reverse.map
          B.map.toCombinatorialMap.edgeInv).map I.toEquiv =
        (B'.rightPath.darts.take k).reverse.map
          B'.map.toCombinatorialMap.edgeInv := by
      calc
        _ = (B.rightPath.darts.take k).reverse.map
            (fun d => I.toEquiv (B.map.toCombinatorialMap.edgeInv d)) := by
              simp [List.map_map, Function.comp_def]
        _ = (B.rightPath.darts.take k).reverse.map
            (fun d => B'.map.toCombinatorialMap.edgeInv (I.toEquiv d)) := by
              apply List.map_congr_left
              intro d hd
              exact hInv d
        _ = (B'.rightPath.darts.take k).reverse.map
            B'.map.toCombinatorialMap.edgeInv := by
              have hmiddle :
                  (B.rightPath.darts.take k).reverse.map
                      (fun d => B'.map.toCombinatorialMap.edgeInv (I.toEquiv d)) =
                    ((B.rightPath.darts.take k).map I.toEquiv).reverse.map
                      B'.map.toCombinatorialMap.edgeInv := by
                simp [List.map_reverse, List.map_map, Function.comp_def]
              rw [hmiddle, htake]
    rw [List.map_append, hflipPrefix, hleftDarts]
  · change C.rightPath.darts.map I.toEquiv = C'.rightPath.darts
    rw [rightPrefixReversal_rightPath_darts, rightPrefixReversal_rightPath_darts]
    have hrightDarts : B.rightPath.darts.map I.toEquiv = B'.rightPath.darts := by
      change B.toBase.rightPath.darts.map I.toEquiv = B'.toBase.rightPath.darts
      exact I.rightDarts
    rw [List.map_drop, hrightDarts]

private theorem boundaryMbcClassEquiv_baseIso
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

/-- The restricted right endpoint reversal transports across an isomorphism
of channeled representatives, using the same dart equivalence. Helper toward -/
theorem kmswRightEndpointReverseRep_iso
    {ℓ n : ℕ} (hℓ : 2 ≤ ℓ) (R R' : KMSWMapRep 1 ℓ n)
    (hbc : R.IsChanneled) (hbc' : R'.IsChanneled)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswRightEndpointReverseRep R hℓ hbc).B
      (kmswRightEndpointReverseRep R' hℓ hbc').B) := by
  let B := toStrongRightEndpoint R.B hℓ
  let B' := toStrongRightEndpoint R'.B hℓ
  let C := toBoundaryMbcClassRightEndpoint R.B hℓ hbc
  let C' := toBoundaryMbcClassRightEndpoint R'.B hℓ hbc'
  have hbcB : B.IsBoundaryChanneled := by
    exact (isBoundaryChanneledBase_iff_toStrongRightEndpoint R.B hℓ).mp hbc
  have hbcB' : B'.IsBoundaryChanneled := by
    exact (isBoundaryChanneledBase_iff_toStrongRightEndpoint R'.B hℓ).mp hbc'
  have hrev := rightPrefixReversal_baseIso (B := B) (B' := B') (I := I)
    (k := ℓ - 1) (by omega) (by omega) hbcB hbcB'
  change Nonempty (BipolarBoundaryBaseIso
    (rightEndpointReversalEquiv (D := Fin R.dartCount) (r := ℓ) hℓ
      (toBoundaryMbcClassRightEndpoint R.B hℓ hbc)).val.toBase
    (rightEndpointReversalEquiv (D := Fin R'.dartCount) (r := ℓ) hℓ
      (toBoundaryMbcClassRightEndpoint R'.B hℓ hbc')).val.toBase)
  rcases hrev with ⟨J⟩
  have hcast := boundaryMbcClassEquiv_baseIso
    (D := Fin R.dartCount) (D' := Fin R'.dartCount)
    (a := 1 + (ℓ - 1)) (b := ℓ - (ℓ - 1)) (c := ℓ) (d := 1)
    (by omega) (by omega)
    (rightPrefixReversalMbc (D := Fin R.dartCount) (ℓ := 1) (r := ℓ)
      (ℓ - 1) (by omega) (by omega) C)
    (rightPrefixReversalMbc (D := Fin R'.dartCount) (ℓ := 1) (r := ℓ)
      (ℓ - 1) (by omega) (by omega) C') J
  simpa only [rightEndpointReversalEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, C, C'] using hcast

end DirectedDistances.PlanarMap
