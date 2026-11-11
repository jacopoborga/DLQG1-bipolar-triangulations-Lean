module

public import DirectedDistances.PlanarMap.KMSWMapSimpleBoundary
public import DirectedDistances.PlanarMap.RightPrefixReversalNat
public import DirectedDistances.PlanarMap.KMSWRightEndpointClass

public section
namespace DirectedDistances.PlanarMap

open BipolarTriangulationWithBoundary

private theorem boundaryMbcClassEquiv_baseIso_local
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

private theorem boundaryMbcClassEquiv_val_local
    {D : Type*} [Fintype D] [DecidableEq D] {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv (D := D) ha hb B).val =
      cast (by cases ha; cases hb; rfl) B.val := by
  cases ha
  cases hb
  rfl

private theorem rightPrefixReversalMbc_transport_local
    {D : Type*} [Fintype D] [DecidableEq D] {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b)
    (k : ℕ) (hk : 1 ≤ k) (hkb : k < b) (hkd : k < d) :
    rightPrefixReversalMbc (D := D) (ℓ := c) (r := d) k hk hkd
        (boundaryMbcClassEquiv (D := D) ha hb B) =
      boundaryMbcClassEquiv (D := D)
        (congrArg (fun x => x + k) ha) (congrArg (fun x => x - k) hb)
        (rightPrefixReversalMbc (D := D) (ℓ := a) (r := b) k hk hkb B) := by
  cases ha
  cases hb
  rfl

namespace KMSWMapRep

variable {ℓ r n : ℕ}

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
@[expose] noncomputable def kmswRightPrefixReverseRep
    (R : KMSWMapRep ℓ r n) (k : ℕ) (_hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hkr : k < r) (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    KMSWMapRep (ℓ + k) (r - k) n := by
  let B := R.toStrongMbc hs hc
  refine ⟨R.dartCount, (rightPrefixReversalMbc k hk hkr B).val.toBase, ?_⟩
  change (rightPrefixReversal B.val k hk hkr B.property).map.toCombinatorialMap.numEdges = n
  calc
    (rightPrefixReversal B.val k hk hkr B.property).map.toCombinatorialMap.numEdges =
        B.val.map.toCombinatorialMap.numEdges :=
      rightPrefixReversal_numEdges B.val k hk hkr B.property
    _ = R.B.map.toCombinatorialMap.numEdges := by
      change (R.toStrong hs).map.toCombinatorialMap.numEdges = _
      have h := congrArg
        (fun X : BipolarTriangulationWithBoundaryBase (Fin R.dartCount) ℓ r =>
          X.map.toCombinatorialMap.numEdges) (R.toStrong_toBase hs)
      exact h
    _ = n := R.edges

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReverseRep_isChanneled
    (R : KMSWMapRep ℓ r n) (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hkr : k < r) (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc).IsChanneled := by
  let B := R.toStrongMbc hs hc
  let C := rightPrefixReversalMbc k hk hkr B
  change (C.val.toBase).IsBoundaryChanneledBase
  exact BipolarTriangulationWithBoundary.isBoundaryChanneledBase_toBase _
    C.property

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReverseRep_isSimpleOuterBoundary
    (R : KMSWMapRep ℓ r n) (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hkr : k < r) (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc).IsSimpleOuterBoundary := by
  let B := R.toStrongMbc hs hc
  let C := rightPrefixReversalMbc k hk hkr B
  change (∀ v, v ∈ (C.val.toBase).leftPath.vertices →
      v ∈ (C.val.toBase).rightPath.vertices →
      v = (C.val.toBase).source ∨ v = (C.val.toBase).sink) ∧
    (∀ d, d ∈ (C.val.toBase).leftPath.darts →
      ∀ e, e ∈ (C.val.toBase).rightPath.darts →
      ¬ Equiv.Perm.SameCycle (C.val.toBase.map.toCombinatorialMap.edgeInv) d e)
  exact ⟨C.val.paths_internally_vertex_disjoint, C.val.paths_edge_disjoint⟩

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
@[expose] noncomputable def kmswLeftPrefixReverseRep
    (k : ℕ) (R : KMSWMapRep (ℓ + k) (r - k) n) (hℓ : 1 ≤ ℓ)
    (hk : 1 ≤ k) (hkr : k < r)
    (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    KMSWMapRep ℓ r n := by
  let B := R.toStrongMbc hs hc
  let C := boundaryMbcClassEquiv (D := Fin R.dartCount)
    (show (ℓ + k) - k = ℓ by omega)
    (show (r - k) + k = r by omega)
    (leftPrefixReversalMbc k hk (by omega) B)
  refine ⟨R.dartCount, C.val.toBase, ?_⟩
  change C.val.map.toCombinatorialMap.numEdges = n
  have hcast := boundaryMbcClassEquiv_numEdges
    (show (ℓ + k) - k = ℓ by omega) (show (r - k) + k = r by omega)
    (leftPrefixReversalMbc k hk (by omega) B)
  have hrev := leftPrefixReversal_numEdges B.val hk (by omega) B.property
  calc
    C.val.map.toCombinatorialMap.numEdges =
        ((leftPrefixReversalMbc k hk (by omega) B).val.map.toCombinatorialMap.numEdges) :=
      hcast
    _ = B.val.map.toCombinatorialMap.numEdges := hrev
    _ = n := by
      change (R.toStrong hs).map.toCombinatorialMap.numEdges = n
      have h := congrArg
        (fun X : BipolarTriangulationWithBoundaryBase (Fin R.dartCount)
            (ℓ + k) (r - k) => X.map.toCombinatorialMap.numEdges)
        (R.toStrong_toBase hs)
      exact h.trans R.edges

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswLeftPrefixReverseRep_isChanneled
    (k : ℕ) (R : KMSWMapRep (ℓ + k) (r - k) n) (hℓ : 1 ≤ ℓ)
    (hk : 1 ≤ k) (hkr : k < r)
    (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    (kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc).IsChanneled := by
  let B := R.toStrongMbc hs hc
  let C := leftPrefixReversalMbc k hk (by omega) B
  let D := boundaryMbcClassEquiv (D := Fin R.dartCount)
    (show (ℓ + k) - k = ℓ by omega)
    (show (r - k) + k = r by omega) C
  change D.val.toBase.IsBoundaryChanneledBase
  exact BipolarTriangulationWithBoundary.isBoundaryChanneledBase_toBase
    D.val D.property

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswLeftPrefixReverseRep_isSimpleOuterBoundary
    (k : ℕ) (R : KMSWMapRep (ℓ + k) (r - k) n) (hℓ : 1 ≤ ℓ)
    (hk : 1 ≤ k) (hkr : k < r)
    (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    (kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc).IsSimpleOuterBoundary := by
  let B := R.toStrongMbc hs hc
  let C := leftPrefixReversalMbc k hk (by omega) B
  let D := boundaryMbcClassEquiv (D := Fin R.dartCount)
    (show (ℓ + k) - k = ℓ by omega)
    (show (r - k) + k = r by omega) C
  constructor
  · intro v hvL hvR
    exact D.val.paths_internally_vertex_disjoint v hvL hvR
  · intro d hdL e heR
    exact D.val.paths_edge_disjoint d hdL e heR

end KMSWMapRep

namespace KMSWMapRep

variable {ℓ r n : ℕ}

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReverseRep_iso
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (R R' : KMSWMapRep ℓ r n)
    (hs : R.IsSimpleOuterBoundary) (hs' : R'.IsSimpleOuterBoundary)
    (hc : R.IsChanneled) (hc' : R'.IsChanneled)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (BipolarBoundaryBaseIso
      (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc).B
      (R'.kmswRightPrefixReverseRep k hℓ hk hkr hs' hc').B) := by
  let B := R.toStrongMbc hs hc
  let B' := R'.toStrongMbc hs' hc'
  have I' : BipolarBoundaryBaseIso B.val.toBase B'.val.toBase := by
    change BipolarBoundaryBaseIso (R.toStrong hs).toBase (R'.toStrong hs').toBase
    simpa only [R.toStrong_toBase, R'.toStrong_toBase] using I
  have h := rightPrefixReversal_baseIso_public B.val B'.val I' hk hkr
    B.property B'.property
  exact h

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswLeftPrefixReverseRep_iso
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (R R' : KMSWMapRep (ℓ + k) (r - k) n)
    (hs : R.IsSimpleOuterBoundary) (hs' : R'.IsSimpleOuterBoundary)
    (hc : R.IsChanneled) (hc' : R'.IsChanneled)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc).B
      (kmswLeftPrefixReverseRep k R' hℓ hk hkr hs' hc').B) := by
  let B := R.toStrongMbc hs hc
  let B' := R'.toStrongMbc hs' hc'
  have I' : BipolarBoundaryBaseIso B.val.toBase B'.val.toBase := by
    change BipolarBoundaryBaseIso (R.toStrong hs).toBase (R'.toStrong hs').toBase
    simpa only [R.toStrong_toBase, R'.toStrong_toBase] using I
  have h := leftPrefixReversal_baseIso B.val B'.val I' hk (by omega)
    B.property B'.property
  have hcst := boundaryMbcClassEquiv_baseIso_local
    (D := Fin R.dartCount) (D' := Fin R'.dartCount)
    (show (ℓ + k) - k = ℓ by omega) (show (r - k) + k = r by omega)
    (leftPrefixReversalMbc k hk (by omega) B)
    (leftPrefixReversalMbc k hk (by omega) B') (Classical.choice h)
  exact hcst

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result.
The left-prefix inverse after the right-prefix map returns a base-isomorphic
representative. -/
theorem kmswLeftPrefixReverseRep_right_roundTrip
    (R : KMSWMapRep ℓ r n) (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hkr : k < r) (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      (kmswLeftPrefixReverseRep k
        (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc) hℓ hk hkr
        (R.kmswRightPrefixReverseRep_isSimpleOuterBoundary k hℓ hk hkr hs hc)
        (R.kmswRightPrefixReverseRep_isChanneled k hℓ hk hkr hs hc)).B R.B) := by
  let S := R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc
  have hsS := R.kmswRightPrefixReverseRep_isSimpleOuterBoundary
    k hℓ hk hkr hs hc
  have hcS := R.kmswRightPrefixReverseRep_isChanneled k hℓ hk hkr hs hc
  let B := R.toStrongMbc hs hc
  let C := rightPrefixReversalMbc k hk hkr B
  have hSC : S.toStrongMbc hsS hcS = C := by
    apply Subtype.ext
    change (C.val.toBase).toStrong hsS.1 hsS.2 = C.val
    exact BipolarTriangulationWithBoundaryBase.toBase_toStrong C.val hsS.1 hsS.2
  let T := kmswLeftPrefixReverseRep k S hℓ hk hkr hsS hcS
  let hL : (ℓ + k) - k = ℓ := by omega
  let hR : (r - k) + k = r := by omega
  have hround := leftPrefixReversal_rightPrefixReversal B.val k hk hkr B.property
  have hval :
      (boundaryMbcClassEquiv (D := Fin R.dartCount) hL hR
        (leftPrefixReversalMbc k hk (by omega) C)).val = B.val := by
    rw [boundaryMbcClassEquiv_val_local]
    dsimp only [leftPrefixReversalMbc, rightPrefixReversalMbc]
    change cast _ (leftPrefixReversal
      (rightPrefixReversal B.val k hk hkr B.property) k hk
      (by have := B.val.left_length_pos; omega)
      (rightPrefixReversal_isBoundaryChanneled B.val k hk hkr B.property)) = B.val
    rw [hround]
    simp
  have hbase : T.B = R.B := by
    change (boundaryMbcClassEquiv (D := Fin R.dartCount) hL hR
      (leftPrefixReversalMbc k hk (by omega) (S.toStrongMbc hsS hcS))).val.toBase =
        R.B
    rw [hSC, hval]
    exact R.toStrong_toBase hs
  rw [hbase]
  exact ⟨BipolarBoundaryBaseIso.refl R.B⟩

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result.
The right-prefix map after its left-prefix inverse returns a base-isomorphic
representative. -/
theorem kmswRightPrefixReverseRep_left_roundTrip
    (k : ℕ) (R : KMSWMapRep (ℓ + k) (r - k) n) (hℓ : 1 ≤ ℓ)
    (hk : 1 ≤ k) (hkr : k < r)
    (hs : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    Nonempty (BipolarBoundaryBaseIso
      ((kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc).kmswRightPrefixReverseRep
        k hℓ hk hkr
        (R.kmswLeftPrefixReverseRep_isSimpleOuterBoundary k hℓ hk hkr hs hc)
        (R.kmswLeftPrefixReverseRep_isChanneled k hℓ hk hkr hs hc)).B R.B) := by
  let B := R.toStrongMbc hs hc
  let C := leftPrefixReversalMbc k hk (by omega) B
  let hL : (ℓ + k) - k = ℓ := by omega
  let hR : (r - k) + k = r := by omega
  let E := boundaryMbcClassEquiv (D := Fin R.dartCount) hL hR C
  let T := R.kmswLeftPrefixReverseRep k hℓ hk hkr hs hc
  have hsT := R.kmswLeftPrefixReverseRep_isSimpleOuterBoundary
    k hℓ hk hkr hs hc
  have hcT := R.kmswLeftPrefixReverseRep_isChanneled k hℓ hk hkr hs hc
  have hTE : T.toStrongMbc hsT hcT = E := by
    apply Subtype.ext
    change (E.val.toBase).toStrong hsT.1 hsT.2 = E.val
    exact BipolarTriangulationWithBoundaryBase.toBase_toStrong E.val hsT.1 hsT.2
  have hround := rightPrefixReversal_leftPrefixReversal B.val k hk (by omega)
    B.property
  have htransport := rightPrefixReversalMbc_transport_local hL hR C k hk
    (by omega) (by omega)
  have hclass : rightPrefixReversalMbc k hk hkr E = B := by
    calc
      rightPrefixReversalMbc k hk hkr E =
          boundaryMbcClassEquiv (D := Fin R.dartCount)
            (show ((ℓ + k) - k + k) = ℓ + k by omega)
            (show ((r - k) + k - k) = r - k by omega)
            (rightPrefixReversalMbc k hk (by omega) C) := htransport
      _ = B := by
        apply Subtype.ext
        rw [boundaryMbcClassEquiv_val_local]
        dsimp only [rightPrefixReversalMbc, leftPrefixReversalMbc]
        change cast _ (rightPrefixReversal
          (leftPrefixReversal B.val k hk (by omega) B.property)
          k hk (by omega)
          (leftPrefixReversal_isBoundaryChanneled B.val k hk (by omega)
            B.property)) = B.val
        rw [hround]
        simp
  have hbase :
      (T.kmswRightPrefixReverseRep k hℓ hk hkr hsT hcT).B = R.B := by
    change (rightPrefixReversalMbc (D := Fin R.dartCount) (ℓ := ℓ)
      (r := r) k hk hkr (T.toStrongMbc hsT hcT)).val.toBase = R.B
    rw [hTE]
    change (rightPrefixReversalMbc (D := Fin R.dartCount) (ℓ := ℓ)
      (r := r) k hk hkr E).val.toBase = R.B
    have hB : B.val.toBase = R.B := by
      change (R.toStrong hs).toBase = R.B
      exact R.toStrong_toBase hs
    have hclass' : rightPrefixReversalMbc (D := Fin R.dartCount)
        (ℓ := ℓ) (r := r) k hk hkr E = B := hclass
    rw [hclass']
    exact hB
  rw [hbase]
  exact ⟨BipolarBoundaryBaseIso.refl R.B⟩

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result.
This republishes the two-direction naturality interface used by the
representative-level class assembly. -/
theorem rightLeftPrefixReversalMbc_baseIso_public
    {D D' : Type*} [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] {ℓ r k : ℕ}
    (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (B : {B : BipolarTriangulationWithBoundary D ℓ r // InMbc ℓ r B})
    (B' : {X : BipolarTriangulationWithBoundary D' ℓ r // InMbc ℓ r X})
    (I : BipolarBoundaryBaseIso B.val.toBase B'.val.toBase)
    (C : {C : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) C})
    (C' : {X : BipolarTriangulationWithBoundary D' (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) X})
    (J : BipolarBoundaryBaseIso C.val.toBase C'.val.toBase) :
    Nonempty (BipolarBoundaryBaseIso
      (rightPrefixReversalMbc (D := D) (ℓ := ℓ) (r := r) k hk hkr B).val.toBase
      (rightPrefixReversalMbc (D := D') (ℓ := ℓ) (r := r) k hk hkr B').val.toBase) ∧
    Nonempty (BipolarBoundaryBaseIso
      (leftPrefixReversalMbc (D := D) (a := ℓ + k) (b := r - k) k hk
        (by omega) C).val.toBase
      (leftPrefixReversalMbc (D := D') (a := ℓ + k) (b := r - k) k hk
        (by omega) C').val.toBase) :=
  rightLeftPrefixReversalMbc_baseIso hℓ hk hkr B B' I C C' J

end KMSWMapRep

namespace KMSWMapIsoClass

variable {ℓ r n : ℕ}

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
@[expose] noncomputable def kmswRightPrefixReversalClassMap
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    {q : KMSWMapIsoClass ℓ r n // q.IsChanneled ∧ q.IsSimpleOuterBoundary} →
      {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
        q.IsChanneled ∧ q.IsSimpleOuterBoundary} := by
  classical
  intro q
  let R : KMSWMapRep ℓ r n := Quotient.out q.val
  have hmk : KMSWMapIsoClass.mk R = q.val := Quotient.out_eq q.val
  have hchClass : (KMSWMapIsoClass.mk R).IsChanneled := by
    rw [hmk]
    exact q.property.1
  have hsiClass : (KMSWMapIsoClass.mk R).IsSimpleOuterBoundary := by
    rw [hmk]
    exact q.property.2
  have hc : R.IsChanneled := (KMSWMapIsoClass.isChanneled_mk R).mp hchClass
  have hs : R.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mp hsiClass
  let S := R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc
  refine ⟨KMSWMapIsoClass.mk S, ?_⟩
  exact ⟨(KMSWMapIsoClass.isChanneled_mk S).mpr
      (R.kmswRightPrefixReverseRep_isChanneled k hℓ hk hkr hs hc),
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk S).mpr
      (R.kmswRightPrefixReverseRep_isSimpleOuterBoundary k hℓ hk hkr hs hc)⟩

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result.
The value is the reversal of any representative of the source class, up to
the isomorphism defining the class. -/
theorem kmswRightPrefixReversalClassMap_mk
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (R : KMSWMapRep ℓ r n) (hc : R.IsChanneled)
    (hs : R.IsSimpleOuterBoundary) :
    (kmswRightPrefixReversalClassMap k hℓ hk hkr
      ⟨KMSWMapIsoClass.mk R,
        (KMSWMapIsoClass.isChanneled_mk R).mpr hc,
        (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs⟩).val =
      KMSWMapIsoClass.mk (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc) := by
  classical
  let R₀ : KMSWMapRep ℓ r n := Quotient.out (KMSWMapIsoClass.mk R)
  have hmk : KMSWMapIsoClass.mk R₀ = KMSWMapIsoClass.mk R :=
    Quotient.out_eq (KMSWMapIsoClass.mk R)
  have hchClass : (KMSWMapIsoClass.mk R₀).IsChanneled := by
    rw [hmk]
    exact (KMSWMapIsoClass.isChanneled_mk R).mpr hc
  have hsiClass : (KMSWMapIsoClass.mk R₀).IsSimpleOuterBoundary := by
    rw [hmk]
    exact (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs
  have hc₀ : R₀.IsChanneled :=
    (KMSWMapIsoClass.isChanneled_mk R₀).mp hchClass
  have hs₀ : R₀.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R₀).mp hsiClass
  have hI : Nonempty (BipolarBoundaryBaseIso R₀.B R.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff R₀ R).mp hmk
  change KMSWMapIsoClass.mk
      (R₀.kmswRightPrefixReverseRep k hℓ hk hkr hs₀ hc₀) = _
  apply (KMSWMapIsoClass.mk_eq_mk_iff _ _).2
  exact R₀.kmswRightPrefixReverseRep_iso k hℓ hk hkr R
    hs₀ hs hc₀ hc (Classical.choice hI)

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
@[expose] noncomputable def kmswLeftPrefixReversalClassMap
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} →
      {q : KMSWMapIsoClass ℓ r n // q.IsChanneled ∧ q.IsSimpleOuterBoundary} := by
  classical
  intro q
  let R : KMSWMapRep (ℓ + k) (r - k) n := Quotient.out q.val
  have hmk : KMSWMapIsoClass.mk R = q.val := Quotient.out_eq q.val
  have hchClass : (KMSWMapIsoClass.mk R).IsChanneled := by
    rw [hmk]
    exact q.property.1
  have hsiClass : (KMSWMapIsoClass.mk R).IsSimpleOuterBoundary := by
    rw [hmk]
    exact q.property.2
  have hc : R.IsChanneled := (KMSWMapIsoClass.isChanneled_mk R).mp hchClass
  have hs : R.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mp hsiClass
  let S := KMSWMapRep.kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc
  refine ⟨KMSWMapIsoClass.mk S, ?_⟩
  exact ⟨(KMSWMapIsoClass.isChanneled_mk S).mpr
      (KMSWMapRep.kmswLeftPrefixReverseRep_isChanneled k R hℓ hk hkr hs hc),
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk S).mpr
      (KMSWMapRep.kmswLeftPrefixReverseRep_isSimpleOuterBoundary k R hℓ hk hkr hs hc)⟩

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result.
The value is the left-prefix reversal of any representative, up to class
isomorphism. -/
theorem kmswLeftPrefixReversalClassMap_mk
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (R : KMSWMapRep (ℓ + k) (r - k) n) (hc : R.IsChanneled)
    (hs : R.IsSimpleOuterBoundary) :
    (kmswLeftPrefixReversalClassMap k hℓ hk hkr
      ⟨KMSWMapIsoClass.mk R,
        (KMSWMapIsoClass.isChanneled_mk R).mpr hc,
        (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs⟩).val =
      KMSWMapIsoClass.mk (KMSWMapRep.kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc) := by
  classical
  let R₀ : KMSWMapRep (ℓ + k) (r - k) n :=
    Quotient.out (KMSWMapIsoClass.mk R)
  have hmk : KMSWMapIsoClass.mk R₀ = KMSWMapIsoClass.mk R :=
    Quotient.out_eq (KMSWMapIsoClass.mk R)
  have hchClass : (KMSWMapIsoClass.mk R₀).IsChanneled := by
    rw [hmk]
    exact (KMSWMapIsoClass.isChanneled_mk R).mpr hc
  have hsiClass : (KMSWMapIsoClass.mk R₀).IsSimpleOuterBoundary := by
    rw [hmk]
    exact (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs
  have hc₀ : R₀.IsChanneled :=
    (KMSWMapIsoClass.isChanneled_mk R₀).mp hchClass
  have hs₀ : R₀.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R₀).mp hsiClass
  have hI : Nonempty (BipolarBoundaryBaseIso R₀.B R.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff R₀ R).mp hmk
  change KMSWMapIsoClass.mk
      (KMSWMapRep.kmswLeftPrefixReverseRep k R₀ hℓ hk hkr hs₀ hc₀) = _
  apply (KMSWMapIsoClass.mk_eq_mk_iff _ _).2
  exact R₀.kmswLeftPrefixReverseRep_iso k hℓ hk hkr R
    hs₀ hs hc₀ hc (Classical.choice hI)

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswLeftPrefixReversalClassMap_right_roundTrip
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (q : {q : KMSWMapIsoClass ℓ r n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    kmswLeftPrefixReversalClassMap k hℓ hk hkr
      (kmswRightPrefixReversalClassMap k hℓ hk hkr q) = q := by
  classical
  let R : KMSWMapRep ℓ r n := Quotient.out q.val
  have hmk : KMSWMapIsoClass.mk R = q.val := Quotient.out_eq q.val
  have hcClass : (KMSWMapIsoClass.mk R).IsChanneled := by
    rw [hmk]
    exact q.property.1
  have hsClass : (KMSWMapIsoClass.mk R).IsSimpleOuterBoundary := by
    rw [hmk]
    exact q.property.2
  have hc : R.IsChanneled := (KMSWMapIsoClass.isChanneled_mk R).mp hcClass
  have hs : R.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mp hsClass
  let qR : {q : KMSWMapIsoClass ℓ r n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk R, hcClass, hsClass⟩
  have hq : q = qR := Subtype.ext hmk.symm
  let S := R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc
  have hcS := R.kmswRightPrefixReverseRep_isChanneled k hℓ hk hkr hs hc
  have hsS := R.kmswRightPrefixReverseRep_isSimpleOuterBoundary
    k hℓ hk hkr hs hc
  let qS : {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk S, (KMSWMapIsoClass.isChanneled_mk S).mpr hcS,
      (KMSWMapIsoClass.isSimpleOuterBoundary_mk S).mpr hsS⟩
  have hright : kmswRightPrefixReversalClassMap k hℓ hk hkr qR = qS := by
    apply Subtype.ext
    exact kmswRightPrefixReversalClassMap_mk k hℓ hk hkr R hc hs
  let T := KMSWMapRep.kmswLeftPrefixReverseRep k S hℓ hk hkr hsS hcS
  have hcT := KMSWMapRep.kmswLeftPrefixReverseRep_isChanneled
    k S hℓ hk hkr hsS hcS
  have hsT := KMSWMapRep.kmswLeftPrefixReverseRep_isSimpleOuterBoundary
    k S hℓ hk hkr hsS hcS
  let qT : {q : KMSWMapIsoClass ℓ r n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk T, (KMSWMapIsoClass.isChanneled_mk T).mpr hcT,
      (KMSWMapIsoClass.isSimpleOuterBoundary_mk T).mpr hsT⟩
  have hleft : kmswLeftPrefixReversalClassMap k hℓ hk hkr qS = qT := by
    apply Subtype.ext
    exact kmswLeftPrefixReversalClassMap_mk k hℓ hk hkr S hcS hsS
  have hrep := KMSWMapRep.kmswLeftPrefixReverseRep_right_roundTrip
    R k hℓ hk hkr hs hc
  calc
    kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
        k hℓ hk hkr
        (kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr q) =
        kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr
          (kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
            k hℓ hk hkr qR) := by rw [hq]
    _ = qT := by rw [hright, hleft]
    _ = q := by
      apply Subtype.ext
      rw [← hmk]
      exact (KMSWMapIsoClass.mk_eq_mk_iff T R).2 hrep

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReversalClassMap_left_roundTrip
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (q : {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary}) :
    kmswRightPrefixReversalClassMap k hℓ hk hkr
      (kmswLeftPrefixReversalClassMap k hℓ hk hkr q) = q := by
  classical
  let R : KMSWMapRep (ℓ + k) (r - k) n := Quotient.out q.val
  have hmk : KMSWMapIsoClass.mk R = q.val := Quotient.out_eq q.val
  have hcClass : (KMSWMapIsoClass.mk R).IsChanneled := by
    rw [hmk]
    exact q.property.1
  have hsClass : (KMSWMapIsoClass.mk R).IsSimpleOuterBoundary := by
    rw [hmk]
    exact q.property.2
  have hc : R.IsChanneled := (KMSWMapIsoClass.isChanneled_mk R).mp hcClass
  have hs : R.IsSimpleOuterBoundary :=
    (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mp hsClass
  let qR : {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk R, hcClass, hsClass⟩
  have hq : q = qR := Subtype.ext hmk.symm
  let S := KMSWMapRep.kmswLeftPrefixReverseRep k R hℓ hk hkr hs hc
  have hcS := KMSWMapRep.kmswLeftPrefixReverseRep_isChanneled
    k R hℓ hk hkr hs hc
  have hsS := KMSWMapRep.kmswLeftPrefixReverseRep_isSimpleOuterBoundary
    k R hℓ hk hkr hs hc
  let qS : {q : KMSWMapIsoClass ℓ r n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk S, (KMSWMapIsoClass.isChanneled_mk S).mpr hcS,
      (KMSWMapIsoClass.isSimpleOuterBoundary_mk S).mpr hsS⟩
  have hleft : kmswLeftPrefixReversalClassMap k hℓ hk hkr qR = qS := by
    apply Subtype.ext
    exact kmswLeftPrefixReversalClassMap_mk k hℓ hk hkr R hc hs
  let T := S.kmswRightPrefixReverseRep k hℓ hk hkr hsS hcS
  have hcT := S.kmswRightPrefixReverseRep_isChanneled k hℓ hk hkr hsS hcS
  have hsT := S.kmswRightPrefixReverseRep_isSimpleOuterBoundary
    k hℓ hk hkr hsS hcS
  let qT : {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} :=
    ⟨KMSWMapIsoClass.mk T, (KMSWMapIsoClass.isChanneled_mk T).mpr hcT,
      (KMSWMapIsoClass.isSimpleOuterBoundary_mk T).mpr hsT⟩
  have hright : kmswRightPrefixReversalClassMap k hℓ hk hkr qS = qT := by
    apply Subtype.ext
    exact kmswRightPrefixReversalClassMap_mk k hℓ hk hkr S hcS hsS
  have hrep := KMSWMapRep.kmswRightPrefixReverseRep_left_roundTrip
    k R hℓ hk hkr hs hc
  calc
    kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
        k hℓ hk hkr
        (kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr q) =
        kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr
          (kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
            k hℓ hk hkr qR) := by rw [hq]
    _ = qT := by rw [hleft, hright]
    _ = q := by
      apply Subtype.ext
      rw [← hmk]
      exact (KMSWMapIsoClass.mk_eq_mk_iff T R).2 hrep

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
noncomputable def kmswRightPrefixReversalClassEquiv
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    {q : KMSWMapIsoClass ℓ r n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} ≃
    {q : KMSWMapIsoClass (ℓ + k) (r - k) n //
      q.IsChanneled ∧ q.IsSimpleOuterBoundary} where
  toFun := kmswRightPrefixReversalClassMap k hℓ hk hkr
  invFun := kmswLeftPrefixReversalClassMap k hℓ hk hkr
  left_inv := kmswLeftPrefixReversalClassMap_right_roundTrip k hℓ hk hkr
  right_inv := kmswRightPrefixReversalClassMap_left_roundTrip k hℓ hk hkr

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReversalClassEquiv_apply_mk
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r)
    (R : KMSWMapRep ℓ r n) (hc : R.IsChanneled)
    (hs : R.IsSimpleOuterBoundary) :
    (kmswRightPrefixReversalClassEquiv k hℓ hk hkr
      ⟨KMSWMapIsoClass.mk R,
        (KMSWMapIsoClass.isChanneled_mk R).mpr hc,
        (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs⟩).val =
      KMSWMapIsoClass.mk (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc) :=
  kmswRightPrefixReversalClassMap_mk k hℓ hk hkr R hc hs

/-- carrier statement is false by the recorded simple-boundary restriction witness); not the paper result. -/
theorem kmswRightPrefixReversalClassMap_bijective
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    Function.Bijective
      (kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
        k hℓ hk hkr) := by
  constructor
  · intro a b hab
    calc
      a = kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr
          (kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
            k hℓ hk hkr a) :=
        (kmswLeftPrefixReversalClassMap_right_roundTrip k hℓ hk hkr a).symm
      _ = kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
          k hℓ hk hkr
          (kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
            k hℓ hk hkr b) := congrArg _ hab
      _ = b := kmswLeftPrefixReversalClassMap_right_roundTrip k hℓ hk hkr b
  · intro b
    refine ⟨kmswLeftPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := n)
      k hℓ hk hkr b, ?_⟩
    exact kmswRightPrefixReversalClassMap_left_roundTrip k hℓ hk hkr b

end KMSWMapIsoClass

end DirectedDistances.PlanarMap
