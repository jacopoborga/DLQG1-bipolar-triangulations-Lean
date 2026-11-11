module

public import DirectedDistances.PlanarMap.KMSWRightEndpointClass
public import DirectedDistances.PlanarMap.KMSWLeftEndpointClassNat
public import DirectedDistances.PlanarMap.BipolarBoundaryData
public import DirectedDistances.PlanarMap.BdyReverseBijection
public import DirectedDistances.PlanarMap.BdyReverseLeftEndpoint
import all DirectedDistances.PlanarMap.KMSWRightEndpointClass

public section
namespace DirectedDistances.PlanarMap
open BipolarTriangulationWithBoundary

/-- naturality of the boundary-prefix reversal under boundary-preserving
not the paper result. -/
theorem rightPrefixReversal_baseIso_public
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
  exact rightPrefixReversal_baseIso B B' I hk hkb hbc hbc'

/-- naturality of the boundary-prefix reversal under boundary-preserving
not the paper result. Packages the right reversal and its left-reversal
inverse on the `InMbc` subtypes for class-level descent. -/
theorem rightLeftPrefixReversalMbc_baseIso
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
        (by omega) C').val.toBase) := by
  constructor
  · simpa only [rightPrefixReversalMbc] using
      rightPrefixReversal_baseIso_public B.val B'.val I hk hkr B.property B'.property
  · simpa only [leftPrefixReversalMbc] using
      leftPrefixReversal_baseIso C.val C'.val J hk (by omega) C.property C'.property

end DirectedDistances.PlanarMap
