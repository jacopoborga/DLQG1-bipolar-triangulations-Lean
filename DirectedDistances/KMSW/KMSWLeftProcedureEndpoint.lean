module

public import DirectedDistances.KMSW.KMSWLeftProcedureCore
public import DirectedDistances.PlanarMap.KMSWRightEndpointClass
public import DirectedDistances.PlanarMap.KMSWLeftEndpointClass

/-! # Restricted endpoint reversal on procedure-reading KMSW classes

hypothesis where stated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Right endpoint reversal on channeled isomorphism classes. -/
@[expose] noncomputable def rightRevClass {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled}) :
    {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} := by
  have hbc : q.val.out.IsChanneled := by
    change (KMSWMapIsoClass.mk q.val.out).IsChanneled
    rw [show KMSWMapIsoClass.mk q.val.out = q.val from Quotient.out_eq q.val]
    exact q.property
  exact ⟨KMSWMapIsoClass.mk (kmswRightEndpointReverseRep q.val.out hℓ hbc),
    (KMSWMapIsoClass.isChanneled_mk _).mpr
      (kmswRightEndpointReverseRep_isChanneled q.val.out hℓ hbc)⟩

/-- The class map agrees with reversal of any channeled representative. -/
theorem rightRevClass_mk {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (R : KMSWMapRep 1 ℓ N) (hbc : R.IsChanneled) :
    rightRevClass hℓ ⟨KMSWMapIsoClass.mk R,
      (KMSWMapIsoClass.isChanneled_mk R).mpr hbc⟩ =
    ⟨KMSWMapIsoClass.mk (kmswRightEndpointReverseRep R hℓ hbc),
      (KMSWMapIsoClass.isChanneled_mk _).mpr
        (kmswRightEndpointReverseRep_isChanneled R hℓ hbc)⟩ := by
  apply Subtype.ext
  apply (KMSWMapIsoClass.mk_eq_mk_iff _ _).mpr
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff
    (KMSWMapIsoClass.mk R).out R).mp (Quotient.out_eq (KMSWMapIsoClass.mk R))
  exact kmswRightEndpointReverseRep_iso hℓ _ _ _ _ I

/-- Surjectivity follows from right reversal after left reversal. -/
theorem rightRevClass_surjective {ℓ N : ℕ} (hℓ : 2 ≤ ℓ) :
    Function.Surjective (rightRevClass (N := N) hℓ) := by
  rintro ⟨q, hq⟩
  obtain ⟨R, rfl⟩ := Quotient.exists_rep q
  have hbc : R.IsBoundaryChanneled :=
    (KMSWMapRep.isChanneled_iff_isBoundaryChanneled R).mp
      ((KMSWMapIsoClass.isChanneled_mk R).mp hq)
  let L := kmswLeftEndpointReverseRep R hℓ hbc
  have hL : L.IsChanneled :=
    kmswLeftEndpointReverseRep_isBoundaryChanneled R hℓ hbc
  refine ⟨⟨KMSWMapIsoClass.mk L, (KMSWMapIsoClass.isChanneled_mk L).mpr hL⟩, ?_⟩
  rw [rightRevClass_mk hℓ L hL]
  apply Subtype.ext
  exact (KMSWMapIsoClass.mk_eq_mk_iff _ _).mpr
    (kmswRightEndpointReverseRep_left_roundTrip R hℓ hbc)

/-- hypothesis `hnat`; not the paper result.
Injectivity follows by left reversal and the left-after-right round trip. -/
theorem rightRevClass_injective {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (hnat : ∀ (R R' : KMSWMapRep ℓ 1 N)
      (hbc : R.IsBoundaryChanneled) (hbc' : R'.IsBoundaryChanneled),
      Nonempty (BipolarBoundaryBaseIso R.B R'.B) →
      Nonempty (BipolarBoundaryBaseIso
        (kmswLeftEndpointReverseRep R hℓ hbc).B
        (kmswLeftEndpointReverseRep R' hℓ hbc').B)) :
    Function.Injective (rightRevClass (N := N) hℓ) := by
  intro q q' h
  let R := q.val.out
  let R' := q'.val.out
  have hR : R.IsChanneled := by
    change (KMSWMapIsoClass.mk R).IsChanneled
    rw [show KMSWMapIsoClass.mk R = q.val from Quotient.out_eq q.val]
    exact q.property
  have hR' : R'.IsChanneled := by
    change (KMSWMapIsoClass.mk R').IsChanneled
    rw [show KMSWMapIsoClass.mk R' = q'.val from Quotient.out_eq q'.val]
    exact q'.property
  have hclass :
      KMSWMapIsoClass.mk (kmswRightEndpointReverseRep R hℓ hR) =
      KMSWMapIsoClass.mk (kmswRightEndpointReverseRep R' hℓ hR') :=
    congrArg Subtype.val h
  have hbc : (kmswRightEndpointReverseRep R hℓ hR).IsBoundaryChanneled :=
    (KMSWMapRep.isChanneled_iff_isBoundaryChanneled _).mp
      (kmswRightEndpointReverseRep_isChanneled R hℓ hR)
  have hbc' : (kmswRightEndpointReverseRep R' hℓ hR').IsBoundaryChanneled :=
    (KMSWMapRep.isChanneled_iff_isBoundaryChanneled _).mp
      (kmswRightEndpointReverseRep_isChanneled R' hℓ hR')
  obtain ⟨J⟩ := hnat _ _ hbc hbc'
    ((KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hclass)
  obtain ⟨I⟩ := kmswLeftEndpointReverseRep_right_roundTrip R hℓ hR
  obtain ⟨I'⟩ := kmswLeftEndpointReverseRep_right_roundTrip R' hℓ hR'
  apply Subtype.ext
  calc
    q.val = KMSWMapIsoClass.mk R := (Quotient.out_eq q.val).symm
    _ = KMSWMapIsoClass.mk R' :=
      (KMSWMapIsoClass.mk_eq_mk_iff R R').mpr ⟨I.symm.trans (J.trans I')⟩
    _ = q'.val := Quotient.out_eq q'.val

/-- hypothesis `hnat`; not the paper result.
The endpoint equivalence is directed from the `(ℓ,1)` side to `(1,ℓ)`. -/
@[expose] noncomputable def kmswEndpointClassEquivOf {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (hnat : ∀ (R R' : KMSWMapRep ℓ 1 N)
      (hbc : R.IsBoundaryChanneled) (hbc' : R'.IsBoundaryChanneled),
      Nonempty (BipolarBoundaryBaseIso R.B R'.B) →
      Nonempty (BipolarBoundaryBaseIso
        (kmswLeftEndpointReverseRep R hℓ hbc).B
        (kmswLeftEndpointReverseRep R' hℓ hbc').B)) :
    {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} ≃
      {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled} :=
  (Equiv.ofBijective (rightRevClass hℓ)
    ⟨rightRevClass_injective hℓ hnat, rightRevClass_surjective hℓ⟩).symm

/-- hypothesis `hnat`; not the paper result.
Compose the procedure-reading bijection with restricted endpoint reversal. -/
@[expose] noncomputable def kmswLeftEndpointSideEquivOf (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (hnat : ∀ (R R' : KMSWMapRep ℓ 1 (n + ℓ))
      (hbc : R.IsBoundaryChanneled) (hbc' : R'.IsBoundaryChanneled),
      Nonempty (BipolarBoundaryBaseIso R.B R'.B) →
      Nonempty (BipolarBoundaryBaseIso
        (kmswLeftEndpointReverseRep R hℓ hbc).B
        (kmswLeftEndpointReverseRep R' hℓ hbc').B)) :
    KMSWLeftWalkClass ℓ n ≃
      {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
  (kmswLeftRightSideEquiv ℓ n (by omega)).trans
    (kmswEndpointClassEquivOf hℓ hnat).symm




@[expose] noncomputable def kmswLeftEndpointSideEquivOne (n : ℕ) :
    KMSWLeftWalkClass 1 n ≃
      {q : KMSWMapIsoClass 1 1 (n + 1) // q.IsChanneled} :=
  kmswLeftRightSideEquiv 1 n le_rfl

end DirectedDistances.KMSW
