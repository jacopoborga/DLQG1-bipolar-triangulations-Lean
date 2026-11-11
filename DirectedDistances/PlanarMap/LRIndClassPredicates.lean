/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBoltzmannMapLaw
public import DirectedDistances.PlanarMap.KMSWMapIsoClass
public import DirectedDistances.PlanarMap.FiniteXDPSelectorPath

/-! Predicates for the three map classes in `lem-lr-ind`
not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- An XDP geodesic is unique when every other XDP geodesic has the same
ordered dart list (`lem-lr-ind`; helper toward the paper result, -/
@[expose] def IsUniqueXDPGeodesicBase
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  IsXDPGeodesicBase B x P ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesicBase B x Q → Q.darts = P.darts

/-- `Mᴸ_{ℓ,s}` on representatives: the right boundary is the unique
XDP-geodesic (`lem-lr-ind`; helper toward the paper result,
for LDP and `s ≤ min ℓ r` for SDP; these ranges are source context only. -/
@[expose] def IsMLRepresentative (x : XDP)
    {ℓ s n : ℕ} (R : KMSWMapRep ℓ s n) : Prop :=
  IsUniqueXDPGeodesicBase R.B x R.B.rightPath

/-- `Mᴿ_{s,r}` on representatives: the left boundary is an XDP-geodesic,
without a uniqueness requirement (`lem-lr-ind`; helper toward the paper
`s ≥ max ℓ r` for LDP and `s ≤ min ℓ r` for SDP; these ranges are source
context only. -/
@[expose] def IsMRRepresentative (x : XDP)
    {s r n : ℕ} (R : KMSWMapRep s r n) : Prop :=
  IsXDPGeodesicBase R.B x R.B.leftPath

/-- `M_{ℓ,r,s}` on representatives: the selected XDP-geodesic length is
`s` (`lem-lr-ind`; helper toward the paper result, -/
@[expose] def IsMRepresentative (x : XDP) (s : ℕ)
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) : Prop :=
  xdpLengthBase R.B x = s

private noncomputable def BipolarBoundaryBaseIso.transportPath
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    SimpleDirectedDartPath B'.map B'.source B'.sink n where
  darts := P.darts.map I.toEquiv
  vertices := P.vertices.map I.vertexEquiv
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map I.vertexEquiv.injective
  start_vertex := by
    simpa using (congrArg I.vertexEquiv P.start_vertex).trans I.vertexEquiv_source
  end_vertex := by
    simpa using (congrArg I.vertexEquiv P.end_vertex).trans I.vertexEquiv_sink
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartTailVertex _
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartHeadVertex _

private theorem BipolarBoundaryBaseIso.transportPath_darts
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (I.transportPath P).darts = P.darts.map I.toEquiv := rfl

private theorem isXDPGeodesicBase_iff_transportPath
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsXDPGeodesicBase B' x (I.transportPath P) ↔
      IsXDPGeodesicBase B x P := by
  cases x with
  | ldp =>
      simp only [IsXDPGeodesicBase, isLDPGeodesicBase_iff_length_eq]
      rw [ldpLengthBase_eq_of_baseIso I]
  | sdp =>
      simp only [IsXDPGeodesicBase, isSDPGeodesicBase_iff_length_eq]
      rw [sdpLengthBase_eq_of_baseIso I]

private theorem isXDPGeodesicBase_congr_path
    {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (x : XDP) (P Q : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsXDPGeodesicBase B x P ↔ IsXDPGeodesicBase B x Q := by
  cases x <;> rfl

private theorem isUniqueXDPGeodesicBase_iff_transportPath
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (Q : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hQ : Q.darts = (I.transportPath P).darts) :
    IsUniqueXDPGeodesicBase B x P ↔ IsUniqueXDPGeodesicBase B' x Q := by
  constructor
  · rintro ⟨hP, hUnique⟩
    refine ⟨(isXDPGeodesicBase_iff_transportPath I x P).2 hP, ?_⟩
    intro m T hT
    let T₀ := I.symm.transportPath T
    have hT₀ : IsXDPGeodesicBase B x T₀ := by
      exact (isXDPGeodesicBase_iff_transportPath I.symm x T).mpr hT
    have hUnique₀ := hUnique T₀ hT₀
    have hmap : T₀.darts.map I.toEquiv = T.darts := by
      rw [BipolarBoundaryBaseIso.transportPath_darts]
      simp [BipolarBoundaryBaseIso.symm]
    calc
      T.darts = T₀.darts.map I.toEquiv := hmap.symm
      _ = P.darts.map I.toEquiv := congrArg (List.map I.toEquiv) hUnique₀
      _ = (I.transportPath P).darts := by
        rw [BipolarBoundaryBaseIso.transportPath_darts]
      _ = Q.darts := hQ.symm
  · rintro ⟨hQgeo, hUnique⟩
    have hP : IsXDPGeodesicBase B x P := by
      apply (isXDPGeodesicBase_iff_transportPath I x P).mp
      exact (isXDPGeodesicBase_congr_path B' x (I.transportPath P) Q).mp hQgeo
    refine ⟨hP, ?_⟩
    intro m T hT
    have hTgeo : IsXDPGeodesicBase B' x (I.transportPath T) :=
      (isXDPGeodesicBase_iff_transportPath I x T).mpr hT
    have hUnique' := hUnique (I.transportPath T) hTgeo
    have htransport : (I.transportPath T).darts =
        (I.transportPath P).darts := hUnique'.trans hQ
    apply List.map_injective_iff.mpr I.toEquiv.injective
    rw [BipolarBoundaryBaseIso.transportPath_darts,
      BipolarBoundaryBaseIso.transportPath_darts] at htransport
    exact htransport

private theorem geodesic_iff_of_boundary_list
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r n : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (Q : SimpleDirectedDartPath B'.map B'.source B'.sink n) :
    IsXDPGeodesicBase B' x (I.transportPath P) ↔
      IsXDPGeodesicBase B' x Q :=
  isXDPGeodesicBase_congr_path B' x (I.transportPath P) Q

/-- The representative predicate for `Mᴸ_{ℓ,s}` is invariant under
`BipolarBoundaryBaseIso` (`lem-lr-ind`; helper toward the paper result, -/
theorem IsMLRepresentative_eq_of_baseIso (x : XDP)
    {ℓ s n : ℕ} (R R' : KMSWMapRep ℓ s n)
    (hI : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    IsMLRepresentative x R = IsMLRepresentative x R' := by
  rcases hI with ⟨I⟩
  apply propext
  exact isUniqueXDPGeodesicBase_iff_transportPath I x R.B.rightPath
    R'.B.rightPath (by
      rw [BipolarBoundaryBaseIso.transportPath_darts]
      exact I.rightDarts.symm)

/-- The representative predicate for `Mᴿ_{s,r}` is invariant under
`BipolarBoundaryBaseIso` (`lem-lr-ind`; helper toward the paper result, -/
theorem IsMRRepresentative_eq_of_baseIso (x : XDP)
    {s r n : ℕ} (R R' : KMSWMapRep s r n)
    (hI : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    IsMRRepresentative x R = IsMRRepresentative x R' := by
  rcases hI with ⟨I⟩
  apply propext
  change IsXDPGeodesicBase R.B x R.B.leftPath ↔
    IsXDPGeodesicBase R'.B x R'.B.leftPath
  calc
    IsXDPGeodesicBase R.B x R.B.leftPath ↔
        IsXDPGeodesicBase R'.B x (I.transportPath R.B.leftPath) :=
      (isXDPGeodesicBase_iff_transportPath I x R.B.leftPath).symm
    _ ↔ IsXDPGeodesicBase R'.B x R'.B.leftPath :=
      geodesic_iff_of_boundary_list I x R.B.leftPath R'.B.leftPath

/-- The representative predicate for `M_{ℓ,r,s}` is invariant under
`BipolarBoundaryBaseIso` (`lem-lr-ind`; helper toward the paper result, -/
theorem IsMRepresentative_eq_of_baseIso (x : XDP) (s : ℕ)
    {ℓ r n : ℕ} (R R' : KMSWMapRep ℓ r n)
    (hI : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    IsMRepresentative x s R = IsMRepresentative x s R' := by
  rcases hI with ⟨I⟩
  cases x with
  | ldp =>
      simp only [IsMRepresentative, xdpLengthBase, ldpLengthBase_eq_of_baseIso I]
  | sdp =>
      simp only [IsMRepresentative, xdpLengthBase, sdpLengthBase_eq_of_baseIso I]

/-- The quotient-class predicate for `Mᴸ_{ℓ,s}`. Representative invariance
makes this lift well-defined (`lem-lr-ind`; helper toward the paper result, -/
@[expose] noncomputable def IsMLClass (x : XDP) {ℓ s n : ℕ} :
    KMSWMapIsoClass ℓ s n → Prop :=
  KMSWMapIsoClass.lift (fun R => IsMLRepresentative x R)
    (fun R R' h => IsMLRepresentative_eq_of_baseIso x R R' h)

/-- The quotient-class predicate for `Mᴿ_{s,r}`. Representative invariance
makes this lift well-defined (`lem-lr-ind`; helper toward the paper result, -/
@[expose] noncomputable def IsMRClass (x : XDP) {s r n : ℕ} :
    KMSWMapIsoClass s r n → Prop :=
  KMSWMapIsoClass.lift (fun R => IsMRRepresentative x R)
    (fun R R' h => IsMRRepresentative_eq_of_baseIso x R R' h)

/-- The quotient-class predicate for `M_{ℓ,r,s}`. Representative invariance
makes this lift well-defined (`lem-lr-ind`; helper toward the paper result, -/
@[expose] noncomputable def IsMClass (x : XDP) (s : ℕ) {ℓ r n : ℕ} :
    KMSWMapIsoClass ℓ r n → Prop :=
  KMSWMapIsoClass.lift (fun R => IsMRepresentative x s R)
    (fun R R' h => IsMRepresentative_eq_of_baseIso x s R R' h)

/-- Evaluating the `Mᴸ` class predicate on a representative class recovers
the representative predicate (`lem-lr-ind`; helper toward the paper result, -/
@[simp] theorem IsMLClass_mk (x : XDP) {ℓ s n : ℕ}
    (R : KMSWMapRep ℓ s n) :
    IsMLClass x (KMSWMapIsoClass.mk R) = IsMLRepresentative x R := by
  exact KMSWMapIsoClass.lift_mk _ _ R

/-- Evaluating the `Mᴿ` class predicate on a representative class recovers
the representative predicate (`lem-lr-ind`; helper toward the paper result, -/
@[simp] theorem IsMRClass_mk (x : XDP) {s r n : ℕ}
    (R : KMSWMapRep s r n) :
    IsMRClass x (KMSWMapIsoClass.mk R) = IsMRRepresentative x R := by
  exact KMSWMapIsoClass.lift_mk _ _ R

/-- Evaluating the `M` class predicate on a representative class recovers
the representative predicate (`lem-lr-ind`; helper toward the paper result, -/
@[simp] theorem IsMClass_mk (x : XDP) (s : ℕ) {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) :
    IsMClass x s (KMSWMapIsoClass.mk R) = IsMRepresentative x s R := by
  exact KMSWMapIsoClass.lift_mk _ _ R

/-- The `Mᴸ_{ℓ,s}` predicate on the Boltzmann space `BoltzmannSpace ℓ s`
(`lem-lr-ind`; helper toward the paper result, -/
@[expose] def IsML (x : XDP) {ℓ s : ℕ}
    (ω : BoltzmannSpace ℓ s) : Prop := IsMLClass x ω.2

/-- The `Mᴿ_{s,r}` predicate on the Boltzmann space `BoltzmannSpace s r`
(`lem-lr-ind`; helper toward the paper result, -/
@[expose] def IsMR (x : XDP) {s r : ℕ}
    (ω : BoltzmannSpace s r) : Prop := IsMRClass x ω.2

/-- The `M_{ℓ,r,s}` predicate on the Boltzmann space `BoltzmannSpace ℓ r`
(`lem-lr-ind`; helper toward the paper result, -/
@[expose] def IsM (x : XDP) (s : ℕ) {ℓ r : ℕ}
    (ω : BoltzmannSpace ℓ r) : Prop := IsMClass x s ω.2

/-- The `Mᴸ` event is measurable since the Boltzmann space has the top
measurable structure (`lem-lr-ind`; helper toward the paper result, -/
@[measurability] theorem IsML_measurableSet (x : XDP) {ℓ s : ℕ} :
    MeasurableSet {ω : BoltzmannSpace ℓ s | IsML x ω} := by
  exact MeasurableSpace.measurableSet_top

/-- The `Mᴿ` event is measurable since the Boltzmann space has the top
measurable structure (`lem-lr-ind`; helper toward the paper result, -/
@[measurability] theorem IsMR_measurableSet (x : XDP) {s r : ℕ} :
    MeasurableSet {ω : BoltzmannSpace s r | IsMR x ω} := by
  exact MeasurableSpace.measurableSet_top

/-- The `M` event is measurable since the Boltzmann space has the top
measurable structure (`lem-lr-ind`; helper toward the paper result, -/
@[measurability] theorem IsM_measurableSet (x : XDP) (s : ℕ) {ℓ r : ℕ} :
    MeasurableSet {ω : BoltzmannSpace ℓ r | IsM x s ω} := by
  exact MeasurableSpace.measurableSet_top

/-- On a quotient class, `M_{ℓ,r,s}` is exactly the selected-length fiber
(`lem-lr-ind`; helper toward the paper result, -/
theorem IsMClass_iff_xdpLenClass {ℓ r n : ℕ} (x : XDP) (s : ℕ)
    (q : KMSWMapIsoClass ℓ r n) :
    IsMClass x s q ↔ xdpLenClass x q = s := by
  refine KMSWMapIsoClass.ind
    (motive := fun q => IsMClass x s q ↔ xdpLenClass x q = s) ?_ q
  intro R
  rw [IsMClass_mk, xdpLenClass_mk]
  rfl

/-- On `BoltzmannSpace ℓ r`, the `M_{ℓ,r,s}` predicate is exactly the
selected-length fiber (`lem-lr-ind`; helper toward the paper result, -/
theorem IsM_iff_xdpLen {ℓ r : ℕ} (x : XDP) (s : ℕ)
    (ω : BoltzmannSpace ℓ r) :
    IsM x s ω ↔ xdpLen x ω = s := by
  exact IsMClass_iff_xdpLenClass x s ω.2

/-- The selected-length fiber is the Boltzmann-space predicate for
`M_{ℓ,r,s}` (`lem-lr-ind`; helper toward the paper result, -/
theorem xdpLen_fiber_eq_IsM {ℓ r : ℕ} (x : XDP) (s : ℕ) :
    {ω : BoltzmannSpace ℓ r | xdpLen x ω = s} =
      {ω : BoltzmannSpace ℓ r | IsM x s ω} := by
  ext ω
  exact (IsM_iff_xdpLen x s ω).symm

end DirectedDistances.PlanarMap
