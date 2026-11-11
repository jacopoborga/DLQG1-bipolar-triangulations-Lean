module

public import DirectedDistances.KMSW.KMSWLeftProcedurePartial
public import DirectedDistances.KMSW.KMSWLeftProcedurePartialOne

public section
namespace DirectedDistances.PlanarMap

private theorem boundary_dart_mem_map_iff {D D' : Type*}
    [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv d ∈ B'.leftPath.darts ++ B'.rightPath.darts ↔
      d ∈ B.leftPath.darts ++ B.rightPath.darts := by
  rw [← I.leftDarts, ← I.rightDarts, ← List.map_append]
  exact List.mem_map_of_injective I.toEquiv.injective

private theorem non_boundary_edge_map_iff {D D' : Type*}
    [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :
    (∀ d ∈ B.leftPath.darts ++ B.rightPath.darts, Quotient.mk _ d ≠ e) ↔
      ∀ d ∈ B'.leftPath.darts ++ B'.rightPath.darts,
        Quotient.mk _ d ≠ I.edgeEquiv e := by
  have hmk (d : D) : I.edgeEquiv (Quotient.mk _ d) =
      Quotient.mk _ (I.toEquiv d) := rfl
  constructor
  · intro h d hd he
    have hd' : I.toEquiv (I.toEquiv.symm d) ∈
        B'.leftPath.darts ++ B'.rightPath.darts := by
      simpa only [Equiv.apply_symm_apply] using hd
    apply h (I.toEquiv.symm d) ((boundary_dart_mem_map_iff I _).mp hd')
    apply I.edgeEquiv.injective
    rw [hmk, Equiv.apply_symm_apply]
    exact he
  · intro h d hd he
    apply h (I.toEquiv d) ((boundary_dart_mem_map_iff I d).mpr hd)
    exact (hmk d).symm.trans (congrArg I.edgeEquiv he)

private theorem non_boundary_iff_not_range {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r)
    (e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :
    (∀ d ∈ B.leftPath.darts ++ B.rightPath.darts, Quotient.mk _ d ≠ e) ↔
      e ∉ Set.range (boundaryEdgeInjection B) := by
  constructor
  · intro h ⟨i, hi⟩
    cases i with
    | inl i => exact h _ (List.mem_append_left _ (List.get_mem _ i)) hi
    | inr i => exact h _ (List.mem_append_right _ (List.get_mem _ i)) hi
  · intro h d hd he
    apply h
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨i, hi⟩ := List.get_of_mem hd
      refine ⟨Sum.inl i, ?_⟩
      change Quotient.mk _ (B.leftPath.darts.get i) = e
      rw [hi]
      exact he
    · obtain ⟨i, hi⟩ := List.get_of_mem hd
      refine ⟨Sum.inr i, ?_⟩
      change Quotient.mk _ (B.rightPath.darts.get i) = e
      rw [hi]
      exact he

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
@[expose] noncomputable def KMSWMapRep.nonBoundaryEdgeCount {ℓ r N : ℕ}
    (R : KMSWMapRep ℓ r N) : ℕ := by
  classical
  exact Fintype.card
    {e : CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap //
      ∀ d ∈ R.B.leftPath.darts ++ R.B.rightPath.darts, Quotient.mk _ d ≠ e}

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
theorem KMSWMapRep.nonBoundaryEdgeCount_eq_of_iso {ℓ r N : ℕ}
    (R R' : KMSWMapRep ℓ r N) (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.nonBoundaryEdgeCount = R'.nonBoundaryEdgeCount := by
  classical
  exact Fintype.card_congr
    (I.edgeEquiv.subtypeEquiv (non_boundary_edge_map_iff I))

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
@[expose] noncomputable def KMSWMapIsoClass.nonBoundaryEdgeCount {ℓ r N : ℕ}
    (q : KMSWMapIsoClass ℓ r N) : ℕ :=
  Quotient.lift (fun R : KMSWMapRep ℓ r N => R.nonBoundaryEdgeCount)
    (by
      intro R R' h
      obtain ⟨I⟩ := h
      exact R.nonBoundaryEdgeCount_eq_of_iso R' I) q

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
@[simp] theorem KMSWMapIsoClass.nonBoundaryEdgeCount_mk {ℓ r N : ℕ}
    (R : KMSWMapRep ℓ r N) :
    nonBoundaryEdgeCount (KMSWMapIsoClass.mk R) = R.nonBoundaryEdgeCount := rfl

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
theorem KMSWMapRep.nonBoundaryEdgeCount_eq_leftEndpoint {ℓ N : ℕ}
    (R : KMSWMapRep ℓ 1 N) (hℓ : 2 ≤ ℓ) :
    R.nonBoundaryEdgeCount = R.leftEndpointNonBoundaryEdgeCount hℓ := by
  classical
  change _ = innerEdgeCount (toStrongLeftEndpoint R.B hℓ)
  rw [innerEdgeCount_eq_card_not_boundary]
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (non_boundary_iff_not_range (toStrongLeftEndpoint R.B hℓ)))

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
theorem KMSWMapRep.nonBoundaryEdgeCount_eq_oneOne {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    R.nonBoundaryEdgeCount = R.oneOneNonBoundaryEdgeCount hN := by
  classical
  rw [R.oneOneNonBoundaryEdgeCount_eq_card_not_boundary hN]
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (non_boundary_iff_not_range (R.toStrongOneOne hN)))

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result. -/
theorem KMSWMapIsoClass.nonBoundaryEdgeCount_eq {ℓ n : ℕ}
    (q : KMSWMapIsoClass ℓ 1 (n + ℓ)) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    q.nonBoundaryEdgeCount = n - 1 := by
  induction q using KMSWMapIsoClass.ind with
  | h R =>
    rw [nonBoundaryEdgeCount_mk]
    by_cases h : ℓ = 1
    · subst ℓ
      rw [R.nonBoundaryEdgeCount_eq_oneOne (by omega),
        R.oneOneNonBoundaryEdgeCount_eq_total (by omega)]
      omega
    · have htwo : 2 ≤ ℓ := by omega
      rw [R.nonBoundaryEdgeCount_eq_leftEndpoint htwo]
      exact R.leftEndpointNonBoundaryEdgeCount_eq htwo hn

end DirectedDistances.PlanarMap

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result.
The explicit witness is `kmswLeftEndpointSideEquiv ℓ n hℓ` for `ℓ ≥ 2`. -/
theorem lem_kmsw_left_procedureReading_uniform_of_two_le (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (hn : 1 ≤ n) :
    (∀ c, Nonempty (DirectedMapWithMissingIso
      (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) →
            q = kmswLeftEndpointSideEquiv ℓ n hℓ c) ∧
      (∀ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = n - 1) := by
  have h := lem_kmsw_left_procedureReading_partial ℓ n hℓ hn
  exact ⟨h.2.1, h.2.2.1,
    fun q => KMSWMapIsoClass.nonBoundaryEdgeCount_eq q.val (by omega) hn⟩

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result.
The explicit witness is `kmswLeftEndpointSideEquivOne n` at `ℓ = 1`. -/
theorem lem_kmsw_left_procedureReading_uniform_one (n : ℕ) (hn : 1 ≤ n) :
    (∀ c, Nonempty (DirectedMapWithMissingIso
      (kmswLeftEndpointSideEquivOne n c).val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass 1 1 (n + 1) // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) →
            q = kmswLeftEndpointSideEquivOne n c) ∧
      (∀ q : {q : KMSWMapIsoClass 1 1 (n + 1) // q.IsChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = n - 1) := by
  have h := lem_kmsw_left_procedureReading_partial_one n hn
  exact ⟨h.2.1, h.2.2.1,
    fun q => KMSWMapIsoClass.nonBoundaryEdgeCount_eq q.val le_rfl hn⟩

/-- N = n + ℓ excludes the one-edge map m₀ (S7-singleton, proposed resolution in
simple-boundary restriction not assumed; not the paper result.
This is NOT the printed statement. Gates per clause: the equivalence uses legal-step convention and
S7-count, and at ℓ ≥ 2 the direction to `(ℓ,1)` uses S7-inverse. Direct procedure
compatibility and uniqueness use these same readings, with I3 (Φ₀ = id) at ℓ = 1.
The count clause is a geometric identity for all target classes on the stated carrier;
interpreting this carrier as the printed second set at ℓ = 1 requires S7-singleton. -/
theorem lem_kmsw_left_procedureReading_uniform (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (hn : 1 ≤ n) :
    ∃ F : KMSWLeftWalkClass ℓ n ≃
        {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
      (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) → q = F c) ∧
      (∀ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = n - 1) := by
  by_cases h : ℓ = 1
  · subst ℓ
    exact ⟨kmswLeftEndpointSideEquivOne n,
      lem_kmsw_left_procedureReading_uniform_one n hn⟩
  · have htwo : 2 ≤ ℓ := by omega
    exact ⟨kmswLeftEndpointSideEquiv ℓ n htwo,
      lem_kmsw_left_procedureReading_uniform_of_two_le ℓ n htwo hn⟩

end DirectedDistances.KMSW
