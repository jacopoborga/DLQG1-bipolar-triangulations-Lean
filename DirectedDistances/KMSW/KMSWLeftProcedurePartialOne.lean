module

public import DirectedDistances.KMSW.KMSWLeftProcedurePartial
import DirectedDistances.PlanarMap.KMSWLeftPartialInjective
import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot
import DirectedDistances.PlanarMap.KMSWLeftDecoration

public section
namespace DirectedDistances.PlanarMap

private theorem not_mem_leftMissingDarts_one {D : Type*} [Fintype D] [DecidableEq D]
    (B : BipolarTriangulationWithBoundaryBase D 1 1) (d : D) :
    d ∉ leftMissingDarts B := by
  rintro ⟨i, hi, _⟩
  have hlen := B.leftPath.darts_length
  omega

private theorem base_tail_iff_one {N : ℕ} (R : KMSWMapRep 1 1 N)
    (d : Fin R.dartCount) : R.partialMap.tail d ↔ R.B.map.tail d := by
  change (R.B.map.tail d ∧
    ¬ (d ∈ leftMissingDarts R.B ∨ R.B.map.edgeInv d ∈ leftMissingDarts R.B)) ↔ _
  simp only [not_mem_leftMissingDarts_one, or_self, not_false_eq_true, and_true]

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapRep.mk_eq_mk_iff_partialMapIso_one {N : ℕ}
    (R R' : KMSWMapRep 1 1 N) :
    KMSWMapIsoClass.mk R = KMSWMapIsoClass.mk R' ↔
      Nonempty (DirectedMapWithMissingIso R.partialMap R'.partialMap) := by
  constructor
  · exact R.partialMapIso_of_mk_eq_mk R'
  · rintro ⟨J⟩
    apply (KMSWMapIsoClass.mk_eq_mk_iff R R').mpr
    refine ⟨bipolarBoundaryBaseIsoOfRot R.B R'.B J.toEquiv J.rot_comm
      J.edgeInv_comm ?_ ?_⟩
    · intro d
      exact (base_tail_iff_one R' _).symm.trans
        ((J.tail_iff d).trans (base_tail_iff_one R d))
    · have ho : R.B.map.IsOuter R.B.map.outer := Equiv.Perm.SameCycle.rfl
      exact ⟨R.B.map.outer, ho, (J.outer_iff _).mpr ho⟩

private theorem singleton_of_length_one {α : Type*} (xs : List α)
    (hlen : xs.length = 1) {d : α} (hd : d ∈ xs) : xs = [d] := by
  cases xs with
  | nil => simp only [List.not_mem_nil] at hd
  | cons a xs =>
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at hd
      subst a
      rfl
    | cons b ys => simp only [List.length_cons] at hlen; omega

private theorem shared_oneOne_card_le_two {D : Type*} [Fintype D] [DecidableEq D]
    (B : BipolarTriangulationWithBoundaryBase D 1 1) (d : D)
    (hl : d ∈ B.leftPath.darts) (hr : d ∈ B.rightPath.darts) :
    Fintype.card D ≤ 2 := by
  have hleft := singleton_of_length_one _ B.leftPath.darts_length hl
  have hright := singleton_of_length_one _ B.rightPath.darts_length hr
  have hbd : canonicalOuterBoundaryDarts B = [d, B.map.edgeInv d] := by
    simp only [canonicalOuterBoundaryDarts, hleft, hright, List.reverse_singleton,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  have ho := canonicalOuterBoundaryDarts_mem_isOuter B
    (show d ∈ canonicalOuterBoundaryDarts B by rw [hbd]; exact List.Mem.head _)
  have hoi := canonicalOuterBoundaryDarts_mem_isOuter B
    (show B.map.edgeInv d ∈ canonicalOuterBoundaryDarts B by
      rw [hbd]
      exact List.Mem.tail _ (List.Mem.head _))
  have hf := canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B ho
  have hfi := canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B hoi
  rw [hbd, List.formPerm_pair] at hf hfi
  simp only [Equiv.swap_apply_left] at hf
  simp only [Equiv.swap_apply_right] at hfi
  have hrot : B.map.rot d = d := by
    have h := congrArg B.map.rot hfi
    change B.map.rot (B.map.rot.symm (B.map.edgeInv (B.map.edgeInv d))) =
      B.map.rot d at h
    simpa only [Equiv.apply_symm_apply, B.map.edgeInv_invol] using h.symm
  have hroti : B.map.rot (B.map.edgeInv d) = B.map.edgeInv d := by
    have h := congrArg B.map.rot hf
    change B.map.rot (B.map.rot.symm (B.map.edgeInv d)) =
      B.map.rot (B.map.edgeInv d) at h
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hrot' : B.map.rot.symm d = d := by
    apply B.map.rot.injective
    simpa only [Equiv.apply_symm_apply] using hrot.symm
  have hroti' : B.map.rot.symm (B.map.edgeInv d) = B.map.edgeInv d := by
    apply B.map.rot.injective
    simpa only [Equiv.apply_symm_apply] using hroti.symm
  have hinv' (x : D) : B.map.edgeInv.symm x = B.map.edgeInv x := by
    apply B.map.edgeInv.injective
    rw [Equiv.apply_symm_apply, B.map.edgeInv_invol]
  have hall (x : D) : x = d ∨ x = B.map.edgeInv d := by
    have hconn := B.planar.1 d x
    induction hconn with
    | refl => exact Or.inl rfl
    | @tail y z hy hyz ih =>
      rcases hyz with rfl | rfl | rfl | rfl <;>
        rcases ih with rfl | rfl <;>
        simp only [hrot, hroti, hrot', hroti', hinv', B.map.edgeInv_invol,
          true_or, or_true]
  have hinj : Function.Injective (fun x : D => decide (x = d)) := by
    intro x y hxy
    by_cases hx : x = d
    · by_cases hy : y = d
      · exact hx.trans hy.symm
      · simp only [hx, decide_true, hy, decide_false, Bool.true_eq_false] at hxy
    · by_cases hy : y = d
      · simp only [hx, decide_false, hy, decide_true, Bool.false_eq_true] at hxy
      · exact ((hall x).resolve_left hx).trans ((hall y).resolve_left hy).symm
  exact (Fintype.card_le_of_injective _ hinj).trans (by rw [Fintype.card_bool])

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapRep.oneOne_paths_edge_disjoint {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    ∀ d ∈ R.B.leftPath.darts, ∀ e ∈ R.B.rightPath.darts,
      ¬ Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.edgeInv d e := by
  intro d hd e he hsame
  have hdt := ((R.B.outerSplit.2.2.1 d).mp hd).2.1
  have het := (R.B.rightPath.exists_index e he).choose_spec.choose_spec.2.1
  rcases (CombinatorialMap.edgeInv_sameCycle_iff R.B.map.toCombinatorialMap d e).mp
      hsame with heq | heq
  · subst e
    have hcard := shared_oneOne_card_le_two R.B d hd he
    rw [Fintype.card_fin, R.dartCount_eq_two_mul] at hcard
    omega
  · exact (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp hdt (heq ▸ het)

/-- this is the S7-singleton question (proposed resolution in -/
@[expose] def KMSWMapRep.toStrongOneOne {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    BipolarTriangulationWithBoundary (Fin R.dartCount) 1 1 :=
  R.B.toStrong (fun _ _ hv => rightPath_vertex_mem_endpoint R.B hv)
    (R.oneOne_paths_edge_disjoint hN)

/-- this is the S7-singleton question (proposed resolution in -/
@[expose] noncomputable def KMSWMapRep.oneOneNonBoundaryEdgeCount {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) : ℕ :=
  innerEdgeCount (R.toStrongOneOne hN)

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapRep.oneOneNonBoundaryEdgeCount_eq_card_not_boundary {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    R.oneOneNonBoundaryEdgeCount hN = Fintype.card
      {e : CombinatorialMap.EdgeQuotient (R.toStrongOneOne hN).map.toCombinatorialMap //
        e ∉ Set.range (boundaryEdgeInjection (R.toStrongOneOne hN))} :=
  innerEdgeCount_eq_card_not_boundary (R.toStrongOneOne hN)

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapRep.oneOneNonBoundaryEdgeCount_eq_total {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    R.oneOneNonBoundaryEdgeCount hN = N - 2 := by
  change R.B.map.toCombinatorialMap.numEdges - (1 + 1) = N - 2
  rw [R.edges]

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapRep.oneOneNonBoundaryEdgeCount_eq_of_iso {N : ℕ}
    (R R' : KMSWMapRep 1 1 N) (hN : 2 ≤ N)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.oneOneNonBoundaryEdgeCount hN = R'.oneOneNonBoundaryEdgeCount hN := by
  change R.B.map.toCombinatorialMap.numEdges - (1 + 1) =
    R'.B.map.toCombinatorialMap.numEdges - (1 + 1)
  rw [I.numEdges_eq]

/-- this is the S7-singleton question (proposed resolution in -/
@[expose] noncomputable def KMSWMapIsoClass.oneOneNonBoundaryEdgeCount {N : ℕ}
    (q : KMSWMapIsoClass 1 1 N) (hN : 2 ≤ N) : ℕ :=
  Quotient.lift (fun R : KMSWMapRep 1 1 N => R.oneOneNonBoundaryEdgeCount hN)
    (by
      intro R R' h
      obtain ⟨I⟩ := h
      exact R.oneOneNonBoundaryEdgeCount_eq_of_iso R' hN I) q

/-- this is the S7-singleton question (proposed resolution in -/
@[simp] theorem KMSWMapIsoClass.oneOneNonBoundaryEdgeCount_mk {N : ℕ}
    (R : KMSWMapRep 1 1 N) (hN : 2 ≤ N) :
    oneOneNonBoundaryEdgeCount (KMSWMapIsoClass.mk R) hN =
      R.oneOneNonBoundaryEdgeCount hN := rfl

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapIsoClass.oneOneNonBoundaryEdgeCount_eq_total {N : ℕ}
    (q : KMSWMapIsoClass 1 1 N) (hN : 2 ≤ N) :
    q.oneOneNonBoundaryEdgeCount hN = N - 2 := by
  induction q using KMSWMapIsoClass.ind with
  | h R => exact R.oneOneNonBoundaryEdgeCount_eq_total hN

/-- this is the S7-singleton question (proposed resolution in -/
theorem KMSWMapIsoClass.oneOneNonBoundaryEdgeCount_eq {n : ℕ}
    (q : KMSWMapIsoClass 1 1 (n + 1)) (hn : 1 ≤ n) :
    q.oneOneNonBoundaryEdgeCount (by omega) = n - 1 := by
  rw [oneOneNonBoundaryEdgeCount_eq_total]
  omega

end DirectedDistances.PlanarMap

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- this is the S7-singleton question (proposed resolution in -/
theorem lem_kmsw_left_procedureReading_partial_one (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (kmswLeftEndpointSideEquivOne n) ∧
      (∀ c, Nonempty (DirectedMapWithMissingIso
        (kmswLeftEndpointSideEquivOne n c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass 1 1 (n + 1) // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) →
            q = kmswLeftEndpointSideEquivOne n c) ∧
      (∀ c, KMSWMapIsoClass.oneOneNonBoundaryEdgeCount
        (kmswLeftEndpointSideEquivOne n c).val (by omega) = n - 1) := by
  refine ⟨(kmswLeftEndpointSideEquivOne n).bijective,
    kmswLeftEndpointSideEquivOne_partialMapIso n, ?_, ?_⟩
  · intro c q hq
    obtain ⟨I⟩ := hq
    obtain ⟨J⟩ := kmswLeftEndpointSideEquivOne_partialMapIso n c
    have hclass := (KMSWMapRep.mk_eq_mk_iff_partialMapIso_one
      q.val.out (kmswLeftEndpointSideEquivOne n c).val.out).mpr ⟨I.trans J.symm⟩
    rw [show KMSWMapIsoClass.mk q.val.out = q.val from Quotient.out_eq _,
      show KMSWMapIsoClass.mk (kmswLeftEndpointSideEquivOne n c).val.out =
        (kmswLeftEndpointSideEquivOne n c).val from Quotient.out_eq _] at hclass
    exact Subtype.ext hclass
  · intro c
    exact KMSWMapIsoClass.oneOneNonBoundaryEdgeCount_eq _ hn

end DirectedDistances.KMSW
