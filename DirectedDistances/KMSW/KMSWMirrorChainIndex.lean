module

public import DirectedDistances.KMSW.KMSWMirrorSymmetryFinite
public import DirectedDistances.KMSW.KMSWMissingChainOrder
public import DirectedDistances.PlanarMap.MirrorMap

/-! Missing-edge index transport for the finite mirror symmetry. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- missing-edge index under the finite mirror symmetry
not the paper result. -/
theorem outerFaceSucc_mirror_edgeInv {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (a : D) :
    outerFaceSucc M.mirror (M.edgeInv a) =
      M.edgeInv (M.toCombinatorialMap.faceSucc a) := by
  apply M.mirror.toCombinatorialMap.faceSucc.injective
  change M.mirror.toCombinatorialMap.faceSucc
    (M.mirror.toCombinatorialMap.faceSucc.symm _) = _
  rw [Equiv.apply_symm_apply]
  change M.edgeInv a = M.rot (M.edgeInv (M.edgeInv (M.rot.symm (M.edgeInv a))))
  rw [M.edgeInv_invol, Equiv.apply_symm_apply]

private def mirrorIndexWord {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :=
  R.B.leftPath.darts ++ R.B.rightPath.darts.reverse.map R.B.map.edgeInv

private theorem mirrorIndexWord_rot {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    R.B.outerWord.letters ~r mirrorIndexWord R := by
  simpa only [mirrorIndexWord, List.append_nil] using R.B.outerSplit.2.1

private theorem mirrorIndexWord_nodup {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    (mirrorIndexWord R).Nodup :=
  (mirrorIndexWord_rot R).nodup_iff.mp R.B.outerWord.nodup

private theorem mirrorIndexWord_length {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    (mirrorIndexWord R).length = ℓ + 1 := by
  simp only [mirrorIndexWord, List.length_append, List.length_map, List.length_reverse,
    R.B.leftPath.darts_length, R.B.rightPath.darts_length]

private theorem mirrorIndexWord_outer {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) (a) :
    a ∈ mirrorIndexWord R ↔ R.partialMap.IsOuter a := by
  exact (mirrorIndexWord_rot R).mem_iff.symm.trans
    (mem_iff_isOuter R.B.map R.B.outerWord R.B.outerSplit.1 a)

private theorem mirrorIndexWord_succ {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (i : ℕ) (hi : i < (mirrorIndexWord R).length) :
    R.partialMap.toCombinatorialMap.faceSucc (mirrorIndexWord R)[i] =
      (mirrorIndexWord R)[(i + 1) % (mirrorIndexWord R).length]'(Nat.mod_lt _ (by omega)) := by
  have hm := List.getElem_mem hi
  have hmo := (mirrorIndexWord_rot R).mem_iff.mpr hm
  have hf := R.B.outerSplit.1.2.2 _ hmo
  have he := List.formPerm_eq_of_isRotated R.B.outerWord.nodup (mirrorIndexWord_rot R)
  change R.B.map.toCombinatorialMap.faceSucc _ = _
  rw [hf, he, List.formPerm_apply_getElem _ (mirrorIndexWord_nodup R)]

private theorem mirrorIndexWord_missing {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (i : ℕ) (hi : i < (mirrorIndexWord R).length) :
    R.partialMap.missing (mirrorIndexWord R)[i] ↔ i + 1 < ℓ := by
  have hout := (mirrorIndexWord_outer R _).mp (List.getElem_mem hi)
  have hleft : R.partialMap.missing (mirrorIndexWord R)[i] ↔
      (mirrorIndexWord R)[i] ∈ leftMissingDarts R.B := by
    constructor
    · intro hm
      have ht := (R.tail_iff_isOuter_of_partialMap_missing hℓ _ hm).mpr hout
      change _ ∈ leftMissingDarts R.B ∨ _ ∈ leftMissingDarts R.B at hm
      rcases hm with hm | hm
      · exact hm
      · have hflip := ((mem_leftMissingDarts_iff R.B _).mp hm).1
        have htflip := ((R.B.outerSplit.2.2.1 _).mp hflip).2.1
        exact False.elim ((R.B.map.tail_iff _ (R.B.noMissingDarts _)).mp ht htflip)
    · intro hm
      exact Or.inl hm
  rw [hleft]
  constructor
  · rintro ⟨j, hj, he⟩
    have hjl : j.val < (mirrorIndexWord R).length := by
      rw [mirrorIndexWord_length R]
      have hj' := j.isLt
      have hdl := R.B.leftPath.darts_length
      omega
    have hg : (mirrorIndexWord R)[j.val] = R.B.leftPath.darts.get j := by
      exact List.getElem_append_left j.isLt
    have hij : i = j.val := (mirrorIndexWord_nodup R).getElem_inj_iff.mp
      (he.trans hg.symm)
    have hdl := R.B.leftPath.darts_length
    omega
  · intro hiℓ
    let j : Fin R.B.leftPath.darts.length :=
      ⟨i, by rw [R.B.leftPath.darts_length]; omega⟩
    refine ⟨j, by simpa only [R.B.leftPath.darts_length] using hiℓ, ?_⟩
    exact List.getElem_append_left j.isLt


private theorem mirrorIndexWord_last {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    (mirrorIndexWord R)[ℓ]'(by rw [mirrorIndexWord_length]; omega) =
      R.partialMap.edgeInv
        (R.B.rightPath.darts.get ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩) := by
  have hr := List.eq_cons_of_length_one R.B.rightPath.darts_length
  simp only [mirrorIndexWord, hr, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_cons, List.map_nil]
  rw [List.getElem_append_right (by rw [R.B.leftPath.darts_length])]
  simp only [R.B.leftPath.darts_length, Nat.sub_self, List.getElem_cons_zero]
  rfl

private theorem mirrorIndexWord_mirror_missing {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (i : ℕ) (hi : i < (mirrorIndexWord R).length) :
    R.partialMap.mirror.missing (R.partialMap.edgeInv ((mirrorIndexWord R)[i])) ↔
      i + 1 < ℓ := by
  change R.partialMap.missing (R.partialMap.edgeInv _) ↔ _
  rw [← R.partialMap.missing_edgeInv]
  exact mirrorIndexWord_missing R hℓ i hi

private theorem mirrorIndexWord_mirror_succ {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (i : ℕ) (hi : i < (mirrorIndexWord R).length) :
    outerFaceSucc R.partialMap.mirror (R.partialMap.edgeInv ((mirrorIndexWord R)[i])) =
      R.partialMap.edgeInv
        ((mirrorIndexWord R)[(i + 1) % (mirrorIndexWord R).length]'(by
          apply Nat.mod_lt; have := mirrorIndexWord_length R; omega)) := by
  rw [outerFaceSucc_mirror_edgeInv, mirrorIndexWord_succ R i hi]

/-- missing-edge index under the finite mirror symmetry
not the paper result. -/
theorem rep_mirror_isMissingChainAnchor_iff {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (a : Fin R.dartCount) :
    IsMissingChainAnchor R.partialMap.mirror a ↔
      a = R.B.rightPath.darts.get ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩ := by
  have hlen := mirrorIndexWord_length R
  have hlast : R.partialMap.edgeInv ((mirrorIndexWord R)[ℓ]'(by omega)) =
      R.B.rightPath.darts.get ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩ := by
    rw [mirrorIndexWord_last, R.partialMap.edgeInv_invol]
  constructor
  · rintro ⟨ho, hp, hm⟩
    have ho' := (DirectedMapWithMissing.mirror_isOuter_iff R.partialMap a).mp ho
    obtain ⟨i, he⟩ := List.mem_iff_get.mp ((mirrorIndexWord_outer R _).mpr ho')
    have hi := i.isLt
    have ha : a = R.partialMap.edgeInv ((mirrorIndexWord R)[i.val]) := by
      change (mirrorIndexWord R)[i.val] = R.partialMap.edgeInv a at he
      rw [he, R.partialMap.edgeInv_invol]
    rw [ha] at hp hm ⊢
    have hpres := (mirrorIndexWord_mirror_missing R hℓ i.val hi).not.mp hp
    rw [mirrorIndexWord_mirror_succ R i.val hi] at hm
    have hmiss := (mirrorIndexWord_mirror_missing R hℓ
      ((i.val + 1) % (mirrorIndexWord R).length) (Nat.mod_lt _ (by omega))).mp hm
    have hie : i.val = ℓ := by
      by_contra hn
      have hm : (i.val + 1) % (mirrorIndexWord R).length = i.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hm] at hmiss
      omega
    simpa only [hie] using hlast
  · intro ha
    rw [← hlast] at ha
    subst a
    refine ⟨?_, ?_, ?_⟩
    · apply (DirectedMapWithMissing.mirror_isOuter_iff R.partialMap _).mpr
      rw [R.partialMap.edgeInv_invol]
      exact (mirrorIndexWord_outer R _).mp (List.getElem_mem _)
    · exact (mirrorIndexWord_mirror_missing R hℓ ℓ (by omega)).not.mpr (by omega)
    · rw [mirrorIndexWord_mirror_succ R ℓ (by omega)]
      have hm : (ℓ + 1) % (mirrorIndexWord R).length = 0 := by rw [hlen, Nat.mod_self]
      simp only [hm]
      exact (mirrorIndexWord_mirror_missing R hℓ 0 (by omega)).mpr (by omega)

/-- missing-edge index under the finite mirror symmetry
not the paper result. -/
theorem rep_mirror_missingChainDart {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (j : ℕ) (hj : j < ℓ - 1) :
    missingChainDart R.partialMap.mirror
      (R.B.rightPath.darts.get ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩)
      (j + 1) =
      R.partialMap.edgeInv
        (R.B.leftPath.darts.get ⟨j, by rw [R.B.leftPath.darts_length]; omega⟩) := by
  have hlen := mirrorIndexWord_length R
  have hlast : R.B.rightPath.darts.get
      ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩ =
      R.partialMap.edgeInv ((mirrorIndexWord R)[ℓ]'(by omega)) := by
    rw [mirrorIndexWord_last, R.partialMap.edgeInv_invol]
  have hstep : ∀ (m : ℕ) (hm : m < ℓ),
      missingChainDart R.partialMap.mirror
        (R.B.rightPath.darts.get ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩)
        (m + 1) = R.partialMap.edgeInv ((mirrorIndexWord R)[m]'(by have := hm; omega)) := by
    intro m hm
    induction m with
    | zero =>
      change outerFaceSucc R.partialMap.mirror _ = _
      rw [hlast, mirrorIndexWord_mirror_succ R ℓ (by omega)]
      have hz : (ℓ + 1) % (mirrorIndexWord R).length = 0 := by rw [hlen, Nat.mod_self]
      simp only [hz]
    | succ m ih =>
      rw [missingChainDart, Function.iterate_succ_apply']
      change outerFaceSucc R.partialMap.mirror
        (missingChainDart R.partialMap.mirror _ (m + 1)) = _
      rw [ih (by omega), mirrorIndexWord_mirror_succ R m (by omega)]
      simp only [Nat.mod_eq_of_lt
        (show m + 1 < (mirrorIndexWord R).length by omega)]
  rw [hstep j (by omega)]
  congr 1
  exact List.getElem_append_left (by rw [R.B.leftPath.darts_length]; omega)

/-- missing-edge index under the finite mirror symmetry
not the paper result. -/
theorem kmswMirrorSymmetryEquiv_missing_dart {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled})
    (I : DirectedMapWithMissingIso
      (kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.partialMap q.val.out.partialMap.mirror)
    (k : ℕ) (hk : k < ℓ - 1) :
    I.toEquiv ((kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.B.leftPath.darts.get
      ⟨k, by rw [(kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.B.leftPath.darts_length]
             omega⟩) =
      q.val.out.partialMap.edgeInv (q.val.out.B.leftPath.darts.get
        ⟨ℓ - 2 - k, by rw [q.val.out.B.leftPath.darts_length]; omega⟩) := by
  let R := q.val.out
  let S := (kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out
  let a := S.B.leftPath.darts.get
    ⟨ℓ - 1, by rw [S.B.leftPath.darts_length]; omega⟩
  have ha : IsMissingChainAnchor S.partialMap a :=
    (rep_isMissingChainAnchor_iff S hℓ a).mpr rfl
  have hb : I.toEquiv a = R.B.rightPath.darts.get
      ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩ :=
    (rep_mirror_isMissingChainAnchor_iff R hℓ _).mp
      ((isMissingChainAnchor_iff I a).mpr ha)
  have hj : ℓ - 2 - k < ℓ - 1 := by omega
  have hindex : ℓ - 2 - (ℓ - 2 - k) = k := by omega
  have hs := rep_missingChainDart S hℓ (ℓ - 2 - k) hj
  simp only [hindex] at hs
  change I.toEquiv (S.B.leftPath.darts.get _) = R.partialMap.edgeInv _
  rw [← hs, missingChainDart_comm I, hb]
  exact rep_mirror_missingChainDart R hℓ (ℓ - 2 - k) hj

/-- missing-edge index under the finite mirror symmetry
not the paper result. -/
theorem kmswMirrorSymmetryEquiv_missing_dart_rev {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled})
    (I : DirectedMapWithMissingIso
      (kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.partialMap q.val.out.partialMap.mirror)
    (k : Fin (ℓ - 1)) :
    I.toEquiv ((kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.B.leftPath.darts.get
      ⟨(Fin.rev k).val, by
        rw [(kmswMirrorSymmetryEquiv ℓ N hℓ q).val.out.B.leftPath.darts_length]
        have := (Fin.rev k).isLt
        omega⟩) =
      q.val.out.partialMap.edgeInv (q.val.out.B.leftPath.darts.get
        ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; have := k.isLt; omega⟩) := by
  have hindex : ℓ - 2 - (Fin.rev k).val = k.val := by
    rw [Fin.val_rev]
    have := k.isLt
    omega
  have h := kmswMirrorSymmetryEquiv_missing_dart hℓ q I (Fin.rev k).val
    (Fin.rev k).isLt
  simpa only [hindex] using h

end DirectedDistances.KMSW
