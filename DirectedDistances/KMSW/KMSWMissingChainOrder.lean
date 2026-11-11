module

public import DirectedDistances.KMSW.KMSWDiskFiniteSample
public import DirectedDistances.KMSW.KMSWLeftProcedureUniform
public import DirectedDistances.PlanarMap.DirectedMapIso












public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. This direction is the inverse of `faceSucc`. -/
@[expose] def outerFaceSucc (M : DirectedMapWithMissing D) : Equiv.Perm D :=
  M.toCombinatorialMap.faceSucc.symm

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. The successor restricts to the outer-face darts. -/
theorem outerFaceSucc_isOuter_iff (M : DirectedMapWithMissing D) (a : D) :
    M.IsOuter (outerFaceSucc M a) ↔ M.IsOuter a :=
  Equiv.Perm.sameCycle_symm_apply_right

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. A present outer dart immediately precedes a missing dart. -/
@[expose] def IsMissingChainAnchor (M : DirectedMapWithMissing D) (a : D) : Prop :=
  M.IsOuter a ∧ ¬ M.missing a ∧ M.missing (outerFaceSucc M a)

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. Index zero denotes the anchor itself. -/
@[expose] def missingChainDart (M : DirectedMapWithMissing D) (a : D) (j : ℕ) : D :=
  (outerFaceSucc M)^[j] a

private theorem iso_rot_symm_comm (I : DirectedMapWithMissingIso M N) (a : D) :
    I.toEquiv (M.rot.symm a) = N.rot.symm (I.toEquiv a) := by
  apply N.rot.injective
  rw [← I.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. The original face permutation also commutes with the iso. -/
theorem missingChain_faceSucc_comm (I : DirectedMapWithMissingIso M N) (a : D) :
    I.toEquiv (M.toCombinatorialMap.faceSucc a) =
      N.toCombinatorialMap.faceSucc (I.toEquiv a) := by
  change I.toEquiv (M.rot.symm (M.edgeInv a)) = N.rot.symm (N.edgeInv (I.toEquiv a))
  rw [iso_rot_symm_comm, I.edgeInv_comm]

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. The sink-to-source outer successor commutes with the iso. -/
theorem outerFaceSucc_comm (I : DirectedMapWithMissingIso M N) (a : D) :
    I.toEquiv (outerFaceSucc M a) = outerFaceSucc N (I.toEquiv a) := by
  apply N.toCombinatorialMap.faceSucc.injective
  rw [← missingChain_faceSucc_comm]
  simp only [outerFaceSucc, Equiv.apply_symm_apply]

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. Anchors are intrinsic to the partial map. -/
theorem isMissingChainAnchor_iff (I : DirectedMapWithMissingIso M N) (a : D) :
    IsMissingChainAnchor N (I.toEquiv a) ↔ IsMissingChainAnchor M a := by
  unfold IsMissingChainAnchor
  rw [← outerFaceSucc_comm, I.outer_iff, I.missing_iff, I.missing_iff]

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. Every chain index transports without a boundary-path marking. -/
theorem missingChainDart_comm (I : DirectedMapWithMissingIso M N) (a : D) (j : ℕ) :
    I.toEquiv (missingChainDart M a j) = missingChainDart N (I.toEquiv a) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [missingChainDart, Function.iterate_succ_apply'] at ih ⊢
    rw [outerFaceSucc_comm, ih]

private def repBoundaryWord {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :=
  R.B.leftPath.darts ++ R.B.rightPath.darts.reverse.map R.B.map.edgeInv

private theorem repBoundaryWord_rot {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    R.B.outerWord.letters ~r repBoundaryWord R := by
  simpa only [repBoundaryWord, List.append_nil] using R.B.outerSplit.2.1

private theorem repBoundaryWord_nodup {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    (repBoundaryWord R).Nodup :=
  (repBoundaryWord_rot R).nodup_iff.mp R.B.outerWord.nodup

private theorem repBoundaryWord_length {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) :
    (repBoundaryWord R).length = ℓ + 1 := by
  simp only [repBoundaryWord, List.length_append, List.length_map, List.length_reverse,
    R.B.leftPath.darts_length, R.B.rightPath.darts_length]

private theorem repBoundaryWord_outer {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N) (a) :
    a ∈ repBoundaryWord R ↔ R.partialMap.IsOuter a := by
  exact (repBoundaryWord_rot R).mem_iff.symm.trans
    (mem_iff_isOuter R.B.map R.B.outerWord R.B.outerSplit.1 a)

private theorem repBoundaryWord_succ {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (i : ℕ) (hi : i < (repBoundaryWord R).length) :
    R.partialMap.toCombinatorialMap.faceSucc (repBoundaryWord R)[i] =
      (repBoundaryWord R)[(i + 1) % (repBoundaryWord R).length]'(Nat.mod_lt _ (by omega)) := by
  have hm := List.getElem_mem hi
  have hmo := (repBoundaryWord_rot R).mem_iff.mpr hm
  have hf := R.B.outerSplit.1.2.2 _ hmo
  have he := List.formPerm_eq_of_isRotated R.B.outerWord.nodup (repBoundaryWord_rot R)
  change R.B.map.toCombinatorialMap.faceSucc _ = _
  rw [hf, he, List.formPerm_apply_getElem _ (repBoundaryWord_nodup R)]

private theorem repBoundaryWord_pred {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (i : ℕ) (hi : i < (repBoundaryWord R).length) (hi0 : 0 < i) :
    outerFaceSucc R.partialMap (repBoundaryWord R)[i] =
      (repBoundaryWord R)[i - 1] := by
  apply R.partialMap.toCombinatorialMap.faceSucc.injective
  change R.partialMap.toCombinatorialMap.faceSucc
    (R.partialMap.toCombinatorialMap.faceSucc.symm _) = _
  rw [Equiv.apply_symm_apply, repBoundaryWord_succ R (i - 1) (by omega)]
  have he : i - 1 + 1 = i := by omega
  simp only [he, Nat.mod_eq_of_lt hi]

private theorem repBoundaryWord_missing {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (i : ℕ) (hi : i < (repBoundaryWord R).length) :
    R.partialMap.missing (repBoundaryWord R)[i] ↔ i + 1 < ℓ := by
  have hout := (repBoundaryWord_outer R _).mp (List.getElem_mem hi)
  have hleft : R.partialMap.missing (repBoundaryWord R)[i] ↔
      (repBoundaryWord R)[i] ∈ leftMissingDarts R.B := by
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
    have hjl : j.val < (repBoundaryWord R).length := by
      rw [repBoundaryWord_length R]
      have hj' := j.isLt
      have hdl := R.B.leftPath.darts_length
      omega
    have hg : (repBoundaryWord R)[j.val] = R.B.leftPath.darts.get j := by
      exact List.getElem_append_left j.isLt
    have hij : i = j.val := (repBoundaryWord_nodup R).getElem_inj_iff.mp
      (he.trans hg.symm)
    have hdl := R.B.leftPath.darts_length
    omega
  · intro hiℓ
    let j : Fin R.B.leftPath.darts.length :=
      ⟨i, by rw [R.B.leftPath.darts_length]; omega⟩
    refine ⟨j, by simpa only [R.B.leftPath.darts_length] using hiℓ, ?_⟩
    exact List.getElem_append_left j.isLt

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. The anchor is uniquely the last left-path dart. -/
theorem rep_isMissingChainAnchor_iff {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (a : Fin R.dartCount) :
    IsMissingChainAnchor R.partialMap a ↔
      a = R.B.leftPath.darts.get ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩ := by
  have hlen := repBoundaryWord_length R
  have hlast : (repBoundaryWord R)[ℓ - 1]'(by omega) =
      R.B.leftPath.darts.get ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩ :=
    List.getElem_append_left (by rw [R.B.leftPath.darts_length]; omega)
  constructor
  · rintro ⟨ho, hp, hm⟩
    obtain ⟨i, he⟩ := List.mem_iff_get.mp ((repBoundaryWord_outer R a).mpr ho)
    have hi := i.isLt
    change (repBoundaryWord R)[i.val] = a at he
    rw [← he] at hp hm ⊢
    have hpres := (repBoundaryWord_missing R hℓ i.val hi).not.mp hp
    have hi0 : 0 < i.val := by omega
    rw [repBoundaryWord_pred R i.val hi hi0] at hm
    have hmiss := (repBoundaryWord_missing R hℓ (i.val - 1) (by omega)).mp hm
    have hie : i.val = ℓ - 1 := by omega
    simpa only [hie] using hlast
  · intro ha
    rw [← hlast] at ha
    subst a
    refine ⟨(repBoundaryWord_outer R _).mp (List.getElem_mem _), ?_, ?_⟩
    · exact (repBoundaryWord_missing R hℓ (ℓ - 1) (by omega)).not.mpr (by omega)
    · rw [repBoundaryWord_pred R (ℓ - 1) (by omega) (by omega)]
      exact (repBoundaryWord_missing R hℓ (ℓ - 1 - 1) (by omega)).mpr (by omega)

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. Successors enumerate the missing left edges from the sink. -/
theorem rep_missingChainDart {ℓ N : ℕ} (R : KMSWMapRep ℓ 1 N)
    (hℓ : 2 ≤ ℓ) (j : ℕ) (hj : j < ℓ - 1) :
    missingChainDart R.partialMap
      (R.B.leftPath.darts.get ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩)
      (j + 1) =
      R.B.leftPath.darts.get ⟨ℓ - 2 - j, by rw [R.B.leftPath.darts_length]; omega⟩ := by
  have hlen := repBoundaryWord_length R
  have hstep : ∀ m ≤ ℓ - 1,
      missingChainDart R.partialMap
        (R.B.leftPath.darts.get ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩) m =
        (repBoundaryWord R)[ℓ - 1 - m]'(by omega) := by
    intro m hm
    induction m with
    | zero =>
      exact (List.getElem_append_left (by rw [R.B.leftPath.darts_length]; omega)).symm
    | succ m ih =>
      have hm' : m ≤ ℓ - 1 := by omega
      simp only [missingChainDart, Function.iterate_succ_apply'] at ih ⊢
      rw [ih hm', repBoundaryWord_pred R (ℓ - 1 - m) (by omega) (by omega)]
      congr 1
  rw [hstep (j + 1) (by omega)]
  have hind : ℓ - 1 - (j + 1) = ℓ - 2 - j := by omega
  simp only [hind]
  exact List.getElem_append_left (by rw [R.B.leftPath.darts_length]; omega)

/-- intrinsic order of the missing boundary chain of decorated (ℓ,1) maps
not the paper result. Every admissible stage has exactly one intrinsic anchor. -/
theorem kmswDisk_missingChainAnchor_unique {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    ∃! a, IsMissingChainAnchor
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n) a := by
  let R := (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out
  obtain ⟨I⟩ := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ c
  let a := R.B.leftPath.darts.get
    ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩
  have ha : IsMissingChainAnchor R.partialMap a :=
    (rep_isMissingChainAnchor_iff R hℓ a).mpr rfl
  refine ⟨I.toEquiv a, (isMissingChainAnchor_iff I a).mpr ha, ?_⟩
  intro b hb
  have hb' : IsMissingChainAnchor R.partialMap (I.toEquiv.symm b) := by
    apply (isMissingChainAnchor_iff I _).mp
    simpa only [Equiv.apply_symm_apply] using hb
  have he : I.toEquiv.symm b = a := (rep_isMissingChainAnchor_iff R hℓ _).mp hb'
  calc
    b = I.toEquiv (I.toEquiv.symm b) := (I.toEquiv.apply_symm_apply b).symm
    _ = I.toEquiv a := congrArg I.toEquiv he

private def twoLeftClass : KMSWLeftWalkClass 3 2 := ⟨fun _ => 0, by decide⟩

private def twoLeftCode : ℕ → Fin 3 :=
  finiteCodeExtend (n := 3) twoLeftClass.val

private theorem twoLeft_order_values :
    (kmswStage twoLeftCode 2).LL = [4, 2] ∧
      (missingChainDart (kmswStageDirectedMap twoLeftCode 2)
        (stageULHeadDart twoLeftCode 2) 1).1.val = 4 ∧
      (kmswStage twoLeftCode 2).LL.reverse.get ⟨0, by decide⟩ = 2 := by
  decide

private theorem twoLeft_order_obstruction :
    ∃ a : StageDart (kmswStage twoLeftCode 2).nextEdge,
      IsMissingChainAnchor (kmswStageDirectedMap twoLeftCode 2) a ∧
        (missingChainDart (kmswStageDirectedMap twoLeftCode 2) a 1).1.val ≠
          (kmswStage twoLeftCode 2).LL.reverse.get ⟨0, by decide⟩ := by
  refine ⟨stageULHeadDart twoLeftCode 2,
    ⟨Equiv.Perm.SameCycle.rfl, ?_, ?_⟩, ?_⟩
  · change ¬ ((kmswStage twoLeftCode 2).present
      (stageULHeadDart twoLeftCode 2).1.val = false)
    decide
  · change (kmswStage twoLeftCode 2).present
      (outerFaceSucc (kmswStageDirectedMap twoLeftCode 2)
        (stageULHeadDart twoLeftCode 2)).1.val = false
    decide
  · decide

end DirectedDistances.KMSW
