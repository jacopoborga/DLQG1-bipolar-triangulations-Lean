module

public import DirectedDistances.KMSW.KMSWMissingChainStage
public import DirectedDistances.KMSW.KMSWMirrorRootedLaw
public import DirectedDistances.KMSW.KMSWDiskFiniteSample
public import DirectedDistances.KMSW.KMSWLeftProcedureUniform

/-! # Finite rooted law for the decorated disk sample

The root is the outer dart of the selected missing edge, with Boolean orientation `true`.
These are helpers for the proposed I4 reading only, not an adopted source interpretation. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory

private theorem inverse_cycle_get {α : Type*} [DecidableEq α]
    (l : List α) (f : Equiv.Perm α) (hl : l.Nodup)
    (hf : ∀ a ∈ l, f a = l.formPerm a) (j : ℕ) (hj : j < l.length) :
    (f.symm)^[j + 1] (l[0]'(by omega)) = l[l.length - 1 - j]'(by omega) := by
  induction j with
  | zero =>
    change f.symm l[0] = _
    apply f.injective
    rw [Equiv.apply_symm_apply, hf _ (List.getElem_mem _),
      List.formPerm_apply_getElem _ hl]
    have he : l.length - 1 - 0 + 1 = l.length := by omega
    simp only [he, Nat.mod_self]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    apply f.injective
    rw [Equiv.apply_symm_apply, hf _ (List.getElem_mem _),
      List.formPerm_apply_getElem _ hl]
    have he : l.length - 1 - (j + 1) + 1 = l.length - 1 - j := by omega
    simp only [he, Nat.mod_eq_of_lt (show l.length - 1 - j < l.length by omega)]

private theorem stage_word_head (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWord w n)[0]'(List.length_pos_of_ne_nil (stageOuterWord_nonempty w n)) =
      stageULHeadDart w n := by
  have hne := (kmswStage_UL_nonempty_active_last w n).1
  cases he : (kmswStage w n).UL with
  | nil => exact (hne he).elim
  | cons e es =>
    simp [stageOuterWord, stageDarts, stageULHeadDart, he]

private theorem stage_word_length (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWord w n).length =
      (kmswStage w n).UL.length + (kmswStage w n).UR.length +
      (kmswStage w n).LR.length + (kmswStage w n).LL.length := by
  simp [stageOuterWord, stageDarts, Nat.add_assoc]

private theorem stage_chain_value (w : ℕ → Fin 3) (n j : ℕ)
    (hj : j < (kmswStage w n).LL.length) :
    let d := missingChainDart (kmswStageDirectedMap w n) (stageULHeadDart w n) (j + 1)
    (d.1.val, d.2) = ((kmswStage w n).LL[j], true) := by
  have hlen := stage_word_length w n
  have hUL : 0 < (kmswStage w n).UL.length :=
    List.length_pos_of_ne_nil (kmswStage_UL_nonempty_active_last w n).1
  have hji : j < (stageOuterWord w n).length := by omega
  have he := inverse_cycle_get (stageOuterWord w n) (kmswMap w n).faceSucc
    (stageOuterWord_nodup w n) (stageOuterWord_faceSucc w n) j hji
  rw [stage_word_head] at he
  dsimp only [missingChainDart, outerFaceSucc]
  change (((kmswMap w n).faceSucc.symm^[j + 1] (stageULHeadDart w n)).1.val,
    ((kmswMap w n).faceSucc.symm^[j + 1] (stageULHeadDart w n)).2) = _
  rw [he]
  have hv : (stageOuterWordVal w n)[(stageOuterWord w n).length - 1 - j]? =
      some ((stageOuterWord w n)[(stageOuterWord w n).length - 1 - j].1.val,
        (stageOuterWord w n)[(stageOuterWord w n).length - 1 - j].2) := by
    simp only [stageOuterWordVal, List.getElem?_map,
      List.getElem?_eq_getElem (show (stageOuterWord w n).length - 1 - j <
        (stageOuterWord w n).length by omega), Option.map_some]
  have hv' : (stageOuterWordVal w n)[(stageOuterWord w n).length - 1 - j]? =
      some ((kmswStage w n).LL[j], true) := by
    rw [stageOuterWordVal_eq_runs]
    rw [List.getElem?_append_right (by
      simp only [List.length_append, List.length_map, List.length_reverse]
      omega)]
    simp only [List.length_append, List.length_map, List.length_reverse]
    rw [List.getElem?_eq_getElem (by
      simp only [List.length_map, List.length_reverse]
      omega)]
    simp only [List.getElem_map, List.getElem_reverse]
    congr 3
    omega
  exact Option.some.inj (hv.symm.trans hv')

private theorem stage_head_anchor (w : ℕ → Fin 3) (n : ℕ)
    (hLL : 0 < (kmswStage w n).LL.length) :
    IsMissingChainAnchor (kmswStageDirectedMap w n) (stageULHeadDart w n) := by
  refine ⟨Equiv.Perm.SameCycle.rfl, ?_, ?_⟩
  · change ¬ (kmswStage w n).present (stageULHeadDart w n).1.val = false
    have hp := (kmswStage_status w n).2.1 _
      (List.head_mem (kmswStage_UL_nonempty_active_last w n).1)
    change (kmswStage w n).present
      ((kmswStage w n).UL.head (kmswStage_UL_nonempty_active_last w n).1) = true at hp
    change ¬ (kmswStage w n).present
      ((kmswStage w n).UL.head (kmswStage_UL_nonempty_active_last w n).1) = false
    rw [hp]
    decide
  · have hv := congrArg Prod.fst (stage_chain_value w n 0 hLL)
    change (outerFaceSucc (kmswStageDirectedMap w n) (stageULHeadDart w n)).1.val =
      (kmswStage w n).LL[0] at hv
    change (kmswStage w n).present
      (outerFaceSucc (kmswStageDirectedMap w n) (stageULHeadDart w n)).1.val = false
    rw [hv]
    exact ((kmswStage_status w n).1 _
      (stageRun_edge_bound w n _ (Or.inl (Or.inr (List.getElem_mem hLL))))).mpr
        (Or.inr (List.getElem_mem hLL))

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
@[expose] noncomputable def kmswDiskRootDart {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    StageDart (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge :=
  (⟨kmswLLCreatedEdge (finiteCodeExtend (n := n + 1) c.val) (kmswDiskFirstHit c k),
    by
      let u := finiteCodeExtend (n := n + 1) c.val
      have he := (kmswDiskFirstHit_spec c k).2.2.2.2.2
      rw [← he]
      exact stageRun_edge_bound u n _
        (Or.inl (Or.inr (List.mem_reverse.mp (List.get_mem _ _))))⟩, true)

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem kmswDiskRootDart_eq_missingChainDart {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (a : StageDart (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge)
    (ha : IsMissingChainAnchor
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n) a) :
    kmswDiskRootDart c k =
      missingChainDart (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)
        a (ℓ - 1 - k.val) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let j : Fin (ℓ - 1) := ⟨ℓ - 2 - k.val, by omega⟩
  have hlen : (kmswStage u n).LL.length = ℓ - 1 :=
    (kmswDiskFiniteSample_index_bound c k).1
  have hj : j.val + 1 = ℓ - 1 - k.val := by dsimp only [j]; omega
  obtain ⟨b, _, hb⟩ := kmswDisk_missingChainAnchor_unique hℓ c
  have he : a = stageULHeadDart u n :=
    (hb a ha).trans (hb _ (stage_head_anchor u n (by omega))).symm
  have hchain := stage_chain_value u n j.val (by rw [hlen]; exact j.isLt)
  rw [hj] at hchain
  apply Prod.ext
  · apply Fin.ext
    have hedge := kmswDisk_missingChainDart_edge hℓ c a ha j
    dsimp only at hedge
    have hreverse : (kmswStage u n).LL.get
        ⟨j.val, by rw [hlen]; exact j.isLt⟩ =
        (kmswStage u n).LL.reverse.get
          ⟨k.val, by simpa only [List.length_reverse, hlen] using k.isLt⟩ := by
      simp only [List.get_eq_getElem, List.getElem_reverse]
      congr 1
      dsimp only [j]
      omega
    rw [hreverse, (kmswDiskFirstHit_spec c k).2.2.2.2.2, hj] at hedge
    exact hedge.symm
  · change true = _
    rw [he]
    exact (congrArg Prod.snd hchain).symm

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem kmswDiskRootDart_isOuter {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).IsOuter
      (kmswDiskRootDart c k) := by
  obtain ⟨a, ha, _⟩ := kmswDisk_missingChainAnchor_unique hℓ c
  rw [kmswDiskRootDart_eq_missingChainDart hℓ c k a ha]
  have houter : ∀ j, (kmswStageDirectedMap
      (finiteCodeExtend (n := n + 1) c.val) n).IsOuter
      (missingChainDart (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1) c.val) n) a j) := by
    intro j
    induction j with
    | zero => exact ha.1
    | succ j ih =>
      simp only [missingChainDart, Function.iterate_succ_apply'] at ih ⊢
      exact (outerFaceSucc_isOuter_iff _ _).mpr ih
  exact houter _

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem iso_leftPathDart_eq_rootDart {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n)
    (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled})
    (I : DirectedMapWithMissingIso q.val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))
    (k : Fin (ℓ - 1)) :
    I.toEquiv (q.val.out.B.leftPath.darts.get
      ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; omega⟩) =
      kmswDiskRootDart c k := by
  let R := q.val.out
  let a := R.B.leftPath.darts.get
    ⟨ℓ - 1, by rw [R.B.leftPath.darts_length]; omega⟩
  let j : Fin (ℓ - 1) := ⟨ℓ - 2 - k.val, by omega⟩
  have ha : IsMissingChainAnchor R.partialMap a :=
    (rep_isMissingChainAnchor_iff R hℓ a).mpr rfl
  have hIa := (isMissingChainAnchor_iff I a).mpr ha
  have hrep := rep_missingChainDart R hℓ j.val j.isLt
  have hind : ℓ - 2 - j.val = k.val := by dsimp only [j]; omega
  have hrep' : missingChainDart R.partialMap a (j.val + 1) =
      R.B.leftPath.darts.get ⟨k.val, by rw [R.B.leftPath.darts_length]; omega⟩ :=
    hrep.trans (congrArg R.B.leftPath.darts.get (Fin.ext hind))
  have hj : j.val + 1 = ℓ - 1 - k.val := by dsimp only [j]; omega
  rw [← hrep', missingChainDart_comm, hj]
  exact (kmswDiskRootDart_eq_missingChainDart hℓ c k (I.toEquiv a) hIa).symm

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
@[expose] noncomputable def rootedStage {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : RootedFiniteDirectedMapClass :=
  (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) p.1.val) n).toRootedClass
    (kmswDiskRootDart p.1 p.2)

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem rootedDecorated_eq_rootedStage {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    rootedDecorated (kmswLeftEndpointSideEquiv ℓ n hℓ c, k) = rootedStage (c, k) := by
  obtain ⟨I⟩ := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ c
  apply (DirectedMapWithMissing.toRootedClass_eq_iff _ _ _ _).mpr
  exact ⟨I, iso_leftPathDart_eq_rootDart hℓ c _ I k⟩

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem rootedDecorated_uniform_eq_rootedStage (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedDecorated =
      ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStage := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  let : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  let f := fun p : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} × Fin (ℓ - 1) =>
    ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)
  have h := congrArg (fun μ => μ.map (rootedStage (ℓ := ℓ) (n := n)))
    (kmswDiskFiniteSample_uniform_prod ℓ n hℓ)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  have hf : rootedStage ∘ f = rootedDecorated := by
    funext p
    exact (rootedDecorated_eq_rootedStage hℓ
      ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1) p.2).symm.trans
        (congrArg (fun q => rootedDecorated (q, p.2))
          ((kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply p.1))
  rw [hf] at h
  exact h

/-- finite rooted law of the decorated disk sample as the KMSW stage map rooted at the
edge created at the first hit (I4 proposed ordered-boundary-dart reading, NOT adopted; -/
theorem rootedDecorated_uniform_firstHit_eq_rootedStage (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    letI : MeasurableSpace ℕ := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => (rootedDecorated p,
          kmswDiskFirstHit ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1) p.2)) =
      ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => (rootedStage p, kmswDiskFirstHit p.1 p.2)) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  let : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  let : MeasurableSpace ℕ := ⊤
  let f := fun p : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} × Fin (ℓ - 1) =>
    ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)
  let g := fun p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1) =>
    (rootedStage p, kmswDiskFirstHit p.1 p.2)
  have h := congrArg (fun μ => μ.map g) (kmswDiskFiniteSample_uniform_prod ℓ n hℓ)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  have hf : g ∘ f = fun p => (rootedDecorated p,
      kmswDiskFirstHit ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1) p.2) := by
    funext p
    apply Prod.ext
    · exact (rootedDecorated_eq_rootedStage hℓ
        ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1) p.2).symm.trans
          (congrArg (fun q => rootedDecorated (q, p.2))
            ((kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply p.1))
    · rfl
  rw [hf] at h
  exact h

end DirectedDistances.KMSW
