module

public import DirectedDistances.KMSW.KMSWLeftProcedureEndpointFinal
public import DirectedDistances.PlanarMap.KMSWRightReversePartial
public import DirectedDistances.KMSW.KMSWWalkClassRepStage
public import DirectedDistances.KMSW.StageMapCongr
public import DirectedDistances.KMSW.KMSWLeftSimMap
public import DirectedDistances.PlanarMap.KMSWLeftPartialInjective





public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
Marking depends only on the edge-involution saturation of the selected darts. -/
@[expose] def markMissingIsoOfSaturation {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (S S' : Set D)
    (hS : ∀ d ∈ S, M.IsOuter d ∨ M.IsOuter (M.edgeInv d))
    (hS' : ∀ d ∈ S', M.IsOuter d ∨ M.IsOuter (M.edgeInv d))
    (h : ∀ d, (d ∈ S ∨ M.edgeInv d ∈ S) ↔
      (d ∈ S' ∨ M.edgeInv d ∈ S')) :
    DirectedMapWithMissingIso (M.markMissing S hS) (M.markMissing S' hS') where
  toEquiv := Equiv.refl D
  rot_comm := fun _ => rfl
  edgeInv_comm := fun _ => rfl
  missing_iff := fun d => or_congr Iff.rfl (h d).symm
  tail_iff := fun d => and_congr Iff.rfl (not_congr (h d).symm)
  outer_iff := fun _ => Iff.rfl

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
The forward endpoint equivalence applies right endpoint reversal. -/
theorem kmswLeftEndpointSideEquiv_eq (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    kmswLeftEndpointSideEquiv ℓ n hℓ c =
      rightRevClass hℓ (kmswLeftRightSideEquiv ℓ n (by omega) c) := rfl

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
The cut/add code agrees with the infinite prefixed code before the terminal time. -/
theorem kmswLeftCutAdd_code_agree (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    ∀ i < n + ℓ - 1,
      codeExtend ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val i =
        kmswLeftPrefixed ℓ (finiteCodeExtend (n := n + 1) c.val) i := by
  intro i hi
  rw [codeExtend_of_lt _ i hi]
  by_cases hip : i < ℓ - 1
  · rw [kmswLeftWalkCutAdd_symm_val_of_lt ℓ n hℓ c _ hip]
    simp only [kmswLeftPrefixed, ite_eq_left hip]
  · have his : i - (ℓ - 1) < n := by omega
    have hshift := kmswLeftWalkCutAdd_symm_val_shift ℓ n hℓ c
      ⟨i - (ℓ - 1), his⟩
    have heq : ℓ - 1 + (i - (ℓ - 1)) = i := by omega
    simpa only [heq, kmswLeftPrefixed, ite_eq_right hip, finiteCodeExtend,
      Nat.add_sub_cancel, dite_eq_left his] using hshift

private theorem mem_take_iff_get {α : Type*} (xs : List α) (k : ℕ) (d : α) :
    d ∈ xs.take k ↔ ∃ i : Fin xs.length, i.val < k ∧ xs.get i = d := by
  constructor
  · intro hd
    obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp hd
    exact ⟨⟨i, by omega⟩, (Nat.lt_min.mp hi).1, heq⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_take_iff_getElem.mpr ⟨i.val, lt_min hi i.isLt, rfl⟩

private theorem dart_val_injective {N : ℕ} :
    Function.Injective (fun d : StageDart N => (d.1.val, d.2)) := by
  intro d e h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact congrArg (fun p : ℕ × Bool => p.2) h

private theorem rep_prefix_mem_iff {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (k : ℕ)
    (d : Fin (kmswWalkClassRep hN c).dartCount) :
    d ∈ rightPrefixDarts (kmswWalkClassRep hN c).B k ↔
      ((kmswWalkClassRep_mapIso hN c).toEquiv d).1.val ∈
          (kmswStage (codeExtend c) (N - 1)).LR.take k ∧
        ((kmswWalkClassRep_mapIso hN c).toEquiv d).2 = false := by
  let I := kmswWalkClassRep_mapIso hN c
  have hpath := kmswWalkClassRep_rightPath_darts_map hN c
  rw [kmswWalkClassBase_rightPath_darts] at hpath
  have hv := congrArg (List.map (fun d => (d.1.val, d.2))) hpath
  rw [stageDarts_val] at hv
  have htake := congrArg (List.take k) hv
  rw [← List.map_take, ← List.map_take, ← List.map_take] at htake
  change (∃ i : Fin (kmswWalkClassRep hN c).B.rightPath.darts.length,
    i.val < k ∧ (kmswWalkClassRep hN c).B.rightPath.darts.get i = d) ↔ _
  rw [← mem_take_iff_get]
  rw [← List.mem_map_of_injective I.toEquiv.injective]
  rw [← List.mem_map_of_injective dart_val_injective, htake]
  constructor
  · intro hd
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hd
    have heqv : e = (I.toEquiv d).1.val := congrArg Prod.fst heq
    refine ⟨?_, (congrArg Prod.snd heq).symm⟩
    change (I.toEquiv d).1.val ∈ _
    rw [← heqv]
    exact he
  · rintro ⟨he, hb⟩
    exact List.mem_map.mpr ⟨_, he, Prod.ext rfl hb.symm⟩

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
The representative obtained by adding the forced prefix is channeled. -/
theorem kmswLeftCutAdd_rep_isChanneled (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    (kmswWalkClassRep (by omega : 1 ≤ n + ℓ)
      ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val).IsChanneled := by
  have h := (kmswLeftRightSideEquiv ℓ n hℓ c).property
  rw [kmswLeftRightSideEquiv_apply] at h
  exact (KMSWMapIsoClass.isChanneled_mk _).mp h

private theorem leftCutAdd_LR (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    (kmswStage (codeExtend ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val)
      (n + ℓ - 1)).LR = List.range ℓ :=
  kmswWalkClassBase_LR_eq_range_of_downPrefix (by omega) hℓ
    ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val
    ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).property

private theorem leftCutAdd_mark_outer (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    let w := codeExtend ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val
    ∀ d ∈ ({d | d.1.val < ℓ - 1} : Set (StageDart (kmswStage w (n + ℓ - 1)).nextEdge)),
      (kmswStageDirectedMap w (n + ℓ - 1)).IsOuter d ∨
        (kmswStageDirectedMap w (n + ℓ - 1)).IsOuter
          ((kmswStageDirectedMap w (n + ℓ - 1)).edgeInv d) := by
  intro w d hd
  have he : d.1.val ∈ (kmswStage w (n + ℓ - 1)).LR := by
    rw [leftCutAdd_LR ℓ n hℓ c]
    exact List.mem_range.mpr (by exact Nat.lt_of_lt_of_le hd (Nat.sub_le ℓ 1))
  have ho := ((kmswStageDirectedMap_LR_bridge w (n + ℓ - 1) d.1).mp he).2.2
  rcases d with ⟨e, b⟩
  cases b
  · exact Or.inr ho
  · exact Or.inl ho

private theorem leftCutAdd_rep_markIso (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    let cb := ((kmswLeftWalkCutAdd ℓ n hℓ).symm c).val
    let R := kmswWalkClassRep (by omega : 1 ≤ n + ℓ) cb
    Nonempty (DirectedMapWithMissingIso
      (R.B.map.markMissing (rightPrefixDarts R.B (ℓ - 1))
        (rightPrefixDarts_outer R.B (ℓ - 1)))
      ((kmswStageDirectedMap (codeExtend cb) (n + ℓ - 1)).markMissing
        {d | d.1.val < ℓ - 1} (leftCutAdd_mark_outer ℓ n hℓ c))) := by
  intro cb R
  let I := kmswWalkClassRep_mapIso (by omega : 1 ≤ n + ℓ) cb
  let M := kmswStageDirectedMap (codeExtend cb) (n + ℓ - 1)
  let T : Set (StageDart (kmswStage (codeExtend cb) (n + ℓ - 1)).nextEdge) :=
    {d | d.1.val < ℓ - 1 ∧ d.2 = false}
  have hT : ∀ d ∈ T, M.IsOuter d ∨ M.IsOuter (M.edgeInv d) := by
    intro d hd
    exact leftCutAdd_mark_outer ℓ n hℓ c d hd.1
  have hST : ∀ d, I.toEquiv d ∈ T ↔ d ∈ rightPrefixDarts R.B (ℓ - 1) := by
    intro d
    rw [rep_prefix_mem_iff]
    change (_ ∧ _) ↔ (_ ∈ (kmswStage (codeExtend cb) (n + ℓ - 1)).LR.take _ ∧ _)
    rw [leftCutAdd_LR ℓ n hℓ c, List.take_range,
      Nat.min_eq_left (Nat.sub_le ℓ 1), List.mem_range]
  let J := I.markMissing (rightPrefixDarts R.B (ℓ - 1)) T
    (rightPrefixDarts_outer R.B (ℓ - 1)) hT hST
  have hsat : ∀ d, (d ∈ T ∨ M.edgeInv d ∈ T) ↔
      (d ∈ {d | d.1.val < ℓ - 1} ∨ M.edgeInv d ∈ {d | d.1.val < ℓ - 1}) := by
    intro d
    change ((d.1.val < ℓ - 1 ∧ d.2 = false) ∨
      (d.1.val < ℓ - 1 ∧ (!d.2) = false)) ↔
        (d.1.val < ℓ - 1 ∨ d.1.val < ℓ - 1)
    cases d.2 <;> simp
  exact ⟨J.trans (markMissingIsoOfSaturation M T _ hT
    (leftCutAdd_mark_outer ℓ n hℓ c) hsat)⟩

private def stage_markMissing_timeIso (w : ℕ → Fin 3) (a b : ℕ) (hab : a = b)
    (P : ℕ → Bool → Prop)
    (ha : ∀ d : StageDart (kmswStage w a).nextEdge, P d.1.val d.2 →
      (kmswStageDirectedMap w a).IsOuter d ∨
        (kmswStageDirectedMap w a).IsOuter ((kmswStageDirectedMap w a).edgeInv d))
    (hb : ∀ d : StageDart (kmswStage w b).nextEdge, P d.1.val d.2 →
      (kmswStageDirectedMap w b).IsOuter d ∨
        (kmswStageDirectedMap w b).IsOuter ((kmswStageDirectedMap w b).edgeInv d)) :
    DirectedMapWithMissingIso
      ((kmswStageDirectedMap w a).markMissing {d | P d.1.val d.2} ha)
      ((kmswStageDirectedMap w b).markMissing {d | P d.1.val d.2} hb) := by
  subst b
  exact DirectedMapWithMissingIso.refl _

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
At the explicit reversed representative, partialization gives the direct stage map. -/
theorem kmswLeftCutAdd_reverse_partialMapIso (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    let cb := ((kmswLeftWalkCutAdd ℓ n (by omega)).symm c).val
    let R := kmswWalkClassRep (by omega : 1 ≤ n + ℓ) cb
    let hbc := kmswLeftCutAdd_rep_isChanneled ℓ n (by omega) c
    Nonempty (DirectedMapWithMissingIso
      (kmswRightEndpointReverseRep R hℓ hbc).partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) := by
  intro cb R hbc
  obtain ⟨J⟩ := leftCutAdd_rep_markIso ℓ n (by omega) c
  let u := finiteCodeExtend (n := n + 1) c.val
  let w := codeExtend cb
  have ht : n + ℓ - 1 = ℓ - 1 + n := by omega
  have hsim := kmswLeftRun_admissible_mapIso ℓ n c (by omega)
  obtain ⟨K⟩ := hsim
  have htarget : ∀ d : StageDart (kmswStage (kmswLeftPrefixed ℓ u) (n + ℓ - 1)).nextEdge,
      d.1.val < ℓ - 1 →
        (kmswStageDirectedMap (kmswLeftPrefixed ℓ u) (n + ℓ - 1)).IsOuter d ∨
          (kmswStageDirectedMap (kmswLeftPrefixed ℓ u) (n + ℓ - 1)).IsOuter
            ((kmswStageDirectedMap (kmswLeftPrefixed ℓ u) (n + ℓ - 1)).edgeInv d) := by
    have aux (t : ℕ) (heq : t = ℓ - 1 + n) :
        ∀ d : StageDart (kmswStage (kmswLeftPrefixed ℓ u) t).nextEdge,
          d.1.val < ℓ - 1 →
            (kmswStageDirectedMap (kmswLeftPrefixed ℓ u) t).IsOuter d ∨
              (kmswStageDirectedMap (kmswLeftPrefixed ℓ u) t).IsOuter
                ((kmswStageDirectedMap (kmswLeftPrefixed ℓ u) t).edgeInv d) := by
      subst t
      exact kmswLeftSim_markMissing_outer ℓ u (by omega) n
        (kmswLeftRun_admissible_quadrant ℓ n c.val c.property)
    exact aux _ ht
  let P := kmswStageDirectedMapIsoOfPrefix_markMissing w (kmswLeftPrefixed ℓ u)
    (n + ℓ - 1) (kmswLeftCutAdd_code_agree ℓ n (by omega) c)
    (fun e _ => e < ℓ - 1) (leftCutAdd_mark_outer ℓ n (by omega) c) htarget
  let Q := stage_markMissing_timeIso (kmswLeftPrefixed ℓ u)
    (n + ℓ - 1) (ℓ - 1 + n) ht (fun e _ => e < ℓ - 1) htarget
    (kmswLeftSim_markMissing_outer ℓ u (by omega) n
      (kmswLeftRun_admissible_quadrant ℓ n c.val c.property))
  exact ⟨(kmswRightEndpointReverseRep_partialMapIso R hℓ hbc).trans
    (J.trans (P.trans (Q.trans K.symm)))⟩

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
The chosen representative of the output class has the direct run's partial map. -/
theorem kmswLeftEndpointSideEquiv_partialMapIso (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) :
    Nonempty (DirectedMapWithMissingIso
      (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) := by
  let cb := ((kmswLeftWalkCutAdd ℓ n (by omega)).symm c).val
  let R := kmswWalkClassRep (by omega : 1 ≤ n + ℓ) cb
  have hbc : R.IsChanneled := kmswLeftCutAdd_rep_isChanneled ℓ n (by omega) c
  have hq : kmswLeftRightSideEquiv ℓ n (by omega) c =
      ⟨KMSWMapIsoClass.mk R, (KMSWMapIsoClass.isChanneled_mk R).mpr hbc⟩ := by
    apply Subtype.ext
    exact kmswLeftRightSideEquiv_apply ℓ n (by omega) c
  have hF : (kmswLeftEndpointSideEquiv ℓ n hℓ c).val =
      KMSWMapIsoClass.mk (kmswRightEndpointReverseRep R hℓ hbc) := by
    rw [kmswLeftEndpointSideEquiv_eq, hq, rightRevClass_mk]
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff
    (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out
    (kmswRightEndpointReverseRep R hℓ hbc)).mp
      ((Quotient.out_eq _).trans hF)
  obtain ⟨J⟩ := kmswLeftCutAdd_reverse_partialMapIso ℓ n hℓ c
  exact ⟨(KMSWMapRep.partialMapIso_of_baseIso _ _ I).trans J⟩






theorem lem_kmsw_left_procedureReading_partial (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (hn : 1 ≤ n) :
    Function.Bijective (kmswLeftEndpointSideEquiv ℓ n hℓ) ∧
      (∀ c, Nonempty (DirectedMapWithMissingIso
        (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) →
            q = kmswLeftEndpointSideEquiv ℓ n hℓ c) ∧
      (∀ c, KMSWMapIsoClass.leftEndpointNonBoundaryEdgeCount
        (kmswLeftEndpointSideEquiv ℓ n hℓ c).val hℓ = n - 1) := by
  refine ⟨(kmswLeftEndpointSideEquiv ℓ n hℓ).bijective,
    kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ, ?_, ?_⟩
  · intro c q hq
    obtain ⟨I⟩ := hq
    obtain ⟨J⟩ := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ c
    have hclass := (KMSWMapRep.mk_eq_mk_iff_partialMapIso hℓ
      q.val.out (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out).mpr
        ⟨I.trans J.symm⟩
    rw [show KMSWMapIsoClass.mk q.val.out = q.val from Quotient.out_eq _,
      show KMSWMapIsoClass.mk (kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out =
        (kmswLeftEndpointSideEquiv ℓ n hℓ c).val from Quotient.out_eq _] at hclass
    exact Subtype.ext hclass
  · intro c
    exact KMSWMapIsoClass.leftEndpointNonBoundaryEdgeCount_eq _ hℓ hn

private def partialMapOneIso {N : ℕ} (R : KMSWMapRep 1 1 N) :
    DirectedMapWithMissingIso R.partialMap R.B.map := by
  have hnone (d : Fin R.dartCount) : d ∉ leftMissingDarts R.B := by
    rintro ⟨i, hi, _⟩
    have hlen := R.B.leftPath.darts_length
    omega
  exact {
    toEquiv := Equiv.refl _
    rot_comm := fun _ => rfl
    edgeInv_comm := fun _ => rfl
    missing_iff := by
      intro d
      change R.B.map.missing d ↔ d ∈ leftMissingDarts R.B ∨
        R.B.map.edgeInv d ∈ leftMissingDarts R.B
      simp only [R.B.noMissingDarts d, hnone d, hnone (R.B.map.edgeInv d), or_self]
    tail_iff := by
      intro d
      change R.B.map.tail d ↔ R.B.map.tail d ∧
        ¬ (d ∈ leftMissingDarts R.B ∨ R.B.map.edgeInv d ∈ leftMissingDarts R.B)
      simp only [hnone d, hnone (R.B.map.edgeInv d), or_self,
        not_false_eq_true, and_true]
    outer_iff := fun _ => Iff.rfl }

/-- not adopted; simple-boundary restriction not assumed; not the paper result.
The `ℓ = 1` partial-map comparison includes Lean's `n = 0`, which is outside
the paper's convention `ℕ = {1,2,…}`. No count clause or singleton ruling is asserted. -/
theorem kmswLeftEndpointSideEquivOne_partialMapIso (n : ℕ)
    (c : KMSWLeftWalkClass 1 n) :
    Nonempty (DirectedMapWithMissingIso
      (kmswLeftEndpointSideEquivOne n c).val.out.partialMap
      (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) := by
  let cb := ((kmswLeftWalkCutAdd 1 n le_rfl).symm c).val
  let R := kmswWalkClassRep (by omega : 1 ≤ n + 1) cb
  have hF : (kmswLeftEndpointSideEquivOne n c).val = KMSWMapIsoClass.mk R :=
    kmswLeftRightSideEquiv_apply 1 n le_rfl c
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff
    (kmswLeftEndpointSideEquivOne n c).val.out R).mp
      ((Quotient.out_eq _).trans hF)
  let u := finiteCodeExtend (n := n + 1) c.val
  have hagree : ∀ i < n, codeExtend cb i = u i := by
    intro i hi
    have h := kmswLeftCutAdd_code_agree 1 n le_rfl c i (by omega)
    simpa only [kmswLeftPrefixed, Nat.sub_self, Nat.not_lt_zero,
      ite_false, Nat.sub_zero] using h
  let J := kmswStageDirectedMapIsoOfPrefix (codeExtend cb) u n hagree
  exact ⟨(KMSWMapRep.partialMapIso_of_baseIso _ _ I).trans
    ((partialMapOneIso R).trans ((kmswWalkClassRep_mapIso (by omega) cb).trans J))⟩

end DirectedDistances.KMSW
