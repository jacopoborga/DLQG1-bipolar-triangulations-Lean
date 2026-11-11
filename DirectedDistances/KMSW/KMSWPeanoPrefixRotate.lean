module

public import DirectedDistances.KMSW.KMSWPeanoPrefix
public import DirectedDistances.KMSW.KMSWInverseStepLink
public import DirectedDistances.PlanarMap.BipolarPeanoConfiguration
public import DirectedDistances.PlanarMap.BipolarInnerFaceShape
public import DirectedDistances.KMSW.StageOuterWordSucc

/-! Supporting lemmas for paper labels `def-kmsw`, `thm-kmsw` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
variable {B : BipolarTriangulationWithBoundaryBase D ℓ r}
variable {c : KMSWWalkClass ℓ r n} {j : ℕ}
variable {hj : j < B.map.toCombinatorialMap.numEdges}



@[expose] noncomputable def kmswPeanoRotateDartMap
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge) : D :=
  let s := kmswStage (codeExtend c) j
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  if h : d.1.val < s.nextEdge then
    P.emb.dartMap (⟨d.1.val, h⟩, d.2)
  else if d.1.val = s.nextEdge then
    if d.2 then B.map.toCombinatorialMap.edgeInv b else b
  else if d.2 then B.map.toCombinatorialMap.edgeInv q else q



theorem kmswPeanoRotateDartMap_old
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoRotateDartMap P hj1
      (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
        P.emb.dartMap d := by
  simp only [kmswPeanoRotateDartMap, outerSucc_castDart, Fin.val_castLE,
    d.1.isLt, ↓reduceDIte]



theorem kmswPeanoRotateDartMap_new
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1) (side : Bool) :
    let s := kmswStage (codeExtend c) j
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    kmswPeanoRotateDartMap P hj1 (⟨s.nextEdge, by
        have h := (kmswStage_step_up_facts (codeExtend c) j hcode).1
        dsimp only [s]
        omega⟩, side) =
        (if side then B.map.toCombinatorialMap.edgeInv b else b) ∧
      kmswPeanoRotateDartMap P hj1 (⟨s.nextEdge + 1, by
          have h := (kmswStage_step_up_facts (codeExtend c) j hcode).1
          dsimp only [s]
          omega⟩, side) =
        (if side then B.map.toCombinatorialMap.edgeInv q else q) := by
  dsimp only
  constructor <;> simp only [kmswPeanoRotateDartMap, Nat.lt_irrefl,
    Nat.not_succ_lt_self, Nat.add_one_ne_self,
    ↓reduceDIte, ↓reduceIte]



theorem kmswPeanoRotateDartMap_flip
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge) :
    kmswPeanoRotateDartMap P hj1 (edgeFlip _ d) =
      B.map.toCombinatorialMap.edgeInv (kmswPeanoRotateDartMap P hj1 d) := by
  change kmswPeanoRotateDartMap P hj1 (d.1, !d.2) =
    B.map.toCombinatorialMap.edgeInv (kmswPeanoRotateDartMap P hj1 d)
  by_cases hold : d.1.val < (kmswStage (codeExtend c) j).nextEdge
  · have hf := P.emb.flip_comm (⟨d.1.val, hold⟩, d.2)
    change P.emb.dartMap (⟨d.1.val, hold⟩, !d.2) =
      B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (⟨d.1.val, hold⟩, d.2)) at hf
    simpa only [kmswPeanoRotateDartMap, hold, ↓reduceDIte] using hf
  · by_cases hnew : d.1.val = (kmswStage (codeExtend c) j).nextEdge <;>
      cases hs : d.2 <;>
      simp only [kmswPeanoRotateDartMap, hold, hnew, hs, Nat.lt_irrefl,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
        B.map.toCombinatorialMap.edgeInv_invol]

private theorem rotate_config
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    PeanoStepConfig B j hj1 .rotate := by
  rw [← hkind]
  exact peanoStepKind_config B j hj1



theorem kmswPeanoRotate_third_side
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)) =
      B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.faceSucc (peanoEdge B ⟨j, hj⟩)) := by
  have hc := rotate_config hj1 hkind
  have hf := hc.2.2.2.2.1
  change B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.faceSucc (peanoEdge B ⟨j, hj⟩))) =
    B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩) at hf
  exact (B.map.toCombinatorialMap.rot.eq_symm_apply.mp hf.symm)



theorem kmswPeanoRotateDartMap_root
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1) :
    kmswPeanoRotateDartMap P hj1 (kmswRootedStage (codeExtend c) (j + 1)).root =
      peanoEdge B ⟨j + 1, hj1⟩ := by
  have ha := (kmswStage_step_up_facts (codeExtend c) j hcode).2.2.2.2.2.2.1
  change kmswPeanoRotateDartMap P hj1
    (⟨(kmswStage (codeExtend c) (j + 1)).active, _⟩, false) = _
  simp only [kmswPeanoRotateDartMap, ha, Nat.lt_irrefl, ↓reduceDIte,
    ↓reduceIte, Bool.false_eq_true]

private theorem rotate_present_old (hcode : codeExtend c j = 1)
    {e : ℕ} (he : e < (kmswStage (codeExtend c) j).nextEdge) :
    (kmswStage (codeExtend c) (j + 1)).present e =
      (kmswStage (codeExtend c) j).present e := by
  have ha := (kmswStage_step_up_facts (codeExtend c) j hcode).2.2.2.2.2.2.1
  change (kmswStep (kmswStage (codeExtend c) j) (codeExtend c j)).present e = _
  rw [kmswStep_present_existing _ _ he]
  change (if e = (kmswStage (codeExtend c) (j + 1)).active then true
    else (kmswStage (codeExtend c) j).present e) = _
  rw [ha, ite_eq_right (ne_of_lt he)]



theorem kmswPeanoRotateDartMap_tail
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : ¬ (kmswRootedStage (codeExtend c) (j + 1)).map.missing d) :
    (kmswRootedStage (codeExtend c) (j + 1)).map.tail d ↔
      B.map.tail (kmswPeanoRotateDartMap P hj1 d) := by
  change ¬ (kmswStage (codeExtend c) (j + 1)).present d.1.val = false at hd
  have hp := Bool.eq_true_of_not_eq_false hd
  change ((kmswStage (codeExtend c) (j + 1)).present d.1.val = true ∧
    d.2 = false) ↔ _
  simp only [hp, true_and]
  by_cases hold : d.1.val < (kmswStage (codeExtend c) j).nextEdge
  · have hpold : (kmswStage (codeExtend c) j).present d.1.val = true := by
      rw [← rotate_present_old hcode hold]
      exact hp
    have hh := P.emb.tail_comm (⟨d.1.val, hold⟩, d.2) (by
      change ¬ (kmswStage (codeExtend c) j).present d.1.val = false
      rw [hpold]
      decide)
    change ((kmswStage (codeExtend c) j).present d.1.val = true ∧
      d.2 = false) ↔ B.map.tail (P.emb.dartMap (⟨d.1.val, hold⟩, d.2)) at hh
    simpa only [kmswPeanoRotateDartMap, hold, ↓reduceDIte, hpold, true_and] using hh
  · have hc := kmswStage_step_up_facts (codeExtend c) j hcode
    have hbound := d.1.isLt
    have he : d.1.val = (kmswStage (codeExtend c) j).nextEdge := by
      by_contra hne
      have hid : d.1.val = (kmswStage (codeExtend c) j).nextEdge + 1 := by
        have hcount := hc.1
        omega
      have hmissing := hc.2.2.2.2.2.2.2.2.1
      rw [hid, hmissing] at hp
      contradiction
    have hb := peanoEdge_forward B (⟨j + 1, hj1⟩ : Fin _)
    have hbinv := (B.map.tail_iff _ (B.noMissingDarts _)).1 hb
    cases hs : d.2 <;>
      simp only [kmswPeanoRotateDartMap, he, Nat.lt_irrefl,
        ↓reduceDIte, ↓reduceIte, hs, Bool.false_eq_true, Bool.true_eq_false, hb, hbinv]




@[expose] def KMSWRotateFreshVertex
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges) : Prop :=
  ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    dartTailVertex B.map (P.emb.dartMap d) ≠
      dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩)

private theorem rotate_rot_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact ⟨-1, by simp⟩




theorem kmswPeanoRotate_new_not_in_old_image
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    b ∉ Set.range P.emb.dartMap ∧
      B.map.toCombinatorialMap.edgeInv b ∉ Set.range P.emb.dartMap ∧
      q ∉ Set.range P.emb.dartMap ∧
      B.map.toCombinatorialMap.edgeInv q ∉ Set.range P.emb.dartMap := by
  dsimp only
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  have hinvb : B.map.toCombinatorialMap.edgeInv b ∉ Set.range P.emb.dartMap := by
    rintro ⟨d, hd⟩
    exact hfresh d (congrArg (dartTailVertex B.map) hd)
  have hflip {x : D} (hx : x ∉ Set.range P.emb.dartMap) :
      B.map.toCombinatorialMap.edgeInv x ∉ Set.range P.emb.dartMap := by
    rintro ⟨d, hd⟩
    apply hx
    refine ⟨edgeFlip _ d, ?_⟩
    calc
      P.emb.dartMap (edgeFlip _ d) =
          B.map.toCombinatorialMap.edgeInv (P.emb.dartMap d) := P.emb.flip_comm d
      _ = x := by rw [hd, B.map.toCombinatorialMap.edgeInv_invol]
  have hb : b ∉ Set.range P.emb.dartMap := by
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hflip hinvb
  have hq : q ∉ Set.range P.emb.dartMap := by
    rintro ⟨d, hd⟩
    apply hfresh d
    exact (congrArg (dartTailVertex B.map) hd).trans
      (rotate_rot_vertex (B.map.toCombinatorialMap.edgeInv b))
  exact ⟨hb, hinvb, hq, hflip hq⟩

private theorem rotate_new_edges_distinct
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    b ≠ q ∧ b ≠ B.map.toCombinatorialMap.edgeInv q := by
  dsimp only
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  have htailq : dartTailVertex B.map q = dartHeadVertex B.map b :=
    rotate_rot_vertex (B.map.toCombinatorialMap.edgeInv b)
  have hinvq : B.map.toCombinatorialMap.edgeInv q =
      B.map.toCombinatorialMap.faceSucc a := by
    dsimp only [q]
    rw [kmswPeanoRotate_third_side (hj := by omega) hj1 hkind,
      B.map.toCombinatorialMap.edgeInv_invol]
  have htailb : dartTailVertex B.map b = dartTailVertex B.map a :=
    (rotate_config hj1 hkind).2.1
  constructor
  · intro h
    exact peano_dart_no_loop B b
      ((congrArg (dartTailVertex B.map) h).trans htailq)
  · intro h
    apply peano_dart_no_loop B a
    calc
      dartTailVertex B.map a = dartTailVertex B.map b := htailb.symm
      _ = dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv q) :=
        congrArg (dartTailVertex B.map) h
      _ = dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc a) :=
        congrArg (dartTailVertex B.map) hinvq
      _ = dartHeadVertex B.map a := (corner_consecutiveDarts B a).2.2

private theorem rotate_four_darts_injective (b q : D)
    (hbq : b ≠ q) (hbiq : b ≠ B.map.toCombinatorialMap.edgeInv q) :
    Function.Injective (fun d : Fin 2 × Bool =>
      if d.1 = 0 then
        if d.2 then B.map.toCombinatorialMap.edgeInv b else b
      else if d.2 then B.map.toCombinatorialMap.edgeInv q else q) := by
  have hiq : B.map.toCombinatorialMap.edgeInv b ≠ q := by
    intro h
    apply hbiq
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
      congrArg B.map.toCombinatorialMap.edgeInv h
  have hiiq : B.map.toCombinatorialMap.edgeInv b ≠
      B.map.toCombinatorialMap.edgeInv q := fun h => hbq
        (B.map.toCombinatorialMap.edgeInv.injective h)
  have hbb := B.map.toCombinatorialMap.edgeInv_ne b
  have hqq := B.map.toCombinatorialMap.edgeInv_ne q
  rintro ⟨i, x⟩ ⟨i', y⟩ h
  fin_cases i <;> fin_cases i' <;> cases x <;> cases y <;>
    simp only [Fin.isValue, Fin.reduceFinMk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals first
    | exact (hbq h).elim
    | exact (hbq h.symm).elim
    | exact (hbiq h).elim
    | exact (hbiq h.symm).elim
    | exact (hiq h).elim
    | exact (hiq h.symm).elim
    | exact (hiiq h).elim
    | exact (hiiq h.symm).elim
    | exact (hbb h).elim
    | exact (hbb h.symm).elim
    | exact (hqq h).elim
    | exact (hqq h.symm).elim




theorem kmswPeanoRotateDartMap_injective_of_freshVertex
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    Function.Injective (kmswPeanoRotateDartMap P hj1) := by
  let s := kmswStage (codeExtend c) j
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  let v : Fin 2 × Bool → D := fun d =>
    if d.1 = 0 then if d.2 then B.map.toCombinatorialMap.edgeInv b else b
    else if d.2 then B.map.toCombinatorialMap.edgeInv q else q
  obtain ⟨hbq, hbiq⟩ := rotate_new_edges_distinct hj1 hkind
  have hv : Function.Injective v := rotate_four_darts_injective b q hbq hbiq
  have hnot := kmswPeanoRotate_new_not_in_old_image P hj1 hfresh
  have hdisj (d : StageDart s.nextEdge) (e : Fin 2 × Bool) :
      P.emb.dartMap d ≠ v e := by
    dsimp only [v]
    split_ifs <;> intro h
    · exact hnot.2.1 ⟨d, h⟩
    · exact hnot.1 ⟨d, h⟩
    · exact hnot.2.2.2 ⟨d, h⟩
    · exact hnot.2.2.1 ⟨d, h⟩
  let enc : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge → Fin 2 × Bool :=
    fun d => (if d.1.val = s.nextEdge then 0 else 1, d.2)
  have hval (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
      (hd : ¬ d.1.val < s.nextEdge) :
      kmswPeanoRotateDartMap P hj1 d = v (enc d) := by
    dsimp only [kmswPeanoRotateDartMap, enc, v, s] at hd ⊢
    rw [dite_eq_right hd]
    by_cases hid : d.1.val = (kmswStage (codeExtend c) j).nextEdge
    · simp [hid, b]
    · simp [hid, q, b]
  have holdval (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
      (hd : d.1.val < s.nextEdge) :
      kmswPeanoRotateDartMap P hj1 d = P.emb.dartMap (⟨d.1.val, hd⟩, d.2) := by
    dsimp only [s] at hd
    simp only [kmswPeanoRotateDartMap, hd, ↓reduceDIte]
  have hcount := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  intro d e h
  by_cases hd : d.1.val < s.nextEdge
  · by_cases he : e.1.val < s.nextEdge
    · rw [holdval d hd, holdval e he] at h
      have hh : ((⟨d.1.val, hd⟩, d.2) : StageDart s.nextEdge) =
          (⟨e.1.val, he⟩, e.2) := P.emb.injective h
      exact Prod.ext (Fin.ext (congrArg (fun x : StageDart s.nextEdge => x.1.val) hh))
        (congrArg (fun x : StageDart s.nextEdge => x.2) hh)
    · rw [holdval d hd, hval e he] at h
      exact (hdisj (⟨d.1.val, hd⟩, d.2) (enc e) h).elim
  · by_cases he : e.1.val < s.nextEdge
    · rw [holdval e he, hval d hd] at h
      exact (hdisj (⟨e.1.val, he⟩, e.2) (enc d) h.symm).elim
    · have henc : enc d = enc e := hv (by rw [← hval d hd, ← hval e he]; exact h)
      have hid := congrArg (fun x : Fin 2 × Bool => x.1.val) henc
      have hside := congrArg Prod.snd henc
      have hdb := d.1.isLt
      have heb := e.1.isLt
      have hde : d.1.val = e.1.val := by
        dsimp only [enc, s] at hid
        dsimp only [s] at hd he ⊢
        split_ifs at hid <;> simp only [Fin.val_zero, Fin.val_one] at hid <;> omega
      exact Prod.ext (Fin.ext hde) hside

private theorem rotate_eq_or_inv_of_index_eq {d e : D}
    (h : peanoIndex B d = peanoIndex B e) :
    d = e ∨ d = B.map.toCombinatorialMap.edgeInv e := by
  classical
  have hidx := congrArg Fin.val h
  change (firstVisitOrder B).idxOf (peanoForwardDart B d) =
    (firstVisitOrder B).idxOf (peanoForwardDart B e) at hidx
  have hfwd : peanoForwardDart B d = peanoForwardDart B e :=
    (List.idxOf_inj
      ((mem_firstVisitOrder_iff B _).2 (peanoForwardDart_tail B d))).1 hidx
  by_cases hd : B.map.tail d <;> by_cases he : B.map.tail e
  · exact Or.inl (by simpa only [peanoForwardDart, hd, he, ↓reduceIte] using hfwd)
  · exact Or.inr (by simpa only [peanoForwardDart, hd, he, ↓reduceIte] using hfwd)
  · have hde : B.map.toCombinatorialMap.edgeInv d = e := by
      simpa only [peanoForwardDart, hd, he, ↓reduceIte] using hfwd
    exact Or.inr (by
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
        congrArg B.map.toCombinatorialMap.edgeInv hde)
  · have hde : B.map.toCombinatorialMap.edgeInv d =
        B.map.toCombinatorialMap.edgeInv e := by
      simpa only [peanoForwardDart, hd, he, ↓reduceIte] using hfwd
    exact Or.inl (B.map.toCombinatorialMap.edgeInv.injective hde)




theorem kmswPeanoRotate_third_is_future
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    j + 1 < (peanoIndex B (B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)))).val := by
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  have hnot := kmswPeanoRotate_new_not_in_old_image P hj1 hfresh
  have hgt : j < (peanoIndex B q).val := by
    by_contra hle
    obtain ⟨d, hd⟩ := P.edges_cover_prefix (peanoIndex B q).val (by omega)
    have hidx : peanoIndex B (P.emb.dartMap d) = peanoIndex B q := Fin.ext hd
    rcases rotate_eq_or_inv_of_index_eq hidx with he | he
    · exact hnot.2.2.1 ⟨d, he⟩
    · exact hnot.2.2.2 ⟨d, he⟩
  have hne : (peanoIndex B q).val ≠ j + 1 := by
    intro h
    have hidx : peanoIndex B q = peanoIndex B b := by
      rw [peanoIndex_peanoEdge]
      exact Fin.ext h
    obtain ⟨hbq, hbiq⟩ := rotate_new_edges_distinct hj1 hkind
    rcases rotate_eq_or_inv_of_index_eq hidx with he | he
    · exact hbq he.symm
    · apply hbiq
      change b = B.map.toCombinatorialMap.edgeInv q
      rw [he, B.map.toCombinatorialMap.edgeInv_invol]
  change j + 1 < (peanoIndex B q).val
  omega

private theorem rotate_old_index_ne_next
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hfresh : KMSWRotateFreshVertex P hj1)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    (peanoIndex B (P.emb.dartMap d)).val ≠ j + 1 := by
  intro h
  have hidx : peanoIndex B (P.emb.dartMap d) =
      peanoIndex B (peanoEdge B ⟨j + 1, hj1⟩) := by
    rw [peanoIndex_peanoEdge]
    exact Fin.ext h
  have hnot := kmswPeanoRotate_new_not_in_old_image P hj1 hfresh
  rcases rotate_eq_or_inv_of_index_eq hidx with he | he
  · exact hnot.1 ⟨d, he⟩
  · exact hnot.2.1 ⟨d, he⟩





theorem kmswPeanoRotateDartMap_prefix_of_freshVertex
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    let t := kmswStage (codeExtend c) (j + 1)
    let φ := kmswPeanoRotateDartMap P hj1
    (∀ d : StageDart t.nextEdge,
      t.present d.1.val = true ↔ (peanoIndex B (φ d)).val ≤ j + 1) ∧
    (∀ k : ℕ, k ≤ j + 1 → ∃ d : StageDart t.nextEdge,
      (peanoIndex B (φ d)).val = k) ∧
    (∀ d : StageDart t.nextEdge,
      t.present d.1.val = false ↔ d.1.val ∈ t.UR ∨ d.1.val ∈ t.LL) ∧
    (∀ d : StageDart t.nextEdge,
      t.present d.1.val = false → j + 1 < (peanoIndex B (φ d)).val) := by
  dsimp only
  let s := kmswStage (codeExtend c) j
  let t := kmswStage (codeExtend c) (j + 1)
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  have hc := kmswStage_step_up_facts (codeExtend c) j hcode
  have hfuture := kmswPeanoRotate_third_is_future P hj1 hkind hfresh
  have hprefix (d : StageDart t.nextEdge) :
      t.present d.1.val = true ↔
        (peanoIndex B (kmswPeanoRotateDartMap P hj1 d)).val ≤ j + 1 := by
    by_cases hold : d.1.val < s.nextEdge
    · have hp := P.present_prefix (⟨d.1.val, hold⟩, d.2)
      have hne := rotate_old_index_ne_next P hj1 hfresh (⟨d.1.val, hold⟩, d.2)
      dsimp only [s] at hold
      dsimp only [t]
      rw [rotate_present_old hcode hold]
      simp only [kmswPeanoRotateDartMap, hold, ↓reduceDIte]
      exact hp.trans (by omega)
    · have hbound := d.1.isLt
      by_cases hid : d.1.val = s.nextEdge
      · have hp : t.present d.1.val = true := by
          rw [hid]
          exact hc.2.2.2.2.2.2.2.1
        apply iff_of_true hp
        dsimp only [s] at hid
        cases hs : d.2 <;>
          simp only [kmswPeanoRotateDartMap, hid, Nat.lt_irrefl, hs,
            Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, peanoIndex_edgeInv,
            peanoIndex_peanoEdge, le_refl]
      · have hid1 : d.1.val = s.nextEdge + 1 := by
          have hcount := hc.1
          dsimp only [s, t] at hold hid hbound ⊢
          omega
        have hp : t.present d.1.val = false := by
          rw [hid1]
          exact hc.2.2.2.2.2.2.2.2.1
        dsimp only [s] at hid1
        rw [hp]
        simp only [kmswPeanoRotateDartMap, hid1, Nat.not_succ_lt_self,
          Nat.add_one_ne_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, false_iff]
        cases hs : d.2 <;>
          simpa only [hs, Bool.false_eq_true, ↓reduceIte, peanoIndex_edgeInv] using
            (Nat.not_le_of_lt hfuture)
  refine ⟨hprefix, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hkj : k ≤ j
    · obtain ⟨d, hd⟩ := P.edges_cover_prefix k hkj
      refine ⟨outerSucc_castDart
        (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d, ?_⟩
      rw [kmswPeanoRotateDartMap_old]
      exact hd
    · have hk1 : k = j + 1 := by omega
      refine ⟨(kmswRootedStage (codeExtend c) (j + 1)).root, ?_⟩
      rw [kmswPeanoRotateDartMap_root P hj1 hcode, peanoIndex_peanoEdge]
      exact hk1.symm
  · intro d
    exact (kmswStage_status (codeExtend c) (j + 1)).1 d.1.val d.1.isLt
  · intro d hd
    by_contra hnot
    have hp := (hprefix d).2 (by omega)
    rw [hd] at hp
    contradiction

private theorem rotate_iter_vertex (m : ℕ) (d : D) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[m] d) =
      dartTailVertex B.map d := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (rotate_rot_vertex _).trans ih




private theorem kmswPeanoRotate_new_vertex_firstReturn
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    let φ := kmswPeanoRotateDartMap P hj1
    let ρ : D → D := B.map.toCombinatorialMap.rot
    (∃ k : ℕ, 0 < k ∧ ρ^[k] (B.map.toCombinatorialMap.edgeInv b) = q ∧
      ∀ m : ℕ, 0 < m → m < k →
        ρ^[m] (B.map.toCombinatorialMap.edgeInv b) ∉ Set.range φ) ∧
    (∃ k : ℕ, 0 < k ∧ ρ^[k] q = B.map.toCombinatorialMap.edgeInv b ∧
      ∀ m : ℕ, 0 < m → m < k → ρ^[m] q ∉ Set.range φ) := by
  dsimp only
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  let φ := kmswPeanoRotateDartMap P hj1
  let ρ := B.map.toCombinatorialMap.rot
  have hqv : dartTailVertex B.map q = dartHeadVertex B.map b := rotate_rot_vertex _
  have hqne : q ≠ B.map.toCombinatorialMap.edgeInv b := by
    intro h
    have hne := (rotate_new_edges_distinct hj1 hkind).2
    apply hne
    change b = B.map.toCombinatorialMap.edgeInv q
    rw [h, B.map.toCombinatorialMap.edgeInv_invol]
  have hinvqv : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv q) ≠
      dartHeadVertex B.map b := by
    rw [← hqv]
    exact (peano_dart_no_loop B q).symm
  have hclass (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
      (hv : dartTailVertex B.map (φ d) = dartHeadVertex B.map b) :
      φ d = B.map.toCombinatorialMap.edgeInv b ∨ φ d = q := by
    by_cases hold : d.1.val < (kmswStage (codeExtend c) j).nextEdge
    · apply False.elim
      apply hfresh (⟨d.1.val, hold⟩, d.2)
      simpa only [φ, kmswPeanoRotateDartMap, hold, ↓reduceDIte] using hv
    · by_cases hnew : d.1.val = (kmswStage (codeExtend c) j).nextEdge
      · cases hs : d.2
        · have hh : φ d = b := by
            simp only [φ, kmswPeanoRotateDartMap, hnew, Nat.lt_irrefl, hs, b,
              Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
          exact ((peano_dart_no_loop B b) (hh ▸ hv)).elim
        · exact Or.inl (by
            simp only [φ, kmswPeanoRotateDartMap, hnew, Nat.lt_irrefl, hs, b, ↓reduceDIte, ↓reduceIte])
      · cases hs : d.2
        · exact Or.inr (by
            simp only [φ, kmswPeanoRotateDartMap, hold, hnew, hs, q, b,
              Bool.false_eq_true, ↓reduceDIte, ↓reduceIte])
        · have hh : φ d = B.map.toCombinatorialMap.edgeInv q := by
            simp only [φ, kmswPeanoRotateDartMap, hold, hnew, hs, q, b, ↓reduceDIte, ↓reduceIte]
          exact (hinvqv (hh ▸ hv)).elim
  have hqmem : q ∈ Set.range φ := by
    have hh := (kmswPeanoRotateDartMap_new P hj1 hcode false).2
    exact ⟨_, hh⟩
  have hibmem : B.map.toCombinatorialMap.edgeInv b ∈ Set.range φ := by
    have hh := (kmswPeanoRotateDartMap_new P hj1 hcode true).1
    exact ⟨_, hh⟩
  constructor
  · refine ⟨1, Nat.zero_lt_one, rfl, ?_⟩
    intro m hm hmk
    omega
  · have hex : ∃ k : ℕ, 0 < k ∧ (ρ : D → D)^[k] q ∈ Set.range φ := by
      refine ⟨orderOf ρ, orderOf_pos ρ, ?_⟩
      have hpow := congrArg (fun σ : Equiv.Perm D => σ q) (pow_orderOf_eq_one ρ)
      have he : (ρ : D → D)^[orderOf ρ] q = q := by
        simpa only [Equiv.Perm.coe_pow, Equiv.Perm.one_apply] using hpow
      rw [he]
      exact hqmem
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    obtain ⟨d, hd⟩ := hk.2
    have hgap : ∀ m : ℕ, 0 < m → m < k → (ρ : D → D)^[m] q ∉ Set.range φ := by
      intro m hm hmk hmem
      exact Nat.find_min hex hmk ⟨hm, hmem⟩
    have hv : dartTailVertex B.map (φ d) = dartHeadVertex B.map b := by
      rw [hd]
      exact (rotate_iter_vertex k q).trans hqv
    rcases hclass d hv with he | he
    · exact ⟨k, hk.1, hd.symm.trans he, hgap⟩
    · have hreturn : (ρ : D → D)^[k] q = q := hd.symm.trans he
      cases hk0 : k with
      | zero => have := hk.1; omega
      | succ m =>
        have hprev : (ρ : D → D)^[m] q = B.map.toCombinatorialMap.edgeInv b := by
          apply ρ.injective
          change ρ ((ρ : D → D)^[m] q) = q
          have hh := hreturn
          rw [hk0, Function.iterate_succ_apply'] at hh
          exact hh
        cases m with
        | zero => exact (hqne hprev).elim
        | succ m =>
          apply False.elim
          apply hgap (m + 1) (by omega) (by omega)
          rw [hprev]
          exact hibmem

private def rotate_castDart {k l : ℕ} (h : k = l) (d : StageDart k) : StageDart l :=
  (Fin.cast h d.1, d.2)

private theorem rotate_castDart_injective {k l : ℕ} (h : k = l) :
    Function.Injective (rotate_castDart h) := by
  cases h
  exact fun _ _ he => he

private theorem rotate_castDart_rot {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (d : StageDart k) :
    rotate_castDart h (σ d) = StageRotation.resize h σ (rotate_castDart h d) := by
  cases h
  rfl

private def rotate_newDart (hcode : codeExtend c j = 1) (e : Fin 2) (side : Bool) :
    StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge :=
  (⟨(kmswStage (codeExtend c) j).nextEdge + e.val, by
    have hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
    have he := e.isLt
    omega⟩, side)

private theorem rotate_newDart_rot (hcode : codeExtend c j = 1) :
    (kmswRootedStage (codeExtend c) (j + 1)).map.rot (rotate_newDart (B := B) hcode 0 true) =
        rotate_newDart (B := B) hcode 1 false ∧
      (kmswRootedStage (codeExtend c) (j + 1)).map.rot (rotate_newDart (B := B) hcode 1 false) =
        rotate_newDart (B := B) hcode 0 true := by
  let s := kmswStage (codeExtend c) j
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, true)
  let hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  have hr : StageRotation.resize hc (stageRot (codeExtend c) (j + 1)) =
      StageRotation.up s.nextEdge (stageRot (codeExtend c) j) a A :=
    StageRotation.step_up s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ j) (stageRot (codeExtend c) j) _ (by rw [hcode]; rfl)
  have hcast (e : Fin 2) (side : Bool) :
      rotate_castDart hc (rotate_newDart (B := B) hcode e side) =
        StageRotation.allocation s.nextEdge 2 (.inr (e, side)) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  have ht := StageRotation.up_new s.nextEdge (stageRot (codeExtend c) j) a A
  constructor
  · apply rotate_castDart_injective hc
    change rotate_castDart hc (stageRot (codeExtend c) (j + 1)
      (rotate_newDart (B := B) hcode 0 true)) = _
    rw [rotate_castDart_rot, hr, hcast, hcast, ht.2.2.1]
  · apply rotate_castDart_injective hc
    change rotate_castDart hc (stageRot (codeExtend c) (j + 1)
      (rotate_newDart (B := B) hcode 1 false)) = _
    rw [rotate_castDart_rot, hr, hcast, hcast, ht.2.2.2]




theorem kmswPeanoRotateDartMap_new_vertex_rot_induced
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : (d.1.val = (kmswStage (codeExtend c) j).nextEdge ∧ d.2 = true) ∨
      (d.1.val = (kmswStage (codeExtend c) j).nextEdge + 1 ∧ d.2 = false)) :
    ∃ k : ℕ, 0 < k ∧
      (B.map.toCombinatorialMap.rot : D → D)^[k] (kmswPeanoRotateDartMap P hj1 d) =
        kmswPeanoRotateDartMap P hj1
          ((kmswRootedStage (codeExtend c) (j + 1)).map.rot d) ∧
      ∀ m : ℕ, 0 < m → m < k →
        (B.map.toCombinatorialMap.rot : D → D)^[m]
          (kmswPeanoRotateDartMap P hj1 d) ∉ Set.range (kmswPeanoRotateDartMap P hj1) := by
  have hrot := rotate_newDart_rot (B := B) hcode
  have hval0 : kmswPeanoRotateDartMap P hj1 (rotate_newDart (B := B) hcode 0 true) =
      B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩) := by
    exact (kmswPeanoRotateDartMap_new P hj1 hcode true).1
  have hval1 : kmswPeanoRotateDartMap P hj1 (rotate_newDart (B := B) hcode 1 false) =
      B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)) := by
    exact (kmswPeanoRotateDartMap_new P hj1 hcode false).2
  have hfirst := kmswPeanoRotate_new_vertex_firstReturn P hj1 hcode hkind hfresh
  rcases hd with hd | hd
  · have heq : d = rotate_newDart (B := B) hcode 0 true :=
      Prod.ext (Fin.ext (by simpa only [rotate_newDart, Fin.val_zero, Nat.add_zero] using hd.1)) hd.2
    rw [heq, hrot.1, hval0, hval1]
    exact hfirst.1
  · have heq : d = rotate_newDart (B := B) hcode 1 false :=
      Prod.ext (Fin.ext (by simpa only [rotate_newDart, Fin.val_one] using hd.1)) hd.2
    rw [heq, hrot.2, hval1, hval0]
    exact hfirst.2

private theorem rotate_old_root_rot (hcode : codeExtend c j = 1) :
    (kmswRootedStage (codeExtend c) (j + 1)).map.rot
      (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
        (kmswRootedStage (codeExtend c) j).root) =
      rotate_newDart (B := B) hcode 0 false := by
  let s := kmswStage (codeExtend c) j
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, true)
  let hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  have hr : StageRotation.resize hc (stageRot (codeExtend c) (j + 1)) =
      StageRotation.up s.nextEdge (stageRot (codeExtend c) j) a A :=
    StageRotation.step_up s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ j) (stageRot (codeExtend c) j) _ (by rw [hcode]; rfl)
  have hcastOld :
      rotate_castDart hc
        (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
          (kmswRootedStage (codeExtend c) j).root) =
        StageRotation.allocation s.nextEdge 2 (.inl a) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  have hcastNew : rotate_castDart hc (rotate_newDart (B := B) hcode 0 false) =
      StageRotation.allocation s.nextEdge 2 (.inr (0, false)) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  apply rotate_castDart_injective hc
  change rotate_castDart hc (stageRot (codeExtend c) (j + 1) _) = _
  rw [rotate_castDart_rot, hr, hcastOld, hcastNew, StageRotation.up_old]
  simp only [↓reduceIte]




theorem kmswPeanoRotateDartMap_old_root_rot_induced
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    let d := outerSucc_castDart
      (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
      (kmswRootedStage (codeExtend c) j).root
    ∃ k : ℕ, 0 < k ∧
      (B.map.toCombinatorialMap.rot : D → D)^[k] (kmswPeanoRotateDartMap P hj1 d) =
        kmswPeanoRotateDartMap P hj1
          ((kmswRootedStage (codeExtend c) (j + 1)).map.rot d) ∧
      ∀ m : ℕ, 0 < m → m < k →
        (B.map.toCombinatorialMap.rot : D → D)^[m]
          (kmswPeanoRotateDartMap P hj1 d) ∉ Set.range (kmswPeanoRotateDartMap P hj1) := by
  dsimp only
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · rw [Function.iterate_one, rotate_old_root_rot (B := B) hcode,
      kmswPeanoRotateDartMap_old]
    have hroot : P.emb.dartMap (kmswRootedStage (codeExtend c) j).root =
        peanoEdge B ⟨j, hj⟩ := P.emb.root_comm
    rw [hroot]
    have hnew : kmswPeanoRotateDartMap P hj1 (rotate_newDart (B := B) hcode 0 false) =
        peanoEdge B ⟨j + 1, hj1⟩ :=
      (kmswPeanoRotateDartMap_new P hj1 hcode false).1
    rw [hnew]
    exact (rotate_config hj1 hkind).1.symm
  · intro m hm hmk
    omega

private theorem rotate_missing_reverse_rot (hcode : codeExtend c j = 1) :
    (kmswRootedStage (codeExtend c) (j + 1)).map.rot
      (rotate_newDart (B := B) hcode 1 true) =
      outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
        (edgeFlip _ (kmswRootedStage (codeExtend c) j).root) := by
  let s := kmswStage (codeExtend c) j
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, true)
  let hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  have hr : StageRotation.resize hc (stageRot (codeExtend c) (j + 1)) =
      StageRotation.up s.nextEdge (stageRot (codeExtend c) j) a A :=
    StageRotation.step_up s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ j) (stageRot (codeExtend c) j) _ (by rw [hcode]; rfl)
  have hcastOld :
      rotate_castDart hc
        (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
          (edgeFlip _ (kmswRootedStage (codeExtend c) j).root)) =
        StageRotation.allocation s.nextEdge 2 (.inl A) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  have hcastNew : rotate_castDart hc (rotate_newDart (B := B) hcode 1 true) =
      StageRotation.allocation s.nextEdge 2 (.inr (1, true)) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  apply rotate_castDart_injective hc
  change rotate_castDart hc (stageRot (codeExtend c) (j + 1) _) = _
  rw [rotate_castDart_rot, hr, hcastOld, hcastNew]
  exact (StageRotation.up_new s.nextEdge (stageRot (codeExtend c) j) a A).2.1




theorem kmswPeanoRotateDartMap_missing_reverse_rot_induced
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hedge : d.1.val = (kmswStage (codeExtend c) j).nextEdge + 1)
    (hside : d.2 = true) :
    ∃ k : ℕ, 0 < k ∧
      (B.map.toCombinatorialMap.rot : D → D)^[k] (kmswPeanoRotateDartMap P hj1 d) =
        kmswPeanoRotateDartMap P hj1
          ((kmswRootedStage (codeExtend c) (j + 1)).map.rot d) ∧
      ∀ m : ℕ, 0 < m → m < k →
        (B.map.toCombinatorialMap.rot : D → D)^[m]
          (kmswPeanoRotateDartMap P hj1 d) ∉ Set.range (kmswPeanoRotateDartMap P hj1) := by
  have heq : d = rotate_newDart (B := B) hcode 1 true :=
    Prod.ext (Fin.ext (by simpa only [rotate_newDart, Fin.val_one] using hedge)) hside
  rw [heq]
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · rw [Function.iterate_one, rotate_missing_reverse_rot (B := B) hcode,
      kmswPeanoRotateDartMap_old]
    have hflip := P.emb.flip_comm (kmswRootedStage (codeExtend c) j).root
    change P.emb.dartMap (edgeFlip _ (kmswRootedStage (codeExtend c) j).root) =
      B.map.toCombinatorialMap.edgeInv
        (P.emb.dartMap (kmswRootedStage (codeExtend c) j).root) at hflip
    rw [hflip, P.emb.root_comm]
    have hnew := (kmswPeanoRotateDartMap_new P hj1 hcode true).2
    change kmswPeanoRotateDartMap P hj1 (rotate_newDart (B := B) hcode 1 true) = _ at hnew
    rw [hnew, kmswPeanoRotate_third_side (hj := hj) hj1 hkind,
      B.map.toCombinatorialMap.edgeInv_invol]
    change B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.edgeInv _)) = _
    exact B.map.toCombinatorialMap.rot.apply_symm_apply _
  · intro m hm hmk
    omega

private theorem rotate_old_rot (hcode : codeExtend c j = 1)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    let cast := outerSucc_castDart
      (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
    let a := (kmswRootedStage (codeExtend c) j).root
    let A := edgeFlip _ a
    (kmswRootedStage (codeExtend c) (j + 1)).map.rot (cast d) =
      if d = a then rotate_newDart (B := B) hcode 0 false
      else if stageRot (codeExtend c) j d = A then rotate_newDart (B := B) hcode 1 true
      else cast (stageRot (codeExtend c) j d) := by
  dsimp only
  let s := kmswStage (codeExtend c) j
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, true)
  let hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  have hr : StageRotation.resize hc (stageRot (codeExtend c) (j + 1)) =
      StageRotation.up s.nextEdge (stageRot (codeExtend c) j) a A :=
    StageRotation.step_up s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ j) (stageRot (codeExtend c) j) _ (by rw [hcode]; rfl)
  have hcastOld (e : StageDart s.nextEdge) :
      rotate_castDart hc
        (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) e) =
        StageRotation.allocation s.nextEdge 2 (.inl e) :=
    Prod.ext (Fin.ext rfl) rfl
  have hcastNew (e : Fin 2) (v : Bool) :
      rotate_castDart hc (rotate_newDart (B := B) hcode e v) =
        StageRotation.allocation s.nextEdge 2 (.inr (e, v)) :=
    Prod.ext (Fin.ext rfl) rfl
  change (kmswRootedStage (codeExtend c) (j + 1)).map.rot
    (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
      if d = a then rotate_newDart (B := B) hcode 0 false
      else if stageRot (codeExtend c) j d = A then rotate_newDart (B := B) hcode 1 true
      else outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
        (stageRot (codeExtend c) j d)
  apply rotate_castDart_injective hc
  change rotate_castDart hc (stageRot (codeExtend c) (j + 1) _) = _
  rw [rotate_castDart_rot, hr, hcastOld, StageRotation.up_old]
  by_cases hd : d = a
  · simp only [hd, ↓reduceIte, hcastNew]
  · by_cases hA : stageRot (codeExtend c) j d = A <;>
      simp only [hd, hA, ↓reduceIte, hcastNew, hcastOld]

private theorem rotate_active_rot (hcode : codeExtend c j = 1) :
    let a := (kmswRootedStage (codeExtend c) j).root
    let A := edgeFlip _ a
    (kmswRootedStage (codeExtend c) (j + 1)).map.rot
        (rotate_newDart (B := B) hcode 0 false) =
      if stageRot (codeExtend c) j a = A then rotate_newDart (B := B) hcode 1 true
      else outerSucc_castDart
        (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
        (stageRot (codeExtend c) j a) := by
  dsimp only
  let s := kmswStage (codeExtend c) j
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge _ le_rfl⟩, true)
  let hc := (kmswStage_step_up_facts (codeExtend c) j hcode).1
  have hr : StageRotation.resize hc (stageRot (codeExtend c) (j + 1)) =
      StageRotation.up s.nextEdge (stageRot (codeExtend c) j) a A :=
    StageRotation.step_up s (act_lt_nextEdge _ le_rfl)
      (stageRotation_UL_bound _ j) (stageRot (codeExtend c) j) _ (by rw [hcode]; rfl)
  have hcastOld (e : StageDart s.nextEdge) :
      rotate_castDart hc
        (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) e) =
        StageRotation.allocation s.nextEdge 2 (.inl e) :=
    Prod.ext (Fin.ext rfl) rfl
  have hcastNew (e : Fin 2) (v : Bool) :
      rotate_castDart hc (rotate_newDart (B := B) hcode e v) =
        StageRotation.allocation s.nextEdge 2 (.inr (e, v)) :=
    Prod.ext (Fin.ext rfl) rfl
  change (kmswRootedStage (codeExtend c) (j + 1)).map.rot
    (rotate_newDart (B := B) hcode 0 false) =
      if stageRot (codeExtend c) j a = A then rotate_newDart (B := B) hcode 1 true
      else outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
        (stageRot (codeExtend c) j a)
  apply rotate_castDart_injective hc
  change rotate_castDart hc (stageRot (codeExtend c) (j + 1) _) = _
  rw [rotate_castDart_rot, hr, hcastNew, (StageRotation.up_new _ _ a A).1]
  by_cases hA : stageRot (codeExtend c) j a = A <;>
    simp only [hA, ↓reduceIte, hcastNew, hcastOld]

private theorem rotate_before_arc {α β : Type*} [DecidableEq α]
    (ρ : Equiv.Perm β) (i : α → β) (hi : Function.Injective i)
    (A q : α) (x z : β) (hxz : x ≠ z) (hz : ρ z = i A)
    (k : ℕ) (hk : 0 < k) (hr : (ρ : β → β)^[k] x = i q)
    (hm : ∀ m : ℕ, 0 < m → m < k → (ρ : β → β)^[m] x ∉ Set.range i) :
    ∃ v : ℕ, 0 < v ∧ v ≤ k ∧
      (ρ : β → β)^[v] x = (if q = A then z else i q) ∧
      ∀ m : ℕ, 0 < m → m < v →
        (ρ : β → β)^[m] x ∉ Set.range i ∧ (ρ : β → β)^[m] x ≠ z := by
  have step (m : ℕ) (he : (ρ : β → β)^[m] x = z) :
      (ρ : β → β)^[m + 1] x = i A := by
    rw [Function.iterate_succ_apply', he, hz]
  by_cases hq : q = A
  · have hk1 : 1 < k := by
      by_contra hh
      have hke : k = 1 := by omega
      have hh : ρ x = ρ z := by simpa only [hke, Function.iterate_one, hq, hz] using hr
      exact hxz (ρ.injective hh)
    refine ⟨k - 1, by omega, by omega, ?_, ?_⟩
    · simp only [hq, ↓reduceIte]
      apply ρ.injective
      rw [← Function.iterate_succ_apply' (f := (ρ : β → β))]
      change (ρ : β → β)^[k - 1 + 1] x = ρ z
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k), hz, ← hq]
      exact hr
    · intro m hm0 hmv
      refine ⟨hm m hm0 (by omega), ?_⟩
      intro he
      exact hm (m + 1) (by omega) (by omega) ⟨A, (step m he).symm⟩
  · refine ⟨k, hk, le_rfl, ?_, ?_⟩
    · simpa only [hq, ↓reduceIte] using hr
    · intro m hm0 hmk
      refine ⟨hm m hm0 hmk, ?_⟩
      intro he
      have hs := step m he
      by_cases heq : m + 1 = k
      · rw [heq, hr] at hs
        exact hq (hi hs)
      · exact hm (m + 1) (by omega) (by omega) ⟨A, hs.symm⟩

private theorem rotate_avoid_after {α β : Type*}
    (ρ : Equiv.Perm β) (i : α → β) (hi : Function.Injective i)
    (a d : α) (b : β) (hb : ρ (i a) = b) (hd : d ≠ a)
    (k : ℕ)
    (hm : ∀ m : ℕ, 0 < m → m < k → (ρ : β → β)^[m] (i d) ∉ Set.range i)
    (m : ℕ) (hm0 : 0 < m) (hmk : m < k) :
    (ρ : β → β)^[m] (i d) ≠ b := by
  intro he
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hu : (ρ : β → β)^[u] (i d) = i a := by
    apply ρ.injective
    rw [← Function.iterate_succ_apply' (f := (ρ : β → β)), hb]
    exact he
  by_cases hu0 : u = 0
  · simp only [hu0, Function.iterate_zero, id_eq] at hu
    exact hd (hi hu)
  · exact hm u (by omega) (by omega) ⟨a, hu.symm⟩

private theorem rotate_image_cases
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge) :
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    kmswPeanoRotateDartMap P hj1 d ∈ Set.range P.emb.dartMap ∨
      kmswPeanoRotateDartMap P hj1 d = b ∨
      kmswPeanoRotateDartMap P hj1 d = B.map.toCombinatorialMap.edgeInv b ∨
      kmswPeanoRotateDartMap P hj1 d = q ∨
      kmswPeanoRotateDartMap P hj1 d = B.map.toCombinatorialMap.edgeInv q := by
  dsimp only
  by_cases hold : d.1.val < (kmswStage (codeExtend c) j).nextEdge
  · exact Or.inl ⟨(⟨d.1.val, hold⟩, d.2), by
      simp only [kmswPeanoRotateDartMap, hold, ↓reduceDIte]⟩
  · by_cases hnew : d.1.val = (kmswStage (codeExtend c) j).nextEdge
    · cases hs : d.2
      · exact Or.inr (Or.inl (by simp only [kmswPeanoRotateDartMap, hnew, Nat.lt_irrefl, hs,
          Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]))
      · exact Or.inr (Or.inr (Or.inl (by simp only [kmswPeanoRotateDartMap, hnew,
          Nat.lt_irrefl, hs, ↓reduceDIte, ↓reduceIte])))
    · cases hs : d.2
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only [kmswPeanoRotateDartMap,
          hold, hnew, hs, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp only [kmswPeanoRotateDartMap,
          hold, hnew, hs, ↓reduceDIte, ↓reduceIte]))))




theorem kmswPeanoRotateDartMap_rot_induced
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge) :
    ∃ k : ℕ, 0 < k ∧
      (B.map.toCombinatorialMap.rot : D → D)^[k]
          (kmswPeanoRotateDartMap P hj1 d) =
        kmswPeanoRotateDartMap P hj1
          ((kmswRootedStage (codeExtend c) (j + 1)).map.rot d) ∧
      ∀ m : ℕ, 0 < m → m < k →
        (B.map.toCombinatorialMap.rot : D → D)^[m]
          (kmswPeanoRotateDartMap P hj1 d) ∉
            Set.range (kmswPeanoRotateDartMap P hj1) := by
  classical
  let s := kmswStage (codeExtend c) j
  let a := (kmswRootedStage (codeExtend c) j).root
  let A := edgeFlip _ a
  let i := P.emb.dartMap
  let σ := stageRot (codeExtend c) j
  let ρ := B.map.toCombinatorialMap.rot
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := ρ (B.map.toCombinatorialMap.edgeInv b)
  let z := B.map.toCombinatorialMap.edgeInv q
  let φ := kmswPeanoRotateDartMap P hj1
  let cast := outerSucc_castDart
    (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j))
  have hroot : i a = peanoEdge B ⟨j, hj⟩ := P.emb.root_comm
  have hA : i A = B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j, hj⟩) := by
    have hh := P.emb.flip_comm a
    change i A = B.map.toCombinatorialMap.edgeInv (i a) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv hroot)
  have hba : ρ (i a) = b := by
    rw [hroot]
    exact (rotate_config hj1 hkind).1.symm
  have hzthird : z = B.map.toCombinatorialMap.faceSucc (peanoEdge B ⟨j, hj⟩) := by
    dsimp only [z, q, ρ, b]
    rw [kmswPeanoRotate_third_side (hj := hj) hj1 hkind,
      B.map.toCombinatorialMap.edgeInv_invol]
  have hza : ρ z = i A := by
    rw [hzthird, hA]
    exact B.map.toCombinatorialMap.rot.apply_symm_apply _
  have hnot := kmswPeanoRotate_new_not_in_old_image P hj1 hfresh
  have hb : b ∉ Set.range i := hnot.1
  have hz : z ∉ Set.range i := hnot.2.2.2
  have hφold (e : StageDart s.nextEdge) : φ (cast e) = i e :=
    kmswPeanoRotateDartMap_old P hj1 e
  have hφb : φ (rotate_newDart (B := B) hcode 0 false) = b :=
    (kmswPeanoRotateDartMap_new P hj1 hcode false).1
  have hφz : φ (rotate_newDart (B := B) hcode 1 true) = z :=
    (kmswPeanoRotateDartMap_new P hj1 hcode true).2
  have sep (e : StageDart s.nextEdge) (m : ℕ) :
      (ρ : D → D)^[m] (i e) ≠ B.map.toCombinatorialMap.edgeInv b ∧
      (ρ : D → D)^[m] (i e) ≠ q := by
    have hv : dartTailVertex B.map ((ρ : D → D)^[m] (i e)) =
        dartTailVertex B.map (i e) := rotate_iter_vertex m (i e)
    constructor
    · intro he
      apply hfresh e
      exact hv.symm.trans (congrArg (dartTailVertex B.map) he)
    · intro he
      apply hfresh e
      exact hv.symm.trans ((congrArg (dartTailVertex B.map) he).trans
        (rotate_rot_vertex (B.map.toCombinatorialMap.edgeInv b)))
  have liftGap (x : D) (v : ℕ)
      (hg : ∀ m : ℕ, 0 < m → m < v →
        (ρ : D → D)^[m] x ∉ Set.range i ∧
        (ρ : D → D)^[m] x ≠ b ∧ (ρ : D → D)^[m] x ≠ z)
      (hs : ∀ m : ℕ, (ρ : D → D)^[m] x ≠ B.map.toCombinatorialMap.edgeInv b ∧
        (ρ : D → D)^[m] x ≠ q) :
      ∀ m : ℕ, 0 < m → m < v → (ρ : D → D)^[m] x ∉ Set.range φ := by
    rintro m hm0 hmv ⟨e, he⟩
    obtain ⟨hI, hB, hZ⟩ := hg m hm0 hmv
    rcases rotate_image_cases P hj1 e with h | h | h | h | h
    · exact hI (he ▸ h)
    · exact hB (he.symm.trans h)
    · exact (hs m).1 (he.symm.trans h)
    · exact (hs m).2 (he.symm.trans h)
    · exact hZ (he.symm.trans h)
  by_cases hold : d.1.val < s.nextEdge
  · let e : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
    have hd : d = cast e := Prod.ext (Fin.ext rfl) rfl
    rw [hd]
    by_cases hea : e = a
    · rw [hea]
      exact kmswPeanoRotateDartMap_old_root_rot_induced P hj1 hcode hkind
    · obtain ⟨k, hk, hr, hm⟩ := P.emb.rot_induced e
      change (ρ : D → D)^[k] (i e) = i (σ e) at hr
      obtain ⟨v, hv, hvk, hvr, hvm⟩ := rotate_before_arc ρ i P.emb.injective
        A (σ e) (i e) z (fun he => hz ⟨e, he⟩) hza k hk hr hm
      refine ⟨v, hv, ?_, ?_⟩
      · have hsucc : φ ((kmswRootedStage (codeExtend c) (j + 1)).map.rot (cast e)) =
            if σ e = A then z else i (σ e) := by
          rw [rotate_old_rot (B := B) hcode e]
          change φ (if e = a then _ else if σ e = A then _ else _) = _
          rw [ite_eq_right hea]
          by_cases heA : σ e = A
          · simp only [heA, ↓reduceIte, hφz]
          · simp only [heA, ↓reduceIte]
            exact hφold (σ e)
        change (ρ : D → D)^[v] (φ (cast e)) = _
        rw [hφold]
        exact hvr.trans hsucc.symm
      · change ∀ m : ℕ, 0 < m → m < v → (ρ : D → D)^[m] (φ (cast e)) ∉ Set.range φ
        rw [hφold]
        apply liftGap (i e) v
        · intro m hm0 hmv
          obtain ⟨hI, hZ⟩ := hvm m hm0 hmv
          exact ⟨hI, rotate_avoid_after ρ i P.emb.injective a e b hba hea
            k hm m hm0 (by omega), hZ⟩
        · exact sep e
  · have hn := (kmswStage_step_up_facts (codeExtend c) j hcode).1
    have hdlt := d.1.isLt
    by_cases hnew : d.1.val = s.nextEdge
    · cases hs : d.2
      · have hd : d = rotate_newDart (B := B) hcode 0 false :=
          Prod.ext (Fin.ext (by simpa only [rotate_newDart, Fin.val_zero, Nat.add_zero] using hnew)) hs
        rw [hd]
        obtain ⟨k, hk, hr, hm⟩ := P.emb.rot_induced a
        change (ρ : D → D)^[k] (i a) = i (σ a) at hr
        have hk1 : 1 < k := by
          by_contra hh
          have hke : k = 1 := by omega
          have hh : b = i (σ a) := by
            simpa only [hke, Function.iterate_one, hba] using hr
          exact hb ⟨σ a, hh.symm⟩
        have hshift (m : ℕ) : (ρ : D → D)^[m] b = (ρ : D → D)^[m + 1] (i a) := by
          rw [Function.iterate_succ_apply, hba]
        have hret : (ρ : D → D)^[k - 1] b = i (σ a) := by
          rw [hshift, Nat.sub_add_cancel (by omega : 1 ≤ k)]
          exact hr
        have hmin : ∀ m : ℕ, 0 < m → m < k - 1 →
            (ρ : D → D)^[m] b ∉ Set.range i := by
          intro m hm0 hmk
          rw [hshift]
          exact hm (m + 1) (by omega) (by omega)
        have hneq : b ≠ z := (rotate_new_edges_distinct hj1 hkind).2
        obtain ⟨v, hv, hvk, hvr, hvm⟩ := rotate_before_arc ρ i P.emb.injective
          A (σ a) b z hneq hza (k - 1) (by omega) hret hmin
        refine ⟨v, hv, ?_, ?_⟩
        · have hsucc : φ ((kmswRootedStage (codeExtend c) (j + 1)).map.rot
                (rotate_newDart (B := B) hcode 0 false)) =
              if σ a = A then z else i (σ a) := by
            rw [rotate_active_rot (B := B) hcode]
            change φ (if σ a = A then _ else _) = _
            by_cases haA : σ a = A
            · simp only [haA, ↓reduceIte, hφz]
            · simp only [haA, ↓reduceIte]
              exact hφold (σ a)
          change (ρ : D → D)^[v] (φ (rotate_newDart (B := B) hcode 0 false)) = _
          rw [hφb]
          exact hvr.trans hsucc.symm
        · change ∀ m : ℕ, 0 < m → m < v →
            (ρ : D → D)^[m] (φ (rotate_newDart (B := B) hcode 0 false)) ∉ Set.range φ
          rw [hφb]
          apply liftGap b v
          · intro m hm0 hmv
            obtain ⟨hI, hZ⟩ := hvm m hm0 hmv
            refine ⟨hI, ?_, hZ⟩
            intro he
            have hperiod : (ρ : D → D)^[m] (i a) = i a := by
              apply ρ.injective
              rw [← Function.iterate_succ_apply' (f := (ρ : D → D)), ← hshift, hba]
              exact he
            exact hm m hm0 (by omega) ⟨a, hperiod.symm⟩
          · intro m
            rw [hshift]
            exact sep a (m + 1)
      · exact kmswPeanoRotateDartMap_new_vertex_rot_induced P hj1 hcode hkind hfresh d
          (Or.inl ⟨hnew, hs⟩)
    · have hedge : d.1.val = s.nextEdge + 1 := by
        dsimp only [s] at hold hnew ⊢
        omega
      cases hs : d.2
      · exact kmswPeanoRotateDartMap_new_vertex_rot_induced P hj1 hcode hkind hfresh d
          (Or.inr ⟨hedge, hs⟩)
      · exact kmswPeanoRotateDartMap_missing_reverse_rot_induced P hj1 hcode hkind d hedge hs




@[expose] noncomputable def kmswPeanoPrefixEmbedding_rotate
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    KMSWPeanoPrefixEmbedding B c (j + 1) hj1 := by
  obtain ⟨hp, hcover, hmissing, hfuture⟩ :=
    kmswPeanoRotateDartMap_prefix_of_freshVertex P hj1 hcode hkind hfresh
  exact {
    emb := {
      dartMap := kmswPeanoRotateDartMap P hj1
      injective := kmswPeanoRotateDartMap_injective_of_freshVertex P hj1 hcode hkind hfresh
      flip_comm := kmswPeanoRotateDartMap_flip P hj1
      present := by
        intro d _
        exact B.noMissingDarts (kmswPeanoRotateDartMap P hj1 d)
      tail_comm := kmswPeanoRotateDartMap_tail P hj1 hcode
      rot_induced := kmswPeanoRotateDartMap_rot_induced P hj1 hcode hkind hfresh
      root_comm := kmswPeanoRotateDartMap_root P hj1 hcode
    }
    present_prefix := hp
    edges_cover_prefix := hcover
    missing_iff_frontier := hmissing
    missing_is_future := hfuture
  }

end DirectedDistances.KMSW
