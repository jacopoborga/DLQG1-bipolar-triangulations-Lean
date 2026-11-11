module

public import DirectedDistances.KMSW.KMSWPeanoPrefix
public import DirectedDistances.KMSW.KMSWInverseStepLink
public import DirectedDistances.PlanarMap.BipolarPeanoConfiguration
public import DirectedDistances.KMSW.StageOuterWordSucc

/-! Supporting lemmas for paper labels `def-kmsw`, `thm-kmsw` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}





@[expose] def KMSWPeanoDescendFrontier
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges) : Prop :=
  (∀ (e : ℕ) (es : List ℕ), (kmswStage (codeExtend c) j).UR = e :: es →
    ∀ he : e < (kmswStage (codeExtend c) j).nextEdge,
      P.emb.dartMap (⟨e, he⟩, false) = peanoEdge B ⟨j + 1, hj1⟩) ∧
  ((kmswStage (codeExtend c) j).UR = [] →
    peanoEdge B ⟨j + 1, hj1⟩ ∉ Set.range P.emb.dartMap ∧
    ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) ≠
        dartTailVertex B.map (P.emb.dartMap d))



theorem kmswPeanoDescend_UR_head_west
    (u : ℕ → Fin 3) (j e : ℕ) (es : List ℕ)
    (hUR : (kmswStage u j).UR = e :: es) :
    (kmswStage u j).west e = (kmswStage u j).east (kmswStage u j).active :=
  (kmswStage_boundary_chain_invariant u j).2.2.2.2.2.1 e es hUR




theorem kmswPeanoDescendFrontier_activation_rightmost
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend)
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage (codeExtend c) j).UR = e :: es)
    (he : e < (kmswStage (codeExtend c) j).nextEdge) :
    ∃ ht : dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩) ≠ B.sink,
      P.emb.dartMap (⟨e, he⟩, false) =
        rightmostOutgoing B (dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩)) ht := by
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨_, ht, _, hb⟩ := hc
  exact ⟨ht, (hF.1 e es hUR he).trans hb⟩

private def descendCastEquiv {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l :=
  Equiv.prodCongr (finCongr h) (Equiv.refl Bool)

private theorem descend_resize_eq {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) :
    StageRotation.resize h σ = (descendCastEquiv h).permCongr σ := by
  cases h
  rfl

private theorem descend_index_eq_or_flip
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d e : D}
    (h : peanoIndex B d = peanoIndex B e) :
    d = e ∨ d = B.map.toCombinatorialMap.edgeInv e := by
  classical
  have hidx := congrArg Fin.val h
  change (firstVisitOrder B).idxOf (peanoForwardDart B d) =
    (firstVisitOrder B).idxOf (peanoForwardDart B e) at hidx
  have hf := (List.idxOf_inj
    ((mem_firstVisitOrder_iff B _).2 (peanoForwardDart_tail B d))).1 hidx
  by_cases hd : B.map.tail d <;> by_cases he : B.map.tail e
  · exact Or.inl (by simpa [peanoForwardDart, hd, he] using hf)
  · exact Or.inr (by simpa [peanoForwardDart, hd, he] using hf)
  · have hi : B.map.toCombinatorialMap.edgeInv d = e := by
      simpa [peanoForwardDart, hd, he] using hf
    exact Or.inr (by
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
        congrArg B.map.toCombinatorialMap.edgeInv hi)
  · exact Or.inl (B.map.toCombinatorialMap.edgeInv.injective (by
      simpa [peanoForwardDart, hd, he] using hf))




noncomputable def kmswPeanoPrefixEmbedding_descend_activation
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage (codeExtend c) j).UR = e :: es)
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1) :
    KMSWPeanoPrefixEmbedding B c (j + 1) hj1 := by
  classical
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  have facts := kmswStage_step_activation_facts u j e es hcode hUR
  have hs : t.nextEdge = s.nextEdge := facts.1
  let E : StageDart t.nextEdge ≃ StageDart s.nextEdge := descendCastEquiv hs
  have hEval (d : StageDart t.nextEdge) : (E d).1.val = d.1.val := rfl
  have hEside (d : StageDart t.nextEdge) : (E d).2 = d.2 := rfl
  have he : e < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u j).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (by rw [hUR]; exact List.mem_cons_self))))
  let ed : StageDart s.nextEdge := (⟨e, he⟩, false)
  have hed : P.emb.dartMap ed = peanoEdge B ⟨j + 1, hj1⟩ := hF.1 e es hUR he
  have hpres (f : ℕ) : t.present f = if f = e then true else s.present f :=
    facts.2.2.2.2.2.2.1 f
  have hactive : t.active = e := facts.2.2.2.2.1
  have hrot : ∀ d : StageDart t.nextEdge,
      E (stageRot u (j + 1) d) = stageRot u j (E d) := by
    have ht := StageRotation.step_activation s (act_lt_nextEdge u (le_refl j))
      (stageRotation_UL_bound u j) (stageRot u j) (u j)
      (by change kmswCodeStep (codeExtend c j) = .down; rw [hcode]; rfl) e es hUR
    have hr : StageRotation.resize hs (stageRot u (j + 1)) = stageRot u j := by
      rw [stageRot_succ]
      exact ht
    rw [descend_resize_eq] at hr
    change E.permCongr (stageRot u (j + 1)) = stageRot u j at hr
    intro d
    have hh := congrArg (fun σ : Equiv.Perm (StageDart s.nextEdge) => σ (E d)) hr
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using hh
  have hflip (d : StageDart t.nextEdge) :
      E (edgeFlip _ d) = edgeFlip _ (E d) := by
    rcases d with ⟨f, b⟩
    rfl
  have hPflip (d : StageDart s.nextEdge) : P.emb.dartMap (edgeFlip _ d) =
      B.map.toCombinatorialMap.edgeInv (P.emb.dartMap d) := P.emb.flip_comm d
  have hindex (d : StageDart t.nextEdge) :
      (peanoIndex B (P.emb.dartMap (E d))).val = j + 1 ↔ d.1.val = e := by
    constructor
    · intro hi
      have hi' : peanoIndex B (P.emb.dartMap (E d)) =
          peanoIndex B (P.emb.dartMap ed) := by
        rw [hed, peanoIndex_peanoEdge]
        exact Fin.ext hi
      rcases descend_index_eq_or_flip B hi' with h | h
      · have hh := congrArg (fun x : StageDart s.nextEdge => x.1.val)
          (P.emb.injective h)
        exact hh
      · rw [← hPflip] at h
        have hh := congrArg (fun x : StageDart s.nextEdge => x.1.val)
          (P.emb.injective h)
        exact hh
    · intro hde
      rcases d with ⟨f, b⟩
      cases b
      · have hE : E (f, false) = ed := by
          apply Prod.ext
          · exact Fin.ext hde
          · rfl
        rw [hE, hed, peanoIndex_peanoEdge]
      · have hE : E (f, true) = edgeFlip _ ed := by
          apply Prod.ext
          · exact Fin.ext hde
          · rfl
        rw [hE, hPflip, peanoIndex_edgeInv, hed, peanoIndex_peanoEdge]
  refine { emb := { dartMap := fun d => P.emb.dartMap (E d)
                    injective := P.emb.injective.comp E.injective
                    flip_comm := ?_
                    present := ?_
                    tail_comm := ?_
                    rot_induced := ?_
                    root_comm := ?_ }
           present_prefix := ?_
           edges_cover_prefix := ?_
           missing_iff_frontier := ?_
           missing_is_future := ?_ }
  · intro d
    exact (congrArg P.emb.dartMap (hflip d)).trans (hPflip (E d))
  · intro d _
    exact B.noMissingDarts _
  · intro d hd
    change ¬ t.present d.1.val = false at hd
    change (t.present d.1.val = true ∧ d.2 = false) ↔ B.map.tail (P.emb.dartMap (E d))
    have htp := Bool.eq_true_of_not_eq_false hd
    by_cases hde : d.1.val = e
    · rcases d with ⟨f, b⟩
      cases b
      · have hE : E (f, false) = ed := by
          apply Prod.ext
          · exact Fin.ext hde
          · rfl
        rw [hE, hed]
        exact iff_of_true ⟨htp, rfl⟩ (peanoEdge_forward B _)
      · have hE : E (f, true) = edgeFlip _ ed := by
          apply Prod.ext
          · exact Fin.ext hde
          · rfl
        rw [hE, hPflip, hed]
        have hn := (B.map.tail_iff _ (B.noMissingDarts _)).1 (peanoEdge_forward B ⟨j + 1, hj1⟩)
        simp only [Bool.true_eq_false, and_false, false_iff]
        exact hn
    · have hp : s.present (E d).1.val = true := by
        simpa only [hpres, hde, ↓reduceIte, hEval] using htp
      have ht := P.emb.tail_comm (E d) (by change ¬ s.present (E d).1.val = false; rw [hp]; decide)
      change (s.present (E d).1.val = true ∧ (E d).2 = false) ↔
        B.map.tail (P.emb.dartMap (E d)) at ht
      simpa only [hp, htp, true_and, hEside] using ht
  · intro d
    obtain ⟨k, hk, hr, hmin⟩ := P.emb.rot_induced (E d)
    refine ⟨k, hk, ?_, ?_⟩
    · exact hr.trans (congrArg P.emb.dartMap (hrot d).symm)
    · intro i hi hik hmem
      apply hmin i hi hik
      obtain ⟨f, hf⟩ := hmem
      exact ⟨E f, hf⟩
  · change P.emb.dartMap (E (⟨t.active, _⟩, false)) = _
    have hE : E (⟨t.active, act_lt_nextEdge u (le_refl (j + 1))⟩, false) = ed := by
      apply Prod.ext
      · exact Fin.ext hactive
      · rfl
    exact (congrArg P.emb.dartMap hE).trans hed
  · intro d
    change t.present d.1.val = true ↔ _
    rw [hpres]
    by_cases hde : d.1.val = e
    · simp only [hde, ↓reduceIte, true_iff]
      exact le_of_eq ((hindex d).2 hde)
    · simp only [hde, ↓reduceIte]
      have hp := P.present_prefix (E d)
      have hn : (peanoIndex B (P.emb.dartMap (E d))).val ≠ j + 1 :=
        fun hi => hde ((hindex d).1 hi)
      exact hp.trans (by omega)
  · intro k hk
    by_cases hkj : k ≤ j
    · obtain ⟨d, hd⟩ := P.edges_cover_prefix k hkj
      exact ⟨E.symm d, by simpa only [E.apply_symm_apply] using hd⟩
    · have hk1 : k = j + 1 := by omega
      refine ⟨E.symm ed, ?_⟩
      change (peanoIndex B (P.emb.dartMap (E (E.symm ed)))).val = k
      rw [E.apply_symm_apply, hed, peanoIndex_peanoEdge]
      exact hk1.symm
  · intro d
    exact (kmswStage_status u (j + 1)).1 d.1.val d.1.isLt
  · intro d hd
    change j + 1 < (peanoIndex B (P.emb.dartMap (E d))).val
    have hp := (show t.present d.1.val = true ↔
        (peanoIndex B (P.emb.dartMap (E d))).val ≤ j + 1 from by
      rw [hpres]
      by_cases hde : d.1.val = e
      · simp only [hde, ↓reduceIte, true_iff]
        exact le_of_eq ((hindex d).2 hde)
      · simp only [hde, ↓reduceIte]
        have hn : (peanoIndex B (P.emb.dartMap (E d))).val ≠ j + 1 :=
          fun hi => hde ((hindex d).1 hi)
        exact (P.present_prefix (E d)).trans (by omega))
    by_contra hn
    have ht := hp.2 (by omega)
    rw [hd] at ht
    contradiction




theorem kmswPeanoPrefixEmbedding_descend_activation_old
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage (codeExtend c) j).UR = e :: es)
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    (kmswPeanoPrefixEmbedding_descend_activation B c j hj P hj1 hcode e es hUR hF).emb.dartMap
      (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
        P.emb.dartMap d := by
  rfl





@[expose] def KMSWPeanoDescendCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges) : Prop :=
  ∃ k : ℕ, 0 < k ∧
    (B.map.toCombinatorialMap.rot : D → D)^[k] (peanoEdge B ⟨j + 1, hj1⟩) =
      B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j, hj⟩) ∧
    ∀ i : ℕ, 0 < i → i < k →
      (B.map.toCombinatorialMap.rot : D → D)^[i] (peanoEdge B ⟨j + 1, hj1⟩) ∉
        Set.range P.emb.dartMap

private theorem descend_insert_arc {α β : Type*} [DecidableEq α]
    (ρ : Equiv.Perm β) (i : α → β) (hi : Function.Injective i)
    (A : α) (b : β) (hb : b ∉ Set.range i)
    (l : ℕ) (hl : 0 < l) (hBA : (ρ : β → β)^[l] b = i A)
    (hgap : ∀ m : ℕ, 0 < m → m < l → (ρ : β → β)^[m] b ∉ Set.range i)
    (p q : α) (k : ℕ) (hk : 0 < k)
    (hret : (ρ : β → β)^[k] (i p) = i q)
    (hmin : ∀ m : ℕ, 0 < m → m < k → (ρ : β → β)^[m] (i p) ∉ Set.range i) :
    ∃ v : ℕ, 0 < v ∧
      (ρ : β → β)^[v] (i p) = (if q = A then b else i q) ∧
      ∀ m : ℕ, 0 < m → m < v →
        (ρ : β → β)^[m] (i p) ∉ Set.range i ∧ (ρ : β → β)^[m] (i p) ≠ b := by
  have shift (m : ℕ) (hm : (ρ : β → β)^[m] (i p) = b) :
      (ρ : β → β)^[m + l] (i p) = i A := by
    rw [Nat.add_comm m l, Function.iterate_add_apply, hm, hBA]
  have hit (m : ℕ) (hm0 : 0 < m) (hmk : m < k)
      (hm : (ρ : β → β)^[m] (i p) = b) : q = A := by
    rcases lt_trichotomy k (m + l) with hlt | heq | hgt
    · have hh : (ρ : β → β)^[k - m] b = i q := by
        rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hret
      exact False.elim (hgap (k - m) (by omega) (by omega) ⟨q, hh.symm⟩)
    · apply hi
      rw [← hret, heq]
      exact shift m hm
    · exact False.elim (hmin (m + l) (by omega) hgt ⟨A, (shift m hm).symm⟩)
  by_cases hq : q = A
  · have hretA : (ρ : β → β)^[k] (i p) = i A := by rw [hret, hq]
    have hlk : l < k := by
      by_contra hn
      have hkl : k ≤ l := by omega
      have hh : (ρ : β → β)^[l - k] b = i p := by
        apply ρ.injective.iterate k
        rw [← Function.iterate_add_apply, Nat.add_sub_of_le hkl, hBA, hretA]
      by_cases he : l = k
      · apply hb
        exact ⟨p, by simpa only [he, Nat.sub_self, Function.iterate_zero_apply] using hh.symm⟩
      · exact hgap (l - k) (by omega) (by omega) ⟨p, hh.symm⟩
    have hcut : (ρ : β → β)^[k - l] (i p) = b := by
      apply ρ.injective.iterate l
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (by omega), hretA, hBA]
    refine ⟨k - l, by omega, ?_, ?_⟩
    · simpa only [hq, ↓reduceIte] using hcut
    · intro m hm0 hmv
      refine ⟨hmin m hm0 (by omega), ?_⟩
      intro hm
      exact hmin (m + l) (by omega) (by omega) ⟨A, (shift m hm).symm⟩
  · refine ⟨k, hk, ?_, ?_⟩
    · simpa only [hq, ↓reduceIte] using hret
    · intro m hm0 hmk
      exact ⟨hmin m hm0 hmk, fun hm => hq (hit m hm0 hmk hm)⟩

private theorem descend_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (k : ℕ) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (show Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot d
      ((B.map.toCombinatorialMap.rot : D → D)^[k] d) from
    ⟨(k : ℤ), by simp only [zpow_natCast]; rfl⟩).symm

private theorem descend_first_return {α β : Type*} [Finite β]
    (ρ : Equiv.Perm β) (f : α → β) (d : α) :
    ∃ k : ℕ, 0 < k ∧ (∃ e, f e = (ρ : β → β)^[k] (f d)) ∧
      ∀ m : ℕ, 0 < m → m < k → (ρ : β → β)^[m] (f d) ∉ Set.range f := by
  classical
  obtain ⟨k, hk, _, he⟩ := (Equiv.Perm.SameCycle.refl ρ (f d)).exists_pow_eq''
  have hex : ∃ k : ℕ, 0 < k ∧ (ρ : β → β)^[k] (f d) ∈ Set.range f :=
    ⟨k, hk, d, he.symm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro m hm hmk hmem
  exact Nat.find_min hex hmk ⟨hm, hmem⟩



noncomputable def kmswPeanoPrefixEmbedding_descend_pendant
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (hUR : (kmswStage (codeExtend c) j).UR = [])
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (hC : KMSWPeanoDescendCorner B c j hj P hj1) :
    KMSWPeanoPrefixEmbedding B c (j + 1) hj1 := by
  classical
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let z := B.map.toCombinatorialMap.edgeInv b
  let ρ := B.map.toCombinatorialMap.rot
  have hb : b ∉ Set.range P.emb.dartMap := (hF.2 hUR).1
  have hfresh := (hF.2 hUR).2
  have hz : z ∉ Set.range P.emb.dartMap := by
    rintro ⟨d, hd⟩
    apply hb
    refine ⟨edgeFlip _ d, ?_⟩
    have hh := P.emb.flip_comm d
    change P.emb.dartMap (edgeFlip _ d) = B.map.toCombinatorialMap.edgeInv (P.emb.dartMap d) at hh
    rw [hh, hd]
    exact B.map.toCombinatorialMap.edgeInv_invol b
  have hzb : z ≠ b := B.map.toCombinatorialMap.edgeInv_ne b
  have hsep (d : StageDart s.nextEdge) (k : ℕ) :
      (ρ : D → D)^[k] (P.emb.dartMap d) ≠ z := by
    intro hh
    apply hfresh d
    change dartTailVertex B.map z = dartTailVertex B.map (P.emb.dartMap d)
    rw [← hh]
    exact descend_rot_vertex B _ k
  have hsepz (d : StageDart s.nextEdge) (k : ℕ) :
      (ρ : D → D)^[k] z ≠ P.emb.dartMap d := by
    intro hh
    apply hfresh d
    change dartTailVertex B.map z = dartTailVertex B.map (P.emb.dartMap d)
    rw [← hh]
    exact (descend_rot_vertex B _ k).symm
  have hsepzb (k : ℕ) : (ρ : D → D)^[k] z ≠ b := by
    intro hh
    apply peano_dart_no_loop B b
    change dartTailVertex B.map b = dartTailVertex B.map z
    rw [← hh]
    exact descend_rot_vertex B _ k
  have hsepbz (k : ℕ) : (ρ : D → D)^[k] b ≠ z := by
    intro hh
    apply peano_dart_no_loop B b
    change dartTailVertex B.map b = dartTailVertex B.map z
    rw [← hh]
    exact (descend_rot_vertex B _ k).symm
  have facts := kmswStage_step_pendant_facts u j hcode hUR
  have hs : t.nextEdge = s.nextEdge + 1 := facts.1
  let Q : StageDart t.nextEdge ≃ StageDart s.nextEdge ⊕ StageDart 1 :=
    (descendCastEquiv hs).trans (StageRotation.allocation s.nextEdge 1).symm
  let f : StageDart s.nextEdge ⊕ StageDart 1 → D :=
    Sum.elim P.emb.dartMap (fun d => if d.2 then z else b)
  have f_old (d : StageDart s.nextEdge) : f (.inl d) = P.emb.dartMap d := rfl
  have f_new (v : Bool) : f (.inr (0, v)) = if v then z else b := rfl
  have old_val (d : StageDart s.nextEdge) :
      ((Q.symm (.inl d)).1.val, (Q.symm (.inl d)).2) = (d.1.val, d.2) := rfl
  have new_val (v : Bool) :
      ((Q.symm (.inr (0, v))).1.val, (Q.symm (.inr (0, v))).2) = (s.nextEdge, v) := by
    simp only [Q, Equiv.symm_trans_apply, Equiv.symm_symm, StageRotation.allocation_new]
    rfl
  have fin1 (d : StageDart 1) : d = (0, d.2) := by
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hf : Function.Injective f := by
    rintro (d | ⟨e, v⟩) (d' | ⟨e', w⟩) hh
    · exact congrArg Sum.inl (P.emb.injective hh)
    · cases v : w
      · exact False.elim (hb ⟨d, by simpa only [f, Sum.elim_inl, Sum.elim_inr, v, Bool.false_eq_true, ↓reduceIte] using hh⟩)
      · exact False.elim (hz ⟨d, by simpa only [f, Sum.elim_inl, Sum.elim_inr, v, ↓reduceIte] using hh⟩)
    · cases hv : v
      · exact False.elim (hb ⟨d', by simpa only [f, Sum.elim_inl, Sum.elim_inr, hv, Bool.false_eq_true, ↓reduceIte] using hh.symm⟩)
      · exact False.elim (hz ⟨d', by simpa only [f, Sum.elim_inl, Sum.elim_inr, hv, ↓reduceIte] using hh.symm⟩)
    · cases v <;> cases w
      · exact congrArg Sum.inr (Prod.ext (Subsingleton.elim _ _) rfl)
      · exact False.elim (hzb hh.symm)
      · exact False.elim (hzb hh)
      · exact congrArg Sum.inr (Prod.ext (Subsingleton.elim _ _) rfl)
  have hpold (d : StageDart s.nextEdge) :
      t.present (Q.symm (.inl d)).1.val = s.present d.1.val := by
    rw [show (Q.symm (.inl d)).1.val = d.1.val from congrArg Prod.fst (old_val d)]
    change (kmswStep s (u j)).present d.1.val = _
    have hc : kmswCodeStep (u j) = .down := by change kmswCodeStep (codeExtend c j) = .down; rw [hcode]; rfl
    have hURs : s.UR = [] := hUR
    simp only [kmswStep, hc, kmswStepOfStep, hURs, State.addEdge]
    exact ite_eq_right (Nat.ne_of_lt d.1.isLt)
  have hpnew (v : Bool) : t.present (Q.symm (.inr (0, v))).1.val = true := by
    rw [show (Q.symm (.inr (0, v))).1.val = s.nextEdge from congrArg Prod.fst (new_val v)]
    exact facts.2.2.2.2.2.1
  let A : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)
  let τ : Equiv.Perm (StageDart s.nextEdge ⊕ StageDart 1) :=
    insertBefore (Equiv.sumCongr (stageRot u j) (Equiv.refl _)) (.inl A) (.inr (0, false))
  have τold (d : StageDart s.nextEdge) :
      τ (.inl d) = if stageRot u j d = A then .inr (0, false) else .inl (stageRot u j d) := by
    by_cases hh : stageRot u j d = A <;> simp [τ, insertBefore, Equiv.swap_apply_def, hh]
  have τnew : τ (.inr (0, false)) = .inl A ∧ τ (.inr (0, true)) = .inr (0, true) := by
    simp [τ, insertBefore, Equiv.swap_apply_def]
  have hrot (d : StageDart s.nextEdge ⊕ StageDart 1) :
      Q (stageRot u (j + 1) (Q.symm d)) = τ d := by
    have hc : kmswCodeStep (u j) = .down := by change kmswCodeStep (codeExtend c j) = .down; rw [hcode]; rfl
    have hr := StageRotation.step_pendant s (act_lt_nextEdge u (le_refl j))
      (stageRotation_UL_bound u j) (stageRot u j) (u j) hc hUR
    have hr' : StageRotation.resize hs (stageRot u (j + 1)) =
        StageRotation.pendant s.nextEdge (stageRot u j) A := by
      rw [stageRot_succ]
      exact hr
    rw [descend_resize_eq] at hr'
    change (descendCastEquiv hs).permCongr (stageRot u (j + 1)) =
      (StageRotation.allocation s.nextEdge 1).permCongr τ at hr'
    have hh := congrArg (fun σ : Equiv.Perm (StageDart (s.nextEdge + 1)) =>
      (StageRotation.allocation s.nextEdge 1).symm (σ (StageRotation.allocation s.nextEdge 1 d))) hr'
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Q,
      Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm] using hh
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j, hj⟩) := by
    have hh := P.emb.flip_comm (kmswRootedStage u j).root
    change P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (kmswRootedStage u j).root) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv P.emb.root_comm)
  have hfinduced (d : StageDart s.nextEdge ⊕ StageDart 1) :
      ∃ k : ℕ, 0 < k ∧ (ρ : D → D)^[k] (f d) = f (τ d) ∧
        ∀ m : ℕ, 0 < m → m < k → (ρ : D → D)^[m] (f d) ∉ Set.range f := by
    obtain ⟨l, hl, hBA, hgap⟩ := hC
    have hBA' : (ρ : D → D)^[l] b = P.emb.dartMap A := hBA.trans hA.symm
    cases d with
    | inl d =>
      obtain ⟨k, hk, hr, hm⟩ := P.emb.rot_induced d
      change (ρ : D → D)^[k] (P.emb.dartMap d) = P.emb.dartMap (stageRot u j d) at hr
      obtain ⟨v, hv, hvr, hvm⟩ := descend_insert_arc ρ P.emb.dartMap P.emb.injective A b hb
        l hl hBA' hgap d (stageRot u j d) k hk hr hm
      refine ⟨v, hv, ?_, ?_⟩
      · rw [τold]
        by_cases hh : stageRot u j d = A <;>
          simp only [hh, ↓reduceIte] at hvr ⊢ <;> exact hvr
      · intro m hm0 hmv ⟨e, he⟩
        obtain ⟨hn, hnb⟩ := hvm m hm0 hmv
        cases e with
        | inl e => exact hn ⟨e, he⟩
        | inr e =>
          rcases e with ⟨ed, v⟩
          obtain rfl : ed = 0 := Subsingleton.elim _ _
          cases v
          · exact hnb he.symm
          · exact hsep d m he.symm
    | inr d =>
      rw [fin1 d]
      cases d.2
      · refine ⟨l, hl, ?_, ?_⟩
        · rw [τnew.1]
          exact hBA'
        · intro m hm0 hml ⟨e, he⟩
          cases e with
          | inl e => exact hgap m hm0 hml ⟨e, he⟩
          | inr e =>
            rcases e with ⟨ed, v⟩
            obtain rfl : ed = 0 := Subsingleton.elim _ _
            cases v
            · have hperiod : (ρ : D → D)^[l - m] b = P.emb.dartMap A := by
                change b = (ρ : D → D)^[m] b at he
                rw [he, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
                exact hBA'
              exact hgap (l - m) (by omega) (by omega) ⟨A, hperiod.symm⟩
            · exact hsepbz m he.symm
      · obtain ⟨k, hk, ⟨e, he⟩, hm⟩ := descend_first_return ρ f (.inr (0, true))
        have heq : e = .inr (0, true) := by
          cases e with
          | inl e => exact False.elim (hsepz e k he.symm)
          | inr e =>
            rcases e with ⟨ed, v⟩
            obtain rfl : ed = 0 := Subsingleton.elim _ _
            cases v
            · exact False.elim (hsepzb k he.symm)
            · rfl
        refine ⟨k, hk, ?_, hm⟩
        rw [τnew.2, ← he, heq]
  have hidxold (d : StageDart s.nextEdge) :
      (peanoIndex B (P.emb.dartMap d)).val ≠ j + 1 := by
    intro hh
    have hi : peanoIndex B (P.emb.dartMap d) = peanoIndex B b := by
      rw [peanoIndex_peanoEdge]
      exact Fin.ext hh
    rcases descend_index_eq_or_flip B hi with hh | hh
    · exact hb ⟨d, hh⟩
    · exact hz ⟨d, hh⟩
  have hidxnew (v : Bool) : (peanoIndex B (f (.inr (0, v)))).val = j + 1 := by
    cases v
    · exact congrArg Fin.val (peanoIndex_peanoEdge B ⟨j + 1, hj1⟩)
    · exact congrArg Fin.val ((peanoIndex_edgeInv B b).trans (peanoIndex_peanoEdge B ⟨j + 1, hj1⟩))
  have hprefix (d : StageDart t.nextEdge) :
      t.present d.1.val = true ↔ (peanoIndex B (f (Q d))).val ≤ j + 1 := by
    obtain ⟨d, rfl⟩ := Q.symm.surjective d
    rw [Q.apply_symm_apply]
    cases d with
    | inl d =>
      rw [hpold, f_old]
      exact (P.present_prefix d).trans (by have := hidxold d; omega)
    | inr d =>
      rw [fin1 d, hpnew, hidxnew]
      simp only [le_refl]
  refine { emb := { dartMap := fun d => f (Q d)
                    injective := hf.comp Q.injective
                    flip_comm := ?_
                    present := fun d _ => B.noMissingDarts _
                    tail_comm := ?_
                    rot_induced := ?_
                    root_comm := ?_ }
           present_prefix := hprefix
           edges_cover_prefix := ?_
           missing_iff_frontier := fun d => (kmswStage_status u (j + 1)).1 d.1.val d.1.isLt
           missing_is_future := ?_ }
  · intro d
    obtain ⟨d, rfl⟩ := Q.symm.surjective d
    have hflip : edgeFlip _ (Q.symm d) =
        Q.symm (Sum.map (edgeFlip _) (edgeFlip 1) d) := by
      cases d with
      | inl d => rcases d with ⟨e, v⟩; rfl
      | inr d => rcases d with ⟨e, v⟩; rfl
    change f (Q (edgeFlip _ (Q.symm d))) = B.map.toCombinatorialMap.edgeInv (f (Q (Q.symm d)))
    rw [hflip, Q.apply_symm_apply, Q.apply_symm_apply]
    cases d with
    | inl d => exact P.emb.flip_comm d
    | inr d =>
      rw [fin1 d]
      cases d.2
      · rfl
      · exact (B.map.toCombinatorialMap.edgeInv_invol b).symm
  · intro d hd
    obtain ⟨d, rfl⟩ := Q.symm.surjective d
    change ¬ t.present (Q.symm d).1.val = false at hd
    change (t.present (Q.symm d).1.val = true ∧ (Q.symm d).2 = false) ↔
      B.map.tail (f (Q (Q.symm d)))
    rw [Q.apply_symm_apply]
    cases d with
    | inl d =>
      rw [hpold, show (Q.symm (.inl d)).2 = d.2 from congrArg Prod.snd (old_val d), f_old]
      change ¬ t.present (Q.symm (.inl d)).1.val = false at hd
      rw [hpold] at hd
      exact P.emb.tail_comm d hd
    | inr d =>
      rw [fin1 d] at hd ⊢
      rw [hpnew, show (Q.symm (.inr (0, d.2))).2 = d.2 from congrArg Prod.snd (new_val d.2)]
      cases d.2
      · exact iff_of_true ⟨rfl, rfl⟩ (peanoEdge_forward B _)
      · exact iff_of_false (by simp only [Bool.true_eq_false, and_false, not_false_eq_true])
          ((B.map.tail_iff b (B.noMissingDarts b)).1 (peanoEdge_forward B _))
  · intro d
    obtain ⟨k, hk, hr, hm⟩ := hfinduced (Q d)
    refine ⟨k, hk, ?_, ?_⟩
    · change (ρ : D → D)^[k] (f (Q d)) = f (Q (stageRot u (j + 1) d))
      have hh := hrot (Q d)
      rw [Q.symm_apply_apply] at hh
      exact hr.trans (congrArg f hh.symm)
    · intro m hm0 hmk ⟨e, he⟩
      exact hm m hm0 hmk ⟨Q e, he⟩
  · have hr : (kmswRootedStage u (j + 1)).root = Q.symm (.inr (0, false)) := by
      apply Prod.ext
      · apply Fin.ext
        exact facts.2.2.2.2.1.trans (congrArg Prod.fst (new_val false)).symm
      · rfl
    change f (Q (kmswRootedStage u (j + 1)).root) = b
    rw [hr, Q.apply_symm_apply]
    rfl
  · intro k hk
    by_cases hkj : k ≤ j
    · obtain ⟨d, hd⟩ := P.edges_cover_prefix k hkj
      refine ⟨Q.symm (.inl d), ?_⟩
      change (peanoIndex B (f (Q (Q.symm (.inl d))))).val = k
      rw [Q.apply_symm_apply]
      exact hd
    · refine ⟨Q.symm (.inr (0, false)), ?_⟩
      change (peanoIndex B (f (Q (Q.symm (.inr (0, false)))))).val = k
      rw [Q.apply_symm_apply, hidxnew]
      omega
  · intro d hd
    change j + 1 < (peanoIndex B (f (Q d))).val
    by_contra hn
    have hh := (hprefix d).2 (by omega)
    rw [hd] at hh
    contradiction



theorem kmswPeanoPrefixEmbedding_descend_pendant_old
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (hUR : (kmswStage (codeExtend c) j).UR = [])
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (hC : KMSWPeanoDescendCorner B c j hj P hj1)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    (kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR hF hC).emb.dartMap
      (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
        P.emb.dartMap d := by
  let hs := (kmswStage_step_pendant_facts (codeExtend c) j hcode hUR).1
  let d' := outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d
  have hd : descendCastEquiv hs d' =
      StageRotation.allocation (kmswStage (codeExtend c) j).nextEdge 1 (.inl d) := rfl
  change Sum.elim P.emb.dartMap
    (fun d => if d.2 then B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)
      else peanoEdge B ⟨j + 1, hj1⟩)
    ((StageRotation.allocation (kmswStage (codeExtend c) j).nextEdge 1).symm
      (descendCastEquiv hs d')) = P.emb.dartMap d
  rw [hd, Equiv.symm_apply_apply]
  rfl



theorem kmswPeanoPrefixEmbedding_descend_pendant_new
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (hUR : (kmswStage (codeExtend c) j).UR = [])
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (hC : KMSWPeanoDescendCorner B c j hj P hj1)
    (e : Fin (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (he : e.val = (kmswStage (codeExtend c) j).nextEdge) (v : Bool) :
    (kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR hF hC).emb.dartMap
      (e, v) = if v then B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)
        else peanoEdge B ⟨j + 1, hj1⟩ := by
  let hs := (kmswStage_step_pendant_facts (codeExtend c) j hcode hUR).1
  have hd : descendCastEquiv hs (e, v) =
      StageRotation.allocation (kmswStage (codeExtend c) j).nextEdge 1 (.inr (0, v)) := by
    apply Prod.ext
    · exact Fin.ext he
    · rfl
  change Sum.elim P.emb.dartMap
    (fun d => if d.2 then B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)
      else peanoEdge B ⟨j + 1, hj1⟩)
    ((StageRotation.allocation (kmswStage (codeExtend c) j).nextEdge 1).symm
      (descendCastEquiv hs (e, v))) = _
  rw [hd, Equiv.symm_apply_apply]
  rfl



noncomputable def kmswPeanoPrefixEmbedding_descend
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 2)
    (hF : KMSWPeanoDescendFrontier B c j hj P hj1)
    (hC : (kmswStage (codeExtend c) j).UR = [] →
      KMSWPeanoDescendCorner B c j hj P hj1) :
    KMSWPeanoPrefixEmbedding B c (j + 1) hj1 := by
  cases hUR : (kmswStage (codeExtend c) j).UR with
  | nil => exact kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR hF (hC hUR)
  | cons e es => exact kmswPeanoPrefixEmbedding_descend_activation B c j hj P hj1 hcode e es hUR hF

-- Concrete check of the supplied admissible example, and of its UR-head order.
private def descendExampleCode : Fin (5 - 1) → Fin 3 := fun i => if i.val < 2 then 1 else 2

private theorem descendExample_admissible : KMSWWalkAdmissible 3 1 5 descendExampleCode := by
  decide

private theorem descendExample_frontiers :
    let u := finiteCodeExtend descendExampleCode
    (kmswStage u 1).UR = [2] ∧ (kmswStage u 2).UR = [4, 2] ∧
      (kmswStage u 3).UR = [2] ∧ (kmswStage u 4).UR = [] ∧
      (kmswStage u 2).west 4 = (kmswStage u 2).east (kmswStage u 2).active ∧
      (kmswStage u 3).west 2 = (kmswStage u 3).east (kmswStage u 3).active := by
  decide

end DirectedDistances.KMSW
