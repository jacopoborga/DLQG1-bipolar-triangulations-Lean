module

public import DirectedDistances.KMSW.KMSWPeanoPrefixDescend
public import DirectedDistances.KMSW.KMSWStageFrontierChain

/-! Supporting lemmas for paper labels `def-kmsw`, `thm-kmsw` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}








structure KMSWPeanoPrefixInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) : Prop where
  geometric_forward : ∀ (e : ℕ) (he : e < (kmswStage (codeExtend c) j).nextEdge),
    B.map.tail (P.emb.dartMap (⟨e, he⟩, false))
  vertices_prefix : ∀ v : MapVertex B.map,
    (∃ d, dartTailVertex B.map (P.emb.dartMap d) = v) ↔
      ∃ k : Fin B.map.toCombinatorialMap.numEdges, k.val ≤ j ∧
        (dartTailVertex B.map (peanoEdge B k) = v ∨
          dartHeadVertex B.map (peanoEdge B k) = v)
  UR_head : ∀ e es, (kmswStage (codeExtend c) j).UR = e :: es →
    ∀ (he : e < (kmswStage (codeExtend c) j).nextEdge)
      (ht : dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩) ≠ B.sink),
      P.emb.dartMap (⟨e, he⟩, false) =
        rightmostOutgoing B (dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩)) ht
  UR_chain : List.IsChain (fun e f =>
    ∀ (he : e < (kmswStage (codeExtend c) j).nextEdge)
      (hf : f < (kmswStage (codeExtend c) j).nextEdge)
      (ht : dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false)) ≠ B.sink),
      P.emb.dartMap (⟨f, hf⟩, false) =
        rightmostOutgoing B (dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false))) ht)
    (kmswStage (codeExtend c) j).UR
  top_reachable_empty : (kmswStage (codeExtend c) j).UR = [] → ∀ d,
    Relation.ReflTransGen B.map.directedStep
      (dartTailVertex B.map (P.emb.dartMap d))
      (dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩))
  top_reachable_nonempty : ∀ e,
    (kmswStage (codeExtend c) j).UR.getLast? = some e →
    ∀ (he : e < (kmswStage (codeExtend c) j).nextEdge) d,
      Relation.ReflTransGen B.map.directedStep
        (dartTailVertex B.map (P.emb.dartMap d))
        (dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false)))
  UL_parent : ∀ e ∈ (kmswStage (codeExtend c) j).UL.dropLast,
    ∀ he : e < (kmswStage (codeExtend c) j).nextEdge,
      ∃ hs : dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false)) ≠ B.source,
        P.emb.dartMap (⟨e, he⟩, true) =
          leftmostIncoming B (dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false))) hs
  LL_parent : ∀ e ∈ (kmswStage (codeExtend c) j).LL,
    ∀ he : e < (kmswStage (codeExtend c) j).nextEdge,
      ∃ hs : dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false)) ≠ B.source,
        P.emb.dartMap (⟨e, he⟩, true) =
          leftmostIncoming B (dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false))) hs



theorem kmswPeanoPrefixInv_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) :
    KMSWPeanoPrefixInv B c 0 (contour_numEdges_pos B)
      (kmswPeanoPrefixEmbedding_zero B c) := by
  let a := peanoEdge B ⟨0, contour_numEdges_pos B⟩
  have hmap (d : StageDart (kmswStage (codeExtend c) 0).nextEdge) :
      (kmswPeanoPrefixEmbedding_zero B c).emb.dartMap d =
        if d.2 then B.map.toCombinatorialMap.edgeInv a else a := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [hmap]
    exact peanoEdge_forward B _
  · intro v
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨⟨0, contour_numEdges_pos B⟩, Nat.le_refl 0, ?_⟩
      rw [hmap]
      cases d.2
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro ⟨k, hk, hv⟩
      have hk0 : k = ⟨0, contour_numEdges_pos B⟩ := Fin.ext (Nat.eq_zero_of_le_zero hk)
      subst k
      rcases hv with hv | hv
      · exact ⟨(⟨0, by simp [kmswStage, kmswInit]⟩, false), hv⟩
      · exact ⟨(⟨0, by simp [kmswStage, kmswInit]⟩, true), hv⟩
  · intro e es h
    simp [kmswStage, kmswInit] at h
  · exact List.IsChain.nil
  · intro _ d
    rw [hmap]
    cases d.2
    · exact Relation.ReflTransGen.single
        ⟨a, B.noMissingDarts a, peanoEdge_forward B _, rfl, rfl⟩
    · exact Relation.ReflTransGen.refl
  · intro e h
    simp [kmswStage, kmswInit] at h
  · intro e h
    simp [kmswStage, kmswInit] at h
  · intro e h
    simp [kmswStage, kmswInit] at h

private theorem inv_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (k : ℕ) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (show B.map.toCombinatorialMap.rot.SameCycle d
      ((B.map.toCombinatorialMap.rot : D → D)^[k] d) from
    ⟨(k : ℤ), by simp only [zpow_natCast]; rfl⟩).symm

private theorem inv_no_outgoing_at_top
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) (v : MapVertex B.map)
    (hreach : ∀ d, Relation.ReflTransGen B.map.directedStep
      (dartTailVertex B.map (P.emb.dartMap d)) v)
    (q : D) (hq : B.map.tail q) (hqv : dartTailVertex B.map q = v) :
    q ∉ Set.range P.emb.dartMap := by
  rintro ⟨d, hd⟩
  have hp := hreach (edgeFlip _ d)
  have hf := P.emb.flip_comm d
  change P.emb.dartMap (edgeFlip _ d) =
    B.map.toCombinatorialMap.edgeInv (P.emb.dartMap d) at hf
  rw [hf, hd] at hp
  have hs : B.map.directedStep v (dartHeadVertex B.map q) :=
    ⟨q, B.noMissingDarts q, hq, hqv, rfl⟩
  exact B.acyclic v (Relation.TransGen.head' hs hp)





theorem kmswPeanoPrefixInv_descendFrontier
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend) :
    KMSWPeanoDescendFrontier B c j hj P hj1 := by
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, ht, _, hb⟩ := hc
  constructor
  · intro e es hUR he
    exact (I.UR_head e es hUR he ht).trans hb.symm
  · intro hUR
    have hreach := I.top_reachable_empty hUR
    have hbTail := peanoEdge_forward B ⟨j + 1, hj1⟩
    have hbVertex : dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) =
        dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩) := by
      rw [hb]
      exact (rightmostOutgoing_internal_characterization B _ hs ht).1
    refine ⟨inv_no_outgoing_at_top B c j hj P _ hreach _ hbTail hbVertex, ?_⟩
    intro d hd
    have hstep : B.map.directedStep
        (dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩))
        (dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩)) :=
      ⟨_, B.noMissingDarts _, hbTail, hbVertex, rfl⟩
    have hp := hreach d
    rw [← hd] at hp
    exact B.acyclic _ (Relation.TransGen.head' hstep hp)




theorem kmswPeanoPrefixInv_descendCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend)
    (hUR : (kmswStage (codeExtend c) j).UR = []) :
    KMSWPeanoDescendCorner B c j hj P hj1 := by
  classical
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, ht, ha, hb⟩ := hc
  let v := dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩)
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let ρ := B.map.toCombinatorialMap.rot
  have hli := leftmostIncoming_internal_characterization B v hs ht
  have hro := rightmostOutgoing_internal_characterization B v hs ht
  have hbVertex : dartTailVertex B.map b = v := by
    change dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) = v
    rw [hb]
    exact hro.1
  have hcycle : ρ.SameCycle b (leftmostIncoming B v hs) :=
    Quotient.exact (hbVertex.trans hli.1.symm)
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hex : ∃ k : ℕ, ¬ B.map.tail ((ρ : D → D)^[k] b) := by
    refine ⟨k, ?_⟩
    have hpow : (ρ : D → D)^[k] b = leftmostIncoming B v hs := by
      simpa only [Equiv.Perm.coe_pow] using hk
    rw [hpow]
    exact hli.2.1
  let k := Nat.find hex
  have hkNot : ¬ B.map.tail ((ρ : D → D)^[k] b) := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hkNot
    exact hkNot (peanoEdge_forward B _)
  have hprev : B.map.tail ((ρ : D → D)^[k - 1] b) := by
    by_contra h
    exact Nat.find_min hex (by dsimp [k]; omega) h
  have hback : ρ.symm ((ρ : D → D)^[k] b) = (ρ : D → D)^[k - 1] b := by
    have heq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [heq, Function.iterate_succ_apply']
    exact ρ.symm_apply_apply _
  have hfirst : (ρ : D → D)^[k] b = leftmostIncoming B v hs :=
    hli.2.2.2 _ ((inv_rot_vertex B b k).trans hbVertex) hkNot (by rw [hback]; exact hprev)
  refine ⟨k, hkpos, hfirst.trans ha.symm, ?_⟩
  intro i _ hik
  have hiTail : B.map.tail ((ρ : D → D)^[i] b) := by
    by_contra h
    exact Nat.find_min hex hik h
  exact inv_no_outgoing_at_top B c j hj P v (I.top_reachable_empty hUR)
    _ hiTail ((inv_rot_vertex B b i).trans hbVertex)

private theorem inv_descend_activation
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend)
    (hcode : codeExtend c j = 2) (e : ℕ) (es : List ℕ)
    (hUR : (kmswStage (codeExtend c) j).UR = e :: es) :
    KMSWPeanoPrefixInv B c (j + 1) hj1
      (kmswPeanoPrefixEmbedding_descend_activation B c j hj P hj1 hcode e es hUR
        (kmswPeanoPrefixInv_descendFrontier B c j hj P I hj1 hkind)) := by
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let F := kmswPeanoPrefixInv_descendFrontier B c j hj P I hj1 hkind
  let Q := kmswPeanoPrefixEmbedding_descend_activation B c j hj P hj1 hcode e es hUR F
  have facts := kmswStage_step_activation_facts u j e es hcode hUR
  have hn : t.nextEdge = s.nextEdge := facts.1
  have bounds (f : ℕ) (hf : f < (kmswStage (codeExtend c) (j + 1)).nextEdge) :
      f < (kmswStage (codeExtend c) j).nextEdge := by
    change f < s.nextEdge
    rw [← hn]
    exact hf
  have hUL : t.UL = s.UL ++ [e] := facts.2.2.2.2.2.2.2.1
  have hURt : t.UR = es := facts.2.2.2.2.2.2.2.2.2.1
  have hLL : t.LL = s.LL := facts.2.2.2.2.2.2.2.2.2.2
  have hmap (f : ℕ) (hf : f < s.nextEdge) (hf' : f < t.nextEdge) (v : Bool) :
      Q.emb.dartMap (⟨f, hf'⟩, v) = P.emb.dartMap (⟨f, hf⟩, v) :=
    kmswPeanoPrefixEmbedding_descend_activation_old B c j hj P hj1 hcode e es hUR F
      (⟨f, hf⟩, v)
  have he : e < s.nextEdge :=
    ((kmswStageFrontierChain_all u j).UR_missing_bounded e
      (by rw [hUR]; exact List.mem_cons_self)).2
  have heImg : P.emb.dartMap (⟨e, he⟩, false) = peanoEdge B ⟨j + 1, hj1⟩ :=
    F.1 e es hUR he
  have old (d : StageDart t.nextEdge) :
      Q.emb.dartMap d = P.emb.dartMap (⟨d.1.val, by exact bounds _ d.1.isLt⟩, d.2) :=
    hmap _ _ _ _
  have old' (d : StageDart s.nextEdge) :
      Q.emb.dartMap (outerSucc_castDart (kmswStage_nextEdge_mono u (Nat.le_succ j)) d) =
        P.emb.dartMap d :=
    kmswPeanoPrefixEmbedding_descend_activation_old B c j hj P hj1 hcode e es hUR F d
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, _, ha, _⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hmap f (bounds _ hf) hf false]
    exact I.geometric_forward f _
  · intro v
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨k, hk, hv⟩ := (I.vertices_prefix v).1 ⟨_, (congrArg (dartTailVertex B.map) (old d).symm).trans hd⟩
      exact ⟨k, by omega, hv⟩
    · rintro ⟨k, hk, hv⟩
      by_cases hkj : k.val ≤ j
      · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, hv⟩
        exact ⟨_, (congrArg (dartTailVertex B.map) (old' d)).trans hd⟩
      · have hk1 : k = ⟨j + 1, hj1⟩ := Fin.ext (by change k.val = j + 1; omega)
        subst k
        rcases hv with hv | hv
        · refine ⟨(kmswRootedStage u (j + 1)).root, ?_⟩
          exact (congrArg (dartTailVertex B.map) Q.emb.root_comm).trans hv
        · refine ⟨edgeFlip _ (kmswRootedStage u (j + 1)).root, ?_⟩
          have hh := Q.emb.flip_comm (kmswRootedStage u (j + 1)).root
          change Q.emb.dartMap (edgeFlip _ _) = B.map.toCombinatorialMap.edgeInv
            (Q.emb.dartMap (kmswRootedStage u (j + 1)).root) at hh
          rw [hh, Q.emb.root_comm]
          exact hv
  · intro f fs hfs hf ht
    have hfs' : es = f :: fs := hURt.symm.trans hfs
    have hchain := I.UR_chain
    rw [hUR, hfs', List.isChain_cons_cons] at hchain
    have hh := hchain.1 he (bounds _ hf)
    rw [heImg] at hh
    rw [hmap f (bounds _ hf) hf false]
    exact hh ht
  · have hchain := I.UR_chain
    rw [hUR] at hchain
    have htail := hchain.tail
    change List.IsChain _ es at htail
    change List.IsChain _ t.UR
    rw [hURt]
    apply htail.imp
    intro f g hfg hf hg ht
    have hff := hmap f (bounds _ hf) hf false
    have hgg := hmap g (bounds _ hg) hg false
    dsimp only [Q] at hff hgg
    simpa only [hff, hgg] using hfg (bounds _ hf) (bounds _ hg)
      (by simpa only [hff] using ht)
  · intro hnil d
    have hes : es = [] := hURt.symm.trans hnil
    have hlast : s.UR.getLast? = some e := by rw [hUR, hes]; rfl
    have hh := I.top_reachable_nonempty e hlast he
      (⟨d.1.val, by exact bounds _ d.1.isLt⟩, d.2)
    rw [heImg] at hh
    rw [old d]
    exact hh
  · intro f hlast hf d
    change t.UR.getLast? = some f at hlast
    rw [hURt] at hlast
    have hes : es ≠ [] := by
      intro hnil
      rw [hnil] at hlast
      cases hlast
    have hlastOld : s.UR.getLast? = some f := by
      rw [hUR]
      cases es with
      | nil => exact False.elim (hes rfl)
      | cons g gs => simpa only [List.getLast?_cons_cons] using hlast
    rw [old d, hmap f (bounds _ hf) hf false]
    exact I.top_reachable_nonempty f hlastOld _ _
  · intro f hf hfBound
    have hfUL : f ∈ s.UL := by
      change f ∈ t.UL.dropLast at hf
      rw [hUL, List.dropLast_concat] at hf
      exact hf
    have hsplit : f ∈ s.UL.dropLast ∨ f = s.active := by
      have hh := List.dropLast_append_getLast? s.active
        (show s.active ∈ s.UL.getLast? from
          by rw [(kmswStageFrontierChain_all u j).UL_nonempty_active_last.2]; rfl)
      rw [← hh, List.mem_append, List.mem_singleton] at hfUL
      exact hfUL
    rw [hmap f (bounds _ hfBound) hfBound true, hmap f (bounds _ hfBound) hfBound false]
    rcases hsplit with hfOld | rfl
    · exact I.UL_parent f hfOld _
    · have hr : P.emb.dartMap
          (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, false) = peanoEdge B ⟨j, hj⟩ :=
        P.emb.root_comm
      have hh := P.emb.flip_comm
        (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, false)
      change P.emb.dartMap (⟨s.active, _⟩, true) =
        B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (⟨s.active, _⟩, false)) at hh
      refine ⟨by simpa only [hr] using hs, ?_⟩
      apply hh.trans
      simpa only [hr] using ha
  · intro f hf hfBound
    change f ∈ t.LL at hf
    rw [hLL] at hf
    rw [hmap f (bounds _ hfBound) hfBound true, hmap f (bounds _ hfBound) hfBound false]
    exact I.LL_parent f hf _

private theorem inv_descend_pendant
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend)
    (hcode : codeExtend c j = 2)
    (hUR : (kmswStage (codeExtend c) j).UR = []) :
    KMSWPeanoPrefixInv B c (j + 1) hj1
      (kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR
        (kmswPeanoPrefixInv_descendFrontier B c j hj P I hj1 hkind)
        (kmswPeanoPrefixInv_descendCorner B c j hj P I hj1 hkind hUR)) := by
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let F := kmswPeanoPrefixInv_descendFrontier B c j hj P I hj1 hkind
  let C := kmswPeanoPrefixInv_descendCorner B c j hj P I hj1 hkind hUR
  let Q := kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR F C
  let b := peanoEdge B ⟨j + 1, hj1⟩
  have facts := kmswStage_step_pendant_facts u j hcode hUR
  have hn : t.nextEdge = s.nextEdge + 1 := facts.1
  have hUL : t.UL = s.UL ++ [s.nextEdge] := facts.2.2.2.2.2.2.1
  have hURt : t.UR = [] := facts.2.2.2.2.2.2.2.2.1
  have hLL : t.LL = s.LL := facts.2.2.2.2.2.2.2.2.2
  have hmap (f : ℕ) (hf : f < s.nextEdge) (hf' : f < t.nextEdge) (v : Bool) :
      Q.emb.dartMap (⟨f, hf'⟩, v) = P.emb.dartMap (⟨f, hf⟩, v) :=
    kmswPeanoPrefixEmbedding_descend_pendant_old B c j hj P hj1 hcode hUR F C
      (⟨f, hf⟩, v)
  have hnew (f : Fin t.nextEdge) (hf : f.val = s.nextEdge) (v : Bool) :
      Q.emb.dartMap (f, v) = if v then B.map.toCombinatorialMap.edgeInv b else b :=
    kmswPeanoPrefixEmbedding_descend_pendant_new B c j hj P hj1 hcode hUR F C f hf v
  have old' (d : StageDart s.nextEdge) :
      Q.emb.dartMap (outerSucc_castDart (kmswStage_nextEdge_mono u (Nat.le_succ j)) d) =
        P.emb.dartMap d :=
    kmswPeanoPrefixEmbedding_descend_pendant_old B c j hj P hj1 hcode hUR F C d
  have old (d : StageDart t.nextEdge) (hd : d.1.val < s.nextEdge) :
      Q.emb.dartMap d = P.emb.dartMap (⟨d.1.val, hd⟩, d.2) := hmap _ _ _ _
  have bound (f : Fin t.nextEdge) : f.val < s.nextEdge ∨ f.val = s.nextEdge := by
    have hh : f.val < s.nextEdge + 1 := by rw [← hn]; exact f.isLt
    omega
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, ht, ha, hb⟩ := hc
  have hbVertex : dartTailVertex B.map b =
      dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩) := by
    change dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) = _
    rw [hb]
    exact (rightmostOutgoing_internal_characterization B _ hs ht).1
  have hstep : B.map.directedStep
      (dartHeadVertex B.map (peanoEdge B ⟨j, hj⟩)) (dartHeadVertex B.map b) :=
    ⟨b, B.noMissingDarts b, peanoEdge_forward B _, hbVertex, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rcases bound ⟨f, hf⟩ with hold | hnewf
    · rw [hmap f hold hf false]
      exact I.geometric_forward f hold
    · rw [hnew ⟨f, hf⟩ hnewf false]
      exact peanoEdge_forward B _
  · intro v
    constructor
    · rintro ⟨d, hd⟩
      rcases bound d.1 with hold | hnewf
      · obtain ⟨k, hk, hv⟩ := (I.vertices_prefix v).1
          ⟨_, (congrArg (dartTailVertex B.map) (old d hold).symm).trans hd⟩
        exact ⟨k, by omega, hv⟩
      · refine ⟨⟨j + 1, hj1⟩, Nat.le_refl _, ?_⟩
        have hh := hnew d.1 hnewf d.2
        change Q.emb.dartMap d = _ at hh
        change dartTailVertex B.map (Q.emb.dartMap d) = v at hd
        rw [hh] at hd
        cases hv : d.2
        · exact Or.inl (by simpa only [hv, Bool.false_eq_true, ↓reduceIte] using hd)
        · exact Or.inr (by simpa only [hv, ↓reduceIte, b, dartHeadVertex, dartTailVertex] using hd)
    · rintro ⟨k, hk, hv⟩
      by_cases hkj : k.val ≤ j
      · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, hv⟩
        exact ⟨_, (congrArg (dartTailVertex B.map) (old' d)).trans hd⟩
      · have hk1 : k = ⟨j + 1, hj1⟩ := Fin.ext (by change k.val = j + 1; omega)
        subst k
        rcases hv with hv | hv
        · refine ⟨(kmswRootedStage u (j + 1)).root, ?_⟩
          exact (congrArg (dartTailVertex B.map) Q.emb.root_comm).trans hv
        · refine ⟨edgeFlip _ (kmswRootedStage u (j + 1)).root, ?_⟩
          have hh := Q.emb.flip_comm (kmswRootedStage u (j + 1)).root
          change Q.emb.dartMap (edgeFlip _ _) = B.map.toCombinatorialMap.edgeInv
            (Q.emb.dartMap (kmswRootedStage u (j + 1)).root) at hh
          rw [hh, Q.emb.root_comm]
          exact hv
  · intro f fs hfs
    change t.UR = f :: fs at hfs
    rw [hURt] at hfs
    cases hfs
  · change List.IsChain _ t.UR
    rw [hURt]
    exact List.IsChain.nil
  · intro _ d
    rcases bound d.1 with hold | hnewf
    · rw [old d hold]
      exact (I.top_reachable_empty hUR _).tail hstep
    · have hh := hnew d.1 hnewf d.2
      change Q.emb.dartMap d = _ at hh
      change Relation.ReflTransGen B.map.directedStep
        (dartTailVertex B.map (Q.emb.dartMap d)) (dartHeadVertex B.map b)
      rw [hh]
      cases d.2
      · exact Relation.ReflTransGen.single
          ⟨b, B.noMissingDarts b, peanoEdge_forward B _, rfl, rfl⟩
      · exact Relation.ReflTransGen.refl
  · intro f hlast
    change t.UR.getLast? = some f at hlast
    rw [hURt] at hlast
    cases hlast
  · intro f hf hfBound
    have hfUL : f ∈ s.UL := by
      change f ∈ t.UL.dropLast at hf
      rw [hUL, List.dropLast_concat] at hf
      exact hf
    have hfOld : f < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u j).2 f
      (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hfUL)))
    have hsplit : f ∈ s.UL.dropLast ∨ f = s.active := by
      have hh := List.dropLast_append_getLast? s.active
        (show s.active ∈ s.UL.getLast? from
          by rw [(kmswStageFrontierChain_all u j).UL_nonempty_active_last.2]; rfl)
      rw [← hh, List.mem_append, List.mem_singleton] at hfUL
      exact hfUL
    rw [hmap f hfOld hfBound true, hmap f hfOld hfBound false]
    rcases hsplit with hfOldMem | rfl
    · exact I.UL_parent f hfOldMem _
    · have hr : P.emb.dartMap
          (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, false) = peanoEdge B ⟨j, hj⟩ :=
        P.emb.root_comm
      have hh := P.emb.flip_comm
        (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, false)
      change P.emb.dartMap (⟨s.active, _⟩, true) =
        B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (⟨s.active, _⟩, false)) at hh
      refine ⟨by simpa only [hr] using hs, ?_⟩
      apply hh.trans
      simpa only [hr] using ha
  · intro f hf hfBound
    change f ∈ t.LL at hf
    rw [hLL] at hf
    have hfOld : f < s.nextEdge :=
      ((kmswStageFrontierChain_all u j).LL_missing_bounded f hf).2
    rw [hmap f hfOld hfBound true, hmap f hfOld hfBound false]
    exact I.LL_parent f hf _





theorem kmswPeanoPrefixInv_descend
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .descend)
    (hcode : codeExtend c j = 2) :
    ∃ Q : KMSWPeanoPrefixEmbedding B c (j + 1) hj1,
      KMSWPeanoPrefixInv B c (j + 1) hj1 Q ∧
      ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
        Q.emb.dartMap
          (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
            P.emb.dartMap d := by
  let F := kmswPeanoPrefixInv_descendFrontier B c j hj P I hj1 hkind
  cases hUR : (kmswStage (codeExtend c) j).UR with
  | nil =>
    let C := kmswPeanoPrefixInv_descendCorner B c j hj P I hj1 hkind hUR
    refine ⟨kmswPeanoPrefixEmbedding_descend_pendant B c j hj P hj1 hcode hUR F C,
      inv_descend_pendant B c j hj P I hj1 hkind hcode hUR, ?_⟩
    exact kmswPeanoPrefixEmbedding_descend_pendant_old B c j hj P hj1 hcode hUR F C
  | cons e es =>
    refine ⟨kmswPeanoPrefixEmbedding_descend_activation B c j hj P hj1 hcode e es hUR F,
      inv_descend_activation B c j hj P I hj1 hkind hcode e es hUR, ?_⟩
    exact kmswPeanoPrefixEmbedding_descend_activation_old B c j hj P hj1 hcode e es hUR F

/-! Rotate and climb must re-establish exactly `geometric_forward`,
`vertices_prefix`, `UR_head`, `UR_chain`, `top_reachable_empty`,
`top_reachable_nonempty`, `UL_parent`, and `LL_parent`. The UL and LL parent
fields concern reverse darts at edge heads; the stage frontier chain bundle
supplies the ordered west/east incidences. In particular the active UL edge
is excluded from `UL_parent`. These are induction obligations, not conclusions
of the prefix embedding API. -/

end DirectedDistances.KMSW
