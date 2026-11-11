module

public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariant
public import DirectedDistances.KMSW.KMSWPeanoPrefixRotate
public import DirectedDistances.KMSW.KMSWPeanoRotateFresh
public import DirectedDistances.KMSW.KMSWPeanoPrefixInduction

/-! Supporting lemmas for paper labels `thm-kmsw` (see CORRESPONDENCE.md). -/

/-! # Rotate-step preservation of the Peano-prefix geometric invariant

not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
variable {B : BipolarTriangulationWithBoundaryBase D ℓ r}
variable {c : KMSWWalkClass ℓ r n} {j : ℕ}
variable {hj : j < B.map.toCombinatorialMap.numEdges}

private theorem rotateInvariant_rot_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem rotateInvariant_config
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    PeanoStepConfig B j hj1 .rotate := by
  rw [← hkind]
  exact peanoStepKind_config B j hj1

private theorem rotateInvariant_newUR_geometry
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    let a := peanoEdge B ⟨j, by omega⟩
    let b := peanoEdge B ⟨j + 1, hj1⟩
    let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
    B.map.tail b ∧ B.map.tail q ∧
      dartTailVertex B.map q = dartHeadVertex B.map b ∧
      dartHeadVertex B.map q = dartHeadVertex B.map a ∧
      ∃ ht : dartHeadVertex B.map b ≠ B.sink,
        q = rightmostOutgoing B (dartHeadVertex B.map b) ht := by
  classical
  dsimp only
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  have ha : B.map.tail a := peanoEdge_forward B ⟨j, hj⟩
  have hb : B.map.tail b := peanoEdge_forward B ⟨j + 1, hj1⟩
  have hc := rotateInvariant_config (B := B) (j := j) hj1 hkind
  obtain ⟨hrot, htail, hcontour, _, hface, _⟩ := hc
  have hqv : dartTailVertex B.map q = dartHeadVertex B.map b := by
    dsimp [q]
    exact (rotateInvariant_rot_vertex (B := B) (B.map.toCombinatorialMap.edgeInv b)).trans rfl
  have hface₂ : B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.faceSucc a) = B.map.toCombinatorialMap.edgeInv b := hface
  have hqeq : q = B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.faceSucc a) := by
    dsimp [q]
    rw [← hface₂]
    simp [CombinatorialMap.faceSucc]
  have hsource : dartHeadVertex B.map a ≠ B.source :=
    contour_forward_head_ne_source B a ha
  have hfaceSucc_not : ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc a) := by
    by_cases hsink : dartHeadVertex B.map a = B.sink
    · intro hforward
      apply B.isSink
      have hvertex : dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc a) = B.sink :=
        (corner_consecutiveDarts B a).2.2.trans hsink
      exact ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.faceSucc a),
        ⟨B.map.toCombinatorialMap.faceSucc a, B.noMissingDarts _, hforward,
          hvertex, rfl⟩⟩
    · have hleft : B.map.toCombinatorialMap.edgeInv a ≠
          leftmostIncoming B (dartHeadVertex B.map a) hsource := by
        intro heq
        have hnext : contourNext B a =
            rightmostOutgoing B (dartHeadVertex B.map a) hsink := by
          simp [contourNext, ha, heq, hsink]
        have hsel := hnext.symm.trans hcontour
        have hselTail := (rightmostOutgoing_internal_characterization B
          (dartHeadVertex B.map a) hsource hsink).2.1
        have hinvNot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv a) :=
          (B.map.tail_iff a (B.noMissingDarts a)).mp ha
        exact hinvNot (hsel ▸ hselTail)
      intro hforward
      apply hleft
      exact (leftmostIncoming_internal_characterization B
        (dartHeadVertex B.map a) hsource hsink).2.2.2
          (B.map.toCombinatorialMap.edgeInv a)
          (by simp [dartTailVertex, dartHeadVertex])
          ((B.map.tail_iff a (B.noMissingDarts a)).mp ha)
          (by simpa [CombinatorialMap.faceSucc] using hforward)
  have hqtail : B.map.tail q := by
    rw [hqeq]
    exact (B.map.tail_iff (B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.faceSucc a)) (B.noMissingDarts _)).2
        (by simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hfaceSucc_not)
  have hqhead : dartHeadVertex B.map q = dartHeadVertex B.map a := by
    rw [hqeq]
    simp only [dartHeadVertex, B.map.toCombinatorialMap.edgeInv_invol]
    exact (corner_consecutiveDarts B a).2.2
  have htailSink : dartHeadVertex B.map b ≠ B.sink := by
    intro h
    apply B.isSink
    exact ⟨dartHeadVertex B.map q,
      ⟨q, B.noMissingDarts q, hqtail, (hqv.trans h), rfl⟩⟩
  have hprev : ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm q) := by
    dsimp [q]
    simp only [Equiv.symm_apply_apply]
    exact (B.map.tail_iff b (B.noMissingDarts b)).mp hb
  have hsel := (rightmostOutgoing_internal_characterization B
    (dartHeadVertex B.map b) (contour_forward_head_ne_source B b hb) htailSink).2.2.2
      q hqv hqtail hprev
  exact ⟨hb, hqtail, hqv, hqhead, ⟨htailSink, hsel⟩⟩

private theorem rotateInvariant_rightmost_congr
    (v w : MapVertex B.map) (hvw : v = w)
    (hv : v ≠ B.sink) (hw : w ≠ B.sink) :
    rightmostOutgoing B v hv = rightmostOutgoing B w hw := by
  let sv : {x : MapVertex B.map // x ≠ B.sink} := ⟨v, hv⟩
  let sw : {x : MapVertex B.map // x ≠ B.sink} := ⟨w, hw⟩
  have hsub : sv = sw := Subtype.ext hvw
  exact congrArg (fun x : {x : MapVertex B.map // x ≠ B.sink} =>
    rightmostOutgoing B x.1 x.2) hsub



theorem kmswPeanoPrefixInv_rotate
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 1)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hfresh : KMSWRotateFreshVertex P hj1) :
    KMSWPeanoPrefixInv B c (j + 1) hj1
      (kmswPeanoPrefixEmbedding_rotate P hj1 hcode hkind hfresh) := by
  classical
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let a := peanoEdge B ⟨j, hj⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let q := B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)
  let Q := kmswPeanoPrefixEmbedding_rotate P hj1 hcode hkind hfresh
  have hfacts := kmswStage_step_up_facts u j hcode
  rcases hfacts with ⟨hn, _, _, _, _, _, _, _, _, hUL, _, hUR, hLL⟩
  have hURt : t.UR = (s.nextEdge + 1) :: s.UR := hUR
  have hactiveLt : s.nextEdge < t.nextEdge := by
    calc
      s.nextEdge < s.nextEdge + 2 := by omega
      _ = t.nextEdge := hn.symm
  have hmissingLt : s.nextEdge + 1 < t.nextEdge := by
    calc
      s.nextEdge + 1 < s.nextEdge + 2 := by omega
      _ = t.nextEdge := hn.symm
  have hgeom := rotateInvariant_newUR_geometry (B := B) (j := j) (hj := hj) hj1 hkind
  dsimp only [a, b, q] at hgeom
  obtain ⟨hb, hq, hqv, hqhead, ⟨htq, hqsel⟩⟩ := hgeom
  have htailb : dartTailVertex B.map b = dartTailVertex B.map a := by
    have hc := rotateInvariant_config (B := B) (j := j) hj1 hkind
    exact hc.2.1
  have oldAt (d : StageDart t.nextEdge) (hold : d.1.val < s.nextEdge) :
      Q.emb.dartMap d = P.emb.dartMap (⟨d.1.val, hold⟩, d.2) := by
    change kmswPeanoRotateDartMap P hj1 d = _
    have hold' : d.1.val < (kmswStage (codeExtend c) j).nextEdge := hold
    simp only [kmswPeanoRotateDartMap, dite_eq_left hold']
  have oldCast (d : StageDart s.nextEdge) :
      Q.emb.dartMap (outerSucc_castDart
        (kmswStage_nextEdge_mono u (Nat.le_succ j)) d) = P.emb.dartMap d := by
    change kmswPeanoRotateDartMap P hj1 _ = _
    exact kmswPeanoRotateDartMap_old P hj1 d
  have newActive (side : Bool) :
      Q.emb.dartMap
        ((⟨s.nextEdge, hactiveLt⟩ : Fin t.nextEdge), side) =
          (if side then B.map.toCombinatorialMap.edgeInv b else b) := by
    change kmswPeanoRotateDartMap P hj1 _ = _
    simpa only [s, b, q] using
      (kmswPeanoRotateDartMap_new P hj1 hcode side).1
  have newUR (side : Bool) :
      Q.emb.dartMap
        ((⟨s.nextEdge + 1, hmissingLt⟩ : Fin t.nextEdge), side) =
          (if side then B.map.toCombinatorialMap.edgeInv q else q) := by
    change kmswPeanoRotateDartMap P hj1 _ = _
    simpa only [s, b, q] using
      (kmswPeanoRotateDartMap_new P hj1 hcode side).2
  let activeDart : StageDart t.nextEdge :=
    ((⟨s.nextEdge, hactiveLt⟩ : Fin t.nextEdge), false)
  let missingDart : StageDart t.nextEdge :=
    ((⟨s.nextEdge + 1, hmissingLt⟩ : Fin t.nextEdge), false)
  let activeOld : StageDart s.nextEdge :=
    (kmswRootedStage u j).root
  let activeOldFlip : StageDart s.nextEdge :=
    (kmswRootedStage u j).map.edgeInv activeOld
  have hrActive : P.emb.dartMap activeOld = a := by
    dsimp only [activeOld, a, u]
    exact P.emb.root_comm
  have hflipActive := P.emb.flip_comm activeOld
  change P.emb.dartMap activeOldFlip =
      B.map.toCombinatorialMap.edgeInv (P.emb.dartMap activeOld) at hflipActive
  have hrActiveFlip : P.emb.dartMap activeOldFlip =
      B.map.toCombinatorialMap.edgeInv a := by
    rw [hrActive] at hflipActive
    exact hflipActive
  have activeReverseVal : Q.emb.dartMap (edgeFlip t.nextEdge activeDart) =
      B.map.toCombinatorialMap.edgeInv b := by
    have hh := Q.emb.flip_comm activeDart
    rw [newActive false] at hh
    exact hh
  have missingReverseVal : Q.emb.dartMap (edgeFlip t.nextEdge missingDart) =
      B.map.toCombinatorialMap.edgeInv q := by
    have hh := Q.emb.flip_comm missingDart
    rw [newUR false] at hh
    exact hh
  have hqstep : B.map.directedStep (dartHeadVertex B.map b)
      (dartHeadVertex B.map a) := by
    refine ⟨q, B.noMissingDarts q, hq, hqv, ?_⟩
    exact hqhead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he' : e < s.nextEdge ∨ e = s.nextEdge ∨ e = s.nextEdge + 1 := by
      have hbnd : e < s.nextEdge + 2 := by rw [← hn]; exact he
      omega
    rcases he' with hold | hactive | hmissing
    · have hmap := oldAt ((⟨e, he⟩ : Fin t.nextEdge), false) hold
      rw [hmap]
      exact I.geometric_forward e hold
    · have hmap : Q.emb.dartMap ((⟨e, he⟩ : Fin t.nextEdge), false) = b := by
        subst e
        simp only [newActive, Bool.false_eq_true, ↓reduceIte]
      rw [hmap]
      exact hb
    · have hmap : Q.emb.dartMap ((⟨e, he⟩ : Fin t.nextEdge), false) = q := by
        subst e
        simp only [newUR, Bool.false_eq_true, ↓reduceIte]
      rw [hmap]
      exact hq
  · intro v
    constructor
    · rintro ⟨d, hd⟩
      have hold : d.1.val < s.nextEdge ∨ d.1.val = s.nextEdge ∨
          d.1.val = s.nextEdge + 1 := by
        have hbnd : d.1.val < s.nextEdge + 2 := by rw [← hn]; exact d.1.isLt
        omega
      rcases hold with hold | hactive | hmissing
      · obtain ⟨k, hk, hv⟩ := (I.vertices_prefix v).1
          ⟨_, (congrArg (dartTailVertex B.map) (oldAt d hold).symm).trans hd⟩
        exact ⟨k, by omega, hv⟩
      · cases hs : d.2
        · have hdval : d = activeDart := by
            apply Prod.ext
            · exact Fin.ext hactive
            · exact hs
          subst d
          refine ⟨⟨j, hj⟩, Nat.le_succ j, Or.inl ?_⟩
          have htailMap : dartTailVertex B.map b = v := by
            rw [newActive false] at hd
            simpa only [Bool.false_eq_true, ↓reduceIte] using hd
          exact htailb.symm.trans htailMap
        · have hdval : d = edgeFlip _ activeDart := by
            apply Prod.ext
            · exact Fin.ext hactive
            · exact hs
          subst d
          refine ⟨⟨j + 1, hj1⟩, Nat.le_refl _, Or.inr ?_⟩
          rw [activeReverseVal] at hd
          change dartHeadVertex B.map b = v at hd
          exact hd
      · cases hs : d.2
        · have hdval : d = missingDart := by
            apply Prod.ext
            · exact Fin.ext hmissing
            · exact hs
          subst d
          refine ⟨⟨j + 1, hj1⟩, Nat.le_refl _, Or.inr ?_⟩
          rw [newUR false] at hd
          change dartTailVertex B.map q = v at hd
          exact hqv.symm.trans hd
        · have hdval : d = edgeFlip _ missingDart := by
            apply Prod.ext
            · exact Fin.ext hmissing
            · exact hs
          subst d
          refine ⟨⟨j, hj⟩, Nat.le_succ j, Or.inr ?_⟩
          rw [missingReverseVal] at hd
          change dartHeadVertex B.map q = v at hd
          exact hqhead.symm.trans hd
    · rintro ⟨k, hk, hv⟩
      by_cases hkj : k.val ≤ j
      · rcases hv with hv | hv
        · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, Or.inl hv⟩
          exact ⟨outerSucc_castDart
            (kmswStage_nextEdge_mono u (Nat.le_succ j)) d,
            (congrArg (dartTailVertex B.map) (oldCast d)).trans hd⟩
        · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, Or.inr hv⟩
          exact ⟨outerSucc_castDart
            (kmswStage_nextEdge_mono u (Nat.le_succ j)) d,
            (congrArg (dartTailVertex B.map) (oldCast d)).trans hd⟩
      · have hkval : k.val = j + 1 := by omega
        have hk' : k = ⟨j + 1, hj1⟩ := Fin.ext hkval
        subst k
        rcases hv with hv | hv
        · refine ⟨activeDart, ?_⟩
          change dartTailVertex B.map (Q.emb.dartMap activeDart) = _
          rw [newActive false]
          exact hv
        · refine ⟨edgeFlip _ activeDart, ?_⟩
          rw [activeReverseVal]
          change dartHeadVertex B.map b = _
          exact hv
  · intro e es hlist he ht
    have hlist' : t.UR = (s.nextEdge + 1) :: s.UR := hURt
    rw [hlist'] at hlist
    have heq : e = s.nextEdge + 1 := by injection hlist with hhead htail; exact hhead.symm
    subst e
    have hmap := newUR false
    rw [hmap]
    have hproof : ht = htq := Subsingleton.elim _ _
    rw [hproof]
    exact hqsel
  · have hchainOld := I.UR_chain
    cases hURold : s.UR with
    | nil =>
        rw [hURt, hURold]
        exact List.isChain_singleton _
    | cons f fs =>
        rw [hURt, hURold, List.isChain_cons_cons]
        constructor
        · intro hf hg ht
          have hfBound : f < s.nextEdge :=
            ((kmswStageFrontierChain_all u j).UR_missing_bounded f
              (by rw [hURold]; simp)).2
          have hqHead : dartHeadVertex B.map
              (Q.emb.dartMap ((⟨s.nextEdge + 1, hf⟩ : Fin t.nextEdge), false)) =
                dartHeadVertex B.map a := by
            simpa only [newUR, Bool.false_eq_true, ↓reduceIte] using hqhead
          have htOld : dartHeadVertex B.map a ≠ B.sink := by
            rw [← hqHead]
            exact ht
          have hparent := I.UR_head f fs hURold hfBound htOld
          change P.emb.dartMap (⟨f, hfBound⟩, false) =
            rightmostOutgoing B (dartHeadVertex B.map a) htOld at hparent
          have hright := rotateInvariant_rightmost_congr (B := B)
            (dartHeadVertex B.map a)
            (dartHeadVertex B.map
              (Q.emb.dartMap ((⟨s.nextEdge + 1, hf⟩ : Fin t.nextEdge), false)))
            hqHead.symm htOld ht
          have hmap := oldAt ((⟨f, lt_trans hfBound hactiveLt⟩ : Fin t.nextEdge), false)
            hfBound
          calc
            Q.emb.dartMap ((⟨f, lt_trans hfBound hactiveLt⟩ : Fin t.nextEdge), false) =
                P.emb.dartMap (⟨f, hfBound⟩, false) := hmap
            _ = rightmostOutgoing B
                (dartHeadVertex B.map
                  (Q.emb.dartMap ((⟨s.nextEdge + 1, hf⟩ : Fin t.nextEdge), false))) ht :=
                    hparent.trans hright
        · rw [hURold] at hchainOld
          apply hchainOld.imp_of_mem_imp
          intro f' g' hfMem hgMem hfg hf' hg' ht
          have hfIn : f' ∈ s.UR := by rw [hURold]; exact hfMem
          have hgIn : g' ∈ s.UR := by rw [hURold]; exact hgMem
          have hfBound : f' < s.nextEdge :=
            ((kmswStageFrontierChain_all u j).UR_missing_bounded f'
              hfIn).2
          have hgBound : g' < s.nextEdge :=
            ((kmswStageFrontierChain_all u j).UR_missing_bounded g'
              hgIn).2
          have hff := oldAt ((⟨f', hf'⟩ : Fin t.nextEdge), false) hfBound
          have hgg := oldAt ((⟨g', hg'⟩ : Fin t.nextEdge), false) hgBound
          have hff' : Q.emb.dartMap (⟨f', hf'⟩, false) =
              P.emb.dartMap (⟨f', hfBound⟩, false) := by simpa using hff
          have hgg' : Q.emb.dartMap (⟨g', hg'⟩, false) =
              P.emb.dartMap (⟨g', hgBound⟩, false) := by simpa using hgg
          have htOld : dartHeadVertex B.map (P.emb.dartMap (⟨f', hfBound⟩, false)) ≠ B.sink := by
            rw [← hff']
            exact ht
          calc
            Q.emb.dartMap (⟨g', hg'⟩, false) = P.emb.dartMap (⟨g', hgBound⟩, false) := hgg'
            _ = rightmostOutgoing B
                (dartHeadVertex B.map (P.emb.dartMap (⟨f', hfBound⟩, false))) htOld :=
                  hfg hfBound hgBound htOld
            _ = rightmostOutgoing B
                (dartHeadVertex B.map (Q.emb.dartMap (⟨f', hf'⟩, false))) ht := by
                  simp only [← hff']
  · intro hnil d
    rw [hURt] at hnil
    cases hnil
  · intro e hlast he d
    cases hURold : s.UR with
    | nil =>
        have heq : e = s.nextEdge + 1 := by
          have hh := hlast
          rw [hURt, hURold] at hh
          simp only [List.getLast?_singleton] at hh
          exact (Option.some.inj hh).symm
        have htop : dartHeadVertex B.map
            (Q.emb.dartMap ((⟨e, he⟩ : Fin t.nextEdge), false)) =
              dartHeadVertex B.map a := by
          subst e
          rw [newUR false]
          exact hqhead
        rw [htop]
        have oldReach (d' : StageDart s.nextEdge) :
            Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map (P.emb.dartMap d')) (dartHeadVertex B.map a) :=
          I.top_reachable_empty hURold d'
        have qToActiveFlip : Relation.ReflTransGen B.map.directedStep
            (dartHeadVertex B.map b)
            (dartTailVertex B.map (P.emb.dartMap activeOldFlip)) := by
          rw [hrActiveFlip]
          simpa only [dartTailVertex, dartHeadVertex,
            B.map.toCombinatorialMap.edgeInv_invol] using
              (Relation.ReflTransGen.single hqstep)
        have hcase : d.1.val < s.nextEdge ∨ d.1.val = s.nextEdge ∨
            d.1.val = s.nextEdge + 1 := by
          have hbnd : d.1.val < s.nextEdge + 2 := by rw [← hn]; exact d.1.isLt
          omega
        rcases hcase with hold | hactive | hmissing
        · rw [oldAt d hold]
          exact oldReach (⟨d.1.val, hold⟩, d.2)
        · cases hs : d.2
          · have hdval : d = activeDart := Prod.ext (Fin.ext hactive) hs
            subst d
            rw [newActive false]
            change Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map b) (dartHeadVertex B.map a)
            rw [htailb]
            have hreach := oldReach activeOld
            rw [hrActive] at hreach
            exact hreach
          · have hdval : d = edgeFlip _ activeDart := Prod.ext (Fin.ext hactive) hs
            subst d
            rw [activeReverseVal]
            have htailInv : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv b) =
                dartHeadVertex B.map b := rfl
            rw [htailInv]
            exact qToActiveFlip.trans (oldReach activeOldFlip)
        · cases hs : d.2
          · have hdval : d = missingDart := Prod.ext (Fin.ext hmissing) hs
            subst d
            rw [newUR false]
            change Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map q) (dartHeadVertex B.map a)
            rw [hqv]
            exact qToActiveFlip.trans (oldReach activeOldFlip)
          · have hdval : d = edgeFlip _ missingDart := Prod.ext (Fin.ext hmissing) hs
            subst d
            rw [missingReverseVal]
            have htailInv : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv q) =
                dartHeadVertex B.map q := rfl
            rw [htailInv, hqhead]
    | cons f fs =>
        have hlastInList : (f :: fs).getLast? = some e := by
          change t.UR.getLast? = some e at hlast
          rw [hURt] at hlast
          rw [hURold] at hlast
          simp only [List.getLast?_cons_cons] at hlast
          exact hlast
        have hlastOld : s.UR.getLast? = some e := hURold.symm ▸ hlastInList
        have hmem : e ∈ s.UR := by
          have hmem' : e ∈ f :: fs :=
            List.mem_of_mem_getLast? (by simp only [hlastInList, Option.mem_def])
          exact hURold.symm ▸ hmem'
        have heOld : e < s.nextEdge :=
          ((kmswStageFrontierChain_all u j).UR_missing_bounded e
            hmem).2
        let oldTop : MapVertex B.map :=
          dartHeadVertex B.map (P.emb.dartMap (⟨e, heOld⟩, false))
        have htop : dartHeadVertex B.map
            (Q.emb.dartMap ((⟨e, he⟩ : Fin t.nextEdge), false)) = oldTop := by
          rw [oldAt ((⟨e, he⟩ : Fin t.nextEdge), false) heOld]
        rw [htop]
        have oldReach (d' : StageDart s.nextEdge) :
            Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map (P.emb.dartMap d')) oldTop :=
          I.top_reachable_nonempty e hlastOld heOld d'
        have qToActiveFlip : Relation.ReflTransGen B.map.directedStep
            (dartHeadVertex B.map b)
            (dartTailVertex B.map (P.emb.dartMap activeOldFlip)) := by
          rw [hrActiveFlip]
          simpa only [dartTailVertex, dartHeadVertex,
            B.map.toCombinatorialMap.edgeInv_invol] using
              (Relation.ReflTransGen.single hqstep)
        have hcase : d.1.val < s.nextEdge ∨ d.1.val = s.nextEdge ∨
            d.1.val = s.nextEdge + 1 := by
          have hbnd : d.1.val < s.nextEdge + 2 := by rw [← hn]; exact d.1.isLt
          omega
        rcases hcase with hold | hactive | hmissing
        · rw [oldAt d hold]
          exact oldReach (⟨d.1.val, hold⟩, d.2)
        · cases hs : d.2
          · have hdval : d = activeDart := Prod.ext (Fin.ext hactive) hs
            subst d
            rw [newActive false]
            change Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map b) oldTop
            rw [htailb]
            have hreach := oldReach activeOld
            rw [hrActive] at hreach
            exact hreach
          · have hdval : d = edgeFlip _ activeDart := Prod.ext (Fin.ext hactive) hs
            subst d
            rw [activeReverseVal]
            have htailInv : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv b) =
                dartHeadVertex B.map b := rfl
            rw [htailInv]
            exact qToActiveFlip.trans (oldReach activeOldFlip)
        · cases hs : d.2
          · have hdval : d = missingDart := Prod.ext (Fin.ext hmissing) hs
            subst d
            rw [newUR false]
            change Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map q) oldTop
            rw [hqv]
            exact qToActiveFlip.trans (oldReach activeOldFlip)
          · have hdval : d = edgeFlip _ missingDart := Prod.ext (Fin.ext hmissing) hs
            subst d
            rw [missingReverseVal]
            have htailInv : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv q) =
                dartHeadVertex B.map q := rfl
            rw [htailInv, hqhead]
            have hstart : dartTailVertex B.map (P.emb.dartMap activeOldFlip) =
                dartHeadVertex B.map a := by
              exact congrArg (dartTailVertex B.map) hrActiveFlip
            rw [← hstart]
            exact oldReach activeOldFlip
  · intro e he
    rw [hUL] at he
    have heOld : e ∈ s.UL.dropLast := by
      rw [List.dropLast_concat] at he
      exact he
    have heUL : e ∈ s.UL := List.mem_of_mem_dropLast heOld
    have heLt : e < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge u j).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl heUL)))
    intro heBound
    rw [oldAt ((⟨e, heBound⟩ : Fin t.nextEdge), true) heLt,
      oldAt ((⟨e, heBound⟩ : Fin t.nextEdge), false) heLt]
    exact I.UL_parent e heOld heLt
  · intro e he
    rw [hLL] at he
    have heLt : e < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge u j).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inr he))
    intro heBound
    rw [oldAt ((⟨e, heBound⟩ : Fin t.nextEdge), true) heLt,
      oldAt ((⟨e, heBound⟩ : Fin t.nextEdge), false) heLt]
    exact I.LL_parent e he heLt

/-- The fresh rotate vertex and inverse construction turn rotate-step
embedding preservation into full invariant preservation. Helper toward -/
theorem kmswPeanoPrefixInv_rotate_of_inv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hcode : codeExtend c j = 1) :
    KMSWPeanoPrefixInv B c (j + 1) hj1
      (kmswPeanoPrefixEmbedding_rotate_of_inv B c j hj P I hj1 hkind hcode) := by
  have hfresh := kmswPeanoPrefixInv_rotateFresh B c j hj P I hj1 hkind
  exact kmswPeanoPrefixInv_rotate B c j hj P I hj1 hcode hkind hfresh

/-- The rotate step preserves the full Peano-prefix invariant. Helper toward -/
theorem kmswPeanoRotatePreserves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) : KMSWPeanoRotatePreserves B c := by
  intro j hj P I hj1 hkind hcode
  exact ⟨kmswPeanoPrefixEmbedding_rotate_of_inv B c j hj P I hj1 hkind hcode,
    kmswPeanoPrefixInv_rotate_of_inv B c j hj P I hj1 hkind hcode⟩

end DirectedDistances.KMSW
