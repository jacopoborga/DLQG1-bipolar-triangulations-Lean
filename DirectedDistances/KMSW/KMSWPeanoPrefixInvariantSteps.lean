module

public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariant
public import DirectedDistances.KMSW.KMSWInverseStepLink
public import DirectedDistances.KMSW.KMSWInverseClass
public import DirectedDistances.PlanarMap.BipolarPeanoFirstVisit

/-! Supporting lemmas for paper labels `thm-kmsw` (see CORRESPONDENCE.md). -/

/-! # Consequences of the Peano prefix invariant -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}



theorem codeExtend_kmswRepInverseWalkClass
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    codeExtend (kmswRepInverseWalkClass R) j =
      kmswRepInverseCode R ⟨j, by omega⟩ := by
  rw [codeExtend_of_lt _ j (by omega), kmswRepInverseWalkClass_val]

/-- Code `2` for the inverse class is exactly the descend kind. -/
theorem codeExtend_kmswRepInverseWalkClass_eq_two_iff_peanoStepKind_descend
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    codeExtend (kmswRepInverseWalkClass R) j = 2 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .descend := by
  rw [codeExtend_kmswRepInverseWalkClass R j hj]
  exact kmswRepInverseCode_eq_two_iff_peanoStepKind_descend R j hj

/-- Code `0` for the inverse class is exactly the climb kind. -/
theorem codeExtend_kmswRepInverseWalkClass_eq_zero_iff_peanoStepKind_climb
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    codeExtend (kmswRepInverseWalkClass R) j = 0 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .climb := by
  rw [codeExtend_kmswRepInverseWalkClass R j hj]
  exact kmswRepInverseCode_eq_zero_iff_peanoStepKind_climb R j hj

/-- Code `1` for the inverse class is exactly the rotate kind. -/
theorem codeExtend_kmswRepInverseWalkClass_eq_one_iff_peanoStepKind_rotate
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    codeExtend (kmswRepInverseWalkClass R) j = 1 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .rotate := by
  rw [codeExtend_kmswRepInverseWalkClass R j hj]
  exact kmswRepInverseCode_eq_one_iff_peanoStepKind_rotate R j hj

private theorem steps_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (k : ℕ) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (show B.map.toCombinatorialMap.rot.SameCycle d
      ((B.map.toCombinatorialMap.rot : D → D)^[k] d) from
    ⟨(k : ℤ), by simp only [zpow_natCast]; rfl⟩).symm

private theorem steps_image_endpoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d e : StageDart (kmswStage (codeExtend c) j).nextEdge)
    (h : stageEndpoint (kmswStage (codeExtend c) j) d =
      stageEndpoint (kmswStage (codeExtend c) j) e) :
    dartTailVertex B.map (P.emb.dartMap d) =
      dartTailVertex B.map (P.emb.dartMap e) := by
  have hrot (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
      dartTailVertex B.map (P.emb.dartMap (stageRot (codeExtend c) j d)) =
        dartTailVertex B.map (P.emb.dartMap d) := by
    obtain ⟨k, _, hk, _⟩ := P.emb.rot_induced d
    change (B.map.toCombinatorialMap.rot : D → D)^[k] (P.emb.dartMap d) =
      P.emb.dartMap (stageRot (codeExtend c) j d) at hk
    rw [← hk]
    exact steps_rot_vertex B _ k
  obtain ⟨k, hk⟩ :=
    ((stageRot_sameCycle_iff_endpoint_eq (codeExtend c) j d e).2 h).exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hrot]
      exact ih

/-- The nearest UL predecessor is the third edge in a climb configuration.
This is the nonempty clause of the climb frontier predicate, written inline
so the module is independent of the climb construction under development. -/
theorem kmswPeanoPrefixInv_climbFrontier_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    ∀ e es, (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es →
      ∃ he : e < (kmswStage (codeExtend c) j).nextEdge,
        (kmswStage (codeExtend c) j).present e = true ∧
        P.emb.dartMap ((⟨e, he⟩, false) :
          StageDart (kmswStage (codeExtend c) j).nextEdge) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot
            (peanoEdge B ⟨j, by omega⟩)) := by
  intro e es hUL
  have hmem : e ∈ (kmswStage (codeExtend c) j).UL.dropLast :=
    List.mem_reverse.mp (by rw [hUL]; exact List.mem_cons_self)
  have hmemUL := List.mem_of_mem_dropLast hmem
  have F := kmswStageFrontierChain_all (codeExtend c) j
  have he := stageRotation_UL_bound (codeExtend c) j e hmemUL
  refine ⟨he, F.UL_present e hmemUL, ?_⟩
  have hv := steps_image_endpoint B c j hj P (⟨e, he⟩, true)
    (kmswRootedStage (codeExtend c) j).root
    (F.UL_predecessor_incidence e es hUL)
  rw [P.emb.root_comm] at hv
  change dartTailVertex B.map (P.emb.dartMap (⟨e, he⟩, true)) =
    dartTailVertex B.map (peanoEdge B ⟨j, hj⟩) at hv
  have hf := P.emb.flip_comm (⟨e, he⟩, false)
  change P.emb.dartMap (⟨e, he⟩, true) =
    B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (⟨e, he⟩, false)) at hf
  obtain ⟨hs, hp⟩ := I.UL_parent e hmem he
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hsA, _, _, _, _, hsel, _, _, _⟩ := hc
  have hhead : dartHeadVertex B.map (P.emb.dartMap (⟨e, he⟩, false)) =
      dartTailVertex B.map (peanoEdge B ⟨j, hj⟩) := by
    change dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv (P.emb.dartMap (⟨e, he⟩, false))) = _
    rw [← hf]
    exact hv
  have hp' : P.emb.dartMap (⟨e, he⟩, true) =
      B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩) := by
    rw [hp]
    simpa only [hhead] using hsel.symm
  have h := congrArg B.map.toCombinatorialMap.edgeInv (hf.symm.trans hp')
  simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h

private theorem steps_formPerm_map_consec {α β : Type*} [DecidableEq α]
    (f : α → β) (W : List α) (hnd : W.Nodup) (pre post : List β) (x y : β)
    (hV : W.map f = pre ++ x :: y :: post) :
    ∃ a ∈ W, ∃ b, f a = x ∧ f b = y ∧ W.formPerm a = b := by
  have hlen : pre.length + 1 < W.length := by
    have := congrArg List.length hV
    simp only [List.length_map, List.length_append, List.length_cons] at this
    omega
  have hmap : pre.length < (W.map f).length := by rw [List.length_map]; omega
  have hmap1 : pre.length + 1 < (W.map f).length := by rw [List.length_map]; omega
  refine ⟨W[pre.length], List.getElem_mem _, W[pre.length + 1], ?_, ?_, ?_⟩
  · have := List.getElem_of_eq hV hmap
    simpa using this
  · have := List.getElem_of_eq hV hmap1
    simpa using this
  · exact List.formPerm_apply_lt_getElem W hnd pre.length hlen

private theorem steps_active_successor_missing_forward
    (u : ℕ → Fin 3) (j : ℕ) :
    let a := (kmswRootedStage u j).root
    let d := (kmswMap u j).faceSucc a
    (kmswStage u j).present d.1.val = false → d.2 = false := by
  let s := kmswStage u j
  let a := (kmswRootedStage u j).root
  have hnext (y : ℕ × Bool) (post : List (ℕ × Bool))
      (hV : stageOuterWordVal u j =
        s.UL.dropLast.map (fun e => (e, false)) ++ (s.active, false) :: y :: post) :
      (((kmswMap u j).faceSucc a).1.val, ((kmswMap u j).faceSucc a).2) = y := by
    obtain ⟨x, hx, z, hxa, hz, hperm⟩ := steps_formPerm_map_consec
      (fun d : StageDart s.nextEdge => (d.1.val, d.2))
      (stageOuterWord u j) (stageOuterWord_nodup u j) _ _ _ _ hV
    have hroot : x = a := by
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst hxa)
      · change x.2 = false
        exact congrArg (fun z : ℕ × Bool => z.2) hxa
    have hf := (stageOuterWord_faceSucc u j x hx).trans hperm
    rw [hroot] at hf
    rw [hf]
    exact hz
  have hUL : s.UL = s.UL.dropLast ++ [s.active] := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
    have hd : s.UL.dropLast = xs := by rw [hxs]; simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    rw [hd]
    exact hxs
  change s.present ((kmswMap u j).faceSucc a).1.val = false →
    ((kmswMap u j).faceSucc a).2 = false
  intro hmiss
  cases hUR : s.UR with
  | cons e es =>
      have hv := hnext (e, false)
        ((es.map fun f => (f, false)) ++
          (s.LR.reverse.map fun f => (f, true)) ++
          (s.LL.reverse.map fun f => (f, true))) (by
            rw [stageOuterWordVal_eq_runs]
            change s.UL.map _ ++ s.UR.map _ ++ s.LR.reverse.map _ ++ s.LL.reverse.map _ = _
            nth_rw 1 [hUL]
            rw [hUR]
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.cons_append, List.nil_append])
      exact congrArg Prod.snd hv
  | nil =>
      cases hLR : s.LR.reverse with
      | nil =>
          have hnil : s.LR = [] := List.reverse_eq_nil_iff.mp hLR
          exact (kmswStage_LR_nonempty u j hnil).elim
      | cons e es =>
          have hv := hnext (e, true)
            ((es.map fun f => (f, true)) ++ (s.LL.reverse.map fun f => (f, true))) (by
              rw [stageOuterWordVal_eq_runs]
              change s.UL.map _ ++ s.UR.map _ ++ s.LR.reverse.map _ ++ s.LL.reverse.map _ = _
              nth_rw 1 [hUL]
              rw [hUR, hLR]
              simp only [List.map_append, List.map_cons, List.map_nil,
                List.append_assoc, List.cons_append, List.nil_append, List.append_nil])
          have he : e ∈ s.LR := List.mem_reverse.mp (by rw [hLR]; exact List.mem_cons_self)
          have hp := (kmswStageFrontierChain_all u j).LR_present e he
          have hid := congrArg Prod.fst hv
          change ((kmswMap u j).faceSucc a).1.val = e at hid
          rw [hid, hp] at hmiss
          cases hmiss

private theorem steps_image_immediate_rot
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d e : StageDart (kmswStage (codeExtend c) j).nextEdge)
    (h : B.map.toCombinatorialMap.rot (P.emb.dartMap d) = P.emb.dartMap e) :
    stageRot (codeExtend c) j d = e := by
  obtain ⟨k, hkpos, hk, hgap⟩ := P.emb.rot_induced d
  have hk1 : k = 1 := by
    by_contra hn
    have heNot := hgap 1 (by omega) (by omega)
    apply heNot
    exact ⟨e, h.symm⟩
  rw [hk1] at hk
  change B.map.toCombinatorialMap.rot (P.emb.dartMap d) =
    P.emb.dartMap (stageRot (codeExtend c) j d) at hk
  exact P.emb.injective (hk.symm.trans h)

private theorem steps_forward_eq_of_index
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : B.map.tail d) (k : Fin B.map.toCombinatorialMap.numEdges)
    (hi : peanoIndex B d = k) : d = peanoEdge B k := by
  classical
  have hidx := congrArg Fin.val (hi.trans (peanoIndex_peanoEdge B k).symm)
  change (firstVisitOrder B).idxOf (peanoForwardDart B d) =
    (firstVisitOrder B).idxOf (peanoForwardDart B (peanoEdge B k)) at hidx
  simp only [peanoForwardDart, hd, peanoEdge_forward, ↓reduceIte] at hidx
  exact (List.idxOf_inj ((mem_firstVisitOrder_iff B d).2 hd)).1 hidx

/-- No missing image dart has the next Peano index in a climb. This is the
collision predicate's body, independent of the climb module being edited. -/
theorem kmswPeanoPrefixInv_climbNoNextFrontierCollision
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      (kmswStage (codeExtend c) j).present d.1.val = false →
        (peanoIndex B (P.emb.dartMap d)).val ≠ j + 1 := by
  intro d hmiss hi
  let f : StageDart (kmswStage (codeExtend c) j).nextEdge := (d.1, false)
  let g : StageDart (kmswStage (codeExtend c) j).nextEdge := (d.1, true)
  let a := (kmswRootedStage (codeExtend c) j).root
  let A := edgeFlip _ a
  have hflip : P.emb.dartMap g =
      B.map.toCombinatorialMap.edgeInv (P.emb.dartMap f) := P.emb.flip_comm f
  have hif : (peanoIndex B (P.emb.dartMap f)).val = j + 1 := by
    cases hside : d.2 with
    | false =>
        have hd : d = f := Prod.ext rfl hside
        simpa only [hd] using hi
    | true =>
        have hd : d = g := Prod.ext rfl hside
        rw [hd, hflip, peanoIndex_edgeInv] at hi
        exact hi
  have hf : P.emb.dartMap f = peanoEdge B ⟨j + 1, hj1⟩ :=
    steps_forward_eq_of_index B _ (I.geometric_forward d.1.val d.1.isLt) _ (Fin.ext hif)
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv
      (peanoEdge B ⟨j, hj⟩) := by
    exact (P.emb.flip_comm a).trans
      (congrArg B.map.toCombinatorialMap.edgeInv P.emb.root_comm)
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨_, _, _, _, _, _, hb, _, _⟩ := hc
  have hrot : B.map.toCombinatorialMap.rot (P.emb.dartMap g) = P.emb.dartMap A := by
    rw [hflip, hf, hb, B.map.toCombinatorialMap.edgeInv_invol, hA]
    exact B.map.toCombinatorialMap.rot.apply_symm_apply _
  have hlocal := steps_image_immediate_rot B c j hj P g A hrot
  have hface : (kmswMap (codeExtend c) j).faceSucc a = g := by
    change (stageRot (codeExtend c) j).symm A = g
    rw [← hlocal]
    exact (stageRot (codeExtend c) j).symm_apply_apply g
  have hforward := steps_active_successor_missing_forward (codeExtend c) j
  dsimp only at hforward
  change (kmswStage (codeExtend c) j).present
      ((kmswMap (codeExtend c) j).faceSucc a).1.val = false →
    ((kmswMap (codeExtend c) j).faceSucc a).2 = false at hforward
  rw [hface] at hforward
  have hbad : true = false := hforward hmiss
  cases hbad

private def steps_geoStep (s : State) (x y : ℕ) : Prop :=
  ∃ e < s.nextEdge, s.west e = x ∧ s.east e = y

private theorem steps_geo_stable (u : ℕ → Fin 3) (j : ℕ) {x y : ℕ}
    (h : Relation.ReflTransGen (steps_geoStep (kmswStage u j)) x y) :
    Relation.ReflTransGen (steps_geoStep (kmswStage u (j + 1))) x y := by
  apply Relation.ReflTransGen.mono (r := steps_geoStep (kmswStage u j)) ?_ x y h
  rintro a b ⟨e, he, hw, ht⟩
  have hs := kmswStage_endpoints_stable u (Nat.le_succ j) he
  exact ⟨e, he.trans_le (kmswStage_nextEdge_mono u (Nat.le_succ j)),
    hs.1.trans hw, hs.2.trans ht⟩

private theorem steps_start_stable (s t : State) (es : List ℕ)
    (hwest : ∀ e ∈ es, t.west e = s.west e) :
    boundaryStart t es = boundaryStart s es := by
  cases es with
  | nil => rfl
  | cons e es =>
      change some (t.west e) = some (s.west e)
      rw [hwest e (List.mem_cons_self)]

private theorem steps_geo_source (u : ℕ → Fin 3) (j : ℕ) :
    ∃ v, boundaryStart (kmswStage u j) (kmswStage u j).UL = some v ∧
      ∀ x < (kmswStage u j).nextVertex,
        Relation.ReflTransGen (steps_geoStep (kmswStage u j)) v x := by
  induction j with
  | zero =>
      refine ⟨0, rfl, ?_⟩
      intro x hx
      change x < 2 at hx
      have h : x = 0 ∨ x = 1 := by omega
      rcases h with rfl | rfl
      · exact .refl
      · exact .single ⟨0, by change 0 < 1; decide, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨v, hv, hr⟩ := ih
      let s := kmswStage u j
      let t := kmswStage u (j + 1)
      change boundaryStart s s.UL = some v at hv
      have hULne := (kmswStage_UL_nonempty_active_last u j).1
      have hstart : boundaryStart t s.UL = some v := by
        rw [steps_start_stable s t s.UL]
        · exact hv
        · intro e he
          exact (kmswStage_endpoints_stable u (Nat.le_succ j)
            (stageRotation_UL_bound u j e he)).1
      have hbound := kmswStage_endpoints_lt_nextVertex u j s.active
        (act_lt_nextEdge u (le_refl j))
      have old (x : ℕ) (hx : x < s.nextVertex) :
          Relation.ReflTransGen (steps_geoStep t) v x := steps_geo_stable u j (hr x hx)
      by_cases h0 : u j = 0
      · cases hUL : s.UL.dropLast.reverse with
        | nil =>
            have facts := kmswStage_step_leftFresh_facts u j h0 hUL
            have hE : t.nextEdge = s.nextEdge + 2 := facts.1
            have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
            have hsingle : s.UL = [s.active] := by
              obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
              change s.UL = xs ++ [s.active] at hxs
              have hdrop : s.UL.dropLast = [] := List.reverse_eq_nil_iff.mp hUL
              have hx : xs = [] := by
                have hd := congrArg List.dropLast hxs
                simpa only [List.dropLast_append_cons, List.dropLast_singleton,
                  List.append_nil, hdrop] using hd.symm
              simpa only [hx, List.nil_append] using hxs
            have hv' : s.west s.active = v := by
              change boundaryStart s s.UL = some v at hv
              rw [hsingle] at hv
              exact Option.some.inj hv
            refine ⟨s.nextVertex, ?_, ?_⟩
            · change boundaryStart t t.UL = _
              rw [facts.2.2.2.2.2.2.2.2.2.1]
              change some (t.west s.nextEdge) = _
              rw [facts.2.2.1]
            · intro x hx
              have hn : t.nextVertex = s.nextVertex + 1 := facts.2.1
              have hedge : steps_geoStep t s.nextVertex v :=
                ⟨s.nextEdge + 1, by omega,
                  facts.2.2.2.2.1, facts.2.2.2.2.2.1.trans hv'⟩
              by_cases hold : x < s.nextVertex
              · exact (Relation.ReflTransGen.single hedge).trans (old x hold)
              · have heq : x = s.nextVertex := by change x < t.nextVertex at hx; omega
                subst x
                exact .refl
        | cons e es =>
            have facts := kmswStage_step_leftExisting_facts u j e es h0 hUL
            have hV : t.nextVertex = s.nextVertex := facts.2.1
            have hdrop : s.UL.dropLast = es.reverse ++ [e] := by
              have hh := congrArg List.reverse hUL
              simpa only [List.reverse_reverse, List.reverse_cons] using hh
            have hfull : s.UL = es.reverse ++ [e, s.active] := by
              obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
              change s.UL = xs ++ [s.active] at hxs
              have hxsD : xs = s.UL.dropLast := by rw [hxs]; simp
              rw [hxs, hxsD, hdrop]
              simp only [List.append_assoc, List.singleton_append]
            refine ⟨v, ?_, ?_⟩
            · change boundaryStart t t.UL = some v
              rw [facts.2.2.2.2.2.2.1]
              cases hs : es.reverse with
              | nil =>
                  have hv' : s.west e = v := by
                    rw [hfull, hs] at hv
                    exact Option.some.inj hv
                  change some (t.west s.nextEdge) = _
                  rw [facts.2.2.1, hv']
              | cons f fs =>
                  have hm : f ∈ s.UL := by rw [hfull, hs]; exact List.mem_cons_self
                  have hb := stageRotation_UL_bound u j f hm
                  change some (t.west f) = _
                  rw [(kmswStage_endpoints_stable u (Nat.le_succ j) hb).1]
                  simpa only [hfull, hs, boundaryStart, List.cons_append,
                    List.head?_cons, Option.map_some] using hv
            · intro x hx
              exact old x (by change x < t.nextVertex at hx; omega)
      · by_cases h1 : u j = 1
        · have facts := kmswStage_step_up_facts u j h1
          have hE : t.nextEdge = s.nextEdge + 2 := facts.1
          have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
          refine ⟨v, ?_, ?_⟩
          · change boundaryStart t t.UL = some v
            rw [facts.2.2.2.2.2.2.2.2.2.1]
            obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
            change s.UL = xs ++ [s.active] at hxs
            have hdrop : s.UL.dropLast = xs := by rw [hxs]; simp
            rw [hdrop]
            cases xs with
            | nil =>
                have hv' : s.west s.active = v := by
                  rw [hxs] at hv
                  exact Option.some.inj hv
                change some (t.west s.nextEdge) = _
                rw [facts.2.2.1, hv']
            | cons e es =>
                have hm : e ∈ s.UL := by rw [hxs]; exact List.mem_cons_self
                have he := stageRotation_UL_bound u j e hm
                change some (t.west e) = _
                rw [(kmswStage_endpoints_stable u (Nat.le_succ j) he).1]
                simpa only [hxs, boundaryStart, List.cons_append, List.head?_cons,
                  Option.map_some] using hv
          · intro x hx
            by_cases hold : x < s.nextVertex
            · exact old x hold
            · have heq : x = s.nextVertex := by
                change x < t.nextVertex at hx
                omega
              subst x
              exact (old _ hbound.1).tail
                ⟨s.nextEdge, by omega, facts.2.2.1, facts.2.2.2.1⟩
        · have h2 : u j = 2 := by
            have hn0 : (u j).val ≠ 0 := fun h => h0 (Fin.ext h)
            have hn1 : (u j).val ≠ 1 := fun h => h1 (Fin.ext h)
            have hb := (u j).isLt
            apply Fin.ext
            change (u j).val = 2
            omega
          cases hUR : s.UR with
          | cons e es =>
              have facts := kmswStage_step_activation_facts u j e es h2 hUR
              have hV : t.nextVertex = s.nextVertex := facts.2.1
              refine ⟨v, ?_, ?_⟩
              · change boundaryStart t t.UL = some v
                rw [facts.2.2.2.2.2.2.2.1]
                unfold boundaryStart
                rw [List.head?_append_of_ne_nil _ hULne]
                exact hstart
              · intro x hx
                exact old x (by change x < t.nextVertex at hx; omega)
          | nil =>
              have facts := kmswStage_step_pendant_facts u j h2 hUR
              have hE : t.nextEdge = s.nextEdge + 1 := facts.1
              have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
              refine ⟨v, ?_, ?_⟩
              · change boundaryStart t t.UL = some v
                rw [facts.2.2.2.2.2.2.1]
                unfold boundaryStart
                rw [List.head?_append_of_ne_nil _ hULne]
                exact hstart
              · intro x hx
                by_cases hold : x < s.nextVertex
                · exact old x hold
                · have heq : x = s.nextVertex := by
                    change x < t.nextVertex at hx
                    omega
                  subst x
                  exact (old _ hbound.2).tail
                    ⟨s.nextEdge, by omega, facts.2.2.1, facts.2.2.2.1⟩

private theorem steps_geo_image_reach
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P) {x y : ℕ}
    (h : Relation.ReflTransGen (steps_geoStep (kmswStage (codeExtend c) j)) x y) :
    ∀ d e : StageDart (kmswStage (codeExtend c) j).nextEdge,
      stageEndpoint (kmswStage (codeExtend c) j) d = x →
      stageEndpoint (kmswStage (codeExtend c) j) e = y →
      Relation.ReflTransGen B.map.directedStep
        (dartTailVertex B.map (P.emb.dartMap d))
        (dartTailVertex B.map (P.emb.dartMap e)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro d e hd he
      rw [steps_image_endpoint B c j hj P d e (hd.trans he.symm)]
  | @head x y hs _ ih =>
      intro d e hd he
      obtain ⟨f, hf, hw, ht⟩ := hs
      let p : StageDart (kmswStage (codeExtend c) j).nextEdge := (⟨f, hf⟩, false)
      let q : StageDart (kmswStage (codeExtend c) j).nextEdge := (⟨f, hf⟩, true)
      have hdp := steps_image_endpoint B c j hj P d p (hd.trans hw.symm)
      have hqe := ih q e ht he
      have hflip := P.emb.flip_comm p
      change P.emb.dartMap q = B.map.toCombinatorialMap.edgeInv (P.emb.dartMap p) at hflip
      rw [hflip] at hqe
      rw [hdp]
      exact Relation.ReflTransGen.head
        ⟨P.emb.dartMap p, B.noMissingDarts _, I.geometric_forward f hf, rfl, rfl⟩ hqe

private theorem steps_climb_empty_no_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = []) :
    ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      dartTailVertex B.map (P.emb.dartMap d) ≠
        dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
  let s := kmswStage (codeExtend c) j
  let a := (kmswRootedStage (codeExtend c) j).root
  have hsingle : s.UL = [s.active] := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last (codeExtend c) j
    change s.UL = xs ++ [s.active] at hxs
    have hdrop : s.UL.dropLast = [] := List.reverse_eq_nil_iff.mp hUL
    have hx : xs = [] := by
      have hd := congrArg List.dropLast hxs
      simpa only [List.dropLast_append_cons, List.dropLast_singleton,
        List.append_nil, hdrop] using hd.symm
    simpa only [hx, List.nil_append] using hxs
  obtain ⟨v, hv, hr⟩ := steps_geo_source (codeExtend c) j
  change boundaryStart s s.UL = some v at hv
  rw [hsingle] at hv
  have hav : stageEndpoint s a = v := Option.some.inj hv
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, _, _, _, hparent, hsel, _, _, _⟩ := hc
  let q := B.map.toCombinatorialMap.edgeInv
    (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩))
  have hq : B.map.tail q := by
    have hh := (canonicalULSelector B _ hs).property.2.1
    rw [canonicalULSelector_val, ← hsel] at hh
    exact hh
  have hqtail : dartTailVertex B.map q =
      dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
    rw [hparent]
    simp only [ulParent, hs, ↓reduceDIte, canonicalULSelector_val, ← hsel]
    rfl
  have hqhead : dartHeadVertex B.map q =
      dartTailVertex B.map (peanoEdge B ⟨j, hj⟩) := by
    change dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩)))) = _
    rw [B.map.toCombinatorialMap.edgeInv_invol]
    exact steps_rot_vertex B _ 1
  intro d hd
  have hreach := steps_geo_image_reach B c j hj P I
    (hr (stageEndpoint s d) (stageEndpoint_lt_nextVertex (codeExtend c) j d)) a d hav rfl
  rw [P.emb.root_comm, hd] at hreach
  have hstep : B.map.directedStep
      (dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩))
      (dartTailVertex B.map (peanoEdge B ⟨j, hj⟩)) :=
    ⟨q, B.noMissingDarts q, hq, hqtail, hqhead⟩
  exact B.acyclic _ (Relation.TransGen.head' hstep hreach)

private theorem steps_index_edge_in_image
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P) (q : D) (hq : B.map.tail q)
    (hidx : (peanoIndex B q).val ≤ j) : q ∈ Set.range P.emb.dartMap := by
  obtain ⟨d, hd⟩ := P.edges_cover_prefix _ hidx
  let f : StageDart (kmswStage (codeExtend c) j).nextEdge := (d.1, false)
  have hif : peanoIndex B (P.emb.dartMap f) = peanoIndex B q := by
    apply Fin.ext
    cases hb : d.2 with
    | false =>
        have he : d = f := Prod.ext rfl hb
        simpa only [he] using hd
    | true =>
        have hh := P.emb.flip_comm f
        change P.emb.dartMap (edgeFlip _ f) =
          B.map.toCombinatorialMap.edgeInv (P.emb.dartMap f) at hh
        have he : d = edgeFlip _ f := Prod.ext rfl hb
        rw [he, hh, peanoIndex_edgeInv] at hd
        exact hd
  have hf := steps_forward_eq_of_index B _ (I.geometric_forward d.1.val d.1.isLt) _ hif
  have hq' := steps_forward_eq_of_index B q hq _ rfl
  exact ⟨f, hf.trans hq'.symm⟩

/-- All climb frontier clauses follow from the prefix invariant. The three
predicates from the climb module are expanded inline, including the exact
present-tail definition of vertex membership. -/
theorem kmswPeanoPrefixInv_climbFrontier
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    let s := kmswStage (codeExtend c) j
    let a := peanoEdge B ⟨j, by omega⟩
    let b := peanoEdge B ⟨j + 1, hj1⟩
    (∀ e es, s.UL.dropLast.reverse = e :: es →
      ∃ he : e < s.nextEdge, s.present e = true ∧
        P.emb.dartMap ((⟨e, he⟩, false) : StageDart s.nextEdge) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) ∧
    (s.UL.dropLast.reverse = [] →
      ¬ (∃ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
        (kmswRootedStage (codeExtend c) j).map.tail d ∧
          B.map.tail (P.emb.dartMap d) ∧
          dartTailVertex B.map (P.emb.dartMap d) = dartTailVertex B.map b)) ∧
    (s.UL.dropLast.reverse = [] →
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) ∉
          Set.range P.emb.dartMap ∧
        j + 1 < (peanoIndex B
          (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a))).val) := by
  dsimp only
  refine ⟨kmswPeanoPrefixInv_climbFrontier_nonempty B c j hj P I hj1 hkind, ?_, ?_⟩
  · intro hUL
    rintro ⟨d, _, _, hd⟩
    exact steps_climb_empty_no_vertex B c j hj P I hj1 hkind hUL d hd
  · intro hUL
    let a := peanoEdge B ⟨j, hj⟩
    let q := B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)
    have hc := peanoStepKind_config B j hj1
    rw [hkind] at hc
    obtain ⟨hs, _, _, hhead, hparent, hsel, _, _, _⟩ := hc
    have hq : B.map.tail q := by
      have hh := (canonicalULSelector B _ hs).property.2.1
      rw [canonicalULSelector_val, ← hsel] at hh
      exact hh
    have hqtail : dartTailVertex B.map q =
        dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
      rw [hparent]
      simp only [ulParent, hs, ↓reduceDIte, canonicalULSelector_val, ← hsel]
      rfl
    have hnot : q ∉ Set.range P.emb.dartMap := by
      rintro ⟨d, hd⟩
      apply steps_climb_empty_no_vertex B c j hj P I hj1 hkind hUL d
      exact (congrArg (dartTailVertex B.map) hd).trans hqtail
    refine ⟨hnot, ?_⟩
    change j + 1 < (peanoIndex B q).val
    have hgt : j < (peanoIndex B q).val := by
      by_contra h
      exact hnot (steps_index_edge_in_image B c j hj P I q hq (by omega))
    have hne : (peanoIndex B q).val ≠ j + 1 := by
      intro hi
      have he := steps_forward_eq_of_index B q hq ⟨j + 1, hj1⟩ (Fin.ext hi)
      have hv : dartTailVertex B.map a = dartHeadVertex B.map a := by
        calc
          dartTailVertex B.map a = dartHeadVertex B.map q := by
            change dartTailVertex B.map a = dartTailVertex B.map
              (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.edgeInv
                (B.map.toCombinatorialMap.rot a)))
            rw [B.map.toCombinatorialMap.edgeInv_invol]
            exact (steps_rot_vertex B a 1).symm
          _ = dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := congrArg _ he
          _ = dartHeadVertex B.map a := hhead
      have hloop : B.map.directedStep (dartTailVertex B.map a) (dartTailVertex B.map a) :=
        ⟨a, B.noMissingDarts a, peanoEdge_forward B _, rfl, hv.symm⟩
      exact B.acyclic _ (Relation.TransGen.single hloop)
    omega

/- Remaining rotate obligation, isolated without adding a premise or a placeholder.
The exact Peano vertex-first-visit fact required by `vertices_prefix` is:

  (B : BipolarTriangulationWithBoundaryBase D ℓ r)
  (j : ℕ) (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
  (hkind : peanoStepKind B j hj1 = .rotate)
  ⊢ ∀ k : Fin B.map.toCombinatorialMap.numEdges, k.val ≤ j →
      dartTailVertex B.map (peanoEdge B k) ≠
        dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) ∧
      dartHeadVertex B.map (peanoEdge B k) ≠
        dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩)

The inspected `BipolarPeanoFirstVisit` results establish forward-before-reverse
and increasing edge contour positions. Neither is this vertex exclusion.
`BipolarPeanoContour` and `BipolarPeanoConfiguration` were also inspected;
no proof of the displayed vertex exclusion was located there. This file does
not assume it. In particular `kmswPeanoPrefixInv_rotateFresh` is not defined.
The climb and code results above do not discharge rotate freshness. -/

end DirectedDistances.KMSW
