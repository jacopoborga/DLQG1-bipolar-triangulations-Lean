module

public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariant
public import DirectedDistances.KMSW.KMSWPeanoPrefixClimb
public import DirectedDistances.KMSW.KMSWPeanoPrefixInduction
import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantSteps
import DirectedDistances.KMSW.KMSWPeanoPrefixClimbCorner
import DirectedDistances.KMSW.KMSWPeanoClimbFreshVacuous

/-! # Existing-predecessor climb invariant

not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- The geometric prefix invariant is preserved by a climb with an existing
upper-left predecessor, and the new embedding agrees with the old one on every
cast old dart. This is a helper toward thm-kmsw
paper result. -/
theorem kmswPeanoPrefixInv_climb_leftExisting
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb)
    (hcode : codeExtend c j = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es) :
    ∃ Q : KMSWPeanoPrefixEmbedding B c (j + 1) hj1,
      KMSWPeanoPrefixInv B c (j + 1) hj1 Q ∧
      ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
        Q.emb.dartMap
          (outerSucc_castDart
            (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ j)) d) =
          P.emb.dartMap d := by
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let a := peanoEdge B ⟨j, hj⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  have hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P :=
    kmswPeanoPrefixInv_climbFrontier B c j hj P I hj1 hkind
  have hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P :=
    kmswPeanoPrefixInv_climbNoNextFrontierCollision B c j hj P I hj1 hkind
  have hcorner : KMSWPeanoClimbCorner B c j hj P hj1
      ((⟨e, (stageRotation_UL_bound u j) e
        (List.mem_of_mem_dropLast (List.mem_reverse.mp (by
          rw [hUL]
          exact List.mem_cons_self)))⟩, false))
      ((⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)) :=
    kmswPeanoPrefixInv_climbCorner B c j hj P I hj1 hkind e es hUL
  let Q := kmswPeanoPrefixEmbedding_climb_leftExisting
    B c j hj P hj1 hcode hkind e es hUL hfrontier hno hcorner
  have facts := kmswStage_step_leftExisting_facts u j e es hcode hUL
  have hnext : t.nextEdge = s.nextEdge + 1 := facts.1
  have hULt : t.UL = es.reverse ++ [s.nextEdge] :=
    facts.2.2.2.2.2.2.1
  have hURt : t.UR = s.UR := facts.2.2.2.2.2.2.2.2.1
  have hLLt : t.LL = s.LL := facts.2.2.2.2.2.2.2.2.2
  have oldCast (d : StageDart s.nextEdge) :
      Q.emb.dartMap
        (outerSucc_castDart
          (kmswStage_nextEdge_mono u (m := j) (n := j + 1)
            (Nat.le_succ j)) d) = P.emb.dartMap d := by
    change (kmswPeanoPrefixEmbedding_climb_leftExisting
      B c j hj P hj1 hcode hkind e es hUL hfrontier hno hcorner).emb.dartMap _ = _
    rw [kmswPeanoPrefixEmbedding_climb_leftExisting_dartMap]
    exact kmswPeanoPrefixClimbLeftExistingDartMap_old B c j hj hj1 P d
  have oldAt (d : StageDart t.nextEdge) (hd : d.1.val < s.nextEdge) :
      Q.emb.dartMap d =
        P.emb.dartMap ((⟨d.1.val, hd⟩, d.2) : StageDart s.nextEdge) := by
    let d₀ : StageDart s.nextEdge := (⟨d.1.val, hd⟩, d.2)
    have hcast : outerSucc_castDart
        (kmswStage_nextEdge_mono u (m := j) (n := j + 1)
          (Nat.le_succ j)) d₀ = d := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    exact (congrArg Q.emb.dartMap hcast.symm).trans (oldCast d₀)
  have newAt (d : StageDart t.nextEdge) (hd : d.1.val = s.nextEdge) :
      Q.emb.dartMap d = if d.2 then B.map.toCombinatorialMap.edgeInv b else b := by
    change (kmswPeanoPrefixEmbedding_climb_leftExisting
      B c j hj P hj1 hcode hkind e es hUL hfrontier hno hcorner).emb.dartMap d = _
    rw [kmswPeanoPrefixEmbedding_climb_leftExisting_dartMap]
    exact kmswPeanoPrefixClimbLeftExistingDartMap_new B c j hj hj1 P d hd
  have hcfg := peanoStepKind_config B j hj1
  rw [hkind] at hcfg
  have hcfg' := Classical.choose_spec hcfg
  have hhead : dartHeadVertex B.map b = dartHeadVertex B.map a := hcfg'.2.2.1
  let A : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv a := by
    have hh := P.emb.flip_comm (kmswRootedStage u j).root
    change P.emb.dartMap A =
      B.map.toCombinatorialMap.edgeInv
        (P.emb.dartMap (kmswRootedStage u j).root) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv P.emb.root_comm)
  have hstepB : B.map.directedStep (dartTailVertex B.map b)
      (dartHeadVertex B.map b) :=
    ⟨b, B.noMissingDarts b, peanoEdge_forward B ⟨j + 1, hj1⟩, rfl, rfl⟩
  have htailA : dartHeadVertex B.map b = dartTailVertex B.map (P.emb.dartMap A) := by
    rw [hA, hhead]
    rfl
  refine ⟨Q, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      have hcase : f < s.nextEdge ∨ f = s.nextEdge := by
        have hbound : f < s.nextEdge + 1 := by rw [← hnext]; exact hf
        omega
      rcases hcase with hold | hnew
      · have h := oldAt ((⟨f, hf⟩, false) : StageDart t.nextEdge) hold
        rw [h]
        exact I.geometric_forward f hold
      · have h := newAt ((⟨f, hf⟩, false) : StageDart t.nextEdge) hnew
        rw [h]
        exact peanoEdge_forward B ⟨j + 1, hj1⟩
    · intro v
      constructor
      · rintro ⟨d, hd⟩
        have hcase : d.1.val < s.nextEdge ∨ d.1.val = s.nextEdge := by
          have hbound : d.1.val < s.nextEdge + 1 := by rw [← hnext]; exact d.1.isLt
          omega
        rcases hcase with hold | hnew
        · let d₀ : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
          have hmap := oldAt d hold
          obtain ⟨k, hk, hv⟩ := (I.vertices_prefix v).1
            ⟨d₀, (congrArg (dartTailVertex B.map) hmap).symm.trans hd⟩
          exact ⟨k, by omega, hv⟩
        · refine ⟨⟨j + 1, hj1⟩, Nat.le_refl _, ?_⟩
          have hmap := newAt d hnew
          cases hs : d.2
          · rw [hmap, hs] at hd
            exact Or.inl hd
          · rw [hmap, hs] at hd
            exact Or.inr hd
      · rintro ⟨k, hk, hv | hv⟩
        · by_cases hkj : k.val ≤ j
          · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, Or.inl hv⟩
            exact ⟨outerSucc_castDart
              (kmswStage_nextEdge_mono u (m := j) (n := j + 1)
                (Nat.le_succ j)) d,
              (congrArg (dartTailVertex B.map) (oldCast d)).trans hd⟩
          · have hkval : k.val = j + 1 := by omega
            have hk' : k = ⟨j + 1, hj1⟩ := Fin.ext hkval
            subst k
            let d : StageDart t.nextEdge :=
              ((⟨s.nextEdge, by rw [hnext]; omega⟩), false)
            refine ⟨d, ?_⟩
            have hmap := newAt d (by rfl)
            change dartTailVertex B.map (Q.emb.dartMap d) = v
            rw [hmap]
            have hd : d.2 = false := rfl
            rw [hd]
            exact hv
        · by_cases hkj : k.val ≤ j
          · obtain ⟨d, hd⟩ := (I.vertices_prefix v).2 ⟨k, hkj, Or.inr hv⟩
            exact ⟨outerSucc_castDart
              (kmswStage_nextEdge_mono u (m := j) (n := j + 1)
                (Nat.le_succ j)) d,
              (congrArg (dartTailVertex B.map) (oldCast d)).trans hd⟩
          · have hkval : k.val = j + 1 := by omega
            have hk' : k = ⟨j + 1, hj1⟩ := Fin.ext hkval
            subst k
            let d : StageDart t.nextEdge :=
              ((⟨s.nextEdge, by rw [hnext]; omega⟩), true)
            refine ⟨d, ?_⟩
            have hmap := newAt d (by rfl)
            change dartTailVertex B.map (Q.emb.dartMap d) = v
            rw [hmap]
            have hd : d.2 = true := rfl
            rw [hd]
            exact hv
    · intro f fs hUR he ht
      have hURold : s.UR = f :: fs := by rw [← hURt]; exact hUR
      have hfOld : f < s.nextEdge :=
        ((kmswStageFrontierChain_all u j).UR_missing_bounded f
          (by rw [hURold]; exact List.mem_cons_self)).2
      have hmap := oldAt ((⟨f, he⟩, false) : StageDart t.nextEdge) (by omega)
      have hhtB : dartHeadVertex B.map b ≠ B.sink := by simpa only [b] using ht
      have hht : dartHeadVertex B.map a ≠ B.sink := by
        rw [← hhead]
        exact hhtB
      have hq := I.UR_head f fs hURold hfOld hht
      have hmap' : Q.emb.dartMap (⟨f, he⟩, false) =
          P.emb.dartMap (⟨f, hfOld⟩, false) := by simpa using hmap
      have hq' : P.emb.dartMap (⟨f, hfOld⟩, false) =
          rightmostOutgoing B (dartHeadVertex B.map b) ht := by
        have hsel : (⟨dartHeadVertex B.map a, hht⟩ :
            {v : MapVertex B.map // v ≠ B.sink}) =
            ⟨dartHeadVertex B.map b, ht⟩ := by
          apply Subtype.ext
          exact hhead.symm
        have hro := congrArg
          (fun v : {v : MapVertex B.map // v ≠ B.sink} =>
            rightmostOutgoing B v.1 v.2) hsel
        exact hq.trans hro
      exact hmap'.trans hq'
    · change List.IsChain _ t.UR
      rw [hURt]
      cases hURs : s.UR with
      | nil =>
          exact List.IsChain.nil
      | cons f fs =>
          cases hfs : fs with
          | nil =>
              exact List.IsChain.singleton _
          | cons g gs =>
              rw [List.isChain_cons_cons]
              constructor
              · intro hfT hgT ht
                have hfMem : f ∈ s.UR := by rw [hURs]; simp
                have hgMem : g ∈ s.UR := by rw [hURs, hfs]; simp
                have hfOld : f < s.nextEdge :=
                  ((kmswStageFrontierChain_all u j).UR_missing_bounded f hfMem).2
                have hgOld : g < s.nextEdge :=
                  ((kmswStageFrontierChain_all u j).UR_missing_bounded g hgMem).2
                have hmapf := oldAt ((⟨f, hfT⟩, false) : StageDart t.nextEdge) hfOld
                have hmapg := oldAt ((⟨g, hgT⟩, false) : StageDart t.nextEdge) hgOld
                have hmapf' : Q.emb.dartMap (⟨f, hfT⟩, false) =
                    P.emb.dartMap (⟨f, hfOld⟩, false) := by simpa using hmapf
                have hmapg' : Q.emb.dartMap (⟨g, hgT⟩, false) =
                    P.emb.dartMap (⟨g, hgOld⟩, false) := by simpa using hmapg
                have htOld : dartHeadVertex B.map
                    (P.emb.dartMap (⟨f, hfOld⟩, false)) ≠ B.sink := by
                  simpa only [hmapf'] using ht
                have hchain := I.UR_chain
                rw [hURs, hfs, List.isChain_cons_cons] at hchain
                calc
                  Q.emb.dartMap (⟨g, hgT⟩, false) =
                      P.emb.dartMap (⟨g, hgOld⟩, false) := hmapg'
                  _ = rightmostOutgoing B
                      (dartHeadVertex B.map (P.emb.dartMap (⟨f, hfOld⟩, false))) htOld :=
                        hchain.1 hfOld hgOld htOld
                  _ = rightmostOutgoing B
                      (dartHeadVertex B.map (Q.emb.dartMap (⟨f, hfT⟩, false))) ht := by
                        simp only [← hmapf']
              · let oldRel : ℕ → ℕ → Prop := fun x y =>
                    ∀ (hx : x < s.nextEdge) (hy : y < s.nextEdge)
                      (ht : dartHeadVertex B.map
                        (P.emb.dartMap (⟨x, hx⟩, false)) ≠ B.sink),
                      P.emb.dartMap (⟨y, hy⟩, false) =
                        rightmostOutgoing B
                          (dartHeadVertex B.map (P.emb.dartMap (⟨x, hx⟩, false))) ht
                let newRel : ℕ → ℕ → Prop := fun x y =>
                    ∀ (hx : x < t.nextEdge) (hy : y < t.nextEdge)
                      (ht : dartHeadVertex B.map
                        (Q.emb.dartMap (⟨x, hx⟩, false)) ≠ B.sink),
                      Q.emb.dartMap (⟨y, hy⟩, false) =
                        rightmostOutgoing B
                          (dartHeadVertex B.map (Q.emb.dartMap (⟨x, hx⟩, false))) ht
                have transport : ∀ l, (∀ x ∈ l, x < s.nextEdge) →
                    List.IsChain oldRel l → List.IsChain newRel l := by
                  intro l
                  induction l with
                  | nil =>
                      intro _ _
                      exact List.IsChain.nil
                  | cons x xs ih =>
                      intro hbound hchain
                      cases xs with
                      | nil => exact List.IsChain.singleton _
                      | cons y ys =>
                        rw [List.isChain_cons_cons] at hchain ⊢
                        constructor
                        · dsimp [newRel]
                          intro hxT hyT ht
                          have hxOld := hbound x (by simp)
                          have hyOld := hbound y (by simp)
                          have hxMap := oldAt ((⟨x, hxT⟩, false) : StageDart t.nextEdge) hxOld
                          have hyMap := oldAt ((⟨y, hyT⟩, false) : StageDart t.nextEdge) hyOld
                          have hxMap' : Q.emb.dartMap (⟨x, hxT⟩, false) =
                              P.emb.dartMap (⟨x, hxOld⟩, false) := by simpa using hxMap
                          have hyMap' : Q.emb.dartMap (⟨y, hyT⟩, false) =
                              P.emb.dartMap (⟨y, hyOld⟩, false) := by simpa using hyMap
                          have htOld : dartHeadVertex B.map
                              (P.emb.dartMap (⟨x, hxOld⟩, false)) ≠ B.sink := by
                            simpa only [hxMap'] using ht
                          have hsel :
                              (⟨dartHeadVertex B.map
                                (P.emb.dartMap (⟨x, hxOld⟩, false)), htOld⟩ :
                                {v : MapVertex B.map // v ≠ B.sink}) =
                              ⟨dartHeadVertex B.map
                                (Q.emb.dartMap (⟨x, hxT⟩, false)), ht⟩ := by
                            apply Subtype.ext
                            exact (congrArg (dartHeadVertex B.map) hxMap').symm
                          have hro := congrArg
                            (fun v : {v : MapVertex B.map // v ≠ B.sink} =>
                              rightmostOutgoing B v.1 v.2) hsel
                          exact hyMap'.trans ((hchain.1 hxOld hyOld htOld).trans hro)
                        · apply ih
                          · intro z hz
                            exact hbound z (by simp [hz])
                          · exact hchain.2
                have htailOld : List.IsChain oldRel (s.UR.tail) := by
                  exact I.UR_chain.tail
                rw [hURs, hfs] at htailOld
                have htailBound : ∀ x ∈ g :: gs, x < s.nextEdge := by
                  intro x hx
                  have hxUR : x ∈ s.UR := by
                    rw [hURs, hfs]
                    exact List.mem_cons_of_mem f hx
                  exact ((kmswStageFrontierChain_all u j).UR_missing_bounded x hxUR).2
                have htailNew := transport (g :: gs) htailBound htailOld
                simpa only [newRel] using htailNew
    · intro hnil d
      change t.UR = [] at hnil
      rw [hURt] at hnil
      have hnilOld : s.UR = [] := hnil
      by_cases hold : d.1.val < s.nextEdge
      · have hmap := oldAt d hold
        rw [hmap]
        have hreach := I.top_reachable_empty hnilOld
          ((⟨d.1.val, hold⟩, d.2) : StageDart s.nextEdge)
        change Relation.ReflTransGen B.map.directedStep
          (dartTailVertex B.map (P.emb.dartMap ((⟨d.1.val, hold⟩, d.2))) )
          (dartHeadVertex B.map a) at hreach
        change Relation.ReflTransGen B.map.directedStep
          (dartTailVertex B.map (P.emb.dartMap ((⟨d.1.val, hold⟩, d.2))) )
          (dartHeadVertex B.map b)
        rw [hhead]
        exact hreach
      · have hnew : d.1.val = s.nextEdge := by
          have hdlt : d.1.val < s.nextEdge + 1 := by rw [← hnext]; exact d.1.isLt
          omega
        rw [newAt d hnew]
        cases hs : d.2
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Relation.ReflTransGen.single hstepB
        · simp only [↓reduceIte]
          exact Relation.ReflTransGen.refl
    · intro f hlast he d
      change t.UR.getLast? = some f at hlast
      rw [hURt] at hlast
      have hlastOld : s.UR.getLast? = some f := hlast
      have hmem : f ∈ s.UR :=
        List.mem_of_mem_getLast? (by simp only [hlastOld, Option.mem_def];)
      have hfOld : f < s.nextEdge :=
        ((kmswStageFrontierChain_all u j).UR_missing_bounded f
          hmem).2
      have hmapTop := oldAt ((⟨f, he⟩, false) : StageDart t.nextEdge) (by omega)
      have hreachOld (d₀ : StageDart s.nextEdge) :=
        I.top_reachable_nonempty f hlastOld hfOld d₀
      by_cases hold : d.1.val < s.nextEdge
      · have hmap := oldAt d hold
        rw [hmap, hmapTop]
        exact hreachOld ((⟨d.1.val, hold⟩, d.2))
      · have hnew : d.1.val = s.nextEdge := by
          have hdlt : d.1.val < s.nextEdge + 1 := by rw [← hnext]; exact d.1.isLt
          omega
        rw [newAt d hnew, hmapTop]
        cases hs : d.2
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hfirst : Relation.ReflTransGen B.map.directedStep
              (dartTailVertex B.map b)
              (dartTailVertex B.map (P.emb.dartMap A)) := by
            simpa only [htailA] using Relation.ReflTransGen.single hstepB
          exact hfirst.trans (hreachOld A)
        · simp only [↓reduceIte]
          have hreach := hreachOld A
          have htailInv : dartTailVertex B.map
              (B.map.toCombinatorialMap.edgeInv b) = dartHeadVertex B.map b := rfl
          rw [htailInv, htailA]
          exact hreach
    · intro f hf he
      have hfEs : f ∈ es.reverse := by
        change f ∈ t.UL.dropLast at hf
        rw [hULt, List.dropLast_concat] at hf
        exact hf
      have hOldUL : s.UL.dropLast = es.reverse ++ [e] := by
        calc
          s.UL.dropLast = s.UL.dropLast.reverse.reverse := by simp
          _ = (e :: es).reverse := congrArg List.reverse hUL
          _ = es.reverse ++ [e] := by simp
      have hfOld : f ∈ s.UL.dropLast := by
        rw [hOldUL]
        simp only [List.mem_append]
        exact Or.inl hfEs
      have hfUL : f ∈ s.UL := List.mem_of_mem_dropLast hfOld
      have hfLt : f < s.nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge u j).2 f (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inl hfUL)))
      rw [oldAt ((⟨f, he⟩, true) : StageDart t.nextEdge) hfLt,
        oldAt ((⟨f, he⟩, false) : StageDart t.nextEdge) hfLt]
      exact I.UL_parent f hfOld hfLt
    · intro f hf he
      change f ∈ t.LL at hf
      rw [hLLt] at hf
      have hfOld : f ∈ s.LL := hf
      have hfLt : f < s.nextEdge :=
        ((kmswStageFrontierChain_all u j).LL_missing_bounded f hfOld).2
      rw [oldAt ((⟨f, he⟩, true) : StageDart t.nextEdge) hfLt,
        oldAt ((⟨f, he⟩, false) : StageDart t.nextEdge) hfLt]
      exact I.LL_parent f hfOld hfLt
  · intro d
    simpa only [u] using oldCast d

/-- Every climb step preserves the geometric prefix invariant. The fresh-left
branch is vacuous along a geometric prefix; the existing-predecessor branch is -/
theorem kmswPeanoClimbPreserves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) : KMSWPeanoClimbPreserves B c := by
  intro j hj P I hj1 hkind hcode
  have hULne : (kmswStage (codeExtend c) j).UL.dropLast.reverse ≠ [] :=
    kmswPeanoPrefixInv_climb_UL_ne_nil B c j hj P I hj1 hkind
  cases hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse with
  | nil => exact (hULne hUL).elim
  | cons e es =>
      obtain ⟨Q, hInv, _hOldCompatibility⟩ :=
        kmswPeanoPrefixInv_climb_leftExisting
          B c j hj P I hj1 hkind hcode e es hUL
      exact ⟨Q, hInv⟩

end DirectedDistances.KMSW
