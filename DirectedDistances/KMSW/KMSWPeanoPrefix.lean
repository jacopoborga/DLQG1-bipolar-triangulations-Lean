/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatInducedEmbedding
public import DirectedDistances.PlanarMap.BipolarPeanoContour
public import DirectedDistances.KMSW.FiniteWalkClass

/-! # Peano prefix reconstruction helper

Helper toward thm-kmsw surjectivity by procedure reading
not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- View a bipolar map as rooted at a dart. Helper toward thm-kmsw -/
@[expose] def baseRootedAt (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (d : D) (hd : B.map.tail d) : RootedDirectedMapWithMissing D := by
  exact ⟨B.map, d, B.noMissingDarts d, hd⟩

/-- The oriented representative of the geometric edge containing a dart.
Helper toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
@[expose] noncomputable def peanoForwardDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) : D := by
  classical
  exact if B.map.tail d then d else B.map.toCombinatorialMap.edgeInv d

/-- The chosen representative is the forward dart of its edge. Helper toward
thm-kmsw surjectivity by procedure reading
is not the paper result. -/
theorem peanoForwardDart_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    B.map.tail (peanoForwardDart B d) := by
  by_cases hd : B.map.tail d
  · simp [peanoForwardDart, hd]
  · have hi : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      by_contra hnot
      exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 hnot)
    simp [peanoForwardDart, hd, hi]

private theorem peanoForwardDart_edgeInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    peanoForwardDart B (B.map.toCombinatorialMap.edgeInv d) =
      peanoForwardDart B d := by
  by_cases hd : B.map.tail d
  · have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) :=
      (B.map.tail_iff d (B.noMissingDarts d)).1 hd
    simp [peanoForwardDart, hd, hnot,
      B.map.toCombinatorialMap.edgeInv_invol]
  · have hi : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      by_contra hnot
      exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 hnot)
    simp [peanoForwardDart, hd, hi]

/-- The zero-based first-visit index of the forward dart on the geometric
edge containing `d`. Helper toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
@[expose] noncomputable def peanoIndex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    Fin B.map.toCombinatorialMap.numEdges := by
  classical
  let e := peanoForwardDart B d
  refine Fin.cast (firstVisitOrder_length B) ⟨(firstVisitOrder B).idxOf e, ?_⟩
  exact List.idxOf_lt_length_iff.2
    ((mem_firstVisitOrder_iff B e).2 (peanoForwardDart_tail B d))

/-- The index recovers each enumerated Peano edge. Helper toward thm-kmsw -/
theorem peanoIndex_peanoEdge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    peanoIndex B (peanoEdge B j) = j := by
  classical
  apply Fin.ext
  have htail := peanoEdge_forward B j
  change (firstVisitOrder B).idxOf
      (peanoForwardDart B (peanoEdge B j)) = j.val
  simp only [peanoForwardDart, htail]
  have hidx := List.get_idxOf (firstVisitOrder_nodup B)
    (⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩ :
      Fin (firstVisitOrder B).length)
  change (firstVisitOrder B).idxOf
      ((firstVisitOrder B).get ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩) = j.val
  exact hidx

/-- Reversing a dart does not change its geometric Peano edge index. Helper
toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
theorem peanoIndex_edgeInv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    peanoIndex B (B.map.toCombinatorialMap.edgeInv d) = peanoIndex B d := by
  apply Fin.ext
  change (firstVisitOrder B).idxOf
      (peanoForwardDart B (B.map.toCombinatorialMap.edgeInv d)) =
    (firstVisitOrder B).idxOf (peanoForwardDart B d)
  rw [peanoForwardDart_edgeInv]

/-- An induced embedding of the generated stage into the bipolar map that
identifies exactly the present prefix edges, covers the full prefix, and
identifies the missing UR/LL frontier with image edges beyond that prefix. Helper
toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
structure KMSWPeanoPrefixEmbedding
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges) where
  emb : RootedInducedEmbedding
    (kmswRootedStage (codeExtend c) j)
    (baseRootedAt B (peanoEdge B ⟨j, hj⟩)
      (peanoEdge_forward B ⟨j, hj⟩))
  present_prefix : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    (kmswStage (codeExtend c) j).present d.1.val = true ↔
      (peanoIndex B (emb.dartMap d)).val ≤ j
  edges_cover_prefix : ∀ k : ℕ, k ≤ j →
    ∃ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      (peanoIndex B (emb.dartMap d)).val = k
  missing_iff_frontier : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    (kmswStage (codeExtend c) j).present d.1.val = false ↔
      d.1.val ∈ (kmswStage (codeExtend c) j).UR ∨
        d.1.val ∈ (kmswStage (codeExtend c) j).LL
  missing_is_future : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    (kmswStage (codeExtend c) j).present d.1.val = false →
      j < (peanoIndex B (emb.dartMap d)).val

/-- The UR/LL frontier darts are exactly those whose embedded edges lie after
the Peano prefix. Helper toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
theorem kmswPeanoPrefixEmbedding_frontier_iff_future
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    (d.1.val ∈ (kmswStage (codeExtend c) j).UR ∨
      d.1.val ∈ (kmswStage (codeExtend c) j).LL) ↔
        j < (peanoIndex B (P.emb.dartMap d)).val := by
  rw [← P.missing_iff_frontier d]
  constructor
  · intro hmiss
    by_contra hnot
    have hle : (peanoIndex B (P.emb.dartMap d)).val ≤ j := by omega
    have hp := (P.present_prefix d).2 hle
    rw [hmiss] at hp
    contradiction
  · intro hfuture
    by_contra hnot
    have hp : (kmswStage (codeExtend c) j).present d.1.val = true :=
      Bool.eq_true_of_not_eq_false hnot
    have hle := (P.present_prefix d).1 hp
    omega

private theorem peanoForwardDart_eq_of_index_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d e : D}
    (h : peanoIndex B d = peanoIndex B e) :
    peanoForwardDart B d = peanoForwardDart B e := by
  classical
  have hidx := congrArg Fin.val h
  change (firstVisitOrder B).idxOf (peanoForwardDart B d) =
    (firstVisitOrder B).idxOf (peanoForwardDart B e) at hidx
  exact (List.idxOf_inj
    ((mem_firstVisitOrder_iff B _).2 (peanoForwardDart_tail B d))).1 hidx

private theorem eq_or_edgeInv_of_peanoIndex_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d e : D}
    (h : peanoIndex B d = peanoIndex B e) :
    d = e ∨ d = B.map.toCombinatorialMap.edgeInv e := by
  have hfwd := peanoForwardDart_eq_of_index_eq B h
  by_cases hd : B.map.tail d <;> by_cases he : B.map.tail e
  · have hde : d = e := by
      simpa [peanoForwardDart, hd, he] using hfwd
    exact Or.inl hde
  · have hde : d = B.map.toCombinatorialMap.edgeInv e := by
      simpa [peanoForwardDart, hd, he] using hfwd
    exact Or.inr hde
  · have hde : B.map.toCombinatorialMap.edgeInv d = e := by
      simpa [peanoForwardDart, hd, he] using hfwd
    exact Or.inr (by
      have := congrArg B.map.toCombinatorialMap.edgeInv hde
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using this)
  · have hde : B.map.toCombinatorialMap.edgeInv d =
      B.map.toCombinatorialMap.edgeInv e := by
      simpa [peanoForwardDart, hd, he] using hfwd
    exact Or.inl (B.map.toCombinatorialMap.edgeInv.injective hde)

/-- At the last prefix, every dart of the bipolar map is in the induced
embedding's image. This is a helper toward thm-kmsw surjectivity by procedure
and this is not the paper result. -/
theorem kmswPeanoPrefixEmbedding_dartMap_surjective
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hfinal : j + 1 = B.map.toCombinatorialMap.numEdges) :
    Function.Surjective P.emb.dartMap := by
  intro e
  let k := peanoIndex B e
  have hk : k.val ≤ j := by
    dsimp [k]
    have he := (peanoIndex B e).isLt
    omega
  obtain ⟨d, hd⟩ := P.edges_cover_prefix k.val hk
  have hidx : peanoIndex B (P.emb.dartMap d) = k := by
    apply Fin.ext
    exact hd
  rcases eq_or_edgeInv_of_peanoIndex_eq B hidx with heq | heq
  · exact ⟨d, heq⟩
  · refine ⟨edgeFlip _ d, ?_⟩
    calc
      P.emb.dartMap (edgeFlip _ d) =
          B.map.toCombinatorialMap.edgeInv (P.emb.dartMap d) := P.emb.flip_comm d
      _ = e := by
        simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
          congrArg B.map.toCombinatorialMap.edgeInv heq

/-- With the full prefix present, the last-prefix dart map is bijective.
Helper toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
theorem kmswPeanoPrefixEmbedding_dartMap_bijective
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hfinal : j + 1 = B.map.toCombinatorialMap.numEdges) :
    Function.Bijective P.emb.dartMap := by
  exact ⟨P.emb.injective,
    kmswPeanoPrefixEmbedding_dartMap_surjective B c j hj P hfinal⟩

/-- The dart equivalence obtained from a complete Peano prefix, retaining its
rotation, edge involution, orientation, and root. Helper toward thm-kmsw -/
structure KMSWPeanoPrefixDartEquiv
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hfinal : j + 1 = B.map.toCombinatorialMap.numEdges)
    (hcomplete : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      (kmswStage (codeExtend c) j).present d.1.val = true) where
  dartEquiv : StageDart (kmswStage (codeExtend c) j).nextEdge ≃ D
  rot_comm : ∀ d,
    dartEquiv ((kmswRootedStage (codeExtend c) j).map.rot d) =
      B.map.toCombinatorialMap.rot (dartEquiv d)
  edgeInv_comm : ∀ d,
    dartEquiv ((kmswRootedStage (codeExtend c) j).map.toCombinatorialMap.edgeInv d) =
      B.map.toCombinatorialMap.edgeInv (dartEquiv d)
  tail_iff : ∀ d,
    (kmswRootedStage (codeExtend c) j).map.tail d ↔ B.map.tail (dartEquiv d)
  root_comm : dartEquiv (kmswRootedStage (codeExtend c) j).root =
    peanoEdge B ⟨j, hj⟩

/-- Full image turns the induced cyclic order into rotation commutation and
packages the last-prefix dart map as an oriented rooted equivalence. Helper
toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
noncomputable def kmswPeanoPrefixEmbedding_finalDartEquiv
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hfinal : j + 1 = B.map.toCombinatorialMap.numEdges)
    (hcomplete : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      (kmswStage (codeExtend c) j).present d.1.val = true) :
    KMSWPeanoPrefixDartEquiv B c j hj P hfinal hcomplete := by
  classical
  have hb := kmswPeanoPrefixEmbedding_dartMap_bijective B c j hj P hfinal
  let e : StageDart (kmswStage (codeExtend c) j).nextEdge ≃ D :=
    Equiv.ofBijective P.emb.dartMap hb
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro d
    obtain ⟨k, hkpos, hkrot, hkfirst⟩ := P.emb.rot_induced d
    have hk : k = 1 := by
      by_contra hkne
      have hlt : 1 < k := by omega
      have himage :
          B.map.toCombinatorialMap.rot (P.emb.dartMap d) ∈
            Set.range P.emb.dartMap := by
        obtain ⟨d', hd'⟩ := hb.2
          (B.map.toCombinatorialMap.rot (P.emb.dartMap d))
        exact ⟨d', hd'⟩
      exact hkfirst 1 Nat.one_pos hlt himage
    subst k
    simpa only [e, baseRootedAt, Function.iterate_one,
      Equiv.ofBijective_apply] using hkrot.symm
  · intro d
    exact P.emb.flip_comm d
  · intro d
    apply P.emb.tail_comm d
    change ¬ (kmswStage (codeExtend c) j).present d.1.val = false
    rw [hcomplete d]
    decide
  · exact P.emb.root_comm

/-- A dart and its reverse have different tail vertices in a bipolar map,
since otherwise the directed orientation contains a one-edge cycle. Helper
toward thm-kmsw surjectivity by procedure reading
is not the paper result. -/
theorem peano_dart_no_loop
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map d ≠
      dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) := by
  intro h
  by_cases htail : B.map.tail d
  · have hstep : B.map.directedStep
        (dartTailVertex B.map d)
        (dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d)) := by
      exact ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
    apply B.acyclic (dartTailVertex B.map d)
    exact Relation.TransGen.single (h.symm ▸ hstep)
  · have hinvTail : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      by_contra hnot
      exact htail ((B.map.tail_iff d (B.noMissingDarts d)).2 hnot)
    have hinvPresent :
        ¬ B.map.missing (B.map.toCombinatorialMap.edgeInv d) := by
      intro hmissing
      exact B.noMissingDarts d ((B.map.missing_edgeInv d).mpr hmissing)
    have hstep : B.map.directedStep
        (dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d))
        (dartTailVertex B.map d) := by
      refine ⟨B.map.toCombinatorialMap.edgeInv d, hinvPresent, hinvTail, rfl, ?_⟩
      simp [dartTailVertex, B.map.toCombinatorialMap.edgeInv_invol]
    apply B.acyclic (dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d))
    exact Relation.TransGen.single (h ▸ hstep)

private theorem peano_rot_vertex
    (M : RootedDirectedMapWithMissing D) (d : D) :
    dartTailVertex M.map (M.map.rot d) = dartTailVertex M.map d := by
  apply Quotient.sound
  exact ⟨-1, by simp⟩

private theorem peano_rot_iter_vertex
    (M : RootedDirectedMapWithMissing D) (n : ℕ) :
    ∀ d : D,
      dartTailVertex M.map ((M.map.rot : D → D)^[n] d) =
        dartTailVertex M.map d := by
  induction n with
  | zero => intro d; rfl
  | succ n ih =>
    intro d
    rw [Function.iterate_succ_apply']
    exact (peano_rot_vertex M ((M.map.rot : D → D)^[n] d)).trans (ih d)

/-- The zero-step prefix embedding sends the two darts of the initial edge to
the forward Peano edge and its reverse. Helper toward thm-kmsw surjectivity by -/
@[expose] noncomputable def kmswPeanoPrefixEmbedding_zero
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) :
    KMSWPeanoPrefixEmbedding B c 0 (contour_numEdges_pos B) := by
  classical
  let w := codeExtend c
  let eidx : Fin B.map.toCombinatorialMap.numEdges :=
    ⟨0, contour_numEdges_pos B⟩
  let e : D := peanoEdge B eidx
  let S := kmswRootedStage w 0
  let φ : StageDart (kmswStage w 0).nextEdge → D :=
    fun d => if d.2 then B.map.toCombinatorialMap.edgeInv e else e
  have heForward : B.map.tail e := by
    simpa [e] using peanoEdge_forward B eidx
  have heNoLoop : dartTailVertex B.map e ≠
      dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e) :=
    peano_dart_no_loop B e
  have hEdgeCount : (kmswStage w 0).nextEdge = 1 := by
    simp [kmswStage, kmswInit]
  have hTailVertexUnique :
      ∀ d d' : StageDart (kmswStage w 0).nextEdge,
        dartTailVertex B.map (φ d') = dartTailVertex B.map (φ d) → d' = d := by
    intro d d' hvertex
    rcases d with ⟨ed, side⟩
    rcases d' with ⟨ed', side'⟩
    have hed : ed = ed' := by
      apply Fin.ext
      have hed' : ed.val = 0 := by
        have hh : ed.val < 1 := by
          simpa [kmswStage, kmswInit] using ed.isLt
        omega
      have hed'' : ed'.val = 0 := by
        have hh : ed'.val < 1 := by
          simpa [kmswStage, kmswInit] using ed'.isLt
        omega
      rw [hed', hed'']
    have hside : side' = side := by
      cases hs' : side' <;> cases hs : side
      · rfl
      · have hbad : dartTailVertex B.map e =
            dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e) := by
          simpa [φ, hs', hs] using hvertex
        exact False.elim (heNoLoop hbad)
      · have hbad : dartTailVertex B.map e =
            dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e) := by
          simpa [φ, hs', hs] using hvertex.symm
        exact False.elim (heNoLoop hbad)
      · rfl
    exact Prod.ext hed.symm hside
  have hindex (d : StageDart (kmswStage w 0).nextEdge) :
      peanoIndex B (φ d) = eidx := by
    cases hs : d.2
    · simpa [φ, hs, e] using peanoIndex_peanoEdge B eidx
    · have hinv := peanoIndex_edgeInv B e
      simpa [φ, hs, e] using hinv.trans (peanoIndex_peanoEdge B eidx)
  have hsourceRot (d : StageDart (kmswStage w 0).nextEdge) : S.map.rot d = d := by
    simp [S, kmswRootedStage, kmswStageDirectedMap, kmswDirectedMap,
      kmswMap, stageRot]
  refine {
      emb := {
        dartMap := φ
        injective := by
          intro d d' h
          exact (hTailVertexUnique d d'
            (congrArg (dartTailVertex B.map) h.symm)).symm
        flip_comm := by
          intro d
          change φ (edgeFlip (kmswStage w 0).nextEdge d) =
            B.map.toCombinatorialMap.edgeInv (φ d)
          rcases d with ⟨ed, side⟩
          cases side <;> simp [φ, edgeFlip,
            B.map.toCombinatorialMap.edgeInv_invol]
        present := by
          intro d hd
          exact B.noMissingDarts (φ d)
        tail_comm := by
          intro d hd
          change ((kmswStage w 0).present d.1.val = true ∧ d.2 = false) ↔
            B.map.tail (φ d)
          have hpresent : (kmswStage w 0).present d.1.val = true := by
            simp [kmswStage, kmswInit]
          cases hs : d.2
          · simpa [φ, hs, hpresent] using heForward
          · have hnot :
                ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv e) :=
              (B.map.tail_iff e (B.noMissingDarts e)).1 heForward
            simp [φ, hs, hpresent, hnot]
        rot_induced := by
          intro d
          let π := B.map.toCombinatorialMap.rot
          let x := φ d
          let P : ℕ → Prop := fun k =>
            0 < k ∧ (π : D → D)^[k] x = x
          have hP : ∃ k, P k := by
            refine ⟨orderOf π, orderOf_pos π, ?_⟩
            have hpow := congrArg (fun σ : Equiv.Perm D => σ x)
              (pow_orderOf_eq_one π)
            simpa only [Equiv.Perm.coe_pow, Equiv.Perm.one_apply] using hpow
          let k := Nat.find hP
          have hk : P k := Nat.find_spec hP
          refine ⟨k, hk.1, ?_, ?_⟩
          · change (π : D → D)^[k] x = φ (S.map.rot d)
            rw [hsourceRot d]
            exact hk.2
          · intro m hm0 hmk hmem
            rcases hmem with ⟨d', hd'⟩
            have hvertex :
                dartTailVertex B.map (φ d') = dartTailVertex B.map (φ d) := by
              calc
                dartTailVertex B.map (φ d') =
                    dartTailVertex B.map ((π : D → D)^[m] x) :=
                  congrArg (dartTailVertex B.map) hd'
                _ = dartTailVertex B.map x := peano_rot_iter_vertex
                  (baseRootedAt B e heForward) m x
                _ = dartTailVertex B.map (φ d) := rfl
            have hdEq : d' = d := hTailVertexUnique d d' hvertex
            have hmreturn : (π : D → D)^[m] x = x := by
              change φ d' = (π : D → D)^[m] x at hd'
              rw [hdEq] at hd'
              exact hd'.symm
            have hmin : k ≤ m := Nat.find_min' hP ⟨hm0, hmreturn⟩
            omega
        root_comm := by
          simp [e, φ, baseRootedAt, kmswRootedStage, kmswStage, kmswInit]
          apply congrArg (peanoEdge B)
          apply Fin.ext
          rfl
      }
      present_prefix := by
        intro d
        rw [hindex d]
        simp [kmswStage, kmswInit, eidx]
      edges_cover_prefix := by
        intro k hk
        have hk0 : k = 0 := by omega
        subst k
        let d : StageDart (kmswStage w 0).nextEdge :=
          (⟨0, by simp [kmswStage, kmswInit]⟩, false)
        refine ⟨d, ?_⟩
        simpa [eidx] using congrArg Fin.val (hindex d)
      missing_iff_frontier := by
        intro d
        simp [kmswStage, kmswInit]
      missing_is_future := by
        intro d hd
        simp [kmswStage, kmswInit] at hd
    }

end DirectedDistances.KMSW
