/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization2
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteRadiusLawBridge
import DirectedDistances.KMSW.KMSWPeanoClimbFreshVacuous

/-! # Peano indices and finite KMSW stages

The procedure representative is a dart relabelling of the final stage, rather
than a different boundary map. The prefix induction below retains old dart
images, so one final isomorphism aligns every chronological index at once.
The imported procedure-reading qualification is retained. This file makes no -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

private theorem peanoPrefix_step_old {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ ρ n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ ρ)
    (c : KMSWWalkClass ℓ ρ n) (t : ℕ)
    (ht : t < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c t ht)
    (I : KMSWPeanoPrefixInv B c t ht P)
    (ht1 : t + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : (codeExtend c t = 2 ↔ peanoStepKind B t ht1 = .descend) ∧
      (codeExtend c t = 0 ↔ peanoStepKind B t ht1 = .climb) ∧
      (codeExtend c t = 1 ↔ peanoStepKind B t ht1 = .rotate)) :
    ∃ Q : KMSWPeanoPrefixEmbedding B c (t + 1) ht1,
      KMSWPeanoPrefixInv B c (t + 1) ht1 Q ∧
      ∀ d, Q.emb.dartMap
        (outerSucc_castDart (kmswStage_nextEdge_mono (codeExtend c) (Nat.le_succ t)) d) =
          P.emb.dartMap d := by
  cases hk : peanoStepKind B t ht1 with
  | descend =>
      exact kmswPeanoPrefixInv_descend B c t ht P I ht1 hk (hkind.1.mpr hk)
  | rotate =>
      have hc := hkind.2.2.mpr hk
      let hf := kmswPeanoPrefixInv_rotateFresh B c t ht P I ht1 hk
      refine ⟨kmswPeanoPrefixEmbedding_rotate P ht1 hc hk hf,
        kmswPeanoPrefixInv_rotate B c t ht P I ht1 hc hk hf, ?_⟩
      intro d
      exact kmswPeanoRotateDartMap_old P ht1 d
  | climb =>
      have hc := hkind.2.1.mpr hk
      have hne := kmswPeanoPrefixInv_climb_UL_ne_nil B c t ht P I ht1 hk
      cases hUL : (kmswStage (codeExtend c) t).UL.dropLast.reverse with
      | nil => exact (hne hUL).elim
      | cons e es =>
          exact kmswPeanoPrefixInv_climb_leftExisting B c t ht P I ht1 hk hc e es hUL

private theorem peanoPrefix_history {ℓ ρ n : ℕ} (R : KMSWMapRep ℓ ρ n) :
    ∀ t (ht : t < R.B.map.toCombinatorialMap.numEdges),
      ∃ P : KMSWPeanoPrefixEmbedding R.B (kmswRepInverseWalkClass R) t ht,
        KMSWPeanoPrefixInv R.B (kmswRepInverseWalkClass R) t ht P ∧
        ∀ k (hk : k ≤ t), P.emb.dartMap
          ((⟨act (codeExtend (kmswRepInverseWalkClass R)) k,
            act_lt_nextEdge _ hk⟩, false) :
            StageDart (kmswStage (codeExtend (kmswRepInverseWalkClass R)) t).nextEdge) =
          peanoEdge R.B ⟨k, lt_of_le_of_lt hk ht⟩ := by
  intro t
  induction t with
  | zero =>
      intro ht
      refine ⟨kmswPeanoPrefixEmbedding_zero R.B _, kmswPeanoPrefixInv_zero R.B _, ?_⟩
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact (kmswPeanoPrefixEmbedding_zero R.B _).emb.root_comm
  | succ t ih =>
      intro ht1
      have ht : t < R.B.map.toCombinatorialMap.numEdges := by omega
      obtain ⟨P, I, hhist⟩ := ih ht
      have htn : t + 1 < n := by simpa only [R.edges] using ht1
      obtain ⟨Q, IQ, hold⟩ := peanoPrefix_step_old R.B _ t ht P I ht1
        ⟨codeExtend_kmswRepInverseWalkClass_eq_two_iff_peanoStepKind_descend R t htn,
         codeExtend_kmswRepInverseWalkClass_eq_zero_iff_peanoStepKind_climb R t htn,
         codeExtend_kmswRepInverseWalkClass_eq_one_iff_peanoStepKind_rotate R t htn⟩
      refine ⟨Q, IQ, ?_⟩
      intro k hk
      by_cases hkt : k ≤ t
      · exact (hold (⟨act _ k, act_lt_nextEdge _ hkt⟩, false)).trans (hhist k hkt)
      · have hkeq : k = t + 1 := by omega
        subst k
        exact Q.emb.root_comm

/-- Helper toward Proposition 3.9: any representative of the procedure class
has precisely the original code as its inverse code, with no extra premise. -/
theorem uibotPeano_inverseWalkClass_eq {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) :
    kmswRepInverseWalkClass R = c := by
  rw [← kmswClassInverseWalkClass_mk, hR]
  exact kmswClassInverseWalkClass_comp_forward_of_prefix
    (kmswPeanoPrefixExistsFinal_holds ℓ ρ n) hn c

/-- Helper toward Proposition 3.9: one directed plane-map isomorphism from
the final stage to every actual representative preserves rotation, reversal,
missing tags, tails and exterior face, and sends every chronological active
dart `j` to the SAME zero-based Peano index `j`. In manuscript notation this
is `λ_(j+1)` in the inverse procedure, with no reversal of orientation. -/
theorem uibotPeano_stageMapIso_exists {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) :
    ∃ I : DirectedMapWithMissingIso
        (kmswStageDirectedMap (codeExtend c) (n - 1)) R.B.map,
      ∀ j : Fin n, I.toEquiv
        (⟨act (codeExtend c) j.val, act_lt_nextEdge _ (by have := j.isLt; omega)⟩,
          false) = peanoEdge R.B (Fin.cast R.edges.symm j) := by
  have hc := uibotPeano_inverseWalkClass_eq hn c R hR
  subst c
  obtain ⟨P, _, hhist⟩ := peanoPrefix_history R (n - 1) (kmswPeanoPrefixFinal_lt R)
  let c := kmswRepInverseWalkClass R
  let B := kmswWalkClassBase (kmswPeanoPrefixFinal_pos R) c
  have hfinal := kmswPeanoPrefixFinal_hfinal R
  have hcomplete := kmswPeanoPrefixFinal_complete R
  let e := Equiv.ofBijective P.emb.dartMap
    (kmswPeanoPrefixEmbedding_dartMap_bijective R.B c (n - 1)
      (kmswPeanoPrefixFinal_lt R) P hfinal)
  have hrot (d) : e ((kmswStageDirectedMap (codeExtend c) (n - 1)).rot d) =
      R.B.map.rot (e d) := by
    obtain ⟨k, hkpos, hkrot, hkfirst⟩ := P.emb.rot_induced d
    have hk : k = 1 := by
      by_contra hkne
      have hlt : 1 < k := by omega
      exact hkfirst 1 Nat.one_pos hlt
        ⟨e.symm (R.B.map.rot (e d)), e.apply_symm_apply _⟩
    subst k
    simpa only [e, c, kmswRootedStage, baseRootedAt, Function.iterate_one,
      Equiv.ofBijective_apply]
      using hkrot.symm
  have hinv (d) : e ((kmswStageDirectedMap (codeExtend c) (n - 1)).edgeInv d) =
      R.B.map.edgeInv (e d) := P.emb.flip_comm d
  have htail (d) : R.B.map.tail (e d) ↔ B.map.tail d := by
    exact (P.emb.tail_comm d (by
      change ¬ (kmswStage (codeExtend c) (n - 1)).present d.1.val = false
      rw [hcomplete d]
      decide)).symm
  have hroot : e (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) =
      pathLastDart R.B.leftPath (Nat.zero_lt_of_lt R.B.left_length_pos) := by
    rw [← kmswPeanoPrefixFinal_stageRoot_eq_lastLeft R]
    change P.emb.dartMap _ = _
    rw [P.emb.root_comm]
    convert peanoEdge_last R.B using 1
    apply congrArg (peanoEdge R.B)
    apply Fin.ext
    simp only [R.edges]
  have houter (d) : R.B.map.IsOuter (e d) ↔ B.map.IsOuter d := by
    apply bipolarOuter_iff_of_matchedOuterDart B R.B e hrot hinv
      (d₀ := pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos))
    · apply canonicalOuterBoundaryDarts_mem_isOuter B
      exact List.mem_append_left _ (List.get_mem _ _)
    · rw [hroot]
      apply canonicalOuterBoundaryDarts_mem_isOuter R.B
      exact List.mem_append_left _ (List.get_mem _ _)
  refine ⟨{
    toEquiv := e
    rot_comm := hrot
    edgeInv_comm := hinv
    missing_iff := fun d => iff_of_false (R.B.noMissingDarts _) (B.noMissingDarts d)
    tail_iff := htail
    outer_iff := houter }, ?_⟩
  intro j
  exact hhist j.val (by have := j.isLt; omega)

/-- Helper toward Proposition 3.9: the finite stage rooted at an earlier
chronological active dart. Its root is present and oriented from west to east. -/
@[expose] def uibotChronologicalRootedStage (w : ℕ → Fin 3) (m k : ℕ)
    (hk : k ≤ m) : RootedDirectedMapWithMissing (StageDart (kmswStage w m).nextEdge) := by
  let d : StageDart (kmswStage w m).nextEdge :=
    (⟨act w k, act_lt_nextEdge w hk⟩, false)
  have hp : (kmswStage w m).present (act w k) = true :=
    (present_mono w (act_lt_nextEdge w le_rfl)
      (kmswStage_active_present w k) m hk).2
  refine ⟨kmswStageDirectedMap w m, d, ?_, ?_⟩
  · change ¬ (kmswStage w m).present (act w k) = false
    rw [hp]
    exact Bool.noConfusion
  · exact ⟨hp, rfl⟩

/-- Helper toward Proposition 3.9: every actual Peano-rooted representative
is isomorphic to the SAME-index chronologically rooted final stage. The
`RootedDirectedMapIso` fields retain rotation, edge reversal, missing/present
status, directed tails, exterior-face orbit and the ordered root dart. -/
@[expose] noncomputable def uibotPeanoChronologicalRootedIso {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n) :
    RootedDirectedMapIso (uibotPeanoRootedAt R j)
      (uibotChronologicalRootedStage (codeExtend c) (n - 1) j.val
        (by have := j.isLt; omega)) := by
  let I := (uibotPeano_stageMapIso_exists hn c R hR).choose
  have hh := (uibotPeano_stageMapIso_exists hn c R hR).choose_spec
  exact {
    dartEquiv := I.symm.toEquiv
    rot_comm := I.symm.rot_comm
    edgeFlip_comm := I.symm.edgeInv_comm
    missing_iff := fun d => (I.symm.missing_iff d).symm
    present_iff := fun d => not_congr (I.symm.missing_iff d).symm
    tail_iff := fun d => (I.symm.tail_iff d).symm
    outer_iff := fun d => (I.symm.outer_iff d).symm
    root_comm := I.toEquiv.symm_apply_eq.mpr (hh j).symm }






theorem uibotPeanoChronologicalRootedIso_geometricRoot {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1)) :
    let I := uibotPeanoChronologicalRootedIso hn c R hR j
    let e := Quotient.mk P.edgeSetoid (I.dartEquiv (uibotPeanoRootedAt R j).root)
    (e, !e.out.2) =
      uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega) := by
  dsimp only
  rw [(uibotPeanoChronologicalRootedIso hn c R hR j).root_comm]
  rfl

/-- Helper toward Proposition 3.9: transport individual edge identities from
the actual representative to the drawing. Parallel edges stay distinct;
this is an equivalence of flip orbits, not of adjacency pairs. -/
@[expose] noncomputable def uibotPeanoStageDrawingEdgeEquiv {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1)) :
    CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap ≃ P.GeometricEdge := by
  let I := uibotPeanoChronologicalRootedIso hn c R hR j
  apply Quotient.congr I.dartEquiv
  intro d e
  change R.B.map.edgeInv.SameCycle d e ↔
    I.dartEquiv d = I.dartEquiv e ∨ I.dartEquiv d = edgeFlip _ (I.dartEquiv e)
  have hrel : R.B.map.edgeInv.SameCycle d e ↔
      d = e ∨ d = R.B.map.edgeInv e :=
    ⟨fun h => (CombinatorialMap.edgeInv_sameCycle_iff _ e d).mp h.symm,
      fun h => ((CombinatorialMap.edgeInv_sameCycle_iff _ e d).mpr h).symm⟩
  have hflip : I.dartEquiv (R.B.map.edgeInv e) = edgeFlip _ (I.dartEquiv e) :=
    I.edgeFlip_comm e
  rw [hrel, ← hflip]
  exact or_congr I.dartEquiv.injective.eq_iff.symm I.dartEquiv.injective.eq_iff.symm

/-- Helper toward Proposition 3.9: on each dart the edge equivalence is the
geometric edge orbit of its transported stage dart. -/
theorem uibotPeanoStageDrawingEdgeEquiv_mk {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1)) (d : Fin R.dartCount) :
    uibotPeanoStageDrawingEdgeEquiv hn c R hR j P (Quotient.mk _ d) =
      Quotient.mk P.edgeSetoid
        ((uibotPeanoChronologicalRootedIso hn c R hR j).dartEquiv d) := rfl

/-- Helper toward Proposition 3.9: the entire drawing edge equivalence
preserves missing status, for every cell certificate `Q`. -/
theorem uibotPeanoStageDrawingEdgeEquiv_missing {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1))
    (Q : StageGeom (codeExtend c) (n - 1) P) (d : Fin R.dartCount) :
    (kmswStageDrawingDirectedPlaneMap P Q).missing
      (uibotPeanoStageDrawingEdgeEquiv hn c R hR j P (Quotient.mk _ d)) ↔
        R.B.map.missing d := by
  rw [uibotPeanoStageDrawingEdgeEquiv_mk, kmswStageDrawing_missing_mk]
  exact (uibotPeanoChronologicalRootedIso hn c R hR j).missing_iff d |>.symm



theorem uibotPeanoStageDrawingEdgeEquiv_root {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1)) :
    uibotPeanoStageDrawingEdgeEquiv hn c R hR j P (uibotPeanoEdgeEquiv R j) =
      (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)).1 := by
  rw [uibotPeanoEdgeEquiv_apply, uibotPeanoStageDrawingEdgeEquiv_mk]
  exact congrArg (fun d => Quotient.mk P.edgeSetoid d)
    (uibotPeanoChronologicalRootedIso hn c R hR j).root_comm

/-- Helper toward Proposition 3.9: the ordered geometric dart corresponding
to a stage dart. The Boolean selects the drawing's stored source precisely
when its representative has the same endpoint bit as the input dart. -/
@[expose] noncomputable def uibotStageDrawingOrderedDart {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (d : StageDart (kmswStage w m).nextEdge) :
    P.GeometricEdge × Bool :=
  let e := Quotient.mk P.edgeSetoid d
  (e, e.out.2 == d.2)

/-- Helper toward Proposition 3.9: the ordered geometric dart retains its
initial stage vertex, independently of the quotient representative. -/
theorem uibotStageDrawingOrderedDart_initial {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (Q : StageGeom w m P)
    (d : StageDart (kmswStage w m).nextEdge) :
    d39GeomRootVertex (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotStageDrawingOrderedDart P d) = stageVertex w m d := by
  change (if (Quotient.mk P.edgeSetoid d).out.2 == d.2
    then stageVertex w m (Quotient.mk P.edgeSetoid d).out
    else stageVertex w m (edgeFlip _ (Quotient.mk P.edgeSetoid d).out)) = _
  rcases P.geometricEdge_out_mk d with ho | ho
  · rw [ho]
    cases d.2 <;> rfl
  · rw [ho]
    rcases d with ⟨e, b⟩
    cases b <;> rfl

/-- Helper toward Proposition 3.9: on present edges the drawing's actual
orientation agrees with the stage tail tag for the ordered geometric dart. -/
theorem uibotStageDrawingOrderedDart_orientation {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (Q : StageGeom w m P)
    (d : StageDart (kmswStage w m).nextEdge)
    (hd : ¬ (kmswStageDrawingDirectedPlaneMap P Q).missing
      (uibotStageDrawingOrderedDart P d).1) :
    (kmswStageDirectedMap w m).tail d ↔
      (kmswStageDrawingDirectedPlaneMap P Q).forward
        ⟨(uibotStageDrawingOrderedDart P d).1, hd⟩ =
          (uibotStageDrawingOrderedDart P d).2 := by
  have hm : ¬ (kmswStageDirectedMap w m).missing d :=
    fun h => hd ((kmswStageDrawing_missing_mk P Q d).mpr h)
  have hp : (kmswStage w m).present d.1.val = true :=
    Bool.eq_true_of_not_eq_false hm
  change ((kmswStage w m).present d.1.val = true ∧ d.2 = false) ↔
    (!(Quotient.mk P.edgeSetoid d).out.2) = ((Quotient.mk P.edgeSetoid d).out.2 == d.2)
  rw [hp]
  cases (Quotient.mk P.edgeSetoid d).out.2 <;> cases d.2 <;> decide

/-- Helper toward Proposition 3.9: the finite drawing realizes the
orientation of EVERY dart of an actual representative under the rooted
isomorphism, as well as its ordered initial vertex. -/
theorem uibotPeanoStageDrawing_dart_data {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1))
    (Q : StageGeom (codeExtend c) (n - 1) P) (d : Fin R.dartCount) :
    let I := uibotPeanoChronologicalRootedIso hn c R hR j
    let mark := uibotStageDrawingOrderedDart P (I.dartEquiv d)
    d39GeomRootVertex (kmswStageDrawingDirectedPlaneMap P Q) mark =
        stageVertex (codeExtend c) (n - 1) (I.dartEquiv d) ∧
      ∀ hd : ¬ (kmswStageDrawingDirectedPlaneMap P Q).missing mark.1,
        R.B.map.tail d ↔ (kmswStageDrawingDirectedPlaneMap P Q).forward
          ⟨mark.1, hd⟩ = mark.2 := by
  dsimp only
  refine ⟨uibotStageDrawingOrderedDart_initial P Q _, ?_⟩
  intro hd
  exact ((uibotPeanoChronologicalRootedIso hn c R hR j).tail_iff d).trans
    (uibotStageDrawingOrderedDart_orientation P Q _ hd)

/-- Helper toward Proposition 3.9: identification with the underlying finite
stage dart map for every drawing and cell certificate, rooted at exactly the
specified chronological geometric mark. The isomorphism notion is
`RootedDirectedMapIso`; its fields preserve the full finite rotation system,
edge reversal, missing/present tags, tails, exterior-face orbit and root.
The geometric missing tags are identified on every dart as well. -/
theorem uibotPeanoStageDrawing_identification {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1))
    (Q : StageGeom (codeExtend c) (n - 1) P) :
    ∃ I : RootedDirectedMapIso (uibotPeanoRootedAt R j)
        (uibotChronologicalRootedStage (codeExtend c) (n - 1) j.val
          (by have := j.isLt; omega)),
      uibotStageDrawingOrderedDart P (I.dartEquiv (uibotPeanoRootedAt R j).root) =
        uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega) ∧
      ∀ d : Fin R.dartCount,
        (kmswStageDrawingDirectedPlaneMap P Q).missing
          (uibotStageDrawingOrderedDart P (I.dartEquiv d)).1 ↔ R.B.map.missing d := by
  let I := uibotPeanoChronologicalRootedIso hn c R hR j
  refine ⟨I, ?_, ?_⟩
  · rw [I.root_comm]
    let d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
      (⟨act (codeExtend c) j.val, act_lt_nextEdge _ (by have := j.isLt; omega)⟩, false)
    change (Quotient.mk P.edgeSetoid d,
        (Quotient.mk P.edgeSetoid d).out.2 == false) =
      (Quotient.mk P.edgeSetoid d, !(Quotient.mk P.edgeSetoid d).out.2)
    cases (Quotient.mk P.edgeSetoid d).out.2 <;> rfl
  · intro d
    exact (kmswStageDrawing_missing_mk P Q (I.dartEquiv d)).trans
      (I.missing_iff d).symm

/- Scope of the identification and the remaining stronger geometric statement.

The finite drawing is parametrized by the stage rotation, reversal and vertex
map by definition of StageDrawing. The theorem above identifies this finite
dart map, all its edge orbits, and its ordered geometric root with every
actual representative. The independently specified geometric local topology realization
requires further face and topological rotation data; those are not fields of
RootedDirectedMapIso. A precise stronger open statement (not a declaration) is:

∀ (ℓ ρ n : ℕ) (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (j : Fin n)
  (P : StageDrawing (codeExtend c) (n - 1))
  (Q : StageGeom (codeExtend c) (n - 1) P),
  let S := uibotChronologicalRootedStage (codeExtend c) (n - 1) j.val
    (by have := j.isLt; omega)
  let M : D39RootedMap :=
    ⟨(kmswStageD39RootedMap (codeExtend c) (n - 1)).core,
      .present S.root S.root_present S.root_tail⟩
  let B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2 :=
    ⟨_, _, kmswStageDrawingDirectedPlaneMap P Q,
      uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega),
      uibotFiniteStageGeometricMap_domain P Q j.val (by have := j.isLt; omega)⟩
  Nonempty (D39DrawingRepresentationData3 M B).

Routes examined: the procedure's canonical carrier is a dart relabelling of
kmswWalkClassBase, whose map is definitionally the final stage. The existing
final-prefix equivalence aligns only its last root in its exported signature;
retaining old-dart compatibility in the induction proves all chronological
indices simultaneously here. The drawing's quotient supplies geometric edge
identity, missing labels, endpoints and orientations, as proved above. The
remaining representation fields include faceOfDart, faceOrbit_iff,
face_surjective, face_left_of_dart, the topological counterclockwise successor,
and full face-frontier incidence. The available finite drawing base module
records these as open; no such representation is assumed here. No finite to
whole-paper completion is claimed. -/

end DirectedDistances.PaperProofs.Section3
