module

public import DirectedDistances.KMSW.KMSWPeanoRotateFresh
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantSteps

/-! The empty upper-left predecessor branch cannot occur in a geometric prefix climb. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- The incoming third edge of a climb has already been visited, strictly before
the active edge. -/
theorem peanoIndex_edgeInv_rot_lt_of_climb
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (j : ℕ)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    (peanoIndex B (B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, by omega⟩)))).val < j := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let q := B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, _, _, _, _, hsel, _, _, _⟩ := hc
  have hq : B.map.tail q := by
    have h := (canonicalULSelector B _ hs).property.2.1
    rw [canonicalULSelector_val, ← hsel] at h
    exact h
  have hqhead : dartHeadVertex B.map q = dartTailVertex B.map a := by
    simpa only [q, dartHeadVertex, dartTailVertex,
      B.map.toCombinatorialMap.edgeInv_invol] using
      fresh_rot_vertex B a
  have hpos := fresh_incoming_before_outgoing B (dartTailVertex B.map a) q a
    hq (peanoEdge_forward B _) hqhead rfl
  have hqedge : peanoEdge B (peanoIndex B q) = q := by
    have hmem := (mem_firstVisitOrder_iff B q).2 hq
    have hget := List.idxOf_get (List.idxOf_lt_length_iff.mpr hmem)
    simpa only [peanoEdge, peanoIndex, peanoForwardDart, ite_eq_left hq,
      Fin.val_cast] using hget
  change (peanoIndex B q).val < j
  by_contra hnot
  have hle : j ≤ (peanoIndex B q).val := by omega
  have horder : (contourPosition B a).val ≤ (contourPosition B q).val := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hi : (⟨j, by omega⟩ : Fin B.map.toCombinatorialMap.numEdges) =
          peanoIndex B q := Fin.ext heq
      have ha : a = q := (congrArg (peanoEdge B) hi).trans hqedge
      exact (congrArg (fun d => (contourPosition B d).val) ha).le
    · have h := peanoEdge_increasing_firstVisit B ⟨j, by omega⟩ (peanoIndex B q) hlt
      rw [hqedge] at h
      exact h.le
  omega

/-- A geometric prefix climb always has an upper-left predecessor, so its
fresh-left branch is vacuous. -/
theorem kmswPeanoPrefixInv_climb_UL_ne_nil
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    (kmswStage (codeExtend c) j).UL.dropLast.reverse ≠ [] := by
  intro hUL
  have hfuture := ((kmswPeanoPrefixInv_climbFrontier B c j hj P I hj1 hkind).2.2 hUL).2
  have hpast := peanoIndex_edgeInv_rot_lt_of_climb B j hj1 hkind
  omega

end DirectedDistances.KMSW
