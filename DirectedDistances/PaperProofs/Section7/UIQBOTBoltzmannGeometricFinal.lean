module

public import DirectedDistances.PaperProofs.Section7.UIQBOTBoltzmannGeometric
public import DirectedDistances.KMSW.KMSWConstructedRealizationProof

/-! # The coherent realization witness for Lemma 7.9

The conditional provider `uiqbot_boltzmann_geometric_of_realization` assumed that every
admissible stream has a coherent realization witness (stage drawings with monotone
invariants and a classified limit drawing). The x-monotone layout supplies one, so the
hypothesis is discharged here. Provider only; no anchor is installed or counted. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Filter MeasureTheory Set DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4

/-- Every stream satisfying the UIQBOT hypotheses has a coherent realization witness: the
x-monotone layout drawings, their invariants and their classified union
Provider toward Lemma 7.9; not a paper result. -/
theorem coherentRealizationWitness_all (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    Tendsto (L w) atTop atTop → (∀ a : ℤ, ∃ n, R w n ≤ a) →
      (∀ j, 0 ≤ L w j) → Nonempty (CoherentRealizationWitness w hfin) := by
  intro htrans hR hL0
  have hfam := monotone_family_all w
  have hbd := monotoneRegionBoundedExhaustion_of_KMSW w hfin htrans hR hL0
    (familyQ w hfam) (familyG w hfam)
  obtain ⟨U, hU1, hU2, hU3⟩ := monotoneFamily_hface w hfin htrans hR hL0 hfam
    (monotoneLimitExterior_isOpen_of_boundedExhaustion _ _ hbd)
    (monotoneLimitExterior_isPathConnected_of_KMSW w hfin htrans hR hL0 _ _)
    (monotoneLimitExterior_unbounded_of_xmin_zero _ _
      (fun n => monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 _))
    (monotoneLimitExterior_frontier_subset_trace _ _ hbd)
    (fun n => monotoneLimitExterior_disjoint_stageImage _ _ n)
    (by
      intro z hz hzE
      apply monotoneStageRegionUnion_mem_cap_of_not_trace _ _ (not_not.mp hzE)
      simp only [monotoneLayoutTraceUnion, mem_iUnion, not_exists]
      exact hz)
  exact ⟨{ Q := familyQ w hfam
           hExtends := fun n => stageExtends_monotoneLayout w n _ _
           G := familyG w hfam
           P := monotoneFamilyDrawing w hfin hfam
           pos_agree := familyDrawing_pos w hfin hfam
           arc_agree := familyDrawing_arc w hfin hfam
           U := U
           unbounded := hU1
           unique_unbounded := hU2
           borders := hU3 }⟩

 
theorem uiqbot_boltzmann_geometric_final :
    (∀ r : ℕ, ∀ hr : 1 ≤ r,
      (conditionedVectorPathLaw 0 0).map (stoppedMarked r hr) =
        rightVertexMarkedBoltzmannLaw r) ∧
    (∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let w := boltzmannKMSWStream (pathCode p)
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let m := (stoppedMarked r hr p).2.val
      conditionedSecondCoordinateFirstHit r p < ⊤ ∧
      (∀ e < (kmswStage w (t - 1)).nextEdge, (kmswStage w (t - 1)).present e = true) ∧
      (kmswMap w (t - 1)).IsPlanar ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        (∀ e < (kmswStage w (t - 1)).nextEdge, (kmswStage w (t - 1)).present e = true →
          EdgePresent w e ∧
          (kmswStage w (t - 1)).west e = edgeWest w e ∧
          (kmswStage w (t - 1)).east e = edgeEast w e ∧
          ∀ n, t - 1 ≤ n →
            e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true ∧
            (kmswStage w n).west e = (kmswStage w (t - 1)).west e ∧
            (kmswStage w n).east e = (kmswStage w (t - 1)).east e) ∧
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (∃ k : ℕ, 0 < k ∧
            (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
              ((stageRot w (t - 1) d).1.val, (stageRot w (t - 1) d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                ((kmswInfRot w hfin ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, d.2) =
              (((stageRot w (t - 1)).symm d).1.val, ((stageRot w (t - 1)).symm d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, !d.2) =
              (((kmswMap w (t - 1)).faceSucc d).1.val,
                ((kmswMap w (t - 1)).faceSucc d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, !d.2)).1)) ∧
        (∃ W : CoherentRealizationWitness w hfin,
          ∃ Us : (W.Q (t - 1)).Face,
            (W.Q (t - 1)).IsUnbounded Us ∧
            StageLeftBoundaryVertex (W.Q (t - 1)) Us
              ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
            TopLeftBoundaryVertex w W.P W.U
              ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
            (∀ j, m < j → j ≤ (L w t).toNat →
              ¬ (StageLeftBoundaryVertex (W.Q (t - 1)) Us
                    ((stoppedLeftBoundaryVertices w t).getD j 0) ∧
                  TopLeftBoundaryVertex w W.P W.U
                    ((stoppedLeftBoundaryVertices w t).getD j 0)))) ∧
        ∃ (ht : 1 ≤ t) (ell : ℕ) (c : KMSWWalkClass ell r t),
          (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
          (stoppedMarked r hr p).1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
          Nonempty (DirectedMapWithMissingIso
            (kmswStageDirectedMap (codeExtend c) (t - 1))
            (kmswStageDirectedMap w (t - 1))) ∧
          (stageMapVertex (codeExtend c) (t - 1)
            ((kmswWalkClassRep_baseIso ht c).vertexEquiv
              ((kmswWalkClassRep ht c).B.leftPath.vertices.getD m
                (kmswWalkClassRep ht c).B.source))).id =
            (stoppedLeftBoundaryVertices w t).getD m 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ (conditionedVectorPathLaw 0 0).real {p | ∃ t : ℕ,
        (p t).2 = -(r : ℤ) ∧ (∀ j < t, (p j).2 ≠ -(r : ℤ)) ∧
        (r : ℝ) ^ 2 / A ≤
          ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ∧
        ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ≤
          A * (r : ℝ) ^ 2}) :=
  uiqbot_boltzmann_geometric_of_realization coherentRealizationWitness_all

end DirectedDistances.PaperProofs.Section7
