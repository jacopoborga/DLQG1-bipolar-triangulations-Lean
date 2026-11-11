module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.StageInfiniteOutgoingOrder
public import DirectedDistances.KMSW.Lemma79StageEdges
import DirectedDistances.KMSW.PathSpaceTransfer

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open MeasureTheory Filter

private theorem stage_faceSucc_eq_inverse_flip (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswMap w n).faceSucc d = (stageRot w n).symm (edgeFlip _ d) := rfl







theorem kmswStage_embeddedSubmap (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) :
    (kmswMap w n).IsPlanar ∧
    (∀ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true →
      EdgePresent w e ∧
      (kmswStage w n).west e = edgeWest w e ∧
      (kmswStage w n).east e = edgeEast w e ∧
      ∀ m, n ≤ m →
        e < (kmswStage w m).nextEdge ∧ (kmswStage w m).present e = true ∧
        (kmswStage w m).west e = (kmswStage w n).west e ∧
        (kmswStage w m).east e = (kmswStage w n).east e) ∧
    (∀ d : StageDart (kmswStage w n).nextEdge,
      (∃ k : ℕ, 0 < k ∧
        (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
          ((stageRot w n d).1.val, (stageRot w n d).2) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (kmswStage w n).nextEdge ≤
            ((kmswInfRot w hfin ^ j) (d.1.val, d.2)).1) ∧
      (∃ k : ℕ, 0 < k ∧
        ((kmswInfRot w hfin).symm ^ k) (d.1.val, d.2) =
          (((stageRot w n).symm d).1.val, ((stageRot w n).symm d).2) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (kmswStage w n).nextEdge ≤
            (((kmswInfRot w hfin).symm ^ j) (d.1.val, d.2)).1) ∧
      (∃ k : ℕ, 0 < k ∧
        ((kmswInfRot w hfin).symm ^ k) (d.1.val, !d.2) =
          (((kmswMap w n).faceSucc d).1.val, ((kmswMap w n).faceSucc d).2) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (kmswStage w n).nextEdge ≤
            (((kmswInfRot w hfin).symm ^ j) (d.1.val, !d.2)).1)) := by
  refine ⟨kmswMap_isPlanar w n, ?_, ?_⟩
  · intro e he hp
    obtain ⟨hw, hE⟩ := edge_endpoints_eq w he
    refine ⟨EdgePresent.of_stage_present he hp, hw, hE, ?_⟩
    intro m hm
    exact ⟨(present_mono w he hp m hm).1, (present_mono w he hp m hm).2,
      present_endpoints_stable w he hp hm⟩
  · intro d
    refine ⟨kmswInfRot_firstReturn_stage w hfin n d,
      kmswInfRot_symm_firstReturn_stage w hfin n d, ?_⟩
    rcases d with ⟨e, b⟩
    simpa only [stage_faceSucc_eq_inverse_flip, edgeFlip_apply] using
      kmswInfRot_symm_firstReturn_stage w hfin n (edgeFlip _ (e, b))

private theorem decoded_integrates (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    integrateCodes (boltzmannKMSWStream (pathCode p)) = p := by
  change codeWalk (pathCode p) = p
  funext n
  rw [codeWalk_pathCode p hp n, h0]
  exact sub_zero _

private theorem conditioned_finite_incidence :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let w := boltzmannKMSWStream (pathCode p)
      ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
        ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite := by
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp hc
  obtain ⟨w, hwp, hfin, _⟩ := hc
  have hw := decoded_integrates p hp.1 hp.2
  have heq := integrateCodes_injective (hwp.trans hw.symm)
  exact heq ▸ hfin






theorem stoppedStage_embeddedSubmap_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let w := boltzmannKMSWStream (pathCode p)
      let n := (conditionedSecondCoordinateFirstHit r p).toNat - 1
      conditionedSecondCoordinateFirstHit r p < ⊤ ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
          ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite,
        (∀ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true) ∧
        (kmswMap w n).IsPlanar ∧
        (∀ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true →
          EdgePresent w e ∧
          (kmswStage w n).west e = edgeWest w e ∧
          (kmswStage w n).east e = edgeEast w e ∧
          ∀ m, n ≤ m →
            e < (kmswStage w m).nextEdge ∧ (kmswStage w m).present e = true ∧
            (kmswStage w m).west e = (kmswStage w n).west e ∧
            (kmswStage w m).east e = (kmswStage w n).east e) ∧
        (∀ d : StageDart (kmswStage w n).nextEdge,
          (∃ k : ℕ, 0 < k ∧
            (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
              ((stageRot w n d).1.val, (stageRot w n d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w n).nextEdge ≤
                ((kmswInfRot w hfin ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, d.2) =
              (((stageRot w n).symm d).1.val, ((stageRot w n).symm d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w n).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, !d.2) =
              (((kmswMap w n).faceSucc d).1.val, ((kmswMap w n).faceSucc d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w n).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, !d.2)).1)) := by
  filter_upwards [stoppedStage_edges_present_ae r hr,
    conditioned_finite_incidence] with p hp hfin
  exact ⟨hp.1, hfin, hp.2, kmswStage_embeddedSubmap _ hfin _⟩

private theorem stoppedMap_stageClass (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    ∃ (ht : 1 ≤ boltzmannTau r ω) (ℓ : ℕ)
      (c : KMSWWalkClass ℓ r (boltzmannTau r ω)),
      c.val = stoppedWord r ω ∧
      stoppedMap r hr ω = some ⟨ℓ, ⟨boltzmannTau r ω, kmswToMapIsoClass ht c⟩⟩ ∧
      Nonempty (DirectedMapWithMissingIso
        (kmswStageDirectedMap (codeExtend c) (boltzmannTau r ω - 1))
        (kmswStageDirectedMap (boltzmannKMSWStream ω) (boltzmannTau r ω - 1))) := by
  classical
  let ℓ := (L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat
  let c : KMSWWalkClass ℓ r (boltzmannTau r ω) :=
    ⟨stoppedWord r ω, (stoppedWord_admissible r hr ω hE).1⟩
  have ht := (boltzmann_boundary_observable r hr ω hE).1
  refine ⟨ht, ℓ, c, rfl, ?_, ?_⟩
  · unfold stoppedMap stoppedIndex
    rw [dite_eq_left hE]
    dsimp only [Option.bind, stoppedWalkMapOption]
    rw [dite_eq_left ht]
    rfl
  · refine ⟨kmswStageDirectedMapIsoOfPrefix _ _ _ ?_⟩
    intro i hi
    rw [codeExtend_of_lt c i hi]
    rfl







theorem stoppedMap_stageClass_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      ∃ (ht : 1 ≤ t) (ℓ : ℕ) (c : KMSWWalkClass ℓ r t),
        (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
        stoppedMap r hr (pathCode p) = some ⟨ℓ, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
        Nonempty (DirectedMapWithMissingIso
          (kmswStageDirectedMap (codeExtend c) (t - 1))
          (kmswStageDirectedMap (boltzmannKMSWStream (pathCode p)) (t - 1))) := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    stoppedStage_edges_present_ae r hr] with p hp hc hs
  obtain ⟨w, hwp, _, _, _, hL, _⟩ := hc
  have hw : codeWalk (pathCode p) = p := decoded_integrates p hp.1 hp.2
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hh
    simpa only [conditionedSecondCoordinateFirstHit, dite_eq_right hh,
      lt_self_iff_false] using hs.1
  have hE : pathCode p ∈ boltzmannEvent r := by
    obtain ⟨t, ht⟩ := hh
    refine ⟨t, ?_, ?_⟩
    · rw [hw]
      exact ht
    · intro j _
      rw [hw, ← hwp, ← kmsw_L_eq]
      exact hL j
  have htau : boltzmannTau r (pathCode p) =
      (conditionedSecondCoordinateFirstHit r p).toNat := by
    simp only [boltzmannTau, hw, dite_eq_left hh,
      conditionedSecondCoordinateFirstHit, ENat.toNat_natCast]
  dsimp only
  rw [← htau]
  obtain ⟨ht, ℓ, c, hc, hmap, hiso⟩ := stoppedMap_stageClass r hr (pathCode p) hE
  exact ⟨ht, ℓ, c, fun i => congrFun hc i, hmap, hiso⟩

end DirectedDistances.KMSW
