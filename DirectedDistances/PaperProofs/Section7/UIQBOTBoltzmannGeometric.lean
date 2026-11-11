/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.Lemma79SourceBoundaryBridge
public import DirectedDistances.KMSW.Lemma79MarkHeadline
public import DirectedDistances.KMSW.Lemma79StageEdges
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLawFull
public import DirectedDistances.KMSW.Lemma79StoppedSubmap
import DirectedDistances.KMSW.StageMapCongr

/-! # Geometric boundary helper toward Lemma 7.9

Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`), conditional on the n308
realization hypothesis `hreal`; not a paper result. Source: -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`), conditional on the n308
realization hypothesis `hreal`; not a paper result. See -/
theorem uiqbot_boltzmann_geometric_of_realization
    (hreal : ∀ (w : ℕ → Fin 3)
      (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite),
      Tendsto (L w) atTop atTop → (∀ a : ℤ, ∃ n, R w n ≤ a) →
      (∀ j, 0 ≤ L w j) → Nonempty (CoherentRealizationWitness w hfin)) :
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
          A * (r : ℝ) ^ 2}) := by
  refine ⟨stoppedMarked_law, fun r hr => ?_, stoppedStage_edges_window_tight⟩
  filter_upwards [stoppedStage_embeddedSubmap_ae r hr,
    stoppedMark_vertex_is_last_shared_ae r hr,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    conditionedVectorPathLaw_ae_legal,
    stoppedMarked_clamp_inactive_ae r hr,
    postHitMinimum_attained_ae r] with p hemb hmark hpath hlegal hclamp hpost
  let w := boltzmannKMSWStream (pathCode p)
  let t := (conditionedSecondCoordinateFirstHit r p).toNat
  let m := (stoppedMarked r hr p).2.val
  dsimp only [w, t, m] at hemb hmark
  obtain ⟨hfinite, hfin, hpresent, hplanar, hedges, hdarts⟩ := hemb
  obtain ⟨_, hcodeMark, hcodeLater, ht, ell, c, hpre, hclass, _, hvert⟩ :=
    hmark
  obtain ⟨u, hup, hfinPath, htrans, hR, hL0, _, _⟩ := hpath
  have hcode : integrateCodes (boltzmannKMSWStream (pathCode p)) = p := by
    funext n
    change integrateCodes (fun i => pathCode p (i + 1)) n = p n
    rw [← codeWalk_eq_integrateCodes (pathCode p) n]
    rw [codeWalk_pathCode p hlegal.2 n, hlegal.1]
    simp
  have hu : u = w := integrateCodes_injective (hup.trans hcode.symm)
  subst u
  have hL : ∀ s, L w s = (p s).1 := by
    intro s
    rw [kmsw_L_eq, hcode]
  have hmell : m ≤ ell := by
    have hlen : ((stoppedMarked r hr p).1).1 = ell :=
      congrArg (fun q : AllBoltzmannSpace r => q.1) hclass
    have hlt : m < ell + 1 := by
      have h := (stoppedMarked r hr p).2.isLt
      change m < ((stoppedMarked r hr p).1).1 + 1 at h
      rw [hlen] at h
      exact h
    omega
  have hclampM : m = (postHitMinimum r p).toNat := by
    simpa only [m] using hclamp.1
  have hm : m ≤ (L w t).toNat := by
    have hmin := hpost.2.1 t le_rfl
    have hnat : (postHitMinimum r p).toNat ≤ ((p t).1).toNat :=
      Int.toNat_le_toNat hmin
    rw [hclampM, hL t]
    exact hnat
  obtain ⟨W⟩ := hreal w hfin htrans hR hL0
  have hprefix : ∀ i : Fin (t - 1), c.val i = w i.val := by
    intro i
    simpa [w, boltzmannKMSWStream] using hpre i
  obtain ⟨Us, hUs, hstageM, htopM, hnoLater⟩ :=
    stoppedMark_last_shared_geometric W ht htrans hR hL0 c hprefix hmell hm
      hcodeMark hcodeLater
  refine And.intro hfinite ?_
  refine And.intro hpresent ?_
  refine And.intro hplanar ?_
  refine Exists.intro hfin ?_
  refine And.intro hedges ?_
  refine And.intro hdarts ?_
  refine And.intro ?_ ?_
  · refine Exists.intro W ?_
    refine Exists.intro Us ?_
    refine And.intro hUs ?_
    refine And.intro hstageM ?_
    refine And.intro htopM ?_
    simpa only [w, t, m] using hnoLater
  · refine Exists.intro ht ?_
    refine Exists.intro ell ?_
    refine Exists.intro c ?_
    refine And.intro hpre ?_
    refine And.intro hclass ?_
    refine And.intro ?_ hvert
    refine ⟨kmswStageDirectedMapIsoOfPrefix _ _ _ ?_⟩
    intro i hi
    rw [codeExtend_of_lt c i hi]
    simpa [boltzmannKMSWStream] using hpre ⟨i, hi⟩

end DirectedDistances.PaperProofs.Section7
