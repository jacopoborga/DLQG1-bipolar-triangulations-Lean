module

public import DirectedDistances.KMSW.Lemma79MarkTransport
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLaw
public import DirectedDistances.KMSW.Lemma79StoppedSubmap

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4







theorem stoppedMark_vertex_is_last_shared_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let w := boltzmannKMSWStream (pathCode p)
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let m := (stoppedMarked r hr p).2.val
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        mapLeftBoundaryVertex w hfin
          ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
        (∀ j, m < j → j ≤ (L w t).toNat →
          ¬ mapLeftBoundaryVertex w hfin
            ((stoppedLeftBoundaryVertices w t).getD j 0)) ∧
        ∃ (ht : 1 ≤ t) (ell : ℕ) (c : KMSWWalkClass ell r t),
          (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
          (stoppedMarked r hr p).1 =
            ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
          stoppedMap r hr (pathCode p) =
            some ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
          (stageMapVertex (codeExtend c) (t - 1)
            ((kmswWalkClassRep_baseIso ht c).vertexEquiv
              ((kmswWalkClassRep ht c).B.leftPath.vertices.getD m
                (kmswWalkClassRep ht c).B.source))).id =
            (stoppedLeftBoundaryVertices w t).getD m 0 := by
  filter_upwards [stoppedLeftBoundaryVertices_shared_indices_ae,
    stoppedMarked_clamp_inactive_ae r hr, stoppedMap_stageClass_ae r hr,
    postHitMinimum_attained_ae r] with p hshared hmark hclass hpost
  dsimp only at hshared hclass ⊢
  rcases hshared with ⟨_, hL, ⟨hfin, hindices⟩⟩
  obtain ⟨hmarkEq, hmapMark⟩ := hmark
  obtain ⟨ht, ell, c, hprefix, hmapClass, _⟩ := hclass
  obtain ⟨⟨s, hts, hsmin⟩, hpostMin, _⟩ := hpost
  obtain ⟨_, m₀, hmBound, hu, hminBound, hshared⟩ :=
    hindices r hr
  obtain ⟨u, htu, hum⟩ := hu
  have hm₀le : (m₀ : ℤ) ≤ postHitMinimum r p := by
    calc
      (m₀ : ℤ) ≤ L (boltzmannKMSWStream (pathCode p)) s := hminBound s hts
      _ = (p s).1 := hL s
      _ = postHitMinimum r p := hsmin
  have hpostle : postHitMinimum r p ≤ (m₀ : ℤ) := by
    calc
      postHitMinimum r p ≤ (p u).1 := hpostMin u htu
      _ = L (boltzmannKMSWStream (pathCode p)) u := (hL u).symm
      _ = (m₀ : ℤ) := hum
  have hminimum : (m₀ : ℤ) = postHitMinimum r p := le_antisymm hm₀le hpostle
  have hmarkIndex : (stoppedMarked r hr p).2.val = m₀ := by
    calc
      (stoppedMarked r hr p).2.val = (postHitMinimum r p).toNat := hmarkEq
      _ = ((m₀ : ℤ).toNat) := by rw [← hminimum]
      _ = m₀ := by simp
  have hmarkedClass : (stoppedMarked r hr p).1 =
      ⟨ell, ⟨(conditionedSecondCoordinateFirstHit r p).toNat,
        kmswToMapIsoClass ht c⟩⟩ := by
    exact Option.some.inj (hmapMark.symm.trans hmapClass)
  have hlength : ((stoppedMarked r hr p).1).1 = ell :=
    congrArg (fun q : AllBoltzmannSpace r => q.1) hmarkedClass
  have hmarkLt : (stoppedMarked r hr p).2.val < ell + 1 := by
    have h := (stoppedMarked r hr p).2.isLt
    change (stoppedMarked r hr p).2.val <
      ((stoppedMarked r hr p).1).1 + 1 at h
    omega
  have hprefix' : ∀ i : Fin ((conditionedSecondCoordinateFirstHit r p).toNat - 1),
      c.val i = (boltzmannKMSWStream (pathCode p)) i.val := by
    intro i
    simpa [boltzmannKMSWStream] using hprefix i
  have hbridge := kmswWalkClassRep_leftBoundaryVertex_getD_stagePrefix
    ht c (boltzmannKMSWStream (pathCode p)) hprefix'
      ⟨(stoppedMarked r hr p).2.val, hmarkLt⟩
  have hroot : activeInitial (boltzmannKMSWStream (pathCode p)) 0 = 0 := by
    simp [activeInitial, edgeWest, act, kmswStage, kmswInit]
  refine ⟨hfin, ?_, ?_, ht, ell, c, hprefix, hmarkedClass, hmapClass, ?_⟩
  · have hmem := (hshared (stoppedMarked r hr p).2.val
      (by omega)).2 (by omega)
    simpa only [hroot] using hmem
  · intro j hj hjbound hmem
    have hle := (hshared j hjbound).1 (by simpa only [hroot] using hmem)
    omega
  · simpa only [Fin.val_mk] using hbridge

end DirectedDistances.KMSW
